package org.jetbrains.kotlin.backend.konan.lower.loops

import org.jetbrains.kotlin.backend.common.IrElementTransformerVoidWithContext
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.backend.konan.Context
import org.jetbrains.kotlin.backend.konan.irasdescriptors.isSubtypeOf
import org.jetbrains.kotlin.backend.konan.irasdescriptors.typeWithoutArguments
import org.jetbrains.kotlin.builtins.KotlinBuiltIns
import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.incremental.components.NoLookupLocation
import org.jetbrains.kotlin.ir.IrElement
import org.jetbrains.kotlin.ir.builders.irCall
import org.jetbrains.kotlin.ir.builders.irCallOp
import org.jetbrains.kotlin.ir.declarations.IrVariable
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.expressions.impl.IrCallImpl
import org.jetbrains.kotlin.ir.expressions.impl.IrCompositeImpl
import org.jetbrains.kotlin.ir.expressions.impl.IrConstImpl
import org.jetbrains.kotlin.ir.symbols.IrClassSymbol
import org.jetbrains.kotlin.ir.symbols.IrFunctionSymbol
import org.jetbrains.kotlin.ir.types.IrType
import org.jetbrains.kotlin.ir.types.toKotlinType
import org.jetbrains.kotlin.ir.util.getPropertyGetter
import org.jetbrains.kotlin.ir.util.irCallOp
import org.jetbrains.kotlin.ir.util.referenceFunction
import org.jetbrains.kotlin.ir.visitors.IrElementVisitor
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.types.KotlinType
import org.jetbrains.kotlin.types.typeUtil.makeNotNullable
import org.jetbrains.kotlin.util.OperatorNameConventions


// TODO: Replace with a cast when such support is added in the boxing lowering.
// TODO: Use IrType
internal data class ProgressionType(val elementType: KotlinType, val numberCastFunctionName: Name) {
    fun isIntProgression() = KotlinBuiltIns.isInt(elementType)
    fun isLongProgression() = KotlinBuiltIns.isLong(elementType)
    fun isCharProgression() = KotlinBuiltIns.isChar(elementType)
}

/** Contains information about variables used in the loop. */
internal data class ForLoopInfo(
        val progressionInfo: ProgressionInfo,
        val inductionVariable: IrVariable,
        val bound: IrVariable,
        val last: IrVariable,
        val step: IrVariable,
        var loopVariable: IrVariable? = null)

internal data class ProgressionInfo(
        val progressionType: ProgressionType,
        val first: IrExpression,
        val bound: IrExpression,
        val step: IrExpression? = null,
        val increasing: Boolean = true,
        var needLastCalculation: Boolean = false,
        val closed: Boolean = true)

/**
 * Gives IR representation of methods, properties and extensions of given [classes].
 */
internal class SymbolsProvider(val context: Context, val classes: List<IrClassSymbol>) {

    private val symbols = context.ir.symbols

    fun getMethods(name: String,
                   filter: (SimpleFunctionDescriptor) -> Boolean = { true }): Set<IrFunctionSymbol> =
            classes.flatMap { klass ->
                klass.descriptor.unsubstitutedMemberScope
                        .getContributedFunctions(Name.identifier(name), NoLookupLocation.FROM_BACKEND)
                        .filter(filter)
                        .map { symbols.symbolTable.referenceFunction(it) }
            }.toSet()

    fun getExtensionFunctions(name: String, pkg: FqName,
                              filter: (SimpleFunctionDescriptor) -> Boolean = { true }): Set<IrFunctionSymbol> =
            classes.flatMap { klass ->
                context.builtIns.builtInsModule.getPackage(pkg).memberScope
                        .getContributedFunctions(Name.identifier(name), NoLookupLocation.FROM_BACKEND)
                        .filter(filter)
                        .map { symbols.symbolTable.referenceFunction(it) }
            }.toSet()

    // TODO: replace with property
    fun getExtensionPropertyGetters(name: String, pkg: FqName,
                                    filter: (PropertyDescriptor) -> Boolean = { true }): Set<IrFunctionSymbol> =
            classes.flatMap { klass ->
                context.builtIns.builtInsModule.getPackage(pkg).memberScope
                        .getContributedVariables(Name.identifier(name), NoLookupLocation.FROM_BACKEND)
                        .filter(filter)
                        .map { symbols.symbolTable.referenceFunction(it.getter!!) }
            }.toSet()
}

private class ArraySymbolsProvider(val context: Context) {
    val symbolsProvider = SymbolsProvider(context, listOf(context.ir.symbols.array))

    val indices by lazy { symbolsProvider.getExtensionPropertyGetters("indices", FqName("kotlin.collections")) }
}

private class ProgressionSymbolsProvider(val context: Context) {

    private val symbols = context.ir.symbols

    val symbolsProvider = SymbolsProvider(context, symbols.integerClasses + symbols.char)

    val rangeTo by lazy { symbolsProvider.getMethods("rangeTo") }

    val until by lazy { symbolsProvider.getExtensionFunctions("until", FqName("kotlin.ranges")) }

    val downTo by lazy { symbolsProvider.getExtensionFunctions("downTo", FqName("kotlin.ranges")) }

    val step by lazy {
        symbolsProvider.getExtensionFunctions("step", FqName("kotlin.ranges")) {
            it.extensionReceiverParameter?.type in symbols.progressionClassesTypes &&
                    it.valueParameters.size == 1 && (KotlinBuiltIns.isLong(it.valueParameters[0].type)
                    || KotlinBuiltIns.isInt(it.valueParameters[0].type))
        }
    }

}

private fun IrConst<*>.isOne() =
        when (kind) {
            IrConstKind.Long -> value as Long == 1L
            IrConstKind.Int -> value as Int == 1
            else -> false
        }

internal class ProgressionInfoBuilder(val context: Context) : IrElementVisitor<ProgressionInfo?, Nothing?> {

    private val symbols = context.ir.symbols

    private val progressionSymbolsProvider = ProgressionSymbolsProvider(context)
    private val arraySymbolsProvider = ArraySymbolsProvider(context)

    private val intProgression = ProgressionType(context.builtIns.intType, Name.identifier("toInt"))
    private val longProgression = ProgressionType(context.builtIns.longType, Name.identifier("toLong"))
    private val charProgression = ProgressionType(context.builtIns.charType, Name.identifier("toChar"))


    private fun buildIndices(expression: IrCall, progressionType: ProgressionType): ProgressionInfo {
        val int0 = IrConstImpl.int(expression.startOffset, expression.endOffset, symbols.int.typeWithoutArguments, 0)
        val int1 = IrConstImpl.int(expression.startOffset, expression.endOffset, symbols.int.typeWithoutArguments, 1)

        val bound = with(context.createIrBuilder(expression.symbol, expression.startOffset, expression.endOffset)) {
            val size = irCall(symbols.array.getPropertyGetter("size")!!).apply {
                dispatchReceiver = expression.extensionReceiver
            }
            // TODO: What if size is not returning Int?
            val minusOperator = symbols.getBinaryOperator(
                    OperatorNameConventions.MINUS,
                    context.builtIns.intType,
                    context.builtIns.intType
            )
            irCallOp(minusOperator.owner, size, int1)
        }
        return ProgressionInfo(progressionType, int0, bound)
    }

    private fun buildRangeTo(expression: IrCall, progressionType: ProgressionType) =
            ProgressionInfo(progressionType,
                    expression.dispatchReceiver!!,
                    expression.getValueArgument(0)!!)

    private fun buildUntil(expression: IrCall, progressionType: ProgressionType) =
            ProgressionInfo(progressionType,
                    expression.extensionReceiver!!,
                    expression.getValueArgument(0)!!,
                    closed = false)

    private fun buildDownTo(expression: IrCall, progressionType: ProgressionType) =
            ProgressionInfo(progressionType,
                    expression.extensionReceiver!!,
                    expression.getValueArgument(0)!!,
                    increasing = false)

    private fun buildStep(expression: IrCall, progressionType: ProgressionType) =
            expression.extensionReceiver!!.accept(this, null)?.let {
                val newStep = expression.getValueArgument(0)!!
                val (newStepCheck, needBoundCalculation) = irCheckProgressionStep(progressionType, newStep)
                val step = when {
                    it.step == null -> newStepCheck
                    // There were step calls before. Just add our check in the container or create a new one.
                    it.step is IrStatementContainer -> {
                        it.step.statements.add(newStepCheck)
                        it.step
                    }
                    else -> IrCompositeImpl(expression.startOffset, expression.endOffset, newStep.type).apply {
                        statements.add(it.step)
                        statements.add(newStepCheck)
                    }
                }
                ProgressionInfo(progressionType, it.first, it.bound, step, it.increasing, needBoundCalculation, it.closed)
            }

    private fun irCheckProgressionStep(progressionType: ProgressionType,
                                       step: IrExpression): Pair<IrExpression, Boolean> {
        if (step is IrConst<*> &&
                ((step.kind == IrConstKind.Long && step.value as Long > 0) ||
                        (step.kind == IrConstKind.Int && step.value as Int > 0))) {
            return step to !step.isOne()
        }
        // The frontend checks if the step has a right type (Long for LongProgression and Int for {Int/Char}Progression)
        // so there is no need to cast it.
        assert(stepHasRightType(step, progressionType))

        val symbol = symbols.checkProgressionStep[step.type.toKotlinType().makeNotNullable()]
                ?: throw IllegalArgumentException("Unknown progression element type: ${step.type}")
        return IrCallImpl(step.startOffset, step.endOffset, symbol.owner.returnType, symbol).apply {
            putValueArgument(0, step)
        } to true
    }

    // Used only by the assert.
    private fun stepHasRightType(step: IrExpression, progressionType: ProgressionType) =
            ((progressionType.isCharProgression() || progressionType.isIntProgression()) &&
                    KotlinBuiltIns.isInt(step.type.toKotlinType().makeNotNullable())) ||
                    (progressionType.isLongProgression() &&
                            KotlinBuiltIns.isLong(step.type.toKotlinType().makeNotNullable()))


    private fun IrType.getProgressionType(): ProgressionType? = when {
        isSubtypeOf(symbols.charProgression.descriptor.defaultType) -> charProgression
        isSubtypeOf(symbols.intProgression.descriptor.defaultType) -> intProgression
        isSubtypeOf(symbols.longProgression.descriptor.defaultType) -> longProgression
        else -> null
    }

    override fun visitElement(element: IrElement, data: Nothing?): ProgressionInfo? = null

    override fun visitCall(expression: IrCall, data: Nothing?): ProgressionInfo? {
        val progressionType = expression.type.getProgressionType()
                ?: return null

        // TODO: Process constructors and other factory functions.
        return when (expression.symbol) {
            in progressionSymbolsProvider.rangeTo   -> buildRangeTo(expression, progressionType)
            in progressionSymbolsProvider.until     -> buildUntil(expression, progressionType)
            in progressionSymbolsProvider.downTo    -> buildDownTo(expression, progressionType)
            in progressionSymbolsProvider.step      -> buildStep(expression, progressionType)
            in arraySymbolsProvider.indices         -> buildIndices(expression, progressionType)
            else -> null
        }
    }
}