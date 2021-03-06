/*
 * Copyright 2010-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the LICENSE file.
 */

package org.jetbrains.kotlin.backend.konan.llvm

import org.jetbrains.kotlin.backend.konan.Context
import org.jetbrains.kotlin.backend.konan.descriptors.isExpectMember
import org.jetbrains.kotlin.descriptors.DeclarationDescriptor
import org.jetbrains.kotlin.descriptors.konan.CompiledKonanModuleOrigin
import org.jetbrains.kotlin.descriptors.konan.SyntheticModulesOrigin
import org.jetbrains.kotlin.descriptors.konan.konanModuleOrigin
import org.jetbrains.kotlin.resolve.descriptorUtil.module

internal interface LlvmImports {
    fun add(origin: CompiledKonanModuleOrigin)
}

internal val DeclarationDescriptor.llvmSymbolOrigin: CompiledKonanModuleOrigin
    get() {
        assert(!this.isExpectMember) { this }

        val module = this.module
        val moduleOrigin = module.konanModuleOrigin
        when (moduleOrigin) {
            is CompiledKonanModuleOrigin -> return moduleOrigin
            SyntheticModulesOrigin -> error("Declaration is synthetic and can't be an origin of LLVM symbol:\n${this}")
        }
    }

internal val Context.standardLlvmSymbolsOrigin: CompiledKonanModuleOrigin get() = this.stdlibModule.llvmSymbolOrigin
