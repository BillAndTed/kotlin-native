#include <stdlib.h>
#include <assert.h>
#include <jni.h>
#include <ffi.h>

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeVoid
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeVoid(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_void;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeUInt8
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeUInt8(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_uint8;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeSInt8
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeSInt8(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_sint8;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeUInt16
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeUInt16(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_uint16;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeSInt16
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeSInt16(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_sint16;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeUInt32
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeUInt32(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_uint32;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeSInt32
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeSInt32(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_sint32;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeUInt64
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeUInt64(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_uint64;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeSInt64
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeSInt64(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_sint64;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypePointer
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypePointer(JNIEnv *env, jclass cls) {
    return (jlong) &ffi_type_pointer;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiTypeStruct0
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiTypeStruct0(JNIEnv *env, jclass cls, jlong elements) {
    ffi_type* res = malloc(sizeof(ffi_type));
    if (res != NULL) {
        res->size = 0;
        res->alignment = 0;
        res->elements = (ffi_type**) elements;
        res->type = FFI_TYPE_STRUCT;
    }
    return (jlong) res;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiCreateCif0
 * Signature: (IJJ)J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiCreateCif0(JNIEnv *env, jclass cls, jint nArgs, jlong rType, jlong argTypes) {
    ffi_cif* res = malloc(sizeof(ffi_cif));
    if (res != NULL) {
        ffi_status status = ffi_prep_cif(res, FFI_DEFAULT_ABI, nArgs, (ffi_type*)rType, (ffi_type**)argTypes);
        if (status != FFI_OK) {
            if (status == FFI_BAD_TYPEDEF) {
                return -(jlong)1;
            } else if (status == FFI_BAD_ABI) {
                return -(jlong)2;
            } else {
                return -(jlong)3;
            }
        }
    }
    return (jlong) res;
}

static JavaVM *vm = NULL;

// Returns the JNI env which can be used by the caller.
// If current thread is not attached to JVM, then it gets attached as daemon.
static JNIEnv* getCurrentEnv() {
    JNIEnv* env;
    assert(vm != NULL);
    jint res = (*vm)->GetEnv(vm, (void**)&env, JNI_VERSION_1_1);
    if (res != JNI_OK) {
        assert(res == JNI_EDETACHED);
        res = (*vm)->AttachCurrentThreadAsDaemon(vm, (void**)&env, NULL);
        assert(res == JNI_OK);
    }
    return env;
}

jint JNI_OnLoad(JavaVM *vm_, void *reserved) {
    vm = vm_;
    return JNI_VERSION_1_1;
}

// Checks for pending exception. If there is one, describes it and terminates the process.
static void checkException(JNIEnv *env) {
    if ((*env)->ExceptionCheck(env)) {
        (*env)->ExceptionDescribe(env);
        abort();
    }
}

static void ffi_fun(ffi_cif *cif, void *ret, void **args, void *user_data) {
    JNIEnv* env = getCurrentEnv();

    static jmethodID ffiFunImpl0 = NULL;
    static jclass cls = NULL;
    if (ffiFunImpl0 == NULL) {
        jclass clsLocal = (*env)->FindClass(env, "kotlin_native/interop/CallbacksKt");
        checkException(env);
        assert(clsLocal != NULL);

        cls = (jclass) (*env)->NewGlobalRef(env, clsLocal);
        checkException(env);
        assert(cls != NULL);

        ffiFunImpl0 = (*env)->GetStaticMethodID(env, cls, "ffiFunImpl0", "(JJJLjava/lang/Object;)V");
        checkException(env);
        assert(ffiFunImpl0 != NULL);
    }

    (*env)->CallStaticVoidMethod(env, cls, ffiFunImpl0, (jlong) cif, (jlong) ret, (jlong) args, (jobject) user_data);
    checkException(env);
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    ffiCreateClosure0
 * Signature: (JLjava/lang/Object;)J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_ffiCreateClosure0(JNIEnv *env, jclass cls, jlong ffiCif, jobject userData) {
    jobject userDataGlobalRef = (*env)->NewGlobalRef(env, userData);
    if (userDataGlobalRef == NULL) {
        return (jlong)0;
    }

    assert(sizeof(jobject) == sizeof(void*)); // TODO: check statically
    void* userDataPtr = (void*) userDataGlobalRef;

    void* res;
    ffi_closure *closure = ffi_closure_alloc(sizeof(ffi_closure), &res);
    if (closure == NULL) {
        return (jlong)0;
    }
    ffi_status status = ffi_prep_closure_loc(closure, (ffi_cif*)ffiCif, ffi_fun, userDataPtr, res);
    if (status != FFI_OK) {
        return -(jlong)1;
    }

    return (jlong) res;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    newGlobalRef
 * Signature: (Ljava/lang/Object;)J
 */
JNIEXPORT jlong JNICALL Java_kotlin_1native_interop_CallbacksKt_newGlobalRef(JNIEnv *env, jclass cls, jobject obj) {
    jobject res = (*env)->NewGlobalRef(env, obj);
    return (jlong) res;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    derefGlobalRef
 * Signature: (J)Ljava/lang/Object;
 */
JNIEXPORT jobject JNICALL Java_kotlin_1native_interop_CallbacksKt_derefGlobalRef(JNIEnv *env, jclass cls, jlong ref) {
    return (jobject) ref;
}

/*
 * Class:     kotlin_native_interop_CallbacksKt
 * Method:    deleteGlobalRef
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_kotlin_1native_interop_CallbacksKt_deleteGlobalRef(JNIEnv *env, jclass cls, jlong ref) {
    (*env)->DeleteGlobalRef(env, (jobject) ref);
}
