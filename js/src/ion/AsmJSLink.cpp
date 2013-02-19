/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "jsmath.h"
#include "jscntxt.h"

#include "jstypedarrayinlines.h"

#include "AsmJS.h"
#include "AsmJSModule.h"
#include "AsmJSSignalHandlers.h"

using namespace js;
using namespace mozilla;

extern Class AsmLinkedModuleClass;

static const unsigned ASM_LINKED_MODULE_MODULE_SLOT = 0;
static const unsigned ASM_LINKED_MODULE_GLOBAL_DATA_SLOT = 1;
static const unsigned ASM_LINKED_MODULE_HEAP_SLOT = 2;
static const unsigned ASM_LINKED_MODULE_NUM_RESERVED_SLOTS = 3;

static const AsmJSModule &
AsmLinkedModuleToModule(JSObject *obj)
{
    JS_ASSERT(obj->getClass() == &AsmLinkedModuleClass);
    JSObject *moduleObj = &obj->getReservedSlot(ASM_LINKED_MODULE_MODULE_SLOT).toObject();
    return AsmJSModuleObjectToModule(moduleObj);
}

static uint8_t *
AsmLinkedModuleToGlobalData(JSObject *obj)
{
    JS_ASSERT(obj->getClass() == &AsmLinkedModuleClass);
    return (uint8_t *)obj->getReservedSlot(ASM_LINKED_MODULE_GLOBAL_DATA_SLOT).toPrivate();
}

static uint8_t *
AsmLinkedModuleToHeapOrNull(JSObject *obj)
{
    JS_ASSERT(obj->getClass() == &AsmLinkedModuleClass);
    if (JSObject *bufObj = obj->getReservedSlot(ASM_LINKED_MODULE_HEAP_SLOT).toObjectOrNull()) {
        ArrayBufferObject &buf = bufObj->asArrayBuffer();
        JS_ASSERT(buf.isAsmJSArrayBuffer());
        return buf.dataPointer();
    }
    return NULL;
}

static void
AsmLinkedModuleObject_finalize(FreeOp *fop, RawObject obj)
{
    fop->free_(AsmLinkedModuleToGlobalData(obj));
}

static void
AsmLinkedModuleObject_trace(JSTracer *trc, JSRawObject obj)
{
    const AsmJSModule &module = AsmLinkedModuleToModule(obj);
    uint8_t *globalData = AsmLinkedModuleToGlobalData(obj);
    for (unsigned i = 0; i < module.numExits(); i++) {
        AsmJSModule::ExitDatum &e = module.exitIndexToGlobalDatum(globalData, i);
        if (e.fun)
            MarkObject(trc, &e.fun, "AsmFFIGlobalDatum.fun");
    }
}

Class AsmLinkedModuleClass = {
    "AsmLinkedModuleClass",
    JSCLASS_IS_ANONYMOUS | JSCLASS_HAS_RESERVED_SLOTS(ASM_LINKED_MODULE_NUM_RESERVED_SLOTS),
    JS_PropertyStub,         /* addProperty */
    JS_PropertyStub,         /* delProperty */
    JS_PropertyStub,         /* getProperty */
    JS_StrictPropertyStub,   /* setProperty */
    JS_EnumerateStub,
    JS_ResolveStub,
    NULL,                    /* convert     */
    AsmLinkedModuleObject_finalize,
    NULL,                    /* checkAccess */
    NULL,                    /* call        */
    NULL,                    /* hasInstance */
    NULL,                    /* construct   */
    AsmLinkedModuleObject_trace
};

static JSObject *
NewAsmLinkedModuleObject(JSContext *cx, HandleObject module, ScopedJSDeletePtr<uint8_t> &globalData,
                        Handle<ArrayBufferObject*> heap)
{
    JSObject *obj = NewObjectWithGivenProto(cx, &AsmLinkedModuleClass, NULL, NULL);
    if (!obj)
        return NULL;

    obj->setReservedSlot(ASM_LINKED_MODULE_MODULE_SLOT, ObjectValue(*module));
    obj->setReservedSlot(ASM_LINKED_MODULE_GLOBAL_DATA_SLOT, PrivateValue(globalData.forget()));
    obj->setReservedSlot(ASM_LINKED_MODULE_HEAP_SLOT, ObjectOrNullValue(heap));
    return obj;
}

static bool
LinkFail(JSContext *cx, const char *str)
{
    JS_ReportErrorFlagsAndNumber(cx, JSREPORT_WARNING, js_GetErrorMessage,
                                 NULL, JSMSG_USE_ASM_LINK_FAIL, str);
    return false;
}

static bool
ValidateGlobalVariable(JSContext *cx, const AsmJSModule &module, AsmJSModule::Global global,
                       HandleValue importVal, uint8_t *globalData)
{
    JS_ASSERT(global.which() == AsmJSModule::Global::Variable);

    void *datum = module.globalVarIndexToGlobalDatum(globalData, global.varIndex());

    switch (global.varInitKind()) {
      case AsmJSModule::Global::InitConstant: {
        const Value &v = global.varInitConstant();
        if (v.isInt32())
            *(int32_t *)datum = v.toInt32();
        else
            *(double *)datum = v.toDouble();
        break;
      }
      case AsmJSModule::Global::InitImport: {
        RootedPropertyName field(cx, global.varImportField());
        RootedValue v(cx);
        if (!GetProperty(cx, importVal, field, &v))
            return false;

        switch (global.varImportCoercion()) {
          case AsmJS_ToInt32:
            if (!ToInt32(cx, v, (int32_t *)datum))
                return false;
            break;
          case AsmJS_ToNumber:
            if (!ToNumber(cx, v, (double *)datum))
                return false;
            break;
        }
        break;
      }
    }

    return true;
}

static bool
ValidateFFI(JSContext *cx, AsmJSModule::Global global, HandleValue importVal,
            AutoObjectVector *ffis)
{
    RootedPropertyName field(cx, global.ffiField());
    RootedValue v(cx);
    if (!GetProperty(cx, importVal, field, &v))
        return false;

    if (!v.isObject() || !v.toObject().isFunction())
        return LinkFail(cx, "FFI imports must be functions");

    (*ffis)[global.ffiIndex()] = v.toObject().toFunction();
    return true;
}

static bool
ValidateArrayView(JSContext *cx, AsmJSModule::Global global, HandleValue globalVal,
                  HandleValue bufferVal)
{
    RootedPropertyName field(cx, global.viewName());
    RootedValue v(cx);
    if (!GetProperty(cx, globalVal, field, &v))
        return false;

    if (!IsTypedArrayConstructor(v, global.viewType()))
        return LinkFail(cx, "bad typed array constructor");

    size_t byteLength = bufferVal.toObject().asArrayBuffer().byteLength();
    if (byteLength % (1 << TypedArrayShift(global.viewType())) != 0)
        return LinkFail(cx, "ArrayBuffer length must be a multiple of view element size");

    return true;
}

static bool
ValidateMathBuiltin(JSContext *cx, AsmJSModule::Global global, HandleValue globalVal)
{
    RootedValue v(cx);
    if (!GetProperty(cx, globalVal, cx->names().Math, &v))
        return false;
    RootedPropertyName field(cx, global.mathName());
    if (!GetProperty(cx, v, field, &v))
        return false;

    Native native;
    switch (global.mathBuiltin()) {
      case AsmJSMathBuiltin_sin: native = math_sin; break;
      case AsmJSMathBuiltin_cos: native = math_cos; break;
      case AsmJSMathBuiltin_tan: native = math_tan; break;
      case AsmJSMathBuiltin_asin: native = math_asin; break;
      case AsmJSMathBuiltin_acos: native = math_acos; break;
      case AsmJSMathBuiltin_atan: native = math_atan; break;
      case AsmJSMathBuiltin_ceil: native = js_math_ceil; break;
      case AsmJSMathBuiltin_floor: native = js_math_floor; break;
      case AsmJSMathBuiltin_exp: native = math_exp; break;
      case AsmJSMathBuiltin_log: native = math_log; break;
      case AsmJSMathBuiltin_pow: native = js_math_pow; break;
      case AsmJSMathBuiltin_sqrt: native = js_math_sqrt; break;
      case AsmJSMathBuiltin_abs: native = js_math_abs; break;
      case AsmJSMathBuiltin_atan2: native = math_atan2; break;
      case AsmJSMathBuiltin_imul: native = math_imul; break;
    }

    if (!IsNativeFunction(v, native))
        return LinkFail(cx, "bad Math.* builtin");

    return true;
}

static bool
ValidateGlobalConstant(JSContext *cx, AsmJSModule::Global global, HandleValue globalVal)
{
    RootedPropertyName field(cx, global.constantName());
    RootedValue v(cx);
    if (!GetProperty(cx, globalVal, field, &v))
        return false;

    if (!v.isNumber())
        return LinkFail(cx, "global constant value needs to be a number");

    // NaN != NaN
    if (MOZ_DOUBLE_IS_NaN(global.constantValue())) {
        if (!MOZ_DOUBLE_IS_NaN(v.toNumber()))
            return LinkFail(cx, "global constant value needs to be NaN");
    } else {
        if (v.toNumber() != global.constantValue())
            return LinkFail(cx, "global constant value mismatch");
    }

    return true;
}

static bool
DynamicallyLinkModule(JSContext *cx, StackFrame *fp, HandleObject moduleObj,
                      MutableHandleObject obj)
{
    const AsmJSModule &module = AsmJSModuleObjectToModule(moduleObj);

    RootedValue globalVal(cx, UndefinedValue());
    if (fp->numActualArgs() > 0)
        globalVal = fp->unaliasedActual(0);

    RootedValue importVal(cx, UndefinedValue());
    if (fp->numActualArgs() > 1)
        importVal = fp->unaliasedActual(1);

    RootedValue bufferVal(cx, UndefinedValue());
    if (fp->numActualArgs() > 2)
        bufferVal = fp->unaliasedActual(2);

    Rooted<ArrayBufferObject*> heap(cx);
    if (module.hasArrayView()) {
        if (!IsTypedArrayBuffer(bufferVal))
            return LinkFail(cx, "bad ArrayBuffer argument");

        heap = &bufferVal.toObject().asArrayBuffer();

        if (!ArrayBufferObject::prepareForAsmJS(cx, heap))
            return LinkFail(cx, "Unable to prepare ArrayBuffer for asm.js use");
    }

    ScopedJSDeletePtr<uint8_t> globalDataGuard;
    if (module.byteLength() > 0) {
        globalDataGuard = cx->pod_calloc<uint8_t>(module.byteLength());
        if (!globalDataGuard)
            return NULL;
    }
    uint8_t *globalData = globalDataGuard.get();

    AutoObjectVector ffis(cx);
    if (!ffis.resize(module.numFFIs()))
        return false;

    for (unsigned i = 0; i < module.numGlobals(); i++) {
        AsmJSModule::Global global = module.global(i);
        switch (global.which()) {
          case AsmJSModule::Global::Variable:
            if (!ValidateGlobalVariable(cx, module, global, importVal, globalData))
                return false;
            break;
          case AsmJSModule::Global::FFI:
            if (!ValidateFFI(cx, global, importVal, &ffis))
                return false;
            break;
          case AsmJSModule::Global::ArrayView:
            if (!ValidateArrayView(cx, global, globalVal, bufferVal))
                return false;
            break;
          case AsmJSModule::Global::MathBuiltin:
            if (!ValidateMathBuiltin(cx, global, globalVal))
                return false;
            break;
          case AsmJSModule::Global::Constant:
            if (!ValidateGlobalConstant(cx, global, globalVal))
                return false;
            break;
        }
    }

    obj.set(NewAsmLinkedModuleObject(cx, moduleObj, globalDataGuard, heap));
    if (!obj)
        return false;

    // Initialize after linked module object creation so that GC-thing pointers
    // in globalData do not become stale.

    for (unsigned i = 0; i < module.numExits(); i++) {
        AsmJSModule::ExitDatum &datum = module.exitIndexToGlobalDatum(globalData, i);
        const AsmJSModule::Exit &exit = module.exit(i);
        datum.exit = exit.code();
        datum.fun = ffis[exit.ffiIndex()]->toFunction();
    }

    for (unsigned i = 0; i < module.numFuncPtrTableElems(); i++)
        module.funcPtrTableElemIndexToGlobalDatum(globalData, i) = module.funcPtrTableElem(i);

    return true;
}

AsmJSActivation::AsmJSActivation(JSContext *cx, const AsmJSModule &module, unsigned entryIndex,
                                 uint8_t *heap)
  : cx_(cx),
    module_(module),
    entryIndex_(entryIndex),
    heap_(heap),
    errorRejoinSP_(NULL),
    profiler_(NULL),
    resumePC_(NULL)
{
    if (cx->runtime->spsProfiler.enabled()) {
        profiler_ = &cx->runtime->spsProfiler;
        JSFunction *fun = module_.exportedFunction(entryIndex_).unclonedFunObj();
        profiler_->enter(cx_, fun->nonLazyScript(), fun);
    }

    prev_ = cx_->runtime->mainThread.asmJSActivationStack_;

    PerThreadData::AsmJSActivationStackLock lock(cx_->runtime->mainThread);
    cx_->runtime->mainThread.asmJSActivationStack_ = this;
}

AsmJSActivation::~AsmJSActivation()
{
    if (profiler_) {
        JSFunction *fun = module_.exportedFunction(entryIndex_).unclonedFunObj();
        profiler_->exit(cx_, fun->nonLazyScript(), fun);
    }

    JS_ASSERT(cx_->runtime->mainThread.asmJSActivationStack_ == this);

    PerThreadData::AsmJSActivationStackLock lock(cx_->runtime->mainThread);
    cx_->runtime->mainThread.asmJSActivationStack_ = prev_;
}

static const unsigned ASM_LINKED_MODULE_SLOT = 0;
static const unsigned ASM_EXPORT_INDEX_SLOT = 1;

static JSBool
CallAsmJS(JSContext *cx, unsigned argc, Value *vp)
{
    CallArgs callArgs = CallArgsFromVp(argc, vp);
    RootedFunction callee(cx, callArgs.callee().toFunction());

    // An asm.js function stores, in its extended slots:
    //  - a pointer to the linked module from which it was returned
    //  - its index in the ordered list of exported functions
    RootedObject linkedModule(cx, &callee->getExtendedSlot(ASM_LINKED_MODULE_SLOT).toObject());
    unsigned exportIndex = callee->getExtendedSlot(ASM_EXPORT_INDEX_SLOT).toInt32();

    // A linked module links a heap (ArrayBuffer) and globalData to a module
    const AsmJSModule &module = AsmLinkedModuleToModule(linkedModule);
    uint8_t *heap =             AsmLinkedModuleToHeapOrNull(linkedModule);
    uint8_t *globalData =       AsmLinkedModuleToGlobalData(linkedModule);

    // An exported function points to the code as well as the exported
    // function's signature, which implies the dynamic coercions performed on
    // the arguments.
    const AsmJSModule::ExportedFunction &func = module.exportedFunction(exportIndex);

    // The calling convention for an external call into asm.js is to pass an
    // array of 8-byte values where each value contains either a coerced int32
    // (in the low word) or double value, with the coercions specified by the
    // asm.js signature. The external entry point unpacks this array into the
    // system-ABI-specified registers and stack memory and then calls into the
    // internal entry point. The return value is stored in the first element of
    // the array (which, therefore, must have length >= 1).

    Vector<uint64_t, 8> coercedArgs(cx);
    if (!coercedArgs.resize(Max<size_t>(1, func.numArgs())))
        return false;

    RootedValue v(cx);
    for (unsigned i = 0; i < func.numArgs(); ++i) {
        v = i < callArgs.length() ? callArgs[i] : UndefinedValue();
        switch (func.argCoercion(i)) {
          case AsmJS_ToInt32:
            if (!ToInt32(cx, v, (int32_t*)&coercedArgs[i]))
                return false;
            break;
          case AsmJS_ToNumber:
            if (!ToNumber(cx, v, (double*)&coercedArgs[i]))
                return false;
            break;
        }
    }

    AsmJSActivation activation(cx, module, exportIndex, heap);

    if (!func.code()(heap, globalData, coercedArgs.begin()))
        return false;

    switch (func.returnType()) {
      case AsmJSModule::Return_Void:
        callArgs.rval().set(UndefinedValue());
        break;
      case AsmJSModule::Return_Int32:
        callArgs.rval().set(Int32Value(*(int32_t*)&coercedArgs[0]));
        break;
      case AsmJSModule::Return_Double:
        callArgs.rval().set(NumberValue(*(double*)&coercedArgs[0]));
        break;
    }

    return true;
}

static JSFunction *
NewExportedFunction(JSContext *cx, const AsmJSModule::ExportedFunction &func,
                    HandleObject linkedModule, unsigned exportIndex)
{
    RootedPropertyName name(cx, func.name());
    JSFunction *fun = NewFunction(cx, NullPtr(), CallAsmJS, func.numArgs(),
                                  JSFunction::NATIVE_FUN, cx->global(), name,
                                  JSFunction::ExtendedFinalizeKind);
    if (!fun)
        return NULL;

    fun->setExtendedSlot(ASM_LINKED_MODULE_SLOT, ObjectValue(*linkedModule));
    fun->setExtendedSlot(ASM_EXPORT_INDEX_SLOT, Int32Value(exportIndex));
    return fun;
}

bool
js::LinkAsmJS(JSContext *cx, StackFrame *fp, MutableHandleValue rval)
{
    RootedObject moduleObj(cx, fp->fun()->nonLazyScript()->asmJS);
    const AsmJSModule &module = AsmJSModuleObjectToModule(moduleObj);

    RootedObject linkedModule(cx);
    if (!DynamicallyLinkModule(cx, fp, moduleObj, &linkedModule))
        return !cx->isExceptionPending();

    // Uncomment this to validate asm.js tests against non-asm.js
    //return true;

    if (module.numExportedFunctions() == 1) {
        const AsmJSModule::ExportedFunction &func = module.exportedFunction(0);
        if (!func.maybeFieldName()) {
            RootedFunction fun(cx, NewExportedFunction(cx, func, linkedModule, 0));
            if (!fun)
                return false;

            rval.set(ObjectValue(*fun));
            return true;
        }
    }

    gc::AllocKind allocKind = gc::GetGCObjectKind(module.numExportedFunctions());
    RootedObject obj(cx, NewBuiltinClassInstance(cx, &ObjectClass, allocKind));
    if (!obj)
        return false;

    for (unsigned i = 0; i < module.numExportedFunctions(); i++) {
        const AsmJSModule::ExportedFunction &func = module.exportedFunction(i);

        RootedFunction fun(cx, NewExportedFunction(cx, func, linkedModule, i));
        if (!fun)
            return false;

        JS_ASSERT(func.maybeFieldName() != NULL);
        RootedId id(cx, NameToId(func.maybeFieldName()));
        RootedValue val(cx, ObjectValue(*fun));
        if (!DefineNativeProperty(cx, obj, id, val, NULL, NULL, JSPROP_ENUMERATE, 0, 0))
            return false;
    }

    rval.set(ObjectValue(*obj));
    return true;
}

