/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#if !defined(jsion_asmjs_h__)
#define jsion_asmjs_h__

namespace js {

namespace frontend { struct ParseNode; struct TokenStream; }

// The JSRuntime maintains a stack of asm.js module activations. A "module"
// is the collection of functions from one (function() { "use asm"; ... }); an
// "activation" of module A is an initial call from outside A into a function
// in A, followed by a sequence of calls inside A, and terminated by a call
// that leaves A. Modules can call between each other; each cross-module call
// pushes a new activation. Activations serve three primary purposes:
//  - record the correct cx to pass to VM calls from asm.js;
//  - record enough information to pop all the frames of an activation if an
//    exception is thrown;
//  - (TODO) record the information necessary for asm.js signal handlers to
//    safely recover from (expected) out-of-bounds access, the operation
//    callback, stack overflow, division by zero, etc.
class AsmJSActivation
{
    AsmJSActivation *prev_;
    JSContext *cx_;
    void *errorRejoinPC_;
    void *errorRejoinSP_;

  public:
    AsmJSActivation(JSContext *cx);
    ~AsmJSActivation();

    // Read by JIT code:
    static unsigned offsetOfContext() { return offsetof(AsmJSActivation, cx_); }

    // Initialized by JIT code:
    static unsigned offsetOfErrorRejoinSP() { return offsetof(AsmJSActivation, errorRejoinSP_); }
};

// Called after parsing a function 'fn' which contains the "use asm" directive.
// This function performs type-checking and code-generation. If type-checking
// succeeds, the generated module is assigned to script->asmJS. Otherwise, a
// warning will be emitted and script->asmJS is left null. The function returns
// 'false' only if a real JS semantic error (probably OOM) is pending.
bool
CompileAsmJS(JSContext *cx, frontend::TokenStream &ts, frontend::ParseNode *fn, HandleScript s);

// Called by the JSOP_LINKASMJS opcode (which is emitted as the first opcode of
// a "use asm" function which successfully typechecks). This function performs
// the validation and dynamic linking of a module to it's given arguments. If
// validation succeeds, the module's return value (it's exports) are returned
// as an object in 'rval' and the interpreter should return 'rval' immediately.
// Otherwise, there was a validation error and execution should continue
// normally in the interpreter. The function returns 'false' only if a real JS
// semantic error (OOM or exception thrown when executing GetProperty on the
// arguments) is pending.
bool
LinkAsmJS(JSContext *cx, StackFrame *fp, MutableHandleValue rval);

} // namespace js

#endif // jsion_asmjs_h__

