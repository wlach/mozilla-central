/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#if !defined(jsion_asmjs_h__)
#define jsion_asmjs_h__

namespace js {

namespace frontend { struct TokenStream; struct ParseNode; }

// Called after parsing a function 'fn' which contains the "use asm" directive.
// This function performs type-checking and code-generation. If type-checking
// succeeds, the generated module is assigned to script->asmJS. Otherwise, a
// warning will be emitted and script->asmJS is left null. The function returns
// 'false' only if a real JS semantic error (probably OOM) is pending.
extern bool
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
// (Implemented in AsmJSLink.cpp.)
extern bool
LinkAsmJS(JSContext *cx, StackFrame *fp, MutableHandleValue rval);

} // namespace js

#endif // jsion_asmjs_h__

