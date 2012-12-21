/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "jsmath.h"

#include "frontend/ParseNode.h"
#include "ion/AsmJS.h"
#include "ion/CodeGenerator.h"
#include "ion/MIR.h"
#include "ion/MIRGraph.h"

#include "jstypedarrayinlines.h"

#include "frontend/ParseNode-inl.h"

// (TEMPORARY) Set to 'false' to pretend we have signal handlers setup to
// protect us from out-of-bounds access and we are using DataView so there is
// no masking necessary before loading [heap+index].
static const bool SAFE = true;

using namespace js;
using namespace js::ion;
using namespace js::frontend;
using namespace mozilla;

typedef ScopedReleasePtr<JSC::ExecutablePool> ExecPoolPtr;
typedef Vector<PropertyName*,1> AsmLabelVector;
typedef Vector<MBasicBlock*,16> AsmCaseVector;
typedef Vector<MAsmPassStackArg*,8> MIRStackArgVector;

/*****************************************************************************/
// All asm.js events (success or failure) generate warnings to provide the
// developer with a tangible confirmation or a reason for failure.

static bool
AsmMessage(JSContext *cx, int code, const char *str = NULL)
{
    return JS_ReportErrorFlagsAndNumber(cx, JSREPORT_WARNING,
                                        js_GetErrorMessage,
                                        NULL, code, str);
}

/*****************************************************************************/
// ParseNode utilities

static inline ParseNode *
NextNode(ParseNode *pn)
{
    return pn->pn_next;
}

static inline ParseNode *
UnaryKid(ParseNode *pn)
{
    JS_ASSERT(pn->isArity(PN_UNARY));
    return pn->pn_kid;
}

static inline ParseNode *
BinaryRight(ParseNode *pn)
{
    JS_ASSERT(pn->isArity(PN_BINARY));
    return pn->pn_right;
}

static inline ParseNode *
BinaryLeft(ParseNode *pn)
{
    JS_ASSERT(pn->isArity(PN_BINARY));
    return pn->pn_left;
}

static inline ParseNode *
TernaryKid1(ParseNode *pn)
{
    JS_ASSERT(pn->isArity(PN_TERNARY));
    return pn->pn_kid1;
}

static inline ParseNode *
TernaryKid2(ParseNode *pn)
{
    JS_ASSERT(pn->isArity(PN_TERNARY));
    return pn->pn_kid2;
}

static inline ParseNode *
TernaryKid3(ParseNode *pn)
{
    JS_ASSERT(pn->isArity(PN_TERNARY));
    return pn->pn_kid3;
}

static inline ParseNode *
ListHead(ParseNode *pn)
{
    JS_ASSERT(pn->isArity(PN_LIST));
    return pn->pn_head;
}

static inline unsigned
ListLength(ParseNode *pn)
{
    JS_ASSERT(pn->isArity(PN_LIST));
    return pn->pn_count;
}

static inline ParseNode *
CallCallee(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_CALL));
    return ListHead(pn);
}

static inline unsigned
CallArgListLength(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_CALL));
    JS_ASSERT(ListLength(pn) >= 1);
    return ListLength(pn) - 1;
}

static inline ParseNode *
CallArgList(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_CALL));
    return NextNode(ListHead(pn));
}

static inline ParseNode *
VarListHead(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_VAR));
    return ListHead(pn);
}

static inline ParseNode *
CaseExpr(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_CASE) || pn->isKind(PNK_DEFAULT));
    return BinaryLeft(pn);
}

static inline ParseNode *
CaseBody(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_CASE) || pn->isKind(PNK_DEFAULT));
    return BinaryRight(pn);
}

static inline JSAtom *
StringAtom(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_STRING));
    return pn->pn_atom;
}

static inline ParseNode *
StatementExpressionExpr(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_SEMI));
    return UnaryKid(pn);
}

static inline PropertyName *
LoopControlMaybeLabel(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_BREAK) || pn->isKind(PNK_CONTINUE));
    JS_ASSERT(pn->isArity(PN_NULLARY));
    return pn->as<LoopControlStatement>().label();
}

static inline PropertyName *
LabeledStatementLabel(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_COLON));
    return pn->pn_atom->asPropertyName();
}

static inline ParseNode *
LabeledStatementStatement(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_COLON));
    return pn->expr();
}

static double
NumberNodeValue(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_NUMBER));
    return pn->pn_dval;
}

static bool
NumberNodeHasFrac(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_NUMBER));
    return pn->pn_u.number.decimalPoint == HasDecimal;
}

static ParseNode *
DotBase(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_DOT));
    JS_ASSERT(pn->isArity(PN_NAME));
    return pn->expr();
}

static PropertyName *
DotMember(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_DOT));
    JS_ASSERT(pn->isArity(PN_NAME));
    return pn->pn_atom->asPropertyName();
}

static ParseNode *
ElemBase(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_ELEM));
    return BinaryLeft(pn);
}

static ParseNode *
ElemIndex(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_ELEM));
    return BinaryRight(pn);
}

static inline JSFunction *
FunctionObject(ParseNode *fn)
{
    JS_ASSERT(fn->isKind(PNK_FUNCTION));
    JS_ASSERT(fn->isArity(PN_FUNC));
    return fn->pn_funbox->function();
}

static inline PropertyName *
FunctionName(ParseNode *fn)
{
    if (JSAtom *atom = FunctionObject(fn)->atom())
        return atom->asPropertyName();
    return NULL;
}

static inline ParseNode *
FunctionArgsList(ParseNode *fn, unsigned *numFormals)
{
    JS_ASSERT(fn->isKind(PNK_FUNCTION));
    ParseNode *argsBody = fn->pn_body;
    JS_ASSERT(argsBody->isKind(PNK_ARGSBODY));
    *numFormals = argsBody->pn_count - 1;
    return ListHead(argsBody);
}

static inline ParseNode *
FunctionStatementList(ParseNode *fn)
{
    JS_ASSERT(fn->isKind(PNK_FUNCTION));
    ParseNode *argsBody = fn->pn_body;
    JS_ASSERT(argsBody->isKind(PNK_ARGSBODY));
    ParseNode *body = argsBody->last();
    JS_ASSERT(body->isKind(PNK_STATEMENTLIST));
    return body;
}

static inline ParseNode *
FunctionLastStatementOrNull(ParseNode *fn)
{
    ParseNode *list = FunctionStatementList(fn);
    return list->pn_count == 0 ? NULL : list->last();
}

static inline bool
IsNormalObjectField(JSContext *cx, ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_COLON));
    return pn->getOp() == JSOP_INITPROP &&
           BinaryLeft(pn)->isKind(PNK_NAME) &&
           BinaryLeft(pn)->name() != cx->names().proto;
}

static inline PropertyName *
ObjectNormalFieldName(JSContext *cx, ParseNode *pn)
{
    JS_ASSERT(IsNormalObjectField(cx, pn));
    return BinaryLeft(pn)->name();
}

static inline ParseNode *
ObjectFieldInitializer(ParseNode *pn)
{
    JS_ASSERT(pn->isKind(PNK_COLON));
    return BinaryRight(pn);
}

static inline bool
IsUseOfName(ParseNode *pn, PropertyName *name)
{
    return pn->isKind(PNK_NAME) && pn->name() == name;
}

static inline ParseNode *
SkipEmptyStatements(ParseNode *pn)
{
    while (pn && pn->isKind(PNK_SEMI) && !UnaryKid(pn))
        pn = pn->pn_next;
    return pn;
}

static inline ParseNode *
NextNonEmptyStatement(ParseNode *pn)
{
    return SkipEmptyStatements(pn->pn_next);
}

/*****************************************************************************/
// asm.js type system type values

// Respresents the type of a general asm.js expression.
class AsmType
{
  public:
    enum Which {
        Double,
        Doublish,
        Fixnum,
        Int,
        Signed,
        Unsigned,
        Intish,
        Void
    };

  private:
    Which which_;

  public:
    AsmType() : which_(Which(-1)) {}
    AsmType(Which w) : which_(w) {}

    bool operator==(AsmType rhs) const { return which_ == rhs.which_; }
    bool operator!=(AsmType rhs) const { return which_ != rhs.which_; }

    bool isSigned() const {
        return which_ == Signed || which_ == Fixnum;
    }

    bool isUnsigned() const {
        return which_ == Unsigned || which_ == Fixnum;
    }

    bool isInt() const {
        return isSigned() || isUnsigned() || which_ == Int;
    }

    bool isIntish() const {
        return isInt() || which_ == Intish;
    }

    bool isDouble() const {
        return which_ == Double;
    }

    bool isDoublish() const {
        return isDouble() || which_ == Doublish;
    }

    bool isVoid() const {
        return which_ == Void;
    }

    bool isExtern() const {
        return isDouble() || isSigned() || isUnsigned();
    }

    MIRType toMIRType() const {
        switch (which_) {
          case Double:
          case Doublish:
            return MIRType_Double;
          case Fixnum:
          case Int:
          case Signed:
          case Unsigned:
          case Intish:
            return MIRType_Int32;
          case Void:
            return MIRType_None;
        }
        JS_NOT_REACHED("Invalid AsmType");
        return MIRType_None;
    }
};

// Represents the type of an explicit type coercion (+e, e|0) as required for
// arguments, return statements and global variables.
class AsmCoercionType
{
  public:
    enum Which {
        Signed = AsmType::Signed,
        Double = AsmType::Double
    };

  private:
    Which which_;

  public:
    AsmCoercionType() {}
    AsmCoercionType(Which w) : which_(w) {}
    Which which() const { return which_; }
};

// Represents the subset of AsmType that can be used as the return type of a
// function.
class AsmRetType
{
  public:
    enum Which {
        Void = AsmType::Void,
        Signed = AsmType::Signed,
        Double = AsmType::Double
    };

  private:
    Which which_;

  public:
    AsmRetType() {}
    AsmRetType(Which w) : which_(w) {}
    AsmRetType(AsmCoercionType t) {
        switch (t.which()) {
          case AsmCoercionType::Signed: which_ = Signed; break;
          case AsmCoercionType::Double: which_ = Double; break;
        }
    }
    Which which() const {
        return which_;
    }
    AsmType widen() const {
        return AsmType::Which(which_);
    }
    MIRType toMIRType() const {
        switch (which_) {
          case Void: return MIRType_None;
          case Signed: return MIRType_Int32;
          case Double: return MIRType_Double;
        }
        JS_NOT_REACHED("Unexpected return type");
        return MIRType_None;
    }
    bool operator==(AsmRetType rhs) const { return which_ == rhs.which_; }
    bool operator!=(AsmRetType rhs) const { return which_ != rhs.which_; }
};

// Implements <: (subtype) operator when the rhs is an AsmRetType
static inline bool
operator<=(AsmType lhs, AsmRetType rhs)
{
    switch (rhs.which()) {
      case AsmRetType::Signed: return lhs.isSigned();
      case AsmRetType::Double: return lhs == AsmType::Double;
      case AsmRetType::Void:   return lhs == AsmType::Void;
    }
    JS_NOT_REACHED("Unexpected rhs type");
    return false;
}

// Represents the subset of AsmType that can be used as a variable or
// argument's type. Note: AsmCoercionType and AsmVarType are kept separate to
// make very clear the signed/int distinction: a coercion may explicitly sign
// an *expression* but, when stored as a variable, this signedness information
// is explicitly thrown away by the asm.js type system. E.g., in
//
//   function f(i) {
//     i = i | 0;             (1)
//     if (...)
//         i = foo() >>> 0;
//     else
//         i = bar() | 0;
//     return i | 0;          (2)
//
// the AsmCoercionType of (1) is Signed (since | performs ToInt32) but, when
// translated to an AsmVarType, the result is a plain Int since, as shown, it
// is legal to assign both Signed and Unsigned (or some other Int) values to
// it. For (2), the AsmCoercionType is also Signed but, when translated to an
// AsmRetType, the result is Signed since callers (asm.js and non-asm.js) can
// rely on the return value being Signed.
class AsmVarType
{
  public:
    enum Which {
        Int = AsmType::Int,
        Double = AsmType::Double
    };

  private:
    Which which_;

  public:
    AsmVarType() {}
    AsmVarType(Which w) : which_(w) {}
    AsmVarType(AsmCoercionType t) {
        switch (t.which()) {
          case AsmCoercionType::Signed: which_ = Int; break;
          case AsmCoercionType::Double: which_ = Double; break;
        }
    }
    Which which() const {
        return which_;
    }
    AsmType widen() const {
        return AsmType::Which(which_);
    }
    MIRType toMIRType() const {
        return which_ == Int ? MIRType_Int32 : MIRType_Double;
    }
    static AsmVarType FromMIRType(MIRType type) {
        JS_ASSERT(type == MIRType_Int32 || type == MIRType_Double);
        return type == MIRType_Int32 ? Int : Double;
    }
    bool operator==(AsmVarType rhs) const { return which_ == rhs.which_; }
    bool operator!=(AsmVarType rhs) const { return which_ != rhs.which_; }
};

// Implements <: (subtype) operator when the rhs is an AsmVarType
static inline bool
operator<=(AsmType lhs, AsmVarType rhs)
{
    switch (rhs.which()) {
      case AsmVarType::Int:    return lhs.isInt();
      case AsmVarType::Double: return lhs.isDouble();
    }
    JS_NOT_REACHED("Unexpected rhs type");
    return false;
}

// Passed from parent expressions to child expressions to indicate if and how
// the child expression's result will be coerced. While most type checking
// occurs bottom-up (with child expressions returning the type of the result
// and parents checking these types), FFI calls naturally want to know the
// parent's context to determine the appropriate result type. If a parent
// passes NoCoercion to an FFI all, then the FFI's return type will be "Void"
// which will cause a type error if the result is used.
//
// The other application of AsmUse is to support the asm.js type rule which
// allows (a-b+c-d+e)|0 without intermediate conversions. The type system has
// only binary +/- nodes so we simulate the n-ary expression by having the
// outer parent +/- expression pass in AsmUse::AddOrSub so that the inner
// expression knows to return type Int instead of Intish.
class AsmUse
{
  public:
    enum Which {
        NoCoercion,
        ToInt32,
        ToNumber,
        AddOrSub
    };

  private:
    Which which_;
    unsigned *pcount_;

  public:
    AsmUse()
      : which_(Which(-1)), pcount_(NULL) {}
    AsmUse(Which w)
      : which_(w), pcount_(NULL) { JS_ASSERT(w != AddOrSub); }
    AsmUse(unsigned *pcount)
      : which_(AddOrSub), pcount_(pcount) {}
    Which which() const {
        return which_;
    }
    unsigned &addOrSubCount() const {
        JS_ASSERT(which_ == AddOrSub);
        return *pcount_;
    }
    AsmType toFFIReturnType() const {
        switch (which_) {
          case NoCoercion: return AsmType::Void;
          case ToInt32: return AsmType::Intish;
          case ToNumber: return AsmType::Doublish;
          case AddOrSub: return AsmType::Void;
        }
        JS_NOT_REACHED("unexpected use type");
        return AsmType::Void;
    }
    MIRType toMIRType() const {
        switch (which_) {
          case NoCoercion: return MIRType_None;
          case ToInt32: return MIRType_Int32;
          case ToNumber: return MIRType_Double;
          case AddOrSub: return MIRType_None;
        }
        JS_NOT_REACHED("unexpected use type");
        return MIRType_None;
    }
    static AsmUse FromReturnCoercion(AsmRetType retType) {
        switch (retType.which()) {
          case AsmRetType::Void: return NoCoercion;
          case AsmRetType::Signed: return ToInt32;
          case AsmRetType::Double: return ToNumber;
        }
        JS_NOT_REACHED("unexpected return type");
        return NoCoercion;
    }
    bool operator==(AsmUse rhs) const { return which_ == rhs.which_; }
    bool operator!=(AsmUse rhs) const { return which_ != rhs.which_; }
};

/*****************************************************************************/
// Numeric literal utilities

// Represents the type and value of an asm.js numeric literal.
//
// A literal is a double iff the literal contains an exponent or decimal point
// (even if the fractional part is 0). Otherwise, integers may be classified:
//  fixnum: [0, 2^31)
//  negative int: [-2^31, 0)
//  big unsigned: [2^31, 2^32)
//  out of range: otherwise
class AsmNumLit
{
  public:
    enum Which {
        Fixnum = AsmType::Fixnum,
        NegativeInt = AsmType::Signed,
        BigUnsigned = AsmType::Unsigned,
        Double = AsmType::Double,
        OutOfRangeInt = -1
    };

  private:
    Which which_;
    Value v_;

  public:
    AsmNumLit(Which w, Value v)
      : which_(w), v_(v)
    {}

    Which which() const {
        return which_;
    }

    int32_t toInt32() const {
        JS_ASSERT(which_ == Fixnum || which_ == NegativeInt || which_ == BigUnsigned);
        return v_.toInt32();
    }

    double toDouble() const {
        return v_.toDouble();
    }

    AsmType type() const {
        JS_ASSERT(which_ != OutOfRangeInt);
        return AsmType::Which(which_);
    }

    Value value() const {
        JS_ASSERT(which_ != OutOfRangeInt);
        return v_;
    }
};

// Note: '-' is never rolled into the number; numbers are always positive and
// negations must be applied manually.
static bool
IsNumericLiteral(ParseNode *pn)
{
    return pn->isKind(PNK_NUMBER) ||
           (pn->isKind(PNK_NEG) && UnaryKid(pn)->isKind(PNK_NUMBER));
}

static AsmNumLit
ExtractNumericLiteral(ParseNode *pn)
{
    JS_ASSERT(IsNumericLiteral(pn));
    ParseNode *numberNode;
    double d;
    if (pn->isKind(PNK_NEG)) {
        numberNode = UnaryKid(pn);
        d = -NumberNodeValue(numberNode);
    } else {
        numberNode = pn;
        d = NumberNodeValue(numberNode);
    }

    if (NumberNodeHasFrac(numberNode))
        return AsmNumLit(AsmNumLit::Double, DoubleValue(d));

    int64_t i64 = int64_t(d);
    if (d != double(i64))
        return AsmNumLit(AsmNumLit::OutOfRangeInt, UndefinedValue());

    if (i64 >= 0) {
        if (i64 <= INT32_MAX)
            return AsmNumLit(AsmNumLit::Fixnum, Int32Value(i64));
        if (i64 <= UINT32_MAX)
            return AsmNumLit(AsmNumLit::BigUnsigned, Int32Value(uint32_t(i64)));
        return AsmNumLit(AsmNumLit::OutOfRangeInt, UndefinedValue());
    }
    if (i64 >= INT32_MIN)
        return AsmNumLit(AsmNumLit::NegativeInt, Int32Value(i64));
    return AsmNumLit(AsmNumLit::OutOfRangeInt, UndefinedValue());
}

static inline bool
IsLiteralUint32(ParseNode *pn, uint32_t *u32)
{
    if (!IsNumericLiteral(pn))
        return false;

    AsmNumLit literal = ExtractNumericLiteral(pn);
    switch (literal.which()) {
      case AsmNumLit::Fixnum:
      case AsmNumLit::BigUnsigned:
        *u32 = uint32_t(literal.toInt32());
        return true;
      case AsmNumLit::NegativeInt:
      case AsmNumLit::Double:
      case AsmNumLit::OutOfRangeInt:
        return false;
    }

    JS_NOT_REACHED("Bad literal type");
}

static inline bool
IsBits32(ParseNode *pn, int32_t i)
{
    if (!IsNumericLiteral(pn))
        return false;

    AsmNumLit literal = ExtractNumericLiteral(pn);
    switch (literal.which()) {
      case AsmNumLit::Fixnum:
      case AsmNumLit::BigUnsigned:
      case AsmNumLit::NegativeInt:
        return literal.toInt32() == i;
      case AsmNumLit::Double:
      case AsmNumLit::OutOfRangeInt:
        return false;
    }

    JS_NOT_REACHED("Bad literal type");
}

/*****************************************************************************/
// Typed array utilities

static unsigned
TypedArrayShift(ArrayBufferView::ViewType viewType)
{
    switch (viewType) {
      case ArrayBufferView::TYPE_INT8:
      case ArrayBufferView::TYPE_UINT8:
        return 0;
      case ArrayBufferView::TYPE_INT16:
      case ArrayBufferView::TYPE_UINT16:
        return 1;
      case ArrayBufferView::TYPE_INT32:
      case ArrayBufferView::TYPE_UINT32:
      case ArrayBufferView::TYPE_FLOAT32:
        return 2;
      case ArrayBufferView::TYPE_FLOAT64:
        return 3;
      default:;
    }
    JS_NOT_REACHED("Unexpected array type");
    return 0;
}

static AsmType
TypedArrayLoadType(ArrayBufferView::ViewType viewType)
{
    switch (viewType) {
      case ArrayBufferView::TYPE_INT8:
      case ArrayBufferView::TYPE_INT16:
      case ArrayBufferView::TYPE_INT32:
      case ArrayBufferView::TYPE_UINT8:
      case ArrayBufferView::TYPE_UINT16:
      case ArrayBufferView::TYPE_UINT32:
        return AsmType::Intish;
      case ArrayBufferView::TYPE_FLOAT32:
      case ArrayBufferView::TYPE_FLOAT64:
        return AsmType::Doublish;
      default:;
    }
    JS_NOT_REACHED("Unexpected array type");
    return AsmType();
}

enum ArrayStoreEnum {
    ArrayStore_Intish,
    ArrayStore_Double
};

static ArrayStoreEnum
TypedArrayStoreType(ArrayBufferView::ViewType viewType)
{
    switch (viewType) {
      case ArrayBufferView::TYPE_INT8:
      case ArrayBufferView::TYPE_INT16:
      case ArrayBufferView::TYPE_INT32:
      case ArrayBufferView::TYPE_UINT8:
      case ArrayBufferView::TYPE_UINT16:
      case ArrayBufferView::TYPE_UINT32:
        return ArrayStore_Intish;
      case ArrayBufferView::TYPE_FLOAT32:
      case ArrayBufferView::TYPE_FLOAT64:
        return ArrayStore_Double;
      default:;
    }
    JS_NOT_REACHED("Unexpected array type");
    return ArrayStore_Double;
}

/*****************************************************************************/
// asm.js FFI calls
//
// asm.js allows calling out to non-asm.js via "FFI calls". The asm.js type
// system does not place any constraints on the FFI call. In particular:
//  - an FFI call's target is not known or speculated at module-compile time;
//  - a single external function can be called with different signatures.
//
// If performance didn't matter, all FFI calls could simply box their arguments
// and call js::Invoke. However, we'd like to be able to specialize FFI calls
// to be more efficient in several cases:
//
//  - for calls to JS functions which have been jitted, we'd like to call
//    directly into JIT code without going through C++.
//
//  - for calls to certain builtins, we'd like to be call directly into the C++
//    code for the builtin without going through the general call path.
//
// All of this requires dynamic specialization techniques which must happen
// after module compilation. To support this, at module-compilation time, each
// FFI call generates a call signature according to the system ABI, as if the
// callee was a C++ function taking/returning the same types as the caller was
// passing/expecting. The callee is loaded from a fixed offset in the global
// data array which allows the callee to change at runtime. Initially, the
// callee is stub which boxes its arguments and calls js::Invoke.
//
// To do this, we need to generate a callee stub for each pairing of FFI callee
// and signature. We call this pairing an "exit". For example, this code has
// two external functions and three exits:
//
//  function f(global, imports) {
//    "use asm";
//    var foo = imports.foo;
//    var bar = imports.bar;
//    function g() {
//      foo(1);      // Exit #1: (int) -> void
//      foo(1.5);    // Exit #2: (double) -> void
//      bar(1)|0;    // Exit #3: (int) -> int
//      bar(2)|0;    // Exit #3: (int) -> int
//    }
//
// The AsmModuleCompiler maintains a hash table (AsmExitMap) which allows
// a call site to add a new exit or reuse an existing one. The key is an
// AsmExitDescriptor (which holds the exit pairing) and the value is an
// AsmExitIndex (typed wrapper for a simple index into the dense array of
// AsmExit's). An AsmExit receives the compiled default exit stub (which boxes
// arguments and calls js::Invoke) and the array of AsmExit's lives in the
// AsmLinkData (since it must survive compilation so that it may be used to
// initialize the global array mentioned above).

// Typed wrapper for an index into the dense array of FFI-callable external
// functions. This array is built at dynamic-link time by DynamicallyLinkModule
// and consists of the values loaded from the import object by ValidateFFI.
class AsmFFIIndex
{
    unsigned value_;
  public:
    AsmFFIIndex() : value_(-1) {}
    explicit AsmFFIIndex(unsigned value) : value_(value) {}
    unsigned value() const { return value_; }
};

// Typed wrapper for an index into the dense array of exits stored in
// AsmLinkData::exits_.
class AsmExitIndex
{
    unsigned value_;
  public:
    AsmExitIndex() : value_(-1) {}
    explicit AsmExitIndex(unsigned value) : value_(value) {}
    unsigned value() const { return value_; }
};

// See "asm.js FFI calls" comment.
class AsmExitDescriptor
{
    PropertyName *name_;
    MIRTypeVector argTypes_;
    AsmUse use_;

  public:
    AsmExitDescriptor(PropertyName *name, MoveRef<MIRTypeVector> argTypes, AsmUse use)
      : name_(name),
        argTypes_(argTypes),
        use_(use)
    {}
    AsmExitDescriptor(MoveRef<AsmExitDescriptor> rhs)
      : name_(rhs->name_),
        argTypes_(Move(rhs->argTypes_)),
        use_(rhs->use_)
    {}
    const MIRTypeVector &argTypes() const {
        return argTypes_;
    }
    AsmUse use() const {
        return use_;
    }

    typedef AsmExitDescriptor Lookup;
    static HashNumber hash(const AsmExitDescriptor &d) {
        HashNumber hn = HashGeneric(d.name_, d.use_.which());
        for (unsigned i = 0; i < d.argTypes_.length(); i++)
            hn = AddToHash(hn, d.argTypes_[i]);
        return hn;
    }
    static bool match(const AsmExitDescriptor &lhs, const AsmExitDescriptor &rhs) {
        if (lhs.name_ != rhs.name_ ||
            lhs.argTypes_.length() != rhs.argTypes_.length() ||
            lhs.use_ != rhs.use_)
        {
            return false;
        }
        for (unsigned i = 0; i < lhs.argTypes_.length(); i++) {
            if (lhs.argTypes_[i] != rhs.argTypes_[i])
                return false;
        }
        return true;
    }

  private:
    AsmExitDescriptor(const AsmExitDescriptor &) MOZ_DELETE;
    void operator=(const AsmExitDescriptor &) MOZ_DELETE;
};

// See "asm.js FFI calls" comment.
typedef HashMap<AsmExitDescriptor,
                AsmExitIndex,
                AsmExitDescriptor,
                ContextAllocPolicy> AsmExitMap;

// See "asm.js FFI calls" comment.
class AsmExit
{
    friend class AsmLinkData;
    AsmFFIIndex ffiIndex_;
    uint8_t *defaultExit_;
  public:
    AsmExit(AsmFFIIndex ffiIndex) : ffiIndex_(ffiIndex), defaultExit_(NULL) {}
    AsmFFIIndex ffiIndex() const { return ffiIndex_; }
    uint8_t *defaultExit() const { return defaultExit_; }
};

// An AsmExitGlobalDatum represents an exit in a linked module's globalData. The
// 'exit' field starts as AsmExit.defaultExit and may later be re-pointed to a
// more optimal call path (for builtins or calls to Ion code). The 'fun'
// remembers the actual JSFunction pulled off the import object and keeps it
// alive. (See "asm.js FFI calls" comment above.)
struct AsmExitGlobalDatum
{
    uint8_t *exit;
    HeapPtrFunction fun;
};
JS_STATIC_ASSERT(sizeof(AsmExitGlobalDatum) == 2 * sizeof(void*));
JS_STATIC_ASSERT(offsetof(AsmExitGlobalDatum, exit) == 0);
JS_STATIC_ASSERT(offsetof(AsmExitGlobalDatum, fun) == sizeof(void*));

/*****************************************************************************/

class AsmGlobalVarInit
{
  public:
    enum Which { Import, Constant };

  protected:
    Which which_;
    union {
        Value constant_;
        struct {
            PropertyName *field_;
            AsmVarType::Which type_;
        } import;
    } u;
    friend class AsmLinkData;

  public:
    Which which() const { return which_; }
    const Value &constant() const { JS_ASSERT(which_ == Constant); return u.constant_; }
    PropertyName *importField() const { JS_ASSERT(which_ == Import); return u.import.field_; }
    AsmVarType importType() const { JS_ASSERT(which_ == Import); return u.import.type_; }
};

struct AsmGlobalVarInitConstant : AsmGlobalVarInit
{
    AsmGlobalVarInitConstant(const Value &v) {
        which_ = Constant;
        u.constant_ = v;
    }
};

struct AsmGlobalVarImport : AsmGlobalVarInit
{
    AsmGlobalVarImport(PropertyName *field, AsmVarType type) {
        which_ = Import;
        u.import.field_ = field;
        u.import.type_ = type.which();
    }
};

enum AsmMathBuiltin
{
    AsmMathBuiltin_sin, AsmMathBuiltin_cos, AsmMathBuiltin_tan,
    AsmMathBuiltin_asin, AsmMathBuiltin_acos, AsmMathBuiltin_atan,
    AsmMathBuiltin_ceil, AsmMathBuiltin_floor, AsmMathBuiltin_exp,
    AsmMathBuiltin_log, AsmMathBuiltin_pow, AsmMathBuiltin_sqrt,
    AsmMathBuiltin_abs, AsmMathBuiltin_atan2, AsmMathBuiltin_imul
};

/*****************************************************************************/

// The 'link data' holds data necessary for DynamicallyLinkModule step. This
// data structure is initially owned by AsmModuleCompiler and moved into the
// AsmModule at the end of compilation (in AsmModule::New). Thus, unlike the
// other compiler data structures, AsmLinkData must be GC-safe.
class AsmLinkData
{
  public:
    struct Export {
        PropertyName *field;
        PropertyName *functionName;
        Export(PropertyName *field, PropertyName *fun) : field(field), functionName(fun) {}
    };
    typedef Vector<Export, 0, SystemAllocPolicy> ExportVector;

    class Global {
      public:
        enum Which { Variable, FFI, ArrayView, MathBuiltin, Constant };

      private:
        Which which_;
        union {
            struct {
                AsmGlobalVarInit init_;
                uint32_t index_;
            } var;
            struct {
                PropertyName *field_;
                uint32_t index_;
            } ffi;
            struct {
                PropertyName *name_;
                ArrayBufferView::ViewType type_;
            } view;
            struct {
                PropertyName *name_;
                AsmMathBuiltin builtin_;
            } math;
            struct {
                PropertyName *name_;
                double value_;
            } constant;
        } u;

        friend class AsmLinkData;
        Global(Which which) : which_(which) {}

      public:
        Which which() const {
            return which_;
        }
        AsmGlobalVarInit varInit() const {
            JS_ASSERT(which_ == Variable);
            return u.var.init_;
        }
        uint32_t varIndex() const {
            JS_ASSERT(which_ == Variable);
            return u.var.index_;
        }
        PropertyName *ffiField() const {
            JS_ASSERT(which_ == FFI);
            return u.ffi.field_;
        }
        uint32_t ffiIndex() const {
            JS_ASSERT(which_ == FFI);
            return u.ffi.index_;
        }
        PropertyName *viewName() const {
            JS_ASSERT(which_ == ArrayView);
            return u.view.name_;
        }
        ArrayBufferView::ViewType viewType() const {
            JS_ASSERT(which_ == ArrayView);
            return u.view.type_;
        }
        PropertyName *mathName() const {
            JS_ASSERT(which_ == MathBuiltin);
            return u.math.name_;
        }
        AsmMathBuiltin mathBuiltin() const {
            JS_ASSERT(which_ == MathBuiltin);
            return u.math.builtin_;
        }
        PropertyName *constantName() const {
            JS_ASSERT(which_ == Constant);
            return u.constant.name_;
        }
        double constantValue() const {
            JS_ASSERT(which_ == Constant);
            return u.constant.value_;
        }
    };

    typedef Vector<uint8_t*, 0, SystemAllocPolicy> FuncPtrTableElemVector;

  private:
    typedef Vector<Global, 0, SystemAllocPolicy> GlobalVector;
    typedef Vector<AsmExit, 0, SystemAllocPolicy> ExitVector;

    GlobalVector           globals_;
    ExitVector             exits_;
    ExportVector           exportObject_;
    FuncPtrTableElemVector funcPtrTableElems_;
    PropertyName *         exportedFunction_;
    uint32_t               numGlobalVars_;
    uint32_t               numFFIs_;
    uint32_t               numFuncPtrTableElems_;
    uint32_t               exactHeapSize_;
    uint32_t               maxConstantPointer_;
    bool                   usesArrayBuffer_;
    ExecPoolPtr            defaultExitPool_;

  public:
    AsmLinkData()
      : exportedFunction_(NULL),
        numGlobalVars_(0),
        numFFIs_(0),
        numFuncPtrTableElems_(0),
        exactHeapSize_(0),
        maxConstantPointer_(0),
        usesArrayBuffer_(false)
    {}

    void operator=(MoveRef<AsmLinkData> rhs) {
        globals_ = Move(rhs->globals_);
        exits_ = Move(rhs->exits_);
        exportObject_ = Move(rhs->exportObject_);
        funcPtrTableElems_ = Move(rhs->funcPtrTableElems_);
        exportedFunction_ = rhs->exportedFunction_;
        numGlobalVars_ = rhs->numGlobalVars_;
        numFFIs_ = rhs->numFFIs_;
        numFuncPtrTableElems_ = rhs->numFuncPtrTableElems_;
        exactHeapSize_ = rhs->exactHeapSize_;
        maxConstantPointer_ = rhs->maxConstantPointer_;
        usesArrayBuffer_ = rhs->usesArrayBuffer_;
        defaultExitPool_ = rhs->defaultExitPool_.forget();
    }

    void trace(JSTracer *trc) {
        // TODO: write barrier all these for GGC
        for (unsigned i = 0; i < globals_.length(); i++) {
            switch (globals_[i].which()) {
              case Global::Variable:
                switch (globals_[i].u.var.init_.which()) {
                  case AsmGlobalVarInit::Import:
                    MarkStringUnbarriered(trc, &globals_[i].u.var.init_.u.import.field_, "asm.js global");
                    break;
                  case AsmGlobalVarInit::Constant:
                    break;
                }
                break;
              case Global::FFI:
                MarkStringUnbarriered(trc, &globals_[i].u.ffi.field_, "asm.js global");
                break;
              case Global::ArrayView:
                MarkStringUnbarriered(trc, &globals_[i].u.view.name_, "asm.js global");
                break;
              case Global::MathBuiltin:
                MarkStringUnbarriered(trc, &globals_[i].u.math.name_, "asm.js global");
                break;
              case Global::Constant:
                MarkStringUnbarriered(trc, &globals_[i].u.constant.name_, "asm.js global");
                break;
            }
        }
        for (unsigned i = 0; i < exportObject_.length(); i++) {
            MarkStringUnbarriered(trc, &exportObject_[i].field, "asm export object field");
            MarkStringUnbarriered(trc, &exportObject_[i].functionName, "asm export object function");
        }
        if (exportedFunction_)
            MarkStringUnbarriered(trc, &exportedFunction_, "asm exported function");
    }

    bool addGlobalVar(AsmGlobalVarInit init, uint32_t *index) {
        if (numGlobalVars_ == UINT32_MAX)
            return false;
        Global g(Global::Variable);
        g.u.var.init_ = init;
        g.u.var.index_ = *index = numGlobalVars_++;
        return globals_.append(g);
    }
    bool addFuncPtrTableElems(uint32_t numElems) {
        if (UINT32_MAX - numFuncPtrTableElems_ < numElems)
            return false;
        numFuncPtrTableElems_ += numElems;
        return true;
    }
    bool addFFI(PropertyName *field, uint32_t *index) {
        if (numFFIs_ == UINT32_MAX)
            return false;
        Global g(Global::FFI);
        g.u.ffi.field_ = field;
        g.u.ffi.index_ = *index = numFFIs_++;
        return globals_.append(g);
    }
    bool addArrayView(ArrayBufferView::ViewType vt, PropertyName *field) {
        usesArrayBuffer_ = true;
        Global g(Global::ArrayView);
        g.u.view.name_ = field;
        g.u.view.type_ = vt;
        return globals_.append(g);
    }
    bool addMathBuiltin(AsmMathBuiltin mathBuiltin, PropertyName *field) {
        Global g(Global::MathBuiltin);
        g.u.math.name_ = field;
        g.u.math.builtin_ = mathBuiltin;
        return globals_.append(g);
    }
    bool addGlobalConstant(double value, PropertyName *fieldName) {
        Global g(Global::Constant);
        g.u.constant.name_ = fieldName;
        g.u.constant.value_ = value;
        return globals_.append(g);
    }
    bool addExit(AsmExit exit, AsmExitIndex *index) {
        *index = AsmExitIndex(exits_.length());
        return exits_.append(exit);
    }
    bool hasExportedFunction() const {
        return !!exportedFunction_;
    }
    PropertyName *exportedFunction() const {
        JS_ASSERT(hasExportedFunction());
        return exportedFunction_;
    }
    void setExportedFunction(PropertyName *name) {
        JS_ASSERT(!hasExportedFunction());
        JS_ASSERT(exportObject_.empty());
        exportedFunction_ = name;
    }
    const ExportVector &exportObject() const {
        JS_ASSERT(!hasExportedFunction());
        return exportObject_;
    }
    bool addToExportObject(PropertyName *field, PropertyName *functionName) {
        JS_ASSERT(!hasExportedFunction());
        return exportObject_.append(Export(field, functionName));
    }
    bool usesArrayBuffer() const {
        return usesArrayBuffer_;
    }
    uint32_t exactHeapSize() const {
        return exactHeapSize_;
    }
    uint32_t maxConstantPointer() const {
        return maxConstantPointer_;
    }
    bool attemptUseLengthMask(uint32_t mask) {
        JS_ASSERT(usesArrayBuffer_);
        if (maxConstantPointer_ > mask)
            return false;
        if (exactHeapSize_)
            return mask == exactHeapSize_ - 1;
        if (!IsPowerOfTwo(mask + 1))
            return false;
        exactHeapSize_ = mask + 1;
        return true;
    }
    bool attemptUseConstantPointer(uint32_t pointer) {
        if (exactHeapSize_ && pointer >= exactHeapSize_)
            return false;
        maxConstantPointer_ = Max(maxConstantPointer_, pointer);
        return true;
    }
    void setDefaultExitPool(JSC::ExecutablePool *pool) {
        defaultExitPool_ = pool;
    }
    void setDefaultExit(AsmExitIndex i, uint8_t *defaultExit) {
        exits_[i.value()].defaultExit_ = defaultExit;
    }
    void initFuncPtrTableElems(MoveRef<FuncPtrTableElemVector> funcPtrTableElems) {
        funcPtrTableElems_ = funcPtrTableElems;
        JS_ASSERT(funcPtrTableElems_.length() == numFuncPtrTableElems_);
    }

    unsigned numFFIs() const {
        return numFFIs_;
    }
    unsigned numGlobals() const {
        return globals_.length();
    }
    Global global(unsigned i) const {
        return globals_[i];
    }
    unsigned numFuncPtrTableElems() const {
        return numFuncPtrTableElems_;
    }
    uint8_t *funcPtrTableElem(unsigned i) const {
        JS_ASSERT(funcPtrTableElems_.length() == numFuncPtrTableElems_);
        return funcPtrTableElems_[i];
    }
    unsigned numExits() const {
        return exits_.length();
    }
    const AsmExit &exit(unsigned i) const {
        return exits_[i];
    }

    // The order in the global segment is [globals, func-ptr table elements, exits].
    // Put the exit array at the end since it grows during the second pass of
    // module compilation and would otherwise break global/func-ptr offsets.
    uint32_t byteLength() const {
        return numGlobalVars_ * sizeof(uint64_t) +
               numFuncPtrTableElems_ * sizeof(void*) +
               exits_.length() * sizeof(AsmExit);
    }
    int32_t globalVarIndexToGlobalDataOffset(unsigned i) const {
        JS_ASSERT(i < numGlobalVars_);
        return i * sizeof(uint64_t);
    }
    void *globalVarIndexToGlobalDatum(uint8_t *globalData, unsigned i) const {
        return (void *)(globalData + globalVarIndexToGlobalDataOffset(i));
    }
    int32_t funcPtrTableElemIndexToGlobalDataOffset(unsigned i) const {
        return numGlobalVars_ * sizeof(uint64_t) +
               i * sizeof(void*);
    }
    uint8_t *&funcPtrTableElemIndexToGlobalDatum(uint8_t *globalData, unsigned i) const {
        return *(uint8_t **)(globalData + funcPtrTableElemIndexToGlobalDataOffset(i));
    }
    int32_t exitIndexToGlobalDataOffset(AsmExitIndex i) const {
        JS_ASSERT(i.value() < exits_.length());
        return numGlobalVars_ * sizeof(uint64_t) +
               numFuncPtrTableElems_ * sizeof(void*) +
               i.value() * sizeof(AsmExitGlobalDatum);
    }
    AsmExitGlobalDatum &exitIndexToGlobalDatum(uint8_t *globalData, AsmExitIndex i) const {
        return *(AsmExitGlobalDatum *)(globalData + exitIndexToGlobalDataOffset(i));
    }

  private:
    AsmLinkData(const AsmLinkData &) MOZ_DELETE;
    void operator=(const AsmLinkData &) MOZ_DELETE;
};

/*****************************************************************************/

// AsmModuleCompiler encapsulates the compilation of an entire asm.js module.
// Over the course of an AsmModuleCompiler object's lifetime, many
// AsmFunctionCompiler objects will be created and destroyed in sequence, one
// for each function in the module.
class AsmModuleCompiler
{
  public:
    class Func;

    struct Call
    {
        size_t offset;
        const Func *target;
        Call(size_t offset, const Func *target) : offset(offset), target(target) {}
    };

    typedef Vector<Call, 8, SystemAllocPolicy> CallVector;

    class Func
    {
        ParseNode *fn_;
        ParseNode *body_;
        MIRTypeVector argTypes_;
        AsmRetType returnType_;
        CallVector calls_;
        AsmCodePtr codePtr_;
        ExecPoolPtr pool_;
        bool isExported_;

        Func(const Func &) MOZ_DELETE;
        void operator=(const Func &) MOZ_DELETE;

      public:
        Func(ParseNode *fn, ParseNode *body, MoveRef<MIRTypeVector> types, AsmRetType returnType)
          : fn_(fn),
            body_(body),
            argTypes_(types),
            returnType_(returnType),
            isExported_(false)
        {}

        Func(MoveRef<Func> rhs)
          : fn_(rhs->fn_),
            body_(rhs->body_),
            argTypes_(Move(rhs->argTypes_)),
            returnType_(rhs->returnType_),
            calls_(Move(rhs->calls_)),
            codePtr_(rhs->codePtr_),
            pool_(rhs->pool_.forget()),
            isExported_(rhs->isExported_)
        {}

        ParseNode *fn() const { return fn_; }
        ParseNode *body() const { return body_; }

        unsigned numArgs() const { return argTypes_.length(); }
        AsmVarType argType(unsigned i) const { return AsmVarType::FromMIRType(argTypes_[i]); }
        const MIRTypeVector &argMIRTypes() const { return argTypes_; }

        AsmRetType returnType() const { return returnType_; }

        bool addCall(Call call) { return calls_.append(call); }
        unsigned numCalls() const { return calls_.length(); }
        Call call(unsigned i) const { return calls_[i]; }

        void setIsExported() { isExported_ = true; }
        bool isExported() const { return isExported_; }

        AsmCodePtr &codePtr() { return codePtr_; }
        AsmCodePtr codePtr() const { return codePtr_; }
        ExecPoolPtr &pool() { return pool_; }
    };

    class Global
    {
      public:
        enum Which { Variable, Function, FuncPtrTable, FFI, ArrayView, MathBuiltin, Constant };

      private:
        Which which_;
        union {
            struct {
                uint32_t index_;
                AsmVarType::Which type_;
            } var;
            uint32_t funcIndex_;
            uint32_t funcPtrTableIndex_;
            uint32_t ffiIndex_;
            ArrayBufferView::ViewType viewType_;
            AsmMathBuiltin mathBuiltin_;
            double constant_;
        } u;

        friend class AsmModuleCompiler;
        Global(Which which) : which_(which) {}

      public:
        Which which() const {
            return which_;
        }
        AsmVarType varType() const {
            JS_ASSERT(which_ == Variable);
            return AsmVarType(u.var.type_);
        }
        uint32_t varIndex() const {
            JS_ASSERT(which_ == Variable);
            return u.var.index_;
        }
        uint32_t funcIndex() const {
            JS_ASSERT(which_ == Function);
            return u.funcIndex_;
        }
        uint32_t funcPtrTableIndex() const {
            JS_ASSERT(which_ == FuncPtrTable);
            return u.funcPtrTableIndex_;
        }
        AsmFFIIndex ffiIndex() const {
            JS_ASSERT(which_ == FFI);
            return AsmFFIIndex(u.ffiIndex_);
        }
        ArrayBufferView::ViewType viewType() const {
            JS_ASSERT(which_ == ArrayView);
            return u.viewType_;
        }
        AsmMathBuiltin mathBuiltin() const {
            JS_ASSERT(which_ == MathBuiltin);
            return u.mathBuiltin_;
        }
        double constant() const {
            JS_ASSERT(which_ == Constant);
            return u.constant_;
        }
    };

    typedef Vector<const Func*> FuncPtrVector;

    class FuncPtrTable
    {
        FuncPtrVector elems_;
        unsigned baseIndex_;

      public:
        FuncPtrTable(MoveRef<FuncPtrVector> elems, unsigned baseIndex)
          : elems_(elems), baseIndex_(baseIndex) {}
        FuncPtrTable(MoveRef<FuncPtrTable> rhs)
          : elems_(Move(rhs->elems_)), baseIndex_(rhs->baseIndex_) {}

        const Func &sig() const { return *elems_[0]; }
        unsigned numElems() const { return elems_.length(); }
        const Func &elem(unsigned i) const { return *elems_[i]; }
        unsigned baseIndex() const { return baseIndex_; }
        unsigned mask() const { JS_ASSERT(IsPowerOfTwo(numElems())); return numElems() - 1; }

      private:
        FuncPtrTable(const FuncPtrTable &) MOZ_DELETE;
        void operator=(const FuncPtrTable &) MOZ_DELETE;
    };
    typedef Vector<FuncPtrTable> FuncPtrTableVector;

  private:
    typedef HashMap<PropertyName*, AsmMathBuiltin> MathNameMap;
    typedef HashMap<PropertyName*, Global> GlobalMap;
    typedef Vector<Func> FuncVector;

    Maybe<AutoAssertNoGC>        noGC_;
    JSContext *                  cx_;
    LifoAlloc                    alloc_;

    AsmLinkData                  linkData_;

    PropertyName *               moduleName_;
    PropertyName *               globalName_;
    PropertyName *               importName_;
    PropertyName *               bufferName_;

    GlobalMap                    globals_;
    FuncVector                   functions_;
    FuncPtrTableVector           funcPtrTables_;
    AsmExitMap                   exits_;
    MathNameMap                  standardLibraryMathNames_;

    const char *                 errorString_;
    ParseNode *                  errorNode_;
    TokenStream &                tokenStream_;
    DebugOnly<bool>              firstPassComplete_;

    bool addStandardLibraryMathName(const char *name, AsmMathBuiltin code) {
        JSAtom *atom = Atomize(cx_, name, strlen(name));
        if (!atom)
            return false;
        return standardLibraryMathNames_.putNew(atom->asPropertyName(), code);
    }

    static const size_t LIFO_ALLOC_PRIMARY_CHUNK_SIZE = 1 << 12;

  public:
    AsmModuleCompiler(JSContext *cx, TokenStream &ts)
      : cx_(cx),
        alloc_(LIFO_ALLOC_PRIMARY_CHUNK_SIZE),
        moduleName_(NULL),
        globalName_(NULL),
        importName_(NULL),
        bufferName_(NULL),
        globals_(cx),
        functions_(cx),
        funcPtrTables_(cx),
        exits_(cx),
        standardLibraryMathNames_(cx),
        errorString_(NULL),
        errorNode_(NULL),
        tokenStream_(ts),
        firstPassComplete_(false)
    {}

    ~AsmModuleCompiler() {
        noGC_.destroy();
        if (errorString_)
            tokenStream_.reportAsmError(errorNode_, JSMSG_USE_ASM_TYPE_FAIL, errorString_);
    }

    bool init() {
        if (!globals_.init() || !exits_.init())
            return false;

        if (!standardLibraryMathNames_.init() ||
            !addStandardLibraryMathName("sin", AsmMathBuiltin_sin) ||
            !addStandardLibraryMathName("cos", AsmMathBuiltin_cos) ||
            !addStandardLibraryMathName("tan", AsmMathBuiltin_tan) ||
            !addStandardLibraryMathName("asin", AsmMathBuiltin_asin) ||
            !addStandardLibraryMathName("acos", AsmMathBuiltin_acos) ||
            !addStandardLibraryMathName("atan", AsmMathBuiltin_atan) ||
            !addStandardLibraryMathName("ceil", AsmMathBuiltin_ceil) ||
            !addStandardLibraryMathName("floor", AsmMathBuiltin_floor) ||
            !addStandardLibraryMathName("exp", AsmMathBuiltin_exp) ||
            !addStandardLibraryMathName("log", AsmMathBuiltin_log) ||
            !addStandardLibraryMathName("pow", AsmMathBuiltin_pow) ||
            !addStandardLibraryMathName("sqrt", AsmMathBuiltin_sqrt) ||
            !addStandardLibraryMathName("abs", AsmMathBuiltin_abs) ||
            !addStandardLibraryMathName("atan2", AsmMathBuiltin_atan2) ||
            !addStandardLibraryMathName("imul", AsmMathBuiltin_imul))
        {
            return false;
        }

        noGC_.construct();
        return true;
    }

    bool fail(const char *str, ParseNode *pn) {
        JS_ASSERT(!errorString_);
        JS_ASSERT(!errorNode_);
        JS_ASSERT(str);
        JS_ASSERT(pn);
        errorString_ = str;
        errorNode_ = pn;
        return false;
    }

    /*************************************************** Read-only interface */

    JSContext *cx() const { return cx_; }
    LifoAlloc &alloc() { return alloc_; }
    bool hasError() const { return errorString_ != NULL; }
    const AsmLinkData &linkData() const { return linkData_; }
    PropertyName *maybeModuleName() const { return moduleName_; }
    PropertyName *maybeGlobalName() const { return globalName_; }
    PropertyName *maybeImportName() const { return importName_; }
    PropertyName *maybeBufferName() const { return bufferName_; }

    const Global *lookupGlobal(PropertyName *name) const {
        if (GlobalMap::Ptr p = globals_.lookup(name))
            return &p->value;
        return NULL;
    }
    const FuncPtrTable *lookupFuncPtrTable(PropertyName *name) const {
        if (GlobalMap::Ptr p = globals_.lookup(name)) {
            if (p->value.which() == Global::FuncPtrTable)
                return &funcPtrTables_[p->value.funcPtrTableIndex()];
        }
        return NULL;
    }
    const Func *lookupFunction(PropertyName *name) const {
        if (GlobalMap::Ptr p = globals_.lookup(name)) {
            if (p->value.which() == Global::Function)
                return &functions_[p->value.funcIndex()];
        }
        return NULL;
    }
    unsigned numFunctions() const {
        return functions_.length();
    }
    const Func &function(unsigned i) const {
        return functions_[i];
    }
    unsigned numFuncPtrTables() const {
        return funcPtrTables_.length();
    }
    const FuncPtrTable &funcPtrTable(unsigned i) const {
        return funcPtrTables_[i];
    }
    Maybe<AsmMathBuiltin> lookupStandardLibraryMathName(PropertyName *name) const {
        if (MathNameMap::Ptr p = standardLibraryMathNames_.lookup(name))
            return p->value;
        return Maybe<AsmMathBuiltin>();
    }
    AsmExitMap::Range allExits() const {
        return exits_.all();
    }

    /***************************************************** Mutable interface */

    void initModuleName(PropertyName *n) { moduleName_ = n; }
    void initGlobalName(PropertyName *n) { globalName_ = n; }
    void initImportName(PropertyName *n) { importName_ = n; }
    void initBufferName(PropertyName *n) { bufferName_ = n; }

    bool addGlobalVar(PropertyName *varName, AsmVarType type, AsmGlobalVarInit init) {
        JS_ASSERT(!firstPassComplete_);
        Global g(Global::Variable);
        uint32_t index;
        if (!linkData_.addGlobalVar(init, &index))
            return false;
        g.u.var.index_ = index;
        g.u.var.type_ = type.which();
        return globals_.putNew(varName, g);
    }
    bool addFunction(MoveRef<Func> func) {
        JS_ASSERT(!firstPassComplete_);
        Global g(Global::Function);
        g.u.funcIndex_ = functions_.length();
        if (!globals_.putNew(FunctionName(func->fn()), g))
            return false;
        return functions_.append(func);
    }
    bool addFuncPtrTable(PropertyName *varName, MoveRef<FuncPtrVector> funcPtrTableElems) {
        JS_ASSERT(!firstPassComplete_);
        Global g(Global::FuncPtrTable);
        g.u.funcPtrTableIndex_ = funcPtrTables_.length();
        if (!globals_.putNew(varName, g))
            return false;
        FuncPtrTable table(funcPtrTableElems, linkData_.numFuncPtrTableElems());
        if (!linkData_.addFuncPtrTableElems(table.numElems()))
            return false;
        return funcPtrTables_.append(Move(table));
    }
    bool addFFI(PropertyName *varName, PropertyName *field) {
        JS_ASSERT(!firstPassComplete_);
        Global g(Global::FFI);
        uint32_t index;
        if (!linkData_.addFFI(field, &index))
            return false;
        g.u.ffiIndex_ = index;
        return globals_.putNew(varName, g);
    }
    bool addArrayView(PropertyName *varName, ArrayBufferView::ViewType vt, PropertyName *fieldName) {
        JS_ASSERT(!firstPassComplete_);
        Global g(Global::ArrayView);
        if (!linkData_.addArrayView(vt, fieldName))
            return false;
        g.u.viewType_ = vt;
        return globals_.putNew(varName, g);
    }
    bool addMathBuiltin(PropertyName *varName, AsmMathBuiltin mathBuiltin, PropertyName *fieldName) {
        JS_ASSERT(!firstPassComplete_);
        if (!linkData_.addMathBuiltin(mathBuiltin, fieldName))
            return false;
        Global g(Global::MathBuiltin);
        g.u.mathBuiltin_ = mathBuiltin;
        return globals_.putNew(varName, g);
    }
    bool addGlobalConstant(PropertyName *varName, double constant, PropertyName *fieldName) {
        JS_ASSERT(!firstPassComplete_);
        if (!linkData_.addGlobalConstant(constant, fieldName))
            return false;
        Global g(Global::Constant);
        g.u.constant_ = constant;
        return globals_.putNew(varName, g);
    }
    void setExportedFunction(PropertyName *name) {
        JS_ASSERT(!firstPassComplete_);
        functions_[globals_.lookup(name)->value.funcIndex()].setIsExported();
        linkData_.setExportedFunction(name);
    }
    bool addToExportObject(PropertyName *fieldName, PropertyName *functionName) {
        JS_ASSERT(!firstPassComplete_);
        functions_[globals_.lookup(functionName)->value.funcIndex()].setIsExported();
        return linkData_.addToExportObject(fieldName, functionName);
    }
    void setFirstPassComplete() {
        // After the first pass is complete, there should be no more additions
        // to the global scope. This also means that functions_ and globals_
        // are stable and the second pass can pass around pointers to their
        // entries.
        firstPassComplete_ = true;
    }
    Func &function(unsigned funcIndex) {
        JS_ASSERT(firstPassComplete_);
        return functions_[funcIndex];
    }
    bool addExit(AsmFFIIndex ffi, PropertyName *name, MoveRef<MIRTypeVector> argTypes, AsmUse use,
                 AsmExitIndex *i)
    {
        JS_ASSERT(firstPassComplete_);
        AsmExitDescriptor exitDescriptor(name, argTypes, use);
        AsmExitMap::AddPtr p = exits_.lookupForAdd(exitDescriptor);
        if (p) {
            *i = p->value;
            return true;
        }
        if (!linkData_.addExit(AsmExit(ffi), i))
            return false;
        return exits_.add(p, Move(exitDescriptor), *i);
    }
    bool attemptUseLengthMask(uint32_t mask) {
        JS_ASSERT(firstPassComplete_);
        return linkData_.attemptUseLengthMask(mask);
    }
    bool attemptUseConstantPointer(uint32_t pointer) {
        JS_ASSERT(firstPassComplete_);
        return linkData_.attemptUseConstantPointer(pointer);
    }
    void setDefaultExitPool(JSC::ExecutablePool *pool) {
        linkData_.setDefaultExitPool(pool);
    }
    void setDefaultExit(AsmExitIndex i, uint8_t *defaultExit) {
        JS_ASSERT(firstPassComplete_);
        linkData_.setDefaultExit(i, defaultExit);
    }
    void initFuncPtrTableElems(MoveRef<AsmLinkData::FuncPtrTableElemVector> funcPtrTableElems) {
        JS_ASSERT(firstPassComplete_);
        linkData_.initFuncPtrTableElems(funcPtrTableElems);
    }
    MoveRef<AsmLinkData> transferModuleData() {
        return Move(linkData_);
    }
};

/*****************************************************************************/

// Utility class to implement asm.js callbacks called by the IM backend.
class AsmMIRGenerator : public MIRGenerator
{
    AsmModuleCompiler &m_;
    AsmModuleCompiler::Func &caller_;
    uint32_t maxStackBytes_;

  public:
    AsmMIRGenerator(JSCompartment *compartment,
                    TempAllocator *temp,
                    MIRGraph *graph,
                    CompileInfo *info,
                    AsmModuleCompiler &m,
                    AsmModuleCompiler::Func &caller)
      : MIRGenerator(compartment, temp, graph, info),
        m_(m),
        caller_(caller),
        maxStackBytes_(0)
    {}

    bool observeAsmCall(size_t offsetOfCall, const void *observerData) MOZ_OVERRIDE {
        const AsmModuleCompiler::Func *callee = (const AsmModuleCompiler::Func *)observerData;
        return caller_.addCall(AsmModuleCompiler::Call(offsetOfCall, callee));
    }

    uint32_t maxAsmStackArgBytes() const MOZ_OVERRIDE {
        return maxStackBytes_;
    }

    uint32_t resetMaxStackBytes() {
        uint32_t old = maxStackBytes_;
        maxStackBytes_ = 0;
        return old;
    }

    void setMaxStackBytes(uint32_t n) {
        maxStackBytes_ = n;
    }
};

/*****************************************************************************/

// Encapsulates the compilation of a single function in an asm.js module. The
// function compiler handles the creation and final backend compilation of the
// MIR graph.
class AsmFunctionCompiler
{
  public:
    struct Local
    {
        enum Which { Var, Arg } which;
        AsmVarType type;
        unsigned slot;
        Value initialValue;

        Local(AsmVarType t, unsigned slot)
          : which(Arg), type(t), slot(slot), initialValue(MagicValue(JS_GENERIC_MAGIC)) {}
        Local(AsmVarType t, unsigned slot, const Value &init)
          : which(Var), type(t), slot(slot), initialValue(init) {}
    };
    typedef HashMap<PropertyName*, Local> LocalMap;

  private:
    typedef Vector<MBasicBlock*, 2> BlockVector;
    typedef HashMap<PropertyName*, BlockVector> LabeledBlockMap;
    typedef HashMap<ParseNode*, BlockVector> UnlabeledBlockMap;
    typedef Vector<ParseNode*, 4> NodeStack;

    AsmModuleCompiler &       m_;
    AsmModuleCompiler::Func & func_;
    LocalMap                  locals_;

    TempAllocator             tempAlloc_;
    IonContext                ionContext_;
    AutoFlushCache            autoFlushCache_;
    MIRGraph                  mirGraph_;
    CompileInfo               compileInfo_;
    AsmMIRGenerator           mirGen_;

    MBasicBlock *             curBlock_;
    size_t                    maxStackArgsBytes_;
    NodeStack                 loopStack_;
    NodeStack                 breakableStack_;
    UnlabeledBlockMap         unlabeledBreaks_;
    UnlabeledBlockMap         unlabeledContinues_;
    LabeledBlockMap           labeledBreaks_;
    LabeledBlockMap           labeledContinues_;

  public:
    AsmFunctionCompiler(AsmModuleCompiler &m, AsmModuleCompiler::Func &func,
                        MoveRef<LocalMap> locals)
      : m_(m),
        func_(func),
        locals_(locals),
        tempAlloc_(&m_.alloc()),
        ionContext_(m.cx(), m.cx()->compartment, &tempAlloc_),
        autoFlushCache_("asm.js"),  // TODO: right place?
        mirGraph_(&tempAlloc_),
        compileInfo_(locals_.count()),
        mirGen_(m.cx()->compartment, &tempAlloc_, &mirGraph_, &compileInfo_, m, func),
        curBlock_(NULL),
        loopStack_(m.cx()),
        breakableStack_(m.cx()),
        unlabeledBreaks_(m.cx()),
        unlabeledContinues_(m.cx()),
        labeledBreaks_(m.cx()),
        labeledContinues_(m.cx())
    {}

    bool init()
    {
        if (!unlabeledBreaks_.init() ||
            !unlabeledContinues_.init() ||
            !labeledBreaks_.init() ||
            !labeledContinues_.init())
        {
            return false;
        }

        curBlock_ = newBlock(/* pred = */ NULL);

        for (ABIArgIter i(func_.argMIRTypes()); !i.done(); i++) {
            MAsmParameter *param = MAsmParameter::New(*i, i.mirType());
            curBlock_->add(param);
            curBlock_->initSlot(compileInfo_.localSlot(i.index()), param);
        }

        for (LocalMap::Range r = locals_.all(); !r.empty(); r.popFront()) {
            const Local &local = r.front().value;
            if (local.which == Local::Var) {
                MConstant *constant = MConstant::New(local.initialValue);
                curBlock_->add(constant);
                curBlock_->initSlot(compileInfo_.localSlot(local.slot), constant);
            }
        }

        return true;
    }

    bool fail(const char *str, ParseNode *pn)
    {
        m_.fail(str, pn);
        return false;
    }

    ~AsmFunctionCompiler()
    {
        m_.alloc().release(NULL);

        if (!m().hasError() && !cx()->isExceptionPending()) {
            JS_ASSERT(loopStack_.empty());
            JS_ASSERT(unlabeledBreaks_.empty());
            JS_ASSERT(unlabeledContinues_.empty());
            JS_ASSERT(labeledBreaks_.empty());
            JS_ASSERT(labeledContinues_.empty());
            JS_ASSERT(curBlock_ == NULL);
        }
    }

    /*************************************************** Read-only interface */

    JSContext *               cx() const { return m_.cx(); }
    AsmModuleCompiler &       m() const { return m_; }
    AsmModuleCompiler::Func & func() const { return func_; }
    TempAllocator &           tempAlloc() { return tempAlloc_; }
    MIRGraph &                mirGraph() { return mirGraph_; }
    MIRGenerator &            mirGen() { return mirGen_; }

    const Local *lookupLocal(PropertyName *name) const
    {
        if (LocalMap::Ptr p = locals_.lookup(name))
            return &p->value;
        return NULL;
    }

    MDefinition *getLocalDef(const Local &local)
    {
        if (!curBlock_)
            return NULL;
        return curBlock_->getSlot(compileInfo_.localSlot(local.slot));
    }

    const AsmModuleCompiler::Func *lookupFunction(PropertyName *name) const
    {
        if (locals_.has(name))
            return NULL;
        if (const AsmModuleCompiler::Func *func = m_.lookupFunction(name))
            return func;
        return NULL;
    }

    const AsmModuleCompiler::Global *lookupGlobal(PropertyName *name) const
    {
        if (locals_.has(name))
            return NULL;
        return m_.lookupGlobal(name);
    }

    /************************************************* Expression generation */

    // TODO: figure out the OOM story

    MDefinition *constant(const Value &v)
    {
        if (!curBlock_)
            return NULL;
        JS_ASSERT(v.isNumber());
        MConstant *constant = MConstant::New(v);
        curBlock_->add(constant);
        return constant;
    }

    template <class T>
    MDefinition *unary(MDefinition *op)
    {
        if (!curBlock_)
            return NULL;
        T *ins = T::NewAsm(op);
        curBlock_->add(ins);
        return ins;
    }

    template <class T>
    MDefinition *unary(MDefinition *op, MIRType type)
    {
        if (!curBlock_)
            return NULL;
        T *ins = T::NewAsm(op, type);
        curBlock_->add(ins);
        return ins;
    }

    template <class T>
    MDefinition *binary(MDefinition *lhs, MDefinition *rhs)
    {
        if (!curBlock_)
            return NULL;
        T *ins = T::New(lhs, rhs);
        curBlock_->add(ins);
        return ins;
    }

    template <class T>
    MDefinition *binary(MDefinition *lhs, MDefinition *rhs, MIRType type)
    {
        if (!curBlock_)
            return NULL;
        T *ins = T::NewAsm(lhs, rhs, type);
        curBlock_->add(ins);
        return ins;
    }

    MDefinition *mul(MDefinition *lhs, MDefinition *rhs, MIRType type, MMul::Mode mode)
    {
        if (!curBlock_)
            return NULL;
        MMul *ins = MMul::New(lhs, rhs, type, mode);
        curBlock_->add(ins);
        return ins;
    }

    template <class T>
    MDefinition *bitwise(MDefinition *lhs, MDefinition *rhs)
    {
        if (!curBlock_)
            return NULL;
        T *ins = T::NewAsm(lhs, rhs);
        curBlock_->add(ins);
        return ins;
    }

    template <class T>
    MDefinition *bitwise(MDefinition *op)
    {
        if (!curBlock_)
            return NULL;
        T *ins = T::NewAsm(op);
        curBlock_->add(ins);
        return ins;
    }

    MDefinition *compare(MDefinition *lhs, MDefinition *rhs, JSOp op, MCompare::CompareType type)
    {
        if (!curBlock_)
            return NULL;
        MCompare *ins = MCompare::NewAsm(lhs, rhs, op, type);
        curBlock_->add(ins);
        return ins;
    }

    void assign(const Local &local, MDefinition *def)
    {
        if (!curBlock_)
            return;
        curBlock_->setSlot(compileInfo_.localSlot(local.slot), def);
    }

    MDefinition *loadHeap(ArrayBufferView::ViewType vt, uint32_t mask, MDefinition *ptr)
    {
        if (!curBlock_)
            return NULL;
        MAsmLoad *load = MAsmLoad::New(vt, MAsmLoad::Heap, maskArrayAccess(ptr, mask));
        curBlock_->add(load);
        return load;
    }

    void storeHeap(ArrayBufferView::ViewType vt, uint32_t mask, MDefinition *ptr, MDefinition *v)
    {
        if (!curBlock_)
            return;
        curBlock_->add(MAsmStore::New(vt, MAsmStore::Heap, maskArrayAccess(ptr, mask), v));
    }

    MDefinition *loadGlobalVar(const AsmModuleCompiler::Global &global)
    {
        if (!curBlock_)
            return NULL;
        ArrayBufferView::ViewType vt;
        switch (global.varType().which()) {
          case AsmVarType::Int: vt = ArrayBufferView::TYPE_INT32; break;
          case AsmVarType::Double: vt = ArrayBufferView::TYPE_FLOAT64; break;
        }
        int32_t disp = m_.linkData().globalVarIndexToGlobalDataOffset(global.varIndex());
        MDefinition *index = constant(Int32Value(disp));
        MAsmLoad *load = MAsmLoad::New(vt, MAsmLoad::Global, index);
        curBlock_->add(load);
        return load;
    }

    void storeGlobalVar(const AsmModuleCompiler::Global &global, MDefinition *v)
    {
        if (!curBlock_)
            return;
        ArrayBufferView::ViewType vt;
        switch (global.varType().which()) {
          case AsmVarType::Int: vt = ArrayBufferView::TYPE_INT32; break;
          case AsmVarType::Double: vt = ArrayBufferView::TYPE_FLOAT64; break;
        }
        int32_t disp = m_.linkData().globalVarIndexToGlobalDataOffset(global.varIndex());
        MDefinition *index = constant(Int32Value(disp));
        curBlock_->add(MAsmStore::New(vt, MAsmStore::Global, index, v));
    }

    /***************************************************************** Calls */

    // To implement calls, we must accumulate, for the entire function, the
    // maximum required stack space for argument passing. Naively, this would
    // just be the maximum of the stack space required for each individual call
    // (as determined by the call ABI). However, as an optimization, we store
    // stack arguments to the stack immediately after evaluation (to decrease
    // live ranges and reduce spilling). This introduces the complexity that,
    // between evaluating an argument and making the call, another argument
    // evaluation could perform a call that also needs to store to the stack.
    // When this occurs childClobbers_ = true and the parent's arguments are
    // stored above the maximum depth clobbered by a child expression.

    class Args
    {
        ABIArgGenerator abi_;
        uint32_t prevMaxStackBytes_;
        uint32_t maxChildStackBytes_;
        Vector<AsmType, 8> types_;
        MAsmCall::Args regArgs_;
        MIRStackArgVector stackArgs_;
        bool childClobbers_;
        friend class AsmFunctionCompiler;
      public:
        Args(AsmFunctionCompiler &f)
          : prevMaxStackBytes_(0),
            maxChildStackBytes_(0),
            types_(f.cx()),
            regArgs_(f.cx()),
            stackArgs_(f.cx()),
            childClobbers_(false)
        {}
        unsigned length() const {
            return types_.length();
        }
        AsmType type(unsigned i) const {
            return types_[i];
        }
    };

    void startCallArgs(Args *args)
    {
        if (!curBlock_)
            return;
        args->prevMaxStackBytes_ = mirGen_.resetMaxStackBytes();
    }

    bool passArg(MDefinition *argDef, AsmType type, Args *args)
    {
        if (!args->types_.append(type))
            return false;

        if (!curBlock_)
            return true;

        uint32_t childStackBytes = mirGen_.resetMaxStackBytes();
        args->maxChildStackBytes_ = Max(args->maxChildStackBytes_, childStackBytes);
        if (childStackBytes > 0 && !args->stackArgs_.empty())
            args->childClobbers_ = true;

        ABIArg arg = args->abi_.next(type.toMIRType());
        if (arg.kind() == ABIArg::Stack) {
            MAsmPassStackArg *mir = MAsmPassStackArg::New(arg.offsetFromArg0(), argDef);
            curBlock_->add(mir);
            if (!args->stackArgs_.append(mir))
                return false;
        } else {
            if (!args->regArgs_.append(MAsmCall::Arg(arg.reg(), argDef)))
                return false;
        }
        return true;
    }

    void finishCallArgs(Args *args)
    {
        if (!curBlock_)
            return;
        uint32_t parentStackBytes = args->abi_.stackBytesConsumedSoFar();
        if (args->childClobbers_) {
            for (unsigned i = 0; i < args->stackArgs_.length(); i++)
                args->stackArgs_[i]->incrementOffset(args->maxChildStackBytes_);
            mirGen_.setMaxStackBytes(Max(args->prevMaxStackBytes_,
                                         args->maxChildStackBytes_ + parentStackBytes));
        } else {
            mirGen_.setMaxStackBytes(Max(args->prevMaxStackBytes_,
                                         Max(args->maxChildStackBytes_, parentStackBytes)));
        }
    }

    MDefinition *call(MAsmCall::Callee callee, const Args &args, MIRType returnType)
    {
        if (!curBlock_)
            return NULL;
        uint32_t spIncrement = args.childClobbers_ ? args.maxChildStackBytes_ : 0;
        MAsmCall *ins = MAsmCall::New(callee, args.regArgs_, returnType, spIncrement);
        curBlock_->add(ins);
        return ins;
    }

    MDefinition *internalCall(const AsmModuleCompiler::Func &func, const Args &args)
    {
        if (!curBlock_)
            return NULL;
        MAsmCall::Callee callee = MAsmCall::Callee::internal(&func);
        MIRType returnType = func.returnType().toMIRType();
        return call(callee, args, returnType);
    }

    MDefinition *funcPtrCall(const AsmModuleCompiler::FuncPtrTable &funcPtrTable, MDefinition *index,
                             const Args &args)
    {
        if (!curBlock_)
            return NULL;

        MConstant *mask = MConstant::New(Int32Value(funcPtrTable.mask()));
        curBlock_->add(mask);
        MBitAnd *masked = MBitAnd::NewAsm(index, mask);
        curBlock_->add(masked);
        int32_t disp = m_.linkData().funcPtrTableElemIndexToGlobalDataOffset(funcPtrTable.baseIndex());
        Scale scale = ScaleFromElemWidth(sizeof(void*));
        MAsmLoad *ptrFun = MAsmLoad::New(MAsmLoad::FUNC_PTR, MAsmLoad::Global, masked, scale, disp);
        curBlock_->add(ptrFun);

        MAsmCall::Callee callee = MAsmCall::Callee::dynamic(ptrFun);
        MIRType returnType = funcPtrTable.sig().returnType().toMIRType();
        return call(callee, args, returnType);
    }

    MDefinition *ffiCall(AsmExitIndex exitIndex, const Args &args, MIRType returnType)
    {
        if (!curBlock_)
            return NULL;

        int32_t offset = m_.linkData().exitIndexToGlobalDataOffset(exitIndex);
        MDefinition *index = constant(Int32Value(offset));
        MAsmLoad *ptrFun = MAsmLoad::New(MAsmLoad::FUNC_PTR, MAsmLoad::Global, index);
        curBlock_->add(ptrFun);

        MAsmCall::Callee callee = MAsmCall::Callee::dynamic(ptrFun);
        return call(callee, args, returnType);
    }

    MDefinition *builtinCall(void *builtin, const Args &args, MIRType returnType)
    {
        if (!curBlock_)
            return NULL;
        MAsmCall::Callee callee = MAsmCall::Callee::builtin(builtin);
        return call(callee, args, returnType);
    }

    /*********************************************** Control flow generation */

    void returnExpr(MDefinition *expr)
    {
        if (!curBlock_)
            return;
        MAsmReturn *ins = MAsmReturn::New(expr);
        curBlock_->end(ins);
        curBlock_ = NULL;
    }

    void returnVoid()
    {
        if (!curBlock_)
            return;
        MAsmVoidReturn *ins = MAsmVoidReturn::New();
        curBlock_->end(ins);
        curBlock_ = NULL;
    }

    void branchAndStartThen(MDefinition *cond, MBasicBlock **thenBlock, MBasicBlock **elseBlock)
    {
        if (!curBlock_) {
            *thenBlock = NULL;
            *elseBlock = NULL;
            return;
        }
        *thenBlock = newBlock(curBlock_);
        *elseBlock = newBlock(curBlock_);
        curBlock_->end(MTest::New(cond, *thenBlock, *elseBlock));
        curBlock_ = *thenBlock;
    }

    void joinIf(MBasicBlock *joinBlock)
    {
        if (!joinBlock)
            return;
        if (curBlock_) {
            curBlock_->end(MGoto::New(joinBlock));
            joinBlock->addPredecessor(curBlock_);
        }
        curBlock_ = joinBlock;
        mirGraph_.moveBlockToEnd(curBlock_);
    }

    MBasicBlock *switchToElse(MBasicBlock *elseBlock)
    {
        if (!elseBlock)
            return NULL;
        MBasicBlock *thenEnd = curBlock_;
        curBlock_ = elseBlock;
        mirGraph_.moveBlockToEnd(curBlock_);
        return thenEnd;
    }

    void joinIfElse(MBasicBlock *thenEnd)
    {
        if (!curBlock_ && !thenEnd)
            return;
        MBasicBlock *pred = curBlock_ ? curBlock_ : thenEnd;
        MBasicBlock *join = newBlock(pred);
        if (curBlock_)
            curBlock_->end(MGoto::New(join));
        if (thenEnd)
            thenEnd->end(MGoto::New(join));
        if (curBlock_ && thenEnd)
            join->addPredecessor(thenEnd);
        curBlock_ = join;
    }

    void pushPhiInput(MDefinition *def)
    {
        if (!curBlock_)
            return;
        JS_ASSERT(curBlock_->stackDepth() == compileInfo_.firstStackSlot());
        curBlock_->push(def);
    }

    MDefinition *popPhiOutput()
    {
        if (!curBlock_)
            return NULL;
        JS_ASSERT(curBlock_->stackDepth() == compileInfo_.firstStackSlot() + 1);
        return curBlock_->pop();
    }

    MBasicBlock *startPendingLoop(ParseNode *pn)
    {
        pushLoop(pn);
        JS_ASSERT_IF(curBlock_, curBlock_->loopDepth() == loopStack_.length() - 1);
        if (!curBlock_)
            return NULL;
        MBasicBlock *next = MBasicBlock::NewPendingLoopHeader(mirGraph_, compileInfo_, curBlock_, NULL);
        mirGraph_.addBlock(next);
        next->setLoopDepth(loopStack_.length());
        curBlock_->end(MGoto::New(next));
        curBlock_ = next;
        return next;
    }

    MBasicBlock *branchAndStartLoopBody(MDefinition *cond)
    {
        if (!curBlock_)
            return NULL;
        JS_ASSERT(curBlock_->loopDepth() > 0);
        MBasicBlock *body = newBlock(curBlock_);
        MBasicBlock *afterLoop = NULL;
        if (cond->isConstant() && ToBoolean(cond->toConstant()->value())) {
            curBlock_->end(MGoto::New(body));
        } else {
            afterLoop = newBlockWithDepth(curBlock_, curBlock_->loopDepth() - 1);
            curBlock_->end(MTest::New(cond, body, afterLoop));
        }
        curBlock_ = body;
        return afterLoop;
    }

    void closeLoop(MBasicBlock *loopEntry, MBasicBlock *afterLoop)
    {
        ParseNode *pn = popLoop();
        if (!loopEntry) {
            JS_ASSERT(!afterLoop);
            JS_ASSERT(!curBlock_);
            JS_ASSERT(unlabeledBreaks_.empty());
            return;
        }
        JS_ASSERT(loopEntry->loopDepth() == loopStack_.length() + 1);
        JS_ASSERT_IF(afterLoop, afterLoop->loopDepth() == loopStack_.length());
        if (curBlock_) {
            JS_ASSERT(curBlock_->loopDepth() == loopStack_.length() + 1);
            curBlock_->end(MGoto::New(loopEntry));
            loopEntry->setBackedge(curBlock_);
        }
        curBlock_ = afterLoop;
        if (curBlock_)
            mirGraph_.moveBlockToEnd(curBlock_);
        bindUnlabeledBreaks(pn);
    }

    void branchAndCloseDoWhileLoop(MDefinition *cond, MBasicBlock *loopEntry)
    {
        ParseNode *pn = popLoop();
        if (!loopEntry) {
            JS_ASSERT(!curBlock_);
            JS_ASSERT(unlabeledBreaks_.empty());
            return;
        }
        JS_ASSERT(loopEntry->loopDepth() == loopStack_.length() + 1);
        if (curBlock_) {
            JS_ASSERT(curBlock_->loopDepth() == loopStack_.length() + 1);
            if (cond->isConstant()) {
                if (ToBoolean(cond->toConstant()->value())) {
                    curBlock_->end(MGoto::New(loopEntry));
                    loopEntry->setBackedge(curBlock_);
                    curBlock_ = NULL;
                } else {
                    MBasicBlock *afterLoop = newBlock(curBlock_);
                    curBlock_->end(MGoto::New(afterLoop));
                    curBlock_ = afterLoop;
                }
            } else {
                MBasicBlock *afterLoop = newBlock(curBlock_);
                curBlock_->end(MTest::New(cond, loopEntry, afterLoop));
                loopEntry->setBackedge(curBlock_);
                curBlock_ = afterLoop;
            }
        }
        bindUnlabeledBreaks(pn);
    }

    void bindContinues(ParseNode *pn, const AsmLabelVector *maybeLabels)
    {
        MBasicBlock *joinBlock = NULL;
        if (UnlabeledBlockMap::Ptr p = unlabeledContinues_.lookup(pn)) {
            joinBlock = bindBreaksOrContinues(joinBlock, &p->value);
            unlabeledContinues_.remove(p);
        }
        joinBlock = bindLabeledBreaksOrContinues(joinBlock, maybeLabels, &labeledContinues_);
        if (joinBlock)
            curBlock_ = joinBlock;
    }

    void bindLabeledBreaks(const AsmLabelVector *maybeLabels)
    {
        curBlock_ = bindLabeledBreaksOrContinues(curBlock_, maybeLabels, &labeledBreaks_);
    }

    bool addBreak(PropertyName *maybeLabel) {
        if (maybeLabel)
            return addBreakOrContinue(maybeLabel, &labeledBreaks_);
        return addBreakOrContinue(breakableStack_.back(), &unlabeledBreaks_);
    }

    bool addContinue(PropertyName *maybeLabel) {
        if (maybeLabel)
            return addBreakOrContinue(maybeLabel, &labeledContinues_);
        return addBreakOrContinue(loopStack_.back(), &unlabeledContinues_);
    }

    MBasicBlock *startSwitch(ParseNode *pn, MDefinition *expr, int32_t low, int32_t high)
    {
        breakableStack_.append(pn);
        if (!curBlock_)
            return NULL;
        curBlock_->end(MTableSwitch::New(expr, low, high));
        MBasicBlock *switchBlock = curBlock_;
        curBlock_ = NULL;
        return switchBlock;
    }

    MBasicBlock *startSwitchCase(MBasicBlock *switchBlock)
    {
        if (!switchBlock)
            return NULL;
        MBasicBlock *next = newBlock(switchBlock);
        if (curBlock_) {
            curBlock_->end(MGoto::New(next));
            next->addPredecessor(curBlock_);
        }
        curBlock_ = next;
        return next;
    }

    MBasicBlock *startSwitchDefault(MBasicBlock *switchBlock, AsmCaseVector *cases)
    {
        MBasicBlock *defaultBlock = startSwitchCase(switchBlock);
        if (!defaultBlock)
            return NULL;
        for (unsigned i = 0; i < cases->length(); i++) {
            if (!(*cases)[i]) {
                MBasicBlock *bb = newBlock(switchBlock);
                bb->end(MGoto::New(defaultBlock));
                defaultBlock->addPredecessor(bb);
                (*cases)[i] = bb;
            }
        }
        mirGraph_.moveBlockToEnd(defaultBlock);
        return defaultBlock;
    }

    void joinSwitch(MBasicBlock *switchBlock, const AsmCaseVector &cases, MBasicBlock *defaultBlock)
    {
        ParseNode *pn = breakableStack_.popCopy();
        if (!switchBlock)
            return;
        MTableSwitch *mir = switchBlock->lastIns()->toTableSwitch();
        mir->addDefault(defaultBlock);
        for (unsigned i = 0; i < cases.length(); i++)
            mir->addCase(cases[i]);
        if (curBlock_) {
            MBasicBlock *next = newBlock(curBlock_);
            curBlock_->end(MGoto::New(next));
            curBlock_ = next;
        }
        bindUnlabeledBreaks(pn);
    }

    /*************************************************************************/
  private:
    MDefinition *maskArrayAccess(MDefinition *ptr, uint32_t mask)
    {
        // If !SAFE, pretend this is a DataView access guarded by a signal
        // handler. In that case, there is no checking required at the load; we
        // depend on signal handlers and carefully setting everything up so
        // that out of bounds access always trap.
        if (!SAFE || mask == UINT32_MAX)
            return ptr;

        MConstant *constant = MConstant::New(Int32Value(mask));
        curBlock_->add(constant);
        MBitAnd *bitAnd = MBitAnd::NewAsm(ptr, constant);
        curBlock_->add(bitAnd);
        return bitAnd;
    }

    MBasicBlock *newBlockWithDepth(MBasicBlock *pred, unsigned loopDepth)
    {
        MBasicBlock *bb = MBasicBlock::New(mirGraph_, compileInfo_, pred, /* pc = */NULL,
                                           MBasicBlock::NORMAL);
        mirGraph_.addBlock(bb);
        bb->setLoopDepth(loopDepth);
        return bb;
    }

    MBasicBlock *newBlock(MBasicBlock *pred)
    {
        return newBlockWithDepth(pred, loopStack_.length());
    }

    MBasicBlock *bindBreaksOrContinues(MBasicBlock *joinBlock, BlockVector *preds)
    {
        for (unsigned i = 0; i < preds->length(); i++) {
            MBasicBlock *pred = (*preds)[i];
            if (!joinBlock) {
                joinBlock = newBlock(pred);
                if (curBlock_) {
                    curBlock_->end(MGoto::New(joinBlock));
                    joinBlock->addPredecessor(curBlock_);
                }
                pred->end(MGoto::New(joinBlock));
            } else {
                pred->end(MGoto::New(joinBlock));
                joinBlock->addPredecessor(pred);
            }
        }
        preds->clear();
        return joinBlock;
    }

    MBasicBlock *bindLabeledBreaksOrContinues(MBasicBlock *joinBlock,
                                              const AsmLabelVector *maybeLabels,
                                              LabeledBlockMap *map)
    {
        if (!maybeLabels)
            return joinBlock;
        const AsmLabelVector &labels = *maybeLabels;
        for (unsigned i = 0; i < labels.length(); i++) {
            if (LabeledBlockMap::Ptr p = map->lookup(labels[i])) {
                joinBlock = bindBreaksOrContinues(joinBlock, &p->value);
                map->remove(p);
            }
        }
        return joinBlock;
    }

    template <class Key, class Map>
    bool addBreakOrContinue(Key key, Map *map)
    {
        if (!curBlock_)
            return true;
        typename Map::AddPtr p = map->lookupForAdd(key);
        if (!p) {
            BlockVector empty(m().cx());
            if (!map->add(p, key, Move(empty)))
                return false;
        }
        if (!p->value.append(curBlock_))
            return false;
        curBlock_ = NULL;
        return true;
    }

    void pushLoop(ParseNode *pn)
    {
        loopStack_.append(pn);
        breakableStack_.append(pn);
    }

    ParseNode *popLoop()
    {
        ParseNode *pn = loopStack_.back();
        JS_ASSERT(!unlabeledContinues_.has(pn));
        loopStack_.popBack();
        breakableStack_.popBack();
        return pn;
    }

    void bindUnlabeledBreaks(ParseNode *pn)
    {
        if (UnlabeledBlockMap::Ptr p = unlabeledBreaks_.lookup(pn)) {
            curBlock_ = bindBreaksOrContinues(curBlock_, &p->value);
            unlabeledBreaks_.remove(p);
        }
    }
};

/*****************************************************************************/
// An AsmModule contains the persistent results of asm.js module compilation,
// viz., the jit code and dynamic link information.
//
// An AsmModule object is created at the end of module compilation and
// subsequently owned by an AsmModuleClass JSObject.

class AsmModule
{
  public:
    typedef Vector<AsmVarType, 4, SystemAllocPolicy> Args;

    struct Func
    {
        Args args;
        AsmRetType returnType;
        AsmCodePtr codePtr;
        ExecPoolPtr pool;

        Func(MoveRef<Args> args, AsmRetType returnType, AsmCodePtr codePtr, ExecPoolPtr *pool)
          : args(args),
            returnType(returnType),
            codePtr(codePtr),
            pool(pool->forget())
        {}
        Func(MoveRef<Func> rhs)
          : args(Move(rhs->args)),
            returnType(rhs->returnType),
            codePtr(rhs->codePtr),
            pool(rhs->pool.forget())
        {}

      private:
        Func(const Func &) MOZ_DELETE;
        void operator=(const Func &) MOZ_DELETE;
    };

  private:
    typedef HashMap<PropertyName*,
                    Func,
                    DefaultHasher<PropertyName*>,
                    SystemAllocPolicy> FuncMap;

    AsmLinkData linkData_;
    FuncMap functions_;

  public:
    AsmModule() {}
    static AsmModule *New(AsmModuleCompiler &m);

    AsmModule(MoveRef<AsmModule> m)
      : functions_(Move(m->functions_))
    {}

    void operator=(MoveRef<AsmModule> m) {
        functions_ = Move(m->functions_);
    }

    const Func &function(PropertyName *name) const {
        return functions_.lookup(name)->value;
    }

    const AsmLinkData &linkData() const {
        return linkData_;
    }

    void trace(JSTracer *trc);

  private:
    AsmModule(const AsmModule &) MOZ_DELETE;
    void operator=(const AsmModule &) MOZ_DELETE;
};

AsmModule *
AsmModule::New(AsmModuleCompiler &m)
{
    ScopedJSDeletePtr<AsmModule> module(m.cx()->new_<AsmModule>());
    if (!module)
        return NULL;

    module->linkData_ = m.transferModuleData();

    if (!module->functions_.init())
        return NULL;

    for (unsigned i = 0; i < m.numFunctions(); i++) {
        AsmModuleCompiler::Func &oldFunc = m.function(i);

        Args dstArgs;
        for (unsigned i = 0; i < oldFunc.numArgs(); i++) {
            if (!dstArgs.append(oldFunc.argType(i)))
                return NULL;
        }

        Func newFunc(Move(dstArgs), oldFunc.returnType(), oldFunc.codePtr(), &oldFunc.pool());
        if (!module->functions_.putNew(FunctionName(oldFunc.fn()), Move(newFunc)))
            return NULL;
    }

    return module.forget();
}

void
AsmModule::trace(JSTracer *trc)
{
    for (FuncMap::Enum e(functions_); !e.empty(); e.popFront()) {
        PropertyName *key = e.front().key;
        MarkStringUnbarriered(trc, &key, "asm function name");
        if (key != e.front().key)
            e.rekeyFront(key);
    }

    linkData_.trace(trc);
}

extern Class AsmModuleClass;

static const unsigned ASM_CODE_RESERVED_SLOT = 0;
static const unsigned ASM_CODE_NUM_RESERVED_SLOTS = 1;

static AsmModule &
AsmModuleObjectToModule(JSObject *obj)
{
    JS_ASSERT(obj->getClass() == &AsmModuleClass);
    return *(AsmModule *)obj->getReservedSlot(ASM_CODE_RESERVED_SLOT).toPrivate();
}

static void
AsmModuleObject_finalize(FreeOp *fop, RawObject obj)
{
    fop->delete_(&AsmModuleObjectToModule(obj));
}

static void
AsmModuleObject_trace(JSTracer *trc, JSRawObject obj)
{
    AsmModuleObjectToModule(obj).trace(trc);
}

Class AsmModuleClass = {
    "AsmModuleObject",
    JSCLASS_IS_ANONYMOUS | JSCLASS_HAS_RESERVED_SLOTS(ASM_CODE_NUM_RESERVED_SLOTS),
    JS_PropertyStub,         /* addProperty */
    JS_PropertyStub,         /* delProperty */
    JS_PropertyStub,         /* getProperty */
    JS_StrictPropertyStub,   /* setProperty */
    JS_EnumerateStub,
    JS_ResolveStub,
    NULL,                    /* convert     */
    AsmModuleObject_finalize,
    NULL,                    /* checkAccess */
    NULL,                    /* call        */
    NULL,                    /* hasInstance */
    NULL,                    /* construct   */
    AsmModuleObject_trace
};

static JSObject *
NewAsmModuleObject(JSContext *cx, ScopedJSDeletePtr<AsmModule> *module)
{
    JSObject *obj = NewObjectWithGivenProto(cx, &AsmModuleClass, NULL, NULL);
    if (!obj)
        return NULL;

    obj->setReservedSlot(ASM_CODE_RESERVED_SLOT, PrivateValue(module->forget()));
    return obj;
}


/*****************************************************************************/
// An AsmLinkedModuleClass represents the result of the dynamic-link step which
// binds a heap and global data segment to an AsmModule.

extern Class AsmLinkedModuleClass;

static const unsigned ASM_LINKED_MODULE_MODULE_SLOT = 0;
static const unsigned ASM_LINKED_MODULE_GLOBAL_DATA_SLOT = 1;
static const unsigned ASM_LINKED_MODULE_HEAP_SLOT = 2;
static const unsigned ASM_LINKED_MODULE_NUM_RESERVED_SLOTS = 3;

static AsmModule &
AsmLinkedModuleToModule(JSObject *obj)
{
    JS_ASSERT(obj->getClass() == &AsmLinkedModuleClass);
    JSObject *moduleObj = &obj->getReservedSlot(ASM_LINKED_MODULE_MODULE_SLOT).toObject();
    return AsmModuleObjectToModule(moduleObj);
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
    if (JSObject *buf = obj->getReservedSlot(ASM_LINKED_MODULE_HEAP_SLOT).toObjectOrNull())
        return buf->asArrayBuffer().dataPointer();
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
    const AsmLinkData &linkData = AsmLinkedModuleToModule(obj).linkData();
    uint8_t *globalData = AsmLinkedModuleToGlobalData(obj);
    for (unsigned i = 0; i < linkData.numExits(); i++) {
        AsmExitGlobalDatum &exitDatum = linkData.exitIndexToGlobalDatum(globalData, AsmExitIndex(i));
        if (exitDatum.fun)
            MarkObject(trc, &exitDatum.fun, "AsmFFIGlobalDatum.fun");
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

/*****************************************************************************/
// asm.js type-checking and code-generation algorithm

static bool
CheckIdentifier(AsmModuleCompiler &m, PropertyName *name, ParseNode *nameNode)
{
    if (name == m.cx()->names().arguments || name == m.cx()->names().eval)
        return m.fail("disallowed asm.js parameter name", nameNode);
    return true;
}

static bool
CheckModuleLevelName(AsmModuleCompiler &m, PropertyName *name, ParseNode *nameNode)
{
    if (!CheckIdentifier(m, name, nameNode))
        return false;

    if (name == m.maybeModuleName() ||
        name == m.maybeGlobalName() ||
        name == m.maybeImportName() ||
        m.lookupGlobal(name))
    {
        return m.fail("Duplicate names not allowed", nameNode);
    }

    return true;
}

static bool
CheckFunctionHead(AsmModuleCompiler &m, ParseNode *fn, ParseNode **stmtIter)
{
    if (FunctionObject(fn)->hasRest())
        return m.fail("rest args not allowed in asm.js", fn);

    *stmtIter = ListHead(FunctionStatementList(fn));
    return true;
}

static bool
CheckArgument(AsmModuleCompiler &m, ParseNode *arg, PropertyName **name)
{
    if (!arg->isKind(PNK_NAME) || arg->isUsed())
        return m.fail("overlapping argument names not allowed", arg);

    if (arg->expr())
        return m.fail("default arguments not allowed", arg);

    if (!CheckIdentifier(m, arg->name(), arg))
        return false;

    *name = arg->name();
    return true;
}

static bool
CheckModuleArgument(AsmModuleCompiler &m, ParseNode *arg, PropertyName **name)
{
    if (!CheckArgument(m, arg, name))
        return false;

    if (!CheckModuleLevelName(m, *name, arg))
        return false;

    return true;
}

static bool
CheckModuleArguments(AsmModuleCompiler &m, ParseNode *fn)
{
    unsigned numFormals;
    ParseNode *arg1 = FunctionArgsList(fn, &numFormals);
    ParseNode *arg2 = arg1 ? NextNode(arg1) : NULL;
    ParseNode *arg3 = arg2 ? NextNode(arg2) : NULL;

    if (numFormals > 3)
        return m.fail("asm.js modules takes at most 3 argument.", fn);

    PropertyName *arg1Name = NULL;
    if (numFormals >= 1 && !CheckModuleArgument(m, arg1, &arg1Name))
        return false;
    m.initGlobalName(arg1Name);

    PropertyName *arg2Name = NULL;
    if (numFormals >= 2 && !CheckModuleArgument(m, arg2, &arg2Name))
        return false;
    m.initImportName(arg2Name);

    PropertyName *arg3Name = NULL;
    if (numFormals >= 3 && !CheckModuleArgument(m, arg3, &arg3Name))
        return false;
    m.initBufferName(arg3Name);

    return true;
}

static bool
SkipUseAsmDirective(AsmModuleCompiler &m, ParseNode **stmtIter)
{
    ParseNode *firstStatement = *stmtIter;

    if (StringAtom(StatementExpressionExpr(firstStatement)) != m.cx()->names().useAsm)
        return m.fail("asm.js precludes other directives", firstStatement);

    *stmtIter = NextNode(firstStatement);
    return true;
}

static bool
CheckGlobalVariableInitConstant(AsmModuleCompiler &m, PropertyName *varName, ParseNode *initExpr)
{
    AsmNumLit literal = ExtractNumericLiteral(initExpr);
    AsmVarType type;
    switch (literal.which()) {
      case AsmNumLit::Fixnum:
      case AsmNumLit::NegativeInt:
      case AsmNumLit::BigUnsigned:
        type = AsmVarType::Int;
        break;
      case AsmNumLit::Double:
        type = AsmVarType::Double;
        break;
      case AsmNumLit::OutOfRangeInt:
        return m.fail("Global initializer is out of representable integer range", initExpr);
    }
    return m.addGlobalVar(varName, type, AsmGlobalVarInitConstant(literal.value()));
}

static bool
CheckTypeAnnotation(AsmModuleCompiler &m, ParseNode *coercion, AsmCoercionType *type,
                    ParseNode **coercedExpr = NULL)
{
    switch (coercion->getKind()) {
      case PNK_BITOR: {
        ParseNode *rhs = BinaryRight(coercion);

        if (!IsNumericLiteral(rhs))
            return m.fail("Must use |0 for argument/return coercion.", rhs);

        AsmNumLit rhsLiteral = ExtractNumericLiteral(rhs);
        if (rhsLiteral.which() != AsmNumLit::Fixnum || rhsLiteral.toInt32() != 0)
            return m.fail("Must use |0 for argument/return coercion.", rhs);

        *type = AsmCoercionType::Signed;
        if (coercedExpr)
            *coercedExpr = BinaryLeft(coercion);
        return true;
      }
      case PNK_POS: {
        *type = AsmCoercionType::Double;
        if (coercedExpr)
            *coercedExpr = UnaryKid(coercion);
        return true;
      }
      default:;
    }

    return m.fail("in coercion expression, the expression must be of the form +x or x|0", coercion);
}

static bool
CheckGlobalVariableInitImport(AsmModuleCompiler &m, PropertyName *varName, ParseNode *initExpr)
{
    AsmCoercionType coercionType;
    ParseNode *coercedExpr;
    if (!CheckTypeAnnotation(m, initExpr, &coercionType, &coercedExpr))
        return false;

    if (!coercedExpr->isKind(PNK_DOT))
        return m.fail("Bad global variable import expression", coercedExpr);

    ParseNode *base = DotBase(coercedExpr);
    PropertyName *field = DotMember(coercedExpr);

    if (!IsUseOfName(base, m.maybeImportName()))
        return m.fail("Expecting c.y where c is the import parameter", coercedExpr);

    return m.addGlobalVar(varName, coercionType, AsmGlobalVarImport(field, coercionType));
}

static bool
CheckNewArrayView(AsmModuleCompiler &m, PropertyName *varName, ParseNode *newExpr, bool first)
{
    ParseNode *ctorExpr = ListHead(newExpr);
    if (!ctorExpr->isKind(PNK_DOT))
        return m.fail("Only valid 'new' import is 'new global.XYZArray(buf)'", ctorExpr);

    ParseNode *base = DotBase(ctorExpr);
    PropertyName *field = DotMember(ctorExpr);

    if (!IsUseOfName(base, m.maybeGlobalName()))
        return m.fail("Expecting global.y", base);

    ParseNode *bufArg = NextNode(ctorExpr);
    if (!bufArg)
        return m.fail("Constructor needs an argument", ctorExpr);

    if (NextNode(bufArg) != NULL)
        return m.fail("Only one argument may be passed to a typed array constructor", bufArg);

    if (!bufArg->isKind(PNK_NAME))
        return m.fail("Argument to typed array constructor must be ArrayBuffer name", bufArg);

    if (bufArg->name() != m.maybeBufferName())
        return m.fail("Argument to typed array constructor must be ArrayBuffer name", bufArg);

    JSAtomState &names = m.cx()->names();
    ArrayBufferView::ViewType type;
    if (field == names.Int8Array)
        type = ArrayBufferView::TYPE_INT8;
    else if (field == names.Uint8Array)
        type = ArrayBufferView::TYPE_UINT8;
    else if (field == names.Int16Array)
        type = ArrayBufferView::TYPE_INT16;
    else if (field == names.Uint16Array)
        type = ArrayBufferView::TYPE_UINT16;
    else if (field == names.Int32Array)
        type = ArrayBufferView::TYPE_INT32;
    else if (field == names.Uint32Array)
        type = ArrayBufferView::TYPE_UINT32;
    else if (field == names.Float32Array)
        type = ArrayBufferView::TYPE_FLOAT32;
    else if (field == names.Float64Array)
        type = ArrayBufferView::TYPE_FLOAT64;
    else
        return m.fail("could not match typed array name", ctorExpr);

    return m.addArrayView(varName, type, field);
}

static bool
CheckGlobalDotImport(AsmModuleCompiler &m, PropertyName *varName, ParseNode *initExpr)
{
    ParseNode *base = DotBase(initExpr);
    PropertyName *field = DotMember(initExpr);

    if (base->isKind(PNK_DOT)) {
        ParseNode *global = DotBase(base);
        PropertyName *math = DotMember(base);
        if (!IsUseOfName(global, m.maybeGlobalName()) || math != m.cx()->names().Math)
            return m.fail("Expecting global.Math", base);

        Maybe<AsmMathBuiltin> mathBuiltin = m.lookupStandardLibraryMathName(field);
        if (!mathBuiltin)
            return m.fail("Does not match a standard Math builtin", initExpr);

        return m.addMathBuiltin(varName, mathBuiltin.get(), field);
    }

    if (IsUseOfName(base, m.maybeGlobalName())) {
        if (field == m.cx()->names().NaN)
            return m.addGlobalConstant(varName, js_NaN, field);
        if (field == m.cx()->names().Infinity)
            return m.addGlobalConstant(varName, js_PositiveInfinity, field);
        return m.fail("Does not match a standard global constant", initExpr);
    }

    if (IsUseOfName(base, m.maybeImportName()))
        return m.addFFI(varName, field);

    return m.fail("Expecting c.y where c is either the global or import parameter", initExpr);
}

static bool
CheckModuleGlobal(AsmModuleCompiler &m, ParseNode *var, bool first)
{
    if (!var->isKind(PNK_NAME))
        return m.fail("Import variable names must be unique", var);

    if (!CheckModuleLevelName(m, var->name(), var))
        return false;

    if (!var->expr())
        return m.fail("Module import needs initializer", var);

    ParseNode *initExpr = var->expr();

    if (IsNumericLiteral(initExpr))
        return CheckGlobalVariableInitConstant(m, var->name(), initExpr);

    if (initExpr->isKind(PNK_BITOR) || initExpr->isKind(PNK_POS))
        return CheckGlobalVariableInitImport(m, var->name(), initExpr);

    if (initExpr->isKind(PNK_NEW))
        return CheckNewArrayView(m, var->name(), initExpr, first);

    if (initExpr->isKind(PNK_DOT))
        return CheckGlobalDotImport(m, var->name(), initExpr);

    return m.fail("Unsupported import expression", initExpr);

}

static bool
CheckModuleGlobals(AsmModuleCompiler &m, ParseNode **stmtIter)
{
    ParseNode *stmt = SkipEmptyStatements(*stmtIter);

    bool first = true;

    for (; stmt && stmt->isKind(PNK_VAR); stmt = NextNonEmptyStatement(stmt)) {
        for (ParseNode *var = VarListHead(stmt); var; var = NextNode(var)) {
            if (!CheckModuleGlobal(m, var, first))
                return false;
            first = false;
        }
    }

    *stmtIter = stmt;
    return true;
}

static bool
CheckArgumentType(AsmModuleCompiler &m, ParseNode *fn, PropertyName *argName, ParseNode *stmt,
                  AsmVarType *type)
{
    if (!stmt || !stmt->isKind(PNK_SEMI) || !UnaryKid(stmt)->isKind(PNK_ASSIGN))
        return m.fail("expecting argument type declaration of the form 'arg = coercion;' where "
                      "coercion is one of ~~arg, +arg, arg|0, arg>>>0.", fn);

    ParseNode *initExpr = UnaryKid(stmt);
    ParseNode *arg = BinaryLeft(initExpr);
    ParseNode *coercion = BinaryRight(initExpr);

    if (!IsUseOfName(arg, argName))
        return m.fail("left-hand side of 'arg = expr;' decl must be the name of "
                      "an argument.", arg);

    ParseNode *coercedExpr;
    AsmCoercionType coercionType;
    if (!CheckTypeAnnotation(m, coercion, &coercionType, &coercedExpr))
        return false;

    if (!IsUseOfName(coercedExpr, argName))
        return m.fail("For argument type declaration, need 'x = coercion(x)'", coercedExpr);

    *type = coercionType;
    return true;
}

static bool
CheckArguments(AsmModuleCompiler &m, ParseNode *fn, MIRTypeVector *argTypes, ParseNode **stmtIter)
{
    ParseNode *stmt = *stmtIter;

    unsigned numFormals;
    ParseNode *argpn = FunctionArgsList(fn, &numFormals);

    HashSet<PropertyName*> dupSet(m.cx());
    if (!dupSet.init())
        return false;

    for (unsigned i = 0; i < numFormals; i++, argpn = NextNode(argpn), stmt = NextNode(stmt)) {
        PropertyName *argName;
        if (!CheckArgument(m, argpn, &argName))
            return false;

        if (dupSet.has(argName))
            return m.fail("asm.js arguments must have distinct names", argpn);
        if (!dupSet.putNew(argName))
            return false;

        AsmVarType argType;
        if (!CheckArgumentType(m, fn, argName, stmt, &argType))
            return false;

        if (!argTypes->append(argType.toMIRType()))
            return false;
    }

    *stmtIter = stmt;
    return true;
}

static bool
CheckReturnCoercion(AsmModuleCompiler &m, ParseNode *coercion, AsmRetType *returnType)
{
    if (IsNumericLiteral(coercion)) {
        switch (ExtractNumericLiteral(coercion).which()) {
          case AsmNumLit::BigUnsigned:
          case AsmNumLit::OutOfRangeInt:
            return m.fail("Returned literal is out of integer range", coercion);
          case AsmNumLit::Fixnum:
          case AsmNumLit::NegativeInt:
            *returnType = AsmRetType::Signed;
            break;
          case AsmNumLit::Double:
            *returnType = AsmRetType::Double;
            break;
        }
    } else {
        AsmCoercionType type;
        if (!CheckTypeAnnotation(m, coercion, &type))
            return false;
        *returnType = type;
    }

    return true;
}

static bool
CheckReturnType(AsmModuleCompiler &m, ParseNode *fn, AsmRetType *returnType)
{
    ParseNode *stmt = FunctionLastStatementOrNull(fn);
    if (!stmt || !stmt->isKind(PNK_RETURN) || !UnaryKid(stmt)) {
        *returnType = AsmRetType::Void;
        return true;
    }

    if (!CheckReturnCoercion(m, UnaryKid(stmt), returnType))
        return false;

    JS_ASSERT(returnType->widen().isExtern());
    return true;
}

static bool
CheckFunctionSignature(AsmModuleCompiler &m, ParseNode *fn)
{
    PropertyName *name = FunctionName(fn);
    if (!CheckModuleLevelName(m, name, fn))
        return false;

    ParseNode *stmtIter = NULL;

    if (!CheckFunctionHead(m, fn, &stmtIter))
        return false;

    MIRTypeVector argTypes(m.cx());
    if (!CheckArguments(m, fn, &argTypes, &stmtIter))
        return false;

    AsmRetType returnType;
    if (!CheckReturnType(m, fn, &returnType))
        return false;

    AsmModuleCompiler::Func func(fn, stmtIter, Move(argTypes), returnType);
    if (!m.addFunction(Move(func)))
        return false;

    return true;
}

static bool
CheckFunctionSignatures(AsmModuleCompiler &m, ParseNode **stmtIter)
{
    ParseNode *fn = SkipEmptyStatements(*stmtIter);

    for (; fn && fn->isKind(PNK_FUNCTION); fn = NextNonEmptyStatement(fn)) {
        if (!CheckFunctionSignature(m, fn))
            return false;
    }

    if (fn && fn->isKind(PNK_NOP))
        return m.fail("duplicate function names are not allowed", fn);

    *stmtIter = fn;
    return true;
}

static bool
SameSignature(const AsmModuleCompiler::Func &a, const AsmModuleCompiler::Func &b)
{
    if (a.numArgs() != b.numArgs() || a.returnType() != b.returnType())
        return false;
    for (unsigned i = 0; i < a.numArgs(); i++) {
        if (a.argType(i) != b.argType(i))
            return false;
    }
    return true;
}

static bool
CheckFuncPtrTable(AsmModuleCompiler &m, ParseNode *var)
{
    if (!var->isKind(PNK_NAME))
        return m.fail("Function-pointer table name must be unique", var);

    PropertyName *name = var->name();

    if (!CheckModuleLevelName(m, name, var))
        return false;

    if (!var->expr() || !var->expr()->isKind(PNK_ARRAY))
        return m.fail("Function-pointer table's initializer must be an array literal", var);

    ParseNode *arrayLiteral = var->expr();
    unsigned length = ListLength(arrayLiteral);

    if (!IsPowerOfTwo(length))
        return m.fail("Function-pointer table's length must be a power of 2", arrayLiteral);

    AsmModuleCompiler::FuncPtrVector funcPtrTableElems(m.cx());
    const AsmModuleCompiler::Func *firstFunction = NULL;

    for (ParseNode *elem = ListHead(arrayLiteral); elem; elem = NextNode(elem)) {
        if (!elem->isKind(PNK_NAME))
            return m.fail("Function-pointer table's elements must be names of functions", elem);

        PropertyName *funcName = elem->name();
        const AsmModuleCompiler::Func *func = m.lookupFunction(funcName);
        if (!func)
            return m.fail("Function-pointer table's elements must be names of functions", elem);

        if (firstFunction) {
            if (!SameSignature(*firstFunction, *func))
                return m.fail("All functions in table must have same signature", elem);
        } else {
            firstFunction = func;
        }

        if (!funcPtrTableElems.append(func))
            return false;
    }

    return m.addFuncPtrTable(name, Move(funcPtrTableElems));
}

static bool
CheckFuncPtrTables(AsmModuleCompiler &m, ParseNode **stmtIter)
{
    ParseNode *stmt = SkipEmptyStatements(*stmtIter);

    for (; stmt && stmt->isKind(PNK_VAR); stmt = NextNonEmptyStatement(stmt)) {
        for (ParseNode *var = VarListHead(stmt); var; var = NextNode(var)) {
            if (!CheckFuncPtrTable(m, var))
                return false;
        }
    }

    *stmtIter = stmt;
    return true;
}

static bool
CheckModuleExportFunction(AsmModuleCompiler &m, ParseNode *returnExpr)
{
    if (!returnExpr->isKind(PNK_NAME))
        return m.fail("an asm.js export statement must be of the form 'return name'", returnExpr);

    PropertyName *functionName = returnExpr->name();

    if (!m.lookupFunction(functionName))
        return m.fail("exported function name not found", returnExpr);

    m.setExportedFunction(functionName);
    return true;
}

static bool
CheckModuleExportObject(AsmModuleCompiler &m, ParseNode *object)
{
    JS_ASSERT(object->isKind(PNK_OBJECT));

    for (ParseNode *pn = ListHead(object); pn; pn = NextNode(pn)) {
        if (!IsNormalObjectField(m.cx(), pn))
            return m.fail("Only normal object properties may be used in the export object literal", pn);

        PropertyName *field = ObjectNormalFieldName(m.cx(), pn);

        ParseNode *initExpr = ObjectFieldInitializer(pn);
        if (!initExpr->isKind(PNK_NAME))
            return m.fail("Initializer of exported object literal must be name of function", initExpr);

        PropertyName *functionName = initExpr->name();

        if (!m.lookupFunction(functionName))
            return m.fail("exported function name not found", initExpr);

        if (!m.addToExportObject(field, functionName))
            return false;
    }

    return true;
}

static bool
CheckModuleExports(AsmModuleCompiler &m, ParseNode *fn, ParseNode **stmtIter)
{
    ParseNode *returnNode = SkipEmptyStatements(*stmtIter);

    if (!returnNode || !returnNode->isKind(PNK_RETURN))
        return m.fail("asm.js must end with a return export statement", fn);

    ParseNode *returnExpr = UnaryKid(returnNode);

    if (!returnExpr)
        return m.fail("an asm.js export statement must return something", returnExpr);

    if (returnExpr->isKind(PNK_OBJECT)) {
        if (!CheckModuleExportObject(m, returnExpr))
            return false;
    } else {
        if (!CheckModuleExportFunction(m, returnExpr))
            return false;
    }

    *stmtIter = NextNonEmptyStatement(returnNode);
    return true;
}

static bool
CheckExpr(AsmFunctionCompiler &f, ParseNode *expr, AsmUse use, MDefinition **def, AsmType *type);

static bool
CheckNumericLiteral(AsmFunctionCompiler &f, ParseNode *num, MDefinition **def, AsmType *type)
{
    JS_ASSERT(IsNumericLiteral(num));
    AsmNumLit literal = ExtractNumericLiteral(num);

    switch (literal.which()) {
      case AsmNumLit::Fixnum:
      case AsmNumLit::NegativeInt:
      case AsmNumLit::BigUnsigned:
      case AsmNumLit::Double:
        break;
      case AsmNumLit::OutOfRangeInt:
        return f.fail("Numeric literal out of representable integer range", num);
    }

    *type = literal.type();
    *def = f.constant(literal.value());
    return true;
}

static bool
CheckVarRef(AsmFunctionCompiler &f, ParseNode *varRef, MDefinition **def, AsmType *type)
{
    PropertyName *name = varRef->name();

    if (const AsmFunctionCompiler::Local *local = f.lookupLocal(name)) {
        *def = f.getLocalDef(*local);
        *type = local->type.widen();
        return true;
    }

    if (const AsmModuleCompiler::Global *global = f.lookupGlobal(name)) {
        switch (global->which()) {
          case AsmModuleCompiler::Global::Constant:
            *def = f.constant(DoubleValue(global->constant()));
            *type = AsmType::Double;
            break;
          case AsmModuleCompiler::Global::Variable:
            *def = f.loadGlobalVar(*global);
            *type = global->varType().widen();
            break;
          case AsmModuleCompiler::Global::Function:
          case AsmModuleCompiler::Global::FFI:
          case AsmModuleCompiler::Global::MathBuiltin:
          case AsmModuleCompiler::Global::FuncPtrTable:
          case AsmModuleCompiler::Global::ArrayView:
            return f.fail("Global may not be accessed by ordinary expressions", varRef);
        }
        return true;
    }

    return f.fail("Name not found in scope", varRef);
}

static bool
CheckArrayAccess(AsmFunctionCompiler &f, ParseNode *elem, ArrayBufferView::ViewType *viewType,
                 uint32_t *mask, MDefinition **def)
{
    ParseNode *viewName = ElemBase(elem);
    ParseNode *indexExpr = ElemIndex(elem);

    if (!viewName->isKind(PNK_NAME))
        return f.fail("Left-hand side of x[y] must be a name", viewName);

    const AsmModuleCompiler::Global *global = f.lookupGlobal(viewName->name());
    if (!global || global->which() != AsmModuleCompiler::Global::ArrayView)
        return f.fail("Left-hand side of x[y] must be typed array view name", viewName);

    *viewType = global->viewType();

    uint32_t pointer;
    if (IsLiteralUint32(indexExpr, &pointer)) {
        pointer <<= TypedArrayShift(*viewType);
        if (!f.m().attemptUseConstantPointer(pointer))
            return f.fail("Constant pointer out of heap mask range", indexExpr);

        *mask = UINT32_MAX;
        *def = f.constant(Int32Value(pointer));
        return true;
    }

    ParseNode *maskExpr;
    if (indexExpr->isKind(PNK_RSH)) {
        ParseNode *shiftNode = BinaryRight(indexExpr);

        uint32_t shift;
        if (!IsLiteralUint32(shiftNode, &shift) || shift != TypedArrayShift(*viewType))
            return f.fail("The shift amount must be a constant matching the array "
                          "element size", shiftNode);

        maskExpr = BinaryLeft(indexExpr);
    } else {
        if (TypedArrayShift(*viewType) != 0)
            return f.fail("The shift amount is 0 so this must be a Int8/Uint8 array", indexExpr);

        maskExpr = indexExpr;
    }

    if (!maskExpr->isKind(PNK_BITAND))
        return f.fail("Expecting & mask in shifted expression", maskExpr);

    ParseNode *maskNode = BinaryRight(maskExpr);
    ParseNode *pointerNode = BinaryLeft(maskExpr);

    uint32_t lengthMask;
    if (!IsLiteralUint32(maskNode, &lengthMask) || !f.m().attemptUseLengthMask(lengthMask))
        return f.fail("Expecting rhs of & mask to have the same value as other masks and "
                      "subsume all preceding constant pointer loads", maskNode);

    MDefinition *pointerDef;
    AsmType pointerType;
    if (!CheckExpr(f, pointerNode, AsmUse::ToInt32, &pointerDef, &pointerType))
        return false;

    if (!pointerType.isIntish())
        return f.fail("Pointer input must be intish", pointerNode);

    // For a typed array access, there are two masks we need to perform
    // (that we fold into one 'and' operation):
    //  1. wrap around the length to keep the access in-bounds.
    //  2. mask off the low bits to account for clearing effect of a right
    //     shift followed by the left shift implicit in the array access.
    //     E.g., H32[i>>2] loses the low two bits.
    *mask = lengthMask & ~((uint32_t(1) << TypedArrayShift(*viewType)) - 1);
    *def = pointerDef;
    return true;
}

static bool
CheckArrayLoad(AsmFunctionCompiler &f, ParseNode *elem, MDefinition **def, AsmType *type)
{
    ArrayBufferView::ViewType viewType;
    uint32_t mask;
    MDefinition *pointerDef;
    if (!CheckArrayAccess(f, elem, &viewType, &mask, &pointerDef))
        return false;

    *def = f.loadHeap(viewType, mask, pointerDef);
    *type = TypedArrayLoadType(viewType);
    return true;
}

static bool
CheckStoreArray(AsmFunctionCompiler &f, ParseNode *lhs, ParseNode *rhs, MDefinition **def, AsmType *type)
{
    ArrayBufferView::ViewType viewType;
    uint32_t mask;
    MDefinition *pointerDef;
    if (!CheckArrayAccess(f, lhs, &viewType, &mask, &pointerDef))
        return false;

    MDefinition *rhsDef;
    AsmType rhsType;
    if (!CheckExpr(f, rhs, AsmUse::NoCoercion, &rhsDef, &rhsType))
        return false;

    switch (TypedArrayStoreType(viewType)) {
      case ArrayStore_Intish:
        if (!rhsType.isIntish())
            return f.fail("Right-hand side of store must be intish", lhs);
        break;
      case ArrayStore_Double:
        if (rhsType != AsmType::Double)
            return f.fail("Right-hand side of store must be double", lhs);
        break;
    }

    f.storeHeap(viewType, mask, pointerDef, rhsDef);

    *def = rhsDef;
    *type = rhsType;
    return true;
}

static bool
CheckAssignName(AsmFunctionCompiler &f, ParseNode *lhs, ParseNode *rhs, MDefinition **def, AsmType *type)
{
    PropertyName *name = lhs->name();

    MDefinition *rhsDef;
    AsmType rhsType;
    if (!CheckExpr(f, rhs, AsmUse::NoCoercion, &rhsDef, &rhsType))
        return false;

    if (const AsmFunctionCompiler::Local *lhsVar = f.lookupLocal(name)) {
        if (!(rhsType <= lhsVar->type))
            return f.fail("Right-hand side of assignment must be subtype of left-hand side", lhs);
        f.assign(*lhsVar, rhsDef);
    } else if (const AsmModuleCompiler::Global *global = f.lookupGlobal(name)) {
        if (global->which() != AsmModuleCompiler::Global::Variable)
            return f.fail("Only global variables are mutable, not FFI functions etc", lhs);
        if (!(rhsType <= global->varType()))
            return f.fail("Right-hand side of assignment must be subtype of left-hand side", lhs);
        f.storeGlobalVar(*global, rhsDef);
    } else {
        return f.fail("Variable name in left-hand side of assignment not found", lhs);
    }

    *def = rhsDef;
    *type = rhsType;
    return true;
}

static bool
CheckAssign(AsmFunctionCompiler &f, ParseNode *assign, MDefinition **def, AsmType *type)
{
    JS_ASSERT(assign->isKind(PNK_ASSIGN));
    ParseNode *lhs = BinaryLeft(assign);
    ParseNode *rhs = BinaryRight(assign);

    if (lhs->getKind() == PNK_ELEM)
        return CheckStoreArray(f, lhs, rhs, def, type);

    if (lhs->getKind() == PNK_NAME)
        return CheckAssignName(f, lhs, rhs, def, type);

    return f.fail("Left-hand side of assignment must be a variable or heap", assign);
}

static bool
CheckMathIMul(AsmFunctionCompiler &f, ParseNode *call, MDefinition **def, AsmType *type)
{
    if (CallArgListLength(call) != 2)
        return f.fail("Math.imul must be passed 2 arguments", call);

    ParseNode *lhs = CallArgList(call);
    ParseNode *rhs = NextNode(lhs);

    MDefinition *lhsDef;
    AsmType lhsType;
    if (!CheckExpr(f, lhs, AsmUse::ToInt32, &lhsDef, &lhsType))
        return false;

    MDefinition *rhsDef;
    AsmType rhsType;
    if (!CheckExpr(f, rhs, AsmUse::ToInt32, &rhsDef, &rhsType))
        return false;

    if (!lhsType.isIntish() || !rhsType.isIntish())
        return f.fail("Math.imul calls must be passed 2 intish arguments", call);

    *def = f.mul(lhsDef, rhsDef, MIRType_Int32, MMul::Integer);
    *type = AsmType::Signed;
    return true;
}

static bool
CheckMathAbs(AsmFunctionCompiler &f, ParseNode *call, MDefinition **def, AsmType *type)
{
    if (CallArgListLength(call) != 1)
        return f.fail("Math.abs must be passed 1 argument", call);

    ParseNode *arg = CallArgList(call);

    MDefinition *argDef;
    AsmType argType;
    if (!CheckExpr(f, arg, AsmUse::ToNumber, &argDef, &argType))
        return false;

    if (argType.isSigned()) {
        *def = f.unary<MAbs>(argDef, MIRType_Int32);
        *type = AsmType::Unsigned;
        return true;
    }

    if (argType.isDoublish()) {
        *def = f.unary<MAbs>(argDef, MIRType_Double);
        *type = AsmType::Double;
        return true;
    }

    return f.fail("Math.abs must be passed either a signed or doublish argument", call);
}

static bool
CheckCallArgs(AsmFunctionCompiler &f, ParseNode *callNode, AsmUse use, AsmFunctionCompiler::Args *args)
{
    f.startCallArgs(args);

    ParseNode *argNode = CallArgList(callNode);
    for (unsigned i = 0; i < CallArgListLength(callNode); i++, argNode = NextNode(argNode)) {
        MDefinition *argDef;
        AsmType argType;
        if (!CheckExpr(f, argNode, use, &argDef, &argType))
            return false;

        if (argType.isVoid())
            return f.fail("Void cannot be passed as an argument", argNode);

        if (!f.passArg(argDef, argType, args))
            return false;
    }

    f.finishCallArgs(args);
    return true;
}

static bool
CheckInternalCall(AsmFunctionCompiler &f, ParseNode *callNode, const AsmModuleCompiler::Func &callee,
                  MDefinition **def, AsmType *type)
{
    AsmFunctionCompiler::Args args(f);

    if (!CheckCallArgs(f, callNode, AsmUse::NoCoercion, &args))
        return false;

    if (args.length() != callee.numArgs()) {
        fprintf(stderr, "has %d\n", args.length());
        fprintf(stderr, "given %d\n", callee.numArgs());
        return f.fail("Wrong number of arguments", callNode);
    }

    for (unsigned i = 0; i < args.length(); i++) {
        if (!(args.type(i) <= callee.argType(i)))
            return f.fail("actual arg type is not subtype of formal arg type", callNode);
    }

    *def = f.internalCall(callee, args);
    *type = callee.returnType().widen();
    return true;
}

static bool
CheckFuncPtrCall(AsmFunctionCompiler &f, ParseNode *callNode, MDefinition **def, AsmType *type)
{
    ParseNode *callee = CallCallee(callNode);
    ParseNode *elemBase = ElemBase(callee);
    ParseNode *indexExpr = ElemIndex(callee);

    if (!elemBase->isKind(PNK_NAME))
        return f.fail("Expecting name (of function-pointer array)", elemBase);

    const AsmModuleCompiler::FuncPtrTable *table = f.m().lookupFuncPtrTable(elemBase->name());
    if (!table)
        return f.fail("Expecting name of function-pointer array", elemBase);

    if (!indexExpr->isKind(PNK_BITAND))
        return f.fail("Function-pointer table index expression needs & mask", indexExpr);

    ParseNode *indexNode = BinaryLeft(indexExpr);
    ParseNode *maskNode = BinaryRight(indexExpr);

    uint32_t mask;
    if (!IsLiteralUint32(maskNode, &mask) || mask != table->mask())
        return f.fail("Function-pointer table index mask must be the table length minus 1", maskNode);

    MDefinition *indexDef;
    AsmType indexType;
    if (!CheckExpr(f, indexNode, AsmUse::ToInt32, &indexDef, &indexType))
        return false;

    if (!indexType.isIntish())
        return f.fail("Function-pointer table index expression must be intish", indexNode);

    AsmFunctionCompiler::Args args(f);

    if (!CheckCallArgs(f, callNode, AsmUse::NoCoercion, &args))
        return false;

    if (args.length() != table->sig().numArgs())
        return f.fail("Wrong number of arguments", callNode);

    for (unsigned i = 0; i < args.length(); i++) {
        if (!(args.type(i) <= table->sig().argType(i)))
            return f.fail("actual arg type is not subtype of formal arg type", callNode);
    }

    *def = f.funcPtrCall(*table, indexDef, args);
    *type = table->sig().returnType().widen();
    return true;
}

static bool
CheckFFICall(AsmFunctionCompiler &f, ParseNode *callNode, AsmFFIIndex ffi, AsmUse use,
             MDefinition **def, AsmType *type)
{
    AsmFunctionCompiler::Args args(f);

    if (!CheckCallArgs(f, callNode, AsmUse::NoCoercion, &args))
        return false;

    MIRTypeVector argMIRTypes(f.cx());
    for (unsigned i = 0; i < args.length(); i++) {
        if (!args.type(i).isExtern())
            return f.fail("args to FFI call must be <: extern", callNode);
        if (!argMIRTypes.append(args.type(i).toMIRType()))
            return false;
    }

    AsmExitIndex exitIndex;
    if (!f.m().addExit(ffi, CallCallee(callNode)->name(), Move(argMIRTypes), use, &exitIndex))
        return false;

    *def = f.ffiCall(exitIndex, args, use.toMIRType());
    *type = use.toFFIReturnType();
    return true;
}

static bool
CheckMathBuiltinCall(AsmFunctionCompiler &f, ParseNode *callNode, AsmMathBuiltin mathBuiltin,
                     MDefinition **def, AsmType *type)
{
    unsigned arity;
    void *callee;
    switch (mathBuiltin) {
      case AsmMathBuiltin_imul:  return CheckMathIMul(f, callNode, def, type);
      case AsmMathBuiltin_abs:   return CheckMathAbs(f, callNode, def, type);
      case AsmMathBuiltin_sin:   arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, sin);     break;
      case AsmMathBuiltin_cos:   arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, cos);     break;
      case AsmMathBuiltin_tan:   arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, tan);     break;
      case AsmMathBuiltin_asin:  arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, asin);    break;
      case AsmMathBuiltin_acos:  arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, acos);    break;
      case AsmMathBuiltin_atan:  arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, atan);    break;
      case AsmMathBuiltin_ceil:  arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, ceil);    break;
      case AsmMathBuiltin_floor: arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, floor);   break;
      case AsmMathBuiltin_exp:   arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, exp);     break;
      case AsmMathBuiltin_log:   arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, log);     break;
      case AsmMathBuiltin_sqrt:  arity = 1; callee = JS_FUNC_TO_DATA_PTR(void*, sqrt);    break;
      case AsmMathBuiltin_pow:   arity = 2; callee = JS_FUNC_TO_DATA_PTR(void*, ecmaPow); break;
      case AsmMathBuiltin_atan2: arity = 2; callee = JS_FUNC_TO_DATA_PTR(void*, atan2);   break;
    }

    AsmFunctionCompiler::Args args(f);

    if (!CheckCallArgs(f, callNode, AsmUse::ToNumber, &args))
        return false;

    if (args.length() != arity)
        return f.fail("Math builtin call passed wrong number of argument", callNode);

    for (unsigned i = 0; i < args.length(); i++) {
        if (!args.type(i).isDoublish())
            return f.fail("Builtin calls must be passed 1 doublish argument", callNode);
    }

    *def = f.builtinCall(callee, args, MIRType_Double);
    *type = AsmType::Double;
    return true;
}

static bool
CheckCall(AsmFunctionCompiler &f, ParseNode *call, AsmUse use, MDefinition **def, AsmType *type)
{
    ParseNode *callee = CallCallee(call);

    if (callee->isKind(PNK_ELEM))
        return CheckFuncPtrCall(f, call, def, type);

    if (!callee->isKind(PNK_NAME))
        return f.fail("Unexpected callee expression type", callee);

    if (const AsmModuleCompiler::Global *global = f.lookupGlobal(callee->name())) {
        switch (global->which()) {
          case AsmModuleCompiler::Global::Function:
            return CheckInternalCall(f, call, f.m().function(global->funcIndex()), def, type);
          case AsmModuleCompiler::Global::FFI:
            return CheckFFICall(f, call, global->ffiIndex(), use, def, type);
          case AsmModuleCompiler::Global::MathBuiltin:
            return CheckMathBuiltinCall(f, call, global->mathBuiltin(), def, type);
          case AsmModuleCompiler::Global::Constant:
          case AsmModuleCompiler::Global::Variable:
          case AsmModuleCompiler::Global::FuncPtrTable:
          case AsmModuleCompiler::Global::ArrayView:
            return f.fail("Global is not callable function", callee);
        }
    }

    return f.fail("Call target not found in global scope", callee);
}

static bool
CheckPos(AsmFunctionCompiler &f, ParseNode *pos, MDefinition **def, AsmType *type)
{
    JS_ASSERT(pos->isKind(PNK_POS));
    ParseNode *operand = UnaryKid(pos);

    MDefinition *operandDef;
    AsmType operandType;
    if (!CheckExpr(f, operand, AsmUse::ToNumber, &operandDef, &operandType))
        return false;

    if (operandType.isSigned())
        *def = f.unary<MToDouble>(operandDef);
    else if (operandType.isUnsigned())
        *def = f.unary<MAsmUnsignedToDouble>(operandDef);
    else if (operandType.isDoublish())
        *def = operandDef;
    else
        return f.fail("Operand to unary + must be signed, unsigned or doubleish", operand);

    *type = AsmType::Double;
    return true;
}

static bool
CheckNot(AsmFunctionCompiler &f, ParseNode *expr, MDefinition **def, AsmType *type)
{
    JS_ASSERT(expr->isKind(PNK_NOT));
    ParseNode *operand = UnaryKid(expr);

    MDefinition *operandDef;
    AsmType operandType;
    if (!CheckExpr(f, operand, AsmUse::NoCoercion, &operandDef, &operandType))
        return false;

    if (!operandType.isInt())
        return f.fail("Operand to ! must be int", operand);

    *def = f.unary<MNot>(operandDef);
    *type = AsmType::Int;
    return true;
}

static bool
CheckNeg(AsmFunctionCompiler &f, ParseNode *expr, MDefinition **def, AsmType *type)
{
    JS_ASSERT(expr->isKind(PNK_NEG));
    ParseNode *operand = UnaryKid(expr);

    MDefinition *operandDef;
    AsmType operandType;
    if (!CheckExpr(f, operand, AsmUse::ToNumber, &operandDef, &operandType))
        return false;

    if (operandType.isInt()) {
        *def = f.unary<MAsmNeg>(operandDef, MIRType_Int32);
        *type = AsmType::Intish;
        return true;
    }

    if (operandType.isDoublish()) {
        *def = f.unary<MAsmNeg>(operandDef, MIRType_Double);
        *type = AsmType::Double;
        return true;
    }

    return f.fail("Operand to unary - must be an int", operand);
}

static bool
CheckBitNot(AsmFunctionCompiler &f, ParseNode *neg, MDefinition **def, AsmType *type)
{
    JS_ASSERT(neg->isKind(PNK_BITNOT));
    ParseNode *operand = UnaryKid(neg);

    if (operand->isKind(PNK_BITNOT)) {
        MDefinition *operandDef;
        AsmType operandType;
        if (!CheckExpr(f, UnaryKid(operand), AsmUse::NoCoercion, &operandDef, &operandType))
            return false;

        if (operandType.isDouble()) {
            *def = f.unary<MTruncateToInt32>(operandDef);
            *type = AsmType::Signed;
            return true;
        }
    }

    MDefinition *operandDef;
    AsmType operandType;
    if (!CheckExpr(f, operand, AsmUse::ToInt32, &operandDef, &operandType))
        return false;

    if (!operandType.isIntish())
        return f.fail("Operand to ~ must be intish", operand);

    *def = f.bitwise<MBitNot>(operandDef);
    *type = AsmType::Signed;
    return true;
}

static bool
CheckComma(AsmFunctionCompiler &f, ParseNode *comma, AsmUse use, MDefinition **def, AsmType *type)
{
    JS_ASSERT(comma->isKind(PNK_COMMA));
    ParseNode *operands = ListHead(comma);

    ParseNode *pn = operands;
    for (; NextNode(pn); pn = NextNode(pn)) {
        if (!CheckExpr(f, pn, AsmUse::NoCoercion, def, type))
            return false;
    }

    if (!CheckExpr(f, pn, use, def, type))
        return false;

    return true;
}

static bool
CheckConditional(AsmFunctionCompiler &f, ParseNode *ternary, MDefinition **def, AsmType *type)
{
    JS_ASSERT(ternary->isKind(PNK_CONDITIONAL));
    ParseNode *cond = TernaryKid1(ternary);
    ParseNode *thenExpr = TernaryKid2(ternary);
    ParseNode *elseExpr = TernaryKid3(ternary);

    MDefinition *condDef;
    AsmType condType;
    if (!CheckExpr(f, cond, AsmUse::NoCoercion, &condDef, &condType))
        return false;

    if (!condType.isInt())
        return f.fail("Condition of if must be boolish", cond);

    MBasicBlock *thenBlock, *elseBlock;
    f.branchAndStartThen(condDef, &thenBlock, &elseBlock);

    MDefinition *thenDef;
    AsmType thenType;
    if (!CheckExpr(f, thenExpr, AsmUse::NoCoercion, &thenDef, &thenType))
        return false;

    f.pushPhiInput(thenDef);
    MBasicBlock *thenEnd = f.switchToElse(elseBlock);

    MDefinition *elseDef;
    AsmType elseType;
    if (!CheckExpr(f, elseExpr, AsmUse::NoCoercion, &elseDef, &elseType))
        return false;

    f.pushPhiInput(elseDef);
    f.joinIfElse(thenEnd);
    *def = f.popPhiOutput();

    if (thenType.isInt() && elseType.isInt())
        *type = AsmType::Int;
    else if (thenType.isDouble() && elseType.isDouble())
        *type = AsmType::Double;
    else
        return f.fail("Then/else branches of conditional must both be int or double", ternary);

    return true;
}

static bool
CheckFloatMultiply(AsmFunctionCompiler &f, ParseNode *star, MDefinition **def, AsmType *type)
{
    JS_ASSERT(star->isKind(PNK_STAR));
    ParseNode *lhs = BinaryLeft(star);
    ParseNode *rhs = BinaryRight(star);

    MDefinition *lhsDef, *rhsDef;
    AsmType lhsType, rhsType;
    if (!CheckExpr(f, lhs, AsmUse::ToNumber, &lhsDef, &lhsType))
        return false;
    if (!CheckExpr(f, rhs, AsmUse::ToNumber, &rhsDef, &rhsType))
        return false;

    if (!lhsType.isDoublish() || !rhsType.isDoublish())
        return f.fail("Arguments to * must both be doubles", star);

    *def = f.mul(lhsDef, rhsDef, MIRType_Double, MMul::Normal);
    *type = AsmType::Double;
    return true;
}

static bool
CheckAddOrSub(AsmFunctionCompiler &f, ParseNode *expr, AsmUse use, MDefinition **def, AsmType *type)
{
    JS_ASSERT(expr->isKind(PNK_ADD) || expr->isKind(PNK_SUB));
    ParseNode *lhs = BinaryLeft(expr);
    ParseNode *rhs = BinaryRight(expr);

    AsmUse argUse;
    unsigned addOrSubCount = 1;
    if (use.which() == AsmUse::AddOrSub) {
        if (++use.addOrSubCount() > (1<<20))
            return f.fail("Too many + or - without intervening coercion", expr);
        argUse = use;
    } else {
        argUse = AsmUse(&addOrSubCount);
    }

    MDefinition *lhsDef, *rhsDef;
    AsmType lhsType, rhsType;
    if (!CheckExpr(f, lhs, argUse, &lhsDef, &lhsType))
        return false;
    if (!CheckExpr(f, rhs, argUse, &rhsDef, &rhsType))
        return false;

    if (lhsType.isInt() && rhsType.isInt()) {
        *def = expr->isKind(PNK_ADD)
               ? f.binary<MAdd>(lhsDef, rhsDef, MIRType_Int32)
               : f.binary<MSub>(lhsDef, rhsDef, MIRType_Int32);
        if (use.which() == AsmUse::AddOrSub)
            *type = AsmType::Int;
        else
            *type = AsmType::Intish;
        return true;
    }

    if (expr->isKind(PNK_ADD) && lhsType.isDouble() && rhsType.isDouble()) {
        *def = f.binary<MAdd>(lhsDef, rhsDef, MIRType_Double);
        *type = AsmType::Double;
        return true;
    }

    if (expr->isKind(PNK_SUB) && lhsType.isDoublish() && rhsType.isDoublish()) {
        *def = f.binary<MSub>(lhsDef, rhsDef, MIRType_Double);
        *type = AsmType::Double;
        return true;
    }

    return f.fail("Arguments to + or - must both be ints or doubles", expr);
}

static bool
CheckDivOrMod(AsmFunctionCompiler &f, ParseNode *expr, MDefinition **def, AsmType *type)
{
    JS_ASSERT(expr->isKind(PNK_DIV) || expr->isKind(PNK_MOD));
    ParseNode *lhs = BinaryLeft(expr);
    ParseNode *rhs = BinaryRight(expr);

    MDefinition *lhsDef, *rhsDef;
    AsmType lhsType, rhsType;
    if (!CheckExpr(f, lhs, AsmUse::ToNumber, &lhsDef, &lhsType))
        return false;
    if (!CheckExpr(f, rhs, AsmUse::ToNumber, &rhsDef, &rhsType))
        return false;

    if (lhsType.isDoublish() && rhsType.isDoublish()) {
        *def = expr->isKind(PNK_DIV)
               ? f.binary<MDiv>(lhsDef, rhsDef, MIRType_Double)
               : f.binary<MMod>(lhsDef, rhsDef, MIRType_Double);
        *type = AsmType::Double;
        return true;
    }

    if (lhsType.isSigned() && rhsType.isSigned()) {
        if (expr->isKind(PNK_DIV)) {
            *def = f.binary<MDiv>(lhsDef, rhsDef, MIRType_Int32);
            *type = AsmType::Intish;
        } else {
            *def = f.binary<MMod>(lhsDef, rhsDef, MIRType_Int32);
            *type = AsmType::Int;
        }
        return true;
    }

    if (lhsType.isUnsigned() && rhsType.isUnsigned()) {
        if (expr->isKind(PNK_DIV)) {
            *def = f.binary<MAsmUDiv>(lhsDef, rhsDef);
            *type = AsmType::Intish;
        } else {
            *def = f.binary<MAsmUMod>(lhsDef, rhsDef);
            *type = AsmType::Int;
        }
        return true;
    }

    return f.fail("Arguments to / or % must both be double, signed, or unsigned", expr);
}

static bool
CheckComparison(AsmFunctionCompiler &f, ParseNode *comp, MDefinition **def, AsmType *type)
{
    JS_ASSERT(comp->isKind(PNK_LT) || comp->isKind(PNK_LE) || comp->isKind(PNK_GT) ||
              comp->isKind(PNK_GE) || comp->isKind(PNK_EQ) || comp->isKind(PNK_NE));
    ParseNode *lhs = BinaryLeft(comp);
    ParseNode *rhs = BinaryRight(comp);

    MDefinition *lhsDef, *rhsDef;
    AsmType lhsType, rhsType;
    if (!CheckExpr(f, lhs, AsmUse::NoCoercion, &lhsDef, &lhsType))
        return false;
    if (!CheckExpr(f, rhs, AsmUse::NoCoercion, &rhsDef, &rhsType))
        return false;

    if ((lhsType.isSigned() && rhsType.isSigned()) || (lhsType.isUnsigned() && rhsType.isUnsigned())) {
        MCompare::CompareType compareType = lhsType.isUnsigned()
                                            ? MCompare::Compare_UInt32
                                            : MCompare::Compare_Int32;
        *def = f.compare(lhsDef, rhsDef, comp->getOp(), compareType);
        *type = AsmType::Int;
        return true;
    }

    if (lhsType.isDouble() && rhsType.isDouble()) {
        *def = f.compare(lhsDef, rhsDef, comp->getOp(), MCompare::Compare_Double);
        *type = AsmType::Int;
        return true;
    }

    return f.fail("The arguments to a comparison must both be signed, unsigned or doubles", comp);
}

static bool
CheckBitwise(AsmFunctionCompiler &f, ParseNode *bitwise, MDefinition **def, AsmType *type)
{
    ParseNode *lhs = BinaryLeft(bitwise);
    ParseNode *rhs = BinaryRight(bitwise);

    int32_t identityElement;
    bool onlyOnRight;
    switch (bitwise->getKind()) {
      case PNK_BITOR:  identityElement = 0;  onlyOnRight = false; *type = AsmType::Signed;   break;
      case PNK_BITAND: identityElement = -1; onlyOnRight = false; *type = AsmType::Signed;   break;
      case PNK_BITXOR: identityElement = 0;  onlyOnRight = false; *type = AsmType::Signed;   break;
      case PNK_LSH:    identityElement = 0;  onlyOnRight = true;  *type = AsmType::Signed;   break;
      case PNK_RSH:    identityElement = 0;  onlyOnRight = true;  *type = AsmType::Signed;   break;
      case PNK_URSH:   identityElement = 0;  onlyOnRight = true;  *type = AsmType::Unsigned; break;
      default: JS_NOT_REACHED("not a bitwise op");
    }

    if (!onlyOnRight && IsBits32(lhs, identityElement)) {
        AsmType rhsType;
        if (!CheckExpr(f, rhs, AsmUse::ToInt32, def, &rhsType))
            return false;
        if (!rhsType.isIntish())
            return f.fail("Operands to bitwise ops must be intish", bitwise);
        return true;
    }

    if (IsBits32(rhs, identityElement)) {
        AsmType lhsType;
        if (!CheckExpr(f, lhs, AsmUse::ToInt32, def, &lhsType))
            return false;
        if (!lhsType.isIntish())
            return f.fail("Operands to bitwise ops must be intish", bitwise);
        return true;
    }

    MDefinition *lhsDef;
    AsmType lhsType;
    if (!CheckExpr(f, lhs, AsmUse::ToInt32, &lhsDef, &lhsType))
        return false;

    MDefinition *rhsDef;
    AsmType rhsType;
    if (!CheckExpr(f, rhs, AsmUse::ToInt32, &rhsDef, &rhsType))
        return false;

    if (!lhsType.isIntish() || !rhsType.isIntish())
        return f.fail("Operands to bitwise ops must be intish", bitwise);

    switch (bitwise->getKind()) {
      case PNK_BITOR:  *def = f.bitwise<MBitOr>(lhsDef, rhsDef); break;
      case PNK_BITAND: *def = f.bitwise<MBitAnd>(lhsDef, rhsDef); break;
      case PNK_BITXOR: *def = f.bitwise<MBitXor>(lhsDef, rhsDef); break;
      case PNK_LSH:    *def = f.bitwise<MLsh>(lhsDef, rhsDef); break;
      case PNK_RSH:    *def = f.bitwise<MRsh>(lhsDef, rhsDef); break;
      case PNK_URSH:   *def = f.bitwise<MUrsh>(lhsDef, rhsDef); break;
      default: JS_NOT_REACHED("not a bitwise op");
    }

    return true;
}

static bool
CheckExpr(AsmFunctionCompiler &f, ParseNode *expr, AsmUse use, MDefinition **def, AsmType *type)
{
    JS_CHECK_RECURSION(f.cx(), return false);

    if (IsNumericLiteral(expr))
        return CheckNumericLiteral(f, expr, def, type);

    switch (expr->getKind()) {
      case PNK_NAME:        return CheckVarRef(f, expr, def, type);
      case PNK_ELEM:        return CheckArrayLoad(f, expr, def, type);
      case PNK_ASSIGN:      return CheckAssign(f, expr, def, type);
      case PNK_CALL:        return CheckCall(f, expr, use, def, type);
      case PNK_POS:         return CheckPos(f, expr, def, type);
      case PNK_NOT:         return CheckNot(f, expr, def, type);
      case PNK_NEG:         return CheckNeg(f, expr, def, type);
      case PNK_BITNOT:      return CheckBitNot(f, expr, def, type);
      case PNK_COMMA:       return CheckComma(f, expr, use, def, type);
      case PNK_CONDITIONAL: return CheckConditional(f, expr, def, type);

      case PNK_STAR:        return CheckFloatMultiply(f, expr, def, type);

      case PNK_ADD:
      case PNK_SUB:         return CheckAddOrSub(f, expr, use, def, type);

      case PNK_DIV:
      case PNK_MOD:         return CheckDivOrMod(f, expr, def, type);

      case PNK_LT:
      case PNK_LE:
      case PNK_GT:
      case PNK_GE:
      case PNK_EQ:
      case PNK_NE:          return CheckComparison(f, expr, def, type);

      case PNK_BITOR:
      case PNK_BITAND:
      case PNK_BITXOR:
      case PNK_LSH:
      case PNK_RSH:
      case PNK_URSH:        return CheckBitwise(f, expr, def, type);

      default:;
    }

    return f.fail("Unsupported expression", expr);
}

static bool
CheckStatement(AsmFunctionCompiler &f, ParseNode *stmt, AsmLabelVector *maybeLabels = NULL);

static bool
CheckExprStatement(AsmFunctionCompiler &f, ParseNode *exprStmt)
{
    JS_ASSERT(exprStmt->isKind(PNK_SEMI));
    ParseNode *expr = UnaryKid(exprStmt);

    if (!expr)
        return true;

    MDefinition *_1;
    AsmType _2;
    if (!CheckExpr(f, UnaryKid(exprStmt), AsmUse::NoCoercion, &_1, &_2))
        return false;

    return true;
}

static bool
CheckWhile(AsmFunctionCompiler &f, ParseNode *whileStmt, const AsmLabelVector *maybeLabels)
{
    JS_ASSERT(whileStmt->isKind(PNK_WHILE));
    ParseNode *cond = BinaryLeft(whileStmt);
    ParseNode *body = BinaryRight(whileStmt);

    MBasicBlock *loopEntry = f.startPendingLoop(whileStmt);

    MDefinition *condDef;
    AsmType condType;
    if (!CheckExpr(f, cond, AsmUse::NoCoercion, &condDef, &condType))
        return false;

    if (!condType.isInt())
        return f.fail("Condition of while loop must be boolish", cond);

    MBasicBlock *afterLoop = f.branchAndStartLoopBody(condDef);

    if (!CheckStatement(f, body))
        return false;

    f.bindContinues(whileStmt, maybeLabels);
    f.closeLoop(loopEntry, afterLoop);
    return true;
}

static bool
CheckFor(AsmFunctionCompiler &f, ParseNode *forStmt, const AsmLabelVector *maybeLabels)
{
    JS_ASSERT(forStmt->isKind(PNK_FOR));
    ParseNode *forHead = BinaryLeft(forStmt);
    ParseNode *body = BinaryRight(forStmt);

    if (!forHead->isKind(PNK_FORHEAD))
        return f.fail("Unsupported for-loop statement", forHead);

    ParseNode *maybeInit = TernaryKid1(forHead);
    ParseNode *cond = TernaryKid2(forHead);
    ParseNode *maybeInc = TernaryKid3(forHead);

    if (maybeInit) {
        MDefinition *_1;
        AsmType _2;
        if (!CheckExpr(f, maybeInit, AsmUse::NoCoercion, &_1, &_2))
            return false;
    }

    MBasicBlock *loopEntry = f.startPendingLoop(forStmt);

    MDefinition *condDef;
    AsmType condType;
    if (!CheckExpr(f, cond, AsmUse::NoCoercion, &condDef, &condType))
        return false;

    if (!condType.isInt())
        return f.fail("Condition of while loop must be boolish", cond);

    MBasicBlock *afterLoop = f.branchAndStartLoopBody(condDef);

    if (!CheckStatement(f, body))
        return false;

    f.bindContinues(forStmt, maybeLabels);

    if (maybeInc) {
        MDefinition *_1;
        AsmType _2;
        if (!CheckExpr(f, maybeInc, AsmUse::NoCoercion, &_1, &_2))
            return false;
    }

    f.closeLoop(loopEntry, afterLoop);
    return true;
}

static bool
CheckDoWhile(AsmFunctionCompiler &f, ParseNode *whileStmt, const AsmLabelVector *maybeLabels)
{
    JS_ASSERT(whileStmt->isKind(PNK_DOWHILE));
    ParseNode *body = BinaryLeft(whileStmt);
    ParseNode *cond = BinaryRight(whileStmt);

    MBasicBlock *loopEntry = f.startPendingLoop(whileStmt);

    if (!CheckStatement(f, body))
        return false;

    f.bindContinues(whileStmt, maybeLabels);

    MDefinition *condDef;
    AsmType condType;
    if (!CheckExpr(f, cond, AsmUse::NoCoercion, &condDef, &condType))
        return false;

    if (!condType.isInt())
        return f.fail("Condition of while loop must be boolish", cond);

    f.branchAndCloseDoWhileLoop(condDef, loopEntry);
    return true;
}

static bool
CheckLabel(AsmFunctionCompiler &f, ParseNode *labeledStmt, AsmLabelVector *maybeLabels)
{
    JS_ASSERT(labeledStmt->isKind(PNK_COLON));
    PropertyName *label = LabeledStatementLabel(labeledStmt);
    ParseNode *stmt = LabeledStatementStatement(labeledStmt);

    if (maybeLabels) {
        if (!maybeLabels->append(label))
            return false;
        if (!CheckStatement(f, stmt, maybeLabels))
            return false;
        return true;
    }

    AsmLabelVector labels(f.cx());
    if (!labels.append(label))
        return false;

    if (!CheckStatement(f, stmt, &labels))
        return false;

    f.bindLabeledBreaks(&labels);
    return true;
}

static bool
CheckIf(AsmFunctionCompiler &f, ParseNode *ifStmt)
{
    JS_ASSERT(ifStmt->isKind(PNK_IF));
    ParseNode *cond = TernaryKid1(ifStmt);
    ParseNode *thenStmt = TernaryKid2(ifStmt);
    ParseNode *elseStmt = TernaryKid3(ifStmt);

    MDefinition *condDef;
    AsmType condType;
    if (!CheckExpr(f, cond, AsmUse::NoCoercion, &condDef, &condType))
        return false;

    if (!condType.isInt())
        return f.fail("Condition of if must be boolish", cond);

    MBasicBlock *thenBlock, *elseBlock;
    f.branchAndStartThen(condDef, &thenBlock, &elseBlock);

    if (!CheckStatement(f, thenStmt))
        return false;

    if (!elseStmt) {
        f.joinIf(elseBlock);
    } else {
        MBasicBlock *thenEnd = f.switchToElse(elseBlock);
        if (!CheckStatement(f, elseStmt))
            return false;
        f.joinIfElse(thenEnd);
    }

    return true;
}

static bool
CheckCaseExpr(AsmFunctionCompiler &f, ParseNode *caseExpr, int32_t *value)
{
    if (!IsNumericLiteral(caseExpr))
        return f.fail("Switch case expression must be an integer literal", caseExpr);

    AsmNumLit literal = ExtractNumericLiteral(caseExpr);
    switch (literal.which()) {
      case AsmNumLit::Fixnum:
      case AsmNumLit::NegativeInt:
        *value = literal.toInt32();
        break;
      case AsmNumLit::OutOfRangeInt:
      case AsmNumLit::BigUnsigned:
        return f.fail("Switch case expression out of integer range", caseExpr);
      case AsmNumLit::Double:
        return f.fail("Switch case expression must be an integer literal", caseExpr);
    }

    return true;
}

static bool
CheckDefaultAtEnd(AsmFunctionCompiler &f, ParseNode *stmt)
{
    for (; stmt; stmt = NextNode(stmt)) {
        JS_ASSERT(stmt->isKind(PNK_CASE) || stmt->isKind(PNK_DEFAULT));
        if (stmt->isKind(PNK_DEFAULT) && NextNode(stmt) != NULL)
            return f.fail("default label must be at the end", stmt);
    }

    return true;
}

static bool
CheckSwitchRange(AsmFunctionCompiler &f, ParseNode *stmt, int32_t *low, int32_t *high,
                 int32_t *tableLength)
{
    if (stmt->isKind(PNK_DEFAULT)) {
        *low = 0;
        *high = -1;
        *tableLength = 0;
        return true;
    }

    int32_t i;
    if (!CheckCaseExpr(f, CaseExpr(stmt), &i))
        return false;

    *low = *high = i;

    for (stmt = NextNode(stmt); stmt && stmt->isKind(PNK_CASE); stmt = NextNode(stmt)) {
        int32_t i;
        if (!CheckCaseExpr(f, CaseExpr(stmt), &i))
            return false;

        *low = Min(*low, i);
        *high = Max(*high, i);
    }

    int64_t i64 = (int64_t(*high) - int64_t(*low)) + 1;
    if (i64 > INT32_MAX)
        return f.fail("The range of a switch must not exceed INT32_MAX", stmt);

    *tableLength = int32_t(i64);
    return true;
}

static bool
CheckSwitch(AsmFunctionCompiler &f, ParseNode *switchStmt)
{
    JS_ASSERT(switchStmt->isKind(PNK_SWITCH));
    ParseNode *switchExpr = BinaryLeft(switchStmt);
    ParseNode *switchBody = BinaryRight(switchStmt);

    if (!switchBody->isKind(PNK_STATEMENTLIST))
        return f.fail("Switch body may not contain 'let' declarations", switchBody);

    MDefinition *exprDef;
    AsmType exprType;
    if (!CheckExpr(f, switchExpr, AsmUse::NoCoercion, &exprDef, &exprType))
        return false;

    if (!exprType.isSigned())
        return f.fail("Switch expression must be a signed integer", switchExpr);

    ParseNode *stmt = ListHead(switchBody);

    if (!CheckDefaultAtEnd(f, stmt))
        return false;

    if (!stmt)
        return true;

    int32_t low, high, tableLength;
    if (!CheckSwitchRange(f, stmt, &low, &high, &tableLength))
        return false;

    AsmCaseVector cases(f.cx());
    if (!cases.resize(tableLength))
        return false;

    MBasicBlock *switchBlock = f.startSwitch(switchStmt, exprDef, low, high);

    for (; stmt && stmt->isKind(PNK_CASE); stmt = NextNode(stmt)) {
        int32_t i = ExtractNumericLiteral(CaseExpr(stmt)).toInt32();

        cases[i - low] = f.startSwitchCase(switchBlock);

        if (!CheckStatement(f, CaseBody(stmt)))
            return false;
    }

    MBasicBlock *defaultBlock = f.startSwitchDefault(switchBlock, &cases);

    if (stmt && stmt->isKind(PNK_DEFAULT)) {
        if (!CheckStatement(f, CaseBody(stmt)))
            return false;
    }

    f.joinSwitch(switchBlock, cases, defaultBlock);
    return true;
}

static bool
CheckReturn(AsmFunctionCompiler &f, ParseNode *returnStmt)
{
    JS_ASSERT(returnStmt->isKind(PNK_RETURN));
    ParseNode *coercion = UnaryKid(returnStmt);

    if (!!coercion != (f.func().returnType().which() != AsmRetType::Void))
        return f.fail("All returns must return a value (of the same type) or all must "
                      "return void", coercion);

    if (!coercion) {
        f.returnVoid();
        return true;
    }

    AsmRetType returnType;
    if (!CheckReturnCoercion(f.m(), coercion, &returnType))
        return false;

    if (returnType != f.func().returnType())
        return f.fail("All returns must return the same type", coercion);

    MDefinition *def;
    AsmType type;
    if (!CheckExpr(f, coercion, AsmUse::FromReturnCoercion(returnType), &def, &type))
        return false;

    JS_ASSERT(type <= returnType);

    f.returnExpr(def);
    return true;
}

static bool
CheckStatements(AsmFunctionCompiler &f, ParseNode *stmtHead)
{
    for (ParseNode *stmt = stmtHead; stmt; stmt = NextNode(stmt)) {
        if (!CheckStatement(f, stmt))
            return false;
    }

    return true;
}

static bool
CheckStatementList(AsmFunctionCompiler &f, ParseNode *stmt)
{
    JS_ASSERT(stmt->isKind(PNK_STATEMENTLIST));
    return CheckStatements(f, ListHead(stmt));
}

static bool
CheckStatement(AsmFunctionCompiler &f, ParseNode *stmt, AsmLabelVector *maybeLabels)
{
    JS_CHECK_RECURSION(f.cx(), return false);

    switch (stmt->getKind()) {
      case PNK_SEMI:          return CheckExprStatement(f, stmt);
      case PNK_WHILE:         return CheckWhile(f, stmt, maybeLabels);
      case PNK_FOR:           return CheckFor(f, stmt, maybeLabels);
      case PNK_DOWHILE:       return CheckDoWhile(f, stmt, maybeLabels);
      case PNK_COLON:         return CheckLabel(f, stmt, maybeLabels);
      case PNK_IF:            return CheckIf(f, stmt);
      case PNK_SWITCH:        return CheckSwitch(f, stmt);
      case PNK_RETURN:        return CheckReturn(f, stmt);
      case PNK_STATEMENTLIST: return CheckStatementList(f, stmt);
      case PNK_BREAK:         return f.addBreak(LoopControlMaybeLabel(stmt));
      case PNK_CONTINUE:      return f.addContinue(LoopControlMaybeLabel(stmt));
      default:;
    }

    return f.fail("Unexpected statement kind", stmt);
}

static bool
CompileMIR(AsmFunctionCompiler &f)
{
    ScopedJSDeletePtr<CodeGenerator> codegen(CompileBackEnd(&f.mirGen(), /* useAsm = */ true));
    if (!codegen)
        return false;

    if (!f.func().isExported())
        return codegen->generateAsm(&f.func().codePtr(), &f.func().pool(), NULL, MIRType_None);

    return codegen->generateAsm(&f.func().codePtr(), &f.func().pool(), &f.func().argMIRTypes(),
                                f.func().returnType().toMIRType());
}

static bool
CheckVariableDecl(AsmModuleCompiler &m, ParseNode *var, AsmFunctionCompiler::LocalMap *locals)
{
    if (!var->isKind(PNK_NAME))
        return m.fail("Local variable names should not restate argument names.", var);

    PropertyName *name = var->name();

    if (!CheckIdentifier(m, name, var))
        return false;

    if (!var->expr())
        return m.fail("Variable needs explicit type declaration via an initial value", var);

    ParseNode *initExpr = var->expr();

    if (!IsNumericLiteral(initExpr))
        return m.fail("Variable initialization value needs to be a numeric literal", initExpr);

    AsmNumLit literal = ExtractNumericLiteral(initExpr);
    AsmVarType type;
    switch (literal.which()) {
      case AsmNumLit::Fixnum:
      case AsmNumLit::NegativeInt:
      case AsmNumLit::BigUnsigned:
        type = AsmVarType::Int;
        break;
      case AsmNumLit::Double:
        type = AsmVarType::Double;
        break;
      case AsmNumLit::OutOfRangeInt:
        return m.fail("Variable initializer is out of representable integer range", initExpr);
    }

    AsmFunctionCompiler::LocalMap::AddPtr p = locals->lookupForAdd(name);
    if (p)
        return m.fail("Local names should be unique", initExpr);

    unsigned slot = locals->count();
    if (!locals->add(p, name, AsmFunctionCompiler::Local(type, slot, literal.value())))
        return false;

    return true;
}

static bool
CheckVariableDecls(AsmModuleCompiler &m, AsmFunctionCompiler::LocalMap *locals, ParseNode **stmtIter)
{
    ParseNode *stmt = *stmtIter;

    for (; stmt && stmt->isKind(PNK_VAR); stmt = NextNode(stmt)) {
        for (ParseNode *var = VarListHead(stmt); var; var = NextNode(var)) {
            if (!CheckVariableDecl(m, var, locals))
                return false;
        }
    }

    *stmtIter = stmt;
    return true;
}

static bool
CheckFunctionBody(AsmModuleCompiler &m, AsmModuleCompiler::Func &func)
{
    // CheckFunctionSignature already has already checked the
    // function head as well as argument type declarations. The ParseNode*
    // stored in f.body points to the first non-argument statement.
    ParseNode *stmtIter = func.body();

    AsmFunctionCompiler::LocalMap locals(m.cx());
    if (!locals.init())
        return false;

    unsigned numFormals;
    ParseNode *arg = FunctionArgsList(func.fn(), &numFormals);
    for (unsigned i = 0; i < numFormals; i++, arg = NextNode(arg)) {
        if (!locals.putNew(arg->name(), AsmFunctionCompiler::Local(func.argType(i), i)))
            return false;
    }

    if (!CheckVariableDecls(m, &locals, &stmtIter))
        return false;

    AsmFunctionCompiler f(m, func, Move(locals));
    if (!f.init())
        return false;

    if (!CheckStatements(f, stmtIter))
        return false;

    f.returnVoid();

    if (!CompileMIR(f))
        return false;

    return true;
}

static bool
CheckFunctionBodies(AsmModuleCompiler &m)
{
    for (unsigned i = 0; i < m.numFunctions(); i++) {
        if (!CheckFunctionBody(m, m.function(i)))
            return false;
    }

    return true;
}

static int32_t
InvokeFromAsmJS_Ignore(JSContext *cx, AsmExitGlobalDatum *exitDatum, int32_t argc, Value *argv)
{
    RootedValue fval(cx, ObjectValue(*exitDatum->fun));
    RootedValue rval(cx);
    if (!Invoke(cx, UndefinedValue(), fval, argc, argv, rval.address()))
        return false;

    return JS_CHECK_OPERATION_LIMIT(cx);  // (TEMPORARY)
}

static int32_t
InvokeFromAsmJS_ToInt32(JSContext *cx, AsmExitGlobalDatum *exitDatum, int32_t argc, Value *argv)
{
    RootedValue fval(cx, ObjectValue(*exitDatum->fun));
    RootedValue rval(cx);
    if (!Invoke(cx, UndefinedValue(), fval, argc, argv, rval.address()))
        return false;

    int32_t i32;
    if (!ToInt32(cx, rval, &i32))
        return false;
    argv[0] = Int32Value(i32);

    return JS_CHECK_OPERATION_LIMIT(cx);  // (TEMPORARY)
}

static int32_t
InvokeFromAsmJS_ToNumber(JSContext *cx, AsmExitGlobalDatum *exitDatum, int32_t argc, Value *argv)
{
    RootedValue fval(cx, ObjectValue(*exitDatum->fun));
    RootedValue rval(cx);
    if (!Invoke(cx, UndefinedValue(), fval, argc, argv, rval.address()))
        return false;

    double dbl;
    if (!ToNumber(cx, rval, &dbl))
        return false;
    argv[0] = DoubleValue(dbl);

    return JS_CHECK_OPERATION_LIMIT(cx);  // (TEMPORARY)
}

static bool
GenerateDefaultExit(AsmModuleCompiler &m, MacroAssembler &masm, Label &errorLabel,
                    const AsmExitDescriptor &descriptor, AsmExitIndex exitIndex)
{
    const unsigned arrayLength = Max<size_t>(1, descriptor.argTypes().length());
    const unsigned arraySize = arrayLength * sizeof(Value);
    const unsigned remainder = (AlignmentAtPrologue + arraySize) % StackAlignment;
    const unsigned padding = remainder ? StackAlignment - remainder : 0;
    const unsigned reserveSize = arraySize + padding;
    const unsigned callerArgsOffset = reserveSize + NativeFrameSize;

    masm.reserveStack(reserveSize);
    Register argv = StackPointer;

    for (ABIArgIter i(descriptor.argTypes()); !i.done(); i++) {
        unsigned argOffset = i.index() * sizeof(Value);
        Address dstAddr = Address(argv, argOffset);
        switch (i->kind()) {
          case ABIArg::GPR:
            masm.storeValue(JSVAL_TYPE_INT32, i->gpr(), dstAddr);
            break;
          case ABIArg::FPU:
            masm.canonicalizeDouble(i->fpu());
            masm.storeDouble(i->fpu(), dstAddr);
            break;
          case ABIArg::Stack:
            if (i.mirType() == MIRType_Int32) {
                Address src(StackPointer, callerArgsOffset + i->offsetFromArg0());
                masm.load32(src, ScratchReg);
                masm.storeValue(JSVAL_TYPE_INT32, ScratchReg, dstAddr);
            } else {
                JS_ASSERT(i.mirType() == MIRType_Double);
                Address src(StackPointer, callerArgsOffset + i->offsetFromArg0());
                masm.loadDouble(src, ScratchFloatReg);
                masm.canonicalizeDouble(ScratchFloatReg);
                masm.storeDouble(ScratchFloatReg, dstAddr);
            }
            break;
        }
    }

    // argument 0: cx
    masm.movePtr(ImmWord(GetIonContext()->compartment->rt), IntArgReg0);
    masm.loadPtr(Address(IntArgReg0, offsetof(JSRuntime, asmJSActivation)), IntArgReg0);
    masm.loadPtr(Address(IntArgReg0, AsmJSActivation::offsetOfContext()), IntArgReg0);

    // argument 1: exitDatum
    masm.lea(Operand(GlobalReg, m.linkData().exitIndexToGlobalDataOffset(exitIndex)), IntArgReg1);

    // argument 2: argc
    masm.mov(Imm32(descriptor.argTypes().length()), IntArgReg2);

    // argument 3: argv
    masm.mov(argv, IntArgReg3);

    switch (descriptor.use().which()) {
      case AsmUse::NoCoercion:
        masm.call(ImmWord(JS_FUNC_TO_DATA_PTR(void*, &InvokeFromAsmJS_Ignore)));
        masm.testl(ReturnReg, ReturnReg);
        masm.j(Assembler::Zero, &errorLabel);
        break;
      case AsmUse::ToInt32:
        masm.call(ImmWord(JS_FUNC_TO_DATA_PTR(void*, &InvokeFromAsmJS_ToInt32)));
        masm.testl(ReturnReg, ReturnReg);
        masm.j(Assembler::Zero, &errorLabel);
        masm.unboxInt32(Address(argv, 0), ReturnReg);
        break;
      case AsmUse::ToNumber:
        masm.call(ImmWord(JS_FUNC_TO_DATA_PTR(void*, &InvokeFromAsmJS_ToNumber)));
        masm.testl(ReturnReg, ReturnReg);
        masm.j(Assembler::Zero, &errorLabel);
        masm.loadDouble(Address(argv, 0), ReturnFloatReg);
        break;
      case AsmUse::AddOrSub:
        JS_NOT_REACHED("Should have been a type error");
    }

    masm.freeStack(reserveSize);
    masm.ret();
    return true;
}

static bool
GenerateDefaultExits(AsmModuleCompiler &m)
{
    MacroAssembler masm(m.cx());

    // If there is an error during the FFI call, we must propagate the
    // exception. Since try-catch isn't supported by asm.js (atm), we can
    // simply pop all frames, returning to CallAsmJS. To do this, there are
    // three steps:
    //  1. Restore 'sp' to it's value right after the PushRegsInMask in
    //     generateAsmPrologue.
    //  2. PopRegsInMask to restore the caller's non-volatile registers.
    //  3. Return (to CallAsmJS).
    // These steps are implemented by a single error handling stub. The FFI
    // call stubs jump to this stub when an error is returned.

    // c.f. CodeGeneratorX64::generateAsmPrologue
    RegisterSet nonVolatileRegs = RegisterSet(GeneralRegisterSet(Registers::NonVolatileMask),
                                              FloatRegisterSet(FloatRegisters::NonVolatileMask));
    masm.setFramePushed(nonVolatileRegs.gprs().size() * STACK_SLOT_SIZE +
                        nonVolatileRegs.fpus().size() * sizeof(double));

    // Generate the error stub.
    Label errorLabel;
    masm.bind(&errorLabel);
    masm.movq(ImmWord(GetIonContext()->compartment->rt), ScratchReg);
    masm.movq(Operand(ScratchReg, offsetof(JSRuntime, asmJSActivation)), ScratchReg);
    masm.movq(Operand(ScratchReg, AsmJSActivation::offsetOfErrorRejoinSP()), StackPointer);
    masm.PopRegsInMask(nonVolatileRegs);
    masm.ret();

    // Generate the default exits.
    Vector<size_t, 32> offsets(m.cx());
    for (AsmExitMap::Range r = m.allExits(); !r.empty(); r.popFront()) {
        offsets.append(masm.size());
        if (!GenerateDefaultExit(m, masm, errorLabel, r.front().key, r.front().value))
            return false;
        masm.align(16);
    }

    masm.finish();
    if (masm.oom()) {
        js_ReportOutOfMemory(m.cx());
        return false;
    }

    JS_ASSERT(masm.bytesNeeded() == masm.size());
    JSC::ExecutableAllocator *execAlloc = m.cx()->compartment->ionCompartment()->execAlloc();
    JSC::ExecutablePool *rawPool;
    uint8_t *code = (uint8_t*)execAlloc->alloc(masm.bytesNeeded(), &rawPool, JSC::ASMJS_CODE);
    if (!code)
        return false;

    m.setDefaultExitPool(rawPool);

    // c.f. CodeGenerator::generateAsm
    masm.executableCopy(code);
    JS_ASSERT(masm.jumpRelocationTableBytes() == 0);
    JS_ASSERT(masm.dataRelocationTableBytes() == 0);
    JS_ASSERT(masm.preBarrierTableBytes() == 0);
    JS_ASSERT(masm.numCodeLabels() == 0);

    unsigned i = 0;
    for (AsmExitMap::Range r = m.allExits(); !r.empty(); r.popFront(), i++)
        m.setDefaultExit(r.front().value, code + offsets[i]);

    return true;
}

static bool
StaticallyLinkModule(AsmModuleCompiler &m)
{
    // When each individual function body is compiled, we can't always have the
    // offset to the callee that is necessary for a pc-relative jump. Thus,
    // calls are saved and patched after compilation is complete.
    for (unsigned i = 0; i < m.numFunctions(); i++) {
        const AsmModuleCompiler::Func &func = m.function(i);
        for (unsigned j = 0; j < func.numCalls(); j++) {
            AsmModuleCompiler::Call call = func.call(j);
            CodeLocationJump jump(func.codePtr().baseAddress, call.offset);
            PatchJump(jump, CodeLocationLabel(call.target->codePtr().internalEntry));
        }
    }

    // Now that compilation has completed, record the actual callee addresses
    // for the function-pointer tables. These are stored in the (unlinked)
    // module and will be copied into the (linked) module's global data
    // according to the global data layout specified by the AsmLinkData
    // *GlobalDataOffset helper functions.
    AsmLinkData::FuncPtrTableElemVector elems;
    for (unsigned i = 0; i < m.numFuncPtrTables(); i++) {
        const AsmModuleCompiler::FuncPtrTable &table = m.funcPtrTable(i);
        JS_ASSERT(elems.length() == table.baseIndex());
        for (unsigned j = 0; j < table.numElems(); j++) {
            const AsmModuleCompiler::Func &func = table.elem(j);
            if (!elems.append(func.codePtr().internalEntry))
                return false;
        }
        JS_ASSERT(elems.length() == table.baseIndex() + table.numElems());
    }
    m.initFuncPtrTableElems(Move(elems));

    // Generate the default stub for each exit.  (See "asm.js FFI calls" comment.)
    if (!GenerateDefaultExits(m))
        return false;

    return true;
}

static bool
CheckModule(JSContext *cx, TokenStream &ts, ParseNode *fn, ScopedJSDeletePtr<AsmModule> *module)
{
    AsmModuleCompiler m(cx, ts);
    if (!m.init())
        return false;

    if (PropertyName *maybeModuleName = FunctionName(fn)) {
        if (!CheckModuleLevelName(m, maybeModuleName, fn))
            return false;
        m.initModuleName(maybeModuleName);
    }

    ParseNode *stmtIter = NULL;

    if (!CheckFunctionHead(m, fn, &stmtIter))
        return false;

    if (!CheckModuleArguments(m, fn))
        return false;

    if (!SkipUseAsmDirective(m, &stmtIter))
        return false;

    if (!CheckModuleGlobals(m, &stmtIter))
        return false;

    if (!CheckFunctionSignatures(m, &stmtIter))
        return false;

    if (!CheckFuncPtrTables(m, &stmtIter))
        return false;

    if (!CheckModuleExports(m, fn, &stmtIter))
        return false;

    if (stmtIter)
        return m.fail("The top-level export (return) must be the last statement.", stmtIter);

    m.setFirstPassComplete();

    if (!CheckFunctionBodies(m))
        return false;

    if (!StaticallyLinkModule(m))
        return false;

    *module = AsmModule::New(m);
    if (!*module)
        return false;

    return true;
}

bool
js::CompileAsmJS(JSContext *cx, TokenStream &ts, ParseNode *fn, HandleScript script)
{
    if (cx->compartment->debugMode())
        return AsmMessage(cx, JSMSG_USE_ASM_TYPE_FAIL, "The debugger disables asm.js optimization");

    if (!cx->compartment->ensureIonCompartmentExists(cx))
        return false;

    ScopedJSDeletePtr<AsmModule> module;
    if (!CheckModule(cx, ts, fn, &module))
        return !cx->isExceptionPending();

    RootedObject moduleObj(cx, NewAsmModuleObject(cx, &module));
    if (!moduleObj)
        return false;


    if (!AsmMessage(cx, JSMSG_USE_ASM_TYPE_OK))
        return false;

    JS_ASSERT(!script->asmJS);
    script->asmJS.init(moduleObj);
    return true;
}

/*****************************************************************************/
// Dynamic-link step

static bool
AsmLinkFail(JSContext *cx, const char *str)
{
    AsmMessage(cx, JSMSG_USE_ASM_LINK_FAIL, str);
    return false;
}

static bool
ValidateGlobalVariable(JSContext *cx, const AsmLinkData &linkData, AsmLinkData::Global global,
                       HandleValue importVal, uint8_t *globalData)
{
    JS_ASSERT(global.which() == AsmLinkData::Global::Variable);

    void *datum = linkData.globalVarIndexToGlobalDatum(globalData, global.varIndex());

    AsmGlobalVarInit varInit = global.varInit();
    switch (varInit.which()) {
      case AsmGlobalVarInit::Constant: {
        const Value &v = varInit.constant();
        if (v.isInt32())
            *(int32_t *)datum = v.toInt32();
        else
            *(double *)datum = v.toDouble();
        break;
      }
      case AsmGlobalVarInit::Import: {
        RootedPropertyName field(cx, varInit.importField());
        RootedValue v(cx);
        if (!GetProperty(cx, importVal, field, &v))
            return false;

        switch (varInit.importType().which()) {
          case AsmVarType::Int:
            if (!ToInt32(cx, v, (int32_t *)datum))
                return false;
            break;
          case AsmVarType::Double:
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
ValidateFFI(JSContext *cx, AsmLinkData::Global global, HandleValue importVal, AutoObjectVector *ffis)
{
    RootedPropertyName field(cx, global.ffiField());
    RootedValue v(cx);
    if (!GetProperty(cx, importVal, field, &v))
        return false;

    if (!v.isObject() || !v.toObject().isFunction())
        return AsmLinkFail(cx, "FFI imports must be functions");

    (*ffis)[global.ffiIndex()] = v.toObject().toFunction();
    return true;
}

static bool
ValidateArrayView(JSContext *cx, AsmLinkData::Global global, HandleValue globalVal, HandleValue bufferVal)
{
    RootedPropertyName field(cx, global.viewName());
    RootedValue v(cx);
    if (!GetProperty(cx, globalVal, field, &v))
        return false;

    if (!IsTypedArrayConstructor(v, global.viewType()))
        return AsmLinkFail(cx, "bad typed array constructor");

    size_t byteLength = bufferVal.toObject().asArrayBuffer().byteLength();
    if (byteLength % (1 << TypedArrayShift(global.viewType())) != 0)
        return AsmLinkFail(cx, "ArrayBuffer length must be a multiple of view element size");

    return true;
}

static bool
ValidateMathBuiltin(JSContext *cx, AsmLinkData::Global global, HandleValue globalVal)
{
    RootedValue v(cx);
    if (!GetProperty(cx, globalVal, cx->names().Math, &v))
        return false;
    RootedPropertyName field(cx, global.mathName());
    if (!GetProperty(cx, v, field, &v))
        return false;

    Native native;
    switch (global.mathBuiltin()) {
      case AsmMathBuiltin_sin: native = math_sin; break;
      case AsmMathBuiltin_cos: native = math_cos; break;
      case AsmMathBuiltin_tan: native = math_tan; break;
      case AsmMathBuiltin_asin: native = math_asin; break;
      case AsmMathBuiltin_acos: native = math_acos; break;
      case AsmMathBuiltin_atan: native = math_atan; break;
      case AsmMathBuiltin_ceil: native = js_math_ceil; break;
      case AsmMathBuiltin_floor: native = js_math_floor; break;
      case AsmMathBuiltin_exp: native = math_exp; break;
      case AsmMathBuiltin_log: native = math_log; break;
      case AsmMathBuiltin_pow: native = js_math_pow; break;
      case AsmMathBuiltin_sqrt: native = js_math_sqrt; break;
      case AsmMathBuiltin_abs: native = js_math_abs; break;
      case AsmMathBuiltin_atan2: native = math_atan2; break;
      case AsmMathBuiltin_imul: native = math_imul; break;
    }

    if (!IsNativeFunction(v, native))
        return AsmLinkFail(cx, "bad Math.* builtin");

    return true;
}

static bool
ValidateGlobalConstant(JSContext *cx, AsmLinkData::Global global, HandleValue globalVal)
{
    RootedPropertyName field(cx, global.constantName());
    RootedValue v(cx);
    if (!GetProperty(cx, globalVal, field, &v))
        return false;

    if (!v.isNumber())
        return AsmLinkFail(cx, "global constant value needs to be a number");

    // NaN != NaN
    if (MOZ_DOUBLE_IS_NaN(global.constantValue())) {
        if (!MOZ_DOUBLE_IS_NaN(v.toNumber()))
            return AsmLinkFail(cx, "global constant value needs to be NaN");
    } else {
        if (v.toNumber() != global.constantValue())
            return AsmLinkFail(cx, "global constant value mismatch");
    }

    return true;
}

static bool
DynamicallyLinkModule(JSContext *cx, StackFrame *fp, HandleObject moduleObj, MutableHandleObject obj)
{
    const AsmLinkData &linkData = AsmModuleObjectToModule(moduleObj).linkData();

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
    if (linkData.usesArrayBuffer()) {
        if (!IsTypedArrayBuffer(bufferVal))
            return AsmLinkFail(cx, "bad ArrayBuffer argument");
        heap = &bufferVal.toObject().asArrayBuffer();
        if (linkData.exactHeapSize() && heap->byteLength() != linkData.exactHeapSize())
            return AsmLinkFail(cx, "asm.js module function heap must be exactly TODO bytes");
        if (linkData.maxConstantPointer() && heap->byteLength() <= linkData.maxConstantPointer())
            return AsmLinkFail(cx, "asm.js module function heap too small");
    }

    ScopedJSDeletePtr<uint8_t> globalDataGuard;
    if (linkData.byteLength() > 0) {
        globalDataGuard = cx->pod_calloc<uint8_t>(linkData.byteLength());
        if (!globalDataGuard)
            return NULL;
    }
    uint8_t *globalData = globalDataGuard.get();

    AutoObjectVector ffis(cx);
    if (!ffis.resize(linkData.numFFIs()))
        return false;

    for (unsigned i = 0; i < linkData.numGlobals(); i++) {
        AsmLinkData::Global global = linkData.global(i);
        switch (global.which()) {
          case AsmLinkData::Global::Variable:
            if (!ValidateGlobalVariable(cx, linkData, global, importVal, globalData))
                return false;
            break;
          case AsmLinkData::Global::FFI:
            if (!ValidateFFI(cx, global, importVal, &ffis))
                return false;
            break;
          case AsmLinkData::Global::ArrayView:
            if (!ValidateArrayView(cx, global, globalVal, bufferVal))
                return false;
            break;
          case AsmLinkData::Global::MathBuiltin:
            if (!ValidateMathBuiltin(cx, global, globalVal))
                return false;
            break;
          case AsmLinkData::Global::Constant:
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

    for (unsigned i = 0; i < linkData.numExits(); i++) {
        AsmExitGlobalDatum &datum = linkData.exitIndexToGlobalDatum(globalData, AsmExitIndex(i));
        const AsmExit &exit = linkData.exit(i);
        datum.exit = exit.defaultExit();
        datum.fun = ffis[exit.ffiIndex().value()]->toFunction();
    }

    for (unsigned i = 0; i < linkData.numFuncPtrTableElems(); i++)
        linkData.funcPtrTableElemIndexToGlobalDatum(globalData, i) = linkData.funcPtrTableElem(i);

    return true;
}

AsmJSActivation::AsmJSActivation(JSContext *cx)
  : prev_(cx->runtime->asmJSActivation),
    cx_(cx),
    errorRejoinPC_(NULL),
    errorRejoinSP_(NULL)
{
    cx->runtime->asmJSActivation = this;
}

AsmJSActivation::~AsmJSActivation()
{
    JS_ASSERT(cx_->runtime->asmJSActivation == this);
    cx_->runtime->asmJSActivation = prev_;
}

static const unsigned ASM_FUN_EXTENDED_SLOT = 0;

static JSBool
CallAsmJS(JSContext *cx, unsigned argc, Value *vp)
{
    // Follow the callee back to the linked module
    CallArgs callArgs = CallArgsFromVp(argc, vp);
    RootedFunction callee(cx, callArgs.callee().toFunction());
    RootedObject linkedModule(cx, &callee->getExtendedSlot(ASM_FUN_EXTENDED_SLOT).toObject());

    // A linked module links a heap (ArrayBuffer) and globalData to a module
    uint8_t *heap =       AsmLinkedModuleToHeapOrNull(linkedModule);
    uint8_t *globalData = AsmLinkedModuleToGlobalData(linkedModule);
    AsmModule &module =   AsmLinkedModuleToModule(linkedModule);

    // A module contains a set of compiled functions, indexed by name
    const AsmModule::Func &func = module.function(callee->name());

    // The calling convention for an external call into asm.js is to pass an
    // array of 8-byte values where each value contains either a coerced int32
    // (in the low word) or double value, with the coercions specified by the
    // asm.js signature. The external entry point unpacks this array into the
    // system-ABI-specified registers and stack memory and then calls into the
    // internal entry point. The return value is stored in the first element of
    // the array (which, therefore, must have length >= 1).

    Vector<uint64_t, 8> coercedArgs(cx);
    if (!coercedArgs.resize(Max<size_t>(1, func.args.length())))
        return false;

    RootedValue v(cx);
    for (unsigned i = 0; i < func.args.length(); ++i) {
        v = i < callArgs.length() ? callArgs[i] : UndefinedValue();
        switch (func.args[i].which()) {
          case AsmVarType::Int:
            if (!ToInt32(cx, v, (int32_t*)&coercedArgs[i]))
                return false;
            break;
          case AsmVarType::Double:
            if (!ToNumber(cx, v, (double*)&coercedArgs[i]))
                return false;
            break;
        }
    }

    AsmJSActivation activation(cx);

    if (!func.codePtr.externalEntry(heap, globalData, coercedArgs.begin()))
        return false;

    switch (func.returnType.which()) {
      case AsmRetType::Void:
        callArgs.rval().set(UndefinedValue());
        break;
      case AsmRetType::Signed:
        callArgs.rval().set(Int32Value(*(int32_t*)&coercedArgs[0]));
        break;
      case AsmRetType::Double:
        callArgs.rval().set(NumberValue(*(double*)&coercedArgs[0]));
        break;
    }

    return true;
}

static JSFunction *
NewExportedFunction(JSContext *cx, const AsmModule &module, HandlePropertyName name,
                    HandleObject linkedModule)
{
    const AsmModule::Func &func = module.function(name);

    JSFunction *fun = js_NewFunction(cx, NullPtr(), CallAsmJS, func.args.length(),
                                     JSFunction::NATIVE_FUN, cx->global(), name,
                                     JSFunction::ExtendedFinalizeKind);
    if (!fun)
        return NULL;

    fun->setExtendedSlot(ASM_FUN_EXTENDED_SLOT, ObjectValue(*linkedModule));
    return fun;
}

bool
js::LinkAsmJS(JSContext *cx, StackFrame *fp, MutableHandleValue rval)
{
    RootedObject moduleObj(cx, fp->fun()->nonLazyScript()->asmJS);
    AsmModule &module = AsmModuleObjectToModule(moduleObj);

    RootedObject linkedModule(cx);
    if (!DynamicallyLinkModule(cx, fp, moduleObj, &linkedModule))
        return !cx->isExceptionPending();

    // Uncomment this to validate asm.js tests against non-asm.js
    //return true;

    RootedPropertyName functionName(cx);
    RootedFunction fun(cx);
    RootedValue funVal(cx);
    RootedId id(cx);

    const AsmLinkData &linkData = module.linkData();
    if (linkData.hasExportedFunction()) {
        functionName = linkData.exportedFunction();
        fun = NewExportedFunction(cx, module, functionName, linkedModule);
        if (!fun)
            return false;

        rval.set(ObjectValue(*fun));
        return true;
    }

    const AsmLinkData::ExportVector &exports = linkData.exportObject();

    gc::AllocKind allocKind = gc::GetGCObjectKind(exports.length());
    RootedObject obj(cx, NewBuiltinClassInstance(cx, &ObjectClass, allocKind));
    if (!obj)
        return false;

    for (unsigned i = 0; i < exports.length(); i++) {
        functionName = exports[i].functionName;
        fun = NewExportedFunction(cx, module, functionName, linkedModule);
        if (!fun)
            return false;

        id = NameToId(exports[i].field);
        funVal = ObjectValue(*fun);
        if (!DefineNativeProperty(cx, obj, id, funVal, NULL, NULL, JSPROP_ENUMERATE, 0, 0))
            return false;
    }

    rval.set(ObjectValue(*obj));
    return true;
}

