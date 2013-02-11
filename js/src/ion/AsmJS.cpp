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

using namespace js;
using namespace js::ion;
using namespace js::frontend;
using namespace mozilla;

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
// AsmModule (since it must survive compilation so that it may be used to
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
// AsmModule::exits_.
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
};

// See "asm.js FFI calls" comment.
typedef HashMap<AsmExitDescriptor,
                AsmExitIndex,
                AsmExitDescriptor,
                ContextAllocPolicy> AsmExitMap;

// See "asm.js FFI calls" comment.
class AsmExit
{
    AsmFFIIndex ffiIndex_;
    union {
        unsigned codeOffset_;
        uint8_t *code_;
    } u;

  public:
    AsmExit(AsmFFIIndex ffiIndex) : ffiIndex_(ffiIndex) { u.codeOffset_ = 0; }
    AsmFFIIndex ffiIndex() const { return ffiIndex_; }
    void initCodeOffset(unsigned off) { JS_ASSERT(!u.codeOffset_); u.codeOffset_ = off; }
    void patch(uint8_t *baseAddress) { u.code_ = baseAddress + u.codeOffset_; }
    uint8_t *code() const { return u.code_; }
};

// An AsmExitGlobalDatum represents an exit in a linked module's globalData. The
// 'exit' field starts as AsmExit.code and may later be re-pointed to a more
// optimal call path (for builtins or calls to Ion code). The 'fun' remembers
// the actual JSFunction pulled off the import object and keeps it alive. (See
// "asm.js FFI calls" comment above.)
struct AsmExitGlobalDatum
{
    uint8_t *exit;
    HeapPtrFunction fun;
};

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

    friend class AsmModule;

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

// An AsmModule contains all the byproducts of the module compilation: the jit
// code, entry points and their signatures, and all the data needed by the
// dynamic link step to verify that the module compilation assumptions held
// (e.g., that 'global.Math.imul' is really math_imul).
//
// NB: this means that, unlike the rest of the compiler, which asserts there is
// no GC during compilation, AsmModule must be GC-safe.
class AsmModule
{
  public:
    class Global
    {
      public:
        enum Which { Variable, FFI, ArrayView, MathBuiltin, Constant };

      private:
        Which which_;
        union {
            struct {
                AsmGlobalVarInit init_;
                uint32_t index_;
            } var;
            uint32_t ffiIndex_;
            ArrayBufferView::ViewType viewType_;
            AsmMathBuiltin mathBuiltin_;
            double constantValue_;
        } u;
        HeapPtrPropertyName name_;

        friend class AsmModule;

        Global(Which which)
          : which_(which)
        {}
        void trace(JSTracer *trc) {
            if (name_) MarkString(trc, &name_, "asm.js global name");
        }

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
            return name_;
        }
        uint32_t ffiIndex() const {
            JS_ASSERT(which_ == FFI);
            return u.ffiIndex_;
        }
        PropertyName *viewName() const {
            JS_ASSERT(which_ == ArrayView);
            return name_;
        }
        ArrayBufferView::ViewType viewType() const {
            JS_ASSERT(which_ == ArrayView);
            return u.viewType_;
        }
        PropertyName *mathName() const {
            JS_ASSERT(which_ == MathBuiltin);
            return name_;
        }
        AsmMathBuiltin mathBuiltin() const {
            JS_ASSERT(which_ == MathBuiltin);
            return u.mathBuiltin_;
        }
        PropertyName *constantName() const {
            JS_ASSERT(which_ == Constant);
            return name_;
        }
        double constantValue() const {
            JS_ASSERT(which_ == Constant);
            return u.constantValue_;
        }
    };

    typedef int32_t (*CodePtr)(uint8_t *globalData, uint8_t *heap, uint64_t *args);

    class ExportedFunction
    {
        HeapPtrFunction fun_;
        HeapPtrPropertyName maybeFieldName_;
        Vector<AsmVarType, 0, SystemAllocPolicy> argTypes_;
        AsmRetType returnType_;
        bool hasCodePtr_;
        union {
            unsigned codeOffset_;
            CodePtr code_;
        } u;

        friend class AsmModule;

        ExportedFunction(JSFunction *fun,
                         PropertyName *maybeFieldName,
                         MoveRef<Vector<AsmVarType, 0, SystemAllocPolicy> > argTypes,
                         AsmRetType returnType)
          : fun_(fun),
            maybeFieldName_(maybeFieldName),
            argTypes_(argTypes),
            returnType_(returnType),
            hasCodePtr_(false)
        {
            u.codeOffset_ = 0;
        }

      public:
        ExportedFunction(MoveRef<ExportedFunction> rhs)
          : fun_(rhs->fun_),
            maybeFieldName_(rhs->maybeFieldName_),
            argTypes_(Move(rhs->argTypes_)),
            returnType_(rhs->returnType_),
            hasCodePtr_(rhs->hasCodePtr_),
            u(rhs->u)
        {}

        void trace(JSTracer *trc) {
            MarkObject(trc, &fun_, "asm export name");
            if (maybeFieldName_)
                MarkString(trc, &maybeFieldName_, "asm export field");
        }

        void initCodeOffset(unsigned off) {
            JS_ASSERT(!hasCodePtr_); 
            JS_ASSERT(!u.codeOffset_);
            u.codeOffset_ = off;
        }
        void patch(uint8_t *baseAddress) {
            JS_ASSERT(!hasCodePtr_);
            JS_ASSERT(u.codeOffset_);
            hasCodePtr_ = true;
            u.code_ = JS_DATA_TO_FUNC_PTR(CodePtr, baseAddress + u.codeOffset_);
        }

        PropertyName *name() const {
            return fun_->name();
        }
        JSFunction *unclonedFunObj() const {
            return fun_;
        }
        PropertyName *maybeFieldName() const {
            return maybeFieldName_;
        }
        unsigned numArgs() const {
            return argTypes_.length();
        }
        AsmVarType argType(unsigned i) const {
            return argTypes_[i];
        }
        AsmRetType returnType() const {
            return returnType_;
        }
        CodePtr code() const {
            JS_ASSERT(hasCodePtr_);
            return u.code_;
        }
    };

  private:
    typedef Vector<ExportedFunction, 0, SystemAllocPolicy> ExportedFunctionVector;
    typedef Vector<uint8_t*, 0, SystemAllocPolicy> FuncPtrTableElemVector;
    typedef Vector<Global, 0, SystemAllocPolicy> GlobalVector;
    typedef Vector<AsmExit, 0, SystemAllocPolicy> ExitVector;

    GlobalVector                          globals_;
    ExitVector                            exits_;
    ExportedFunctionVector                exports_;
    FuncPtrTableElemVector                funcPtrTableElems_;
    uint32_t                              numGlobalVars_;
    uint32_t                              numFFIs_;
    bool                                  hasArrayView_;

    ScopedReleasePtr<JSC::ExecutablePool> codePool_;
    uint8_t *                             code_;
    size_t                                bytesNeeded_;

  public:
    AsmModule()
      : numGlobalVars_(0),
        numFFIs_(0),
        hasArrayView_(false),
        code_(NULL),
        bytesNeeded_(0)
    {}

    void trace(JSTracer *trc) {
        for (unsigned i = 0; i < globals_.length(); i++)
            globals_[i].trace(trc);
        for (unsigned i = 0; i < exports_.length(); i++)
            exports_[i].trace(trc);
    }

    bool addGlobalVar(AsmGlobalVarInit init, uint32_t *index) {
        Global g(Global::Variable);
        g.u.var.init_ = init;
        g.u.var.index_ = *index = numGlobalVars_++;
        return globals_.append(g);
    }
    bool addFuncPtrTableElems(uint32_t numElems) {
        return funcPtrTableElems_.growBy(numElems);
    }
    bool addFFI(PropertyName *field, uint32_t *index) {
        Global g(Global::FFI);
        g.u.ffiIndex_ = *index = numFFIs_++;
        g.name_ = field;
        return globals_.append(g);
    }
    bool addArrayView(ArrayBufferView::ViewType vt, PropertyName *field) {
        hasArrayView_ = true;
        Global g(Global::ArrayView);
        g.u.viewType_ = vt;
        g.name_ = field;
        return globals_.append(g);
    }
    bool addMathBuiltin(AsmMathBuiltin mathBuiltin, PropertyName *field) {
        Global g(Global::MathBuiltin);
        g.u.mathBuiltin_ = mathBuiltin;
        g.name_ = field;
        return globals_.append(g);
    }
    bool addGlobalConstant(double value, PropertyName *fieldName) {
        Global g(Global::Constant);
        g.u.constantValue_ = value;
        g.name_ = fieldName;
        return globals_.append(g);
    }
    bool addExit(AsmExit exit, AsmExitIndex *index) {
        *index = AsmExitIndex(exits_.length());
        return exits_.append(exit);
    }

    bool addExportedFunction(JSFunction *fun, PropertyName *maybeFieldName,
                             const MIRTypeVector &args, AsmRetType ret)
    {
        Vector<AsmVarType, 0, SystemAllocPolicy> argTypes;
        for (unsigned i = 0; i < args.length(); i++) {
            if (!argTypes.append(AsmVarType::FromMIRType(args[i])))
                return false;
        }
        ExportedFunction func(fun, maybeFieldName, Move(argTypes), ret);
        return exports_.append(Move(func));
    }
    unsigned numExportedFunctions() const {
        return exports_.length();
    }
    const ExportedFunction &exportedFunction(unsigned i) const {
        return exports_[i];
    }
    ExportedFunction &exportedFunction(unsigned i) {
        return exports_[i];
    }

    bool hasArrayView() const {
        return hasArrayView_;
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
        return funcPtrTableElems_.length();
    }
    uint8_t *funcPtrTableElem(unsigned i) const {
        return funcPtrTableElems_[i];
    }
    void setFuncPtrTableElem(unsigned i, uint8_t *addr) {
        funcPtrTableElems_[i] = addr;
    }
    unsigned numExits() const {
        return exits_.length();
    }
    AsmExit &exit(unsigned i) {
        return exits_[i];
    }
    const AsmExit &exit(unsigned i) const {
        return exits_[i];
    }

    // The order in the globalData is [globals, func-ptr table elements, exits].
    // Put the exit array at the end since it grows during the second pass of
    // module compilation which would otherwise invalidate global/func-ptr
    // offsets.
    uint32_t byteLength() const {
        return numGlobalVars_ * sizeof(uint64_t) +
               funcPtrTableElems_.length() * sizeof(void*) +
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
               funcPtrTableElems_.length() * sizeof(void*) +
               i.value() * sizeof(AsmExitGlobalDatum);
    }
    AsmExitGlobalDatum &exitIndexToGlobalDatum(uint8_t *globalData, AsmExitIndex i) const {
        return *(AsmExitGlobalDatum *)(globalData + exitIndexToGlobalDataOffset(i));
    }

    void takeOwnershipOfCodePool(JSC::ExecutablePool *pool, uint8_t *code, size_t bytesNeeded) {
        codePool_ = pool;
        code_ = code;
        bytesNeeded_ = bytesNeeded;
    }
};

/*****************************************************************************/

// AsmModuleCompiler encapsulates the compilation of an entire asm.js module.
// Over the course of an AsmModuleCompiler object's lifetime, many
// AsmFunctionCompiler objects will be created and destroyed in sequence, one
// for each function in the module.
class AsmModuleCompiler
{
  public:
    class Func
    {
        ParseNode *fn_;
        ParseNode *body_;
        MIRTypeVector argTypes_;
        AsmRetType returnType_;
        mutable Label code_;

      public:
        Func(ParseNode *fn, ParseNode *body, MoveRef<MIRTypeVector> types, AsmRetType returnType)
          : fn_(fn),
            body_(body),
            argTypes_(types),
            returnType_(returnType),
            code_()
        {}

        Func(MoveRef<Func> rhs)
          : fn_(rhs->fn_),
            body_(rhs->body_),
            argTypes_(Move(rhs->argTypes_)),
            returnType_(rhs->returnType_),
            code_(rhs->code_)
        {}

        ParseNode *fn() const { return fn_; }
        ParseNode *body() const { return body_; }
        unsigned numArgs() const { return argTypes_.length(); }
        AsmVarType argType(unsigned i) const { return AsmVarType::FromMIRType(argTypes_[i]); }
        const MIRTypeVector &argMIRTypes() const { return argTypes_; }
        AsmRetType returnType() const { return returnType_; }
        Label *codeLabel() const { return &code_; }
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
    };

    typedef Vector<FuncPtrTable> FuncPtrTableVector;

  private:
    typedef HashMap<PropertyName*, AsmMathBuiltin> MathNameMap;
    typedef HashMap<PropertyName*, Global> GlobalMap;
    typedef Vector<Func> FuncVector;

    Maybe<AutoAssertNoGC>        noGC_;

    JSContext *                  cx_;
    LifoAlloc                    lifo_;
    TempAllocator                alloc_;
    IonContext                   ionContext_;
    MacroAssembler               masm_;

    ScopedJSDeletePtr<AsmModule> module_;

    PropertyName *               moduleFunctionName_;
    PropertyName *               globalArgumentName_;
    PropertyName *               importArgumentName_;
    PropertyName *               bufferArgumentName_;

    GlobalMap                    globals_;
    FuncVector                   functions_;
    FuncPtrTableVector           funcPtrTables_;
    AsmExitMap                   exits_;
    MathNameMap                  standardLibraryMathNames_;

    Label                        checkStackAndInterrupt_;

    const char *                 errorString_;
    ParseNode *                  errorNode_;
    TokenStream &                tokenStream_;

    DebugOnly<int>               currentPass_;

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
        lifo_(LIFO_ALLOC_PRIMARY_CHUNK_SIZE),
        alloc_(&lifo_),
        ionContext_(cx, cx->compartment, &alloc_),
        masm_(),
        moduleFunctionName_(NULL),
        globalArgumentName_(NULL),
        importArgumentName_(NULL),
        bufferArgumentName_(NULL),
        globals_(cx),
        functions_(cx),
        funcPtrTables_(cx),
        exits_(cx),
        standardLibraryMathNames_(cx),
        errorString_(NULL),
        errorNode_(NULL),
        tokenStream_(ts),
        currentPass_(1)
    {}

    ~AsmModuleCompiler() {
        noGC_.destroy();
        if (errorString_)
            tokenStream_.reportAsmError(errorNode_, JSMSG_USE_ASM_TYPE_FAIL, errorString_);

        // Avoid spurious Label assertions on compilation failure.
        if (!checkStackAndInterrupt_.bound())
            checkStackAndInterrupt_.bind(0);
    }

    bool init() {
        if (!cx_->compartment->ensureIonCompartmentExists(cx_))
            return false;

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

        module_ = cx_->new_<AsmModule>();
        if (!module_)
            return false;

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
    LifoAlloc &lifo() { return lifo_; }
    TempAllocator &alloc() { return alloc_; }
    MacroAssembler &masm() { return masm_; }
    Label *checkStackAndInterrupt() { return &checkStackAndInterrupt_; }
    bool hasError() const { return errorString_ != NULL; }
    const AsmModule &module() const { return *module_.get(); }

    PropertyName *moduleFunctionName() const { return moduleFunctionName_; }
    PropertyName *globalArgumentName() const { return globalArgumentName_; }
    PropertyName *importArgumentName() const { return importArgumentName_; }
    PropertyName *bufferArgumentName() const { return bufferArgumentName_; }

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
    Maybe<AsmMathBuiltin> lookupStandardLibraryMathName(PropertyName *name) const {
        if (MathNameMap::Ptr p = standardLibraryMathNames_.lookup(name))
            return p->value;
        return Maybe<AsmMathBuiltin>();
    }
    AsmExitMap::Range allExits() const {
        return exits_.all();
    }

    /***************************************************** Mutable interface */

    void initModuleFunctionName(PropertyName *n) { moduleFunctionName_ = n; }
    void initGlobalArgumentName(PropertyName *n) { globalArgumentName_ = n; }
    void initImportArgumentName(PropertyName *n) { importArgumentName_ = n; }
    void initBufferArgumentName(PropertyName *n) { bufferArgumentName_ = n; }

    bool addGlobalVar(PropertyName *varName, AsmVarType type, AsmGlobalVarInit init) {
        JS_ASSERT(currentPass_ == 1);
        Global g(Global::Variable);
        uint32_t index;
        if (!module_->addGlobalVar(init, &index))
            return false;
        g.u.var.index_ = index;
        g.u.var.type_ = type.which();
        return globals_.putNew(varName, g);
    }
    bool addFunction(MoveRef<Func> func) {
        JS_ASSERT(currentPass_ == 1);
        Global g(Global::Function);
        g.u.funcIndex_ = functions_.length();
        if (!globals_.putNew(FunctionName(func->fn()), g))
            return false;
        return functions_.append(func);
    }
    bool addFuncPtrTable(PropertyName *varName, MoveRef<FuncPtrVector> funcPtrTableElems) {
        JS_ASSERT(currentPass_ == 1);
        Global g(Global::FuncPtrTable);
        g.u.funcPtrTableIndex_ = funcPtrTables_.length();
        if (!globals_.putNew(varName, g))
            return false;
        FuncPtrTable table(funcPtrTableElems, module_->numFuncPtrTableElems());
        if (!module_->addFuncPtrTableElems(table.numElems()))
            return false;
        return funcPtrTables_.append(Move(table));
    }
    bool addFFI(PropertyName *varName, PropertyName *field) {
        JS_ASSERT(currentPass_ == 1);
        Global g(Global::FFI);
        uint32_t index;
        if (!module_->addFFI(field, &index))
            return false;
        g.u.ffiIndex_ = index;
        return globals_.putNew(varName, g);
    }
    bool addArrayView(PropertyName *varName, ArrayBufferView::ViewType vt, PropertyName *fieldName) {
        JS_ASSERT(currentPass_ == 1);
        Global g(Global::ArrayView);
        if (!module_->addArrayView(vt, fieldName))
            return false;
        g.u.viewType_ = vt;
        return globals_.putNew(varName, g);
    }
    bool addMathBuiltin(PropertyName *varName, AsmMathBuiltin mathBuiltin, PropertyName *fieldName) {
        JS_ASSERT(currentPass_ == 1);
        if (!module_->addMathBuiltin(mathBuiltin, fieldName))
            return false;
        Global g(Global::MathBuiltin);
        g.u.mathBuiltin_ = mathBuiltin;
        return globals_.putNew(varName, g);
    }
    bool addGlobalConstant(PropertyName *varName, double constant, PropertyName *fieldName) {
        JS_ASSERT(currentPass_ == 1);
        if (!module_->addGlobalConstant(constant, fieldName))
            return false;
        Global g(Global::Constant);
        g.u.constant_ = constant;
        return globals_.putNew(varName, g);
    }
    bool addExportedFunction(const Func *func, PropertyName *maybeFieldName) {
        JS_ASSERT(currentPass_ == 1);
        return module_->addExportedFunction(FunctionObject(func->fn()), maybeFieldName,
                                            func->argMIRTypes(), func->returnType());
    }

    void setFirstPassComplete() {
        JS_ASSERT(currentPass_ == 1);
        currentPass_ = 2;
    }

    Func &function(unsigned funcIndex) {
        JS_ASSERT(currentPass_ == 2);
        return functions_[funcIndex];
    }
    bool addExit(AsmFFIIndex ffi, PropertyName *name, MoveRef<MIRTypeVector> argTypes, AsmUse use,
                 AsmExitIndex *i)
    {
        JS_ASSERT(currentPass_ == 2);
        AsmExitDescriptor exitDescriptor(name, argTypes, use);
        AsmExitMap::AddPtr p = exits_.lookupForAdd(exitDescriptor);
        if (p) {
            *i = p->value;
            return true;
        }
        if (!module_->addExit(AsmExit(ffi), i))
            return false;
        return exits_.add(p, Move(exitDescriptor), *i);
    }
    void setExitOffset(AsmExitIndex exitIndex) {
        JS_ASSERT(currentPass_ == 2);
        module_->exit(exitIndex.value()).initCodeOffset(masm_.size());
    }
    void setEntryOffset(unsigned exportIndex) {
        JS_ASSERT(currentPass_ == 2);
        module_->exportedFunction(exportIndex).initCodeOffset(masm_.size());
    }

    bool finish(ScopedJSDeletePtr<AsmModule> *module) {
        // After finishing, the only valid operation on an AsmModuleCompiler is
        // destruction.
        JS_ASSERT(currentPass_ == 2);
        currentPass_ = -1;

        // Perform any final patching on the buffer before the final copy.
        masm_.finish();
        if (masm_.oom())
            return false;

        // Allocate the executable memory.
        JSC::ExecutableAllocator *execAlloc = cx_->compartment->ionCompartment()->execAlloc();
        JSC::ExecutablePool *pool;
        uint8_t *code = (uint8_t*)execAlloc->alloc(masm_.bytesNeeded(), &pool, JSC::ASMJS_CODE);
        if (!code)
            return false;

        // The ExecutablePool owns the memory and must be released with the AsmModule.
        module_->takeOwnershipOfCodePool(pool, code, masm_.bytesNeeded());

        // Copy the buffer into the executable memory (c.f. IonCode::copyFrom).
        masm_.executableCopy(code);
        masm_.processCodeLabels(code);
        JS_ASSERT(masm_.jumpRelocationTableBytes() == 0);
        JS_ASSERT(masm_.dataRelocationTableBytes() == 0);
        JS_ASSERT(masm_.preBarrierTableBytes() == 0);
        JS_ASSERT(!masm_.hasEnteredExitFrame());

        // Patch anything in the AsmModule that needs an absolute address:

        // Entry points
        for (unsigned i = 0; i < module_->numExportedFunctions(); i++)
            module_->exportedFunction(i).patch(code);

        // Exit points
        for (unsigned i = 0; i < module_->numExits(); i++)
            module_->exit(i).patch(code);

        // Function-pointer table entries
        unsigned elemIndex = 0;
        for (unsigned i = 0; i < funcPtrTables_.length(); i++) {
            FuncPtrTable &table = funcPtrTables_[i];
            JS_ASSERT(elemIndex == table.baseIndex());
            for (unsigned j = 0; j < table.numElems(); j++) {
                uint8_t *funcPtr = code + masm_.actualOffset(table.elem(j).codeLabel()->offset());
                module_->setFuncPtrTableElem(elemIndex++, funcPtr);
            }
            JS_ASSERT(elemIndex == table.baseIndex() + table.numElems());
        }
        JS_ASSERT(elemIndex == module_->numFuncPtrTableElems());

        *module = module_.forget();
        return true;
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

    LifoAllocScope            lifoAllocScope_;
    MIRGraph                  mirGraph_;
    MIRGenerator              mirGen_;
    CompileInfo               compileInfo_;
    AutoFlushCache            autoFlushCache_;  // TODO: where does this go Marty?

    MBasicBlock *             curBlock_;
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
        lifoAllocScope_(&m.lifo()),
        mirGraph_(&m.alloc()),
        mirGen_(m.cx()->compartment, &m.alloc(), &mirGraph_, &compileInfo_),
        compileInfo_(locals_.count()),
        autoFlushCache_("asm.js"),
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

        if (!newBlock(/* pred = */ NULL, &curBlock_))
            return false;

        for (ABIArgIter i(func_.argMIRTypes()); !i.done(); i++) {
            MAsmParameter *ins = MAsmParameter::New(*i, i.mirType());
            curBlock_->add(ins);
            curBlock_->initSlot(compileInfo_.localSlot(i.index()), ins);
        }

        if (!m_.cx()->runtime->asmJSUnsafe)
            curBlock_->add(MAsmCheckStackAndInterrupt::New(m_.checkStackAndInterrupt()));

        for (LocalMap::Range r = locals_.all(); !r.empty(); r.popFront()) {
            const Local &local = r.front().value;
            if (local.which == Local::Var) {
                MConstant *ins = MConstant::New(local.initialValue);
                curBlock_->add(ins);
                curBlock_->initSlot(compileInfo_.localSlot(local.slot), ins);
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

    MDefinition *loadHeap(ArrayBufferView::ViewType vt, MDefinition *ptr)
    {
        if (!curBlock_)
            return NULL;
        MAsmLoad *load = MAsmLoad::New(vt, MAsmLoad::Heap, ptr);
        curBlock_->add(load);
        return load;
    }

    void storeHeap(ArrayBufferView::ViewType vt, MDefinition *ptr, MDefinition *v)
    {
        if (!curBlock_)
            return;
        curBlock_->add(MAsmStore::New(vt, MAsmStore::Heap, ptr, v));
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
        int32_t disp = m_.module().globalVarIndexToGlobalDataOffset(global.varIndex());
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
        int32_t disp = m_.module().globalVarIndexToGlobalDataOffset(global.varIndex());
        MDefinition *index = constant(Int32Value(disp));
        curBlock_->add(MAsmStore::New(vt, MAsmStore::Global, index, v));
    }

    /***************************************************************** Calls */

    // The IonMonkey backend maintains a single stack offset (from the stack
    // pointer to the base of the frame) by adding the total amount of spill
    // space required plus the maximum stack required for argument passing.
    // Since we do not use IonMonkey's MPrepareCall/MPassArg/MCall, we must
    // manually accumulate, for the entire function, the maximum required stack
    // space for argument passing. (This is passed to the CodeGenerator via
    // MIRGenerator::maxAsmStackArgBytes.) Naively, this would just be the
    // maximum of the stack space required for each individual call (as
    // determined by the call ABI). However, as an optimization, arguments are
    // stored to the stack immediately after evaluation (to decrease live
    // ranges and reduce spilling). This introduces the complexity that,
    // between evaluating an argument and making the call, another argument
    // evaluation could perform a call that also needs to store to the stack.
    // When this occurs childClobbers_ = true and the parent expression's
    // arguments are stored above the maximum depth clobbered by a child
    // expression.

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
        args->prevMaxStackBytes_ = mirGen_.resetAsmMaxStackArgBytes();
    }

    bool passArg(MDefinition *argDef, AsmType type, Args *args)
    {
        if (!args->types_.append(type))
            return false;

        if (!curBlock_)
            return true;

        uint32_t childStackBytes = mirGen_.resetAsmMaxStackArgBytes();
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
        uint32_t newStackBytes;
        if (args->childClobbers_) {
            for (unsigned i = 0; i < args->stackArgs_.length(); i++)
                args->stackArgs_[i]->incrementOffset(args->maxChildStackBytes_);
            newStackBytes = Max(args->prevMaxStackBytes_,
                                args->maxChildStackBytes_ + parentStackBytes);
        } else {
            newStackBytes = Max(args->prevMaxStackBytes_,
                                Max(args->maxChildStackBytes_, parentStackBytes));
        }
        mirGen_.setAsmMaxStackArgBytes(newStackBytes);
    }

  private:
    bool call(MAsmCall::Callee callee, const Args &args, MIRType returnType, MDefinition **def)
    {
        if (!curBlock_) {
            *def = NULL;
            return true;
        }
        uint32_t spIncrement = args.childClobbers_ ? args.maxChildStackBytes_ : 0;
        MAsmCall *ins = MAsmCall::New(callee, args.regArgs_, returnType, spIncrement);
        if (!ins)
            return false;
        curBlock_->add(ins);
        *def = ins;
        return true;
    }

  public:
    bool internalCall(const AsmModuleCompiler::Func &func, const Args &args, MDefinition **def)
    {
        MIRType returnType = func.returnType().toMIRType();
        return call(MAsmCall::Callee(func.codeLabel()), args, returnType, def);
    }

    bool funcPtrCall(const AsmModuleCompiler::FuncPtrTable &funcPtrTable, MDefinition *index,
                     const Args &args, MDefinition **def)
    {
        if (!curBlock_) {
            *def = NULL;
            return true;
        }

        MConstant *mask = MConstant::New(Int32Value(funcPtrTable.mask()));
        curBlock_->add(mask);
        MBitAnd *masked = MBitAnd::NewAsm(index, mask);
        curBlock_->add(masked);
        int32_t disp = m_.module().funcPtrTableElemIndexToGlobalDataOffset(funcPtrTable.baseIndex());
        Scale scale = ScaleFromElemWidth(sizeof(void*));
        MAsmLoad *ptrFun = MAsmLoad::New(MAsmLoad::FUNC_PTR, MAsmLoad::Global, masked, scale, disp);
        curBlock_->add(ptrFun);

        MIRType returnType = funcPtrTable.sig().returnType().toMIRType();
        return call(MAsmCall::Callee(ptrFun), args, returnType, def);
    }

    bool ffiCall(AsmExitIndex exitIndex, const Args &args, MIRType returnType, MDefinition **def)
    {
        if (!curBlock_) {
            *def = NULL;
            return true;
        }

        JS_STATIC_ASSERT(offsetof(AsmExitGlobalDatum, exit) == 0);
        int32_t offset = m_.module().exitIndexToGlobalDataOffset(exitIndex);
        MDefinition *index = constant(Int32Value(offset));
        MAsmLoad *ptrFun = MAsmLoad::New(MAsmLoad::FUNC_PTR, MAsmLoad::Global, index);
        curBlock_->add(ptrFun);

        return call(MAsmCall::Callee(ptrFun), args, returnType, def);
    }

    bool builtinCall(void *builtin, const Args &args, MIRType returnType, MDefinition **def)
    {
        return call(MAsmCall::Callee(builtin), args, returnType, def);
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

    bool branchAndStartThen(MDefinition *cond, MBasicBlock **thenBlock, MBasicBlock **elseBlock)
    {
        if (!curBlock_) {
            *thenBlock = NULL;
            *elseBlock = NULL;
            return true;
        }
        if (!newBlock(curBlock_, thenBlock) || !newBlock(curBlock_, elseBlock))
            return false;
        curBlock_->end(MTest::New(cond, *thenBlock, *elseBlock));
        curBlock_ = *thenBlock;
        return true;
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

    bool joinIfElse(MBasicBlock *thenEnd)
    {
        if (!curBlock_ && !thenEnd)
            return true;
        MBasicBlock *pred = curBlock_ ? curBlock_ : thenEnd;
        MBasicBlock *join;
        if (!newBlock(pred, &join))
            return false;
        if (curBlock_)
            curBlock_->end(MGoto::New(join));
        if (thenEnd)
            thenEnd->end(MGoto::New(join));
        if (curBlock_ && thenEnd)
            join->addPredecessor(thenEnd);
        curBlock_ = join;
        return true;
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

    bool startPendingLoop(ParseNode *pn, MBasicBlock **loopEntry)
    {
        if (!loopStack_.append(pn) || !breakableStack_.append(pn))
            return false;
        JS_ASSERT_IF(curBlock_, curBlock_->loopDepth() == loopStack_.length() - 1);
        if (!curBlock_) {
            *loopEntry = NULL;
            return true;
        }
        *loopEntry = MBasicBlock::NewPendingLoopHeader(mirGraph_, compileInfo_, curBlock_, NULL);
        if (!*loopEntry)
            return false;
        mirGraph_.addBlock(*loopEntry);
        (*loopEntry)->setLoopDepth(loopStack_.length());
        curBlock_->end(MGoto::New(*loopEntry));
        curBlock_ = *loopEntry;
        if (!m_.cx()->runtime->asmJSUnsafe)
            curBlock_->add(MAsmCheckStackAndInterrupt::New(m_.checkStackAndInterrupt()));
        return true;
    }

    bool branchAndStartLoopBody(MDefinition *cond, MBasicBlock **afterLoop)
    {
        if (!curBlock_) {
            *afterLoop = NULL;
            return true;
        }
        JS_ASSERT(curBlock_->loopDepth() > 0);
        MBasicBlock *body;
        if (!newBlock(curBlock_, &body))
            return false;
        if (cond->isConstant() && ToBoolean(cond->toConstant()->value())) {
            *afterLoop = NULL;
            curBlock_->end(MGoto::New(body));
        } else {
            if (!newBlockWithDepth(curBlock_, curBlock_->loopDepth() - 1, afterLoop))
                return false;
            curBlock_->end(MTest::New(cond, body, *afterLoop));
        }
        curBlock_ = body;
        return true;
    }

  private:
    ParseNode *popLoop()
    {
        ParseNode *pn = loopStack_.back();
        JS_ASSERT(!unlabeledContinues_.has(pn));
        loopStack_.popBack();
        breakableStack_.popBack();
        return pn;
    }

  public:
    bool closeLoop(MBasicBlock *loopEntry, MBasicBlock *afterLoop)
    {
        ParseNode *pn = popLoop();
        if (!loopEntry) {
            JS_ASSERT(!afterLoop);
            JS_ASSERT(!curBlock_);
            JS_ASSERT(unlabeledBreaks_.empty());
            return true;
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
        return bindUnlabeledBreaks(pn);
    }

    bool branchAndCloseDoWhileLoop(MDefinition *cond, MBasicBlock *loopEntry)
    {
        ParseNode *pn = popLoop();
        if (!loopEntry) {
            JS_ASSERT(!curBlock_);
            JS_ASSERT(unlabeledBreaks_.empty());
            return true;
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
                    MBasicBlock *afterLoop;
                    if (!newBlock(curBlock_, &afterLoop))
                        return false;
                    curBlock_->end(MGoto::New(afterLoop));
                    curBlock_ = afterLoop;
                }
            } else {
                MBasicBlock *afterLoop;
                if (!newBlock(curBlock_, &afterLoop))
                    return false;
                curBlock_->end(MTest::New(cond, loopEntry, afterLoop));
                loopEntry->setBackedge(curBlock_);
                curBlock_ = afterLoop;
            }
        }
        return bindUnlabeledBreaks(pn);
    }

    bool bindContinues(ParseNode *pn, const AsmLabelVector *maybeLabels)
    {
        if (UnlabeledBlockMap::Ptr p = unlabeledContinues_.lookup(pn)) {
            if (!bindBreaksOrContinues(&p->value))
                return false;
            unlabeledContinues_.remove(p);
        }
        return bindLabeledBreaksOrContinues(maybeLabels, &labeledContinues_);
    }

    bool bindLabeledBreaks(const AsmLabelVector *maybeLabels)
    {
        return bindLabeledBreaksOrContinues(maybeLabels, &labeledBreaks_);
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

    bool startSwitch(ParseNode *pn, MDefinition *expr, int32_t low, int32_t high,
                     MBasicBlock **switchBlock)
    {
        if (!breakableStack_.append(pn))
            return false;
        if (!curBlock_)
            return true;
        curBlock_->end(MTableSwitch::New(expr, low, high));
        *switchBlock = curBlock_;
        curBlock_ = NULL;
        return true;
    }

    bool startSwitchCase(MBasicBlock *switchBlock, MBasicBlock **next)
    {
        if (!switchBlock) {
            *next = NULL;
            return true;
        }
        if (!newBlock(switchBlock, next))
            return false;
        if (curBlock_) {
            curBlock_->end(MGoto::New(*next));
            (*next)->addPredecessor(curBlock_);
        }
        curBlock_ = *next;
        return true;
    }

    bool startSwitchDefault(MBasicBlock *switchBlock, AsmCaseVector *cases, MBasicBlock **defaultBlock)
    {
        if (!startSwitchCase(switchBlock, defaultBlock))
            return false;
        if (!*defaultBlock)
            return true;
        for (unsigned i = 0; i < cases->length(); i++) {
            if (!(*cases)[i]) {
                MBasicBlock *bb;
                if (!newBlock(switchBlock, &bb))
                    return false;
                bb->end(MGoto::New(*defaultBlock));
                (*defaultBlock)->addPredecessor(bb);
                (*cases)[i] = bb;
            }
        }
        mirGraph_.moveBlockToEnd(*defaultBlock);
        return true;
    }

    bool joinSwitch(MBasicBlock *switchBlock, const AsmCaseVector &cases, MBasicBlock *defaultBlock)
    {
        ParseNode *pn = breakableStack_.popCopy();
        if (!switchBlock)
            return true;
        MTableSwitch *mir = switchBlock->lastIns()->toTableSwitch();
        mir->addDefault(defaultBlock);
        for (unsigned i = 0; i < cases.length(); i++)
            mir->addCase(cases[i]);
        if (curBlock_) {
            MBasicBlock *next;
            if (!newBlock(curBlock_, &next))
                return false;
            curBlock_->end(MGoto::New(next));
            curBlock_ = next;
        }
        return bindUnlabeledBreaks(pn);
    }

    /*************************************************************************/
  private:
    bool newBlockWithDepth(MBasicBlock *pred, unsigned loopDepth, MBasicBlock **block)
    {
        *block = MBasicBlock::New(mirGraph_, compileInfo_, pred, /* pc = */ NULL, MBasicBlock::NORMAL);
        if (!*block)
            return false;
        mirGraph_.addBlock(*block);
        (*block)->setLoopDepth(loopDepth);
        return true;
    }

    bool newBlock(MBasicBlock *pred, MBasicBlock **block)
    {
        return newBlockWithDepth(pred, loopStack_.length(), block);
    }

    bool bindBreaksOrContinues(BlockVector *preds)
    {
        for (unsigned i = 0; i < preds->length(); i++) {
            MBasicBlock *pred = (*preds)[i];
            if (curBlock_ && curBlock_->begin() == curBlock_->end()) {
                pred->end(MGoto::New(curBlock_));
                curBlock_->addPredecessor(pred);
            } else {
                MBasicBlock *next;
                if (!newBlock(pred, &next))
                    return false;
                pred->end(MGoto::New(next));
                if (curBlock_) {
                    curBlock_->end(MGoto::New(next));
                    next->addPredecessor(curBlock_);
                }
                curBlock_ = next;
            }
            JS_ASSERT(curBlock_->begin() == curBlock_->end());
        }
        preds->clear();
        return true;
    }

    bool bindLabeledBreaksOrContinues(const AsmLabelVector *maybeLabels, LabeledBlockMap *map)
    {
        if (!maybeLabels)
            return true;
        const AsmLabelVector &labels = *maybeLabels;
        for (unsigned i = 0; i < labels.length(); i++) {
            if (LabeledBlockMap::Ptr p = map->lookup(labels[i])) {
                if (!bindBreaksOrContinues(&p->value))
                    return false;
                map->remove(p);
            }
        }
        return true;
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

    bool bindUnlabeledBreaks(ParseNode *pn)
    {
        if (UnlabeledBlockMap::Ptr p = unlabeledBreaks_.lookup(pn)) {
            if (!bindBreaksOrContinues(&p->value))
                return false;
            unlabeledBreaks_.remove(p);
        }
        return true;
    }
};

/*****************************************************************************/
// An AsmModule contains the persistent results of asm.js module compilation,
// viz., the jit code and dynamic link information.
//
// An AsmModule object is created at the end of module compilation and
// subsequently owned by an AsmModuleClass JSObject.

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
    const AsmModule &module = AsmLinkedModuleToModule(obj);
    uint8_t *globalData = AsmLinkedModuleToGlobalData(obj);
    for (unsigned i = 0; i < module.numExits(); i++) {
        AsmExitGlobalDatum &exitDatum = module.exitIndexToGlobalDatum(globalData, AsmExitIndex(i));
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

    if (name == m.moduleFunctionName() ||
        name == m.globalArgumentName() ||
        name == m.importArgumentName() ||
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
    m.initGlobalArgumentName(arg1Name);

    PropertyName *arg2Name = NULL;
    if (numFormals >= 2 && !CheckModuleArgument(m, arg2, &arg2Name))
        return false;
    m.initImportArgumentName(arg2Name);

    PropertyName *arg3Name = NULL;
    if (numFormals >= 3 && !CheckModuleArgument(m, arg3, &arg3Name))
        return false;
    m.initBufferArgumentName(arg3Name);

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

    if (!IsUseOfName(base, m.importArgumentName()))
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

    if (!IsUseOfName(base, m.globalArgumentName()))
        return m.fail("Expecting global.y", base);

    ParseNode *bufArg = NextNode(ctorExpr);
    if (!bufArg)
        return m.fail("Constructor needs an argument", ctorExpr);

    if (NextNode(bufArg) != NULL)
        return m.fail("Only one argument may be passed to a typed array constructor", bufArg);

    if (!bufArg->isKind(PNK_NAME))
        return m.fail("Argument to typed array constructor must be ArrayBuffer name", bufArg);

    if (bufArg->name() != m.bufferArgumentName())
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
        if (!IsUseOfName(global, m.globalArgumentName()) || math != m.cx()->names().Math)
            return m.fail("Expecting global.Math", base);

        Maybe<AsmMathBuiltin> mathBuiltin = m.lookupStandardLibraryMathName(field);
        if (!mathBuiltin)
            return m.fail("Does not match a standard Math builtin", initExpr);

        return m.addMathBuiltin(varName, mathBuiltin.get(), field);
    }

    if (IsUseOfName(base, m.globalArgumentName())) {
        if (field == m.cx()->names().NaN)
            return m.addGlobalConstant(varName, js_NaN, field);
        if (field == m.cx()->names().Infinity)
            return m.addGlobalConstant(varName, js_PositiveInfinity, field);
        return m.fail("Does not match a standard global constant", initExpr);
    }

    if (IsUseOfName(base, m.importArgumentName()))
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

    PropertyName *funcName = returnExpr->name();

    const AsmModuleCompiler::Func *func = m.lookupFunction(funcName);
    if (!func)
        return m.fail("exported function name not found", returnExpr);

    return m.addExportedFunction(func, /* maybeFieldName = */ NULL);
}

static bool
CheckModuleExportObject(AsmModuleCompiler &m, ParseNode *object)
{
    JS_ASSERT(object->isKind(PNK_OBJECT));

    for (ParseNode *pn = ListHead(object); pn; pn = NextNode(pn)) {
        if (!IsNormalObjectField(m.cx(), pn))
            return m.fail("Only normal object properties may be used in the export object literal", pn);

        PropertyName *fieldName = ObjectNormalFieldName(m.cx(), pn);

        ParseNode *initExpr = ObjectFieldInitializer(pn);
        if (!initExpr->isKind(PNK_NAME))
            return m.fail("Initializer of exported object literal must be name of function", initExpr);

        PropertyName *funcName = initExpr->name();

        const AsmModuleCompiler::Func *func = m.lookupFunction(funcName);
        if (!func)
            return m.fail("exported function name not found", initExpr);

        if (!m.addExportedFunction(func, fieldName))
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
                 MDefinition **def)
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
        *def = f.constant(Int32Value(pointer));
        return true;
    }

    ParseNode *pointerNode;
    if (indexExpr->isKind(PNK_RSH)) {
        ParseNode *shiftNode = BinaryRight(indexExpr);

        uint32_t shift;
        if (!IsLiteralUint32(shiftNode, &shift) || shift != TypedArrayShift(*viewType))
            return f.fail("The shift amount must be a constant matching the array "
                          "element size", shiftNode);

        pointerNode = BinaryLeft(indexExpr);
    } else {
        if (TypedArrayShift(*viewType) != 0)
            return f.fail("The shift amount is 0 so this must be a Int8/Uint8 array", indexExpr);

        pointerNode = indexExpr;
    }

    MDefinition *pointerDef;
    AsmType pointerType;
    if (!CheckExpr(f, pointerNode, AsmUse::ToInt32, &pointerDef, &pointerType))
        return false;

    if (!pointerType.isIntish())
        return f.fail("Pointer input must be intish", pointerNode);

    // Mask off the low bits to account for clearing effect of a right shift
    // followed by the left shift implicit in the array access. E.g., H32[i>>2]
    // loses the low two bits.
    int32_t mask = ~((uint32_t(1) << TypedArrayShift(*viewType)) - 1);
    if (f.m().cx()->runtime->asmJSUnsafe)
        *def = pointerDef;
    else
        *def = f.bitwise<MBitAnd>(pointerDef, f.constant(Int32Value(mask)));
    return true;
}

static bool
CheckArrayLoad(AsmFunctionCompiler &f, ParseNode *elem, MDefinition **def, AsmType *type)
{
    ArrayBufferView::ViewType viewType;
    MDefinition *pointerDef;
    if (!CheckArrayAccess(f, elem, &viewType, &pointerDef))
        return false;

    *def = f.loadHeap(viewType, pointerDef);
    *type = TypedArrayLoadType(viewType);
    return true;
}

static bool
CheckStoreArray(AsmFunctionCompiler &f, ParseNode *lhs, ParseNode *rhs, MDefinition **def, AsmType *type)
{
    ArrayBufferView::ViewType viewType;
    MDefinition *pointerDef;
    if (!CheckArrayAccess(f, lhs, &viewType, &pointerDef))
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

    f.storeHeap(viewType, pointerDef, rhsDef);

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

    if (!f.internalCall(callee, args, def))
        return false;

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

    if (!f.funcPtrCall(*table, indexDef, args, def))
        return false;

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

    if (!f.ffiCall(exitIndex, args, use.toMIRType(), def))
        return false;

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

    if (!f.builtinCall(callee, args, MIRType_Double, def))
        return false;

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
    if (!f.branchAndStartThen(condDef, &thenBlock, &elseBlock))
        return false;

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
    if (!f.joinIfElse(thenEnd))
        return false;
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
IsValidIntMultiplyConstant(ParseNode *expr)
{
    if (!IsNumericLiteral(expr))
        return false;

    AsmNumLit literal = ExtractNumericLiteral(expr);
    switch (literal.which()) {
      case AsmNumLit::Fixnum:
      case AsmNumLit::NegativeInt:
        if (abs(literal.toInt32()) < (1<<20))
            return true;
        return false;
      case AsmNumLit::BigUnsigned:
      case AsmNumLit::Double:
      case AsmNumLit::OutOfRangeInt:
        return false;
    }

    JS_NOT_REACHED("Bad literal");
    return false;
}

static bool
CheckMultiply(AsmFunctionCompiler &f, ParseNode *star, MDefinition **def, AsmType *type)
{
    JS_ASSERT(star->isKind(PNK_STAR));
    ParseNode *lhs = BinaryLeft(star);
    ParseNode *rhs = BinaryRight(star);

    MDefinition *lhsDef;
    AsmType lhsType;
    if (!CheckExpr(f, lhs, AsmUse::ToNumber, &lhsDef, &lhsType))
        return false;

    MDefinition *rhsDef;
    AsmType rhsType;
    if (!CheckExpr(f, rhs, AsmUse::ToNumber, &rhsDef, &rhsType))
        return false;

    if (lhsType.isInt() && rhsType.isInt()) {
        if (!IsValidIntMultiplyConstant(lhs) && !IsValidIntMultiplyConstant(rhs))
            return f.fail("One arg to int multiply must be small (-2^20, 2^20) int literal", star);
        *def = f.mul(lhsDef, rhsDef, MIRType_Int32, MMul::Integer);
        *type = AsmType::Signed;
        return true;
    }

    if (lhsType.isDoublish() && rhsType.isDoublish()) {
        *def = f.mul(lhsDef, rhsDef, MIRType_Double, MMul::Normal);
        *type = AsmType::Double;
        return true;
    }

    return f.fail("Arguments to * must both be doubles", star);
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

    if (!f.m().alloc().ensureBallast())
        return false;

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

      case PNK_STAR:        return CheckMultiply(f, expr, def, type);

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

    MBasicBlock *loopEntry;
    if (!f.startPendingLoop(whileStmt, &loopEntry))
        return false;

    MDefinition *condDef;
    AsmType condType;
    if (!CheckExpr(f, cond, AsmUse::NoCoercion, &condDef, &condType))
        return false;

    if (!condType.isInt())
        return f.fail("Condition of while loop must be boolish", cond);

    MBasicBlock *afterLoop;
    if (!f.branchAndStartLoopBody(condDef, &afterLoop))
        return false;

    if (!CheckStatement(f, body))
        return false;

    if (!f.bindContinues(whileStmt, maybeLabels))
        return false;

    return f.closeLoop(loopEntry, afterLoop);
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

    MBasicBlock *loopEntry;
    if (!f.startPendingLoop(forStmt, &loopEntry))
        return false;

    MDefinition *condDef;
    AsmType condType;
    if (!CheckExpr(f, cond, AsmUse::NoCoercion, &condDef, &condType))
        return false;

    if (!condType.isInt())
        return f.fail("Condition of while loop must be boolish", cond);

    MBasicBlock *afterLoop;
    if (!f.branchAndStartLoopBody(condDef, &afterLoop))
        return false;

    if (!CheckStatement(f, body))
        return false;

    if (!f.bindContinues(forStmt, maybeLabels))
        return false;

    if (maybeInc) {
        MDefinition *_1;
        AsmType _2;
        if (!CheckExpr(f, maybeInc, AsmUse::NoCoercion, &_1, &_2))
            return false;
    }

    return f.closeLoop(loopEntry, afterLoop);
}

static bool
CheckDoWhile(AsmFunctionCompiler &f, ParseNode *whileStmt, const AsmLabelVector *maybeLabels)
{
    JS_ASSERT(whileStmt->isKind(PNK_DOWHILE));
    ParseNode *body = BinaryLeft(whileStmt);
    ParseNode *cond = BinaryRight(whileStmt);

    MBasicBlock *loopEntry;
    if (!f.startPendingLoop(whileStmt, &loopEntry))
        return false;

    if (!CheckStatement(f, body))
        return false;

    if (!f.bindContinues(whileStmt, maybeLabels))
        return false;

    MDefinition *condDef;
    AsmType condType;
    if (!CheckExpr(f, cond, AsmUse::NoCoercion, &condDef, &condType))
        return false;

    if (!condType.isInt())
        return f.fail("Condition of while loop must be boolish", cond);

    return f.branchAndCloseDoWhileLoop(condDef, loopEntry);
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

    return f.bindLabeledBreaks(&labels);
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
    if (!f.branchAndStartThen(condDef, &thenBlock, &elseBlock))
        return false;

    if (!CheckStatement(f, thenStmt))
        return false;

    if (!elseStmt) {
        f.joinIf(elseBlock);
    } else {
        MBasicBlock *thenEnd = f.switchToElse(elseBlock);
        if (!CheckStatement(f, elseStmt))
            return false;
        if (!f.joinIfElse(thenEnd))
            return false;
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

    MBasicBlock *switchBlock;
    if (!f.startSwitch(switchStmt, exprDef, low, high, &switchBlock))
        return false;

    for (; stmt && stmt->isKind(PNK_CASE); stmt = NextNode(stmt)) {
        int32_t i = ExtractNumericLiteral(CaseExpr(stmt)).toInt32();

        if (!f.startSwitchCase(switchBlock, &cases[i - low]))
            return false;

        if (!CheckStatement(f, CaseBody(stmt)))
            return false;
    }

    MBasicBlock *defaultBlock;
    if (!f.startSwitchDefault(switchBlock, &cases, &defaultBlock))
        return false;

    if (stmt && stmt->isKind(PNK_DEFAULT)) {
        if (!CheckStatement(f, CaseBody(stmt)))
            return false;
    }

    return f.joinSwitch(switchBlock, cases, defaultBlock);
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

    if (!f.m().alloc().ensureBallast())
        return false;

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

    m.masm().bind(func.codeLabel());

    ScopedJSDeletePtr<CodeGenerator> codegen(CompileBackEnd(&f.mirGen(), &m.masm()));
    if (!codegen)
        return false;

    // Unlike regular IonMonkey which links and generates a new IonCode for
    // every function, we accumulate all the functions in the module in a
    // single MacroAssembler and link at end. Linking asm.js doesn't require a
    // CodeGenerator so we can destory it now.
    return true;
}

// TODO: consider 16-byte alignment like GCC; note: execAlloc only
// aligns to 8-byte boundaries.
static const unsigned CodeAlignment = 8;

static bool
CheckFunctionBodies(AsmModuleCompiler &m)
{
    for (unsigned i = 0; i < m.numFunctions(); i++) {
        if (!CheckFunctionBody(m, m.function(i)))
            return false;

        // A single MacroAssembler is reused for all function compilations
        // so that there is a single linear code segment for each module.
        // To avoid spiking memory, each AsmFunctionCompiler creates a
        // LifoAllocScope so that all MIR/LIR nodes are freed after each
        // function is compiled. This method is responsible for cleaning
        // out any dangling pointers that the MacroAssembler may have kept.
        m.masm().resetForNewCodeGenerator();

        // Align internal function headers.
        m.masm().align(CodeAlignment);
    }

    return true;
}

static RegisterSet VolatileRegs = RegisterSet(GeneralRegisterSet(Registers::VolatileMask),
                                              FloatRegisterSet(FloatRegisters::VolatileMask));
static RegisterSet NonVolatileRegs = RegisterSet(GeneralRegisterSet(Registers::NonVolatileMask),
                                                 FloatRegisterSet(FloatRegisters::NonVolatileMask));

#if defined(JS_CPU_X64)
static bool
GenerateEntry(AsmModuleCompiler &m, const AsmModule::ExportedFunction &exportedFunc)
{
    const AsmModuleCompiler::Func &func = *m.lookupFunction(exportedFunc.name());

    MacroAssembler &masm = m.masm();

    // In constrast to the X64 system ABI, the Ion convention is that all
    // registers are clobbered by calls. Thus, we must save the caller's
    // non-volatile registers.
    //
    // NB: GenerateExits assumes that masm.framePushed() == 0 before
    // PushRegsInMask(NonVolatileRegs).
    masm.setFramePushed(0);
    masm.PushRegsInMask(NonVolatileRegs);
    JS_ASSERT(masm.framePushed() == NonVolatileRegs.gprs().size() * STACK_SLOT_SIZE +
                                    NonVolatileRegs.fpus().size() * sizeof(double));
    JS_ASSERT(masm.framePushed() % 16 == 0);

    // Remember the stack pointer in the current AsmJSActivation. This will be
    // used by error exit paths to set the stack pointer back to what it was
    // right after the (C++) caller's non-volatile registers were saved so that
    // they can be restored.
    masm.movq(ImmWord(GetIonContext()->compartment->rt), ScratchReg);
    masm.movq(Operand(ScratchReg, offsetof(JSRuntime, asmJSActivation)), ScratchReg);
    masm.movq(StackPointer, Operand(ScratchReg, AsmJSActivation::offsetOfErrorRejoinSP()));

    // Move the parameters into non-argument registers since we are about to
    // clobber these registers with the contents of argv.
    Register argv = r13;
    masm.movq(IntArgReg0, HeapReg);    // buffer
    masm.movq(IntArgReg1, GlobalReg);  // globalData
    masm.movq(IntArgReg2, argv);       // argv

    // Remember argv so that we can load argv[0] after the call.
    JS_ASSERT(masm.framePushed() % 16 == 0);
    masm.Push(argv);
    JS_ASSERT(masm.framePushed() % 16 == 8);

    // Determine how many stack slots we need to hold arguments that don't fit
    // in registers.
    unsigned numStackArgs = 0;
    for (ABIArgIter iter(func.argMIRTypes()); !iter.done(); iter++) {
        if (iter->kind() == ABIArg::Stack)
            numStackArgs++;
    }

    // Before calling, we must ensure sp % 16 == 0. Since (sp % 16) = 8 on
    // entry, we need to push 8 (mod 16) bytes.
    JS_ASSERT(AlignmentAtPrologue == 8);
    JS_ASSERT(masm.framePushed() % 16 == 8);
    unsigned stackDec = (numStackArgs + numStackArgs % 2) * sizeof(uint64_t);
    masm.reserveStack(stackDec);
    JS_ASSERT(masm.framePushed() % 16 == 8);

    // Copy parameters out of argv into the registers/stack-slots specified by
    // the system ABI.
    for (ABIArgIter iter(func.argMIRTypes()); !iter.done(); iter++) {
        unsigned argOffset = iter.index() * sizeof(uint64_t);
        switch (iter->kind()) {
          case ABIArg::GPR:
            masm.movl(Operand(argv, argOffset), iter->gpr());
            break;
          case ABIArg::FPU:
            masm.movsd(Operand(argv, argOffset), iter->fpu());
            break;
          case ABIArg::Stack:
            masm.movq(Operand(argv, argOffset), ScratchReg);
            masm.movq(ScratchReg, Operand(StackPointer, iter->offsetFromArg0()));
            break;
        }
    }

    masm.call(func.codeLabel());

    // Recover argv.
    masm.freeStack(stackDec);
    masm.Pop(argv);

    // Store the result in argv[0].
    switch (func.returnType().which()) {
      case AsmRetType::Void:
        break;
      case AsmRetType::Signed:
        masm.storeValue(JSVAL_TYPE_INT32, ReturnReg, Address(argv, 0));
        break;
      case AsmRetType::Double:
        masm.canonicalizeDouble(ReturnFloatReg);
        masm.storeDouble(ReturnFloatReg, Address(argv, 0));
        break;
    }

    masm.PopRegsInMask(NonVolatileRegs);

    masm.movl(Imm32(true), ReturnReg);
    masm.ret();
    return true;
}
#endif

static bool
GenerateEntries(AsmModuleCompiler &m)
{
    for (unsigned i = 0; i < m.module().numExportedFunctions(); i++) {
        m.setEntryOffset(i);
        if (!GenerateEntry(m, m.module().exportedFunction(i)))
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

static unsigned
PaddingForAlignedCall(unsigned frameSize)
{
    const unsigned remainder = (AlignmentAtPrologue + frameSize) % StackAlignment;
    return remainder ? StackAlignment - remainder : 0;
}

static bool
GenerateExit(AsmModuleCompiler &m, MacroAssembler &masm, const AsmExitDescriptor &descriptor,
             AsmExitIndex exitIndex, Label *popAllFramesLabel)
{
    masm.align(CodeAlignment);
    m.setExitOffset(exitIndex);

    const unsigned arrayLength = Max<size_t>(1, descriptor.argTypes().length());
    const unsigned arraySize = arrayLength * sizeof(Value);
    const unsigned padding = PaddingForAlignedCall(arraySize);
    const unsigned reserveSize = arraySize + padding;
    const unsigned callerArgsOffset = reserveSize + NativeFrameSize;

    masm.setFramePushed(0);
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
    masm.lea(Operand(GlobalReg, m.module().exitIndexToGlobalDataOffset(exitIndex)), IntArgReg1);

    // argument 2: argc
    masm.mov(Imm32(descriptor.argTypes().length()), IntArgReg2);

    // argument 3: argv
    masm.mov(argv, IntArgReg3);

    switch (descriptor.use().which()) {
      case AsmUse::NoCoercion:
        masm.call(ImmWord(JS_FUNC_TO_DATA_PTR(void*, &InvokeFromAsmJS_Ignore)));
        masm.testl(ReturnReg, ReturnReg);
        masm.j(Assembler::Zero, popAllFramesLabel);
        break;
      case AsmUse::ToInt32:
        masm.call(ImmWord(JS_FUNC_TO_DATA_PTR(void*, &InvokeFromAsmJS_ToInt32)));
        masm.testl(ReturnReg, ReturnReg);
        masm.j(Assembler::Zero, popAllFramesLabel);
        masm.unboxInt32(Address(argv, 0), ReturnReg);
        break;
      case AsmUse::ToNumber:
        masm.call(ImmWord(JS_FUNC_TO_DATA_PTR(void*, &InvokeFromAsmJS_ToNumber)));
        masm.testl(ReturnReg, ReturnReg);
        masm.j(Assembler::Zero, popAllFramesLabel);
        masm.loadDouble(Address(argv, 0), ReturnFloatReg);
        break;
      case AsmUse::AddOrSub:
        JS_NOT_REACHED("Should have been a type error");
    }

    masm.freeStack(reserveSize);
    masm.ret();
    return true;
}

static void
LoadJSContextIntoRegister(MacroAssembler &masm, Register reg)
{
    masm.movePtr(ImmWord(GetIonContext()->compartment->rt), reg);
    masm.loadPtr(Address(reg, offsetof(JSRuntime, asmJSActivation)), reg);
    masm.loadPtr(Address(reg, AsmJSActivation::offsetOfContext()), reg);
}

static bool
GenerateExits(AsmModuleCompiler &m)
{
    MacroAssembler &masm = m.masm();

    Label popAllFramesLabel;

    // See CodeGenerator::visitOutOfLineAsmCheckStackAndInterrupt.
    if (m.checkStackAndInterrupt()->used()) {
        masm.align(CodeAlignment);
        masm.bind(m.checkStackAndInterrupt());

        masm.setFramePushed(0);
        masm.PushRegsInMask(VolatileRegs);
        const unsigned padding = PaddingForAlignedCall(masm.framePushed());
        masm.reserveStack(padding);

        bool (*pf)(JSContext*) = CheckOverRecursed;
        LoadJSContextIntoRegister(masm, IntArgReg0);
        masm.call(ImmWord(JS_FUNC_TO_DATA_PTR(void*, pf)));
        masm.testl(ReturnReg, ReturnReg);
        masm.j(Assembler::Zero, &popAllFramesLabel);

        masm.freeStack(padding);
        masm.PopRegsInMask(VolatileRegs);
        masm.ret();
    }

    // Generate FFI call exit stubs.
    for (AsmExitMap::Range r = m.allExits(); !r.empty(); r.popFront()) {
        if (!GenerateExit(m, masm, r.front().key, r.front().value, &popAllFramesLabel))
            return false;
    }

    // If an exception is thrown, simply pop all frames (since asm.js does not
    // contain try/catch). To do this:
    //  1. Restore 'sp' to it's value right after the PushRegsInMask in GenerateEntry.
    //  2. PopRegsInMask to restore the caller's non-volatile registers.
    //  3. Return (to CallAsmJS).
    if (popAllFramesLabel.used()) {
        masm.setFramePushed(NonVolatileRegs.gprs().size() * STACK_SLOT_SIZE +
                            NonVolatileRegs.fpus().size() * sizeof(double));
        masm.bind(&popAllFramesLabel);
        masm.movq(ImmWord(GetIonContext()->compartment->rt), ScratchReg);
        masm.movq(Operand(ScratchReg, offsetof(JSRuntime, asmJSActivation)), ScratchReg);
        masm.movq(Operand(ScratchReg, AsmJSActivation::offsetOfErrorRejoinSP()), StackPointer);
        masm.PopRegsInMask(NonVolatileRegs);
        masm.ret();
    }

    return true;
}

static bool
CheckModule(JSContext *cx, TokenStream &ts, ParseNode *fn, ScopedJSDeletePtr<AsmModule> *module)
{
    AsmModuleCompiler m(cx, ts);
    if (!m.init())
        return false;

    if (PropertyName *moduleFunctionName = FunctionName(fn)) {
        if (!CheckModuleLevelName(m, moduleFunctionName, fn))
            return false;
        m.initModuleFunctionName(moduleFunctionName);
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

    if (!GenerateEntries(m))
        return false;

    if (!GenerateExits(m))
        return false;

    return m.finish(module);
}

bool
js::CompileAsmJS(JSContext *cx, TokenStream &ts, ParseNode *fn, HandleScript script)
{
    if (cx->compartment->debugMode())
        return AsmMessage(cx, JSMSG_USE_ASM_TYPE_FAIL, "The debugger disables asm.js optimization");

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
ValidateGlobalVariable(JSContext *cx, const AsmModule &module, AsmModule::Global global,
                       HandleValue importVal, uint8_t *globalData)
{
    JS_ASSERT(global.which() == AsmModule::Global::Variable);

    void *datum = module.globalVarIndexToGlobalDatum(globalData, global.varIndex());

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
ValidateFFI(JSContext *cx, AsmModule::Global global, HandleValue importVal, AutoObjectVector *ffis)
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
ValidateArrayView(JSContext *cx, AsmModule::Global global, HandleValue globalVal, HandleValue bufferVal)
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
ValidateMathBuiltin(JSContext *cx, AsmModule::Global global, HandleValue globalVal)
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
ValidateGlobalConstant(JSContext *cx, AsmModule::Global global, HandleValue globalVal)
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
    const AsmModule &module = AsmModuleObjectToModule(moduleObj);

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
            return AsmLinkFail(cx, "bad ArrayBuffer argument");
        heap = &bufferVal.toObject().asArrayBuffer();
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
        AsmModule::Global global = module.global(i);
        switch (global.which()) {
          case AsmModule::Global::Variable:
            if (!ValidateGlobalVariable(cx, module, global, importVal, globalData))
                return false;
            break;
          case AsmModule::Global::FFI:
            if (!ValidateFFI(cx, global, importVal, &ffis))
                return false;
            break;
          case AsmModule::Global::ArrayView:
            if (!ValidateArrayView(cx, global, globalVal, bufferVal))
                return false;
            break;
          case AsmModule::Global::MathBuiltin:
            if (!ValidateMathBuiltin(cx, global, globalVal))
                return false;
            break;
          case AsmModule::Global::Constant:
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
        AsmExitGlobalDatum &datum = module.exitIndexToGlobalDatum(globalData, AsmExitIndex(i));
        const AsmExit &exit = module.exit(i);
        datum.exit = exit.code();
        datum.fun = ffis[exit.ffiIndex().value()]->toFunction();
    }

    for (unsigned i = 0; i < module.numFuncPtrTableElems(); i++)
        module.funcPtrTableElemIndexToGlobalDatum(globalData, i) = module.funcPtrTableElem(i);

    return true;
}

AsmJSActivation::AsmJSActivation(JSContext *cx, UnrootedFunction fun)
  : prev_(cx->runtime->asmJSActivation),
    cx_(cx),
    errorRejoinPC_(NULL),
    errorRejoinSP_(NULL),
    profiler_(NULL),
    fun_(cx, fun)
{
    cx->runtime->asmJSActivation = this;
    cx->runtime->resetIonStackLimit();

    if (cx->runtime->spsProfiler.enabled()) {
        profiler_ = &cx->runtime->spsProfiler;
        profiler_->enter(cx_, fun_->nonLazyScript(), fun_);
    }
}

AsmJSActivation::~AsmJSActivation()
{
    JS_ASSERT(cx_->runtime->asmJSActivation == this);
    cx_->runtime->asmJSActivation = prev_;

    if (profiler_)
        profiler_->exit(cx_, fun_->nonLazyScript(), fun_);
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
    AsmModule &module =   AsmLinkedModuleToModule(linkedModule);
    uint8_t *heap =       AsmLinkedModuleToHeapOrNull(linkedModule);
    uint8_t *globalData = AsmLinkedModuleToGlobalData(linkedModule);

    // An exported function points to the code as well as the exported
    // function's signature, which implies the dynamic coercions performed on
    // the arguments.
    const AsmModule::ExportedFunction &func = module.exportedFunction(exportIndex);

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
        switch (func.argType(i).which()) {
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

    AsmJSActivation activation(cx, func.unclonedFunObj());

    if (!func.code()(heap, globalData, coercedArgs.begin()))
        return false;

    switch (func.returnType().which()) {
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
NewExportedFunction(JSContext *cx, const AsmModule::ExportedFunction &func,
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
    AsmModule &module = AsmModuleObjectToModule(moduleObj);

    RootedObject linkedModule(cx);
    if (!DynamicallyLinkModule(cx, fp, moduleObj, &linkedModule))
        return !cx->isExceptionPending();

    // Uncomment this to validate asm.js tests against non-asm.js
    //return true;

    if (module.numExportedFunctions() == 1) {
        const AsmModule::ExportedFunction &func = module.exportedFunction(0);
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
        const AsmModule::ExportedFunction &func = module.exportedFunction(i);

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

