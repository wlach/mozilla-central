/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "jsnum.h"

#include "CodeGenerator-x64.h"
#include "ion/MIR.h"
#include "ion/MIRGraph.h"
#include "ion/shared/CodeGenerator-shared-inl.h"
#include "vm/Shape.h"

#include "vm/Shape-inl.h"

using namespace js;
using namespace js::ion;

CodeGeneratorX64::CodeGeneratorX64(MIRGenerator *gen, LIRGraph *graph)
  : CodeGeneratorX86Shared(gen, graph)
{
}

bool
CodeGeneratorX64::generateAsmPrologue(const MIRTypeVector &argTypes, MIRType returnType,
                                      Label *internalEntry)
{
    // In constrast to the X64 system ABI, the Ion convention is that all
    // registers are clobbered by calls. Thus, we must save the caller's
    // non-volatile registers.
    //
    // NB: GenerateDefaultExits assumes that masm.framePushed() == 0 before
    // PushRegsInMask(nonVolatileRegs).
    JS_ASSERT(masm.framePushed() == 0);
    RegisterSet nonVolatileRegs = RegisterSet(GeneralRegisterSet(Registers::NonVolatileMask),
                                              FloatRegisterSet(FloatRegisters::NonVolatileMask));
    masm.PushRegsInMask(nonVolatileRegs);
    JS_ASSERT(masm.framePushed() == nonVolatileRegs.gprs().size() * STACK_SLOT_SIZE +
                                    nonVolatileRegs.fpus().size() * sizeof(double));
    JS_ASSERT(masm.framePushed() % 16 == 0);

    // Remember the stack pointer in the current AsmJSActivation. This will be
    // used by error exit paths to set the stack pointer back to what it was
    // right after the (C++) caller's non-volatile registers were saved so that
    // they can be restored.
    masm.movq(ImmWord(GetIonContext()->compartment->rt), ScratchReg);
    masm.movq(Operand(ScratchReg, offsetof(JSRuntime, asmJSActivation)), ScratchReg);
    masm.movq(StackPointer, Operand(ScratchReg, AsmJSActivation::offsetOfErrorRejoinSP()));

    // Move the externalEntry parameters into non-argument registers since we
    // are about to clobber these registers with the contents of argv.
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
    for (ABIArgIter iter(argTypes); !iter.done(); iter++) {
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
    for (ABIArgIter iter(argTypes); !iter.done(); iter++) {
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

    masm.call(internalEntry);

    // Recover argv.
    masm.freeStack(stackDec);
    masm.Pop(argv);

    // Store the result in argv[0].
    if (returnType == MIRType_Int32) {
        masm.storeValue(JSVAL_TYPE_INT32, ReturnReg, Address(argv, 0));
    } else if (returnType == MIRType_Double) {
        masm.canonicalizeDouble(ReturnFloatReg);
        masm.storeDouble(ReturnFloatReg, Address(argv, 0));
    } else {
        JS_ASSERT(returnType == MIRType_None);
    }

    masm.PopRegsInMask(nonVolatileRegs);

    masm.movl(Imm32(true), ReturnReg);
    masm.ret();
    return true;
}

ValueOperand
CodeGeneratorX64::ToValue(LInstruction *ins, size_t pos)
{
    return ValueOperand(ToRegister(ins->getOperand(pos)));
}

ValueOperand
CodeGeneratorX64::ToOutValue(LInstruction *ins)
{
    return ValueOperand(ToRegister(ins->getDef(0)));
}

ValueOperand
CodeGeneratorX64::ToTempValue(LInstruction *ins, size_t pos)
{
    return ValueOperand(ToRegister(ins->getTemp(pos)));
}

bool
CodeGeneratorX64::visitDouble(LDouble *ins)
{
    const LDefinition *out = ins->output();
    masm.loadConstantDouble(ins->getDouble(), ToFloatRegister(out));
    return true;
}

FrameSizeClass
FrameSizeClass::FromDepth(uint32_t frameDepth)
{
    return FrameSizeClass::None();
}

FrameSizeClass
FrameSizeClass::ClassLimit()
{
    return FrameSizeClass(0);
}

uint32_t
FrameSizeClass::frameSize() const
{
    JS_NOT_REACHED("x64 does not use frame size classes");
    return 0;
}

bool
CodeGeneratorX64::visitValue(LValue *value)
{
    LDefinition *reg = value->getDef(0);
    masm.moveValue(value->value(), ToRegister(reg));
    return true;
}

bool
CodeGeneratorX64::visitOsrValue(LOsrValue *value)
{
    const LAllocation *frame  = value->getOperand(0);
    const LDefinition *target = value->getDef(0);

    const ptrdiff_t valueOffset = value->mir()->frameOffset();

    masm.movq(Operand(ToRegister(frame), valueOffset), ToRegister(target));

    return true;
}

bool
CodeGeneratorX64::visitBox(LBox *box)
{
    const LAllocation *in = box->getOperand(0);
    const LDefinition *result = box->getDef(0);

    if (box->type() != MIRType_Double)
        masm.boxValue(ValueTypeFromMIRType(box->type()), ToRegister(in), ToRegister(result));
    else
        masm.movqsd(ToFloatRegister(in), ToRegister(result));
    return true;
}

bool
CodeGeneratorX64::visitUnbox(LUnbox *unbox)
{
    const ValueOperand value = ToValue(unbox, LUnbox::Input);
    const LDefinition *result = unbox->output();
    MUnbox *mir = unbox->mir();

    if (mir->fallible()) {
        Assembler::Condition cond;
        switch (mir->type()) {
          case MIRType_Int32:
            cond = masm.testInt32(Assembler::NotEqual, value);
            break;
          case MIRType_Boolean:
            cond = masm.testBoolean(Assembler::NotEqual, value);
            break;
          case MIRType_Object:
            cond = masm.testObject(Assembler::NotEqual, value);
            break;
          case MIRType_String:
            cond = masm.testString(Assembler::NotEqual, value);
            break;
          default:
            JS_NOT_REACHED("Given MIRType cannot be unboxed.");
            return false;
        }
        if (!bailoutIf(cond, unbox->snapshot()))
            return false;
    }

    switch (mir->type()) {
      case MIRType_Int32:
        masm.unboxInt32(value, ToRegister(result));
        break;
      case MIRType_Boolean:
        masm.unboxBoolean(value, ToRegister(result));
        break;
      case MIRType_Object:
        masm.unboxObject(value, ToRegister(result));
        break;
      case MIRType_String:
        masm.unboxString(value, ToRegister(result));
        break;
      default:
        JS_NOT_REACHED("Given MIRType cannot be unboxed.");
        break;
    }
    
    return true;
}

bool
CodeGeneratorX64::visitLoadSlotV(LLoadSlotV *load)
{
    Register dest = ToRegister(load->outputValue());
    Register base = ToRegister(load->input());
    int32_t offset = load->mir()->slot() * sizeof(js::Value);

    masm.movq(Operand(base, offset), dest);
    return true;
}

void
CodeGeneratorX64::loadUnboxedValue(Operand source, MIRType type, const LDefinition *dest)
{
    switch (type) {
      case MIRType_Double:
        masm.loadInt32OrDouble(source, ToFloatRegister(dest));
        break;

      case MIRType_Object:
      case MIRType_String:
        masm.unboxObject(source, ToRegister(dest));
        break;

      case MIRType_Int32:
      case MIRType_Boolean:
        masm.movl(source, ToRegister(dest));
        break;

      default:
        JS_NOT_REACHED("unexpected type");
    }
}

bool
CodeGeneratorX64::visitLoadSlotT(LLoadSlotT *load)
{
    Register base = ToRegister(load->input());
    int32_t offset = load->mir()->slot() * sizeof(js::Value);

    loadUnboxedValue(Operand(base, offset), load->mir()->type(), load->output());

    return true;
}

void
CodeGeneratorX64::storeUnboxedValue(const LAllocation *value, MIRType valueType,
                                    Operand dest, MIRType slotType)
{
    if (valueType == MIRType_Double) {
        masm.movsd(ToFloatRegister(value), dest);
        return;
    }

    // For known integers and booleans, we can just store the unboxed value if
    // the slot has the same type.
    if ((valueType == MIRType_Int32 || valueType == MIRType_Boolean) && slotType == valueType) {
        if (value->isConstant()) {
            Value val = *value->toConstant();
            if (valueType == MIRType_Int32)
                masm.movl(Imm32(val.toInt32()), dest);
            else
                masm.movl(Imm32(val.toBoolean() ? 1 : 0), dest);
        } else {
            masm.movl(ToRegister(value), dest);
        }
        return;
    }

    if (value->isConstant()) {
        masm.moveValue(*value->toConstant(), ScratchReg);
        masm.movq(ScratchReg, dest);
    } else {
        masm.storeValue(ValueTypeFromMIRType(valueType), ToRegister(value), dest);
    }
}

bool
CodeGeneratorX64::visitStoreSlotT(LStoreSlotT *store)
{
    Register base = ToRegister(store->slots());
    int32_t offset = store->mir()->slot() * sizeof(js::Value);

    const LAllocation *value = store->value();
    MIRType valueType = store->mir()->value()->type();
    MIRType slotType = store->mir()->slotType();

    if (store->mir()->needsBarrier())
        emitPreBarrier(Address(base, offset), slotType);

    storeUnboxedValue(value, valueType, Operand(base, offset), slotType);
    return true;
}

bool
CodeGeneratorX64::visitLoadElementT(LLoadElementT *load)
{
    Operand source = createArrayElementOperand(ToRegister(load->elements()), load->index());

    if (load->mir()->loadDoubles()) {
        FloatRegister fpreg = ToFloatRegister(load->output());
        if (source.kind() == Operand::REG_DISP)
            masm.loadDouble(source.toAddress(), fpreg);
        else
            masm.loadDouble(source.toBaseIndex(), fpreg);
    } else {
        loadUnboxedValue(source, load->mir()->type(), load->output());
    }

    JS_ASSERT(!load->mir()->needsHoleCheck());
    return true;
}


void
CodeGeneratorX64::storeElementTyped(const LAllocation *value, MIRType valueType, MIRType elementType,
                                    const Register &elements, const LAllocation *index)
{
    Operand dest = createArrayElementOperand(elements, index);
    storeUnboxedValue(value, valueType, dest, elementType);
}

bool
CodeGeneratorX64::visitImplicitThis(LImplicitThis *lir)
{
    Register callee = ToRegister(lir->callee());

    // The implicit |this| is always |undefined| if the function's environment
    // is the current global.
    GlobalObject *global = &gen->info().script()->global();
    masm.cmpPtr(Operand(callee, JSFunction::offsetOfEnvironment()), ImmGCPtr(global));

    // TODO: OOL stub path.
    if (!bailoutIf(Assembler::NotEqual, lir->snapshot()))
        return false;

    masm.moveValue(UndefinedValue(), ToOutValue(lir));
    return true;
}

bool
CodeGeneratorX64::visitRecompileCheck(LRecompileCheck *lir)
{
    // Bump the script's use count and bailout if the script is hot. Note that
    // it's safe to bake in this pointer since scripts are never nursery
    // allocated and jitcode will be purged before doing a compacting GC.
    const uint32_t *useCount = gen->info().script()->addressOfUseCount();
    masm.movq(ImmWord(useCount), ScratchReg);

    Operand addr(ScratchReg, 0);
    masm.addl(Imm32(1), addr);
    masm.cmpl(addr, Imm32(lir->mir()->minUses()));
    if (!bailoutIf(Assembler::AboveOrEqual, lir->snapshot()))
        return false;
    return true;
}

typedef bool (*InterruptCheckFn)(JSContext *);
static const VMFunction InterruptCheckInfo = FunctionInfo<InterruptCheckFn>(InterruptCheck);

bool
CodeGeneratorX64::visitInterruptCheck(LInterruptCheck *lir)
{
    OutOfLineCode *ool = oolCallVM(InterruptCheckInfo, lir, (ArgList()), StoreNothing());
    if (!ool)
        return false;

    void *interrupt = (void*)&gen->compartment->rt->interrupt;
    masm.movq(ImmWord(interrupt), ScratchReg);
    masm.cmpl(Operand(ScratchReg, 0), Imm32(0));
    masm.j(Assembler::NonZero, ool->entry());
    masm.bind(ool->rejoin());
    return true;
}

bool
CodeGeneratorX64::visitCompareB(LCompareB *lir)
{
    MCompare *mir = lir->mir();

    const ValueOperand lhs = ToValue(lir, LCompareB::Lhs);
    const LAllocation *rhs = lir->rhs();
    const Register output = ToRegister(lir->output());

    JS_ASSERT(mir->jsop() == JSOP_STRICTEQ || mir->jsop() == JSOP_STRICTNE);

    // Load boxed boolean in ScratchReg.
    if (rhs->isConstant())
        masm.moveValue(*rhs->toConstant(), ScratchReg);
    else
        masm.boxValue(JSVAL_TYPE_BOOLEAN, ToRegister(rhs), ScratchReg);

    // Perform the comparison.
    masm.cmpq(lhs.valueReg(), ScratchReg);
    emitSet(JSOpToCondition(mir->compareType(), mir->jsop()), output);
    return true;
}

bool
CodeGeneratorX64::visitCompareBAndBranch(LCompareBAndBranch *lir)
{
    MCompare *mir = lir->mir();

    const ValueOperand lhs = ToValue(lir, LCompareBAndBranch::Lhs);
    const LAllocation *rhs = lir->rhs();

    JS_ASSERT(mir->jsop() == JSOP_STRICTEQ || mir->jsop() == JSOP_STRICTNE);

    // Load boxed boolean in ScratchReg.
    if (rhs->isConstant())
        masm.moveValue(*rhs->toConstant(), ScratchReg);
    else
        masm.boxValue(JSVAL_TYPE_BOOLEAN, ToRegister(rhs), ScratchReg);

    // Perform the comparison.
    masm.cmpq(lhs.valueReg(), ScratchReg);
    emitBranch(JSOpToCondition(mir->compareType(), mir->jsop()), lir->ifTrue(), lir->ifFalse());
    return true;
}
bool
CodeGeneratorX64::visitCompareV(LCompareV *lir)
{
    MCompare *mir = lir->mir();
    const ValueOperand lhs = ToValue(lir, LCompareV::LhsInput);
    const ValueOperand rhs = ToValue(lir, LCompareV::RhsInput);
    const Register output = ToRegister(lir->output());

    JS_ASSERT(mir->jsop() == JSOP_EQ || mir->jsop() == JSOP_STRICTEQ ||
              mir->jsop() == JSOP_NE || mir->jsop() == JSOP_STRICTNE);

    masm.cmpq(lhs.valueReg(), rhs.valueReg());
    emitSet(JSOpToCondition(mir->compareType(), mir->jsop()), output);
    return true;
}

bool
CodeGeneratorX64::visitCompareVAndBranch(LCompareVAndBranch *lir)
{
    MCompare *mir = lir->mir();

    const ValueOperand lhs = ToValue(lir, LCompareVAndBranch::LhsInput);
    const ValueOperand rhs = ToValue(lir, LCompareVAndBranch::RhsInput);

    JS_ASSERT(mir->jsop() == JSOP_EQ || mir->jsop() == JSOP_STRICTEQ ||
              mir->jsop() == JSOP_NE || mir->jsop() == JSOP_STRICTNE);

    masm.cmpq(lhs.valueReg(), rhs.valueReg());
    emitBranch(JSOpToCondition(mir->compareType(), mir->jsop()), lir->ifTrue(), lir->ifFalse());
    return true;
}
