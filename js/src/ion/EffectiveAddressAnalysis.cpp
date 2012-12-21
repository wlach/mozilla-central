/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "EffectiveAddressAnalysis.h"

using namespace js;
using namespace ion;

// Recognize patterns of the form (x + (y << {0,1,2,3}) + imm32) and convert
// them into an MEffectiveAddress which, on x86/x64 can be emitted with a
// single instruction.
static void
AnalyzeLsh(MBasicBlock *block, MLsh *lsh)
{
    if (lsh->specialization() != MIRType_Int32)
        return;

    MDefinition *index = lsh->lhs();
    JS_ASSERT(index->type() == MIRType_Int32);

    MDefinition *shift = lsh->rhs();
    if (!shift->isConstant())
        return;

    Value shiftValue = shift->toConstant()->value();
    if (!shiftValue.isInt32() || !IsShiftInScaleRange(shiftValue.toInt32()))
        return;

    Scale scale = ShiftToScale(shiftValue.toInt32());

    int32_t displacement = 0;
    MInstruction *last = lsh;
    MDefinition *base = NULL;
    while (true) {
        if (last->useCount() != 1)
            break;

        MUseIterator use = last->usesBegin();
        if (!use->consumer()->isDefinition() || !use->consumer()->toDefinition()->isAdd())
            break;

        MAdd *add = use->consumer()->toDefinition()->toAdd();
        if (add->specialization() != MIRType_Int32 || !add->isTruncated())
            break;

        MDefinition *other = add->getOperand(1 - use->index());
        JS_ASSERT(other->type() == MIRType_Int32);

        if (other->isConstant()) {
            displacement += other->toConstant()->value().toInt32();
        } else {
            if (base)
                break;
            base = other;
        }

        last = add;
    }

    if (!base)
        return;

    MEffectiveAddress *eaddr = MEffectiveAddress::New(base, index, scale, displacement);

    for (MUseIterator i = last->usesBegin(); i != last->usesEnd();)
        i = i->consumer()->replaceOperand(i, eaddr);
    block->insertAfter(last, eaddr);
}

template <class T>
static void
AnalyzeAsmMemoryOp(T *ins)
{
    if (ins->getOperand(0)->isAdd()) {
        MAdd *add = ins->getOperand(0)->toAdd();
        JS_ASSERT(add->type() == MIRType_Int32);

        if (add->lhs()->isConstant()) {
            ins->addDisplacement(add->lhs()->toConstant()->value().toInt32());
            ins->replaceOperand(0, add->rhs());
        } else if (add->rhs()->isConstant()) {
            ins->addDisplacement(add->rhs()->toConstant()->value().toInt32());
            ins->replaceOperand(0, add->lhs());
        }
    }

    if (ins->scale() == TimesOne && ins->getOperand(0)->isLsh()) {
        MLsh *lsh = ins->getOperand(0)->toLsh();
        JS_ASSERT(lsh->type() == MIRType_Int32);

        if (lsh->rhs()->isConstant()) {
            int32_t shift = lsh->rhs()->toConstant()->value().toInt32();
            if (IsShiftInScaleRange(shift)) {
                ins->setScale(ShiftToScale(shift));
                ins->replaceOperand(0, lsh->lhs());
            }
        }
    }
}

bool
EffectiveAddressAnalysis::analyze()
{
    for (ReversePostorderIterator block(graph_.rpoBegin()); block != graph_.rpoEnd(); block++) {
        for (MInstructionIterator i = block->begin(); i != block->end(); i++) {
            if (i->isLsh())
                AnalyzeLsh(*block, i->toLsh());
            else if (i->isAsmLoad())
                AnalyzeAsmMemoryOp(i->toAsmLoad());
            else if (i->isAsmStore())
                AnalyzeAsmMemoryOp(i->toAsmStore());

        }
    }

    return true;
}
