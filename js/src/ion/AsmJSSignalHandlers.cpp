/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include <signal.h>

#include "jscntxt.h"

#include "jstypedarrayinlines.h"

#include "ion/AsmJS.h"
#include "ion/AsmJSModule.h"
#include "ion/AsmJSSignalHandlers.h"
#include "assembler/assembler/MacroAssembler.h"

using namespace js;
using namespace js::ion;

#ifdef JS_THREADSAFE
# include "jslock.h"

// Prevent races trying to install the signal handlers.
class SignalMutex
{
    PRLock *mutex_;

  public:
    SignalMutex() {
        mutex_ = PR_NewLock();
        if (!mutex_)
            MOZ_CRASH();
    }
    ~SignalMutex() {
        PR_DestroyLock(mutex_);
    }
    class Lock {
        static bool sHandlersInstalled;
      public:
        Lock();
        ~Lock();
        bool handlersInstalled() const { return sHandlersInstalled; }
        void setHandlersInstalled() { sHandlersInstalled = true; }
    };
} signalMutex;

bool SignalMutex::Lock::sHandlersInstalled = false;

SignalMutex::Lock::Lock()
{
    PR_Lock(signalMutex.mutex_);
}

SignalMutex::Lock::~Lock()
{
    PR_Unlock(signalMutex.mutex_);
}
#else
struct SignalMutex
{
    class Lock {
        static bool sHandlersInstalled;
      public:
        Lock() { (void)this; }
        bool handlersInstalled() const { return sHandlersInstalled; }
        void setHandlersInstalled() { sHandlersInstalled = true; }
    };
};

bool SignalMutex::Lock::sHandlersInstalled = false;
#endif

template <class T>
static void
SetXMMRegToNaN(T *xmm_reg)
{
    JS_STATIC_ASSERT(sizeof(T) == 2 * sizeof(double));
    double *dbls = reinterpret_cast<double*>(xmm_reg);
    dbls[0] = js_NaN;
    dbls[1] = 0;
}

#if defined(__linux__)

static const int SignalCode = SIGSEGV;

static uint8_t **
ContextToPC(mcontext_t &mcontext)
{
# if defined(JS_CPU_X64)
    JS_STATIC_ASSERT(sizeof(mcontext.gregs[REG_RIP]) == 8);
    return reinterpret_cast<uint8_t**>(&mcontext.gregs[REG_RIP]);
# else
#  error "TODO"
# endif
}

static void
SetRegisterToCoercedUndefined(mcontext_t &mcontext, AnyRegister reg)
{
# if defined(JS_CPU_X64)
    if (reg.isFloat()) {
        switch (reg.fpu().code()) {
          case JSC::X86Registers::xmm0:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[0]); break;
          case JSC::X86Registers::xmm1:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[1]); break;
          case JSC::X86Registers::xmm2:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[2]); break;
          case JSC::X86Registers::xmm3:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[3]); break;
          case JSC::X86Registers::xmm4:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[4]); break;
          case JSC::X86Registers::xmm5:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[5]); break;
          case JSC::X86Registers::xmm6:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[6]); break;
          case JSC::X86Registers::xmm7:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[7]); break;
          case JSC::X86Registers::xmm8:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[8]); break;
          case JSC::X86Registers::xmm9:  SetXMMRegToNaN(&mcontext.fpregs->_xmm[9]); break;
          case JSC::X86Registers::xmm10: SetXMMRegToNaN(&mcontext.fpregs->_xmm[10]); break;
          case JSC::X86Registers::xmm11: SetXMMRegToNaN(&mcontext.fpregs->_xmm[11]); break;
          case JSC::X86Registers::xmm12: SetXMMRegToNaN(&mcontext.fpregs->_xmm[12]); break;
          case JSC::X86Registers::xmm13: SetXMMRegToNaN(&mcontext.fpregs->_xmm[13]); break;
          case JSC::X86Registers::xmm14: SetXMMRegToNaN(&mcontext.fpregs->_xmm[14]); break;
          case JSC::X86Registers::xmm15: SetXMMRegToNaN(&mcontext.fpregs->_xmm[15]); break;
          default: MOZ_CRASH();
        }
    } else {
        switch (reg.gpr().code()) {
          case JSC::X86Registers::eax: mcontext.gregs[REG_RAX] = 0; break;
          case JSC::X86Registers::ecx: mcontext.gregs[REG_RCX] = 0; break;
          case JSC::X86Registers::edx: mcontext.gregs[REG_RDX] = 0; break;
          case JSC::X86Registers::ebx: mcontext.gregs[REG_RBX] = 0; break;
          case JSC::X86Registers::esp: mcontext.gregs[REG_RSP] = 0; break;
          case JSC::X86Registers::ebp: mcontext.gregs[REG_RBP] = 0; break;
          case JSC::X86Registers::esi: mcontext.gregs[REG_RSI] = 0; break;
          case JSC::X86Registers::edi: mcontext.gregs[REG_RDI] = 0; break;
          case JSC::X86Registers::r8:  mcontext.gregs[REG_R8]  = 0; break;
          case JSC::X86Registers::r9:  mcontext.gregs[REG_R9]  = 0; break;
          case JSC::X86Registers::r10: mcontext.gregs[REG_R10] = 0; break;
          case JSC::X86Registers::r11: mcontext.gregs[REG_R11] = 0; break;
          case JSC::X86Registers::r12: mcontext.gregs[REG_R12] = 0; break;
          case JSC::X86Registers::r13: mcontext.gregs[REG_R13] = 0; break;
          case JSC::X86Registers::r14: mcontext.gregs[REG_R14] = 0; break;
          case JSC::X86Registers::r15: mcontext.gregs[REG_R15] = 0; break;
          default: MOZ_CRASH();
        }
    }
# else
#  error "TODO"
# endif
}

#elif defined(XP_MACOSX)

static const int SignalCode = SIGBUS;

static uint8_t **
ContextToPC(mcontext_t mcontext)
{
    JS_STATIC_ASSERT(sizeof(mcontext->__ss.__rip) == 8);
    return reinterpret_cast<uint8_t **>(&mcontext->__ss.__rip);
}

static void
SetRegisterToCoercedUndefined(mcontext_t &mcontext, AnyRegister reg)
{
    if (reg.isFloat()) {
        switch (reg.fpu().code()) {
          case JSC::X86Registers::xmm0:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm0); break;
          case JSC::X86Registers::xmm1:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm1); break;
          case JSC::X86Registers::xmm2:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm2); break;
          case JSC::X86Registers::xmm3:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm3); break;
          case JSC::X86Registers::xmm4:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm4); break;
          case JSC::X86Registers::xmm5:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm5); break;
          case JSC::X86Registers::xmm6:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm6); break;
          case JSC::X86Registers::xmm7:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm7); break;
          case JSC::X86Registers::xmm8:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm8); break;
          case JSC::X86Registers::xmm9:  SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm9); break;
          case JSC::X86Registers::xmm10: SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm10); break;
          case JSC::X86Registers::xmm11: SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm11); break;
          case JSC::X86Registers::xmm12: SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm12); break;
          case JSC::X86Registers::xmm13: SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm13); break;
          case JSC::X86Registers::xmm14: SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm14); break;
          case JSC::X86Registers::xmm15: SetXMMRegToNaN(&mcontext->__fs.__fpu_xmm15); break;
          default: MOZ_CRASH();
        }
    } else {
        switch (reg.gpr().code()) {
          case JSC::X86Registers::eax: mcontext->__ss.__rax = 0; break;
          case JSC::X86Registers::ecx: mcontext->__ss.__rcx = 0; break;
          case JSC::X86Registers::edx: mcontext->__ss.__rdx = 0; break;
          case JSC::X86Registers::ebx: mcontext->__ss.__rbx = 0; break;
          case JSC::X86Registers::esp: mcontext->__ss.__rsp = 0; break;
          case JSC::X86Registers::ebp: mcontext->__ss.__rbp = 0; break;
          case JSC::X86Registers::esi: mcontext->__ss.__rsi = 0; break;
          case JSC::X86Registers::edi: mcontext->__ss.__rdi = 0; break;
          case JSC::X86Registers::r8:  mcontext->__ss.__r8  = 0; break;
          case JSC::X86Registers::r9:  mcontext->__ss.__r9  = 0; break;
          case JSC::X86Registers::r10: mcontext->__ss.__r10 = 0; break;
          case JSC::X86Registers::r11: mcontext->__ss.__r11 = 0; break;
          case JSC::X86Registers::r12: mcontext->__ss.__r12 = 0; break;
          case JSC::X86Registers::r13: mcontext->__ss.__r13 = 0; break;
          case JSC::X86Registers::r14: mcontext->__ss.__r14 = 0; break;
          case JSC::X86Registers::r15: mcontext->__ss.__r15 = 0; break;
          default: MOZ_CRASH();
        }
    }
}

#endif

struct sigaction prevSigAction;

// Perform a binary search on the projected offsets of the known heap accesses
// in the module.
static const AsmJSHeapAccess *
LookupHeapAccess(const AsmJSModule &module, void *pc)
{
    if (!module.containsPC(pc))
        return NULL;

    if (module.numHeapAccesses() == 0)
        return NULL;

    uint32_t targetOffset = module.offsetOfPC(pc);
    size_t low = 0;
    size_t high = module.numHeapAccesses() - 1;
    while (high - low >= 2) {
        size_t mid = low + (high - low) / 2;
        uint32_t midOffset = module.heapAccess(mid).offset();
        if (targetOffset == midOffset)
            return &module.heapAccess(mid);
        if (targetOffset < midOffset)
            high = mid;
        else
            low = mid;
    }
    if (targetOffset == module.heapAccess(low).offset())
        return &module.heapAccess(low);
    if (targetOffset == module.heapAccess(high).offset())
        return &module.heapAccess(high);

    return NULL;
}

// Be very cautious and default to not handling; we don't want to accidentally
// silence real crashes from real bugs.
static bool
HandleSignal(int signum, siginfo_t *info, void *context)
{
    if (signum != SignalCode)
        return false;
    
    PerThreadData *threadData = TlsPerThreadData.get();
    if (!threadData)
        return false;

    AsmJSActivation *activation = threadData->asmJSActivation;
    if (!activation)
        return false;

#ifdef JS_CPU_X64
    void *addr = info->si_addr;
    if (addr < activation->heap() || addr >= activation->heap() + FourGiB)
        return false;
#endif

    mcontext_t &mcontext = reinterpret_cast<ucontext_t*>(context)->uc_mcontext;
    uint8_t **ppc = ContextToPC(mcontext);

    const AsmJSModule &module = activation->module();
    const AsmJSHeapAccess *heapAccess = LookupHeapAccess(module, *ppc);
    if (!heapAccess)
        return false;

    // We now know that this is an out-of-bounds access made by an asm.js
    // load/store that we should handle. If this is a load, assign the
    // JS-defined result value to the destination register (ToInt32(undefined)
    // or ToNumber(undefined), determined by the type of the destination
    // register) and set the PC to the next op. Upon return from the handler,
    // execution will resume at this next PC.
    if (heapAccess->isLoad())
        SetRegisterToCoercedUndefined(mcontext, heapAccess->loadedReg());
    *ppc += heapAccess->opLength();
    return true;
}

static void
AsmJSOutOfBoundsHandler(int signum, siginfo_t *info, void *context)
{
    if (HandleSignal(signum, info, context))
        return;

    // This signal is not for any asm.js code we expect, so we need to forward
    // the signal to the next handler. If there is no next handler (SIG_IGN or
    // SIG_DFL), then it's time to crash. To do this, we set the signal back to
    // it's previous disposition and return. This will cause the faulting op to
    // be re-executed which will crash in the normal way. The advantage to
    // doing this is that we remove ourselves from the crash stack which
    // simplifies crash reports. Note: the order of these tests matter.
    if (prevSigAction.sa_flags & SA_SIGINFO)
        prevSigAction.sa_sigaction(signum, info, context);
    else if (prevSigAction.sa_handler == SIG_DFL || prevSigAction.sa_handler == SIG_IGN)
        sigaction(SignalCode, &prevSigAction, NULL);
    else
        prevSigAction.sa_handler(signum);
}

bool
js::EnsureAsmJSSignalHandlersInstalled()
{
    SignalMutex::Lock lock;
    if (lock.handlersInstalled())
        return true;

    struct sigaction sigAction;
    sigAction.sa_sigaction = &AsmJSOutOfBoundsHandler;
    sigemptyset(&sigAction.sa_mask);
    sigAction.sa_flags = SA_SIGINFO;
    if (sigaction(SignalCode, &sigAction, &prevSigAction))
        return false;

    lock.setHandlersInstalled();
    return true;
}
