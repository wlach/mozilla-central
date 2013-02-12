/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=4 sw=4 et tw=99:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "gc/Marking.h"
#include "ion/AsmJSModule.h"

using namespace js;

void
AsmJSModule::Global::trace(JSTracer *trc)
{
    if (name_)
        MarkString(trc, &name_, "asm.js global name");
}

void
AsmJSModule::ExportedFunction::trace(JSTracer *trc)
{
    MarkObject(trc, &fun_, "asm export name");
    if (maybeFieldName_)
        MarkString(trc, &maybeFieldName_, "asm export field");
}

void
AsmJSModule::trace(JSTracer *trc)
{
    for (unsigned i = 0; i < globals_.length(); i++)
        globals_[i].trace(trc);
    for (unsigned i = 0; i < exports_.length(); i++)
        exports_[i].trace(trc);
}
