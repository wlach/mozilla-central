/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 *
 * The contents of this file are subject to the Netscape Public License
 * Version 1.0 (the "NPL"); you may not use this file except in
 * compliance with the NPL.  You may obtain a copy of the NPL at
 * http://www.mozilla.org/NPL/
 *
 * Software distributed under the NPL is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the NPL
 * for the specific language governing rights and limitations under the
 * NPL.
 *
 * The Initial Developer of this code under the NPL is Netscape
 * Communications Corporation.  Portions created by Netscape are
 * Copyright (C) 1998 Netscape Communications Corporation.  All Rights
 * Reserved.
 */
#include "nsHTMLAtoms.h"

nsIAtom* nsHTMLAtoms::a;
nsIAtom* nsHTMLAtoms::above;
nsIAtom* nsHTMLAtoms::action;
nsIAtom* nsHTMLAtoms::align;
nsIAtom* nsHTMLAtoms::alink;
nsIAtom* nsHTMLAtoms::alt;
nsIAtom* nsHTMLAtoms::archive;
nsIAtom* nsHTMLAtoms::background;
nsIAtom* nsHTMLAtoms::below;
nsIAtom* nsHTMLAtoms::bgcolor;
nsIAtom* nsHTMLAtoms::body;
nsIAtom* nsHTMLAtoms::border;
nsIAtom* nsHTMLAtoms::bordercolor;
nsIAtom* nsHTMLAtoms::bottompadding;
nsIAtom* nsHTMLAtoms::br;
nsIAtom* nsHTMLAtoms::cellpadding;
nsIAtom* nsHTMLAtoms::cellspacing;
nsIAtom* nsHTMLAtoms::checked;
nsIAtom* nsHTMLAtoms::kClass;
nsIAtom* nsHTMLAtoms::classid;
nsIAtom* nsHTMLAtoms::clear;
nsIAtom* nsHTMLAtoms::clip;
nsIAtom* nsHTMLAtoms::code;
nsIAtom* nsHTMLAtoms::codebase;
nsIAtom* nsHTMLAtoms::color;
nsIAtom* nsHTMLAtoms::cols;
nsIAtom* nsHTMLAtoms::colspan;
nsIAtom* nsHTMLAtoms::compact;
nsIAtom* nsHTMLAtoms::coords;
nsIAtom* nsHTMLAtoms::data;
nsIAtom* nsHTMLAtoms::dir;
nsIAtom* nsHTMLAtoms::disabled;
nsIAtom* nsHTMLAtoms::div;
nsIAtom* nsHTMLAtoms::dl;
nsIAtom* nsHTMLAtoms::encoding;
nsIAtom* nsHTMLAtoms::face;
nsIAtom* nsHTMLAtoms::font;
nsIAtom* nsHTMLAtoms::fontWeight;
nsIAtom* nsHTMLAtoms::frameborder;
nsIAtom* nsHTMLAtoms::gutter;
nsIAtom* nsHTMLAtoms::h1;
nsIAtom* nsHTMLAtoms::h2;
nsIAtom* nsHTMLAtoms::h3;
nsIAtom* nsHTMLAtoms::h4;
nsIAtom* nsHTMLAtoms::h5;
nsIAtom* nsHTMLAtoms::h6;
nsIAtom* nsHTMLAtoms::height;
nsIAtom* nsHTMLAtoms::hidden;
nsIAtom* nsHTMLAtoms::href;
nsIAtom* nsHTMLAtoms::hspace;
nsIAtom* nsHTMLAtoms::httpEquiv;
nsIAtom* nsHTMLAtoms::id;
nsIAtom* nsHTMLAtoms::ismap;
nsIAtom* nsHTMLAtoms::language;
nsIAtom* nsHTMLAtoms::li;
nsIAtom* nsHTMLAtoms::link;
nsIAtom* nsHTMLAtoms::left;
nsIAtom* nsHTMLAtoms::leftpadding;
nsIAtom* nsHTMLAtoms::lowsrc;
nsIAtom* nsHTMLAtoms::marginheight;
nsIAtom* nsHTMLAtoms::marginwidth;
nsIAtom* nsHTMLAtoms::maxlength;
nsIAtom* nsHTMLAtoms::mayscript;
nsIAtom* nsHTMLAtoms::menu;
nsIAtom* nsHTMLAtoms::method;
nsIAtom* nsHTMLAtoms::multicol;
nsIAtom* nsHTMLAtoms::multiple;
nsIAtom* nsHTMLAtoms::name;
nsIAtom* nsHTMLAtoms::noresize;
nsIAtom* nsHTMLAtoms::noshade;
nsIAtom* nsHTMLAtoms::nowrap;
nsIAtom* nsHTMLAtoms::ol;
nsIAtom* nsHTMLAtoms::onblur;
nsIAtom* nsHTMLAtoms::onfocus;
nsIAtom* nsHTMLAtoms::onload;
nsIAtom* nsHTMLAtoms::onunload;
nsIAtom* nsHTMLAtoms::overflow;
nsIAtom* nsHTMLAtoms::p;
nsIAtom* nsHTMLAtoms::pagex;
nsIAtom* nsHTMLAtoms::pagey;
nsIAtom* nsHTMLAtoms::pointSize;
nsIAtom* nsHTMLAtoms::pre;
nsIAtom* nsHTMLAtoms::prompt;
nsIAtom* nsHTMLAtoms::readonly;
nsIAtom* nsHTMLAtoms::rel;
nsIAtom* nsHTMLAtoms::rightpadding;
nsIAtom* nsHTMLAtoms::rows;
nsIAtom* nsHTMLAtoms::rowspan;
nsIAtom* nsHTMLAtoms::scrolling;
nsIAtom* nsHTMLAtoms::selected;
nsIAtom* nsHTMLAtoms::shape;
nsIAtom* nsHTMLAtoms::size;
nsIAtom* nsHTMLAtoms::src;
nsIAtom* nsHTMLAtoms::start;
nsIAtom* nsHTMLAtoms::style;
nsIAtom* nsHTMLAtoms::suppress;
nsIAtom* nsHTMLAtoms::table;
nsIAtom* nsHTMLAtoms::tabstop;
nsIAtom* nsHTMLAtoms::target;
nsIAtom* nsHTMLAtoms::text;
nsIAtom* nsHTMLAtoms::top;
nsIAtom* nsHTMLAtoms::toppadding;
nsIAtom* nsHTMLAtoms::type;
nsIAtom* nsHTMLAtoms::ul;
nsIAtom* nsHTMLAtoms::usemap;
nsIAtom* nsHTMLAtoms::valign;
nsIAtom* nsHTMLAtoms::value;
nsIAtom* nsHTMLAtoms::variable;
nsIAtom* nsHTMLAtoms::visibility;
nsIAtom* nsHTMLAtoms::vlink;
nsIAtom* nsHTMLAtoms::vspace;
nsIAtom* nsHTMLAtoms::width;
nsIAtom* nsHTMLAtoms::wrap;
nsIAtom* nsHTMLAtoms::zindex;


static nsrefcnt gRefCnt;

void nsHTMLAtoms::AddrefAtoms()
{
  if (0 == gRefCnt) {
    a = NS_NewAtom("A");
    above = NS_NewAtom("ABOVE");
    action = NS_NewAtom("ACTION");
    align = NS_NewAtom("ALIGN");
    alink = NS_NewAtom("ALINK");
    alt = NS_NewAtom("ALT");
    archive = NS_NewAtom("ARCHIVE");
    background = NS_NewAtom("BACKGROUND");
    below = NS_NewAtom("BELOW");
    bgcolor = NS_NewAtom("BGCOLOR");
    body = NS_NewAtom("BODY");
    border = NS_NewAtom("BORDER");
    bordercolor = NS_NewAtom("BORDERCOLOR");
    bottompadding = NS_NewAtom("BOTTOMPADDING");
    br = NS_NewAtom("BR");
    cellpadding = NS_NewAtom("CELLPADDING");
    cellspacing = NS_NewAtom("CELLSPACING");
    checked = NS_NewAtom("CHECKED");
    kClass = NS_NewAtom("CLASS");
    classid = NS_NewAtom("CLASSID");
    clear = NS_NewAtom("CLEAR");
    clip = NS_NewAtom("CLIP");
    code = NS_NewAtom("CODE");
    codebase = NS_NewAtom("CODEBASE");
    color = NS_NewAtom("COLOR");
    cols = NS_NewAtom("COLS");
    colspan = NS_NewAtom("COLSPAN");
    compact = NS_NewAtom("COMPACT");
    coords = NS_NewAtom("COORDS");
    dir = NS_NewAtom("DIR");
    div = NS_NewAtom("DIV");
    disabled = NS_NewAtom("DISABLED");
    dl = NS_NewAtom("DL");
    data = NS_NewAtom("DATA");
    encoding = NS_NewAtom("ENCODING");
    face = NS_NewAtom("FACE");
    font = NS_NewAtom("FONT");
    fontWeight = NS_NewAtom("FONT-WEIGHT");
    frameborder = NS_NewAtom("FRAMEBORDER");
    gutter = NS_NewAtom("GUTTER");
    h1 = NS_NewAtom("H1");
    h2 = NS_NewAtom("H2");
    h3 = NS_NewAtom("H3");
    h4 = NS_NewAtom("H4");
    h5 = NS_NewAtom("H5");
    h6 = NS_NewAtom("H6");
    height = NS_NewAtom("HEIGHT");
    hidden = NS_NewAtom("HIDDEN");
    href = NS_NewAtom("HREF");
    hspace = NS_NewAtom("HSPACE");
    httpEquiv = NS_NewAtom("HTTP-EQUIV");
    id = NS_NewAtom("ID");
    ismap = NS_NewAtom("ISMAP");
    language = NS_NewAtom("LANGUAGE");
    li = NS_NewAtom("LI");
    link = NS_NewAtom("LINK");
    left = NS_NewAtom("LEFT");
    leftpadding = NS_NewAtom("LEFTPADDING");
    lowsrc = NS_NewAtom("LOWSRC");
    marginheight = NS_NewAtom("MARGINHEIGHT");
    marginwidth = NS_NewAtom("MARGINWIDTH");
    maxlength = NS_NewAtom("MAXLENGTH");
    mayscript = NS_NewAtom("MAYSCRIPT");
    menu = NS_NewAtom("MENU");
    method = NS_NewAtom("METHOD");
    multicol = NS_NewAtom("MULTICOL");
    multiple = NS_NewAtom("MULTIPLE");
    name = NS_NewAtom("NAME");
    noresize = NS_NewAtom("NORESIZE");
    noshade = NS_NewAtom("NOSHADE");
    nowrap = NS_NewAtom("NOWRAP");
    ol = NS_NewAtom("OL");
    onblur = NS_NewAtom("ONBLUR");
    onfocus = NS_NewAtom("ONFOCUS");
    onload = NS_NewAtom("ONLOAD");
    onunload = NS_NewAtom("ONUNLOAD");
    overflow = NS_NewAtom("OVERFLOW");
    p = NS_NewAtom("P");
    pagex = NS_NewAtom("PAGEX");
    pagey = NS_NewAtom("PAGEY");
    pointSize = NS_NewAtom("POINT-SIZE");
    pre = NS_NewAtom("PRE");
    prompt = NS_NewAtom("PROMPT");
    readonly = NS_NewAtom("READONLY");
    rel = NS_NewAtom("REL");
    rightpadding = NS_NewAtom("RIGHTPADDING");
    rows = NS_NewAtom("ROWS");
    rowspan = NS_NewAtom("ROWSPAN");
    scrolling = NS_NewAtom("SCROLLING");
    selected = NS_NewAtom("SELECTED");
    shape = NS_NewAtom("SHAPE");
    size = NS_NewAtom("SIZE");
    src = NS_NewAtom("SRC");
    start = NS_NewAtom("START");
    style = NS_NewAtom("STYLE");
    suppress = NS_NewAtom("SUPPRESS");
    table = NS_NewAtom("TABLE");
    tabstop = NS_NewAtom("TABSTOP");
    target = NS_NewAtom("TARGET");
    text = NS_NewAtom("TEXT");
    top = NS_NewAtom("TOP");
    toppadding = NS_NewAtom("TOPPADDING");
    type = NS_NewAtom("TYPE");
    ul = NS_NewAtom("UL");
    usemap = NS_NewAtom("USEMAP");
    valign = NS_NewAtom("VALIGN");
    value = NS_NewAtom("VALUE");
    variable = NS_NewAtom("VARIABLE");
    visibility = NS_NewAtom("VISIBILITY");
    vlink = NS_NewAtom("VLINK");
    vspace = NS_NewAtom("VSPACE");
    width = NS_NewAtom("WIDTH");
    wrap = NS_NewAtom("WRAP");
    zindex = NS_NewAtom("ZINDEX");
  }
  ++gRefCnt;
}

void nsHTMLAtoms::ReleaseAtoms()
{
  NS_PRECONDITION(gRefCnt != 0, "bad release atoms");
  if (--gRefCnt == 0) {
    NS_RELEASE(a);
    NS_RELEASE(above);
    NS_RELEASE(action);
    NS_RELEASE(align);
    NS_RELEASE(alink);
    NS_RELEASE(alt);
    NS_RELEASE(archive);
    NS_RELEASE(background);
    NS_RELEASE(below);
    NS_RELEASE(bgcolor);
    NS_RELEASE(body);
    NS_RELEASE(border);
    NS_RELEASE(bordercolor);
    NS_RELEASE(bottompadding);
    NS_RELEASE(br);
    NS_RELEASE(cellpadding);
    NS_RELEASE(cellspacing);
    NS_RELEASE(checked);
    NS_RELEASE(kClass);
    NS_RELEASE(classid);
    NS_RELEASE(clear);
    NS_RELEASE(clip);
    NS_RELEASE(code);
    NS_RELEASE(codebase);
    NS_RELEASE(color);
    NS_RELEASE(cols);
    NS_RELEASE(colspan);
    NS_RELEASE(compact);
    NS_RELEASE(coords);
    NS_RELEASE(dir);
    NS_RELEASE(disabled);
    NS_RELEASE(div);
    NS_RELEASE(dl);
    NS_RELEASE(data);
    NS_RELEASE(encoding);
    NS_RELEASE(face);
    NS_RELEASE(font);
    NS_RELEASE(fontWeight);
    NS_RELEASE(frameborder);
    NS_RELEASE(gutter);
    NS_RELEASE(h1);
    NS_RELEASE(h2);
    NS_RELEASE(h3);
    NS_RELEASE(h4);
    NS_RELEASE(h5);
    NS_RELEASE(h6);
    NS_RELEASE(height);
    NS_RELEASE(hidden);
    NS_RELEASE(href);
    NS_RELEASE(hspace);
    NS_RELEASE(httpEquiv);
    NS_RELEASE(id);
    NS_RELEASE(ismap);
    NS_RELEASE(language);
    NS_RELEASE(li);
    NS_RELEASE(link);
    NS_RELEASE(left);
    NS_RELEASE(leftpadding);
    NS_RELEASE(lowsrc);
    NS_RELEASE(marginheight);
    NS_RELEASE(marginwidth);
    NS_RELEASE(maxlength);
    NS_RELEASE(mayscript);
    NS_RELEASE(menu);
    NS_RELEASE(method);
    NS_RELEASE(multicol);
    NS_RELEASE(multiple);
    NS_RELEASE(name);
    NS_RELEASE(noresize);
    NS_RELEASE(noshade);
    NS_RELEASE(nowrap);
    NS_RELEASE(ol);
    NS_RELEASE(onblur);
    NS_RELEASE(onfocus);
    NS_RELEASE(onload);
    NS_RELEASE(onunload);
    NS_RELEASE(overflow);
    NS_RELEASE(p);
    NS_RELEASE(pagex);
    NS_RELEASE(pagey);
    NS_RELEASE(pointSize);
    NS_RELEASE(pre);
    NS_RELEASE(prompt);
    NS_RELEASE(readonly);
    NS_RELEASE(rel);
    NS_RELEASE(rightpadding);
    NS_RELEASE(rows);
    NS_RELEASE(rowspan);
    NS_RELEASE(scrolling);
    NS_RELEASE(selected);
    NS_RELEASE(shape);
    NS_RELEASE(size);
    NS_RELEASE(src);
    NS_RELEASE(start);
    NS_RELEASE(style);
    NS_RELEASE(suppress);
    NS_RELEASE(table);
    NS_RELEASE(tabstop);
    NS_RELEASE(target);
    NS_RELEASE(text);
    NS_RELEASE(top);
    NS_RELEASE(toppadding);
    NS_RELEASE(type);
    NS_RELEASE(ul);
    NS_RELEASE(usemap);
    NS_RELEASE(valign);
    NS_RELEASE(value);
    NS_RELEASE(variable);
    NS_RELEASE(visibility);
    NS_RELEASE(vlink);
    NS_RELEASE(vspace);
    NS_RELEASE(width);
    NS_RELEASE(wrap);
    NS_RELEASE(zindex);
  }
}

