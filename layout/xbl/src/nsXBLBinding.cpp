/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 *
 * The contents of this file are subject to the Netscape Public
 * License Version 1.1 (the "License"); you may not use this file
 * except in compliance with the License. You may obtain a copy of
 * the License at http://www.mozilla.org/NPL/
 *
 * Software distributed under the License is distributed on an "AS
 * IS" basis, WITHOUT WARRANTY OF ANY KIND, either express or
 * implied. See the License for the specific language governing
 * rights and limitations under the License.
 *
 * The Original Code is Mozilla Communicator client code.
 *
 * The Initial Developer of the Original Code is Netscape Communications
 * Corporation.  Portions created by Netscape are
 * Copyright (C) 1998 Netscape Communications Corporation. All
 * Rights Reserved.
 *
 * Original Author: David W. Hyatt (hyatt@netscape.com)
 *
 * Contributor(s): 
 */

#include "nsCOMPtr.h"
#include "nsIXBLBinding.h"
#include "nsIInputStream.h"
#include "nsINameSpaceManager.h"
#include "nsHashtable.h"
#include "nsIURI.h"
#include "nsIURL.h"
#include "nsIDOMEventReceiver.h"
#include "nsIChannel.h"
#include "nsXPIDLString.h"
#include "nsIParser.h"
#include "nsParserCIID.h"
#include "nsNetUtil.h"
#include "plstr.h"
#include "nsIContent.h"
#include "nsIDocument.h"
#include "nsIXMLContent.h"
#include "nsIXULContent.h"
#include "nsIXMLContentSink.h"
#include "nsLayoutCID.h"
#include "nsXMLDocument.h"
#include "nsIDOMElement.h"
#include "nsIDOMText.h"
#include "nsSupportsArray.h"
#include "nsINameSpace.h"
#include "nsJSUtils.h"
#include "nsIJSRuntimeService.h"
#include "nsXBLService.h"

// Event listeners
#include "nsIEventListenerManager.h"
#include "nsIDOMMouseListener.h"
#include "nsIDOMMouseMotionListener.h"
#include "nsIDOMLoadListener.h"
#include "nsIDOMFocusListener.h"
#include "nsIDOMPaintListener.h"
#include "nsIDOMKeyListener.h"
#include "nsIDOMFormListener.h"
#include "nsIDOMMenuListener.h"
#include "nsIDOMDragListener.h"

#include "nsIDOMAttr.h"
#include "nsIDOMNamedNodeMap.h"

#include "nsXBLEventHandler.h"
#include "nsIXBLBinding.h"

// Static IIDs/CIDs. Try to minimize these.
static char kNameSpaceSeparator = ':';

// Helper classes
// {A2892B81-CED9-11d3-97FB-00400553EEF0}
#define NS_IXBLATTR_IID \
{ 0xa2892b81, 0xced9, 0x11d3, { 0x97, 0xfb, 0x0, 0x40, 0x5, 0x53, 0xee, 0xf0 } }

class nsIXBLAttributeEntry : public nsISupports {
public:
  static const nsIID& GetIID() { static nsIID iid = NS_IXBLATTR_IID; return iid; }

  NS_IMETHOD GetAttribute(nsIAtom** aResult) = 0;
  NS_IMETHOD GetElement(nsIContent** aResult) = 0;
  NS_IMETHOD GetNext(nsIXBLAttributeEntry** aResult) = 0;
  NS_IMETHOD SetNext(nsIXBLAttributeEntry* aEntry) = 0;
};
  

class nsXBLAttributeEntry : public nsIXBLAttributeEntry {
public:
  NS_IMETHOD GetAttribute(nsIAtom** aResult) { *aResult = mAttribute; NS_IF_ADDREF(*aResult); return NS_OK; };
  NS_IMETHOD GetElement(nsIContent** aResult) { *aResult = mElement; NS_IF_ADDREF(*aResult); return NS_OK; };

  NS_IMETHOD GetNext(nsIXBLAttributeEntry** aResult) { NS_IF_ADDREF(*aResult = mNext); return NS_OK; }
  NS_IMETHOD SetNext(nsIXBLAttributeEntry* aEntry) { mNext = aEntry; return NS_OK; }

  nsCOMPtr<nsIContent> mElement;
  nsCOMPtr<nsIAtom> mAttribute;
  nsCOMPtr<nsIXBLAttributeEntry> mNext;

  nsXBLAttributeEntry(nsIAtom* aAtom, nsIContent* aContent) {
    NS_INIT_REFCNT(); mAttribute = aAtom; mElement = aContent;
  };

  virtual ~nsXBLAttributeEntry() {};

  NS_DECL_ISUPPORTS
};

NS_IMPL_ISUPPORTS1(nsXBLAttributeEntry, nsIXBLAttributeEntry)

/***********************************************************************/
//
// The JS class for XBLBinding
//
PR_STATIC_CALLBACK(void)
XBLFinalize(JSContext *cx, JSObject *obj)
{
  nsJSUtils::nsGenericFinalize(cx, obj);
}

//
// XULElement constructor
//
PR_STATIC_CALLBACK(JSBool)
XBLBindingCtor(JSContext *cx, JSObject *obj, uintN argc, jsval *argv, jsval *rval)
{
  return JS_FALSE;
}

// *********************************************************************/
// The XBLBinding class

class nsXBLBinding: public nsIXBLBinding
{
  NS_DECL_ISUPPORTS

  // nsIXBLBinding
  NS_IMETHOD GetBaseBinding(nsIXBLBinding** aResult);
  NS_IMETHOD SetBaseBinding(nsIXBLBinding* aBinding);

  NS_IMETHOD GetAnonymousContent(nsIContent** aParent);
  NS_IMETHOD SetAnonymousContent(nsIContent* aParent);

  NS_IMETHOD GetBindingElement(nsIContent** aResult);
  NS_IMETHOD SetBindingElement(nsIContent* aElement);

  NS_IMETHOD GenerateAnonymousContent(nsIContent* aBoundElement);
  NS_IMETHOD InstallEventHandlers(nsIContent* aBoundElement);
  NS_IMETHOD InstallProperties(nsIContent* aBoundElement);

  NS_IMETHOD GetBaseTag(PRInt32* aNameSpaceID, nsIAtom** aResult);

  NS_IMETHOD AttributeChanged(nsIAtom* aAttribute, PRInt32 aNameSpaceID, PRBool aRemoveFlag);

  NS_IMETHOD ChangeDocument(nsIDocument* aOldDocument, nsIDocument* aNewDocument);

  NS_IMETHOD GetBindingURI(nsString& aResult);
  
  NS_IMETHOD GetInsertionPoint(nsIContent* aChild, nsIContent** aResult);
  NS_IMETHOD GetSingleInsertionPoint(nsIContent** aResult, PRBool* aMultipleInsertionPoints);

public:
  nsXBLBinding();
  virtual ~nsXBLBinding();

  NS_IMETHOD AddScriptEventListener(nsIContent* aElement, nsIAtom* aName, const nsString& aValue, REFNSIID aIID);

  PRBool AllowScripts();

  static nsresult GetTextData(nsIContent *aParent, nsString& aResult);
  
// Static members
  static PRUint32 gRefCnt;
  
  static nsIAtom* kContentAtom;
  static nsIAtom* kInterfaceAtom;
  static nsIAtom* kHandlersAtom;
  static nsIAtom* kExcludesAtom;
  static nsIAtom* kIncludesAtom;
  static nsIAtom* kInheritsAtom;
  static nsIAtom* kTypeAtom;
  static nsIAtom* kCapturerAtom;
  static nsIAtom* kExtendsAtom;
  static nsIAtom* kChildrenAtom;
  static nsIAtom* kMethodAtom;
  static nsIAtom* kArgumentAtom;
  static nsIAtom* kBodyAtom;
  static nsIAtom* kPropertyAtom;
  static nsIAtom* kOnSetAtom;
  static nsIAtom* kOnGetAtom;
  static nsIAtom* kGetterAtom;
  static nsIAtom* kSetterAtom;
  static nsIAtom* kHTMLAtom;
  static nsIAtom* kValueAtom;
  static nsIAtom* kNameAtom;
  static nsIAtom* kReadOnlyAtom;
  static nsIAtom* kURIAtom;

  // Used to easily obtain the correct IID for an event.
  struct EventHandlerMapEntry {
    const char*  mAttributeName;
    nsIAtom*     mAttributeAtom;
    const nsIID* mHandlerIID;
  };

  static EventHandlerMapEntry kEventHandlerMap[];

// Internal member functions
protected:
  NS_IMETHOD InitClass(const nsCString& aClassName,
                       nsIScriptContext* aContext, nsIDocument* aDocument,
                       void** aScriptObject, void** aClassObject);

  void GetImmediateChild(nsIAtom* aTag, nsIContent** aResult);
  void GetNestedChild(nsIAtom* aTag, nsIContent* aContent, nsIContent** aResult);
  void GetNestedChildren(nsIAtom* aTag, nsIContent* aContent, nsISupportsArray* aList);
  void BuildInsertionTable();
  void GetNestedChildren();
  PRBool IsInExcludesList(nsIAtom* aTag, const nsString& aList);

  NS_IMETHOD ConstructAttributeTable(nsIContent* aElement); 

  PRBool IsMouseHandler(const nsString& aName);
  PRBool IsKeyHandler(const nsString& aName);
  PRBool IsFocusHandler(const nsString& aName);
  PRBool IsXULHandler(const nsString& aName);

  static void GetEventHandlerIID(nsIAtom* aName, nsIID* aIID, PRBool* aFound);

// MEMBER VARIABLES
protected:
  nsCOMPtr<nsIContent> mBinding; // Strong. As long as we're around, the binding can't go away.
  nsCOMPtr<nsIContent> mContent; // Strong. Our anonymous content stays around with us.
  nsCOMPtr<nsIXBLBinding> mNextBinding; // Strong. The derived binding owns the base class bindings.
     
  nsIContent* mBoundElement; // [WEAK] We have a reference, but we don't own it.
  
  nsSupportsHashtable* mAttributeTable; // A table for attribute entries.
  nsSupportsHashtable* mInsertionPointTable; // A table of insertion points.
};

// Static initialization
PRUint32 nsXBLBinding::gRefCnt = 0;
 
nsIAtom* nsXBLBinding::kContentAtom = nsnull;
nsIAtom* nsXBLBinding::kInterfaceAtom = nsnull;
nsIAtom* nsXBLBinding::kHandlersAtom = nsnull;
nsIAtom* nsXBLBinding::kExcludesAtom = nsnull;
nsIAtom* nsXBLBinding::kIncludesAtom = nsnull;
nsIAtom* nsXBLBinding::kInheritsAtom = nsnull;
nsIAtom* nsXBLBinding::kTypeAtom = nsnull;
nsIAtom* nsXBLBinding::kCapturerAtom = nsnull;
nsIAtom* nsXBLBinding::kExtendsAtom = nsnull;
nsIAtom* nsXBLBinding::kChildrenAtom = nsnull;
nsIAtom* nsXBLBinding::kValueAtom = nsnull;
nsIAtom* nsXBLBinding::kHTMLAtom = nsnull;
nsIAtom* nsXBLBinding::kMethodAtom = nsnull;
nsIAtom* nsXBLBinding::kArgumentAtom = nsnull;
nsIAtom* nsXBLBinding::kBodyAtom = nsnull;
nsIAtom* nsXBLBinding::kPropertyAtom = nsnull;
nsIAtom* nsXBLBinding::kOnSetAtom = nsnull;
nsIAtom* nsXBLBinding::kOnGetAtom = nsnull;
nsIAtom* nsXBLBinding::kGetterAtom = nsnull;
nsIAtom* nsXBLBinding::kSetterAtom = nsnull;
nsIAtom* nsXBLBinding::kNameAtom = nsnull;
nsIAtom* nsXBLBinding::kReadOnlyAtom = nsnull;
nsIAtom* nsXBLBinding::kURIAtom = nsnull;

nsXBLBinding::EventHandlerMapEntry
nsXBLBinding::kEventHandlerMap[] = {
    { "click",         nsnull, &NS_GET_IID(nsIDOMMouseListener)       },
    { "dblclick",      nsnull, &NS_GET_IID(nsIDOMMouseListener)       },
    { "mousedown",     nsnull, &NS_GET_IID(nsIDOMMouseListener)       },
    { "mouseup",       nsnull, &NS_GET_IID(nsIDOMMouseListener)       },
    { "mouseover",     nsnull, &NS_GET_IID(nsIDOMMouseListener)       },
    { "mouseout",      nsnull, &NS_GET_IID(nsIDOMMouseListener)       },

    { "mousemove",     nsnull, &NS_GET_IID(nsIDOMMouseMotionListener) },

    { "keydown",       nsnull, &NS_GET_IID(nsIDOMKeyListener)         },
    { "keyup",         nsnull, &NS_GET_IID(nsIDOMKeyListener)         },
    { "keypress",      nsnull, &NS_GET_IID(nsIDOMKeyListener)         },

    { "load",          nsnull, &NS_GET_IID(nsIDOMLoadListener)        },
    { "unload",        nsnull, &NS_GET_IID(nsIDOMLoadListener)        },
    { "abort",         nsnull, &NS_GET_IID(nsIDOMLoadListener)        },
    { "error",         nsnull, &NS_GET_IID(nsIDOMLoadListener)        },

    { "create",        nsnull, &NS_GET_IID(nsIDOMMenuListener)        },
    { "close",         nsnull, &NS_GET_IID(nsIDOMMenuListener)        },
    { "destroy",       nsnull, &NS_GET_IID(nsIDOMMenuListener)        },
    { "command",       nsnull, &NS_GET_IID(nsIDOMMenuListener)        },
    { "broadcast",     nsnull, &NS_GET_IID(nsIDOMMenuListener)        },
    { "commandupdate", nsnull, &NS_GET_IID(nsIDOMMenuListener)        },

    { "focus",         nsnull, &NS_GET_IID(nsIDOMFocusListener)       },
    { "blur",          nsnull, &NS_GET_IID(nsIDOMFocusListener)       },

    { "submit",        nsnull, &NS_GET_IID(nsIDOMFormListener)        },
    { "reset",         nsnull, &NS_GET_IID(nsIDOMFormListener)        },
    { "change",        nsnull, &NS_GET_IID(nsIDOMFormListener)        },
    { "select",        nsnull, &NS_GET_IID(nsIDOMFormListener)        },
    { "input",         nsnull, &NS_GET_IID(nsIDOMFormListener)        },

    { "paint",         nsnull, &NS_GET_IID(nsIDOMPaintListener)       },
    
    { "dragenter",     nsnull, &NS_GET_IID(nsIDOMDragListener)        },
    { "dragover",      nsnull, &NS_GET_IID(nsIDOMDragListener)        },
    { "dragexit",      nsnull, &NS_GET_IID(nsIDOMDragListener)        },
    { "dragdrop",      nsnull, &NS_GET_IID(nsIDOMDragListener)        },
    { "draggesture",   nsnull, &NS_GET_IID(nsIDOMDragListener)        },

    { nsnull,            nsnull, nsnull                                 }
};

// Implementation /////////////////////////////////////////////////////////////////

// Implement our nsISupports methods
NS_IMPL_ISUPPORTS1(nsXBLBinding, nsIXBLBinding)

// Constructors/Destructors
nsXBLBinding::nsXBLBinding(void)
: mAttributeTable(nsnull),
  mInsertionPointTable(nsnull)
{
  NS_INIT_REFCNT();
  gRefCnt++;
  if (gRefCnt == 1) {
    kContentAtom = NS_NewAtom("content");
    kInterfaceAtom = NS_NewAtom("interface");
    kHandlersAtom = NS_NewAtom("handlers");
    kExcludesAtom = NS_NewAtom("excludes");
    kIncludesAtom = NS_NewAtom("includes");
    kInheritsAtom = NS_NewAtom("inherits");
    kTypeAtom = NS_NewAtom("type");
    kCapturerAtom = NS_NewAtom("capturer");
    kExtendsAtom = NS_NewAtom("extends");
    kChildrenAtom = NS_NewAtom("children");
    kHTMLAtom = NS_NewAtom("html");
    kValueAtom = NS_NewAtom("value");
    kMethodAtom = NS_NewAtom("method");
    kArgumentAtom = NS_NewAtom("argument");
    kBodyAtom = NS_NewAtom("body");
    kPropertyAtom = NS_NewAtom("property");
    kOnSetAtom = NS_NewAtom("onset");
    kOnGetAtom = NS_NewAtom("onget");
    kGetterAtom = NS_NewAtom("getter");
    kSetterAtom = NS_NewAtom("setter");    
    kNameAtom = NS_NewAtom("name");
    kReadOnlyAtom = NS_NewAtom("readonly");
    kURIAtom = NS_NewAtom("uri");

    EventHandlerMapEntry* entry = kEventHandlerMap;
    while (entry->mAttributeName) {
      entry->mAttributeAtom = NS_NewAtom(entry->mAttributeName);
      ++entry;
    }
  }
}


nsXBLBinding::~nsXBLBinding(void)
{
  delete mAttributeTable;
  delete mInsertionPointTable;

  gRefCnt--;
  if (gRefCnt == 0) {
    NS_RELEASE(kContentAtom);
    NS_RELEASE(kInterfaceAtom);
    NS_RELEASE(kHandlersAtom);
    NS_RELEASE(kExcludesAtom);
    NS_RELEASE(kIncludesAtom);
    NS_RELEASE(kInheritsAtom);
    NS_RELEASE(kTypeAtom);
    NS_RELEASE(kCapturerAtom);
    NS_RELEASE(kExtendsAtom);
    NS_RELEASE(kChildrenAtom);
    NS_RELEASE(kHTMLAtom);
    NS_RELEASE(kValueAtom);
    NS_RELEASE(kMethodAtom);
    NS_RELEASE(kArgumentAtom);
    NS_RELEASE(kBodyAtom);
    NS_RELEASE(kPropertyAtom); 
    NS_RELEASE(kOnSetAtom);
    NS_RELEASE(kOnGetAtom);
    NS_RELEASE(kGetterAtom);
    NS_RELEASE(kSetterAtom);
    NS_RELEASE(kNameAtom);
    NS_RELEASE(kReadOnlyAtom);
    NS_RELEASE(kURIAtom);

    EventHandlerMapEntry* entry = kEventHandlerMap;
    while (entry->mAttributeName) {
      NS_IF_RELEASE(entry->mAttributeAtom);
      ++entry;
    }
  }
}

// nsIXBLBinding Interface ////////////////////////////////////////////////////////////////

NS_IMETHODIMP
nsXBLBinding::GetBaseBinding(nsIXBLBinding** aResult)
{
  *aResult = mNextBinding;
  NS_IF_ADDREF(*aResult);
  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::SetBaseBinding(nsIXBLBinding* aBinding)
{
  mNextBinding = aBinding; // Comptr handles rel/add
  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::GetAnonymousContent(nsIContent** aResult)
{
  *aResult = mContent;
  NS_IF_ADDREF(*aResult);
  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::SetAnonymousContent(nsIContent* aParent)
{
  // First cache the element.
  mContent = aParent;

  // Now we need to ensure two things.
  // (1) The anonymous content should be fooled into thinking it's in the bound
  // element's document.
  nsCOMPtr<nsIDocument> doc;
  mBoundElement->GetDocument(*getter_AddRefs(doc));

  mContent->SetDocument(doc, PR_TRUE, AllowScripts());
  
  // (2) The children's parent back pointer should not be to this synthetic root
  // but should instead point to the bound element.
  PRInt32 childCount;
  mContent->ChildCount(childCount);
  for (PRInt32 i = 0; i < childCount; i++) {
    nsCOMPtr<nsIContent> child;
    mContent->ChildAt(i, *getter_AddRefs(child));
    child->SetParent(mBoundElement);
  }

  // (3) We need to insert entries into our attribute table for any elements
  // that are inheriting attributes.  This table allows us to quickly determine 
  // which elements in our anonymous content need to be updated when attributes change.
  ConstructAttributeTable(aParent);
  
  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::GetBindingElement(nsIContent** aResult)
{
  *aResult = mBinding;
  NS_IF_ADDREF(*aResult);
  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::SetBindingElement(nsIContent* aElement)
{
  mBinding = aElement;
  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::GenerateAnonymousContent(nsIContent* aBoundElement)
{
  // Set our bound element.
  mBoundElement = aBoundElement;

  // Fetch the content element for this binding.
  nsCOMPtr<nsIContent> content;
  GetImmediateChild(kContentAtom, getter_AddRefs(content));

  if (!content) {
    // We have no anonymous content.
    if (mNextBinding)
      return mNextBinding->GenerateAnonymousContent(aBoundElement);
    else return NS_OK;
  }

  // Plan to build the content by default.
  PRBool buildContent = PR_TRUE;
  PRInt32 childCount;
  aBoundElement->ChildCount(childCount);
  if (childCount > 0) {
    // See if there's an excludes attribute.
    // We'll only build content if all the explicit children are 
    // in the excludes list.
    nsAutoString excludes;
    content->GetAttribute(kNameSpaceID_None, kExcludesAtom, excludes);
    if (!excludes.EqualsWithConversion("*")) {
      if (!excludes.IsEmpty()) {
        // Walk the children and ensure that all of them
        // are in the excludes array.
        for (PRInt32 i = 0; i < childCount; i++) {
          nsCOMPtr<nsIContent> child;
          aBoundElement->ChildAt(i, *getter_AddRefs(child));
          nsCOMPtr<nsIAtom> tag;
          child->GetTag(*getter_AddRefs(tag));
          if (!IsInExcludesList(tag, excludes)) {
            buildContent = PR_FALSE;
            break;
          }
        }
      }
      else buildContent = PR_FALSE;
    }
  }
  
  nsCOMPtr<nsIContent> childrenElement;
  // see if we have a <children/> element
  GetNestedChild(kChildrenAtom, content, getter_AddRefs(childrenElement));
  if (childrenElement)
    buildContent = PR_TRUE;

  if (buildContent) {
     // Always check the content element for potential attributes.
    nsCOMPtr<nsIDOMNode> node(do_QueryInterface(content));
    nsCOMPtr<nsIDOMNamedNodeMap> namedMap;

    node->GetAttributes(getter_AddRefs(namedMap));
    PRUint32 length;
    namedMap->GetLength(&length);

    nsCOMPtr<nsIDOMNode> attribute;
    for (PRUint32 i = 0; i < length; ++i)
    {
      namedMap->Item(i, getter_AddRefs(attribute));
      nsCOMPtr<nsIDOMAttr> attr(do_QueryInterface(attribute));
      nsAutoString name;
      attr->GetName(name);
      if (!name.EqualsWithConversion("excludes")) {
        nsAutoString value;
        nsCOMPtr<nsIDOMElement> element(do_QueryInterface(mBoundElement));
        element->GetAttribute(name, value);
        if (value.IsEmpty()) {
          nsAutoString value2;
          attr->GetValue(value2);
          nsCOMPtr<nsIAtom> atom = getter_AddRefs(NS_NewAtom(name));
          mBoundElement->SetAttribute(kNameSpaceID_None, atom, value2, PR_FALSE);
        }
      }
    }
  
    nsCOMPtr<nsIDOMElement> domElement = do_QueryInterface(content);

    nsCOMPtr<nsIDOMNode> clonedNode;
    domElement->CloneNode(PR_TRUE, getter_AddRefs(clonedNode));
    
    nsCOMPtr<nsIContent> clonedContent = do_QueryInterface(clonedNode);
    SetAnonymousContent(clonedContent);

    if (childrenElement)
      BuildInsertionTable();
  }
  
  if (mNextBinding) {
    return mNextBinding->GenerateAnonymousContent(aBoundElement);
  }

  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::InstallEventHandlers(nsIContent* aBoundElement)
{
  // Fetch the handlers element for this binding.
  nsCOMPtr<nsIContent> handlers;
  GetImmediateChild(kHandlersAtom, getter_AddRefs(handlers));

  if (handlers && AllowScripts()) {
    // Now walk the handlers and add event listeners to the bound
    // element.
    PRInt32 childCount;
    handlers->ChildCount(childCount);
    for (PRInt32 i = 0; i < childCount; i++) {
      nsCOMPtr<nsIContent> child;
      handlers->ChildAt(i, *getter_AddRefs(child));

      // Fetch the type attribute.
      // XXX Deal with a comma-separated list of types
      nsAutoString type;
      child->GetAttribute(kNameSpaceID_None, kTypeAtom, type);
    
      if (!type.IsEmpty()) {
        nsCOMPtr<nsIAtom> eventAtom = getter_AddRefs(NS_NewAtom(type));
        PRBool found = PR_FALSE;
        nsIID iid;
        GetEventHandlerIID(eventAtom, &iid, &found);
        if (found) {
          // Add an event listener for mouse and key events only.
          PRBool mouse = IsMouseHandler(type);
          PRBool key = IsKeyHandler(type);
          PRBool focus = IsFocusHandler(type);
          PRBool xul = IsXULHandler(type);

          nsCOMPtr<nsIDOMEventReceiver> receiver = do_QueryInterface(mBoundElement);
            
          if (mouse || key || focus || xul) {
            // Create a new nsXBLEventHandler.
            nsXBLEventHandler* handler;
            NS_NewXBLEventHandler(mBoundElement, child, type, &handler);

            // Figure out if we're using capturing or not.
            PRBool useCapture = PR_FALSE;
            nsAutoString capturer;
            child->GetAttribute(kNameSpaceID_None, kCapturerAtom, capturer);
            if (capturer.EqualsWithConversion("true"))
              useCapture = PR_TRUE;

            // Add the event listener.
            if (mouse)
              receiver->AddEventListener(type, (nsIDOMMouseListener*)handler, useCapture);
            else if(key)
              receiver->AddEventListener(type, (nsIDOMKeyListener*)handler, useCapture);
            else if(focus)
              receiver->AddEventListener(type, (nsIDOMFocusListener*)handler, useCapture);
            else
              receiver->AddEventListener(type, (nsIDOMMenuListener*)handler, useCapture);

            NS_RELEASE(handler);
          }
          else {
            // Call AddScriptEventListener for other IID types
            nsAutoString value;
            child->GetAttribute(kNameSpaceID_None, kValueAtom, value);
            if (value.IsEmpty())
                GetTextData(child, value);

            AddScriptEventListener(mBoundElement, eventAtom, value, iid);
          }
        }
      }
    }
  }

  if (mNextBinding)
    mNextBinding->InstallEventHandlers(aBoundElement);

  return NS_OK;
}

const char* gPropertyArg[] = { "val" };

NS_IMETHODIMP
nsXBLBinding::InstallProperties(nsIContent* aBoundElement)
{
  // Always install the base class properties first, so that
  // derived classes can reference the base class properties.
  if (mNextBinding)
    mNextBinding->InstallProperties(aBoundElement);

   // Fetch the interface element for this binding.
  nsCOMPtr<nsIContent> interfaceElement;
  GetImmediateChild(kInterfaceAtom, getter_AddRefs(interfaceElement));

  if (interfaceElement && AllowScripts()) {
    // Get our bound element's script context.
    nsresult rv;
    nsCOMPtr<nsIDocument> document;
    mBoundElement->GetDocument(*getter_AddRefs(document));
    if (!document)
      return NS_OK;

    nsCOMPtr<nsIScriptGlobalObject> global;
    document->GetScriptGlobalObject(getter_AddRefs(global));

    if (!global)
      return NS_OK;

    nsCOMPtr<nsIScriptContext> context;
    rv = global->GetContext(getter_AddRefs(context));
    if (NS_FAILED(rv)) return rv;

    // Init our class and insert it into the prototype chain.
    nsAutoString className;
    interfaceElement->GetAttribute(kNameSpaceID_None, kNameAtom, className);
    if (className.IsEmpty()) {
      mBinding->GetAttribute(kNameSpaceID_None, kURIAtom, className);
      if (className.IsEmpty())
        return NS_ERROR_FAILURE;
    }

    nsCAutoString classStr; classStr.AssignWithConversion(className);

    JSObject* scriptObject;
    JSObject* classObject;
    if (NS_FAILED(rv = InitClass(classStr, context, document, (void**)&scriptObject, (void**)&classObject)))
      return rv;

    JSContext* cx = (JSContext*)context->GetNativeContext();

    // Do a walk.
    PRInt32 childCount;
    interfaceElement->ChildCount(childCount);
    for (PRInt32 i = 0; i < childCount; i++) {
      nsCOMPtr<nsIContent> child;
      interfaceElement->ChildAt(i, *getter_AddRefs(child));

      // See if we're a property or a method.
      nsCOMPtr<nsIAtom> tagName;
      child->GetTag(*getter_AddRefs(tagName));

      if (tagName.get() == kMethodAtom && classObject) {
        // Obtain our name attribute.
        nsAutoString name, body;
        child->GetAttribute(kNameSpaceID_None, kNameAtom, name);

        // Now walk all of our args.
        // XXX I'm lame. 32 max args allowed.
        char* args[32];
        PRUint32 argCount = 0;
        PRInt32 kidCount;
        child->ChildCount(kidCount);
        for (PRInt32 j = 0; j < kidCount; j++)
        {
          nsCOMPtr<nsIContent> arg;
          child->ChildAt(j, *getter_AddRefs(arg));
          nsCOMPtr<nsIAtom> kidTagName;
          arg->GetTag(*getter_AddRefs(kidTagName));
          if (kidTagName.get() == kArgumentAtom) {
            // Get the argname and add it to the array.
            nsAutoString argName;
            arg->GetAttribute(kNameSpaceID_None, kNameAtom, argName);
            char* argStr = argName.ToNewCString();
            args[argCount] = argStr;
            argCount++;
          }
          else if (kidTagName.get() == kBodyAtom) {
            PRInt32 textCount;
            arg->ChildCount(textCount);
            
            for (PRInt32 k = 0; k < textCount; k++) {
              // Get the child.
              nsCOMPtr<nsIContent> textChild;
              arg->ChildAt(k, *getter_AddRefs(textChild));
              nsCOMPtr<nsIDOMText> text(do_QueryInterface(textChild));
              if (text) {
                nsAutoString data;
                text->GetData(data);
                body += data;
              }
            }
          }
        }

        // Now that we have a body and args, compile the function
        // and then define it as a property.
        if (!body.IsEmpty()) {
          void* myFunc;
          nsCAutoString cname; cname.AssignWithConversion(name.GetUnicode());
          rv = context->CompileFunction(classObject,
                                        cname,
                                        argCount,
                                        (const char**)args,
                                        body, 
                                        nsnull,
                                        0,
                                        PR_FALSE,
                                        &myFunc);
        }
      }
      else if (tagName.get() == kPropertyAtom) {
        // Obtain our name attribute.
        nsAutoString name;
        child->GetAttribute(kNameSpaceID_None, kNameAtom, name);

        if (!name.IsEmpty()) {
          // We have a property.
          nsAutoString getter, setter, readOnly;
          child->GetAttribute(kNameSpaceID_None, kOnGetAtom, getter);
          child->GetAttribute(kNameSpaceID_None, kOnSetAtom, setter);
          child->GetAttribute(kNameSpaceID_None, kReadOnlyAtom, readOnly);

          void* getFunc = nsnull;
          void* setFunc = nsnull;
          uintN attrs = 0;

          if (readOnly.EqualsWithConversion("true"))
            attrs |= JSPROP_READONLY;

          // try for first <getter> tag
          if (getter.IsEmpty()) {
            PRInt32 childCount;
            child->ChildCount(childCount);

            nsCOMPtr<nsIContent> getterElement;
            for (PRInt32 j=0; j<childCount; j++) {
              child->ChildAt(j, *getter_AddRefs(getterElement));
              
              if (!getterElement) continue;
              
              nsCOMPtr<nsIAtom> getterTag;
              getterElement->GetTag(*getter_AddRefs(getterTag));
              
              if (getterTag.get() == kGetterAtom) {
                GetTextData(getterElement, getter);
                break;          // stop at first tag
              }
            }

          }
          
          if (!getter.IsEmpty() && classObject) {
            rv = context->CompileFunction(classObject,
                                          "onget",
                                          0,
                                          nsnull,
                                          getter, 
                                          nsnull,
                                          0,
                                          PR_FALSE,
                                          &getFunc);
            if (NS_FAILED(rv)) return NS_ERROR_FAILURE;
            attrs |= JSPROP_GETTER;
          }

          // try for first <setter> tag
          if (setter.IsEmpty()) {
            PRInt32 childCount;
            child->ChildCount(childCount);

            nsCOMPtr<nsIContent> setterElement;
            for (PRInt32 j=0; j<childCount; j++) {
              child->ChildAt(j, *getter_AddRefs(setterElement));
              
              if (!setterElement) continue;
              
              nsCOMPtr<nsIAtom> setterTag;
              setterElement->GetTag(*getter_AddRefs(setterTag));
              if (setterTag.get() == kSetterAtom) {
                GetTextData(setterElement, setter);
                break;          // stop at first tag
              }
            }
          }
          
          if (!setter.IsEmpty() && classObject) {
            rv = context->CompileFunction(classObject,
                                          "onset",
                                          1,
                                          gPropertyArg,
                                          setter, 
                                          nsnull,
                                          0,
                                          PR_FALSE,
                                          &setFunc);
            if (NS_FAILED(rv)) return NS_ERROR_FAILURE;
            attrs |= JSPROP_SETTER;
          }

          if ((getFunc || setFunc) && classObject) {
            // Having either a getter or setter results in the
            // destruction of any initial value that might be set.
            // This means we only have to worry about defining the getter
            // or setter.
            ::JS_DefineUCProperty(cx, (JSObject*)classObject, name.GetUnicode(), 
                                       name.Length(), JSVAL_VOID,
                                       (JSPropertyOp) getFunc, 
                                       (JSPropertyOp) setFunc, 
                                       attrs); 
          } else {
            // Look for a normal value and just define that.
            nsCOMPtr<nsIContent> textChild;
            PRInt32 textCount;
            child->ChildCount(textCount);
            nsAutoString answer;
            for (PRInt32 j = 0; j < textCount; j++) {
              // Get the child.
              child->ChildAt(j, *getter_AddRefs(textChild));
              nsCOMPtr<nsIDOMText> text(do_QueryInterface(textChild));
              if (text) {
                nsAutoString data;
                text->GetData(data);
                answer += data;
              }
            }

            if (!answer.IsEmpty()) {
              // Evaluate our script and obtain a value.
              jsval result = nsnull;
              PRBool undefined;
              rv = context->EvaluateStringWithValue(answer, 
                                           scriptObject,
                                           nsnull, nsnull, 0, nsnull,
                                           (void*) &result, &undefined);
              
              if (!undefined) {
                // Define that value as a property
                ::JS_DefineUCProperty(cx, (JSObject*)scriptObject, name.GetUnicode(), 
                                           name.Length(), result,
                                           nsnull, nsnull,
                                           attrs); 
              }
            }
          }
        }
      }
    }
  }

  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::GetBaseTag(PRInt32* aNameSpaceID, nsIAtom** aResult)
{
  if (mNextBinding)
    return mNextBinding->GetBaseTag(aNameSpaceID, aResult);

  // XXX Cache the value as a "base" attribute so that we don't do this
  // check over and over each time the bound element occurs.

  // We are the base binding. Obtain the extends attribute.
  nsAutoString extends;
  mBinding->GetAttribute(kNameSpaceID_None, kExtendsAtom, extends);

  if (!extends.IsEmpty()) {
    // Obtain the namespace prefix.
    nsAutoString prefix;
    PRInt32 offset = extends.FindChar(kNameSpaceSeparator);
    if (-1 != offset) {
      extends.Left(prefix, offset);
      extends.Cut(0, offset+1);
    }
    if (prefix.Length() > 0) {
      // Look up the prefix.
      nsCOMPtr<nsIAtom> prefixAtom = getter_AddRefs(NS_NewAtom(prefix));
      nsCOMPtr<nsINameSpace> nameSpace;
      nsCOMPtr<nsIXMLContent> xmlContent(do_QueryInterface(mBinding));
      if (xmlContent) {
        xmlContent->GetContainingNameSpace(*getter_AddRefs(nameSpace));

        if (nameSpace) {
          nsCOMPtr<nsINameSpace> tagSpace;
          nameSpace->FindNameSpace(prefixAtom, *getter_AddRefs(tagSpace));
          if (tagSpace) {
            // Score! Return the tag.
            tagSpace->GetNameSpaceID(*aNameSpaceID);
            *aResult = NS_NewAtom(extends); // The addref happens here
          }
        }
      }
    }
  }

  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::AttributeChanged(nsIAtom* aAttribute, PRInt32 aNameSpaceID, PRBool aRemoveFlag)
{
// XXX check to see if we inherit anonymous content from a base binding 
// if (mNextBinding)
//    mNextBinding->AttributeChanged(aAttribute, aNameSpaceID, aRemoveFlag);

  if (!mAttributeTable)
    return NS_OK;

  nsISupportsKey key(aAttribute);
  nsCOMPtr<nsISupports> supports = getter_AddRefs(NS_STATIC_CAST(nsISupports*, 
                                                                 mAttributeTable->Get(&key)));

  nsCOMPtr<nsIXBLAttributeEntry> xblAttr = do_QueryInterface(supports);
  if (!xblAttr)
    return NS_OK;

  // Iterate over the elements in the array.

  while (xblAttr) {
    nsCOMPtr<nsIContent> element;
    nsCOMPtr<nsIAtom> setAttr;
    xblAttr->GetElement(getter_AddRefs(element));
    xblAttr->GetAttribute(getter_AddRefs(setAttr));

    if (aRemoveFlag)
      element->UnsetAttribute(aNameSpaceID, setAttr, PR_TRUE);
    else {
      nsAutoString value;
      nsresult result = mBoundElement->GetAttribute(aNameSpaceID, aAttribute, value);
      PRBool attrPresent = (result == NS_CONTENT_ATTR_NO_VALUE ||
                            result == NS_CONTENT_ATTR_HAS_VALUE);

      if (attrPresent)
        element->SetAttribute(aNameSpaceID, setAttr, value, PR_TRUE);
    }

    // See if we're the <html> tag in XUL, and see if value is being
    // set or unset on us.
    nsCOMPtr<nsIAtom> tag;
    element->GetTag(*getter_AddRefs(tag));
    if ((tag.get() == kHTMLAtom) && (setAttr.get() == kValueAtom)) {
      // Flush out all our kids.
      PRInt32 childCount;
      element->ChildCount(childCount);
      if (childCount > 0)
        element->RemoveChildAt(0, PR_TRUE);
      
      if (!aRemoveFlag) {
        // Construct a new text node and insert it.
        nsAutoString value;
        nsresult result = mBoundElement->GetAttribute(aNameSpaceID, aAttribute, value);
        if (!value.IsEmpty()) {
          nsCOMPtr<nsIDOMText> textNode;
          nsCOMPtr<nsIDocument> doc;
          mBoundElement->GetDocument(*getter_AddRefs(doc));
          nsCOMPtr<nsIDOMDocument> domDoc(do_QueryInterface(doc));
          domDoc->CreateTextNode(value, getter_AddRefs(textNode));
          nsCOMPtr<nsIDOMNode> dummy;
          nsCOMPtr<nsIDOMElement> domElement(do_QueryInterface(element));
          domElement->AppendChild(textNode, getter_AddRefs(dummy));
        }
      }
    }
    nsCOMPtr<nsIXBLAttributeEntry> tmpAttr = xblAttr;
    tmpAttr->GetNext(getter_AddRefs(xblAttr));
  }

  return NS_OK;
}

NS_IMETHODIMP
nsXBLBinding::ChangeDocument(nsIDocument* aOldDocument, nsIDocument* aNewDocument)
{
  if (aOldDocument != aNewDocument) {
    if (mNextBinding)
      mNextBinding->ChangeDocument(aOldDocument, aNewDocument);

     if (aOldDocument) {
      // Now the binding dies.  Unhook our prototypes.
      nsCOMPtr<nsIContent> interfaceElement;
      GetImmediateChild(kInterfaceAtom, getter_AddRefs(interfaceElement));

      if (interfaceElement) {   
        nsCOMPtr<nsIScriptGlobalObject> global;
        aOldDocument->GetScriptGlobalObject(getter_AddRefs(global));
        if (global) {
          nsCOMPtr<nsIScriptContext> context;
          global->GetContext(getter_AddRefs(context));
          if (context) {
            JSObject* scriptObject;
            nsCOMPtr<nsIScriptObjectOwner> owner(do_QueryInterface(mBoundElement));
            owner->GetScriptObject(context, (void**)&scriptObject);
            if (scriptObject) {
              // XXX Sanity check to make sure our class name matches
              // Pull ourselves out of the proto chain.
              JSContext* jscontext = (JSContext*)context->GetNativeContext();
              JSObject* ourProto = JS_GetPrototype(jscontext, scriptObject);
              JSObject* grandProto = JS_GetPrototype(jscontext, ourProto);
              JS_SetPrototype(jscontext, scriptObject, grandProto);
            }
          }
        }
      }
    }

    // Kill the anonymous content.
    nsCOMPtr<nsIContent> anonymous;
    GetAnonymousContent(getter_AddRefs(anonymous));
    if (anonymous)
      anonymous->SetDocument(nsnull, PR_TRUE, AllowScripts());
  }

  return NS_OK;
}

NS_IMETHODIMP 
nsXBLBinding::GetBindingURI(nsString& aResult)
{
  return mBinding->GetAttribute(kNameSpaceID_None, kURIAtom, aResult);
}

// Internal helper methods ////////////////////////////////////////////////////////////////

NS_IMETHODIMP
nsXBLBinding::InitClass(const nsCString& aClassName, nsIScriptContext* aContext, 
                        nsIDocument* aDocument, void** aScriptObject, void** aClassObject)
{
  *aClassObject = nsnull;
  *aScriptObject = nsnull;

  // Obtain the bound element's current script object.
  nsCOMPtr<nsIScriptObjectOwner> owner(do_QueryInterface(mBoundElement));
  owner->GetScriptObject(aContext, aScriptObject);
  if (!(*aScriptObject))
    return NS_ERROR_FAILURE;

  JSObject* object = (JSObject*)(*aScriptObject);

  // First ensure our JS class is initialized.
  JSContext* jscontext = (JSContext*)aContext->GetNativeContext();
  JSObject* proto = nsnull;
  JSObject* constructor = nsnull;
  JSObject* parent_proto = nsnull;
  JSObject* global = JS_GetGlobalObject(jscontext);
  jsval vp;

  if ((PR_TRUE != JS_LookupProperty(jscontext, global, aClassName, &vp)) ||
      !JSVAL_IS_OBJECT(vp) ||
      ((constructor = JSVAL_TO_OBJECT(vp)) == nsnull) ||
      (PR_TRUE != JS_LookupProperty(jscontext, JSVAL_TO_OBJECT(vp), "prototype", &vp)) || 
      !JSVAL_IS_OBJECT(vp)) {
    // We need to initialize the class.
    
    JSClass* c;
    void* classObject;
    nsStringKey key(aClassName);
    classObject = (nsXBLService::gClassTable)->Get(&key);

    if (classObject)
      c = (JSClass*)classObject;
    else {
      // We need to create a struct for this class.
      c = new JSClass;
      memset(c, 0, sizeof(JSClass));
      c->name = nsXPIDLCString::Copy(aClassName);
      c->flags = JSCLASS_HAS_PRIVATE | JSCLASS_PRIVATE_IS_NSISUPPORTS;
      c->addProperty = c->delProperty = c->setProperty = c->getProperty = JS_PropertyStub;
      c->enumerate = JS_EnumerateStub;
      c->resolve = JS_ResolveStub;
      c->convert = JS_ConvertStub;
      c->finalize = XBLFinalize;

      // Add c to our table.
      (nsXBLService::gClassTable)->Put(&key, (void*)c);
    }
    
    // Retrieve the current prototype for the JS object.
    parent_proto = JS_GetPrototype(jscontext, object);
    proto = JS_InitClass(jscontext,     // context
                         global,        // global object
                         parent_proto,  // parent proto 
                         c,      // JSClass
                         XBLBindingCtor,            // JSNative ctor
                         0,             // ctor args
                         nsnull,  // proto props
                         nsnull,     // proto funcs
                         nsnull,        // ctor props (static)
                         nsnull);       // ctor funcs (static)
    if (nsnull == proto) {
      return NS_ERROR_FAILURE;
    }

    *aClassObject = (void*)proto;
  }
  else if ((nsnull != constructor) && JSVAL_IS_OBJECT(vp)) {
    proto = JSVAL_TO_OBJECT(vp);
  }
  else {
    return NS_ERROR_FAILURE;
  }

  // Set the prototype of our object to be the new class.
  JS_SetPrototype(jscontext, object, proto);

  return NS_OK;
}

void
nsXBLBinding::GetImmediateChild(nsIAtom* aTag, nsIContent** aResult) 
{
  *aResult = nsnull;
  PRInt32 childCount;
  mBinding->ChildCount(childCount);
  for (PRInt32 i = 0; i < childCount; i++) {
    nsCOMPtr<nsIContent> child;
    mBinding->ChildAt(i, *getter_AddRefs(child));
    nsCOMPtr<nsIAtom> tag;
    child->GetTag(*getter_AddRefs(tag));
    if (aTag == tag.get()) {
      *aResult = child;
      NS_ADDREF(*aResult);
      return;
    }
  }

  return;
}

void
nsXBLBinding::GetNestedChild(nsIAtom* aTag, nsIContent* aContent, nsIContent** aResult) 
{
  *aResult = nsnull;
  PRInt32 childCount;
  aContent->ChildCount(childCount);
  for (PRInt32 i = 0; i < childCount; i++) {
    nsCOMPtr<nsIContent> child;
    aContent->ChildAt(i, *getter_AddRefs(child));
    nsCOMPtr<nsIAtom> tag;
    child->GetTag(*getter_AddRefs(tag));
    if (aTag == tag.get()) {
      *aResult = aContent; // We return the parent of the correct child.
      NS_ADDREF(*aResult);
      return;
    }
    else {
      GetNestedChild(aTag, child, aResult);
      if (*aResult)
        return;
    }
  }
}

void
nsXBLBinding::GetNestedChildren(nsIAtom* aTag, nsIContent* aContent, nsISupportsArray* aList)
{
  PRInt32 childCount;
  aContent->ChildCount(childCount);
  for (PRInt32 i = 0; i < childCount; i++) {
    nsCOMPtr<nsIContent> child;
    aContent->ChildAt(i, *getter_AddRefs(child));
    nsCOMPtr<nsIAtom> tag;
    child->GetTag(*getter_AddRefs(tag));
    if (aTag == tag.get()) 
      aList->AppendElement(child);
    else
      GetNestedChildren(aTag, child, aList);
  }
}

void 
nsXBLBinding::BuildInsertionTable()
{
  if (!mInsertionPointTable) 
    mInsertionPointTable = new nsSupportsHashtable;
  
  nsCOMPtr<nsISupportsArray> childrenElements;
  NS_NewISupportsArray(getter_AddRefs(childrenElements));
  GetNestedChildren(kChildrenAtom, mContent, childrenElements);

  PRUint32 count;
  childrenElements->Count(&count);
  for (PRUint32 i = 0; i < count; i++) {
    nsCOMPtr<nsISupports> supp;
    childrenElements->GetElementAt(i, getter_AddRefs(supp));
    nsCOMPtr<nsIContent> child(do_QueryInterface(supp));
    if (child) {
      nsCOMPtr<nsIContent> parent; 
      child->GetParent(*getter_AddRefs(parent));
      nsAutoString includes;
      child->GetAttribute(kNameSpaceID_None, kIncludesAtom, includes);
      if (includes.IsEmpty()) {
        nsISupportsKey key(kChildrenAtom);
        mInsertionPointTable->Put(&key, parent);
      }
      else {
        // The user specified at least one attribute.
        char* str = includes.ToNewCString();
        char* newStr;
        // XXX We should use a strtok function that tokenizes PRUnichar's
        // so that we don't have to convert from Unicode to ASCII and then back

        char* token = nsCRT::strtok( str, ", ", &newStr );
        while( token != NULL ) {
          // Build an atom out of this string.
          nsCOMPtr<nsIAtom> atom;
            
          nsAutoString tok; tok.AssignWithConversion(token);
          atom = getter_AddRefs(NS_NewAtom(tok.GetUnicode()));
           
          nsISupportsKey key(atom);
          mInsertionPointTable->Put(&key, parent);
          
          token = nsCRT::strtok( newStr, ", ", &newStr );
        }

        nsAllocator::Free(str);
      }
    }
  }
}

PRBool
nsXBLBinding::IsInExcludesList(nsIAtom* aTag, const nsString& aList) 
{ 
  nsAutoString element;
  aTag->ToString(element);

  if (aList.EqualsWithConversion("*"))
      return PR_TRUE; // match _everything_!

  PRInt32 indx = aList.Find(element);
  if (indx == -1)
    return PR_FALSE; // not in the list at all

  // okay, now make sure it's not a substring snafu; e.g., 'ur'
  // found inside of 'blur'.
  if (indx > 0) {
    PRUnichar ch = aList[indx - 1];
    if (! nsCRT::IsAsciiSpace(ch) && ch != PRUnichar(','))
      return PR_FALSE;
  }

  if (indx + element.Length() < aList.Length()) {
    PRUnichar ch = aList[indx + element.Length()];
    if (! nsCRT::IsAsciiSpace(ch) && ch != PRUnichar(','))
      return PR_FALSE;
  }

  return PR_TRUE;
}

NS_IMETHODIMP
nsXBLBinding::ConstructAttributeTable(nsIContent* aElement)
{
  // XXX This function still needs to deal with the
  // ability to map one attribute to another.
  nsAutoString inherits;
  aElement->GetAttribute(kNameSpaceID_None, kInheritsAtom, inherits);
  if (!inherits.IsEmpty()) {
    if (!mAttributeTable) {
      mAttributeTable = new nsSupportsHashtable(4);
    }

    // The user specified at least one attribute.
    char* str = inherits.ToNewCString();
    char* newStr;
    // XXX We should use a strtok function that tokenizes PRUnichar's
    // so that we don't have to convert from Unicode to ASCII and then back

    char* token = nsCRT::strtok( str, ", ", &newStr );
    while( token != NULL ) {
      // Build an atom out of this attribute.
      nsCOMPtr<nsIAtom> atom;
      nsCOMPtr<nsIAtom> attribute;

      // Figure out if this token contains a :. 
      nsAutoString attrTok; attrTok.AssignWithConversion(token);
      PRInt32 index = attrTok.Find(":", PR_TRUE);
      if (index != -1) {
        // This attribute maps to something different.
        nsAutoString left, right;
        attrTok.Left(left, index);
        attrTok.Right(right, attrTok.Length()-index-1);

        atom = getter_AddRefs(NS_NewAtom(left.GetUnicode()));
        attribute = getter_AddRefs(NS_NewAtom(right.GetUnicode()));
      }
      else {
        nsAutoString tok; tok.AssignWithConversion(token);
        atom = getter_AddRefs(NS_NewAtom(tok.GetUnicode()));
        attribute = atom;
      }
      
      // Create an XBL attribute entry.
      nsXBLAttributeEntry* xblAttr = new nsXBLAttributeEntry(attribute, aElement);

      // Now we should see if some element within our anonymous
      // content is already observing this attribute.
      nsISupportsKey key(atom);
      nsCOMPtr<nsISupports> supports = getter_AddRefs(NS_STATIC_CAST(nsISupports*, 
                                                                     mAttributeTable->Get(&key)));
  
      nsCOMPtr<nsIXBLAttributeEntry> entry = do_QueryInterface(supports);
      if (!entry) {
        // Put it in the table.
        mAttributeTable->Put(&key, xblAttr);
      } else {
        nsCOMPtr<nsIXBLAttributeEntry> attr = entry;
        nsCOMPtr<nsIXBLAttributeEntry> tmpAttr = entry;
        do {
          attr = tmpAttr;
          attr->GetNext(getter_AddRefs(tmpAttr));
        } while (tmpAttr);
        attr->SetNext(xblAttr);
      }

      // Now make sure that this attribute is initially set.
      // XXX How to deal with NAMESPACES!!!?
      nsAutoString value;
      nsresult result = mBoundElement->GetAttribute(kNameSpaceID_None, atom, value);
      PRBool attrPresent = (result == NS_CONTENT_ATTR_NO_VALUE ||
                            result == NS_CONTENT_ATTR_HAS_VALUE);

      if (attrPresent) {
        aElement->SetAttribute(kNameSpaceID_None, attribute, value, PR_FALSE);
        nsCOMPtr<nsIAtom> tag;
        aElement->GetTag(*getter_AddRefs(tag));
        if ((tag.get() == kHTMLAtom) && (attribute.get() == kValueAtom) && !value.IsEmpty()) {
          nsCOMPtr<nsIDOMText> textNode;
          nsCOMPtr<nsIDocument> doc;
          mBoundElement->GetDocument(*getter_AddRefs(doc));
          nsCOMPtr<nsIDOMDocument> domDoc(do_QueryInterface(doc));
          domDoc->CreateTextNode(value, getter_AddRefs(textNode));
          nsCOMPtr<nsIDOMNode> dummy;
          nsCOMPtr<nsIDOMElement> domElement(do_QueryInterface(aElement));
          domElement->AppendChild(textNode, getter_AddRefs(dummy));
        }
      }

      token = nsCRT::strtok( newStr, ", ", &newStr );
    }

    nsAllocator::Free(str);
  }

  // Recur into our children.
  PRInt32 childCount;
  aElement->ChildCount(childCount);
  for (PRInt32 i = 0; i < childCount; i++) {
    nsCOMPtr<nsIContent> child;
    aElement->ChildAt(i, *getter_AddRefs(child));
    ConstructAttributeTable(child);
  }
  return NS_OK;
}

void
nsXBLBinding::GetEventHandlerIID(nsIAtom* aName, nsIID* aIID, PRBool* aFound)
{
  *aFound = PR_FALSE;

  EventHandlerMapEntry* entry = kEventHandlerMap;
  while (entry->mAttributeAtom) {
    if (entry->mAttributeAtom == aName) {
        *aIID = *entry->mHandlerIID;
        *aFound = PR_TRUE;
        break;
    }
    ++entry;
  }
}

PRBool
nsXBLBinding::IsMouseHandler(const nsString& aName)
{
  return ((aName.EqualsWithConversion("click")) || (aName.EqualsWithConversion("dblclick")) || (aName.EqualsWithConversion("mousedown")) ||
          (aName.EqualsWithConversion("mouseover")) || (aName.EqualsWithConversion("mouseout")) || (aName.EqualsWithConversion("mouseup")));
}

PRBool
nsXBLBinding::IsKeyHandler(const nsString& aName)
{
  return ((aName.EqualsWithConversion("keypress")) || (aName.EqualsWithConversion("keydown")) || (aName.EqualsWithConversion("keyup")));
}

PRBool
nsXBLBinding::IsFocusHandler(const nsString& aName)
{
  return ((aName.EqualsWithConversion("focus")) || (aName.EqualsWithConversion("blur")));
}

PRBool
nsXBLBinding::IsXULHandler(const nsString& aName)
{
  return ((aName.EqualsWithConversion("create")) || (aName.EqualsWithConversion("destroy")) || (aName.EqualsWithConversion("broadcast")) ||
          (aName.EqualsWithConversion("command")) || (aName.EqualsWithConversion("commandupdate")) || (aName.EqualsWithConversion("close")));
}

NS_IMETHODIMP
nsXBLBinding::AddScriptEventListener(nsIContent* aElement, nsIAtom* aName, const nsString& aValue, REFNSIID aIID)
{
  nsAutoString val;
  aName->ToString(val);
  
  nsAutoString eventStr; eventStr.AssignWithConversion("on");
  eventStr += val;

  nsCOMPtr<nsIAtom> eventName = getter_AddRefs(NS_NewAtom(eventStr));

  nsresult rv;
  nsCOMPtr<nsIDocument> document;
  aElement->GetDocument(*getter_AddRefs(document));
  if (!document)
    return NS_OK;

  nsCOMPtr<nsIDOMEventReceiver> receiver(do_QueryInterface(aElement));
  if (!receiver)
    return NS_OK;

  nsCOMPtr<nsIScriptGlobalObject> global;
  document->GetScriptGlobalObject(getter_AddRefs(global));

  // This can happen normally as part of teardown code.
  if (!global)
    return NS_OK;

  nsCOMPtr<nsIScriptContext> context;
  rv = global->GetContext(getter_AddRefs(context));
  if (NS_FAILED(rv)) return rv;

  nsCOMPtr<nsIEventListenerManager> manager;
  rv = receiver->GetListenerManager(getter_AddRefs(manager));
  if (NS_FAILED(rv)) return rv;

  nsCOMPtr<nsIScriptObjectOwner> scriptOwner(do_QueryInterface(receiver));
  if (!scriptOwner)
    return NS_OK;

  rv = manager->AddScriptEventListener(context, scriptOwner, eventName, aValue, aIID, PR_FALSE);

  return rv;
}

nsresult
nsXBLBinding::GetTextData(nsIContent *aParent, nsString& aResult)
{
  aResult.Truncate(0);

  nsCOMPtr<nsIContent> textChild;
  PRInt32 textCount;
  aParent->ChildCount(textCount);
  nsAutoString answer;
  for (PRInt32 j = 0; j < textCount; j++) {
    // Get the child.
    aParent->ChildAt(j, *getter_AddRefs(textChild));
    nsCOMPtr<nsIDOMText> text(do_QueryInterface(textChild));
    if (text) {
      nsAutoString data;
      text->GetData(data);
      aResult += data;
    }
  }
  return NS_OK;
}

PRBool
nsXBLBinding::AllowScripts()
{
  nsresult rv;
  nsCOMPtr<nsIXBLService> xblService(do_GetService("component://netscape/xbl", &rv));
  if (xblService) {
    PRBool allowScripts;
    xblService->AllowScripts(mBinding, &allowScripts);
    return allowScripts;
  }

  return PR_FALSE;
}

NS_IMETHODIMP
nsXBLBinding::GetInsertionPoint(nsIContent* aChild, nsIContent** aResult)
{
  *aResult = nsnull;
  if (mInsertionPointTable) {
    nsCOMPtr<nsIAtom> tag;
    aChild->GetTag(*getter_AddRefs(tag));
    nsISupportsKey key(tag);
    nsCOMPtr<nsIContent> content = getter_AddRefs(NS_STATIC_CAST(nsIContent*, 
                                                                 mInsertionPointTable->Get(&key)));
    if (!content) {
      nsISupportsKey key2(kChildrenAtom);
      content = getter_AddRefs(NS_STATIC_CAST(nsIContent*, mInsertionPointTable->Get(&key2)));
    }

    *aResult = content;
    NS_IF_ADDREF(*aResult);
  }
  return NS_OK;  
}

NS_IMETHODIMP
nsXBLBinding::GetSingleInsertionPoint(nsIContent** aResult, PRBool* aMultipleInsertionPoints)
{
  *aResult = nsnull;
  *aMultipleInsertionPoints = PR_FALSE;
  if (mInsertionPointTable) {
    if(mInsertionPointTable->Count() == 1) {
      nsISupportsKey key(kChildrenAtom);
      nsCOMPtr<nsIContent> content = getter_AddRefs(NS_STATIC_CAST(nsIContent*, 
                                                                   mInsertionPointTable->Get(&key)));
      *aResult = content;
      NS_IF_ADDREF(*aResult);
    }
    else 
      *aMultipleInsertionPoints = PR_TRUE;
  }
  return NS_OK;  
}

// Creation Routine ///////////////////////////////////////////////////////////////////////

nsresult
NS_NewXBLBinding(nsIXBLBinding** aResult)
{
  *aResult = new nsXBLBinding;
  if (!*aResult)
    return NS_ERROR_OUT_OF_MEMORY;
  NS_ADDREF(*aResult);
  return NS_OK;
}

