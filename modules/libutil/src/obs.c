/* -*- Mode: C; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 2 -*-
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

#if 0
#include "platform.h"
#include "coremem.h"
#else
#include "prmem.h"
#endif

#include "xp_obs.h"
#include "prclist.h"
#include "prtypes.h"

#define MK_OUT_OF_MEMORY -1

typedef struct Observer
{
	struct PRCListStr	mLink;
	XP_ObserverProc	mCallback;
	void*				mClosure;

} Observer;

#define	NextObserver(_obsptr_)	((Observer*)(_obsptr_)->mLink.next)
#define ObserverLinks(_obsptr_)	(&((_obsptr_)->mLink))

struct OpaqueObserverList
{
	Observer*		mObserverList;
	XP_Observable	mObservable;
	PRBool		mNotificationEnabled;	
};



/* 
        Creates a new XP_Observable, to which you can add observers,
        who are notified when XP_NotifyObservers is called.
        
        Observerer notification is enabled by default.
*/
NS_Error
XP_NewObserverList(       
	XP_Observable		inObservable,
	XP_ObserverList*	outObserverList )
{
	NS_Error result = 0;
	
	PR_ASSERT(outObserverList != NULL);
	*outObserverList = PR_MALLOC(sizeof(struct OpaqueObserverList));
	
	if (*outObserverList != NULL)  
	{
		(*outObserverList)->mObserverList = NULL;
		(*outObserverList)->mObservable = inObservable;
		(*outObserverList)->mNotificationEnabled = PR_TRUE;
	}
	else 	{
		result = MK_OUT_OF_MEMORY;
	}
	
	return result;
}        
        

/* 
        Disposes of an XP_Observable. Does nothing with
        its observers.
*/
void
XP_DisposeObserverList(
        XP_ObserverList inObserverList )
{
	Observer	*obs, *next = NULL;
	
	PR_ASSERT(inObserverList != NULL);
	for (obs = inObserverList->mObserverList; obs != NULL; )
	{
		
		next = NextObserver(obs);
		if (next == obs) {
			break;
		}
		
		PR_REMOVE_LINK(ObserverLinks(obs));
		inObserverList->mObserverList = next;
		PR_FREEIF(obs);
		obs = inObserverList->mObserverList;
	}
	
	
	PR_FREEIF(inObserverList);
}        

/*
	XP_GetObserverListObservable
*/       
XP_Observable
XP_GetObserverListObservable(
	XP_ObserverList inObserverList)
{	
	PR_ASSERT(inObserverList != NULL);
	
	return inObserverList->mObservable;
}	


void
XP_SetObserverListObservable(
	XP_ObserverList inObserverList,
	XP_Observable	inObservable	)
{
	PR_ASSERT(inObserverList != NULL);
	
	inObserverList->mObservable = inObservable;
}	
        

/*
        Registers a function pointer and void* closure
        as an "observer", which will be called whenever
        XP_NotifyObservers is called an observer notification
        is enabled.
*/
NS_Error
XP_AddObserver(
        XP_ObserverList  inObserverList,
        XP_ObserverProc inObserver,
        void*                   inClosure       )
{
	Observer*	obs;
	NS_Error	result = 0;
	
	PR_ASSERT(inObserverList != NULL);
	if (inObserverList == NULL) {
		return -1;
	}
	
	obs = PR_MALLOC(sizeof (Observer));
	if (obs != NULL)
	{
		obs->mCallback = inObserver;
		obs->mClosure = inClosure;
		
		if (inObserverList->mObserverList == NULL) 
		{
			PR_INIT_CLIST(ObserverLinks(obs));
			inObserverList->mObserverList = obs;			
		}
		else {
			PR_INSERT_AFTER(ObserverLinks(obs), ObserverLinks(inObserverList->mObserverList));
		}
	
	} else {
		result = MK_OUT_OF_MEMORY;
	}

	return result;
	
}

        
        
/*
        Removes a registered observer. If there are duplicate
        (XP_ObserverProc/void* closure) pairs registered,
        it is undefined which one will be removed.

        Returns false if the observer is not registered.
*/
PRBool
XP_RemoveObserver(      
        XP_ObserverList 	inObserverList,
        XP_ObserverProc inObserver,
        void*                   inClosure       )
{
	PRBool result = PR_FALSE;
		
	if ( inObserverList->mObserverList != NULL )
	{
		Observer 	*tail = (Observer*) PR_LIST_TAIL(ObserverLinks(inObserverList->mObserverList));
		Observer  	*obs = inObserverList->mObserverList;
		do
		{
			if (obs->mCallback == inObserver && obs->mClosure == inClosure) 
			{
				PR_REMOVE_LINK(ObserverLinks(obs));
				if (obs == inObserverList->mObserverList) 
				{	
					Observer*	next = NextObserver(obs);
					inObserverList->mObserverList = (next != obs) ? next : NULL;
				}
				
				PR_FREEIF(obs);
				result = PR_TRUE;
				break;
			}
			
			obs = NextObserver(obs);
		
		} while (obs != tail);
	}

	return result;
}        
        

/*
        If observer notification is enabled for this XP_Observable,
        this will call each registered observer proc, passing it
        the given message and void* ioData, in addition to the 
        observer's closure void*.
        
        There is no defined order in which observers are called.
*/
void
XP_NotifyObservers(
        XP_ObserverList           	inObserverList,
        XP_ObservableMsg      	inMessage,
        void*                          	ioData  )
{
	Observer*	obs;
	Observer *tail;
	Observer *temp;
	PRBool done = PR_FALSE;
	
	if (	! inObserverList->mNotificationEnabled	||
		inObserverList->mObserverList == NULL) 	
	{
		return;
	}

	obs = inObserverList->mObserverList;
	tail = (Observer *) PR_LIST_TAIL(ObserverLinks(obs));
	
	do
	{
		if (obs == tail) done = PR_TRUE;
		(obs->mCallback)(inObserverList->mObservable, inMessage, ioData, obs->mClosure);
		if (done != PR_TRUE) {

			temp = inObserverList->mObserverList; /* just in case this callback free this observable
											    entry. */
			if (temp != obs) {
				obs = temp;
				tail = (Observer *) PR_LIST_TAIL(ObserverLinks(obs));
			}
			else
				obs = NextObserver(obs);
		}
	} while (done != PR_TRUE);
}        
      
      
        

/*
        When called, subsequent calls to XP_NotifyObservers
        will do nothing until XP_EnableObserverNotification
        is called.
*/
void
XP_DisableObserverNotification(
         XP_ObserverList   inObserverList    )
{
	inObserverList->mNotificationEnabled = PR_FALSE;
}        
        
        
/*
        Enables calling observers when XP_NotifyObservers
        is invoked. 
*/
void
XP_EnableObserverNotification(
        XP_ObserverList   inObserverList    )
{
	inObserverList->mNotificationEnabled = PR_TRUE;
}        
        

/*
        Returns true if observer notification is enabled.
*/
PRBool
XP_IsObserverNotificationEnabled(
        XP_ObserverList   inObserverList    )
{
	return inObserverList->mNotificationEnabled;
}                      
        
        
       
       
