/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_prove 
///////////////////////////////////

// The Goals and Proving Stacks.
var jslog_frontier = new Array();
var jslog_explored = new Array();


///////////////////////////////////
// jslog_user_* functions for User Initiated Queries
///////////////////////////////////

function jslog_user_prove(query)
{var terms;

 jslog_frontier = new Array();
 jslog_explored = new Array();

 terms = getTermArrayFromBinaryTerm(query.term,isConsPair); 
 addBodyGoalsToFrontier(null,new ArrayEnclosure(query.enclosure,terms),jslog_kb,jslog_frontier);

 return jslog_prove(jslog_kb,jslog_frontier,jslog_explored);
}

function jslog_user_retry()
{ 
 return jslog_prove_retry(jslog_kb,jslog_frontier,jslog_explored);
}

function jslog_user_stop()
{ 
 // FIX: doesn't really stop existing proof, just allows a new one to start
 jslog_frontier = new Array();
 jslog_explored = new Array();
}

///////////////////////////////////
// jslog_prove_* functions for Prolog Prover
///////////////////////////////////

// proves all enclosures on the goals stack.
// kb is the KnowledgeBase to use for the proof.
function jslog_prove(kb,frontier,explored)
{var goal;

 while ((goal = frontier.pop()) != undefined)
 {
  if (!tryGoal(goal,kb,frontier,explored))
  {
   do
   {
    if ((goal = explored.pop()) == undefined)
	 return false;
   } while (!retryGoal(goal,kb,frontier,explored));
  }
 }
 
 return true;
}


function jslog_prove_retry(kb,frontier,explored)
{
 do
 {
  if ((goal = explored.pop()) == undefined)
   return false;
 } while (!retryGoal(goal,kb,frontier,explored));

 return jslog_prove(kb,frontier,explored);
}

