/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// Prover Object 
///////////////////////////////////

var QUERY_STATE_INITIAL = 1;
var QUERY_STATE_PROVING = 2;
var QUERY_STATE_WAITING = 3;
var QUERY_STATE_DONE = 4;


// kb is the KB object associated with this prover
function Prover(kb)
{
 this.kb = kb;
 this.state = QUERY_STATE_INITIAL;
 this.frontier = new Array();
 this.explored = new Array();
 
 //// Other Properties (document here):
 // this.query : the given query encl
  
 return this;
}

function newQueryProver(kb,query)
{var prover = new Prover(kb);
 var terms = getTermArrayFromBinaryTerm(query.term,isConsPair);
 
 prover.query = query;
 
 addBodyGoalsToFrontier(null,new ArrayEnclosure(query.enclosure,terms),prover.kb,prover.frontier);

 return prover; 
}


///////////////////////////////////
// * Prover proof functions
///////////////////////////////////

// proves all enclosures on the frontier stack.
function proveProver(prover)
{var goal = null;

 if (prover.state == QUERY_STATE_DONE)
  return false;

 prover.state = QUERY_STATE_PROVING;
 
 try
 {
  while ((goal = prover.frontier.pop()) != undefined)
  {
   if (!tryGoal(goal,prover))
   {
    do
    {
     if ((goal = prover.explored.pop()) == undefined)
	 {
      prover.state = QUERY_STATE_DONE;
	  return false;
	 } 
    } while (!retryGoal(goal,prover));
   }
  }
 }
 catch (err)
 {
  if (goal != null)
   undoGoal(goal,false);
  
  prover.state = QUERY_STATE_WAITING;
  throw err;
 } 
 
 prover.state = QUERY_STATE_WAITING;
 return true;
}

function retryProver(prover)
{var goal = null;

 if (prover.state == QUERY_STATE_DONE)
  return false;

 prover.state = QUERY_STATE_PROVING;

 try
 {
  do
  {
   if ((goal = prover.explored.pop()) == undefined)
   {
    prover.state = QUERY_STATE_DONE;
    return false;
   } 
  } while (!retryGoal(goal,prover));
 }
 catch (err)
 {
  if (goal != null)
   undoGoal(goal,false);
  
  prover.state = QUERY_STATE_WAITING;
  throw err;
 }
 
 return proveProver(prover);
}

function stopProver(prover)
{
 if (prover.state == QUERY_STATE_DONE)
  return;

 prover.state = QUERY_STATE_PROVING;

 try
 {
  do
  {
   if ((goal = prover.explored.pop()) != undefined)
    undoGoal(goal,false);
   
  } while (goal != undefined);
 }
 catch (err)
 {
  prover.state = QUERY_STATE_WAITING;
  throw err;
 }
 
 prover.frontier = new Array();
 prover.explored = new Array();
 prover.state = QUERY_STATE_DONE;
}

// immediately ends the prover without unbinding.
// prover.query may be mutated
function haltProver(prover)
{ 
 // FIX: doesn't really stop existing proof immediately if called during QUERY_STATE_PROVING
 prover.frontier = new Array();
 prover.explored = new Array();
 prover.state = QUERY_STATE_DONE;
}

///////////////////////////////////
// * Prover test functions
///////////////////////////////////

function isProverStateInitial(prover)
{
 return (prover.state == QUERY_STATE_INITIAL);
}

function isProverStateProving(prover)
{
 return (prover.state == QUERY_STATE_PROVING);
}

function isProverStateWaiting(prover)
{
 return (prover.state == QUERY_STATE_WAITING);
}

function isProverStateDone(prover)
{
 return (prover.state == QUERY_STATE_DONE);
}


///////////////////////////////////
// * ProverStatistics
///////////////////////////////////

// prover is the Prover object associated with these statistics
function ProverStatistics(prover)
{
 this.prover = prover;
 this.frontier_goals_count = 0;
 this.frontier_bindings_count = 0;
 this.explored_goals_count = 0;
 this.explored_bindings_count = 0;
 
 //// Other Properties (document here):
 
 this.toString = function() 
 {  
  return "EXPLORED - goals:" + this.explored_goals_count.toString() + 
					" bindings:" + this.explored_bindings_count.toString() + " ; " +
		 "FRONTIER - goals:" + this.frontier_goals_count.toString() + 
					" bindings:" + this.frontier_bindings_count.toString(); 
 };
  
 return this;
}


///////////////////////////////////
// * Prover Statistics functions
///////////////////////////////////

function calculateStatistics(prover)
{var stats = new ProverStatistics(prover);
 var i;
 
 stats.frontier_goals_count = prover.frontier.length;
 stats.explored_goals_count = prover.explored.length;

 for (i = 0; i < prover.frontier.length; ++i)
  if (prover.frontier[i] != null && prover.frontier[i].bindings != null)
   stats.frontier_bindings_count += prover.frontier[i].bindings.length;  

 for (i = 0; i < prover.explored.length; ++i)
  if (prover.explored[i] != null && prover.explored[i].bindings != null)
   stats.explored_bindings_count += prover.explored[i].bindings.length;  
 
 return stats;
}
