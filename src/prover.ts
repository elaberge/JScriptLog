/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.

    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

import {
  ArrayEnclosure
} from "./enclosures";
import {
  addBodyGoalsToFrontier, retryGoal, tryGoal, undoGoal
} from "./goals";
import {
  getTermArrayFromBinaryTerm, isConsPair
} from "./types";

///////////////////////////////////
// Prover Object
///////////////////////////////////

var QUERY_STATE_INITIAL = 1;
var QUERY_STATE_PROVING = 2;
var QUERY_STATE_WAITING = 3;
var QUERY_STATE_DONE = 4;


// kb is the KB object associated with this prover
export class Prover {
  state = QUERY_STATE_INITIAL;
  frontier: any[] = [];
  explored: any[] = [];
  query: any; // the given query encl

  //// Other Properties (document here):
  // this.query_variables : array of variable encls in the original query

  constructor(public kb: any) {
  }
}

export function newQueryProver(kb: any, query: any)
{var prover = new Prover(kb);
 var terms = getTermArrayFromBinaryTerm(query.term,isConsPair);

 prover.query = query;

 addBodyGoalsToFrontier(null,null,new ArrayEnclosure(query.enclosure,terms),prover.kb,prover.frontier);

 return prover;
}


///////////////////////////////////
// * Prover proof functions
///////////////////////////////////

// proves all enclosures on the frontier stack.
export function proveProver(prover: any)
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

export function retryProver(prover: any)
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

export function stopProver(prover: any)
{
 if (prover.state == QUERY_STATE_DONE)
  return;

 prover.state = QUERY_STATE_PROVING;

 try
 {
   let goal: any;
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
export function haltProver(prover: any)
{
 // FIX: doesn't really stop existing proof immediately if called during QUERY_STATE_PROVING
 prover.frontier = new Array();
 prover.explored = new Array();
 prover.state = QUERY_STATE_DONE;
}

///////////////////////////////////
// * Prover test functions
///////////////////////////////////

function isProverStateInitial(prover: any)
{
 return (prover.state == QUERY_STATE_INITIAL);
}

function isProverStateProving(prover: any)
{
 return (prover.state == QUERY_STATE_PROVING);
}

export function isProverStateWaiting(prover: any)
{
 return (prover.state == QUERY_STATE_WAITING);
}

export function isProverStateDone(prover: any)
{
 return (prover.state == QUERY_STATE_DONE);
}


///////////////////////////////////
// * ProverStatistic
///////////////////////////////////

// prover is the Prover object associated with these statistics
export class ProverStatistic {
  // properties for the last statistic calculation for this object
  frontier_goals_count = 0;
  frontier_bindings_count = 0;
  explored_goals_count = 0;
  explored_bindings_count = 0;

  // properties summarized all statistic calculations for this object
  max_frontier_goals_count = 0;
  max_frontier_bindings_count = 0;
  max_explored_goals_count = 0;
  max_explored_bindings_count = 0;

  constructor(public prover: any) {
  }

  toString() {
    var s;

     s = "EXPLORED - goals:" + this.explored_goals_count.toString();

     if (this.max_explored_goals_count > this.explored_goals_count)
      s += " (max:" + this.max_explored_goals_count.toString() + ")";

     s += " bindings:" + this.explored_bindings_count.toString();

     if (this.max_explored_bindings_count > this.explored_bindings_count)
      s += " (max:" + this.max_explored_bindings_count.toString() + ")";

     s += " ; "

     s += "FRONTIER - goals:" + this.frontier_goals_count.toString();

     if (this.max_frontier_goals_count > this.frontier_goals_count)
      s += " (max:" + this.max_frontier_goals_count.toString() + ")";

     s += " bindings:" + this.frontier_bindings_count.toString();

     if (this.max_frontier_bindings_count > this.frontier_bindings_count)
      s += " (max:" + this.max_frontier_bindings_count.toString() + ")";

     return s;
  }
}

///////////////////////////////////
// * Prover Statistic functions
///////////////////////////////////

// stats is a ProverStatistic object
export function calculateStatistics(stats: any)
{var i;

 stats.frontier_goals_count = stats.prover.frontier.length;
 stats.explored_goals_count = stats.prover.explored.length;
 stats.frontier_bindings_count = 0;
 stats.explored_bindings_count = 0;

 for (i = 0; i < stats.prover.frontier.length; ++i)
  if (stats.prover.frontier[i] != null && stats.prover.frontier[i].bindings != null)
   stats.frontier_bindings_count += stats.prover.frontier[i].bindings.length;

 for (i = 0; i < stats.prover.explored.length; ++i)
  if (stats.prover.explored[i] != null && stats.prover.explored[i].bindings != null)
   stats.explored_bindings_count += stats.prover.explored[i].bindings.length;

 stats.max_frontier_goals_count = Math.max(stats.max_frontier_goals_count,
											stats.frontier_goals_count);
 stats.max_frontier_bindings_count = Math.max(stats.max_frontier_bindings_count,
											stats.frontier_bindings_count);
 stats.max_explored_goals_count = Math.max(stats.max_explored_goals_count,
											stats.explored_goals_count);
 stats.max_explored_bindings_count = Math.max(stats.max_explored_bindings_count,
											stats.explored_bindings_count);

 return stats;
}
