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

var PROVER_PHASE_CONSULT = 1;
var PROVER_PHASE_QUERY = 2;

var QUERY_STATE_INITIAL = 1;
var QUERY_STATE_PROVING = 2;
var QUERY_STATE_WAITING = 3;
var QUERY_STATE_DONE = 4;


// kb is the KB object associated with this prover
// mode is one of the PROVER_MODE_* constants
function Prover(kb,phase)
{
 this.kb = kb;
 this.phase = phase; 
 this.state = QUERY_STATE_INITIAL;
 this.frontier = new Array();
 this.explored = new Array();
 
 //// Other Properties (document here):
 // this.query : the given query encl
  
 return this;
}

function newQueryProver(kb,query)
{var prover = new Prover(kb,PROVER_PHASE_QUERY);
 var terms = getTermArrayFromBinaryTerm(query.term,isConsPair);
 
 prover.query = query;
 
 addBodyGoalsToFrontier(null,new ArrayEnclosure(query.enclosure,terms),prover.kb,prover.frontier);

 return prover; 
}

function newCommandProver(kb,query)
{var prover = newQueryProver(kb,query);

 prover.phase = PROVER_PHASE_CONSULT;

 return prover; 
}


///////////////////////////////////
// * Prover proof functions
///////////////////////////////////

// proves all enclosures on the frontier stack.
function proveProver(prover)
{var goal;

 if (prover.state == QUERY_STATE_DONE)
  return false;

 prover.state = QUERY_STATE_PROVING;
 
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
 
 prover.state = QUERY_STATE_WAITING;
 return true;
}

function retryProver(prover)
{
 if (prover.state == QUERY_STATE_DONE)
  return false;

 prover.state = QUERY_STATE_PROVING;

 do
 {
  if ((goal = prover.explored.pop()) == undefined)
  {
   prover.state = QUERY_STATE_DONE;
   return false;
  } 
 } while (!retryGoal(goal,prover));

 return proveProver(prover);
}

function stopProver(prover)
{ 
 // FIX: doesn't really stop existing proof immediately
 prover.frontier = new Array();
 prover.explored = new Array();
 prover.state = QUERY_STATE_DONE;
}
