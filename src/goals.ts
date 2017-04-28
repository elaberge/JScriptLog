/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.

    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

import {
  ArrayEnclosure,
  getFinalEnclosure, newErrorException, getBoundEnclosure, removeBindings, newSubtermEnclosure
} from "./enclosures";
import {
  getRuleSet, getUnifiedRuleEnclosure, newRuleBodyArrayEnclosure
} from "./kb";
import {
  isAtom, isVariable, getTermNameArity, getTermNameArityFromNameArity
} from "./types";

///////////////////////////////////
// * Goal Objects
///////////////////////////////////

export var TYPE_ATOM_GOAL = 1; // KB predicates
export var TYPE_VARIABLE_GOAL = 2; // KB predicates, with a variable term


export class Goal {
  bindings: any = null;
  ruleset: any;
  rule_index: any;
  parent_is_ancestor: any;

  //// Other Properties (document here):
  // this.kb : the KB used to try the goal
  // this.ruleset :
  // this.rule_index :
  // this.prover : a sub-prover
  // this.noretry : if true, the next retry must fail.
  // this.parent_is_ancestor : true if parent set to grand+-parent (ancestor).
  // this.rulesets_array : an array of rulesets
  // this.rulesets_index : the current index into rulesets_array

  constructor(public type: any, public encl: any, public parent: any) {
  }
}

// encl is the enclosure for goal to prove
// parent is the parent goal
function newGoal(encl: any, parent: any, kb: any)
{
 if (encl.term.goal_type != undefined)
 {
  switch (encl.term.goal_type)
  {
   case TYPE_ATOM_GOAL:
    return newAtomGoal(encl,parent,kb);
   case TYPE_VARIABLE_GOAL:
    return newVariableGoal(encl,parent);
   default:
    break;
  }
 }

 if (isVariable(encl.term))
  return newVariableGoal(encl,parent);

 return newAtomGoal(encl,parent,kb);
}

// isAtom(encl.term) must be true
export function newAtomGoal(encl: any, parent: any, kb: any)
{var goal = new Goal(TYPE_ATOM_GOAL,encl,parent);

 goal.rule_index = 0;

 if (encl.term.ruleset != null)
  goal.ruleset = encl.term.ruleset;
 else
 {
  goal.ruleset = encl.term.ruleset = getRuleSet(kb,encl.term);
 }
 return goal;
}

// isAtom(encl.term) or isVariable(encl.term) must be true
export function newAtomGoalFromRuleSet(encl: any, parent: any, ruleset: any, kb: any)
{var goal = new Goal(TYPE_ATOM_GOAL,encl,parent);

 goal.rule_index = 0;

 goal.ruleset = ruleset;

 return goal;
}

export function newVariableGoal(encl: any, parent: any)
{var goal = new Goal(TYPE_VARIABLE_GOAL,encl,parent);

 goal.rule_index = 0;
 goal.ruleset = null;

 return goal;
}


///////////////////////////////////
// * Goal test functions
///////////////////////////////////

export function isAtomGoal(goal: any)
{
 return (goal.type == TYPE_ATOM_GOAL);
}

export function isVariableGoal(goal: any)
{
 return (goal.type == TYPE_VARIABLE_GOAL);
}


///////////////////////////////////
// * Goal prove functions
///////////////////////////////////


// tryGoal(goal,prover) returns true if succeeds, false otherwise
// goal must be placed on appropriate stack (frontier if fail or explored if true).
// goal.bindings must be empty, if fail, or no unification occured.
export function tryGoal(goal: any, prover: any)
{
 goal.kb = prover.kb;
 if (goal.bindings == null)
  goal.bindings = new Array();

 switch (goal.type)
 {
  case TYPE_VARIABLE_GOAL:
     var encl = getFinalEnclosure(goal.encl);

	 if (!isAtom(encl.term))
	 {
	  prover.frontier.push(goal);
      throw newErrorException("Variable must be bound to atom.");
     }

     if (encl.term.ruleset != null)
      goal.ruleset = encl.term.ruleset;
     else
	  goal.ruleset = getRuleSet(prover.kb,encl.term);

	 goal.retry_fn = null;
	 goal.undo_fn = null;

  case TYPE_ATOM_GOAL:
     var rule_body;

     if (goal.ruleset == null)
	 {
	  prover.frontier.push(goal);
      throw newErrorException("Unknown predicate: "+getTermNameArity(getBoundEnclosure(goal.encl).term));
     }

	 goal.noretry = undefined;

	 goal.rule_index = 0;
	 rule_body = nextUnifiedRuleBodyForGoal(goal);

	 if (rule_body == null)
	 {
	  prover.frontier.push(goal);
	  return false;
	 }
	 else if (rule_body.terms != null)
	 {
	  // if last-try
	  if (goal.parent != null && // entails prover.explored.length >= 1
			goal.rule_index == goal.ruleset.rules.length - 1 &&
			prover.explored[prover.explored.length - 1] == goal.parent)
	  {
	   mergeGoalBindings(goal,goal.parent);
	   addBodyGoalsToFrontier(goal.parent,true,rule_body,prover.kb,prover.frontier);
	  }
	  else
	  {
	   prover.explored.push(goal);
       addBodyGoalsToFrontier(goal,undefined,rule_body,prover.kb,prover.frontier);
	  }
	  return true;
	 }
	 else // handle FUNCTION and TRAVERSAL
	 {
	  if (rule_body.fn != null)
	  {
	   if (rule_body.fn(goal))
       {
	    if (goal.parent != null && // entails prover.explored.length >= 1
			prover.explored[prover.explored.length - 1] == goal.parent)
	     mergeGoalBindings(goal,goal.parent);
		else
	   	 prover.explored.push(goal);

        return true;
       }
	   else
	   {
	    prover.frontier.push(goal);
		return false;
	   }
	  }
	  else if (rule_body.try_fn != null)
	  {
	   goal.retry_fn = rule_body.retry_fn;
	   goal.undo_fn = rule_body.undo_fn;

	   return rule_body.try_fn(goal,prover);
	  }
	  else
	  {
	   prover.frontier.push(goal);
	   return false;
	  }
	 }
 }
}

// retryGoal(goal,prover) returns true if succeeds, false otherwise
// goal must be placed on appropriate stack (frontier if fail or explored if true).
// goal.bindings must be non-null on start, empty on fail.
export function retryGoal(goal: any, prover: any)
{var rule_body = null;

 undoGoal(goal,true);

 removeChildGoalsFromFrontier(goal,prover.frontier);

 // handle TRAVERSAL retry
 if (goal.retry_fn != null)
  return goal.retry_fn(goal,prover);

 goal.rule_index++;
 if (goal.noretry != true)
  rule_body = nextUnifiedRuleBodyForGoal(goal);

 if (rule_body == null)
 {
  prover.frontier.push(goal);
  return false;
 }
 else if (rule_body.terms != null)
 {
  // if last-try
  if (goal.parent != null && // entails prover.explored.length >= 1
		goal.rule_index == goal.ruleset.rules.length - 1 &&
		prover.explored[prover.explored.length - 1] == goal.parent)
  {
   mergeGoalBindings(goal,goal.parent);
   addBodyGoalsToFrontier(goal.parent,true,rule_body,prover.kb,prover.frontier);
  }
  else
  {
   prover.explored.push(goal);
   addBodyGoalsToFrontier(goal,undefined,rule_body,goal.kb,prover.frontier);
  }
  return true;
 }
 else
 {
  prover.frontier.push(goal);
  return false;
 }
}

// undoGoal(goal,retry) undoes the binding for goal.
// retry is true if a retry will follow, false if not.
export function undoGoal(goal: any, retry: any)
{
 if (goal.bindings != null)
  removeBindings(goal.bindings);

 if (goal.undo_fn != null)
  goal.undo_fn(goal,retry);
}

// removes the contiguous top-most goals from frontier which are children of the parent goal
export function removeChildGoalsFromFrontier(parent: any, frontier: any)
{var goal;

 while ((goal = frontier.pop()) != undefined)
 {
  if (goal.parent != parent)
  {
   frontier.push(goal);
   break;
  }
 };
}

// returns an ArrayEnclosure for the next matching Rule, starting from goal.rule_index (inclusive).
// goal.bindings must be null or an empty array when passed in, may be mutated (empty if fail).
// returns null if no rules match.  goal.rule_index equals the index for the matched rule.
export function nextUnifiedRuleBodyForGoal(goal: any)
{var rule;
 var enclosure;

 if (goal.bindings == null)
  goal.bindings = new Array();

 while (goal.rule_index < goal.ruleset.rules.length)
 {
  rule = goal.ruleset.rules[goal.rule_index];

  if ((enclosure = getUnifiedRuleEnclosure(rule,goal.encl,goal.bindings)) != undefined)
  {
   enclosure.goal = goal;
   return newRuleBodyArrayEnclosure(enclosure,rule);
  }
  goal.rule_index++;
 }
 return null;
}

// body is an ArrayEnclosure
// isgp is true if parent is actually the grandparent for the added body.
export function addBodyGoalsToFrontier(parent: any, isgp: any, body: any, kb: any, frontier: any)
{var encl;
 var goal;

 for (var i = body.terms.length - 1; i >= 0; i--)
 {
  encl = newSubtermEnclosure(body.enclosure,body.terms[i]);
  goal = newGoal(getFinalEnclosure(encl),parent,kb);
  goal.parent_is_ancestor = isgp;
  frontier.push(goal);
 }
}

// merge bindings from sgoal to dgoal
// dgoal should be a predecessor of sgoal
export function mergeGoalBindings(sgoal: any, dgoal: any)
{var b;

 while ((b = sgoal.bindings.pop()) != undefined)
 {
  if (b.enclosure.goal == sgoal)
  {
   b.enclosure.goal = dgoal;
   b.enclosure.transferred = true;
  }
  else if (b.enclosure.goal != dgoal || b.enclosure.transferred != true)
   dgoal.bindings.push(b);
 };
}
