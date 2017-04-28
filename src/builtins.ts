/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.

    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

import {
  jslog_toString
} from "./display";
import {
  Exception,
  enumFinalVariableEnclosures, getConsPairEnclosureFromEnclosureArray, getFinalEnclosure,
  newBlankEnclosure, newDuplicateEnclosure, newDuplicateTermFromEnclosure, newErrorException,
  newInternalErrorException, newSubtermEnclosure, newTermEnclosure, removeBindings
 } from "./enclosures";
 import {
   jslog_Evaluate, jslog_Evaluate_Function
 } from "./evaluate";
 import {
   mergeGoalBindings, newAtomGoal, newAtomGoalFromRuleSet, nextUnifiedRuleBodyForGoal,
   removeChildGoalsFromFrontier, undoGoal, isAtomGoal, isVariableGoal, newVariableGoal
 } from "./goals";
 import {
   OP_TYPE_FX, isOperatorRuleSet, getOperatorTypeFromString , getRuleSetFromNameArity,
   getOperatorType, getOperatorPrecedence, getRuleSetName, getOperatorTypeStringFromType,
   isDynamicRuleSet, newRule, getRuleNameArity, addRule, removeRuleFromRuleSet
  } from "./kb";
import {
  isProverStateDone, newQueryProver, proveProver, retryProver, stopProver
} from "./prover";
import {
  Term,
  isAtom, isConstant, isInteger, isListNull, isListPair, isNumber,
  isObjectReference, isVariable, newAtom, newConstant, newListNull,
  newListPair, newNumber, newObjectReference, newVariable
} from "./types";
import {
  jslog_unify, jslog_compare, jslog_equivalent, jslog_unify_with_occurs_check
} from "./unify";

///////////////////////////////////
// * Builtin functions
///////////////////////////////////

///////////////////////////////////
// *_try_fn(goal) is a traversal function called when attempting to prove
// goal.  goal was just removed from frontier, but is not on either frontier or explored stack.
// goal will need to be placed on one of either the frontier or explored stack.
// Returns true if the goal can be explored further, false if not.
// If false, then all bindings must be undone.
// If an exception is thrown, only the bindings for goal are undone externally. If the *_try_fn
// has caused any bindings for another goal, it must try / catch for exceptions and clean up
// before re-throwing.
// Assumes goal.bindings == new Array()
///////////////////////////////////

function true_try_fn(goal: any, prover: any)
{
 prover.explored.push(goal);
 return true;
}


export function cut_try_fn(goal: any, prover: any)
{var g;
 var gs_with_undo_fn = null;

 while ((g = prover.explored.pop()) != undefined)
 {
  if (g == goal.parent) // cutoff parent found -- break
  {
   if (gs_with_undo_fn != null) // non-mergeable goals to return to explored stack
   {
    prover.explored.push(g);

    while ((g = gs_with_undo_fn.pop()) != undefined)
     prover.explored.push(g);

    prover.explored.push(goal);
   }
   else if (goal.parent_is_ancestor)
   {
    prover.explored.push(g);
   }
   else if (g.parent != null && prover.explored[prover.explored.length - 1] == g.parent)
   {var i = prover.frontier.length - 1;

	while (i >= 0 && prover.frontier[i].parent == g)
	{
	 prover.frontier[i].parent = g.parent;
	 prover.frontier[i].parent_is_ancestor = true;
	 --i;
	}

	mergeGoalBindings(g,g.parent);
   }
   else
   {
    g.noretry = true;
    prover.explored.push(g);
   }

   return true;
  }
  else if (g.undo_fn != undefined) // goal with unmergeable bindings (must wait for retry to undo)
  {
   if (gs_with_undo_fn == null)
    gs_with_undo_fn = new Array();
   gs_with_undo_fn.push(g);
  }
  else // sub-goal with mergeable bindings
  {
   mergeGoalBindings(g,g.parent);
  }
 };

 prover.explored.push(goal);
 return true;
}


export function internal_clause_try_fn(goal: any, prover: any)
{var encl = getFinalEnclosure(goal.encl);
 var head = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var body = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var rref = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[2]));
 var idx = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[3]));
 var ruleset;

 // find ruleset
 if (isObjectReference(rref.term) && (isAtom(head.term) || isVariable(head.term)))
  goal.subgoal = newAtomGoalFromRuleSet(head,goal,rref.term.name,goal.kb);
 else if (isAtom(head.term))
  goal.subgoal = newAtomGoal(head,goal,goal.kb);
 else
  throw newErrorException("Expected head atom or a ruleset object reference in internal:clause/5.");

 if (isVariable(idx.term))
  goal.subgoal.rule_index = 0;
 else if (isInteger(idx.term))
  goal.subgoal.rule_index = idx.term.name;
 else
  throw newErrorException("Expected variable or integer for rule index in internal:clause/5.");

 goal.subgoal.kb = goal.kb;

 if (goal.subgoal.ruleset == undefined)
 {
  prover.frontier.push(goal);
  goal.subgoal = null;
  return false;
 }

 return internal_clause_test(body,rref,idx,goal,prover);
}

// helper for internal_clause_*_fn
// removes all goal bindings on failure.
function internal_clause_test(body: any, rref: any, idx: any, goal: any, prover: any)
{var rule_body;

 do
 {
  rule_body = nextUnifiedRuleBodyForGoal(goal.subgoal);

  if (rule_body != null)
  {var rbody = getConsPairEnclosureFromEnclosureArray(rule_body);
   var rset = newTermEnclosure(newObjectReference(goal.subgoal.ruleset));
   var n = newTermEnclosure(newNumber(goal.subgoal.rule_index));

   if (jslog_unify(body,rbody,goal.bindings) && jslog_unify(rref,rset,goal.bindings) &&
		jslog_unify(idx,n,goal.bindings))
   {
    prover.explored.push(goal);
    return true;
   }
   else
   {
    removeBindings(goal.bindings);
    internal_clause_undo_fn(goal);
	goal.subgoal.rule_index++;
   }
  }
 } while (rule_body != null && !isNumber(idx.term)) // one chance only if idx bound

 // no rules matches
 {
  removeBindings(goal.bindings);
  internal_clause_undo_fn(goal);
  prover.frontier.push(goal);
  goal.subgoal = null;
  return false;
 }
}


export function internal_current_op_try_fn(goal: any, prover: any)
{var encl = getFinalEnclosure(goal.encl);
 var name = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var optype = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var pri = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[2]));
 var rref = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[3]));

 goal.rulesets_array = new Array();
 goal.rulesets_index = 0;

 if (isObjectReference(rref.term))
 {
   if (!isOperatorRuleSet(rref.term.name))
    throw newErrorException("Invalid ruleset reference:current_op/4.");

   goal.rulesets_array[0] = rref.term.name;
 }
 else if (isConstant(name.term))
 {
  if (isConstant(optype.term))
  {
   var type_num = getOperatorTypeFromString(optype.term.name);

   if (type_num == null)
    throw newErrorException("Invalid operator type ("+optype.term.name+"):current_op/4.");

   var arity;

   if (type_num < OP_TYPE_FX)
    arity = 2;
   else
    arity = 1;

   var ruleset = getRuleSetFromNameArity(goal.kb,name.term.name,arity);

   if (ruleset != null)
    goal.rulesets_array[0] = ruleset;
  }
  else
  {
   var ruleset;

   ruleset = getRuleSetFromNameArity(goal.kb,name.term.name,1);

   if (ruleset != null)
    goal.rulesets_array[goal.rulesets_array.length] = ruleset;

   ruleset = getRuleSetFromNameArity(goal.kb,name.term.name,2);

   if (ruleset != null)
    goal.rulesets_array[goal.rulesets_array.length] = ruleset;
  }
 }
 else if (isConstant(optype.term))
 {
   var type_num = getOperatorTypeFromString(optype.term.name);
   var pri_num = null;

   if (type_num == null)
    throw newErrorException("Invalid operator type ("+optype.term.name+"):current_op/4.");

  if (isInteger(pri.term))
  {
   if (pri.term.name < 0 || pri.term.name > 1200)
    throw newErrorException("Invalid operator priority value ("+pri.term.name+"):current_op/4.");

   pri_num = pri.term.name;
  }

  internal_current_op_collect_rulesets(goal.rulesets_array,goal.kb,type_num,pri_num);
 }
 else if (isInteger(pri.term))
 {
   if (pri.term.name < 0 || pri.term.name > 1200)
    throw newErrorException("Invalid operator priority value ("+pri.term.name+"):current_op/4.");

  internal_current_op_collect_rulesets(goal.rulesets_array,goal.kb,null,pri.term.name);
 }
 else // collect all rulesets
 {
  internal_current_op_collect_rulesets(goal.rulesets_array,goal.kb,null,null);
 }

 if (goal.rulesets_array.length <= 0)
 {
  prover.frontier.push(goal);
  return false;
 }

 return internal_current_op_test(name,optype,pri,rref,goal,prover);
}

// helper for internal_current_op_*_fn
// addes all rulesets matching type_num and pri_num filters to rulesets_array
// null filters match any value.
function internal_current_op_collect_rulesets(rulesets_array: any, kb: any, type_num: any, pri_num: any)
{
 for (var r in kb.rulesets)
 {
  var ruleset = kb.rulesets[r];

  if (isOperatorRuleSet(ruleset) &&
		(type_num == null || type_num == getOperatorType(ruleset)) &&
		(pri_num == null || pri_num == getOperatorPrecedence(ruleset)))
   rulesets_array[rulesets_array.length] = ruleset;
 }
}

// helper for internal_current_op_*_fn
// removes all goal bindings on failure.
function internal_current_op_test(name: any, optype: any, pri: any, rref: any, goal: any, prover: any)
{
 while (goal.rulesets_index < goal.rulesets_array.length)
 {
  var ruleset = goal.rulesets_array[goal.rulesets_index];

  var rref2 = newTermEnclosure(newObjectReference(ruleset));
  var name2 = newTermEnclosure(newConstant(getRuleSetName(ruleset)));
  var pri2 = newTermEnclosure(newNumber(getOperatorPrecedence(ruleset)));
  var optype2 = newTermEnclosure(newConstant(getOperatorTypeStringFromType(getOperatorType(ruleset))));

  if (jslog_unify(name,name2,goal.bindings) && jslog_unify(rref,rref2,goal.bindings) &&
		jslog_unify(optype,optype2,goal.bindings) && jslog_unify(pri,pri2,goal.bindings))
  {
   prover.explored.push(goal);
   return true;
  }
  else
  {
   removeBindings(goal.bindings);
   goal.rulesets_index++;
  }
 }

 // no ruleset matches
 {
  removeBindings(goal.bindings);
  prover.frontier.push(goal);
  return false;
 }
}


export function internal_catch_try_fn(goal: any, prover: any)
{var encl = getFinalEnclosure(goal.encl);
 var g = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var t3 = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[2]));

 goal.prover = newQueryProver(prover.kb,g);

 try
 {var t = newSubtermEnclosure(encl.enclosure,newConstant('true'));

  if (proveProver(goal.prover) && jslog_unify(t3,t,goal.bindings))
  {
   prover.explored.push(goal);
   return true;
  }

  removeBindings(goal.bindings);
  stopProver(goal.prover);
  prover.frontier.push(goal);
  return false;
 }
 catch (err)
 {
  return internal_catch_handle_catch(encl,err,t3,goal,prover);
 }
}

function internal_catch_handle_catch(encl: any, err: any, t3: any, goal: any, prover: any)
{var e;
 var ex = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));

 stopProver(goal.prover);

 if (err.constructor == Exception)
  e = err.encl;
 else
 {
  err = newInternalErrorException(err.toString())
  e = err.encl;
 }

 if (jslog_unify(e,ex,goal.bindings))
 {var f = newSubtermEnclosure(encl.enclosure,newConstant('fail'));

  if (jslog_unify(t3,f,goal.bindings))
  {
   prover.explored.push(goal);
   return true;
  }

  removeBindings(goal.bindings);
  prover.frontier.push(goal);
  return false;
 }
 else
 {
  removeBindings(goal.bindings);
  throw err;
 }
}


///////////////////////////////////
// *_retry_fn(goal,prover) is a traversal function called when attempting to prove
// goal again (i.e., a goal retry).  goal was just removed from explored, but is not on either
// frontier or explored stack.
// goal will need to be placed on one of either the frontier or explored stack.
// Returns true if the goal can be explored further, false if not.
// If false, then all bindings must be undone.
// If an exception is thrown, only the bindings for goal are undone externally. If the *_try_fn
// has caused any bindings for another goal, it must try / catch for exceptions and clean up
// before re-throwing.
// Assumes goal.bindings == new Array()
///////////////////////////////////

export function cut_retry_fn(goal: any, prover: any)
{var g;

 if (!goal.parent_is_ancestor)
  removeChildGoalsFromFrontier(goal.parent,prover.frontier)

 while ((g = prover.explored.pop()) != undefined)
 {
  undoGoal(g,false);
  if (g == goal.parent)
  {
   if (goal.parent_is_ancestor)
    prover.explored.push(g);
   else
    prover.frontier.push(g);
   break;
  }
 };

 return false;
}


export function internal_clause_retry_fn(goal: any, prover: any)
{var encl = getFinalEnclosure(goal.encl);
 var body = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var rref = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[2]));
 var idx = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[3]));
 var doinc = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[4]));

 // if idx was bound, there is no retry
 if (isNumber(idx.term))
 {
  prover.frontier.push(goal);
  goal.subgoal = null;
  return false;
 }

 if (isInteger(doinc.term))
  goal.subgoal.rule_index += doinc.term.name;
 else
  goal.subgoal.rule_index++;

 return internal_clause_test(body,rref,idx,goal,prover);
}


export function internal_current_op_retry_fn(goal: any, prover: any)
{var encl = getFinalEnclosure(goal.encl);
 var name = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var optype = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var pri = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[2]));
 var rref = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[3]));

 goal.rulesets_index++;

 if (goal.rulesets_index >= goal.rulesets_array.length)
 {
  prover.frontier.push(goal);
  return false;
 }

 return internal_current_op_test(name,optype,pri,rref,goal,prover);
}


export function internal_catch_retry_fn(goal: any, prover: any)
{var encl = getFinalEnclosure(goal.encl);
 var t3 = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[2]));

 if (isProverStateDone(goal.prover))
 {
  prover.frontier.push(goal);
  return false;
 }

 try
 {var t = newSubtermEnclosure(encl.enclosure,newConstant('true'));

  if (retryProver(goal.prover) && jslog_unify(t3,t,goal.bindings))
  {
   prover.explored.push(goal);
   return true;
  }

  removeBindings(goal.bindings);
  stopProver(goal.prover);
  prover.frontier.push(goal);
  return false;
 }
 catch (err)
 {
  return internal_catch_handle_catch(encl,err,t3,goal,prover);
 }
}


///////////////////////////////////
// *_undo_fn(goal,retry) is a binding undo function called when undoing or retrying traversal goal.
// If retry is true, then a retry attempt will follow, if retry if false, undo completely.
// Only needs to undo bindings other than goal.bindings.
// It is important that *_undo_fn functions never fail to undo their bindings, even if called
// multiple times for the same goal, and they should never throw exceptions -- except if system
// integrity is compromised.
///////////////////////////////////

export function internal_clause_undo_fn(goal: any, retry: any = undefined)
{
 if (goal.subgoal != null && goal.subgoal.bindings != null)
  removeBindings(goal.subgoal.bindings);
}

export function internal_catch_undo_fn(goal: any, retry: any)
{
 if (!retry && goal.prover != null)
  stopProver(goal.prover);
}


///////////////////////////////////
// *_fn(goal) is a function called when attempting to prove goal.
// Returns true if the goal succeeds, false if not.
// If false, then all bindings must be undone.  Only use goal.bindings to register bindings.
// Assumes goal.bindings == new Array()
///////////////////////////////////

export function is_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x;

 x = jslog_Evaluate(goal.kb,rhs);

 if (!isNumber(x))
  throw newErrorException("Expected RHS to evaluate to a number in operator: is/2");

 return jslog_unify(lhs,newBlankEnclosure(0,x),goal.bindings);
}

export function throw_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var term = newDuplicateTermFromEnclosure(lhs);

 throw new Exception(newTermEnclosure(term));
}

export function isvar_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));

 return (isVariable(lhs.term));
}

export function isnonvar_fn(goal: any)
{
 return (!isvar_fn(goal));
}

export function isconstant_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));

 return (isConstant(lhs.term));
}

export function isconstornum_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));

 return (isConstant(lhs.term) || isNumber(lhs.term));
}

export function iscompound_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));

 return (isAtom(lhs.term) && lhs.term.children.length > 0);
}

export function isnumber_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));

 return (isNumber(lhs.term));
}

export function isinteger_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));

 return (isInteger(lhs.term));
}

export function lt_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;

 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);

 if (isNumber(x) && isNumber(y))
  return x.name < y.name;
 else
  throw newErrorException("Expression evaluating to Number expected in operator: </2");
}

export function lte_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;

 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);

 if (isNumber(x) && isNumber(y))
  return x.name <= y.name;
 else
  throw newErrorException("Expression evaluating to Number expected in operator: =</2");
}

export function gt_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;

 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);

 if (isNumber(x) && isNumber(y))
  return x.name > y.name;
 else
  throw newErrorException("Expression evaluating to Number expected in operator: >/2");
}

export function gte_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;

 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);

 if (isNumber(x) && isNumber(y))
  return x.name >= y.name;
 else
  throw newErrorException("Expression evaluating to Number expected in operator: >=/2");
}

export function eq_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;

 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);

 if (isNumber(x) && isNumber(y))
  return x.name == y.name;
 else
  throw newErrorException("Expression evaluating to Number expected in operator: =:=/2");
}

export function neq_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;

 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);

 if (isNumber(x) && isNumber(y))
  return x.name != y.name;
 else
  throw newErrorException("Expression evaluating to Number expected in operator: =\=/2");
}

export function unify_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);

 return jslog_unify(lhs,rhs,goal.bindings);
}

export function unify_with_occurs_check_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);

 return jslog_unify_with_occurs_check(lhs,rhs,goal.bindings);
}

export function identical_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);

 return (result == 0);
}

export function internal_equivalent_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));

 return jslog_equivalent(lhs,rhs);
}

export function internal_nequivalent_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));

 return !jslog_equivalent(lhs,rhs);
}

export function internal_compare_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var cret = newSubtermEnclosure(encl.enclosure,encl.term.children[2]);
 var result = jslog_compare(lhs,rhs);
 var cval;

 if (result < 0)
  cval = '<';
 else if (result > 0)
  cval = '>';
 else
  cval = '=';

 return jslog_unify(cret,newSubtermEnclosure(encl.enclosure,newConstant(cval)),goal.bindings);
}

export function compare_lt_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);

 return (result < 0);
}

export function compare_lte_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);

 return (result <= 0);
}

export function compare_gt_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);

 return (result > 0);
}

export function compare_gte_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);

 return (result >= 0);
}

export function arg_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var idx = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[2]);

 if (isInteger(idx.term))
 {var i = idx.term.name - 1;

  if (isAtom(lhs.term))
  {
   if (i >= 0 && i < lhs.term.children.length)
   {var t = getFinalEnclosure(newSubtermEnclosure(lhs.enclosure,lhs.term.children[i]));

    return jslog_unify(rhs,t,goal.bindings);
   }
   else
    throw newErrorException("Index out of bounds in arg/3.");
  }
  else
   throw newErrorException("Expected atom in arg/3.");
 }
 else
  throw newErrorException("Expected integer in arg/3.");
}

export function atom_to_list_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));

 if (isAtom(lhs.term))
 {var list = newListNull();

  for (var i = lhs.term.children.length - 1; i >= 0; i--)
   list = newListPair(lhs.term.children[i],list);

  lhs = newSubtermEnclosure(lhs.enclosure,newListPair(newConstant(lhs.term.name),list));
 }
 else if (isNumber(lhs.term))
 {
  lhs = newBlankEnclosure(0,newListPair(lhs.term,newListNull()));
 }
 else if (isListPair(rhs.term))
 {var head = getFinalEnclosure(newSubtermEnclosure(rhs.enclosure,rhs.term.children[0]));
  var atom;

  if (isConstant(head.term))
  {
   atom = newBlankEnclosure(0,newAtom(head.term.name,[]));
  }
  else
   throw newErrorException("Expected constant value in =../2.");

  do
  {
   rhs = getFinalEnclosure(newSubtermEnclosure(rhs.enclosure,rhs.term.children[1]));

   if (isListPair(rhs.term))
   {let i = atom.term.children.length;
    var v = newVariable('_');

    head = getFinalEnclosure(newSubtermEnclosure(rhs.enclosure,rhs.term.children[0]));

	v.children[0] = i;
    atom.term.children[i] = v;
	atom.enclosure[i] = head;
   }
   else if (isListNull(rhs.term))
    break;
   else
    throw newErrorException("Expected list pair in =../2.");

  } while (head != null);

  rhs = atom;
 }
 else
  throw newErrorException("Expected valid instantiated value in =../2.");

 return jslog_unify(lhs,rhs,goal.bindings);
}

export function atom_length_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var l;

 if (!isConstant(lhs.term))
  throw newErrorException("Expected constant atom in atom_lenth/2.");

 l = newSubtermEnclosure(encl.enclosure,newNumber(lhs.term.name.length));

 return jslog_unify(rhs,l,goal.bindings);
}

export function char_code_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var c;

 if (isConstant(lhs.term))
 {
  if (lhs.term.name.length != 1)
   throw newErrorException("Expected single character atom in char_code/2.");

  c = newSubtermEnclosure(encl.enclosure,newNumber(lhs.term.name.charCodeAt(0)));

  return jslog_unify(rhs,c,goal.bindings);
 }
 else if (isInteger(rhs.term))
 {
  c = newSubtermEnclosure(encl.enclosure,newConstant(String.fromCharCode(rhs.term.name)));

  return jslog_unify(lhs,c,goal.bindings);
 }
 else
  throw newErrorException("Expected either atom or integer in char_code/2.");
}

export function atom_chars_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var c;

 if (isConstant(lhs.term))
 {var cp = newListNull();

  for (var i = lhs.term.name.length - 1; i >= 0; i--)
   cp = newListPair(newConstant(lhs.term.name.charAt(i)),cp);

  c = newSubtermEnclosure(encl.enclosure,cp);

  return jslog_unify(rhs,c,goal.bindings);
 }
 else
 {var s = "";
  let cp;

  while (!isListNull(rhs.term))
  {
   if (!isListPair(rhs.term))
    throw newErrorException("Expected either atom constant or character list in atom_chars/2.");

   cp = getFinalEnclosure(newSubtermEnclosure(rhs.enclosure,rhs.term.children[0]));

   if (isConstant(cp.term) && cp.term.name.length == 1)
   {
    s += cp.term.name;
   }
   else
    throw newErrorException("Expected single character atoms in character list in atom_chars/2.");

   rhs = getFinalEnclosure(newSubtermEnclosure(rhs.enclosure,rhs.term.children[1]));
  }

  c = newSubtermEnclosure(encl.enclosure,newConstant(s));

  return jslog_unify(lhs,c,goal.bindings);
 }
}

export function internal_number_atom_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var c;

 if (isNumber(lhs.term))
 {
  c = newSubtermEnclosure(encl.enclosure,newConstant(lhs.term.name.toString()));
  return jslog_unify(rhs,c,goal.bindings);
 }
 else if (isConstant(rhs.term))
 {var n = parseFloat(rhs.term.name);

  if (isNaN(n))
   throw newErrorException("Expected atom representing number in internal:number_atom/2.");

  c = newSubtermEnclosure(encl.enclosure,newNumber(n));
  return jslog_unify(lhs,c,goal.bindings);
 }
 else
  throw newErrorException("Expected number or atom constant in internal:number_atom/2.");
}

export function copy_term_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);

 return jslog_unify(newDuplicateEnclosure(lhs),rhs,goal.bindings);
}

export function internal_copy_term_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var term = newDuplicateTermFromEnclosure(lhs);

 return jslog_unify(newTermEnclosure(term),rhs,goal.bindings);
}

export function internal_term_variables_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var vencls = enumFinalVariableEnclosures(lhs);
 var vlist;
 var result;

 vlist = newListNull();

 for (var i = vencls.length - 1; i >= 0; i--)
 {var v = newVariable('_');

  v.children[0] = i;

  vlist = newListPair(v,vlist);
 }

 result = newSubtermEnclosure(vencls,vlist);

 return jslog_unify(result,rhs,goal.bindings);
}

export function internal_current_predicate_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var lterm = newListNull();
 var ruleset;
 var name;
 var arity;

 // test for name/arity structure
 {var namearity = newTermEnclosure(newAtom('/',[newVariable('N'),newVariable('A')]));

  if (!jslog_unify(lhs,namearity,goal.bindings))
   throw newErrorException("Expected name/arity functor in internal:current_predicate/2.");
 }

 {var nlhs = getFinalEnclosure(lhs);

  name = getFinalEnclosure(newSubtermEnclosure(nlhs.enclosure,nlhs.term.children[0]));
  arity = getFinalEnclosure(newSubtermEnclosure(nlhs.enclosure,nlhs.term.children[1]));
 }

 if (isConstant(name.term) && isInteger(arity.term))
 {var functor = newAtom('/',[name.term,arity.term]);
  var isdyn;
  var rref;

  ruleset = getRuleSetFromNameArity(goal.kb,name.term.name,arity.term.name);

  if (ruleset == undefined)
  {
   removeBindings(goal.bindings);
   return false;
  }

  isdyn = newConstant(isDynamicRuleSet(ruleset) ? 'true' : 'fail' );
  rref = newObjectReference(ruleset);

  lterm = newListPair(newAtom('rs',[functor,isdyn,rref]),lterm);
 }
 else if ((isConstant(name.term) || isVariable(name.term)) &&
			(isInteger(arity.term) || isVariable(arity.term)))
 {var rulekey

  for (rulekey in goal.kb.rulesets)
  {var slashidx = rulekey.lastIndexOf('/');
   var rname = rulekey.substring(0,slashidx);
   var rarity = parseInt(rulekey.substring(slashidx+1));

   ruleset = getRuleSetFromNameArity(goal.kb,rname,rarity);

   if ((isVariable(name.term) || name.term.name == ruleset.name) &&
		(isVariable(arity.term) || arity.term.name == ruleset.arity))
   {var functor = newAtom('/',[newConstant(ruleset.name),newNumber(ruleset.arity)]);
    let isdyn = newConstant(isDynamicRuleSet(ruleset) ? 'true' : 'fail' );
    let rref = newObjectReference(ruleset);

    lterm = newListPair(newAtom('rs',[functor,isdyn,rref]),lterm);
   }
  }
 }
 else
  throw newErrorException("Expected name/arity functor in internal:current_predicate/2.");

 return jslog_unify(rhs,newSubtermEnclosure(encl.enclosure,lterm),goal.bindings);
}

function internal_assert_fn(append: any, goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var orig = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var term = newDuplicateTermFromEnclosure(orig);
 var rule = newRule(term);
 var ruleset = getRuleSetFromNameArity(goal.kb,rule.name,rule.arity);

 if (!isDynamicRuleSet(ruleset))
  throw newErrorException("Must declare rule dynamic to modify: "+getRuleNameArity(rule));

 addRule(goal.kb,rule,append);

 return true;
}

export function asserta_fn(goal: any)
{
 return internal_assert_fn(false,goal);
}

export function assertz_fn(goal: any)
{
 return internal_assert_fn(true,goal);
}

export function write_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);

 (<any> window.document).formUI.output.value += jslog_toString(lhs,goal.kb);
 return true;
}

export function nl_fn(goal: any)
{
 (<any> window.document).formUI.output.value += "\n";
 return true;
}

export function internal_atom_append_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));

 if (isAtom(lhs.term))
 {var ci = lhs.term.children.length;
  var ei = lhs.enclosure.length;
  var v = newVariable('_');

  v.children[0] = ei;
  lhs.term.children[ci] = v;
  lhs.enclosure[ei] = rhs;

  lhs.ruleset = undefined;
 }
 else
  throw newErrorException("Expected atom in internal:atom_append!/2.");

 return true;
}

export function internal_atom_setarg_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var idx = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[2]));

 if (isInteger(idx.term))
 {var i = idx.term.name - 1;

  if (isAtom(lhs.term))
  {
   if (i >= 0 && i < lhs.term.children.length)
   {var t = lhs.term.children[i];

    if (isVariable(t))
	{
     lhs.enclosure[t.children[0]] = rhs;
	}
	else
	{var v = newVariable('_');
     var ei = lhs.enclosure.length;

     v.children[0] = ei;
     lhs.term.children[i] = v;
     lhs.enclosure[ei] = rhs;
	}
   }
   else
    throw newErrorException("Index out of bounds in internal:atom_setarg!/3.");
  }
  else
   throw newErrorException("Expected atom in internal:atom_setarg!/3.");
 }
 else
  throw newErrorException("Expected integer in internal:atom_setarg!/3.");

 return true;
}

export function internal_retract_fn(goal: any)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var ruleset;

 if (!(isObjectReference(lhs.term) && lhs.term.name != undefined))
  throw newErrorException("Expected ruleset object reference in internal:retract/2.");

 if (!isInteger(rhs.term))
  throw newErrorException("Expected integer rule index in internal:retract/2.");

 removeRuleFromRuleSet(lhs.term.name,rhs.term.name);

 return true;
}


///////////////////////////////////
// *_eval_fn(values) is a function called when evaluating an expression.
// values is a stack of value terms.  The function should pop off the N number of values
// from the values stack it needs, compute the single value result, and push the
// result back onto values.
// The argument order of values is the same order as for the function (i.e., Nth argument
// is the Nth pop).
// Must succeed, returning the computed value, or throw an exception.
// NOTE: Terms on the values stack are immutable and should never be changed.
///////////////////////////////////

export function positive_eval_fn(values: any)
{var i = values.pop();

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 values.push(i);
 return i;
}

export function negative_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(-1 * i.name);
 values.push(result);
 return result;
}

export function plus_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber(i.name + j.name);
 values.push(result);
 return result;
}

export function minus_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber(i.name - j.name);
 values.push(result);
 return result;
}

export function multiply_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber(i.name * j.name);
 values.push(result);
 return result;
}

export function divide_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber(i.name / j.name);
 values.push(result);
 return result;
}

export function intdivide_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var val;
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber(i.name / j.name);
 values.push(result);

 result = trunc_eval_fn(values);
 return result;
}

export function mod_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber(i.name % j.name);
 values.push(result);
 return result;
}

export function pow_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber(Math.pow(i.name,j.name));
 values.push(result);
 return result;
}

export function exp_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.exp(i.name));
 values.push(result);
 return result;
}

export function log_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.log(i.name));
 values.push(result);
 return result;
}

export function sqrt_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.sqrt(i.name));
 values.push(result);
 return result;
}

export function abs_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.abs(i.name));
 values.push(result);
 return result;
}

export function sin_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.sin(i.name));
 values.push(result);
 return result;
}

export function cos_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.cos(i.name));
 values.push(result);
 return result;
}

export function tan_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.tan(i.name));
 values.push(result);
 return result;
}

export function asin_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.asin(i.name));
 values.push(result);
 return result;
}

export function acos_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.acos(i.name));
 values.push(result);
 return result;
}

export function atan_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.atan(i.name));
 values.push(result);
 return result;
}

export function atan2_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber(Math.atan2(i.name,j.name));
 values.push(result);
 return result;
}

export function trunc_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 if (i.name < 0)
  result = newNumber(-1 * Math.floor(Math.abs(i.name)));
 else
  result = newNumber(Math.floor(i.name));

 values.push(result);
 return result;
}

export function floor_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.floor(i.name));
 values.push(result);
 return result;
}

export function ceiling_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.ceil(i.name));
 values.push(result);
 return result;
}

export function round_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber(Math.round(i.name));
 values.push(result);
 return result;
}

export function sign_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 if (i.name > 0)
  result = newNumber(1);
 else if (i.name < 0)
  result = newNumber(-1);
 else
  result = newNumber(0);

 values.push(result);
 return result;
}

export function fractional_part_eval_fn(values: any)
{var i = values.pop();
 var v;
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 v = i.name;

 values.push(i);
 trunc_eval_fn(values);

 i = values.pop(); // trunc_eval_fn returns a number

 result = newNumber(v - i.name);
 values.push(result);
 return result;
}

export function bitwise_and_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber((i.name & j.name));
 values.push(result);
 return result;
}

export function bitwise_or_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber((i.name | j.name));
 values.push(result);
 return result;
}

export function bitwise_xor_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber((i.name ^ j.name));
 values.push(result);
 return result;
}

export function bitwise_negate_eval_fn(values: any)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i))
  throw newErrorException("Expected Number value.");

 result = newNumber((~ i.name));
 values.push(result);
 return result;
}

export function bitwise_lshift_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber((i.name << j.name));
 values.push(result);
 return result;
}

export function bitwise_rshift_eval_fn(values: any)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j))
  throw newErrorException("Expected Number values.");

 result = newNumber((i.name >> j.name));
 values.push(result);
 return result;
}
