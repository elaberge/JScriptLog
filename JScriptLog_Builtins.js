/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// * Builtin functions
///////////////////////////////////

///////////////////////////////////
// *_try_fn(goal,frontier,explored) is a traversal function called when attempting to prove
// goal.  goal was just removed from frontier, but is not on either frontier or explored stack.
// goal will need to be placed on one of either the frontier or explored stack.
// Returns true if the goal can be explored further, false if not.
///////////////////////////////////

function true_try_fn(goal,frontier,explored)
{
 explored.push(goal);
 return true;
}

// FIX: Handle case where term is a rule.
function retract_try_fn(goal,frontier,explored)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));

 goal.subgoal = newAtomGoal(lhs,goal,goal.kb);
 goal.subgoal.kb = goal.kb;
 goal.subgoal.rule_index = 0;
 
 if (goal.subgoal.ruleset == undefined)
 {
  frontier.push(goal);
  goal.subgoal = null;
  return false;
 }

 var rule_body = nextUnifiedRuleBodyForGoal(goal.subgoal);
 
 if (rule_body != null)
 {
  removeRuleFromRuleSet(goal.subgoal.ruleset,goal.subgoal.rule_index);
  explored.push(goal);
  return true;
 }
 else // no rule matches
 {
  frontier.push(goal);
  goal.subgoal = null;
  return false;
 } 
}

///////////////////////////////////
// *_retry_fn(goal,frontier,explored) is a traversal function called when attempting to prove
// goal again (i.e., a goal retry).  goal was just removed from explored, but is not on either 
// frontier or explored stack.
// goal will need to be placed on one of either the frontier or explored stack.
// Returns true if the goal can be explored further, false if not.
///////////////////////////////////

function cut_retry_fn(goal,frontier,explored)
{var g;

 removeChildGoalsFromFrontier(goal.parent,frontier)

 undoGoalBindings(goal);

 while ((g = explored.pop()) != undefined)
 {
  undoGoalBindings(g);
  if (g == goal.parent)
  {
   frontier.push(g);
   break;
  }
 };
 
 return false;
}

// FIX: Handle case where term is a rule.
function retract_retry_fn(goal,frontier,explored)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 
 undoGoalBindings(goal.subgoal);

 var rule_body = nextUnifiedRuleBodyForGoal(goal.subgoal);
 
 if (rule_body != null)
 {
  removeRuleFromRuleSet(goal.subgoal.ruleset,goal.subgoal.rule_index);
  explored.push(goal);
  return true;
 }
 else // no rule matches
 {
  frontier.push(goal);
  goal.subgoal = null;
  return false;
 } 
}

///////////////////////////////////
// *_fn(goal) is a function called when attempting to prove goal.  
// Returns true if the goal succeeds, false if not.
///////////////////////////////////

function is_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x;
 
 x = jslog_Evaluate(goal.kb,rhs);
 
 if (!isNumber(x))
  throw new Error("Expected RHS to evaluate to a number in operator: is/2");
  
 return jslog_unify(lhs,newBlankEnclosure(0,x),goal.bindings);
}

function throw_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var term = newDuplicateTermFromEnclosure(lhs);

 throw new Exception(newTermEnclosure(term));
 return false;
}

function isvar_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 
 return (isVariable(lhs.term));
}

function isnonvar_fn(goal)
{
 return (!isvar_fn(goal));
}

function isconstant_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 
 return (isConstant(lhs.term));
}

function isconstornum_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 
 return (isConstant(lhs.term) || isNumber(lhs.term));
}

function iscompound_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 
 return (isAtom(lhs.term) && lhs.term.children.length > 0);
}

function isnumber_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 
 return (isNumber(lhs.term));
}

function isinteger_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));

 return (isNumber(lhs.term) && (Math.round(lhs.term.name) == lhs.term.name));
}

function lt_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;
 
 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);
 
 if (isNumber(x) && isNumber(y))
  return x.name < y.name;
 else
  throw new Error("Expression evaluating to Number expected in operator: </2");
}

function lte_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;
 
 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);
 
 if (isNumber(x) && isNumber(y))
  return x.name <= y.name;
 else
  throw new Error("Expression evaluating to Number expected in operator: =</2");
}

function gt_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;
 
 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);
 
 if (isNumber(x) && isNumber(y))
  return x.name > y.name;
 else
  throw new Error("Expression evaluating to Number expected in operator: >/2");
}

function gte_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;
 
 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);
 
 if (isNumber(x) && isNumber(y))
  return x.name >= y.name;
 else
  throw new Error("Expression evaluating to Number expected in operator: >=/2"); 
}

function eq_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;
 
 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);
 
 if (isNumber(x) && isNumber(y))
  return x.name == y.name;
 else
  throw new Error("Expression evaluating to Number expected in operator: =:=/2"); 
}

function neq_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x,y;
 
 x = jslog_Evaluate(goal.kb,lhs);
 y = jslog_Evaluate(goal.kb,rhs);
 
 if (isNumber(x) && isNumber(y))
  return x.name != y.name;
 else
  throw new Error("Expression evaluating to Number expected in operator: =\=/2"); 
}

function unify_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 
 return jslog_unify(lhs,rhs,goal.bindings); 
}

function identical_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);
 
 return (result == 0); 
}

function internal_compare_fn(goal)
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

function compare_lt_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);
 
 return (result < 0); 
}

function compare_lte_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);
 
 return (result <= 0); 
}

function compare_gt_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);
 
 return (result > 0); 
}

function compare_gte_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var result = jslog_compare(lhs,rhs);
 
 return (result >= 0); 
}

function arg_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var idx = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[2]);

 if (isNumber(idx.term) && (Math.round(idx.term.name) == idx.term.name))
 {var i = idx.term.name - 1;
 
  if (isAtom(lhs.term))
  {
   if (i >= 0 && i < lhs.term.children.length) 
   {var t = getFinalEnclosure(newSubtermEnclosure(lhs.enclosure,lhs.term.children[i]));
   
    return jslog_unify(rhs,t,goal.bindings);  
   }	
   else
    throw new Error("Index out of bounds in arg/3.");
  }
  else
   throw new Error("Expected atom in arg/3.");
 }
 else
  throw new Error("Expected integer in arg/3.");

 return false; 
}

function atom_to_list_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 
 if (isAtom(lhs.term))
 {var list = newListNull();
  var i;
  
  for (i = lhs.term.children.length - 1; i >= 0; i--)
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
   throw new Error("Expected constant value in =../2.");
  
  do
  {
   rhs = getFinalEnclosure(newSubtermEnclosure(rhs.enclosure,rhs.term.children[1]));

   if (isListPair(rhs.term))
   {var i = atom.term.children.length;
    var v = newVariable('_');
	
    head = getFinalEnclosure(newSubtermEnclosure(rhs.enclosure,rhs.term.children[0]));
   
	v.children[0] = i;
    atom.term.children[i] = v;
	atom.enclosure[i] = head;
   }
   else if (isListNull(rhs.term))
    break;
   else
    throw new Error("Expected list pair in =../2.");
    
  } while (head != null);

  rhs = atom;
 }
 else
  throw new Error("Expected valid instantiated value in =../2.");

 return jslog_unify(lhs,rhs,goal.bindings); 
}

function copy_term_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);

 return jslog_unify(newDuplicateEnclosure(lhs),rhs,goal.bindings);
}

function internal_copy_term_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var term = newDuplicateTermFromEnclosure(lhs);

 return jslog_unify(newTermEnclosure(term),rhs,goal.bindings);
}

function internal_term_variables_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 var vencls = enumFinalVariableEnclosures(lhs);
 var vlist;
 var result;
 var i;

 vlist = newListNull();
 
 for (i = vencls.length - 1; i >= 0; i--)
 {var v = newVariable('_');
 
  v.children[0] = i;
  
  vlist = newListPair(v,vlist);
 }

 result = newSubtermEnclosure(vencls,vlist);
 
 return jslog_unify(result,rhs,goal.bindings);
}

function internal_assert_fn(append,goal)
{var encl = getFinalEnclosure(goal.encl);
 var orig = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var term = newDuplicateTermFromEnclosure(orig);
 var rule = newRule(term);
 var ruleset = getRuleSet(goal.kb,term);
 
 if (!isDynamicRuleSet(ruleset))
  throw new Error("Must declare rule dynamic to modify: "+getRuleNameArity(rule));
    
 addRule(goal.kb,rule,append);
 
 return true;
}

function asserta_fn(goal)
{
 return internal_assert_fn(false,goal);
}

function assertz_fn(goal)
{
 return internal_assert_fn(true,goal);
}

function write_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 
 window.document.formUI.output.value += jslog_toString(lhs);
 return true; 
}

function nl_fn(goal)
{
 window.document.formUI.output.value += "\n";
 return true; 
}

function internal_atom_append_fn(goal)
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
 }
 else
  throw new Error("Expected atom in internal:atom_append!/2.");

 return true; 
}

function internal_atom_setarg_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var idx = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[2]));

 if (isNumber(idx.term) && (Math.round(idx.term.name) == idx.term.name))
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
    throw new Error("Index out of bounds in internal:atom_setarg!/3.");
  }
  else
   throw new Error("Expected atom in internal:atom_setarg!/3.");
 }
 else
  throw new Error("Expected integer in internal:atom_setarg!/3.");
 
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

function positive_eval_fn(values)
{var i = values.pop();

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
  
 values.push(i);
 return i;
}

function negative_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(-1 * i.name);
 values.push(result);
 return result;
}

function plus_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber(i.name + j.name);   
 values.push(result);
 return result;
}

function minus_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber(i.name - j.name);   
 values.push(result);
 return result;
}

function multiply_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber(i.name * j.name);   
 values.push(result);
 return result;
}

function divide_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber(i.name / j.name);   
 values.push(result);
 return result;
}

function intdivide_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var val;
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber(i.name / j.name); 
 values.push(result);
 
 result = trunc_eval_fn(values);
 return result;
}

function mod_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber(i.name % j.name);   
 values.push(result);
 return result;
}

function pow_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber(Math.pow(i.name,j.name));   
 values.push(result);
 return result;
}

function exp_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.exp(i.name));
 values.push(result);
 return result;
}

function log_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.log(i.name));
 values.push(result);
 return result;
}

function sqrt_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.sqrt(i.name));
 values.push(result);
 return result;
}

function abs_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.abs(i.name));
 values.push(result);
 return result;
}

function sin_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.sin(i.name));
 values.push(result);
 return result;
}

function cos_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.cos(i.name));
 values.push(result);
 return result;
}

function tan_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.tan(i.name));
 values.push(result);
 return result;
}

function asin_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.asin(i.name));
 values.push(result);
 return result;
}

function acos_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.acos(i.name));
 values.push(result);
 return result;
}

function atan_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber(Math.atan(i.name));
 values.push(result);
 return result;
}

function atan2_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber(Math.atan2(i.name,j.name));   
 values.push(result);
 return result;
}

function trunc_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");

 if (i.name < 0)
  result = newNumber(-1 * Math.floor(Math.abs(i.name)));
 else 
  result = newNumber(Math.floor(i.name));
 
 values.push(result);
 return result;
}

function floor_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");

 result = newNumber(Math.floor(i.name));
 values.push(result);
 return result;
}

function ceiling_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");

 result = newNumber(Math.ceil(i.name));
 values.push(result);
 return result;
}

function round_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");

 result = newNumber(Math.round(i.name));
 values.push(result);
 return result;
}

function sign_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");

 if (i.name > 0)
  result = newNumber(1);
 else if (i.name < 0)
  result = newNumber(-1);
 else 
  result = newNumber(0);

 values.push(result);
 return result;
}

function fractional_part_eval_fn(values)
{var i = values.pop();
 var v;
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");

 v = i.name;

 values.push(i);
 trunc_eval_fn(values);
 
 i = values.pop(); // trunc_eval_fn returns a number
 
 result = newNumber(v - i.name);  
 values.push(result);
 return result;
}

function bitwise_and_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber((i.name & j.name));   
 values.push(result);
 return result;
}

function bitwise_or_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber((i.name | j.name));   
 values.push(result);
 return result;
}

function bitwise_xor_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber((i.name ^ j.name));   
 values.push(result);
 return result;
}

function bitwise_negate_eval_fn(values)
{var i = values.pop();
 var result;

 if (i == undefined || !isNumber(i)) 
  throw new Error("Expected Number value.");
 
 result = newNumber((~ i.name));   
 values.push(result);
 return result;
}

function bitwise_lshift_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber((i.name << j.name));   
 values.push(result);
 return result;
}

function bitwise_rshift_eval_fn(values)
{var i = values.pop();
 var j = values.pop();
 var result;

 if (i == undefined || j == undefined || !isNumber(i) || !isNumber(j)) 
  throw new Error("Expected Number values.");
 
 result = newNumber((i.name >> j.name));   
 values.push(result);
 return result;
}
