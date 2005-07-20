/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_kb_* functions for Prolog KnowledgeBase
// KB* member functions for KnowledgeBase
///////////////////////////////////

// FIX: Change fn(goal) to fn(encl) where encl is the FinalEnclosure.
// FIX: RuleSets should be denote operator information (if it represents an operator).

// The KnowledgeBase (array of prolog rule clauses).
var jslog_kb = new KB();


function KB()
{var ruleset;
 var rule;

 this.rulesets = new Object();

 // true.
 {
  ruleset = new RuleSet('true',0,false);
 
  ruleset.rules.push(newRule(newConstant('true')));

  addRuleSet(this,ruleset);
 }
 // fail/0 
 {
  ruleset = new RuleSet('fail',0,false);
 
  addRuleSet(this,ruleset);
 }
 // \+(X) :- X, !, fail.
 // \+(_).
 {
  ruleset = new RuleSet('\\+',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('\\+',[newVariable('X')]),
		newConsPair(newVariable('X'),
			newConsPair(newConstant('!'),newConstant('fail'))))));
  ruleset.rules.push(newRule(newAtom('\\+',[newVariable('_')])));
 
  addRuleSet(this,ruleset);
 }
 // ;(X,_) :- X.
 // ;(_,X) :- Y.
 {
  ruleset = new RuleSet(';',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newOrPair(newVariable('X'),newVariable('_')),
		newVariable('X'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newOrPair(newVariable('_'),newVariable('X')),
		newVariable('X'))));
 
  addRuleSet(this,ruleset);
 }
 // FIX: expand all ConsPairs in Y -- shouldn't need this rule?
 // ,(X,Y) :- X,Y.
 {
  ruleset = new RuleSet(',',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newConsPair(newVariable('X'),newVariable('Y')),
		newConsPair(newVariable('X'),newVariable('Y')))));
 
  addRuleSet(this,ruleset);
 }
 // call(X) :- X.
 {
  ruleset = new RuleSet('call',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('call',[newVariable('X')]),
		newVariable('X'))));
 
  addRuleSet(this,ruleset);
 }
 // !/0 : traversal functions
 {
  ruleset = new RuleSet('!',0,false);

  ruleset.rules.push(newTraversalRule(newConstant('!'),true_try_fn,cut_retry_fn));
 
  addRuleSet(this,ruleset);
 }
 // is/2 : eval function
 {
  ruleset = new RuleSet('is',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('is',[newVariable('X'),newVariable('E')]),is_fn));
 
  addRuleSet(this,ruleset);  
 }
 // </2 : compare function
 {
  ruleset = new RuleSet('<',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('<',[newVariable('L'),newVariable('R')]),lt_fn));
 
  addRuleSet(this,ruleset);  
 }
 // =</2 : compare function
 {
  ruleset = new RuleSet('=<',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=<',[newVariable('L'),newVariable('R')]),lte_fn));
 
  addRuleSet(this,ruleset);  
 }
 // >/2 : compare function
 {
  ruleset = new RuleSet('>',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('>',[newVariable('L'),newVariable('R')]),gt_fn));
 
  addRuleSet(this,ruleset);  
 }
 // >=/2 : compare function
 {
  ruleset = new RuleSet('>=',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('>=',[newVariable('L'),newVariable('R')]),gte_fn));
 
  addRuleSet(this,ruleset);  
 }
 // =/2 : unify function
 {
  ruleset = new RuleSet('=',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=',[newVariable('L'),newVariable('R')]),unify_fn));
 
  addRuleSet(this,ruleset);  
 }
 // write/1 : ouput function
 {
  ruleset = new RuleSet('write',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('write',[newVariable('O')]),write_fn));
 
  addRuleSet(this,ruleset);  
 }
 // writeln/1 : ouput function
 {
  ruleset = new RuleSet('writeln',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('writeln',[newVariable('O')]),writeln_fn));
 
  addRuleSet(this,ruleset);  
 }
 // nl/0 : ouput function
 {
  ruleset = new RuleSet('nl',0,false);

  ruleset.rules.push(newFunctionRule(newConstant('nl'),nl_fn));
 
  addRuleSet(this,ruleset);  
 }
 // +/1 eval function
 {
  ruleset = new RuleSet('+',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,positive_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // -/1 eval function 
 {
  ruleset = new RuleSet('-',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,negative_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // +/2 eval function
 {
  ruleset = new RuleSet('+',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,plus_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // -/2 eval function
 {
  ruleset = new RuleSet('-',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,minus_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // */2 eval function
 {
  ruleset = new RuleSet('*',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,multiply_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // //2 eval function
 {
  ruleset = new RuleSet('/',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,divide_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 
 return this;
}

function RuleSet(name,arity,dynamic)
{
 this.name = name;
 this.arity = arity;
 this.dynamic = dynamic;
 this.rules = new Array();
 
 return this;
}

function Rule(name,arity,enclosure,head)
{
 this.name = name;
 this.arity = arity;
 this.enclosure = enclosure;
 this.head = head;
 this.body = new Array();

 return this;
}

function newRule(term)
{var encl = newTermEnclosure(term);
 var rule;
  
 if (isRuleTerm(term))
 {var t = term.children[0];

  if (!isAtom(t))
   throw Error("Rule LHS must be atom.");
  
  rule = new Rule(t.name,t.children.length,encl.enclosure,t);
  rule.body = getTermArrayFromBinaryTerm(term.children[1],isConsPair);
  return rule;
 }
 else if (isAtom(term))
 {
  rule = new Rule(term.name,term.children.length,encl.enclosure,encl.term);
  return rule;
 }
 else
  throw Error("Rule LHS must be atom.");
}

function newFunctionRule(term,fn)
{var encl = newTermEnclosure(term);
 var rule;
  
 if (!isAtom(term))
  throw Error("Rule LHS must be atom.");
 
 rule = new Rule(term.name,term.children.length,encl.enclosure,encl.term);
 rule.body = null;
 rule.fn = fn;

 return rule;
}

function newTraversalRule(term,try_fn,retry_fn)
{var encl = newTermEnclosure(term);
 var rule;
  
 if (!isAtom(term))
  throw Error("Rule LHS must be atom.");
 
 rule = new Rule(term.name,term.children.length,encl.enclosure,encl.term);
 rule.body = null;
 rule.try_fn = try_fn;
 rule.retry_fn = retry_fn;
 
 return rule;
}

function newRuleBodyArrayEnclosure(enclosure,rule)
{
 if (rule.body != null)
 {
  return new ArrayEnclosure(enclosure,rule.body);
 }
 else
 {var ae = new ArrayEnclosure(enclosure,null);
 
  ae.fn = rule.fn;
  ae.try_fn = rule.try_fn;
  ae.retry_fn = rule.retry_fn;
  
  return ae;
 } 
}

///////////////////////////////////
// * KB / RuleSet / Rule utility functions
///////////////////////////////////

// Add ruleset to kb.  This must occur before attempting to add the corresponding rules.
function addRuleSet(kb,ruleset)
{
 kb.rulesets[getRuleNameArity(ruleset)] = ruleset;
}

// Add rule to kb.  The corresponding RuleSet to rule must already exist in kb.
// If append is true, rule is appended at the end of the ruleset, otherwise
// it is prepended to the beginning. 
function addRule(kb,rule,append)
{var ruleset;

 if ((ruleset = kb.rulesets[getRuleNameArity(rule)]) == null)
  throw new Error("Must declare rule dynamic to add: "+getRuleNameArity(rule));
 
 if (append)
  ruleset.rules.push(rule);
 else
  ruleset.rules.unshift(rule);
}

function getRuleSet(kb,term)
{
 return kb.rulesets[getTermNameArity(term)];
}

function getRuleNameArity(rule)
{
 return (rule.name.toString()+"/"+rule.arity.toString());
}

// return the enclosure array for unifying rule.head with encl
// returns null if unification fails.
// binding is an array, updated with the unification bindings if succeeds.
function getUnifiedRuleEnclosure(rule,encl,binding)
{var head_encl = newBlankEnclosure(rule.enclosure.length,rule.head);

 if (jslog_unify(head_encl,encl,binding))
  return head_encl.enclosure;

 return null;
}

function setEvaluateFunctionForRuleSet(ruleset,eval_fn)
{
 ruleset.eval_fn = eval_fn;

 return ruleset;
}

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

///////////////////////////////////
// *_fn(goal) is a function called when attempting to prove goal.  
// Returns true if the goal succeeds, false if not.
///////////////////////////////////

// FIX: pass in the current KB in use (currently uses the globally defined jslog_kb).
function is_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var x;
 
 x = jslog_Evaluate(jslog_kb,rhs);
 
 if (!isNumber(x))
  throw new Error("Expected RHS to evaluate to a number in operator: is/2");
  
 return jslog_unify(lhs,newBlankEnclosure(0,x),goal.bindings);
}

function lt_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 
 if (isNumber(lhs.term) && isNumber(rhs.term))
  return lhs.term.name < rhs.term.name;
 else
  throw new Error("Number expected in operator: </2");
}

function lte_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 
 if (isNumber(lhs.term) && isNumber(rhs.term))
  return lhs.term.name <= rhs.term.name;
 else
  throw new Error("Number expected in operator: =</2");
}

function gt_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 
 if (isNumber(lhs.term) && isNumber(rhs.term))
  return lhs.term.name > rhs.term.name;
 else
  throw new Error("Number expected in operator: >/2");
}

function gte_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 
 if (isNumber(lhs.term) && isNumber(rhs.term))
  return lhs.term.name >= rhs.term.name;
 else
  throw new Error("Number expected in operator: >=/2"); 
}

function unify_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 
 return jslog_unify(lhs,rhs,goal.bindings); 
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

function writeln_fn(goal)
{
 write_fn(goal);
 nl_fn(goal);
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
