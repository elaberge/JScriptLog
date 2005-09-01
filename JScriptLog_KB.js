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

// FIX: RuleSets should denote operator information (if it represents an operator).

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
 // !/0 : commit function
 {
  ruleset = new RuleSet('!',0,false);

  ruleset.rules.push(newTraversalRule(newConstant('!'),true_try_fn,cut_retry_fn));
 
  addRuleSet(this,ruleset);
 }
 // findall(T,G,L) :- internal:copy_term([],M), internal:findall(T,G,M), M =.. [_|L].
 {
  ruleset = new RuleSet('findall',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('findall',[newVariable('T'),newVariable('G'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('internal:copy_term',[newListNull(),newVariable('M')]),
			newAtom('internal:findall',[newVariable('T'),newVariable('G'),newVariable('M')]),
			newAtom('=..',[newVariable('M'),newListPair(newVariable('_'),newVariable('L'))])]))));
 
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
 // \=(X,Y) :- \+(=(X,Y)).
 {
  ruleset = new RuleSet('\\=',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('\\=',[newVariable('X'),newVariable('Y')]),
		newAtom('\\+',[newAtom('=',[newVariable('X'),newVariable('Y')])]))));
 
  addRuleSet(this,ruleset);
 }
 // ==/2 : identical function
 {
  ruleset = new RuleSet('==',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('==',[newVariable('L'),newVariable('R')]),identical_fn));
 
  addRuleSet(this,ruleset);  
 }
 // \==(X,Y) :- \+(==(X,Y)).
 {
  ruleset = new RuleSet('\\==',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('\\==',[newVariable('X'),newVariable('Y')]),
		newAtom('\\+',[newAtom('==',[newVariable('X'),newVariable('Y')])]))));
 
  addRuleSet(this,ruleset);
 }
 // =../2 : atom to list
 {
  ruleset = new RuleSet('=..',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=..',[newVariable('L'),newVariable('R')]),atom_to_list_fn));
 
  addRuleSet(this,ruleset);  
 }
 // copy_term/2 : copy term function
 {
  ruleset = new RuleSet('copy_term',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('copy_term',[newVariable('L'),newVariable('R')]),copy_term_fn));
 
  addRuleSet(this,ruleset);  
 } 
 // asserta/1
 {
  ruleset = new RuleSet('asserta',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('asserta',[newVariable('L')]),asserta_fn));
 
  addRuleSet(this,ruleset);  
 }
 // assertz/1
 {
  ruleset = new RuleSet('assertz',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('assertz',[newVariable('L')]),assertz_fn));
 
  addRuleSet(this,ruleset);  
 }
 // FIX: build retract/1 from internal predicates which support both abolish/1 and clause/2.
 // retract/1
 {
  ruleset = new RuleSet('retract',1,false);

  ruleset.rules.push(newTraversalRule(newAtom('retract',[newVariable('A')]),
		retract_try_fn,retract_retry_fn));
 
  addRuleSet(this,ruleset);
 }
 // write/1 : ouput function
 {
  ruleset = new RuleSet('write',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('write',[newVariable('O')]),write_fn));
 
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

 // internal:atom_append!/2 a atom mutate function that adds an argument
 // internal:atom_append!(A,E).  Adds E as an extra argument of A.
 {
  ruleset = new RuleSet('internal:atom_append!',2,false);
  
  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:atom_append!',[newVariable('A'),newVariable('E')]),internal_atom_append_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:copy_term/2 copy term so that term is copied, not just the enclosures
 // internal:copy_term(T,C).  C is a copy of T.
 {
  ruleset = new RuleSet('internal:copy_term',2,false);
  
  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:copy_term',[newVariable('T'),newVariable('C')]),internal_copy_term_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:findall(T,G,M) :- call(G), copy_term(T,U), internal:atom_append!(M,U), fail.
 // internal:findall(_,_,_) :- !.
 {
  ruleset = new RuleSet('internal:findall',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:findall',[newVariable('T'),newVariable('G'),newVariable('M')]),
		newConsPairsFromTerms([
			newAtom('call',[newVariable('G')]),
			newAtom('copy_term',[newVariable('T'),newVariable('U')]),
			newAtom('internal:atom_append!',[newVariable('M'),newVariable('U')]),
			newConstant('fail')]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:findall',[newVariable('_'),newVariable('_'),newVariable('_')]),
			newConstant('!'))));
 
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

// Remove rule at index from ruleset.  
function removeRuleFromRuleSet(ruleset,index)
{
 if (!isDynamicRuleSet(ruleset))
  throw new Error("Must declare rule dynamic to remove: "+getRuleNameArity(ruleset));
 
 ruleset.rules.splice(index,1);
}

// Get ruleset used to prove term.
function getRuleSet(kb,term)
{
 return kb.rulesets[getTermNameArity(term)];
}

function getRuleNameArityFromTerm(term)
{
 if (isRuleTerm(term))
  return getTermNameArity(term.children[0]);
 else
  return getTermNameArity(term);
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

function isDynamicRuleSet(ruleset)
{
 return (ruleset == undefined || ruleset.dynamic);
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

function identical_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 
 return jslog_identical(lhs,rhs); 
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
