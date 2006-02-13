/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// * Goal Objects
///////////////////////////////////

var TYPE_ATOM_GOAL = 1; // KB predicates 
var TYPE_VARIABLE_GOAL = 2; // KB predicates, with a variable term 
var TYPE_FUNCTION_GOAL = 3; // single-shot external function, no retry
var TYPE_TRAVERSAL_GOAL = 4; // single-shot traversal function for try and retry


function Goal(type,encl,parent)
{
 this.type = type;
 this.encl = encl;
 this.parent = parent;
 this.bindings = null;
 
 //// Other Properties (document here):
 // this.kb : the KB used to try the goal
 // this.ruleset :
 // this.rule_index : 
 // this.fn : the goal function
 // this.try_fn : the try traversal function
 // this.retry_fn : the retry traversal function
 // this.undo_fn : the undo special bindings function
 // this.prover : a sub-prover
 // this.noretry : if true, the next retry must fail.
  
 return this;
}

// encl is the enclosure for goal to prove
// parent is the parent goal 
function newGoal(encl,parent,kb)
{
 if (isVariable(encl.term))
  return newVariableGoal(encl,parent);
  
 if (encl.term.fn != undefined)
  return newFunctionGoal(encl,parent,encl.term.fn);
  
 if (encl.term.try_fn != undefined || encl.term.retry_fn != undefined)
  return newTraversalGoal(encl,parent,encl.term.try_fn,encl.term.try_fn);
  
 return newAtomGoal(encl,parent,kb);
}

// isAtom(encl.term) must be true
function newAtomGoal(encl,parent,kb)
{var goal = new Goal(TYPE_ATOM_GOAL,encl,parent);

 goal.rule_index = 0;
 
 if (encl.term.ruleset != null)
  goal.ruleset = encl.term.ruleset;
 else
  goal.ruleset = getRuleSet(kb,encl.term);
  
 return goal;
}

// isAtom(encl.term) or isVariable(encl.term) must be true
function newAtomGoalFromRuleSet(encl,parent,ruleset,kb)
{var goal = new Goal(TYPE_ATOM_GOAL,encl,parent);

 goal.rule_index = 0;
 
 goal.ruleset = ruleset;
  
 return goal;
}

function newVariableGoal(encl,parent)
{var goal = new Goal(TYPE_VARIABLE_GOAL,encl,parent);

 goal.rule_index = 0;
 goal.ruleset = null;
 
 return goal;
}

function newFunctionGoal(encl,parent,fn)
{var goal = new Goal(TYPE_FUNCTION_GOAL,encl,parent);

 goal.fn = fn; // fn(goal) : returns true if succeeds, false otherwise.
 
 return goal;
}

function newTraversalGoal(encl,parent,try_fn,retry_fn)
{var goal = new Goal(TYPE_TRAVERSAL_GOAL,encl,parent);

 goal.try_fn = try_fn; // t_fn(goal,frontier,explored): true if succeeds, false otherwise.
 goal.retry_fn = retry_fn; // t_fn(goal,frontier,explored): true if succeeds, false otherwise.
 
 return goal;
}


///////////////////////////////////
// * Goal test functions
///////////////////////////////////

function isAtomGoal(goal)
{
 return (goal.type == TYPE_ATOM_GOAL);
}

function isVariableGoal(goal)
{
 return (goal.type == TYPE_VARIABLE_GOAL);
}

function isFunctionGoal(goal)
{
 return (goal.type == TYPE_FUNCTION_GOAL);
}

function isTraversalGoal(goal)
{
 return (goal.type == TYPE_TRAVERSAL_GOAL);
}

///////////////////////////////////
// * Goal prove functions
///////////////////////////////////


// tryGoal(goal,prover) returns true if succeeds, false otherwise
// goal must be placed on appropriate stack (frontier if fail or explored if true).
// goal.bindings must be empty, if fail, or no unification occured.
function tryGoal(goal,prover)
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
	 {// if deterministic, or last-try
	  if (goal.parent != null && // entails prover.explored.length >= 1
			(goal.ruleset.rules.length == 1 || 
			(goal.rule_index == goal.ruleset.rules.length - 1 && 
			 prover.explored[prover.explored.length - 1] == goal.parent)))
	  {
	   mergeGoalBindings(goal,goal.parent);
	   addBodyGoalsToFrontier(goal.parent,rule_body,prover.kb,prover.frontier);
	  }
	  else
	  {
	   prover.explored.push(goal);
       addBodyGoalsToFrontier(goal,rule_body,prover.kb,prover.frontier);
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
   break; 
  case TYPE_FUNCTION_GOAL:
	 if (goal.fn(goal))
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
   break;
  case TYPE_TRAVERSAL_GOAL:
	if (goal.try_fn != null)
	 return goal.try_fn(goal,prover);
    else
	{
	 prover.frontier.push(goal);
	 return false;
	} 
   break;
 }
}

// retryGoal(goal,prover) returns true if succeeds, false otherwise
// goal must be placed on appropriate stack (frontier if fail or explored if true).
// goal.bindings must be non-null on start, empty on fail.
function retryGoal(goal,prover)
{
 undoGoal(goal,true);

 switch (goal.type)
 {
  case TYPE_VARIABLE_GOAL:
  case TYPE_ATOM_GOAL:
     var rule_body = null;

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
	 {// if deterministic, or last-try
	  if (goal.parent != null && // entails prover.explored.length >= 1
			(goal.ruleset.rules.length == 1 || 
			(goal.rule_index == goal.ruleset.rules.length - 1 && 
			 prover.explored[prover.explored.length - 1] == goal.parent)))
	  {
	   mergeGoalBindings(goal,goal.parent);
	   addBodyGoalsToFrontier(goal.parent,rule_body,prover.kb,prover.frontier);
	  }
	  else
	  {
	   prover.explored.push(goal);
       addBodyGoalsToFrontier(goal,rule_body,goal.kb,prover.frontier);
	  }
	  return true;
	 }
	 else
	 {
	  prover.frontier.push(goal);
	  return false;
	 }
   break; 
  case TYPE_FUNCTION_GOAL:
	prover.frontier.push(goal);
    return false;
   break;
  case TYPE_TRAVERSAL_GOAL:
	if (goal.retry_fn != null)
	 return goal.retry_fn(goal,prover);
    else
	 prover.frontier.push(goal);

    return false;
   break;
 }
}

// undoGoal(goal,retry) undoes the binding for goal.
// retry is true if a retry will follow, false if not.
function undoGoal(goal,retry)
{
 if (goal.bindings != null)
  removeBindings(goal.bindings);

 if (goal.undo_fn != null)
  goal.undo_fn(goal,retry);
}

// removes the contiguous top-most goals from frontier which are children of the parent goal
function removeChildGoalsFromFrontier(parent,frontier)
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
function nextUnifiedRuleBodyForGoal(goal)
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
function addBodyGoalsToFrontier(parent,body,kb,frontier)
{var encl;
 var goal;
 var i;

 for (i = body.terms.length - 1; i >= 0; i--)
 {
  encl = newSubtermEnclosure(body.enclosure,body.terms[i]);
  goal = newGoal(encl,parent,kb);
  frontier.push(goal);
 }
}

// merge bindings from sgoal to dgoal
// dgoal should be a predecessor of sgoal
function mergeGoalBindings(sgoal,dgoal)
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

