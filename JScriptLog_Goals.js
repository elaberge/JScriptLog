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

var TYPE_PREDICATE_GOAL = 1; // KB predicates 
var TYPE_VARIABLE_GOAL = 2; // KB predicates, with a variable term 
var TYPE_FUNCTION_GOAL = 3; // single-shot external function, no retry
var TYPE_TRAVERSAL_GOAL = 4; // single-shot traversal function for try and retry


function Goal(type,encl,parent)
{
 this.type = type;
 this.encl = encl;
 this.parent = parent;
 this.bindings = null;
 
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
  
 return newPredicateGoal(encl,parent,kb);
}

// isPredicate(encl.term) must be true
function newPredicateGoal(encl,parent,kb)
{var goal = new Goal(TYPE_PREDICATE_GOAL,encl,parent);

 goal.rule_index = 0;
 
 if (encl.term.ruleset != null)
  goal.ruleset = encl.term.ruleset;
 else
  goal.ruleset = getRuleSet(kb,encl.term);
  
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

function isPredicateGoal(goal)
{
 return (goal.type == TYPE_PREDICATE_GOAL);
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


// tryGoal(goal,frontier,explored) returns true if succeeds, false otherwise
// goal must be placed on appropriate stack (frontier if fail or explored if true).
// goal.bindings must be null if fail, or no unification occured.
function tryGoal(goal,kb,frontier,explored)
{
 switch (goal.type)
 {
  case TYPE_VARIABLE_GOAL:
     var encl;
     
	 if ((encl = getBoundEnclosure(goal.encl)) == null)
	 {
	  frontier.push(goal); 
      throw new Error("Cannot call variable.");
     }

     if (encl.term.ruleset != null)
      goal.ruleset = encl.term.ruleset;
     else
	  goal.ruleset = getRuleSet(kb,encl.term);
  case TYPE_PREDICATE_GOAL:
     var rule_body;

     if (goal.ruleset == null)
	 {
	  frontier.push(goal);
      throw new Error("Unknown predicate: "+getTermNameArity(getBoundEnclosure(goal.encl).term)); 
     }

	 goal.rule_index = 0;
	 rule_body = nextUnifiedRuleBodyForGoal(goal);
	 
	 if (rule_body == null)
	 {
	  frontier.push(goal);
	  return false;
	 }
	 else if (rule_body.terms != null)
	 {
	  explored.push(goal);
      addBodyGoalsToFrontier(goal,rule_body,kb,frontier);
	  return true;
	 }
	 else // handle FUNCTION and TRAVERSAL // FIX: Remove to optimize pred path (move to var)
	 {
	  if (rule_body.fn != null)
	  {
	   if (rule_body.fn(goal))
       {
	   	explored.push(goal);
        return true;
       }
	   else
	   {
	    frontier.push(goal);
		return false;
	   }
	  }
	  else if (rule_body.try_fn != null)
	  {
	   return rule_body.try_fn(goal,frontier,explored);
	  }
	  else
	  {
	   frontier.push(goal);
	   return false;
	  }
	 }
   break; 
  case TYPE_FUNCTION_GOAL:
	 if (goal.fn(goal))
     {
	  explored.push(goal);
      return true;
     }
	 else
	 {
	  frontier.push(goal);
	  return false;
	 }
   break;
  case TYPE_TRAVERSAL_GOAL:
	if (goal.try_fn != null)
	 return goal.try_fn(goal,frontier,explored);
    else
	{
	 frontier.push(goal);
	 return false;
	} 
   break;
 }
}

// retryGoal(goal,frontier,explored) returns true if succeeds, false otherwise
// goal must be placed on appropriate stack (frontier if fail or explored if true).
// goal.bindings must be null if fail, or no unification occured.
function retryGoal(goal,kb,frontier,explored)
{
 undoGoalBindings(goal);

 switch (goal.type)
 {
  case TYPE_VARIABLE_GOAL:
  case TYPE_PREDICATE_GOAL:
     var rule_body;

	 removeChildGoalsFromFrontier(goal,frontier);

	 // handle FUNCTION and TRAVERSAL // FIX: Remove to optimize pred path (move to var)
     rule_body = newRuleBodyArrayEnclosure(goal.encl.enclosure,goal.ruleset.rules[goal.rule_index]);
	 if (rule_body.retry_fn != null)
	  return rule_body.retry_fn(goal,frontier,explored);
	 
	 goal.rule_index++;
	 rule_body = nextUnifiedRuleBodyForGoal(goal);
	 
	 if (rule_body == null)
	 {
	  frontier.push(goal);
	  return false;
	 }
	 else if (rule_body.terms != null)
	 {
	  explored.push(goal);
      addBodyGoalsToFrontier(goal,rule_body,kb,frontier);
	  return true;
	 }
	 else // FIX: Remove (ensure rule_body.terms cannot be null)
	 {
	  frontier.push(goal);
	  return false;
	 }
   break; 
  case TYPE_FUNCTION_GOAL:
	frontier.push(goal);
    return false;
   break;
  case TYPE_TRAVERSAL_GOAL:
	if (goal.retry_fn != null)
	 return goal.retry_fn(goal,frontier,explored);
    else
	 frontier.push(goal);

    return false;
   break;
 }
}

function undoGoalBindings(goal)
{
 if (goal.bindings != null)
  removeBindings(goal.bindings);

 goal.bindings = null;
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

// returns an ArrayEnclosure for the next matching Rule, startng from goal.rule_index (inclusive).
// goal.binding is mutated to an array (empty if fail).
// returns null if no rules match.
function nextUnifiedRuleBodyForGoal(goal)
{var rule;
 var enclosure;

 goal.bindings = new Array();
 
 for (;goal.rule_index < goal.ruleset.rules.length;)
 {
  rule = goal.ruleset.rules[goal.rule_index];

  if ((enclosure = getUnifiedRuleEnclosure(rule,goal.encl,goal.bindings)) != undefined)
   return newRuleBodyArrayEnclosure(enclosure,rule);

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
