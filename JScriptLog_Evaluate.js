/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_Evaluate_* functions for expression Evaluation
///////////////////////////////////

// encl is an Enclosure of an expression
// kb is the KB
// Returns a Term which encl evaluates to.
function jslog_Evaluate(kb,encl)
{var toeval_ops = new Array(1);
 var value_terms = new Array();
 var toeval;

 toeval_ops[0] = encl;
 
 while ((toeval = toeval_ops.pop()) != undefined)
 {
  if (toeval.constructor == Term)
  {
   toeval_ops.push(newBlankEnclosure(0,toeval));
   continue;
  }

  if (toeval.constructor == Enclosure)
  {
   if (isVariable(toeval.term)) // eval Variable
   {
    toeval = getBoundEnclosure(toeval);

    if (toeval == null)
     throw new Error("Unbound variable in evaluated expression.");
   }
  
   var eval_fn = jslog_Evaluate_Function(kb,toeval.term);
  
   if (eval_fn != undefined)
   {
    toeval_ops.push(eval_fn);

    for (i = 0 ; i < toeval.term.children.length; i++)
     toeval_ops.push(newSubtermEnclosure(toeval.enclosure,toeval.term.children[i]));
   }
   else
    value_terms.push(toeval.term);   
  }
  else  // Evaluate Function
  {
   toeval(value_terms);
  }
 };

 if (value_terms.length != 1)
  throw new Error("Expression did not evaluate to single value.");
  
 return value_terms.pop();
}

function jslog_Evaluate_Function(kb,term)
{
 if (term.eval_fn != undefined)
  return term.eval_fn;

 if (isAtom(term))
 {var ruleset = getRuleSet(kb,term);

  if (ruleset != null)
   return ruleset.eval_fn;
 }

 return undefined;	
}
