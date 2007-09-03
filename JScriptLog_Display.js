/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_toString_* functions for Display
///////////////////////////////////

// FIX: Display all unary and binary operators as operators (needs table of operators from KB).
// FIX: Display variables uniquely (not just by their local names).

// encl is either a Term or Enclosure (preferrable)
// kb is the KB used for operator display info.  If kb == null, then the default
// display procedure is used (with the exception of lists and argument separators,
// operators are displayed as predicates).
function jslog_toString(encl,kb)
{var tostr_terms = new Array();
 var tostr;
 var str = "";
 var prev_token = null; 
 
 tostr_terms.push(encl);
 
 while ((tostr = tostr_terms.pop()) != undefined)
 {
  var ruleset = null;

  if (tostr.constructor == String)
  {
   if (prev_token != null && jslog_Display_needsSpace(prev_token,tostr))
    str += " ";
	
   str += tostr;
   prev_token = tostr;
   continue;
  }
  if (tostr.constructor == Term)
  {
   tostr_terms.push(newBlankEnclosure(0,tostr));
   continue;
  }

  // from here on: assume tostr is an enclosure
  if (isVariable(tostr.term)) // display Variable
  {
   jslog_toString_Variable(tostr,tostr_terms);
  }
  else if (isObjectReference(tostr.term))  // display ObjectReference
  {
   tostr_terms.push(tostr.term.name.toString());
  }
  else if (isListPair(tostr.term))  // display ListPairs
  {
   tostr_terms.push("]");
   jslog_toString_List(tostr,tostr_terms,kb);
   tostr_terms.push("[");
  } 
  else if (tostr.term.name == '{}' && tostr.term.children.length == 1)  // display {} sequences
  {
   tostr_terms.push("}");
   tostr_terms.push(newSubtermEnclosure(tostr.enclosure,tostr.term.children[0]));
   tostr_terms.push("{");
  } 
  else if (tostr.term.name == '()' && tostr.term.children.length == 1)  // display () sequences
  {
   tostr_terms.push(")");
   tostr_terms.push(newSubtermEnclosure(tostr.enclosure,tostr.term.children[0]));
   tostr_terms.push("(");
  }
  else if (kb != null && isAtom(tostr.term) && ((ruleset = getRuleSet(kb,tostr.term)) != null) &&
			isOperatorRuleSet(ruleset))
  {   
   switch (getOperatorType(ruleset))
   {
	case OP_TYPE_XFX:
	case OP_TYPE_XFY:
	case OP_TYPE_YFX:
	  {var needs_paren0 = jslog_Display_needsParentheses(tostr,ruleset,0,kb);
	   var needs_paren1 = jslog_Display_needsParentheses(tostr,ruleset,1,kb);
	   
	   if (needs_paren1)
	    tostr_terms.push(")");
       tostr_terms.push(newSubtermEnclosure(tostr.enclosure,tostr.term.children[1]));
	   if (needs_paren1)
	    tostr_terms.push("(");
       tostr_terms.push(jslog_Display_AtomName(tostr.term.name.toString(),true));
	   if (needs_paren0)
	    tostr_terms.push(")");
       tostr_terms.push(newSubtermEnclosure(tostr.enclosure,tostr.term.children[0]));
	   if (needs_paren0)
	    tostr_terms.push("(");
	  } 
	 break;
	  
	case OP_TYPE_FX:
	case OP_TYPE_FY:
	  {var needs_paren0 = jslog_Display_needsParentheses(tostr,ruleset,0,kb);
	   
	   if (needs_paren0)
	    tostr_terms.push(")");
       tostr_terms.push(newSubtermEnclosure(tostr.enclosure,tostr.term.children[0]));
	   if (needs_paren0)
	    tostr_terms.push("(");
	   tostr_terms.push(jslog_Display_AtomName(tostr.term.name.toString(),true));
	  }
	 break;
	  
    case OP_TYPE_XF:
	case OP_TYPE_YF:
	  {var needs_paren0 = jslog_Display_needsParentheses(tostr,ruleset,0,kb);

       tostr_terms.push(jslog_Display_AtomName(tostr.term.name.toString(),true));
	   if (needs_paren0)
	    tostr_terms.push(")");
       tostr_terms.push(newSubtermEnclosure(tostr.enclosure,tostr.term.children[0]));
	   if (needs_paren0)
	    tostr_terms.push("(");
	  }
	 break;
   }
  }
  else if (isConsPair(tostr.term))  // display ConsPairs if it wasn't previously
  {
   tostr_terms.push(")");
   tostr_terms.push(newSubtermEnclosure(tostr.enclosure,tostr.term.children[1]));	 
   tostr_terms.push("),(");
   tostr_terms.push(newSubtermEnclosure(tostr.enclosure,tostr.term.children[0]));
   tostr_terms.push("(");
  }
  else if (isNumber(tostr.term))  // display Number
  {
   tostr_terms.push(tostr.term.name.toString());
  }
  else if (tostr.term.children.length == 0)  // display Constant, or Atom/0
  {
   tostr_terms.push(jslog_Display_AtomName(tostr.term.name.toString(),false));
  }
  else  // display Atom/N
  {
   tostr_terms.push(")");
   
   // push children in reverse order
   for (i = tostr.term.children.length - 1; i >= 0; i--)
   {
    var tostr_encl = newSubtermEnclosure(tostr.enclosure,tostr.term.children[i]);
    var is_cons_pair = isConsPair(tostr_encl.term);
	
	if (is_cons_pair)
     tostr_terms.push(")"); 
	 
    tostr_terms.push(tostr_encl);

	if (is_cons_pair)
     tostr_terms.push("("); 

    if (i != 0)
     tostr_terms.push(","); 
   }
   
   tostr_terms.push("(");
   tostr_terms.push(""); // force no space
   tostr_terms.push(jslog_Display_AtomName(tostr.term.name.toString(),false));
  }
 };
  
 return str;
}

// determines if a space is needed between two String tokens.
// token is the string which will display next, prev_token was display previously.
// returns true if a space was needed, false otherwise.
function jslog_Display_needsSpace(prev_token,token)
{var needs_space = true;

 if (prev_token == null)
  return false;
  
 // empty string forces tokens together
 if (prev_token == "" || token == "")
  return false;
  
 // make exceptions
 if (prev_token == ":-" || token == ":-")
  return true;

 var pt_allword = prev_token.search(/\W/) < 0;
 var pt_allnonword = prev_token.search(/\w/) < 0;
 var pt_isquoted = prev_token.length >= 2 && prev_token[0] == "'" && prev_token[prev_token.length-1] == "'";
 var t_allword = token.search(/\W/) < 0;
 var t_allnonword = token.search(/\w/) < 0;
 var t_isquoted = token.length >= 2 && token[0] == "'" && token[token.length-1] == "'";

 // need a space if pre_token and token are in the same display class
 // (display classes: i] all word chars, ii] all non-word chars) or if either
 // token is in the mixed class iii] (i.e., neither i] nor ii] above).
 needs_space = (pt_allword && t_allword) || (pt_allnonword && t_allnonword) ||
				(!pt_allword && !pt_allnonword) || (!t_allword && !t_allnonword);

 // keep symbols close to mixed tokens if it is quoted.
 if ((pt_isquoted && t_allnonword) || (t_isquoted && pt_allnonword))
  return false;

 // keep single character symbols together if they are in the small set of 'reserved' symbols
 if (prev_token.length == 1 && token.length == 1 && 
		prev_token.search(/[\[\]\{\}\(\)\,\;\!]/) == 0 && token.search(/[\[\]\{\}\(\)\,\.\;\!]/) == 0)
  return false;

 // keep null list token and 'reserved' single character symbols together
 if (prev_token.length == 1 && token == "[]" && prev_token.search(/[\[\]\{\}\(\)\,\;\!]/) == 0)
  return false;

 // keep null list token and 'reserved' single character symbols together
 if (token.length == 1 && prev_token == "[]" && token.search(/[\[\]\{\}\(\)\,\.\;\!]/) == 0)
  return false;
  
 // keep \+ and -> near 'reserved' single character symbols
 if ((token == "\\+" || token == "->") && prev_token.length == 1 && prev_token.search(/[\,\;]/) == 0)
  return false;
  
 return needs_space; 
}

// determines if the child (at child_idx number) of encl.term needs to have a parenthesis to
// distinguish it from parent (assumes using infix). if kb == null, returns true 
// (assume everything needs parentheses -- if displayed in predicate format, 
// i.e. not infix, then don't call this).
// ruleset = getRuleSet(kb,encl.term) && ruleset != null && isOperatorRuleSet(ruleset)
// child_idx is the index of the child term to evaluate.  encl.term must represent an
// operator and encl.term.children[child_idx] must be a valid.
function jslog_Display_needsParentheses(encl,ruleset,child_idx,kb)
{
 if (kb == null)
  return true;

 var op_type = getOperatorType(ruleset);
 var op_prec = getOperatorPrecedence(ruleset);

 var child = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[child_idx]));

 if (!isAtom(child.term))
  return false;

 var child_ruleset = getRuleSet(kb,child.term);
 
 if (child_ruleset == null || !isOperatorRuleSet(child_ruleset))
  return false;

 var child_op_prec = getOperatorPrecedence(child_ruleset);

 if (child_op_prec < op_prec)
  return false;

 if (child_op_prec > op_prec)
  return true;

 // child_op_prec == op_prec, so handle via specific cases
 
 switch (op_type)
 {
  case OP_TYPE_XFY:
    if (child_idx == 1)
	 return false;
   break;
  case OP_TYPE_YFX:
    if (child_idx == 0)
	 return false;
   break;
  case OP_TYPE_FY:
  case OP_TYPE_YF:
    return false;
 }
 
 return true;
}

// given an atom_name, returns a displayable version of it (i.e., quotes it if it contains
// symbols which could confuse the parser).
// is_op is true if atom_name represents an operator. 
function jslog_Display_AtomName(atom_name,is_op)
{
 // if operators are all symbols, do not quote
 if (is_op && atom_name.search(/\w/) < 0)
  return atom_name;
  
 // if name is alphanumeric(_), do not quote 
 if (atom_name.search(/\W/) < 0)
  return atom_name;
 
 // display some known atoms without quotes
 if (atom_name == "[]" || atom_name == "!" || atom_name == "->" )
  return atom_name;
  
 return "'"+atom_name+"'";
}

// isVariable(encl.term)
function jslog_toString_Variable(encl,stack)
{var tostr = getBoundEnclosure(encl);

 if (tostr == null)
  stack.push(encl.term.name.toString()); // FIX: Need global (for original toString) naming scheme
 else
  stack.push(tostr);
}

// isListPair(encl.term) must be true.
// push terms / strings to display onto stack.
function jslog_toString_List(encl,stack,kb)
{var list = new Array();
 
 list.push(getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0])));
 encl = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));

 while (isListPair(encl.term))
 {
  list.push(getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0])));
  encl = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 }

 if (!isListNull(encl.term))
 {
  stack.push(encl);
  stack.push("|");  
 }
   
 if ((encl = list.pop()) != undefined)
 {var needs_paren;

  needs_paren = isConsPair(encl.term) || isOrPair(encl.term); //FIX: Change to test operator precedence
  
  if (needs_paren)
   stack.push(")");

  stack.push(encl);

  if (needs_paren)
   stack.push("(");

  while ((encl = list.pop()) != undefined)
  {
   needs_paren = isConsPair(encl.term) || isOrPair(encl.term); //FIX: Change to test operator precedence
   
   stack.push(",");
   
   if (needs_paren)
	stack.push(")");

   stack.push(encl);

   if (needs_paren)
	stack.push("(");
  }
 }
} 

function jslog_GoalStack_toString(gstack)
{var str = "";
 var i;
 
 for(i=gstack.length - 1; i >= 0; --i)
  str += jslog_Goal_toString(gstack[i],true) + "\n";

 return str;
}

function jslog_Goal_toString(goal,show_parent)
{var str;

 str = "goal term:" + jslog_toString(goal.encl);
 if (show_parent && goal.parent != undefined)
 {
  if (goal.parent_is_ancestor)
   str += " ancestor:";
  else
   str += " parent:";
   
  str += jslog_Goal_toString(goal.parent,false);
 }

 return str;
}
