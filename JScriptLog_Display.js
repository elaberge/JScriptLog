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
function jslog_toString(encl)
{var tostr_terms = new Array(1);
 var tostr;
 var str = "";

 tostr_terms[0] = encl;
 
 while ((tostr = tostr_terms.pop()) != undefined)
 {
  if (tostr.constructor == String)
  {
   str += tostr;
   continue;
  }
  if (tostr.constructor == Term)
  {
   tostr_terms.push(newBlankEnclosure(0,tostr));
   continue;
  }

  if (isVariable(tostr.term)) // display Variable
  {
   jslog_toString_Variable(tostr_terms,tostr);
  }
  else if (isConsPair(tostr.term))  // display ConsPairs
  {
   jslog_toString_BinaryOp(tostr_terms,tostr,isConsPair,",",false);
  } 
  else if (isOrPair(tostr.term))  // display OrPairs
  {
   jslog_toString_BinaryOp(tostr_terms,tostr,isOrPair,";",false);
  } 
  else if (isListPair(tostr.term))  // display ListPairs
  {
   str += "[";
   tostr_terms.push("]");

   jslog_toString_BinaryOp(tostr_terms,tostr,isListPair,",",true);
  } 
  else if (tostr.term.name == '{}' && tostr.term.children.length == 1)  // display {} sequences
  {
   str += "{";
   tostr_terms.push("}");
   tostr_terms.push(newSubTermEnclosure(tostr.enclosure,tostr.term.children[0]));
  } 
  else if (tostr.term.name == '()' && tostr.term.children.length == 1)  // display () sequences
  {
   str += "(";
   tostr_terms.push(")");
   tostr_terms.push(newSubTermEnclosure(tostr.enclosure,tostr.term.children[0]));
  } 
  else if (tostr.term.children.length == 0)  // display Constant, Number, or Atom/0
   str += tostr.term.name.toString();
  else  // display Atom/N
  {var args = newConsPairsFromTerms(tostr.term.children);
  
   str += tostr.term.name.toString() + "(";
   tostr_terms.push(")");
   
   tostr_terms.push(newSubtermEnclosure(tostr.enclosure,args));
  }
 };
  
 return str;
}

// isVariable(encl.term)
function jslog_toString_Variable(stack,encl)
{var tostr = getBoundEnclosure(encl);

 if (tostr == null)
  stack.push(encl.term.name.toString()); // FIX: Need global (for original toString) naming scheme
 else
  stack.push(tostr);
}

// eval_fn(encl.term) must be true.
// eval_fn is a type evaluation function taking a single term.
// sep is the separator string to use.
// If islist is true, the tail end of the sequence is treated like a list 
// (e.g., '|' if not null terminated).
function jslog_toString_BinaryOp(stack,encl,eval_fn,sep,islist)
{var list = new Array(1);
   
 list.push(getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0])));
 encl = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));

 while (eval_fn(encl.term))
 {
  list.push(getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0])));
  encl = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 }

 if (islist)
 {
  if (!isListNull(encl.term))
  {
   stack.push(encl);
   stack.push("|");
  }
 } 
 else
  list.push(encl);

 if ((encl = list.pop()) != undefined)
 {
  stack.push(encl);

  while ((encl = list.pop()) != undefined)
  {
   stack.push(sep);
   if (isConsPair(encl.term) || isOrPair(encl.term)) //FIX: Change to test operator precedence
   {
	stack.push(")");
    stack.push(encl);
	stack.push("(");
   }
   else
    stack.push(encl);
  }
 }
} 
