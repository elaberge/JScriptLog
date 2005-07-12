/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// * Type objects
///////////////////////////////////

var TYPE_PREDICATE = 1; 
var TYPE_VARIABLE = 2; // children[0] is the index into the Enclosure

// type is one of the TYPE_* values, 
// name is the name of the term (typically the predicate or function symbol),
// The default is a term with no children.
function Term(type, name)
{
 this.type = type;
 this.name = name;
 this.children = new Array();
 return this;
}


function newPredicate(name,terms)
{var term = new Term(TYPE_PREDICATE,name);

 term.children = terms;
 return term;
}

function newConstant(name)
{
 return new Term(TYPE_PREDICATE,name);
}

function newNumber(value)
{
 return new Term(TYPE_PREDICATE,parseFloat(value));
}

function newVariable(name)
{
 return new Term(TYPE_VARIABLE,name);
}

function newConsPair(lhs,rhs)
{var term = new Term(TYPE_PREDICATE,',');
 
 term.children[0] = lhs;
 term.children[1] = rhs;
 return term;
}

// terms should be a non-empty array of Terms
// returns undefined if terms is empty
// returns terms[0] if terms has only a single Term
function newConsPairsFromTerms(terms)
{var cp;

 if (terms.length < 2)
  return terms[0];

 cp = newConsPair(terms[terms.length-2],terms[terms.length-1]);
   
 for (i = terms.length - 3; i >= 0; i--)
  cp = newConsPair(terms[i],cp);
  
 return cp;
}

function newOrPair(lhs,rhs)
{var term = new Term(TYPE_PREDICATE,';');

 term.children[0] = lhs;
 term.children[1] = rhs;
 return term;
}

function newListPair(lhs,rhs)
{var term = new Term(TYPE_PREDICATE,'.');

 term.children[0] = lhs;
 term.children[1] = rhs;
 return term;
}

function newListNull()
{
 return new Term(TYPE_PREDICATE,'[]');
}

// Returns a single list term where each element in the list is the element in terms.
// terms should be an array of Terms
function newListFromTerms(terms)
{var cp = newListNull();

 if (terms.length == 0)
  return newListNull();

 for (i = terms.length - 1; i >= 0; i--)
  cp = newListPair(terms[i],cp);
  
 return cp;
}

function newRuleTerm(lhs,rhs)
{var term = new Term(TYPE_PREDICATE,':-');

 term.children[0] = lhs;
 term.children[1] = rhs;
 return term;
}

function newCommandOp(rhs)
{var term = new Term(TYPE_PREDICATE,':-');

 term.children[0] = rhs;
 return term;
}

///////////////////////////////////
// * Type test functions
///////////////////////////////////

function isPredicate(term)
{
 return (term.type == TYPE_PREDICATE);
}

function isConstant(term)
{
 return (term.type == TYPE_PREDICATE && term.children.length == 0);
}

function isNumber(term)
{
 return (term.type == TYPE_PREDICATE && 
			term.children.length == 0 && 
				term.name.constructor == Number);
}

function isVariable(term)
{
 return (term.type == TYPE_VARIABLE);
}

function isConsPair(term)
{
 return (term.type == TYPE_PREDICATE && term.name == ',' && term.children.length == 2);
}

function isOrPair(term)
{
 return (term.type == TYPE_PREDICATE && term.name == ';' && term.children.length == 2);
}

function isListPair(term)
{
 return (term.type == TYPE_PREDICATE && term.name == '.' && term.children.length == 2);
}

function isListNull(term)
{
 return (term.type == TYPE_PREDICATE && term.name == '[]' && term.children.length == 0);
}

function isRuleTerm(term)
{
 return (term.type == TYPE_PREDICATE && term.name == ':-' && term.children.length == 2);
}

function isCommandOp(term)
{
 return (term.type == TYPE_PREDICATE && term.name == ':-' && term.children.length == 1);
}


///////////////////////////////////
// * Type getter / setter functions
///////////////////////////////////

function getTermNameArity(term)
{
 return (term.name.toString()+"/"+term.children.length.toString());
}

// term should be Terms
// returns empty array if term is undefined
// returns array of terms, where each element is the head of a binary pair (or last tail).
// eval_fn(t) should be true if t is a binary pair (arity 2) of the appropriate type.
function getTermArrayFromBinaryTerm(term,eval_fn)
{var terms = new Array();

 if (term != undefined)
 {var t = term;

  while (eval_fn(t))
  {
   terms[terms.length] = t.children[0];
   t = t.children[1];
  }
  terms[terms.length] = t;
 }

 return terms;
}

