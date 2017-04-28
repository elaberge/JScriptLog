/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.

    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

import {
  Hashtable,
  hashGet, hashPut
} from "./hashtable";

///////////////////////////////////
// * Type objects
///////////////////////////////////

var TYPE_ATOM = 1;
var TYPE_NUMBER = 2;
export var TYPE_VARIABLE = 3; // children[0] is the index into the Enclosure
var TYPE_OBJECT = 4; // name is an object reference

// type is one of the TYPE_* values,
// name is the name of the term (typically the predicate or function symbol),
// The default is a term with no children.
export class Term {
  children: any[] = [];

  //// Other Properties (document here):
  // this.ruleset : the ruleset ruleset associated with the term
  // this.goal_type : the TYPE_*_GOAL associated with the term

  constructor(public type: any, public name: any) {
  }
}

export function newAtom(name: any, terms: any)
{var term = new Term(TYPE_ATOM,name);

 term.children = terms;
 return term;
}

export function newConstant(name: any)
{
 return new Term(TYPE_ATOM,name);
}

export function newNumber(value: any)
{
 return new Term(TYPE_NUMBER,parseFloat(value));
}

export function newVariable(name: any)
{
 return new Term(TYPE_VARIABLE,name);
}

export function newObjectReference(obj: any)
{
 return new Term(TYPE_OBJECT,obj);
}

export function newConsPair(lhs: any, rhs: any)
{var term = new Term(TYPE_ATOM,',');

 term.children[0] = lhs;
 term.children[1] = rhs;
 return term;
}

// terms should be a non-empty array of Terms
// returns undefined if terms is empty
// returns terms[0] if terms has only a single Term
export function newConsPairsFromTerms(terms: any)
{var cp;

 if (terms.length < 2)
  return terms[0];

 cp = newConsPair(terms[terms.length-2],terms[terms.length-1]);

 for (var i = terms.length - 3; i >= 0; i--)
  cp = newConsPair(terms[i],cp);

 return cp;
}

export function newOrPair(lhs: any, rhs: any)
{var term = new Term(TYPE_ATOM,';');

 term.children[0] = lhs;
 term.children[1] = rhs;
 return term;
}

// terms should be a non-empty array of Terms
// returns undefined if terms is empty
// returns terms[0] if terms has only a single Term
export function newOrPairsFromTerms(terms: any)
{var cp;

 if (terms.length < 2)
  return terms[0];

 cp = newOrPair(terms[terms.length-2],terms[terms.length-1]);

 for (var i = terms.length - 3; i >= 0; i--)
  cp = newOrPair(terms[i],cp);

 return cp;
}

export function newListPair(lhs: any, rhs: any)
{var term = new Term(TYPE_ATOM,'.');

 term.children[0] = lhs;
 term.children[1] = rhs;
 return term;
}

export function newListNull()
{
 return new Term(TYPE_ATOM,'[]');
}

// Returns a single list term where each element in the list is the element in terms.
// terms should be an array of Terms
export function newListFromTerms(terms: any)
{var cp = newListNull();

 for (var i = terms.length - 1; i >= 0; i--)
  cp = newListPair(terms[i],cp);

 return cp;
}

export function newRuleTerm(lhs: any, rhs: any)
{var term = new Term(TYPE_ATOM,':-');

 term.children[0] = lhs;
 term.children[1] = rhs;
 return term;
}

function newCommandOp(rhs: any)
{var term = new Term(TYPE_ATOM,':-');

 term.children[0] = rhs;
 return term;
}

// Given a term, returns a duplicate of that term.
// The term must already have had an enclosure created via newTermEnclosure to bind
// variable children[0] to the enclosure array -- duped vars reference the same enclosure entry.
// The duplicate term has the same type and name, the same number of children,
// and duplicated children -- performs a deep copy.
// Variables in the duplicate term are represented via a single unnamed variable instance
// (i.e., variables lose their names, and the number of variables may be reduced).
// The variables parameter must be an array, with each element either undefined or a Variable
// instance.  On completion, variables contains the duplicated variables at the same index they
// point to in the enclosure -- new Variable instances are created only if the variables array
// is undefined at the index position a variable references.
export function newDuplicateTerm(term: any, variables: any[] = [])
{var terms_hash = new Hashtable();
 var terms_todo = new Array();
 var terms = new Array();
 var t;
 var t_copy;

 terms.push(term);

 // find and copy all terms
 while ((t = terms.pop()) != undefined)
 {
  if (isVariable(t))
  {
   if (variables[t.children[0]] == undefined)
   {
    t_copy = newVariable('_');

    t_copy.children[0] = t.children[0];

    variables[t.children[0]] = t_copy;
	hashPut(terms_hash,t,t_copy);
   }
   else
    hashPut(terms_hash,t,variables[t.children[0]]);
  }
  else if (hashGet(terms_hash,t) == undefined)
  {
   t_copy = new Term(t.type,t.name);
   t_copy.children = new Array(t.children.length);
   terms_todo.push(t);

   hashPut(terms_hash,t,t_copy);

   for (var i=0; i < t.children.length; i++)
	terms.push(t.children[i]);
  }
 }

 // connect duplicate terms like original ones
 while ((t = terms_todo.pop()) != undefined)
 {
  t_copy = hashGet(terms_hash,t);

  for (var i=0; i < t.children.length; i++)
   t_copy.children[i] = hashGet(terms_hash,t.children[i]);
 }

 return hashGet(terms_hash,term);
}

///////////////////////////////////
// * Type test functions
///////////////////////////////////

export function isAtom(term: any)
{
 return (term.type == TYPE_ATOM);
}

export function isConstant(term: any)
{
 return (term.type == TYPE_ATOM && term.children.length == 0);
}

export function isNumber(term: any)
{
 return (term.type == TYPE_NUMBER);
}

export function isInteger(term: any)
{
 return (term.type == TYPE_NUMBER && (Math.round(term.name) == term.name));
}

export function isVariable(term: any)
{
 return (term.type == TYPE_VARIABLE);
}

export function isObjectReference(term: any)
{
 return (term.type == TYPE_OBJECT);
}

export function isConsPair(term: any)
{
 return (term.type == TYPE_ATOM && term.name == ',' && term.children.length == 2);
}

export function isOrPair(term: any)
{
 return (term.type == TYPE_ATOM && term.name == ';' && term.children.length == 2);
}

export function isListPair(term: any)
{
 return (term.type == TYPE_ATOM && term.name == '.' && term.children.length == 2);
}

export function isListNull(term: any)
{
 return (term.type == TYPE_ATOM && term.name == '[]' && term.children.length == 0);
}

export function isRuleTerm(term: any)
{
 return (term.type == TYPE_ATOM && term.name == ':-' && term.children.length == 2);
}

function isCommandOp(term: any)
{
 return (term.type == TYPE_ATOM && term.name == ':-' && term.children.length == 1);
}


///////////////////////////////////
// * Type getter / setter functions
///////////////////////////////////

export function getTermNameArity(term: any)
{
 if (!isAtom(term))
  throw new Error("Expected atom.");

 return (term.name.toString()+"/"+term.children.length.toString());
}

export function getTermNameArityFromNameArity(name: any, arity: any)
{
 return (name.toString()+"/"+arity.toString());
}

// term should be Terms
// returns empty array if term is undefined
// returns array of terms, where each element is the head of a binary pair (or last tail).
// eval_fn(t) should be true if t is a binary pair (arity 2) of the appropriate type.
export function getTermArrayFromBinaryTerm(term: any, eval_fn: any)
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

// Return array of variables in given term
export function enumVariables(term: any)
{var vars = new Array();
 var terms_hash = new Hashtable();
 var terms = new Array();
 var t;

 terms.push(term);

 // find all variables
 while ((t = terms.pop()) != undefined)
 {
  if (hashGet(terms_hash,t) == undefined)
  {
   hashPut(terms_hash,t,t);

   if (isVariable(t))
   {
    vars[vars.length] = t;
   }
   else
   {
    for (var i = t.children.length - 1; i >= 0; i--)
	 terms.push(t.children[i]);
   }
  }
 }

 return vars;
}
