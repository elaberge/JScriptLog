/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// * Enclosures
// An Enclosure is an array of variable references.  
// Variable terms reference bound values via an index into the enclosure.
///////////////////////////////////

// encl must be an Array of enclosures
function Enclosure(enclosure,term)
{
 this.enclosure = enclosure;
 this.term = term;

 //// Other Properties (document here):
 // this.enclosure.goal : the single top goal node the enclosure array exists at, or below
 // this.enclosure.transferred : true if bindings were transferred from original goal

 return this;
}

// encl must be an Array of enclosures
// terms is an array of terms
function ArrayEnclosure(enclosure,terms)
{
 this.enclosure = enclosure;
 this.terms = terms;

 return this;
}

function Binding(enclosure,index)
{
 this.enclosure = enclosure;
 this.index = index;
 
 return this;
}

function Exception(encl)
{
 this.encl = encl;
 
 this.toString = function() { return "Exception - " + jslog_toString(this.encl); };
 
 return this;
}

// Creates an enclosure of size for existing term
function newBlankEnclosure(size,term)
{
 return new Enclosure(new Array(size),term);
}

// Creates an enclosure from an existing enclosure array encl and term
// term should be a sub-term of the rule clause owning the encl.
function newSubtermEnclosure(encl,term)
{
 return new Enclosure(encl,term);
}

// Creates an Exception term from the given string
function newErrorException(str)
{
 return new Exception(newBlankEnclosure(0,newAtom('Error',[newConstant(str)])));
}

// Creates an InternalError Exception term from the given string
// InternalError exceptions denote possibly serious errors affecting internal operations.
// They can be caught, however, the system may be in an inconsistent, or unknown, state.
function newInternalErrorException(str)
{
 return new Exception(newBlankEnclosure(0,newAtom('InternalError',[newConstant(str)])));
}

// Creates a duplicate enclosure via a deep copy.  The terms in encl remain unchanged
// but all enclosures in the enclosure tree are copied.
function newDuplicateEnclosure(encl)
{var encls_hash = new Hashtable();
 var encls_todo = new Array();
 var encls = new Array();
 var e;
 var e_copy;
 
 encl = getFinalEnclosure(encl);
 encls.push(encl);

 // find and copy all enclosures
 while ((e = encls.pop()) != undefined)
 {
  if (hashGet(encls_hash,e.enclosure) == undefined)
  {var i;
  
   e_copy = new Array(e.enclosure.length);
   hashPut(encls_hash,e.enclosure,e_copy);
   encls_todo.push(e);
   
   for (i=0; i < e_copy.length; i++)
   {
    if (e.enclosure[i] != null)
	 encls.push(getFinalEnclosure(e.enclosure[i]));
   }
  }
 }
 
 // connect duplicate enclosures like original ones
 while ((e = encls_todo.pop()) != undefined)
 {var i;

  e_copy = hashGet(encls_hash,e.enclosure);
   
  for (i=0; i < e_copy.length; i++)
  {
   if (e.enclosure[i] != null)
   {var fin_encl = getFinalEnclosure(e.enclosure[i]);

    e_copy[i] = newSubtermEnclosure(hashGet(encls_hash,fin_encl.enclosure),fin_encl.term);
   }
  } 
 }
 
 return newSubtermEnclosure(hashGet(encls_hash,encl.enclosure),encl.term);
}

// Creates a duplicate term from the given enclosure.  Terms are copied.
// Variable equivalence is maintained by using the same variable instance.
function newDuplicateTermFromEnclosure(encl)
{var encls_hash = new Hashtable();
 var enclosures_hash = new Hashtable();
 var encls_todo = new Array();
 var encls = new Array();
 var e;
 
 encl = getFinalEnclosure(encl);
 encls.push(encl);

 // find and copy all terms
 while ((e = encls.pop()) != undefined)
 {
  if (hashGet(encls_hash,e) == undefined)
  {var variables = hashGet(enclosures_hash,e.enclosure);
   var t_copy;
   var i;

   if (variables == undefined)
   {
    variables = new Array(e.enclosure.length);
    hashPut(enclosures_hash,e.enclosure,variables);
   }
    
   t_copy = newDuplicateTerm(e.term,variables);
   hashPut(encls_hash,e,t_copy);
   encls_todo.push(e);
      
   for (i=0; i < e.enclosure.length; i++)
   {
    if (e.enclosure[i] != null && variables[i] != undefined)
	 encls.push(getFinalEnclosure(e.enclosure[i]));
   }
  }
 }

 // replace bound variables in terms with their bound values
 while ((e = encls_todo.pop()) != undefined)
 {var t = hashGet(encls_hash,e);

  replaceVariablesWithTerms(t,e.enclosure,encls_hash);
 }

 return hashGet(encls_hash,encl);
}

// helper function for newDuplicateTermFromEnclosure
function replaceVariablesWithTerms(term,enclosure,encls_hash)
{var terms = new Array();
 var terms_hash = new Hashtable();
 var t;
 
 terms.push(term);

 // find variables and replace them with bound term copies
 while ((t = terms.pop()) != undefined)
 {
  if ((!isVariable(t)) && (hashGet(terms_hash,t) == undefined))
  {var i;
  
   hashPut(terms_hash,t,t);
   
   for (i=0; i < t.children.length; i++)
   {var c = t.children[i];
   
    if (isVariable(c))
	{
	 if (enclosure[c.children[0]] != null)
	  t.children[i] = hashGet(encls_hash,getFinalEnclosure(enclosure[c.children[0]]));
	}
	else 
     terms.push(c);
   }
  }
 }
 
 return true;
}

// Creates a new enclosure for term.
// All variables in term are modified to reference index in new enclosure.
// NOTE: This function mutates term.  Do not use on terms within other enclosures.
function newTermEnclosure(term)
{var encl = new Array();
 var vars = new Object();
 var terms = new Array();
 var t;
 
 terms.push(term);
 
 while ((t = terms.pop()) != undefined)
 {
  if (t.type == TYPE_VARIABLE)
  {
   if (t.name == "_")
   {
    t.children[0] = encl.length;
    encl[t.children[0]] = null;
   }
   else if (vars["_"+t.name] == undefined)
   {
    vars["_"+t.name] = encl.length;
    t.children[0] = vars["_"+t.name];
    encl[encl.length] = null;
   }
   else
   {
    t.children[0] = vars["_"+t.name];
   }	
  }
  else
  {var i;
  
   for (i = t.children.length - 1; i >= 0 ; i--)
    terms.push(t.children[i]);
  }
 };
 
 return new Enclosure(encl,term);
}

///////////////////////////////////
// * Enclosure getter / setter functions
///////////////////////////////////

// Return deepest enclosure for encl term.  
// Returns either last unbound variable (possibly encl), or bound non-var enclosure.
function getFinalEnclosure(encl)
{var et = encl;
 var et2;

 while (et.term.type == TYPE_VARIABLE)
  if ((et2 = et.enclosure[et.term.children[0]]) != null)
   et = et2;
  else
   break;

 return et; 
}

// Return bound enclosure for encl term.  returns null if unbound.
// If term is a bound variable, returns the non-var bound value;
function getBoundEnclosure(encl)
{var et = encl;

 while (et.term.type == TYPE_VARIABLE)
  if ((et = et.enclosure[et.term.children[0]]) == null)
   break;

 return et; 
}

// body is an ArrayEnclosure
function getConsPairEnclosureFromEnclosureArray(body)
{var bterm;
 var i;

 if (body.terms.length >= 1)
  bterm = body.terms[body.terms.length - 1];
 else
  bterm = newConstant('true');
  
 for (i = body.terms.length - 2; i >= 0; i--)
  bterm = newConsPair(body.terms[i],bterm);
 
 return newSubtermEnclosure(body.enclosure,bterm);
}

// Return an array of unbound variable enclosures contained in the given encl
function enumFinalVariableEnclosures(encl)
{var encls_hash = new Hashtable();
 var enclosures_hash = new Hashtable();
 var encls = new Array();
 var vars = new Array();
 var e;
 
 encl = getFinalEnclosure(encl);
 encls.push(encl);

 // find all final variable terms
 while ((e = encls.pop()) != undefined)
 {
  if (hashGet(encls_hash,e) == undefined)
  {var vs = enumVariables(e.term);
   var lencls = new Array();
   var variables;
   var i;

   hashPut(encls_hash,e,e);

   if ((variables = hashGet(enclosures_hash,e.enclosure)) == undefined)
   {
    variables = new Array(e.enclosure.length);
	hashPut(enclosures_hash,e.enclosure,variables);
   }

   for (i = 0; i < vs.length; i++)
   {var idx = vs[i].children[0];
   
    if (variables[idx] == undefined)
	{
     if (e.enclosure[idx] == undefined)
	  vars[vars.length] = newSubtermEnclosure(e.enclosure,vs[i]);
	 else
	  lencls.push(getFinalEnclosure(e.enclosure[idx]));
    
	 variables[idx] = true;
	}
   }

   // local lencls stack trasfered to encls stack to preserve find order for variables
   while ((e = lencls.pop()) != undefined)
    encls.push(e);
  }
 }

 return vars;
}

// encl is the enclosure to bind the value enclosure to
// returns true if the value was bound, false otherwise
function setEnclosureBinding(encl,value)
{var et = encl;
 
 while (et.term.type == TYPE_VARIABLE)
 {
  if (et.enclosure[et.term.children[0]] == null)
  {
   et.enclosure[et.term.children[0]] = value;
   return true;
  }
  else
   et = et.enclosure[et.term.children[0]];
 };
 
 return false; 
}

// encl is the enclosure to bind the value enclosure to
// returns true if the value was bound, false otherwise
// does not actually perform the binding, but adds Binding to bindings array
function setTentativeEnclosureBinding(encl,value,bindings)
{var et = encl;
 
 while (et.term.type == TYPE_VARIABLE)
 {
  if (et.enclosure[et.term.children[0]] == null)
  {
   bindings.push(new Binding(et.enclosure,et.term.children[0],value));
   return true;
  }
  else
   et = et.enclosure[et.term.children[0]];
 };
 
 return false; 
}

///////////////////////////////////
// * Binding functions
///////////////////////////////////

// Remove each Binding in bindings array.
// Mutates bindings to empty array.
function removeBindings(bindings)
{var b;
 
 while ((b = bindings.pop()) != undefined)
 {
  b.enclosure[b.index] = null;
 };
}
