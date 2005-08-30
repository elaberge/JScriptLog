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
  if (hashGet(encls_hash,e) == undefined)
  {var i;
  
   e_copy = new Array(e.enclosure.length);
   hashPut(encls_hash,e,e_copy);
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
  
  e_copy = hashGet(encls_hash,e);
   
  for (i=0; i < e_copy.length; i++)
  {
   if (e.enclosure[i] != null)
   {var fin_encl = getFinalEnclosure(e.enclosure[i]);
   
    e_copy[i] = newSubtermEnclosure(hashGet(encls_hash,fin_encl),fin_encl.term);
	encls.push(fin_encl);
   }
  } 
 }
 
 return newSubtermEnclosure(hashGet(encls_hash,encl),encl.term);
}

// Creates a duplicate term from the given enclosure.  Terms are copied.
// Variable equivalence is maintained by using the same variable instance.
function newDuplicateTermFromEnclosure(encl)
{var encls_hash = new Hashtable();
 var encls = new Array();
 var e;
 
 encl = getFinalEnclosure(encl);
 encls.push(encl);

 // find and copy all terms
 while ((e = encls.pop()) != undefined)
 {
  if (hashGet(encls_hash,e) == undefined)
  {var variables = new Array();
   var t_copy;
   var i;

   t_copy = newDuplicateTerm(e.term,variables);
   hashPut(encls_hash,e,new Pair(variables,t_copy));
   
   for (i=0; i < e.enclosure.length; i++)
   {
    if (e.enclosure[i] != null && variables[i] != undefined)
	 encls.push(getFinalEnclosure(e.enclosure[i]));
   }
  }
 }

 encls.push(encl);
 
 // replace bound variables in terms with their bound values
 while ((e = encls.pop()) != undefined)
 {var i;
  var hash_pair = hashGet(encls_hash,e);
  
  replaceVariablesWithTerms(hash_pair.second,e.enclosure,encls_hash);
  
  for (i=0; i < e.enclosure.length; i++)
  {
   if (e.enclosure[i] != null && hash_pair.first[i] != undefined)
    encls.push(getFinalEnclosure(e.enclosure[i]));
  }
 }
 
 return hashGet(encls_hash,encl).second;
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
  if (!isVariable(t) && hashGet(terms_hash,t) == undefined)
  {var i;
  
   hashPut(terms_hash,t,t);
   
   for (i=0; i < t.children.length; i++)
   {var c = t.children[i];
   
    if (isVariable(c))
	{
	 if (enclosure[c.children[0]] != null)
	  t.children[i] = hashGet(encls_hash,getFinalEnclosure(enclosure[c.children[0]])).second;
	}
	else 
     terms.push(t.children[i]);
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
