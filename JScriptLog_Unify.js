/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_unify_* functions for Unification
///////////////////////////////////

// Unify Enclosures encl1 with encl2
// Returns true if they unify, false otherwise.
// encl1 and encl2 are mutated only in the case that unification occurs, 
// bindings is the array of affected enclosure entries, and their bound enclosures.
// bindings must be an empty array (e.g., new Array()) when passed in.
function jslog_unify(encl1,encl2,bindings)
{var lhs_encls = new Array(1);
 var rhs_encls = new Array(1);
 var lhs, rhs;

 lhs_encls[0] = encl1;
 rhs_encls[0] = encl2;

 while ((lhs = lhs_encls.pop()) != undefined && (rhs = rhs_encls.pop()) != undefined)
 {
  lhs = getFinalEnclosure(lhs);
  rhs = getFinalEnclosure(rhs);
  
  if (isVariable(lhs.term))
  {
   if (isVariable(rhs.term) && lhs.enclosure == rhs.enclosure && 
		lhs.term.children[0] == rhs.term.children[0])
   {
    // do nothing, variables are equal
   }
   else
   {
    bindings.push(new Binding(lhs.enclosure,lhs.term.children[0],rhs));
    lhs.enclosure[lhs.term.children[0]] = rhs;
   }
  }
  else if (isVariable(rhs.term))
  {
   bindings.push(new Binding(rhs.enclosure,rhs.term.children[0],lhs));
   rhs.enclosure[rhs.term.children[0]] = lhs;
  }
  else if ((lhs.term.type != rhs.term.type) || (lhs.term.name != rhs.term.name) ||
			(lhs.term.children.length != rhs.term.children.length))
  {
   removeBindings(bindings);			
   return false;
  }
  else
  {
   for (var i = lhs.term.children.length - 1; i >= 0; i--)
   {
    lhs_encls.push(newSubtermEnclosure(lhs.enclosure,lhs.term.children[i]));
    rhs_encls.push(newSubtermEnclosure(rhs.enclosure,rhs.term.children[i]));
   }
  }
 };

 if (lhs_encls.length == 0 && rhs_encls.length == 0)
  return true;

 removeBindings(bindings);
 return false;
}

// Compares the ordering of two Enclosures, encl1 and encl2.
// Returns 0 if they are identical, -1 if encl1 is ordered before encl2, 1 if after.
// The standard ordering is: variables @< numbers @< constants @< atoms @< object references. 
//   variables are ordered by Javascript internals and their enclosure index number; 
//   numbers are sorted in increasing order; 
//   constants are sorted in lexicographic order; 
//   atoms are ordered first by name, then arity, then by their arguments in left-to-right order; 
//   object references are ordered by Javascript internals.
function jslog_compare(encl1,encl2)
{var lhs_encls = new Array(1);
 var rhs_encls = new Array(1);
 var lhs, rhs;

 lhs_encls[0] = encl1;
 rhs_encls[0] = encl2;

 while ((lhs = lhs_encls.pop()) != undefined && (rhs = rhs_encls.pop()) != undefined)
 {
  lhs = getFinalEnclosure(lhs);
  rhs = getFinalEnclosure(rhs);
  
  if (isVariable(lhs.term))
  {
   if (isVariable(rhs.term))
   {
    if (lhs.enclosure == rhs.enclosure)
    {
	 if (lhs.term.children[0] == rhs.term.children[0])
	 {// do nothing, variables are equal
	 }
     else if (lhs.term.children[0] < rhs.term.children[0])
	  return -1;
	 else
	  return 1;
    }
    else if (lhs.enclosure < rhs.enclosure)
     return -1;
	else
	 return 1;
   }
   else
    return -1;	
  }
  else if (isVariable(rhs.term))
  {
   return 1;
  }
  else if (isNumber(lhs.term))
  {
   if (isNumber(rhs.term))
   {
    if (lhs.term.name < rhs.term.name)
	 return -1;
    else if (lhs.term.name > rhs.term.name)
	 return 1;
    // else do nothing, numbers are equal
   }
   else
    return -1;
  }
  else if (isNumber(rhs.term))
  {
   return 1;
  }
  else if (isAtom(lhs.term))
  {
   if (isAtom(rhs.term))
   {
    if (lhs.term.name < rhs.term.name)
	 return -1;
    else if (lhs.term.name > rhs.term.name)
	 return 1;
    else // atom names are equal
	{
	 if (lhs.term.children.length < rhs.term.children.length)
	  return -1;
	 else if (lhs.term.children.length > rhs.term.children.length)
	  return 1;
	 else // atom name / arity are equal
	 {
      for (var i = lhs.term.children.length - 1; i >= 0; i--)
      {
       lhs_encls.push(newSubtermEnclosure(lhs.enclosure,lhs.term.children[i]));
       rhs_encls.push(newSubtermEnclosure(rhs.enclosure,rhs.term.children[i]));
      }
	 }
	}
   }
   else
    return -1;
  }
  else if (isAtom(rhs.term))
  {
   return 1;
  }
  else if (isObjectReference(lhs.term))
  {
   if (isObjectReference(rhs.term))
   {
    if (lhs.term.name == rhs.term.name)
	{// do nothing, object references are equal
	}
    else if (lhs.term.name < rhs.term.name)
	 return -1;
    else 
	 return 1;
   }
   else
    return -1;
  }
  else if (isObjectReference(rhs.term))
  {
   return 1;
  }
 };

 if (lhs_encls.length == 0 && rhs_encls.length == 0)
  return 0;

 throw newErrorException("Error comparing terms in jslog_compare.");
}

// Same as jslog_unify, 
// except that unification fails if the binding variable appears in the bound term.
// NOTE: do not maintain separately from jslog_unify -- if jslog_unify is modified,
// copy it, then add the two jslog_occurs_check tests.
function jslog_unify_with_occurs_check(encl1,encl2,bindings)
{var lhs_encls = new Array(1);
 var rhs_encls = new Array(1);
 var lhs, rhs;

 lhs_encls[0] = encl1;
 rhs_encls[0] = encl2;

 while ((lhs = lhs_encls.pop()) != undefined && (rhs = rhs_encls.pop()) != undefined)
 {
  lhs = getFinalEnclosure(lhs);
  rhs = getFinalEnclosure(rhs);
  
  if (isVariable(lhs.term))
  {
   if (isVariable(rhs.term) && lhs.enclosure == rhs.enclosure && 
		lhs.term.children[0] == rhs.term.children[0])
   {
    // do nothing, variables are equal
   }
   else
   {
    if (jslog_occurs_check(lhs,rhs))
	{
     bindings.push(new Binding(lhs.enclosure,lhs.term.children[0],rhs));
     lhs.enclosure[lhs.term.children[0]] = rhs;
    }
	else
    {
     removeBindings(bindings);			
     return false;
    }
   }
  }
  else if (isVariable(rhs.term))
  {
   if (jslog_occurs_check(rhs,lhs))
   {
    bindings.push(new Binding(rhs.enclosure,rhs.term.children[0],lhs));
    rhs.enclosure[rhs.term.children[0]] = lhs;
   }
   else
   {
    removeBindings(bindings);			
    return false;
   }   
  }
  else if ((lhs.term.type != rhs.term.type) || (lhs.term.name != rhs.term.name) ||
			(lhs.term.children.length != rhs.term.children.length))
  {
   removeBindings(bindings);			
   return false;
  }
  else
  {
   for (var i = lhs.term.children.length - 1; i >= 0; i--)
   {
    lhs_encls.push(newSubtermEnclosure(lhs.enclosure,lhs.term.children[i]));
    rhs_encls.push(newSubtermEnclosure(rhs.enclosure,rhs.term.children[i]));
   }
  }
 };

 if (lhs_encls.length == 0 && rhs_encls.length == 0)
  return true;

 removeBindings(bindings);
 return false;
}

// Performs the occurs check (determine if variable v_encl is unbound in t_encl).
// returns true if the occurs check succeeds (i.e., v_encl is not in t_encl), 
// returns false otherwise (i.e., v_encl occurs in t_encl).
// isVariable(v_encl.term) must be true.
function jslog_occurs_check(v_encl,t_encl)
{var v_encls = enumFinalVariableEnclosures(t_encl);
 var e;
 
 for (var i = 0; i < v_encls.length; i++)
 {
  e = v_encls[i];
  
  if (v_encl.enclosure == e.enclosure && v_encl.term.children[0] == e.term.children[0])
   return false;
 }

 return true;
}

// Equivalence test Enclosures encl1 with encl2
// Returns true if they are structurally equivalent, false otherwise.
// encl1 and encl2 are not mutated.
// NOTE: based on jslog_unify -- if jslog_unify is modified, verify this remains valid.
function jslog_equivalent(encl1,encl2)
{var vars_hash = new Hashtable();
 var lhs_encls = new Array(1);
 var rhs_encls = new Array(1);
 var lhs, rhs;

 lhs_encls[0] = encl1;
 rhs_encls[0] = encl2;

 while ((lhs = lhs_encls.pop()) != undefined && (rhs = rhs_encls.pop()) != undefined)
 {
  lhs = getFinalEnclosure(lhs);
  rhs = getFinalEnclosure(rhs);
  
  if (isVariable(lhs.term) && isVariable(rhs.term))
  {
   if (lhs.enclosure == rhs.enclosure && 
		lhs.term.children[0] == rhs.term.children[0])
   {
    // do nothing, variables are equal
   }
   else
   {
    // mapping is an array of (enclosure,index) pairs
	// NOTE: lhs_encl_mapping and rhs_encl_mapping may be the same object
    var lhs_encl_mapping = hashGet(vars_hash,lhs.enclosure);

	if (lhs_encl_mapping == undefined)
	{
	 lhs_encl_mapping = new Array(lhs.enclosure.length);
	 hashPut(vars_hash,lhs.enclosure,lhs_encl_mapping);
	}
	
	// lhs_encl_mapping must already be hashPut since lhs and rhs enclosures may be equal.
    var rhs_encl_mapping = hashGet(vars_hash,rhs.enclosure);

	if (rhs_encl_mapping == undefined)
	{
	 rhs_encl_mapping = new Array(rhs.enclosure.length);
	 hashPut(vars_hash,rhs.enclosure,rhs_encl_mapping);
	}
	
	var lhs_mapping = lhs_encl_mapping[lhs.term.children[0]];
	var rhs_mapping = rhs_encl_mapping[rhs.term.children[0]];
	
	if (lhs_mapping == undefined && rhs_mapping == undefined)
	{
	 lhs_mapping = new Pair(rhs.enclosure,rhs.term.children[0]);
	 rhs_mapping = new Pair(lhs.enclosure,lhs.term.children[0]);
	 
	 lhs_encl_mapping[lhs.term.children[0]] = lhs_mapping;
	 rhs_encl_mapping[rhs.term.children[0]] = rhs_mapping;
	}
	else if (lhs_mapping == undefined || rhs_mapping == undefined)
	{
	 return false;
	}
	else
	{
	 if (lhs_mapping.first != lhs.enclosure || rhs_mapping.first != lhs.enclosure ||
		 lhs_mapping.second != rhs.term.children[0] || rhs_mapping.second != lhs.term.children[0])
	  return false; 
	}
   }
  }
  else if ((lhs.term.type != rhs.term.type) || (lhs.term.name != rhs.term.name) ||
			(lhs.term.children.length != rhs.term.children.length))
  {
   return false;
  }
  else
  {
   for (var i = lhs.term.children.length - 1; i >= 0; i--)
   {
    lhs_encls.push(newSubtermEnclosure(lhs.enclosure,lhs.term.children[i]));
    rhs_encls.push(newSubtermEnclosure(rhs.enclosure,rhs.term.children[i]));
   }
  }
 };

 if (lhs_encls.length == 0 && rhs_encls.length == 0)
  return true;

 return false;
}
