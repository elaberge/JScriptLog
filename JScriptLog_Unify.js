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
   for (i = lhs.term.children.length - 1; i >= 0; i--)
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
      for (i = lhs.term.children.length - 1; i >= 0; i--)
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
