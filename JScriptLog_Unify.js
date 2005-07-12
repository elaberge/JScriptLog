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

// unify Enclosures encl1 with encl2
// returns true if they unify, false otherwise.
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
   bindings.push(new Binding(lhs.enclosure,lhs.term.children[0],rhs));
   lhs.enclosure[lhs.term.children[0]] = rhs;
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
