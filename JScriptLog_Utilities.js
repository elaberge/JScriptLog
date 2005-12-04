/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_library_utilities(kb)
///////////////////////////////////

function jslog_library_utilities(kb)
{var t;

 // writeln(O) :- write(O), nl.
 {
  addRuleSet(kb,new RuleSet('writeln',1,false));

  addRule(kb,newRule(
    t = newRuleTerm(
		newAtom('writeln',[newVariable('O')]),
		newConsPair(newAtom('write',[newVariable('O')]),newConstant('nl')))),
	true);
 }
 // assert(X) :- assertz(X).
 {
  addRuleSet(kb,new RuleSet('assert',1,false));

  addRule(kb,newRule(
	t = newRuleTerm(
		newAtom('assert',[newVariable('X')]),
		newAtom('assertz',[newVariable('X')]))),
	true);
 }
 // ground(X) :- internal:term_variables(X,[]).
 {
  addRuleSet(kb,new RuleSet('ground',1,false));

  addRule(kb,newRule(
	t = newRuleTerm(
		newAtom('ground',[newVariable('X')]),
		newAtom('internal:term_variables',[newVariable('X'),newListNull()]))),
	true);
 }
 // term_variables(X,V) :- internal:term_variables(X,V).
 {
  addRuleSet(kb,new RuleSet('term_variables',2,false));

  addRule(kb,newRule(
	t = newRuleTerm(
		newAtom('term_variables',[newVariable('X'),newVariable('V')]),
		newAtom('internal:term_variables',[newVariable('X'),newVariable('V')]))),
	true);
 }
 // member(X,Xs) :- internal:member(X,Xs).
 {
  addRuleSet(kb,new RuleSet('member',2,false));

  addRule(kb,newRule(
	t = newRuleTerm(
		newAtom('member',[newVariable('X'),newVariable('Xs')]),
		newAtom('internal:member',[newVariable('X'),newVariable('Xs')]))),
	true);
 }
 // append(X,Y,Z) :- internal:append(X,Y,Z).
 {
  addRuleSet(kb,new RuleSet('append',3,false));

  addRule(kb,newRule(
	t = newRuleTerm(
		newAtom('append',[newVariable('X'),newVariable('Y'),newVariable('Z')]),
		newAtom('internal:append',[newVariable('X'),newVariable('Y'),newVariable('Z')]))),
	true);
 }
 // select(X,[X|Xs],Xs).  
 // select(X,[Y|Ys],[Y|Zs]) :- select(X,Ys,Zs). 
 {
  addRuleSet(kb,new RuleSet('select',3,false));
 
  addRule(kb,newRule(
	t = newAtom('select',[newVariable('X'),newListPair(newVariable('X'),newVariable('Xs')),newVariable('Xs')])),
	true);
  addRule(kb,newRule(
    t = newRuleTerm(
		newAtom('select',[newVariable('X'),newListPair(newVariable('Y'),newVariable('Ys')),newListPair(newVariable('Y'),newVariable('Zs'))]),
		newAtom('select',[newVariable('X'),newVariable('Ys'),newVariable('Zs')]))),
	true);
 }
}
