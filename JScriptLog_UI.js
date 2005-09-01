/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_ui_* functions are controllers user interface functionality
///////////////////////////////////

var jslog_query = null;

var QUERY_STATE_INITIAL = 1;
var QUERY_STATE_PROVING = 2;
var QUERY_STATE_WAITING = 3;

var jslog_query_state = QUERY_STATE_INITIAL;

function jslog_ui_clear()
{
 window.document.formUI.output.value = "";
}

// FIX: N-Queens predicates are for demo purposes only.  Remove.
// FIX: member/2, writeln/1, assert/1, etc. are non-ISO builtins.  Move to builtins library.
// FIX: jslog_ui_init_query is for demo purposes only.  Remove.
// FIX: needs to parse kb source, update KB, and perform post-consult optimizations.
function jslog_ui_consult()
{var t;

 jslog_kb = new KB(); 

 // PRE-MADE QUERIES
 jslog_ui_init_query(); 
  
 // BUILTINS
 
 // member(X,[X|_]).
 // member(X,[_|Xs]) :- member(X,Xs).
 {
  addRuleSet(jslog_kb,new RuleSet('member',2,false));
 
  addRule(jslog_kb,newRule(
	t = newAtom('member',[newVariable('X'),newListPair(newVariable('X'),newVariable('_'))])),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('member',[newVariable('X'),newListPair(newVariable('_'),newVariable('Xs'))]),
		newAtom('member',[newVariable('X'),newVariable('Xs')]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 // writeln(O) :- write(O), nl.
 {
  addRuleSet(jslog_kb,new RuleSet('writeln',1,false));

  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('writeln',[newVariable('O')]),
		newConsPair(newAtom('write',[newVariable('O')]),newConstant('nl')))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 // assert(X) :- assertz(X).
 {
  addRuleSet(jslog_kb,new RuleSet('assert',1,false));

  addRule(jslog_kb,newRule(
	t = newRuleTerm(
		newAtom('assert',[newVariable('X')]),
		newAtom('assertz',[newVariable('X')]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 // :- dynamic(p/2).
 {
  addRuleSet(jslog_kb,new RuleSet('p',2,true));

  window.document.formUI.kb.value += ":- dynamic p/2\n\n";	
 }
 
 //queens(N,Qs) :- range(1,N,Ns), queens(Ns,[],Qs).
 {
  addRuleSet(jslog_kb,new RuleSet('queens',2,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('queens',[newVariable('N'),newVariable('Qs')]),
		newConsPair(
			newAtom('range',[newNumber(1),newVariable('N'),newVariable('Ns')]),
			newAtom('queens',[newVariable('Ns'),newListNull(),newVariable('Qs')])))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 //queens(UQs, SQs, Qs) :- selectq(Q,UQs,UQs1),\+ attack(Q,SQs), queens(UQs1,[Q|SQs],Qs).
 //queens([],Qs,Qs).
 {
  addRuleSet(jslog_kb,new RuleSet('queens',3,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('queens',[newVariable('UQs'),newVariable('SQs'),newVariable('Qs')]),
		newConsPairsFromTerms([
			newAtom('selectq',[newVariable('Q'),newVariable('UQs'),newVariable('UQs1')]),
			newAtom('\\+',[newAtom('attack',[newVariable('Q'),newVariable('SQs')])]),
			newAtom('queens',[newVariable('UQs1'),
				newListPair(newVariable('Q'),newVariable('SQs')),newVariable('Qs')])]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
	t = newAtom('queens',[newListNull(),newVariable('Qs'),newVariable('Qs')])),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 // attack(X,Xs) :- attack(X, 1, Xs).
 {
  addRuleSet(jslog_kb,new RuleSet('attack',2,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('attack',[newVariable('X'),newVariable('Xs')]),
		 newAtom('attack',[newVariable('X'),newNumber(1),newVariable('Xs')]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 // attack(X,N,[Y|_]) :- X is Y+N ; X is Y-N.
 // attack(X,N,[_|Ys]) :- N1 is N+1, attack(X,N1,Ys).
 {
  addRuleSet(jslog_kb,new RuleSet('attack',3,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('attack',[newVariable('X'),newVariable('N'),newListPair(newVariable('Y'),newVariable('_'))]),
		newOrPair(
			newAtom('is',[newVariable('X'),newAtom('+',[newVariable('Y'),newVariable('N')])]),
			newAtom('is',[newVariable('X'),newAtom('-',[newVariable('Y'),newVariable('N')])])))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('attack',[newVariable('X'),newVariable('N'),newListPair(newVariable('_'),newVariable('Ys'))]),
		newConsPair(
			newAtom('is',[newVariable('N1'),newAtom('+',[newVariable('N'),newNumber(1)])]),
			newAtom('attack',[newVariable('X'),newVariable('N1'),newVariable('Ys')])))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }

 // range(M,N,[M|Ns]) :- M < N, M1 is M+1, range(M1,N,Ns).
 // range(N,N,[N]).
 {
  addRuleSet(jslog_kb,new RuleSet('range',3,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('range',[newVariable('M'),newVariable('N'),newListPair(newVariable('M'),newVariable('Ns'))]),
		newConsPairsFromTerms([
			newAtom('<',[newVariable('M'),newVariable('N')]),
			newAtom('is',[newVariable('M1'),newAtom('+',[newVariable('M'),newNumber(1)])]),
			newAtom('range',[newVariable('M1'),newVariable('N'),newVariable('Ns')])]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
	t = newAtom('range',[newVariable('N'),newVariable('N'),newListPair(newVariable('N'),newListNull())])),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }

 // selectq(X,[X|Xs],Xs).  
 // selectq(X,[Y|Ys],[Y|Zs]) :- selectq(X,Ys,Zs). 
 {
  addRuleSet(jslog_kb,new RuleSet('selectq',3,false));
 
  addRule(jslog_kb,newRule(
	t = newAtom('selectq',[newVariable('X'),newListPair(newVariable('X'),newVariable('Xs')),newVariable('Xs')])),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('selectq',[newVariable('X'),newListPair(newVariable('Y'),newVariable('Ys')),newListPair(newVariable('Y'),newVariable('Zs'))]),
		newAtom('selectq',[newVariable('X'),newVariable('Ys'),newVariable('Zs')]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }

 try
 {
//  jslog_kb = jslog_parse(window.document.formUI.kb.value);
  window.document.formUI.output.value += "Consulted KB.";  
 }
 catch (ex)
 {
  window.document.formUI.output.value += ex;
 }
 window.document.formUI.output.value += "\n";  
}

// FIX: When parser is working, remove pre-made queries.
var jslog_premade_queries = new Array();

// FIX: When parser is working, remove pre-made queries function.
function jslog_ui_init_query()
{var q = new Array();
 var i = 0;
  
 q[i++] = newAtom('member',[newVariable('Y'),
		newListFromTerms([newConstant('a'),newConstant('b'),newConstant('c'),
			newNumber(1),newNumber(2),newVariable('Z')])]);
  
 q[i++] = newAtom('queens',[newNumber(4),newVariable('X')]);
 q[i++] = newAtom('queens',[newNumber(5),newVariable('X')]);
 q[i++] = newAtom('queens',[newNumber(6),newVariable('X')]);
 q[i++] = newAtom('queens',[newNumber(7),newVariable('X')]);
 q[i++] = newAtom('queens',[newNumber(8),newVariable('X')]);


 q[i++] = newAtom('\\+',[newConstant('true')]);
 q[i++] = newAtom('call',[newConstant('true')]);
 q[i++] = newConstant('fail');
 q[i++] = newAtom('<',[newNumber(4),newNumber(3)]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('+',[newAtom('*',[newNumber(3),newNumber(4)]),newAtom('/',[newAtom('-',[newAtom('-',[newNumber(3)]),newNumber(4)]),newNumber(4)])])]);
 q[i++] = newAtom(';',[newConstant('fail'),newConstant('true')]);
 q[i++] = newAtom('selectq',[newVariable('X'),newListFromTerms([newConstant('a'),newConstant('b'),newConstant('c'),newConstant('d')]),newVariable('Y')]);
 q[i++] = newAtom('range',[newNumber(1),newNumber(4),newVariable('X')]);
 q[i++] = newAtom('\\+',[newAtom('attack',[newNumber(3),newListFromTerms([newNumber(1),newNumber(4),newNumber(2)])])]);
 q[i++] = newAtom('\\+',[newAtom('attack',[newNumber(4),newListFromTerms([newNumber(1)])])]);
 q[i++] = newAtom('\\+',[newAtom('attack',[newNumber(4),newListFromTerms([newNumber(3),newNumber(1)])])]);
 q[i++] = newConsPair(newAtom('=..',[newAtom('p',[newConstant('a'),newConstant('b'),newConstant('c')]),newVariable('L')]),
					  newAtom('=..',[newVariable('X'),newVariable('L')]));
 q[i++] = newAtom('=..',[newNumber(4),newVariable('L')]);
 q[i++] = newAtom('=..',[newAtom('p',[newVariable('A'),newVariable('B')]),
						newListFromTerms([newConstant('p'),newConstant('a'),newVariable('X')])]);
 q[i++] = newAtom('=',[newVariable('A'),newVariable('A')]);
 q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('X'),newAtom('p',[newConstant('a'),newVariable('Y')])]),
			newAtom('copy_term',[newVariable('X'),newVariable('Z')]),
			newAtom('=',[newVariable('Z'),newAtom('p',[newVariable('A'),newConstant('b')])])]);
/* q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('X'),newAtom('p',[newConstant('a'),newVariable('Y')])]),
			newAtom('internal:copy_term',[newVariable('X'),newVariable('Z')]),
			newAtom('=',[newVariable('Z'),newAtom('p',[newVariable('A'),newConstant('b')])])]); */
 q[i++] = newAtom('internal:atom_append!',[newConstant('[]'),newConstant('a')]);
 q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('M'),newListNull()]),
			newAtom('internal:atom_append!',[newVariable('M'),newConstant('a')])]);
 q[i++] = newAtom('=',[newVariable('M'),newListNull()]);
 q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('M'),newAtom('p',[newVariable('X'),newConstant('b')])]),
			newAtom('=',[newVariable('N'),newAtom('p',[newConstant('a'),newVariable('Y')])]),
			newAtom('\\==',[newVariable('M'),newVariable('N')])]);
/* q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('M'),newAtom('p',[newVariable('X'),newConstant('b'),newVariable('A')])]),
			newAtom('=',[newVariable('N'),newAtom('p',[newConstant('a'),newVariable('Y'),newVariable('B')])]),
			newAtom('=',[newVariable('M'),newVariable('N')]),
			newAtom('==',[newVariable('M'),newVariable('N')])]); */
 q[i++] = newAtom('findall',[newVariable('T'),
			newAtom('member',[newVariable('T'),
				newListFromTerms([newConstant('a'),newConstant('b'),newConstant('c'),
				newNumber(1),newNumber(2),newVariable('Z')])]),
			newVariable('L')]);
 q[i++] = newAtom('findall',[newVariable('X'),
			newAtom('queens',[newNumber(4),newVariable('X')]),
			newVariable('L')]);
 q[i++] = newAtom('assertz',[newRuleTerm(
			newAtom('p',[newVariable('X'),newVariable('Y')]),
			newConsPair(newAtom('p',[newVariable('A'),newVariable('Y')]),
						newAtom('is',[newVariable('X'),newAtom('+',[newVariable('A'),newNumber(2)])])))]);
 q[i++] = newAtom('asserta',[newAtom('p',[newNumber(4),newVariable('X')])]);
 q[i++] = newAtom('p',[newVariable('X'),newVariable('Y')]);
 q[i++] = newAtom('retract',[newAtom('p',[newVariable('X'),newVariable('Y')])]);
 
 for (i = 0; i < q.length; i++)
 {
  window.document.formUI.premade_queries[i] = new Option(jslog_toString(q[i]),i.toString(),i==1);
 }

 jslog_premade_queries = q;
}

// FIX: parse query text instead of picking from pre-made queries.
function jslog_ui_query()
{var query_str = window.document.formUI.query.value;
 var query_term;
 
 if (jslog_query_state == QUERY_STATE_WAITING)
  jslog_ui_stop();

 if (jslog_query_state == QUERY_STATE_INITIAL)
 {
  //FIX: until parser is working, use builtin queries.
  query_term = jslog_premade_queries[window.document.formUI.premade_queries.selectedIndex];
    
  jslog_query = newTermEnclosure(query_term); 

  window.document.formUI.output.value += "?- " + jslog_toString(jslog_query) + "\n";
  
  jslog_query_state = QUERY_STATE_PROVING;
  
  try
  {
   if (jslog_user_prove(jslog_query))
   {
    jslog_query_state = QUERY_STATE_WAITING;
    window.document.formUI.output.value += jslog_toString(jslog_query);
   }
   else
   {
    jslog_query_state = QUERY_STATE_INITIAL;
    jslog_query = null;
    window.document.formUI.output.value += "No";
   }
  }
  catch (err)
  {
   jslog_query_state = QUERY_STATE_INITIAL;
   jslog_query = null;
   window.document.formUI.output.value += err.toString();
  } 
  window.document.formUI.output.value += "\n";  
 }
 else
  alert("Stop running query first.");
}

function jslog_ui_retry()
{
 if (jslog_query_state == QUERY_STATE_WAITING)
 {
  jslog_query_state = QUERY_STATE_PROVING;
  
  try
  {
   if (jslog_user_retry())
   {
    jslog_query_state = QUERY_STATE_WAITING;
    window.document.formUI.output.value += jslog_toString(jslog_query);
   }
   else
   {
    jslog_query_state = QUERY_STATE_INITIAL;
    jslog_query = null;
    window.document.formUI.output.value += "No";
   }
  } 
  catch (err)
  {
   jslog_query_state = QUERY_STATE_INITIAL;
   jslog_query = null;
   window.document.formUI.output.value += err.toString();
  } 
  window.document.formUI.output.value += "\n";
 } 
 else
  alert("Cannot retry.");
}

function jslog_ui_stop()
{
 if (jslog_query_state != QUERY_STATE_INITIAL)
 {
  jslog_query_state = QUERY_STATE_INITIAL;
  window.document.formUI.output.value += "stopped query.\n";
 }
 
 jslog_user_stop();  
}
