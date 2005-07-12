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

// FIX: member/2 and N-Queens predicates are for demo purposes only.  Remove.
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
	t = newPredicate('member',[newVariable('X'),newListPair(newVariable('X'),newVariable('_'))])),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newPredicate('member',[newVariable('X'),newListPair(newVariable('_'),newVariable('Xs'))]),
		newPredicate('member',[newVariable('X'),newVariable('Xs')]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 //queens(N,Qs) :- range(1,N,Ns), queens(Ns,[],Qs).
 {
  addRuleSet(jslog_kb,new RuleSet('queens',2,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newPredicate('queens',[newVariable('N'),newVariable('Qs')]),
		newConsPair(
			newPredicate('range',[newNumber(1),newVariable('N'),newVariable('Ns')]),
			newPredicate('queens',[newVariable('Ns'),newListNull(),newVariable('Qs')])))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 //queens(UQs, SQs, Qs) :- selectq(Q,UQs,UQs1),\+ attack(Q,SQs), queens(UQs1,[Q|SQs],Qs).
 //queens([],Qs,Qs).
 {
  addRuleSet(jslog_kb,new RuleSet('queens',3,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newPredicate('queens',[newVariable('UQs'),newVariable('SQs'),newVariable('Qs')]),
		newConsPairsFromTerms([
			newPredicate('selectq',[newVariable('Q'),newVariable('UQs'),newVariable('UQs1')]),
			newPredicate('\\+',[newPredicate('attack',[newVariable('Q'),newVariable('SQs')])]),
			newPredicate('queens',[newVariable('UQs1'),
				newListPair(newVariable('Q'),newVariable('SQs')),newVariable('Qs')])]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
	t = newPredicate('queens',[newListNull(),newVariable('Qs'),newVariable('Qs')])),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 // attack(X,Xs) :- attack(X, 1, Xs).
 {
  addRuleSet(jslog_kb,new RuleSet('attack',2,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newPredicate('attack',[newVariable('X'),newVariable('Xs')]),
		 newPredicate('attack',[newVariable('X'),newNumber(1),newVariable('Xs')]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 // attack(X,N,[Y|_]) :- X is Y+N ; X is Y-N.
 // attack(X,N,[_|Ys]) :- N1 is N+1, attack(X,N1,Ys).
 {
  addRuleSet(jslog_kb,new RuleSet('attack',3,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newPredicate('attack',[newVariable('X'),newVariable('N'),newListPair(newVariable('Y'),newVariable('_'))]),
		newOrPair(
			newPredicate('is',[newVariable('X'),newPredicate('+',[newVariable('Y'),newVariable('N')])]),
			newPredicate('is',[newVariable('X'),newPredicate('-',[newVariable('Y'),newVariable('N')])])))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newPredicate('attack',[newVariable('X'),newVariable('N'),newListPair(newVariable('_'),newVariable('Ys'))]),
		newConsPair(
			newPredicate('is',[newVariable('N1'),newPredicate('+',[newVariable('N'),newNumber(1)])]),
			newPredicate('attack',[newVariable('X'),newVariable('N1'),newVariable('Ys')])))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }

 // range(M,N,[M|Ns]) :- M < N, M1 is M+1, range(M1,N,Ns).
 // range(N,N,[N]).
 {
  addRuleSet(jslog_kb,new RuleSet('range',3,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newPredicate('range',[newVariable('M'),newVariable('N'),newListPair(newVariable('M'),newVariable('Ns'))]),
		newConsPairsFromTerms([
			newPredicate('<',[newVariable('M'),newVariable('N')]),
			newPredicate('is',[newVariable('M1'),newPredicate('+',[newVariable('M'),newNumber(1)])]),
			newPredicate('range',[newVariable('M1'),newVariable('N'),newVariable('Ns')])]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
	t = newPredicate('range',[newVariable('N'),newVariable('N'),newListPair(newVariable('N'),newListNull())])),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }

 // selectq(X,[X|Xs],Xs).  
 // selectq(X,[Y|Ys],[Y|Zs]) :- selectq(X,Ys,Zs). 
 {
  addRuleSet(jslog_kb,new RuleSet('selectq',3,false));
 
  addRule(jslog_kb,newRule(
	t = newPredicate('selectq',[newVariable('X'),newListPair(newVariable('X'),newVariable('Xs')),newVariable('Xs')])),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newPredicate('selectq',[newVariable('X'),newListPair(newVariable('Y'),newVariable('Ys')),newListPair(newVariable('Y'),newVariable('Zs'))]),
		newPredicate('selectq',[newVariable('X'),newVariable('Ys'),newVariable('Zs')]))),
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
  
 q[i++] = newPredicate('member',[newVariable('Y'),
		newListFromTerms([newConstant('a'),newConstant('b'),newConstant('c'),
			newNumber(1),newNumber(2),newVariable('Z')])]);
  
 q[i++] = newPredicate('queens',[newNumber(4),newVariable('X')]);
 q[i++] = newPredicate('queens',[newNumber(5),newVariable('X')]);
 q[i++] = newPredicate('queens',[newNumber(6),newVariable('X')]);
 q[i++] = newPredicate('queens',[newNumber(7),newVariable('X')]);
 q[i++] = newPredicate('queens',[newNumber(8),newVariable('X')]);


 q[i++] = newPredicate('\\+',[newConstant('true')]);
 q[i++] = newPredicate('call',[newConstant('true')]);
 q[i++] = newConstant('fail');
 q[i++] = newPredicate('<',[newNumber(4),newNumber(3)]);
 q[i++] = newPredicate('is',[newVariable('X'),newPredicate('+',[newNumber(3),newNumber(4)])]);
 q[i++] = newPredicate(';',[newConstant('fail'),newConstant('true')]);
 q[i++] = newPredicate('selectq',[newVariable('X'),newListFromTerms([newConstant('a'),newConstant('b'),newConstant('c'),newConstant('d')]),newVariable('Y')]);
 q[i++] = newPredicate('range',[newNumber(1),newNumber(4),newVariable('X')]);
 q[i++] = newPredicate('\\+',[newPredicate('attack',[newNumber(3),newListFromTerms([newNumber(1),newNumber(4),newNumber(2)])])]);
 q[i++] = newPredicate('\\+',[newPredicate('attack',[newNumber(4),newListFromTerms([newNumber(1)])])]);
 q[i++] = newPredicate('\\+',[newPredicate('attack',[newNumber(4),newListFromTerms([newNumber(3),newNumber(1)])])]);

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
