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

var jslog_kb = new KB();
var jslog_prover = null;

function jslog_ui_clear()
{
 window.document.formUI.output.value = "";
}

// FIX: N-Queens predicates are for demo purposes only.  Remove.
// FIX: jslog_ui_init_query is for demo purposes only.  Remove, keeping tests in testing harness.
// FIX: needs to parse kb source, update KB, and perform post-consult optimizations.
function jslog_ui_consult()
{var t;

 jslog_kb = newKB(); 
 
 loadKBLibrary(jslog_kb,jslog_library_utilities);

 // PRE-MADE QUERIES
 jslog_ui_init_query(); 
  
 // DEMO TEST PREDICATES
  
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
 //queens(UQs, SQs, Qs) :- select(Q,UQs,UQs1),\+ attack(Q,SQs), queens(UQs1,[Q|SQs],Qs).
 //queens([],Qs,Qs).
 {
  addRuleSet(jslog_kb,new RuleSet('queens',3,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('queens',[newVariable('UQs'),newVariable('SQs'),newVariable('Qs')]),
		newConsPairsFromTerms([
			newAtom('select',[newVariable('Q'),newVariable('UQs'),newVariable('UQs1')]),
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
 
 // predicate_property(queens(_,_),_) :- !, fail.
 // predicate_property(queens(_,_,_),_) :- !, fail.
 // predicate_property(attack(_,_),_) :- !, fail.
 // predicate_property(attack(_,_,_),_) :- !, fail.
 // predicate_property(range(_,_,_),_) :- !, fail.
 // predicate_property(select(_,_,_),_) :- !, fail.
 // predicate_property(X,built_in) :- !.
 {
  addRuleSet(jslog_kb,new RuleSet('predicate_property',2,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('predicate_property',[
			newAtom('queens',[newVariable('_'),newVariable('_')]),newVariable('_')]),
		newConsPair(newConstant('!'),newConstant('fail')))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('predicate_property',[
			newAtom('queens',[newVariable('_'),newVariable('_'),newVariable('_')]),newVariable('_')]),
		newConsPair(newConstant('!'),newConstant('fail')))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('predicate_property',[
			newAtom('attack',[newVariable('_'),newVariable('_')]),newVariable('_')]),
		newConsPair(newConstant('!'),newConstant('fail')))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('predicate_property',[
			newAtom('attack',[newVariable('_'),newVariable('_'),newVariable('_')]),newVariable('_')]),
		newConsPair(newConstant('!'),newConstant('fail')))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('predicate_property',[
			newAtom('range',[newVariable('_'),newVariable('_'),newVariable('_')]),newVariable('_')]),
		newConsPair(newConstant('!'),newConstant('fail')))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('predicate_property',[
			newAtom('select',[newVariable('_'),newVariable('_'),newVariable('_')]),newVariable('_')]),
		newConsPair(newConstant('!'),newConstant('fail')))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('predicate_property',[
			newVariable('X'),newConstant('built_in')]),
		newConstant('!'))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 // pprove((A;B)) :- !, pprove(A) ; pprove(B).
 // pprove((A,B)) :- !, pprove(A) , pprove(B).
 // pprove(!) :- !, pprove_cut.
 // pprove(X) :- predicate_property(X,built_in), !, call(X).
 // pprove(H) :- catch((clause(H,B), pprove(B)), pprove_cut_exception, fail).
 {
  addRuleSet(jslog_kb,new RuleSet('pprove',1,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('pprove',[newOrPair(newVariable('A'),newVariable('B'))]),
		newConsPair(newConstant('!'),
			newOrPair(newAtom('pprove',[newVariable('A')]),newAtom('pprove',[newVariable('B')]))))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('pprove',[newConsPair(newVariable('A'),newVariable('B'))]),
		newConsPair(newConstant('!'),
			newConsPair(newAtom('pprove',[newVariable('A')]),newAtom('pprove',[newVariable('B')]))))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('pprove',[newConstant('!')]),
		newConsPair(newConstant('!'),newConstant('pprove_cut')))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('pprove',[newVariable('X')]),
		newConsPairsFromTerms([newAtom('predicate_property',[newVariable('X'),newConstant('built_in')]),
			newConstant('!'),
			newAtom('call',[newVariable('X')])]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('pprove',[newVariable('H')]),
		newAtom('catch',[newConsPair(newAtom('clause',[newVariable('H'),newVariable('B')]),
									newAtom('pprove',[newVariable('B')])),
						newConstant('pprove_cut_exception'),
						newConstant('fail')]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }

 // pprove_cut. 
 // pprove_cut :- throw(pprove_cut_exception). 
 {
  addRuleSet(jslog_kb,new RuleSet('pprove_cut',0,false));
 
  addRule(jslog_kb,newRule(
    t = newConstant('pprove_cut')),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newConstant('pprove_cut'),
		newAtom('throw',[newConstant('pprove_cut_exception')]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }


 // plus(X,Y,Z) :- Z is X + Y.  
 {
  addRuleSet(jslog_kb,new RuleSet('plus',3,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('plus',[newVariable('X'),newVariable('Y'),newVariable('Z')]),
		newAtom('is',[newVariable('Z'),newAtom('+',[newVariable('X'),newVariable('Y')])]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }

 // :- dynamic(p/2).
 {
  addRuleSet(jslog_kb,new RuleSet('p',2,true));

  window.document.formUI.kb.value += ":- dynamic p/2\n\n";	
 }
 
 // f/2 : testing facts.
 {
  addRuleSet(jslog_kb,new RuleSet('f',2,true));

  window.document.formUI.kb.value += ":- dynamic f/2\n\n";	
 
  addRule(jslog_kb,newRule(t = newAtom('f',[newNumber(1),newNumber(1)])),true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(t = newAtom('f',[newNumber(1),newNumber(2)])),true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(t = newAtom('f',[newNumber(2),newNumber(1)])),true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(t = newAtom('f',[newNumber(2),newNumber(2)])),true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(t = newAtom('f',[newNumber(3),newNumber(1)])),true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(t = newAtom('f',[newNumber(4),newNumber(2)])),true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(t = newAtom('f',[newNumber(3),newNumber(1)])),true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(t = newAtom('f',[newNumber(4),newNumber(2)])),true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n\n";	
 }
 // throw_long(0) :- throw(err('test throw').  
 // throw_long(N) :- N1 is N - 1, throw_long(N1). 
 {
  addRuleSet(jslog_kb,new RuleSet('throw_long',1,false));
 
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('throw_long',[newNumber(0)]),
		newAtom('throw',[newAtom('err',[newConstant('test throw')])]))),
	true);
  window.document.formUI.kb.value += jslog_toString(t) + "\n";	
  addRule(jslog_kb,newRule(
    t = newRuleTerm(
		newAtom('throw_long',[newVariable('N')]),
		newConsPair(
			newAtom('is',[newVariable('N1'),newAtom('-',[newVariable('N'),newNumber(1)])]),
			newAtom('throw_long',[newVariable('N1')])))),
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

 q[i++] = newAtom('pprove',[newAtom('queens',[newNumber(4),newVariable('X')])]);

 q[i++] = newAtom('\\+',[newConstant('true')]);
 q[i++] = newAtom('call',[newConstant('true')]);
 q[i++] = newAtom('once',[newAtom('queens',[newNumber(4),newVariable('X')])]);
 q[i++] = newConsPair(newConstant('repeat'),newAtom('writeln',[newConstant('hi there.')]));
 q[i++] = newConstant('fail');
 q[i++] = newAtom('<',[newNumber(4),newNumber(3)]);
 q[i++] = newAtom('>=',[newAtom('*',[newNumber(4),newNumber(3)]),newAtom('+',[newNumber(3),newNumber(4)])]);
 q[i++] = newAtom('=<',[newAtom('*',[newNumber(4),newNumber(3)]),newAtom('+',[newNumber(3),newNumber(4)])]);
 q[i++] = newAtom('=:=',[newAtom('*',[newNumber(2),newNumber(2)]),newAtom('+',[newNumber(2),newNumber(2)])]);
 q[i++] = newAtom('=\\=',[newAtom('*',[newNumber(2),newNumber(2)]),newAtom('+',[newNumber(2),newNumber(2)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('+',[newAtom('*',[newNumber(3),newNumber(4)]),newAtom('/',[newAtom('-',[newAtom('-',[newNumber(3)]),newNumber(4)]),newNumber(4)])])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('//',[newNumber(10),newNumber(3)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('mod',[newNumber(10),newNumber(3)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('**',[newNumber(2),newNumber(4)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('exp',[newAtom('log',[newNumber(3)])])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('sqrt',[newAtom('abs',[newNumber(-2)])])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('integer',[newNumber(-3.6)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('integer',[newNumber(6.3)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('float',[newNumber(6.3)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('float_fractional_part',[newNumber(-3.6)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('float_fractional_part',[newNumber(6.3)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('floor',[newNumber(6.3)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('ceiling',[newNumber(6.3)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('round',[newNumber(6.5)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('sign',[newNumber(5)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('sign',[newNumber(-4)])]);
 q[i++] = newAtom('is',[newVariable('X'),newAtom('<<',[newNumber(2),newNumber(1)])]);
 q[i++] = newAtom('var',[newVariable('X')]);
 q[i++] = newAtom('nonvar',[newVariable('X')]);
 q[i++] = newAtom('nonvar',[newConstant('abc')]);
 q[i++] = newAtom('atom',[newConstant('abc')]);
 q[i++] = newAtom('atom',[newAtom('abc',[newVariable('X')])]);
 q[i++] = newAtom('atomic',[newConstant('abc')]);
 q[i++] = newAtom('atomic',[newNumber(42)]);
 q[i++] = newAtom('atomic',[newAtom('abc',[newVariable('X')])]);
 q[i++] = newAtom('number',[newConstant('abc')]);
 q[i++] = newAtom('number',[newNumber(42)]);
 q[i++] = newAtom('integer',[newNumber(42)]);
 q[i++] = newAtom('integer',[newNumber(3.14)]);
 q[i++] = newAtom('compound',[newConstant('abc')]);
 q[i++] = newAtom('compound',[newNumber(42)]);
 q[i++] = newAtom('compound',[newAtom('abc',[newVariable('X')])]);

 q[i++] = newAtom('ground',[newAtom('abc',[newVariable('X')])]);
 q[i++] = newAtom('ground',[newAtom('abc',[newConstant('abc')])]);

 q[i++] = newAtom('term_variables',[newAtom('a',[newVariable('X'),newConstant('b'),
					newAtom('c',[newVariable('X'),newVariable('Y')])]),newVariable('L')]);
 q[i++] = newConsPairsFromTerms([newAtom('=',[newVariable('A'),newAtom('a',[newVariable('X'),newVariable('Y'),newVariable('Z')])]),
			newAtom('=',[newVariable('A'),newAtom('a',[newConstant('b'),newAtom('c',[newVariable('B'),newVariable('Z')]),newVariable('B')])]),
			newAtom('term_variables',[newVariable('A'),newVariable('L')])]);
 
 q[i++] = newAtom(';',[newConstant('fail'),newConstant('true')]);
 q[i++] = newAtom('select',[newVariable('X'),newListFromTerms([newConstant('a'),newConstant('b'),newConstant('c'),newConstant('d')]),newVariable('Y')]);
 q[i++] = newAtom('range',[newNumber(1),newNumber(4),newVariable('X')]);
 q[i++] = newAtom('\\+',[newAtom('attack',[newNumber(3),newListFromTerms([newNumber(1),newNumber(4),newNumber(2)])])]);
 q[i++] = newAtom('\\+',[newAtom('attack',[newNumber(4),newListFromTerms([newNumber(1)])])]);
 q[i++] = newAtom('\\+',[newAtom('attack',[newNumber(4),newListFromTerms([newNumber(3),newNumber(1)])])]);
 q[i++] = newAtom('arg',[newNumber(2),newAtom('a',[newConstant('a'),newConstant('b'),newConstant('c')]),newVariable('T')]);
 q[i++] = newConsPair(newAtom('=..',[newAtom('p',[newConstant('a'),newConstant('b'),newConstant('c')]),newVariable('L')]),
					  newAtom('=..',[newVariable('X'),newVariable('L')]));
 q[i++] = newAtom('=..',[newNumber(4),newVariable('L')]);
 q[i++] = newAtom('=..',[newAtom('p',[newVariable('A'),newVariable('B')]),
						newListFromTerms([newConstant('p'),newConstant('a'),newVariable('X')])]);
 q[i++] = newAtom('=',[newVariable('A'),newVariable('A')]);
 q[i++] = newAtom('unify_with_occurs_check',[
				newAtom('a',[newNumber(1),newConstant('b'),newVariable('Z')]),
				newAtom('a',[newVariable('A'),newVariable('B'),newAtom('c',[newVariable('Y')])])]);
 q[i++] = newAtom('unify_with_occurs_check',[
				newAtom('a',[newNumber(1),newConstant('b'),newVariable('Z')]),
				newAtom('a',[newVariable('A'),newVariable('B'),newAtom('c',[newVariable('Z')])])]);

/* q[i++] = newConsPair(newAtom('=',[
				newAtom('a',[newNumber(1),newConstant('b'),newVariable('Z')]),
				newAtom('a',[newVariable('A'),newVariable('B'),newAtom('c',[newVariable('Z')])])]),
			newAtom('writeln',[newConstant('unified... but hangs on display of cyclic term.')]));
*/

 q[i++] = newAtom('atom_length',[newAtom('abc',[newVariable('X')]),newVariable('Y')]);
 q[i++] = newAtom('atom_length',[newConstant('abc'),newVariable('Y')]);
 q[i++] = newAtom('char_code',[newConstant('a'),newVariable('Y')]);
 q[i++] = newAtom('char_code',[newVariable('Y'),newNumber(98)]);
 q[i++] = newAtom('atom_chars',[newConstant('abcd134'),newVariable('Y')]);
 q[i++] = newAtom('atom_chars',[newVariable('Y'),newListFromTerms([newConstant('a'),newConstant('b'),newConstant('1'),newConstant('2')])]);
 q[i++] = newAtom('atom_codes',[newConstant('abcd134'),newVariable('Y')]);
 q[i++] = newAtom('atom_codes',[newVariable('Y'),newListFromTerms([newNumber(97),newNumber(98),newNumber(99),newNumber(42)])]);
 q[i++] = newAtom('number_chars',[newNumber(1.2e3),newVariable('Y')]);
 q[i++] = newConsPair(
			newAtom('number_chars',[newVariable('Y'),newListFromTerms([newConstant('1'),newConstant('2'),newConstant('.'),newConstant('3')])]),
			newAtom('number',[newVariable('Y')]));
 q[i++] = newAtom('number_codes',[newNumber(1.2e3),newVariable('Y')]);
 q[i++] = newConsPair(
			newAtom('number_codes',[newVariable('Y'),newListFromTerms([newNumber(49),newNumber(50),newNumber(51),newNumber(52)])]),
			newAtom('number',[newVariable('Y')]));
 q[i++] = newAtom('atom_concat',[newConstant('abc'),newVariable('Y'),newConstant('abc123')]);
 q[i++] = newAtom('atom_concat',[newVariable('Y'),newConstant('123'),newConstant('abc123')]);
 q[i++] = newAtom('atom_concat',[newConstant('abc'),newConstant('123'),newVariable('Y')]);
 q[i++] = newAtom('atom_concat',[newVariable('Y'),newVariable('Z'),newConstant('abc123')]);
 q[i++] = newAtom('sub_atom',[newConstant('abc123'),newVariable('A'),newVariable('B'),newVariable('C'),newVariable('D')]);
 q[i++] = newAtom('sub_atom',[newConstant('abc123'),newVariable('A'),newNumber(3),newVariable('C'),newVariable('D')]);
 q[i++] = newAtom('internal:number_atom',[newNumber(123),newVariable('Y')]);
 q[i++] = newAtom('internal:number_atom',[newNumber(123.123),newVariable('Y')]);
 q[i++] = newAtom('internal:number_atom',[newVariable('Y'),newConstant('98')]);
 q[i++] = newAtom('internal:number_atom',[newVariable('Y'),newConstant('98.98')]);
 q[i++] = newAtom('internal:number_atom',[newVariable('Y'),newConstant('1.2e3')]);

 q[i++] = newAtom('if',[newAtom('queens',[newNumber(4),newVariable('X')]),
			newAtom('queens',[newNumber(4),newVariable('Y')]),
			newAtom('writeln',[newConstant('NO SOLNS')])]);
 q[i++] = newAtom('if',[newConstant('fail'),
			newAtom('writeln',[newConstant('YES')]),
			newAtom('writeln',[newConstant('NO')])]);

 q[i++] = newAtom('->',[newAtom('queens',[newNumber(4),newVariable('X')]),
			newAtom('queens',[newNumber(4),newVariable('Y')])]);
 q[i++] = newAtom('->',[newAtom('queens',[newNumber(4),newVariable('X')]),
			newAtom('queens',[newNumber(4),newVariable('Y')]),
			newAtom('writeln',[newConstant('NO SOLNS')])]);
 q[i++] = newAtom('->',[newConstant('fail'),
			newAtom('writeln',[newConstant('YES')])]);
 q[i++] = newAtom('->',[newConstant('fail'),
			newAtom('writeln',[newConstant('YES')]),
			newAtom('writeln',[newConstant('NO')])]);

 q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('X'),newAtom('p',[newConstant('a'),newVariable('Y')])]),
			newAtom('copy_term',[newVariable('X'),newVariable('Z')]),
			newAtom('=',[newVariable('Z'),newAtom('p',[newVariable('A'),newConstant('b')])])]);

/* q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('X'),newAtom('p',[newConstant('a'),newVariable('Y')])]),
			newAtom('internal:copy_term',[newVariable('X'),newVariable('Z')]),
			newAtom('=',[newVariable('Z'),newAtom('p',[newVariable('A'),newConstant('b')])])]); 
*/

 q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('Y'),newVariable('X')]),
			newAtom('copy_term',[newAtom('f', [newVariable('X'),newVariable('Y')]),newVariable('F')]),
			]);
 q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('Y'),newVariable('X')]),
			newAtom('copy_term',[newAtom('f', [newVariable('X'),newVariable('Y')]),
                        newAtom('f',[newConstant('a'),newVariable('Z')])])]);			
 q[i++] = newConsPairsFromTerms([
			newAtom('copy_term',[newAtom('f', [newVariable('X'),newVariable('Y')]),
                        newAtom('f',[newConstant('a'),newVariable('Z')])]),
			newAtom('=', [newVariable('Y'),newVariable('X')])]);			
 q[i++] = newAtom('copy_term', [newAtom('f',[newVariable('X'),newVariable('X')]),
                        newAtom('f',[newConstant('a'),newVariable('Z')])]);			

 q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('Y'),newVariable('X')]),
			newAtom('internal:copy_term',[newAtom('f', [newVariable('X'),newVariable('Y')]),
                        newAtom('f',[newConstant('a'),newVariable('Z')])])]);			
 q[i++] = newConsPairsFromTerms([
			newAtom('internal:copy_term',[newAtom('f', [newVariable('X'),newVariable('Y')]),
                        newAtom('f',[newConstant('a'),newVariable('Z')])]),
			newAtom('=', [newVariable('Y'),newVariable('X')])]);			
 q[i++] = newAtom('internal:copy_term', [newAtom('f',[newVariable('X'),newVariable('X')]),
                        newAtom('f',[newConstant('a'),newVariable('Z')])]);			


 q[i++] = newAtom('internal:atom_append!',[newConstant('[]'),newConstant('a')]);
 q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('M'),newListNull()]),
			newAtom('internal:atom_append!',[newVariable('M'),newConstant('a')])]);
 q[i++] = newAtom('=',[newVariable('M'),newListNull()]);
 q[i++] = newConsPairsFromTerms([
			newAtom('=',[newVariable('M'),newAtom('p',[newVariable('X'),newConstant('b')])]),
			newAtom('=',[newVariable('N'),newAtom('p',[newConstant('a'),newVariable('Y')])]),
			newAtom('\\==',[newVariable('M'),newVariable('N')])]);

 q[i++] = newAtom('@<',[newVariable('X'),newNumber(2)]);
 q[i++] = newAtom('@>=',[newVariable('X'),newNumber(2)]);
 q[i++] = newAtom('@>',[newConstant('a'),newNumber(1)]);
 q[i++] = newAtom('@=<',[newConstant('a'),newNumber(1)]);
 q[i++] = newAtom('@<',[newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)]),
				newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)])]);
 q[i++] = newAtom('@>',[newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)]),
				newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)])]);
 q[i++] = newAtom('@=<',[newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)]),
				newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)])]);
 q[i++] = newAtom('@>=',[newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)]),
				newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)])]);

 q[i++] = newAtom('findall',[newVariable('T'),
			newAtom('member',[newVariable('T'),
				newListFromTerms([newConstant('a'),newConstant('b'),newConstant('c'),
				newNumber(1),newNumber(2),newVariable('Z')])]),
			newVariable('L')]);
 q[i++] = newAtom('findall',[newVariable('X'),
			newAtom('queens',[newNumber(4),newVariable('X')]),
			newVariable('L')]);
 q[i++] = newAtom('bagof',[newVariable('X'),
			newAtom('f',[newVariable('X'),newVariable('Y')]),newVariable('L')]);
 q[i++] = newAtom('setof',[newVariable('X'),
			newAtom('f',[newVariable('X'),newVariable('Y')]),newVariable('L')]);
 q[i++] = newAtom('assertz',[newRuleTerm(
			newAtom('p',[newVariable('X'),newVariable('Y')]),
			newConsPair(newAtom('p',[newVariable('A'),newVariable('Y')]),
						newAtom('is',[newVariable('X'),newAtom('+',[newVariable('A'),newNumber(2)])])))]);
 q[i++] = newAtom('asserta',[newAtom('p',[newNumber(4),newVariable('X')])]);
 q[i++] = newAtom('p',[newVariable('X'),newVariable('Y')]);
 q[i++] = newAtom('retract',[newAtom('p',[newVariable('X'),newVariable('Y')])]);
 q[i++] = newAtom('retract',[newRuleTerm(
			newAtom('p',[newVariable('X'),newVariable('Y')]),
			newConsPair(newAtom('p',[newVariable('A'),newVariable('Y')]),
						newAtom('is',[newVariable('X'),newAtom('+',[newVariable('A'),newNumber(2)])])))]);
 q[i++] = newAtom('abolish',[newAtom('/',[newConstant('f'),newNumber(2)])]);
 q[i++] = newAtom('internal:rule',[newRuleTerm(
			newAtom('p',[newVariable('X'),newVariable('Y')]),
			newConsPair(newAtom('p',[newVariable('A'),newVariable('Y')]),
						newAtom('is',[newVariable('X'),newAtom('+',[newVariable('A'),newNumber(2)])]))),
						newVariable('Head'),newVariable('Body')]);
 q[i++] = newAtom('clause',[newAtom('f',[newVariable('X'),newVariable('Y')]),newVariable('B')]);
 q[i++] = newAtom('internal:clause',[newAtom('f',[newVariable('X'),newVariable('Y')]),newVariable('B'),newVariable('R'),newNumber(2),newVariable('_')]);
 q[i++] = newAtom('internal:clause',[newAtom('internal:length',[newVariable('X'),newVariable('Y')]),newVariable('B'),newVariable('R'),newVariable('N'),newVariable('_')]);
 q[i++] = newAtom('internal:clause',[newAtom('p',[newVariable('X'),newVariable('Y')]),newVariable('B'),newVariable('R'),newVariable('N'),newVariable('_')]);
 q[i++] = newAtom('current_predicate',[newVariable('F')]);
 q[i++] = newAtom('internal:current_predicate',[newAtom('/',[newConstant('f'),newNumber(2)]),newVariable('L')]);
 q[i++] = newAtom('internal:current_predicate',[newAtom('/',[newVariable('X'),newNumber(2)]),newVariable('L')]);
 q[i++] = newAtom('internal:current_predicate',[newVariable('F'),newVariable('L')]);
 q[i++] = newAtom('internal:call',[newAtom('f',[newVariable('X')]),newListPair(newVariable('Y'),newListNull())]);
 q[i++] = newAtom('internal:append',[newListFromTerms([newConstant('a'),newConstant('b')]),
				newListFromTerms([newNumber(1),newNumber(2)]),newVariable('Y')]);
 q[i++] = newAtom('internal:append',[newVariable('X'),newVariable('Y'),
				newListFromTerms([newConstant('a'),newConstant('b'),newNumber(1),newNumber(2)])]);
 q[i++] = newAtom('internal:merge_sort',[newListFromTerms([
				newConstant('b'),newNumber(2),newConstant('a'),newNumber(1),newNumber(2),
				newVariable('X'),newVariable('Y'),newVariable('X'),newAtom('a',[newVariable('X'),newNumber(2)]),
				newAtom('a',[newVariable('X'),newNumber(1)])]),newVariable('Z')]);
 q[i++] = newAtom('internal:merge_sort',[newListFromTerms([
				newNumber(3),newNumber(2),newNumber(4),newNumber(1),newNumber(2)]),newVariable('Z')]);
 q[i++] = newAtom('internal:merge_sort',[newListFromTerms([
				newConstant('c'),newConstant('d'),newConstant('a'),newConstant('c'),newConstant('b')]),newVariable('Z')]);
 q[i++] = newAtom('internal:merge_sort',[newListFromTerms([
				newConstant('c'),newNumber(3),newConstant('c'),newNumber(2),newNumber(4),newConstant('d'),
				newConstant('a'),newNumber(1),newConstant('b'),newNumber(2)]),newVariable('Z')]);
 q[i++] = newAtom('internal:compare',[newVariable('X'),newNumber(2),newVariable('Z')]);
 q[i++] = newAtom('internal:compare',[newConstant('a'),newNumber(1),newVariable('Z')]);
 q[i++] = newAtom('internal:compare',[newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)]),
				newAtom('b',[newVariable('X'),newConstant('f'),newNumber(3)]),newVariable('Z')]);
 q[i++] = newAtom('plus',[newNumber(1),newNumber(2),newVariable('X')]);
 q[i++] = newAtom('internal:sumlist',[newConstant('plus'),
		newListFromTerms([newNumber(1),newNumber(2),newNumber(3)]),
		newNumber(0),newVariable('X')]);
				
 q[i++] = newAtom('throw_long',[newNumber(10)]);
 q[i++] = newAtom('throw',[newAtom('err',[newConstant('exception'),newVariable('X'),newNumber(1)])]);
 q[i++] = newConstant('halt');
 q[i++] = newAtom('halt',[newNumber(-1)]);
 q[i++] = newAtom('halt',[newConstant('a')]);
 q[i++] = newAtom('internal:catch',[
				newAtom('queens',[newNumber(4),newVariable('X')]),
				newVariable('E'),
				newVariable('P')]);
 q[i++] = newAtom('catch',[
				newAtom('queens',[newNumber(4),newVariable('X')]),
				newVariable('E'),
				newAtom('writeln',[newConstant('thrown')])]);
 q[i++] = newAtom('catch',[
				newAtom('throw_long',[newNumber(10)]),
				newVariable('E'),
				newAtom('writeln',[newConsPair(newConstant('thrown: '),newVariable('E'))])]);

 
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
 
 if (jslog_prover != null && !isProverStateDone(jslog_prover))
  jslog_ui_stop();

 //FIX: until parser is working, use builtin queries.
 query_term = jslog_premade_queries[window.document.formUI.premade_queries.selectedIndex];
    
 try
 {
  jslog_prover = newQueryProver(jslog_kb,newTermEnclosure(query_term)); 

  window.document.formUI.output.value += "?- " + jslog_toString(jslog_prover.query) + "\n";
  
  if (proveProver(jslog_prover))
  {
   window.document.formUI.output.value += jslog_toString(jslog_prover.query);
  }
  else
  {
   jslog_prover = null;
   window.document.formUI.output.value += "No";
  }
 }
 catch (err)
 {
  jslog_prover = null;
  window.document.formUI.output.value += err.toString();
 } 

 window.document.formUI.output.value += "\n";  
}

function jslog_ui_retry()
{
 if (jslog_prover != null && isProverStateWaiting(jslog_prover))
 {
  try
  {
   if (retryProver(jslog_prover))
   {
    window.document.formUI.output.value += jslog_toString(jslog_prover.query);
   }
   else
   {
    jslog_prover = null;
    window.document.formUI.output.value += "No";
   }
  } 
  catch (err)
  {
   jslog_prover = null;
   window.document.formUI.output.value += err.toString();
  } 
  window.document.formUI.output.value += "\n";
 } 
 else
  alert("Cannot retry.");
}

function jslog_ui_stop()
{
 if (jslog_prover != null)
 {
  haltProver(jslog_prover);
  jslog_prover = null;
  window.document.formUI.output.value += "stopped query.\n";
 }
}
