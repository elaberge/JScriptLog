/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_kb_* functions for Prolog KnowledgeBase
// KB* member functions for KnowledgeBase
///////////////////////////////////

// FIX: RuleSets should denote operator information (if it represents an operator).

// The KnowledgeBase (array of prolog rule clauses).
var jslog_kb = new KB();


function KB()
{var ruleset;
 var rule;

 this.rulesets = new Object();

 // true.
 {
  ruleset = new RuleSet('true',0,false);
 
  ruleset.rules.push(newRule(newConstant('true')));

  addRuleSet(this,ruleset);
 }
 // fail/0 
 {
  ruleset = new RuleSet('fail',0,false);
 
  addRuleSet(this,ruleset);
 }
 // \+(X) :- X, !, fail.
 // \+(_).
 {
  ruleset = new RuleSet('\\+',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('\\+',[newVariable('X')]),
		newConsPair(newVariable('X'),
			newConsPair(newConstant('!'),newConstant('fail'))))));
  ruleset.rules.push(newRule(newAtom('\\+',[newVariable('_')])));
 
  addRuleSet(this,ruleset);
 }
 // ;(X,_) :- X.
 // ;(_,X) :- Y.
 {
  ruleset = new RuleSet(';',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newOrPair(newVariable('X'),newVariable('_')),
		newVariable('X'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newOrPair(newVariable('_'),newVariable('X')),
		newVariable('X'))));
 
  addRuleSet(this,ruleset);
 }
 // ,(X,Y) :- X,Y.
 {
  ruleset = new RuleSet(',',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newConsPair(newVariable('X'),newVariable('Y')),
		newConsPair(newVariable('X'),newVariable('Y')))));
 
  addRuleSet(this,ruleset);
 }
 // repeat.
 // repeat :- repeat.
 {
  ruleset = new RuleSet('repeat',0,false);

  ruleset.rules.push(newRule(newConstant('repeat')));
  ruleset.rules.push(newRule(newRuleTerm(newConstant('repeat'),newConstant('repeat'))));
 
  addRuleSet(this,ruleset);
 }
 // once(X) :- X, !.
 {
  ruleset = new RuleSet('once',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('once',[newVariable('X')]),
		newConsPair(newVariable('X'),newConstant('!')))));
 
  addRuleSet(this,ruleset);
 }
 // call(X) :- X.
 {
  ruleset = new RuleSet('call',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('call',[newVariable('X')]),
		newVariable('X'))));
 
  addRuleSet(this,ruleset);
 }
 // throw/1 : throw function
 {
  ruleset = new RuleSet('throw',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('throw',[newVariable('E')]),throw_fn));
 
  addRuleSet(this,ruleset);  
 }
 // halt :- throw(0).
 {
  ruleset = new RuleSet('halt',0,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newConstant('halt'),
		newAtom('throw',[newNumber(0)]))));
 
  addRuleSet(this,ruleset);  
 }
 // halt(N) :- I is integer(N), throw(E).
 {
  ruleset = new RuleSet('halt',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('halt',[newVariable('N')]),
		newConsPair(
			newAtom('is',[newVariable('I'),newAtom('integer',[newVariable('N')])]),
			newAtom('throw',[newVariable('I')])))));
 
  addRuleSet(this,ruleset);  
 }
 
 // var/1 : isvar function
 {
  ruleset = new RuleSet('var',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('var',[newVariable('V')]),isvar_fn));
 
  addRuleSet(this,ruleset);  
 }
 // nonvar/1 : isnonvar function
 {
  ruleset = new RuleSet('nonvar',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('nonvar',[newVariable('V')]),isnonvar_fn));
 
  addRuleSet(this,ruleset);  
 }
 // atom/1 : isconstant function
 {
  ruleset = new RuleSet('atom',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('atom',[newVariable('A')]),isconstant_fn));
 
  addRuleSet(this,ruleset);  
 }
 // atomic/1 : isconstornum function
 {
  ruleset = new RuleSet('atomic',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('atomic',[newVariable('A')]),isconstornum_fn));
 
  addRuleSet(this,ruleset);  
 }
 // compound/1 : iscompound function
 {
  ruleset = new RuleSet('compound',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('compound',[newVariable('T')]),iscompound_fn));
 
  addRuleSet(this,ruleset);  
 }
 // number/1 : isnumber function
 {
  ruleset = new RuleSet('number',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('number',[newVariable('N')]),isnumber_fn));
 
  addRuleSet(this,ruleset);  
 }
 // float/1 eval function : isnumber function -- all numbers are floats.
 {
  ruleset = new RuleSet('float',1,false);

  setEvaluateFunctionForRuleSet(ruleset,positive_eval_fn);

  ruleset.rules.push(newFunctionRule(
  		newAtom('float',[newVariable('N')]),isnumber_fn));
 
  addRuleSet(this,ruleset);  
 }
 
 // !/0 : commit function
 {
  ruleset = new RuleSet('!',0,false);

  ruleset.rules.push(newTraversalRule(newConstant('!'),true_try_fn,cut_retry_fn));
 
  addRuleSet(this,ruleset);
 }
 // ->(G,T) :- call(G), !, call(T).
 {
  ruleset = new RuleSet('->',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('->',[newVariable('G'),newVariable('T')]),
		newConsPairsFromTerms([
			newAtom('call',[newVariable('G')]),
			newConstant('!'),
			newAtom('call',[newVariable('T')])]))));
 
  addRuleSet(this,ruleset);
 }
 // ->(G,T,_) :- call(G), !, call(T).
 // ->(_,_,F) :- call(F).
 {
  ruleset = new RuleSet('->',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('->',[newVariable('G'),newVariable('T'),newVariable('_')]),
		newConsPairsFromTerms([
			newAtom('call',[newVariable('G')]),
			newConstant('!'),
			newAtom('call',[newVariable('T')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('->',[newVariable('_'),newVariable('_'),newVariable('F')]),
		newAtom('call',[newVariable('F')]))));
 
  addRuleSet(this,ruleset);
 }
 // if(G,T,F) :- internal:copy_term(test(fail),V), internal:if(G,T,F).
 {
  ruleset = new RuleSet('if',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('if',[newVariable('G'),newVariable('T'),newVariable('F')]),
		newConsPairsFromTerms([
			newAtom('internal:copy_term',[newAtom('test',[newConstant('fail')]),newVariable('V')]),
			newAtom('internal:if',[newVariable('G'),newVariable('T'),newVariable('F'),newVariable('V')])]))));
 
  addRuleSet(this,ruleset);
 }
 // findall(T,G,L) :- internal:copy_term([],M), internal:findall(T,G,M), M =.. [_|L].
 {
  ruleset = new RuleSet('findall',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('findall',[newVariable('T'),newVariable('G'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('internal:copy_term',[newListNull(),newVariable('M')]),
			newAtom('internal:findall',[newVariable('T'),newVariable('G'),newVariable('M')]),
			newAtom('=..',[newVariable('M'),newListPair(newVariable('_'),newVariable('L'))])]))));
 
  addRuleSet(this,ruleset);
 }
 // bagof(T,G,L) :- internal:term_variables(T,Tv), internal:term_variables(G,Gv),
 //				internal:selectlist(internal:inlist(Tv,_),Gv,_,Dv), findall(T-Dv,G,M), 
 //				internal:bagof_results(M,Dv,L).
 {
  ruleset = new RuleSet('bagof',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('bagof',[newVariable('T'),newVariable('G'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('internal:term_variables',[newVariable('T'),newVariable('Tv')]),
			newAtom('internal:term_variables',[newVariable('G'),newVariable('Gv')]),
			newAtom('internal:selectlist',[newAtom('internal:inlist',[newVariable('Tv')]),
						newVariable('Gv'),newVariable('_'),newVariable('Dv')]),
			newAtom('findall',[newAtom('-',[newVariable('T'),newVariable('Dv')]),newVariable('G'),newVariable('M')]),
			newAtom('internal:bagof_results',[newVariable('M'),newVariable('Dv'),newVariable('L')])]))));
 
  addRuleSet(this,ruleset);
 }
 // setof(T,G,S) :- bagof(T,G,L), internal:merge_sort(L,S).
 {
  ruleset = new RuleSet('setof',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('setof',[newVariable('T'),newVariable('G'),newVariable('S')]),
		newConsPair(
			newAtom('bagof',[newVariable('T'),newVariable('G'),newVariable('L')]),
			newAtom('internal:merge_sort',[newVariable('L'),newVariable('S')])))));
 
  addRuleSet(this,ruleset);
 }
 // is/2 : eval function
 {
  ruleset = new RuleSet('is',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('is',[newVariable('X'),newVariable('E')]),is_fn));
 
  addRuleSet(this,ruleset);  
 }
 // </2 : compare function
 {
  ruleset = new RuleSet('<',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('<',[newVariable('L'),newVariable('R')]),lt_fn));
 
  addRuleSet(this,ruleset);  
 }
 // =</2 : compare function
 {
  ruleset = new RuleSet('=<',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=<',[newVariable('L'),newVariable('R')]),lte_fn));
 
  addRuleSet(this,ruleset);  
 }
 // >/2 : compare function
 {
  ruleset = new RuleSet('>',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('>',[newVariable('L'),newVariable('R')]),gt_fn));
 
  addRuleSet(this,ruleset);  
 }
 // >=/2 : compare function
 {
  ruleset = new RuleSet('>=',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('>=',[newVariable('L'),newVariable('R')]),gte_fn));
 
  addRuleSet(this,ruleset);  
 }
 // =:=/2 : compare function
 {
  ruleset = new RuleSet('=:=',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=:=',[newVariable('L'),newVariable('R')]),eq_fn));
 
  addRuleSet(this,ruleset);  
 }
 // =\=/2 : compare function
 {
  ruleset = new RuleSet('=\\=',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=\\=',[newVariable('L'),newVariable('R')]),neq_fn));
 
  addRuleSet(this,ruleset);  
 }
 // =/2 : unify function
 {
  ruleset = new RuleSet('=',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=',[newVariable('L'),newVariable('R')]),unify_fn));
 
  addRuleSet(this,ruleset);  
 }
 // \=(X,Y) :- \+(=(X,Y)).
 {
  ruleset = new RuleSet('\\=',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('\\=',[newVariable('X'),newVariable('Y')]),
		newAtom('\\+',[newAtom('=',[newVariable('X'),newVariable('Y')])]))));
 
  addRuleSet(this,ruleset);
 }
 // ==/2 : identical function
 {
  ruleset = new RuleSet('==',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('==',[newVariable('L'),newVariable('R')]),identical_fn));
 
  addRuleSet(this,ruleset);  
 }
 // \==(X,Y) :- \+(==(X,Y)).
 {
  ruleset = new RuleSet('\\==',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('\\==',[newVariable('X'),newVariable('Y')]),
		newAtom('\\+',[newAtom('==',[newVariable('X'),newVariable('Y')])]))));
 
  addRuleSet(this,ruleset);
 }
 // @</2 : compare less than function
 {
  ruleset = new RuleSet('@<',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('@<',[newVariable('L'),newVariable('R')]),compare_lt_fn));
 
  addRuleSet(this,ruleset);  
 }
 // @=</2 : compare less than equal function
 {
  ruleset = new RuleSet('@=<',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('@=<',[newVariable('L'),newVariable('R')]),compare_lte_fn));
 
  addRuleSet(this,ruleset);  
 }
 // @>/2 : compare greater than function
 {
  ruleset = new RuleSet('@>',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('@>',[newVariable('L'),newVariable('R')]),compare_gt_fn));
 
  addRuleSet(this,ruleset);  
 }
 // @>=/2 : compare greater than equal function
 {
  ruleset = new RuleSet('@>=',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('@>=',[newVariable('L'),newVariable('R')]),compare_gte_fn));
 
  addRuleSet(this,ruleset);  
 }
 // arg/3 : Nth arg term of atom
 {
  ruleset = new RuleSet('arg',3,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('arg',[newVariable('N'),newVariable('A'),newVariable('T')]),arg_fn));
 
  addRuleSet(this,ruleset);  
 }
 // =../2 : atom to list
 {
  ruleset = new RuleSet('=..',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=..',[newVariable('L'),newVariable('R')]),atom_to_list_fn));
 
  addRuleSet(this,ruleset);  
 }
 // copy_term/2 : copy term function
 {
  ruleset = new RuleSet('copy_term',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('copy_term',[newVariable('L'),newVariable('R')]),copy_term_fn));
 
  addRuleSet(this,ruleset);  
 } 
 // asserta/1
 {
  ruleset = new RuleSet('asserta',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('asserta',[newVariable('L')]),asserta_fn));
 
  addRuleSet(this,ruleset);  
 }
 // assertz/1
 {
  ruleset = new RuleSet('assertz',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('assertz',[newVariable('L')]),assertz_fn));
 
  addRuleSet(this,ruleset);  
 }
 // retract(T) :- internal:rule(T,H,B), internal:clause(H,B,R,N,0), internal:retract(R,N).
 {
  ruleset = new RuleSet('retract',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('retract',[newVariable('T')]),
		newConsPairsFromTerms([
			newAtom('internal:rule',[newVariable('T'),newVariable('H'),newVariable('B')]),
			newAtom('internal:clause',[newVariable('H'),newVariable('B'),newVariable('R'),newVariable('N'),newNumber(0)]),
			newAtom('internal:retract',[newVariable('R'),newVariable('N')])]))));
 
  addRuleSet(this,ruleset);
 }
 // clause(H,B) :- internal:clause(H,B,_,_,_).
 {
  ruleset = new RuleSet('clause',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('clause',[newVariable('H'),newVariable('B')]),
		newAtom('internal:clause',[newVariable('H'),newVariable('B'),newVariable('_'),newVariable('_'),newVariable('_')]))));
 
  addRuleSet(this,ruleset);
 }
 // abolish(F) :- internal:current_predicate(F,true,R), internal:abolish(R).
 {
  ruleset = new RuleSet('abolish',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('abolish',[newVariable('F')]),
		newConsPairsFromTerms([
			newAtom('internal:current_predicate',[newVariable('F'),newConstant('true'),newVariable('R')]),
			newAtom('internal:abolish',[newVariable('R')])]))));
 
  addRuleSet(this,ruleset);
 }
 // current_predicate(F) :- internal:current_predicate(F,_,_).
 {
  ruleset = new RuleSet('current_predicate',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('current_predicate',[newVariable('F')]),
		newAtom('internal:current_predicate',[newVariable('F'),newVariable('_'),newVariable('_')]))));
 
  addRuleSet(this,ruleset);
 }
 // write/1 : ouput function
 {
  ruleset = new RuleSet('write',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('write',[newVariable('O')]),write_fn));
 
  addRuleSet(this,ruleset);  
 }
 // nl/0 : ouput function
 {
  ruleset = new RuleSet('nl',0,false);

  ruleset.rules.push(newFunctionRule(newConstant('nl'),nl_fn));
 
  addRuleSet(this,ruleset);  
 }

 // +/1 eval function
 {
  ruleset = new RuleSet('+',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,positive_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // -/1 eval function 
 {
  ruleset = new RuleSet('-',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,negative_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // +/2 eval function
 {
  ruleset = new RuleSet('+',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,plus_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // -/2 eval function
 {
  ruleset = new RuleSet('-',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,minus_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // */2 eval function
 {
  ruleset = new RuleSet('*',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,multiply_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // //2 eval function
 {
  ruleset = new RuleSet('/',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,divide_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // ///2 eval function
 {
  ruleset = new RuleSet('//',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,intdivide_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // mod/2 eval function
 {
  ruleset = new RuleSet('mod',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,mod_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // **/2 eval function
 {
  ruleset = new RuleSet('**',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,pow_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // exp/1 eval function
 {
  ruleset = new RuleSet('exp',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,exp_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // log/1 eval function
 {
  ruleset = new RuleSet('log',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,log_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // sqrt/1 eval function
 {
  ruleset = new RuleSet('sqrt',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,sqrt_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // abs/1 eval function
 {
  ruleset = new RuleSet('abs',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,abs_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // sin/1 eval function
 {
  ruleset = new RuleSet('sin',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,sin_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // cos/1 eval function
 {
  ruleset = new RuleSet('cos',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,cos_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // tan/1 eval function
 {
  ruleset = new RuleSet('tan',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,tan_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // asin/1 eval function
 {
  ruleset = new RuleSet('asin',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,asin_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // acos/1 eval function
 {
  ruleset = new RuleSet('acos',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,acos_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // atan/1 eval function
 {
  ruleset = new RuleSet('atan',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,atan_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // atan2/2 eval function
 {
  ruleset = new RuleSet('atan2',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,atan2_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // integer/1 eval function : isinteger_fn 
 {
  ruleset = new RuleSet('integer',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,trunc_eval_fn);

  ruleset.rules.push(newFunctionRule(
  		newAtom('integer',[newVariable('N')]),isinteger_fn));
 
  addRuleSet(this,ruleset);
 }
 // float_factional_part/1 eval function.
 {
  ruleset = new RuleSet('float_fractional_part',1,false);

  setEvaluateFunctionForRuleSet(ruleset,fractional_part_eval_fn);
 
  addRuleSet(this,ruleset);  
 }
 // float_integer_part/1 eval function.
 {
  ruleset = new RuleSet('float_integer_part',1,false);

  setEvaluateFunctionForRuleSet(ruleset,trunc_eval_fn);
 
  addRuleSet(this,ruleset);  
 }
 // floor/1 eval function
 {
  ruleset = new RuleSet('floor',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,floor_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // ceiling/1 eval function
 {
  ruleset = new RuleSet('ceiling',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,ceiling_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // round/1 eval function
 {
  ruleset = new RuleSet('round',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,round_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // sign/1 eval function
 {
  ruleset = new RuleSet('sign',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,sign_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // /\/2 eval function
 {
  ruleset = new RuleSet('/\\',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,bitwise_and_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // \//2 eval function
 {
  ruleset = new RuleSet('\\/',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,bitwise_or_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // #/2 eval function
 {
  ruleset = new RuleSet('#',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,bitwise_xor_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // \\/1 eval function
 {
  ruleset = new RuleSet('\\',1,false);
  
  setEvaluateFunctionForRuleSet(ruleset,bitwise_negate_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // <</2 eval function
 {
  ruleset = new RuleSet('<<',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,bitwise_lshift_eval_fn);
   
  addRuleSet(this,ruleset);
 }
 // >>/2 eval function
 {
  ruleset = new RuleSet('>>',2,false);
  
  setEvaluateFunctionForRuleSet(ruleset,bitwise_rshift_eval_fn);
   
  addRuleSet(this,ruleset);
 }

 // internal:atom_append!/2 an atom mutate function that adds an argument
 // internal:atom_append!(A,E).  Adds E as an extra argument of A.
 {
  ruleset = new RuleSet('internal:atom_append!',2,false);
  
  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:atom_append!',[newVariable('A'),newVariable('E')]),internal_atom_append_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:atom_setarg!/3 an atom mutate function that changes an argument
 // internal:atom_setarg!(I,A,E). Set arg at index I (I in 1..N) in atom A (with N args) to E
 {
  ruleset = new RuleSet('internal:atom_setarg!',3,false);
  
  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:atom_setarg!',[newVariable('I'),newVariable('A'),newVariable('E')]),internal_atom_setarg_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:copy_term/2 copy term so that term is copied, not just the enclosures
 // internal:copy_term(T,C).  C is a copy of T.
 {
  ruleset = new RuleSet('internal:copy_term',2,false);
  
  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:copy_term',[newVariable('T'),newVariable('C')]),internal_copy_term_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:term_variables/2 return list of unbound variables in given term
 // internal:term_variables(T,V).  V is a list of variables in T.
 {
  ruleset = new RuleSet('internal:term_variables',2,false);
  
  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:term_variables',[newVariable('T'),newVariable('V')]),internal_term_variables_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:compare/3 compare two terms, and return constants '<','=', or '>'.
 {
  ruleset = new RuleSet('internal:compare',3,false);
  
  ruleset.rules.push(newFunctionRule(newAtom('internal:compare',[
				newVariable('S'),newVariable('T'),newVariable('C')]),internal_compare_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:findall(T,G,M) :- call(G), copy_term(T,U), internal:atom_append!(M,U), fail.
 // internal:findall(_,_,_) :- !.
 {
  ruleset = new RuleSet('internal:findall',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:findall',[newVariable('T'),newVariable('G'),newVariable('M')]),
		newConsPairsFromTerms([
			newAtom('call',[newVariable('G')]),
			newAtom('copy_term',[newVariable('T'),newVariable('U')]),
			newAtom('internal:atom_append!',[newVariable('M'),newVariable('U')]),
			newConstant('fail')]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:findall',[newVariable('_'),newVariable('_'),newVariable('_')]),
			newConstant('!'))));
 
  addRuleSet(this,ruleset);
 }
 // internal:bagof_results(M,Dv,L) :- M = [_-G|_], 
 //				internal:convlist(internal:bagof_match(G),M,Ls,Rs), !, 
 //				(L = Ls, Dv = G ; internal:bagof_results(Rs,Dv,L)).
 {
  ruleset = new RuleSet('internal:bagof_results',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:bagof_results',[newVariable('M'),newVariable('Dv'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('=',[newVariable('M'),
				newListPair(newAtom('-',[newVariable('_'),newVariable('G')]),newVariable('_'))]),
			newAtom('internal:convlist',[newAtom('internal:bagof_match',[newVariable('G')]),
				newVariable('M'),newVariable('Ls'),newVariable('Rs')]),
			newConstant('!'),
			newOrPair(
				newConsPair(newAtom('=',[newVariable('L'),newVariable('Ls')]),
						newAtom('=',[newVariable('Dv'),newVariable('G')])),
				newAtom('internal:bagof_results',[newVariable('Rs'),newVariable('Dv'),newVariable('L')]))]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:bagof_match(G,T-D,T) :- G == D.
 {
  ruleset = new RuleSet('internal:bagof_match',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:bagof_match',[newVariable('G'),
				newAtom('-',[newVariable('T'),newVariable('D')]),newVariable('T')]),
		newAtom('==',[newVariable('G'),newVariable('D')]))));
 
  addRuleSet(this,ruleset);
 } 
 // internal:if(G,T,_,V) :- call(G), internal:atom_setarg!(1,V,true), call(T).
 // internal:if(_,_,F,test(fail)) :- call(F).
 {
  ruleset = new RuleSet('internal:if',4,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:if',[newVariable('G'),newVariable('T'),newVariable('_'),newVariable('V')]),
		newConsPairsFromTerms([
			newAtom('call',[newVariable('G')]),
			newAtom('internal:atom_setarg!',[newNumber(1),newVariable('V'),newConstant('true')]),
			newAtom('call',[newVariable('T')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:if',[newVariable('_'),newVariable('_'),newVariable('F'),newAtom('test',[newConstant('fail')])]),
				newAtom('call',[newVariable('F')]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:selectlist(_,[],[],[]) :- !.
 // internal:selectlist(P,[L|Ls],[L|Os],Rs) :- internal:call(P,[L]), !, internal:selectlist(P,Ls,Os,Rs). 
 // internal:selectlist(P,[L|Ls],Os,[L|Rs]) :- internal:selectlist(P,Ls,Os,Rs). 
 {
  ruleset = new RuleSet('internal:selectlist',4,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:selectlist',[newVariable('_'),newListNull(),newListNull(),newListNull()]),
				newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:selectlist',[newVariable('P'),
				newListPair(newVariable('L'),newVariable('Ls')),
				newListPair(newVariable('L'),newVariable('Os')),
				newVariable('Rs')]),
		newConsPairsFromTerms([
			newAtom('internal:call',[newVariable('P'),newListPair(newVariable('L'),newListNull())]),
			newConstant('!'),
			newAtom('internal:selectlist',
				[newVariable('P'),newVariable('Ls'),newVariable('Os'),newVariable('Rs')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:selectlist',[newVariable('P'),
				newListPair(newVariable('L'),newVariable('Ls')),
				newVariable('Os'),
				newListPair(newVariable('L'),newVariable('Rs'))]),
		newConsPairsFromTerms([
			newAtom('internal:selectlist',
				[newVariable('P'),newVariable('Ls'),newVariable('Os'),newVariable('Rs')])]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:convlist(_,[],[],[]) :- !.
 // internal:convlist(P,[L|Ls],[O|Os],Rs) :- internal:call(P,[L,O]), !, internal:convlist(P,Ls,Os,Rs). 
 // internal:convlist(P,[L|Ls],Os,[L|Rs]) :- internal:convlist(P,Ls,Os,Rs). 
 {
  ruleset = new RuleSet('internal:convlist',4,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:convlist',[newVariable('_'),newListNull(),newListNull(),newListNull()]),
				newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:convlist',[newVariable('P'),
				newListPair(newVariable('L'),newVariable('Ls')),
				newListPair(newVariable('O'),newVariable('Os')),
				newVariable('Rs')]),
		newConsPairsFromTerms([
			newAtom('internal:call',[newVariable('P'),newListFromTerms([newVariable('L'),newVariable('O')])]),
			newConstant('!'),
			newAtom('internal:convlist',
				[newVariable('P'),newVariable('Ls'),newVariable('Os'),newVariable('Rs')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:convlist',[newVariable('P'),
				newListPair(newVariable('L'),newVariable('Ls')),
				newVariable('Os'),
				newListPair(newVariable('L'),newVariable('Rs'))]),
		newConsPairsFromTerms([
			newAtom('internal:convlist',
				[newVariable('P'),newVariable('Ls'),newVariable('Os'),newVariable('Rs')])]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:member(E,[E|_]).
 // internal:member(E,[_|Es]) :- internal:member(E,Es).
 {
  ruleset = new RuleSet('internal:member',2,false);

  ruleset.rules.push(newRule(
		newAtom('internal:member',[newVariable('E'),newListPair(newVariable('E'),newVariable('_'))])));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:member',[newVariable('E'),newListPair(newVariable('_'),newVariable('Es'))]),
		newAtom('internal:member',[newVariable('E'),newVariable('Es')]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:append([],L,L).
 // internal:append([E|Es],Ls,[E|Rs]) :- internal:append(Es,Ls,Rs).
 {
  ruleset = new RuleSet('internal:append',3,false);

  ruleset.rules.push(newRule(
		newAtom('internal:append',[newListNull(),newVariable('L'),newVariable('L')])));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:append',[newListPair(newVariable('E'),newVariable('Es')),newVariable('Ls'),newListPair(newVariable('E'),newVariable('Rs'))]),
		newAtom('internal:append',[newVariable('Es'),newVariable('Ls'),newVariable('Rs')]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:inlist(L,E) :- internal:member(X,L), E == X, !.
 {
  ruleset = new RuleSet('internal:inlist',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:inlist',[newVariable('L'),newVariable('E')]),
		newConsPairsFromTerms([
			newAtom('internal:member',[newVariable('X'),newVariable('L')]),
			newAtom('==',[newVariable('E'),newVariable('X')]),
			newConstant('!')]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:singleton(L,[L]).
 {
  ruleset = new RuleSet('internal:singleton',2,false);

  ruleset.rules.push(newRule(
		newAtom('internal:singleton',[newVariable('L'),newListPair(newVariable('L'),newListNull())])));
 
  addRuleSet(this,ruleset);
 }
 // internal:length([],0).
 // internal:length([L|Ls],N1) :- internal:length(Ls,N), N1 is N + 1.
 {
  ruleset = new RuleSet('internal:length',2,false);

  ruleset.rules.push(newRule(
		newAtom('internal:length',[newListNull(),newNumber(0)])));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:length',[newListPair(newVariable('L'),newVariable('Ls')),newVariable('N1')]),
		newConsPair(
			newAtom('internal:length',[newVariable('Ls'),newVariable('N')]),
			newAtom('is',[newVariable('N1'),newAtom('+',[newVariable('N'),newNumber(1)])])))));
 
  addRuleSet(this,ruleset);
 }
 // internal:call(P,As) :- P =.. Q, internal:append(Q,As,S), T =.. S, call(T).
 {
  ruleset = new RuleSet('internal:call',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:call',[newVariable('P'),newVariable('As')]),
		newConsPairsFromTerms([
			newAtom('=..',[newVariable('P'),newVariable('Q')]),
			newAtom('internal:append',[newVariable('Q'),newVariable('As'),newVariable('S')]),
			newAtom('=..',[newVariable('T'),newVariable('S')]),
			newAtom('call',[newVariable('T')])]))));
 
  addRuleSet(this,ruleset);
 } 
 // internal:current_predicate/3 enumerates available rules.
 // internal:current_predicate(F,D,R) R is a rule reference for functor F (name/arity). D=true
 // matches dynamic rules, D=fail matches static rules. Leave D unbound for any rule type.
 {
  ruleset = new RuleSet('internal:current_predicate',3,false);
  
  ruleset.rules.push(newTraversalRule(newAtom('internal:current_predicate',[
				newVariable('F'),newVariable('D'),newVariable('R')]),
				internal_current_predicate_try_fn,internal_current_predicate_retry_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:clause/5 enumerates clauses in ruleset.
 // internal:clause(H,B,R,N,X) H is head of rule, B is body of rule (true for a fact), 
 // R is a rule reference and N is the rule number for (H :- B).
 // X is the increment counter on retries (defaults to 1 - use 0 for no increment)
 {
  ruleset = new RuleSet('internal:clause',5,false);
  
  ruleset.rules.push(newTraversalRule(newAtom('internal:clause',[
				newVariable('H'),newVariable('B'),newVariable('R'),newVariable('N'),newVariable('X')]),
				internal_clause_try_fn,internal_clause_retry_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:retract/2 retract rule of given rule reference and index number.
 {
  ruleset = new RuleSet('internal:retract',2,false);
  
  ruleset.rules.push(newFunctionRule(newAtom('internal:retract',[
				newVariable('R'),newVariable('N')]),internal_retract_fn));
   
  addRuleSet(this,ruleset);
 }
 // internal:abolish(R) :- internal:clause(_,_,R,N,0), internal:retract(R,N), fail.
 // internal:abolish(_).
 {
  ruleset = new RuleSet('internal:abolish',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:abolish',[newVariable('R')]),
		newConsPairsFromTerms([
			newAtom('internal:clause',[newVariable('_'),newVariable('_'),newVariable('R'),newVariable('N'),newNumber(0)]),
			newAtom('internal:retract',[newVariable('R'),newVariable('N')]),
			newConstant('fail')]))));
  ruleset.rules.push(newRule(newAtom('internal:abolish',[newVariable('_')])));
 
  addRuleSet(this,ruleset);
 } 
 // internal:rule(:-(H,B),H,B) :- !.
 // internal:rule(H,H,true) :- !.
 {
  ruleset = new RuleSet('internal:rule',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:rule',[newRuleTerm(newVariable('H'),newVariable('B')),newVariable('H'),newVariable('B')]),
		newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:rule',[newVariable('H'),newVariable('H'),newConstant('true')]),
		newConstant('!'))));
 
  addRuleSet(this,ruleset);
 }
 // internal:merge_sort(L,S) :- internal:convlist(internal:singleton,L,M,[]), internal:merge_lists(M,N,S).
 {
  ruleset = new RuleSet('internal:merge_sort',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_sort',[newVariable('L'),newVariable('S')]),
		newConsPairsFromTerms([
			newAtom('internal:convlist',[newConstant('internal:singleton'),newVariable('L'),newVariable('M'),newListNull()]),
			newAtom('internal:merge_lists',[newVariable('M'),newVariable('S')])]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:merge_lists([],[]) :- !.
 // internal:merge_lists([L],L) :- !.
 // internal:merge_lists(L,S) :- internal:merge_all_pairs(L,M), internal:merge_lists(M,S).
 {
  ruleset = new RuleSet('internal:merge_lists',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_lists',[newListNull(),newListNull()]),
		newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_lists',[newListPair(newVariable('L'),newListNull()),newVariable('L')]),
		newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_lists',[newVariable('L'),newVariable('S')]),
		newConsPairsFromTerms([
			newAtom('internal:merge_all_pairs',[newVariable('L'),newVariable('M')]),
			newAtom('internal:merge_lists',[newVariable('M'),newVariable('S')])]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:merge_all_pairs([],[]) :- !.
 // internal:merge_all_pairs([L],[L]) :- !.
 // internal:merge_all_pairs([L1,L2|Ls],[S|Ss]) :- internal:merge_pair(L1,L2,S), 
 //				internal:merge_all_pairs(Ls,Ss).
 {
  ruleset = new RuleSet('internal:merge_all_pairs',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_all_pairs',[newListNull(),newListNull()]),
		newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_all_pairs',[newListPair(newVariable('L'),newListNull()),
				newListPair(newVariable('L'),newListNull())]),
		newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_all_pairs',[
				newListPair(newVariable('L1'),newListPair(newVariable('L2'),newVariable('Ls'))),
				newListPair(newVariable('S'),newVariable('Ss'))]),
		newConsPairsFromTerms([
			newAtom('internal:merge_pair',[newVariable('L1'),newVariable('L2'),newVariable('S')]),
			newAtom('internal:merge_all_pairs',[newVariable('Ls'),newVariable('Ss')])]))));
 
  addRuleSet(this,ruleset);
 }
 // internal:merge_pair([],L,L) :- !.
 // internal:merge_pair(L,[],L) :- !.
 // internal:merge_pair([L1|L1s],[L2|L2s],[L1|Ls]) :- L1 == L2, !, internal:merge_pair(L1s,L2s,Ls).
 // internal:merge_pair([L1|L1s],[L2|L2s],[L1|Ls]) :- L1 @< L2, !, internal:merge_pair(L1s,[L2|L2s],Ls).
 // internal:merge_pair([L1|L1s],[L2|L2s],[L2|Ls]) :- !, internal:merge_pair([L1|L1s],L2s,Ls).
 {
  ruleset = new RuleSet('internal:merge_pair',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_pair',[newListNull(),newVariable('L'),newVariable('L')]),
		newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_pair',[newVariable('L'),newListNull(),newVariable('L')]),
		newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_pair',[
				newListPair(newVariable('L1'),newVariable('L1s')),
				newListPair(newVariable('L2'),newVariable('L2s')),
				newListPair(newVariable('L1'),newVariable('Ls'))]),
		newConsPairsFromTerms([
			newAtom('==',[newVariable('L1'),newVariable('L2')]),
			newConstant('!'),
			newAtom('internal:merge_pair',[newVariable('L1s'),newVariable('L2s'),newVariable('Ls')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_pair',[
				newListPair(newVariable('L1'),newVariable('L1s')),
				newListPair(newVariable('L2'),newVariable('L2s')),
				newListPair(newVariable('L1'),newVariable('Ls'))]),
		newConsPairsFromTerms([
			newAtom('@<',[newVariable('L1'),newVariable('L2')]),
			newConstant('!'),
			newAtom('internal:merge_pair',[newVariable('L1s'),
				newListPair(newVariable('L2'),newVariable('L2s')),newVariable('Ls')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_pair',[
				newListPair(newVariable('L1'),newVariable('L1s')),
				newListPair(newVariable('L2'),newVariable('L2s')),
				newListPair(newVariable('L2'),newVariable('Ls'))]),
		newConsPairsFromTerms([
			newConstant('!'),
			newAtom('internal:merge_pair',[newListPair(newVariable('L1'),newVariable('L1s')),
				newVariable('L2s'),newVariable('Ls')])]))));
 
  addRuleSet(this,ruleset);
 }

 return this;
}

function RuleSet(name,arity,dynamic)
{
 this.name = name;
 this.arity = arity;
 this.dynamic = dynamic;
 this.rules = new Array();
 
 return this;
}

function Rule(name,arity,enclosure,head)
{
 this.name = name;
 this.arity = arity;
 this.enclosure = enclosure;
 this.head = head;
 this.body = new Array();

 return this;
}

function newRule(term)
{var encl = newTermEnclosure(term);
 var rule;
  
 if (isRuleTerm(term))
 {var t = term.children[0];

  if (!isAtom(t))
   throw newErrorException("Rule LHS must be atom.");
  
  rule = new Rule(t.name,t.children.length,encl.enclosure,t);
  rule.body = getTermArrayFromBinaryTerm(term.children[1],isConsPair);
  return rule;
 }
 else if (isAtom(term))
 {
  rule = new Rule(term.name,term.children.length,encl.enclosure,encl.term);
  return rule;
 }
 else
  throw newErrorException("Rule LHS must be atom.");
}

function newFunctionRule(term,fn)
{var encl = newTermEnclosure(term);
 var rule;
  
 if (!isAtom(term))
  throw newErrorException("Rule LHS must be atom.");
 
 rule = new Rule(term.name,term.children.length,encl.enclosure,encl.term);
 rule.body = null;
 rule.fn = fn;

 return rule;
}

function newTraversalRule(term,try_fn,retry_fn)
{var encl = newTermEnclosure(term);
 var rule;
  
 if (!isAtom(term))
  throw newErrorException("Rule LHS must be atom.");
 
 rule = new Rule(term.name,term.children.length,encl.enclosure,encl.term);
 rule.body = null;
 rule.try_fn = try_fn;
 rule.retry_fn = retry_fn;
 
 return rule;
}

function newRuleBodyArrayEnclosure(enclosure,rule)
{
 if (rule.body != null)
 {
  return new ArrayEnclosure(enclosure,rule.body);
 }
 else
 {var ae = new ArrayEnclosure(enclosure,null);
 
  ae.fn = rule.fn;
  ae.try_fn = rule.try_fn;
  ae.retry_fn = rule.retry_fn;
  
  return ae;
 } 
}

///////////////////////////////////
// * KB / RuleSet / Rule utility functions
///////////////////////////////////

// Add ruleset to kb.  This must occur before attempting to add the corresponding rules.
function addRuleSet(kb,ruleset)
{
 kb.rulesets[getRuleNameArity(ruleset)] = ruleset;
}

// Add rule to kb.  The corresponding RuleSet to rule must already exist in kb.
// If append is true, rule is appended at the end of the ruleset, otherwise
// it is prepended to the beginning. 
function addRule(kb,rule,append)
{var ruleset;

 if ((ruleset = kb.rulesets[getRuleNameArity(rule)]) == null)
  throw newErrorException("Must declare rule dynamic to add: "+getRuleNameArity(rule));
 
 if (append)
  ruleset.rules.push(rule);
 else
  ruleset.rules.unshift(rule);
}

// Remove rule at index from ruleset.  
function removeRuleFromRuleSet(ruleset,index)
{
 if (!isDynamicRuleSet(ruleset))
  throw newErrorException("Must declare rule dynamic to remove: "+getRuleNameArity(ruleset));
 
 ruleset.rules.splice(index,1);
}

// Get ruleset used to prove term.
function getRuleSet(kb,term)
{
 return kb.rulesets[getTermNameArity(term)];
}

// Get ruleset for given name and arity.
function getRuleSetFromNameArity(kb,name,arity)
{
 return kb.rulesets[getTermNameArityFromNameArity(name,arity)];
}

function getRuleNameArityFromTerm(term)
{
 if (isRuleTerm(term))
  return getTermNameArity(term.children[0]);
 else
  return getTermNameArity(term);
}

function getRuleNameArity(rule)
{
 return (rule.name.toString()+"/"+rule.arity.toString());
}

// return the enclosure array for unifying rule.head with encl
// returns null if unification fails.
// binding is an array, updated with the unification bindings if succeeds.
function getUnifiedRuleEnclosure(rule,encl,binding)
{var head_encl = newBlankEnclosure(rule.enclosure.length,rule.head);

 if (jslog_unify(head_encl,encl,binding))
  return head_encl.enclosure;

 return null;
}

function setEvaluateFunctionForRuleSet(ruleset,eval_fn)
{
 ruleset.eval_fn = eval_fn;

 return ruleset;
}

function isDynamicRuleSet(ruleset)
{
 return (ruleset == undefined || ruleset.dynamic);
}

