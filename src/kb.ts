/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.

    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

import {
  abs_eval_fn, acos_eval_fn, arg_fn, asin_eval_fn, asserta_fn, assertz_fn, atan2_eval_fn,
  atan_eval_fn, atom_chars_fn, atom_length_fn, atom_to_list_fn, bitwise_and_eval_fn,
  bitwise_lshift_eval_fn, bitwise_negate_eval_fn, bitwise_or_eval_fn, bitwise_rshift_eval_fn,
  bitwise_xor_eval_fn, ceiling_eval_fn, char_code_fn, compare_gt_fn, compare_gte_fn, compare_lt_fn,
  compare_lte_fn, copy_term_fn, cos_eval_fn, cut_retry_fn, cut_try_fn, divide_eval_fn, eq_fn,
  exp_eval_fn, floor_eval_fn, fractional_part_eval_fn, gt_fn, gte_fn, identical_fn,
  intdivide_eval_fn, internal_atom_append_fn, internal_atom_setarg_fn, internal_catch_retry_fn,
  internal_catch_try_fn, internal_catch_undo_fn, internal_clause_retry_fn, internal_clause_try_fn,
  internal_clause_undo_fn, internal_compare_fn, internal_copy_term_fn, internal_current_op_retry_fn,
  internal_current_op_try_fn, internal_current_predicate_fn, internal_equivalent_fn,
  internal_nequivalent_fn, internal_number_atom_fn, internal_retract_fn, internal_term_variables_fn,
  is_fn, iscompound_fn, isconstant_fn, isconstornum_fn, isinteger_fn, isnonvar_fn,
  isnumber_fn, isvar_fn, log_eval_fn, lt_fn, lte_fn, minus_eval_fn, mod_eval_fn, multiply_eval_fn,
  negative_eval_fn, neq_fn, nl_fn, plus_eval_fn, positive_eval_fn, pow_eval_fn, round_eval_fn,
  sign_eval_fn, sin_eval_fn, sqrt_eval_fn, tan_eval_fn, throw_fn, trunc_eval_fn,
  unify_fn, unify_with_occurs_check_fn, write_fn
} from "./builtins";
import {
  ArrayEnclosure,
  newBlankEnclosure, newErrorException, newTermEnclosure
} from "./enclosures";
import {
  TYPE_ATOM_GOAL, TYPE_VARIABLE_GOAL,
  isAtomGoal, isVariableGoal, newAtomGoal, newAtomGoalFromRuleSet, newVariableGoal
} from "./goals";
import {
  getTermNameArity, getTermNameArityFromNameArity, isAtom, isConsPair, isVariable,
  newAtom, newConsPair, newConsPairsFromTerms, newConstant, newListNull, newListPair,
  newNumber, newVariable, getTermArrayFromBinaryTerm, isRuleTerm, newListFromTerms,
  newOrPair, newOrPairsFromTerms, newRuleTerm
} from "./types";
import {
  jslog_unify, jslog_unify_with_occurs_check
} from "./unify";

///////////////////////////////////
// KB* member functions for KnowledgeBase
///////////////////////////////////

var KB_PHASE_CONSULT = 1;
var KB_PHASE_READY = 2;

// note: preservation of order is important!
// type < OP_TYPE_FX is arity 2, type >= OP_TYPE_FX is arity 1
export var OP_TYPE_XFX = 1;
export var OP_TYPE_XFY = 2;
export var OP_TYPE_YFX = 3;
export var OP_TYPE_FX = 4;
export var OP_TYPE_FY = 5;
export var OP_TYPE_XF = 6;
export var OP_TYPE_YF = 7;


export class KB {
  rulesets = new Object();
  phase = KB_PHASE_READY;
}

export function newKB()
{var ruleset;
 var rule;
 var kb = new KB();

 kb.phase = KB_PHASE_CONSULT;

 // true.
 {
  ruleset = new RuleSet('true',0,false);

  ruleset.rules.push(newRule(newConstant('true')));

  addRuleSet(kb,ruleset);
 }
 // fail/0
 {
  ruleset = new RuleSet('fail',0,false);

  addRuleSet(kb,ruleset);
 }
 // :-/2 and :-/1 : entry exists to establish op precedence
 {
  ruleset = new RuleSet(':-',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,1200);

  addRuleSet(kb,ruleset);

  ruleset = new RuleSet(':-',1,false);
  setOperatorInfo(ruleset,OP_TYPE_FX,1200);

  addRuleSet(kb,ruleset);
 }
 // \+(X) :- X, !, fail.
 // \+(_).
 {
  ruleset = new RuleSet('\\+',1,false);
  setOperatorInfo(ruleset,OP_TYPE_FY,900);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('\\+',[newVariable('X')]),
		newConsPair(newVariable('X'),
			newConsPair(newConstant('!'),newConstant('fail'))))));
  ruleset.rules.push(newRule(newAtom('\\+',[newVariable('_')])));

  addRuleSet(kb,ruleset);
 }
 // ;(X,_) :- X.
 // ;(_,X) :- Y.
 {
  ruleset = new RuleSet(';',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFY,1100);

  ruleset.rules.push(newRule(newRuleTerm(
		newOrPair(newVariable('X'),newVariable('_')),
		newVariable('X'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newOrPair(newVariable('_'),newVariable('X')),
		newVariable('X'))));

  addRuleSet(kb,ruleset);
 }
 // ,(X,Y) :- X,Y.
 {
  ruleset = new RuleSet(',',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFY,1000);

  ruleset.rules.push(newRule(newRuleTerm(
		newConsPair(newVariable('X'),newVariable('Y')),
		newConsPair(newVariable('X'),newVariable('Y')))));

  addRuleSet(kb,ruleset);
 }
 // repeat.
 // repeat :- repeat.
 {
  ruleset = new RuleSet('repeat',0,false);

  ruleset.rules.push(newRule(newConstant('repeat')));
  ruleset.rules.push(newRule(newRuleTerm(newConstant('repeat'),newConstant('repeat'))));

  addRuleSet(kb,ruleset);
 }
 // once(X) :- X, !.
 {
  ruleset = new RuleSet('once',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('once',[newVariable('X')]),
		newConsPair(newVariable('X'),newConstant('!')))));

  addRuleSet(kb,ruleset);
 }
 // call(X) :- X.
 {
  ruleset = new RuleSet('call',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('call',[newVariable('X')]),
		newVariable('X'))));

  addRuleSet(kb,ruleset);
 }
  // catch(G,E,H) :- internal:catch(G,E,P), (P==true;P==fail,call(H)).
 {
  ruleset = new RuleSet('catch',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('catch',[newVariable('G'),newVariable('E'),newVariable('H')]),
		newConsPairsFromTerms([
			newAtom('internal:catch',[newVariable('G'),newVariable('E'),newVariable('P')]),
			newOrPair(newAtom('==',[newVariable('P'),newConstant('true')]),
				newConsPair(newAtom('==',[newVariable('P'),newConstant('fail')]),
					newAtom('call',[newVariable('H')])))]))));

  addRuleSet(kb,ruleset);
 }
 // throw/1 : throw function
 {
  ruleset = new RuleSet('throw',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('throw',[newVariable('E')]),throw_fn));

  addRuleSet(kb,ruleset);
 }
 // halt :- throw(0).
 {
  ruleset = new RuleSet('halt',0,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newConstant('halt'),
		newAtom('throw',[newNumber(0)]))));

  addRuleSet(kb,ruleset);
 }
 // halt(N) :- I is integer(N), throw(E).
 {
  ruleset = new RuleSet('halt',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('halt',[newVariable('N')]),
		newConsPair(
			newAtom('is',[newVariable('I'),newAtom('integer',[newVariable('N')])]),
			newAtom('throw',[newVariable('I')])))));

  addRuleSet(kb,ruleset);
 }

 // var/1 : isvar function
 {
  ruleset = new RuleSet('var',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('var',[newVariable('V')]),isvar_fn));

  addRuleSet(kb,ruleset);
 }
 // nonvar/1 : isnonvar function
 {
  ruleset = new RuleSet('nonvar',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('nonvar',[newVariable('V')]),isnonvar_fn));

  addRuleSet(kb,ruleset);
 }
 // atom/1 : isconstant function
 {
  ruleset = new RuleSet('atom',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('atom',[newVariable('A')]),isconstant_fn));

  addRuleSet(kb,ruleset);
 }
 // atomic/1 : isconstornum function
 {
  ruleset = new RuleSet('atomic',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('atomic',[newVariable('A')]),isconstornum_fn));

  addRuleSet(kb,ruleset);
 }
 // compound/1 : iscompound function
 {
  ruleset = new RuleSet('compound',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('compound',[newVariable('T')]),iscompound_fn));

  addRuleSet(kb,ruleset);
 }
 // number/1 : isnumber function
 {
  ruleset = new RuleSet('number',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('number',[newVariable('N')]),isnumber_fn));

  addRuleSet(kb,ruleset);
 }
 // float/1 eval function : isnumber function -- all numbers are floats.
 {
  ruleset = new RuleSet('float',1,false);

  setEvaluateFunctionForRuleSet(ruleset,positive_eval_fn);

  ruleset.rules.push(newFunctionRule(
  		newAtom('float',[newVariable('N')]),isnumber_fn));

  addRuleSet(kb,ruleset);
 }

 // !/0 : commit function
 {
  ruleset = new RuleSet('!',0,false);

  ruleset.rules.push(newTraversalRule(newConstant('!'),cut_try_fn,cut_retry_fn,null));

  addRuleSet(kb,ruleset);
 }
 // ->(G,T) :- call(G), !, call(T).
 {
  ruleset = new RuleSet('->',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFY,1050);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('->',[newVariable('G'),newVariable('T')]),
		newConsPairsFromTerms([
			newAtom('call',[newVariable('G')]),
			newConstant('!'),
			newAtom('call',[newVariable('T')])]))));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }
 // if(G,T,F) :- internal:copy_term(test(fail),V), internal:if(G,T,F).
 {
  ruleset = new RuleSet('if',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('if',[newVariable('G'),newVariable('T'),newVariable('F')]),
		newConsPairsFromTerms([
			newAtom('internal:copy_term',[newAtom('test',[newConstant('fail')]),newVariable('V')]),
			newAtom('internal:if',[newVariable('G'),newVariable('T'),newVariable('F'),newVariable('V')])]))));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }
 // bagof(T,G,L) :- internal:term_split_existential(G,E,G2), internal:term_variables((T,E),TEv),
 //				internal:term_variables(G,Gv), internal:selectlist(internal:inlist(TEv,_),Gv,_,Dv),
 //				findall(T-Dv,G2,M), internal:bagof_results(M,Dv,L).
 {
  ruleset = new RuleSet('bagof',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('bagof',[newVariable('T'),newVariable('G'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('internal:term_split_existential',[newVariable('G'),newVariable('E'),newVariable('G2')]),
			newAtom('internal:term_variables',[newConsPair(newVariable('T'),newVariable('E')),newVariable('TEv')]),
			newAtom('internal:term_variables',[newVariable('G'),newVariable('Gv')]),
			newAtom('internal:selectlist',[newAtom('internal:inlist',[newVariable('TEv')]),
						newVariable('Gv'),newVariable('_'),newVariable('Dv')]),
			newAtom('findall',[newAtom('-',[newVariable('T'),newVariable('Dv')]),newVariable('G2'),newVariable('M')]),
			newAtom('internal:bagof_results',[newVariable('M'),newVariable('Dv'),newVariable('L')])]))));

  addRuleSet(kb,ruleset);
 }
 // setof(T,G,S) :- bagof(T,G,L), internal:merge_sort(L,S).
 {
  ruleset = new RuleSet('setof',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('setof',[newVariable('T'),newVariable('G'),newVariable('S')]),
		newConsPair(
			newAtom('bagof',[newVariable('T'),newVariable('G'),newVariable('L')]),
			newAtom('internal:merge_sort',[newVariable('L'),newVariable('S')])))));

  addRuleSet(kb,ruleset);
 }
 // is/2 : eval function
 {
  ruleset = new RuleSet('is',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('is',[newVariable('X'),newVariable('E')]),is_fn));

  addRuleSet(kb,ruleset);
 }
 // </2 : compare function
 {
  ruleset = new RuleSet('<',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('<',[newVariable('L'),newVariable('R')]),lt_fn));

  addRuleSet(kb,ruleset);
 }
 // =</2 : compare function
 {
  ruleset = new RuleSet('=<',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=<',[newVariable('L'),newVariable('R')]),lte_fn));

  addRuleSet(kb,ruleset);
 }
 // >/2 : compare function
 {
  ruleset = new RuleSet('>',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('>',[newVariable('L'),newVariable('R')]),gt_fn));

  addRuleSet(kb,ruleset);
 }
 // >=/2 : compare function
 {
  ruleset = new RuleSet('>=',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('>=',[newVariable('L'),newVariable('R')]),gte_fn));

  addRuleSet(kb,ruleset);
 }
 // =:=/2 : compare function
 {
  ruleset = new RuleSet('=:=',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=:=',[newVariable('L'),newVariable('R')]),eq_fn));

  addRuleSet(kb,ruleset);
 }
 // =\=/2 : compare function
 {
  ruleset = new RuleSet('=\\=',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=\\=',[newVariable('L'),newVariable('R')]),neq_fn));

  addRuleSet(kb,ruleset);
 }
 // =/2 : unify function
 {
  ruleset = new RuleSet('=',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=',[newVariable('L'),newVariable('R')]),unify_fn));

  addRuleSet(kb,ruleset);
 }
 // \=(X,Y) :- \+(=(X,Y)).
 {
  ruleset = new RuleSet('\\=',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('\\=',[newVariable('X'),newVariable('Y')]),
		newAtom('\\+',[newAtom('=',[newVariable('X'),newVariable('Y')])]))));

  addRuleSet(kb,ruleset);
 }
 // unify_with_occurs_check/2 : unify with occurs check function
 {
  ruleset = new RuleSet('unify_with_occurs_check',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('unify_with_occurs_check',[newVariable('L'),newVariable('R')]),unify_with_occurs_check_fn));

  addRuleSet(kb,ruleset);
 }
 // ==/2 : identical function
 {
  ruleset = new RuleSet('==',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('==',[newVariable('L'),newVariable('R')]),identical_fn));

  addRuleSet(kb,ruleset);
 }
 // \==(X,Y) :- \+(==(X,Y)).
 {
  ruleset = new RuleSet('\\==',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('\\==',[newVariable('X'),newVariable('Y')]),
		newAtom('\\+',[newAtom('==',[newVariable('X'),newVariable('Y')])]))));

  addRuleSet(kb,ruleset);
 }
 // @</2 : compare less than function
 {
  ruleset = new RuleSet('@<',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('@<',[newVariable('L'),newVariable('R')]),compare_lt_fn));

  addRuleSet(kb,ruleset);
 }
 // @=</2 : compare less than equal function
 {
  ruleset = new RuleSet('@=<',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('@=<',[newVariable('L'),newVariable('R')]),compare_lte_fn));

  addRuleSet(kb,ruleset);
 }
 // @>/2 : compare greater than function
 {
  ruleset = new RuleSet('@>',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('@>',[newVariable('L'),newVariable('R')]),compare_gt_fn));

  addRuleSet(kb,ruleset);
 }
 // @>=/2 : compare greater than equal function
 {
  ruleset = new RuleSet('@>=',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('@>=',[newVariable('L'),newVariable('R')]),compare_gte_fn));

  addRuleSet(kb,ruleset);
 }
 // arg/3 : Nth arg term of atom
 {
  ruleset = new RuleSet('arg',3,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('arg',[newVariable('N'),newVariable('A'),newVariable('T')]),arg_fn));

  addRuleSet(kb,ruleset);
 }
 // =../2 : atom to list
 {
  ruleset = new RuleSet('=..',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,700);

  ruleset.rules.push(newFunctionRule(
  		newAtom('=..',[newVariable('L'),newVariable('R')]),atom_to_list_fn));

  addRuleSet(kb,ruleset);
 }
 // atom_length/2 : atom name length
 {
  ruleset = new RuleSet('atom_length',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('atom_length',[newVariable('A'),newVariable('L')]),atom_length_fn));

  addRuleSet(kb,ruleset);
 }
 // char_code/2 : character codes
 {
  ruleset = new RuleSet('char_code',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('char_code',[newVariable('C'),newVariable('N')]),char_code_fn));

  addRuleSet(kb,ruleset);
 }
 // atom_chars/2 : constant atom to characters converter
 {
  ruleset = new RuleSet('atom_chars',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('atom_chars',[newVariable('A'),newVariable('C')]),atom_chars_fn));

  addRuleSet(kb,ruleset);
 }
 // number_chars(N,C) :- \+ var(N), !, internal:number_atom(N,A), atom_chars(A,C).
 // number_chars(N,C) :- atom_chars(A,C), internal:number_atom(N,A).
 {
  ruleset = new RuleSet('number_chars',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('number_chars',[newVariable('N'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('\\+',[newAtom('var',[newVariable('N')])]),
			newConstant('!'),
			newAtom('internal:number_atom',[newVariable('N'),newVariable('A')]),
			newAtom('atom_chars',[newVariable('A'),newVariable('C')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('number_chars',[newVariable('N'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('atom_chars',[newVariable('A'),newVariable('C')]),
			newAtom('internal:number_atom',[newVariable('N'),newVariable('A')])]))));

  addRuleSet(kb,ruleset);
 }
 // atom_codes(A,C) :- \+ var(A), !, atom_chars(A,Z), internal:convlist(char_code,Z,C,[]).
 // atom_codes(A,C) :- \+ var(C), !, internal:convlist(internal:code_char,C,Z,[]), atom_chars(A,Z).
 {
  ruleset = new RuleSet('atom_codes',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('atom_codes',[newVariable('A'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('\\+',[newAtom('var',[newVariable('A')])]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('A'),newVariable('Z')]),
			newAtom('internal:convlist',[newConstant('char_code'),newVariable('Z'),newVariable('C'),newListNull()])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('atom_codes',[newVariable('A'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('\\+',[newAtom('var',[newVariable('C')])]),
			newConstant('!'),
			newAtom('internal:convlist',[newConstant('internal:code_char'),newVariable('C'),newVariable('Z'),newListNull()]),
			newAtom('atom_chars',[newVariable('A'),newVariable('Z')])]))));

  addRuleSet(kb,ruleset);
 }
 // number_codes(A,C) :- \+ var(A), !, number_chars(A,Z), internal:convlist(char_code,Z,C,[]).
 // number_codes(A,C) :- \+ var(C), !, internal:convlist(internal:code_char,C,Z,[]), number_chars(A,Z).
 {
  ruleset = new RuleSet('number_codes',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('number_codes',[newVariable('A'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('\\+',[newAtom('var',[newVariable('A')])]),
			newConstant('!'),
			newAtom('number_chars',[newVariable('A'),newVariable('Z')]),
			newAtom('internal:convlist',[newConstant('char_code'),newVariable('Z'),newVariable('C'),newListNull()])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('number_codes',[newVariable('A'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('\\+',[newAtom('var',[newVariable('C')])]),
			newConstant('!'),
			newAtom('internal:convlist',[newConstant('internal:code_char'),newVariable('C'),newVariable('Z'),newListNull()]),
			newAtom('number_chars',[newVariable('A'),newVariable('Z')])]))));

  addRuleSet(kb,ruleset);
 }
 // atom_concat(A,B,C) :- \+ var(A), \+ var(B), !, atom_chars(A,X), atom_chars(B,Y), internal:append(X,Y,Z), atom_chars(C,Z).
 // atom_concat(A,B,C) :- \+ var(B), \+ var(C), !, atom_chars(B,Y), atom_chars(C,Z), internal:append(X,Y,Z), atom_chars(A,X).
 // atom_concat(A,B,C) :- \+ var(A), \+ var(C), !, atom_chars(A,X), atom_chars(C,Z), internal:append(X,Y,Z), atom_chars(B,Y).
 // atom_concat(A,B,C) :- \+ var(C), !, atom_chars(C,Z), internal:append(X,Y,Z), atom_chars(A,X), atom_chars(B,Y).
 {
  ruleset = new RuleSet('atom_concat',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('atom_concat',[newVariable('A'),newVariable('B'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('\\+',[newAtom('var',[newVariable('A')])]),
			newAtom('\\+',[newAtom('var',[newVariable('B')])]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('A'),newVariable('X')]),
			newAtom('atom_chars',[newVariable('B'),newVariable('Y')]),
			newAtom('internal:append',[newVariable('X'),newVariable('Y'),newVariable('Z')]),
			newAtom('atom_chars',[newVariable('C'),newVariable('Z')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('atom_concat',[newVariable('A'),newVariable('B'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('\\+',[newAtom('var',[newVariable('B')])]),
			newAtom('\\+',[newAtom('var',[newVariable('C')])]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('B'),newVariable('Y')]),
			newAtom('atom_chars',[newVariable('C'),newVariable('Z')]),
			newAtom('internal:append',[newVariable('X'),newVariable('Y'),newVariable('Z')]),
			newAtom('atom_chars',[newVariable('A'),newVariable('X')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('atom_concat',[newVariable('A'),newVariable('B'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('\\+',[newAtom('var',[newVariable('A')])]),
			newAtom('\\+',[newAtom('var',[newVariable('C')])]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('A'),newVariable('X')]),
			newAtom('atom_chars',[newVariable('C'),newVariable('Z')]),
			newAtom('internal:append',[newVariable('X'),newVariable('Y'),newVariable('Z')]),
			newAtom('atom_chars',[newVariable('B'),newVariable('Y')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('atom_concat',[newVariable('A'),newVariable('B'),newVariable('C')]),
		newConsPairsFromTerms([
			newAtom('\\+',[newAtom('var',[newVariable('C')])]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('C'),newVariable('Z')]),
			newAtom('internal:append',[newVariable('X'),newVariable('Y'),newVariable('Z')]),
			newAtom('atom_chars',[newVariable('A'),newVariable('X')]),
			newAtom('atom_chars',[newVariable('B'),newVariable('Y')])]))));

  addRuleSet(kb,ruleset);
 }
 // sub_atom(A,B,S,E,Z) :- atom(A), !, atom_concat(X,Y,A), atom_concat(Z,W,Y),
 //							atom_length(Z,S), atom_length(X,B), atom_length(W,E).
 {
  ruleset = new RuleSet('sub_atom',5,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('sub_atom',[newVariable('A'),newVariable('B'),newVariable('S'),newVariable('E'),newVariable('Z')]),
		newConsPairsFromTerms([
			newAtom('atom',[newVariable('A')]),
			newConstant('!'),
			newAtom('atom_concat',[newVariable('X'),newVariable('Y'),newVariable('A')]),
			newAtom('atom_concat',[newVariable('Z'),newVariable('W'),newVariable('Y')]),
			newAtom('atom_length',[newVariable('Z'),newVariable('S')]),
			newAtom('atom_length',[newVariable('X'),newVariable('B')]),
			newAtom('atom_length',[newVariable('W'),newVariable('E')])]))));

  addRuleSet(kb,ruleset);
 }

 // copy_term/2 : copy term function
 {
  ruleset = new RuleSet('copy_term',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('copy_term',[newVariable('L'),newVariable('R')]),copy_term_fn));

  addRuleSet(kb,ruleset);
 }
 // asserta/1
 {
  ruleset = new RuleSet('asserta',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('asserta',[newVariable('L')]),asserta_fn));

  addRuleSet(kb,ruleset);
 }
 // assertz/1
 {
  ruleset = new RuleSet('assertz',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('assertz',[newVariable('L')]),assertz_fn));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }
 // clause(H,B) :- internal:clause(H,B,_,_,_).
 {
  ruleset = new RuleSet('clause',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('clause',[newVariable('H'),newVariable('B')]),
		newAtom('internal:clause',[newVariable('H'),newVariable('B'),newVariable('_'),newVariable('_'),newVariable('_')]))));

  addRuleSet(kb,ruleset);
 }
 // current_op(P,T,N) :- internal:current_op(N,T,P,_).
 {
  ruleset = new RuleSet('current_op',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('current_op',[newVariable('P'),newVariable('T'),newVariable('N')]),
		newAtom('internal:current_op',[newVariable('N'),newVariable('T'),newVariable('P'),newVariable('_')]))));

  addRuleSet(kb,ruleset);
 }
 // abolish(F) :- internal:current_predicate(F,L), internal:member(rs(F,true,R),L), internal:abolish(R).
 {
  ruleset = new RuleSet('abolish',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('abolish',[newVariable('F')]),
		newConsPairsFromTerms([
			newAtom('internal:current_predicate',[newVariable('F'),newVariable('L')]),
			newAtom('internal:member',[
				newAtom('rs',[newVariable('F'),newConstant('true'),newVariable('R')]),
				newVariable('L')]),
			newAtom('internal:abolish',[newVariable('R')])]))));

  addRuleSet(kb,ruleset);
 }
 // current_predicate(F) :- internal:current_predicate(F,L), internal:member(rs(F,_,_),L).
 {
  ruleset = new RuleSet('current_predicate',1,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('current_predicate',[newVariable('F')]),
		newConsPair(newAtom('internal:current_predicate',[newVariable('F'),newVariable('L')]),
			newAtom('internal:member',[
				newAtom('rs',[newVariable('F'),newVariable('_'),newVariable('_')]),
				newVariable('L')])))));

  addRuleSet(kb,ruleset);
 }
 // write/1 : ouput function
 {
  ruleset = new RuleSet('write',1,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('write',[newVariable('O')]),write_fn));

  addRuleSet(kb,ruleset);
 }
 // nl/0 : ouput function
 {
  ruleset = new RuleSet('nl',0,false);

  ruleset.rules.push(newFunctionRule(newConstant('nl'),nl_fn));

  addRuleSet(kb,ruleset);
 }

 // +/1 eval function
 {
  ruleset = new RuleSet('+',1,false);
  setOperatorInfo(ruleset,OP_TYPE_FX,500);

  setEvaluateFunctionForRuleSet(ruleset,positive_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // -/1 eval function
 {
  ruleset = new RuleSet('-',1,false);
  setOperatorInfo(ruleset,OP_TYPE_FX,500);

  setEvaluateFunctionForRuleSet(ruleset,negative_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // +/2 eval function
 {
  ruleset = new RuleSet('+',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,500);

  setEvaluateFunctionForRuleSet(ruleset,plus_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // -/2 eval function
 {
  ruleset = new RuleSet('-',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,500);

  setEvaluateFunctionForRuleSet(ruleset,minus_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // */2 eval function
 {
  ruleset = new RuleSet('*',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,400);

  setEvaluateFunctionForRuleSet(ruleset,multiply_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // //2 eval function
 {
  ruleset = new RuleSet('/',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,400);

  setEvaluateFunctionForRuleSet(ruleset,divide_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // ///2 eval function
 {
  ruleset = new RuleSet('//',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,400);

  setEvaluateFunctionForRuleSet(ruleset,intdivide_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // mod/2 eval function
 {
  ruleset = new RuleSet('mod',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,400);

  setEvaluateFunctionForRuleSet(ruleset,mod_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // **/2 eval function
 {
  ruleset = new RuleSet('**',2,false);
  setOperatorInfo(ruleset,OP_TYPE_XFX,200);

  setEvaluateFunctionForRuleSet(ruleset,pow_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // exp/1 eval function
 {
  ruleset = new RuleSet('exp',1,false);

  setEvaluateFunctionForRuleSet(ruleset,exp_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // log/1 eval function
 {
  ruleset = new RuleSet('log',1,false);

  setEvaluateFunctionForRuleSet(ruleset,log_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // sqrt/1 eval function
 {
  ruleset = new RuleSet('sqrt',1,false);

  setEvaluateFunctionForRuleSet(ruleset,sqrt_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // abs/1 eval function
 {
  ruleset = new RuleSet('abs',1,false);

  setEvaluateFunctionForRuleSet(ruleset,abs_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // sin/1 eval function
 {
  ruleset = new RuleSet('sin',1,false);

  setEvaluateFunctionForRuleSet(ruleset,sin_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // cos/1 eval function
 {
  ruleset = new RuleSet('cos',1,false);

  setEvaluateFunctionForRuleSet(ruleset,cos_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // tan/1 eval function
 {
  ruleset = new RuleSet('tan',1,false);

  setEvaluateFunctionForRuleSet(ruleset,tan_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // asin/1 eval function
 {
  ruleset = new RuleSet('asin',1,false);

  setEvaluateFunctionForRuleSet(ruleset,asin_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // acos/1 eval function
 {
  ruleset = new RuleSet('acos',1,false);

  setEvaluateFunctionForRuleSet(ruleset,acos_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // atan/1 eval function
 {
  ruleset = new RuleSet('atan',1,false);

  setEvaluateFunctionForRuleSet(ruleset,atan_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // atan2/2 eval function
 {
  ruleset = new RuleSet('atan2',2,false);

  setEvaluateFunctionForRuleSet(ruleset,atan2_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // integer/1 eval function : isinteger_fn
 {
  ruleset = new RuleSet('integer',1,false);

  setEvaluateFunctionForRuleSet(ruleset,trunc_eval_fn);

  ruleset.rules.push(newFunctionRule(
  		newAtom('integer',[newVariable('N')]),isinteger_fn));

  addRuleSet(kb,ruleset);
 }
 // float_factional_part/1 eval function.
 {
  ruleset = new RuleSet('float_fractional_part',1,false);

  setEvaluateFunctionForRuleSet(ruleset,fractional_part_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // float_integer_part/1 eval function.
 {
  ruleset = new RuleSet('float_integer_part',1,false);

  setEvaluateFunctionForRuleSet(ruleset,trunc_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // floor/1 eval function
 {
  ruleset = new RuleSet('floor',1,false);

  setEvaluateFunctionForRuleSet(ruleset,floor_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // ceiling/1 eval function
 {
  ruleset = new RuleSet('ceiling',1,false);

  setEvaluateFunctionForRuleSet(ruleset,ceiling_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // round/1 eval function
 {
  ruleset = new RuleSet('round',1,false);

  setEvaluateFunctionForRuleSet(ruleset,round_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // sign/1 eval function
 {
  ruleset = new RuleSet('sign',1,false);

  setEvaluateFunctionForRuleSet(ruleset,sign_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // /\/2 eval function
 {
  ruleset = new RuleSet('/\\',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,500);

  setEvaluateFunctionForRuleSet(ruleset,bitwise_and_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // \//2 eval function
 {
  ruleset = new RuleSet('\\/',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,500);

  setEvaluateFunctionForRuleSet(ruleset,bitwise_or_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // #/2 eval function
 {
  ruleset = new RuleSet('#',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,500);

  setEvaluateFunctionForRuleSet(ruleset,bitwise_xor_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // \\/1 eval function
 {
  ruleset = new RuleSet('\\',1,false);
  setOperatorInfo(ruleset,OP_TYPE_FX,500);

  setEvaluateFunctionForRuleSet(ruleset,bitwise_negate_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // <</2 eval function
 {
  ruleset = new RuleSet('<<',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,400);

  setEvaluateFunctionForRuleSet(ruleset,bitwise_lshift_eval_fn);

  addRuleSet(kb,ruleset);
 }
 // >>/2 eval function
 {
  ruleset = new RuleSet('>>',2,false);
  setOperatorInfo(ruleset,OP_TYPE_YFX,400);

  setEvaluateFunctionForRuleSet(ruleset,bitwise_rshift_eval_fn);

  addRuleSet(kb,ruleset);
 }

 // internal:catch/3 : internal catch function
 // internal:catch(G,E,P) P=true goal G succeeds, P=false if exception unifying E is thrown.
 {
  ruleset = new RuleSet('internal:catch',3,false);

  ruleset.rules.push(newTraversalRule(
  		newAtom('internal:catch',[newVariable('G'),newVariable('E'),newVariable('P')]),
		internal_catch_try_fn,internal_catch_retry_fn,internal_catch_undo_fn));

  addRuleSet(kb,ruleset);
 }

 // internal:atom_append!/2 an atom mutate function that adds an argument
 // internal:atom_append!(A,E).  Adds E as an extra argument of A.
 {
  ruleset = new RuleSet('internal:atom_append!',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:atom_append!',[newVariable('A'),newVariable('E')]),internal_atom_append_fn));

  addRuleSet(kb,ruleset);
 }
 // internal:atom_setarg!/3 an atom mutate function that changes an argument
 // internal:atom_setarg!(I,A,E). Set arg at index I (I in 1..N) in atom A (with N args) to E
 {
  ruleset = new RuleSet('internal:atom_setarg!',3,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:atom_setarg!',[newVariable('I'),newVariable('A'),newVariable('E')]),internal_atom_setarg_fn));

  addRuleSet(kb,ruleset);
 }
 // internal:code_char(N,A) :- char_code(A,N).
 {
  ruleset = new RuleSet('internal:code_char',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:code_char',[newVariable('N'),newVariable('A')]),
			newAtom('char_code',[newVariable('A'),newVariable('N')]))));

  addRuleSet(kb,ruleset);
 }
 // internal:number_atom/2 : number atom converter
 {
  ruleset = new RuleSet('internal:number_atom',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:number_atom',[newVariable('N'),newVariable('A')]),internal_number_atom_fn));

  addRuleSet(kb,ruleset);
 }

 // internal:=@=/2 : equivalence (structural similarity)
 {
  ruleset = new RuleSet('internal:=@=',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:=@=',[newVariable('X'),newVariable('Y')]),internal_equivalent_fn));

  addRuleSet(kb,ruleset);
 }
 // internal:\=@=/2 : non-equivalence (structural difference)
 {
  ruleset = new RuleSet('internal:\\=@=',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:\\=@=',[newVariable('X'),newVariable('Y')]),internal_nequivalent_fn));

  addRuleSet(kb,ruleset);
 }

 // internal:copy_term/2 copy term so that term is copied, not just the enclosures
 // internal:copy_term(T,C).  C is a copy of T.
 {
  ruleset = new RuleSet('internal:copy_term',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:copy_term',[newVariable('T'),newVariable('C')]),internal_copy_term_fn));

  addRuleSet(kb,ruleset);
 }
 // internal:term_variables/2 return list of unbound variables in given term
 // internal:term_variables(T,V).  V is a list of variables in T.
 {
  ruleset = new RuleSet('internal:term_variables',2,false);

  ruleset.rules.push(newFunctionRule(
  		newAtom('internal:term_variables',[newVariable('T'),newVariable('V')]),internal_term_variables_fn));

  addRuleSet(kb,ruleset);
 }
 // internal:term_split_existential(E^G,[E|Es],Rs) :- !, internal:term_split_existential(G,Es,Rs).
 // internal:term_split_existential(G,[],G).
 {
  ruleset = new RuleSet('internal:term_split_existential',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:term_split_existential',[
			newAtom('^',[newVariable('E'),newVariable('G')]),
			newListPair(newVariable('E'),newVariable('Es')),
			newVariable('Rs')]),
		newConsPairsFromTerms([
			newConstant('!'),
			newAtom('internal:term_split_existential',[newVariable('G'),newVariable('Es'),newVariable('Rs')])]))));
  ruleset.rules.push(newRule(
		newAtom('internal:term_split_existential',[newVariable('G'),newListNull(),newVariable('G')])));

  addRuleSet(kb,ruleset);
 }

 // internal:compare/3 compare two terms, and return constants '<','=', or '>'.
 {
  ruleset = new RuleSet('internal:compare',3,false);

  ruleset.rules.push(newFunctionRule(newAtom('internal:compare',[
				newVariable('S'),newVariable('T'),newVariable('C')]),internal_compare_fn));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }
 // internal:bagof_match(G,T-D,T) :- G internal:=@= D.
 {
  ruleset = new RuleSet('internal:bagof_match',3,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:bagof_match',[newVariable('G'),
				newAtom('-',[newVariable('T'),newVariable('D')]),newVariable('T')]),
		newAtom('internal:=@=',[newVariable('G'),newVariable('D')]))));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }
 // internal:sumlist(_,[],A,A) :- !.
 // internal:sumlist(P,[L|Ls],A,O) :- internal:call(P,[L,A,X]), !, internal:sumlist(P,Ls,X,O).
 {
  ruleset = new RuleSet('internal:sumlist',4,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:sumlist',[newVariable('_'),newListNull(),newVariable('A'),newVariable('A')]),
				newConstant('!'))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:sumlist',[newVariable('P'),
				newListPair(newVariable('L'),newVariable('Ls')),
				newVariable('A'),
				newVariable('O')]),
		newConsPairsFromTerms([
			newAtom('internal:call',[newVariable('P'),newListFromTerms([newVariable('L'),newVariable('A'),newVariable('X')])]),
			newConstant('!'),
			newAtom('internal:sumlist',
				[newVariable('P'),newVariable('Ls'),newVariable('X'),newVariable('O')])]))));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }
 // internal:flatten([],F) :- !, F = [].
 // internal:flatten([X|Xs],F) :- internal:flatten(X,F1), internal:flatten(Xs,F2), !, internal:append(F1,F2,F).
 // internal:flatten(L,F) :- nonvar(L), !, F = [L].
 {
  ruleset = new RuleSet('internal:flatten',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:flatten',[newListNull(),newVariable('F')]),
		newConsPairsFromTerms([
			newConstant('!'),
			newAtom('=',[newVariable('F'),newListNull()])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:flatten',[newListPair(newVariable('X'),newVariable('Xs')),newVariable('F')]),
		newConsPairsFromTerms([
			newAtom('internal:flatten',[newVariable('X'),newVariable('F1')]),
			newAtom('internal:flatten',[newVariable('Xs'),newVariable('F2')]),
			newConstant('!'),
			newAtom('internal:append',[newVariable('F1'),newVariable('F2'),newVariable('F')])]))));
  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:flatten',[newVariable('L'),newVariable('F')]),
		newConsPairsFromTerms([
			newAtom('nonvar',[newVariable('L')]),
			newConstant('!'),
			newAtom('=',[newVariable('F'),newListPair(newVariable('L'),newListNull())])]))));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }
 // internal:singleton(L,[L]).
 {
  ruleset = new RuleSet('internal:singleton',2,false);

  ruleset.rules.push(newRule(
		newAtom('internal:singleton',[newVariable('L'),newListPair(newVariable('L'),newListNull())])));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }
 // internal:current_predicate/2 enumerates available rules in a list.
 // internal:current_predicate(F,L) L is a list of rulesets matching functor F (name/arity).
 // L is of the form [rs(F,D,R)|...] where R is a rule reference for bound functor F.
 // D=true for dynamic rules, D=fail for static rules.
 {
  ruleset = new RuleSet('internal:current_predicate',2,false);

  ruleset.rules.push(newFunctionRule(newAtom('internal:current_predicate',[
				newVariable('F'),newVariable('L')]),internal_current_predicate_fn));

  addRuleSet(kb,ruleset);
 }
 // internal:clause/5 enumerates clauses in ruleset.
 // internal:clause(H,B,R,N,X) H is head of rule, B is body of rule (true for a fact),
 // R is a rule reference and N is the rule number for (H :- B).
 // X is the increment counter on retries (defaults to 1 - use 0 for no increment)
 {
  ruleset = new RuleSet('internal:clause',5,false);

  ruleset.rules.push(newTraversalRule(newAtom('internal:clause',[
				newVariable('H'),newVariable('B'),newVariable('R'),newVariable('N'),newVariable('X')]),
				internal_clause_try_fn,internal_clause_retry_fn,internal_clause_undo_fn));

  addRuleSet(kb,ruleset);
 }
 // internal:current_op/4 enumerates operators.
 // internal:current_op(N,T,P,R) N is an atomsymbol, T is the op type, P is the priority number,
 // R is a ruleset reference.
 {
  ruleset = new RuleSet('internal:current_op',4,false);

  ruleset.rules.push(newTraversalRule(newAtom('internal:current_op',[
				newVariable('N'),newVariable('T'),newVariable('P'),newVariable('R')]),
				internal_current_op_try_fn,internal_current_op_retry_fn,null));

  addRuleSet(kb,ruleset);
 }
 // internal:retract/2 retract rule of given rule reference and index number.
 {
  ruleset = new RuleSet('internal:retract',2,false);

  ruleset.rules.push(newFunctionRule(newAtom('internal:retract',[
				newVariable('R'),newVariable('N')]),internal_retract_fn));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }
 // internal:merge_sort(L,S) :- internal:convlist(internal:singleton,L,M,[]), internal:merge_lists(M,N,S).
 {
  ruleset = new RuleSet('internal:merge_sort',2,false);

  ruleset.rules.push(newRule(newRuleTerm(
		newAtom('internal:merge_sort',[newVariable('L'),newVariable('S')]),
		newConsPairsFromTerms([
			newAtom('internal:convlist',[newConstant('internal:singleton'),newVariable('L'),newVariable('M'),newListNull()]),
			newAtom('internal:merge_lists',[newVariable('M'),newVariable('S')])]))));

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
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

  addRuleSet(kb,ruleset);
 }

 kb.phase = KB_PHASE_READY;

 return kb;
}

function isKBReady(kb: any)
{
 return (kb.phase == KB_PHASE_READY);
}

function isKBConsulting(kb: any)
{
 return (kb.phase == KB_PHASE_CONSULT);
}

// FIX: should load into empty KB, then combine with the existing one, keeping track of rule sources,
// and writing warnings if for overwitten / separated predicates.
// FIX: lib should be short library name string, and the function called should be:
// 'jslog_library_'+lib(empty_kb)
export function loadKBLibrary(kb: any, lib: any)
{
 lib(kb);
}


///////////////////////////////////
// Rule* and RuleSet* member functions for KnowledgeBase
///////////////////////////////////

export class RuleSet {
  rules: any[] = [];

  //// Other Properties (document here):
  // this.op_type : the OP_TYPE_* if this rule represents an operator.
  // this.op_precedence : operator precedence in the range 1..1200;

  constructor(public name: any, public arity: any, public dynamic: any) {
  }
}

export class Rule {
  body: any[] = [];
  fn: any;
  try_fn: any;
  retry_fn: any;
  undo_fn: any;

  constructor(public name: any, public arity: any, public enclosure: any, public head: any) {
  }
}

export function newRule(term: any)
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

export function newFunctionRule(term: any, fn: any)
{var encl = newTermEnclosure(term);
 var rule;

 if (!isAtom(term))
  throw newErrorException("Rule LHS must be atom.");

 rule = new Rule(term.name,term.children.length,encl.enclosure,encl.term);
 rule.body = null;
 rule.fn = fn;

 return rule;
}

function newTraversalRule(term: any, try_fn: any, retry_fn: any, undo_fn: any)
{var encl = newTermEnclosure(term);
 var rule;

 if (!isAtom(term))
  throw newErrorException("Rule LHS must be atom.");

 rule = new Rule(term.name,term.children.length,encl.enclosure,encl.term);
 rule.body = null;
 rule.try_fn = try_fn;
 rule.retry_fn = retry_fn;
 rule.undo_fn = undo_fn;

 return rule;
}

export function newRuleBodyArrayEnclosure(enclosure: any, rule: any)
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
  ae.undo_fn = rule.undo_fn;

  return ae;
 }
}

///////////////////////////////////
// * KB / RuleSet / Rule utility functions
///////////////////////////////////

// Add ruleset to kb.  This must occur before attempting to add the corresponding rules.
export function addRuleSet(kb: any, ruleset: any)
{
 kb.rulesets[getRuleNameArity(ruleset)] = ruleset;
}

// Add rule to kb.  The corresponding RuleSet to rule must already exist in kb.
// If append is true, rule is appended at the end of the ruleset, otherwise
// it is prepended to the beginning.
export function addRule(kb: any, rule: any, append: any = undefined)
{var ruleset;

 if ((ruleset = kb.rulesets[getRuleNameArity(rule)]) == null)
  throw newErrorException("Must declare rule dynamic to add: "+getRuleNameArity(rule));

 if (append)
  ruleset.rules.push(rule);
 else
  ruleset.rules.unshift(rule);
}

// Remove rule at index from ruleset.
export function removeRuleFromRuleSet(ruleset: any, index: any)
{
 if (!isDynamicRuleSet(ruleset))
  throw newErrorException("Must declare rule dynamic to remove: "+getRuleNameArity(ruleset));

 ruleset.rules.splice(index,1);
}

// Get ruleset used to prove term.
export function getRuleSet(kb: any, term: any)
{
 return kb.rulesets[getTermNameArity(term)];
}

// Get ruleset for given name and arity.
export function getRuleSetFromNameArity(kb: any, name: any, arity: any)
{
 return kb.rulesets[getTermNameArityFromNameArity(name,arity)];
}

function getRuleNameArityFromTerm(term: any)
{
 if (isRuleTerm(term))
  return getTermNameArity(term.children[0]);
 else
  return getTermNameArity(term);
}

export function getRuleNameArity(rule: any)
{
 return (rule.name.toString()+"/"+rule.arity.toString());
}

export function getRuleSetName(ruleset: any)
{
 return ruleset.name;
}

function getRuleSetArity(ruleset: any)
{
 return ruleset.arity;
}

// return the enclosure array for unifying rule.head with encl
// returns null if unification fails.
// binding is an array, updated with the unification bindings if succeeds.
export function getUnifiedRuleEnclosure(rule: any, encl: any, binding: any)
{var head_encl = newBlankEnclosure(rule.enclosure.length,rule.head);

 if (jslog_unify(head_encl,encl,binding))
  return head_encl.enclosure;

 return null;
}

// returns undefined if ruleset does not represent an operator
export function getOperatorType(ruleset: any)
{
 return ruleset.op_type;
}

// returns null if op_type is not in valid range
export function getOperatorTypeStringFromType(op_type: any)
{
 switch (op_type)
 {
  case OP_TYPE_XFX:
    return 'xfx';
  case OP_TYPE_XFY:
    return 'xfy';
  case OP_TYPE_YFX:
    return 'yfx';
  case OP_TYPE_FX:
    return 'fx';
  case OP_TYPE_FY:
    return 'fy';
  case OP_TYPE_XF:
    return 'xf';
  case OP_TYPE_YF:
    return 'yf';
 }
 return null;
}

// return the OP_TYPE_* value for the given op_type_string
// returns null if op_type_string is not valid
export function getOperatorTypeFromString(op_type_string: any)
{
 if (op_type_string == 'xfx')
  return OP_TYPE_XFX;
 if (op_type_string == 'xfy')
  return OP_TYPE_XFY;
 if (op_type_string == 'yfx')
  return OP_TYPE_YFX;
 if (op_type_string == 'fx')
  return OP_TYPE_FX;
 if (op_type_string == 'fy')
  return OP_TYPE_FY;
 if (op_type_string == 'xf')
  return OP_TYPE_XF;
 if (op_type_string == 'yf')
  return OP_TYPE_YF;

 return null;
}

// returns undefined if ruleset does not represent an operator
export function getOperatorPrecedence(ruleset: any)
{
 return ruleset.op_precedence;
}

// makes ruleset represent an operator with type (OP_TYPE_* value) and precedence (number)
// note: type and ruleset.arity must match (i.e., *F* => arity = 2 ; *F, F* => arity = 1).
function setOperatorInfo(ruleset: any, type: any, precedence: any)
{
 ruleset.op_type = type;
 ruleset.op_precedence = precedence;
}

function setEvaluateFunctionForRuleSet(ruleset: any, eval_fn: any)
{
 ruleset.eval_fn = eval_fn;

 return ruleset;
}

export function isOperatorRuleSet(ruleset: any)
{
 return (ruleset.op_type != null && ruleset.op_precedence != null &&
		ruleset.arity >= 1 && ruleset.arity <= 2);
}

export function isDynamicRuleSet(ruleset: any)
{
 return (ruleset == undefined || ruleset.dynamic);
}


///////////////////////////////////
// * KB / RuleSet / Rule optimization functions
///////////////////////////////////
// NOTE: the following is exploratory code...
// FIX: Optimiztion should be based on general term re-writing (a transform engine).
// FIX: Could fail for deeply nested terms.  Should use stack to track terms to optimize.
// FIX: Add constant propagation (i.e., evaluate constant expressions).

// do not call directly
function optimizeTerm(term: any, kb: any)
{
 if (isVariable(term))
 {
  term.ruleset = undefined;
  term.goal_type = TYPE_VARIABLE_GOAL;
 }
 else if (isAtom(term))
 {
  term.ruleset = getRuleSet(kb,term);
  term.goal_type = TYPE_ATOM_GOAL;
  if (term.ruleset != undefined)
   term.name = term.ruleset.name;
 }
}

// do not call directly
function optimizeTerms(term: any, kb: any)
{
 optimizeTerm(term,kb);

 if (isAtom(term))
 {
  for (var i = 0; i < term.children.length; i++)
   optimizeTerms(term.children[i],kb);
 }
}

// do not call directly
function optimizeRule(rule: any, ruleset: any, kb: any)
{
 rule.name = ruleset.name;
 optimizeTerm(rule.head,kb);
 if (rule.body != null)
 {
  for (var i = 0; i < rule.body.length; i++)
   optimizeTerms(rule.body[i],kb);
 }
}

// do not call directly
function optimizeRuleSet(ruleset: any, kb: any)
{
 for (var i = 0; i < ruleset.rules.length; i++)
  optimizeRule(ruleset.rules[i],ruleset,kb);
}

// call at the end of the consult phase.
export function optimizeKB(kb: any)
{var phase = kb.phase;

 kb.phase = KB_PHASE_CONSULT;

 for (var i in kb.rulesets)
  optimizeRuleSet(kb.rulesets[i],kb);

 kb.phase = phase;
}
