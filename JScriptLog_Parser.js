/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_parse_* functions for the Prolog parser
///////////////////////////////////

// FIX: Create parser in JScriptLog Prolog

// parse string in_src, which represents a sequence of Prolog clauses
function jslog_parse(in_src)
{
}


///////////////////////////////////
// jslog_plog_* functions for the Prolog parser
///////////////////////////////////

// plog:token:name([symbol|O],O,symbol).
// plog:token:name([s1,s2,s3...|O],O,[s1,s2,s3,...]).
function jslog_plog_token(name,symbol,kb)
{var inlist,outlist,i;

 addRuleSet(kb,new RuleSet('plog:token:'+name,3,false));

 if (symbol.constructor != Array)
  symbol = [symbol];
 
 if (symbol.length == 0)
  throw new Error("Expected non-empty symbol array.");
 
 inlist = newListPair(newConstant(symbol[symbol.length - 1]),newVariable('O'));
 outlist = newListPair(newConstant(symbol[symbol.length - 1]),newListNull());
 
 for (i = symbol.length - 2; i >= 0; i--) 
 {
  inlist = newListPair(newConstant(symbol[i]),inlist);
  outlist = newListPair(newConstant(symbol[i]),outlist);
 }
  
 addRule(kb,newRule(newAtom('plog:token:'+name,[inlist,newVariable('O'),outlist])),true);
}

// plog:token:name([I|O],O,I) :- I @>= symbol1, I @=< symbol2.
// plog:token:name([I|O],O,I) :- I @>= s11, I @=< s21,I @>= s21, I @=< s22,...
function jslog_plog_range_token(name,symbol_min,symbol_max,kb)
{var pairs;

 addRuleSet(kb,new RuleSet('plog:token:'+name,3,false));

 if (symbol_max == null)
  symbol_max = symbol_min;

 if (symbol_min.constructor != Array)
  symbol_min = [symbol_min];
 if (symbol_max.constructor != Array)
  symbol_max = [symbol_max];
 
 if (symbol_min.length == 0 || symbol_max.length == 0 || symbol_min.length != symbol_max.length)
  throw new Error("Expected non-empty symbols array of equal length.");
 
 if (symbol_min[symbol_min.length - 1] != symbol_max[symbol_max.length - 1])
  pairs = newConsPair(
			newAtom('@>=',[newVariable('I'),newConstant(symbol_min[symbol_min.length - 1])]),
			newAtom('@=<',[newVariable('I'),newConstant(symbol_max[symbol_max.length - 1])]));
 else
  pairs = newAtom('==',[newVariable('I'),newConstant(symbol_min[symbol_min.length - 1])]);
 			
 for (i = symbol_min.length - 2; i >= 0; i--) 
 {
  if (symbol_min[i] != symbol_max[i])
   pairs = newConsPairsFromTerms([
			newAtom('@>=',[newVariable('I'),newConstant(symbol_min[i])]),
			newAtom('@=<',[newVariable('I'),newConstant(symbol_max[i])]),
			pairs]);
  else
   pairs = newConsPair(newAtom('==',[newVariable('I'),newConstant(symbol_min[i])]),
			pairs);
 }
 
 addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:'+name,[newListPair(newVariable('I'),newVariable('O')),newVariable('O'),newVariable('I')]),
		pairs)),
	true);
}

// plog:token:name*(I,O,N) :- plog:token:name(I,S,N1), !, plog:token:name*(S,O,N2), internal:append(N1,N2,N).
// plog:token:name*(I,I,[]).
function jslog_plog_zero_or_more_token(name,kb)
{
 addRuleSet(kb,new RuleSet('plog:token:'+name+'*',3,false));

 addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:'+name+'*',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:'+name,[newVariable('I'),newVariable('S'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:'+name+'*',[newVariable('S'),newVariable('O'),newVariable('N2')]),
			newAtom('internal:append',[newVariable('N1'),newVariable('N2'),newVariable('N')])
			]))),
	true);
 addRule(kb,newRule(newAtom('plog:token:'+name+'*',[newVariable('I'),newVariable('O'),newListNull()])),
	true); 
}

// requires plog:token:name* to already be defined.
// plog:token:name+(I,O,N) :- plog:token:name(I,S,N1), !, plog:token:name*(S,O,N2), internal:append(N1,N2,N).
function jslog_plog_one_or_more_token(name,kb)
{
 addRuleSet(kb,new RuleSet('plog:token:'+name+'+',3,false));

 addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:'+name+'+',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:'+name,[newVariable('I'),newVariable('S'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:'+name+'*',[newVariable('S'),newVariable('O'),newVariable('N2')]),
			newAtom('internal:append',[newVariable('N1'),newVariable('N2'),newVariable('N')])
			]))),
	true);
}


///////////////////////////////////
// jslog_library_parser(kb)
///////////////////////////////////

function jslog_library_parser(kb)
{
 jslog_plog_token('period','.',kb);
 jslog_plog_token('zero','0',kb);
 jslog_plog_token('two_squotes',['\'','\''],kb);
 jslog_plog_token('squote','\'',kb);
 jslog_plog_token('two_dquotes',['\"','\"'],kb);
 jslog_plog_token('dquote','\"',kb);
 jslog_plog_token('esc','\\',kb);
 jslog_plog_range_token('exp',['e','E'],null,kb);
 jslog_plog_range_token('hexx',['x','X'],null,kb);
 jslog_plog_range_token('sign',['+','-'],null,kb);

 jslog_plog_token('start_linecomment','%',kb);
 jslog_plog_token('end_linecomment','\n',kb);
 jslog_plog_token('start_blockcomment',['/','*'],kb);
 jslog_plog_token('end_blockcomment',['*','/'],kb);

 jslog_plog_range_token('digit','0','9',kb);

 jslog_plog_range_token('solo_char',['!',';'],null,kb);
 jslog_plog_range_token('symbol_char',	['#','&','*','-',':','<','\\','^','`','~'],
										['#','&','+','/',':','@','\\','^','`','~'],kb);
 jslog_plog_range_token('lowercase','a','z',kb);
 jslog_plog_range_token('character',' ','~',kb);
 jslog_plog_range_token('var_start',['_','A'],['_','Z'],kb);
 jslog_plog_range_token('name_char',['A','a','0','_'],['Z','z','9','_'],kb);
 jslog_plog_range_token('hex_char',['0','A','a'],['9','F','f'],kb);
 jslog_plog_range_token('esc_char',['0','a','b','r','f','t','n','v','\\','\"','\'','\`'],null,kb);

 jslog_plog_range_token('whitespace',String.fromCharCode(0),' ',kb);

 jslog_plog_zero_or_more_token('digit',kb); // plog:token:digit*
 jslog_plog_one_or_more_token('digit',kb); // plog:token:digit+
 jslog_plog_zero_or_more_token('hex_char',kb); // plog:token:hex_char*
 jslog_plog_one_or_more_token('hex_char',kb); // plog:token:hex_char+
 jslog_plog_zero_or_more_token('name_char',kb); // plog:token:name_char*
 jslog_plog_zero_or_more_token('symbol_char',kb); // plog:token:symbol_char*
 jslog_plog_one_or_more_token('symbol_char',kb); // plog:token:symbol_char+
 jslog_plog_zero_or_more_token('whitespace',kb); // plog:token:whitespace*
 jslog_plog_one_or_more_token('whitespace',kb); // plog:token:whitespace+

 // plog:token:variable(I,O,V) :- plog:token:var_start(I,S,N1), !, plog:token:name_char*(S,O,N2), 
 //		internal:append(N1,N2,N), !, atom_chars(V,N).
 // V is a constant (i.e., atom name) representing the variable name.
 {
  addRuleSet(kb,new RuleSet('plog:token:variable',3,false));

  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:variable',[newVariable('I'),newVariable('O'),newVariable('V')]),
		newConsPairsFromTerms([
			newAtom('plog:token:var_start',[newVariable('I'),newVariable('S'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:name_char*',[newVariable('S'),newVariable('O'),newVariable('N2')]),
			newAtom('internal:append',[newVariable('N1'),newVariable('N2'),newVariable('N')]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('V'),newVariable('N')])]))),
	true); 
 }

 // plog:token:float(I,O,N) :- plog:token:digit+(I,O1,N1), 
 //		plog:token:period(O1,O2,N2), plog:token:digit+(O2,O3,N3), !, 
 //		(plog:token:float_exp(O3,O,N4), internal:flatten([N1,N2,N3,N4],N5) ;
 //		 O = O3, internal:flatten([N1,N2,N3],N5)), !, number_chars(N,N5).
 // plog:token:float(I,O,N) :- plog:token:digit+(I,O1,N1), 
 //		plog:token:float_exp(O1,O,N2), !, internal:append(N1,N2,N3), number_chars(N,N3).
 // N is a number.
 {
  addRuleSet(kb,new RuleSet('plog:token:float',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:float',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:digit+',[newVariable('I'),newVariable('O1'),newVariable('N1')]),
			newAtom('plog:token:period',[newVariable('O1'),newVariable('O2'),newVariable('N2')]),
			newAtom('plog:token:digit+',[newVariable('O2'),newVariable('O3'),newVariable('N3')]),
			newConstant('!'),
			newOrPair(
				newConsPair(
					newAtom('plog:token:float_exp',[newVariable('O3'),newVariable('O'),newVariable('N4')]),
					newAtom('internal:flatten',[
						newListFromTerms([newVariable('N1'),newVariable('N2'),newVariable('N3'),newVariable('N4')]),
						newVariable('N5')])),
				newConsPair(
					newAtom('=',[newVariable('O'),newVariable('O3')]),
					newAtom('internal:flatten',[
						newListFromTerms([newVariable('N1'),newVariable('N2'),newVariable('N3')]),
						newVariable('N5')]))),
			newConstant('!'),
			newAtom('number_chars',[newVariable('N'),newVariable('N5')])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:float',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:digit+',[newVariable('I'),newVariable('O1'),newVariable('N1')]),
			newAtom('plog:token:float_exp',[newVariable('O1'),newVariable('O'),newVariable('N2')]),
			newConstant('!'),
			newAtom('internal:append',[newVariable('N1'),newVariable('N2'),newVariable('N3')]),
			newAtom('number_chars',[newVariable('N'),newVariable('N3')])]))),
	true);
 }
 // plog:token:float_exp(I,O,N) :- plog:token:exp(I,O1,N1), 
 //		(plog:token:sign(O1,O2,N2) ; O2 = O1, N2 = []), !,
 //		plog:token:digit+(O2,O,N3), !, internal:flatten([N1,N2,N3],N).
 // N is flattened list of chars.
 {
  addRuleSet(kb,new RuleSet('plog:token:float_exp',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:float_exp',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:exp',[newVariable('I'),newVariable('O1'),newVariable('N1')]),
			newOrPair(
				newAtom('plog:token:sign',[newVariable('O1'),newVariable('O2'),newVariable('N2')]),
				newConsPair(
					newAtom('=',[newVariable('O2'),newVariable('O1')]),
					newAtom('=',[newVariable('N2'),newListNull()]))),
			newConstant('!'),
			newAtom('plog:token:digit+',[newVariable('O2'),newVariable('O'),newVariable('N3')]),
			newConstant('!'),
			newAtom('interal:flatten',[
				newListFromTerms([newVariable('N1'),newVariable('N2'),newVariable('N3')]),
				newVariable('N')])]))),
	true);
 }

 // plog:token:integer(I,O,N) :- plog:token:zero(I,O1,N1), plog:token:hexx(O1,O2,N2), !, 
 //			plog:token:hex_char+(O2,O,N3), !, internal:flatten([N1,N2,N3],N4), number_chars(N,N4).
 // plog:token:integer(I,O,N) :- plog:token:digit+(I,O,N1), !, number_chars(N,N1).
 // N is an number.
 {
  addRuleSet(kb,new RuleSet('plog:token:integer',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:integer',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:zero',[newVariable('I'),newVariable('O1'),newVariable('N1')]),
			newAtom('plog:token:hexx',[newVariable('O1'),newVariable('O2'),newVariable('N2')]),
			newConstant('!'),
			newAtom('plog:token:hex_char+',[newVariable('O2'),newVariable('O'),newVariable('N3')]),
			newConstant('!'),
			newAtom('internal:flatten',[
				newListFromTerms([newVariable('N1'),newVariable('N2'),newVariable('N3')]),
				newVariable('N4')]),
			newAtom('number_chars',[newVariable('N'),newVariable('N4')])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:integer',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:digit+',[newVariable('I'),newVariable('O'),newVariable('N1')]),
			newConstant('!'),
			newAtom('number_chars',[newVariable('N'),newVariable('N1')])]))),
	true);
 }

 // plog:token:number(I,O,N) :- (plog:token:float(I,O,N) ; plog:token:integer(I,O,N)), !.
 // N is a number.
 {
  addRuleSet(kb,new RuleSet('plog:token:number',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:number',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newOrPair(
				newAtom('plog:token:float',[newVariable('I'),newVariable('O'),newVariable('N')]),
				newAtom('plog:token:integer',[newVariable('I'),newVariable('O'),newVariable('N')])),
			newConstant('!')]))),
	true);
 }
 
 // plog:token:atomname(I,O,N) :- plog:token:solo_char(I,O,N1), !, atom_chars(N,N1).
 // plog:token:atomname(I,O,N) :- plog:token:lowercase(I,O1,N1), !, plog:token:name_char*(O1,O,N2), !,
 //			internal:append(N1,N2,N3), atom_chars(N,N3).
 // plog:token:atomname(I,O,N) :- plog:token:symbol_char+(I,O,N1), !, atom_chars(N,N1).
 // plog:token:atomname(I,O,N) :- plog:token:two_squotes(I,O,_), !, atom_chars(N,[]).
 // plog:token:atomname(I,O,N) :- plog:token:squote(I,O1,_), !, 
 //			plog:token:atomname_quoted_chars(O1,O2,N1), !, plog:token:squote(O2,O,_), !, 
 //			atom_chars(N,N1).
 // N is a constant (i.e., atom name) representing the variable name.
 {
  addRuleSet(kb,new RuleSet('plog:token:atomname',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:atomname',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:solo_char',[newVariable('I'),newVariable('O'),newVariable('N1')]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('N'),newVariable('N1')])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:atomname',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:lowercase',[newVariable('I'),newVariable('O1'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:name_char*',[newVariable('O1'),newVariable('O2'),newVariable('N2')]),
			newConstant('!'),
			newAtom('internal:append',[newVariable('N1'),newVariable('N2'),newVariable('N3')]),			
			newAtom('atom_chars',[newVariable('N'),newVariable('N3')])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:atomname',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:symbol_char+',[newVariable('I'),newVariable('O'),newVariable('N1')]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('N'),newVariable('N1')])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:atomname',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:two_squotes',[newVariable('I'),newVariable('O'),newVariable('_')]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('N'),newListNull()])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:atomname',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:squote',[newVariable('I'),newVariable('O1'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:atomname_quoted_chars',[newVariable('O1'),newVariable('O2'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:squote',[newVariable('O2'),newVariable('O'),newVariable('_')]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('N'),newVariable('N1')])]))),
	true); 
 }
 // plog:token:atomname_quoted_chars(I,O,N) :- plog:token:two_squotes(I,O1,_), !, 
 //			plog:token:atomname_quoted_chars(O1,O,N1), !, N = ['\''|N1].
 // plog:token:atomname_quoted_chars(I,O,N) :- plog:token:esc_sequence(I,O1,N1), !, 
 //			plog:token:atomname_quoted_chars(O1,O,N2), !, internal:append(N1,N2,N).
 // plog:token:atomname_quoted_chars(I,O,N) :- plog:token:character(I,O1,N1), !, 
 //			plog:token:atomname_quoted_chars(O1,O,N2), !, internal:append(N1,N2,N).
 // N is flattened list of chars.
 {
  addRuleSet(kb,new RuleSet('plog:token:atomname_quoted_chars',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:atomname_quoted_chars',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:two_squotes',[newVariable('I'),newVariable('O1'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:atomname_quoted_chars',[newVariable('O1'),newVariable('O'),newVariable('N1')]),
			newConstant('!'),
			newAtom('=',[newVariable('N'),newListPair(newConstant('\''),newVariable('N1'))])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:atomname_quoted_chars',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:esc_sequence',[newVariable('I'),newVariable('O1'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:atomname_quoted_chars',[newVariable('O1'),newVariable('O'),newVariable('N2')]),
			newConstant('!'),
			newAtom('internal:append',[newVariable('N1'),newVariable('N2'),newVariable('N')])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:atomname_quoted_chars',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:character',[newVariable('I'),newVariable('O1'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:atomname_quoted_chars',[newVariable('O1'),newVariable('O'),newVariable('N2')]),
			newConstant('!'),
			newAtom('internal:append',[newVariable('N1'),newVariable('N2'),newVariable('N')])]))),
	true);
 }
 // FIX: handle unicode \uFFFF\, hex ASCII \xFF\, and octal \377 escapes
 // plog:token:esc_sequence(I,O,N) :- plog:token:esc(I,O1,_), !, 
 //			plog:token:esc_char(O1,O,N1), !, plog:token:esc_char_mapping(N1,N).
 // N is list of char.
 {
  addRuleSet(kb,new RuleSet('plog:token:esc_sequence',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:atomname_quoted_chars',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:two_squotes',[newVariable('I'),newVariable('O1'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:atomname_quoted_chars',[newVariable('O1'),newVariable('O'),newVariable('N1')]),
			newConstant('!'),
			newAtom('=',[newVariable('N'),newListPair(newConstant('\''),newVariable('N1'))])]))),
	true);
 }
 // plog:token:esc_char_mapping(['0'],['\0']) :- !.
 // plog:token:esc_char_mapping(['a'],['\x07']) :- !.
 // plog:token:esc_char_mapping(['b'],['\b']) :- !.
 // plog:token:esc_char_mapping(['r'],['\r']) :- !.
 // plog:token:esc_char_mapping(['f'],['\f']) :- !.
 // plog:token:esc_char_mapping(['t'],['\t']) :- !.
 // plog:token:esc_char_mapping(['n'],['\n']) :- !.
 // plog:token:esc_char_mapping(['v'],['\v']) :- !.
 // plog:token:esc_char_mapping([C],[C]). 
 {
  addRuleSet(kb,new RuleSet('plog:token:esc_char_mapping',2,false));
 
  addRule(kb,newRule(
    newRuleTerm(newAtom('plog:token:esc_char_mapping',[
				newListPair(newConstant('0'),newListNull()),
				newListPair(newConstant('\0'),newListNull())]),
		newConstant('!'))),true);
  addRule(kb,newRule(
    newRuleTerm(newAtom('plog:token:esc_char_mapping',[
				newListPair(newConstant('a'),newListNull()),
				newListPair(newConstant('\x07'),newListNull())]),
		newConstant('!'))),true);
  addRule(kb,newRule(
    newRuleTerm(newAtom('plog:token:esc_char_mapping',[
				newListPair(newConstant('b'),newListNull()),
				newListPair(newConstant('\b'),newListNull())]),
		newConstant('!'))),true);
  addRule(kb,newRule(
    newRuleTerm(newAtom('plog:token:esc_char_mapping',[
				newListPair(newConstant('r'),newListNull()),
				newListPair(newConstant('\r'),newListNull())]),
		newConstant('!'))),true);
  addRule(kb,newRule(
    newRuleTerm(newAtom('plog:token:esc_char_mapping',[
				newListPair(newConstant('f'),newListNull()),
				newListPair(newConstant('\f'),newListNull())]),
		newConstant('!'))),true);
  addRule(kb,newRule(
    newRuleTerm(newAtom('plog:token:esc_char_mapping',[
				newListPair(newConstant('t'),newListNull()),
				newListPair(newConstant('\t'),newListNull())]),
		newConstant('!'))),true);
  addRule(kb,newRule(
    newRuleTerm(newAtom('plog:token:esc_char_mapping',[
				newListPair(newConstant('n'),newListNull()),
				newListPair(newConstant('\n'),newListNull())]),
		newConstant('!'))),true);
  addRule(kb,newRule(
    newRuleTerm(newAtom('plog:token:esc_char_mapping',[
				newListPair(newConstant('v'),newListNull()),
				newListPair(newConstant('\v'),newListNull())]),
		newConstant('!'))),true);
  addRule(kb,newRule(newAtom('plog:token:esc_char_mapping',[
				newListPair(newVariable('C'),newListNull()),
				newListPair(newVariable('C'),newListNull())])),true);
 }

 // plog:token:string(I,O,N) :- plog:token:dquote(I,O1,_), !, 
 //			plog:token:string_quoted_chars(O1,O2,N1), !, plog:token:dquote(O2,O,_), !, 
 //			atom_chars(N2,N1), atom_codes(N2,N).
 // N is a list of char codes.
 {
  addRuleSet(kb,new RuleSet('plog:token:string',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:string',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:dquote',[newVariable('I'),newVariable('O1'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:string_quoted_chars',[newVariable('O1'),newVariable('O2'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:dquote',[newVariable('O2'),newVariable('O'),newVariable('_')]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('N2'),newVariable('N1')]),
			newAtom('atom_codes',[newVariable('N2'),newVariable('N')])]))),
	true); 
 }
 // plog:token:string_quoted_chars(I,O,N) :- plog:token:two_dquotes(I,O1,_), !, 
 //			plog:token:string_quoted_chars(O1,O,N1), !, N = [34|N1].
 // plog:token:string_quoted_chars(I,O,N) :- plog:token:esc_sequence(I,O1,N1), !, 
 //			plog:token:string_quoted_chars(O1,O,N4), !, atom_chars(N2,N1), atom_codes(N2,N3),
 //			internal:append(N3,N4,N).
 // plog:token:string_quoted_chars(I,O,N) :- plog:token:character(I,O1,N1), !, 
 //			plog:token:string_quoted_chars(O1,O,N4), !, atom_chars(N2,N1), atom_codes(N2,N3),
 //			internal:append(N3,N4,N).
 // N is list of char codes.
 {
  addRuleSet(kb,new RuleSet('plog:token:string_quoted_chars',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:string_quoted_chars',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:two_dquotes',[newVariable('I'),newVariable('O1'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:string_quoted_chars',[newVariable('O1'),newVariable('O'),newVariable('N1')]),
			newConstant('!'),
			newAtom('=',[newVariable('N'),newListPair(newNumber(34),newVariable('N1'))])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:string_quoted_chars',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:esc_sequence',[newVariable('I'),newVariable('O1'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:string_quoted_chars',[newVariable('O1'),newVariable('O'),newVariable('N4')]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('N2'),newVariable('N1')]),
			newAtom('atom_codes',[newVariable('N2'),newVariable('N3')]),
			newAtom('internal:append',[newVariable('N3'),newVariable('N4'),newVariable('N')])]))),
	true);
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:string_quoted_chars',[newVariable('I'),newVariable('O'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:character',[newVariable('I'),newVariable('O1'),newVariable('N1')]),
			newConstant('!'),
			newAtom('plog:token:string_quoted_chars',[newVariable('O1'),newVariable('O'),newVariable('N4')]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('N2'),newVariable('N1')]),
			newAtom('atom_codes',[newVariable('N2'),newVariable('N3')]),
			newAtom('internal:append',[newVariable('N3'),newVariable('N4'),newVariable('N')])]))),
	true);
 }

 // plog:token:blank(I,O,[]) :- plog:token:whitespace+(I,O1,_), !, plog:token:blank(O1,O,_).
 // plog:token:blank(I,O,[]) :- plog:token:start_linecomment(I,O1,_), !, 
 //		plog:token:linecomment(O1,O2,_), !, plog:token:blank(O2,O,_).
 // plog:token:blank(I,O,[]) :- plog:token:start_blockcomment(I,O1,_), !, 
 //		plog:token:blockcomment(O1,O2,_), !, plog:token:blank(O2,O,_).
 // plog:token:blank(I,I,[]).
 {
  addRuleSet(kb,new RuleSet('plog:token:blank',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:blank',[newVariable('I'),newVariable('O'),newListNull()]),
		newConsPairsFromTerms([
			newAtom('plog:token:whitespace+',[newVariable('I'),newVariable('O1'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:blank',[newVariable('O1'),newVariable('O'),newVariable('_')])]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:blank',[newVariable('I'),newVariable('O'),newListNull()]),
		newConsPairsFromTerms([
			newAtom('plog:token:start_linecomment',[newVariable('I'),newVariable('O1'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:linecomment',[newVariable('O1'),newVariable('O2'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:blank',[newVariable('O2'),newVariable('O'),newVariable('_')])]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:blank',[newVariable('I'),newVariable('O'),newListNull()]),
		newConsPairsFromTerms([
			newAtom('plog:token:start_blockcomment',[newVariable('I'),newVariable('O1'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:blockcomment',[newVariable('O1'),newVariable('O2'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:token:blank',[newVariable('O2'),newVariable('O'),newVariable('_')])]))),
	true); 
  addRule(kb,newRule(
		newAtom('plog:token:blank',[newVariable('I'),newVariable('I'),newListNull()])),
	true); 
 }
 // plog:token:linecomment(I,O,[]) :- plog:token:end_linecomment(I,O,_), !.
 // plog:token:linecomment([],[],[]) :- !.
 // plog:token:linecomment([_|I],O,[]) :- !, plog:token:linecomment(I,O,_).
 {
  addRuleSet(kb,new RuleSet('plog:token:linecomment',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:linecomment',[newVariable('I'),newVariable('O'),newListNull()]),
		newConsPairsFromTerms([
			newAtom('plog:token:end_linecomment',[newVariable('I'),newVariable('O'),newVariable('_')]),
			newConstant('!')]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:linecomment',[newListNull(),newListNull(),newListNull()]),
		newConstant('!'))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:linecomment',[newListPair(newVariable('_'),newVariable('I')),newVariable('O'),newListNull()]),
		newConsPairsFromTerms([
			newConstant('!'),
			newAtom('plog:token:linecomment',[newVariable('I'),newVariable('O'),newVariable('_')])]))),
	true); 
 }
 // plog:token:blockcomment(I,O,[]) :- plog:token:end_blockcomment(I,O,_), !.
 // plog:token:blockcomment([_|I],O,[]) :- !, plog:token:blockcomment(I,O,_).
 {
  addRuleSet(kb,new RuleSet('plog:token:blockcomment',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:blockcomment',[newVariable('I'),newVariable('O'),newListNull()]),
		newConsPairsFromTerms([
			newAtom('plog:token:end_blockcomment',[newVariable('I'),newVariable('O'),newVariable('_')]),
			newConstant('!')]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:blockcomment',[newListPair(newVariable('_'),newVariable('I')),newVariable('O'),newListNull()]),
		newConsPairsFromTerms([
			newConstant('!'),
			newAtom('plog:token:blockcomment',[newVariable('I'),newVariable('O'),newVariable('_')])]))),
	true); 
 }
}
