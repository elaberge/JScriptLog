/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// jslog_parse functions for the Prolog parser
///////////////////////////////////

// FIX: Create parser in JScriptLog Prolog

// parse string in_src, which represents a sequence of Prolog clauses

function jslog_query(in_src)
{
}

function jslog_consult(in_src,kb)
{
}


///////////////////////////////////
// jslog_plog*_token functions for the Prolog parser
///////////////////////////////////

// plog:token:name([symbol|O],O,[symbol]).
// plog:token:name([s1,s2,s3...|O],O,[s1,s2,s3,...]).
function jslog_plog_token(name,symbol,kb)
{var inlist,outlist;

 addRuleSet(kb,new RuleSet('plog:token:'+name,3,false));

 if (symbol.constructor != Array)
  symbol = [symbol];
 
 if (symbol.length == 0)
  throw new Error("Expected non-empty symbol array.");
 
 inlist = newListPair(newConstant(symbol[symbol.length - 1]),newVariable('O'));
 outlist = newListPair(newConstant(symbol[symbol.length - 1]),newListNull());
 
 for (var i = symbol.length - 2; i >= 0; i--) 
 {
  inlist = newListPair(newConstant(symbol[i]),inlist);
  outlist = newListPair(newConstant(symbol[i]),outlist);
 }
  
 addRule(kb,newRule(newAtom('plog:token:'+name,[inlist,newVariable('O'),outlist])),true);
}

// plog:token:name([I|O],O,[I]) :- I @>= symbol1, I @=< symbol2 ; ...
// plog:token:name([I|O],O,[I]) :- I @>= s11, I @=< s21 ; I @>= s21, I @=< s22,...
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
 			
 for (var i = symbol_min.length - 2; i >= 0; i--) 
 {
  if (symbol_min[i] != symbol_max[i])
   pairs = newOrPair(
			newConsPair(
					newAtom('@>=',[newVariable('I'),newConstant(symbol_min[i])]),
					newAtom('@=<',[newVariable('I'),newConstant(symbol_max[i])])),
			pairs);
  else
   pairs = newOrPair(newAtom('==',[newVariable('I'),newConstant(symbol_min[i])]),
			pairs);
 }
 
 addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:'+name,[newListPair(newVariable('I'),newVariable('O')),newVariable('O'),newListPair(newVariable('I'),newListNull())]),
		pairs)),
	true);
}

// plog:token:name*(I,O,N) :- plog:token:name(I,S,N1), !, plog:token:name*(S,O,N2), !, internal:append(N1,N2,N).
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
			newConstant('!'),
			newAtom('internal:append',[newVariable('N1'),newVariable('N2'),newVariable('N')])
			]))),
	true);
 addRule(kb,newRule(newAtom('plog:token:'+name+'*',[newVariable('I'),newVariable('I'),newListNull()])),
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
 jslog_plog_token('comma',',',kb);
 jslog_plog_token('zero','0',kb);
 jslog_plog_token('two_squotes',['\'','\''],kb);
 jslog_plog_token('squote','\'',kb);
 jslog_plog_token('two_dquotes',['\"','\"'],kb);
 jslog_plog_token('dquote','\"',kb);
 jslog_plog_token('esc','\\',kb);
 jslog_plog_token('lparen','(',kb);
 jslog_plog_token('rparen',')',kb);
 jslog_plog_token('lbrace','{',kb);
 jslog_plog_token('rbrace','}',kb);
 jslog_plog_token('lblock','[',kb);
 jslog_plog_token('rblock',']',kb);
 jslog_plog_token('two_blocks',['[',']'],kb);
 jslog_plog_token('bar',['|'],kb);
 jslog_plog_token('comma_dot_dot',[',','.','.'],kb);
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
 //			plog:token:atomname_quoted_chars(O1,O,N1), !, atom_chars(N,N1).
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
			newAtom('plog:token:name_char*',[newVariable('O1'),newVariable('O'),newVariable('N2')]),
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
			newAtom('plog:token:atomname_quoted_chars',[newVariable('O1'),newVariable('O'),newVariable('N1')]),
			newConstant('!'),
			newAtom('atom_chars',[newVariable('N'),newVariable('N1')])]))),
	true); 
 }
 // plog:token:atomname_quoted_chars(I,O,N) :- plog:token:two_squotes(I,O1,_), !, 
 //			plog:token:atomname_quoted_chars(O1,O,N1), !, N = ['\''|N1].
 // plog:token:atomname_quoted_chars(I,O,N) :- plog:token:esc_sequence(I,O1,N1), !, 
 //			plog:token:atomname_quoted_chars(O1,O,N2), !, internal:append(N1,N2,N).
 // plog:token:atomname_quoted_chars(I,O,[]) :- plog:token:squote(I,O,_), !.
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
		newAtom('plog:token:atomname_quoted_chars',[newVariable('I'),newVariable('O'),newListNull()]),
		newConsPairsFromTerms([
			newAtom('plog:token:squote',[newVariable('I'),newVariable('O'),newVariable('_')]),
			newConstant('!')]))),
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
 // plog:token:string_quoted_chars(I,O,[]) :- plog:token:dquote(I,O,_), !.
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
		newAtom('plog:token:string_quoted_chars',[newVariable('I'),newVariable('O'),newListNull()]),
		newConsPairsFromTerms([
			newAtom('plog:token:dquote',[newVariable('I'),newVariable('O'),newVariable('_')]),
			newConstant('!')]))),
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


 // plog:op(I,O,A,P,T) :- plog:token:atomname(I,O,A), current_op(P,T,A).
 // I is the input, O the remaining chars, A the atomname, P the op priority, T the op type. 
 {
  addRuleSet(kb,new RuleSet('plog:token:op',5,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:token:op',[newVariable('I'),newVariable('O'),newVariable('A'),newVariable('P'),newVariable('T'),]),
		newConsPairsFromTerms([
			newAtom('plog:token:atomname',[newVariable('I'),newVariable('O'),newVariable('A')]),
			newAtom('current_op',[newVariable('P'),newVariable('T'),newVariable('A')])
			]))),
	true); 
 }


 // next_token(+N,+W,+I,-O,-T,+L) N is the name of the token, W is true if leading whitespace ignored, 
 // I is the input char list, O is the remainder of the input after token is removed,
 // T is the token in its preferred form, L is a list of other terms of interest (typically []).
 // plog:next_token(N,W,I,O,T,L) :- (W = true, plog:token:blank(I,O1,_) ; I = O1), !, 
 //			atom_concat('plog:token:',N,N1), internal:append([N1,O1,O,T],L,L1), X =.. L1, !, call(X).
 {
  addRuleSet(kb,new RuleSet('plog:next_token',6,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:next_token',[newVariable('N'),newVariable('W'),newVariable('I'),newVariable('O'),newVariable('T'),newVariable('L')]),
		newConsPairsFromTerms([
			newOrPair(
				newConsPair(
					newAtom('=',[newVariable('W'),newConstant('true')]),
					newAtom('plog:token:blank',[newVariable('I'),newVariable('O1'),newVariable('_')])),
				newAtom('=',[newVariable('I'),newVariable('O1')])),
			newConstant('!'),
			newAtom('atom_concat',[newConstant('plog:token:'),newVariable('N'),newVariable('N1')]),
			newAtom('internal:append',[
				newListFromTerms([newVariable('N1'),newVariable('O1'),newVariable('O'),newVariable('T')]),
				newVariable('L'),newVariable('L1')]),
			newAtom('=..',[newVariable('X'),newVariable('L1')]),
			newConstant('!'),
			newAtom('call',[newVariable('X')])
			]))),
	true); 
 }


 // term(+I,-O,-T) I is the input char list, O is the remainder list, T is the term enclosure.
 // plog:term(I,O,A) :- plog:subterm(I,O1,T,1200), plog:next_token('period',true,O1,O,_,[]), !.
 {
  addRuleSet(kb,new RuleSet('plog:term',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:term',[newVariable('I'),newVariable('O'),newVariable('T')]),
		newConsPairsFromTerms([
			newAtom('plog:subterm',[newVariable('I'),newVariable('O1'),newVariable('T1'),newNumber(1200)]),
			newAtom('plog:next_token',[newConstant('period'),newConstant('true'),newVariable('O1'),newVariable('O'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:util:objectmake_enclosure',[newVariable('T1'),newVariable('T')])
			]))),
	true); 
 }


 // subterm(+I,-O,-T,+N) I is the input char list, O is the remainder list, T is the term obj-ref,
 // N is the term priority number.
 // plog:subterm(I,O,T,N) :- plog:token:blank(I,O1,_), !, plog:term(O1,O,T,M), M =< N, !.
 {
  addRuleSet(kb,new RuleSet('plog:subterm',4,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:subterm',[newVariable('I'),newVariable('O'),newVariable('T'),newVariable('N')]),
		newConsPairsFromTerms([
			newAtom('plog:token:blank',[newVariable('I'),newVariable('O1'),newVariable('_')]),
			newConstant('!'),
			newAtom('plog:term',[newVariable('O1'),newVariable('O'),newVariable('T'),newVariable('M')]),
			newAtom('=<',[newVariable('M'),newVariable('N')]),
			newConstant('!')
			]))),
	true); 
 }


 // term(+I,-O,-T,-N) I is the input char list, O is the remainder list,
 // T is the term obj-ref, N is the priority value of the term.
 // plog:term(I,O,A,0) :- plog:next_token('atomname',true,I,O1,A1,[]), 
 //			plog:atomname_term(A1,O1,O,A), !. 
 // plog:term(I,O,A,0) :- plog:next_token('lparen',true,I,O1,_,[]), plog:subterm(O1,O2,A,1200),
 //			plog:next_token('rparen',true,O2,O,_,[]), !.
 // plog:term(I,O,A,0) :- plog:next_token('lbrace',true,I,O1,_,[]), plog:subterm(O1,O2,A1,1200),
 //			plog:next_token('rbrace',true,O2,O,_,[]), !, L1=[A1], plog:util:makeobject_atom('{}',L1,A).
 // plog:term(I,O,L,0) :- plog:list(I,O,L), !.
 // plog:term(I,O,L,0) :- plog:token:string(I,O,L1), !, plog:util:makeobject_list(L1,L).
 // plog:term(I,O,N,0) :- plog:token:number(I,O,N1), !, plog:util:makeobject_number(N1,N).
 // plog:term(I,O,V,0) :- plog:token:variable(I,O,V1), !, plog:util:makeobject_var(V1,V). 
 {
  addRuleSet(kb,new RuleSet('plog:term',4,false));

  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:term',[newVariable('I'),newVariable('O'),newVariable('A'),newNumber(0)]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('atomname'),newConstant('true'),newVariable('I'),newVariable('O1'),newVariable('A1'),newListNull()]),
			newAtom('plog:atomname_term',[newVariable('A1'),newVariable('O1'),newVariable('O'),newVariable('A')]),
			newConstant('!')]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:term',[newVariable('I'),newVariable('O'),newVariable('A'),newNumber(0)]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('lparen'),newConstant('true'),newVariable('I'),newVariable('O1'),newVariable('_'),newListNull()]),
			newAtom('plog:subterm',[newVariable('O1'),newVariable('O2'),newVariable('A'),newNumber(1200)]),
			newAtom('plog:next_token',[newConstant('rparen'),newConstant('true'),newVariable('O2'),newVariable('O'),newVariable('_'),newListNull()]),
			newConstant('!')
			]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:term',[newVariable('I'),newVariable('O'),newVariable('A'),newNumber(0)]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('lbrace'),newConstant('true'),newVariable('I'),newVariable('O1'),newVariable('_'),newListNull()]),
			newAtom('plog:subterm',[newVariable('O1'),newVariable('O2'),newVariable('A1'),newNumber(1200)]),
			newAtom('plog:next_token',[newConstant('rbrace'),newConstant('true'),newVariable('O2'),newVariable('O'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('=',[newVariable('L1'),newListFromTerms([newVariable('A1')])]),
			newAtom('plog:util:makeobject_atom',[newConstant('{}'),newVariable('L1'),newVariable('A')])
			]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:term',[newVariable('I'),newVariable('O'),newVariable('L'),newNumber(0)]),
		newConsPairsFromTerms([
			newAtom('plog:list',[newVariable('I'),newVariable('O'),newVariable('L')]),
			newConstant('!')]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:term',[newVariable('I'),newVariable('O'),newVariable('L'),newNumber(0)]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('string'),newConstant('true'),newVariable('I'),newVariable('O'),newVariable('L'),newListNull()]),
			newConstant('!')]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:term',[newVariable('I'),newVariable('O'),newVariable('N'),newNumber(0)]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('number'),newConstant('true'),newVariable('I'),newVariable('O'),newVariable('N1'),newListNull()]),
			newConstant('!'),
			newAtom('plog:util:makeobject_number',[newVariable('N1'),newVariable('N')])]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:term',[newVariable('I'),newVariable('O'),newVariable('V'),newNumber(0)]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('variable'),newConstant('true'),newVariable('I'),newVariable('O'),newVariable('V1'),newListNull()]),
			newConstant('!'),
			newAtom('plog:util:makeobject_var',[newVariable('V1'),newVariable('V')])]))),
	true); 
 }

 // atomname_term(+N,-I,-O,-A) I is the input char list, O is the remainder list,
 // A is the complete atom term obj-ref, N is the atom symbol.
 // plog:atomname_term(N,I,O,A) :- plog:next_token('lparen',fail,I,O1,_,[]), !, 
 //			plog:arguments(O1,O2,A1), plog:next_token('rparen',true,O2,O,_,[]), !, 
 //			plog:util:makeobject_atom(N,A1,A).
 // plog:atomname_term(N,I,I,A) :- !, plog:util:makeobject_constant(N,A).
 {
  addRuleSet(kb,new RuleSet('plog:atomname_term',4,false));

  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:atomname_term',[newVariable('N'),newVariable('I'),newVariable('O'),newVariable('A')]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('lparen'),newConstant('fail'),newVariable('I'),newVariable('O1'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:arguments',[newVariable('O1'),newVariable('O2'),newVariable('A1')]),
			newAtom('plog:next_token',[newConstant('rparen'),newConstant('true'),newVariable('O2'),newVariable('O'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:util:makeobject_atom',[newVariable('N'),newVariable('A1'),newVariable('A')])
			]))),
	true); 
  addRule(kb,newRule(
	newRuleTerm(
    	newAtom('plog:atomname_term',[newVariable('N'),newVariable('I'),newVariable('I'),newVariable('A')]),
		newConsPairsFromTerms([
			newConstant('!'),
			newAtom('plog:util:makeobject_constant',[newVariable('N'),newVariable('A')])]))),
	true); 
 }
 
 
 // arguments(+I,-O,-T) I is the input char list, O is the remainder list, T is a list of the term obj-refs.
 // plog:arguments(I,O,T) :- plog:subterm(I,O1,T1,999), plog:arguments2(O1,O,T2), !, T=[T1|T2].
 {
  addRuleSet(kb,new RuleSet('plog:arguments',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:arguments',[newVariable('I'),newVariable('O'),newVariable('T')]),
		newConsPairsFromTerms([
			newAtom('plog:subterm',[newVariable('I'),newVariable('O1'),newVariable('T1'),newNumber(999)]),
			newAtom('plog:arguments2',[newVariable('O1'),newVariable('O'),newVariable('T2')]),
			newConstant('!'),
			newAtom('=',[newVariable('T'),newListPair(newVariable('T1'),newVariable('T2'))])]))),
	true); 
 } 

 // plog:arguments2(I,O,T) :- plog:next_token('comma',true,I,O1,_,[]), !, plog:arguments(O1,O,T).
 // plog:arguments2(I,I,[]).
 {
  addRuleSet(kb,new RuleSet('plog:arguments2',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:arguments2',[newVariable('I'),newVariable('O'),newVariable('T')]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('comma'),newConstant('true'),newVariable('I'),newVariable('O1'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:arguments',[newVariable('O1'),newVariable('O'),newVariable('T')])]))),
	true); 
  addRule(kb,newRule(
		newAtom('plog:arguments2',[newVariable('I'),newVariable('I'),newListNull()])),
	true); 
 } 


 // list(+I,-O,-L) I is the input char list, O is the remainder list, L is the terms list obj-ref.
 // plog:list(I,O,L) :- plog:next_token('two_blocks',true,I,O,_,[]), !, plog:util:makeobject_nulllist(L).
 // plog:list(I,O,L) :- plog:next_token('lblock',true,I,O1,_,[]), !, plog:list_expr(O1,O2,L1), !,  
 //				plog:next_token('rblock',true,O2,O,_,[]), !, plog:util:makeobject_list(L1,L).
 {
  addRuleSet(kb,new RuleSet('plog:list',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:list',[newVariable('I'),newVariable('O'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('two_blocks'),newConstant('true'),newVariable('I'),newVariable('O'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:util:makeobject_nulllist',[newVariable('L')])]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:list',[newVariable('I'),newVariable('O'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('lblock'),newConstant('true'),newVariable('I'),newVariable('O1'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:list_expr',[newVariable('O1'),newVariable('O2'),newVariable('L1')]),
			newConstant('!'),
			newAtom('plog:next_token',[newConstant('rblock'),newConstant('true'),newVariable('O2'),newVariable('O'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:util:makeobject_list',[newVariable('L1'),newVariable('L')])]))),
	true); 
 }
 
 // list_expr(+I,-O,-L) I is the input char list, O is the remainder list, L is the terms list.
 // plog:list_expr(I,O,L) :- plog:subterm(I,O1,L1,999), !, plog:list_tail(O1,O,L2), !, L=[L1|L2].
 {
  addRuleSet(kb,new RuleSet('plog:list_expr',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:list_expr',[newVariable('I'),newVariable('O'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('plog:subterm',[newVariable('I'),newVariable('O1'),newVariable('L1'),newNumber(999)]),
			newConstant('!'),
			newAtom('plog:list_tail',[newVariable('O1'),newVariable('O'),newVariable('L2')]),
			newConstant('!'),
			newAtom('=',[newVariable('L'),newListPair(newVariable('L1'),newVariable('L2'))])]))),
	true); 
 }

 // plog:list_tail(I,O,L) :- plog:next_token('comma_dot_dot',true,I,O1,_,[]), !, plog:subterm(O1,O,L,999), !.
 // plog:list_tail(I,O,L) :- plog:next_token('comma',true,I,O1,_,[]), !, plog:list_expr(O1,O,L), !.
 // plog:list_tail(I,O,L) :- plog:next_token('bar',true,I,O1,_,[]), !, plog:subterm(O1,O,L,999), !.
 // plog:list_tail(I,I,[]).
 {
  addRuleSet(kb,new RuleSet('plog:list_tail',3,false));
 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:list_tail',[newVariable('I'),newVariable('O'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('comma_dot_dot'),newConstant('true'),newVariable('I'),newVariable('O1'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:subterm',[newVariable('O1'),newVariable('O'),newVariable('L'),newNumber(999)]),
			newConstant('!')]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:list_tail',[newVariable('I'),newVariable('O'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('comma'),newConstant('true'),newVariable('I'),newVariable('O1'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:list_expr',[newVariable('O1'),newVariable('O'),newVariable('L')]),
			newConstant('!')]))),
	true); 
  addRule(kb,newRule(
    newRuleTerm(
		newAtom('plog:list_tail',[newVariable('I'),newVariable('O'),newVariable('L')]),
		newConsPairsFromTerms([
			newAtom('plog:next_token',[newConstant('bar'),newConstant('true'),newVariable('I'),newVariable('O1'),newVariable('_'),newListNull()]),
			newConstant('!'),
			newAtom('plog:subterm',[newVariable('O1'),newVariable('O'),newVariable('L'),newNumber(999)]),
			newConstant('!')]))),
	true); 
  addRule(kb,newRule(
		newAtom('plog:list_tail',[newVariable('I'),newVariable('I'),newListNull()])),
	true); 
 }


 // makeobject_var(N,V) : creates an object term V containing a Variable named N.term.name
 {
  addRuleSet(kb,new RuleSet('plog:util:makeobject_var',2,false));

  addRule(kb,newFunctionRule(
  		newAtom('plog:util:makeobject_var',[newVariable('N'),newVariable('V')]),parser_makeobject_var_fn));
 }
 // makeobject_number(N,V) : creates an object term V containing a Number with value N.term.name
 {
  addRuleSet(kb,new RuleSet('plog:util:makeobject_number',2,false));

  addRule(kb,newFunctionRule(
  		newAtom('plog:util:makeobject_number',[newVariable('N'),newVariable('V')]),parser_makeobject_number_fn));
 }
 // makeobject_constant(N,A) : creates an object term A containing a constant (atom/0) term with 
 // name N.term.name
 {
  addRuleSet(kb,new RuleSet('plog:util:makeobject_constant',2,false));

  addRule(kb,newFunctionRule(
  		newAtom('plog:util:makeobject_constant',[newVariable('N'),newVariable('A')]),parser_makeobject_constant_fn));
 }
 // makeobject_atom(N,L,A) : creates an object term A containing an atom term with name N.term.name
 // and arguments from each element object ref term in list L.
 {
  addRuleSet(kb,new RuleSet('plog:util:makeobject_atom',3,false));

  addRule(kb,newFunctionRule(
  		newAtom('plog:util:makeobject_atom',[newVariable('N'),newVariable('L'),newVariable('A')]),parser_makeobject_atom_fn));
 }
 // makeobject_list(L,T) : creates an object term T containing a list term containing 
 // term elements of list L.
 {
  addRuleSet(kb,new RuleSet('plog:util:makeobject_list',2,false));

  addRule(kb,newFunctionRule(
  		newAtom('plog:util:makeobject_list',[newVariable('L'),newVariable('T')]),parser_makeobject_list_fn));
 }
 // makeobject_nulllist(L) : creates an object term L containing a listnull term.
 {
  addRuleSet(kb,new RuleSet('plog:util:makeobject_nulllist',1,false));

  addRule(kb,newFunctionRule(
  		newAtom('plog:util:makeobject_nulllist',[newVariable('L')]),parser_makeobject_nulllist_fn));
 }

 // objectmake_enclosure(O,T) : creates an enclosure T for the term inside object ref O.
 {
  addRuleSet(kb,new RuleSet('plog:util:objectmake_enclosure',2,false));

  addRule(kb,newFunctionRule(
  		newAtom('plog:util:objectmake_enclosure',[newVariable('O'),newVariable('T')]),parser_objectmake_enclosure_fn));
 }
 
} 

///////////////////////////////////
// jslog_parser_*_fn
///////////////////////////////////

function parser_makeobject_var_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 
 if (!isConstant(lhs.term))
  throw newErrorException("Expected LHS to evaluate to a constant: makeobject_var/2");

 var obj = newObjectReference(newVariable(lhs.term.name));
   
 return jslog_unify(rhs,newBlankEnclosure(0,obj),goal.bindings);
}

function parser_makeobject_number_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 
 if (!isNumber(lhs.term))
  throw newErrorException("Expected LHS to evaluate to a number: makeobject_number/2");

 var obj = newObjectReference(lhs.term);
   
 return jslog_unify(rhs,newBlankEnclosure(0,obj),goal.bindings);
}

function parser_makeobject_constant_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);

 if (!isConstant(lhs.term))
  throw newErrorException("Expected LHS to evaluate to a constant: makeobject_constant/2");

 var obj = newObjectReference(lhs.term);
   
 return jslog_unify(rhs,newBlankEnclosure(0,obj),goal.bindings);
}

function parser_makeobject_atom_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var lst = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[1]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[2]);
 
 if (!isConstant(lhs.term))
  throw newErrorException("Expected LHS to evaluate to a constant: makeobject_atom/2");

 var arr = new Array();

 while (isListPair(lst.term))
 {
  var t = getFinalEnclosure(newSubtermEnclosure(lst.enclosure,lst.term.children[0]));
  
  if (!isObjectReference(t.term))
   throw newErrorException("Expected list of object references: makeobject_atom/2");

  arr.push(t.term.name);
    
  lst = getFinalEnclosure(newSubtermEnclosure(lst.enclosure,lst.term.children[1]));
 }

 if (!isListNull(lst.term))
  throw newErrorException("Expected LIST to evaluate to a list: makeobject_atom/2");

 var obj = newObjectReference(newAtom(lhs.term.name,arr));
   
 return jslog_unify(rhs,newBlankEnclosure(0,obj),goal.bindings);
}

function parser_makeobject_list_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]); 
 var arr = new Array();

 while (isListPair(lhs.term))
 {
  var t = getFinalEnclosure(newSubtermEnclosure(lhs.enclosure,lhs.term.children[0]));
  
  if (isObjectReference(t.term))
  {
   arr.push(t.term.name);
  }
  else
  {
   arr.push(t.term);
  }
    
  lhs = getFinalEnclosure(newSubtermEnclosure(lhs.enclosure,lhs.term.children[1]));
 }
 
 var lterm = null;
 
 if (isListNull(lhs.term))
 {
  lterm = newListNull();
 }
 else if (isObjectReference(lhs.term))
 {
  lterm = lhs.term.name;
 }
 else
 {
   lterm = lhs.term;
 }
  
 var elem;
 while ((elem = arr.pop()) != undefined)
 {
  lterm = newListPair(elem,lterm);
 }
  
 var obj = newObjectReference(lterm);
   
 return jslog_unify(rhs,newBlankEnclosure(0,obj),goal.bindings);
}

function parser_makeobject_nulllist_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = newSubtermEnclosure(encl.enclosure,encl.term.children[0]);

 var obj = newObjectReference(newListNull());
   
 return jslog_unify(lhs,newBlankEnclosure(0,obj),goal.bindings);
}

function parser_objectmake_enclosure_fn(goal)
{var encl = getFinalEnclosure(goal.encl);
 var lhs = getFinalEnclosure(newSubtermEnclosure(encl.enclosure,encl.term.children[0]));
 var rhs = newSubtermEnclosure(encl.enclosure,encl.term.children[1]);
 
 if (!isObjectReference(lhs.term))
  throw newErrorException("Expected LHS to evaluate to an object reference: objectmake_enclosure/2");

 return jslog_unify(rhs,newTermEnclosure(lhs.term.name),goal.bindings);
}

