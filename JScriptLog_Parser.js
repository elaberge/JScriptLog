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
 throw jslog_parse_token(in_src);
}

// returns the next token
function jslog_parse_token(in_src)
{
 var clause = /(\w+\.)|(\w+\(\w+(\,\w+)*\)\.)/g;
 var nonclause = /(?!(\w+\.)|(\w+\(\w+(\,\w+)*\)\.))/g;
 var pos = in_src.search(clause); 

 return in_src.match(clause);
// return in_src.match(nonclause);
// RegExp
}
