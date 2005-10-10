JScriptLog: Prolog in JavaScript
Created by Glendon Holst.  Copyright 2005.

INTRODUCTION:

JScriptLog version 0.4.alpha is an exploratory, partial implementation of Prolog in JavaScript.  It has potential, and is released in this early development phase in hopes that it may prove useful (Prolog joke ;-).  It can solve the 8-Queens problem (but about 30x slower than JLog).

It has some critical shortcomings, and room for improvement.

CRITIAL SHORTCOMINGS:

* There is no parser.  It is possible to construct the terms directly (see existing code and queries for N-Queens).  See patch #1311136 for the writeJSLog/1 converter tool, which constructs the terms directly from the given Prolog source code, using an external Prolog interpreter, such as JLog.  A future goal is to write the parser for JScriptLog in Prolog itself.

* The available built in predicates are an incomplete subset of the ISO standard (but sufficient for most typical Prolog KBs, such as the N-Queens solution).  Some notable missing predicates are: control predicates (if/3, ->/2, ->;/3, halt/0, halt/1, catch/3, throw/1), term predicates (integer/1, float/1, arg/3, unify_with_occurs_check/2, the atom/number/char/codes set of predicates), term comparison (@</2, @=</2, @>/2, @>=/2), database predicates (abolish/1, clause/2), collecting solutions (bagof/3, setof/3).

* There is no post-consult optimization phase (e.g., pre-binding).  There is room for performance improvement.

POSSIBLE IMPROVEMENTS:

* 'FIX:' comments throughout code indicate areas of improvement.

* Add a Transform module for term translations to support optimizations (e.g., pre-binding, constant expression evaluation, duplicate removal).

* Improve efficiency of code paths for goals in try and retry (e.g., optimize KB Predicate rule to assume the ruleset is bound to KB predicate -- no test for other goal types).

* Properly support tail-recursion optimizations to save stack space (e.g., if goal can't retry, merge with previous sibling-goal).

* Support operators / precedence during display and parsing (encode in KB rulesets). 

* Add [ISO] predicates from chapter 6 of the YAP Prolog manual (except those for sockets / streams or services which Javascript doesn't support).

* Rewrite display / unify / evaluate expression / some of prove to use generic tree traversal (possible code size reduction without performance penalty?).

* Rewrite the builtin predicate functions in KB which are very similar using generic functions and a parameterized operator.

* Add real documentation (listing of available predicates / operators).

* Not fully tested, except for provided queries.  Only tested in Safari 2 and OmniWeb 5 browsers.  A full automated testing system is needed to test each supported predicate, and do regression testing. 

OTHER ISSUES:

* JavaScript is not multi-threading, and may lock up the browser until query completes (beware infinite recursion).

FUTURE GOALS:

Even though very incomplete, I prefer the JScriptLog implementation of Prolog to that in JLog, and it's design has much greater potential -- though in practise it would only be suitable for small domains.  It is a platform for me to experiment with various implementation ideas as I have time.  The goal is elegance of implementation, small size, and performance where possible within the previous constraints.