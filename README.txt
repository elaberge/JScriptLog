JScriptLog: Prolog in JavaScript
Created by Glendon Holst.  Copyright 2005.

INTRODUCTION:

JScriptLog version 0.1.alpha is an exploratory, partial implementation of Prolog in JavaScript.  It has potential, and is released in this early development phase in hopes that it may prove useful (Prolog joke ;-).  It can solve the 8-Queens problem (but about 30x slower than JLog).

It has many critical shortcomings, and lots of room for improvement.

CRITIAL SHORTCOMINGS:

* There is no parser.  It is possible to construct the terms directly (see existing code and queries for N-Queens).  A future goal is to write the parser in Prolog itself. 

* Does not fully evaluate expressions.  The is/2 predicate only solves for a single, simple (+,-,*,/) binary operation.

* The available built in predicates are very limited (sufficient  for the N-Queens KB example).

* There is no post-consult optimization phase (e.g., pre-binding).  There is room for performance improvement.

POSSIBLE IMPROVEMENTS:

* 'FIX:' comments throughout code indicate areas of improvement.

* Rewrite display / unify / evaluate expression / some of prove to use generic tree traversal (possible code size reduction without performance penalty?).

* Improve efficiency of code paths for goals in try and retry (e.g., optimize KB Predicate rule to assume the ruleset is bound  to KB predicate -- no test for other goal types).

* Support operators / precedence during display and parsing (encode in KB rulesets). 

* Add real documentation (listing of available predicates / operators).

* Not fully tested, except for provided queries.  Only tested in Safari 2 and OmniWeb 5 browsers.

OTHER ISSUES:

* JavaScript is not multi-threading, and may lock up the browser until query completes (beware infinite recursion).

FUTURE GOALS:

Even though very incomplete, I prefer the JScriptLog implementation of Prolog to that in JLog, and it's design has much greater potential -- though in practise it would only be suitable for small domains.  It is a platform for me to experiment with various implementation ideas as I have time.  The goal is elegance of implementation, small size, and performance where possible within the previous constraints.