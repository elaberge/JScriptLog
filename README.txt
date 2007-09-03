JScriptLog: Prolog in JavaScript
Created by Glendon Holst.  Copyright 2005, 2006.

INTRODUCTION:

JScriptLog version 0.7.5.beta is an implementation of ISO-Standard Prolog in JavaScript.  It has potential, and is released in hopes that it may prove useful (Prolog joke ;-).  It can solve the 8-Queens problem (about 30x slower than JLog) and Prolog meta-interpret that same solution too.

The available built-in predicates are the Control, Meta, Comparison, Arithmetic, Clausal Database, Solution Collection, and (almost all) Miscellaneous predicates in the ISO standard (i.e., the non-I/O predicates).

It has some shortcomings and room for improvement.


SHORTCOMINGS:

* The experimental parser is very basic and not suitable for more than simple queries.  It does not give advice on syntax errors (e.g., their location or cause), it does not handle infix operators (i.e., it is primarily suitable for basic single-atom / predicate queries), and it is too slow for consulting KBs.

It is possible to construct the terms directly (see existing code and queries for N-Queens).  See patch #1311136 for the writeJSLog/1 converter tool, which constructs the terms directly from the given Prolog source code, using an external Prolog interpreter, such as JLog.  

* Some notable missing predicates are: miscellaneous (op/3, dynamic/1, current_prolog_flag/2, set_prolog_flag/2), term display and input predicates (write_term/1, write_canonical/1, writeq/1, read_term/1, read/1), consulting predicates (consult/1, include/1, ensure_loaded/1), DCG predicates (e.g., -->), and the stream based I/O predicates.

* The post-consult optimization phase (e.g., pre-binding) is incomplete.  It doesn't perform constant propagation, and it is limited in the nested-depth of terms in the KB  (i.e., not terms constructed during runtime).


OTHER ISSUES:

* JavaScript is not multi-threading, and may lock up the browser until query completes (beware infinite recursion).


FUTURE GOALS:

I prefer the JScriptLog implementation of Prolog to that in JLog, and it's design has much greater potential -- though in practise it would only be suitable for small domains.  It is a platform for me to experiment with various implementation ideas as I have time.  The goal is elegance of implementation, small size, and performance where possible within the previous constraints.