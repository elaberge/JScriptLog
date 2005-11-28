JScriptLog: Prolog in JavaScript
Created by Glendon Holst.  Copyright 2005.

INTRODUCTION:

JScriptLog version 0.5.5.alpha is an exploratory implementation of Prolog in JavaScript.  It has potential, and is released in this early development phase in hopes that it may prove useful (Prolog joke ;-).  It can solve the 8-Queens problem (but about 30x slower than JLog).

The available built-in predicates are (almost all of) the Control, Meta, Comparison, Arithmetic, Clausal Database, and Solution Collection predicates in the ISO standard (i.e., the non-I/O predicates).

It has some shortcomings, and room for improvement.


CRITIAL SHORTCOMINGS:

* There is no parser.  It is possible to construct the terms directly (see existing code and queries for N-Queens).  See patch #1311136 for the writeJSLog/1 converter tool, which constructs the terms directly from the given Prolog source code, using an external Prolog interpreter, such as JLog.  A future goal is to write the parser for JScriptLog in Prolog itself.

* Some notable missing predicates are: control predicate (catch/3), miscellaneous (op/3, dynamic/1, current_op/3, current_prolog_flag/2, set_prolog_flag/2), term display and input predicates (write_term/1, write_canonical/1, writeq/1, read_term/1, read/1), consulting predicates (consult/1, include/1, ensure_loaded/1), DCG predicates (e.g., -->), and the stream based I/O predicates.

* There is no post-consult optimization phase (e.g., pre-binding).  There is room for performance improvement.


OTHER ISSUES:

* JavaScript is not multi-threading, and may lock up the browser until query completes (beware infinite recursion).


FUTURE GOALS:

Even though very incomplete, I prefer the JScriptLog implementation of Prolog to that in JLog, and it's design has much greater potential -- though in practise it would only be suitable for small domains.  It is a platform for me to experiment with various implementation ideas as I have time.  The goal is elegance of implementation, small size, and performance where possible within the previous constraints.