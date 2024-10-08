Typed-PEG-Stack
============

Intro
------

A racket language for PEGs with types and stack. This implementation extends the PEG language to encompass
stack operations,  as in the PEST parsers. In addition to these operations we also include two new
operations that allow to access the top of the stack and use these values in simple computations.
The new operations are checked by the type-system to assure no operations can loop. 
  
Requirements
---------------

In order to type check, the tool need a working installation of 
[Z3 SMT Solver](https://github.com/Z3Prover/z3). The project is known to work with 
Z3 version 4.8.14.

Languages
-----------

Following the racket approach to build small languages, we have build some auxiliar languages 
to ease the task of use/debug the tool.

* `#lang typed-peg`: default language, provides a parse and pretty printing function for the
specified PEG, after infering types for the input PEG.
* `#lang pest-control/debug/parse-only`: outputs the result of the parser.
* `#lang pest-control/debug/constraints-only`: outputs the constraints generated by the algorithm.
* `#lang pest-control/debug/z3-script-only`: outputs the z3 script that encode the constraints.
* `#lang pest-control/debug/infer-only`: outputs the infered types for each grammar non-terminal.
