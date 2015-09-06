These files contain definitions and proof scripts related to the correctness of:

File list:

misc_arith.v: generic arithmetic related lemmas;
misc_list.v: generic list lemmas;
cfg.v: definitions and basic lemmas regarding context-free grammars and derivations;
emptyrules.v: elimination of empty rules in a context-free grammar;
unitrules.v: elimination of unit rules in a context-free grammar;
inaccessible.v: elimination of inaccessible symbols in a context-free grammar;
useless.v: elimination of useless symbols in a context-free grammar;
simplification.v: unification of all previous results.

To compile use, download all files and:
coq_makefile -f > _makefile
make -f _makefile

These files have been created and compiled with the Coq Proof Assistant, version 8.4pl4 (June 2014).simplification algorithms for context-free grammars, namely empty rules elimination, unit rules elimination, useless symbol elimination and inaccessible symbol elimination. More information can be found in the paper "Formalization of simplification for context-free grammars", LSFA 2015. Marcus Vinícius Midena Ramos Ruy J. G. B. de Queiroz mvmramos@gmail.com
