(* ---------------------------------------------------------------------

   This file is part of a repository containing the definitions and 
   proof scripts related to the formalization of context-free language
   theory in Coq. Specifically, the following results were obtained:
   
   (i) closure operations for context-free grammars, 
   (ii) context-free grammars simplification 
   (iii) context-free grammar Chomsky normalization and 
   (iv) pumping lemma for context-free languages.
   
   More information can be found in thesis "Formalization of 
   Context-Free Language Theory", submitted to the Informatics
   Center of the Pernambuco Federal University (CIn/UFPE) in
   Brazil.
   
   The file README.md descbrides the contents of each file and 
   provides instructions to compile them.
   
   Marcus Vinícius Midena Ramos
   mvmramos@gmail.com
   --------------------------------------------------------------------- *)
   
(* --------------------------------------------------------------------- *)
(* EXAMPLE FOR SECTION 6.2.1                                             *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

Inductive terminal: Type:=
| a
| b
| c.

Inductive non_terminal: Type:=
| X
| Y
| Z.

Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation nlist:= (list non_terminal).

Definition sf1: sf:= [inr a; inl X; inl Y; inr b].
Definition sf2: sf:= [].
Definition sentence1: sentence:= [a; a; b; c].
Definition sentence2: sentence:= [].
Definition nlist1: nlist:= [Z; Z; X].
Definition nlist2: nlist:= [].
