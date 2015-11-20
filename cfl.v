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
(* CONTEXT FREE LANGUAGES                                                *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.
Require Import emptyrules.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* CONTEXT-FREE LANGUAGES - DEFINITIONS                                  *)
(* --------------------------------------------------------------------- *)

Section ContextFreeLanguages_Definitions.

Variables non_terminal terminal: Type.

Notation sentence:= (list terminal).
 
Definition lang := sentence -> Prop.

Definition lang_of_g (g: cfg non_terminal terminal): lang :=
fun w: sentence => produces g w.

Definition lang_eq (l k: lang) := 
forall w, l w <-> k w.

Definition contains_empty (l: lang): Prop:=
l [].

Definition contains_non_empty (l: lang): Prop:=
exists w: sentence,
l w /\ w <> [].

End ContextFreeLanguages_Definitions.

Infix "==" := lang_eq (at level 80). 

Definition cfl (terminal: Type) (l: lang terminal): Prop:=
exists non_terminal: Type, 
exists g: cfg non_terminal terminal, 
l == lang_of_g g.

(* --------------------------------------------------------------------- *)
(* CONTEXT-FREE LANGUAGES - LEMMAS                                       *)
(* --------------------------------------------------------------------- *)

Section ContextFreeLanguages_Lemma.

Variables non_terminal non_terminal' terminal: Type.

Lemma produces_empty_equiv_contains_empty:
forall g: cfg non_terminal terminal,
produces_empty g <-> contains_empty (lang_of_g g).
Proof.
intros g.
unfold produces_empty.
unfold contains_empty.
unfold lang_of_g.
split; auto.
Qed.

Lemma produces_non_empty_equiv_contains_non_empty:
forall g: cfg non_terminal terminal,
produces_non_empty g <-> contains_non_empty (lang_of_g g).
Proof.
intros g.
unfold produces_non_empty.
unfold contains_non_empty.
unfold lang_of_g.
split; auto.
Qed.

Lemma g_equiv_lang_eq:
forall g: cfg non_terminal terminal,
forall g': cfg non_terminal' terminal,
g_equiv g' g -> lang_of_g g' == lang_of_g g.
Proof.
unfold g_equiv.
unfold lang_of_g.
unfold lang_eq.
intros g g' H1.
split.
- intros H2.
  apply H1.
  exact H2.
- intros H2.
  apply H1.
  exact H2.
Qed.

Lemma lang_eq_sym:
forall l1 l2: lang terminal,
l1 == l2 ->
l2 == l1.
Proof.
unfold lang_eq.
intros l1 l2 H1 w.
split.
- intros H2.
  apply H1.
  exact H2.
- intros H2.
  apply H1.
  exact H2.
Qed.

Lemma lang_eq_trans:
forall l1 l2 l3: lang terminal,
l1 == l2 ->
l2 == l3 ->
l1 == l3.
Proof.
unfold lang_eq.
intros l1 l2 l3 H1 H3 w.
split.
- intros H4.
  apply H3.
  apply H1.
  exact H4.
- intros H4.
  apply H1.
  apply H3.
  exact H4.
Qed.

Lemma lang_eq_change_g:
forall l: lang terminal,
forall g: cfg non_terminal terminal,
forall g': cfg non_terminal' terminal,
l == lang_of_g g -> 
g_equiv g' g ->
l == lang_of_g g'.
Proof.
intros l g g' H1 H2.
apply g_equiv_lang_eq in H2.
apply lang_eq_trans with (l2 := lang_of_g g).
- exact H1.
- apply lang_eq_sym.
  exact H2.
Qed.

End ContextFreeLanguages_Lemma.
