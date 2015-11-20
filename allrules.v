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
   
Require Import List.
Require Import Ring.
Require Import Omega.
Require Import Compare_dec.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

Section AllRules.

Variables terminal non_terminal: Type.

Notation symbol:= (non_terminal + terminal)%type.
Notation sf:= (list symbol).
Notation sentence := (list terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).

Notation rlist:= (list (non_terminal * sf)).
Notation tlist:= (list terminal).
Notation nlist:= (list non_terminal).
Notation vlist:= (list symbol).
Notation slist:= (list sf).

Fixpoint concat_symbol (s: non_terminal + terminal) (l: slist): slist:=
match l with
| [] => []
| e :: l' => (s :: e) :: concat_symbol s l'
end.

Lemma concat_symbol_correct:
forall e: symbol,
forall s: sf,
forall l: slist,
In s l ->
In (e :: s) (concat_symbol e l).
Proof.
intros e s l.
generalize dependent e.
generalize dependent s.
induction l.
- intros s e H1.
  simpl in H1.
  contradiction.
- intros s e H1.
  simpl in H1.
  simpl. 
  destruct H1 as [H1 | H1].
  + left.
    rewrite H1.
    reflexivity.
  + right.
    specialize (IHl s e H1).
    exact IHl.
Qed.

Lemma concat_symbol_app_right:
forall s: symbol,
forall l1 l2: slist,
concat_symbol s (l1 ++ l2) = concat_symbol s l1 ++ concat_symbol s l2.
Proof.
intros s.
induction l1.
- simpl.
  reflexivity.
- intros l2.
  simpl. 
  rewrite IHl1.
  reflexivity.
Qed.

Fixpoint concat_list (l1: vlist) (l2: slist): slist:=
match l1 with
| [] => []
| s :: l1' => (concat_symbol s l2) ++ (concat_list l1' l2)
end.

Lemma concat_list_correct:
forall l1: vlist,
forall l2: slist,
forall s: symbol,
forall l: sf,
In s l1 ->
In l l2 ->
In (s :: l) (concat_list l1 l2).
Proof.
intros l1.
induction l1.
- intros l2 s l H1 H2.
  simpl in H1.
  contradiction.
- intros l2 s l H1 H2.
  simpl in H1.
  simpl.
  apply in_or_app.
  destruct H1 as [H1 | H1].
  + subst.
    left.
    apply concat_symbol_correct.
    exact H2.
  + right.
    apply IHl1.
    * exact H1.
    * exact H2.  
Qed.

Lemma concat_list_app_left:
forall v1 v2: vlist,
forall l: slist,
concat_list (v1 ++ v2) l = concat_list (v1) l ++ concat_list (v2) l.
Proof.
induction v1.
- simpl.
  reflexivity.
- intros v2 l.
  simpl.
  rewrite (IHv1 v2 l).
  rewrite <- app_assoc. 
  reflexivity.
Qed.

Lemma concat_list_app_right:
forall s: symbol,
forall l1 l2: slist,
concat_list [s] (l1 ++ l2) = concat_list [s] l1 ++ concat_list [s] l2.
Proof.
induction l1.
- intros l2. 
  simpl.
  reflexivity.
- intros l2.
  simpl.
  repeat rewrite app_nil_r.
  rewrite concat_symbol_app_right.
  reflexivity.  
Qed.

Lemma concat_list_empty:
forall s: symbol,
forall v1 v2: vlist,
In [s] (concat_list (v1 ++ s :: v2) [[]]).
Proof.
intros s v1 v2.
rewrite concat_list_app_left.
apply in_or_app.
right.
simpl.
left.
reflexivity.
Qed.

Lemma concat_list_non_empty:
forall s: symbol,
forall s0: sf,
forall v1 v2: vlist,
forall l1 l2: slist,
In (s :: s0) (concat_list (v1 ++ s :: v2) (l1 ++ s0 :: l2)).
Proof.
intros s s0 v1 v2 l1 l2.
rewrite concat_list_app_left.
apply in_or_app.
right.
change (s :: v2) with ([s] ++ v2).
rewrite concat_list_app_left.
apply in_or_app.
left.
rewrite concat_list_app_right.
apply in_or_app.
right.
simpl.
left.
reflexivity.
Qed.

Fixpoint all_sf_with (n: nat) (v: vlist): slist:=
match n with
| O => [[]]
| S n' => concat_list v (all_sf_with n' v)
end.

Fixpoint all_sf_up_to (n: nat) (v: vlist): slist:=
match n with
| O => [[]]
| S n' => (all_sf_with n v) ++ (all_sf_up_to n' v)
end.

Lemma all_sf_with_correct:
forall v: vlist,
forall s: sf,
forall n: nat,
(forall e: symbol, In e s -> In e v) ->
length s = n ->
In s (all_sf_with n v).
Proof.
intros v s n.
generalize dependent v.
generalize dependent s.
induction n.
- intros s v H0 H1.
  apply length_zero in H1.
  rewrite H1.
  simpl.
  left.
  reflexivity.
- intros s v H0 H1.
  simpl.
  destruct s.
  + simpl in H1.
    discriminate.
  + simpl in H1.
    apply eq_add_S in H1.
    apply concat_list_correct.
    * apply H0.
      simpl. 
      left.
      reflexivity.
    * {
      apply IHn.
      - intros e H2.
        apply H0.
        change (s :: s0) with ([s] ++ s0).
        apply in_or_app.
        right.
        exact H2.
      - exact H1.
      }
Qed.

End AllRules.
