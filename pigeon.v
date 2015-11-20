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
Require Import NPeano.
Require Import Classical_Prop.

Require Import misc_arith.
Require Import misc_list.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* PIGEONHOLE PRINCIPLE                                                  *)
(* --------------------------------------------------------------------- *)

Inductive remove {A} (a:A): list A -> list A -> Prop :=
 | remove_nil: remove a nil nil
 | remove_na: forall x xs ys, x <> a -> remove a xs ys -> remove a (x :: xs) (x :: ys)
 | remove_a: forall xs ys, remove a xs ys -> remove a (a :: xs) ys.

Lemma remove_exists: 
forall {A: Type},
forall a: A,
forall xs: list A,
exists ys: list A, 
remove a xs ys.
Proof.
induction xs.
- exists nil.
  apply remove_nil. 
- elim IHxs; intros.
  generalize (classic (a=a0)); intros [HH|HH].
  subst; exists x; constructor 3; assumption.
  exists (a0 :: x).
  apply remove_na.
  + apply not_eq_sym.
    exact HH.
  + exact H.
Qed.

Lemma remove_notin:
forall {A: Type},
forall a: A,
forall xs ys: list A,
~ In a xs ->
remove a xs ys ->
ys = xs.
Proof.
induction xs. 
- intros ys H1 H2.
  inversion H2.
  reflexivity.
- intros ys H1 H2.
  inversion H2.
  + subst.
    assert (~ In a xs).
      {
      simpl in H1. 
      intros H4. 
      apply H1. 
      right. 
      exact H4. 
      }
    specialize (IHxs ys0 H H5).
    subst.
    reflexivity.
  + subst.
    destruct H1.
    simpl.
    left.
    reflexivity.
Qed.

Lemma remove_length_in: 
forall {A: Type},
forall a: A,
forall xs ys: list A,
In a xs -> 
remove a xs ys -> 
length ys < length xs.
Proof.
intros A a xs ys H1 H2.
revert H1.
induction H2.
- intros H.
  simpl in H.
  contradiction.
- intros H3.
  simpl in H3.
  destruct H3 as [H3 | H3].
  + subst.
    destruct H.
    reflexivity.
  + specialize (IHremove H3).
    simpl.
    omega.
- intros H3. 
  assert (In a xs \/ ~ In a xs). 
    {
    apply classic. 
    }
  destruct H as [H | H].
  + specialize (IHremove H).
    simpl.
    omega.
  + apply remove_notin in H2.
    * subst.
      simpl.
      omega.
    * exact H.
Qed.

Lemma remove_in_notin: 
forall {A: Type},
forall a: A,
forall xs ys: list A,
forall e: A,
remove a xs ys -> 
In e xs -> 
e = a \/ In e ys.
Proof.
intros A a xs ys e H.
revert e.
induction H.
- intros e H.
  simpl in H.
  contradiction.
- intros e H1.
  simpl in H1.
  destruct H1 as [H1 | H1].
  + right. 
    simpl. 
    left. 
    exact H1. 
  + specialize (IHremove e H1).
    destruct IHremove as [IHremove | IHremove]. 
    * left. 
      exact IHremove. 
    * right. 
      simpl.  
      right. 
      exact IHremove.
- intros e H1.
  simpl in H1.
  destruct H1 as [H1 | H1].
  + left. 
    symmetry. 
    exact H1. 
  + specialize (IHremove e H1).
    exact IHremove.
Qed.

Lemma pigeon_aux: 
forall {A: Type},
forall x y: list A,
(forall e, In e x -> In e y) ->
(length x > length y) ->
~ NoDup x.
Proof.
intros. 
red. 
intro.
revert y H H0.
elim H1.
- simpl; intros.
  omega.
- intros.
  simpl in H3.
  generalize (remove_exists x0 y); intros [y' Hy'].
  assert (length y' < length y).
  eapply remove_length_in; auto.
  apply H2 with (y:=y').
  + intros.
    generalize (@remove_in_notin A x0 y y'). 
    intros.
    destruct H7 with e. 
    * exact Hy'. 
    * apply H3.
      right.
      exact H6.
    * subst. 
      destruct H. 
      exact H6. 
    * exact H8. 
  + simpl in H4.
    omega.
Qed.

Lemma nodup_or:
forall A: Type,
forall a: A,
forall x: list A,
~ NoDup (a :: x) ->
~ NoDup x \/ In a x.
Proof.
intros.
apply imply_to_or.
intros.
generalize (classic (In a x)).
intros H1.
destruct H1 as [H1 | H1].
- exact H1. 
- destruct H. 
  constructor. 
  + exact H1.
  + exact H0.
Qed.

Lemma pigeon:
forall A: Type,
forall x y: list A,
(forall e: A, In e x -> In e y) ->
length x = length y + 1->
exists d: A,
exists x1 x2 x3: list A,
x = x1 ++ [d] ++ x2 ++ [d] ++ x3.
Proof.
intros A x y H1 H2.
apply pigeon_aux in H1.
- clear H2.
  induction x.
  + destruct H1. 
    apply NoDup_nil. 
  + assert (~ NoDup x \/ In a x). 
      {
      apply nodup_or.
      exact H1. 
      } 
    destruct H as [H | H]. 
    * specialize (IHx H).
      destruct IHx as [d [x1 [x2 [x3 IHx]]]].
      rewrite IHx. 
      exists d, (a :: x1), x2, x3.
      repeat rewrite <- app_assoc.
      reflexivity.
    * apply in_split in H.
      destruct H as [l1 [l2 H]].
      exists a, [], l1, l2.
      rewrite H.
      simpl.
      reflexivity. 
- omega.
Qed.
