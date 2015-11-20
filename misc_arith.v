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
(* BASIC LEMMAS                                                          *)
(* --------------------------------------------------------------------- *)

Require Import Ring.
Require Import Omega.
Require Import NPeano.
Require Import Even.
Require Import NZPow.

Lemma lep1m2_ltp1:
forall i x: nat, i <= x + 1 - 2 -> i < x + 1.
Proof. 
intros i x H.
omega.
Qed.

Lemma lep1m2_lt:
forall i x: nat, x > 0 -> i <= x + 1 - 2 -> i < x.
Proof. 
intros i x H1 H2.
omega.
Qed.

Lemma gt_any_gt_0:
forall i j: nat,
i > j -> i > 0.
Proof.
intros i j H.
destruct i.
- apply lt_n_0 in H.
  contradiction.  
- apply gt_Sn_O.
Qed.

Lemma lt_1_eq_0:
forall i: nat,
i < 1 -> i = 0.
Proof.
intros i H.
destruct i.
- reflexivity.
- apply lt_S_n in H.
  apply lt_n_0 in H.
  contradiction. 
Qed.

Lemma n_minus_1:
forall n: nat,
n <> 0 -> n-1 < n.
Proof.
intros n H.
destruct n.
- omega.
- omega.
Qed.

Lemma gt_zero_exists:
forall i: nat,
i > 0 ->
exists j: nat, i = S j.
Proof.
intros i H.
destruct i.
- omega.
- exists i.
  reflexivity.
Qed.

Lemma max_n_n:
forall n: nat,
max n n = n.
Proof.
induction n.
- simpl. 
  reflexivity.
- simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma max_n_0:
forall n: nat,
max n 0 = n.
Proof.
destruct n.
- simpl. 
  reflexivity.
- simpl.
  reflexivity.
Qed.

Definition injective (A B: Type) (f: A -> B): Prop:=
forall e1 e2: A,
f e1 = f e2 -> e1 = e2.

Lemma odd_1:
odd 1.
Proof.
apply odd_S.
apply even_O.
Qed.

Lemma pow_le:
forall n n1 n2: nat,
n > 0 ->
n1 <= n2 ->
n ^ n1 <= n ^ n2.
Proof.
intros n n1 n2 H1 H2.
apply Nat.pow_le_mono_r.
- omega.
- exact H2.
Qed.

Lemma pow_lt:
forall n n1 n2: nat,
n > 1 ->
n1 < n2 ->
n ^ n1 < n ^ n2.
Proof.
intros n n1 n2 H1 H2.
apply Nat.pow_lt_mono_r.
- exact H1. 
- exact H2.
Qed.

Lemma nat_struct:
forall n: nat,
n = 0 \/ exists n': nat, n = S n'.
destruct n. 
- left. 
  reflexivity. 
- right.
  exists n.
  reflexivity.
Qed.

Lemma sum_double:
forall n: nat,
n + n = 2 * n.
Proof.
induction n.
- simpl.
  reflexivity.
- rewrite plus_Sn_m.
  rewrite plus_comm. 
  rewrite plus_Sn_m.
  rewrite IHn.
  simpl.
  repeat rewrite plus_0_r.
  symmetry.
  rewrite plus_comm. 
  rewrite plus_Sn_m.
  reflexivity.
Qed.

Lemma add_exp:
forall n: nat,
n >= 1 -> 2 * 2 ^ (n - 1) = 2 ^ n.
Proof.
destruct n.
- intros H.
  omega.
- intros H.
  assert (H1: n = 0 \/ n >= 1) by omega.
  destruct H1 as [H1 | H1].
  + subst.
    simpl.
    reflexivity.
  + simpl.
    rewrite <- minus_n_O.
    rewrite <- plus_n_O.
    reflexivity.
Qed.

Lemma ge_exists:
forall x y: nat,
x >= y ->
exists z: nat,
x = z + y.
Proof.
induction y.
- intros H.
  exists x.
  rewrite plus_0_r.
  reflexivity.
- intros H.
  assert (H1: x >= y) by omega.
  specialize (IHy H1).
  destruct IHy as [z IHy].
  rewrite IHy.
  exists (z - 1).
  assert (H2: z >= 1) by omega.
  omega.
Qed.

Lemma pow_2_gt_0:
forall n: nat,
2 ^ n > 0.
Proof.
induction n.
- simpl.
  omega.
- simpl. 
  omega. 
Qed.
