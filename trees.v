(* ---------------------------------------------------------------------
   This file contains definitions and proof scripts related to 
   (i) closure operations for context-free grammars, 
   (ii) context-free grammars simplification 
   (iii) context-free grammar Chomsky normalization and 
   (iv) pumping lemma for context-free languages.
   
   More information can be found in the paper "Formalization of the
   pumping lemma for context-free languages", submitted to
   LATA 2016.
   
   Marcus Vinícius Midena Ramos
   mvmramos@gmail.com
   --------------------------------------------------------------------- *)
   
Require Import misc_arith.
Require Import misc_list.
Require Import misc_logic.
Require Import cfg.
Require Import chomsky.

Require Import List.
Require Import Omega.
Require Import Ring.
Require Import NPeano.
Require Import Even.
Require Import NZPow.


Import ListNotations.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* --------------------------------------------------------------------- *)
(* BINARY TREES                                                          *)
(* --------------------------------------------------------------------- *)

Section Binary_Trees.

Variable non_terminal: Type.
Variable terminal: Type.

Notation symbol:= (non_terminal + terminal)%type.
Notation sf:= (list symbol).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation sentence:= (list terminal).

Inductive btree: Type:=
| bnode_1: non_terminal -> terminal -> btree
| bnode_2: non_terminal -> btree -> btree -> btree.

Definition broot (t: btree): non_terminal:=
match t with
| bnode_1 n t => n
| bnode_2 n t1 t2 => n
end.

Inductive bpath (bt: btree): sf -> Prop:=
| bp_1: forall n: non_terminal,
        forall t: terminal,
        bt = (bnode_1 n t) -> bpath bt [inl n; inr t]
| bp_l: forall n: non_terminal,
        forall bt1 bt2: btree,
        forall p1: sf,
        bt = bnode_2 n bt1 bt2 -> bpath bt1 p1 -> bpath bt ((inl n) :: p1)
| bp_r: forall n: non_terminal,
        forall bt1 bt2: btree,
        forall p2: sf,
        bt = bnode_2 n bt1 bt2 -> bpath bt2 p2 -> bpath bt ((inl n) :: p2).

Inductive bnts (bt: btree) (ntl: list non_terminal): Prop:=
| bn_1: forall n: non_terminal,
        forall t: terminal,
        bt = (bnode_1 n t) -> In n ntl -> bnts bt ntl
| bn_2: forall n: non_terminal,
        forall bt1 bt2: btree,
        bt = bnode_2 n bt1 bt2 ->
        In n ntl -> 
        bnts bt1 ntl ->
        bnts bt2 ntl ->
        bnts bt ntl.

Inductive subtree (t: btree): btree -> Prop:=
| sub_br: forall tl tr: btree,
          forall n: non_terminal,
          t = bnode_2 n tl tr ->
          subtree t tr
| sub_bl: forall tl tr: btree,
          forall n: non_terminal,
          t = bnode_2 n tl tr ->
          subtree t tl
| sub_ir: forall tl tr t': btree,
          forall n: non_terminal,
          subtree tr t' ->
          t = bnode_2 n tl tr ->
          subtree t t'
| sub_il: forall tl tr t': btree,
          forall n: non_terminal,
          subtree tl t' ->
          t = bnode_2 n tl tr ->
          subtree t t'.

Inductive bcode (bt: btree): list bool -> Prop:=
| bcode_0: forall n: non_terminal,
           forall t: terminal,
           bt = (bnode_1 n t) -> bcode bt []
| bcode_1: forall n: non_terminal,
           forall bt1 bt2: btree,
           forall c1: list bool,
           bt = bnode_2 n bt1 bt2 -> bcode bt1 c1 -> bcode bt (false :: c1)
| bcode_2: forall n: non_terminal,
           forall bt1 bt2: btree,
           forall c2: list bool,
           bt = bnode_2 n bt1 bt2 -> bcode bt2 c2 -> bcode bt (true :: c2).

Inductive bpath_bcode (bt: btree): sf -> (list bool) -> Prop:=
| bb_0: forall n: non_terminal,
        forall t: terminal,
        bt = (bnode_1 n t) -> bpath_bcode bt [inl n; inr t] []
| bb_1: forall n: non_terminal,
        forall bt1 bt2: btree,
        forall c1: list bool,
        forall p1: sf,
        bt = (bnode_2 n bt1 bt2) -> 
        bpath bt1 p1 ->
        bpath_bcode bt1 p1 c1 ->
        bpath_bcode bt ((inl n) :: p1) (false :: c1)
| bb_2: forall n: non_terminal,
        forall bt1 bt2: btree,
        forall c2: list bool,
        forall p2: sf,
        bt = (bnode_2 n bt1 bt2) -> 
        bpath bt2 p2 ->
        bpath_bcode bt2 p2 c2 ->
        bpath_bcode bt ((inl n) :: p2) (true :: c2).

Inductive subtree_bcode (t1 t2: btree): list bool -> Prop:=
| sb_br: forall tl: btree,
         forall n: non_terminal,
         t1 = bnode_2 n tl t2 ->
         subtree_bcode t1 t2 [true]
| sb_bl: forall tr: btree,
         forall n: non_terminal,
         t1 = bnode_2 n t2 tr ->
         subtree_bcode t1 t2 [false]
| sb_ir: forall tl tr: btree,
         forall n: non_terminal,
         forall c: list bool,
         subtree_bcode tr t2 c ->
         t1 = bnode_2 n tl tr ->
         subtree_bcode t1 t2 (true :: c)
| sb_il: forall tl tr: btree,
         forall n: non_terminal,
         forall c: list bool,
         subtree_bcode tl t2 c ->
         t1 = bnode_2 n tl tr ->
         subtree_bcode t1 t2 (false :: c).

Lemma bnts_app_l:
forall t: btree,
forall l l': list non_terminal, 
bnts t l -> bnts t (l' ++ l).
Proof.
induction t.
- intros l l' H.
  inversion H.
  + inversion H0.
    subst.
    apply bn_1 with (n:= n0) (t:= t0).
    * reflexivity.
    * apply in_or_app.
      right.
      exact H1.
  + discriminate.
- intros l l' H.
  apply bn_2 with (n:= n) (bt1:= t1) (bt2:= t2).
  + reflexivity.
  + inversion H.
    * discriminate.
    * inversion H0.
      subst.
      apply in_or_app.
      right.
      exact H1.
  + inversion H.
    * discriminate.
    * inversion H0.
      subst.
      specialize (IHt1 l l' H2).
      exact IHt1.
  + inversion H.
    * discriminate.
    * inversion H0.
      subst.
      specialize (IHt2 l l' H3).
      exact IHt2.
Qed.

Lemma bnts_app_r:
forall t: btree,
forall l l': list non_terminal, 
bnts t l -> bnts t (l ++ l').
Proof.
induction t.
- intros l l' H.
  inversion H.
  + inversion H0.
    subst.
    apply bn_1 with (n:= n0) (t:= t0).
    * reflexivity.
    * apply in_or_app.
      left.
      exact H1.
  + discriminate.
- intros l l' H.
  apply bn_2 with (n:= n) (bt1:= t1) (bt2:= t2).
  + reflexivity.
  + inversion H.
    * discriminate.
    * inversion H0.
      subst.
      apply in_or_app.
      left.
      exact H1.
  + inversion H.
    * discriminate.
    * inversion H0.
      subst.
      specialize (IHt1 l l' H2).
      exact IHt1.
  + inversion H.
    * discriminate.
    * inversion H0.
      subst.
      specialize (IHt2 l l' H3).
      exact IHt2.
Qed.

Lemma bnts_app:
forall t: btree,
forall l l' l'': list non_terminal, 
bnts t l -> bnts t (l' ++ l ++ l'').
Proof.
intros t l l' l'' H.
apply bnts_app_l.
apply bnts_app_r.
exact H.
Qed.

Fixpoint bfrontier (t: btree): sentence:=
match t with
| bnode_1 n t => [t]
| bnode_2 n t1 t2 => bfrontier t1 ++ bfrontier t2
end.

Lemma bfrontier_ge_1:
forall t: btree,
length (bfrontier t) >= 1.
Proof.
induction t.
- simpl.
  omega.
- simpl.
  rewrite app_length.
  omega.
Qed.

Fixpoint bheight (t: btree): nat:=
match t with
| bnode_1 n t => 1
| bnode_2 n t1 t2 => S (max (bheight t1) (bheight t2))
end.

Lemma not_bheight_0:
forall t: btree,
~ bheight t = 0.
Proof.
intros t H.
destruct t.
- simpl in H.
  omega.
- simpl in H.
  inversion H.
Qed.  

Lemma bheight_ge_1:
forall t: btree,
bheight t >= 1.
Proof.
intros t.
destruct t.
- simpl.
  omega.
- simpl.
  omega.
Qed.  

Lemma bheight_ge_or:
forall n: non_terminal,
forall bt1 bt2: btree,
forall k: nat,
bheight (bnode_2 n bt1 bt2) >= k ->
(bheight bt1 >= bheight bt2 /\ bheight bt1 >= k - 1)
\/
(bheight bt2 >= bheight bt1 /\ bheight bt2 >= k - 1).
Proof.
intros n bt1 bt2 k H2.
simpl in H2.
assert (H3: (bheight bt1) >= (bheight bt2) \/ (bheight bt1) <= (bheight bt2)) by omega.
destruct H3 as [H3 | H3].
- apply max_l in H3.
  rewrite H3 in H2.
  left.
  split.
  + apply Nat.max_l_iff in H3.
    exact H3.
  + omega. 
- apply max_r in H3.
  rewrite H3 in H2.
  right.
  split.
  + apply Nat.max_r_iff in H3.
    exact H3.
  + omega.
Qed.

Lemma bheight_gt_or:
forall n: non_terminal,
forall bt1 bt2: btree,
forall k: nat,
bheight (bnode_2 n bt1 bt2) > k ->
(bheight bt1 >= bheight bt2 /\ bheight bt1 > k - 1)
\/
(bheight bt2 >= bheight bt1 /\ bheight bt2 > k - 1).
Proof.
intros n bt1 bt2 k H2.
simpl in H2.
assert (H3: (bheight bt1) >= (bheight bt2) \/ (bheight bt1) <= (bheight bt2)) by omega.
destruct H3 as [H3 | H3].
- apply max_l in H3.
  rewrite H3 in H2.
  left.
  split.
  + apply Nat.max_l_iff in H3.
    exact H3.
  + apply gt_S_n.
    destruct bt1.
    * simpl.
      simpl in H2.
      omega.
    * simpl.
      simpl in H2.
      omega.
- apply max_r in H3.
  rewrite H3 in H2.
  right.
  split.
  + apply Nat.max_r_iff in H3.
    exact H3.
  + apply gt_S_n.
    destruct bt2.
    * simpl.
      simpl in H2.
      omega.
    * simpl.
      simpl in H2.
      omega.
Qed.

Lemma bheight_left:
forall n: non_terminal,
forall bt1 bt2: btree,
forall i: nat,
bheight (bnode_2 n bt1 bt2) = S i ->
bheight bt1 >= bheight bt2 ->
bheight bt1 = i.
Proof.
intros n bt1 bt2 i H1 H2.
simpl in H1.
apply max_l in H2.
rewrite H2 in H1.
omega.
Qed.

Lemma bheight_right:
forall n: non_terminal,
forall bt1 bt2: btree,
forall i: nat,
bheight (bnode_2 n bt1 bt2) = S i ->
bheight bt1 <= bheight bt2 ->
bheight bt2 = i.
Proof.
intros n bt1 bt2 i H1 H2.
simpl in H1.
apply max_r in H2.
rewrite H2 in H1.
omega.
Qed.

Fixpoint bnodes (t: btree): nat:=
match t with
| bnode_1 n t => 2
| bnode_2 n t1 t2 => S ((bnodes t1) + (bnodes t2))
end.

Lemma bfrontier_max:
forall t: btree,
length (bfrontier t) <= 2 ^ ((bheight t) - 1).
Proof.
induction t.
- simpl.
  omega.
- simpl.
  rewrite app_length.
  rewrite <- minus_n_O.
  assert (H: (bheight t1) <= (bheight t2) \/
             (bheight t1) >= (bheight t2)) by omega.
  destruct H as [H | H].
  + assert (H':= H). 
    apply max_r in H. 
    rewrite H.
    assert (H1: 2 ^ (bheight t1 - 1) <= 2 ^ (bheight t2 - 1)).
      {
      apply pow_le.
      - omega. 
      - omega. 
      }
    assert (H2: length (bfrontier t1) <= 2 ^ (bheight t2 - 1)) by omega.
    assert (H3: length (bfrontier t1) + length (bfrontier t2) <= 2 ^ (bheight t2 - 1) + 2 ^ (bheight t2 - 1)) by omega.
    assert (H4: (2 ^ ((bheight t2) - 1)) + (2 ^ ((bheight t2) - 1)) = 2 * (2 ^ ((bheight t2) - 1))).
      {
      apply sum_double.
      }
    rewrite H4 in H3.
    assert (H5: 2 * (2 ^ (bheight t2 - 1)) = 2 ^ bheight t2).
      {
      apply add_exp.
      apply bheight_ge_1.
      }
    rewrite H5 in H3.
    exact H3.
  + assert (H':= H). 
    apply max_l in H. 
    rewrite H.
    assert (H1: 2 ^ (bheight t2 - 1) <= 2 ^ (bheight t1 - 1)).
      {
      apply pow_le.
      - omega. 
      - omega. 
      }
    assert (H2: length (bfrontier t2) <= 2 ^ (bheight t1 - 1)) by omega.
    assert (H3: length (bfrontier t1) + length (bfrontier t2) <= 2 ^ (bheight t1 - 1) + 2 ^ (bheight t1 - 1)) by omega.
    assert (H4: (2 ^ ((bheight t1) - 1)) + (2 ^ ((bheight t1) - 1)) = 2 * (2 ^ ((bheight t1) - 1))).
      {
      apply sum_double. 
      }
    rewrite H4 in H3.
    assert (H5: 2 * (2 ^ (bheight t1 - 1)) = 2 ^ bheight t1).
      {
      apply add_exp.
      apply bheight_ge_1.
      }
    rewrite H5 in H3.
    exact H3.
Qed.

Lemma bheight_eq:
forall t: btree,
forall i: nat,
bheight t = i -> length (bfrontier t) <= 2 ^ (i - 1).
Proof.
intros t i H.
rewrite <- H.
apply bfrontier_max.
Qed.

Lemma bheight_le:
forall t: btree,
forall i: nat,
bheight t <= i -> length (bfrontier t) <= 2 ^ (i - 1).
Proof.
intros t i H.
assert (H2: length (bfrontier t) <= 2 ^ ((bheight t) - 1)).
  {  
  apply bfrontier_max.
  }
assert (H3: exists x: nat, i = (bheight t) + x).
  {
  exists (i - bheight t).
  rewrite le_plus_minus_r.
  - reflexivity.
  - exact H.
  }
destruct H3 as [x H3].
rewrite H3.
assert (H4: 2 ^ (bheight t - 1) <= 2 ^ (bheight t + x - 1)).
  {
  induction x.
  - simpl. 
    rewrite <- plus_n_O.
    omega.
  - apply pow_le.
    + omega.
    + omega.
  }
omega.
Qed.

Lemma bheight_lt:
forall t: btree,
forall i: nat,
bheight t < i -> length (bfrontier t) < 2 ^ (i - 1).
Proof.
intros t i H.
assert (H2: length (bfrontier t) <= 2 ^ ((bheight t) - 1)).
  {  
  apply bfrontier_max.
  }
assert (H3: exists x: nat, i = (bheight t) + x).
  {
  exists (i - bheight t).
  rewrite le_plus_minus_r.
  - reflexivity.
  - omega.
  }
destruct H3 as [x H3].
rewrite H3.
assert (H4: 2 ^ (bheight t - 1) < 2 ^ (bheight t + x - 1)).
  {
  induction x.
  - simpl. 
    rewrite <- plus_n_O.
    omega.
  - apply pow_lt.
    + omega.
    + assert (H4: bheight t >= 1). 
        {
        apply bheight_ge_1.
        }
      omega. 
  }
omega.
Qed.

Lemma length_bfrontier_ge:
forall t: btree,
forall i: nat,
length (bfrontier t) >= 2 ^ (i - 1) -> 
bheight t >= i.
Proof.
intros t i H.
assert (H2: bheight t < i -> length (bfrontier t) < 2 ^ (i - 1)).
  {
  apply bheight_lt.
  }
apply contrap in H2.
- assert (H3: bheight t < i \/ bheight t > i \/ bheight t = i) by omega.
  destruct H3 as [H3 | [H3 | H3]].
  + omega. 
  + omega. 
  + omega. 
- intros H3.
  omega.
Qed. 

Lemma length_bfrontier_gt:
forall t: btree,
forall i: nat,
length (bfrontier t) > 2 ^ (i - 1) -> 
bheight t > i.
Proof.
intros t i H.
assert (H2: bheight t <= i -> length (bfrontier t) <= 2 ^ (i - 1)).
  {
  apply bheight_le.
  }
apply contrap in H2.
- assert (H3: bheight t < i \/ bheight t > i \/ bheight t = i) by omega.
  destruct H3 as [H3 | [H3 | H3]].
  + omega. 
  + exact H3.
  + omega. 
- intros H3.
  omega.
Qed. 

Lemma length_ge:
forall t: btree,
forall s: sentence,
forall i: nat,
bfrontier t = s ->
length s >= 2 ^ i -> 
bheight t >= (i + 1).
Proof.
intros t s i H1 H2.
rewrite <- H1 in H2.
apply length_bfrontier_ge.
replace (i + 1 - 1) with i.
- exact H2.
- omega. 
Qed.

Lemma length_gt:
forall t: btree,
forall s: sentence,
forall i: nat,
bfrontier t = s ->
length s > 2 ^ i -> 
bheight t > (i + 1).
Proof.
intros t s i H1 H2.
rewrite <- H1 in H2.
apply length_bfrontier_gt.
replace (i + 1 - 1) with i.
- exact H2.
- omega. 
Qed.

Lemma bpath_length_gt_0:
forall t: btree,
forall p: sf,
bpath t p -> length p > 0.
Proof.
intros t p H.
destruct t.
- inversion H.
  + simpl.   
    omega.
  + simpl.
    omega.
  + simpl.    
    omega.
- inversion H.
  + simpl.   
    omega.
  + simpl.
    omega.
  + simpl.    
    omega.
Qed.

Lemma bpath_bheight_exists:
forall t: btree,
exists p: sf,
bpath t p /\
length p = bheight t + 1.
Proof.
induction t.
- simpl.
  exists [inl n; inr t].
  split.
  + apply bp_1.
    reflexivity.
  + simpl.
    reflexivity.
- destruct IHt1 as [p1 [H1]].
  destruct IHt2 as [p2 [H2]].
  assert (H3: bheight t1 >= bheight t2 \/ bheight t1 <= bheight t2) by omega.
  destruct H3 as [H3 | H3].
  + exists ((inl n) :: p1).
    split.
    * {
      apply bp_l with (bt1:= t1) (bt2:= t2).
      - reflexivity.
      - exact H1.
      }
    * simpl.
      apply max_l in H3.
      rewrite H3.
      rewrite H.
      reflexivity.
  + exists ((inl n) :: p2).
    split.
    * {
      apply bp_r with (bt1:= t1) (bt2:= t2).
      - reflexivity.
      - exact H2.
      }
    * simpl.
      apply max_r in H3.
      rewrite H3.
      rewrite H0.
      reflexivity.
Qed.

Lemma bpath_last_terminal:
forall t: btree,
forall p: sf,
bpath t p ->
exists p': sf,
exists t: terminal,
p = p' ++ [inr t].
Proof.
induction t.
- intros p H.  
  inversion H.
  + subst.
    exists [inl n0].
    exists t0.
    reflexivity.
  + discriminate. 
  + discriminate.
- intros p H.
  inversion H.
  + discriminate.
  + inversion H0.
    subst.
    specialize (IHt1 p1 H1).
    destruct IHt1 as [p' [t IHt1]].
    rewrite IHt1.
    exists (inl n0 :: p').
    exists t.
    reflexivity.
  + inversion H0.
    subst.
    specialize (IHt2 p2 H1).
    destruct IHt2 as [p' [t IHt2]].
    rewrite IHt2.
    exists (inl n0 :: p').
    exists t.
    reflexivity.
Qed.

Lemma bpath_in_ntl:
forall bt: btree,
forall ntl: list non_terminal,
forall p: sf,
forall t: terminal,
bnts bt ntl ->
bpath bt (p ++ [inr t]) ->
(forall s: symbol, In s p -> In s (map inl ntl)).
Proof.
induction bt.
- intros ntl p t0 H1 H2 s H3. 
  apply in_split in H3.
  destruct H3 as [l1 [l2 H3]].
  rewrite H3 in H2.
  clear H3.
  inversion H2.
  + destruct l1. 
    * inversion H.
      {
      destruct s.
      - inversion H4.
        subst.
        inversion H0.
        subst.
        inversion H1.
        + inversion H3. 
          subst. 
          apply in_map.
          exact H6.
        + discriminate.
      - discriminate.
      }
    * inversion H.
      {
      destruct l1.
      - inversion H5.
        destruct l2.
        + inversion H7.
        + inversion H7.
      - inversion H5.
        destruct l1.
        + inversion H7.
        + inversion H7.
      }
  + discriminate.
  + discriminate.
- intros ntl p t H1 H2 s H3.
  apply in_split in H3.
  destruct H3 as [l1 [l2 H3]].
  rewrite H3 in H2.
  clear H3.
  inversion H2.
  + discriminate.
  + clear H2.
    inversion H0.
    subst.
    clear H0.
    destruct l1.
    * inversion H.
      {
      inversion H1.
      - discriminate.
      - inversion H0.
        subst.
        apply in_map.
        exact H5.
      }
    * inversion H.
      rewrite H4 in H3.
      {
      inversion H1.
      - discriminate.
      - inversion H0.
        subst.
        specialize (IHbt1 ntl (l1 ++ s :: l2) t H6 H3).
        apply IHbt1.
        apply in_or_app.
        right.
        simpl.
        left.
        reflexivity.
      }
  + clear H2.
    inversion H0.
    subst.
    clear H0.
    destruct l1.
    * inversion H.
      {
      inversion H1.
      - discriminate.
      - inversion H0.
        subst.
        apply in_map.
        exact H5.
      }
    * inversion H.
      rewrite H4 in H3.
      {
      inversion H1.
      - discriminate.
      - inversion H0.
        subst.
        specialize (IHbt2 ntl (l1 ++ s :: l2) t H7 H3).
        apply IHbt2.
        apply in_or_app.
        right.
        simpl.
        left.
        reflexivity.
      }
Qed.

Lemma btree_exists_bpath:
forall bt: btree,
forall ntl: list non_terminal,
bheight bt >= length ntl + 1 ->
bnts bt ntl ->
exists z: sf,
bpath bt z /\
length z = bheight bt + 1 /\
exists u r: sf,
exists t: terminal,
z = u ++ r ++ [inr t] /\
length u >= 0 /\
length r = length ntl + 1 /\
(forall s: symbol, In s (u ++ r) -> In s (map inl ntl)).
Proof.
intros bt ntl H1 H2.
assert (H3: exists p: sf, bpath bt p /\ length p = bheight bt + 1).
  {
  apply bpath_bheight_exists.
  }
destruct H3 as [p [H3 H4]].
exists p.
split.
- exact H3.
- split.
  + exact H4.
  + assert (H3':= H3).
    apply bpath_last_terminal in H3.
    destruct H3 as [p' [t H3]].
    apply ge_exists in H1. 
    destruct H1 as [z H1]. 
    rewrite H1 in H4.
    clear H1.
    replace (z + length ntl + 1 + 1) with (z + (length ntl + 1) + 1) in H4.
    * rewrite H3 in H4. 
      rewrite app_length in H4.
      simpl in H4.
      assert (H5: length p' = z + (length ntl + 1)) by omega.
      clear H4.
      apply list_split in H5. 
      destruct H5 as [l1 [l2 [H5 [H6 H7]]]].
      exists l1, l2, t.
      {
      split.
      - rewrite H5 in H3.
        rewrite <- app_assoc in H3.
        exact H3.
      - split.
        + apply length_ge_0.
        + split.
          * exact H7.
          * rewrite H5 in H3.
            rewrite H3 in H3'.
            clear H3 H5 H6 H7.
            {
            apply bpath_in_ntl with (bt:= bt) (t:= t).
            - exact H2.
            - exact H3'.
            }
      }
    * rewrite plus_assoc. 
      reflexivity.
Qed.

Lemma bpath_bheight_ge:
forall t: btree,
forall p: sf,
bpath t p ->
bheight t >= length p - 1.
Proof.
induction t.
- intros p H.
  inversion H.
  + simpl.
    omega.
  + discriminate. 
  + discriminate.
- intros p H.
  inversion H.
  + discriminate.
  + inversion H0.
    subst.
    simpl.
    specialize (IHt1 p1 H1).
    assert (H2: bheight bt1 >= bheight bt2 \/ bheight bt1 <= bheight bt2) by omega.
    destruct H2 as [H2 | H2].
    * apply max_l in H2.
      rewrite H2.
      omega.
    * apply max_r in H2.
      rewrite H2.
      apply Nat.max_r_iff in H2.
      omega.
  + inversion H0.
    subst.
    simpl.
    specialize (IHt2 p2 H1).
    assert (H2: bheight bt1 >= bheight bt2 \/ bheight bt1 <= bheight bt2) by omega.
    destruct H2 as [H2 | H2].
    * apply max_l in H2.
      rewrite H2.
      apply Nat.max_l_iff in H2.
      omega.
    * apply max_r in H2.
      rewrite H2.
      omega.
Qed.

Lemma bpath_bheight_max:
forall t1 t2: btree,
forall p1: sf,
bpath t1 p1 ->
length p1 = max (bheight t1) (bheight t2) + 1 ->
max (bheight t1) (bheight t2) = bheight t1.
Proof.
intros t1 t2 p1 H1 H2.
assert (H3: (bheight t1) >= (bheight t2) \/ (bheight t1) <= (bheight t2)) by omega.
destruct H3 as [H3 | H3].
- apply max_l in H3.
  rewrite H3.
  reflexivity.
- apply max_r in H3.
  rewrite H3 in H2.
  rewrite H3.
  apply bpath_bheight_ge in H1.
  rewrite H2 in H1.
  replace (bheight t2 + 1 - 1) with (bheight t2) in H1.
  + apply Nat.max_r_iff in H3.
    omega.
  + omega.
Qed.

Lemma bpath_exists_btree:
forall bt: btree,
forall z1 z2: sf,
forall n: non_terminal,
bpath bt (z1 ++ [inl n] ++ z2) ->
length (z1 ++ [inl n] ++ z2) = bheight bt + 1 ->
exists bt': btree,
broot bt' = n /\
bheight bt' = length z2.
Proof.
induction bt.
- intros z1 z2 n0 H H'.
  inversion H.
  + inversion H1. 
    subst. 
    destruct z1.
    * inversion H0.
      subst.
      exists (bnode_1 n0 t0).
      simpl.
      auto.
    * inversion H0.
      {
      destruct z1.
      - inversion H4.
      - inversion H4.
        destruct z1.
        + inversion H6.
        + inversion H6.
      }
  + discriminate.
  + discriminate.
- intros z1 z2 n0 H H'.
  inversion H.
  + discriminate.
  + clear H IHbt2.
    inversion H1.
    clear H1.
    subst.
    destruct z1.
    * inversion H0.
      clear H0.
      subst.
      exists (bnode_2 n0 bt0 bt3).
      {
      split.
      - simpl. 
        reflexivity.
      - simpl.
        assert (H4: bheight bt0 >= bheight bt3 \/ bheight bt0 <= bheight bt3) by omega.
        destruct H4 as [H4 | H4].
        + apply max_l in H4.
          rewrite H4.
          simpl in H'.
          rewrite H4 in H'.
          omega.
        + apply max_r in H4.
          rewrite H4.
          simpl in H'.
          rewrite H4 in H'.
          omega.
      }
    * inversion H0.
      clear H0.
      subst.
      specialize (IHbt1 z1 z2 n0 H2).
      simpl in H'.
      apply eq_add_S in H'.
      assert (H3: max (bheight bt0) (bheight bt3) = bheight bt0).
        {
        apply bpath_bheight_max with (t2:= bt3) in H2.
        - exact H2.
        - exact H'.
        }
      rewrite H3 in H'.
      specialize (IHbt1 H').
      destruct IHbt1 as [bt' [H4 H5]].
      exists bt'.
      {
      split.
      - exact H4.
      - exact H5.
      }
  + clear H IHbt1.
    inversion H1.
    clear H1.
    subst.
    destruct z1.
    * inversion H0.
      clear H0.
      subst.
      exists (bnode_2 n0 bt0 bt3).
      {
      split.
      - simpl. 
        reflexivity.
      - simpl.
        assert (H4: bheight bt0 >= bheight bt3 \/ bheight bt0 <= bheight bt3) by omega.
        destruct H4 as [H4 | H4].
        + apply max_l in H4.
          rewrite H4.
          simpl in H'.
          rewrite H4 in H'.
          omega.
        + apply max_r in H4.
          rewrite H4.
          simpl in H'.
          rewrite H4 in H'.
          omega.
      }
    * inversion H0.
      clear H0.
      subst.
      specialize (IHbt2 z1 z2 n0 H2).
      simpl in H'.
      apply eq_add_S in H'.
      assert (H3: max (bheight bt0) (bheight bt3) = bheight bt3).
        {
        apply bpath_bheight_max with (t2:= bt0) in H2.
        - replace (max (bheight bt3) (bheight bt0)) with (max (bheight bt0) (bheight bt3)) in H2.
          + exact H2.
          + rewrite Nat.max_comm.
            reflexivity.
        - replace (max (bheight bt3) (bheight bt0)) with (max (bheight bt0) (bheight bt3)).
          + exact H'.
          + rewrite Nat.max_comm.
            reflexivity.
        }
      rewrite H3 in H'.
      specialize (IHbt2 H').
      destruct IHbt2 as [bt' [H4 H5]].
      exists bt'.
      {
      split.
      - exact H4.
      - exact H5.
      }
Qed. 

Lemma bpath_exists_root:
forall t: btree,
forall p: sf,
forall d: symbol,
bpath t p ->
hd d p = inl (broot t).
Proof.
intros t p d H.
inversion H.
- rewrite H0.
  simpl.
  reflexivity.
- rewrite H0.
  simpl.
  reflexivity.
- rewrite H0.
  simpl.
  reflexivity.
Qed.

Lemma bpath_insert_head:
forall bt: btree,
forall n: non_terminal,
forall t: terminal,
forall p1 p2 p3 p4: sf,
bpath bt (p1 ++ p2 ++ [inl n] ++ p3 ++ [inl n] ++ p4 ++ [inr t]) ->
broot bt <> n ->
exists p12': sf,
[inl (broot bt)] ++ p12' = p1 ++ p2.
Proof.
intros bt n t p1 p2 p3 p4 H1 H2.
inversion H1.
- destruct p1.
  + destruct p2.
    * {
      inversion H.
      destruct p3.
      - inversion H5.
      - inversion H5.
        destruct p3.
        + inversion H7.
        + inversion H7.
      }
    * {
      inversion H.
      destruct p2.
      - inversion H5.
      - inversion H5.
        destruct p2.
        + inversion H7.
        + inversion H7.
      }
  + inversion H.
    destruct p1.
    * {
      destruct p2.
      - inversion H5.
      - inversion H5.
        destruct p2.
        + inversion H7.
        + inversion H7.
      }
    * inversion H5.
      {
      destruct p1.
      - destruct p2.
        + inversion H7.
        + inversion H7.
      - inversion H7.
      }
- rewrite H0.
  simpl.
  destruct p1.  
  + destruct p2.
    * simpl in H. 
      apply bpath_exists_root with (d:= inl n) in H1.
      simpl in H1.
      inversion H1.
      symmetry in H5.
      contradiction.  
    * inversion H.
      exists p2. 
      reflexivity.
  + inversion H.
    exists (p1 ++ p2).
    reflexivity.
- rewrite H0.
  simpl.
  destruct p1.
  + destruct p2.
    * simpl in H.
      apply bpath_exists_root with (d:= inl n) in H1.
      simpl in H1.
      inversion H1.
      symmetry in H5.
      contradiction.  
    * inversion H.
      exists p2. 
      reflexivity.
  + inversion H.
    exists (p1 ++ p2).
    reflexivity.  
Qed.

Lemma bpath_broot:
forall bt: btree,
forall d: symbol,
forall p: _,
bpath bt p ->
inl (broot bt) = hd d p.
Proof.
intros bt d p H.
inversion H.
- rewrite H0. 
  simpl. 
  reflexivity. 
- rewrite H0.
  simpl. 
  reflexivity. 
- rewrite H0.
  simpl. 
  reflexivity. 
Qed.  

Lemma bfrontier_not_nil:
forall bt: btree,
~ bfrontier bt = [].
Proof.
induction bt.
- simpl.
  intros H.
  inversion H.
- simpl.
  apply not_nil_app.
  exact IHbt1.
Qed.

Lemma subtree_trans:
forall t1 t2 t3: btree,
subtree t1 t2 ->
subtree t2 t3 ->
subtree t1 t3.
Proof.
intros t1 t2 t3 H1.
induction H1.
- intros H2.
  rewrite H.
  apply sub_ir with (tl:= tl) (tr:= tr) (n:= n).
  + exact H2.
  + reflexivity.
- intros H2.
  rewrite H.
  apply sub_il with (tl:= tl) (tr:= tr) (n:= n).
  + exact H2.
  + reflexivity.
- intros H2.
  specialize (IHsubtree H2).
  rewrite H.
  apply sub_ir with (tl:= tl) (tr:= tr) (n:= n).
  + exact IHsubtree.
  + reflexivity.
- intros H2.
  specialize (IHsubtree H2).
  rewrite H.
  apply sub_il with (tl:= tl) (tr:= tr) (n:= n).
  + exact IHsubtree.
  + reflexivity.
Qed.

Lemma subtree_includes:
forall t1 t2: btree,
subtree t1 t2 ->
exists l r : sentence,
bfrontier t1 = l ++ bfrontier t2 ++ r /\ (l <> [] \/ r <> []).
Proof.
intros t1 t2 H.
induction H.
- exists (bfrontier tl), [].
  split.
  + rewrite H.
    simpl.   
    rewrite app_nil_r.   
    reflexivity.
  + left. 
    apply bfrontier_not_nil.
- exists [], (bfrontier tr).
  split.
  + rewrite H.
    simpl.
    reflexivity.
  + right.
    apply bfrontier_not_nil.
- destruct IHsubtree as [l [r [H1 H2]]].
  rewrite H0.
  simpl.
  rewrite H1.
  exists (bfrontier tl ++ l), r.
  split.
  + repeat rewrite <- app_assoc.
    reflexivity.
  + left.
    apply app_not_nil_inv.
    left.
    apply bfrontier_not_nil.
- destruct IHsubtree as [l [r [H1 H2]]].
  rewrite H0.
  simpl.
  rewrite H1.
  exists l, (r ++ bfrontier tr).
  split.
  + repeat rewrite <- app_assoc.
    reflexivity.
  + right.
    apply app_not_nil_inv.
    right.
    apply bfrontier_not_nil. 
Qed.

Lemma bpath_bpath:
forall t1: btree,
forall n: non_terminal,
forall p1 p2: sf,
bpath t1 (p1 ++ [inl n] ++ p2) ->
exists t2: btree,
bpath t2 ([inl n] ++ p2).
Proof.
intros t1 n p1. 
revert t1 n.
induction p1.
- intros t1 n p2 H.
  exists t1.
  exact H.
- intros t1 n p2 H.
  destruct a.
  + change (inl n0 :: p1) with ([inl n0] ++ p1) in H.
    rewrite <- app_assoc in H.
    inversion H.
    * {
      destruct p1.
      - inversion H2.
      - inversion H2.
        destruct p1.
        + inversion H5.
        + inversion H5.
      }
    * specialize (IHp1 bt1 n p2 H3).
      exact IHp1.
    * specialize (IHp1 bt2 n p2 H3).
      exact IHp1.
  + apply bpath_broot with (d:= inl (broot t1)) in H. 
    simpl in H. 
    inversion H. 
Qed.

Lemma bpath_exists_bcode:
forall t: btree,
forall p: sf,
bpath t p -> 
exists c: list bool,
bcode t c /\
bpath_bcode t p c.
Proof.
induction t.
- intros p H.
  exists [].
  split.
  + apply bcode_0 with (n:= n) (t:= t).
    reflexivity.
  + inversion H. 
    * inversion H0. 
      subst. 
      apply bb_0. 
      reflexivity.
    * discriminate.
    * discriminate.
- intros p H.
  inversion H.
  + discriminate.
  + inversion H0. 
    subst. 
    clear H0.
    specialize (IHt1 p1 H1).
    destruct IHt1 as [c1 IHt1].  
    exists (false :: c1).
    split.
    * {
      apply bcode_1 with (n:= n0) (bt1:= bt1) (bt2:= bt2).
      - reflexivity.
      - apply IHt1.
      }
    * {
      apply bb_1 with (bt1:= bt1) (bt2:= bt2).
      - reflexivity.
      - exact H1.
      - apply IHt1.
      }
  + inversion H0. 
    subst. 
    clear H0.
    specialize (IHt2 p2 H1).
    destruct IHt2 as [c2 IHt2].  
    exists (true :: c2).
    split.
    * {
      apply bcode_2 with (n:= n0) (bt1:= bt1) (bt2:= bt2).
      - reflexivity.
      - apply IHt2.
      }
    * {
      apply bb_2 with (n:= n0) (bt1:= bt1) (bt2:= bt2).
      - reflexivity.
      - apply H1.
      - apply IHt2.
      }
Qed.

Lemma bcode_exists_bpath:
forall t: btree,
forall c: list bool,
bcode t c -> 
exists p: sf,
bpath t p /\
bpath_bcode t p c.
Proof.
induction t.
- intros c H.
  exists [inl n; inr t].
  split.
  + apply bp_1 with (n:= n) (t:= t).
    reflexivity.
  + inversion H. 
    * inversion H0. 
      subst. 
      apply bb_0. 
      reflexivity.
    * discriminate.
    * discriminate.
- intros c H.
  inversion H.
  + discriminate.
  + inversion H0. 
    subst. 
    clear H0.
    specialize (IHt1 c1 H1).
    destruct IHt1 as [p1 IHt1].  
    exists ((inl n0) :: p1).
    split.
    * {
      apply bp_l with (n:= n0) (bt1:= bt1) (bt2:= bt2).
      - reflexivity.
      - apply IHt1.
      }
    * {
      apply bb_1 with (bt1:= bt1) (bt2:= bt2).
      - reflexivity.
      - apply IHt1.
      - apply IHt1.
      }
  + inversion H0. 
    subst. 
    clear H0.
    specialize (IHt2 c2 H1).
    destruct IHt2 as [p2 IHt2].  
    exists ((inl n0) :: p2).
    split.
    * {
      apply bp_r with (n:= n0) (bt1:= bt1) (bt2:= bt2).
      - reflexivity.
      - apply IHt2.
      }
    * {
      apply bb_2 with (n:= n0) (bt1:= bt1) (bt2:= bt2).
      - reflexivity.
      - apply IHt2.
      - apply IHt2.
      }
Qed.

Lemma bpath_bcode_split:
forall t: btree,
forall p: sf,
forall c: list bool,
bpath_bcode t p c ->
bpath t p /\
bcode t c.
Proof.
intros t p c H.
induction H.
- rewrite H.
  split.
  + apply bp_1.
    reflexivity.
  + apply bcode_0 with (n:= n) (t:= t).
    reflexivity.
- rewrite H.
  split.
  + apply bp_l with (bt1:= bt1) (bt2:= bt2).
    * reflexivity.
    * exact H0.
  + apply bcode_1 with (n:= n) (bt1:= bt1) (bt2:= bt2).
    * reflexivity.
    * apply IHbpath_bcode.
- rewrite H.
  split.
  + apply bp_r with (bt1:= bt1) (bt2:= bt2).
    * reflexivity.
    * exact H0.
  + apply bcode_2 with (n:= n) (bt1:= bt1) (bt2:= bt2).
    * reflexivity.
    * apply IHbpath_bcode.
Qed.

(*
Lemma bcode_gt_0:
forall t: btree,
forall c: list nat,
bcode t c ->
length c > 0.
Proof.
intros t c H.
inversion H.
- simpl.
  omega.
- simpl.
  omega.
- simpl.
  omega.
Qed.
*)

Lemma bheight_child:
forall t t1 t2: btree,
forall n: non_terminal,
forall p1 p2: sf,
forall h: nat,
bheight t = h ->
t = bnode_2 n t1 t2 ->
bpath t1 p1 -> 
bpath t2 p2 -> 
(length p1 = h -> bheight t1 = length p1 - 1) \/
(length p2 = h -> bheight t2 = length p2 - 1).
Proof.
intros t t1 t2 n p1 p2 h H1 H2 H3 H4.
assert (H5: bheight t1 >= bheight t2 \/ bheight t1 <= bheight t2) by omega.
destruct H5 as [H5 | H5].
- rewrite H2 in H1.
  destruct h.
  + simpl in H1.
    omega.
  + left.
    intros H6.
    apply bheight_left in H1.
    * rewrite H1, H6.
      omega.
    * exact H5.
- right.
  intros H6.
  rewrite H2 in H1.
  destruct h.
  + simpl in H1.
    omega.
  + apply bheight_right in H1.
    * rewrite H1, H6.
      omega.
    * exact H5.
Qed.

Lemma bpath_bheight:
forall t: btree,
forall p: sf,
bpath t p ->
bheight t >= length p - 1.
Proof.
induction t.
- intros p H.
  inversion H.
  + inversion H0.
    subst.
    simpl.
    omega.
  + discriminate.
  + discriminate.
- intros p H.
  inversion H.
  + discriminate.
  + inversion H0.
    clear H0 IHt2.
    subst.
    specialize (IHt1 p1 H1).
    simpl.
    assert (H2: bheight bt1 >= bheight bt2 \/ bheight bt1 <= bheight bt2) by omega.
    destruct H2 as [H2 | H2].
    * apply Nat.max_l_iff in H2.
      rewrite H2.
      omega.
    * assert (H2':= H2).
      apply Nat.max_r_iff in H2.
      rewrite H2.
      omega.
  + inversion H0.
    clear H0 IHt1.
    subst.
    specialize (IHt2 p2 H1).
    simpl.
    assert (H2: bheight bt1 >= bheight bt2 \/ bheight bt1 <= bheight bt2) by omega.
    destruct H2 as [H2 | H2].
    * assert (H2':= H2).
      apply Nat.max_l_iff in H2.
      rewrite H2.
      omega.
    * apply Nat.max_r_iff in H2.
      rewrite H2.
      omega.
Qed.

Lemma bheight_child_left:
forall t t1 t2: btree,
forall n: non_terminal,
forall p1: sf,
forall h: nat,
bheight t = h ->
t = bnode_2 n t1 t2 ->
bpath t1 p1 -> 
length p1 = h -> 
bheight t1 = length p1 - 1.
Proof.
intros t t1 t2 n p1 h H1 H2 H3 H4.
assert (H5: bheight t1 >= bheight t2 \/ bheight t1 <= bheight t2) by omega.
destruct H5 as [H5 | H5].
- rewrite H2 in H1.
  destruct h.
  + simpl in H1.
    omega.
  + apply bheight_left in H1.
    * rewrite H1, H4.
      omega.
    * exact H5.
- assert (H6: bheight t1 < bheight t2 \/ bheight t1 = bheight t2) by omega.
  destruct H6 as [H6 | H6].
  + clear H5.
    rewrite H2 in H1.
    simpl in H1.
    assert (H7: (max (bheight t1) (bheight t2) = bheight t2)).
      {
      assert (H7: bheight t1 <= bheight t2) by omega.
      apply Nat.max_r_iff in H7.
      exact H7.     
      }
    rewrite H7 in H1.
    assert (H8: bheight t1 >= length p1 - 1).
      {
      apply bpath_bheight.
      exact H3.
      }
    omega.
  + clear H5.
    rewrite H2 in H1. 
    destruct h.
    * simpl in H1.
      omega.
    * {
      apply bheight_left in H1.
      - rewrite H1, H4.
        omega.
      - omega.
      }
Qed.

Lemma bheight_child_right:
forall t t1 t2: btree,
forall n: non_terminal,
forall p2: sf,
forall h: nat,
bheight t = h ->
t = bnode_2 n t1 t2 ->
bpath t2 p2 -> 
length p2 = h -> 
bheight t2 = length p2 - 1.
Proof.
intros t t1 t2 n p2 h H1 H2 H3 H4.
assert (H5: bheight t1 >= bheight t2 \/ bheight t1 <= bheight t2) by omega.
destruct H5 as [H5 | H5].
- assert (H6: bheight t2 < bheight t1 \/ bheight t2 = bheight t1) by omega.
  destruct H6 as [H6 | H6].
  + clear H5.
    rewrite H2 in H1.
    simpl in H1.
    assert (H7: (max (bheight t1) (bheight t2) = bheight t1)).
      {
      assert (H7: bheight t1 >= bheight t2) by omega.
      apply Nat.max_l_iff in H7.
      exact H7.     
      }
    rewrite H7 in H1.
    assert (H8: bheight t2 >= length p2 - 1).
      {
      apply bpath_bheight.
      exact H3.
      }
    omega.
  + clear H5.
    rewrite H2 in H1. 
    destruct h.
    * simpl in H1.
      omega.
    * {
      apply bheight_right in H1.
      - rewrite H1, H4.
        omega.
      - omega.
      }
- rewrite H2 in H1.
  destruct h.
  + simpl in H1.
    omega.
  + apply bheight_right in H1.
    * rewrite H1, H4.
      omega.
    * exact H5.
Qed.

Lemma bcode_subtree:
forall t1: btree,
forall c1 c2: list bool,
bcode t1 (c1 ++ c2) ->
c1 <> [] ->
exists t2: btree,
bcode t2 c2 /\
subtree t1 t2.
Proof.
induction t1.
- intros c1 c2 H1 H2.
  inversion H1.
  + inversion H0.
    clear H0.
    subst.
    assert (H4: c1 = [] \/ c2 = []).
      {
      destruct c1.
      - left.
        reflexivity.
      - right.
        inversion H.
      }
    destruct H4 as [H4 | H4].
    * contradiction. 
    * symmetry in H. 
      apply app_eq_nil in H.
      destruct H as [H _].
      contradiction. 
  + discriminate.
  + discriminate.
- intros c1 c2 H1 H2.
  destruct c1.
  + destruct H2.
    reflexivity.
  + inversion H1.
    * clear H1.
      inversion H3.
      clear H3.
      subst.
      clear H2.
      {
      destruct c1.   
      - exists bt1. 
        split. 
        + exact H4.
        + apply sub_bl with (n:= n0) (tr:= bt2).
          reflexivity.
      - specialize (IHt1_1 (b :: c1) c2 H4).
        assert (H6: b :: c1 <> []).
          {
          apply not_eq_sym.
          apply nil_cons.
          }
        specialize (IHt1_1 H6).
        destruct IHt1_1 as [t2 [H7 H8]].
        exists t2.
        split.
        + exact H7.
        + apply subtree_trans with (t2:= bt1).
          * apply sub_bl with (tr:= bt2) (n:= n0).
            reflexivity.
          * exact H8.
      }
    * clear H1.
      inversion H3.
      clear H3.
      subst.
      clear H2.
      {
      destruct c1.   
      - exists bt2. 
        split. 
        + exact H4.
        + apply sub_br with (n:= n0) (tl:= bt1).
          reflexivity.
      - specialize (IHt1_2 (b :: c1) c2 H4).
        assert (H6: b :: c1 <> []).
          {
          apply not_eq_sym.
          apply nil_cons.
          }
        specialize (IHt1_2 H6).
        destruct IHt1_2 as [t2 [H7 H8]].
        exists t2.
        split.
        + exact H7.
        + apply subtree_trans with (t2:= bt2).
          * apply sub_br with (tl:= bt1) (n:= n0).
            reflexivity.
          * exact H8.
      }
Qed.

Fixpoint get_nt_btree (c: list bool) (bt: btree): option non_terminal:=
match c, bt with
| [], bnode_1 n t => Some n
| _,  bnode_1 n t => None
| [], bnode_2 n bt1 bt2 => Some n
| false :: y, bnode_2 n bt1 bt2 => get_nt_btree y bt1
| true :: y, bnode_2 n bt1 bt2 =>  get_nt_btree y bt2
end. 
 
Lemma get_nt_btree_empty:
forall t: btree,
get_nt_btree [] t = Some (broot t).
Proof.
intros t.
destruct t.
- simpl. 
  reflexivity.
- simpl. 
  reflexivity.
Qed.

Lemma get_nt_btree_single:
forall b: bool,
forall t1 t2: btree,
forall n: non_terminal,
get_nt_btree [b] (bnode_2 n t1 t2) = Some n ->
n = broot t1 \/ n = broot t2.
Proof.
intros b.
destruct b.
- intros t1 t2 n H.
  simpl in H.
  destruct t2.
  + inversion H.
    subst.
    right.
    simpl.
    reflexivity.
  + inversion H.
    subst.
    right.
    simpl.
    reflexivity.
- intros t1 t2 n H.
  simpl in H.
  destruct t1.
  + inversion H.
    subst.
    left.
    simpl.
    reflexivity.
  + inversion H.
    subst.
    left.
    simpl.
    reflexivity.
Qed.

Lemma bcode_get_nt_btree:
forall t: btree,
forall c1 c2: list bool,
bcode t (c1 ++ c2) ->
exists n: non_terminal,
get_nt_btree c1 t = Some n.
Proof.
induction t.
- intros c1 c2 H.
  inversion H.
  + clear H.
    inversion H1.
    clear H1.
    symmetry in H0.
    apply app_eq_nil in H0.
    destruct H0 as [H0 _].
    subst.
    simpl.
    exists n0.
    reflexivity.
  + discriminate.
  + discriminate.
- intros c1 c2 H.
  inversion H.
  + discriminate.
  + clear H.
    inversion H1.
    clear H1.
    subst.
    destruct c1.
    * simpl.
      exists n0.
      reflexivity.
    * {
      destruct b.
      - inversion H0.
      - simpl.
        inversion H0.
        rewrite H1 in H2.
        specialize (IHt1 c1 c2 H2).
        destruct IHt1 as [n IHt1].
        rewrite IHt1.
        exists n.
        reflexivity.
      }
  + clear H.
    inversion H1.
    clear H1.
    subst.
    destruct c1.
    * simpl.
      exists n0.
      reflexivity.
    * {
      destruct b.
      - simpl.
        inversion H0.
        rewrite H1 in H2.
        specialize (IHt2 c1 c2 H2).
        destruct IHt2 as [n IHt2].
        rewrite IHt2.
        exists n.
        reflexivity.
      - inversion H0.
      }
Qed.

Fixpoint btree_subst (t1 t2: btree) (c: list bool): option btree:=
match t1, c with
| bnode_1 n t, [] => Some t2
| bnode_1 n t, _ => None
| bnode_2 n1 bt1 bt2, [] => Some t2
| bnode_2 n1 bt1 bt2, false :: y => 
                                 match (btree_subst bt1 t2 y) with
                                 | None => None
                                 | Some bt1 => Some (bnode_2 n1 bt1 bt2)
                                 end
| bnode_2 n1 bt1 bt2, true :: y => 
                                 match (btree_subst bt2 t2 y) with 
                                 | None => None
                                 | Some bt2 => Some (bnode_2 n1 bt1 bt2)
                                 end
end.

Lemma btree_subst_empty:
forall t1 t2: btree,
btree_subst t1 t2 [] = Some t2.
Proof.
intros t1 t2.
destruct t1.
- simpl.
  reflexivity.
- simpl.
  reflexivity.
Qed.

Lemma btree_subst_single:
forall n: non_terminal,
forall t1 t2 t3 t': btree,
forall b: bool,
btree_subst (bnode_2 n t1 t2) t3 [b] = Some t' ->
(t' = (bnode_2 n t1 t3) \/ t' = (bnode_2 n t3 t2)).
Proof.
intros n t1 t2 t3 t' b H.
destruct b.
- simpl in H.
  rewrite btree_subst_empty in H.
  inversion H.
  left.
  reflexivity.
- simpl in H.
  rewrite btree_subst_empty in H.
  inversion H.
  right.
  reflexivity.
Qed.

Lemma bcode_btree_subst:
forall t1 t2: btree,
forall c1 c2: list bool,
bcode t1 (c1 ++ c2) ->
exists t: btree,
btree_subst t1 t2 c1 = Some t.
Proof.
induction t1.
- intros t2 c1 c2 H.
  inversion H.
  + clear H.
    inversion H1.
    clear H1.
    symmetry in H0. 
    apply app_eq_nil in H0.
    destruct H0 as [H0 H4].
    subst.
    exists t2.
    rewrite btree_subst_empty.
    reflexivity.
  + discriminate.
  + discriminate.
- intros t2 c1 c2 H.
  inversion H.
  + discriminate. 
  + clear H.
    inversion H1.
    clear H1.
    subst.
    destruct c1.
    * exists t2.
      simpl.
      reflexivity.
    * {
      destruct b.
      - inversion H0.
      - simpl.
        inversion H0.
        rewrite H1 in H2.
        specialize (IHt1_1 t2 c1 c2 H2).
        destruct IHt1_1 as [t IHt1_1].
        rewrite IHt1_1.
        exists (bnode_2 n0 t bt2).
        reflexivity.
      }
  + clear H.
    inversion H1.
    clear H1.
    subst.
    destruct c1.
    * exists t2.
      simpl.
      reflexivity.
    * {
      destruct b.
      - simpl.
        inversion H0.
        rewrite H1 in H2.
        specialize (IHt1_2 t2 c1 c2 H2).
        destruct IHt1_2 as [t IHt1_2].
        rewrite IHt1_2.
        exists (bnode_2 n0 bt1 t).
        reflexivity.
      - inversion H0.
      }
Qed.

Lemma btree_subst_preserves_broot_v1:
forall t1 t2 t3: btree,
forall c: list bool,
broot t1 = broot t2 ->
btree_subst t1 t2 c = Some t3 ->
broot t3 = broot t1.
Proof.
intros t1 t2 t3 c H1 H2.
destruct t1, c.
- simpl in H1, H2. 
  inversion H2. 
  subst. 
  simpl.
  reflexivity.
- simpl in H1, H2. 
  inversion H2.
- simpl in H1, H2. 
  inversion H2. 
  subst. 
  simpl.
  reflexivity.
- destruct b. 
  + simpl in H1, H2.
    destruct (btree_subst t1_2 t2 c). 
    * inversion H2.
      subst.
      simpl.
      reflexivity.
    * inversion H2.
  + simpl in H1, H2.
    destruct (btree_subst t1_1 t2 c). 
    * inversion H2.
      subst.
      simpl.
      reflexivity.
    * inversion H2.
Qed.

Lemma btree_subst_preserves_broot_v2:
forall t1 t2 t3: btree,
forall c: list bool,
c <> [] ->
btree_subst t1 t2 c = Some t3 ->
broot t3 = broot t1.
Proof.
intros t1 t2 t3 c H1 H2.
destruct t1, c.
- destruct H1. 
  reflexivity.
- destruct b. 
  + simpl in H2.
    discriminate.
  + simpl in H2.
    discriminate.
- destruct H1. 
  reflexivity. 
- destruct b.
  + simpl.
    simpl in H2.
    destruct (btree_subst t1_2 t2 c).
    * inversion H2.
      simpl.
      reflexivity. 
    * discriminate. 
  + simpl.
    simpl in H2.
    destruct (btree_subst t1_1 t2 c).
    * inversion H2.
      simpl.
      reflexivity.
    * discriminate. 
Qed.

Lemma not_subtree_v1:
forall n: non_terminal,
forall t: terminal,
forall bt: btree,
~ subtree (bnode_1 n t) bt.
Proof. 
intros n t bt H.
inversion H.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
Qed.

Lemma not_subtree_single:
forall n: non_terminal,
forall t: terminal,
forall bt: btree,
~ subtree (bnode_1 n t) bt.
Proof. 
intros n t bt H.
inversion H.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
Qed.

Lemma not_bnode_2_l_same:
forall t1 t2: btree,
forall n: non_terminal,
~ t1 = bnode_2 n t1 t2.
Proof.
induction t1.
- intros t2 n0 H.
  discriminate.
- intros t2 n0 H.
  inversion H.
  specialize (IHt1_1 t1_2 n0).
  contradiction.
Qed.

Lemma not_bnode_2_r_same:
forall t1 t2: btree,
forall n: non_terminal,
~ t2 = bnode_2 n t1 t2.
Proof.
induction t2.
- intros n0 H.
  discriminate.
- intros n0 H.
  inversion H.
  specialize (IHt2_2 n0).
  contradiction.
Qed.

Lemma not_subtree_same:
forall bt: btree,
~ subtree bt bt.
Proof.
induction bt.
- intros H.
  inversion H.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
- intros H. 
  inversion H.  
  + inversion H0.
    apply not_bnode_2_r_same in H5. 
    contradiction. 
  + inversion H0.
    apply not_bnode_2_l_same in H4. 
    contradiction. 
  + clear H.
    inversion H1.
    clear H1. 
    subst.
    remember (bnode_2 n0 tl tr) as t.
    assert (H1: subtree tr tr).
      {
      apply subtree_trans with (t2:= t).
      - exact H0.
      - apply sub_br with (tl:= tl) (n:= n0).
        exact Heqt.
      }
    contradiction.
  + clear H.
    inversion H1.
    clear H1. 
    subst.
    remember (bnode_2 n0 tl tr) as t.
    assert (H1: subtree tl tl).
      {
      apply subtree_trans with (t2:= t).
      - exact H0.
      - apply sub_bl with (tr:= tr) (n:= n0).
        exact Heqt.
      }
    contradiction.
Qed.

Lemma btree_subst_bcode:
forall t1 t2 t': btree,
forall c1 c1' c2: list bool,
bcode t1 (c1 ++ c1') ->
bcode t2 c2 ->
btree_subst t1 t2 c1 = Some t' ->
bcode t' (c1 ++ c2).
Proof.
intros t1 t2 t' c1.
revert t1 t2 t'.
induction c1. 
- intros t1 t2 t' c1' c2 H1 H2 H3.
  rewrite btree_subst_empty in H3.
  inversion H3.
  subst.
  exact H2.
- intros t1 t2 t' c1' c2 H1 H2 H3.
  inversion H1.
  + clear H1. 
    subst.
    assert (H10: exists bt1': btree, btree_subst bt1 t2 c1 = Some bt1').
      {
      apply bcode_btree_subst with (c2:= c1').
      exact H5.
      }
    destruct H10 as [bt1' H10].
    specialize (IHc1 bt1 t2 bt1' c1' c2 H5 H2 H10).
    simpl in H3.
    rewrite H10 in H3.
    inversion H3.
    apply bcode_1 with (bt:= bnode_2 n bt1' bt2) (n:= n) (bt2:= bt2) in IHc1.
    * exact IHc1. 
    * reflexivity.
  + clear H1. 
    subst.
    assert (H10: exists bt2': btree, btree_subst bt2 t2 c1 = Some bt2').
      {
      apply bcode_btree_subst with (c2:= c1').
      exact H5.
      }
    destruct H10 as [bt2' H10].
    specialize (IHc1 bt2 t2 bt2' c1' c2 H5 H2 H10).
    simpl in H3.
    rewrite H10 in H3.
    inversion H3.
    apply bcode_2 with (bt:= bnode_2 n bt1 bt2') (n:= n) (bt1:= bt1) in IHc1.
    * exact IHc1. 
    * reflexivity.
Qed.

Lemma btree_subst_subtree:
forall t1 t2 t3 t': btree,
forall c1 c1': list bool,
bcode t1 (c1 ++ c1') ->
subtree t2 t3 ->
btree_subst t1 t2 c1 = Some t' ->
subtree t' t3.
Proof.
intros t1 t2 t3 t' c1.
revert t1 t2 t3 t'.
induction c1.
- intros t1 t2 t3 t' c1' H1 H2 H3.
  rewrite btree_subst_empty in H3.
  inversion H3.
  subst.
  exact H2.
- intros t1 t2 t3 t' c1' H1 H2 H3.
  inversion H1.
  + subst.
    assert (H6: exists bt1': btree, btree_subst bt1 t2 c1 = Some bt1').
      {
      apply bcode_btree_subst with (c2:= c1').
      exact H5.
      }
    destruct H6 as [bt1' H6].
    simpl in H3.
    rewrite H6 in H3.
    specialize (IHc1 bt1 t2 t3 bt1' c1' H5 H2 H6).
    inversion H3.
    apply subtree_trans with (t2:= bt1').
    * apply sub_bl with (tr:= bt2) (n:= n).
      reflexivity.
    * exact IHc1.
  + subst.
    assert (H6: exists bt2': btree, btree_subst bt2 t2 c1 = Some bt2').
      {
      apply bcode_btree_subst with (c2:= c1').
      exact H5.
      }
    destruct H6 as [bt2' H6].
    simpl in H3.
    rewrite H6 in H3.
    specialize (IHc1 bt2 t2 t3 bt2' c1' H5 H2 H6).
    inversion H3.
    apply subtree_trans with (t2:= bt2').
    * apply sub_br with (tl:= bt1) (n:= n).
      reflexivity.
    * exact IHc1.
Qed.

Lemma btree_subst_subtree_bcode:
forall t1 t2 t3 t': btree,
forall c1 c2: list bool,
subtree_bcode t2 t3 c2 ->
btree_subst t1 t2 c1 = Some t' ->
subtree_bcode t' t3 (c1 ++ c2).
Proof.
intros t1 t2 t3 t' c1.
revert t1 t2 t3 t'.
induction c1.
- intros t1 t2 t3 t' c1' H1 H2.
  rewrite btree_subst_empty in H2.
  inversion H2.
  subst.
  exact H1.
- intros t1 t2 t3 t' c2 H1 H2.
  destruct t1, a.
  + simpl in H2.
    discriminate.
  + simpl in H2.
    discriminate.
  + assert (H3: exists t1_2': btree, btree_subst t1_2 t2 c1 = Some t1_2').
      {
      simpl in H2.
      destruct (btree_subst t1_2 t2 c1).
      - exists b.
        reflexivity.
      - discriminate.
      }
    destruct H3 as [t1_2' H3].
    specialize (IHc1 t1_2 t2 t3 t1_2' c2 H1 H3).
    simpl in H2.
    rewrite H3 in H2.
    inversion H2. 
    apply sb_ir with (t1:= bnode_2 n t1_1 t1_2') (tl:= t1_1) (tr:= t1_2') (n:= n) in IHc1.
    * exact IHc1.
    * reflexivity.
  + assert (H3: exists t1_1': btree, btree_subst t1_1 t2 c1 = Some t1_1').
      {
      simpl in H2.
      destruct (btree_subst t1_1 t2 c1).
      - exists b.
        reflexivity.
      - discriminate.
      }
    destruct H3 as [t1_1' H3].
    specialize (IHc1 t1_1 t2 t3 t1_1' c2 H1 H3).
    simpl in H2.
    rewrite H3 in H2.
    inversion H2. 
    apply sb_il with (t1:= bnode_2 n t1_1' t1_2) (tl:= t1_1') (tr:= t1_2) (n:= n) in IHc1.
    * exact IHc1.
    * reflexivity.
Qed.

Lemma not_subtree_bcode:
forall t1 t2: btree,
~ subtree_bcode t1 t2 [].
Proof.
intros t1 t2 H.
inversion H.
Qed.

Fixpoint btree_decompose (bt: btree) (c: list bool): option (sentence * btree * sentence):=
match bt, c with
| bnode_1 n t, [] => 
          Some ([], bt, [])
| bnode_1 n t, _ =>  
          None
| bnode_2 n bt1 bt2, [] => 
          Some ([], bt, [])
| bnode_2 n bt1 bt2, false :: c =>
          match btree_decompose bt1 c with
          | None => None
          | Some (l, bt, r) => Some (l, bt, r ++ bfrontier bt2)
          end
| bnode_2 n bt1 bt2, true :: c => 
          match btree_decompose bt2 c with
          | None => None
          | Some (l, bt, r) => Some (bfrontier bt1 ++ l, bt, r)
          end
end.

Lemma btree_decompose_empty:
forall t: btree,
btree_decompose t [] = Some ([], t, []).
Proof.
intros t.
destruct t.
- simpl.
  reflexivity.
- simpl.
  reflexivity.
Qed.

Lemma btree_decompose_bfrontier:
forall t1 t2: btree,
forall c: list bool,
forall x y: sentence,
btree_decompose t1 c = Some (x, t2, y) ->
bfrontier t1 = x ++ bfrontier t2 ++ y /\
(c <> [] -> x ++ y <> []).
Proof.
induction t1.
- intros t2 c x y H1.
  destruct c.
  + rewrite btree_decompose_empty in H1.
    inversion H1.
    simpl.
    auto.
  + simpl in H1.
    discriminate.
- intros t2 c x y H1.
  destruct c.
  + rewrite btree_decompose_empty in H1.
    inversion H1.
    simpl.
    rewrite app_nil_r.
    auto.
  + destruct b.
    * assert (H2: exists x' y': sentence,
                  exists t1_2': btree,
                  btree_decompose t1_2 c = Some (x', t1_2', y')).
        {
        simpl in H1. 
        destruct (btree_decompose t1_2 c).
        - destruct p as (p0, r).
          destruct p0 as (l, bt).
          exists l, r, bt.
          reflexivity.
        - discriminate.  
        }
      destruct H2 as [x' [y' [t1_2' H2]]].
      specialize (IHt1_2 t1_2' c x' y' H2).
      simpl in H1.
      rewrite H2 in H1.
      inversion H1.
      subst.
      simpl.
      destruct IHt1_2 as [IHt1_2 HH].
      {
      split.
      - rewrite IHt1_2.
        rewrite <- app_assoc.
        reflexivity.
      - intros _.
        apply app_not_nil_inv.
        left.
        apply app_not_nil_inv.
        left.
        apply bfrontier_not_nil.
      }
    * assert (H2: exists x' y': sentence,
                  exists t1_1': btree,
                  btree_decompose t1_1 c = Some (x', t1_1', y')).
        {
        simpl in H1. 
        destruct (btree_decompose t1_1 c).
        - destruct p as (p0, r).
          destruct p0 as (l, bt).
          exists l, r, bt.
          reflexivity.
        - discriminate.  
        }
      destruct H2 as [x' [y' [t1_1' H2]]].
      specialize (IHt1_1 t1_1' c x' y' H2).
      simpl in H1.
      rewrite H2 in H1.
      inversion H1.
      subst.
      simpl.
      destruct IHt1_1 as [IHt1_1 HH].
      {
      split.
      - rewrite IHt1_1.
        repeat rewrite <- app_assoc.
        reflexivity.
      - intros _.
        apply app_not_nil_inv.
        right.
        apply app_not_nil_inv.
        right.
        apply bfrontier_not_nil.
      }
Qed.

Lemma btree_decompose_subtree_bcode:
forall t1 t2: btree,
forall c1: list bool,
forall v x: sentence,
btree_decompose t1 c1 = Some (v, t2, x) ->
c1 <> [] ->
subtree_bcode t1 t2 c1.
Proof.
induction t1.
- intros t2 c1 v x H1 H2.
  simpl in H1.
  destruct c1.
  + destruct H2.
    reflexivity.
  + discriminate.
- intros t2 c1 v x H1 H2.
  destruct c1.
  + destruct H2.
    reflexivity.
  + destruct b. 
    * assert (H3: c1 = [] \/ c1 <> []). 
        {
        apply nil_not_nil. 
        }
      {
      destruct H3 as [H3 | H3].
      - subst.
        simpl in H1.
        rewrite btree_decompose_empty in H1.
        inversion H1.
        subst.
        apply sb_br with (tl:= t1_1) (n:= n).
        reflexivity.
      - assert (H4: exists v' x': sentence, 
                    exists t1_2': btree,
                    btree_decompose t1_2 c1 = Some (v', t1_2', x')).
          {
          simpl in H1. 
          destruct (btree_decompose t1_2 c1).
          + destruct p as (p0, r).
            destruct p0 as (l, bt).
            exists l, r, bt.
            reflexivity.
          + discriminate.
          }
        destruct H4 as [v' [x' [t1_2' H4]]].
        simpl in H1. 
        rewrite H4 in H1.
        inversion H1.
        specialize (IHt1_2 t1_2' c1 v' x' H4 H3).
        subst.
        apply sb_ir with (tl:= t1_1) (tr:= t1_2) (n:= n).
        + exact IHt1_2.
        + reflexivity.
      }
    * assert (H3: c1 = [] \/ c1 <> []). 
        {
        apply nil_not_nil. 
        }
      {
      destruct H3 as [H3 | H3].
      - subst.
        simpl in H1.
        rewrite btree_decompose_empty in H1.
        inversion H1.
        subst.
        apply sb_bl with (tr:= t1_2) (n:= n).
        reflexivity.
      - assert (H4: exists v' x': sentence, 
                    exists t1_1': btree,
                    btree_decompose t1_1 c1 = Some (v', t1_1', x')).
          {
          simpl in H1. 
          destruct (btree_decompose t1_1 c1).
          + destruct p as (p0, r).
            destruct p0 as (l, bt).
            exists l, r, bt.
            reflexivity.
          + discriminate.
          }
        destruct H4 as [v' [x' [t1_1' H4]]].
        simpl in H1. 
        rewrite H4 in H1.
        inversion H1.
        specialize (IHt1_1 t1_1' c1 v' x' H4 H3).
        subst.
        apply sb_il with (tl:= t1_1) (tr:= t1_2) (n:= n).
        + exact IHt1_1.
        + reflexivity.
      }
Qed.

Lemma btree_decompose_get_nt:
forall t1 t2: btree,
forall c1: list bool,
forall v x: sentence,
btree_decompose t1 c1 = Some (v, t2, x) ->
get_nt_btree c1 t1 = Some (broot t2).
Proof.
induction t1.
- intros t2 c1 v x H.
  destruct c1.
  + rewrite btree_decompose_empty in H.
    inversion H.
    simpl.
    reflexivity.
  + destruct b.
    * simpl in H.
      discriminate.
    * simpl in H.
      discriminate.
- intros t2 c1 v x H1.
  destruct c1.
  + rewrite btree_decompose_empty in H1.
    inversion H1.
    subst.
    simpl.
    reflexivity.
  + destruct b.
    * assert (H2: exists v' x': sentence,
                  exists t1_2': btree,
                  btree_decompose t1_2 c1 = Some (v', t1_2', x')).
        {
        simpl in H1.
        destruct (btree_decompose t1_2 c1).
        - destruct p as (p0, r).
          destruct p0 as (l, bt).
          exists l, r, bt.
          reflexivity.
        - discriminate.
        }
      destruct H2 as [v' [x' [t1_2' H2]]].
      specialize (IHt1_2 t1_2' c1 v' x' H2).
      simpl.
      simpl in H1.
      rewrite H2 in H1.
      inversion H1.
      subst.
      exact IHt1_2.
    * assert (H2: exists v' x': sentence,
                  exists t1_1': btree,
                  btree_decompose t1_1 c1 = Some (v', t1_1', x')).
        {
        simpl in H1.
        destruct (btree_decompose t1_1 c1).
        - destruct p as (p0, r).
          destruct p0 as (l, bt).
          exists l, r, bt.
          reflexivity.
        - discriminate.
        }
      destruct H2 as [v' [x' [t1_1' H2]]].
      specialize (IHt1_1 t1_1' c1 v' x' H2).
      simpl.
      simpl in H1.
      rewrite H2 in H1.
      inversion H1.
      subst.
      exact IHt1_1.
Qed.

Lemma bcode_split:
forall t: btree,
forall p1 p2: sf,
forall c: list bool,
bpath_bcode t (p1 ++ p2) c ->
length p1 > 0 ->
length p2 > 1 ->
bheight t = length p1 + length p2 - 1 ->
exists c1 c2: list bool,
c = c1 ++ c2 /\
length c1 = length p1 /\
exists t2: btree,
exists x y: sentence,
bpath_bcode t2 p2 c2 /\
btree_decompose t c1 = Some (x, t2, y) /\
bheight t2 = length p2 - 1.
Proof.
induction t.
- intros p1 p2 c H1 H2 H3 HH.
  inversion H1.
  + clear H1.
    inversion H0.
    subst.
    clear H0.
    exists [], [].
    split.
    * reflexivity.
    * {
      destruct p1.
      - simpl in H2.
        omega. 
      - inversion H.
        clear H.
        destruct p1.
        + simpl in H4. 
          rewrite <- H4 in H3.
          simpl in H3.
          omega.
        + inversion H4.
          symmetry in H4. 
          inversion H4. 
          apply app_eq_nil in H7.
          destruct H7 as [_ H7].
          rewrite H7 in H3.
          simpl in H3.
          omega.
      }
  + discriminate.
  + discriminate. 
- intros p1 p2 c H1 H2 H3 HH.
  inversion H1.
  + discriminate.
  + clear H1. 
    inversion H0.
    subst.
    clear IHt2.
    destruct p1.
    * simpl in H2. 
      omega. 
    * inversion H.
      clear H.
      subst.
      assert (H6: length p1 = 0 \/ length p1 > 0) by omega.
      {
      destruct H6 as [H6 | H6].
      - apply length_eq_0 in H6. 
        subst. 
        simpl in H4, H5. 
        exists [false], c1.
        split.
        + reflexivity.
        + split.
          * simpl. 
            reflexivity.
          * exists bt1, [], (bfrontier bt2).
            {
            split.
            - exact H5.
            - split.
              + simpl. 
                rewrite btree_decompose_empty.
                reflexivity. 
              + simpl length in HH.
                replace (1 + length p2 - 1) with (length p2) in HH.
                * {
                  apply bheight_child_left with (t1:= bt1) (t2:= bt2) (n:= n0) (p1:= p2) in HH.
                  - exact HH.
                  - reflexivity.
                  - exact H4.
                  - reflexivity.
                  }
                 * omega.
            }
      - specialize (IHt1 p1 p2 c1 H5 H6 H3).
        simpl length in HH.
        replace (S (length p1) + length p2 - 1) with (length p1 + length p2) in HH.
        + apply bheight_child_left with (t1:= bt1) (t2:= bt2) (n:= n0) (p1:= p1 ++ p2) in HH.
          * rewrite app_length in HH. 
            specialize (IHt1 HH).
            destruct IHt1 as [c0 [c2 [H7 [H8 [t2 [x [y [H9 [H10 H11]]]]]]]]].
            rewrite H7.
            exists (false :: c0), c2.
            {
            split.
            - reflexivity.
            - simpl.
              split.
              + rewrite H8.
                reflexivity.
              + exists t2, x, (y ++ bfrontier bt2).
                split.
                * exact H9. 
                * {
                  split.
                  - rewrite H10. 
                    reflexivity.
                  - omega.
                  }
            }
          * reflexivity.
          * exact H4.
          * rewrite app_length.
            reflexivity.
        + omega.
      }
  + clear H1.
    inversion H0.
    subst.
    clear H0.
    clear IHt1.
    destruct p1.
    * {
      destruct p2. 
      - inversion H. 
      - inversion H. 
        clear H.
        subst.
        exists [], (true :: c2).
        split.
        + reflexivity.
        + split.
          * reflexivity.
          * exists (bnode_2 n0 bt1 bt2), [], [].
            {
            split.
            - apply bb_2 with (bt1:= bt1) (bt2:= bt2).
              + reflexivity.
              + exact H4.
              + exact H5.
            - split.
              + rewrite btree_decompose_empty. 
                reflexivity. 
              + simpl in H2.
                omega.
            }
      }
    * inversion H.
      clear H.
      subst.
      assert (H6: length p1 = 0 \/ length p1 > 0) by omega.
      {
      destruct H6 as [H6 | H6].
      - apply length_eq_0 in H6. 
        subst. 
        simpl in H4, H5. 
        exists [true], c2.
        split.
        + reflexivity.
        + split.
          * simpl. 
            reflexivity.
          * exists bt2, (bfrontier bt1), [].
            {
            split.
            - exact H5.
            - split. 
              + simpl. 
                rewrite btree_decompose_empty.
                rewrite app_nil_r.  
                reflexivity.
              + simpl length in HH.
                replace (1 + length p2 - 1) with (length p2) in HH.
                * {
                  apply bheight_child_right with (t1:= bt1) (t2:= bt2) (n:= n0) (p2:= p2) in HH.
                  - exact HH.
                  - reflexivity.
                  - exact H4.
                  - reflexivity.
                  }
                * omega.
            }
      - specialize (IHt2 p1 p2 c2 H5 H6 H3).
        simpl length in HH.
        replace (S (length p1) + length p2 - 1) with (length p1 + length p2) in HH.
        + apply bheight_child_right with (t1:= bt1) (t2:= bt2) (n:= n0) (p2:= p1 ++ p2) in HH.
          * rewrite app_length in HH. 
            specialize (IHt2 HH).
            destruct IHt2 as [c1 [c0 [H7 [H8 [t2 [x [y [H9 [H10 H11]]]]]]]]].
            rewrite H7.
            exists (true :: c1), c0.
            {
            split.
            - reflexivity.
            - simpl.
              split.
              + rewrite H8.
                reflexivity.
              + exists t2, (bfrontier bt1 ++ x), y.
                split.
                * exact H9.
                * {
                  split. 
                  - rewrite H10.
                    reflexivity.
                  - omega.
                  }
            }
          * reflexivity.
          * exact H4.
          * rewrite app_length.
            reflexivity.
        + omega.
      }
Qed.

Lemma btree_subst_decompose:
forall t1 t2 t3 t': btree,
forall c1: list bool,
forall x y: sentence,
btree_decompose t1 c1 = Some (x, t2, y) ->
btree_subst t1 t3 c1 = Some t' ->
btree_decompose t' c1 = Some (x, t3, y).
Proof.
intros t1 t2 t3 t' c1.
revert t1 t2 t3 t'.
induction c1.
- intros t1 t2 t3 t' x y H1 H2.
  rewrite btree_subst_empty in H2.
  inversion H2.
  subst.
  rewrite btree_decompose_empty in H1.
  inversion H1.
  subst.
  rewrite btree_decompose_empty.
  reflexivity.
- intros t1 t2 t3 t' x y H1 H2.
  destruct t1.
  + simpl in H1. 
    discriminate.
  + destruct a.
    * assert (H3: exists t1_2': btree,
                  exists x' y': sentence,
                  btree_decompose t1_2 c1 = Some (x', t1_2', y')). 
        {
        simpl in H1.
        destruct (btree_decompose t1_2 c1).
        - destruct p as (p0, r).
          destruct p0 as (l, bt).
          exists bt, l, r.
          reflexivity.
        - discriminate.
        }
      destruct H3 as [t1_2' [x' [y' H3]]].
      assert (H4: exists t1_2'': btree,
                  btree_subst t1_2 t3 c1 = Some t1_2'').
        {
        simpl in H2.
        destruct (btree_subst t1_2 t3 c1).
        - exists b.
          reflexivity.
        - discriminate.
        }
      destruct H4 as [t1_2'' H4].
      specialize (IHc1 t1_2 t1_2' t3 t1_2'' x' y' H3 H4).
      simpl in H1.
      rewrite H3 in H1.
      inversion H1.
      simpl in H2.
      rewrite H4 in H2.
      inversion H2.
      subst.
      simpl.
      rewrite IHc1.
      reflexivity.
    * assert (H3: exists t1_1': btree,
                  exists x' y': sentence,
                  btree_decompose t1_1 c1 = Some (x', t1_1', y')). 
        {
        simpl in H1.
        destruct (btree_decompose t1_1 c1).
        - destruct p as (p0, r).
          destruct p0 as (l, bt).
          exists bt, l, r.
          reflexivity.
        - discriminate.
        }
      destruct H3 as [t1_1' [x' [y' H3]]].
      assert (H4: exists t1_1'': btree,
                  btree_subst t1_1 t3 c1 = Some t1_1'').
        {
        simpl in H2.
        destruct (btree_subst t1_1 t3 c1).
        - exists b.
          reflexivity.
        - discriminate.
        }
      destruct H4 as [t1_1'' H4].
      specialize (IHc1 t1_1 t1_1' t3 t1_1'' x' y' H3 H4).
      simpl in H1.
      rewrite H3 in H1.
      inversion H1.
      simpl in H2.
      rewrite H4 in H2.
      inversion H2.
      subst.
      simpl.
      rewrite IHc1.
      reflexivity.      
Qed.

Lemma btree_decompose_combine:
forall t0 t1 t2: btree,
forall u v x y: sentence,
forall c0 c1: list bool,
btree_decompose t0 c0 = Some (u, t1, y) ->
btree_decompose t1 c1 = Some (v, t2, x) ->
btree_decompose t0 (c0 ++ c1) = Some (u ++ v, t2, x ++ y).
Proof.
intros t0 t1 t2 u v x y c0.
revert t0 t1 t2 u v x y.
induction c0.
- intros t0 t1 t2 u v x y c1 H1 H2.
  rewrite btree_decompose_empty in H1.
  inversion H1.
  simpl.
  rewrite H2.
  rewrite app_nil_r.
  reflexivity.
- intros t0 t1 t2 u v x y c1 H1 H2.
  destruct t0.
  + simpl in H1.
    discriminate.
  + destruct a.
    * assert (H3: exists t0_2': btree,
                  exists u' y': sentence,
                  btree_decompose t0_2 c0 = Some (u', t0_2', y')).
        {
        simpl in H1.
        destruct (btree_decompose t0_2 c0).
        - destruct p as (p0, r).
          destruct p0 as (l, bt).
          exists bt, l, r.
          reflexivity.
        - discriminate.
        }
      destruct H3 as [t0_2' [u' [y' H3]]].
      simpl in H1.
      rewrite H3 in H1.
      inversion H1.
      subst.
      specialize (IHc0 t0_2 t1 t2 u' v x y c1 H3 H2).
      simpl.
      rewrite IHc0.
      rewrite <- app_assoc.
      reflexivity.
    * assert (H3: exists t0_1': btree,
                  exists u' y': sentence,
                  btree_decompose t0_1 c0 = Some (u', t0_1', y')).
        {
        simpl in H1.
        destruct (btree_decompose t0_1 c0).
        - destruct p as (p0, r).
          destruct p0 as (l, bt).
          exists bt, l, r.
          reflexivity.
        - discriminate.
        }
      destruct H3 as [t0_1' [u' [y' H3]]].
      simpl in H1.
      rewrite H3 in H1.
      inversion H1.
      subst.
      specialize (IHc0 t0_1 t1 t2 u v x y' c1 H3 H2).
      simpl.
      rewrite IHc0.
      rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma btree_subst_bfrontier:
forall t1 t2 t3 t': btree,
forall c1: list bool,
forall x y: sentence,
subtree_bcode t1 t2 c1 ->
btree_decompose t1 c1 = Some (x, t2, y) ->
btree_subst t1 t3 c1 = Some t' ->
bfrontier t' = x ++ bfrontier t3 ++ y.
Proof.
intros t1 t2 t3 t' c1.
revert  t1 t2 t3 t'.
induction c1.
- intros t1 t2 t3 t' x y H.
  apply not_subtree_bcode in H.
  contradiction.
- intros t1 t2 t3 t' x y H1 H2 H3.
  inversion H1.
  + subst.
    clear H1.
    simpl in H3.
    rewrite btree_subst_empty in H3.
    inversion H3.
    clear H0 H3.
    simpl in H2.
    rewrite btree_decompose_empty in H2.
    inversion H2.
    repeat rewrite app_nil_r.
    reflexivity.
  + subst.
    clear H1.
    simpl in H3.
    rewrite btree_subst_empty in H3.
    inversion H3.
    clear H0 H3.
    simpl in H2.
    rewrite btree_decompose_empty in H2.
    inversion H2.
    repeat rewrite app_nil_r.
    reflexivity.
  + subst.
    clear H1.
    assert (H5: exists tr': btree, btree_subst tr t3 c1 = Some tr').
      {
      simpl in H3.
      destruct (btree_subst tr t3 c1).
      - inversion H3.
        exists b.
        reflexivity.
      - discriminate.
      }
    destruct H5 as [tr' H5].
    simpl in H3.
    rewrite H5 in H3.
    inversion H3.
    clear H3.
    assert (H6: exists x' y': sentence,
                exists t2': btree,
                btree_decompose tr c1 = Some (x', t2', y')).
      {
      simpl in H2.
      destruct (btree_decompose tr c1).
      - destruct p as [p r].
        destruct p as [l bt].
        inversion H2.
        clear H2.
        subst.
        exists l, y, t2.
        reflexivity.
      - discriminate.  
      }
    destruct H6 as [x' [y' [t2' H6]]].
    simpl in H2.
    rewrite H6 in H2.
    inversion H2.
    subst.
    specialize (IHc1 tr t2 t3 tr' x' y H4 H6 H5).
    simpl. 
    rewrite IHc1.
    rewrite <- app_assoc.
    reflexivity.
  + subst.
    clear H1.
    assert (H5: exists tl': btree, btree_subst tl t3 c1 = Some tl').
      {
      simpl in H3.
      destruct (btree_subst tl t3 c1).
      - inversion H3.
        exists b.
        reflexivity.
      - discriminate.
      }
    destruct H5 as [tl' H5].
    simpl in H3.
    rewrite H5 in H3.
    inversion H3.
    clear H3.
    assert (H6: exists x' y': sentence,
                exists t2': btree,
                btree_decompose tl c1 = Some (x', t2', y')).
      {
      simpl in H2.
      destruct (btree_decompose tl c1).
      - destruct p as [p r].
        destruct p as [l bt].
        inversion H2.
        clear H2.
        subst.
        exists x, r, t2.
        reflexivity.
      - discriminate.  
      }
    destruct H6 as [x' [y' [t2' H6]]].
    simpl in H2.
    rewrite H6 in H2.
    inversion H2.
    subst.
    specialize (IHc1 tl t2 t3 tl' x y' H4 H6 H5).
    simpl. 
    rewrite IHc1.
    repeat rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma btree_subst_get_nt:
forall t1 t2 t': btree,
forall c1 c1' c2 c2': list bool,
forall n: non_terminal,
bcode t1 (c1 ++ c1') ->
bcode t2 (c2 ++ c2') ->
get_nt_btree c2 t2 = Some n ->
btree_subst t1 t2 c1 = Some t' ->
get_nt_btree (c1 ++ c2) t' = Some n.
Proof.
intros t1 t2 t' c1.
revert t1 t2 t'.
induction c1.
- intros t1 t2 t' c1' c2 c2' n H1 H2 H3 H4.
  rewrite btree_subst_empty in H4.
  inversion H4.
  clear H4.
  subst.
  exact H3.
- intros t1 t2 t' c1' c2 c2' n H1 H2 H3 H4.
  destruct a.
  + inversion H1.
    clear H1.
    assert (H10: exists bt2': btree, btree_subst bt2 t2 c1 = Some bt2').
      {
      apply bcode_btree_subst with (c2:= c1').
      exact H5.
      }
    destruct H10 as [bt2' H10].
    specialize (IHc1 bt2 t2 bt2' c1' c2 c2' n H5 H2 H3 H10).
    destruct t1.
    * discriminate. 
    * simpl in H4.
      inversion H0.
      clear H0.
      subst.
      rewrite H10 in H4.
      inversion H4.
      simpl.
      exact IHc1.
  + inversion H1.
    clear H1.
    assert (H10: exists bt1': btree, btree_subst bt1 t2 c1 = Some bt1').
      {
      apply bcode_btree_subst with (c2:= c1').
      exact H5.
      }
    destruct H10 as [bt1' H10].
    specialize (IHc1 bt1 t2 bt1' c1' c2 c2' n H5 H2 H3 H10).
    destruct t1.
    * discriminate. 
    * simpl in H4.
      inversion H0.
      clear H0.
      subst.
      rewrite H10 in H4.
      inversion H4.
      simpl.
      exact IHc1.
Qed.

Lemma subtree_bcode_subtree:
forall t1 t2: btree,
forall c1: list bool,
subtree_bcode t1 t2 c1 ->
subtree t1 t2.
Proof.
intros t1 t2 c1 H.
induction H.
- rewrite H.
  apply sub_br with (tl:= tl) (n:= n).
  reflexivity.
- rewrite H.
  apply sub_bl with (tr:= tr) (n:= n).
  reflexivity.
- rewrite H0.
  apply subtree_trans with (t2:= tr).
  + apply sub_br with (tl:= tl) (n:= n).
    reflexivity.
  + exact IHsubtree_bcode.
- rewrite H0.
  apply subtree_trans with (t2:= tl).
  + apply sub_bl with (tr:= tr) (n:= n).
    reflexivity.
  + exact IHsubtree_bcode.
Qed.

Lemma subtree_bcode_get_nt:
forall t1 t2: btree,
forall c1: list bool,
subtree_bcode t1 t2 c1 ->
get_nt_btree c1 t1 = Some (broot t2).
Proof.
intros t1 t2 c1 H.
induction H.
- rewrite H.
  simpl.
  destruct t2.
  + simpl.
    reflexivity.
  + simpl.
    reflexivity.
- rewrite H.
  simpl.
  destruct t2.
  + simpl.
    reflexivity.
  + simpl.
    reflexivity.
- rewrite H0.
  simpl. 
  exact IHsubtree_bcode.
- rewrite H0.
  simpl. 
  exact IHsubtree_bcode.
Qed.

End Binary_Trees.

(* --------------------------------------------------------------------- *)
(* TREES                                                                 *)
(* --------------------------------------------------------------------- *)

Section Trees.

Variable non_terminal: Type.
Variable terminal: Type.

Notation symbol:= (non_terminal + terminal)%type.
Notation sf:= (list symbol).

Inductive tree: Type:=
| node_t: terminal -> tree
| node_n: non_terminal -> tree
| node  : non_terminal -> tree_list -> tree
with tree_list: Type :=
| tl_nil : tree_list
| tl_cons: tree -> tree_list -> tree_list.

Scheme tree_ind2:=
Induction for tree Sort Prop
with tree_list_ind2:=
Induction for tree_list Sort Prop.

Scheme tree_min2:=
Minimality for tree Sort Prop
with tree_list_min2:=
Minimality for tree_list Sort Prop.

Definition root (t: tree): symbol:=
match t with
| node_t t => inr t
| node_n n => inl n
| node n l => inl n
end.

Fixpoint frontier (t: tree): sf:=
match t with
| node_t t => [inr t]
| node_n n => [inl n]
| node n l => frontier_list l
end
with frontier_list (l: tree_list): sf:=
match l with
| tl_nil => []
| tl_cons s l' => frontier s ++ frontier_list l'
end.

Fixpoint height (t: tree): nat:=
match t with
| node_t t => 0
| node_n n => 0
| node n l => S (height_list l)
end
with height_list (l: tree_list): nat :=
match l with
| tl_nil => 0
| tl_cons s l' => if leb (height s) (height_list l')
                     then (height_list l')
                     else (height s)
end.

Fixpoint nodes (t: tree): nat:=
match t with
| node_t t => 1
| node_n n => 1
| node n l => S (nodes_list l)
end
with nodes_list (l: tree_list):nat :=
match l with
| tl_nil => 0
| tl_cons s l' => nodes s + nodes_list l'
end.

End Trees.

(* --------------------------------------------------------------------- *)
(* BINARY TREES AND TREES                                                *)
(* --------------------------------------------------------------------- *)

Section Binary_Trees_and_Trees.

Variable non_terminal: Type.
Variable terminal: Type.

Fixpoint btree_to_tree (bt: btree non_terminal terminal): tree non_terminal terminal:=
match bt with
| bnode_1 n t => node n (tl_cons (node_t _ t) (tl_nil _ _))
| bnode_2 n bt1 bt2 => node n (tl_cons (btree_to_tree bt1) (tl_cons (btree_to_tree bt2) (tl_nil _ _)))  
end.

Lemma btree_tree_preserves_root:
forall bt: btree non_terminal terminal,
inl (broot bt) = root (btree_to_tree bt).
Proof.
induction bt.
- simpl. 
  reflexivity.
- simpl.
  reflexivity.
Qed.

Lemma btree_tree_preserves_frontier:
forall bt: btree non_terminal terminal,
map inr (bfrontier bt) = frontier (btree_to_tree bt).
Proof.
induction bt.
- simpl. (* ttt *)
  reflexivity.
- simpl.
  rewrite map_app.
  rewrite IHbt1.
  rewrite IHbt2. 
  admit. (* ttt *)
Qed.

End Binary_Trees_and_Trees.

(* --------------------------------------------------------------------- *)
(* BINARY TREES AND CHOMSKY                                              *)
(* --------------------------------------------------------------------- *)

Section Binary_Chomsky.

Variables non_terminal terminal: Type.

Notation sentence:= (list terminal).
Notation symbol:= (non_terminal + terminal)%type.
Notation sf:= (list symbol).
Notation non_terminal':= (chomsky.non_terminal' non_terminal terminal).
Notation symbol':= (non_terminal' + terminal)%type.
Notation sf':= (list symbol').
Notation term_lift':= ((terminal_lift non_terminal') terminal).

Inductive btree_cnf (g: cfg non_terminal' terminal) (bt: btree non_terminal' terminal): Prop:=
| bt_c1: forall n: non_terminal',
         forall t: terminal,
         rules g n [inr t] -> 
         bt = (bnode_1 n t) -> 
         btree_cnf g bt
| bt_c2: forall n n1 n2: non_terminal',
         forall bt1 bt2: btree _ _,
         rules g n [inl n1; inl n2] -> 
         btree_cnf g bt1 ->
         broot bt1 = n1 ->
         btree_cnf g bt2 -> 
         broot bt2 = n2 ->
         bt = (bnode_2 n bt1 bt2) -> 
         btree_cnf g bt.

Lemma derives_g_cnf_equiv_btree_v1:
forall g: cfg non_terminal terminal,
forall n: non_terminal',
forall s: sentence,
derives (g_cnf g) [inl n] (map term_lift' s) ->
exists t: btree non_terminal' terminal,
btree_cnf (g_cnf g) t /\
broot t = n /\
bfrontier t = s.
Proof.
intros g n s H2.
rewrite derives_equiv_derives6 in H2.
destruct H2 as [n0 H2].
revert H2.
generalize dependent s.
generalize (le_refl n0).
generalize n0 at 1 3 as n0'.
generalize dependent n. 
induction n0.
- intros n n0' HH s H2.
  inversion HH.
  subst.
  inversion H2.
  subst.
  destruct s.
  + simpl in H.
    inversion H.
  + simpl in H.
    inversion H.
- intros n n0' HH s H2.
  assert (HHH: n0' = 0 \/ exists n0'': nat, n0' = S n0'').
    {
    apply nat_struct.
    }
  destruct HHH as [HHH | HHH].
  + subst.
    inversion H2. 
    destruct s.
    * simpl in H.
      inversion H.
    * simpl in H.
      inversion H.
  + destruct HHH as [n0'' HHH].
    subst.
    inversion H2.
    subst.
    assert (H1' := H1).
    assert (Hs1s2: s1 = [] /\ s2 = []).
      {
      destruct s1. 
      - inversion H0. 
        auto. 
      - inversion H0. 
        destruct s1. 
        + inversion H5. 
        + inversion H5. 
      }
    destruct Hs1s2 as [Hs1 Hs2].
    subst.
    inversion H0.
    subst.
    simpl in H1.
    apply g_cnf_right_formats in H1.
    destruct H1 as [H1 | H1].
    * destruct H1 as [t H1].
      subst.
      simpl in H3.
      assert (H5: exists n0'': nat, derives6 (g_cnf g) n0'' [inr t] (map term_lift' s)).
        {
        exists n0''.
        exact H3.
        }
      rewrite <- derives_equiv_derives6 in H5.
      change [inr t] with (map term_lift' [t]) in H5.
      apply derives_sentence_left in H5.
      subst.
      exists (bnode_1 n t).
      {
      split.
      - apply bt_c1 with (n:= n) (t:= t).
        + exact H1'.
        + reflexivity.
      - split.
        + simpl. 
          reflexivity.
        + simpl. 
          apply terminal_lift_inj in H5.
          symmetry.
          exact H5.
      }
    * destruct H1 as [s1 [s0 H1]].
      subst.
      simpl in H3.
      change [inl (Lift_r [s1]); inl (Lift_r s0)] with ([inl (Lift_r [s1])] ++ [inl terminal (Lift_r s0)]) in H3.
      apply derives6_split in H3.
      destruct H3 as [s1' [s2' [n1 [n2 [H5 [H6 [H7 H8]]]]]]].
      assert (IHn0':= IHn0).
      assert (H40: n1 <= n0) by omega.
      symmetry in H5.
      apply map_expand in H5.
      destruct H5 as [s1'0 [s2'0 [H5 [H10 H11]]]].
      subst.
      specialize (IHn0 (Lift_r [s1]) n1 H40 s1'0 H7).
      assert (H50: n2 <= n0) by omega.
      specialize (IHn0' (Lift_r s0) n2 H50 s2'0 H8).
      destruct IHn0 as [t1 [H20 [H21 H22]]].
      destruct IHn0' as [t2 [H30 [H31 H32]]].
      exists (bnode_2 n t1 t2).
      {
      split.
      - apply bt_c2 with (bt1:= t1) (bt2:= t2) (n:= n) (n1:= Lift_r [s1]) (n2:= Lift_r s0). 
        + exact H1'. 
        + exact H20.
        + exact H21.
        + exact H30. 
        + exact H31. 
        + reflexivity.      
      - split.
        + simpl.
          reflexivity.
        + simpl.
          rewrite H22.  
          rewrite H32.
          reflexivity.
      } 
Qed.

Lemma derives_g_cnf_equiv_btree_v2:
forall g: cfg non_terminal' terminal,
forall n: non_terminal',
forall s: sentence,
is_cnf g ->
derives g [inl n] (map term_lift' s) ->
exists t: btree non_terminal' terminal,
btree_cnf g t /\
broot t = n /\
bfrontier t = s.
Proof.
intros g n s H1 H2.
rewrite derives_equiv_derives6 in H2.
destruct H2 as [n0 H2].
revert H2.
generalize dependent s.
generalize (le_refl n0).
generalize n0 at 1 3 as n0'.
generalize dependent n. 
induction n0.
- intros n n0' HH s H2.
  inversion HH.
  subst.
  inversion H2.
  subst.
  destruct s.
  + simpl in H.
    inversion H.
  + simpl in H.
    inversion H.
- intros n n0' HH s H2.
  assert (HHH: n0' = 0 \/ exists n0'': nat, n0' = S n0'').
    {
    apply nat_struct.
    }
  destruct HHH as [HHH | HHH].
  + subst.
    inversion H2. 
    destruct s.
    * simpl in H.
      inversion H.
    * simpl in H.
      inversion H.
  + destruct HHH as [n0'' HHH].
    subst.
    inversion H2.
    subst.
    assert (H1':= H1).
    assert (Hs1s2: s1 = [] /\ s2 = []).
      {
      destruct s1. 
      - inversion H0. 
        auto. 
      - inversion H0. 
        destruct s1. 
        + inversion H6. 
        + inversion H6. 
      }
    destruct Hs1s2 as [Hs1 Hs2].
    subst.
    inversion H0.
    subst.
    apply is_cnf_right_formats_v1 with (left:= n) (right:= right) in H1.
    * {
      destruct H1 as [H1 | H1].
      - destruct H1 as [t H1].
        subst.
        simpl in H4.
        assert (H5: exists n0'': nat, derives6 g n0'' [inr t] (map term_lift' s)).
          {
          exists n0''.
          exact H4.
          }
        rewrite <- derives_equiv_derives6 in H5.
        change [inr t] with (map term_lift' [t]) in H5.
        apply derives_sentence_left in H5.
        subst.
        exists (bnode_1 n t).
        split.
        + apply bt_c1 with (n:= n) (t:= t).
          * exact H3.
          * reflexivity.
        + split.
          * simpl. 
            reflexivity.
          * simpl. 
            apply terminal_lift_inj in H5.
            symmetry.
            exact H5.
      - destruct H1 as [s1 [s2 H1]].
        subst.
        simpl in H4.
        change [inl (Lift_r s1); inl (Lift_r s2)] with ([inl (Lift_r s1)] ++ [inl terminal (Lift_r s2)]) in H4.
        apply derives6_split in H4.
        destruct H4 as [s1' [s2' [n1 [n2 [H5 [H6 [H7 H8]]]]]]].
        assert (IHn0':= IHn0).
        assert (H40: n1 <= n0) by omega.
        symmetry in H5.
        apply map_expand in H5.
        destruct H5 as [s1'0 [s2'0 [H5 [H10 H11]]]].
        subst.
        specialize (IHn0 (Lift_r s1) n1 H40 s1'0 H7).
        assert (H50: n2 <= n0) by omega.
        specialize (IHn0' (Lift_r s2) n2 H50 s2'0 H8).
        destruct IHn0 as [t1 [H20 [H21 H22]]].
        destruct IHn0' as [t2 [H30 [H31 H32]]].
        exists (bnode_2 n t1 t2).
        split.
        + apply bt_c2 with (bt1:= t1) (bt2:= t2) (n:= n) (n1:= Lift_r s1) (n2:= Lift_r s2). 
          * exact H3. 
          * exact H20.
          * exact H21.
          * exact H30. 
          * exact H31. 
          * reflexivity.      
        + split.
          * simpl.
            reflexivity.
          * simpl.
            rewrite H22.  
            rewrite H32.
            reflexivity.
      }
    * exact H3.
Qed.

Lemma derives_g_cnf_equiv_btree_v3:
forall g: cfg non_terminal' terminal,
forall n: non_terminal',
forall s: sentence,
is_cnf g ->
derives g [inl n] (map term_lift' s) ->
exists t: btree non_terminal' terminal,
btree_cnf g t /\
broot t = n /\
bfrontier t = s /\
(exists ntl: list non_terminal', bnts t ntl). 
Proof.
intros g n s H1 H2.
rewrite derives_equiv_derives6 in H2.
destruct H2 as [n0 H2].
revert H2.
generalize dependent s.
generalize (le_refl n0).
generalize n0 at 1 3 as n0'.
generalize dependent n. 
induction n0.
- intros n n0' HH s H2.
  inversion HH.
  subst.
  inversion H2.
  subst.
  destruct s.
  + simpl in H.
    inversion H.
  + simpl in H.
    inversion H.
- intros n n0' HH s H2.
  assert (HHH: n0' = 0 \/ exists n0'': nat, n0' = S n0'').
    {
    apply nat_struct.
    }
  destruct HHH as [HHH | HHH].
  + subst.
    inversion H2. 
    destruct s.
    * simpl in H.
      inversion H.
    * simpl in H.
      inversion H.
  + destruct HHH as [n0'' HHH].
    subst.
    inversion H2.
    subst.
    assert (H1' := H1).
    assert (Hs1s2: s1 = [] /\ s2 = []).
      {
      destruct s1. 
      - inversion H0. 
        auto. 
      - inversion H0. 
        destruct s1. 
        + inversion H6. 
        + inversion H6. 
      }
    destruct Hs1s2 as [Hs1 Hs2].
    subst.
    inversion H0.
    subst.
    apply is_cnf_right_formats_v1 with (left:= n) (right:= right) in H1.
    * {
      destruct H1 as [H1 | H1].
      - destruct H1 as [t H1].
        subst.
        simpl in H4.
        assert (H5: exists n0'': nat, derives6 g n0'' [inr t] (map term_lift' s)).
          {
          exists n0''.
          exact H4.
          }
        rewrite <- derives_equiv_derives6 in H5.
        change [inr t] with (map term_lift' [t]) in H5.
        apply derives_sentence_left in H5.
        subst.
        exists (bnode_1 n t).
        split.
        + apply bt_c1 with (n:= n) (t:= t).
          * exact H3.
          * reflexivity.
        + split.
          * simpl. 
            reflexivity.
          * simpl. 
            apply terminal_lift_inj in H5.
            rewrite H5.
            {
            split.
            - reflexivity.
            - exists [n].
              apply bn_1 with (n:= n) (t:= t).
              + reflexivity.
              + simpl.
                left.
                reflexivity.
            }
      - destruct H1 as [s1 [s2 H1]].
        subst.
        simpl in H4.
        change [inl (Lift_r s1); inl (Lift_r s2)] with ([inl (Lift_r s1)] ++ [inl terminal (Lift_r s2)]) in H4.
        apply derives6_split in H4.
        destruct H4 as [s1' [s2' [n1 [n2 [H5 [H6 [H7 H8]]]]]]].
        assert (IHn0':= IHn0).
        assert (H40: n1 <= n0) by omega.
        symmetry in H5.
        apply map_expand in H5.
        destruct H5 as [s1'0 [s2'0 [H5 [H10 H11]]]].
        subst.
        specialize (IHn0 (Lift_r s1) n1 H40 s1'0 H7).
        assert (H50: n2 <= n0) by omega.
        specialize (IHn0' (Lift_r s2) n2 H50 s2'0 H8).
        destruct IHn0 as [t1 [H20 [H21 H22]]].
        destruct IHn0' as [t2 [H30 [H31 H32]]].
        exists (bnode_2 n t1 t2).
        split.
        + apply bt_c2 with (bt1:= t1) (bt2:= t2) (n:= n) (n1:= Lift_r s1) (n2:= Lift_r s2). 
          * exact H3. 
          * exact H20.
          * exact H21.
          * exact H30. 
          * exact H31. 
          * reflexivity.      
        + split.
          * simpl.
            reflexivity.
          * {
            split.
            - simpl.
              destruct H22 as [H22 _].
              destruct H32 as [H32 _].
              rewrite H22.  
              rewrite H32.
              reflexivity.
            - destruct H22 as [_ [ntl1 H22]].
              destruct H32 as [_ [ntl2 H32]].
              destruct (rules_finite g) as [x [ntl [tl [_ H]]]].
              specialize (H n [inl (Lift_r s1); inl (Lift_r s2)] H3).
              destruct H as [_ [H _]].
              exists (ntl ++ ntl1 ++ ntl2).
              apply bn_2 with (n:= n) (bt1:= t1) (bt2:= t2).
              + reflexivity.
              + apply in_or_app.
                left.
                exact H.
              + apply bnts_app.
                exact H22.
              + apply bnts_app_l.
                apply bnts_app_l.
                exact H32.
            }
      }
    * exact H3.
Qed.

Lemma derives_g_cnf_equiv_btree_v4:
forall g: cfg non_terminal' terminal,
forall n: non_terminal',
forall s: sentence,
s <> [] ->
(is_cnf g \/ is_cnf_with_empty_rule g) ->
start_symbol_not_in_rhs g ->
derives g [inl n] (map term_lift' s) ->
exists t: btree non_terminal' terminal,
btree_cnf g t /\
broot t = n /\
bfrontier t = s.
Proof.
intros g n s H1 H2 Hss H3.
rewrite derives_equiv_derives6 in H3.
destruct H3 as [n0 H3].
revert H1 H2 H3.
generalize dependent s.
generalize (le_refl n0).
generalize n0 at 1 3 as n0'.
generalize dependent n. 
induction n0.
- intros n n0' H1 s H2 H3 H4.
  inversion H1.
  subst.
  inversion H4.
  destruct s.
  + simpl in H.
    inversion H.
  + simpl in H.
    inversion H.
- intros n n0' H1 s H2 H3 H4.
  assert (HHH: n0' = 0 \/ exists n0'': nat, n0' = S n0'').
    {
    apply nat_struct.
    }
  destruct HHH as [HHH | HHH].
  + subst.
    inversion H4. 
    destruct s.
    * simpl in H.
      inversion H.
    * simpl in H.
      inversion H.
  + destruct HHH as [n0'' HHH].
    subst.
    inversion H4.
    subst.
    assert (Hs1s2: s1 = [] /\ s2 = []).
      {
      destruct s1. 
      - inversion H0. 
        auto. 
      - inversion H0. 
        destruct s1. 
        + inversion H8. 
        + inversion H8. 
      }
    destruct Hs1s2 as [Hs1 Hs2].
    subst.
    inversion H0.
    subst.
    clear H0.
    assert (H5':= H5).
    apply is_cnf_right_formats_v2 with (left:= n) (right:= right) in H5.
    * {
      destruct H5 as [H5 | H5].
      - destruct H5 as [t H5].
        subst.
        simpl in H6.
        assert (H7: exists n0'': nat, derives6 g n0'' [inr t] (map term_lift' s)).
          {
          exists n0''.
          exact H6.
          }
        rewrite <- derives_equiv_derives6 in H7.
        change [inr t] with (map term_lift' [t]) in H7.
        apply derives_sentence_left in H7.
        subst.
        exists (bnode_1 n t).
        split.
        + apply bt_c1 with (n:= n) (t:= t).
          * exact H5'.
          * reflexivity.
        + split.
          * simpl. 
            reflexivity.
          * simpl. 
            apply terminal_lift_inj in H7.
            symmetry.
            exact H7.
      - destruct H5 as [s1 [s2 H5]].
        subst.
        simpl in H6.
        change [inl (Lift_r s1); inl (Lift_r s2)] with ([inl (Lift_r s1)] ++ [inl terminal (Lift_r s2)]) in H6.
        apply derives6_split in H6.
        destruct H6 as [s1' [s2' [n1 [n2 [H6 [H7 [H8 H9]]]]]]].
        assert (IHn0':= IHn0).
        assert (H40: n1 <= n0) by omega.
        symmetry in H6.
        apply map_expand in H6.
        destruct H6 as [s1'0 [s2'0 [H6 [H10 H11]]]].
        subst.
        assert (HH: (Lift_r s1) <> start_symbol g /\
                    (Lift_r s2) <> start_symbol g).
          {
          specialize (Hss n [inl (Lift_r s1); inl (Lift_r s2)] H5').
          split. 
          - intros H.
            apply Hss.
            rewrite H.
            simpl.
            left.
            reflexivity.
          - intros H.
            apply Hss.
            rewrite <- H.
            simpl.
            right.
            left.
            reflexivity.
          }
        assert (Hs1'0: s1'0 <> []).
          {
          assert (exists n1: nat, derives6 g n1 [inl (Lift_r s1)] (map term_lift' s1'0)).
            {
            exists n1.
            exact H8.
            }
          apply <-derives_equiv_derives6 in H.
          apply cnf_derives_not_empty in H.
          - apply map_not_nil in H.
            exact H.
          - exact H3.
          - exact Hss. 
          - intros H10. 
            simpl in H10. 
            destruct H10 as [H10 | H10]. 
            + inversion H10. 
              destruct HH as [HH _].
              contradiction. 
            + contradiction.
          - apply not_eq_sym.
            apply nil_cons.
          }
        specialize (IHn0 (Lift_r s1) n1 H40 s1'0 Hs1'0 H3 H8).
        assert (H50: n2 <= n0) by omega.
        assert (Hs2'0: s2'0 <> []).
          {
          assert (exists n2: nat, derives6 g n2 [inl (Lift_r s2)] (map term_lift' s2'0)).
            {
            exists n2.
            exact H9.
            }
          apply <-derives_equiv_derives6 in H.
          apply cnf_derives_not_empty in H.
          - apply map_not_nil in H.
            exact H.
          - exact H3.
          - exact Hss. 
          - intros H10. 
            simpl in H10. 
            destruct H10 as [H10 | H10]. 
            + inversion H10. 
              destruct HH as [_ HH].
              contradiction. 
            + contradiction.
          - apply not_eq_sym.
            apply nil_cons.
          }
        specialize (IHn0' (Lift_r s2) n2 H50 s2'0 Hs2'0 H3 H9).
        destruct IHn0 as [t1 [H20 [H21 H22]]].
        destruct IHn0' as [t2 [H30 [H31 H32]]].
        exists (bnode_2 n t1 t2).
        split.
        + apply bt_c2 with (bt1:= t1) (bt2:= t2) (n:= n) (n1:= Lift_r s1) (n2:= Lift_r s2). 
          * exact H5'. 
          * exact H20.
          * exact H21.
          * exact H30. 
          * exact H31. 
          * reflexivity.      
        + split.
          * simpl.
            reflexivity.
          * simpl.
            rewrite H22.  
            rewrite H32.
            reflexivity.
      }
    * exact H3.
    * assert (Hn0: exists n0'': nat, derives6 g n0'' ([] ++ right ++ []) (map term_lift' s)).
        {
        exists n0''.
        exact H6.
        }
      rewrite <- derives_equiv_derives6 in Hn0.
      {
      apply derives_not_empty in Hn0.
      - simpl in Hn0. 
        rewrite app_nil_r in Hn0.
        exact Hn0.
      - apply map_not_nil_inv.
        exact H2.
      }
Qed.

Lemma decompose (t: btree non_terminal' terminal): list {x: btree non_terminal' terminal | bheight x < bheight t }.
Proof.
induction t.
- exact []. 
- apply cons.
  + exists t1.
    simpl. 
    auto with arith.
  + eapply map; [|exact IHt2]. (* ccc *)
    apply sig_weak. 
    intros. 
    simpl. 
    apply NPeano.Nat.lt_lt_succ_r. 
    auto.
    apply NPeano.Nat.max_lt_iff. 
    right. 
    apply H.
Qed.

Fixpoint convert_list_tree_to_tree_list (l: list (tree non_terminal' terminal)): 
tree_list non_terminal' terminal:=
match l with
| [] => tl_nil _ _
| t :: l => tl_cons t (convert_list_tree_to_tree_list l)
end.

Program Fixpoint convert_btree_to_tree (t: btree non_terminal' terminal) {measure (bheight t)}
: tree non_terminal' terminal:=
let tl:= map (fun x => convert_btree_to_tree (proj1_sig x)) (decompose t) in
           node (broot t) (convert_list_tree_to_tree_list tl).

Lemma btree_bpath_exists_btree_bpath:
forall g: cfg _ _,
forall bt1: btree _ _ ,
forall n: _,
forall p1 p2: list (_ + _),
btree_cnf g bt1 ->
bpath bt1 (p1 ++ [inl n] ++ p2) ->
exists bt2: btree _ _,
btree_cnf g bt2 /\
bpath bt2 ([inl n] ++ p2).
Proof.
intros g bt1 n p1.
revert n.
revert bt1.
induction p1.
- intros bt1 n p2 H1 H2.
  exists bt1.
  split.
  + exact H1.
  + exact H2.
- intros bt1 n p2 H1 H2.
  inversion H2.
  + destruct p1. 
    * inversion H3.
    * {
      inversion H3.
      destruct p1.
      - inversion H6.
      - inversion H6.
      }
  + rewrite H3 in H1.
    inversion H1.
    * discriminate.
    * inversion H10.
      subst.
      specialize (IHp1 bt3 n p2 H6 H4).
      exact IHp1.
  + rewrite H3 in H1.
    inversion H1.
    * discriminate.
    * inversion H10.
      subst.
      specialize (IHp1 bt4 n p2 H8 H4).
      exact IHp1.
Qed.

Lemma btree_bpath_exists_derives:
forall g: cfg _ _,
forall t: btree _ _,
forall n1 n2: _,
forall p1 p2: list (_ + _),
btree_cnf g t ->
bpath t ([inl n1] ++ p1 ++ [inl n2] ++ p2) ->
exists l r: list (_ + _),
derives g [inl n1] (l ++ [inl n2] ++ r) /\ (l ++ r <> []).
Proof.
intros g t n1 n2 p1.
revert n2.
revert n1.
revert t.
induction p1.
- intros t n1 n2 p2 H1 H2.
  simpl in H2.
  inversion H2.
  + subst.
    inversion H1.
    * discriminate.
    * inversion H7.
      subst.
      apply bpath_broot with (d:= inl (broot bt0)) in H4.
      simpl in H4.
      inversion H4.
      exists [], [inl (broot bt3)].
      simpl.
      {
      split.
      - apply derives_start.
        exact H.
      - apply not_eq_sym. 
        apply nil_cons.
      }
  + subst.
    inversion H1.
    * discriminate.
    * inversion H7.
      subst.
      apply bpath_broot with (d:= inl (broot bt3)) in H4.
      simpl in H4.
      inversion H4.
      exists [inl (broot bt0)], [].
      simpl.
      {
      split.
      - apply derives_start.
        exact H.
      - apply not_eq_sym. 
        apply nil_cons.
      }
- intros t n1 n2 p2 H1 H2.
  destruct a.
  + change (inl n :: p1) with ([inl n] ++ p1) in H2.
    rewrite <- app_assoc in H2.
    assert (H2':= H2).
    apply btree_bpath_exists_btree_bpath with (g:= g) in H2.
    * destruct H2 as [bt2 [H2 H3]]. 
      specialize (IHp1 bt2 n n2 p2 H2 H3).
      destruct IHp1 as [l [r IHp1]].
      {
      inversion H2'.
      - rewrite H4 in H1.
        inversion H1.
        + discriminate.
        + inversion H11.
          subst.
          apply bpath_broot with (d:= inl (broot bt3)) in H5.
          simpl in H5.
          inversion H5.
          subst.
          exists l.
          exists (r ++ [inl (broot bt4)]).
          {
          split.
          * apply derives_trans with (s2:= [inl (broot bt3); inl (broot bt4)]).
            - apply derives_start.
              exact H6.
            - change [inl (broot bt3); inl (broot bt4)] with ([inl (broot bt3)] ++ [inl terminal (broot bt4)]).
              rewrite app_assoc.
              rewrite app_assoc.
              apply derives_combine.
              split.
              + rewrite <- app_assoc.
                apply IHp1.
              + apply derives_refl.
          * apply app_not_nil_inv.
            right.
            apply app_not_nil_inv.
            right.
            apply not_eq_sym.
            apply nil_cons.
          }  
      - rewrite H4 in H1.
        inversion H1.
        + discriminate.
        + inversion H11.
          subst.
          apply bpath_broot with (d:= inl (broot bt4)) in H5.
          simpl in H5.
          inversion H5.
          subst.
          exists ([inl (broot bt3)] ++ l).
          exists r.
          split.
          * {
            apply derives_trans with (s2:= [inl (broot bt3); inl (broot bt4)]).
            - apply derives_start.
              exact H6.
            - change [inl (broot bt3); inl (broot bt4)] with ([inl (broot bt3)] ++ [inl terminal (broot bt4)]).
              rewrite <- app_assoc.
              apply derives_combine.
              split.
              + apply derives_refl.
              + apply IHp1.
            }
          * apply app_not_nil_inv.
            left. 
            apply app_not_nil_inv.
            left. 
            apply not_eq_sym.
            apply nil_cons.
      }
    * exact H1.
  + inversion H2.
    * {
      destruct p1.
      - inversion H4.
      - inversion H4.
      } 
    * apply bpath_broot with (d:= inl (broot bt1)) in H4.
      simpl in H4.
      inversion H4. 
    * apply bpath_broot with (d:= inl (broot bt1)) in H4.
      simpl in H4.
      inversion H4. 
Qed.

Lemma start_symbol_only_once:
forall g: cfg _ _,
forall t: btree _ _,
forall n: _,
forall p1 p2 p3: list (_ + _),
start_symbol_not_in_rhs g ->
btree_cnf g t ->
bpath t (p1 ++ [inl n] ++ p2 ++ [inl n] ++ p3) ->
start_symbol g <> n.
Proof.
intros g t n p1 p2 p3 H1 H2 H3.
apply btree_bpath_exists_btree_bpath with (g:= g) in H3.
- clear H2. 
  destruct H3 as [t' [H3 H4]].
  apply btree_bpath_exists_derives with (g:= g) in H4.
  + destruct H4 as [l [r [H4 H5]]]. 
    apply exists_rule' in H4.
    destruct H4 as [H4 | H4].
    * destruct H4 as [H4 [H6 H7]].
      subst. 
      simpl in H5.
      destruct H5.
      reflexivity.
    * destruct H4 as [left [right [H4 H6]]].
      specialize (H1 left right H4).
      intros H7.
      subst.
      contradiction.
  + exact H3.
- exact H2.
Qed.

Lemma cnf_bnts:
forall g: cfg _ _,
forall n: nat,
forall ntl: list _,
forall tl: list _,
forall t: btree _ _,
rules_finite_def (start_symbol g) (rules g) n ntl tl ->
btree_cnf g t ->
bnts t ntl.
Proof.
intros g n ntl tl t H1 H2.
destruct H1 as [H3 H4].
induction H2.
- rewrite H0.
  apply bn_1 with (n:= n0) (t:= t).
  + reflexivity.
  + specialize (H4 n0 [inr t] H).
    destruct H4 as [_ [H4 _]].
    exact H4.
- rewrite H2.
  apply bn_2 with (n:= n0) (bt1:= bt1) (bt2:= bt2).
  + reflexivity.
  + specialize (H4 n0 [inl n1; inl n2] H).
    destruct H4 as [_ [H4 _]].
    exact H4.
  + exact IHbtree_cnf1.
  + exact IHbtree_cnf2.
Qed.

Lemma btree_equiv_derives_g_cnf:
forall g: cfg _ _,
forall t: btree _ _,
btree_cnf g t ->
derives g [inl (broot t)] (map inr (bfrontier t)).
Proof.
intros g.
induction t.
- intros H1.
  inversion H1.
  + inversion H0.
    clear H0.
    subst.
    simpl.
    apply derives_start.
    exact H.
  + discriminate.
- intros H.
  simpl.
  rewrite map_app.
  inversion H.
  + discriminate.
  + inversion H5.
    subst.
    apply derives_trans with (s2:= [inl (broot bt1); inl (broot bt2)]).
    * apply derives_start.
      exact H0.
    * change ([inl (broot bt1); inl (broot bt2)]) with ([inl (broot bt1)] ++ [inl terminal (broot bt2)]).
      apply derives_combine.
      {
      split.
      - apply IHt1.
        exact H1.
      - apply IHt2.
        exact H3.
      }
Qed.

Lemma btree_equiv_produces_g_cnf:
forall g: cfg _ _,
forall t: btree _ _,
broot t = start_symbol g ->
btree_cnf g t ->
produces g (bfrontier t).
Proof.
intros g t H1 H2.
unfold produces, generates.
apply btree_equiv_derives_g_cnf in H2.
rewrite <- H1.
exact H2.
Qed.

Lemma btree_cnf_subtree:
forall g: cfg _ _,
forall t1 t2: btree _ _,
btree_cnf g t1 ->
subtree t1 t2 ->
btree_cnf g t2.
Proof.
intros g t1 t2 H1.
revert t2.
induction H1.
- intros t2 H2.
  rewrite H0 in H2.
  inversion H2.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
- intros t2 H3.
  subst.
  inversion H3.
  + inversion H0.
    clear H0.
    subst.
    exact H1_0.
  + inversion H0.
    clear H0.
    subst.
    exact H1_.
  + inversion H1.
    clear H1.
    subst.
    specialize (IHbtree_cnf2 t2 H0).
    exact IHbtree_cnf2.
  + inversion H1.
    clear H1.
    subst.
    specialize (IHbtree_cnf1 t2 H0).
    exact IHbtree_cnf1.
Qed.

Lemma btree_subst_preserves_cnf:
forall g: cfg _ _,
forall t1 t2 t': btree non_terminal' terminal,
forall c1 c1': list bool,
btree_cnf g t1 ->
bcode t1 (c1 ++ c1') ->
btree_cnf g t2 ->
get_nt_btree c1 t1 = Some (broot t2) ->
btree_subst t1 t2 c1 = Some t' ->
btree_cnf g t'.
Proof.
intros g t1 t2 t' c1.
revert t1 t2 t'.
induction c1.
- intros t1 t2 t' c1' H1 H2 H3 H4 H6.
  rewrite btree_subst_empty in H6.
  inversion H6.
  subst.
  exact H3.
- intros t1 t2 t' c1' H1 H2 H3 H4 H6.
  destruct t1.
  + simpl in H4.
    destruct a.
    * discriminate.
    * discriminate.
  + destruct c1.
    * {
      destruct a.
      - simpl in H6.
        rewrite btree_subst_empty in H6.
        inversion H6.
        inversion H1.
        + discriminate. 
        + inversion H10. 
          subst. 
          apply bt_c2 with (bt1:= bt1) (bt2:= t2) (n1:= broot bt1) (n2:= broot t2) (n:= n0).
          * assert (broot bt2 = broot t2). 
              {
              simpl in H4. 
              destruct bt2. 
              - inversion H4. 
                simpl.
                reflexivity.
              - inversion H4.
                simpl.
                reflexivity. 
              }
            rewrite <- H0. 
            exact H. 
          * exact H5.
          * reflexivity.
          * exact H3. 
          * reflexivity.
          * reflexivity.
      - simpl in H6.
        rewrite btree_subst_empty in H6.
        inversion H6.
        inversion H1.
        + discriminate. 
        + inversion H10. 
          subst. 
          apply bt_c2 with (bt1:= t2) (bt2:= bt2) (n1:= broot t2) (n2:= broot bt2) (n:= n0).
          * assert (broot bt1 = broot t2). 
              {
              simpl in H4. 
              destruct bt1. 
              - inversion H4. 
                simpl.
                reflexivity.
              - inversion H4.
                simpl.
                reflexivity. 
              }
            rewrite <- H0. 
            exact H.
          * exact H3.
          * reflexivity.
          * exact H8. 
          * reflexivity.
          * reflexivity.
      }
    * {
      inversion H1.
      - discriminate.
      - clear H1. 
        inversion H9.
        clear H9.
        subst.
        destruct a.
        + assert (H10: bcode bt2 (b :: c1 ++ c1')).
            {
            inversion H2.
            inversion H5.
            exact H8.
            } 
          assert (H11: exists t'': btree _ _, btree_subst bt2 t2 (b :: c1) = Some t'').
            {
            apply bcode_btree_subst with (c2:= c1').
            exact H10.
            }
          destruct H11 as [t'' H11].
          assert (H12: get_nt_btree (b :: c1) bt2 = Some (broot t2)).
            {
            simpl in H4.
            destruct b.
            - destruct bt2.
              + discriminate. 
              + simpl. 
                exact H4.
            - destruct bt2. 
              + discriminate.
              + simpl. 
                exact H4.
            } 
          specialize (IHc1 bt2 t2 t'' c1' H7 H10 H3 H12 H11).
          assert (broot t'' = broot bt2).
            {
            apply btree_subst_preserves_broot_v2 in H11.
            - exact H11.
            - apply not_eq_sym. 
              apply nil_cons.
            }
          rewrite <- H1 in H.
          simpl in H6.
          rewrite H11 in H6.
          inversion H6.
          apply bt_c2 with (bt1:= bt1) (bt2:= t'') (n1:= broot bt1) (n2:= broot t'') (n:= n0).
          * exact H.
          * exact H0.
          * reflexivity.
          * exact IHc1.
          * reflexivity.
          * reflexivity.
        + assert (H10: bcode bt1 (b :: c1 ++ c1')).
            {
            inversion H2.
            inversion H5.
            exact H8.
            } 
          assert (H11: exists t'': btree _ _, btree_subst bt1 t2 (b :: c1) = Some t'').
            {
            apply bcode_btree_subst with (c2:= c1').
            exact H10.
            }
          destruct H11 as [t'' H11].
          assert (H12: get_nt_btree (b :: c1) bt1 = Some (broot t2)).
            {
            simpl in H4.
            destruct b.
            - destruct bt1.
              + discriminate. 
              + simpl. 
                exact H4.
            - destruct bt1. 
              + discriminate.
              + simpl. 
                exact H4.
            } 
          specialize (IHc1 bt1 t2 t'' c1' H0 H10 H3 H12 H11).
          assert (broot t'' = broot bt1).
            {
            apply btree_subst_preserves_broot_v2 in H11.
            - exact H11.
            - apply not_eq_sym. 
              apply nil_cons.
            }
          rewrite <- H1 in H.
          simpl in H6.
          rewrite H11 in H6.
          inversion H6.
          apply bt_c2 with (bt1:= t'') (bt2:= bt2) (n1:= broot t'') (n2:= broot bt2) (n:= n0).
          * exact H.
          * exact IHc1.
          * reflexivity.
          * exact H7.
          * reflexivity.
          * reflexivity.
      }
Qed.

End Binary_Chomsky.

(* --------------------------------------------------------------------- *)
(* SYNTAX TREES                                                          *)
(* --------------------------------------------------------------------- *)

Section Syntax_Trees.

Variables non_terminal terminal: Type.

Notation symbol:= (non_terminal + terminal)%type.
Notation sf:= (list symbol).
Notation term_lift:= ((terminal_lift non_terminal) terminal).

Inductive syntax_tree (g: cfg non_terminal terminal): tree non_terminal terminal -> Prop:=
| tg_t:    
        forall t: terminal,
        syntax_tree g (node_t _ t)
| tg_n:    
        forall n: non_terminal,
        syntax_tree g (node_n _ n)
| tg_node: 
        forall trl: tree_list _ _,
        forall n: non_terminal, 
        forall right: sf,
        rules g n right ->
        syntax_tree_list g right trl ->
        syntax_tree g (node n trl)
with syntax_tree_list (g: cfg non_terminal terminal): sf -> tree_list non_terminal terminal -> Prop:=
| tlg_nil:  
        syntax_tree_list g [] (tl_nil _ _)
| tlg_cons: 
        forall x: non_terminal + terminal,
        forall xs: sf,
        forall tx: tree _ _,
        forall txs: tree_list _ _,
        x = root tx ->
        syntax_tree g tx ->
        syntax_tree_list g xs txs ->
        syntax_tree_list g (x::xs) (tl_cons tx txs).

Lemma sf_tree_list:
forall g: cfg non_terminal terminal,
forall s: sf,
exists tl: tree_list _ _,
syntax_tree_list g s tl /\ frontier_list tl = s.
Proof.
intros g s.
induction s.
- exists (tl_nil _ _).
  split.
  + apply tlg_nil.
  + simpl.
    reflexivity.
- destruct IHs as [tl [H1 H2]].
  destruct a.
  + exists (tl_cons (node_n _ n) tl).
    split.
    * {
      apply tlg_cons.
      - simpl.
        reflexivity.
      - apply tg_n.
      - exact H1.
      }
    * simpl.
(* 
      rewrite H2.
      reflexivity.
*)
      admit.
  + exists (tl_cons (node_t _ t) tl).
    split.
    * {
      apply tlg_cons.
      - simpl.
        reflexivity.
      - apply tg_t.
      - exact H1.
      }
    * admit.
(*
      simpl. 
      rewrite H2.
      reflexivity.
*)
Qed.

Lemma rule_tree:
forall g: cfg non_terminal terminal,
forall left: non_terminal,
forall right: sf,
rules g left right ->
exists t: tree _ _,
syntax_tree g t /\
root t = (inl left) /\
frontier t = right.
Proof.
intros g left right H.
pose (el:= sf_tree_list g right).
destruct el as [tl el].
exists (node left tl).
split.
- apply tg_node with (right:= right).
  + exact H.
  + apply el.
- split.
  + simpl.
    reflexivity.
  + simpl.
    apply el.
Qed.

Lemma tree_composition:
forall g: cfg non_terminal terminal,
forall t1: tree _ _,
syntax_tree g t1 ->
forall r2: non_terminal,
forall s s' s'': sf,
frontier t1 = s ++ (inl r2) :: s'' ->
rules g r2 s' ->
exists t2: tree _ _,
syntax_tree g t2 /\
root t2 = root t1 /\
frontier t2 = s ++ s' ++ s''.
Proof.
intros g t1.
induction t1 using tree_ind2 with 
  (P:=  fun t: tree _ _ => syntax_tree g t ->
                           forall (r2 : non_terminal) (s s' s'' : sf),
                           frontier t = s ++ inl r2 :: s'' ->
                           rules g r2 s' ->
                           exists t2 : tree _ _,
                           syntax_tree g t2 /\ root t2 = root t /\ frontier t2 = s ++ s' ++ s'')
  (P0:= fun tl: tree_list _ _ => forall r: sf,
                                 syntax_tree_list g r tl ->
                                 forall (r2 : non_terminal) (s s' s'' : sf),
                                 frontier_list tl = s ++ inl r2 :: s'' ->
                                 rules g r2 s' ->
                                 exists tl2 : tree_list _ _,
                                 syntax_tree_list g r tl2 /\ frontier_list tl2 = s ++ s' ++ s'').
- intros H1 r2 s s' s'' H2 H3.
  simpl in H2.
  destruct s.
  + inversion H2.
  + inversion H2.
    destruct s0.
    * inversion H4.
    * inversion H4.
- intros H1 r2 s s' s'' H2 H3.
  simpl in H2.
  destruct s.
  + inversion H2.
    subst.
    clear H2.
    apply rule_tree in H3.
    simpl. 
    rewrite app_nil_r. 
    exact H3.
  + inversion H2.
    destruct s0.
    * inversion H4.
    * inversion H4.
- intros H1 r2 s s' s'' H2 H3.
  simpl.
  simpl in H2.
  inversion H1.
  subst.
  specialize (IHt1 right H5 r2 s s' s'' H2 H3).
  destruct IHt1 as [tl2 [H6 H7]].
  exists (node n tl2).
  split.
  +  apply tg_node with (right:= right).
     * exact H4.
     * exact H6.
  + split.
    * simpl.
      reflexivity.
    * simpl.
      exact H7.
- intros r H1 r2 s s' s'' H2 H3.
  simpl in H2. 
  destruct s.
  + inversion H2.
  + inversion H2.
- intros r H1 r2 s s' s'' H2 H3.
  admit. (* ttt *)
Qed.

Lemma derives_exists_tree_v1:
forall g: cfg non_terminal terminal,
forall n: non_terminal,
forall s: sf,
derives g [inl n] s ->
exists t: tree _ _,
syntax_tree g t /\
root t = (inl n) /\
frontier t = s.
Proof.
intros g n s H.
remember [inl n] as w.
revert Heqw.
revert n.
induction H.
- intros n H.
  subst.
  exists (node_n _ n).
  split.
  + apply tg_n.
  + split.
    * simpl.
      reflexivity.
    * simpl.
      reflexivity.
- intros n H1.
  specialize (IHderives n H1).
  clear H1.
  destruct IHderives as [t [H1 [H2 H3]]].
  assert (H0':= H0).
  apply rule_tree in H0.
  destruct H0 as [t' [H4 [H5 H6]]].
  apply tree_composition with (r2:= left) (s:= s2) (s':= right) (s'':= s3) in H1.
  + destruct H1 as [t2 [H7 [H8 H9]]].
    exists t2.
    split.
    * exact H7.
    * {
      split.
      - congruence.
      - exact H9.
      }
  + exact H3.
  + exact H0'.
Qed.

Lemma derives_exists_tree_v2:
forall g: cfg non_terminal terminal,
forall n: non_terminal,
forall s: sf,
derives g [inl n] s ->
exists t: tree _ _,
syntax_tree g t /\
root t = (inl n) /\
frontier t = s.
Proof.
intros g n s H.
apply derives_equiv_derives6 in H.
destruct H as [n0 H].
generalize dependent H.
generalize dependent s.
generalize dependent n.
generalize (le_refl n0).
generalize n0 at 1 3.
induction n0.
- intros n0 H1 s H2 H3.
  inversion H1.
  subst. 
  inversion H3.
  subst.
  exists (node_n _ s).
  split.
  + apply tg_n.
  + split.
    * simpl.
      reflexivity.
    * simpl.
      reflexivity.
- intros n1 H1 n s H2.
  assert (HHH: n1 = 0 \/ exists n1': nat, n1 = S n1').
    {
    apply nat_struct.
    }
  destruct HHH as [HHH | HHH].
  + subst.
    inversion H2.
    subst.
    exists (node_n _ n).
    split.
    * apply tg_n.
    * {
      split.
      - simpl. 
        reflexivity.
      - simpl.
        reflexivity.
      }
  + destruct HHH as [n1' HHH].
    subst.
    inversion H2.
    assert (H6: s1 = [] /\ s2 = []).
      {
      destruct s1.
      inversion H0.
      - auto.
      - inversion H0.
        destruct s1.
        + inversion H8.
        + inversion H8.
      }
    destruct H6 as [H6 H7].
    subst.
    inversion H0.
    subst.
    clear H0 H2.
    apply Peano.le_S_n in H1.
    simpl in H4.
    rewrite app_nil_r in H4.
    assert (H5: forall e: symbol,
                In e right ->
                exists s2' s2'' s3: sf, 
                exists n': nat,
                derives6 g n' [e] s3 /\
                s = s2' ++ s3 ++ s2'' /\
                n' <= n1').
      {
      apply derives6_split_all.
      exact H4.
      }
    assert (H6: forall e: symbol,
                forall s4: sf,
                forall m: nat,
                In e right ->
                m <= n1' ->
                derives6 g m [e] s4 ->
                exists t: tree _ _,
                syntax_tree g t /\ root t = e /\ frontier t = s4).
      {
      intros e s4 m HH0 HH1 HH2.
      specialize (H5 e HH0).
      destruct H5 as [s2' [s2'' [s3 [n' [H11 [H12 H13]]]]]].
      assert (H14: m <= n0) by omega.
      specialize (IHn0 m H14).
      destruct e.
      - specialize (IHn0 n1 s4 HH2).
        exact IHn0.
      - exists (node_t _ t).
        split.
        + apply tg_t.
        + split.
          * simpl. 
            reflexivity.
          * simpl.
            assert (HH3: exists m, derives6 g m [inr t] s4). 
              {
              exists m. 
              exact HH2. 
              } 
            rewrite <- derives_equiv_derives6 in HH3.
            change [inr t] with (map term_lift [t]) in HH3.  
            apply derives_sentence_left in HH3.
            simpl in HH3.
            symmetry.
            exact HH3. 
      }
    assert (H7: exists tl: tree_list _ _,
                syntax_tree_list g right tl /\ frontier_list tl = s).
      {
      induction right. 
      - exists (tl_nil _ _).
        simpl.
        split.
        + apply tlg_nil.
        + assert (H7: exists n1': nat, derives6 g n1' [] s).
            {
            exists n1'.
            exact H4.
            }
          rewrite <- derives_equiv_derives6 in H7.
          apply derives_empty in H7.
          subst.
          reflexivity.
      - change (a :: right) with ([a] ++ right) in H4.
        apply derives6_split in H4.
        destruct H4 as [s1' [s2' [n1 [n2 [H7 [H8 [H9 H10]]]]]]].
        assert (H11: n1 <= n1') by omega.
        specialize (H6 a s1' n1).
        assert (H12: In a (a :: right)).
          {
          simpl.
          left.
          reflexivity.
          }
        specialize (H6 H12 H11 H9).
        destruct H6 as [t [H13 [H14 H15]]].
        subst.
        admit. (* exists (tl_cons t ...) *) (* ttt *)
      }
    destruct H7 as [tl H7].
    exists (node n tl).
    split.
    * {
      apply tg_node with (right:= right).
      - exact H3.
      - apply H7.
      }
    * {
      split.
      - simpl. 
        reflexivity.
      - simpl. 
        apply H7.
      }
Qed.

Lemma exists_tree_derives_v1:
forall g: cfg non_terminal terminal,
forall t: tree _ _,
syntax_tree g t ->
derives g [root t] (frontier t).
Proof.
intros g t.
induction t using tree_ind2 with 
  (P:=  fun t: tree _ _ => syntax_tree g t -> derives g [root t] (frontier t))
  (P0:= fun tl: tree_list _ _ => forall s: sf, syntax_tree_list g s tl -> derives g s (frontier_list tl)).
- intros H. 
  simpl.
  apply derives_refl.
- intros H. 
  simpl.
  apply derives_refl.
- intros H. 
  simpl.
  inversion H.
  subst.
  apply derives_trans with (s2:= right).
  + apply derives_start.
    exact H2.
  + apply IHt. 
    exact H3.
- intros s H.
  simpl.
  inversion H. 
  apply derives_refl.
- intros s H.
  simpl in H.
  inversion H.
  subst.
  simpl.
  change (root t :: xs) with ([root t] ++ xs).
  apply derives_combine.
  split.
  + apply IHt.
    exact H4.
  + apply IHt0.
    exact H5.
Qed.

Lemma exists_tree_derives_v2:
forall g: cfg non_terminal terminal,
forall t: tree _ _,
syntax_tree g t ->
derives g [root t] (frontier t).
Proof.
intros g t H.
induction H.
- simpl.
  apply derives_refl.
- simpl.
  apply derives_refl.
- simpl.
  apply derives_trans with (s2:= right).
  + apply derives_start.
    exact H.
  + clear H.
    revert H0.
    revert trl.
    induction right.
    * intros trl H. 
      inversion H. 
      simpl.
      apply derives_refl.
    * intros trl H. 
      inversion H.
      simpl.
      subst.
      change (root tx :: right) with ([root tx] ++ right).
      apply derives_combine.
      {
      split.
      - admit. (* ttt *)
      - apply IHright.
        exact H5.
      }
Qed.

Lemma derives_tree:
forall g: cfg non_terminal terminal,
forall n: non_terminal,
forall s: sf,
derives g [inl n] s <->
exists t: tree _ _,
syntax_tree g t /\
root t = (inl n) /\
frontier t = s.
Proof.
intros g n s.
split.
- apply derives_exists_tree_v1.
- intros H. 
  destruct H as [t [H [H1 H2]]].
  apply exists_tree_derives_v1 in H.
  subst.
  rewrite H1 in H.
  exact H.
Qed.

End Syntax_Trees.
