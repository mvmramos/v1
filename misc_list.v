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
   
(* --------------------------------------------------------------------- *)
(* LIST LEMMAS                                                           *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Omega.

Require Import misc_arith.

Import ListNotations.

Open Scope list_scope.

Lemma map_expand:
forall (A B: Type) (f: A -> B) (l: list A) (s1 s2: list B), 
s1 ++ s2 = map f l ->
exists s1' s2': list A,
l = s1' ++ s2' /\ map f s1' = s1 /\ map f s2' = s2.
Proof.
intros A B f l.
induction l.
- intros s1 s2 H.
  simpl in H.
  apply app_eq_nil in H.
  destruct H as [H1 H2].
  subst.
  exists [], [].
  auto.
- intros s1 s2 H.
  simpl in H.
  destruct s1.
  + simpl in H.
    destruct s2.
    * inversion H.
    * inversion H.
      exists [], (a::l). {
      split.
      - simpl.
        reflexivity.
      - split.
        + simpl.
          reflexivity.
        + simpl. 
          reflexivity. }
  + destruct s2.
    * inversion H.
      exists (a::l), []. {
      split.
      - simpl.
        rewrite app_nil_r.
        reflexivity.
      - split.
        + simpl.
          rewrite <- H2.
          rewrite app_nil_r.
          reflexivity.
        + simpl. 
          reflexivity. }
    * inversion H.
      specialize (IHl s1 (b0::s2)).
      specialize (IHl H2).
      destruct IHl as [s1' [s2' [H3 [H4 H5]]]].
      exists (a::s1').
      exists s2'. {
      split.
      - rewrite H3.
        simpl.
        reflexivity.
      - split.
        + simpl.
          rewrite H4.
          reflexivity.
        + rewrite H5.
          reflexivity. }
Qed.

Lemma equal_app (A: Type) :
forall l1 l2 s1 s2 : list A,
l1 ++ l2 = s1 ++ s2 ->
(exists l, s1 = l1 ++ l /\ l2 = l ++ s2) \/ (exists l, l1 = s1 ++ l /\ s2 = l ++ l2).
Proof.
intros l1.
induction l1 as [|a l1 IH].
- intros l2 s1 s2 H.
  simpl in H. 
  subst. 
  simpl. 
  left.
  exists s1.
  split.
  reflexivity.
  reflexivity. 
- intros l2 s1 s2 H. 
  simpl in H.
  destruct s1 as [|a' s1].
  + simpl in H. 
    subst. 
    simpl. 
    right.
    exists (a::l1).
    split.
    * reflexivity.
    * simpl.
      reflexivity.
  + simpl in H. 
    inversion H. 
    subst a'. 
    clear H.
    apply IH in H2.
    destruct H2 as [(l & ? & ?) | (l & ? & ?)]. 
    * subst. 
      simpl.
      left.
      exists l. {
      split.
      - reflexivity.
      - reflexivity. }
    * right.
      exists l. {
      split.
      - rewrite H.
        simpl.
        reflexivity.
      - rewrite H0.
        reflexivity. }
Qed.

Lemma last_last:
forall A: Type,
forall s d: A,
forall l: list A,
last (l++[s]) d = s.
Proof.
intros A s d l.
induction l.
- simpl. 
  reflexivity.
- simpl. 
  destruct l.
  + simpl. 
    reflexivity.
  + rewrite <- app_comm_cons.
    exact IHl.
Qed.

Lemma length_ge_0:
forall A: Type,
forall l: list A,
length l >= 0.
Proof.
intros A l.
destruct l.
- simpl.
  omega.
- simpl.
  omega.
Qed.

Lemma length_ge_2:
forall A: Type,
forall a1 a2: A,
forall l: list A,
length (a1::a2::l) >= 2.
Proof.
intros A a1 a2 l.
simpl.
apply Le.le_n_S.
apply Le.le_n_S.
apply Le.le_0_n.
Qed.

Lemma length_lt_1:
forall A: Type,
forall l: list A,
length l < 1 -> l = [].
Proof.
intros A l H.
destruct l.
- reflexivity.
- replace (a::l) with ([a]++l) in H.
  + rewrite app_length in H.
    simpl in H.
    apply lt_S_n in H.
    apply lt_n_O in H.
    contradiction.
  + simpl.
    reflexivity.
Qed.

Lemma nth_cons:
forall A: Type,
forall a e: A,
forall l: list A,
forall i: nat,
nth (S i) (a::l) e = nth i l e.
Proof.
intros A a e l i.
simpl. 
destruct i.
- simpl.
  reflexivity.
- reflexivity.
Qed. 

Lemma length_not_zero:
forall A: Type,
forall l: list A,
length l > 0 -> [] <> l.
Proof.
intros A l H.
destruct l.
- simpl in H.
  apply gt_irrefl in H.
  contradiction.
- apply nil_cons.
Qed.

Lemma length_not_zero_inv:
forall A: Type,
forall l: list A,
l <> [] -> length l > 0.
Proof.
intros A l H.
destruct l.
- destruct H.
  reflexivity.
- simpl. 
  omega. 
Qed.

Lemma not_nil:
forall A: Type,
forall l: list A,
l <> [] -> length l <> 0.
Proof.
destruct l.
- intro H.
  auto.
- intro H.
  replace (a::l) with ([a]++l). 
  + rewrite app_length.
    simpl.
    apply not_eq_sym.
    apply O_S.
  + simpl.
    reflexivity.
Qed.

Lemma not_nil_ge_1:
forall A: Type,
forall l: list A,
l <> [] -> length l >= 1.
Proof.
intros A l H.
apply not_nil in H. 
destruct l.
- simpl in H. 
  destruct H.
  reflexivity.
- simpl.
  apply le_n_S.
  apply le_0_n.
Qed.

Lemma list_last:
forall A: Type,
forall d: A,
forall l: list A,
removelast l <> [] -> nth (length (removelast l) - 1) (removelast l ++ [last l d]) d = last (removelast l) d.
Proof.
intros A d l H.
rewrite app_nth1 with (l:=removelast l).
- rewrite app_removelast_last with (l:=removelast l)(d:=d).
  + rewrite app_nth2.
    * rewrite app_length.
      assert (H1: Datatypes.length (removelast (removelast l)) + 1 - 1 -
                  Datatypes.length (removelast (removelast l)) = 0).
        {
        omega.
        }
      simpl. 
      rewrite H1.
      rewrite last_last.
      reflexivity.
    * rewrite app_length.
      simpl. 
      omega.
  + exact H.
- apply n_minus_1.
  apply not_nil.
  exact H.
Qed.

Lemma length_zero:
forall A: Type,
forall l: list A,
length l = 0 -> l = [].
Proof.
intros A l H.
destruct l.
- reflexivity.
- simpl in H.
  symmetry in H.
  apply O_S in H.
  contradiction.
Qed.

Lemma list_single:
forall A: Type,
forall l: list A,
forall d e: A,
nth 0 l d = e -> length l = 1 -> l = [e].
Proof.
intros A l d e H1 H2.
destruct l.
- simpl in H2.
  apply O_S in H2.
  contradiction.
- simpl in H1.
  rewrite H1.
  simpl in H2.
  inversion H2.
  apply length_zero in H0.
  rewrite H0.
  reflexivity.
Qed.

Lemma hd_nth0:
forall A: Type,
forall d: A,
forall l: list A,
hd d l = nth 0 l d.
Proof.
intros A d l.
destruct l.
- simpl.
  reflexivity.
- simpl.
  reflexivity.
Qed.

Lemma last_nth1:
forall A: Type,
forall d: A,
forall l: list A,
length l = 2 -> last l d = nth 1 l d.
Proof.
intros A d l H.
destruct l.
- simpl. 
  reflexivity.
- simpl. 
  destruct l.
  + simpl in H.
    inversion H.
  + replace (a :: a0 :: l) with ([a] ++ [a0] ++ l) in H.
    * repeat rewrite app_length in H.
      simpl in H.
      inversion H.
      apply length_zero in H1.
      subst.
      simpl.
      reflexivity. 
    * simpl.
      reflexivity.
Qed.

Lemma hd_tl_nth1:
forall A: Type,
forall d: A,
forall l: list A,
length l > 2 -> hd d (tl l) = nth 1 l d.
Proof.
intros A d l H.
destruct l.
- simpl. 
  reflexivity.
- simpl. 
  apply hd_nth0.
Qed.

Lemma last_tl_last:
forall A: Type,
forall d: A,
forall l: list A,
length l > 2 -> last (tl l) d = last l d.
Proof.
intros A d l H.
destruct l.
- simpl.
  reflexivity.
- simpl.
  destruct l.
  + simpl in H.
    apply gt_S_n in H.
    apply lt_n_0 in H.
    contradiction.
  + reflexivity.
Qed.

Lemma nth_S:
forall A: Type,
forall i: nat,
forall s s0 s1: A,
forall l: list A, 
nth (S i) (s::s0::s1::l) = nth i (s0::s1::l).
Proof.
intros A i s s0 s1 l.
destruct i.
- simpl. 
  reflexivity.
- destruct i.
  + simpl. 
    reflexivity.
  + destruct i.
    * simpl. 
      reflexivity.
    * simpl. 
      reflexivity.
Qed.

Lemma skipn_S:
forall i: nat,
forall A: Type,
forall a: A,
forall l: list A,
skipn (S i) (a :: l) = skipn i l.
Proof.
intros i A a l.
destruct i.
- simpl. 
  reflexivity.
- simpl.
  destruct l.
  + reflexivity.
  + reflexivity.
Qed. 

Lemma hd_skip:
forall i: nat,
forall A: Type,
forall d: A,
forall l: list A,
hd d (skipn i l) = nth i l d.
Proof.
intros i A d.
induction i as [| i IH].
- intros l. 
  destruct l.
  + trivial.
  + trivial.
- intros l.
  destruct l.
  + trivial.
  + simpl.
    rewrite IH.
    reflexivity.  
Qed.

Lemma last_skip:
forall i: nat,
forall A: Type,
forall d: A,
forall l: list A,
i < length l -> last (skipn i l) d = last l d.
Proof.
intros i A d.
induction i as [|i IH].
- intros l.
  destruct l.
  + trivial. 
  + trivial.
- intros l.
  destruct l.
  + trivial. 
  + simpl. 
    intros Hl.
    assert (Hl' : i < length l) by omega.
    rewrite IH. 
    * {
      destruct l. 
      - simpl in Hl'. 
        omega.
      - trivial. 
      } 
    * trivial.
Qed. 

Lemma hd_hd:
forall A: Type,
forall d: A,
forall l l': list A,
length l >= 1 -> hd d l = hd d (l ++ l').
Proof.
intros A d l l' H.
destruct l.
- simpl in H.
  apply le_Sn_0 in H.
  contradiction. 
- simpl.
  reflexivity.
Qed.

Lemma hd_first:
forall A: Type,
forall d: A,
forall l: list A,
forall i: nat,
i >= 1 -> hd d (firstn i l) = hd d l.
Proof.
intros A d l i H.
destruct l.
- destruct i.
  + simpl.
    reflexivity.
  + simpl. 
    reflexivity.
- destruct i. 
  + apply le_Sn_0 in H.
    contradiction.
  + simpl.
    reflexivity.
Qed. 

Lemma firstn_empty:
forall A: Type,
forall a: A,
forall i: nat,
a :: firstn i [] = [a].
Proof.
intros A a i.
destruct i.
- simpl. 
  reflexivity.
- simpl.
  reflexivity.
Qed. 

Lemma firstn_single:
forall A: Type,
forall a: A,
forall i: nat,
firstn (S i) [a] = [a].
intros A a i.
destruct i.
- simpl. 
  reflexivity.
- simpl. 
  reflexivity.
Qed.

Lemma nth_S':
forall i: nat,
forall A: Type,
forall a d: A,
forall l: list A,
nth (S i) (a :: l) d = nth i l d.
Proof.
intros i A a d l.
destruct i.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma firstn_S:
forall A: Type,
forall a: A,
forall l: list A,
forall i: nat,
firstn (S i) (a :: l) = a :: firstn i l.
Proof.
intros A a l.
induction l.
- intros i. simpl. reflexivity.
- intros i. destruct i.
  + simpl. reflexivity.
  + simpl. reflexivity. 
Qed.

Lemma last_cons:
forall A: Type,
forall a d: A,
forall l: list A,
l <> [] -> last (a :: l) d = last l d.
Proof.
intros A a d l H.
induction l.
- destruct H. reflexivity.
- trivial.
Qed.

Lemma not_nil_firstn:
forall A: Type,
forall l: list A,
forall i: nat,
l <> [] -> firstn (S i) l <> [].
Proof.
intros A l i H.
destruct l.
- simpl. exact H.
- simpl. apply not_eq_sym. apply nil_cons.
Qed.

Lemma nil_not_nil:
forall A: Type,
forall l: list A,
l = [] \/ l <> [].
Proof.
destruct l.
- left.
  reflexivity.
- right.
  apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma last_first_nth:
forall A: Type,
forall d: A,
forall l: list A,
forall i: nat,
length l >= S i -> last (firstn (S i) l) d = nth i l d.
Proof.
intros A d l.
induction l.
- destruct i.
  + trivial.
  + trivial.
- destruct i.
  + trivial. 
  + intros H. 
    rewrite nth_S'.  
    rewrite <- IHl.
    * rewrite firstn_S.
      {
      rewrite last_cons.
      - reflexivity.
      - apply not_nil_firstn.
        specialize (IHl i).
        replace (a::l) with ([a]++l) in H.
        + rewrite app_length in H.
          simpl in H.
          assert (H1: length l > 0) by omega.
          destruct l. 
          * simpl in H1.
            omega.   
          * apply not_eq_sym.   
            apply nil_cons.
        + simpl.
          reflexivity.
      }
    * {
      replace (a::l) with ([a]++l) in H.
      - rewrite app_length in H.
        simpl in H.
        omega.
      - simpl.
        reflexivity.
      }
Qed.  

Lemma nth_last:
forall A: Type,
forall l: list A,
forall d: A,
nth (length l - 1) l d = last l d.
Proof.
intros A l d.
destruct l.
- simpl. 
  reflexivity.
- remember (a::l) as l0. 
  rewrite app_removelast_last with (l:=l0) (d:=d).
  + rewrite app_length.
    simpl. 
    rewrite last_last.
    rewrite app_nth2.
    * assert (H: (Datatypes.length (removelast l0) + 1 - 1 - Datatypes.length (removelast l0) = 0)) by omega.
      rewrite H.
      simpl. 
      reflexivity.
    * omega.
  + rewrite Heql0.
    apply not_eq_sym. 
    replace (a::l) with ([]++a::l). 
    * apply app_cons_not_nil.
    * simpl. 
      reflexivity.
Qed.

Lemma hd_app:
forall A: Type,
forall l l': list A,
forall a d: A,
l <> [] ->
l' <> [] -> 
hd d l = hd d l' ->
hd d (l ++ [a]) = hd d (l' ++ [a]).
Proof.
intros A l l' a d H1 H2 H3.
destruct l.
- destruct l'.
  + simpl. 
    reflexivity.
  + destruct H1. 
    reflexivity. 
- destruct l'.
  + destruct H2. 
    reflexivity.
  + simpl. 
    simpl in H3.
    exact H3.
Qed.

Lemma last_2_1:
forall A: Type,
forall l: list A,
forall a1 a2 d: A,
last (a1 :: a2 :: l) d = last (a2 :: l) d.
Proof.
intros A l a1 a2 d.
simpl.
reflexivity.
Qed.

Lemma last_app:
forall A: Type,
forall l l': list A,
forall a d: A,
l <> [] ->
l' <> [] ->
last l d = last l' d -> 
last ([a] ++ l) d = last ([a] ++ l') d.
Proof.
intros A l l' a d H1 H2 H3.
induction l, l'.
- simpl. 
  reflexivity. 
- destruct H1. 
  reflexivity. 
- destruct H2.
  reflexivity.
- replace ([a] ++ a0 :: l) with (a :: a0 :: l).
  + replace ([a] ++ a1 :: l') with (a :: a1 :: l').
    * repeat rewrite last_2_1.
      exact H3.
    * simpl. 
      reflexivity.
  + simpl. 
    reflexivity.
Qed.

Lemma hd_not_nil:
forall A: Type,
forall l: list A,
forall a d: A,
d <> a ->
hd d l = a -> 
l <> [].
Proof.
intros A l a d H1 H2.
destruct l.
- simpl in H2.
  contradiction.
- apply not_eq_sym. 
  apply nil_cons.
Qed.

Lemma hd_not_nil_v2:
forall A: Type,
forall l: list A,
forall d: A,
hd d l <> d -> l <> [].
Proof.
intros A l d H.
destruct l.
- simpl in H.
  destruct H.
  reflexivity.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma hd_not_zero:
forall A: Type,
forall l: list A,
forall a d: A,
d <> a ->
hd d l = a -> 
length l > 0.
Proof.
intros A l a d H1 H2.
destruct l.
- simpl in H2.
  contradiction.
- simpl. 
  apply gt_Sn_O.
Qed.

Lemma hd_removelast:
forall A: Type,
forall s d: A,
forall l l': list A,
l <> [] -> hd d (removelast (s :: l) ++ l') = s.
Proof.
intros A s d l l' H.
destruct l.
- destruct H.
  reflexivity.
- simpl.
  reflexivity.
Qed. 

Lemma length_cons_gt_1:
forall A: Type,
forall s: A,
forall l: list A,
length (s :: l) > 1 -> l <> [].
Proof.
intros A s l H.
replace (s :: l) with ([s] ++ l) in H.
- rewrite app_length in H.
  simpl in H.
  apply gt_S_n in H.
  apply not_eq_sym. 
  apply length_not_zero.
  exact H.
- simpl. 
  reflexivity.
Qed.

Lemma length_cons_eq_1:
forall A: Type,
forall s: A,
forall l: list A,
length (s :: l) = 1 -> l = [].
Proof.
intros A s l H.
destruct l.
- reflexivity.
- simpl in H.
  apply eq_add_S in H.
  symmetry in H.
  apply O_S in H.
  contradiction. 
Qed.

Lemma not_exists_forall_not:
forall A B: Type,
forall l: list (A+B),
~ (exists a': A, l = [inl a']) ->
forall a': A, (l <> [inl a']).
Proof.
intros A B l H a'.
unfold not at 1 in H.
unfold not.
destruct l.
- intro H1.
  inversion H1.
- intro H1.
  apply H.
  exists a'.
  exact H1.
Qed.

Lemma in_in:
forall A: Type,
forall s: A,
forall s1 s2: list A,
In s (s1 ++ [s] ++ s2).
Proof.
intros A s s1 s2.
induction s1.
- simpl.
  left.
  reflexivity.
- apply in_app_iff.
  right.
  simpl.
  left.
  reflexivity.
Qed.

Lemma in_out:
forall A: Type,
forall s: A,
forall l s1 s2: list A,
l = s1 ++ [s] ++ s2 ->
In s l.
Proof.
intros A s l s1 s2 H.
rewrite H.
apply in_in.
Qed.

Lemma exists_length_eq_2:
forall A: Type,
forall l: list A,
length l = 2 ->
exists s1 s2: A,
l = [s1] ++ [s2].
Proof.
intros A l H.
destruct l.
- simpl in H.
  apply O_S in H.
  contradiction.
- destruct l.
  + simpl in H.
    apply eq_add_S in H.
    apply O_S in H.
    contradiction.
  + destruct l.
    * exists a, a0. 
      reflexivity.
    * simpl in H.
      repeat apply eq_add_S in H.
      symmetry in H. 
      apply O_S in H.
      contradiction. 
Qed.

Lemma exists_length_gt_2:
forall A: Type,
forall d: A,
forall l: list A,
length l > 2 ->
exists s1 s2: A,
exists l': list A,
l = [s1] ++ l' ++ [s2].
Proof.
intros A d l H.
destruct l.
- simpl in H.
  apply lt_n_0 in H. 
  contradiction.
- destruct l.
  + simpl in H.
    apply gt_S_n in H. 
    apply lt_n_0 in H. 
    contradiction.
  + destruct l.
    * simpl in H.
      repeat apply gt_S_n in H. 
      apply lt_n_0 in H. 
      contradiction.
    * assert (H1: l = [] \/ l <> []).
        {
        apply nil_not_nil.
        }
      {
      destruct H1 as [H1 | H1].
      - subst.
        exists a, a1, [a0].
        reflexivity.
      - change (a :: a0 :: a1 :: l) with (([a] ++ [a0] ++ [a1]) ++ l) in H.
        exists a.
        rewrite app_removelast_last  with (A:=A) (l:=l) (d:=d).
        + exists (last l d).
          exists (a0 :: a1 :: removelast l).
          reflexivity.
        + exact H1.
      }
Qed.

Lemma exists_length_ge_2:
forall A: Type,
forall def: A,
forall l: list A,
length l >= 2 ->
exists s1 s2: A,
exists l': list A,
l = [s1] ++ l' ++ [s2].
Proof.
intros A def l H1.
assert (H2: length l > 2 \/ length l = 2) by omega.
destruct H2 as [H2 | H2].
- apply (exists_length_gt_2 A def l) in H2.
  exact H2.
- apply exists_length_eq_2 in H2.
  destruct H2 as [s1 [s2 H3]].
  exists s1, s2, [].
  simpl. 
  exact H3.
Qed.

Lemma length_eq_0:
forall A: Type,
forall l: list A,
length l = 0 -> l = [].
Proof.
intros A l H.
destruct l.
- reflexivity.
- change (a ::l) with ([a] ++ l) in H.
  rewrite app_length in H.
  simpl in H.
  symmetry in H. 
  apply O_S in H.
  contradiction.
Qed.

Lemma elem_not_nil:
forall A: Type,
forall w1 w2: list A,
forall X: A,
w1 ++ [X] ++ w2 <> [].
Proof.
intros A w1 w2 X.
destruct w1. 
- simpl. 
  apply not_eq_sym.
  apply nil_cons.
- simpl. 
  apply not_eq_sym. 
  replace (a :: w1 ++ X :: w2) with (([a] ++ w1) ++ [X] ++ w2).
  + apply app_cons_not_nil.
  + simpl. 
    reflexivity.
Qed.

Lemma map_map_app:
forall A B : Type,
forall f: A -> B,
forall x y: list A,
forall z: list B,
map f x = map f y ++ z ->
exists z': list A,
z = map f z'.
Proof.
intros A B f x y z H.
symmetry in H.
apply map_expand in H.
destruct H as [s1' [s2' [H1 [H2 H3]]]].
exists s2'.
symmetry.
exact H3.
Qed.

Lemma cat_left:
forall A: Type,
forall a: A,
forall l1 l2: list A,
l1 = l2 -> [a] ++ l1 = [a] ++ l2.
Proof.
intros A a l1 l2 H.
rewrite H.
reflexivity.
Qed.

Lemma map_not_nil:
forall A B: Type,
forall f: A -> B,
forall l: list A,
map f l <> [] -> l <> [].
Proof.
intros A B f l H.
destruct l.
- destruct H.
  simpl. 
  reflexivity.
- apply not_eq_sym. 
  apply nil_cons.
Qed.

Lemma map_not_nil_inv:
forall A B: Type,
forall f: A -> B,
forall l: list A,
l <> [] -> map f l <> [].
Proof.
intros A B f l H.
destruct l.
- destruct H.
  reflexivity.
- simpl. 
  apply not_eq_sym. 
  apply nil_cons.
Qed.

Lemma app_not_nil:
forall A: Type,
forall x y: list A,
x ++ y <> [] ->
(x <> [] \/ y <> []).
Proof.
intros A x y H.
assert (H1: x = [] \/ x <> []).
  {
  apply nil_not_nil.
  }
assert (H2: y = [] \/ y <> []).
  {
  apply nil_not_nil.
  }
destruct H1 as [H1 | H1].
- destruct H2 as [H2 | H2].
  + rewrite H1 in H.
    rewrite H2 in H.
    simpl in H.
    destruct H.
    reflexivity.
  + right.
    exact H2.
- destruct H2 as [H2 | H2].
  + rewrite H2 in H.
    rewrite app_nil_r in H.
    left.
    exact H.
  + left.
    exact H1.
Qed.

Lemma app_not_nil_inv:
forall A: Type,
forall x y: list A,
(x <> [] \/ y <> []) ->
x ++ y <> [].
Proof.
intros A x y H.
destruct H as [H | H].
- intros H2. 
  apply app_eq_nil in H2.
  destruct H2 as [H2 _].
  contradiction.
- intros H2.
  apply app_eq_nil in H2.
  destruct H2 as [_ H2].
  contradiction.
Qed.

Lemma list_not_nil:
forall A: Type,
forall l: list A,
l <> [] -> 
exists l1 l2 l3: list A,
l = l1 ++ l2 ++ l3 /\
l2 <> [].
Proof.
intros A l H.
destruct l.
- destruct H.
  reflexivity.
- exists [], [a], l.
  split.
  + simpl. 
    reflexivity.
  + apply not_eq_sym.
    apply nil_cons.
Qed.

Lemma app_eq:
forall A: Type,
forall a: A,
forall l1 l2: list A,
l1 = l2 -> [a] ++ l1 = [a] ++ l2.
Proof.
intros A a l1 l2 H.
destruct l1, l2.
- simpl. 
  reflexivity.
- inversion H.
- inversion H.
- rewrite H.
  reflexivity.
Qed.

Lemma list_single_elem:
forall A: Type,
forall l1 l2: list A,
forall a b: A,
l1 ++ a :: l2 = [b] ->
l1 = []/\ l2 = [].
Proof.
intros A l1 l2 a b H1.
split.
- destruct l1.
  + reflexivity.
  + inversion H1.
    destruct l1. 
    * inversion H2.
    * inversion H2.
- destruct l1.
  + inversion H1.
    reflexivity.
  + inversion H1.
    destruct l1.
    * inversion H2.
    * inversion H2.
Qed.

Lemma last_not_nil:
forall A: Type,
forall l: list A,
forall d: A,
(last l d) <> d -> l <> [].
Proof.
intros A l d H.
destruct l.
- simpl in H.
  destruct H.
  reflexivity.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma app_cons_eq:
forall A: Type,
forall s1 s2: list A,
forall a b: A,
s1 ++ a :: s2 = [b] ->
s1 = [] /\ s2 = [] /\ a = b.
Proof.
intros A s1 s2 a b H.
destruct s1.
- inversion H.
  subst.
  auto.
- inversion H.
  destruct s1.
  + inversion H2.
  + inversion H2.
Qed.

Lemma not_in_not_eq:
forall A: Type,
forall a b: A,
~ In a [b] -> a <> b.
Proof.
intros A a b H.
simpl in H.
intros H2.
apply H.
left.
symmetry.
exact H2.
Qed.

Lemma inl_neq:
forall X Y: Type,
forall a b: X,
@inl X Y a <> @inl X Y b -> a <> b.
Proof.
intros X Y a b H.
intro.
apply H.
subst.
reflexivity.
Qed.

Lemma length_cons_le:
forall A: Type,
forall l1 l2: list A,
forall a: A,
forall n: nat,
length (l1 ++ a :: l2) <= n ->
length (l1 ++ l2) <= n.
Proof.
intros A l1 l2 a n H. 
rewrite app_length.
change (a :: l2) with ([a] ++ l2) in H.
repeat rewrite app_length in H.
simpl in H. 
omega. 
Qed.

Lemma in_app_cons:
forall A: Type,
forall l1 l2: list A,
forall a b: A,
In a (l1 ++ l2) ->
In a (l1 ++ b :: l2).
Proof.
intros A l1 l2 a b H.
apply in_app_or in H.
apply in_or_app.
destruct H as [H | H].
- left.
  exact H.
- right.
  change (b :: l2) with ([b] ++ l2).
  apply in_or_app.
  right.
  exact H.
Qed.

Lemma cons_app:
forall (A: Type) (s: A) (l: list A),
s :: l = [s] ++ l.
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma length_map_ge:
forall A B: Type,
forall n: nat,
forall f: A -> B,
forall s: list A,
length s >= n ->
length (map f s) >= n.
Proof.
induction n, s.
- simpl.
  auto.
- simpl. 
  intros H.
  omega.
- simpl.
  auto.
- simpl. 
  intros H.
  apply le_S_n in H.
  specialize (IHn f s H).
  apply le_n_S in IHn.
  exact IHn.
Qed.

Lemma length_map_le:
forall A B: Type,
forall n: nat,
forall f: A -> B,
forall s: list A,
length s <= n ->
length (map f s) <= n.
Proof.
induction n, s.
- simpl.
  auto.
- simpl. 
  intros H.
  omega.
- simpl.
  auto.
- simpl. 
  intros H.
  apply le_S_n in H.
  specialize (IHn f s H).
  apply le_n_S in IHn.
  exact IHn.
Qed.

Lemma length_map_le_inv:
forall A B: Type,
forall n: nat,
forall f: A -> B,
forall s: list A,
length (map f s) <= n ->
length s <= n.
Proof.
induction n, s.
- simpl.
  auto.
- simpl. 
  intros H.
  omega.
- simpl.
  auto.
- simpl. 
  intros H.
  apply le_S_n in H.
  specialize (IHn f s H).
  apply le_n_S in IHn.
  exact IHn.
Qed.

Lemma map_eq:
forall A B: Type,
forall f: A -> B,
forall l1 l2: list A,
injective A B f ->
map f l1 = map f l2 -> l1 = l2.
Proof.
intros A B f.
induction l1.
- intros l2 H1 H2. 
  simpl in H2.
  symmetry in H2.
  apply map_eq_nil in H2.
  symmetry.
  exact H2.
- intros l2 H1 H2.
  simpl in H2.
  destruct l2.
  + simpl in H2.
    inversion H2.
  + simpl in H2.
    inversion H2.
    assert (H1':= H1).
    specialize (H1 a a0 H0).
    specialize (IHl1 l2 H1' H3).
    subst.
    reflexivity.
Qed.

Fixpoint iter {A: Type} (w: list A) (n: nat): list A:=
match n with
| O => []
| S n => w ++ iter w n
end.

Lemma iter_comm:
forall A: Type,
forall l: list A,
forall i: nat,
l ++ iter l i = iter l i ++ l.
Proof.
intros A l i.
revert l.
induction i.
- simpl. 
  intros l.
  rewrite app_nil_r. 
  reflexivity.
- intros l. 
  simpl.
  rewrite <- app_assoc.
  rewrite <- IHi.
  reflexivity.
Qed.

Lemma cons_neq:
forall A: Type,
forall a: A,
forall l: list A,
l <> a :: l.
Proof.
intros A a l.
induction l.
- intros H. 
  inversion H. 
- intros H.
  inversion H.
  contradiction.  
Qed.

Lemma list_split:
forall A: Type,
forall l: list A,
forall n m: nat,
length l = n + m ->
exists l1 l2: list A,
l = l1 ++ l2 /\
length l1 = n /\
length l2 = m.
Proof.
intros A l n m H1.
assert (H2: firstn n l ++ skipn n l = l).
  {
  apply firstn_skipn.
  }
assert (H3: length (firstn n l) = min n (length l)).
  {
  apply firstn_length.
  }
assert (H4: min n (n + m) = n).
  {
  apply min_l.
  omega.
  }
assert (H5: length (firstn n l) = n).
  {  
  rewrite H1 in H3.
  rewrite H4 in H3.
  exact H3.
  }
clear H3 H4.
rewrite <- H2 in H1.
rewrite app_length in H1.
rewrite H5 in H1.
assert (H6: length (skipn n l) = m) by omega.
exists (firstn n l), (skipn n l).
split.
- symmetry.
  exact H2.
- split.
  + exact H5.
  + exact H6.
Qed.
 
Lemma list_split_exists:
forall A: Type,
forall l: list A,
exists l1 l2: list A,
l = l1 ++ l2.
Proof.
intros A.
induction l.
- exists [], [].
  reflexivity.
- destruct IHl as [l1 [l2 IHl]].
  rewrite IHl.
  exists (a :: l1), l2.
  reflexivity.
Qed.

Fixpoint get_As (A B: Type) (l: list (A + B)): list A:=
match l with
| [] => []
| inl a :: l => a :: get_As A B l
| inr b :: l => get_As A B l
end.

Lemma get_As_correct:
forall A B: Type,
forall r: list (A + B),
(forall e: (A + B), In e r -> exists a: A, e = inl a) ->
r = map inl (get_As A B r).
Proof.
intros A B r H.
induction r.
- simpl.
  reflexivity.
- destruct a.
  + simpl. 
    rewrite <- IHr.
    * reflexivity.
    * intros e H1.
      apply H.
      simpl.
      right.
      exact H1.
  + specialize (H (inr b)).
    assert (H1: In (inr b) (inr b :: r)).
      {
      simpl.
      left.
      reflexivity.
      }
    specialize (H H1).
    destruct H as [n H].
    discriminate.
Qed.
 
Fixpoint get_Bs (A B: Type) (l: list (A + B)): list B:=
match l with
| [] => []
| inl a :: l => get_Bs A B l
| inr b :: l => b :: get_Bs A B l
end.

Lemma get_Bs_correct:
forall A B: Type,
forall r: list (A + B),
(forall e: (A + B), In e r -> exists b: B, e = inr b) ->
r = map inr (get_Bs A B r).
Proof.
intros A B r H.
induction r.
- simpl.
  reflexivity.
- destruct a.
  + specialize (H (inl a)).
    assert (H1: In (inl a) (inl a :: r)).
      {
      simpl.
      left.
      reflexivity.
      }
    specialize (H H1).
    destruct H as [n H].
    discriminate.
  + simpl. 
    rewrite <- IHr.
    * reflexivity.
    * intros e H1.
      apply H.
      simpl.
      right.
      exact H1.
Qed.
 
Lemma split_app:
forall A: Type,
forall l l1 l2: list A,
l = l1 ++ l2 ->
exists l' l'': list A,
l = l' ++ l'' /\
l' = l1 /\
l'' = l2.
Proof.
intros A l.
destruct l.
- intros l1 l2 H.
  symmetry in H.
  apply app_eq_nil in H.
  destruct H as [H H1].
  subst.
  exists [], [].
  simpl.
  auto.
- intros l1 l2 H.
  exists l1, l2.
  split.
  + exact H.
  + auto.
Qed.

Lemma not_nil_app:
forall A: Type,
forall l1 l2: list A,
l1 <> [] ->
l1 ++ l2 <> [].
Proof.
intros A l1 l2 H.
destruct l1. 
- destruct H. 
  reflexivity.
- apply not_eq_sym. 
  intros H1.
  inversion H1.
Qed.

Fixpoint flat {A: Type} (l: list (list A)): list A:=
match l with
| [] => []
| s :: l => s ++ flat l
end.

Lemma flat_app:
forall A: Type,
forall l1 l2: list (list A),
flat (l1 ++ l2) = flat l1 ++ flat l2.
Proof.
induction l1.
- simpl.
  reflexivity.
- intros l2.
  simpl.
  specialize (IHl1 l2).
  rewrite IHl1.
  rewrite <- app_assoc.
  reflexivity.
Qed. 

Lemma app_single:
forall A: Type,
forall l1 l2: list A,
forall a: A,
l1 ++ l2 = [a] ->
l1 = [a] /\ l2 = [] \/
l1 = [] /\ l2 = [a].
Proof.
intros A l1 l2 a H.
destruct l1, l2.
- inversion H.
- inversion H.
  subst.
  right.
  auto.
- inversion H.
  subst.
  left.
  rewrite app_nil_r.
  auto.
- inversion H.
  destruct l1.
  + inversion H2.
  + inversion H2.
Qed.

(* --------------------------------------------------------------------- *)
(* SUFFIX                                                                *)
(* --------------------------------------------------------------------- *)

Section Suffix.

Variable A: Type.

Definition suffix_v1 (l1 l2: list A): Prop:=
exists l,
l2 = l ++ l1.

Inductive suffix_v2: list A -> list A -> Prop:=
| suffix_eq:  forall l1 l2: list A, l1 = l2 -> suffix_v2 l1 l2
| suffix_app: forall l1 l2: list A, forall a: A, suffix_v2 l1 l2 -> suffix_v2 l1 (a :: l2).  

Fixpoint suffix_v3 (l1 l2: list A): Prop:=
l1 = l2 \/
match l2 with
| [] => False
| e :: l' => suffix_v3 l1 l'
end.

Lemma suffix_v1_nil:
forall l: list A,
suffix_v1 [] l.
Proof.
intros l.
exists l.
rewrite app_nil_r.
reflexivity.
Qed.

Lemma suffix_v2_nil:
forall l: list A,
suffix_v2 [] l.
Proof.
induction l.
- apply suffix_eq. 
  reflexivity.
- apply suffix_app.
  exact IHl.
Qed.

Lemma suffix_v3_nil:
forall l: list A,
suffix_v3 [] l.
Proof.
intros l.
induction l.
- simpl.
  left.
  reflexivity.
- simpl.
  right.
  exact IHl.
Qed.

Lemma suffix_v1_equiv_suffix_v2:
forall l1 l2: list A,
suffix_v1 l1 l2 <-> suffix_v2 l1 l2.
Proof.
intros l1 l2.
split.
- intros H.
  destruct H as [l H].
  subst.
  induction l.
  + simpl.
    apply suffix_eq.
    reflexivity.
  + simpl.
    apply suffix_app.
    exact IHl.
- intros H.
  induction H.
  + subst.
    exists [].
    reflexivity.
  + destruct IHsuffix_v2 as [l IHsuffix_v2].
    subst.
    exists (a :: l).
    reflexivity.
Qed. 

Lemma suffix_v2_equiv_suffix_v3:
forall l1 l2: list A,
suffix_v2 l1 l2 <-> suffix_v3 l1 l2.
Proof.
intros l1 l2.
split.
- intros H.
  induction H.
  + subst.
    destruct l2. 
    * simpl. 
      left. 
      reflexivity. 
    * simpl. 
      left. 
      reflexivity. 
  + simpl.
    right.
    exact IHsuffix_v2.
- generalize dependent l2.
  induction l2.
  + intros H.
    simpl in H.
    destruct H as [H | H].
    * subst.
      apply suffix_eq.
      reflexivity.
    * contradiction.
  + intros H.
    simpl in H.
    destruct H as [H | H].
    * subst.
      apply suffix_eq.
      reflexivity.
    * apply suffix_app.
      apply IHl2.
      exact H.
Qed.

Lemma suffix_v1_split:
forall l1 l2: list A,
suffix_v1 l1 l2 ->
exists l: list A,
l ++ l1 = l2.
Proof.
intros l1 l2 H.
unfold suffix_v1 in H.
destruct H as [l H].
subst.
exists l.
reflexivity.
Qed.

Lemma suffix_v2_split:
forall l1 l2: list A,
suffix_v2 l1 l2 ->
exists l: list A,
l ++ l1 = l2.
Proof.
intros l1 l2 H.
induction H.
- subst.
  exists []. 
  reflexivity.
- destruct IHsuffix_v2 as [l H2].
  rewrite <- H2.
  exists (a :: l).
  reflexivity.
Qed.

Lemma suffix_v3_split:
forall l1 l2: list A,
suffix_v3 l1 l2 ->
exists l: list A,
l ++ l1 = l2.
Proof.
induction l2.
- intros H.
  simpl in H.
  destruct H as [H | H].
  + subst.
    exists [].
    reflexivity.
  + contradiction.
- intros H.
  simpl in H. 
  destruct H as [H | H].
  + subst.
    exists [].
    reflexivity.
  + specialize (IHl2 H).
    destruct IHl2 as [l H2].
    subst.
    exists (a :: l).
    reflexivity.
Qed.

End Suffix.
