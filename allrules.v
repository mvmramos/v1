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

Fixpoint length_max_sf (l: slist): nat:=
match l with
| [] => 0
| s :: l' => if leb (length_max_sf l') (length s) then length s else length_max_sf l'
end.

Lemma length_max_sf_cons_v1:
forall s: slist,
forall a: sf,
length_max_sf (a :: s) = length a \/
length_max_sf (a :: s) = length_max_sf s.
Proof.
destruct s.
- intros a.
  simpl.
  left.
  reflexivity.
- intros a0.
  assert (H1: s = [] \/ s <> []).
    {
    apply nil_not_nil.
    }
  destruct H1 as [H1 | H1].
  + subst. 
    simpl. 
    assert (H1: (length l) <= (length a0) \/
                (length l) > (length a0)) by omega.
    destruct H1 as [H1 | H1].
    * apply leb_correct in H1.
      rewrite H1.
      left.
      reflexivity.
    * apply leb_correct_conv in H1.
      rewrite H1.
      right.
      reflexivity.
  + simpl.
    assert (H2: (length_max_sf s) <= (length l) \/
                (length_max_sf s) > (length l)) by omega.
    destruct H2 as [H2 | H2].
    * apply leb_correct in H2.
      rewrite H2.
      assert (H3: (length l) <= (length a0) \/
                  (length l) > (length a0)) by omega.
      {
      destruct H3 as [H3 | H3].
      - apply leb_correct in H3.
        rewrite H3.
        left.
        reflexivity.
      - apply leb_correct_conv in H3.
        rewrite H3.
        right.
        reflexivity.
      }
    * apply leb_correct_conv in H2.
      rewrite H2.    
      assert (H3: (length_max_sf s) <= (length a0) \/
                  (length_max_sf s) > (length a0)) by omega.
      {
      destruct H3 as [H3 | H3].
      - apply leb_correct in H3.
        rewrite H3.
        left.
        reflexivity.
      - apply leb_correct_conv in H3.
        rewrite H3.
        right.
        reflexivity.
      }
Qed.

Lemma length_max_sf_cons_gt:
forall s: slist,
forall n: nat,
forall a: sf,
length_max_sf (a :: s) > n ->
length a > n \/ length_max_sf s > n.
Proof.
intros s n a H.
assert (H1: length_max_sf (a :: s) = length a \/
            length_max_sf (a :: s) = length_max_sf s).
  {
  apply length_max_sf_cons_v1. 
  }
destruct H1 as [H1 | H1].
- rewrite H1 in H. 
  left. 
  exact H.
- rewrite H1 in H. 
  right. 
  exact H. 
Qed.

Lemma length_max_sf_cons_le:
forall s: slist,
forall n: nat,
forall a: sf,
length_max_sf (a :: s) <= n ->
length a <= n /\ length_max_sf s <= n.
Proof.
intros s.
destruct s.
- intros n a H.
  simpl in H.
  split. 
  + exact H. 
  + simpl. 
    omega. 
- intros n a H2.
  simpl in H2.
  assert (H3: (length_max_sf s) <= (length l) \/
              (length_max_sf s) > (length l)) by omega.
  destruct H3 as [H3 | H3].
  + apply leb_correct in H3.
    rewrite H3 in H2. 
    assert (H4: (length l) <= (length a) \/
                (length l) > (length a)) by omega.
    destruct H4 as [H4 | H4].
    * apply leb_correct in H4.
      rewrite H4 in H2.
      {
      split.
      - exact H2.
      - simpl.
        rewrite H3.
        apply leb_complete in H4.
        omega.
      }
    * {
      split.
      - apply leb_correct_conv in H4.
        rewrite H4 in H2.
        apply leb_complete_conv in H4.
        omega.
      - simpl.
        rewrite H3.
        apply leb_correct_conv in H4.
        rewrite H4 in H2.
        exact H2.
      }
  + apply leb_correct_conv in H3.
    rewrite H3 in H2. 
    assert (H4: (length_max_sf s) <= (length a) \/
                (length_max_sf s) > (length a)) by omega.
    destruct H4 as [H4 | H4].
    * apply leb_correct in H4.
      rewrite H4 in H2.
      {
      split.
      - exact H2.
      - simpl.
        rewrite H3.
        apply leb_complete in H4.
        omega.
      }
    * {
      split.
      - apply leb_correct_conv in H4.
        rewrite H4 in H2.
        apply leb_complete_conv in H4.
        omega.
      - simpl.
        rewrite H3.
        apply leb_correct_conv in H4.
        rewrite H4 in H2.
        exact H2.
      }
Qed.

Lemma length_max_sf_cons_v2:
forall s: slist,
forall a: sf,
forall n: nat,
length_max_sf (a :: s) = n ->
length a = n /\ length_max_sf s <= n \/
length a <= n /\ length_max_sf s = n.
Proof.
intros s a n H1.
assert (H2: length_max_sf (a :: s) = length a \/
            length_max_sf (a :: s) = length_max_sf s).
  {
  apply length_max_sf_cons_v1.
  }
destruct H2 as [H2 | H2].
- left.
  split.
  + omega.
  + assert (H3: length_max_sf (a :: s) <= n). { admit. } 
    apply length_max_sf_cons_le in H3.
    destruct H3 as [_ H3].
    exact H3.
- right.
  split.
  + assert (H3: length_max_sf (a :: s) <= n). { admit. } 
    apply length_max_sf_cons_le in H3.
    destruct H3 as [H3 _].
    exact H3.
  + omega.
Qed.

Lemma length_max_sf_or:
forall l1 l2: slist,
length_max_sf (l1 ++ l2) = length_max_sf l1 \/
length_max_sf (l1 ++ l2) = length_max_sf l2.
Proof.
induction l1.
- intros l2.
  right.
  simpl. 
  reflexivity.
- intros l2.
  specialize (IHl1 l2).
  destruct IHl1 as [IHl1 | IHl1].
  + left.
    simpl.
    assert (H1: (length_max_sf (l1 ++ l2)) <= (length a) \/
                (length_max_sf (l1 ++ l2)) > (length a)) by omega.
    destruct H1 as [H1 | H1].
    * apply leb_correct in H1.
      rewrite H1.
      apply leb_complete in H1.
      assert (H2: length_max_sf l1 <= length a). 
        { 
        rewrite IHl1 in H1.
        exact H1.
        }
      apply leb_correct in H2.
      rewrite H2.
      reflexivity.
    * apply leb_correct_conv in H1.
      rewrite H1.
      apply leb_complete_conv in H1.
      rewrite IHl1 in H1.
      apply leb_correct_conv in H1.
      rewrite H1.
      exact IHl1.
  + right.
    assert (H1: (length_max_sf l2) <= (length a)  \/
                (length_max_sf l2) > (length a)) by omega.
    destruct H1 as [H1 | H1].
    * admit. (* +++ *)
    * rewrite <- IHl1 in H1.
      simpl. 
      apply leb_correct_conv in H1.
      rewrite H1.
      exact IHl1. 
Qed.

Lemma length_max_sf_or_cons:
forall s: slist,
forall a: sf,
forall n: nat,
length_max_sf s <= n /\ length a = n \/
length_max_sf s = n /\ length a <= n ->
length_max_sf (a :: s) = n.
Proof.
induction s.
- intros a n H.
  destruct H as [H | H].
  + destruct H as [_ H].
    simpl.  
    exact H.
  + destruct H as [H1 H2].
    simpl in H1.
    subst.
    simpl. 
    omega.
- intros a0 n H.
  destruct H as [H | H].
  + destruct H as [H1 H2].
    apply length_max_sf_cons_le in H1.
    destruct H1 as [H1 H3].
    simpl. 
    assert (H5: (length_max_sf s) <= (length a) \/
                (length_max_sf s) > (length a)) by omega.
    destruct H5 as [H5 | H5].
    * apply leb_correct in H5.
      rewrite H5.
      rewrite <- H2 in H1.
      apply leb_correct in H1.
      rewrite H1.
      exact H2.
    * apply leb_correct_conv in H5.
      rewrite H5.
      rewrite <- H2 in H3.
      apply leb_correct in H3.
      rewrite H3.
      exact H2.
  + destruct H as [H1 H2].
    apply length_max_sf_cons_v2 in H1.
    assert (H5: (length_max_sf s) <= (length a) \/
                (length_max_sf s) > (length a)) by omega.
    destruct H5 as [H5 | H5].
    * apply leb_correct in H5.
      simpl.
      rewrite H5.
      {
      destruct H1 as [H1 | H1].
      - destruct H1 as [H3 H4].
        rewrite <- H3 in H2.
        apply leb_correct in H2.
        admit.
      - destruct H1 as [H3 H4].
        admit.
      }
    * apply leb_correct_conv in H5.
      simpl.
      rewrite H5.
      simpl in IHs.
      apply IHs.
      {
      destruct H1 as [H1 | H1].
      - admit.
      - admit.
      } 
Qed.

Lemma length_max_sf_app_le:
forall l1 l2: slist,
forall n: nat,
length_max_sf l1 <= n ->
length_max_sf l2 <= n ->
length_max_sf (l1 ++ l2) <= n.
Proof.
induction l1.
- intros l2 n H1 H2.
  simpl. 
  exact H2.
- intros l2 n H1 H2.
  apply length_max_sf_cons_le in H1.
  destruct H1 as [H3 H4].
  assert (H5: length_max_sf (l1 ++ l2) > length a \/
              length_max_sf (l1 ++ l2) <= length a) by omega.
  destruct H5 as [H5 | H5].
  + simpl.
    apply leb_correct_conv in H5.
    rewrite H5.
    apply IHl1.
    * exact H4.
    * exact H2.
  + simpl.
    apply leb_correct in H5.
    rewrite H5.
    exact H3.
Qed.

Lemma length_max_sf_or_app_eq:
forall l1 l2: slist,
forall n: nat,
(length_max_sf l1 = n /\ length_max_sf l2 <= n) \/
(length_max_sf l2 = n /\ length_max_sf l1 <= n) ->
length_max_sf (l1 ++ l2) = n.
Proof.
induction l1.
- intros l2 n H.
  simpl in H.
  destruct H as [H | H].
  + subst.
    simpl. 
    omega.
  + simpl.
    omega.
- intros l2 n H.
  specialize (IHl1 l2 n).
  destruct H as [H | H].
  + destruct H as [H1 H2].
    apply length_max_sf_cons_v2 in H1.
    change ((a :: l1) ++ l2) with (a :: (l1 ++ l2)).
    apply length_max_sf_or_cons.
    destruct H1 as [H1 | H1].
    * left.
      {
      split.
      - destruct H1 as [H1 _].    
        admit.
      - destruct H1 as [H3 H4].
        exact H3.
      } 
    * right.
      {
      split.
      - destruct H1 as [H1 _].
        admit.
      - destruct H1 as [H1 _].
        exact H1.
      }
  + destruct H as [H1 H2].
    apply length_max_sf_cons_le in H2.
    change ((a :: l1) ++ l2) with (a :: (l1 ++ l2)).
    apply length_max_sf_or_cons.
    destruct H2 as [H3 H4].
    right.
    split.
    * admit. 
    * exact H3.
Qed.

Fixpoint length_max (rl: rlist): nat:=
match rl with
| [] => 0
| (l, r) :: rl' => if leb (length_max rl') (length r) then length r else length_max rl'
end.

Lemma length_max_correct:
forall rl: rlist,
forall left: non_terminal,
forall right: sf,
In (left, right) rl ->
length right <= length_max rl.
Proof.
induction rl.
- intros left right H.
  simpl in H.
  contradiction.
- intros left right H1.
  simpl in H1.
  destruct H1.
  + subst. 
    simpl. 
    assert (H2: (length_max rl) <= (length right) \/
                (length_max rl) > (length right)) by omega.
    destruct H2 as [H2 | H2].
    * apply leb_correct in H2.
      rewrite H2.
      omega.    
    * apply leb_correct_conv in H2.
      rewrite H2.
      assert (H3: leb (length_max rl) (length right) = false -> (length_max rl) > (length right)).
        {
        apply leb_complete_conv.
        }
      specialize (H3 H2).
      omega.
  + destruct a.
    simpl. 
    assert (H2: (length_max rl) <= (length l) \/
                (length_max rl) > (length l)) by omega.
    destruct H2 as [H2 | H2].
    * apply leb_correct in H2.
      rewrite H2.
      specialize (IHrl left right H).
      assert (H3: leb (length_max rl) (length l) = true -> (length_max rl) <= (length l)).
        {
        apply leb_complete.
        }
      specialize (H3 H2).
      omega.
    * apply leb_correct_conv in H2.
      rewrite H2.
      apply IHrl with (left:= left).
      exact H.
Qed.

Lemma length_max_or:
forall l1 l2: rlist,
forall n: nat,
(length_max l1 = n /\ length_max l1 >= length_max l2) \/
(length_max l2 = n /\ length_max l2 > length_max l1) ->
length_max (l1 ++ l2) = n.
Proof.
admit.
Qed.

Lemma length_max_max:
forall l1 l2: rlist,
length_max (l1 ++ l2) = max (length_max l1) (length_max l2).
Proof.
admit.
Qed.

Definition npair (n: non_terminal): (non_terminal + terminal):= inl n.
Definition tpair (t: terminal): (non_terminal + terminal):= inr t.

Fixpoint all_terminals_sf (l: sf): tlist:=
match l with
| [] => []
| (inr t) :: l' => t :: all_terminals_sf l'
| (inl n) :: l' => all_terminals_sf l'
end.

Lemma all_terminals_sf_app:
forall l1 l2: sf,
all_terminals_sf (l1 ++ l2) = all_terminals_sf l1 ++ all_terminals_sf l2.
Proof.
induction l1.
- simpl.
  reflexivity.
- intros l2.
  change (a :: l1) with ([a] ++ l1).
  rewrite <- app_assoc.
  destruct a.
  + simpl.
    exact (IHl1 l2).
  + simpl. 
    apply app_eq.
    apply IHl1. 
Qed.

Fixpoint tin (t: terminal) (l: tlist): bool:=
match l with
| [] => false
| t' :: l' => orb false (* (t = t') ... *) (tin t l')
end.

Fixpoint remove_tduplicates (l: tlist) (p: tlist): tlist:=
match l with
| [] => []
| t :: l' => if tin t p
                then remove_tduplicates l' p
                else remove_tduplicates l' (t :: p)
end.

Fixpoint all_terminals (rl: rlist): tlist:=
match rl with
| [] => []
| (l, r) :: rl' => (all_terminals_sf r) ++ (all_terminals rl')
end.

Lemma all_terminals_app:
forall l1 l2: rlist,
all_terminals (l1 ++ l2) = all_terminals l1 ++ all_terminals l2.
Proof.
induction l1.
- simpl.
  reflexivity.
- intros l2.
  change (a :: l1) with ([a] ++ l1).
  rewrite <- app_assoc.
  destruct a.
  simpl.
  rewrite <- app_assoc.
  specialize (IHl1 l2).
  rewrite IHl1.
  reflexivity.
Qed.

Lemma all_terminals_correct:
forall t: terminal,
forall left: non_terminal,
forall right: sf,
forall rl: rlist,
In (inr t) right -> In (left, right) rl -> In t (all_terminals rl).
Proof.
intros t left right rl.
generalize dependent right.
generalize dependent left.
generalize dependent t.
induction rl.
- intros t left right H1 H2.
  simpl in H2.
  contradiction.
- intros t left right H1 H2.
  simpl in H2.
  destruct H2 as [H2 | H2].
  + subst. 
    simpl.
    apply in_or_app.
    left.
    apply in_split in H1.
    destruct H1 as [l1 [l2 H1]].
    rewrite H1.
    rewrite all_terminals_sf_app.
    apply in_or_app.
    right.
    simpl. 
    left.
    reflexivity.
  + change (a :: rl) with ([a] ++ rl).
    rewrite all_terminals_app.
    apply in_or_app.
    right.
    apply IHrl with (left:= left) (right:= right).
    * exact H1.
    * exact H2.
Qed.

Fixpoint all_non_terminals_sf (l: sf): nlist:=
match l with
| [] => []
| (inr t) :: l' => all_non_terminals_sf l'
| (inl n) :: l' => n :: all_non_terminals_sf l'
end.

Lemma all_non_terminals_sf_app:
forall l1 l2: sf,
all_non_terminals_sf (l1 ++ l2) = all_non_terminals_sf l1 ++ all_non_terminals_sf l2.
Proof.
induction l1.
- simpl.
  reflexivity.
- intros l2.
  change (a :: l1) with ([a] ++ l1).
  rewrite <- app_assoc.
  destruct a.
  + simpl.
    specialize (IHl1 l2).
    rewrite IHl1.
    reflexivity.
  + simpl. 
    specialize (IHl1 l2).
    rewrite IHl1.
    reflexivity.
Qed.

Fixpoint nin (n: non_terminal) (l: nlist): bool:=
match l with
| [] => false
| n' :: l' => orb false (* (n = n') ... *) (nin n l')
end.

Fixpoint remove_nduplicates (l: nlist) (p: nlist): nlist:=
match l with
| [] => []
| n :: l' => if nin n p
                then remove_nduplicates l' p
                else remove_nduplicates l' (n :: p)
end.

Fixpoint all_non_terminals (rl: rlist): nlist:=
match rl with
| [] => []
| (l, r) :: rl' => l :: (all_non_terminals_sf r) ++ (all_non_terminals rl')
end.

Lemma all_non_terminals_app:
forall l1 l2: rlist,
all_non_terminals (l1 ++ l2) = all_non_terminals l1 ++ all_non_terminals l2.
Proof.
induction l1.
- simpl.
  reflexivity.
- intros l2.
  change (a :: l1) with ([a] ++ l1).
  rewrite <- app_assoc.
  destruct a.
  simpl.
  rewrite <- app_assoc.
  specialize (IHl1 l2).
  rewrite IHl1.
  reflexivity.
Qed.

Lemma all_non_terminals_correct:
forall n: non_terminal,
forall left: non_terminal,
forall right: sf,
forall rl: rlist,
(n = left) \/ In (inl n) right -> 
In (left, right) rl -> In n (all_non_terminals rl).
Proof.
intros n left right rl.
generalize dependent right.
generalize dependent left.
generalize dependent n.
induction rl.
- intros n left right H1 H2.
  simpl in H2.
  contradiction.
- intros n left right H1 H2.
  destruct H1 as [H1 | H1].
  + subst. 
    destruct H2 as [H2 | H2].
    * subst.
      simpl.
      left.
      reflexivity.
    * destruct a. 
      simpl. 
      right. 
      apply in_or_app.
      right.
      specialize (IHrl left left right).
      {
      apply IHrl.
      - left.
        reflexivity.
      - exact H2.
      }      
  + simpl in H2.
    destruct H2 as [H2 | H2].
    * apply in_split in H1.
      destruct H1 as [l1 [l2 H1]].
      subst. 
      simpl.
      right.
      apply in_or_app.
      left.
      rewrite all_non_terminals_sf_app.
      apply in_or_app.
      right.
      simpl. 
      left.
      reflexivity.
    * change (a :: rl) with ([a] ++ rl).
      rewrite all_non_terminals_app.
      apply in_or_app.
      right.
      {
      apply IHrl with (left:= left) (right:= right).
      - right.
        exact H1.
      - exact H2.
      }
Qed.

Lemma all_non_terminals_not_nil:
forall rl: rlist,
rl <> [] ->
all_non_terminals rl <> [].
Proof.
destruct rl.
- intros H.
  destruct H.
  reflexivity.
- intros H.
  destruct p.
  simpl.
  change (n :: all_non_terminals_sf l ++ all_non_terminals rl) with ((n :: all_non_terminals_sf l) ++ all_non_terminals rl).
  apply app_not_nil_inv.
  left.
  apply not_eq_sym.
  apply nil_cons. 
Qed.

Definition all_symbols (rl: rlist): vlist:=
let t: tlist:= all_terminals rl in
let l: nlist:= all_non_terminals rl in
(map tpair t) ++ (map npair l).

Lemma all_symbols_correct:
forall n: non_terminal,
forall t: terminal,
forall rl: rlist,
(In (inl n) (map npair (all_non_terminals rl)) -> In (inl n) (all_symbols rl)) /\
(In (inr t) (map tpair (all_terminals rl)) -> In (inr t) (all_symbols rl)).
Proof.
intros n t rl.
split.
- intros H.
  unfold all_symbols.
  apply in_or_app.
  right.
  exact H.
- intros H.
  unfold all_symbols.
  apply in_or_app.
  left.
  exact H.
Qed.

Lemma all_symbols_not_nil:
forall rl: rlist,
rl <> [] ->
all_symbols rl <> [].
Proof.
destruct rl.
- intros H.
  destruct H.
  reflexivity.
- intros H.
  destruct p.
  unfold all_symbols.
  apply app_not_nil_inv.
  right.
  simpl.
  apply not_eq_sym.
  apply nil_cons. 
Qed.

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

Lemma concat_symbol_length_correct:
forall l: slist,
forall e: symbol,
forall d: sf,
length l > 0 ->
forall i: nat,
i < length l ->
length (nth i (concat_symbol e l) d) = length (nth i l d) + 1. 
Proof.
induction l.
- intros e d H.
  simpl in H.
  apply lt_irrefl in H.
  contradiction.
- intros e d H1 i H2.
  simpl concat_symbol.
  assert (H3: i = 0 \/ i > 0) by omega.
  destruct H3 as [H3 | H3].
  + subst.
    simpl.
    omega.
  + apply gt_zero_exists in H3.
    destruct H3 as [j H3].
    subst.
    simpl.
    apply IHl.
    * simpl in H2. 
      omega.
    * simpl in H2.
      apply le_S_n.
      exact H2.
Qed.

Lemma concat_symbol_length_max_sf_correct_aux:
forall l: slist,
forall s: symbol,
forall n: nat,
length_max_sf l <= n ->
length_max_sf (concat_symbol s l) <= S n.
Proof.
induction l.
- intros s n H.
  simpl. 
  omega.
- intros s n H1.
  apply length_max_sf_cons_le in H1.
  simpl concat_symbol.
  change ((s :: a) :: concat_symbol s l) with ([(s :: a)] ++ concat_symbol s l).
  apply length_max_sf_app_le. 
  + simpl. 
    omega.
  + apply IHl.
    destruct H1 as [_ H1].
    exact H1.
Qed.

Lemma concat_symbol_length_max_sf_correct:
forall l: slist,
forall s: symbol,
forall n: nat,
l <> [] ->
length_max_sf l = n ->
length_max_sf (concat_symbol s l) = S n.
Proof.
induction l.
- intros s n H.
  destruct H.
  reflexivity.
- intros s n H1 H2.
  apply length_max_sf_cons_v2 in H2.
  simpl concat_symbol.
  change ((s :: a) :: concat_symbol s l) with ([(s :: a)] ++ concat_symbol s l).
  apply length_max_sf_or_app_eq.
  assert (H: l = [] \/ l <> []). 
    {
    apply nil_not_nil. 
    }
  destruct H as [H | H].
  + subst.
    simpl. 
    destruct H2 as [H2 | H2].
    * left.
      {
      split.
      - omega.
      - omega.
      }
    * left.
      {
      split.
      - simpl in H2.
        destruct H2 as [H3 H4].
        subst.
        omega.
      - omega.
      }
  + destruct H2 as [H2 | H2].
    * left.
      simpl. 
      {
      split. 
      - apply eq_S.
        destruct H2 as [H2 _]. 
        exact H2.
      - apply concat_symbol_length_max_sf_correct_aux. 
        destruct H2 as [_ H2].
        exact H2.
      }
    * right.
      simpl.
      { 
      split.
      - apply IHl.
        + exact H.
        + destruct H2 as [_ H2].
          exact H2.
      - omega. 
      }
Qed.

Lemma concat_symbol_nil:
forall s: symbol,
concat_symbol s [] = [].
Proof.
intros s.
simpl. 
reflexivity.
Qed.

Lemma concat_symbol_not_nil:
forall l: slist,
forall s: symbol,
l <> [] ->
concat_symbol s l <> [].
Proof.
intros l s H.
destruct l.
- destruct H.
  reflexivity.
- simpl.
  apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma concat_symbol_not_nil_inv:
forall l: slist,
forall s: symbol,
concat_symbol s l <> [] ->
l <> [].
Proof.
destruct l.
- intros s H.
  simpl in H.
  destruct H.
  reflexivity.
- intros s H.
  apply not_eq_sym.
  apply nil_cons.
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

Lemma concat_symbol_length_max_sf_not_zero:
forall a: symbol,
forall l: slist,
l <> [] ->
~ length_max_sf (concat_symbol a l) = 0.
Proof.
intros a l H1 H2.
induction l.
- destruct H1.
  reflexivity.
- simpl in H2.
  assert (H3: (length_max_sf (concat_symbol a l)) <= (S (length a0)) \/
              (length_max_sf (concat_symbol a l)) > (S (length a0))) by omega.
  destruct H3 as [H3 | H3].
  + apply leb_correct in H3.
    rewrite H3 in H2.
    omega.
  + apply leb_correct_conv in H3.
    rewrite H3 in H2.
    apply IHl.
    * {
      destruct l. 
      - simpl in H3.
        inversion H3. 
      - apply not_eq_sym.
        apply nil_cons.
      }
    * exact H2.
Qed.

Lemma in_concat_symbol_exists:
forall l: slist,
forall e: symbol,
forall s: sf,
In s (concat_symbol e l) ->
exists s': sf,
In s' l /\
s = e :: s'.
Proof.
induction l. 
- intros e s H.
  simpl in H. 
  contradiction.
- intros e s H.
  simpl in H.
  destruct H as [H | H].
  + exists a.
    split.
    * simpl. 
      left.
      reflexivity.
    * symmetry. 
      exact H.
  + specialize (IHl e s H).
    destruct IHl as [s' [H1 H2]].
    exists s'.
    split. 
    * simpl. 
      right.
      exact H1.
    * exact H2.
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

Lemma concat_list_nil:
forall v: vlist,
forall s: slist,
v = [] \/ s = [] ->
concat_list v s = [].
Proof.
intros v s H.
destruct H as [H | H].
- subst.
  simpl. 
  reflexivity.
- subst.
  induction v.
  + simpl. 
    reflexivity.
  + simpl.  
    exact IHv.
Qed.

Lemma concat_list_not_nil:
forall v: vlist,
forall s: slist,
v <> [] ->
s <> [] ->
concat_list v s <> [].
Proof.
destruct v. 
- intros s H. 
  destruct H.
  reflexivity.
- intros s0 H1 H2.
  simpl.
  apply app_not_nil_inv.
  left.
  apply concat_symbol_not_nil.
  exact H2.
Qed.

Lemma concat_list_not_nil_inv:
forall v: vlist,
forall s: slist,
concat_list v s <> [] ->
v <> [] /\ s <> [].
Proof.
intros v s H.
induction v. 
- simpl in H. 
  destruct H.
  reflexivity.
- simpl in H.
  apply app_not_nil in H.
  destruct H as [H | H].
  + split.
    * apply not_eq_sym.
      apply nil_cons.
    * apply concat_symbol_not_nil_inv in H.
      exact H.
  + split.
    * apply not_eq_sym.
      apply nil_cons.
    * specialize (IHv H).
      destruct IHv as [_ IHv].
      exact IHv.
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

Lemma concat_list_length_max_sf_correct:
forall v: vlist,
forall l: slist,
forall n: nat,
v <> [] ->
l <> [] ->
length_max_sf l = n ->
length_max_sf (concat_list v l) = S n.
Proof.
induction v.
- intros l n H.
  destruct H.
  reflexivity.
- intros l n H1 H2 H3.
  simpl.
  assert (H4: length_max_sf (concat_symbol a l ++ concat_list v l) = length_max_sf (concat_symbol a l) \/
              length_max_sf (concat_symbol a l ++ concat_list v l) = length_max_sf (concat_list v l)).
    {
    apply length_max_sf_or.
    }
  destruct H4 as [H4 | H4].
  + rewrite H4.
    apply concat_symbol_length_max_sf_correct.
    * exact H2.
    * exact H3.
  + assert (H5: v = [] \/ v <> []).
      {
      apply nil_not_nil.
      }
    destruct H5 as [H5 | H5].
    * subst.
      simpl in H4.
      rewrite app_nil_r in H4.
      {
      apply concat_symbol_length_max_sf_not_zero in H4. 
      - contradiction.
      - exact H2.
      } 
    * rewrite H4.
      {
      apply IHv.
      - exact H5.
      - exact H2.
      - exact H3.
      } 
Qed.

Lemma in_concat_list_exists:
forall v: vlist,
forall l: slist,
forall s: sf,
In s (concat_list v l) ->
exists e: symbol,
exists s': sf,
In e v /\
In s' l /\
s = e :: s'.
Proof.
induction v.
- intros l s H.
  simpl in H.
  contradiction.
- intros l s H.
  simpl in H.
  apply in_app_or in H.
  destruct H as [H | H].
  + apply in_concat_symbol_exists in H.
    destruct H as [s' [H1 H2]].
    exists a, s'.
    split.
    * simpl.
      left.
      reflexivity.
    * {
      split.
      - exact H1.
      - exact H2.
      }
  + specialize (IHv l s H).
    destruct IHv as [e [s' [H1 [H2 H3]]]].
    exists e, s'.
    split.
    * simpl.
      right.
      exact H1.
    * {
      split.
      - exact H2.
      - exact H3.
      } 
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

Lemma all_sf_with_length_correct:
forall n: nat,
forall v: vlist,
forall s: sf,
In s (all_sf_with n v) ->
length s = n.
Proof.
induction n.
- intros v s H1.
  simpl in H1.
  destruct H1 as [H1 | H1].
  + rewrite <- H1.
    simpl.
    reflexivity.
  + contradiction.
- intros v s H.
  simpl in H.
  apply in_concat_list_exists in H.
  destruct H as [e [s' [H1 [H2 H3]]]].
  specialize (IHn v s' H2).
  rewrite H3.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma all_sf_with_nil:
forall n: nat,
n >= 1 ->
all_sf_with n [] = [].
Proof.
intros n H.
destruct n.
- omega. 
- simpl.
  reflexivity.
Qed.

Lemma all_sf_with_not_nil:
forall n: nat,
forall v: vlist,
n = 0 \/ v <> [] ->
all_sf_with n v <> [].
Proof.
induction n.
- intros v H. 
  simpl. 
  discriminate.
- intros v H. 
  destruct H as [H | H].
  + omega.
  + simpl. 
    apply concat_list_not_nil.
    * exact H.
    * apply IHn.
      right.
      exact H.
Qed.    

Lemma all_sf_with_length_max_correct:
forall n: nat,
forall v: vlist,
(n = 0 \/ v <> []) ->
length_max_sf (all_sf_with n v) = n.
Proof.
intros n v H.
destruct H as [H | H].
- subst.
  simpl. 
  reflexivity.
- induction n.
  + simpl. 
    reflexivity.
  + simpl. 
    apply concat_list_length_max_sf_correct with (v:= v) in IHn.
    * exact IHn.
    * exact H.
    * apply all_sf_with_not_nil.
      right.
      exact H.
Qed.

Lemma all_sf_with_not_nil_inv:
forall n: nat,
forall v: vlist,
all_sf_with n v <> [] ->
n = 0 \/ v <> [].
Proof.
induction n.
- intros v H.
  left.
  reflexivity.
- intros v H.
  right.
  simpl in H.
  apply concat_list_not_nil_inv in H.
  destruct H as [H _].
  exact H.
Qed.

Fixpoint all_rules_match (n: non_terminal) (l: slist): rlist:=
match l with
| [] => []
| r :: l' => (n, r) :: (all_rules_match n l')
end.

Lemma all_rules_match_correct:
forall n: non_terminal,
forall l: slist,
forall r: sf,
In r l -> In (n, r) (all_rules_match n l).
Proof.
intros n l.
generalize dependent n.
induction l.
- intros n r H.
  simpl in H.
  contradiction.
- intros n r H.
  simpl in H.
  simpl. 
  destruct H as [H | H].
  + subst.
    left.
    reflexivity.
  + right.
    apply IHl.
    exact H.
Qed.

Lemma length_max_all_rules_match_le:
forall s: slist,
forall n: nat,
forall a: non_terminal,
length_max_sf s <= n ->
length_max (all_rules_match a s) <= n.
Proof.
induction s.
- intros n a H0.
  simpl.
  omega.
- intros n a0 H.
  apply length_max_sf_cons_le in H.
  destruct H as [H10 H11].
  simpl.
  assert (H4: (length_max (all_rules_match a0 s)) <= (length a) \/
              (length_max (all_rules_match a0 s)) > (length a)) by omega.
  destruct H4 as [H4 | H4].
  + apply leb_correct in H4.
    rewrite H4.
    exact H10.
  + apply leb_correct_conv in H4.
    rewrite H4.
    apply IHs.
    exact H11.
Qed.

Lemma length_max_all_rules_match_gt:
forall s: slist,
forall n: nat,
forall a: non_terminal,
length_max_sf s > n ->
length_max (all_rules_match a s) > n.
Proof.
induction s.
- intros n a H0.
  simpl.
  simpl in H0.
  omega.
- intros n a0 H.
  apply length_max_sf_cons_gt in H.
  destruct H as [H9 | H9].
  + simpl.
    assert (H4: (length_max (all_rules_match a0 s)) <= (length a) \/
                (length_max (all_rules_match a0 s)) > (length a)) by omega.
    destruct H4 as [H4 | H4].
    * apply leb_correct in H4.
      rewrite H4.
      exact H9.
    * apply leb_correct_conv in H4.
      rewrite H4.
      apply leb_complete_conv in H4.
      omega.
  + simpl.
    assert (H4: (length_max (all_rules_match a0 s)) <= (length a) \/
                (length_max (all_rules_match a0 s)) > (length a)) by omega.
    destruct H4 as [H4 | H4].
    * apply leb_correct in H4.
      rewrite H4.
      apply leb_complete in H4.
      specialize (IHs n a0 H9).
      omega.
    * apply leb_correct_conv in H4.
      rewrite H4.
      apply leb_complete_conv in H4.
      apply IHs. 
      exact H9. 
Qed.

Lemma all_rules_match_length_max_correct:
forall s: slist,
forall n: nat,
forall a: non_terminal,
length_max_sf s = n ->
length_max (all_rules_match a s) = n.
Proof.
induction s.
- intros n a H2.
  simpl. 
  simpl in H2.
  exact H2.
- intros n a0 H2.
  simpl in H2.
  simpl. 
  assert (H3: (length_max_sf s) <= (length a) \/
              (length_max_sf s) > (length a)) by omega.
  destruct H3 as [H3 | H3].
  + apply leb_correct in H3.
    rewrite H3 in H2.
    rewrite H2 in H3.
    rewrite H2.
    assert (H4: (length_max (all_rules_match a0 s)) <= n). 
      {
      apply length_max_all_rules_match_le.
      apply leb_complete in H3.
      exact H3.
      }
    apply leb_correct in H4.
    rewrite H4.
    reflexivity.
  + apply leb_correct_conv in H3.
    rewrite H3 in H2.
    assert (H4: (length_max (all_rules_match a0 s)) > (length a)).
      {
      apply leb_complete_conv in H3. 
      apply length_max_all_rules_match_gt.
      exact H3. 
      }
    apply leb_correct_conv in H4.
    rewrite H4.
    apply IHs.
    exact H2.
Qed.

Lemma all_rules_match_not_nil:
forall l: slist,
forall a: non_terminal,
all_rules_match a l <> [] ->
l <> [].
Proof.
destruct l.
- intros a H.
  simpl in H.
  destruct H.
  reflexivity.
- intros a0 H.
  apply not_eq_sym.
  apply nil_cons.
Qed.

Definition all_rules_left (n: nat) (nt: non_terminal) (v: vlist): rlist:=
all_rules_match nt (all_sf_with n v).

Lemma all_rules_left_correct:
forall n: nat,
forall l: non_terminal,
forall v: vlist,
forall r: sf,
(forall e: symbol, In e r -> In e v) ->
length r = n ->
In (l, r) (all_rules_left n l v).
Proof.
intros n l v r H1 H2.
unfold all_rules_left.
apply all_rules_match_correct.
apply all_sf_with_correct.
- exact H1.
- exact H2.
Qed.

Lemma all_rules_left_length_correct_aux:
forall l: non_terminal,
forall r: sf,
forall n: nat,
forall v: vlist,
In (l, r) (all_rules_left n l v) ->
In r (all_sf_with n v).
Proof.
intros l r n v H.
unfold all_rules_left in H.
induction (all_sf_with n v).
- simpl in H.
  contradiction.
- simpl in H.
  simpl.
  destruct H as [H | H].
  + inversion H.
    left.
    reflexivity.
  + right.
    apply IHl0.
    exact H.
Qed.

Lemma all_rules_left_length_correct:
forall n: nat,
forall v: vlist,
forall l: non_terminal,
forall r: sf,
In (l, r) (all_rules_left n l v) ->
length r = n.
Proof.
induction n.
- intros v l r H. 
  simpl in H.
  destruct H as [H | H].
  + inversion H.
    simpl.
    reflexivity.
  + contradiction.
- intros v l r H.
  apply all_rules_left_length_correct_aux in H.
  apply all_sf_with_length_correct in H. 
  exact H.
Qed. 

Lemma all_rules_left_length_max_correct:
forall n: nat,
forall a: non_terminal,
forall v: vlist,
n = 0 \/ v <> [] ->
length_max (all_rules_left n a v) = n.
Proof.
unfold all_rules_left.
intros n a v H.
apply all_rules_match_length_max_correct.
apply all_sf_with_length_max_correct.
exact H.
Qed.

Lemma all_rules_left_not_nil:
forall n: nat,
forall a: non_terminal,
forall v: vlist,
all_rules_left n a v <> [] ->
n = 0 \/ n >= 1 /\ v <> [].
Proof.
unfold all_rules_left.
intros n a v H.
destruct n, v.
- left. 
  reflexivity.
- left.
  reflexivity.
- simpl in H.
  destruct H.
  reflexivity.
- right.
  apply all_rules_match_not_nil in H.
  apply all_sf_with_not_nil_inv in H.
  destruct H as [H | H].
  + omega. 
  + split.
    * omega. 
    * exact H. 
Qed.

Fixpoint all_rules_with (n: nat) (nl: nlist) (v: vlist): rlist:=
match nl with
| [] => []
| nt :: nl' => (all_rules_left n nt v) ++ (all_rules_with n nl' v)
end.

Lemma all_rules_with_correct:
forall n: nat,
forall nl: nlist,
forall v: vlist,
forall l: non_terminal,
forall r: sf,
In l nl ->
(forall e: symbol, In e r -> In e v) ->
length r = n ->
In (l, r) (all_rules_with n nl v).
Proof.
intros n nl.
generalize dependent n.
induction nl.
- intros n v l r H0 H' H.
  simpl in H.
  contradiction.
- intros n v l r H0 H1 H2.
  simpl in H0.
  simpl.
  apply in_or_app.
  destruct H0 as [H0 | H0].
  + subst.
    left.
    apply all_rules_left_correct.
    * exact H1.
    * reflexivity.
  + right.
    apply IHnl.
    * exact H0.
    * exact H1.
    * exact H2.
Qed.

Lemma all_rules_with_length_correct_aux:
forall l1 l2: non_terminal,
forall r: sf,
forall n: nat,
forall v: vlist,
In (l1, r) (all_rules_left n l2 v) ->
l1 = l2.
Proof.
intros l1 l2 r n v H.
unfold all_rules_left in H.
induction (all_sf_with n v).
- simpl in H.
  contradiction.
- simpl in H.
  destruct H as [H | H].
  + inversion H.
    reflexivity.
  + apply IHl.
    exact H.
Qed.

Lemma all_rules_with_length_correct:
forall nl: nlist,
forall n: nat,
forall v: vlist,
forall l: non_terminal,
forall r: sf,
In (l, r) (all_rules_with n nl v) ->
length r = n.
Proof.
induction nl.
- intros n v l r H.
  simpl in H.
  contradiction.
- intros n v l r H.
  simpl in H.
  apply in_app_or in H.
  destruct H as [H | H].
  + assert (H1: l = a).
      {
      apply all_rules_with_length_correct_aux in H.
      exact H.
      }
    subst.
    apply all_rules_left_length_correct in H.
    exact H.
  + apply IHnl with (l:= l) (v:= v).
    exact H.
Qed.

Lemma all_rules_with_length_max_correct:
forall nl: nlist,
forall v: vlist,
forall n: nat,
nl <> [] ->
v <> [] ->
length_max (all_rules_with n nl v) = n.
Proof.
induction nl.
- intros v n H. 
  destruct H. 
  reflexivity. 
- intros v n H1 H2.
  simpl.
  rewrite length_max_max.
  rewrite all_rules_left_length_max_correct.
  + assert (H3: nl = [] \/ nl <> []).
     {
     apply nil_not_nil. 
     }
   destruct H3 as [H3 | H3].
   * subst.
     simpl. 
     apply max_n_0.
   * {
     rewrite IHnl.
     - apply max_n_n.
     - exact H3. 
     - exact H2.
     }
  + right.
    exact H2.
Qed.

Fixpoint all_rules_up_to (n: nat) (nl: nlist) (v: vlist): rlist:=
match n with
| O => all_rules_with 0 nl v
| S n' => (all_rules_with n nl v) ++ (all_rules_up_to n' nl v)
end. 

Lemma all_rules_up_to_nil:
forall n: nat,
forall v: vlist,
all_rules_up_to n [] v = [].
Proof.
induction n.
- intros v.
  simpl.
  reflexivity.
- intros v.
  simpl.
  apply IHn.
Qed.

Lemma all_rules_up_to_correct:
forall n: nat,
forall nl: nlist,
forall v: vlist,
forall l: non_terminal,
forall r: sf,
In l nl ->
(forall e: symbol, In e r -> In e v) ->
length r <= n ->
In (l, r) (all_rules_up_to n nl v).
Proof.
induction n.
- intros nl v l r H0 H1 H2.
  assert (H3: length r = 0) by omega.
  clear H2.
  apply length_zero in H3.
  subst.
  simpl.
  apply all_rules_with_correct.
  + exact H0.
  + exact H1.
  + simpl.
    reflexivity.
- intros nl v l r H0 H1 H2.
  simpl. 
  apply in_or_app.
  assert (H3: length r = S n \/ length r <= n) by omega.
  clear H2.
  destruct H3 as [H3 | H3].
  + left.
    apply all_rules_with_correct.
    * exact H0.
    * exact H1.
    * exact H3.
  + right.
    apply IHn.
    * exact H0.
    * exact H1.
    * exact H3. 
Qed.

Lemma all_rules_up_to_length_correct:
forall n: nat,
forall nl: nlist,
forall v: vlist,
forall l: non_terminal,
forall r: sf,
In (l, r) (all_rules_up_to n nl v) ->
length r <= n.
Proof.
induction n.
- intros nl v l r H.
  simpl in H.
  apply all_rules_with_length_correct in H.
  omega.
- intros nl v l r H.
  simpl in H.
  apply in_app_or in H.
  destruct H as [H | H].
  + apply all_rules_with_length_correct in H.
    omega.
  + specialize (IHn nl v l r H).
    omega.
Qed.

Lemma all_rules_up_to_length_max_correct:
forall n: nat,
forall nl: nlist,
forall v: vlist,
nl <> [] ->
v <> [] ->
length_max (all_rules_up_to n nl v) = n.
Proof.
induction n.
- intros nl v H1 H2.
  simpl.
  apply all_rules_with_length_max_correct.
  + exact H1.
  + exact H2.
- intros nl v Ha Hb.
  simpl. 
  assert (H1: length_max (all_rules_with (S n) nl v) > length_max (all_rules_up_to n nl v)).
    {
    rewrite all_rules_with_length_max_correct. 
    - rewrite IHn.
      + omega.
      + exact Ha.
      + exact Hb.
    - exact Ha.
    - exact Hb.
    }
  assert (H2: length_max (all_rules_with (S n) nl v ++ all_rules_up_to n nl v) =
              length_max (all_rules_with (S n) nl v)).
    {
    apply length_max_or.
    left.
    split.
    - reflexivity.
    - omega.
    }
  rewrite H2.
  apply all_rules_with_length_max_correct.
  + exact Ha.
  + exact Hb.
Qed.

Definition all_rules (rl: rlist) (n: nat): rlist:=
all_rules_up_to n (all_non_terminals rl) (all_symbols rl).

Lemma all_rules_correct:
forall left: non_terminal,
forall right: sf,
forall n: nat,
forall rl: rlist,
In left (all_non_terminals rl) ->
(forall e: symbol, In e right -> In e (all_symbols rl)) ->
length right <= n ->
In (left,right) (all_rules rl n).
Proof.
intros left right n rl H1 H2 H3.
unfold all_rules.
apply all_rules_up_to_correct.
- exact H1.
- exact H2.
- exact H3.
Qed.

Lemma all_rules_nil:
forall n: nat,
forall rl: rlist,
rl = [] -> 
all_rules rl n = [].
Proof.
unfold all_rules.
induction n.
- intros rl H.
  subst.
  simpl.
  reflexivity.
- intros rl H.
  subst.
  simpl all_non_terminals.
  apply all_rules_up_to_nil. 
Qed.

Lemma all_rules_length_correct:
forall n: nat,
forall rl: rlist,
forall l: non_terminal,
forall r: sf,
In (l, r) (all_rules rl n) ->
length r <= n.
Proof.
intros n rl l r H.
unfold all_rules in H.
apply all_rules_up_to_length_correct in H.
exact H.
Qed.

Lemma all_rules_length_max_correct:
forall rl: list (non_terminal * sf),
forall n: nat,
rl <> [] ->
length_max (all_rules rl n) = n.
Proof.
unfold all_rules.
intros rl n H.
rewrite all_rules_up_to_length_max_correct.
- reflexivity.
- apply all_non_terminals_not_nil.
  exact H.
- apply all_symbols_not_nil. 
  exact H.
Qed.

Lemma in_rl_left_in_all_non_terminals:
forall left: non_terminal,
forall right: sf,
forall rl: rlist,
In (left, right) rl ->
In left (all_non_terminals rl).
Proof.
intros left right.
induction rl.
- intros H.
  simpl in H.
  contradiction.
- intros H.
  apply all_non_terminals_correct with (left:= left) (right:= right).
  + left. 
    reflexivity. 
  + exact H. 
Qed.

Lemma not_nt_t:
forall n: non_terminal,
forall rl: rlist,
~ In (inl n) (map tpair (all_terminals rl)).
Proof.
intros n rl.
generalize dependent n.
induction rl.
- intros n H.
  simpl in H.
  contradiction.
- change (a :: rl) with ([a] ++ rl).
  rewrite all_terminals_app.
  intros n H1.
  specialize (IHrl n).
  destruct a as (l, r).
  rewrite map_app in H1. 
  apply in_app_or in H1.
  destruct H1 as [H1 | H1].
  + simpl in H1.
    rewrite app_nil_r in H1.
    induction r.
    * simpl in H1.
      contradiction.
    * apply IHr.
      change (a :: r) with ([a] ++ r) in H1.
      rewrite all_terminals_sf_app in H1.
      rewrite map_app in H1.
      apply in_app_or in H1.
      {
      destruct H1 as [H1 | H1].
      - destruct a.
        + simpl in H1.
          contradiction.
        + simpl in H1.
          destruct H1 as [H1 | H1].
          * inversion H1.
          * contradiction.
      - specialize(IHr H1).
        contradiction.
      }
  + specialize (IHrl H1).
    contradiction.
Qed.

Lemma not_t_nt:
forall t: terminal,
forall rl: rlist,
~ In (inr t) (map npair (all_non_terminals rl)).
Proof.
intros t rl.
generalize dependent t.
induction rl.
- intros t H.
  simpl in H.
  contradiction.
- change (a :: rl) with ([a] ++ rl).
  rewrite all_non_terminals_app.
  intros t H1.
  specialize (IHrl t).
  destruct a as (l, r).
  rewrite map_app in H1. 
  apply in_app_or in H1.
  destruct H1 as [H1 | H1].
  + simpl in H1.
    destruct H1 as [H1 | H1].
    * inversion H1.
    * rewrite app_nil_r in H1.
      {
      induction r.
      - simpl in H1.
        contradiction.
      - apply IHr.
        change (a :: r) with ([a] ++ r) in H1.
        rewrite all_non_terminals_sf_app in H1.
        rewrite map_app in H1.
        apply in_app_or in H1.
        destruct H1 as [H1 | H1].
        + destruct a.
          * simpl in H1.
            {
            destruct H1 as [H1 | H1].
            - inversion H1.
            - contradiction. 
            }
          * simpl in H1.
            contradiction.
        + exact H1.
      }
  + specialize (IHrl H1).
    contradiction.
Qed.

Lemma in_rl_in_all_symbols:
forall left: non_terminal,
forall right: sf,
forall rl: rlist,
In (left, right) rl ->
forall e : non_terminal + terminal, In e right -> In e (all_symbols rl).
Proof.
intros left right.
generalize dependent right.
generalize dependent left.
induction rl.
- intros H.
  simpl in H.
  contradiction.
- intros H1 e H2.
  destruct a.
  simpl in H1.
  change ((n, l) :: rl) with ([(n, l)] ++ rl).
  unfold all_symbols.
  apply in_or_app.
  destruct H1 as [H1 | H1].
  + inversion H1. 
    apply in_split in H2. 
    destruct H2 as [l1 [l2 H4]].
    subst.
    destruct e.
    * right.   
      simpl.
      right. 
      rewrite all_non_terminals_sf_app.
      rewrite map_app.
      apply in_or_app.
      left.
      rewrite map_app.
      apply in_or_app.
      right.
      simpl. 
      left. 
      unfold npair.
      reflexivity.
    * left.
      rewrite all_terminals_app.
      rewrite map_app.
      apply in_or_app.
      left. 
      simpl. 
      rewrite app_nil_r.
      rewrite all_terminals_sf_app.
      rewrite map_app.
      apply in_or_app.
      right.
      simpl. 
      left.
      unfold tpair.
      reflexivity.
  + destruct e.
    * right.
      rewrite all_non_terminals_app.
      rewrite map_app.
      apply in_or_app.
      right.
      specialize (IHrl H1 (inl n0) H2).
      unfold all_symbols in IHrl.
      apply in_app_or in IHrl.
      {
      destruct IHrl as [IHrl | IHrl].
      - apply not_nt_t in IHrl.
        contradiction.
      - exact IHrl.
      }
    * left.
      rewrite all_terminals_app.
      rewrite map_app.
      apply in_or_app.
      right.
      specialize (IHrl H1 (inr t) H2).
      unfold all_symbols in IHrl.
      apply in_app_or in IHrl.
      {
      destruct IHrl as [IHrl | IHrl].
      - exact IHrl. 
      - apply not_t_nt in IHrl.
        contradiction.
      }
Qed.

Lemma in_npair_in_all_non_terminals:
forall rl: rlist,
forall e: non_terminal,
In (inl e) (map npair (all_non_terminals rl)) ->
In e (all_non_terminals rl).
Proof.
intros rl e H1.
apply in_split in H1.
destruct H1 as [l1 [l2 H1]].
symmetry in H1.
apply map_expand in H1.
destruct H1 as [s1' [s2' [H2 [H3 H4]]]].
change (inl e :: l2) with ([inl e] ++ l2) in H4.
symmetry in H4.
apply map_expand in H4.
destruct H4 as [s1'0 [s2'0 [H5 [H6 H7]]]].
destruct s1'0.
- simpl in H6.
  inversion H6.
- simpl in H6.
  inversion H6.
  subst.
  rewrite H2.
  apply in_or_app.
  right.
  apply in_or_app.
  left.
  simpl.
  left.
  reflexivity.
Qed.

Lemma in_rl_right_in_all_non_terminals:
forall left: non_terminal,
forall right: sf,
forall rl: rlist,
In (left, right) rl ->
forall e : non_terminal, In (inl e) right -> In e (all_non_terminals rl).
Proof.
intros left right rl H1.
assert (H2: forall e : non_terminal + terminal, In e right -> In e (all_symbols rl)).
  {
  apply in_rl_in_all_symbols with (left:= left).
  exact H1.
  }
intros e H3.
specialize (H2 (inl e) H3).
unfold all_symbols in H2.
apply in_app_or in H2.
destruct H2 as [H2 | H2].
- apply not_nt_t in H2.
  contradiction. 
- apply in_npair_in_all_non_terminals. 
  exact H2.
Qed.

End AllRules.
