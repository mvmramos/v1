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
(* CHOMSKY NORMAL FORM                                                   *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.
Require Import inaccessible.
Require Import useless.
Require Import unitrules.
Require Import emptyrules.
Require Import simplification.
Require Import allrules.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* DEFINITIONS                                                           *)
(* --------------------------------------------------------------------- *)

Section Chomsky_Definitions_1.

Variables non_terminal terminal: Type.

Notation sf:= (list (non_terminal + terminal)).

Definition is_cnf_rule (left: non_terminal) (right: sf): Prop:=
(exists s1 s2: non_terminal, right = [inl s1; inl s2]) \/
(exists t: terminal, right = [inr t]).

Definition is_cnf (g: cfg non_terminal terminal): Prop:=
forall left: non_terminal,
forall right: sf,
rules g left right -> is_cnf_rule left right.

Definition is_cnf_with_empty_rule (g: cfg non_terminal terminal): Prop:=
forall left: non_terminal,
forall right: sf,
rules g left right ->
(left = (start_symbol g) /\ right = []) \/
is_cnf_rule left right.

End Chomsky_Definitions_1.

Section Chomsky_Definitions_2.

Variables non_terminal terminal: Type.

Notation sentence := (list terminal).
Notation sf := (list (non_terminal + terminal)).
Notation ntlist:= (list non_terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation symbol:= (non_terminal + terminal)%type.
Notation slist:= (list sf).
Notation vlist:= (list symbol).

Inductive non_terminal': Type:=
| Lift_r: sf -> non_terminal'.

Notation sf':= (list (non_terminal' + terminal)).
Notation ntlist':= (list non_terminal').
Notation tlist:= (list terminal).

Definition non_terminal_lift (n: non_terminal): (non_terminal + terminal):= inl n.
Definition non_terminal'_lift (n: non_terminal'): (non_terminal' + terminal):= inl n.
Definition terminal_lift' (t: terminal): (non_terminal' + terminal):= inr t.
Definition symbol_lift (s: non_terminal + terminal): non_terminal' + terminal:=
match s with
| inr t => inr t
| inl n => inl (Lift_r [inl n])
end.

Inductive g_cnf_rules (g: cfg non_terminal terminal): non_terminal' -> sf' -> Prop:=
| Lift_cnf_t:  forall t: terminal,
               forall left: non_terminal,
               forall s1 s2: sf,
               rules g left (s1++[inr t]++s2) ->
               g_cnf_rules g (Lift_r [inr t]) [inr t]
| Lift_cnf_1:  forall left: non_terminal,
               forall t: terminal,
               rules g left [inr t] ->
               g_cnf_rules g (Lift_r [inl left]) [inr t]
| Lift_cnf_2:  forall left: non_terminal,
               forall s1 s2: symbol,
               forall beta: sf,
               rules g left (s1 :: s2 :: beta) ->
               g_cnf_rules g (Lift_r [inl left]) [inl (Lift_r [s1]); inl (Lift_r (s2 :: beta))]
| Lift_cnf_3:  forall left: sf,
               forall s1 s2 s3: symbol,
               forall beta: sf,
               g_cnf_rules g (Lift_r left) [inl (Lift_r [s1]); inl (Lift_r (s2 :: s3 :: beta))] ->
               g_cnf_rules g (Lift_r (s2 :: s3 :: beta)) [inl (Lift_r [s2]); inl (Lift_r (s3 :: beta))].

(* --------------------------------------------------------------------- *)
(* ALL NTS (non-terminals)                                               *)
(* --------------------------------------------------------------------- *)

Fixpoint all_nts (l: slist): ntlist':=
match l with
| [] => []
| s :: l' => Lift_r s :: all_nts l'
end. 

Lemma all_nts_app:
forall l1 l2: slist,
all_nts (l1 ++ l2) = all_nts l1 ++ all_nts l2.
Proof.
induction l1.
- simpl. 
  reflexivity.
- intros l2.
  simpl.  
  rewrite (IHl1 l2).
  reflexivity.
Qed.

Lemma all_nts_single:
forall s: symbol,
forall l1 l2: vlist,
forall n: nat,
n >= 1 ->
In (Lift_r [s]) (all_nts (all_sf_up_to n (l1 ++ s :: l2))).
Proof.
intros s l1 l2 n.
revert l2.
revert l1.
revert s.
induction n.
- intros s l1 l2 H1.
  omega.
- intros s l1 l2 H1.
  assert (H2: n = 0 \/ n >= 1) by omega.
  destruct H2 as [H2 | H2].
  + subst. 
    simpl.
    rewrite all_nts_app.
    apply in_or_app.
    left.
    rewrite concat_list_app_left. 
    rewrite all_nts_app.
    apply in_or_app.
    right.
    simpl.
    left.
    reflexivity.
  + simpl. 
    rewrite all_nts_app.
    apply in_or_app.
    right.
    apply IHn.
    exact H2.
Qed.

Fixpoint all_nts_up_to (n: nat) (v: vlist): ntlist':=
match n with
| 0 => [Lift_r []]
| S n' => all_nts (all_sf_with n v) ++ all_nts_up_to n' v
end.

Lemma all_nts_up_to_correct_aux:
forall n: nat,
forall s: symbol,
forall v: vlist,
forall s0: sf,
In s v ->
In s0 (all_sf_with n v) -> 
In (Lift_r (s :: s0)) (all_nts (concat_list v (all_sf_with n v))).
Proof.
induction n.
- intros s v s0 H1 H2.
  simpl in H2.
  destruct H2 as [H2 | H2].
  + subst. 
    simpl.
    apply in_split in H1.
    destruct H1 as [l1 [l2 H1]].
    subst.
    assert (H: In [s] (concat_list (l1 ++ s :: l2) [[]])).
      {
      apply concat_list_empty.
      }
    apply in_split in H.
    destruct H as [l0 [l3 H]].
    rewrite H.
    rewrite all_nts_app.
    apply in_or_app.
    right.
    simpl.
    left.
    reflexivity.
  + contradiction.
- intros s v s0 H1 H2.
  simpl.
  simpl in H2.
  apply in_split in H2.
  destruct H2 as [l1 [l2 H2]].
  rewrite H2.
  apply in_split in H1.
  destruct H1 as [l1' [l2' H1]].
  rewrite H1.
  assert (H3: In (s :: s0) (concat_list (l1' ++ s :: l2') (l1 ++ s0 :: l2))).
    {
    apply concat_list_non_empty.
    }
  apply in_split in H3.
  destruct H3 as [l0 [l3 H3]].
  rewrite H3.
  rewrite all_nts_app.
  apply in_or_app.
  right.
  simpl.
  left.
  reflexivity.
Qed.

Lemma all_nts_up_to_correct:
forall n: nat,
forall s: sf,
forall v: vlist,
(forall e: symbol, In e s -> In e v) ->
length s <= n ->
In (Lift_r s) (all_nts_up_to n v).
Proof.
induction n.
- intros s v H1 H2.
  assert (length s = 0) by omega.
  apply length_zero in H.
  subst.
  simpl.
  left.
  reflexivity.
- intros s v H1 H2.
  simpl.
  apply in_or_app.
  assert (H3: length s = S n \/ length s <= n) by omega.
  clear H2.
  destruct H3 as [H3 | H3].
  + left. 
    destruct s. 
    * simpl in H3. 
      omega. 
    * {
      apply all_nts_up_to_correct_aux.
      - apply H1.
        simpl.
        left.
        reflexivity.
      - simpl in H3.
        apply eq_add_S in H3.
        apply all_sf_with_correct.
        + intros e H4.
          apply H1.
          simpl. 
          right. 
          exact H4.
        + exact H3.
      }
  + right.
    apply IHn.
    * exact H1.
    * exact H3. 
Qed.

Lemma rules_g_cnf_to_rules_g_right:
forall g: cfg _ _,
forall right2: sf,
forall n1 n2: non_terminal',
forall s1 s2: symbol,
g_cnf_rules g n1 [inl n2; inl (Lift_r (s1 :: s2 :: right2))] ->
exists left: non_terminal,
exists right1: sf,
rules g left (right1 ++ s1 :: s2 :: right2).
Proof.
intros g right2 n1 n2 s1 s2 H.
remember [inl n2; inl (Lift_r (s1 :: s2 :: right2))] as w.
generalize n2 s1 s2 right2 Heqw.
clear n2 s1 s2 right2 Heqw.
induction H.
- intros n2 s1' s2' right2 H'.
  inversion H'.
- intros n2 s1' s2' right2 H2'.
  inversion H2'.
- intros n2 s0 s3 right2 H2.
  inversion H2.
  destruct n2.
  inversion H1.
  destruct beta.
  + inversion H4.
  + inversion H4.
    subst.
    exists left.
    exists [s1].
    exact H.
- intros n2 s0 s4 right2 H1.
  inversion H1.
  destruct n2.
  destruct beta.
  + inversion H4.
  + inversion H4.
    subst.
    inversion H1.
    subst.
    clear H H1 H2 H4.
    specialize (IHg_cnf_rules (Lift_r [s1]) s2 s0 (s4 :: right2)).
    specialize (IHg_cnf_rules (eq_refl ([inl (Lift_r [s1]); inl (Lift_r (s2 :: s0 :: s4 :: right2))]))).
    destruct IHg_cnf_rules as [left0 [right1 H]].
    exists left0.
    exists (right1 ++ [s2]).
    rewrite <- app_assoc.
    exact H.
Qed.

Lemma rules_g_cnf_to_rules_g_left:
forall g: cfg _ _,
forall s1: sf,
forall s2: sf',
g_cnf_rules g (Lift_r s1) s2 ->
(exists t: terminal, s1 = [inr t]
  /\ exists left s1 s2, rules g left (s1++[inr t]++s2)
) \/
(exists n: non_terminal, s1 = [inl n]
  /\ exists right, rules g n right
) \/
(exists left: non_terminal,
 exists right s3 s4: sf,
 rules g left right /\
 right = s3 ++ s1 ++ s4).
Proof.
intros g s1 s2 H.
inversion H.
- subst.
  left.
  exists t.
  split; [reflexivity|].
  eauto.
- subst.
  right.
  left.
  exists left.
  split; [reflexivity|eauto].
- subst.
  right.
  left.
  exists left.
  split; [reflexivity|eauto].
- subst.
  right.
  right.
  apply rules_g_cnf_to_rules_g_right in H1.
  destruct H1 as [left0 [right1 H1]].
  exists left0.
  exists (right1 ++ s3 :: s4 :: beta).
  exists right1.
  exists (@nil (non_terminal + terminal)).
  split.
  + exact H1.
  + rewrite app_nil_r.
    reflexivity.
Qed.

Lemma g_cnf_right_formats:
forall g: cfg _ _,
forall left: non_terminal',
forall right: sf',
g_cnf_rules g left right ->
(exists t: terminal, right = [inr t]) \/
(exists s1: symbol, 
 exists s: sf,
 right = [inl (Lift_r [s1]); inl (Lift_r s)]).
Proof.
intros g left right H.
inversion H.
- subst.
  left.
  exists t.
  reflexivity.
- subst.
  left.
  exists t.
  reflexivity.
- subst.
  right.
  destruct s1.
  + exists (inl terminal n).
    exists (s2 :: beta).
    simpl. 
    reflexivity.
  + exists (inr non_terminal t).
    exists (s2 :: beta).
    simpl. 
    reflexivity.
- subst.
  right.
  destruct s2.
  + exists (inl terminal n).
    exists (s3 :: beta).
    simpl.
    reflexivity.
  + exists (inr non_terminal t).
    exists (s3 :: beta).
    simpl.
    reflexivity.
Qed.

Lemma is_cnf_right_formats_v1:
forall g: cfg non_terminal' terminal,
forall left: non_terminal',
forall right: sf',
is_cnf g ->
rules g left right ->
(exists t: terminal, right = [inr t]) \/
(exists s1 s2: sf, 
 right = [inl (Lift_r s1); inl (Lift_r s2)]).
Proof.
intros g left right H1 H2.
specialize (H1 left right H2).
destruct H1 as [H1 | H1].
- destruct H1 as [s1 [s2 H1]].
  right.
  destruct s1, s2.
  exists l.
  exists l0.
  exact H1.
- destruct H1 as [t H1].
  left.
  exists t.
  exact H1.
Qed.

Lemma cnf_rules_not_empty:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sf,
is_cnf g \/ is_cnf_with_empty_rule g ->
n <> start_symbol g ->
rules g n s ->
s <> [].
Proof.
intros g n s H1 H2 H3.
destruct H1 as [H1 | H1].
- specialize (H1 n s H3).
  destruct H1 as [H1 | H1].
  + destruct H1 as [s1 [s2 H1]].
    rewrite H1.
    apply not_eq_sym.
    apply nil_cons.
  + destruct H1 as [t H1].
    rewrite H1.
    apply not_eq_sym.
    apply nil_cons. 
- specialize (H1 n s H3).
  destruct H1 as [H1 | H1].
  + destruct H1 as [H1 _].
    contradiction.
  + destruct H1 as [H1 | H1].
    * destruct H1 as [s1 [s2 H1]].
      rewrite H1.
      apply not_eq_sym.
      apply nil_cons. 
    * destruct H1 as [t H1].
      rewrite H1.
      apply not_eq_sym.
      apply nil_cons. 
Qed.

Lemma cnf_derives_not_empty:
forall g: cfg _ _,
forall s1 s2: sf,
is_cnf g \/ is_cnf_with_empty_rule g ->
start_symbol_not_in_rhs g ->
~ In (inl (start_symbol g)) s1 ->
s1 <> [] ->
derives g s1 s2 ->
s2 <> [].
Proof.
intros g s1 s2 H1 H2 H3 H4 H5.
apply derives_equiv_derives6 in H5.
destruct H5 as [n0 H5].
revert s1 s2 H3 H4 H5.
induction n0.
- intros n s H3 H4 H5.
  inversion H5.
  subst.
  exact H4.
- intros s1 s2 H3 H4 H5.
  inversion H5.
  subst.
  clear H4 H5.
  specialize (IHn0 (s0 ++ right ++ s3) s2).
  assert (H7: ~ In (inl (start_symbol g)) (s0 ++ right ++ s3)).
    {
    intros H4. 
    apply H3. 
    apply in_app_or in H4.
    destruct H4 as [H4 | H4].
    - apply in_or_app.
      left.
      exact H4.
    - apply in_app_or in H4.
      destruct H4 as [H4 | H4].
      + specialize (H2 left right H0).
        contradiction.
      + apply in_or_app.
        right.
        apply in_or_app.
        right.
        exact H4.
    }
  assert (H8: right <> []).
    {
    destruct H1 as [H1 | H1].
    - specialize (H1 left right H0). 
      destruct H1 as [H1 | H1].
      + destruct H1 as [s1' [s2' H1]].
        rewrite H1.
        apply not_eq_sym.
        apply nil_cons.
      + destruct H1 as [t H1].
        rewrite H1.
        apply not_eq_sym.
        apply nil_cons.
    - specialize (H1 left right H0).
      destruct H1 as [H1 | H1].
      + destruct H1 as [H1a H1b].
        subst.
        intros _.
        apply H3.
        apply in_or_app.
        right.
        simpl.
        left.
        reflexivity.
      + destruct H1 as [H1 | H1].
        * destruct H1 as [s1' [s2' H1]].
          rewrite H1.
          apply not_eq_sym.
          apply nil_cons.
        * destruct H1 as [t H1].
          rewrite H1.
          apply not_eq_sym.
          apply nil_cons.
    }
  assert (H9: s0 ++ right ++ s3 <> []).
    {
    apply app_not_nil_inv.
    right.
    apply app_not_nil_inv.
    left.
    exact H8.
    }
  specialize (IHn0 H7 H9 H6).
  exact IHn0.  
Qed.

Lemma is_cnf_right_formats_v2:
forall g: cfg non_terminal' terminal,
forall left: non_terminal',
forall right: sf',
is_cnf g \/ is_cnf_with_empty_rule g ->
rules g left right ->
right <> [] ->
(exists t: terminal, right = [inr t]) \/
(exists s1 s2: sf, 
 right = [inl (Lift_r s1); inl (Lift_r s2)]).
Proof.
intros g left right H1 H2 H3.
destruct H1 as [H1 | H1].
- specialize (H1 left right H2).
  destruct H1 as [H1 | H1].
  + destruct H1 as [s1 [s2 H1]].
    right.
    destruct s1, s2.
    exists l.
    exists l0.
    exact H1.
  + destruct H1 as [t H1].
    left.
    exists t.
    exact H1.
- specialize (H1 left right H2). 
  destruct H1 as [H1 | H1]. 
  + destruct H1 as [H1 H4].
    contradiction.
  + destruct H1 as [H1 | H1]. 
    * destruct H1 as [s1 [s2 H1]].
      right.
      destruct s1, s2.
      exists l, l0.
      exact H1.
    * destruct H1 as [t H1].
      left.
      exists t.
      exact H1.
Qed.

Lemma g_cnf_finite:
forall g: cfg non_terminal terminal,
exists n: nat,
exists ntl: ntlist',
exists tl: tlist,
In (Lift_r [inl (start_symbol g)]) ntl /\
forall left: non_terminal',
forall right: sf',
g_cnf_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal', In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
intros g.
destruct (rules_finite g) as [n [ntl [tl H1]]].
exists 2.
exists (all_nts_up_to (S n) (map non_terminal_lift ntl ++ map term_lift tl)).
exists tl.
split.
- (* start_symbol is in the list *)
  destruct H1 as [H1 _].
  apply all_nts_up_to_correct.
  + intros e H2.
    simpl in H2.
    destruct H2 as [H2 | H2].
    * subst.
      apply in_or_app.
      left.
      apply in_map.
      exact H1.
    * contradiction.
  + simpl.
    omega.
- split.
  + (* length rhs <= 2 *)
    inversion H. 
    * simpl. 
      omega.
    * simpl. 
      omega.
    * simpl. 
      omega.
    * simpl. 
      omega.
  + split.
    * (* non-terminals in the lhs are in the list *)
      destruct left.
      {
      apply all_nts_up_to_correct.
      - intros e H2.
        apply rules_g_cnf_to_rules_g_left in H.
        destruct H as [H | [H | H]].
        + destruct H as [t [H [left [s1 [s2 Hg]]]]].
          subst.
          simpl in H2.
          destruct H2 as [H2 | H2].     
          * subst.
            apply in_or_app; right.
            apply in_map.
            destruct H1 as [_ H1].
            specialize (H1 left (s1 ++ [inr t] ++ s2) Hg).
            apply H1.
            apply in_or_app.
            right.
            simpl.
            left.
            reflexivity.
          * contradiction.
        + destruct H as [n0 [H [r Hright]]].
          subst.
          simpl in H2.
          destruct H2 as [H2 | H2].     
          * subst.
            unfold rules_finite_def in H1.
            apply in_or_app; left.
            apply in_map.
            destruct H1 as [_ H1].
            specialize (H1 n0 r Hright).
            destruct H1 as [_ [H1 _]].
            exact H1.
          * contradiction.
        + destruct H as [left [right0 [s3 [s4 [H3 H4]]]]].
          apply in_split in H2.
          destruct H2 as [l1 [l2 H2]].
          subst.
          rewrite <- app_assoc in H3.
          unfold rules_finite_def in H1.
          destruct H1 as [_ H1].
          specialize (H1 left (s3 ++ l1 ++ (e :: l2) ++ s4) H3).
          destruct H1 as [_ [_ [H1 H2]]].
          destruct e.
          * apply in_or_app.
            left. 
            apply in_map.
            apply H1.
            apply in_or_app.
            right.
            apply in_or_app.
            right.
            simpl.
            left.
            reflexivity.
          * apply in_or_app.
            right. 
            apply in_map.
            apply H2.
            apply in_or_app.
            right.
            apply in_or_app.
            right.
            simpl.
            left.
            reflexivity.
      - apply rules_g_cnf_to_rules_g_left in H.
        destruct H as [H | [H | H]].
        + destruct H as [t [H _]].
          subst.
          simpl. 
          omega.
        + destruct H as [n0 [H _]].
          subst.
          simpl. 
          omega.
        + destruct H as [left [right0 [s3 [s4 [H H2]]]]].
          subst.
          unfold rules_finite_def in H1.
          destruct H1 as [_ H1].
          specialize (H1 left (s3 ++ l ++ s4) H).
          destruct H1 as [H1 _].
          repeat rewrite app_length in H1.
          omega.
      }
    * {
      split.
      - (* non-terminals in the rhs are in the list *)
        destruct H1 as [_ H1].
        inversion H.
        + subst.
          intros s H2.
          simpl in H2.
          destruct H2 as [H2 | H2].
          * inversion H2.
          * contradiction.
        + subst.
          intros s H2.
          simpl in H2.
          destruct H2 as [H2 | H2].
          * inversion H2.
          * contradiction.
        + subst.
          intros s H2.
          simpl in H2.
          destruct H2 as [H2 | [H2 | H2]].
          * inversion H2.
            {
            apply all_nts_up_to_correct.
            - intros e H5.
              destruct e, s1.
              + simpl in H5.
                destruct H5 as [H5 | H5].
                * inversion H5.
                  subst.
                  apply in_or_app.
                  left.
                  apply in_map.
                  specialize (H1 left0 (inl n0 :: s2 :: beta) H0).
                  destruct H1 as [_ [_ [H1 _]]].
                  apply H1.
                  simpl. 
                  left.
                  reflexivity.
                * contradiction.
              + simpl in H5.
                destruct H5 as [H5 | H5].
                * inversion H5.
                * contradiction.
              + simpl in H5.
                destruct H5 as [H5 | H5].
                * inversion H5.
                * contradiction.
              + simpl in H5.
                destruct H5 as [H5 | H5].
                * inversion H5.
                  subst.
                  apply in_or_app.
                  right.
                  apply in_map.
                  specialize (H1 left0 (inr t :: s2 :: beta) H0).
                  destruct H1 as [_ [_ [_ H1]]].
                  apply H1.
                  simpl. 
                  left.
                  reflexivity.
                * contradiction.
            - simpl.
              omega.
            }           
          * inversion H2.
            {
            apply all_nts_up_to_correct.
            - intros e H3.
              simpl in H3.
              destruct H3 as [H3 | H3].
              + subst.
                destruct e.
                * apply in_or_app.
                  left.
                  apply in_map.
                  specialize (H1 left0 (s1 :: inl n0 :: beta) H0).
                  destruct H1 as [_ [_ [H1 _]]].
                  apply H1.
                  simpl.
                  right.
                  left.
                  reflexivity.
                * apply in_or_app.
                  right.
                  apply in_map.
                  specialize (H1 left0 (s1 :: inr t :: beta) H0).
                  destruct H1 as [_ [_ [_ H1]]].
                  apply H1.
                  simpl.
                  right.
                  left.
                  reflexivity.
              + apply in_split in H3.
                destruct H3 as [l1 [l2 H3]].
                subst.
                apply in_or_app.
                destruct e.
                * left.
                  apply in_map.
                  specialize (H1 left0 (s1 :: s2 :: l1 ++ inl n0 :: l2) H0).
                  destruct H1 as [_ [_ [H1 _]]].
                  apply H1.
                  simpl.
                  right.
                  right.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  reflexivity.
                * right.
                  apply in_map.
                  specialize (H1 left0 (s1 :: s2 :: l1 ++ inr t :: l2) H0).
                  destruct H1 as [_ [_ [_ H1]]].
                  apply H1.
                  simpl.
                  right.
                  right.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  reflexivity.
            - specialize (H1 left0 (s1 :: s2 :: beta) H0).
              destruct H1 as [H1 _].
              simpl in H1.
              simpl.
              omega.
            }
          * contradiction.
        + apply rules_g_cnf_to_rules_g_right in H0.
          destruct H0 as [left1 [right1 H0]].
          intros s H4.
          simpl in H4.
          destruct H4 as [H4 | [H4 | H4]].
          * inversion H4.
            {
            apply all_nts_up_to_correct.
            - intros e H7.
              destruct e, s2.
              + apply in_or_app.
                left.
                apply in_map.
                simpl in H7.
                destruct H7 as [H7 | H7].
                * inversion H7.
                  subst.
                  specialize (H1 left1 (right1 ++ inl n0 :: s3 :: beta) H0).
                  destruct H1 as [_ [_ [H1 _]]].
                  apply H1.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  reflexivity.
                * contradiction.
              + simpl in H7.
                destruct H7 as [H7 | H7].
                * inversion H7.
                * contradiction.
              + simpl in H7.
                destruct H7 as [H7 | H7].
                * inversion H7.
                * contradiction.
              + simpl in H7.
                destruct H7 as [H7 | H7].
                * inversion H7.
                  subst.
                  apply in_or_app.
                  right.   
                  specialize (H1 left1 (right1 ++ inr t :: s3 :: beta) H0).
                  destruct H1 as [_ [_ [_ H1]]].
                  apply in_map.
                  apply H1.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  reflexivity.
                * contradiction.
            - simpl.
              omega.
            }
          * inversion H4.
            {
            apply all_nts_up_to_correct.
            - intros e H7.
              destruct e.
              + apply in_or_app.
                left.
                apply in_map.
                simpl in H7.
                destruct H7 as [H7 | H7].
                * {
                  destruct s3. 
                  - inversion H7.
                    subst.
                    specialize (H1 left1 (right1 ++ s2 :: inl n0 :: beta) H0).
                    destruct H1 as [_ [_ [H1 _]]].
                    apply H1.
                    apply in_or_app.
                    right.
                    simpl.
                    right.
                    left.
                    reflexivity.
                  - inversion H7.
                  }
                * apply in_split in H7.
                  destruct H7 as [l1 [l2 H7]].
                  subst.
                  specialize (H1 left1 (right1 ++ s2 :: s3 :: l1 ++ inl n0 :: l2) H0).
                  destruct H1 as [_ [_ [H1 _]]].
                  apply H1.
                  apply in_or_app.
                  right.
                  simpl.
                  right.
                  right.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  reflexivity.
              + apply in_or_app.
                right.
                apply in_map.
                simpl in H7.
                destruct H7 as [H7 | H7].
                * {
                  destruct s3.
                  - inversion H7. 
                  - inversion H7.
                    subst.
                    specialize (H1 left1 (right1 ++ s2 :: inr t :: beta) H0).
                    destruct H1 as [_ [_ [_ H1]]].
                    apply H1.
                    apply in_or_app.
                    right.
                    simpl.
                    right.
                    left.
                    reflexivity.
                  }
                * apply in_split in H7.
                  destruct H7 as [l1 [l2 H7]].
                  subst.
                  specialize (H1 left1 (right1 ++ s2 :: s3 :: l1 ++ inr t :: l2) H0).
                  destruct H1 as [_ [_ [_ H1]]].
                  apply H1.
                  apply in_or_app.
                  right.
                  simpl.
                  right.
                  right.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  reflexivity.         
            - simpl.
              specialize (H1 left1 (right1 ++ s2 :: s3 :: beta) H0).
              destruct H1 as [H1 _].
              rewrite app_length in H1.
              simpl in H1.
              omega. 
            }
          * contradiction.
      - (* terminals in the rhs are in the list *)
        destruct H1 as [_ H1].
        inversion H.
        + subst.
          intros s H2.
          simpl in H2.
          destruct H2 as [H2 | H2].
          * inversion H2.
            subst.
            specialize (H1 left0 (s1 ++ [inr s] ++ s2) H0).
            apply H1.
            apply in_or_app.
            right.
            simpl.
            left.
            reflexivity.
          * contradiction.
        + subst.
          intros s H2.
          simpl in H2.
          destruct H2 as [H2 | H2].
          * inversion H2.
            subst.
            specialize (H1 left0 [inr s] H0).
            destruct H1 as [_ [_ [_ H1]]].
            apply H1.
            simpl. 
            left.
            reflexivity.
          * contradiction.
        + intros s H4.
          simpl in H4.
          destruct H4 as [H4 | [H4 | H4]].
          * inversion H4.
          * inversion H4.
          * contradiction.
        + intros s H4.
          simpl in H4.
          destruct H4 as [H4 | [H4 | H4]].
          * inversion H4.
          * inversion H4.
          * contradiction.
      }
Qed.

Definition g_cnf (g: cfg non_terminal terminal): cfg non_terminal' terminal := {|
start_symbol:= Lift_r [inl (start_symbol g)];
rules:= g_cnf_rules g;
rules_finite:= g_cnf_finite g
|}.

Inductive g_cnf'_rules (g: cfg non_terminal terminal): non_terminal' -> sf' -> Prop:=
| Lift_cnf'_all: 
       forall left: non_terminal',
       forall right: sf',
       g_cnf_rules g left right ->
       g_cnf'_rules g left right
| Lift_cnf'_new: 
       g_cnf'_rules g (start_symbol (g_cnf g)) [].

Lemma g_cnf'_finite:
forall g: cfg non_terminal terminal,
exists n: nat,
exists ntl: ntlist',
exists tl: tlist,
In (Lift_r [inl (start_symbol g)]) ntl /\
forall left: non_terminal',
forall right: sf',
g_cnf'_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal', In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
intros g.
destruct (rules_finite (g_cnf g)) as [n [ntl [tl H1]]].
destruct H1 as [H H1].
exists n.
exists ntl.
exists tl.
split.
- simpl in H.
  exact H.
- intros left right H2.
  inversion H2.
  + subst.
    specialize (H1 left right H0).
    destruct H1 as [H1 [H3 [H4 H5]]].
    split.
    * exact H1.
    * {
      split.
      - exact H3.
      - split.
        + exact H4.
        + exact H5.
      }
  + subst.
    split.
    * simpl.
      omega.
    * {
      split.
      - exact H.
      - split.
        + intros s H3.
          simpl in H3.
          contradiction.
        + intros s H3.
          simpl in H3.
          contradiction.
      }
Qed.

Definition g_cnf' (g: cfg non_terminal terminal) : cfg non_terminal' terminal:= {|
start_symbol:= start_symbol (g_cnf g);
rules:= g_cnf'_rules g;
rules_finite:= g_cnf'_finite g
|}.

End Chomsky_Definitions_2.

(* --------------------------------------------------------------------- *)
(* LEMMAS                                                                *)
(* --------------------------------------------------------------------- *)

Section Chomsky_1_Lemmas.

Variables non_terminal non_terminal_1 non_terminal_2 terminal: Type.

Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation ntlist:= (list non_terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation term_lift':= ((terminal_lift (non_terminal' non_terminal terminal)) terminal).
Notation symbol:= (non_terminal + terminal)%type.
Notation slist:= (list sf).
Notation vlist:= (list symbol).
Notation sf':= (list (non_terminal' non_terminal terminal + terminal)).
Notation ntlist':= (list non_terminal').
Notation tlist:= (list terminal).

Fixpoint flat_sf (l: sf'): sf :=
match l with
| nil => nil
| inl (Lift_r x) :: xs => x ++ flat_sf xs
| inr x :: xs => inr x :: flat_sf xs
end.

Lemma flat_sf_cat: 
forall l1 l2: sf',
flat_sf (l1 ++ l2) = flat_sf l1 ++ flat_sf l2.
Proof.
induction l1.
- intros l2. 
  simpl. 
  reflexivity.
- intros l2.
  destruct a.
  + destruct n. 
    simpl. 
    rewrite IHl1.
    rewrite <- app_assoc.
    reflexivity.
  + simpl. 
    rewrite IHl1.
    reflexivity.
Qed.

Lemma flat_sf_symbol_lift: 
forall l: sf,
flat_sf (map (@symbol_lift _ _) l) = l.
Proof.
induction l.
- simpl. 
  reflexivity.
- destruct a. 
  + simpl.
    rewrite IHl.
    reflexivity.
  + simpl. 
    rewrite IHl.
    reflexivity.
Qed.

Lemma derives_g_cnf_g_aux:
forall g: cfg _ _,
forall l r: sf',
derives (g_cnf g) l r ->
derives g (flat_sf l) (flat_sf r).
Proof.
induction 1.
- apply derives_refl.
- inversion H0. 
  + subst.
    repeat rewrite flat_sf_cat in *. 
    simpl in *. 
    exact IHderives.
  + subst.
    repeat rewrite flat_sf_cat in *.
    simpl in *.
    change (inr t :: flat_sf s3) with ([inr t] ++ flat_sf s3).
    apply derives_trans with (s2:= (flat_sf s2 ++ inl left0 :: flat_sf s3)).
    * exact IHderives.
    * change (flat_sf s2 ++ inl left0 :: flat_sf s3) with (flat_sf s2 ++ [inl left0] ++ flat_sf s3).
      {
      apply derives_subs with (s3:= [inl left0]).
      - apply derives_refl.
      - apply derives_start.
        exact H1.
      }
  + subst. 
    repeat rewrite flat_sf_cat in *.
    simpl in *.
    rewrite app_nil_r.
    change (s0 :: s4 :: beta ++ flat_sf s3) with ((s0 :: s4 :: beta) ++ flat_sf s3).
    apply derives_trans with (s2:= (flat_sf s2 ++ inl left0 :: flat_sf s3)).
    * exact IHderives.
    * change (flat_sf s2 ++ inl left0 :: flat_sf s3) with (flat_sf s2 ++ [inl left0] ++ flat_sf s3).
      {
      apply derives_subs with (s3:= [inl left0]).
      - apply derives_refl.
      - apply derives_start.
        exact H1.
      }
  + subst. 
    repeat rewrite flat_sf_cat in *. 
    simpl in *.
    rewrite app_nil_r.
    exact IHderives.
Qed.

Lemma derives_g_cnf_g:
forall g: cfg _ _,
forall s: sentence,
derives (g_cnf g) [inl (start_symbol (g_cnf g))] (map (@symbol_lift _ _) (map term_lift s)) ->
derives g [inl (start_symbol g)] (map term_lift s).
Proof.
intros g s H.
apply derives_g_cnf_g_aux in H.
simpl in H.
rewrite flat_sf_symbol_lift in H.
exact H.
Qed.

Lemma rules_g_derives_g_cnf:
forall g: cfg _ _,
forall left: non_terminal,
forall right: sf,
has_no_unit_rules g ->
right <> [] ->
rules g left right ->
derives (g_cnf g) [inl (Lift_r [inl left])] (map (@symbol_lift _ _) right).
Proof.
intros g left right H1 H2 H3.
destruct right.
- destruct H2.
  reflexivity.
- destruct right.
  + destruct s.
    * specialize (H1 left n [inl n] H3).
      destruct H1.
      reflexivity. 
    * simpl. 
      apply Lift_cnf_1 in H3. 
      apply derives_start.
      exact H3.
  + apply Lift_cnf_2 in H3. 
    generalize H3. 
    clear H1 H2 H3.
    simpl.
    generalize s s0 [inl terminal left]. 
    clear s s0 left.
    elim right.
    * simpl.
      { 
      destruct s, s0.
      - intros l H. 
        apply derives_start.
         exact H.
      - intros l H.
        apply derives_trans with (s2:= [inl (Lift_r [inl n]); inl (Lift_r [inr t])]).
        + apply derives_start.
           exact H.
        + change ([inl (Lift_r [inl n]); inl (Lift_r [inr t])]) with ([inl (Lift_r [inl n])] ++ [inl terminal (Lift_r [inr t])]).
          change ([symbol_lift (inl n); symbol_lift (inr t)]) with ([symbol_lift (inl n)] ++ [symbol_lift (inr t)]).
          apply derives_combine.
          split.
          * simpl. 
            apply derives_refl. 
          * simpl.
            apply derives_start.
            { 
            inversion H. 
            - subst.
              apply Lift_cnf_t with (left:= left) (s1:= [inl n]) (s2:= []).
              exact H2.
            - subst.
              apply rules_g_cnf_to_rules_g_left in H.
              destruct H as [H | [H | H]].
              + destruct H as [t' [H _]].
                inversion H.
              + destruct H as [nt' [H _]].
                inversion H.
              + destruct H as [left0 [right0 [s3 [s4 [H3 H4]]]]]. 
                subst.
                apply Lift_cnf_t with (left:= left0) (s1:= s3 ++ [inl n]) (s2:= s4).
                rewrite <- app_assoc.
                exact H3.
            }
      - intros l H.
        apply derives_trans with (s2:= [inl (Lift_r [inr t]); inl (Lift_r [inl n])]).
        + apply derives_start.
          exact H.
        + change ([inl (Lift_r [inr t]); inl (Lift_r [inl n])]) with ([inl (Lift_r [inr t])] ++ [inl terminal (Lift_r [inl n])]).
          change ([symbol_lift (inr t); symbol_lift (inl n)]) with ([symbol_lift (inr t)] ++ [symbol_lift (inl n)]).
          apply derives_combine.
          split.
          * simpl.
            apply derives_start.
            { 
            inversion H. 
            - subst.
              apply Lift_cnf_t with (left:= left) (s1:= []) (s2:= [inl n]).
              exact H2.
            - subst.
              apply rules_g_cnf_to_rules_g_left in H.
              destruct H as [H | [H | H]].
              + destruct H as [t0 [H _]].
                inversion H.
              + destruct H as [n0 [H _]].
                inversion H.
              + destruct H as [left0 [right0 [s3 [s4 [H3 H4]]]]]. 
                subst.
                apply Lift_cnf_t with (left:= left0) (s1:= s3) (s2:= [inl n] ++ s4).
                simpl.
                exact H3.
            }
          * simpl. 
            apply derives_refl. 
      - intros l H.
        apply derives_trans with (s2:= [inl (Lift_r [inr t]); inl (Lift_r [inr t0])]).
        + apply derives_start.
          exact H.
        + change ([inl (Lift_r [inr t]); inl (Lift_r [inr t0])]) with ([inl (Lift_r [inr t])] ++ [inl terminal (Lift_r [inr non_terminal t0])]).
          change ([symbol_lift (inr t); symbol_lift (inr t0)]) with ([symbol_lift (inr t)] ++ [symbol_lift (inr non_terminal t0)]).
          apply derives_combine.
          split.
          * simpl.
            apply derives_start.
            { 
            inversion H. 
            - subst.
              apply Lift_cnf_t with (left:= left) (s1:= []) (s2:= [inr t0]).
              exact H2.
            - subst.
              apply rules_g_cnf_to_rules_g_left in H.
              destruct H as [H | [H | H]].
              + destruct H as [t1 [H _]].
                inversion H.
              + destruct H as [n [H _]].
                inversion H.
              + destruct H as [left0 [right0 [s3 [s4 [H3 H4]]]]]. 
                subst.
                apply Lift_cnf_t with (left:= left0) (s1:= s3) (s2:= [inr t0] ++ s4).
                simpl.
                exact H3.
            }
          * simpl. 
            apply derives_start.
            { 
            inversion H. 
            - subst.
              apply Lift_cnf_t with (left:= left) (s1:= [inr t]) (s2:= []).
              exact H2.
            - subst.
              apply rules_g_cnf_to_rules_g_left in H.
              destruct H as [H | [H | H]].
              + destruct H as [t1 [H _]].
                inversion H.
              + destruct H as [n [H _]].
                inversion H.
              + destruct H as [left0 [right0 [s3 [s4 [H3 H4]]]]]. 
                subst.
                apply Lift_cnf_t with (left:= left0) (s1:= s3 ++ [inr t]) (s2:= s4).
                rewrite <- app_assoc.
                exact H3.
            }
      } 
    * intros a l H s s0 l0 H0.
      { 
      apply derives_trans with (s2:= [inl (Lift_r [s]); inl (Lift_r (s0 :: a :: l))]).
      - apply derives_start.
        exact H0. 
      - simpl. 
        change [inl (Lift_r [s]); inl (Lift_r (s0 :: a :: l))] with ([inl (Lift_r [s])]++[inl terminal (Lift_r (s0 :: a :: l))]).
        change (symbol_lift s :: symbol_lift s0 :: symbol_lift a :: map (symbol_lift (terminal:=terminal)) l) with ([symbol_lift s]++(symbol_lift s0 :: symbol_lift a :: map (symbol_lift (terminal:=terminal)) l)).
        apply derives_combine.
        split.
        + destruct s. 
          * simpl. 
            apply derives_refl.   
          * simpl.
            apply derives_start.
            { 
            inversion H0. 
            - subst.
              apply Lift_cnf_t with (left:= left) (s1:= []) (s2:= s0 :: a :: l).
              exact H3.
            - subst.
              apply rules_g_cnf_to_rules_g_left in H0.
              destruct H0 as [H0 | [H0 | H0]].
              + destruct H0 as [t0 [H0 _]].
                inversion H0.
              + destruct H0 as [n [H0 _]].
                inversion H0.
              + destruct H0 as [left0 [right0 [s3 [s4 [H4 H5]]]]]. 
                subst.
                apply Lift_cnf_t with (left:= left0) (s1:= s3) (s2:= s0 :: a :: l ++ s4).
                exact H4.
            }
        + apply H.
          apply Lift_cnf_3 in H0.
          exact H0.
      }
Qed.

Lemma derives_g_g_cnf_v1:
forall g: cfg _ _,
forall s: sf,
has_no_unit_rules g ->
has_no_empty_rules g ->
derives g [inl (start_symbol g)] s ->
derives (g_cnf g) [inl (start_symbol (g_cnf g))] (map (@symbol_lift _ _) s).
Proof.
intros g s H1 H2 H3.
remember [inl (start_symbol g)] as w.
induction H3.
- rewrite Heqw.
  simpl. 
  constructor.
- specialize (IHderives Heqw).
  apply derives_trans with (s2:= (map (symbol_lift (terminal:=terminal)) (s2 ++ inl left :: s3))).
  + exact IHderives.
  + clear Heqw H3 IHderives.
    apply rules_g_derives_g_cnf in H.
    * repeat rewrite map_app.
      apply derives_context_free_add_left.
      change (inl left :: s3) with ([inl left] ++ s3).
      rewrite map_app.
      apply derives_context_free_add_right.
      exact H.
    * exact H1. 
    * specialize (H2 left right H). 
      exact H2.
Qed.

Lemma derives_g_g_cnf_v2:
forall g: cfg _ _,
forall s: sf,
has_no_unit_rules g ->
has_one_empty_rule g ->
s <> [] ->
start_symbol_not_in_rhs g ->
derives g [inl (start_symbol g)] s ->
derives (g_cnf g) [inl (start_symbol (g_cnf g))] (map (@symbol_lift _ _) s).
Proof.
intros g s H1 H2 H3 H4 H5.
remember [inl (start_symbol g)] as w.
induction H5.
- rewrite Heqw.
  simpl. 
  constructor.
- assert (H6: s2 ++ inl left :: s3 <> []). 
    {
    apply not_eq_sym.
    apply app_cons_not_nil.  
    }
  specialize (IHderives H6 Heqw).
  apply derives_trans with (s2:= (map (symbol_lift (terminal:=terminal)) (s2 ++ inl left :: s3))).
  + exact IHderives.
  + clear H6 IHderives.
    assert (H6:= H2).
    specialize (H6 left right H).
    destruct H6 as [H6 | H7].
    * destruct H6 as [H6 H7].
      subst.
      {
      apply not_derives_start_symbol in H5.
      - destruct H5.
        apply in_or_app.
        right.
        simpl.
        left.
        reflexivity.
      - exact H4.
      - simpl in H3.
        apply app_not_nil in H3.
        destruct H3 as [H3 | H3].
        + intros H6.
          destruct s2.
          * destruct H3. 
            reflexivity. 
          * inversion H6.
            {
            destruct s2.
            - inversion H8.
            - inversion H8.
            }
        + intros H6.
          destruct s2.
          * inversion H6.
            subst. 
            destruct H3. 
            reflexivity. 
          * inversion H6.
            {
            destruct s2.
            - inversion H8.
            - inversion H8.
            }
      } 
    * repeat rewrite map_app.
      apply derives_context_free_add_left.
      change (inl left :: s3) with ([inl left] ++ s3).
      rewrite map_app.
      apply derives_context_free_add_right.
      {
      apply rules_g_derives_g_cnf in H.
      - exact H.
      - exact H1.
      - exact H7.
      }
Qed.

Lemma map_split:
forall s: sentence,
map ((terminal_lift (non_terminal' _ _)) terminal) s = map (@symbol_lift _ _) (map ((terminal_lift non_terminal) terminal) s).
Proof.
intros s.
induction s.
- simpl. 
  reflexivity.
- simpl.
  change (terminal_lift (non_terminal' _ _) a) with (@inr (non_terminal' non_terminal terminal) terminal a).
  apply app_eq.
  exact IHs.
Qed. 

Lemma remove_empty_rule:
forall g: cfg non_terminal terminal,
forall s: sentence,
s <> [] ->
derives g [inl (start_symbol g)] (map term_lift s) ->
exists g': cfg (emptyrules.non_terminal' non_terminal) terminal,
g_equiv_without_empty g' g /\ 
has_no_unit_rules g' /\ 
has_no_empty_rules g'.
Proof.
intros g s H1 H2.
assert (H3: exists s: sentence, produces g s /\ s <> []).
  {
  exists s.
  exact (conj H2 H1).
  }
apply g_simpl_ex_v2 in H3.
destruct H3 as [g' [H3 [_ [_ [H4 [H5 _]]]]]].
exists g'.
exact (conj H3 (conj H5 H4)).
Qed.

End Chomsky_1_Lemmas.

Section Chomsky_2_Lemmas.

Variables non_terminal non_terminal_1 non_terminal_2 terminal: Type.

Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation ntlist:= (list non_terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation symbol:= (non_terminal + terminal)%type.
Notation slist:= (list sf).
Notation vlist:= (list symbol).
Notation sf':= (list (non_terminal' non_terminal terminal + terminal)).
Notation ntlist':= (list non_terminal').
Notation tlist:= (list terminal).

Lemma g_cnf_preserves_start:
forall g: cfg non_terminal terminal,
start_symbol_not_in_rhs g ->
start_symbol_not_in_rhs (g_cnf g).
Proof.
unfold start_symbol_not_in_rhs.
intros g H1 left right H2 H3.
simpl in H3.
destruct H2.
- simpl in H3.
  destruct H3 as [H3 | H3].
  + inversion H3.
  + contradiction.
- simpl in H3.
  destruct H3 as [H3 | H3].
  + inversion H3.
  + contradiction.
- specialize (H1 left (s1 :: s2 :: beta) H). 
  apply H1.
  destruct H3 as [H3 | [H3 | H3]].
  + simpl.
    left.
    inversion H3.
    reflexivity.
  + inversion H3.
    simpl. 
    right.
    left.
    reflexivity.
  + contradiction.
- apply rules_g_cnf_to_rules_g_right in H2.
  destruct H2 as [left0 [right H2]].
  specialize (H1 left0 (right ++ s2 :: s3 :: beta) H2).
  clear H2.
  simpl in H3.
  destruct H3 as [H3 | [H3 | H3]].
  + inversion H3.
    subst.
    apply H1.
    apply in_or_app.
    right.
    simpl. 
    left.
    reflexivity.
  + inversion H3.
    subst.
    apply H1.
    apply in_or_app.
    right.
    simpl.
    right.
    left.
    reflexivity.
  + contradiction.
Qed.

Lemma g_cnf'_preserves_start:
forall g: cfg non_terminal terminal,
start_symbol_not_in_rhs g ->
start_symbol_not_in_rhs (g_cnf' g).
Proof.
unfold start_symbol_not_in_rhs.
intros g H1 left right H2 H3.
inversion H2.
- subst.
  clear H2.
  simpl in H3.
  assert (H4: start_symbol_not_in_rhs (g_cnf g)).
    {
    apply g_cnf_preserves_start.
    exact H1.
    }
  specialize (H4 left right H).
  apply in_split in H3.
  apply H4.
  destruct H3 as [l1 [l2 H3]].
  subst.
  simpl.
  apply in_or_app.
  right.
  left.
  reflexivity.
- subst.
  inversion H3.
Qed.

Lemma g_cnf_correct_v1:
forall g: cfg non_terminal terminal,
has_no_unit_rules g /\
has_no_empty_rules g /\
start_symbol_not_in_rhs g ->
is_cnf (g_cnf g) /\
g_equiv_without_empty (g_cnf g) g /\
start_symbol_not_in_rhs (g_cnf g).
Proof.
intros g [H1 [H2 HH]].
split.
- unfold is_cnf.
  intros left right H3.
  simpl in H3.
  inversion H3; subst; unfold is_cnf_rule.
  + right; exists t; reflexivity.
  + right; exists t; reflexivity.
  + left; exists (Lift_r [s1]). exists (Lift_r (s2 :: beta)); reflexivity.
  + left; exists (Lift_r [s2]). exists (Lift_r (s3 :: beta)); reflexivity.
- split.
  + unfold g_equiv_without_empty.
    unfold produces.
    unfold generates.
    intros s H3.
    split.
    * intros H4.
      apply derives_g_cnf_g.
      rewrite map_split in H4.
      exact H4.
    * intros H4.
      rewrite map_split.
      {
      apply derives_g_g_cnf_v1.
      - exact H1.
      - exact H2. 
      - exact H4. 
      }
  + apply g_cnf_preserves_start.
    exact HH.
Qed.

Lemma g_cnf_correct_v2:
forall g: cfg non_terminal terminal,
has_no_unit_rules g /\
has_one_empty_rule g /\
start_symbol_not_in_rhs g ->
is_cnf (g_cnf g) /\
g_equiv_without_empty (g_cnf g) g /\
start_symbol_not_in_rhs (g_cnf g).
Proof.
intros g [H1 [H2 HH]].
split.
- unfold is_cnf.
  intros left right H3.
  simpl in H3.
  inversion H3; subst; unfold is_cnf_rule.
  + right; exists t; reflexivity.
  + right; exists t; reflexivity.
  + left; exists (Lift_r [s1]). exists (Lift_r (s2 :: beta)); reflexivity.
  + left; exists (Lift_r [s2]). exists (Lift_r (s3 :: beta)); reflexivity.
- split.
  + unfold g_equiv_without_empty.
    unfold produces.
    unfold generates.
    intros s H3.
    split.
    * intros H4.
      apply derives_g_cnf_g.
      rewrite map_split in H4.
      exact H4.
    * intros H4.
      rewrite map_split.
      {
      apply derives_g_g_cnf_v2.
      - exact H1.
      - exact H2.
      - destruct s.
        + destruct H3.
          reflexivity.
        + simpl.
          apply not_eq_sym.
          apply nil_cons.
      - exact HH.
      - exact H4.
      }
  + apply g_cnf_preserves_start.
    exact HH.
Qed.

Lemma start_g_cnf'_not_in_rhs:
forall g: cfg _ _,
forall s1 s2: sf',
s1 ++ s2 <> [] ->
start_symbol_not_in_rhs g ->
~ derives (g_cnf' g) [inl (start_symbol (g_cnf' g))] (s1 ++ inl (start_symbol (g_cnf' g)) :: s2).
Proof.
intros g s1 s2 H1 H2 H3.
assert (H4: start_symbol_not_in_rhs (g_cnf' g)).
  {
  apply g_cnf'_preserves_start.
  exact H2.
  }
apply exists_rule' in H3.
destruct H3 as [H3 | H3].
- destruct H3 as [_ [H3 H5]].
  subst.
  destruct H1.
  reflexivity.
- destruct H3 as [left [right [H5 H6]]].
  specialize (H4 left right H5).
  simpl in H4.
  contradiction.
Qed.

Lemma g_cnf'_equiv_g_cnf_aux:
forall g: cfg _ _,
forall s: sf',
s <> [] ->
start_symbol_not_in_rhs g ->
(generates (g_cnf' g) s <-> generates (g_cnf g) s).
Proof.
intros g s H HH.
unfold generates.
split.
- intros H1.
  simpl in H1.
  simpl.
  remember [inl (Lift_r [inl (start_symbol g)])] as w.
  induction H1.
  + apply derives_refl.
  + apply derives_trans with (s2:= (s2 ++ inl left :: s3)).
    * {
      apply IHderives.  
      - apply not_eq_sym. 
        apply app_cons_not_nil.
      - exact Heqw.
      }
    * clear IHderives. 
      apply derives_rule.
      {
      inversion H0.
      - exact H2. 
      - subst.
        simpl in H1. 
        apply start_g_cnf'_not_in_rhs in H1. 
        + contradiction. 
        + exact H. 
        + exact HH.
      }
- clear H. 
  intros H1.
  simpl in H1.
  simpl.
  remember [inl (Lift_r [inl (start_symbol g)])] as w.
  induction H1.
  + apply derives_refl.
  + apply derives_trans with (s2:= (s2 ++ inl left :: s3)).
    * apply IHderives.  
      exact Heqw.
    * apply derives_rule.
      apply Lift_cnf'_all.
      exact H.
Qed.

Lemma g_cnf'_equiv_g_cnf:
forall g: cfg non_terminal terminal,
start_symbol_not_in_rhs g ->
g_equiv_without_empty (g_cnf' g) (g_cnf g).
Proof.
intros g H1 s H2.
unfold produces.
apply g_cnf'_equiv_g_cnf_aux.
- apply map_not_nil_inv.
  exact H2.
- exact H1.
Qed.

Lemma g_cnf_rule_is_cnf:
forall g: cfg _ _,
forall left: non_terminal' non_terminal terminal,
forall right: sf',
g_cnf_rules g left right ->
is_cnf_rule left right.
Proof.
intros g left right H.
unfold is_cnf_rule.
inversion H.
- right.
  exists t.
  reflexivity.
- right.
  exists t.
  reflexivity.
- left.
  exists (Lift_r [s1]), (Lift_r (s2 :: beta)).
  reflexivity.
- left.
  exists (Lift_r [s2]), (Lift_r (s3 :: beta)).
  reflexivity.
Qed.

Lemma g_cnf'_correct:
forall g: cfg non_terminal terminal,
has_no_unit_rules g /\
has_no_empty_rules g /\
start_symbol_not_in_rhs g ->
is_cnf_with_empty_rule (g_cnf' g) /\
g_equiv_without_empty (g_cnf' g) g /\
start_symbol_not_in_rhs (g_cnf' g).
Proof.
intros g [H1 [H2 HH]].
split.
- unfold is_cnf_with_empty_rule.
  intros left right H5.
  inversion H5.
  + right. 
    apply g_cnf_rule_is_cnf with (g:= g).
    exact H.
  + left.
    split.
    * simpl.
      reflexivity.
    * reflexivity.
- split.
  + apply g_equiv_without_empty_trans with (g2:= g_cnf g).
    split.
    * apply g_cnf'_equiv_g_cnf.
      exact HH.
    * apply g_cnf_correct_v1.
      {
      split. 
      - exact H1. 
      - split. 
        + exact H2.
        + exact HH.
      }
  + apply g_cnf'_preserves_start.
    exact HH.
Qed.

Lemma g_cnf_has_no_empty_rules:
forall g: cfg non_terminal terminal,
has_no_empty_rules (g_cnf g).
Proof.
intros g.
unfold has_no_empty_rules.
intros left right H.
inversion H.
- apply not_eq_sym.
  apply nil_cons.
- apply not_eq_sym.
  apply nil_cons.
- apply not_eq_sym. 
  apply nil_cons.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma g_cnf'_produces_empty:
forall g: cfg non_terminal terminal,
produces (g_cnf' g) [].
Proof.
intros g.
unfold produces.
unfold generates.
simpl.
apply derives_start.
apply Lift_cnf'_new.
Qed.

End Chomsky_2_Lemmas.

Section Chomsky_3_Lemmas.

Variables non_terminal terminal: Type.

Notation sf:= (list (non_terminal + terminal)).
Notation sf':= (list ((non_terminal' non_terminal) terminal + terminal)).
Notation ntlist':= (list ((non_terminal' non_terminal) terminal)).
Notation tlist:= (list terminal).
Notation sentence:= (list terminal).

Lemma g_cnf_ex_v1:
forall g: cfg non_terminal terminal,
~ produces_empty g ->
produces_non_empty g ->
exists g': cfg (non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal, 
(g_equiv g' g /\ is_cnf g' /\ start_symbol_not_in_rhs g').
Proof.
intros g H0 H.
apply produces_non_empty_equiv_non_empty in H.
apply g_simpl_ex_v1 in H.
destruct H as [g' [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]].
assert (H8: g_equiv (g_cnf g') g <-> g_equiv (g_cnf g') g' /\ g_equiv g' g).
  {
  split.
  - intros H. 
    split. 
    + apply g_equiv_trans with (g2:= g).
      apply g_equiv_sym in H1.
      exact (conj H H1).
    + exact H1. 
  - apply g_equiv_trans.
  } 
exists (g_cnf g').
split. 
- rewrite H8.
  split.
  + assert (H9: has_no_empty_rules (g_cnf g')).
      {
      apply g_cnf_has_no_empty_rules.
      }
    apply with_without_empty.
    * exact H9.
    * specialize (H5 H0). 
      exact H5.
    * apply g_cnf_correct_v1.
      {
      split.
      - exact H6.
      - split.
        + exact (H5 H0).
        + exact H7.
      }
  + exact H1.
- split.
  + apply g_cnf_correct_v1.
    split.
    * exact H6.
    * {
      split. 
      - exact (H5 H0).
      - exact H7.
      }
   + apply g_cnf_preserves_start. 
     exact H7.
Qed.

Lemma g_cnf_ex_v2:
forall g: cfg non_terminal terminal,
produces_empty g -> 
produces_non_empty g ->
exists g': cfg (non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal, 
(g_equiv g' g /\ is_cnf_with_empty_rule g' /\ start_symbol_not_in_rhs g').
Proof.
intros g H0 H1.
apply g_simpl_ex_v2 in H1.
destruct H1 as [g' [H1 [H2 [H3 [H4 [H5 H6]]]]]].
exists (g_cnf' g').
split.
- rewrite g_equiv_split with (g1:= g_cnf' g').
  split.
  + split.
    * intros _.
      exact H0.
    * intros _.
      apply g_cnf'_produces_empty. 
  + apply g_equiv_without_empty_trans with (g2:= g').
    split.
    * apply g_cnf'_correct. 
      {
      split.
      - exact H5. 
      - split. 
        + exact H4.
        + exact H6.
      }
    * exact H1.
- split. 
  + apply g_cnf'_correct.
    split.
    * exact H5.
    * {
      split. 
      - exact H4.
      - exact H6.
      }
  + apply g_cnf'_preserves_start.
    exact H6.
Qed.

Lemma g_cnf_ex_v3:
forall g: cfg non_terminal terminal,
produces_empty g -> 
~ produces_non_empty g ->
exists g': cfg (non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal, 
(g_equiv g' g /\ is_cnf_with_empty_rule g' /\ start_symbol_not_in_rhs g').
Proof.
intros g H0 H1.
pose (ss:= @Lift_r _ terminal [inl (emptyrules.Lift_nt (start_symbol g))]).
pose (rr:= fun nt rhs => nt=ss /\ rhs=(@nil ((non_terminal' (emptyrules.non_terminal' non_terminal) terminal) + terminal))).
assert (rf: exists n: nat,
            exists ntl: _,
            exists tl: _, 
            rules_finite_def ss rr n ntl tl).
  {
  exists 0.
  exists [ss].
  exists (@nil terminal).
  unfold rules_finite_def.
  split.
  - simpl.
    left.
    reflexivity.
  - split.
    + inversion H.
      subst.
      simpl.
      omega.
    + split.
      * inversion H.
        subst.
        simpl.
        left.
        reflexivity.
      * {
        split. 
        - intros s H2.
          inversion H.
          subst.
          simpl in H2.
          contradiction.
        - intros s H2.
          inversion H.
          subst.
          simpl in H2.
          contradiction.
        }
  }
exists {| start_symbol:= ss; rules:= rr; rules_finite:= rf |}.
split.
- apply g_equiv_split. 
  split. 
  + split. 
    * intros _.
      exact H0.
    * intros _.
      apply derives_start.
      simpl.
      red.
      {
      split.
      - reflexivity.
      - reflexivity.
      }
  + intros s H2.
    split.
    * intros H3.
      unfold produces in H3.
      unfold generates in H3.
      simpl in H3.
      apply exists_rule in H3.
      {
      destruct H3 as [H3 | H3].
      - inversion H3.
        destruct s.
        + destruct H2.
          reflexivity.
        + simpl in H4.
          inversion H4.
      - destruct H3 as [right [H3 H4]].
        inversion H3.
        subst.
        apply not_derives in H4.
        + contradiction.
        + destruct s.
          * destruct H2.
            reflexivity.
          * simpl.
            apply not_eq_sym.
            apply nil_cons.
      }
    * intros H3.
      assert (H4: exists s: sentence, produces g s /\ s <> []).
        {
        exists s.
        exact (conj H3 H2).
        }
      contradiction.
- split.
  + left.
    simpl.
    auto.
  + intros left right H2 H3.
    simpl in H2.
    simpl in H3.
    inversion H2.
    rewrite H4 in H3.
    simpl in H3.
    contradiction. 
Qed.

Lemma g_cnf_ex_v4:
forall g: cfg non_terminal terminal,
~ produces_empty g -> 
~ produces_non_empty g ->
exists g': cfg (non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal, 
(g_equiv g' g /\ is_cnf g' /\ start_symbol_not_in_rhs g').
Proof.
intros g H0 H1.
pose (ss:= @Lift_r _ terminal [inl (emptyrules.Lift_nt (start_symbol g))]).
pose (rr:= fun (nt: (non_terminal' (emptyrules.non_terminal' non_terminal) terminal)) 
               (rhs: list ((non_terminal' (emptyrules.non_terminal' non_terminal) terminal) + terminal)) => 
               False).
assert (rf: exists n: nat,
            exists ntl: _,
            exists tl: _, 
            rules_finite_def ss rr n ntl tl).
  {
  exists 0.
  exists [ss].
  exists (@nil terminal).
  unfold rules_finite_def.
  split.
  - simpl.
    left.
    reflexivity.
  - split.
    + inversion H.
    + split.
      * inversion H.
      * {
        split. 
        - inversion H.
        - inversion H.
        }
  }
exists {| start_symbol:= ss; rules:= rr; rules_finite:= rf |}.
split.
- unfold g_equiv.
  intros s.
  split.
  + intros H.
    destruct s.
    * inversion H.
      simpl in H5.
      inversion H5.
    * inversion H.
      simpl in H5.
      inversion H5.
  + intros H.
    destruct s.
    * unfold produces_empty in H0.
      contradiction.
    * unfold produces_non_empty in H1.
      destruct H1.
      exists (t :: s).
      {
      split.
      - exact H.
      - apply not_eq_sym.
        apply nil_cons.
      }
- split.
  + unfold is_cnf.   
    intros left right H2.
    inversion H2.
  + intros left right H2 H3.
    simpl in H2.
    simpl in H3.
    inversion H2.
Qed.

Theorem g_cnf_ex:
forall g: cfg non_terminal terminal,
(produces_empty g \/ ~ produces_empty g) /\ (produces_non_empty g \/ ~ produces_non_empty g) ->
exists g': cfg (non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal,
g_equiv g' g /\ (is_cnf g' \/ is_cnf_with_empty_rule g') /\ start_symbol_not_in_rhs g'.
Proof.
intros g [Ha Hb].
destruct Ha, Hb.
- assert (H2: exists g': cfg (non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal, g_equiv g' g /\ is_cnf_with_empty_rule g' /\ start_symbol_not_in_rhs g').
    {
    apply g_cnf_ex_v2.
    - exact H.
    - exact H0.
    }
  destruct H2 as [g' [H2 [H3 H4]]].
  exists g'.
  split.
  + exact H2.
  + split.
    * right.
      exact H3.
    * exact H4.
- assert (H2: exists g': cfg (non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal, g_equiv g' g /\ is_cnf_with_empty_rule g' /\ start_symbol_not_in_rhs g').
    {
    apply g_cnf_ex_v3.
    - exact H.
    - exact H0.
    }
  destruct H2 as [g' [H2 [H3 H4]]].
  exists g'.
  split.
  + exact H2.
  + split.
    * right.
      exact H3.
    * exact H4.
- assert (H2: exists g': cfg (non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal, g_equiv g' g /\ is_cnf g' /\ start_symbol_not_in_rhs g').
    {
    apply g_cnf_ex_v1.
    - exact H.
    - exact H0.
    }
  destruct H2 as [g' [H2 [H3 H4]]].
  exists g'.
  split.
  + exact H2.
  + split. 
    * left.
      exact H3.
    * exact H4.
- assert (H2: exists g': cfg (non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal, g_equiv g' g /\ is_cnf g' /\ start_symbol_not_in_rhs g').
    {
    apply g_cnf_ex_v4.
    - exact H.
    - exact H0.
    }
  destruct H2 as [g' [H2 [H3 H4]]].
  exists g'.
  split.
  + exact H2.
  + split.
    * left.
      exact H3.
    * exact H4.
Qed.

End Chomsky_3_Lemmas.
