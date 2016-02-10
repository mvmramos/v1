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
(* SIMPLIFICATION                                                        *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.
Require Import useless.
Require Import inaccessible.
Require Import unitrules.
Require Import emptyrules.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - INITIAL THEOREMS                                     *)
(* --------------------------------------------------------------------- *)

Section Simplification.

Variables terminal non_terminal: Type.
Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation term_lift':= ((terminal_lift non_terminal') terminal).

Theorem no_useless_symbols:
forall g: cfg terminal non_terminal,
non_empty g ->
exists g': cfg terminal non_terminal,
g_equiv g' g /\
has_no_useless_symbols g'.
Proof.
intros g.
exists (g_use g).
apply g_use_correct.
exact H.
Qed.

Theorem no_inaccessible_symbols:
forall g: cfg terminal non_terminal,
exists g': cfg terminal non_terminal,
g_equiv g' g /\
has_no_inaccessible_symbols g'.
Proof.
intros g.
exists (g_acc g).
apply g_acc_correct.
Qed.

Theorem no_unit_rules:
forall g: cfg terminal non_terminal,
exists g': cfg terminal non_terminal,
g_equiv g' g /\
has_no_unit_rules g'.
Proof.
intros g.
exists (g_unit g).
apply g_unit_correct.
Qed.

Theorem no_empty_rules:
forall g: cfg non_terminal terminal,
exists g': cfg (non_terminal' non_terminal) terminal,
g_equiv g' g /\
(generates_empty g -> has_one_empty_rule g') /\ 
(~ generates_empty g -> has_no_empty_rules g') /\
start_symbol_not_in_rhs g'.
Proof.
intros g.
exists (g_emp' g).
apply g_emp'_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - INACCESSIBLE AND USELESS SYMBOLS                     *)
(* --------------------------------------------------------------------- *)

Lemma g_acc_preserves_use:
forall g: cfg _ _,
forall s: non_terminal + terminal,
useful g s -> 
accessible g s ->
useful (g_acc g) s.
Proof.
intros g s H1 H2.
destruct s.
- unfold useful in H1.
  unfold useful.
  destruct H1 as [s H3].
  exists s.
  apply derives_sflist in H3.
  destruct H3 as [l [H4 [H5 H6]]].
  assert (H7: length l >= 2 \/ length l < 2) by omega.
  destruct H7 as [H7 | H7].
  + assert (H7':=H7). 
    apply sflist_rules with (g:=g) in H7.
    destruct H7 as [H7 _].
    specialize (H7 H4).
    apply derives_sflist.
    exists l.
    split.
    * {
      apply sflist_rules.
      - exact H7'.
      - intros i H8.
        specialize (H7 i H8).
        destruct H7 as [left [right [s0 [s' [H10 [H11 H12]]]]]].
        exists left, right, s0, s'.
        split.
        + exact H10.
        + split.
          * exact H11.
          * simpl.
            {
            apply Lift_acc.
            - exact H12.
            - unfold accessible in H2.
              destruct H2 as [s2 [s3 H13]].
              assert (H20: derives g [inl n] (s0 ++ inl left :: s')).
                {
                apply derives_sflist.
                rewrite <- (firstn_skipn (S i) l) in H4.
                apply sflist_app_r in H4.
                exists (firstn (S i) l).
                split. 
                - exact H4.
                - split.
                  + rewrite hd_first.
                    * exact H5.
                    * omega. 
                  + rewrite <- H10.
                    apply last_first_nth.
                    omega.
                }
              assert (H21: derives g [inl (start_symbol g)] (s2++s0++inl left::s'++s3)).
                {
                replace (s2 ++ inl n :: s3) with (s2 ++ [inl n] ++ s3) in H13.
                - apply derives_subs with (g:=g) (s1:=[inl (start_symbol g)]) (s2:=s2) (s3:=[inl n]) (s3':=(s0 ++ inl left :: s')) (s4:=s3) in H13.
                  + rewrite <- app_assoc in H13. 
                    exact H13.
                  + exact H20.
                - simpl. 
                  reflexivity.
                }
              exists (s2++s0), (s'++s3).
              rewrite <- app_assoc.
              exact H21.
            }
      }
    * {
      split.
      - exact H5.
      - exact H6.
      }
  + destruct l as [| s0 l].
    * simpl in H5.
      inversion H5.
    * {
      replace (s0::l) with ([s0]++l) in H7.
      - rewrite app_length in H7.
        simpl in H7.
        assert (H8: length l = 0) by omega.
        apply length_zero in H8.
        subst. 
        simpl in H5.
        rewrite H5 in H6.
        simpl in H6.
        destruct s.
        + simpl in H6.
          inversion H6.
        + replace (t::s) with ([t]++s) in H6. 
          * rewrite map_app in H6.
            inversion H6.
          * simpl. 
            reflexivity.
      - simpl. 
        reflexivity.
      }
- simpl. 
  auto.
Qed.

Lemma acc_appears:
forall g: cfg _ terminal,
forall n: non_terminal,
useful g (inl (start_symbol g)) -> 
accessible g (inl n) -> 
appears g (inl n).
Proof.
intros g n H10 H.
unfold accessible in H.
destruct H as [s1 [s2 H2]].
apply exists_rule' in H2.
destruct H2 as [H2 | H2].
- destruct H2 as [H2 [_ _]].
  inversion H2.
  apply (useful_exists).
  exact H10.
- destruct H2 as [left [right [H3 H4]]].
  exists left, right.
  split.
  + exact H3.
  + right.
    exact H4.
Qed.

Lemma in_g_use_acc_is_use:
forall g: cfg non_terminal terminal,
forall n: non_terminal,
useful g (inl (start_symbol g)) ->
accessible (g_use g) (inl n) ->
useful (g_use g) (inl n).
Proof.
intros g n H99 H.
unfold accessible in H.
unfold useful.
destruct H as [s1 [s2 H2]].
apply exists_rule' in H2.
destruct H2 as [H2 | H2]. 
- apply useful_g_use.
  simpl in H2.
  destruct H2 as [H2 [_ _]].
  rewrite H2.  
  apply acc_appears.
  + simpl. 
    apply useful_g_g_use. 
    exact H99.
  + unfold accessible.
    exists [], [].
    constructor.
- destruct H2 as [left [right [H3 H4]]].
  simpl in H3.
  inversion H3.
  subst.
  specialize (H1 (inl n) H4).
  unfold useful in H1.
  destruct H1 as [s0 H7].
  exists s0.
  apply derives_sflist in H7.
  destruct H7 as [l [H10 [H11 H12]]].
  apply derives_sflist.
  exists l.
  split.
  + assert (H6: length l >= 2 \/ length l < 2) by omega.
    destruct H6 as [H6 | H6].
    * assert (H6':=H6).
      apply sflist_rules with (g:=g) in H6.
      destruct H6 as [H6 _].
      specialize (H6 H10).
      {
      apply sflist_rules.
      - exact H6'.
      - intros i H7.
        specialize (H6 i H7).
        destruct H6 as [left0 [right0 [s3 [s' [H20 [H21 H22]]]]]].
        exists left0, right0, s3, s'.
        split.
        + exact H20.
        + split.
          * exact H21.
          * simpl.
            {
            apply Lift_use.
            - exact H22.
            - assert (H30: derives g (s3 ++ inl left0 :: s') (map term_lift s0)).
                {
                apply derives_sflist.
                rewrite <- (firstn_skipn i l) in H10.
                apply sflist_app_l in H10.
                exists (skipn i l).
                split.
                + exact H10.
                + split.
                  * rewrite hd_skip.
                    exact H20.
                  * {
                    rewrite last_skip.
                    - exact H12.
                    - omega.
                    }
                }
              apply derives_split in H30.
              destruct H30 as [s1' [s2' [H31 [H32 H33]]]].
              symmetry in H31.
              apply map_expand in H31.
              destruct H31 as [_ [s2'0 [_ [_ H34]]]].
              rewrite <- H34 in H33.
              replace (inl left0 :: s') with ([inl left0] ++ s') in H33.
              + apply derives_split in H33.
                destruct H33 as [s1'0 [s2'1 [H35 [H36 _]]]].
                symmetry in H35.
                apply map_expand in H35.
                destruct H35 as [s1'1 [_ [_ [H37 _]]]].
                rewrite <- H37 in H36.
                unfold useful.
                exists s1'1.
                exact H36.
              + simpl.
                reflexivity.
            - assert (H30: derives g (s3 ++ right0 ++ s') (map term_lift s0)).
                {
                apply derives_sflist.
                rewrite <- (firstn_skipn (S i) l) in H10.
                apply sflist_app_l in H10.
                exists (skipn (S i) l).
                split.
                + exact H10.
                + split.
                  * rewrite hd_skip.
                    exact H21.
                  * {
                    rewrite last_skip.
                    - exact H12.
                    - omega.
                    }
                } 
              apply derives_split in H30.
              destruct H30 as [s1' [s2' [H31 [H32 H33]]]].
              symmetry in H31.
              apply map_expand in H31.
              destruct H31 as [_ [s2'0 [_ [_ H34]]]].
              rewrite <- H34 in H33.
              apply derives_split in H33.
              destruct H33 as [s1'0 [s2'1 [H35 [H36 _]]]].
              symmetry in H35.
              apply map_expand in H35.
              destruct H35 as [s1'1 [_ [_ [H37 _]]]].
              rewrite <- H37 in H36.
              intros s4 H40.
              destruct s4. 
              + unfold useful.
                apply in_split in H40.
                destruct H40 as [l1 [l2 H41]].
                rewrite H41 in H36.
                apply derives_nt_sentence in H36.
                destruct H36 as [s'0 H42].
                exists s'0.
                exact H42.
              + simpl.
                auto. 
            }
      }
    * apply lt2_sflist.
      exact H6.
  + split.
    * exact H11.
    * exact H12.
Qed. 

End Simplification.

Section Simplification_2.

Variables non_terminal terminal: Type.

Lemma no_useless_no_inaccessible_symbols_v1:
forall g: cfg non_terminal terminal,
non_empty g ->
g_equiv (g_acc (g_use g)) g /\
has_no_inaccessible_symbols (g_acc (g_use g)) /\
has_no_useless_symbols (g_acc (g_use g)).
Proof.
intros g H'.
split.
- assert (H1: g_equiv (g_use g) g).
    {
    apply g_equiv_use.
    exact H'.
    }
  assert (H2: g_equiv (g_acc (g_use g)) (g_use g)).
    {
    apply g_equiv_acc.
    }
  apply g_equiv_trans with (g2:= g_use g).
  split.
  + exact H2.
  + exact H1.
- split.
  + intros s H.
    destruct s. 
    * inversion H.
      destruct H0 as [right [H1 H2]].
      {
      destruct H2 as [H2 | H2].
      - subst.
        simpl in H1.
        inversion H1.
        subst.
        apply accessible_g_g_acc.
        exact H2.
      - simpl in H1.
        inversion H1.
        subst.
        apply accessible_g_g_acc.
        apply acc_step with (s:=inl n) (right:=right) in H3.
        + exact H3.
        + exact H0.
        + exact H2.
      }
    * inversion H.
      destruct H0 as [right [H1 H2]].
      inversion H1.
      subst.
      apply accessible_g_g_acc.
      simpl in H1.
      inversion H1.
      subst.
      {
      apply acc_step with (s:=inr t) (right:=right) in H3.
      - exact H3.
      - exact H0.
      - exact H2.
      }
  + intros s H.
    inversion H.
    destruct H0 as [right [H1 H2]].
    destruct H2 as [H2 | H2].
    * simpl in H1.
      inversion H1.
      subst.
      assert (H4:= H3).
      {
      apply in_g_use_acc_is_use in H3.
      - apply g_acc_preserves_use.
        + exact H3.
        + exact H4.
      - exact H'.
      }
    * inversion H1. 
      subst.
      {
      apply acc_step with (s:=inl s) (right:=right) in H3.
      - assert (H4:=H3). 
        apply in_g_use_acc_is_use in H3.
        + apply g_acc_preserves_use.
          * exact H3.
          * exact H4.
        + exact H'.
      - exact H0.
      - exact H2.   
      }
Qed.

Lemma no_useless_no_inaccessible_symbols_v2:
forall g: cfg non_terminal terminal,
non_empty g ->
exists g': cfg non_terminal terminal,
g_equiv g' g /\
has_no_inaccessible_symbols g' /\
has_no_useless_symbols g'.
Proof.
intros g H'.
exists (g_acc (g_use g)).
apply no_useless_no_inaccessible_symbols_v1.
exact H'.
Qed.

End Simplification_2.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY AND UNIT RULES                                 *)
(* --------------------------------------------------------------------- *)

Section Simplification_3.

Variables non_terminal terminal: Type.

Notation sentence:= (list terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).

Lemma New_ss_not_in_unit_v1:
forall g: cfg non_terminal terminal,
forall n: non_terminal' non_terminal,
~ unit (g_emp' g) n (start_symbol (g_emp' g)).
Proof.
intros g n H.
remember (start_symbol (g_emp' g)) as w.
induction H.
- rewrite Heqw in H. 
  apply New_ss_not_in_right_g_emp'_v2 in H.
  simpl in H.
  unfold New_ss_not_in_sf in H.
  simpl in H.
  apply H.
  left.
  reflexivity.
- apply IHunit2.
  exact Heqw.
Qed.

Lemma New_ss_not_in_unit_v2:
forall g: cfg non_terminal terminal,
forall n1 n2: non_terminal' non_terminal,
unit (g_emp' g) n1 n2 -> n2 <> (start_symbol (g_emp' g)).
Proof.
intros g n1 n2 H1.
assert (H2: n2 = start_symbol (g_emp' g) \/ n2 <> start_symbol (g_emp' g)).
  {
  destruct n2. 
  - right. 
    simpl. 
    discriminate. 
  - left. 
    simpl. 
    reflexivity.
  }
destruct H2 as [H2 | H2].
- rewrite H2 in H1.
  apply New_ss_not_in_unit_v1 in H1.
  contradiction.
- exact H2.
Qed.

Lemma g_unit_preserves_one_empty_rule:
forall g: cfg (non_terminal' non_terminal) terminal,
(forall n1 n2: non_terminal' non_terminal, unit g n1 n2 -> n2 <> (start_symbol g)) ->
has_one_empty_rule g ->
has_one_empty_rule (g_unit g).
Proof.
intros g H0 H1.
unfold has_one_empty_rule.
intros left right H2.
inversion H2.
- subst.
  specialize (H1 left right H3).
  destruct H1 as [H1 | H1].
  + left.
    simpl.
    exact H1.
  + right.
    exact H1.
- clear H2. 
  subst.
  simpl.
  specialize (H1 b right H3).
  destruct H1 as [H1 | H1].
  + specialize (H0 left b H).
    destruct H1 as [H1 _].
    contradiction.
  + right.
    exact H1.
Qed.

Lemma g_unit_preserves_no_empty_rules:
forall g: cfg non_terminal terminal,
has_no_empty_rules g ->
has_no_empty_rules (g_unit g).
Proof.
unfold has_no_empty_rules.
intros g H1.
intros left right H2.
inversion H2.
- subst. 
  apply H1 with (left:= left).
  exact H0.
- subst.
  apply H1 with (left:= b).
  exact H0.
Qed.

End Simplification_3.

Section Simplification_4.

Variables non_terminal terminal: Type.

Notation sentence:= (list terminal).

Lemma no_empty_no_unit_rules_v1:
forall g: cfg non_terminal terminal,
g_equiv (g_unit (g_emp' g)) g /\
(generates_empty g -> has_one_empty_rule (g_unit (g_emp' g))) /\ 
(~ generates_empty g -> has_no_empty_rules (g_unit (g_emp' g))) /\
has_no_unit_rules (g_unit (g_emp' g)).
Proof.
intros g.
split.
- assert (H1: g_equiv (g_unit (g_emp' g)) (g_emp' g)).
    {
    apply g_unit_correct.
    }
  assert (H2: g_equiv (g_emp' g) g).
    {
    apply g_emp'_correct.
    }
  apply g_equiv_trans with (g2:= (g_emp' g)).
  split.
  + exact H1.
  + exact H2.
- split.
  + intros H1.
    assert (H2: has_one_empty_rule (g_emp' g)).
      {
      apply g_emp'_has_one_empty_rule.
      exact H1.
      }
    apply g_unit_preserves_one_empty_rule.
    * apply New_ss_not_in_unit_v2.
    * exact H2.
  + split.
    * intros H1.
      assert (H2: has_no_empty_rules (g_emp' g)).
        {
        apply g_emp'_has_no_empty_rules.
        exact H1.
        }
      apply g_unit_preserves_no_empty_rules.
      exact H2.
    * apply g_unit_has_no_unit_rules.
Qed.

Lemma no_empty_no_unit_rules_v2:
forall g: cfg non_terminal terminal,
g_equiv_without_empty (g_unit (g_emp g)) g /\
has_no_empty_rules (g_unit (g_emp g)) /\
has_no_unit_rules (g_unit (g_emp g)).
Proof.
intros g.
split.
- assert (H1: g_equiv (g_unit (g_emp g)) (g_emp g)).
    {
    apply g_unit_correct.
    }
  assert (H2: g_equiv_without_empty (g_emp g) g).
    {
    apply g_emp_correct.
    }
  apply g_equiv_without_empty_trans with (g2:= (g_emp g)).
  split.
  + apply remove_empty in H1. 
    exact H1.
  + exact H2.
- split.
  + assert (H2: has_no_empty_rules (g_emp g)).
      {
      apply g_emp_has_no_empty_rules.
      }
    apply g_unit_preserves_no_empty_rules.
    exact H2.
  + apply g_unit_has_no_unit_rules.
Qed.

Lemma no_empty_no_unit_rules_v3:
forall g: cfg non_terminal terminal,
exists g': cfg  (non_terminal' non_terminal) terminal,
g_equiv g' g /\
(generates_empty g -> has_one_empty_rule g') /\ 
(~ generates_empty g -> has_no_empty_rules g') /\
has_no_unit_rules g'.
Proof.
intros g.
exists (g_unit (g_emp' g)).
apply no_empty_no_unit_rules_v1.
Qed.

End Simplification_4.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - FINAL THEOREM                                        *)
(* --------------------------------------------------------------------- *)

Section Simplification_5.

Variables non_terminal terminal: Type.

Notation sentence:= (list terminal).

Lemma g_acc_g_use_preserves_rules:
forall g: cfg non_terminal terminal,
forall left: _,
forall right: _,
rules (g_acc (g_use g)) left right -> rules g left right.
Proof.
intros g left right H.
inversion H.
clear H.
subst.
inversion H0.
clear H0.
subst.
exact H.
Qed.

Lemma g_acc_g_use_preserves_empty_rule:
forall g: cfg (non_terminal' non_terminal) terminal,
rules g (start_symbol g) [] ->
rules (g_acc (g_use g)) (start_symbol (g_acc (g_use g))) [].
Proof.
intros g H.
simpl. 
apply Lift_acc.
- apply Lift_use.
  + exact H.
  + unfold useful.
    exists [].
    apply derives_start.
    simpl. 
    exact H.
  + intros s H1.
    simpl in H1.
    contradiction.
- exists [], [].
  simpl.
  apply derives_refl. 
Qed.

Lemma g_emp_preserves_non_empty:
forall g: cfg non_terminal terminal,
(exists s: sentence, produces g s /\ s <> []) ->
non_empty (g_emp g).
Proof.
intros g H0.
unfold non_empty.
unfold produces in H0.
unfold generates in H0.
unfold useful.
destruct H0 as [s [H0 H1]].
assert (H3: g_equiv_without_empty (g_emp g) g).
  {
  apply g_emp_correct.
  }
unfold g_equiv_without_empty in H3.
specialize (H3 s H1).
destruct H3 as [_ H3].
specialize (H3 H0).
exists s.
exact H3.
Qed.

Lemma g_emp'_preserves_non_empty:
forall g: cfg non_terminal terminal,
non_empty g ->
non_empty (g_emp' g).
Proof.
unfold non_empty.
intros g H0.
unfold useful in H0.
destruct H0 as [s H0].
assert (H1: g_equiv (g_emp' g) g).
  {
  apply g_emp'_correct.
  }
unfold g_equiv in H1.
specialize (H1 s).
destruct H1 as [_ H1].
specialize (H1 H0).
unfold useful. 
exists s.
exact H1.
Qed.

Lemma g_unit_preserves_non_empty:
forall g: cfg non_terminal terminal,
non_empty g ->
non_empty (g_unit g).
Proof.
unfold non_empty.
intros g H0.
simpl.
unfold useful in H0. 
destruct H0 as [s H0].
exists s.
assert (H2: g_equiv (g_unit g) g).
  {
  apply g_unit_correct.
  }
unfold g_equiv in H2.
specialize (H2 s).
destruct H2 as [_ H2].
unfold produces in H2.
unfold generates in H2.
apply H2.
exact H0.
Qed.

Lemma g_unit_preserves_start:
forall g: cfg (non_terminal' non_terminal) terminal,
start_symbol_not_in_rhs g ->
start_symbol_not_in_rhs (g_unit g).
Proof.
intros g H1 left right H2 H3.
unfold start_symbol_not_in_rhs in H1.
inversion H2.
- subst.
  specialize (H1 left right H0).
  apply H1.
  simpl in H3.
  exact H3.
- specialize (H1 b right H0).
  apply H1.
  simpl in H3.
  exact H3.
Qed.

Lemma g_use_preserves_start:
forall g: cfg (non_terminal' non_terminal) terminal,
start_symbol_not_in_rhs g ->
start_symbol_not_in_rhs (g_use g).
Proof.
intros g H1 left right H2 H3.
unfold start_symbol_not_in_rhs in H1.
inversion H2.
subst.
specialize (H1 left right H).
apply H1.
simpl in H3.
exact H3.
Qed.

Lemma g_acc_preserves_start:
forall g: cfg (non_terminal' non_terminal) terminal,
start_symbol_not_in_rhs g ->
start_symbol_not_in_rhs (g_acc g).
Proof.
intros g H1 left right H2 H3.
unfold start_symbol_not_in_rhs in H1.
inversion H2.
subst.
specialize (H1 left right H).
apply H1.
simpl in H3.
exact H3.
Qed.

End Simplification_5.

Section Simplification_6.

Variables non_terminal terminal: Type.

Notation sentence:= (list terminal).

Theorem g_simpl_ex_v1:
forall g: cfg non_terminal terminal,
 non_empty g ->
 exists g': cfg (non_terminal' non_terminal) terminal,
 g_equiv g' g /\
 has_no_inaccessible_symbols g' /\
 has_no_useless_symbols g' /\
(produces_empty g -> has_one_empty_rule g') /\ 
(~ produces_empty g -> has_no_empty_rules g') /\
 has_no_unit_rules g' /\
 start_symbol_not_in_rhs g'.
Proof.
intros g H.
exists (g_acc (g_use (g_unit (g_emp' g)))).
split.
- assert (H3: g_equiv (g_acc (g_use (g_unit (g_emp' g)))) (g_unit (g_emp' g))).
    {
    apply no_useless_no_inaccessible_symbols_v1.
    apply g_emp'_preserves_non_empty in H.
    apply g_unit_preserves_non_empty in H.
    exact H.
    }
  apply g_equiv_trans with (g2:= (g_unit (g_emp' g))).
  split.
  + exact H3.
  + apply no_empty_no_unit_rules_v1.
- split.
  + apply g_acc_has_no_inaccessible_symbols.
  + split. 
    * apply no_useless_no_inaccessible_symbols_v1.
      {
      apply g_emp'_preserves_non_empty in H.
      apply g_unit_preserves_non_empty in H.
      exact H.
      }
    * {
      split. 
      - intros H1'.
        assert (H2': has_one_empty_rule (g_unit (g_emp' g))).
          {
          apply no_empty_no_unit_rules_v1. 
          exact H1'.
          }    
        unfold has_one_empty_rule.
        remember (g_unit (g_emp' g)) as g'.
        intros left right HH.
        simpl in HH.
        inversion HH.
        clear HH.
        subst.
        simpl.
        simpl in H0.
        inversion H0.
        clear H0.
        subst.
        specialize (H2' left right H2).
        destruct H2' as [H2' | H2'].
        + simpl in H2'.
          left.
          exact H2'.
        + right.
          exact H2'.
      - split.
        + intros H1'.
          unfold has_no_empty_rules.
          intros left right H2'.
          apply g_acc_g_use_preserves_rules in H2'.
          apply g_emp'_has_no_empty_rules in H1'.
          apply g_unit_preserves_no_empty_rules in H1'.
          unfold has_no_empty_rules in H1'.
          specialize (H1' left right H2').
          exact H1'.
        + split.
          * unfold has_no_unit_rules.
            intros left n right H1'.
            apply g_acc_g_use_preserves_rules in H1'.
            {
            inversion H1'.
            clear H1'.
            - subst. 
              specialize (H0 n).
              exact H0.
            - subst.
              specialize (H2 n).
              exact H2.
            }
          * assert (H1: start_symbol_not_in_rhs (g_emp' g)).
              {
              apply start_symbol_not_in_rhs_g_emp'.
              }
            apply g_unit_preserves_start in H1.
            apply g_use_preserves_start in H1.
            apply g_acc_preserves_start in H1.
            exact H1. 
      }
Qed.

Theorem g_simpl_ex_v2:
forall g: cfg non_terminal terminal,
(exists s: sentence, produces g s /\ s <> [] ) ->
 exists g': cfg (non_terminal' non_terminal) terminal,
 g_equiv_without_empty g' g /\
 has_no_inaccessible_symbols g' /\
 has_no_useless_symbols g' /\
 has_no_empty_rules g' /\
 has_no_unit_rules g' /\
 start_symbol_not_in_rhs g'.
Proof.
intros g H.
exists (g_acc (g_use (g_unit (g_emp g)))).
split.
- assert (H3: g_equiv (g_acc (g_use (g_unit (g_emp g)))) (g_unit (g_emp g))).
    {
    apply no_useless_no_inaccessible_symbols_v1.
    apply g_emp_preserves_non_empty in H.
    apply g_unit_preserves_non_empty in H.
    exact H.
    }
  apply g_equiv_without_empty_trans with (g2:= (g_unit (g_emp g))).
  split.
  + apply remove_empty in H3. 
    exact H3.
  + apply no_empty_no_unit_rules_v2.
- split.
  + apply g_acc_has_no_inaccessible_symbols.
  + split. 
    * apply no_useless_no_inaccessible_symbols_v1.
      {
      apply g_emp_preserves_non_empty in H.
      apply g_unit_preserves_non_empty in H.
      exact H.
      }
    * {
      split. 
      - unfold has_no_empty_rules.
        intros left right H2'.
        apply g_acc_g_use_preserves_rules in H2'.
        apply g_unit_preserves_no_empty_rules in H2'.
        exact H2'.
        apply g_emp_has_no_empty_rules.
      - split.
        + unfold has_no_unit_rules.
          intros left n right H1'.
          apply g_acc_g_use_preserves_rules in H1'.
          inversion H1'.
          clear H1'.
          * subst. 
            specialize (H0 n).
            exact H0.
          * subst.
            specialize (H2 n).
            exact H2.
        + assert (H1: start_symbol_not_in_rhs (g_emp g)).
            {
            apply start_symbol_not_in_rhs_g_emp.
            }
          apply g_unit_preserves_start in H1.
          apply g_use_preserves_start in H1.
          apply g_acc_preserves_start in H1.
          exact H1. 
      }
Qed.

End Simplification_6.
