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
(* SIMPLIFICATION - UNIT RULES                                           *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.
Require Import useless.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - UNIT RULES - DEFINITIONS                             *)
(* --------------------------------------------------------------------- *)

Section UnitRules.

Variables terminal non_terminal: Type.
Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation nlist:= (list non_terminal).
Notation tlist:= (list terminal).

Inductive unit (g: cfg non_terminal terminal) (a: non_terminal): non_terminal -> Prop:=
| unit_rule: forall (b: non_terminal),
             rules g a [inl b] -> unit g a b
| unit_trans: forall b c: non_terminal,
              unit g a b ->
              unit g b c ->
              unit g a c.

Inductive g_unit_rules (g: cfg _ _): non_terminal -> sf -> Prop :=
| Lift_direct' : 
       forall left: non_terminal,
       forall right: sf,
       (forall r: non_terminal,
       right <> [inl r]) -> rules g left right ->
       g_unit_rules g left right
| Lift_indirect':
       forall a b: non_terminal,
       unit g a b ->
       forall right: sf,
       rules g b right ->  
       (forall c: non_terminal,
       right <> [inl c]) -> 
       g_unit_rules g a right.

Lemma unit_exists:
forall g: cfg _ _,
forall a b: non_terminal,
unit g a b ->
exists c : sf, rules g a c.
Proof.
intros g a b H.
induction H.
- exists [inl b].
  exact H.
- exact IHunit1.
Qed.

Lemma g_unit_finite:
forall g: cfg _ _,
exists n: nat,
exists ntl: nlist,
exists tl: tlist,
In (start_symbol g) ntl /\
forall left: non_terminal,
forall right: sf,
g_unit_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
intros g.
destruct (rules_finite g) as [n [ntl [tl H1]]].
exists n, ntl, tl.
split.
- destruct H1 as [H1 _].
  exact H1.
- destruct H1 as [_ H1].
  intros left right H2.
  inversion H2.
  + subst.
    specialize (H1 left right H0).
    destruct H1 as [H4 [H5 H6]].
    split.
    * exact H4.
    * {
      split.
      - exact H5.
      - exact H6.
      }
  + subst.
    apply unit_exists in H.
    destruct H as [c H4].
    split.
    * specialize (H1 b right H0).
      destruct H1 as [H1 _].
      exact H1.
    * {
      split.
      - specialize (H1 left c H4).
        destruct H1 as [_ [H1 _]].
        exact H1.
      - specialize (H1 b right H0).
        destruct H1 as [_ [_ H1]].
        exact H1.
      }  
Qed.

Definition g_unit (g: cfg _ _): cfg _ _ := {|
start_symbol:= start_symbol g;
rules:= g_unit_rules g;
rules_finite:= g_unit_finite g
|}.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - UNIT RULES - LEMMAS AND THEOREMS                     *)
(* --------------------------------------------------------------------- *)

Lemma unit_not_unit:
forall g: cfg _ _,
forall a b: non_terminal,
~ unit (g_unit g) a b.
Proof.
intros g a0 b0 H.
induction H.
- inversion H.
  + specialize (H0 b).
    destruct H0.
    reflexivity.
  + specialize (H2 b).
    destruct H2.
    reflexivity.
- exact IHunit1.
Qed.

Lemma unit_derives:
forall g: cfg _ _,
forall a b: non_terminal,
unit g a b ->
derives g [inl a] [inl b].
Proof.
intros g a b H.
induction H.
- apply derives_start.
  exact H.
- apply derives_trans with (s2:=[inl b]).
  + exact IHunit1.
  + exact IHunit2.
Qed.

Lemma rules_g_unit_g:
forall g: cfg _ _,
forall left: non_terminal,
forall right: sf,
rules (g_unit g) left right ->
rules g left right \/ derives g [inl left] right.
Proof.
intros g left right H.
simpl in H.
inversion H.
- left.
  exact H1.
- right.
  subst.
  replace right with ([] ++ right ++ []).
  + apply derives_step with (left:=b).
    * apply unit_derives in H0.
      exact H0.
    * exact H1.
  + rewrite app_nil_l. 
    rewrite app_nil_r.
    reflexivity.
Qed.

Lemma rules_g_unit_g':
forall g: cfg _ _,
forall left: non_terminal,
forall right: sf,
rules (g_unit g) left right ->
rules g left right \/ 
exists left': non_terminal, unit g left left' /\ rules g left' right.
Proof.
intros g left right H.
inversion H.
- left.
  exact H1.
- right. 
  exists b.
  split.
  + exact H0.
  + exact H1.
Qed.

Lemma rules_g_unit_not_unit:
forall g: cfg _ _,
forall left: non_terminal,
forall right: sf,
(rules (g_unit g) left right) ->
(~ exists n: non_terminal, right = [inl n]).
Proof.
intros g left right H1 H2.
inversion H1.
- subst.
  destruct H2 as [n H2]. 
  specialize (H n).
  contradiction.
- subst.
  destruct H2 as [n H2]. 
  specialize (H3 n).
  contradiction.
Qed.

Lemma generates_g_unit_g:
forall g: cfg _ _,
forall s: sf,
generates (g_unit g) s -> generates g s.
Proof.
unfold generates.
intros g s H.
simpl in H.
remember [inl (start_symbol g)] as w1. 
induction H.
- apply derives_refl.
- apply rules_g_unit_g in H0.
  destruct H0 as [H0 | H0].
  + apply derives_step with (left:=left).
    * apply IHderives.
      exact Heqw1.
    * exact H0.
  + apply derives_subs with (s3:=[inl left]).
    * apply IHderives.
      exact Heqw1.
    * exact H0.
Qed.

Lemma rules_g_g_unit:
forall g: cfg _ _,
forall left: non_terminal,
forall right: sf,
rules g left right ->
(forall n: non_terminal, right <> [inl n]) ->
rules (g_unit g) left right.
Proof.
intros g left right H1 H2.
simpl. 
apply Lift_direct'.
- exact H2.
- exact H1.
Qed.

Lemma derives3_g_g_unit:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sentence, 
derives3 g n s -> derives3 (g_unit g) n s. 
Proof.
intros g.
intros n s H.
apply derives3_ind_2 with (g:=g) (P:=derives3 (g_unit g)) (P0:=derives3_aux (g_unit g)).
- intros n0 lt H1.
  apply derives3_rule.
  apply rules_g_g_unit in H1.
  + exact H1. 
  + destruct lt; discriminate.
- intros n0 ltnt lt H1 H2 H3.
  destruct ltnt.
  + apply rules_g_g_unit in H1.
    * inversion H2. 
      subst. 
      apply derives3_rule.
      exact H1. 
    * discriminate.
  + destruct ltnt.
    * {
      destruct s0. 
      - apply exists_rule_derives3_aux in H2.
        destruct H2 as [H2 | H2].
        + assert (H10: rules (g_unit g) n0 (map term_lift lt)).
            {
            apply Lift_indirect' with (b:=n1).
            * apply unit_rule.
              exact H1.
            * exact H2. 
            * destruct lt; discriminate.
            }
          apply derives3_rule.
          exact H10.
        + destruct H2 as [right [H4 H5]].
          apply exists_rule_derives3_aux in H3.
          destruct H3 as [H3 | H3].
          * apply rules_g_unit_g' in H3.
            {
            destruct H3 as [H3 | H3].
            - assert (H10: rules (g_unit g) n0 (map term_lift lt)).
                {
                apply Lift_indirect' with (b:=n1).
                - apply unit_rule.
                  exact H1.
                - exact H3.
                - intros c0.
                  destruct lt. 
                  + discriminate.
                  + discriminate.
                }  
              apply derives3_rule.
              exact H10.
            - destruct H3 as [left' [H6 H7]].
              assert (H10: rules (g_unit g) n0 (map term_lift lt)).
                {
                apply Lift_indirect' with (b:=left').
                - apply unit_trans with (b:=n1).
                  + apply unit_rule.
                    exact H1.
                  + exact H6.
                - exact H7.
                - intros c0.
                  destruct lt; discriminate.
                }
              apply derives3_rule.
              exact H10.
            }
          * destruct H3 as [right0 [H6 H7]].
            assert (H6':=H6).
            apply rules_g_unit_not_unit in H6'.
            apply rules_g_unit_g' in H6.
            {
            destruct H6 as [H6 | H6].
            - apply derives3_step with (ltnt:=right0).
              + apply Lift_indirect' with (b:=n1).
                * apply unit_rule.
                  exact H1.
                * exact H6.
                * apply not_exists_forall_not.
                  exact H6'.
              + exact H7.
            - apply derives3_step with (ltnt:=right0).
              + destruct H6 as [left' [H8 H9]].
                apply Lift_indirect' with (b:=left').
                * {
                  apply unit_trans with (b:=n1).
                  - apply unit_rule.
                    exact H1.
                  - exact H8.
                  }
                * exact H9.
                * apply not_exists_forall_not.
                  exact H6'.
              + exact H7.
            }  
      - apply rules_g_g_unit in H1.
        + apply derives3_step with (ltnt:=[inr t]).
          * exact H1.
          * exact H3.
        + discriminate.
      }
    * {
      apply rules_g_g_unit in H1.
      - apply derives3_step with (ltnt:=(s0 :: s1 :: ltnt)).
        + exact H1.
        + exact H3.
      - discriminate.
      }
- apply derives3_aux_empty.
- intros t ltnt lt H1 H2.
  apply derives3_aux_t.
  exact H2.
- intros n0 lt lt' ltnt H1 H2 H3 H4.
  apply derives3_aux_nt.
  + exact H2.
  + exact H4.
- exact H.
Qed.

Lemma derives_g_g_unit:
forall g: cfg _ _,
forall s: sentence,
forall n: non_terminal,
derives g [inl n] (map term_lift s) -> derives (g_unit g) [inl n] (map term_lift s).
Proof.
intros g s n.
repeat rewrite derives_equiv_derives3.
apply derives3_g_g_unit.
Qed.

Theorem g_equiv_unit:
forall g: cfg _ _,
g_equiv (g_unit g) g.
Proof.
unfold g_equiv.
unfold produces.
intros g s.
split.
- apply generates_g_unit_g.
- apply derives_g_g_unit.
Qed.

Definition has_no_unit_rules (g: cfg _ _): Prop:=
forall left n: non_terminal,
forall right: sf,
rules g left right -> right <> [inl n].

Lemma g_unit_has_no_unit_rules:
forall g: cfg _ _,
has_no_unit_rules (g_unit g).
Proof.
unfold has_no_unit_rules.
intros g left n right H.
destruct right.
- apply nil_cons.
- inversion_clear H.
  + specialize (H0 n). 
    exact H0.
  + specialize (H2 n). 
    exact H2.
Qed.

Theorem g_unit_correct: 
forall g: cfg _ _,
g_equiv (g_unit g) g /\
has_no_unit_rules (g_unit g).
Proof.
intros g.
split.
- apply g_equiv_unit.
- apply g_unit_has_no_unit_rules.
Qed.

End UnitRules.
