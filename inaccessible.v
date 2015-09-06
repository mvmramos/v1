(* ---------------------------------------------------------------------
   This file contains definitions and proof scripts related to 
   (i) closure operations for context-free grammars, 
   (ii) context-free grammars simplification 
   (iii) context-free grammar Chomsky normalization and 
   (iv) pumping lemma for context-free languages.
   
   More information can be found in the paper "Formalization of the
   pumpung lemma for context-free languages", submitted to
   LFCS 2016.
   
   Marcus Vinícius Midena Ramos
   mvmramos@gmail.com
   --------------------------------------------------------------------- *)
   
(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - INACESSIBLE SYMBOLS                                  *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg useless.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

Section Inaccessible.

Variables terminal non_terminal: Type.
Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation nlist:= (list non_terminal).
Notation tlist:= (list terminal).

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - INACCESSIBLE SYMBOLS - DEFINITIONS                   *)
(* --------------------------------------------------------------------- *)

Definition accessible (g: cfg _ _) (s: non_terminal + terminal): Prop:=
exists s1 s2: sf, derives g [inl (start_symbol g)] (s1++s::s2).

Inductive g_acc_rules (g: cfg _ _): non_terminal -> sf -> Prop :=
| Lift_acc : forall left: non_terminal,
             forall right: sf,
             rules g left right -> accessible g (inl left) -> g_acc_rules g left right.

Lemma g_acc_finite:
forall g: cfg _ _,
exists n: nat,
exists ntl: nlist,
exists tl: tlist,
In (start_symbol g) ntl /\
forall left: non_terminal,
forall right: sf,
g_acc_rules g left right ->
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
  subst.
  specialize (H1 left right H).
  destruct H1 as [H4 [H5 H6]].
  split.
  + exact H4.
  + split.
    * exact H5.
    * exact H6.
Qed.

Definition g_acc (g: cfg _ _): cfg _ _ := {|
start_symbol:= start_symbol g;
rules:= g_acc_rules g;
rules_finite:= g_acc_finite g
|}.

Definition has_no_inaccessible_symbols (g: cfg _ _): Prop:=
forall s: _, appears g s -> accessible g s.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - INACCESSIBLE SYMBOLS - LEMMAS AND THEOREMS           *)
(* --------------------------------------------------------------------- *)

Lemma accessible_g_g_acc:
forall g: cfg _ _,
forall s: non_terminal + terminal,
accessible g s -> accessible (g_acc g) s.
Proof.
intros g s H0.
unfold accessible in H0.
unfold accessible.
destruct H0 as [s1 [s2 H1]].
apply derives_sflist in H1.
destruct H1 as [l [H2 [H3 H4]]].
exists s1, s2.
simpl.
apply derives_sflist.
exists l.
split. 
- assert (H5: length l >= 2 \/ length l < 2) by omega.
  destruct H5 as [H5 | H5].
  + assert (H5':=H5).
    apply sflist_rules with (g:=g) in H5.
    apply sflist_rules.
    * exact H5'.
    * intros i H6.
      destruct H5 as [H5 _].
      specialize (H5 H2 i H6).
      destruct H5 as [left [right [s3 [s' [H10 [H11 H12]]]]]].
      exists left, right, s3, s'.
      {
      split.
      - exact H10.
      - split.
        + exact H11.
        + simpl. 
          apply Lift_acc.
          * exact H12.
          * exists s3, s'.
            rewrite <- (firstn_skipn (S i) l) in H2.
            apply sflist_app_r in H2.
            apply derives_sflist.
            exists (firstn (S i) l).
            {
            split.
            - exact H2.
            - split.
              + rewrite <- H3.
                rewrite hd_first.
                * reflexivity.
                * omega.
              + rewrite <- H10.
                apply last_first_nth.
                omega.
            }
      }
  + destruct l as [| s3 l].
    * apply sflist_empty.
    * {
      replace (s3::l) with ([s3]++l) in H5. 
      - rewrite app_length in H5.
        simpl in H5.
        assert (H7: length l = 0) by omega.
        apply length_zero in H7.
        rewrite H7.
        apply sflist_start.
      - simpl.
        reflexivity.
      }
- split.
  + exact H3.
  + exact H4.
Qed.

Lemma sflist_g_acc_g:
forall g: cfg _ _,
forall l: list sf,
sflist (g_acc g) l -> sflist g l.
Proof.
intros g l H.
induction H.
- apply sflist_empty. 
- apply sflist_start.
- apply sflist_step with (left:=left).
  exact IHsflist.
  exact H0.
  simpl in H1.
  inversion H1.
  exact H2.
Qed.

Lemma produces_g_acc_g:
forall g: cfg _ _,
forall s: sentence,
produces (g_acc g) s -> produces g s.
Proof.
unfold produces.
unfold generates.
intros g s H.
apply derives_sflist in H.
destruct H as [l [H1 [H2 H3]]].
simpl in H2.
apply derives_sflist.
exists l.
split.
- apply sflist_g_acc_g. 
  exact H1.
- split.
  + exact H2.
  + exact H3.
Qed.

Lemma acc_step:
forall g: cfg _ _,
forall n: non_terminal,
forall right: sf,
accessible g (inl n) -> rules g n right -> 
forall s: non_terminal + terminal,
In s right -> accessible g s.
Proof.
intros g n right H1 H2 s H3.
unfold accessible in H1.
unfold accessible.
destruct H1 as [s1 [s2 H4]].
apply derives_step with (right:=right) in H4.
- apply in_split in H3.
  destruct H3 as [l1 [l2 H5]].
  rewrite H5 in H4.
  rewrite <- app_assoc in H4.
  exists (s1++l1), (l2++s2).
  rewrite <- app_assoc. 
  exact H4.
- exact H2.
Qed.

Lemma sflist_g_g_acc:
forall g: cfg _ _,
forall l: list sf,
sflist g l /\ hd [] l = [inl (start_symbol g)] -> sflist (g_acc g) l.
Proof.
intros g l [H1 H2].
assert (H3: length l >= 2 \/ length l < 2) by omega.
destruct H3 as [H3 | H3].
- assert (H3':=H3).
  apply sflist_rules with (g:=g) in H3.
  destruct H3 as [H3 _].
  specialize (H3 H1).
  apply sflist_rules.
  + exact H3'.
  + intros i H4.
    specialize (H3 i H4).
    destruct H3 as [left [right [s0 [s' [H5 [H6 H7]]]]]].
    exists left, right, s0, s'.
    split.
    * exact H5.
    * {
      split.
      - exact H6.
      - simpl.
        apply Lift_acc.
        + exact H7.
        + assert (H20: derives g [inl (start_symbol g)] (s0 ++ inl left :: s')).
            {
            apply derives_sflist.
            rewrite <- (firstn_skipn (S i) l) in H1.
            apply sflist_app_r in H1.
            exists (firstn (S i) l).
            split.
            - exact H1.
            - split.
              + rewrite hd_first.
                * exact H2.
                * omega. 
              + rewrite <- H5. 
                apply last_first_nth.
                omega.
            }
          exists s0, s'.
          exact H20.
      }
- destruct l as [| s l].
  + apply sflist_empty.
  + destruct l as [| s0 l].
    * apply sflist_start.
    * {
      replace (s :: s0 :: l) with ([s] ++ [s0] ++ l) in H3. 
      - repeat rewrite app_length in H3.
        simpl in H3.
        repeat apply lt_S_n in H3.
        apply lt_n_0 in H3.
        contradiction.
      - simpl. 
        reflexivity.
      }
Qed.

Lemma produces_g_g_acc:
forall g: cfg _ _,
forall s: sentence,
produces g s -> produces (g_acc g) s.
Proof.
unfold produces.
unfold generates.
intros g s H.
apply derives_sflist in H.
destruct H as [l [H1 [H2 H3]]].
apply derives_sflist.
exists l.
split.
- apply sflist_g_g_acc.
  split.
  + exact H1.
  + exact H2.
- split.
  + simpl. 
    exact H2.
  + exact H3.
Qed.

Theorem g_equiv_acc:
forall g: cfg _ _,
g_equiv (g_acc g) g.
Proof.
unfold g_equiv.
intros g s.
split.
- apply produces_g_acc_g.
- apply produces_g_g_acc.
Qed.

Lemma g_acc_has_no_inaccessible_symbols:
forall g: cfg _ _,
has_no_inaccessible_symbols (g_acc g).
Proof.
unfold has_no_inaccessible_symbols.
intros g n H. 
destruct n as [nt | t].
- inversion H.
  destruct H0 as [right [H1 H2]].
  destruct H2 as [H2 | H2].
  + subst.
    simpl in H1.
    inversion H1.
    subst.
    apply accessible_g_g_acc.
    exact H2.
  + subst.
    simpl in H1.
    inversion H1.      
    apply accessible_g_g_acc.
    subst.
    apply acc_step with (s:=inl nt) (right:=right) in H3.
    * exact H3.
    * exact H0.
    * exact H2.
- inversion H.
  destruct H0 as [right [H1 H2]].
  simpl in H1.
  inversion H1.
  subst.
  apply acc_step with (s:=inr t) (right:=right) in H3.
  + apply accessible_g_g_acc.
    exact H3.
  + exact H0.
  + exact H2.
Qed.

Theorem g_acc_correct: 
forall g: cfg _ _,
g_equiv (g_acc g) g /\
has_no_inaccessible_symbols (g_acc g). 
Proof.
intro g.
split.
- apply g_equiv_acc.
- apply g_acc_has_no_inaccessible_symbols.
Qed.

End Inaccessible.
