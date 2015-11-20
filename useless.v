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
(* SIMPLIFICATION - USELESS SYMBOLS                                      *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - USELESS SYMBOLS - DEFINITIONS                        *)
(* --------------------------------------------------------------------- *)

Section Useless.

Variables terminal non_terminal: Type.
Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation nlist:= (list non_terminal).
Notation tlist:= (list terminal).

Definition useful (g: cfg _ _) (s: non_terminal + terminal): Prop:=
match s with
| inr t => True
| inl n => exists s: sentence, derives g [inl n] (map term_lift s)
end.

Definition useful_sf (g: cfg _ _)(l: _): Prop:=
forall s: _,
In s l -> useful g s.

Inductive g_use_rules (g: cfg _ _): non_terminal -> sf -> Prop :=
| Lift_use : forall left: non_terminal,
             forall right: sf,
             rules g left right ->
             useful g (inl left) ->
             useful_sf g right ->
             g_use_rules g left right.

Lemma g_use_finite:
forall g: cfg _ _,
exists n: nat,
exists ntl: nlist,
exists tl: tlist,
In (start_symbol g) ntl /\
forall left: non_terminal,
forall right: sf,
g_use_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
intros g.
destruct (rules_finite g) as [n [ntl [ tl H1]]].
exists n, ntl, tl.
split.
- destruct H1 as [H1 _].
  exact H1.
- intros left right H2.
  inversion H2.
  subst.
  destruct H1 as [_ H1].
  specialize (H1 left right H).
  destruct H1 as [H4 [H5 H6]].
  split.
  + exact H4.
  + split.
    * exact H5.
    * exact H6.
Qed.

Definition g_use (g: cfg _ _): cfg _ _:= {|
start_symbol:= start_symbol g;
rules:= g_use_rules g;
rules_finite:= g_use_finite g
|}.

Definition has_no_useless_symbols (g: cfg _ _): Prop:=
forall n: _, appears g (inl n) -> useful g (inl n).

Definition non_empty (g: cfg _ _): Prop:=
useful g (inl (start_symbol g)).

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - USELESS SYMBOLS - LEMMAS AND THEOREMS                *)
(* --------------------------------------------------------------------- *)

Lemma useful_exists:
forall g: cfg _ _,
forall n:non_terminal,
useful g (inl n) -> 
exists (left : non_terminal) (right : sf),
rules g left right /\ (n = left \/ In (inl n) right).
Proof.
intros g n H1.
destruct H1 as [s H2].
apply exists_rule in H2.
destruct H2 as [H2 | H2].
- exists n, (map term_lift s).
  split.
  + exact H2.
  + left.
    reflexivity.
- destruct H2 as [right [H3 H4]].
  exists n, right.
  split.
  + exact H3.
  + left.
    reflexivity.
Qed.

Lemma useful_sf_sentence:
forall l: sf,
forall g: cfg _ _,
useful_sf g l -> exists s': sentence, derives g l (map term_lift s').
Proof.
intros l g H.
induction l.
- exists [].
  simpl.
  apply derives_refl.
- replace (a :: l) with ([a]++l) in H. 
  + assert (H1: forall s: non_terminal + terminal, In s l -> useful g s).
      {
      intros s H1.
      specialize (H s).
      apply H. 
      apply in_or_app.
      right.
      exact H1.
      }
    specialize (IHl H1).
    assert (H2: useful g a).
      {
      apply H.
      simpl. 
      left.
      reflexivity.
      }
    unfold useful in H2.
    destruct a.
    * destruct IHl as [s' H3].
      destruct H2 as [s H2].
      exists (s ++ s').
      simpl.
      {
      rewrite map_app.
      change (inl n :: l) with ([inl n] ++ l).
      apply derives_combine.
      split.
      - exact H2.
      - exact H3.
      }
    * destruct IHl as [s2 H5].
      exists ([t] ++ s2).
      rewrite map_app.
      change (inr t :: l) with ([inr t] ++ l).
      apply derives_combine.
      {
      split. 
      - simpl. 
        constructor. 
      - exact H5.
      } 
  + simpl.
    reflexivity.
Qed.

Lemma use_step:
forall g: cfg _ _,
forall left: non_terminal,
forall right: sf,
rules g left right -> 
(forall s: non_terminal + terminal, In s right -> useful g s) ->
useful g (inl left).
Proof.
intros g left right H1 H2.
unfold useful.
apply derives_rule with (s1:=[]) (s2:=[]) in H1.
simpl in H1.
rewrite app_nil_r in H1.
apply useful_sf_sentence in H2. 
destruct H2 as [s' H3].
exists s'.
apply derives_trans with (s2:=right).
- exact H1.
- exact H3.
Qed.

Lemma useful_g_g_use:
forall g: cfg _ _,
forall n: non_terminal,
useful g (inl n) -> useful (g_use g) (inl n).
Proof.
intros g n H.
unfold useful in H.
destruct H as [x H].
unfold useful. 
exists x.
apply derives_sflist in H.
apply derives_sflist.
destruct H as [l [H2 [H3 H4]]].
exists l.
split.
- assert (H5: length l >= 2 \/ length l < 2).
    {
    omega.
    }
  destruct H5 as [H5 | H5].    
  + assert (H6:= H5).
    apply sflist_rules with (g:=g) in H5.
    destruct H5 as [H5 _].
    specialize (H5 H2).
    apply sflist_rules.
    * exact H6.
    * intros i H7.
      specialize (H5 i H7).
      destruct H5 as [left [right [s0 [s' [H10 [H11 H12]]]]]].
      exists left, right, s0, s'.
      {
      split. 
      - exact H10.
      - split.
        + exact H11.
        + simpl.
          apply Lift_use.
          * exact H12.
          * unfold useful.
            assert (H20: derives g (s0 ++ inl left :: s') (map term_lift x)).
              {
              apply derives_sflist.
              rewrite <- (firstn_skipn i l) in H2.
              apply sflist_app_l in H2.
              exists (skipn i l).
              split.
              - exact H2.
              - split.
                + rewrite hd_skip.
                  exact H10.
                + rewrite last_skip.
                  * exact H4.
                  * omega.
              }
            assert (H21: exists s'': sentence, derives g [inl left] (map term_lift s'')).
              {
              apply derives_split in H20.
              destruct H20 as [s1' [s2' [H21 [_ H22]]]].
              replace (inl left :: s') with ([inl left] ++ s') in H22.
              - apply derives_split in H22.
                destruct H22 as [s1'0 [s2'0 [H31 [H32 _]]]].
                symmetry in H21. 
                apply map_expand in H21.
                destruct H21 as [s1'' [s2'' [H40 [H41 H42]]]].
                rewrite <- H42 in H31.
                symmetry in H31. 
                apply map_expand in H31.
                destruct H31 as [s1''' [s2''' [H50 [H51 H52]]]].
                rewrite <- H51 in H32.
                exists s1'''.
                exact H32.
              - simpl.
                reflexivity.
              }
            exact H21.
          * intros s1 H8.
            {
            destruct s1.
            - assert (H30: derives g (s0 ++ right ++ s') (map term_lift x)).
                {
                apply derives_sflist.
                rewrite <- (firstn_skipn (S i) l) in H2.
                apply sflist_app_l in H2.
                exists (skipn (S i) l).
                split.
                - exact H2.
                - split.
                  + rewrite <- H11.
                    apply hd_skip.
                  + rewrite <- H4.
                    apply last_skip.
                    omega.
                }
              assert (H31: exists s'': sentence, derives g right (map term_lift s'')).
                {
                apply derives_split in H30.
                destruct H30 as [s1' [s2' [H35 [H36 H37]]]].
                apply derives_split in H37.
                destruct H37 as [s1'0 [s2'0 [H38 [H39 H40]]]].
                symmetry in H35.
                apply map_expand in H35.
                destruct H35 as [s1'' [s2'' [H41 [H42 H43]]]].
                rewrite <- H43 in H38.
                symmetry in H38. 
                apply map_expand in H38.
                destruct H38 as [s1''' [s2''' [H50 [H51 H52]]]].
                rewrite <- H51 in H39.
                exists s1'''.
                exact H39.
                }
              assert (H32: exists s'': sentence, derives g [inl n0] (map term_lift s'')).
                {
                apply in_split in H8.
                destruct H8 as [l1 [l2 H60]].
                rewrite H60 in H31.
                destruct H31 as [s'' H61].
                apply derives_split in H61.
                destruct H61 as [s1' [s2' [H35 [H36 H37]]]].
                replace (inl n0 :: l2) with ([inl n0] ++ l2) in H37.
                - apply derives_split in H37.
                  destruct H37 as [s1'0 [s2'0 [H38 [H39 H40]]]].
                  symmetry in H35.
                  apply map_expand in H35.
                  destruct H35 as [s1'' [s2'' [H41 [H42 H43]]]].
                  rewrite <- H43 in H38.
                  symmetry in H38. 
                  apply map_expand in H38.
                  destruct H38 as [s1''' [s2''' [H50 [H51 H52]]]].
                  rewrite <- H51 in H39.
                  exists s1'''.
                  exact H39.
                - simpl. 
                  reflexivity.
                }
              exact H32.
            - simpl. 
              auto. 
          }
      }
  + destruct l as [|s0 l]. 
    * apply sflist_empty.
    * {
      destruct l as [|s1 l].
      - apply sflist_start.
      - replace (s0 :: s1 :: l) with ([s0] ++ [s1] ++ l) in H5. 
        + repeat rewrite app_length in H5.
          simpl in H5.
          repeat apply lt_S_n in H5.
          apply lt_n_0 in H5.
          contradiction. 
        + simpl. 
          reflexivity.
      }
- split.
  + exact H3.
  + exact H4.
Qed.

Lemma useful_g_use:
forall g: cfg _ _,
forall n: non_terminal,
appears (g_use g) (inl n) -> useful (g_use g) (inl n).
Proof.
intros g n H.
inversion H.
clear H.
destruct H0 as [right [H1 H2]].
destruct H2 as [H2| H2].
- subst.
  simpl in H1.
  inversion H1.
  subst.
  apply useful_g_g_use.
  exact H0.
- simpl in H1.
  inversion H1.
  subst.
  apply useful_g_g_use.
  specialize (H3 (inl n)).
  apply H3.
  exact H2.
Qed.

Lemma sflist_g_use_g:
forall g: cfg _ _,
forall l: list sf,
sflist (g_use g) l -> sflist g l.
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

Lemma produces_g_use_g:
forall g: cfg _ _,
forall s: sentence,
produces (g_use g) s -> produces g s.
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
- apply sflist_g_use_g. 
  exact H1.
- split.
  + exact H2.
  + exact H3.
Qed.

Lemma sflist_g_g_use:
forall g: cfg _ _,
forall l: list sf,
forall s: sentence,
sflist g l /\ last l [] = map term_lift s -> sflist (g_use g) l.
Proof.
intros g l s [H1 H2].
assert (H3: length l >= 2 \/ length l < 2).
  {
  omega.
  }
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
        apply Lift_use.
        + exact H7.
        + unfold useful. 
          assert (H20: derives g (s0 ++ inl left :: s') (map term_lift s)).
            {
            apply derives_sflist.
            rewrite <- (firstn_skipn i l) in H1.
            apply sflist_app_l in H1.
            exists (skipn i l).
            split.
            - exact H1.
            - split.
              + rewrite hd_skip.
                exact H5.
              + rewrite last_skip.
                * exact H2.
                * omega.
            }
          assert (H21: exists s'': sentence, derives g [inl left] (map term_lift s'')).
            {
            apply derives_split in H20.
            destruct H20 as [s1' [s2' [H21 [_ H22]]]].
            replace (inl left :: s') with ([inl left] ++ s') in H22.
            - apply derives_split in H22.
              destruct H22 as [s1'0 [s2'0 [H31 [H32 _]]]].
              symmetry in H21. 
              apply map_expand in H21.
              destruct H21 as [s1'' [s2'' [H40 [H41 H42]]]].
              rewrite <- H42 in H31.
              symmetry in H31. 
              apply map_expand in H31.
              destruct H31 as [s1''' [s2''' [H50 [H51 H52]]]].
              rewrite <- H51 in H32.
              exists s1'''.
              exact H32.
            - simpl.
              reflexivity.
            }
          exact H21.
        + intros s1 H99.
          destruct s1.
          * assert (H30: derives g (s0 ++ right ++ s') (map term_lift s)).
              {
              apply derives_sflist.
              rewrite <- (firstn_skipn (S i) l) in H1.
              apply sflist_app_l in H1.
              exists (skipn (S i) l).
                split.
              - exact H1.
              - split.
                + rewrite <- H6.
                  apply hd_skip.
                + rewrite <- H2.
                  apply last_skip.
                  omega.
              }
            assert (H31: exists s'': sentence, derives g right (map term_lift s'')).
              {
              apply derives_split in H30.
              destruct H30 as [s1' [s2' [H35 [H36 H37]]]].
              apply derives_split in H37.
              destruct H37 as [s1'0 [s2'0 [H38 [H39 H40]]]].
              symmetry in H35.
              apply map_expand in H35.
              destruct H35 as [s1'' [s2'' [H41 [H42 H43]]]].
              rewrite <- H43 in H38.
              symmetry in H38. 
              apply map_expand in H38.
              destruct H38 as [s1''' [s2''' [H50 [H51 H52]]]].
              rewrite <- H51 in H39.
              exists s1'''.
              exact H39.
              }
            assert (H32: exists s'': sentence, derives g [inl n] (map term_lift s'')).
              {
              apply in_split in H99.
              destruct H99 as [l1 [l2 H60]].
              rewrite H60 in H31.
              destruct H31 as [s'' H61].
              apply derives_split in H61.
              destruct H61 as [s1' [s2' [H35 [H36 H37]]]].
              replace (inl n :: l2) with ([inl n] ++ l2) in H37.
              - apply derives_split in H37.
                destruct H37 as [s1'0 [s2'0 [H38 [H39 H40]]]].
                symmetry in H35.
                apply map_expand in H35.
                destruct H35 as [s1'' [s2'' [H41 [H42 H43]]]].
                rewrite <- H43 in H38.
                symmetry in H38. 
                apply map_expand in H38.
                destruct H38 as [s1''' [s2''' [H50 [H51 H52]]]].
                rewrite <- H51 in H39.
                exists s1'''.
                exact H39.
              - simpl. 
                reflexivity.
              }
            unfold useful.
            exact H32.
          * simpl.
            auto.
      }   
- destruct l as [|s0 l].
  + apply sflist_empty.
  + destruct l as [|s1 l].
    * apply sflist_start.
    * {
      replace (s0 :: s1 :: l) with ([s0] ++ [s1] ++ l) in H3. 
      - repeat rewrite app_length in H3.
        simpl in H3.
        repeat apply lt_S_n in H3.
        apply lt_n_0 in H3.
        contradiction.
      - simpl. 
        reflexivity.
      }
Qed.

Lemma produces_g_g_use:
forall g: cfg _ _,
forall s: sentence,
produces g s -> produces (g_use g) s.
Proof.
unfold produces.
unfold generates.
intros g s H.
apply derives_sflist in H.
destruct H as [l [H1 [H2 H3]]].
apply derives_sflist.
exists l.
split.
- apply sflist_g_g_use with (s:=s).
  split.
  + exact H1.
  + exact H3.
- split.
  + exact H2.
  + exact H3.
Qed.

Theorem g_equiv_use:
forall g: cfg _ _,
non_empty g -> g_equiv (g_use g) g.
Proof.
unfold g_equiv.
intros g H' s.
split.
- apply produces_g_use_g.
- apply produces_g_g_use.
Qed.

Theorem g_use_correct: 
forall g: cfg _ _,
non_empty g ->
g_equiv (g_use g) g /\
has_no_useless_symbols (g_use g). 
Proof.
intros g H'.
split.
- apply g_equiv_use.
  exact H'.
- unfold has_no_useless_symbols. 
  intros n H.
  inversion H.
  destruct H0 as [right [H1 H2]].
  simpl in H1.
  inversion H1.
  subst.
  destruct H2.
  + subst.
    apply useful_g_g_use in H3.
    exact H3.
  + specialize (H4 (inl n) H2).
    apply useful_g_g_use in H4.
    exact H4.
Qed.

End Useless.
