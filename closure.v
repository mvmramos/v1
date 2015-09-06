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
   
Require Import List.

Require Import misc_list.
Require Import cfg.
Require Import cfl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

(* --------------------------------------------------------------------- *)
(* CLOSURE - DEFINITIONS                                                 *)
(* --------------------------------------------------------------------- *)

Section Closure.

Variables non_terminal terminal: Type.

Inductive g_clo_nt: Type :=
| Start_clo : g_clo_nt
| Transf_clo_nt : non_terminal -> g_clo_nt.

Notation sf:= (list (non_terminal + terminal)).
Notation sfc:= (list (g_clo_nt + terminal)).
Notation nlist:= (list g_clo_nt).
Notation tlist:= (list terminal).
Notation sentence:= (list terminal).

Definition g_clo_sf_lift (c: non_terminal + terminal): g_clo_nt + terminal:=
  match c with
  | inl nt => inl (Transf_clo_nt nt)
  | inr t  => inr t
  end.

Inductive g_clo_rules (g: cfg non_terminal terminal): g_clo_nt -> sfc -> Prop :=
| New1_clo: g_clo_rules g Start_clo ([inl Start_clo] ++ [inl (Transf_clo_nt (start_symbol g))])
| New2_clo: g_clo_rules g Start_clo []
| Lift_clo: forall nt: non_terminal,
            forall s: sf,
            rules g nt s ->
            g_clo_rules g (Transf_clo_nt nt) (map g_clo_sf_lift s).

Lemma g_clo_finite:
forall g: cfg non_terminal terminal,
exists n: nat,
exists ntl: list g_clo_nt,
exists tl: tlist,
In Start_clo ntl /\
forall left: g_clo_nt,
forall right: sfc,
g_clo_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: g_clo_nt, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
intros g.
destruct (rules_finite g) as [n1 [ntl1 [tl1 H1]]].
exists (S (S n1)), (Start_clo :: (map Transf_clo_nt ntl1)), tl1.
split.
- simpl.
  left.
  reflexivity.
- split.
  + inversion H.
    * simpl.
      omega.
    * simpl. 
      omega.
    * destruct H1 as [_ H1].
      subst. 
      specialize (H1 nt s H0). 
      destruct H1 as [H1 _]. 
      rewrite map_length. 
      omega. 
  + split.
    * {
      inversion H.
      - simpl.
        left.
        reflexivity.
      - simpl.
        left.
        reflexivity.
      - simpl.
        right. 
        destruct H1 as [_ H1].
        specialize (H1 nt s H0).
        destruct H1 as [_ [H5 [_ _]]]. 
        apply in_split in H5.
        destruct H5 as [l1 [l2 H5]].
        rewrite H5.
        rewrite map_app.
        apply in_or_app.
        right.
        simpl. 
        left.
        reflexivity.
      }
    * {
      split. 
      - inversion H. 
        + subst. 
          intros s H4.
          simpl in H4.
          destruct H4 as [H4 | H4].
          * inversion H4.
            simpl. 
            left.
            reflexivity. 
          * {
            destruct H4 as [H4 | H4].
            - inversion H4.
              simpl.
              right.
              destruct H1 as [H1 _].
              apply in_split in H1.
              destruct H1 as [l1 [l2 H1]].
              rewrite H1.
              rewrite map_app.
              apply in_or_app.
              right.   
              simpl.   
              left.
              reflexivity.
            - contradiction.
            }
        + subst. 
          intros s H4.
          simpl in H4.
          contradiction.
        + subst. 
          intros s0 H4.
          destruct H1 as [_ H1].
          specialize (H1 nt s H0).
          destruct H1 as [_ [_ [H5 _]]].
          simpl. 
          right.
          destruct s0.
          * apply in_split in H4.
            destruct H4 as [l1 [l2 H4]]. 
            symmetry in H4. 
            apply map_expand in H4.
            destruct H4 as [s1' [s2' [H4' [H4'' H4''']]]].
            change (inl Start_clo :: l2) with ([inl Start_clo] ++ l2) in H4'''.
            symmetry in H4'''. 
            apply map_expand in H4'''.
            destruct H4''' as [s1'0 [s2'0 [H5' [H5'' H5''']]]].
            {
            destruct s1'0.
            - inversion H5''.
            - simpl in H5''. 
              inversion H5''.
              destruct s0.
              + simpl in H2.
                inversion H2.
              + simpl in H2.
                inversion H2.
            }
          * assert (H6: In (inl n) s). 
              { 
              apply in_split in H4. 
              destruct H4 as [l1 [l2 H4]]. 
              symmetry in H4. 
              apply map_expand in H4.
              destruct H4 as [s1' [s2' [H4' [H4'' H4''']]]].
              change (inl (Transf_clo_nt n) :: l2) with ([inl (Transf_clo_nt n)] ++ l2) in H4'''.
              symmetry in H4'''. 
              apply map_expand in H4'''.
              destruct H4''' as [s1'0 [s2'0 [H5' [H5'' H5''']]]].
              destruct s1'0.
              - inversion H5''.
              - inversion H5''.
                destruct s0.
                + simpl in H2.
                  inversion H2.
                  subst.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  reflexivity.
                + simpl in H2.
                  inversion H2.
              }
            specialize (H5 n H6).
            apply in_map.
            exact H5.
      - inversion H. 
        + subst. 
          intros s H4.
          simpl in H4.
          destruct H4 as [H4 | H4].
          * inversion H4.
          * {
            destruct H4 as [H4 | H4].
            - inversion H4.
            - contradiction.
            }
        + subst. 
          intros s H4.
          simpl in H4.
          contradiction.
        + subst. 
          intros s0 H4.
          destruct H1 as [_ H1].
          specialize (H1 nt s H0).
          destruct H1 as [_ [_ [_ H5]]].
          assert (H6: In (inr s0) s).
            {
            apply in_split in H4.
            destruct H4 as [l1 [l2 H4]]. 
            symmetry in H4. 
            apply map_expand in H4.
            destruct H4 as [s1' [s2' [H4' [H4'' H4''']]]].
            change (inr s0 :: l2) with ([inr s0] ++ l2) in H4'''.
            symmetry in H4'''. 
            apply map_expand in H4'''.
            destruct H4''' as [s1'0 [s2'0 [H5' [H5'' H5''']]]].
            destruct s1'0.
            - inversion H5''.
            - simpl in H5''. 
              inversion H5''.
              destruct s1. 
              + simpl in H2.
                inversion H2.
              + simpl in H2.
                inversion H2.
                subst.
                apply in_or_app.
                right.
                simpl.
                left.
                reflexivity.
            }
          specialize (H5 s0 H6).
          exact H5. 
      }
Qed.

Definition g_clo (g: cfg non_terminal terminal): (cfg g_clo_nt terminal):= {|
start_symbol:= Start_clo;
rules:= g_clo_rules g;
rules_finite:= g_clo_finite g
|}.

(* --------------------------------------------------------------------- *)
(* CLOSURE - LEMMAS                                                      *)
(* --------------------------------------------------------------------- *)

Theorem derives_add_clo:
forall g: cfg non_terminal terminal,
forall s1 s2: sf,
derives g s1 s2 -> derives (g_clo g) (map g_clo_sf_lift s1) (map g_clo_sf_lift s2).
Proof.
intros g s1 s2 H.
induction H.
- apply derives_refl.
- rewrite map_app.
  rewrite map_app.
  rewrite map_app in IHderives.
  simpl in IHderives.
  apply derives_step with (g:= g_clo g) (left:= (Transf_clo_nt left)).
  exact IHderives.
  simpl.
  apply Lift_clo.
  exact H0.
Qed.

Theorem g_clo_correct:
forall g: cfg non_terminal terminal,
forall s: sf,
forall s': sfc,
 generates (g_clo g) nil /\
(generates (g_clo g) s' /\ generates g s -> generates (g_clo g) (s'++ map g_clo_sf_lift s)).
Proof.
intros g s s'.
unfold generates.
split.
- simpl.
  rewrite <- app_nil_l.
  rewrite <- app_nil_r.
  rewrite <- app_assoc.
  apply derives_step with (left:= Start_clo).
  + rewrite app_nil_l.
    apply derives_refl.
  + simpl.
    apply New2_clo.
- intros [H1 H2].
  apply derives_trans with (s2:= [inl Start_clo] ++ (map g_clo_sf_lift [inl (start_symbol g)])).
  + simpl.
    apply derives_start.
    simpl. 
    apply New1_clo.
  + apply derives_add_clo in H2.
    apply derives_combine with (g:= (g_clo g)).
    split.
    * exact H1.
    * exact H2.
Qed.

Theorem g_clo_correct_inv:
forall g: cfg non_terminal terminal,
forall s: sfc,
generates (g_clo g) s -> 
(s=[]) \/
(s=[inl (start_symbol (g_clo g))]) \/
(exists s': sfc, 
 exists s'': sf,
 generates (g_clo g) s' /\ generates g s'' /\ s=s' ++ map g_clo_sf_lift s'').
Proof.
unfold generates.
intros g s.
remember ([inl (start_symbol (g_clo g))]) as init.
intro H.
induction H.
- right.
  left.  
  reflexivity.
- subst.
  specialize (IHderives eq_refl).
  destruct IHderives.
  + destruct s2.
    * inversion H1. 
    * inversion H1.
  + destruct H1.
    * { 
      destruct s2.
      - inversion H1.
        subst.
        inversion H0.
        + simpl in *.
          right.
          right. 
          exists [inl Start_clo].
          exists [inl (start_symbol g)].
          split.
          apply derives_refl.
          split.
          apply derives_refl.
          simpl. 
          reflexivity.
        + left.
          trivial.
      - right. 
        right. 
        inversion H1.
        destruct s2.
        + inversion H4. 
        + inversion H4.  
      }
    * destruct H1 as [s' [s'' [H2 [H3 H4]]]]. 
      { 
      inversion H0.
      - (* First case, rule New1_clo *)
        subst. simpl in *.
        assert (IN : In (inl Start_clo) (s' ++ map g_clo_sf_lift s'')).
          { 
          simpl in *. 
          rewrite <- H4. 
          apply in_app_iff. 
          right. 
          simpl. 
          left. 
          reflexivity. 
          }
        apply in_app_iff in IN.
        destruct IN.
        + (* Start_clo is in s', ok *)
          apply equal_app in H4. 
          destruct H4.
          * {
            destruct H4 as [l [H5 H6]].
            destruct l.
            - simpl in H6.
              rewrite cons_app in H6.
              apply map_expand in H6.
              destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
              subst.
              destruct s1'.
              + inversion H8.
              + inversion H8.
                destruct s.
                * inversion H5.
                * inversion H5.
            - right.
              right.
              inversion H6.
              subst.
              exists (s2 ++ inl Start_clo :: inl (Transf_clo_nt (start_symbol g)) :: l).
              exists s''.
              split.
              + apply derives_step with (right:=[inl Start_clo; inl (Transf_clo_nt (start_symbol g))]) in H2.
                * exact H2.
                * exact H0. 
              + split.
                * exact H3.
                * rewrite <- app_assoc.
                  simpl.
                  reflexivity. 
            }
          * destruct H4 as [l [H5 H6]].
            symmetry in H6.
            apply map_expand in H6.
            destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
            {
            destruct s2'.
            - inversion H9.
            - inversion H9.
              destruct s.
              + inversion H6.
              + inversion H6. 
            }
        + (* Start_clo is in s'', contradiction *)
          rewrite in_map_iff in H1. 
          destruct H1 as [x [H5 H6]].
          destruct x.
          * inversion H5.
          * inversion H5.   
      - (* Second case, rule New2_clo *)
        simpl in *.
        subst.
        assert (IN: In (inl Start_clo) (s' ++ map g_clo_sf_lift s'')).
          { 
          simpl in *. 
          rewrite <- H4. 
          rewrite in_app_iff. 
          right. 
          simpl. 
          left. 
          reflexivity. 
          }
        apply in_app_iff in IN.
        destruct IN.
        + (* Start_clo is in s', ok *)
          right.
          right.
          apply equal_app in H4.
          destruct H4.
          * destruct H4 as [l [H5 H6]]. 
            {
            destruct l.
            - simpl in H6.
              rewrite cons_app in H6.
              apply map_expand in H6.
              destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
              destruct s1'.
              + inversion H8.
              + simpl in H8. 
                inversion H8.
                destruct s.
                * inversion H6.
                * inversion H6.
            - inversion H6.
              subst. 
              exists (s2 ++ l).
              exists s''.
              split.
              + replace (s2 ++ l) with (s2 ++ [] ++ l).
                * { 
                  apply derives_step with (left:= Start_clo).
                  - exact H2.
                  - exact H0. 
                  }
                * simpl.
                  reflexivity.
              + split.
                * exact H3.
                * rewrite <- app_assoc.
                  reflexivity. 
            }
          * destruct H4 as [l [H5 H6]].
            symmetry in H6.
            apply map_expand in H6.
            destruct H6 as [s1' [s2' [H7 [H8 H9]]]]. 
            {
            destruct s2'. 
            - inversion H9.
            - inversion H9.
              destruct s.
              + inversion H6.
              + inversion H6. 
            }  
        + (* Start_clo is in s'', contradiction *)
          rewrite in_map_iff in H1. 
          destruct H1 as [x [H5 H6]].
          destruct x.
          * inversion H5.
          * inversion H5.   
      - (* Third case, rule Lift_clo *)
        right.
        right.
        subst.
        apply equal_app in H4.
        destruct H4.
        + destruct H4 as [l [H5 H6]].
          subst.
          destruct l.
          * simpl in H6.
            rewrite cons_app in H6.
            apply map_expand in H6.
            destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
            subst.
            exists s2.
            exists (s ++ s2'). 
            {
            split.
            - rewrite app_nil_r in H2. 
              exact H2.
            - split.
              + destruct s1'.
                * inversion H8.
                * inversion H8. 
                  {
                  destruct s0.
                  - inversion H5.
                    subst.
                    apply map_eq_nil in H6.
                    subst.
                    rewrite <- app_nil_l in H3.
                    apply derives_step with (right:=s) in H3.
                    + exact H3.
                    + exact H1.
                  - inversion H5. 
                  }
              + rewrite map_app.
                reflexivity. 
            }
          * inversion H6.
            subst.  
            exists (s2 ++ map g_clo_sf_lift s ++ l).
            exists s''. 
            {
            split. 
            - apply derives_step with (right:= map g_clo_sf_lift s) in H2.
              + exact H2.
              + exact H0.
            - split.
              + exact H3.
              + repeat rewrite <- app_assoc.
                reflexivity. 
            }
        + destruct H4 as [l [H5 H6]].
          subst.
          symmetry in H6.
          apply map_expand in H6.
          destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
          subst.
          rewrite cons_app in H9.
          symmetry in H9.
          apply map_expand in H9.
          destruct H9 as [s1'' [s2'0 [H6 [H7 H8]]]].
          subst.
          exists s'.
          exists (s1' ++ s ++ s2'0).
          split.
          * exact H2.
          * { 
            split.
            - destruct s1''.
              + inversion H7.
              + simpl in H7.
                inversion H7.
                destruct s0.
                * inversion H5.
                  subst. 
                  apply map_eq_nil in H6.
                  subst. 
                  {
                  apply derives_step with (right:= s) in H3.
                  - exact H3.
                  - exact H1. 
                  } 
                * inversion H5.
            - rewrite <- app_assoc.
              repeat rewrite map_app.
              reflexivity. 
            } 
      }
Qed.

Lemma map_clo_1:
forall s: sentence,
map (@terminal_lift g_clo_nt terminal) s =
map g_clo_sf_lift (map (@terminal_lift non_terminal terminal) s).
Proof.
induction s.
- simpl.
  reflexivity.
- simpl.
  change (inr a) with (terminal_lift g_clo_nt a).
  rewrite IHs.
  reflexivity.
Qed.

Lemma map_clo_2:
forall s: sentence,
forall l: sf,
map (@terminal_lift g_clo_nt terminal) s = map g_clo_sf_lift l ->
(map (@terminal_lift non_terminal terminal) s) = l.
Proof.
induction s.
- intros l H.
  simpl in H.
  simpl.
  symmetry in H.
  apply map_eq_nil in H.
  symmetry.
  exact H.
- intros l H.
  simpl in H.
  simpl.
  destruct l.
  + simpl in H.
    inversion H.
  + simpl in H.
    inversion H.
    specialize (IHs l H2).
    rewrite IHs.
    destruct s0.
    * simpl in H1.
      inversion H1.
    * simpl in H1.
      inversion H1.
      change (inr t) with (terminal_lift non_terminal t).
      reflexivity.
Qed.

Lemma generates_start_symbol_clo:
forall g: cfg non_terminal terminal,
forall n: nat,
generates (g_clo g) (iter [inl (Transf_clo_nt (start_symbol g))] n).
Proof.
intros g n.
induction n.
- simpl.
  apply g_clo_correct.
  + exact [].
  + exact [].
- unfold generates.
  simpl.
  apply derives_trans with (s2:= [inl (start_symbol (g_clo g))] ++ [inl (Transf_clo_nt (start_symbol g))]).
  + apply derives_start.
    simpl.
    apply New1_clo.
  + simpl.
    change (inl (Transf_clo_nt (start_symbol g)) :: iter [inl (Transf_clo_nt (start_symbol g))] n) with
           ([inl (Transf_clo_nt (start_symbol g))] ++ iter [inl terminal (Transf_clo_nt (start_symbol g))] n).
    rewrite iter_comm.
    change [inl Start_clo; inl (Transf_clo_nt (start_symbol g))] with ([inl Start_clo] ++ [inl terminal (Transf_clo_nt (start_symbol g))]).
    apply derives_combine.
    split.
    * exact IHn.
    * apply derives_refl.
Qed.

Lemma produces_split:
forall g: cfg non_terminal terminal,
forall w: sentence,
produces (g_clo g) w ->
w = [] \/
exists w1 w2: sentence,
produces (g_clo g) w1 /\
produces g w2 /\
w = w1 ++ w2.
Proof.
intros g w H.
unfold produces in H.
apply g_clo_correct_inv in H.
destruct H as [H | [H | H]].
- left.
  apply map_eq_nil in H. 
  exact H.
- destruct w.
  + simpl in H.
    inversion H.
  + simpl in H.
    inversion H.
- right.
  destruct H as [s' [s'' [H1 [H2 H3]]]].
  symmetry in H3. 
  apply map_expand in H3.
  destruct H3 as [s1' [s2' [ H4 [H5 H6]]]].
  exists s1', s2'.
  split.
  + unfold produces.
    rewrite H5.
    exact H1.
  + split.   
    * unfold produces.
      apply map_clo_2 in H6.
      rewrite H6.
      exact H2.
    * exact H4.
Qed.

Lemma derives_g_clo_derives_g:
forall g: cfg non_terminal terminal,
forall s: sfc,
forall w: sentence,
derives (g_clo g) s (map (terminal_lift g_clo_nt (terminal:=terminal)) w) ->
forall sg: sf, 
s = (map g_clo_sf_lift sg) ->
derives g sg (map (@terminal_lift non_terminal terminal) w).
Proof.
intros g s w.
rewrite derives_equiv_derives2.
intros H sg Hsg.
rewrite derives_equiv_derives2.
remember (map (terminal_lift g_clo_nt (terminal:=terminal)) w) as W.
revert sg Hsg HeqW. 
induction H.
- intros.
  subst.
  symmetry in HeqW.
  apply map_clo_2 in HeqW.
  rewrite HeqW.
  apply derives2_refl.
- intros.
  subst. 
  simpl in H0. 
  inversion H0. 
  + clear H0.
    subst.
    apply map_expand in Hsg.
    destruct Hsg as [s1' [s2' [_ [_ Hsg]]]].
    destruct s2'. 
    * inversion Hsg.
    * inversion Hsg.
      {
      destruct s.
      - simpl in H1.
        inversion H1.
      - simpl in H1.
        inversion H1.
      } 
  + clear H0. 
    subst. 
    apply map_expand in Hsg.
    destruct Hsg as [s1' [s2' [_ [_ Hsg]]]].
    destruct s2'. 
    * inversion Hsg.
    * inversion Hsg.
      {
      destruct s.
      - simpl in H1.
        inversion H1.
      - simpl in H1.
        inversion H1.
      } 
  + clear H0. 
    subst. 
    apply map_expand in Hsg. 
    destruct Hsg as [s1' [s2' [Hs [Hs1 Hs2]]]].
    destruct s2' as [|[nn|nn] s2'].
    * inversion Hs2.
    * inversion Hs2.
      clear Hs2.
      subst.
      {
      apply derives2_step with (right:= s).
      - apply IHderives2.
        + rewrite map_app. 
          rewrite map_app. 
          reflexivity.
        + reflexivity.
      - exact H1.
      }
    * inversion Hs2.
Qed.

Lemma g_clo_correct_inv_v2:
forall g: cfg non_terminal terminal,
forall w: sentence,
produces (g_clo g) w ->
exists w': list sentence, 
(forall s: sentence, In s w' -> produces g s) /\ w = flat w'.
Proof.
unfold produces, generates.
intros g w.
rewrite derives_equiv_derives6.
intros [n].
generalize (Le.le_refl n).
generalize n at 1 3 as i.
generalize dependent w.
induction n.
- intros w i Hi H.  
  destruct i. 
  + inversion H. 
    clear H.
    destruct w.
    * inversion H0. 
    * inversion H0.
  + omega.
- intros.
  inversion H0.
  clear H0.
  + destruct w.
    * inversion H4.
    * inversion H4.
  + simpl in H1.
    inversion H1.
    assert (s1 = []). 
      {
      destruct s1.
      - reflexivity.
      - inversion H7. 
        destruct s1. 
        + inversion H9. 
        + inversion H9. 
      }
    assert (s2 = []). 
      {
      rewrite H6 in H1.
      inversion H1. 
      reflexivity.
      }
    subst.
    simpl in *.
    inversion H2. 
    clear H2.
    subst.
    * rewrite app_nil_r in H4.
      apply derives6_split in H4.
      destruct H4 as [s1 [s2 [n1 [n2 [HH1 [HH2 [HH3 HH4]]]]]]].
      symmetry in HH1.
      apply map_expand in HH1.
      destruct HH1 as [w1 [w2 [Hw [Hw1 Hw2]]]].
      subst.
      assert (Hn1: n1 <= n).
        { 
        omega.
        }
      specialize (IHn w1 _ Hn1 HH3).
      destruct IHn as [w1' [Hw1A Hw1B]].
      exists (w1' ++ [w2]).
      {
      split.
      - intros.
        apply in_app_or in H2. 
        destruct H2 as [H2 | H2]. 
        + auto.
        + simpl in H2.
          destruct H2 as [H2 | H2].
          * subst.
            {
            eapply derives_g_clo_derives_g.
            - rewrite derives_equiv_derives6.
              exists n2.
              eauto.
            - reflexivity.
            }
          * contradiction. 
      - rewrite flat_app. 
        simpl. 
        subst.
        rewrite app_nil_r. 
        reflexivity.
      }
    * rewrite <- H5 in H4. 
      simpl in H4. 
      {
      inversion H4.
      - exists []. 
        split. 
        + intros s0 H11.
          inversion H11.
        + symmetry in H10. 
          apply map_eq_nil in H10. 
          rewrite H10.
          simpl.
          reflexivity.
      - destruct s1. 
        + inversion H6.
        + inversion H6.
      }
    * rewrite <- H5 in H1. 
      inversion H1.
Qed.

End Closure.

(* --------------------------------------------------------------------- *)
(* AS LANGUAGES                                                          *)
(* --------------------------------------------------------------------- *)

Section Closure_2.

Variable non_terminal terminal: Type.

Notation sentence:= (list terminal).

Inductive l_clo (l: lang terminal): lang terminal:=
| l_clo_nil: l_clo l []
| l_clo_app: forall s1 s2: sentence, (l_clo l) s1 -> l s2 -> l_clo l (s1 ++ s2). 

Theorem l_clo_is_cfl:
forall l: lang terminal,
cfl l ->
cfl (l_clo l).
Proof.
intros l H.
unfold cfl.
unfold cfl in H.
unfold lang_eq.
unfold lang_eq in H.
unfold lang_of_g.
unfold lang_of_g in H.
destruct H as [non_terminal0 [g H]].
exists (g_clo_nt non_terminal0), (g_clo g).
intros w.
split.
- intros H1.
  induction H1.
  + apply g_clo_correct. 
    * exact []. 
    * exact []. 
  + specialize (H s2). 
    destruct H as [H _].
    specialize (H H0).
    unfold produces in H.
    unfold produces in IHl_clo.
    unfold produces.
    rewrite map_app.
    repeat rewrite map_clo_1.
    rewrite map_clo_1 in IHl_clo. 
    apply g_clo_correct with (g:= g).
    split.
    * exact IHl_clo.
    * exact H.
- intros H1.
  apply g_clo_correct_inv_v2 in H1.
  destruct H1 as [w' [H2 H3]].
  subst.
  assert (forall s : sentence, In s w' -> l s).
    {
    intros s H4.
    specialize (H2 s H4).
    specialize (H s).
    destruct H as [_ H].
    specialize (H H2).
    exact H.
    }
  {
  induction w' using rev_ind.  
  - simpl.
    constructor.
  - assert (flat (w' ++ [x]) = flat w' ++ x).
      { 
      rewrite flat_app.
      simpl.
      rewrite app_nil_r.
      reflexivity.
      }
    rewrite H1.
    constructor.
    + apply IHw'.
      * intros s H5.
        apply H2.
        apply in_or_app.
        left.
        exact H5.
      * intros s H5.
        apply H0.
        apply in_or_app.
        left.
        exact H5.
    + apply H0.
      apply in_or_app. 
      right. 
      simpl.
      left.
      reflexivity.
  }
Qed.

Theorem l_clo_correct:
forall l: lang terminal,
(l_clo l) [] /\ 
forall s1 s2: sentence,
(l_clo l) s1 -> 
l s2 ->
(l_clo l) (s1 ++ s2).
Proof.
intros l.
split.
- apply l_clo_nil. 
- intros s1 s2 H1 H2.
  apply l_clo_app.
  + exact H1.
  + exact H2.
Qed.

Theorem l_uni_correct_inv:
forall l: lang terminal,
forall s: sentence,
(l_clo l) s ->
s = [] \/
exists s1 s2: sentence,
s = s1 ++ s2 /\
(l_clo l) s1 /\
l s2.
Proof.
intros l s H.
inversion H.
- left.
  reflexivity.
- right.
  exists s1, s2.
  split.
  + reflexivity.
  + split.
    * exact H0.
    * exact H1.
Qed.

End Closure_2. 
