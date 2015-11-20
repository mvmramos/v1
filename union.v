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

Require Import misc_list.
Require Import cfg.
Require Import cfl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

(* --------------------------------------------------------------------- *)
(* UNION - DEFINITIONS                                                   *)
(* --------------------------------------------------------------------- *)

Section Union.

Variables non_terminal_1 non_terminal_2 terminal: Type.

Inductive g_uni_nt: Type:=
| Start_uni
| Transf1_uni_nt: non_terminal_1 -> g_uni_nt
| Transf2_uni_nt: non_terminal_2 -> g_uni_nt.

Notation sf1:= (list (non_terminal_1 + terminal)).
Notation sf2:= (list (non_terminal_2 + terminal)).
Notation sfu:= (list (g_uni_nt + terminal)).
Notation nlist:= (list g_uni_nt).
Notation tlist:= (list terminal).

Definition g_uni_sf_lift1 (c: non_terminal_1 + terminal): g_uni_nt + terminal:=
  match c with
  | inl nt => inl (Transf1_uni_nt nt)
  | inr t  => inr t
  end.

Definition g_uni_sf_lift2 (c: non_terminal_2 + terminal): g_uni_nt + terminal:=
  match c with
  | inl nt => inl (Transf2_uni_nt nt)
  | inr t  => inr t
  end.

Inductive g_uni_rules (g1: cfg non_terminal_1 terminal) (g2: cfg non_terminal_2 terminal): g_uni_nt -> sfu -> Prop :=
| Start1_uni: g_uni_rules g1 g2 Start_uni [inl (Transf1_uni_nt (start_symbol g1))]
| Start2_uni: g_uni_rules g1 g2 Start_uni [inl (Transf2_uni_nt (start_symbol g2))]
| Lift1_uni: forall nt: non_terminal_1,
             forall s: list (non_terminal_1 + terminal),
             rules g1 nt s ->
             g_uni_rules g1 g2 (Transf1_uni_nt nt) (map g_uni_sf_lift1 s)
| Lift2_uni: forall nt: non_terminal_2,
             forall s: list (non_terminal_2 + terminal),
             rules g2 nt s ->
             g_uni_rules g1 g2 (Transf2_uni_nt nt) (map g_uni_sf_lift2 s).

Lemma g_uni_finite:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
exists n: nat,
exists ntl: list g_uni_nt,
exists tl: tlist,
In Start_uni ntl /\
forall left: g_uni_nt,
forall right: sfu,
g_uni_rules g1 g2 left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: g_uni_nt, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
intros g1 g2.
destruct (rules_finite g1) as [n1 [ntl1 [tl1 H1]]].
destruct (rules_finite g2) as [n2 [ntl2 [tl2 H2]]].
exists (S (max n1 n2)), (Start_uni :: (map Transf1_uni_nt ntl1) ++ (map Transf2_uni_nt ntl2)), (tl1 ++ tl2).
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
      assert (H3: n1 >= n2 \/ n1 <= n2) by omega.
      {
      destruct H3 as [H3 | H3].
      - apply max_l in H3. 
        rewrite H3.
        omega.
      - assert (H3':= H3).
        apply max_r in H3. 
        rewrite H3.
        omega.
      }  
    * destruct H2 as [_ H2].
      subst. 
      specialize (H2 nt s H0). 
      destruct H2 as [H2 _]. 
      rewrite map_length.
      assert (H3: n1 >= n2 \/ n1 <= n2) by omega.
      {
      destruct H3 as [H3 | H3].
      - assert (H3':= H3).
        apply max_l in H3. 
        rewrite H3.
        omega.
      - apply max_r in H3. 
        rewrite H3.
        omega.
      }  
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
        apply in_or_app.
        left.
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
      - simpl.
        right. 
        apply in_or_app.
        right.
        destruct H2 as [_ H2].
        specialize (H2 nt s H0).
        destruct H2 as [_ [H5 [_ _]]]. 
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
            right. 
            apply in_or_app.
            left.
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
          * contradiction.
        + subst. 
          intros s H4.
          simpl in H4.
          destruct H4 as [H4 | H4].
          * inversion H4.
            simpl. 
            right. 
            apply in_or_app.
            right.
            destruct H2 as [H2 _].
            apply in_split in H2.
            destruct H2 as [l1 [l2 H2]].
            rewrite H2.
            rewrite map_app.
            apply in_or_app.
            right. 
            simpl. 
            left.
            reflexivity.
          * contradiction.
        + subst. 
          intros s0 H4.
          destruct H1 as [_ H1].
          specialize (H1 nt s H0).
          destruct H1 as [_ [_ [H5 _]]].
          simpl. 
          right.
          apply in_or_app. 
          left.
          destruct s0.
          * apply in_split in H4.
            destruct H4 as [l1 [l2 H4]]. 
            symmetry in H4. 
            apply map_expand in H4.
            destruct H4 as [s1' [s2' [H4' [H4'' H4''']]]].
            change (inl Start_uni :: l2) with ([inl Start_uni] ++ l2) in H4'''.
            symmetry in H4'''. 
            apply map_expand in H4'''.
            destruct H4''' as [s1'0 [s2'0 [H5' [H5'' H5''']]]].
            {
            destruct s1'0.
            - inversion H5''.
            - simpl in H5''. 
              inversion H5''.
              destruct s0.
              + simpl in H3.
                inversion H3.
              + simpl in H3.
                inversion H3.
            }
          * assert (H6: In (inl n) s). 
              { 
              apply in_split in H4. 
              destruct H4 as [l1 [l2 H4]]. 
              symmetry in H4. 
              apply map_expand in H4.
              destruct H4 as [s1' [s2' [H4' [H4'' H4''']]]].
              change (inl (Transf1_uni_nt n) :: l2) with ([inl (Transf1_uni_nt n)] ++ l2) in H4'''.
              symmetry in H4'''. 
              apply map_expand in H4'''.
              destruct H4''' as [s1'0 [s2'0 [H5' [H5'' H5''']]]].
              destruct s1'0.
              - inversion H5''.
              - inversion H5''.
                destruct s0.
                + simpl in H3.
                  inversion H3.
                  subst.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  reflexivity.
                + simpl in H3.
                  inversion H3.
              }
            specialize (H5 n H6).
            apply in_map.
            exact H5.
          * apply in_split in H4.
            destruct H4 as [l1 [l2 H4]]. 
            symmetry in H4. 
            apply map_expand in H4.
            destruct H4 as [s1' [s2' [H4' [H4'' H4''']]]].
            change (inl (Transf2_uni_nt n) :: l2) with ([inl (Transf2_uni_nt n)] ++ l2) in H4'''.
            symmetry in H4'''. 
            apply map_expand in H4'''.
            destruct H4''' as [s1'0 [s2'0 [H5' [H5'' H5''']]]].
            {
            destruct s1'0.
            - inversion H5''.
            - simpl in H5''. 
              inversion H5''.
              destruct s0.
              + simpl in H3.
                inversion H3.
              + simpl in H3.
                inversion H3.
            }
        + subst. 
          intros s0 H4.
          destruct H2 as [_ H2].
          specialize (H2 nt s H0).
          destruct H2 as [_ [_ [H5 _]]].
          simpl. 
          right.
          apply in_or_app. 
          right.
          destruct s0.
          * apply in_split in H4.
            destruct H4 as [l1 [l2 H4]]. 
            symmetry in H4. 
            apply map_expand in H4.
            destruct H4 as [s1' [s2' [H4' [H4'' H4''']]]].
            change (inl Start_uni :: l2) with ([inl Start_uni] ++ l2) in H4'''.
            symmetry in H4'''. 
            apply map_expand in H4'''.
            destruct H4''' as [s1'0 [s2'0 [H5' [H5'' H5''']]]].
            {
            destruct s1'0.
            - inversion H5''.
            - simpl in H5''. 
              inversion H5''.
              destruct s0.
              + simpl in H3.
                inversion H3.
              + simpl in H3.
                inversion H3.
            }
          * apply in_split in H4.
            destruct H4 as [l1 [l2 H4]]. 
            symmetry in H4. 
            apply map_expand in H4.
            destruct H4 as [s1' [s2' [H4' [H4'' H4''']]]].
            change (inl (Transf1_uni_nt n) :: l2) with ([inl (Transf1_uni_nt n)] ++ l2) in H4'''.
            symmetry in H4'''. 
            apply map_expand in H4'''.
            destruct H4''' as [s1'0 [s2'0 [H5' [H5'' H5''']]]].
            {
            destruct s1'0.
            - inversion H5''.
            - simpl in H5''. 
              inversion H5''.
              destruct s0.
              + simpl in H3.
                inversion H3.
              + simpl in H3.
                inversion H3.
            }
          * assert (H6: In (inl n) s). 
              { 
              apply in_split in H4. 
              destruct H4 as [l1 [l2 H4]]. 
              symmetry in H4. 
              apply map_expand in H4.
              destruct H4 as [s1' [s2' [H4' [H4'' H4''']]]].
              change (inl (Transf2_uni_nt n) :: l2) with ([inl (Transf2_uni_nt n)] ++ l2) in H4'''.
              symmetry in H4'''. 
              apply map_expand in H4'''.
              destruct H4''' as [s1'0 [s2'0 [H5' [H5'' H5''']]]].
              destruct s1'0.
              - inversion H5''.
              - inversion H5''.
                destruct s0.
                + simpl in H3.
                  inversion H3.
                  subst.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  reflexivity.
                + simpl in H3.
                  inversion H3.
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
          * contradiction.
        + subst. 
          intros s H4.
          simpl in H4.
          destruct H4 as [H4 | H4].
          * inversion H4.
          * contradiction.
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
              + simpl in H3.
                inversion H3.
              + simpl in H3.
                inversion H3.
                subst.
                apply in_or_app.
                right.
                simpl.
                left.
                reflexivity.
            }
          specialize (H5 s0 H6).
          apply in_or_app.
          left.
          exact H5. 
        + subst. 
          intros s0 H4.
          destruct H2 as [_ H2].
          specialize (H2 nt s H0).
          destruct H2 as [_ [_ [_ H5]]].
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
              + simpl in H3.
                inversion H3.
              + simpl in H3.
                inversion H3.
                subst.
                apply in_or_app.
                right.
                simpl.
                left.
                reflexivity.
            }
          specialize (H5 s0 H6).
          apply in_or_app.
          right.
          exact H5. 
      }
Qed.

Definition g_uni (g1: cfg non_terminal_1 terminal) (g2: cfg non_terminal_2 terminal): (cfg g_uni_nt terminal):= {|
start_symbol:= Start_uni;
rules:= g_uni_rules g1 g2;
rules_finite:= g_uni_finite g1 g2
|}.

(* --------------------------------------------------------------------- *)
(* UNION - LEMMAS                                                        *)
(* --------------------------------------------------------------------- *)

Lemma derives_add_uni_left:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s s': sf1,
derives g1 s s' ->
derives (g_uni g1 g2) 
        (map g_uni_sf_lift1 s)
        (map g_uni_sf_lift1 s').
Proof.
intros g1 g2 s s' H.
induction H as [|x y z left right H1 H2 H3].
- apply derives_refl.
- rewrite map_app.
  rewrite map_app.
  rewrite map_app in H2. 
  simpl in H2.
  apply derives_step with (left:=(Transf1_uni_nt left)).
  exact H2.
  simpl.
  apply Lift1_uni.
  exact H3.
Qed.

Lemma derives_add_uni_right :
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s s': sf2,
derives g2 s s' ->
derives (g_uni g1 g2) 
        (map g_uni_sf_lift2 s)
        (map g_uni_sf_lift2 s').
Proof.
intros g1 g2 s s' H.
induction H as [|x y z left right H1 H2 H3].
- apply derives_refl.
- rewrite map_app.
  rewrite map_app.
  rewrite map_app in H2. 
  simpl in H2.
  apply derives_step with (left:=(Transf2_uni_nt left)).
  exact H2.
  simpl.
  apply Lift2_uni.
  exact H3.
Qed.

Theorem g_uni_correct_left:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s: sf1,
generates g1 s ->
generates (g_uni g1 g2) (map g_uni_sf_lift1 s).
Proof.
unfold generates. 
intros g1 g2 s H.
apply derives_trans with (s2:= map g_uni_sf_lift1 [(inl (start_symbol g1))]).
- simpl. 
  match goal with
  | |- derives _ ?s1 ?s2 =>
       change s1 with ([] ++ s1)%list;
       change s2 with ([] ++ s2 ++ [])%list
  end.
  apply derives_step with (left:= Start_uni).
  + apply derives_refl.
  + simpl.
    apply Start1_uni.
- apply derives_add_uni_left.
  exact H.
Qed.

Theorem g_uni_correct_right:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s: sf2,
generates g2 s -> generates (g_uni g1 g2) (map g_uni_sf_lift2 s).
Proof.
unfold generates. 
intros g1 g2 s H.
apply derives_trans with (s2:= map g_uni_sf_lift2 [(inl (start_symbol g2))]).
- simpl.
  match goal with
  | |- derives _ ?s1 ?s2 =>
       change s1 with ([] ++ s1)%list;
       change s2 with ([] ++ s2 ++ [])%list
  end.
  apply derives_step with (left:= Start_uni).
  + apply derives_refl.
  + simpl.
    apply Start2_uni.
- apply derives_add_uni_right.
  exact H.
Qed.

Theorem g_uni_correct:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s1: sf1,
forall s2: sf2,
(generates g1 s1 -> generates (g_uni g1 g2) (map g_uni_sf_lift1 s1)) /\
(generates g2 s2 -> generates (g_uni g1 g2) (map g_uni_sf_lift2 s2)).
Proof.
split.
- apply g_uni_correct_left.
- apply g_uni_correct_right.
Qed.

Theorem g_uni_correct_inv:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s: sfu,
generates (g_uni g1 g2) s ->
(s=[inl (start_symbol (g_uni g1 g2))]) \/
(exists s1: sf1,
(s=(map g_uni_sf_lift1 s1) /\ generates g1 s1)) \/
(exists s2: sf2,
(s=(map g_uni_sf_lift2 s2) /\ generates g2 s2)).
Proof.
unfold generates.
intros g1 g2 s.
remember [inl (start_symbol (g_uni g1 g2))] as init.
intro H.
induction H.
  (* Base case *)
- left. reflexivity.
- (* Induction hypothesis *)
  subst.
  specialize (IHderives eq_refl).
  destruct IHderives.
  + (* IHderives, first case *) 
    destruct s2.
    * (* First case, left = Start_uni *)
      simpl in H1. inversion H1. subst. {
      inversion H0. subst. clear H1.
      - (* First case, right = start_symbol g1 *) 
        simpl in *. 
        right.
        left.
        exists [inl (start_symbol g1)].
        split.
        + simpl. reflexivity.
        + apply derives_refl.
      - (* Second case, right = start_symbol g2 *)
        simpl in *.
        right.
        right.
        exists [inl (start_symbol g2)].
        split.
        + simpl. reflexivity.
        + apply derives_refl. }
    * (* Second case, left = non_terminal (g_uni g1 g2 *)
      simpl in H1.
      inversion H1. {
      destruct s2.
      - simpl in H4. inversion H4.
      - inversion H4. }
  + (* IHderives, second case *)
    destruct H1.
    * (* H1, first case: comes from g1 *)
      destruct H1 as [x [H1 H2]]. 
      {
      inversion H0.
      - (* First rule: Start1_uni *)
        (* Contradiction, x cannot contain Start_uni *)
        simpl in *. subst. 
        destruct s2.
        + simpl in H1. 
          destruct x.
          * inversion H1. 
          * simpl in H1. 
            inversion H1. {
            destruct s.
            - inversion H4.
            - inversion H4. }
        + simpl in *.
          assert (IN: In (inl Start_uni) (map g_uni_sf_lift1 x)). 
            { 
            rewrite <- H1. 
            simpl. 
            right. 
            apply in_app_iff. 
            right. 
            simpl. 
            left. 
            reflexivity. 
            }
          rewrite in_map_iff in IN.
          destruct IN.
          destruct H3.
          destruct x0.
          * simpl in H3. inversion H3.
          * simpl in H3. inversion H3. 
      - (* Second rule: Start2_uni *)
        (* Contradiction, x cannot contain Start_uni *)
        simpl in *. subst. 
        destruct s2.
        + simpl in H1. 
          destruct x.
          * inversion H1. 
          * simpl in H1. inversion H1. {
            destruct s.
            - inversion H4.
            - inversion H4. }
        + simpl in *.
          assert (IN: In (inl Start_uni) (map g_uni_sf_lift1 x)). 
            { 
            rewrite <- H1. 
            simpl. 
            right. 
            apply in_app_iff. 
            right. 
            simpl. 
            left. 
            reflexivity. 
            }
          rewrite in_map_iff in IN.
          destruct IN.
          destruct H3.
          destruct x0.
          * simpl in H3. inversion H3.
          * simpl in H3. inversion H3. 
      - (* Third rule: Lift1_uni *)
        (* Should be true *)
        right.
        left.
        apply map_expand in H1.
        destruct H1 as [s1' [s2'[H6 [H7 H8]]]].
        replace (inl left::s3) with ([inl left]++s3) in H8.
        + symmetry in H8.
          apply map_expand in H8.
          destruct H8 as [m [n [H9 [H10 H11]]]].
          exists (s1'++s++n).
          split.
          * subst.
            repeat rewrite map_app.
            reflexivity.
          * subst. 
            {
            destruct m. 
            - inversion H10.
            - simpl in H10.
              inversion H10.
              destruct s0.
              + inversion H4.
                subst.
                apply map_eq_nil in H5.
                subst.
                apply derives_step with (right:=s) in H2.
                exact H2.
                exact H3.
              + inversion H4. 
            }
        + simpl. 
          reflexivity.
      - (* Forth rule: Lift2_uni *)
        (* Should be false *)
        simpl in *. 
        subst. 
        assert (IN: In (inl (Transf2_uni_nt nt)) (map g_uni_sf_lift1 x)). 
          { 
          rewrite <- H1. 
          rewrite in_app_iff. 
          right. 
          simpl. 
          left. 
          reflexivity. 
          }
        rewrite in_map_iff in IN.
        destruct IN as [x0 [H4 H5]].
        destruct x0.
        + inversion H4. 
        + inversion H4. 
      }
    * (* H1, second case: comes from g2 *)
      destruct H1 as [x [H1 H2]]. 
      {
      inversion H0.
      - (* First rule: Start1_uni *)
        (* Contradiction, x cannot contain Start_uni *)
        simpl in *. subst. 
        destruct s2.
        + simpl in H1. 
          destruct x.
          * inversion H1. 
          * simpl in H1. 
            inversion H1. 
            {
            destruct s.
            - inversion H4.
            - inversion H4. 
            }
        + simpl in *.
          assert (IN: In (inl Start_uni) (map g_uni_sf_lift2 x)). 
            { 
            rewrite <- H1. 
            simpl. 
            right. 
            apply in_app_iff. 
            right. simpl. 
            left. 
            reflexivity. 
            }
          rewrite in_map_iff in IN.
          destruct IN.
          destruct H3.
          destruct x0.
          * simpl in H3. inversion H3.
          * simpl in H3. inversion H3. 
      - (* Second rule: Start2_uni *)
        (* Contradiction, x cannot contain Start_uni *)
        simpl in *. 
        subst. 
        destruct s2.
        + simpl in H1. 
          destruct x.
          * inversion H1. 
          * simpl in H1. 
            inversion H1. 
            {
            destruct s.
            - inversion H4.
            - inversion H4. 
            }
        + simpl in *.
          assert (IN: In (inl Start_uni) (map g_uni_sf_lift2 x)). 
            { 
            rewrite <- H1. 
            simpl. 
            right. 
            apply in_app_iff. 
            right. 
            simpl. 
            left. 
            reflexivity. 
            }
          rewrite in_map_iff in IN.
          destruct IN.
          destruct H3.
          destruct x0.
          * simpl in H3. 
            inversion H3.
          * simpl in H3.   
            inversion H3. 
      - (* Third rule: Lift1_uni *)
        (* Should be false *)
        simpl in *. 
        subst. 
        assert (IN: In (inl (Transf1_uni_nt nt)) (map g_uni_sf_lift2 x)). 
          { 
          rewrite <- H1. 
          rewrite in_app_iff. 
          right. 
          simpl. 
          left. 
          reflexivity. 
          }
        rewrite in_map_iff in IN.
        destruct IN as [x0 [H4 H5]].
        destruct x0.
        + inversion H4. 
        + inversion H4.
      - (* Forth rule: Lift2_uni *)
        (* Should be true *)
        right.
        right.
        apply map_expand in H1.
        destruct H1 as [s1' [s2'[H6 [H7 H8]]]].
        replace (inl left::s3) with ([inl left]++s3) in H8.
        + symmetry in H8.
          apply map_expand in H8.
          destruct H8 as [m [n [H9 [H10 H11]]]].
          exists (s1'++s++n).
          split.
          * subst.
            repeat rewrite map_app.
            reflexivity.
          * subst. 
            {
            destruct m. 
            - inversion H10.
            - simpl in H10.
              inversion H10.
              destruct s0.
              + inversion H4.
                subst.
                apply map_eq_nil in H5.
                subst.
                apply derives_step with (right:=s) in H2.
                exact H2.
                exact H3.
              + inversion H4. 
            }
        + simpl. 
          reflexivity. 
      }
Qed.

End Union.

(* --------------------------------------------------------------------- *)
(* AS LANGUAGES                                                          *)
(* --------------------------------------------------------------------- *)

Section Union_2.

Variable non_terminal_1 non_terminal_2 terminal: Type.

Notation sentence:= (list terminal).

Lemma map_uni_1:
forall s: sentence,
map (@g_uni_sf_lift1 non_terminal_1 non_terminal_2 terminal) (map (@terminal_lift non_terminal_1 terminal) s) =
map (@terminal_lift (@g_uni_nt non_terminal_1 non_terminal_2) terminal) s.
Proof.
induction s.
- simpl.
  reflexivity.
- simpl.
  change (inr a) with (terminal_lift (g_uni_nt non_terminal_1 non_terminal_2) a).
  rewrite IHs.
  reflexivity.
Qed.

Lemma map_uni_2:
forall s: sentence,
map (@g_uni_sf_lift2 non_terminal_1 non_terminal_2 terminal) (map (@terminal_lift non_terminal_2 terminal) s) =
map (@terminal_lift (@g_uni_nt non_terminal_1 non_terminal_2) terminal) s.
Proof.
induction s.
- simpl.
  reflexivity.
- simpl.
  change (inr a) with (terminal_lift (g_uni_nt non_terminal_1 non_terminal_2) a).
  rewrite IHs.
  reflexivity.
Qed.

Lemma map_uni_3:
forall s: sentence,
forall l: list (non_terminal_1 + terminal),
map (@terminal_lift (g_uni_nt non_terminal_1 non_terminal_2) terminal) s = 
map (@g_uni_sf_lift1 non_terminal_1 non_terminal_2 terminal) l ->
l = map (@terminal_lift non_terminal_1 terminal) s.
Proof.
induction s.
- intros l H.
  simpl in H.
  symmetry in H. 
  apply map_eq_nil in H.
  subst.
  simpl.
  reflexivity.
- intros l H.
  remember (terminal_lift (g_uni_nt non_terminal_1 non_terminal_2) (terminal:=terminal)) as m1.
  remember (g_uni_sf_lift1 non_terminal_2 (terminal:=terminal)) as m2.
  remember (terminal_lift non_terminal_1 (terminal:=terminal)) as m3.
  simpl in H.
  destruct l.
  + simpl in H.
    inversion H.
  + simpl in H.
    inversion H.
    specialize (IHs l H2).
    rewrite IHs.
    simpl.
    destruct s0.
    * {
      replace (m2 (inl n)) with (inl terminal (Transf1_uni_nt non_terminal_2 n)) in H1.
      - replace (m1 a) with (inr (g_uni_nt non_terminal_1 non_terminal_2) a) in H1. 
        + inversion H1.
        + rewrite Heqm1.
          change (inr a) with (terminal_lift (g_uni_nt non_terminal_1 non_terminal_2) a).
          reflexivity.
      - rewrite Heqm2.
        simpl.
        reflexivity.
      }
    * {
      replace (m2 (inr t)) with (inr (g_uni_nt non_terminal_1 non_terminal_2) t) in H1.
      - replace (m1 a) with (inr (g_uni_nt non_terminal_1 non_terminal_2) a) in H1. 
        + inversion H1.
          replace (m3 t) with (inr non_terminal_1 t).
          * reflexivity.
          * rewrite Heqm3.
            change (inr t) with (terminal_lift non_terminal_1 t).
            reflexivity.
        + rewrite Heqm1.
          change (inr a) with (terminal_lift (g_uni_nt non_terminal_1 non_terminal_2) a).
          reflexivity.
      - rewrite Heqm2. 
        simpl.
        reflexivity.
      }
Qed.      

Lemma map_uni_4:
forall s: sentence,
forall l: list (non_terminal_2 + terminal),
map (@terminal_lift (@g_uni_nt non_terminal_1 non_terminal_2) terminal) s =
map (@g_uni_sf_lift2 non_terminal_1 non_terminal_2 terminal) l ->
l = map (@terminal_lift non_terminal_2 terminal) s.
Proof.
induction s.
- intros l H.
  simpl in H.
  symmetry in H. 
  apply map_eq_nil in H.
  subst.
  simpl.
  reflexivity.
- intros l H.
  remember (terminal_lift (g_uni_nt non_terminal_1 non_terminal_2) (terminal:=terminal)) as m1.
  remember (g_uni_sf_lift2 non_terminal_1 (terminal:=terminal)) as m2.
  remember (terminal_lift non_terminal_2 (terminal:=terminal)) as m3.
  simpl in H.
  destruct l.
  + simpl in H.
    inversion H.
  + simpl in H.
    inversion H.
    specialize (IHs l H2).
    rewrite IHs.
    simpl.
    destruct s0.
    * {
      replace (m2 (inl n)) with (inl terminal (Transf2_uni_nt non_terminal_1 n)) in H1.
      - replace (m1 a) with (inr (g_uni_nt non_terminal_1 non_terminal_2) a) in H1. 
        + inversion H1.
        + rewrite Heqm1.
          change (inr a) with (terminal_lift (g_uni_nt non_terminal_1 non_terminal_2) a).
          reflexivity.
      - rewrite Heqm2.
        simpl.
        reflexivity.
      }
    * {
      replace (m2 (inr t)) with (inr (g_uni_nt non_terminal_1 non_terminal_2) t) in H1.
      - replace (m1 a) with (inr (g_uni_nt non_terminal_1 non_terminal_2) a) in H1. 
        + inversion H1.
          replace (m3 t) with (inr non_terminal_2 t).
          * reflexivity.
          * rewrite Heqm3.
            change (inr t) with (terminal_lift non_terminal_2 t).
            reflexivity.
        + rewrite Heqm1.
          change (inr a) with (terminal_lift (g_uni_nt non_terminal_1 non_terminal_2) a).
          reflexivity.
      - rewrite Heqm2. 
        simpl.
        reflexivity.
      }
Qed.

Inductive l_uni (l1 l2: lang terminal): lang terminal:=
| l_uni_l1: forall s: sentence, l1 s -> l_uni l1 l2 s
| l_uni_l2: forall s: sentence, l2 s -> l_uni l1 l2 s.

(*
Definition l_uni (l1 l2: lang terminal): lang terminal:=
fun s: sentence => l1 s \/ l2 s.
*)

End Union_2.

Variable terminal: Type.

Notation sentence:= (list terminal).

Theorem l_uni_is_cfl:
forall l1 l2: lang terminal,
cfl l1 ->
cfl l2 ->
cfl (l_uni l1 l2).
Proof.
intros l1 l2 H1 H2.
unfold cfl.
unfold cfl in H1.
unfold cfl in H2.
unfold lang_eq.
unfold lang_eq in H1.
unfold lang_eq in H2.
unfold lang_of_g.
unfold lang_of_g in H1.
unfold lang_of_g in H2.
destruct H1 as [non_terminal_1 [g1 H1]].
destruct H2 as [non_terminal_2 [g2 H2]].
exists (g_uni_nt non_terminal_1 non_terminal_2), (g_uni g1 g2).
intros w.
split.
- intros H3.
  inversion H3.
  + subst.
    specialize (H1 w).
    destruct H1 as [H1 _].
    specialize (H1 H).
    unfold produces in H1.
    unfold produces. 
    rewrite <- (map_uni_1 _ _ w).
    apply g_uni_correct.
    * exact [].
    * exact H1.
  + subst.
    specialize (H2 w).
    destruct H2 as [H2 _].
    specialize (H2 H).
    unfold produces in H2.
    unfold produces.
    rewrite <- (map_uni_2 _ _ w).
    apply g_uni_correct.
    * exact []. 
    * exact H2.
- intros H4.
  apply g_uni_correct_inv in H4.
  destruct H4 as [H4 | H4].
  + destruct w.
    * simpl in H4.
      inversion H4.
    * simpl in H4.
      inversion H4.
  + destruct H4 as [H4 | H4].
    * destruct H4 as [s1 [H4 H5]].
      left.
      specialize (H1 w).
      destruct H1 as [_ H1].
      apply H1.
      unfold produces.
      apply map_uni_3 in H4.
      rewrite H4 in H5.
      exact H5.
    * destruct H4 as [s1 [H4 H5]].
      right.
      specialize (H2 w).
      destruct H2 as [_ H2].
      apply H2.
      unfold produces.
      apply map_uni_4 in H4.
      rewrite H4 in H5.
      exact H5.
Qed.

Theorem l_uni_correct:
forall l1 l2: lang terminal,
forall s: sentence,
(l1 s \/ l2 s) -> (l_uni l1 l2) s.
Proof.
intros l1 l2 s H.
destruct H as [H | H].
- apply l_uni_l1.
  exact H.
- apply l_uni_l2.
  exact H.
Qed.

Theorem l_uni_correct_inv:
forall l1 l2: lang terminal,
forall s: sentence,
(l_uni l1 l2) s -> 
l1 s \/ l2 s.
Proof.
intros l1 l2 s H.
inversion H.
- left.
  exact H0.
- right.
  exact H0.
Qed.
