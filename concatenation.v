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
   
Require Import List.

Require Import misc_list.
Require Import cfg.
Require Import cfl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

(* --------------------------------------------------------------------- *)
(* CONCATENATION - DEFINITIONS                                           *)
(* --------------------------------------------------------------------- *)

Section Concatenation.

Variables non_terminal_1 non_terminal_2 terminal: Type.

Inductive g_cat_nt: Type:=
| Start_cat
| Transf1_cat_nt: non_terminal_1 -> g_cat_nt
| Transf2_cat_nt: non_terminal_2 -> g_cat_nt.

Notation sf1:= (list (non_terminal_1 + terminal)).
Notation sf2:= (list (non_terminal_2 + terminal)).
Notation sfc:= (list (g_cat_nt + terminal)).
Notation nlist:= (list g_cat_nt).
Notation tlist:= (list terminal).

Definition g_cat_sf_lift1 (c: non_terminal_1 + terminal): g_cat_nt + terminal:=
  match c with
  | inl nt => inl (Transf1_cat_nt nt)
  | inr t  => inr t
  end.

Definition g_cat_sf_lift2 (c: non_terminal_2 + terminal): g_cat_nt + terminal:=
  match c with
  | inl nt => inl (Transf2_cat_nt nt)
  | inr t  => inr t
  end.

Inductive g_cat_rules (g1: cfg non_terminal_1 terminal) (g2: cfg non_terminal_2 terminal): g_cat_nt -> sfc -> Prop :=
| New_cat: g_cat_rules g1 g2 Start_cat ([inl (Transf1_cat_nt (start_symbol g1))]++[inl (Transf2_cat_nt (start_symbol g2))])
| Lift1_cat: forall nt s,
             rules g1 nt s ->
             g_cat_rules g1 g2 (Transf1_cat_nt nt) (map g_cat_sf_lift1 s)
| Lift2_cat: forall nt s,
             rules g2 nt s ->
             g_cat_rules g1 g2 (Transf2_cat_nt nt) (map g_cat_sf_lift2 s).

Lemma g_cat_finite:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
exists n: nat,
exists ntl: list g_cat_nt,
exists tl: tlist,
In Start_cat ntl /\
forall left: g_cat_nt,
forall right: sfc,
g_cat_rules g1 g2 left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: g_cat_nt, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
intros g1 g2.
destruct (rules_finite g1) as [n1 [ntl1 [tl1 H1]]].
destruct (rules_finite g2) as [n2 [ntl2 [tl2 H2]]].
exists (S (S (max n1 n2))), (Start_cat :: (map Transf1_cat_nt ntl1) ++ (map Transf2_cat_nt ntl2)), (tl1 ++ tl2).
split.
- simpl.
  left.
  reflexivity.
- split.
  + inversion H.
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
          * {
            destruct H4 as [H4 | H4].
            - inversion H4.
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
            - contradiction.
            }
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
            change (inl Start_cat :: l2) with ([inl Start_cat] ++ l2) in H4'''.
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
              change (inl (Transf1_cat_nt n) :: l2) with ([inl (Transf1_cat_nt n)] ++ l2) in H4'''.
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
            change (inl (Transf2_cat_nt n) :: l2) with ([inl (Transf2_cat_nt n)] ++ l2) in H4'''.
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
            change (inl Start_cat :: l2) with ([inl Start_cat] ++ l2) in H4'''.
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
            change (inl (Transf1_cat_nt n) :: l2) with ([inl (Transf1_cat_nt n)] ++ l2) in H4'''.
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
              change (inl (Transf2_cat_nt n) :: l2) with ([inl (Transf2_cat_nt n)] ++ l2) in H4'''.
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
          * {
            destruct H4 as [H4 | H4].
            - inversion H4.
            - contradiction.
            }
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

Definition g_cat (g1: cfg non_terminal_1 terminal) (g2: cfg non_terminal_2 terminal): (cfg g_cat_nt terminal):= {|
start_symbol:= Start_cat;
rules:= g_cat_rules g1 g2;
rules_finite:= g_cat_finite g1 g2
|}.

(* --------------------------------------------------------------------- *)
(* CONCATENATION - LEMMAS                                                *)
(* --------------------------------------------------------------------- *)

Lemma derives_add_cat_left:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s s': sf1,
derives g1 s s' -> derives (g_cat g1 g2) (map g_cat_sf_lift1 s) (map g_cat_sf_lift1 s'). 
Proof.
intros g1 g2 s s' H.
induction H as [| x y z left right H1 H2 H3].
- apply derives_refl.
- rewrite map_app.
  rewrite map_app.
  rewrite map_app in H2.
  simpl in H2.
  apply derives_step with (left:=(Transf1_cat_nt left)).
  exact H2.
  simpl.
  apply Lift1_cat.
  apply H3.
Qed.

Lemma derives_add_cat_right:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s s': sf2,
derives g2 s s' -> derives (g_cat g1 g2) (map g_cat_sf_lift2 s) (map g_cat_sf_lift2 s'). 
Proof.
intros g1 g2 s s' H.
induction H as [| x y z left right H1 H2 H3].
- apply derives_refl.
- rewrite map_app.
  rewrite map_app.
  rewrite map_app in H2.
  simpl in H2.
  apply derives_step with (left:=(Transf2_cat_nt left)).
  exact H2.
  simpl.
  apply Lift2_cat.
  apply H3.
Qed.

Lemma g_cat_correct_aux:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s11 s12: sf1,
forall s21 s22: sf2,
derives g1 s11 s12 /\ derives g2 s21 s22 ->
derives (g_cat g1 g2) 
        ((map g_cat_sf_lift1 s11)++(map g_cat_sf_lift2 s21)) 
        ((map g_cat_sf_lift1 s12)++(map g_cat_sf_lift2 s22)).
Proof.
intros g1 g2 s11 s12 s21 s22 [H1 H2].
induction H1, H2.
- apply derives_refl.
- rewrite map_app.
  rewrite map_app.
  apply derives_trans with (s2:=
    (map g_cat_sf_lift1 s ++
     map g_cat_sf_lift2 (s2 ++ [inl left] ++ s3))).
  apply derives_context_free_add_left.
  apply derives_add_cat_right.
  simpl.
  exact H2.
  apply derives_context_free_add_left.
  rewrite map_app.
  rewrite map_app.
  simpl.
  apply derives_step with (left:= Transf2_cat_nt left).
  + apply derives_refl.
  + simpl.
    apply Lift2_cat.
    exact H.
- apply derives_context_free_add_right.
  apply derives_add_cat_left.
  apply derives_step with (left:=left).
  + exact H1.
  + exact H.
- rewrite map_app.
  rewrite map_app.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  rewrite map_app.
  rewrite map_app.
  rewrite map_app in IHderives.
  rewrite map_app in IHderives.
  rewrite <- app_assoc in IHderives.
  simpl in IHderives.
  rewrite map_app in IHderives.
  remember ((map g_cat_sf_lift1 s1 ++
             map g_cat_sf_lift2 s0)) as w1.
  remember (map g_cat_sf_lift1 s3 ++
            map g_cat_sf_lift2 s4 ++
            map g_cat_sf_lift2 right0 ++
            map g_cat_sf_lift2 s5) as w2.
  apply derives_step with (left:= Transf1_cat_nt left).
  exact IHderives.
  simpl.
  apply Lift1_cat.
  exact H.
Qed.

Theorem g_cat_correct:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s1: sf1,
forall s2: sf2,
generates g1 s1 /\ generates g2 s2 ->
generates (g_cat g1 g2)
          ((map g_cat_sf_lift1 s1)++(map g_cat_sf_lift2 s2)).
Proof.
unfold generates.
intros g1 g2 s1 s2 H.
destruct H as [H1 H2].
apply derives_trans with (s2:= (map g_cat_sf_lift1 [(inl (start_symbol g1))] ++ map g_cat_sf_lift2 [(inl (start_symbol g2))])).
- match goal with
  | |- derives _ ?s1 ?s2 =>
       change s1 with ([] ++ s1);
       change s2 with ([] ++ s2 ++ [])
  end.
  apply derives_step with (left:= (start_symbol (g_cat g1 g2))).
  + apply derives_refl.
  + simpl.
    apply New_cat.
- apply g_cat_correct_aux.
  split.
  + exact H1.
  + exact H2.
Qed.

Theorem g_cat_correct_inv:
forall g1: cfg non_terminal_1 terminal,
forall g2: cfg non_terminal_2 terminal,
forall s: sfc,
generates (g_cat g1 g2) s ->
s = [inl (start_symbol (g_cat g1 g2))] \/
exists s1: sf1,
exists s2: sf2,
s =(map g_cat_sf_lift1 s1)++(map g_cat_sf_lift2 s2) /\
generates g1 s1 /\
generates g2 s2.
Proof.
unfold generates.
intros g1 g2 s.
remember ([inl (start_symbol (g_cat g1 g2))]) as init.
intros H.
induction H.
- left. reflexivity.
- subst. 
  specialize (IHderives eq_refl).
  destruct IHderives.
  + (* IHderives, first case *)
    (* A primeira cadeia gerada é a raiz da gramática *)
    destruct s2.
    * (* Se s2 é vazio, a primeira regra está sendo aplicada *)
      simpl in H1. inversion H1. subst. clear H1.
      simpl in H0. inversion H0. clear H0 H2.
      simpl in *.
      right.
      exists [inl (start_symbol g1)], [inl (start_symbol g2)]. 
      { 
      split. 
      - simpl. reflexivity. 
      - split. apply derives_refl. apply derives_refl. 
      }
    * (* Se s2 não é vazio, temos uma contradição *)
      simpl in H1. 
      {
      destruct s2. 
      - simpl in *. inversion H1. 
      - simpl in *. inversion H1. 
      }
  + (* IHderives, second case *)
    (* A primeira cadeia gerada é a concatenação de map x com map x0 *)
    destruct H1 as (? & ? & ? & ? & ?).
    (* Análise da regra usada *)
    inversion H0. 
    subst. 
    clear H0.
    * (* Case 1: rule New_cat *)
      (* Contradiction: H1 cannot contain Start_cat *)
      assert (IN : In (inl Start_cat) (map g_cat_sf_lift1 x ++ map g_cat_sf_lift2 x0)).
        { 
        rewrite <- H1. 
        rewrite in_app_iff. 
        right. 
        simpl. 
        left. 
        reflexivity. 
        }
      rewrite in_app_iff in IN.
      (* Start_cat is in x or x0 *) 
      {
      destruct IN.
      - (* Start_cat is in x, contradiction *)
        rewrite in_map_iff in H0. 
        destruct H0 as (? & ? & ?).
        (* But Start_cat = lift x1 and x cannot contain x1 *)
        destruct x1. 
        + simpl in H0. 
          inversion H0. 
        + simpl in H0. 
          inversion H0.
      - (* Start_cat is in x0, contradiction *)
        rewrite in_map_iff in H0. 
        destruct H0 as (? & ? & ?).
        destruct x1.
        + simpl in H0. 
          inversion H0. 
        + simpl in H0. 
          inversion H0. 
      }
    * (* Case 2: rule Lift1_cat *)
      (* A rule of g1 has been used *)
      subst.
      (* Consider both situations in H1 *)
      assert (IN : In (inl (Transf1_cat_nt nt)) (map g_cat_sf_lift1 x ++ map g_cat_sf_lift2 x0)).
        { 
        rewrite <- H1. 
        rewrite in_app_iff. 
        right. 
        simpl. 
        left. 
        reflexivity. 
        }
      rewrite in_app_iff in IN.
      (* Transf1_cat_nt is in x or x0 *) 
      {
      destruct IN.
      - (* Transf1_cat_nt is in x, ok *)
        apply equal_app in H1.
        destruct H1.
        + destruct H1 as [l [H1 H6]].
          right. 
          destruct l.
          * {
            destruct x0.
            - simpl in H6.
              inversion H6.
            - simpl in H6.
              inversion H6.
              destruct s0.
              + inversion H8.
              + inversion H8.
            }
          * inversion H6.
            subst. 
            clear H6. 
            {
            apply derives_step with (right:=(map g_cat_sf_lift1 s)) in H.
            - symmetry in H1.
              apply map_expand in H1.
              destruct H1 as [s1' [s2' [H6 [H7 H8]]]].
              replace (inl (Transf1_cat_nt nt) :: l) with ([inl (Transf1_cat_nt nt)]++l) in H8.
              + symmetry in H8.
                apply map_expand in H8.
                destruct H8 as [s1'' [s2'' [H9 [H10 H11]]]].
                exists (s1'++s++s2''), x0.
                split.
                * repeat rewrite map_app.
                  subst.
                  repeat rewrite <- app_assoc.
                  reflexivity.
                * { 
                  split.
                  - subst. 
                    destruct s1''.
                    + simpl in H10.
                      inversion H10.
                    + inversion H10.  
                      destruct s0.
                       * inversion H6.
                         apply map_eq_nil in H7.
                         subst. 
                         {
                         apply derives_step with (right:= s) in H2.
                         - exact H2.
                         - exact H4. 
                         }
                       * inversion H6.
                  - exact H3. 
                  }
              + simpl.
                reflexivity.
            - exact H0. 
            }
        + destruct H1 as [l [H1 H6]].
          assert (IN: In (inl (Transf1_cat_nt nt)) (map g_cat_sf_lift2 x0)).
            { 
            rewrite H6. 
            apply in_app_iff. 
            right. 
            simpl. 
            left. 
            reflexivity. 
            }
          apply in_map_iff in IN. 
          destruct IN.
          destruct H7. 
          destruct x1.
          inversion H7.
          inversion H7.
      - (* Transf1_cat_nt is in x0, contradiction *)
        rewrite in_map_iff in H5.
        destruct H5.
        destruct H5.
        destruct x1.
        + inversion H5.
        + inversion H5. 
      }
    * (* Case 3: rule Lift2_cat *)
      (* A rule of g2 has been used *)
      subst.
      (* Consider both situations in H1 *)
      assert (IN : In (inl (Transf2_cat_nt nt)) (map g_cat_sf_lift1 x ++ map g_cat_sf_lift2 x0)).
        { 
        rewrite <- H1. 
        rewrite in_app_iff. 
        right. 
        simpl. 
        left. 
        reflexivity. 
        }
      rewrite in_app_iff in IN.
      (* Transf2_cat_nt is in x or x0 *) 
      {
      destruct IN.
      - (* Transf2_cat_nt is in x, contradiction *)
        rewrite in_map_iff in H5.
        destruct H5.
        destruct H5.
        destruct x1.
        + inversion H5.
        + inversion H5.
      - (* Transf2_cat_nt is in x0, ok *)
        apply equal_app in H1.
        destruct H1.
        + destruct H1 as [l [H1 H6]].
          right. 
          destruct l.
          * {
            destruct x0.
            - simpl in H6.
              inversion H6.
            - simpl in H6.
              inversion H6.
              rewrite app_nil_r in H1.
              subst.
              exists x.
              exists (s++x0).
              split. 
              rewrite map_app.
              reflexivity.
              split.
              exact H2.
              inversion H6.
              destruct s0.
              + simpl in H7. 
                inversion H7.
                subst.
                rewrite <- app_nil_l in H3.
                apply derives_step with (right:=s) in H3.
                * exact H3.
                * exact H4.
              + inversion H7.
            }
          * inversion H6.
            subst.
            clear H6.
            assert (IN : In (inl (Transf2_cat_nt nt)) (map g_cat_sf_lift1 x)).
              { 
              rewrite H1. 
              rewrite in_app_iff. 
              right. 
              simpl. 
              left. 
              reflexivity. 
              }
            rewrite in_map_iff in IN.
            destruct IN as [x0' [H6 H7]]. 
            {
            destruct x0'.
            - simpl in H6.
              inversion H6.
            - inversion H6. 
            }
        + destruct H1 as [l [H7 H8]].
          subst. 
          symmetry in H8.
          apply map_expand in H8.
          destruct H8 as [ s1' [s2' [H10 [H11 H12]]]].
          subst.
          destruct s2'.
          * inversion H12.
          * inversion H12.
            subst. 
            right.
            exists x.
            exists (s1'++s++s2').
            split.
            rewrite <- app_assoc.
            repeat rewrite map_app.
            reflexivity.
            split.
            exact H2. 
            {
            destruct s0.
            - inversion H6.
              subst.
              apply derives_step with (right:=s) in H3.
              exact H3.
              exact H4.
            - inversion H6. 
            } 
      }
Qed.

End Concatenation.

(* --------------------------------------------------------------------- *)
(* AS LANGUAGES                                                          *)
(* --------------------------------------------------------------------- *)

Section Concatenation_2.

Variable non_terminal_1 non_terminal_2 terminal: Type.

Notation sentence:= (list terminal).

Inductive l_cat (l1 l2: lang terminal): lang terminal:=
| l_cat_app: forall s1 s2: sentence, l1 s1 -> l2 s2 -> l_cat l1 l2 (s1 ++ s2).

Lemma map_cat_1:
forall s: sentence,
map (@g_cat_sf_lift1 non_terminal_1 non_terminal_2 terminal) (map (@terminal_lift non_terminal_1 terminal) s) =
map (@terminal_lift (@g_cat_nt non_terminal_1 non_terminal_2) terminal) s.
Proof.
induction s.
- simpl.
  reflexivity.
- simpl.
  change (inr a) with (terminal_lift (g_cat_nt non_terminal_1 non_terminal_2) a).
  rewrite IHs. 
  reflexivity.
Qed.

Lemma map_cat_2:
forall s: sentence,
map (@g_cat_sf_lift2 non_terminal_1 non_terminal_2 terminal) (map (@terminal_lift non_terminal_2 terminal) s) =
map (@terminal_lift (@g_cat_nt non_terminal_1 non_terminal_2) terminal) s.
Proof.
induction s.
- simpl.
  reflexivity.
- simpl.
  change (inr a) with (terminal_lift (g_cat_nt non_terminal_1 non_terminal_2) a).
  rewrite IHs. 
  reflexivity.
Qed.

Lemma map_cat_3:
forall s: sentence,
forall l: list (non_terminal_1 + terminal),
map (@terminal_lift (@g_cat_nt non_terminal_1 non_terminal_2) terminal) s =
map (@g_cat_sf_lift1 non_terminal_1 non_terminal_2 terminal) l ->
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
  remember (terminal_lift (g_cat_nt non_terminal_1 non_terminal_2) (terminal:=terminal)) as m1.
  remember (g_cat_sf_lift1 non_terminal_2 (terminal:=terminal)) as m2.
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
      replace (m2 (inl n)) with (inl terminal (Transf1_cat_nt non_terminal_2 n)) in H1.
      - replace (m1 a) with (inr (g_cat_nt non_terminal_1 non_terminal_2) a) in H1. 
        + inversion H1.
        + rewrite Heqm1.
          change (inr a) with (terminal_lift (g_cat_nt non_terminal_1 non_terminal_2) a).
          reflexivity.
      - rewrite Heqm2.
        simpl.
        reflexivity.
      }
    * {
      replace (m2 (inr t)) with (inr (g_cat_nt non_terminal_1 non_terminal_2) t) in H1.
      - replace (m1 a) with (inr (g_cat_nt non_terminal_1 non_terminal_2) a) in H1. 
        + inversion H1.
          replace (m3 t) with (inr non_terminal_1 t).
          * reflexivity.
          * rewrite Heqm3.
            change (inr t) with (terminal_lift non_terminal_1 t).
            reflexivity.
        + rewrite Heqm1.
          change (inr a) with (terminal_lift (g_cat_nt non_terminal_1 non_terminal_2) a).
          reflexivity.
      - rewrite Heqm2. 
        simpl.
        reflexivity.
      }
Qed.

Lemma map_cat_4:
forall s: sentence,
forall l: list (non_terminal_2 + terminal),
map (@terminal_lift (@g_cat_nt non_terminal_1 non_terminal_2) terminal) s =
map (@g_cat_sf_lift2 non_terminal_1 non_terminal_2 terminal) l ->
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
  remember (terminal_lift (g_cat_nt non_terminal_1 non_terminal_2) (terminal:=terminal)) as m1.
  remember (g_cat_sf_lift2 non_terminal_1 (terminal:=terminal)) as m2.
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
      replace (m2 (inl n)) with (inl terminal (Transf2_cat_nt non_terminal_1 n)) in H1.
      - replace (m1 a) with (inr (g_cat_nt non_terminal_1 non_terminal_2) a) in H1. 
        + inversion H1.
        + rewrite Heqm1.
          change (inr a) with (terminal_lift (g_cat_nt non_terminal_1 non_terminal_2) a).
          reflexivity.
      - rewrite Heqm2.
        simpl.
        reflexivity.
      }
    * {
      replace (m2 (inr t)) with (inr (g_cat_nt non_terminal_1 non_terminal_2) t) in H1.
      - replace (m1 a) with (inr (g_cat_nt non_terminal_1 non_terminal_2) a) in H1. 
        + inversion H1.
          replace (m3 t) with (inr non_terminal_2 t).
          * reflexivity.
          * rewrite Heqm3.
            change (inr t) with (terminal_lift non_terminal_2 t).
            reflexivity.
        + rewrite Heqm1.
          change (inr a) with (terminal_lift (g_cat_nt non_terminal_1 non_terminal_2) a).
          reflexivity.
      - rewrite Heqm2. 
        simpl.
        reflexivity.
      }
Qed.

End Concatenation_2.

Variable terminal: Type.

Notation sentence:= (list terminal).

Theorem l_cat_is_cfl:
forall l1 l2: lang terminal,
cfl l1 ->
cfl l2 ->
cfl (l_cat l1 l2).
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
exists (g_cat_nt non_terminal_1 non_terminal_2), (g_cat g1 g2).
intros w.
split.
- intros H3.
  inversion H3.
  specialize (H1 s1).
  destruct H1 as [H1 _].
  specialize (H1 H).
  specialize (H2 s2).
  destruct H2 as [H2 _].
  specialize (H2 H0).
  unfold produces in H1.
  unfold produces in H2.
  unfold produces.
  rewrite map_app.
  rewrite <- map_cat_1.
  rewrite <- map_cat_2.
  apply g_cat_correct.
  exact (conj H1 H2).
- intros H4.
  apply g_cat_correct_inv in H4.
  destruct H4 as [H4 | H4].
  + destruct w.
    * simpl in H4.
      inversion H4.
    * simpl in H4.
      inversion H4.
  + destruct H4 as [s1 [s2 [H4 [H5 H6]]]].
    symmetry in H4.
    apply map_expand in H4.
    destruct H4 as [s1' [s2' [H7 [H8 H9]]]].
    rewrite H7.
    apply l_cat_app.
    * specialize (H1 s1'). 
      destruct H1 as [_ H1].
      apply H1.
      unfold produces.
      apply map_cat_3 in H8.
      rewrite H8 in H5.
      exact H5.
    * specialize (H2 s2'). 
      destruct H2 as [_ H2].
      apply H2.
      unfold produces.
      apply map_cat_4 in H9.
      rewrite H9 in H6.
      exact H6.
Qed.

Theorem l_cat_correct:
forall l1 l2: lang terminal,
forall s1 s2: sentence,
(l1 s1 /\ l2 s2) -> (l_cat l1 l2) (s1 ++ s2).
Proof.
intros l1 l2 s1 s2 [H1 H2].
apply l_cat_app.
- exact H1.
- exact H2.
Qed.

Theorem l_cat_correct_inv:
forall l1 l2: lang terminal,
forall s: sentence,
(l_cat l1 l2) s -> 
exists s1 s2: sentence,
s = s1 ++ s2 /\ l1 s1 /\ l2 s2.
Proof.
intros l1 l2 s H.
inversion H.
exists s1, s2.
split.
- reflexivity. 
- split. 
  + exact H0.
  + exact H1.
Qed.
