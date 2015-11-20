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
Require Import NPeano.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.
Require Import cfl.
Require Import inaccessible.
Require Import useless.
Require Import unitrules.
Require Import emptyrules.
Require Import simplification.
Require Import trees.
Require Import allrules.
Require Import chomsky.
Require Import pigeon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* PUMPING LEMMA                                                         *)
(* --------------------------------------------------------------------- *)

Section Pumping.

Variable non_terminal terminal: Type.
Notation sentence:= (list terminal).

Lemma pumping_aux:
forall g: cfg _ _,
forall t1 t2: btree (non_terminal' non_terminal terminal) _,
forall n: _,
forall c1 c2: list bool,
forall v x: sentence,
btree_decompose t1 c1 = Some (v, t2, x) ->
btree_cnf g t1 ->
broot t1 = n ->
bcode t1 (c1 ++ c2) ->
c1 <> [] ->
broot t2 = n ->
bcode t2 c2 ->
(forall i: nat,
 exists t': btree _ _,
 btree_cnf g t' /\
 broot t' = n /\
 btree_decompose t' (iter c1 i) = Some (iter v i, t2, iter x i) /\
 bcode t' (iter c1 i ++ c2) /\
 get_nt_btree (iter c1 i) t' = Some n).
Proof.
induction i.
- exists t2.
  simpl.
  split.
  + apply btree_cnf_subtree with (t2:= t2) in H0.
    * exact H0.
    * {
      apply btree_decompose_subtree_bcode in H.
      - apply subtree_bcode_subtree in H. 
        exact H.
      - exact H3.
      }
  + split.
    * exact H4.
    * {
      split.
      - rewrite btree_decompose_empty. 
        reflexivity.
      - split. 
        + exact H5.
        + destruct t2.
          * simpl in H4.
            subst.
            reflexivity.
          * simpl in H4.
            subst.
            reflexivity.
      }
- destruct IHi as [t' [H10 [H11 [H12 [H13 H14]]]]].
  assert (H15: exists t'': btree _ _, btree_subst t' t1 (iter c1 i) = Some t'').
    {
    apply bcode_btree_subst with (c2:= c2).
    exact H13.
    }
  destruct H15 as [t'' H15].
  exists t''.
  split. 
  + apply btree_subst_preserves_cnf with (g:= g) (c1':= c2) in H15.
    * exact H15. 
    * exact H10. 
    * exact H13. 
    * exact H0.
    * congruence. 
  + split. 
    * {
      apply btree_subst_preserves_broot_v1 in H15.
      - congruence.
      - congruence.
      }
    * {
      split. 
      - apply btree_subst_decompose with (t2:= t2) (x:= iter v i) (y:= iter x i) in H15.
        + simpl. 
          repeat rewrite iter_comm.
          replace (iter x i ++ x) with (x ++ iter x i).
          * {
            apply btree_decompose_combine with (t1:= t1).
            - exact H15.
            - exact H.
            }
          * rewrite iter_comm.
            reflexivity.
        + exact H12.
      - split.
        + apply btree_subst_bcode with (c1':= c2) (c2:= c1 ++ c2) in H15.
          * simpl. 
            rewrite iter_comm. 
            rewrite <- app_assoc. 
            exact H15. 
          * exact H13. 
          * exact H2.
        + simpl.
            rewrite iter_comm.
            {
            apply btree_subst_get_nt with (c1':= c2) (c2:= c1) (c2':= c2) (n:= n) in H15.
            - exact H15.
            - exact H13.
            - exact H2.
            - apply btree_decompose_get_nt in H. 
              congruence. 
            }
      }
Qed.

End Pumping.

Variable terminal: Type.
Notation sentence:= (list terminal).

Theorem pumping_lemma:
forall l: lang terminal,
(contains_empty l \/ ~ contains_empty l) /\ (contains_non_empty l \/ ~ contains_non_empty l) ->
cfl l ->
exists n: nat, 
forall s: sentence, 
l s -> 
length s >= n ->
exists u v w x y: sentence, 
s = u ++ v ++ w ++ x ++ y /\
length (v ++ x) >= 1 /\
length (v ++ w ++ x) <= n /\
forall i: nat, l (u ++ (iter v i) ++ w ++ (iter x i) ++ y).
Proof.
intros l H1 H2.
inversion H2 as [non_terminal H3].
clear H2.
destruct H3 as [g H3].
(* Find g' in CNF *)
assert (H2: exists g': cfg (chomsky.non_terminal' (emptyrules.non_terminal' non_terminal) terminal) terminal, (g_equiv g' g) /\ (is_cnf g' \/ is_cnf_with_empty_rule g') /\ start_symbol_not_in_rhs g').
  {
  apply g_cnf_exists.
  destruct H1 as [H1 H2].
  split.
  - destruct H1 as [H1 | H1].
    + left.
      specialize (H3 []).
      destruct H3 as [H3 _].
      apply H3.
      exact H1.
    + right.
      intros H4.
      apply H1.
      specialize (H3 []).
      destruct H3 as [_ H3].
      apply H3.
      exact H4.
  - destruct H2 as [H2 | H2].
    + left.
      destruct H2 as [w [H2 H4]].
      specialize (H3 w).
      destruct H3 as [H3 _].
      exists w.
      split.
      * apply H3.
        exact H2.
      * exact H4.
    + right.
      intros H4.
      apply H2.
      destruct H4 as [w [H4 H5]].
      specialize (H3 w).
      destruct H3 as [_ H3].
      exists w.
      split.
      * apply H3.
        exact H4.
      * exact H5.
  }
destruct H2 as [g' [H2 H4]].
(* Change g for g' *)
apply lang_eq_change_g with (non_terminal':= chomsky.non_terminal' (emptyrules.non_terminal' non_terminal) terminal) (g':= g') in H3.
- assert (H3':= H3).
  assert (H3copy:= H3).
  destruct (rules_finite g') as [n' [ntl' [tl' H5]]].
  assert (H5':= H5).
  (* exists n *)
  exists (2 ^ (length ntl')).
  intros s H6 H7.
  specialize (H3 s). 
  destruct H3 as [H3 _].
  specialize (H3 H6).
  assert (H6':= H6).
  unfold lang_of_g in H3.
  destruct H4 as [H4 H4'].  
  assert (H4copy:= H4).
  unfold produces, generates in H3.
  (* Find btree *)
  apply derives_g_cnf_equiv_btree_v4 with (n:= start_symbol g') (s:= s) in H4.
  + destruct H4 as [t [H4 [H8 H9]]].
    clear g H1 H2 H3 H5 H6.
    apply length_ge with (t:= t) in H7.
    assert (HHH:= H7).      
    * (* Find bpath *)
      {
      apply btree_exists_bpath with (ntl:= ntl') in H7.
      - destruct H7 as [z [H20 [H21 [m [r [t0 [H22 [H23 [H24 H25]]]]]]]]].
        assert (H26: forall s, In s r -> In s (map inl ntl')).
          {
          intros s0 H27.
          specialize (H25 s0).
          apply H25.
          apply in_or_app.
          right.
          exact H27.
          }
        clear H25.
        assert (H27: exists r': list (non_terminal' (emptyrules.non_terminal' non_terminal) terminal), r = map inl r').
          {
          exists (get_As _ _ r).
          apply get_As_correct.
          intros e H28.
          specialize (H26 e H28).
          apply in_split in H26.
          destruct H26 as [l1 [l2 H26]].
          symmetry in H26.
          apply map_expand in H26.
          destruct H26 as [s1' [s2' [_ [_ H26]]]].
          symmetry in H26. 
          change (e :: l2) with ([e] ++ l2) in H26.
          apply map_expand in H26.
          destruct H26 as [s1'0 [s2'0 [_ [H26 _]]]].
          destruct s1'0.
          - simpl in H26.
            inversion H26. 
          - simpl in H26.
            inversion H26.
            exists n.
            reflexivity.
          }
        destruct H27 as [r' H27].
        assert (H28: length r' = length r).
          {
          rewrite H27.
          rewrite map_length.
          reflexivity.
          }
        assert (H24':= H24).
        rewrite <- H28 in H24.
        rewrite H27 in H26.
        assert (H29: forall n: non_terminal' (emptyrules.non_terminal' non_terminal) terminal, In n r' -> In n ntl').
          {
          intros n H99.
          assert (H29: In (inl n) (map (@inl _ terminal) r')).
            {
            apply in_map.
            exact H99.
            }
          specialize (H26 (inl n) H29).
          apply in_split in H26.
          destruct H26 as [l1 [l2 H26]].
          symmetry in H26.
          apply map_expand in H26.
          destruct H26 as [s1' [s2' [H40 [H41 H42]]]].
          symmetry in H42.
          change (inl n :: l2) with ([inl n] ++ l2) in H42.
          apply map_expand in H42.
          destruct H42 as [s1'0 [s2'0 [H42 [H43 H44]]]].
          destruct s1'0.
          - simpl in H43.
            inversion H43.
          - simpl in H43.
            inversion H43.
            subst.
            apply in_or_app.
            right.
            simpl.
            left.
            reflexivity.
          }
        apply pigeon in H29. 
        + destruct H29 as [n [r1' [r2' [r3' H29]]]].
          rewrite H29 in H27.
          repeat rewrite map_app in H27.
          (* Prepare path *)
          assert (Hpath:= H22).
          rewrite H27 in Hpath.
          repeat rewrite <- app_assoc in Hpath.
          assert (H20copy:= H20). 
          rewrite Hpath in H20copy.
          apply bpath_insert_head in H20copy.
          * destruct H20copy as [p12' H20copy].
            rewrite app_assoc in Hpath.
            rewrite <- H20copy in Hpath.
            rewrite <- app_assoc in Hpath.
            (* Find subtrees and u, v, w, x, y *)
            apply bpath_exists_bcode in H20.
            destruct H20 as [c [H100 H101]].
            rewrite Hpath in H101.
            rewrite app_assoc in H101.
            assert (H101copy:= H101).
            {
            apply bcode_split in H101.
            - destruct H101 as [c1 [c2 [H101 [H102 [t1 [u [y [H104 [H105 H106]]]]]]]]].
              assert (H105copy:= H105).
              assert (Ht:= H105).
              apply btree_decompose_bfrontier in H105.
              destruct H105 as [Ht_a Ht_b].
              assert (Hc1: c1 <> []).
                {
                simpl in H102.
                assert (length c1 > 0) by omega.
                apply length_not_zero in H.
                apply not_eq_sym.
                exact H.
                }
              specialize (Ht_b Hc1).
              assert (Ht_c: subtree_bcode t t1 c1).
                {
                apply btree_decompose_subtree_bcode in H105copy.
                - exact H105copy.
                - exact Hc1.
                }
              rewrite app_assoc in H104.
              assert (H104copy:= H104).
              apply bcode_split in H104.
              + destruct H104 as [c3 [c4 [H104 [H107 [t2 [v [x [H109 [H110 H111]]]]]]]]].
                assert (H110copy:= H110).
                assert (Ht1:= H110).
                apply btree_decompose_bfrontier in H110.
                destruct H110 as [Ht1_a Ht1_b].
                assert (Hc3: c3 <> []).
                  {
                  simpl in H107.
                  assert (length c3 > 0) by omega.
                  apply length_not_zero in H.
                  apply not_eq_sym.
                  exact H.
                  }
                specialize (Ht1_b Hc3).
                assert (Ht1_c: subtree_bcode t1 t2 c3).
                  {
                  apply btree_decompose_subtree_bcode in H110copy.
                  - exact H110copy.
                  - exact Hc3.
                  }
                remember (bfrontier t2) as w.
                (* Find roots *)
                assert (Hroot_t1: broot t1 = n).
                  {
                  apply bpath_bcode_split in H104copy.
                  destruct H104copy as [H104copy _].
                  apply bpath_broot with (d:= inl (broot t1)) in H104copy.
                  simpl in H104copy.
                  inversion H104copy.
                  reflexivity.
                  }
                assert (Hroot_t2: broot t2 = n).
                  {
                  apply bpath_bcode_split in H109.
                  destruct H109 as [H109 _].
                  apply bpath_broot with (d:= inl (broot t2)) in H109.
                  simpl in H109.
                  inversion H109.
                  reflexivity.
                  }
                (* Find heights *)
                remember (length ntl') as k.
                assert (H114: bheight t1 <= k + 1 /\ bheight t1 >= 2).
                  {
                  split.
                  - rewrite H106.
                    rewrite H27 in H24'.
                    repeat rewrite app_length in H24'.
                    repeat rewrite app_length.
                    simpl in H24'.
                    simpl.
                    omega.
                  - rewrite H106.
                    rewrite H27 in H24'.
                    repeat rewrite app_length in H24'.
                    repeat rewrite app_length.
                    simpl in H24'.
                    simpl.
                    omega.
                  }
                assert (H115: bheight t2 <= k /\ bheight t2 >= 1).
                  {
                  split.
                  - rewrite H111.
                    rewrite H27 in H24'.
                    repeat rewrite app_length in H24'.
                    repeat rewrite app_length.
                    simpl in H24'.
                    simpl.
                    omega.
                  - rewrite H111.
                    rewrite H27 in H24'.
                    repeat rewrite app_length in H24'.
                    repeat rewrite app_length.
                    simpl in H24'.
                    simpl.
                    omega.
                  }
                (* Exists u, v, w, x, y *)
                exists u, v, w, x, y.
                split.
                * (* s = u ++ v ++ w ++ x ++ y *)
                  rewrite <- H9.
                  rewrite Ht_a.
                  rewrite Ht1_a.
                  repeat rewrite <- app_assoc.
                  reflexivity.
                * {
                  split.
                  - (* length (v ++ x) >= 1 *)
                    apply length_not_zero_inv in Ht1_b.
                    omega.
                  - split.
                    + (* length (v ++ w ++ x) <= 2 ^ k *)
                      destruct H114 as [H114 H116].
                      apply bheight_le in H114.
                      rewrite Ht1_a in H114.
                      replace (k + 1 - 1) with k in H114.
                      * exact H114. 
                      * omega. 
                    + (* uv^iwx^iy *)
                      intros i.
                      assert (Ht': exists t': btree _ _, 
                                   btree_cnf g' t' /\
                                   broot t' = n /\
                                   btree_decompose t' (iter c3 i) = Some (iter v i, t2, iter x i) /\
                                   bcode t' (iter c3 i ++ c4) /\
                                   get_nt_btree (iter c3 i) t' = Some n).
                        {
                        apply pumping_aux with (g:= g') (t1:= t1) (t2:= t2) (n:= n) (c1:= c3) (c2:= c4) (v:= v) (x:= x) (i:= i).
                        - exact Ht1. 
                        - apply subtree_bcode_subtree in Ht_c.
                          apply btree_cnf_subtree with (g:= g') in Ht_c.
                          + exact Ht_c.
                          + exact H4.
                        - exact Hroot_t1.
                        - rewrite <- H104.
                          apply bpath_bcode_split in H104copy. 
                          apply H104copy.
                        - exact Hc3.
                        - congruence.
                        - apply bpath_bcode_split in H109.
                          apply H109.
                        }
                      destruct Ht' as [t' [Ht'_1 [Ht'_2 [Ht'_3 Ht'_4]]]].
                      assert (Ht'': exists t'': btree _ _, btree_subst t t' c1 = Some t'').
                        {
                        rewrite H101 in H100.
                        apply bcode_btree_subst with (t2:= t') in H100.
                        destruct H100 as [t'' H100].
                        exists t''.
                        exact H100.
                        }
                      destruct Ht'' as [t'' Ht''].
                      assert (Ht''_1: broot t'' = start_symbol g').
                        {
                        apply btree_subst_preserves_broot_v2 in Ht''. 
                        - congruence. 
                        - exact Hc1.
                        }
                      assert (Ht''_2: bfrontier t'' = u ++ iter v i ++ w ++ iter x i ++ y).
                        {
                        apply btree_subst_bfrontier with (t2:= t1) (x:= u) (y:= y) in Ht''.
                        - apply btree_decompose_bfrontier in Ht'_3.
                          destruct Ht'_3 as [Ht'_3 _].
                          rewrite Ht'_3 in Ht''.
                          rewrite Heqw.
                          repeat rewrite <- app_assoc in Ht''.
                          exact Ht''.
                        - exact Ht_c.
                        - exact Ht. 
                        }
                      assert (Ht''_3: btree_cnf g' t'').
                        {
                        apply btree_subst_preserves_cnf with (g:= g') (c1':= c3 ++ c4) in Ht''.
                        - exact Ht''.
                        - exact H4.
                        - rewrite <- H104.
                          rewrite <- H101.
                          exact H100.
                        - exact Ht'_1.
                        - apply btree_decompose_get_nt in Ht.
                          congruence.
                        }
                      apply btree_equiv_produces_g_cnf in Ht''_3.
                      * unfold lang_eq in H3'.
                        specialize (H3' (u ++ iter v i ++ w ++ iter x i ++ y)).
                        destruct H3' as [_ H3'].
                        unfold lang_of_g in H3'.
                        apply H3'.
                        rewrite <- Ht''_2.
                        exact Ht''_3.
                      * congruence.
                  }
              + rewrite app_length.
                simpl.
                omega.
              + repeat rewrite app_length.
                simpl.
                omega.
              + rewrite H106.
                repeat rewrite app_length.
                reflexivity.
            - rewrite app_length.
              simpl.
              omega.
            - repeat rewrite app_length.
              simpl.
              omega.
            - rewrite Hpath in H21.
              repeat rewrite app_length in H21.
              repeat rewrite app_length.
              omega.
            }
          * rewrite H8.
            {
            apply start_symbol_only_once with (g:= g') (t:= t) (p1:= m ++ map inl r1') (p2:= map inl r2') (p3:= map inl r3' ++ [inr t0]).
            - exact H4'.
            - exact H4.
            - repeat rewrite <- app_assoc. 
              exact H20copy.
            }
        + rewrite H28.
          exact H24'.
      - apply cnf_bnts with (g:= g') (n:= n') (tl:= tl').
        + exact H5'.
        + exact H4.
      }
    * exact H9.
  + assert (Hntl': 2 ^ length ntl' > 0).
      {
      apply pow_2_gt_0.
      }
    assert (Hs: length s > 0) by omega.
    apply length_not_zero in Hs.
    apply not_eq_sym.
    exact Hs.
  + exact H4'.
  + exact H3.
- exact H2.
Qed.
