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
(* CONTEXT FREE GRAMMARS                                                 *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.

Require Import misc_arith.
Require Import misc_list.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* CONTEXT-FREE GRAMMARS - DEFINITIONS                                   *)
(* --------------------------------------------------------------------- *)

Section ContextFreeGrammars_Definitions.

Variables non_terminal terminal: Type.

Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation nlist:= (list non_terminal).
Notation tlist:= (list terminal).
Notation symbol:= (non_terminal + terminal)%type.

Definition rules_finite_def (ss: non_terminal) 
                            (rules: non_terminal -> sf -> Prop) 
                            (n: nat) 
                            (ntl: list non_terminal)
                            (tl: list terminal) :=
In ss ntl /\
(forall left: non_terminal,
 forall right: list (non_terminal + terminal),
 rules left right ->
 length right <= n /\
 In left ntl /\
 (forall s : non_terminal, In (inl s) right -> In s ntl) /\
 (forall s : terminal, In (inr s) right -> In s tl)).

Record cfg: Type:= {
start_symbol: non_terminal;
rules: non_terminal -> sf -> Prop;
rules_finite: exists n: nat,
              exists ntl: nlist,
              exists tl: tlist,
              rules_finite_def start_symbol rules n ntl tl
}.

Inductive derives (g: cfg): sf -> sf -> Prop :=
| derives_refl: forall s: sf,
                derives g s s
| derives_step: forall s1 s2 s3: sf,
                forall left: non_terminal,
                forall right: sf,
                derives g s1 (s2 ++ inl left :: s3) ->
                rules g left right ->
                derives g s1 (s2 ++ right ++ s3).

Inductive derives2 (g: cfg): sf -> sf -> Prop :=
| derives2_refl: forall s: sf,
                 derives2 g s s
| derives2_step: forall s1 s2 s3: sf,
                 forall left: non_terminal,
                 forall right: sf,
                 derives2 g (s1 ++ right ++ s2) s3 ->
                 rules g left right ->
                 derives2 g (s1 ++ inl left :: s2) s3.

Inductive derives3 (g: cfg): non_terminal -> sentence -> Prop :=
| derives3_rule: forall (n: non_terminal) (lt: sentence), 
                 rules g n (map inr lt) -> derives3 g n lt
| derives3_step: forall (n: non_terminal) (ltnt: sf) (lt: list terminal), 
                 rules g n ltnt -> derives3_aux g ltnt lt -> derives3 g n lt

with derives3_aux (g: cfg): sf -> sentence -> Prop :=
| derives3_aux_empty: derives3_aux g [] []
| derives3_aux_t:  forall (t: terminal) (ltnt: sf) (lt: sentence), 
                   derives3_aux g ltnt lt -> derives3_aux g (inr t :: ltnt) (t :: lt)
| derives3_aux_nt: forall (n: non_terminal) (lt lt': sentence) (ltnt: sf), 
                   derives3_aux g ltnt lt -> derives3 g n lt' -> derives3_aux g (inl n :: ltnt) (lt' ++ lt).

Scheme derives3_ind_2:= Minimality for derives3 Sort Prop
  with derives3_aux_ind_2:= Minimality for derives3_aux Sort Prop.

Combined Scheme derives3_comb_ind from derives3_ind_2, derives3_aux_ind_2.

Set Elimination Schemes.

Inductive derives4 (g: cfg): sf -> sf -> Prop :=
| derives4_refl: forall s: sf,
                 derives4 g s s
| derives4_rule: forall left: non_terminal,
                 forall s1 s2 right: sf,
                 rules g left right ->
                 derives4 g (s1 ++ [inl left] ++ s2) (s1 ++ right ++ s2)
| derives4_trans: forall s1 s2 s3: sf,
                  derives4 g s1 s2 ->
                  derives4 g s2 s3 ->
                  derives4 g s1 s3.

Inductive derives5 (g: cfg): nat -> sf -> sf -> Prop:=
| derives5_0: forall s: sf,
              derives5 g 0 s s
| derives5_1: forall left: non_terminal,
              forall s1 s2 right: sf,
              rules g left right ->
              derives5 g 1 (s1 ++ [inl left] ++ s2) (s1 ++ right ++ s2)
| derives5_sum: forall i j: nat,
                forall s1 s2 s3: sf,
                derives5 g i s1 s2 ->
                derives5 g j s2 s3 ->
                derives5 g (i+j) s1 s3.

Inductive derives6 (g: cfg): nat -> sf -> sf -> Prop:=
| derives6_0: forall s: sf,
              derives6 g 0 s s
| derives6_sum: forall left: non_terminal,
                forall right: sf,
                forall i: nat,
                forall s1 s2 s3: sf,
                rules g left right ->
                derives6 g i (s1 ++ right ++ s2) s3 ->
                derives6 g (S i) (s1 ++ [inl left] ++ s2) s3.

Inductive derives7 (g: cfg): nat -> sf -> sf -> Prop:=
| derives7_0: forall s: sf,
              derives7 g 0 s s
| derives7_sum: forall left: non_terminal,
                forall right: sf,
                forall i: nat,
                forall s1 s2 s3: sf,
                derives7 g i s1 (s2 ++ [inl left] ++ s3) ->
                rules g left right ->
                derives7 g (S i) s1 (s2 ++ right ++ s3).

Definition derives_direct (g: cfg) (s1 s2: sf): Prop:=
exists s' s'': sf,
exists left: non_terminal,
exists right: sf,
s1 = s' ++ [inl left] ++ s'' /\
s2 = s' ++ right ++ s'' /\
rules g left right.

Definition generates (g: cfg) (s: sf): Prop:=
derives g [inl (start_symbol g)] s.

Definition terminal_lift (t: terminal): non_terminal + terminal:=
inr t.

Definition produces (g: cfg) (s: sentence): Prop:=
generates g (map terminal_lift s).

Definition appears (g: cfg) (s: non_terminal + terminal): Prop:=
match s with
| inl n => exists left: non_terminal,
           exists right: sf,
           rules g left right /\ ((n=left) \/ (In (inl n) right))
| inr t => exists left: non_terminal,
           exists right: sf,
           rules g left right /\ In (inr t) right
end.

Inductive sflist (g: cfg): list sf -> Prop:=
| sflist_empty: sflist g []
| sflist_start: forall s: sf, 
                sflist g [s]
| sflist_step: forall l: list sf,
               forall s2 s3: sf,
               forall left: non_terminal,
               forall right: sf,
               sflist g l -> last l [] = (s2 ++ inl left :: s3) ->
               rules g left right ->
               sflist g (l++[s2 ++ right ++ s3]).

Inductive sflist2 (g: cfg): list sf -> Prop:=
| sflist2_empty: sflist2 g []
| sflist2_start: forall s: sf, 
                 sflist2 g [s]
| sflist2_step: forall l: list sf,
                forall s1 s2: sf,
                l <> [] -> sflist2 g l -> last l [] = s1 ->
                derives g s1 s2 ->
                sflist2 g (l ++ [s2]).

End ContextFreeGrammars_Definitions.

(* --------------------------------------------------------------------- *)
(* CONTEXT-FREE GRAMMARS - DEFINITIONS 2                                 *)
(* --------------------------------------------------------------------- *)

Section ContextFreeGrammars_Definitions_2.

Variables non_terminal non_terminal' terminal: Type.

Notation sentence := (list terminal).
Notation sf:= (list (non_terminal + terminal)). 

Definition g_equiv (g1: cfg non_terminal terminal) (g2: cfg non_terminal' terminal): Prop:=
forall s: sentence,
produces g1 s <-> produces g2 s.

Definition g_equiv_without_empty (g1: cfg non_terminal terminal) (g2: cfg non_terminal' terminal): Prop:=
forall s: sentence,
s <> [] ->
(produces g1 s <-> produces g2 s).

Definition start_symbol_not_in_rhs (g: cfg _ _):=
forall left: non_terminal,
forall right: sf,
rules g left right -> ~ In (inl (start_symbol g)) right.

Definition empty (g: cfg _ _) (s: non_terminal + terminal): Prop:=
derives g [s] [].

Definition not_derives_empty: Prop:=
forall g: cfg non_terminal terminal,
forall n: non_terminal,
~ derives g [inl n] [].

Definition has_no_empty_rules (g: cfg non_terminal terminal): Prop:=
forall left: _,
forall right: _,
rules g left right -> right <> [].

Definition has_one_empty_rule (g: cfg _ _): Prop:=
forall left: non_terminal,
forall right: sf,
rules g left right ->
((left = start_symbol g) /\ (right = []) \/ right <> []).

Definition has_no_nullable_symbols (g: cfg _ _): Prop:=
forall s: non_terminal + terminal, ~ empty g s.

Definition generates_empty (g: cfg _ _): Prop:=
empty g (inl (start_symbol g)).

Definition produces_empty (g: cfg non_terminal terminal): Prop:=
produces g [].

Definition produces_non_empty (g: cfg non_terminal terminal): Prop:=
exists s: sentence, produces g s /\ s <> [].

End ContextFreeGrammars_Definitions_2.

(* --------------------------------------------------------------------- *)
(* CONTEXTT-FREE GRAMMARS - LEMMAS AND THEOREMS                          *)
(* --------------------------------------------------------------------- *)

Section ContextFreeGrammars_Lemmas.

Variables non_terminal non_terminal1 non_terminal2 terminal: Type.

Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation symbol:= (non_terminal + terminal)%type.

Theorem derives_rule:
forall g: cfg _ _,
forall left: non_terminal,
forall right s1 s2: sf,
rules g left right ->
derives g (s1 ++ [inl left] ++ s2) (s1 ++ right ++ s2).
Proof.
intros g left right s1 s2 H.
apply derives_step with (left:=left).
- apply derives_refl.
- exact H.
Qed.

Theorem derives_start:
forall g: cfg _ _,
forall left: non_terminal,
forall right: sf,
rules g left right -> derives g [inl left] right.
Proof.
intros g left right H.
apply derives_rule with (s1:=[]) (s2:=[]) in H.
simpl in H.
rewrite app_nil_r in H.
exact H.
Qed.

Theorem derives_trans (g: cfg _ _) (s1 s2 s3: sf):
derives g s1 s2 ->
derives g s2 s3 ->
derives g s1 s3.
Proof.
intros H1 H2.
induction H2. 
- exact H1.
- apply derives_step with (left:=left).
  + apply IHderives.
    exact H1.
  + exact H. 
Qed.

Theorem derives2_trans (g: cfg _ _) (s1 s2 s3: sf):
derives2 g s1 s2 ->
derives2 g s2 s3 ->
derives2 g s1 s3.
Proof.
intros H1 H2.
induction H1. 
- exact H2.
- apply derives2_step with (right:=right).
  + apply IHderives2.
    exact H2.
  + exact H.
Qed.

Theorem derives_equiv_derives2:
forall g: cfg _ _,
forall s1 s2: sf,
derives g s1 s2 <-> derives2 g s1 s2.
Proof.
intros g s1 s2.
split.
- intro H.
  induction H.
  + apply derives2_refl.
  + inversion IHderives.
    * {
      apply derives2_step with (right:=right).
      - apply derives2_refl.
      - exact H0.
      }
    * {
      apply derives2_step with (right:=right0).
      - apply derives2_trans with (s2:=(s2 ++ inl left :: s3)).
        + exact H1.
        + apply derives2_step with (right:=right).
          * apply derives2_refl.
          * exact H0.
      - exact H2.
      }
- intro H.
  induction H.
  + apply derives_refl.
  + inversion IHderives2.
    * apply derives_rule.
      exact H0.
    * {
      apply derives_trans with (s2:=s1 ++ right ++ s2).
      - apply derives_rule.
        exact H0.
      - apply derives_step with (right:=right0) in H1.
        + exact H1.
        + exact H2.
        }
Qed.

Theorem derives_context_free_add_left (g: cfg _ _) (s1 s2 s: sf):
derives g s1 s2 -> derives g (s++s1) (s++s2).
Proof.
intros H.
induction H as [| x y z left right H1 H2 H3].
apply derives_refl.
remember (s++x) as w1.
rewrite app_assoc.
rewrite app_assoc in H2.
remember (s++y) as w2.
apply derives_step with (left:=left).
exact H2.
exact H3.
Qed.

Theorem derives_context_free_add_right (g: cfg _ _) (s1 s2 s: sf):
derives g s1 s2 -> derives g (s1++s) (s2++s).
Proof.
intros H.
induction H as [| x y z left right H1 H2 H3].
apply derives_refl.
remember (x++s) as w1.
rewrite <- app_assoc.
rewrite <- app_assoc.
rewrite <- app_assoc in H2.
rewrite <- app_comm_cons in H2.
remember (z++s) as w2.
apply derives_step with (left:=left).
exact H2.
exact H3.
Qed.

Theorem derives_context_free_add (g: cfg _ _) (s1 s2 s s': sf):
derives g s1 s2 -> derives g (s++s1++s') (s++s2++s').
Proof.
intros H.
apply derives_context_free_add_left.
apply derives_context_free_add_right.
exact H.
Qed.

Theorem derives6_context_free_add_left (g: cfg _ _) (n: nat) (s1 s2 s: sf):
derives6 g n s1 s2 -> derives6 g n (s++s1) (s++s2).
Proof.
intros H.
induction H.
- apply derives6_0.
- apply derives6_sum with (i:= i) (s1:= s ++ s1) (s2:= s2) (s3:= s ++ s3) in H.
  + rewrite <- app_assoc in H. 
    exact H.
  + rewrite <- app_assoc.
    exact IHderives6.
Qed.

Theorem derives6_context_free_add_right (g: cfg _ _) (n: nat) (s1 s2 s: sf):
derives6 g n s1 s2 -> derives6 g n (s1++s) (s2++s).
Proof.
intros H.
induction H.
- apply derives6_0.
- repeat rewrite <- app_assoc in IHderives6.  
  apply derives6_sum with (i:= i) (s1:= s1) (s2:= s2 ++ s) (s3:= s3 ++ s) in H.
  + repeat rewrite <- app_assoc. 
    exact H.
  + exact IHderives6.
Qed.

Theorem derives6_context_free_add (g: cfg _ _) (n: nat) (s1 s2 s s': sf):
derives6 g n s1 s2 -> derives6 g n (s++s1++s') (s++s2++s').
Proof.
intros H.
apply derives6_context_free_add_left.
apply derives6_context_free_add_right.
exact H.
Qed.

Lemma derives6_cat_sum:
forall g: cfg _ _,
forall n1 n2: nat,
forall s1 s2 s3 s4: sf,
derives6 g n1 s1 s2 ->
derives6 g n2 s3 s4 ->
derives6 g (n1 + n2) (s1 ++ s3) (s2 ++ s4).
Proof.
intros g n1.
induction n1.
- intros n2 s1 s2 s3 s4 H1 H2.
  inversion H1.
  simpl.
  inversion H1.
  apply derives6_context_free_add_left.
  exact H2.
- intros n2 s1 s2 s3 s4 H1 H2.
  inversion H1.
  specialize (IHn1 n2 (s0 ++ right ++ s5) s2 s3 s4 H3 H2).
  apply derives6_sum with (i:= n1 + n2) (s1:= s0) (s2:= s5 ++ s3) (s3:= s2 ++ s4) in H0.
  + repeat rewrite <- app_assoc.
    exact H0.
  + repeat rewrite <- app_assoc in IHn1.
    exact IHn1.
Qed.

Theorem derives_combine (g: cfg _ _) (s1 s2 s3 s4: sf):
derives g s1 s2 /\ derives g s3 s4 -> derives g (s1++s3) (s2++s4).
Proof.
intros [H1 H2].
induction H1,H2.
apply derives_refl.
apply derives_context_free_add_left.
apply derives_step with (left:= left).
exact H2.
exact H.
apply derives_context_free_add_right.
apply derives_step with (left:=left).
exact H1.
exact H.
rewrite <- app_assoc.
rewrite <- app_assoc.
rewrite <- app_assoc in IHderives.
simpl in IHderives.
remember (s0 ++ s4 ++ right0 ++ s5) as w.
apply derives_step with (left:=left).
exact IHderives.
exact H.
Qed.

Lemma derives_multiple (g: cfg _ _) (s1 s2 s3: sf) (left: non_terminal) (right1 right2: sf):
derives g s1 (s2 ++ inl left :: s3) ->
rules g left right1 ->
rules g left right2 ->
derives g s1 (s2 ++ right1 ++ s3) /\ derives g s1 (s2 ++ right2 ++ s3).
Proof.
intros H1 H2 H3.
split.
- apply derives_step with (left:= left).
  exact H1.
  exact H2.
- apply derives_step with (left:= left).
  exact H1.
  exact H3.
Qed.

Lemma derives_subs:
forall g: cfg _ _,
forall s1 s2 s3 s3' s4: sf,
derives g s1 (s2++s3++s4) -> 
derives g s3 s3' ->
derives g s1 (s2++s3'++s4).
Proof.
intros g s1 s2 s3 s3' s4 H1 H2.
induction H2.
- exact H1.
- specialize (IHderives H1).
  rewrite <- app_assoc in IHderives.
  simpl in IHderives.
  repeat rewrite <- app_assoc.
  remember (s5++s4) as w2.
  rewrite app_assoc.
  apply derives_step with (left:=left).
  subst.
  rewrite <- app_assoc.
  exact IHderives.
  exact H.
Qed.

Lemma derives_split:
forall g: cfg _ _,
forall s1 s2 s3: sf,
derives g (s1 ++ s2) s3 ->
exists s1' s2': sf, s3 = s1' ++ s2' /\ derives g s1 s1' /\ derives g s2 s2'.
Proof.
intros g s1 s2 s3 H.
remember (s1++s2) as w.
induction H. 
- exists s1, s2.
  split.
  + exact Heqw.
  + split. 
    * apply derives_refl.
    * apply derives_refl.
- specialize (IHderives Heqw).
  destruct IHderives as [s1' [s2' [H10 [H11 H12]]]].
  apply equal_app in H10.
  destruct H10 as [H10 | H10].
  + destruct H10 as [l [H20 H21]].
    destruct l.
    * simpl in H21.
      {
      destruct s2'.
      - inversion H21.
      - inversion H21.
        subst.
        exists s3, (right ++ s2').
        split.
        + reflexivity.
        + split.
          * rewrite app_nil_r in H11.
            exact H11.
          * rewrite <- app_nil_l in H12.
            { 
            apply derives_step with (right:=right) in H12.
            - exact H12.
            - exact H0.
            }
      }
    * inversion H21.
      subst.
      exists (s3 ++ right ++ l), s2'.
      {
      split.
      - repeat rewrite <- app_assoc. 
        reflexivity.
      - split.
        + apply derives_step with (right:=right) in H11.
          * exact H11.
          * exact H0.
        + exact H12.
      }   
  + destruct H10 as [l [H20 H21]].
    destruct l.
    * simpl in H21.
      rewrite app_nil_r in H20.
      subst.
      exists s1', (right ++ s4).
      {
      split.
      - reflexivity.
      - split.
        exact H11.
        rewrite <- app_nil_l in H12.
        apply derives_step with (right:=right) in H12.
        + exact H12.
        + exact H0.
      }
    * {
      destruct s2'. 
      - inversion H21.
      - inversion H21.
        subst.
        exists s1', (s :: l ++ right ++ s4).
        split.
        + repeat rewrite <- app_assoc.
          reflexivity.
        + split.
          * exact H11.
          * {
            apply derives_step with (s2:=s :: l) (right:=right) in H12.
            - exact H12.
            - exact H0.
            }
      }
Qed. 

Lemma derives_app_empty:
forall g: cfg _ _,
forall s1 s2: sf,
derives g (s1 ++ s2) (map term_lift []) ->
derives g s1 (map term_lift []) /\ derives g s2 (map term_lift []).
Proof.
intros g s1 s2 H.
apply derives_split in H.
destruct H as [s1' [s2' [H1 [H2 H3]]]].
simpl in H1.
symmetry in H1.
apply app_eq_nil in H1.
destruct H1 as [H4 H5].
subst.
split.
- exact H2.
- exact H3.
Qed.

Lemma derives_nt_sentence:
forall g: cfg _ _,
forall l1 l2: sf,
forall n: non_terminal,
forall s: sentence,
derives g (l1 ++ inl n :: l2) (map term_lift s) -> 
exists s': sentence,
derives g [inl n] (map term_lift s').
Proof.
intros g l1 l2 n s H.
apply derives_split in H.
destruct H as [s1' [s2' [H2 [_ H4]]]].
symmetry in H2.
apply map_expand in H2.
destruct H2 as [_ [s2'0 [_ [_ H5]]]].
rewrite <- H5 in H4.
replace (inl n::l2) with ([inl n]++l2) in H4.
- apply derives_split in H4.
  destruct H4 as [s1'0 [s2'1 [H6 [H7 _]]]].
  symmetry in H6.
  apply map_expand in H6.
  destruct H6 as [s1'1 [_ [_ [H8 _]]]].
  rewrite <- H8 in H7.
  exists s1'1.
  exact H7.
- simpl.
  reflexivity.
Qed.

Lemma derives_nt_sf:
forall g: cfg _ _,
forall s1 s2: sf,
derives g s1 s2 ->
forall n: non_terminal,
In (inl n) s1 ->
exists s1' s1'' s2' s2'' beta: sf,
s1 = s1' ++ [inl n] ++ s1'' /\
s2 = s2' ++ beta ++ s2'' /\
derives g [inl n] beta.
Proof.
intros g s1 s2 H1 n H2.
apply in_split in H2.
destruct H2 as [l1 [l2 H3]].
exists l1, l2.
rewrite H3 in H1.
apply derives_split in H1.
destruct H1 as [s1' [s2' [H4 [H5 H6]]]].
change (inl n :: l2) with ([inl n] ++ l2) in H6.
apply derives_split in H6.
destruct H6 as [s1'0 [s2'0 [H7 [H8 H9]]]].
exists s1', s2'0, s1'0.
split. 
- exact H3. 
- split.
  + rewrite H7 in H4.
    exact H4.
  + exact H8. 
Qed.

Lemma derives_nt_sf':
forall g: cfg _ _,
forall l1 l2 l3: sf,
forall n: non_terminal,
derives g (l1 ++ inl n :: l2) l3 -> 
exists l': sf,
derives g [inl n] l'.
Proof.
intros g l1 l2 l3 n H.
apply derives_split in H.
destruct H as [s1' [s2' [H2 [_ H4]]]].
symmetry in H2.
replace (inl n :: l2) with ([inl n] ++ l2) in H4.
- apply derives_split in H4.
  destruct H4 as [s1'0 [s2'0 [H2' [H3' _]]]].
  exists s1'0.
  exact H3'.
- simpl.
  reflexivity.
Qed.

Lemma derives3_equiv_derives3_aux:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sentence,
derives3 g n s <-> derives3_aux g [inl n] s.
Proof.
intros g n s.
split.
- intros H.
  inversion H.
  + subst.
    rewrite <- app_nil_r.
    rewrite <- app_nil_r at 1.
    apply derives3_aux_nt.
    * apply derives3_aux_empty.
    * exact H. 
  + subst.
    rewrite <- app_nil_r.
    rewrite <- app_nil_r at 1.
    apply derives3_aux_nt.
    * apply derives3_aux_empty.
    * exact H.
- intros H.
  inversion H.
  inversion H2.
  subst.
  rewrite app_nil_r.
  exact H4.
Qed.    

Theorem derives3_aux_combine (g: cfg _ _) (s1 s2: sf) (s3 s4: sentence):
derives3_aux g s1 s3 ->
derives3_aux g s2 s4 -> 
derives3_aux g (s1++s2) (s3++s4).
Proof. 
intros H.
induction H.
- intros H.
  exact H.
- intros H1.
  change (inr t :: ltnt) with ([inr t] ++ ltnt).
  change (t :: lt) with ([t] ++ lt).
  repeat rewrite <- app_assoc.
  apply derives3_aux_t.
  apply IHderives3_aux.
  exact H1.
- intros H1.
  change (inl n :: ltnt) with ([inl n] ++ ltnt).
  repeat rewrite <- app_assoc.
  apply derives3_aux_nt.
  + apply IHderives3_aux.
    exact H1.
  + exact H0.
Qed.

Lemma derives3_aux_split:
forall g: cfg _ _,
forall s1 s2: sf,
forall s3: sentence,
derives3_aux g (s1 ++ s2) s3 ->
exists s3' s3'': sentence, 
derives3_aux g s1 s3' /\ derives3_aux g s2 s3'' /\ s3 = s3' ++ s3''.
Proof.
intros g s1 s2.
induction s1 as [ | c s11 IH]. 
- simpl. 
  intros s3 H. 
  exists [], s3.
  split. 
  + apply derives3_aux_empty. 
  + split. 
    * exact H. 
    * trivial.
- destruct c as [n | t]. 
  + simpl. 
    intros s3 H. 
    inversion H. 
    subst. 
    clear H.
    specialize (IH _ H2).
    destruct IH as (s21 & s22 & IH1 & IH2 & IH3). 
    subst.
    exists (lt' ++ s21), s22.
    split.  
    * {
      apply derives3_aux_nt. 
      - exact IH1. 
      - exact H4.
      } 
    * {
      split.
      - exact IH2. 
      - rewrite <- app_assoc. 
        reflexivity.
      } 
  + simpl. 
    intros s3 H. 
    inversion H. 
    subst. 
    clear H.
    specialize (IH _ H3).
    destruct IH as (s21 & s22 & IH1 & IH2 & IH3). 
    subst.
    exists (t :: s21), s22.
    split.
    * apply derives3_aux_t. 
      exact IH1. 
    * {
      split. 
      - exact IH2. 
      - trivial.
      } 
Qed.

Lemma derives_implies_derives3_aux:
forall g: cfg _ _,
forall s1: sf,
forall s2: sentence,
derives g s1 (map term_lift s2) -> derives3_aux g s1 s2.
Proof.
intros g s1 s2.
remember (map term_lift s2) as s2'.
rewrite derives_equiv_derives2.
intros H.
induction H as [s | s_1 s_2 s_3 left right H1 H2 H3].
- subst.
  induction s2 as [| c s IH].
  + apply derives3_aux_empty. 
  + replace (c :: s) with ([c] ++ s).
    * rewrite map_app. 
      apply derives3_aux_t.
      exact IH.
    * simpl. 
      reflexivity.
- rewrite Heqs2' in H2. 
  specialize (H2 eq_refl).
  apply derives3_aux_split in H2.
  destruct H2 as [s3' [s3'' [H4 [H5 H6]]]]. 
  subst s2.
  apply derives3_aux_combine. 
  + exact H4. 
  + apply derives3_aux_split in H5.
    destruct H5 as [s3'0 [s3''0 [H7 [H8 H9]]]].
    subst s3''.
    apply derives3_aux_nt. 
    * exact H8. 
    * {
      apply derives3_step with (ltnt:=right).
      - exact H3.
      - exact H7.
      } 
Qed.

Lemma derives3_implies_derives_and_derives3_aux_implies_derives:
forall g: cfg _ _,
(forall n: non_terminal, 
 forall s: sentence, 
 derives3 g n s -> derives g [inl n] (map term_lift s)) 
/\
(forall s1: sf,
 forall s2: sentence,
 derives3_aux g s1 s2 -> derives g s1 (map term_lift s2)).
Proof.
intros g.
apply derives3_comb_ind.
- intros n lt H.
  rewrite derives_equiv_derives2.
  rewrite <- (app_nil_l [inl n]).
  apply derives2_step with (right:=(map inr lt)).
  + rewrite app_nil_l. 
    rewrite app_nil_r.  
    apply derives2_refl.
  + exact H.
- intros n ltnt lt H1 H2 H3.
  rewrite derives_equiv_derives2.
  rewrite <- (app_nil_l [inl n]).
  apply derives2_step with (right:=ltnt).
  + rewrite app_nil_l. 
    rewrite app_nil_r.  
    rewrite <- derives_equiv_derives2.
    exact H3.
  + exact H1.
- simpl.
  apply derives_refl.
- intros t ltnt lt H1 H2.
  simpl. 
  replace (inr t :: ltnt) with ([inr t] ++ ltnt).
  + replace (term_lift t :: map term_lift lt) with ([term_lift t] ++ map term_lift lt).
    * apply derives_context_free_add_left.
      exact H2.
    * simpl. 
      reflexivity.
  + simpl. 
    reflexivity.
- intros n lt lt' ltnt H1 H2 H3 H4.
  change (inl n :: ltnt) with ([inl n] ++ ltnt).
  rewrite map_app.
  apply derives_combine.
  split. 
  + exact H4.
  + exact H2.  
Qed.

Lemma derives3_implies_derives:
forall g: cfg _ _,
forall n: non_terminal, 
forall s: sentence, 
derives3 g n s -> derives g [inl n] (map term_lift s).
Proof.
intros g n s H.
apply derives3_implies_derives_and_derives3_aux_implies_derives in H.
exact H.
Qed.

Lemma derives3_aux_implies_derives:
forall g: cfg _ _,
forall s1: sf,
forall s2: sentence,
derives3_aux g s1 s2 -> derives g s1 (map term_lift s2).
Proof.
intros g n s H.
apply derives3_implies_derives_and_derives3_aux_implies_derives in H.
exact H.
Qed.

Lemma derives_implies_derives3:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sentence,
derives g [inl n] (map term_lift s) -> derives3 g n s.
Proof.
intros g n s H.
rewrite derives3_equiv_derives3_aux.
apply derives_implies_derives3_aux.
exact H.
Qed.

Lemma derives_equiv_derives3:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sentence,
derives g [inl n] (map term_lift s) <-> derives3 g n s.
Proof.
intros g n s.
split.
- intros H.
  apply derives_implies_derives3.
  exact H.
- intros H.
  apply derives3_implies_derives.
  exact H.
Qed.

Lemma derives_equiv_derives3_aux:
forall g: cfg _ _,
forall s1: sf,
forall s2: sentence,
derives g s1 (map term_lift s2) <-> derives3_aux g s1 s2.
Proof.
intros g s1 s2.
split.
- intros H.
  apply derives_implies_derives3_aux.
  exact H.
- intros H.
  apply derives3_aux_implies_derives.
  exact H.
Qed.

Lemma derives_equiv_derives4:
forall g: cfg _ _,
forall s1 s2: sf,
derives g s1 s2 <-> derives4 g s1 s2.
Proof.
intros g s1 s2.
split.
- intros H.
  induction H.
  + apply derives4_refl.
  + apply derives4_rule with (s1:=s2) (s2:=s3) in H0.
    apply derives4_trans with (s2:=(s2 ++ [inl left] ++ s3)).
    * exact IHderives.
    * exact H0.
- intros H.
  induction H.
  + apply derives_refl.
  + apply derives_step with (left:=left).
    * apply derives_refl.
    * exact H.
  + apply derives_trans with (s2:=s2).
    * exact IHderives4_1.
    * exact IHderives4_2. 
Qed.

Lemma derives4_equiv_derives5:
forall g: cfg _ _,
forall s1 s2: sf,
derives4 g s1 s2 <-> exists n: nat, derives5 g n s1 s2.
Proof.
intros g s1 s2.
split.
- intro H.
  induction H.
  + exists 0.
    apply derives5_0.
  + exists 1.
    apply derives5_1.
    exact H.
  + destruct IHderives4_1 as [n1 H1].
    destruct IHderives4_2 as [n2 H2].
    exists (n1+n2).
    apply derives5_sum with (s2:=s2).
    * exact H1. 
    * exact H2.
- intro H0.
  destruct H0 as [n H1].
  induction H1.
  + apply derives4_refl.
  + apply derives4_rule.
    exact H.
  + apply derives4_trans with (s2:=s2).
    * exact IHderives5_1.
    * exact IHderives5_2.
Qed.

Lemma derives6_trans:
forall g: cfg _ _,
forall i j: nat,
forall s1 s2 s3: sf,
derives6 g i s1 s2 ->
derives6 g j s2 s3 ->
derives6 g (i+j) s1 s3.
Proof.
intros g i j s1 s2 s3 H.
induction H.
- intros H1.
  simpl. 
  exact H1.
- intros H1.
  rewrite plus_Sn_m.
  apply derives6_sum with (right:=right).
  + exact H.
  + apply IHderives6.
    exact H1.
Qed.

Lemma derives5_equiv_derives6:
forall g: cfg _ _,
forall n: nat,
forall s1 s2: sf,
derives5 g n s1 s2 <-> derives6 g n s1 s2.
Proof. 
intros g n s1 s2.
split.
- intros H. 
  induction H.
  + apply derives6_0.
  + apply derives6_sum with (right:=right).
    * exact H.
    * apply derives6_0.
  + apply derives6_trans with (s2:=s2).
    * exact IHderives5_1.
    * exact IHderives5_2.  
- intros H.
  induction H.
  + apply derives5_0.
  + replace (S i) with (1 + i). 
    * {
      apply derives5_sum with (s2:=s1++right++s2).
      - apply derives5_1.
        exact H.
      - exact IHderives6.
      }
    * simpl. 
      reflexivity.     
Qed.

Lemma derives_equiv_derives6:
forall g: cfg _ _,
forall s1 s2: sf,
derives g s1 s2 <-> exists n: nat, derives6 g n s1 s2.
Proof.
intros g s1 s2.
split.
- intros H.
  rewrite derives_equiv_derives4 in H.
  rewrite derives4_equiv_derives5 in H.
  destruct H as [n H1].
  rewrite derives5_equiv_derives6 in H1.
  exists n.
  exact H1.
- intros H.
  destruct H as [n H1].
  rewrite <- derives5_equiv_derives6 in H1.
  assert (H2: exists n: nat, derives5 g n s1 s2).
    {   
    exists n.
    exact H1.
    }
  rewrite <- derives4_equiv_derives5 in H2. 
  rewrite <- derives_equiv_derives4 in H2.
  exact H2.
Qed.

Lemma derives5_0_eq:
forall g: cfg _ _,
forall s1 s2: sf,
derives5 g 0 s1 s2 ->
s1 = s2.
Proof. 
intros g s1 s2 H.
rewrite derives5_equiv_derives6 in H.
inversion H.
reflexivity.
Qed.

Lemma derives6_0_eq:
forall g: cfg _ _,
forall s1 s2: sf,
derives6 g 0 s1 s2 ->
s1 = s2.
Proof. 
intros g s1 s2 H.
inversion H.
reflexivity.
Qed.

Lemma derives7_0_eq:
forall g: cfg _ _,
forall s1 s2: sf,
derives7 g 0 s1 s2 ->
s1 = s2.
Proof. 
intros g s1 s2 H.
inversion H.
reflexivity.
Qed.

Lemma derives7_sum_aux: 
forall g: cfg _ _,
forall left: non_terminal,
forall right: sf,
forall i: nat,
forall s1 s2 s3: sf,
rules g left right ->
derives7 g i (s1 ++ right ++ s2) s3 ->
derives7 g (S i) (s1 ++ [inl left] ++ s2) s3.
Proof.
intros g left right i s1 s2 s3 H1 H2.
remember (s1 ++ right ++ s2) as w.
induction H2.
- rewrite Heqw.
  apply derives7_sum with (left:=left).
  + apply derives7_0. 
  + exact H1.
- specialize (IHderives7 Heqw).
  apply derives7_sum with (left:=left0).
  + exact IHderives7.
  + exact H.
Qed.

Lemma derives7_trans:
forall g: cfg _ _,
forall i j: nat,
forall s1 s2 s3: sf,
derives7 g i s1 s2 ->
derives7 g j s2 s3 ->
derives7 g (i+j) s1 s3.
Proof.
intros g i j s1 s2 s3 H1 H2.
induction H2.
- rewrite plus_0_r.
  exact H1.
- specialize (IHderives7 H1).
  apply derives7_sum with (right:= right) in IHderives7.
  + rewrite plus_n_Sm in IHderives7. 
    exact IHderives7.
  + exact H.
Qed.

Lemma derives6_equiv_derives7:
forall g: cfg _ _,
forall n: nat,
forall s1 s2: sf,
derives6 g n s1 s2 <-> derives7 g n s1 s2.
Proof.
intros g n s1 s2.
split.
- intros H.
  induction H.
  + apply derives7_0.
  + inversion IHderives6.
    * {
      apply derives7_sum with (left:= left).
      - apply derives7_0. 
      - exact H.
      }
    * {
      apply derives7_trans with (g:=g) (i:=1) (j:=S i0) (s2:=s1 ++ right ++ s2).
      - apply derives7_sum with (left:= left).
        + apply derives7_0.
        + exact H.
      - replace (S i0) with (i0 + 1). 
        + apply derives7_trans with (g:=g) (i:=i0) (j:=1) (s2:=(s4 ++ [inl left0] ++ s5)).
          * exact H1.
          * {
            apply derives7_sum with (left:= left0).
            - apply derives7_0.
            - exact H2.
            }
        + omega.
      }
- intros H.
  induction H.
  + apply derives6_0.
  + inversion IHderives7.
    * subst.
      {
      apply derives6_sum with (right:= right).
      - exact H0.
      - apply derives6_0.
      }
    * {
      apply derives6_trans with (g:=g) (i:=1) (j:=S i0) (s2:=s0 ++ right0 ++ s4).
      - apply derives6_sum with (right:=right0).
        + exact H1.
        + apply derives6_0.
      - replace (S i0) with (i0 + 1). 
        + apply derives6_trans with (g:=g) (i:=i0) (j:=1) (s2:=(s2 ++ [inl left] ++ s3)).
          * exact H2. 
          * {
            apply derives6_sum with (right:= right). 
            - exact H0.
            - apply derives6_0.
            } 
        + omega.
      }
Qed.    

Lemma derives6_split:
forall g: cfg _ _,
forall s1 s2 s3: sf,
forall n: nat,
derives6 g n (s1 ++ s2) s3 ->
exists s1' s2': sf, 
exists n1 n2: nat,
s3 = s1' ++ s2' /\ 
n = n1 + n2 /\
derives6 g n1 s1 s1' /\ 
derives6 g n2 s2 s2'.
Proof.
intros g s1 s2 s3 n H.
rewrite derives6_equiv_derives7 in H.
remember (s1 ++ s2) as w.
induction H.
- exists s1, s2, 0, 0.
  split.
  + exact Heqw. 
  + split.    
    * reflexivity.
    * {
      split. 
      - apply derives6_0.
      - apply derives6_0.
      }
- rewrite <- derives6_equiv_derives7 in H.
  specialize (IHderives7 Heqw).
  destruct IHderives7 as [s1' [s2' [n1 [n2 [H10 [H11 [H12 H13]]]]]]].
  apply equal_app in H10.
  destruct H10 as [H10 | H10].
  + destruct H10 as [l [H20 H21]].
    destruct l.
    * simpl in H21.
      {
      destruct s2'.
      - inversion H21.
      - inversion H21.
        subst.
        exists s3, (right ++ s2'), n1, (S n2).
        split.
        + reflexivity.
        + split.
          * omega.
          * {
            split.
            - rewrite app_nil_r in H12.
              exact H12.
            - rewrite derives6_equiv_derives7 in H13.
              replace (inl left :: s2') with ([] ++ [inl left] ++ s2') in H13.
              apply derives7_sum with (right:= right) in H13.
              + rewrite app_nil_l in H13. 
                rewrite <- derives6_equiv_derives7 in H13.
                exact H13.
              + exact H0.
            }
      }
    * inversion H21.
      subst.
      exists (s3 ++ right ++ l), s2', (S n1), n2.
      {
      split.
      - repeat rewrite <- app_assoc. 
        reflexivity.
      - split.
        + omega.
        + split.
          * rewrite derives6_equiv_derives7 in H12.
            { 
            replace (s3 ++ inl left :: l) with (s3 ++ [inl left] ++ l) in H12.
            - apply derives7_sum with (right:= right) in H12.
              + rewrite <- derives6_equiv_derives7 in H12. 
                exact H12.
              + exact H0.
            - simpl.
              reflexivity.
            }
          * exact H13.
      } 
  + destruct H10 as [l [H20 H21]].
    destruct l.
    * simpl in H21.
      rewrite app_nil_r in H20.
      subst.
      exists s1', (right ++ s4), n1, (S n2).
      {
      split.
      - reflexivity.
      - split.
        + omega. 
        + split.
          * exact H12.
          * rewrite derives6_equiv_derives7 in H13.
            {
            replace (inl left :: s4) with ([] ++ [inl left] ++ s4) in H13.
            - apply derives7_sum with (right:= right) in H13.
              + simpl in H13.
                rewrite <- derives6_equiv_derives7 in H13. 
                exact H13.
              + exact H0.
            - simpl.
              reflexivity.
            }
      }   
    * {
      destruct s2'. 
      - inversion H21.
      - inversion H21.
        subst.
        exists s1', (s :: l ++ right ++ s4), n1, (S n2).
        split.
        + repeat rewrite <- app_assoc.
          reflexivity.
        + split.
          * omega.
          * {
            split.
            - exact H12.
            - rewrite derives6_equiv_derives7 in H13.
              replace (s :: l ++ inl left :: s4) with ([s] ++ l ++ [inl left] ++ s4) in H13.
              rewrite app_assoc in H13.
              apply derives7_sum with (right:= right) in H13.
              + replace (s :: l ++ right ++ s4) with ([s] ++ l ++ right ++ s4).
                * rewrite app_assoc.
                  rewrite <- derives6_equiv_derives7 in H13.
                  exact H13.
                * simpl.
                  reflexivity.
              + exact H0.
            }
      } 
Qed. 

Lemma derives6_split_all:
forall g: cfg _ _,
forall s1 s2: sf,
forall n: nat,
derives6 g n s1 s2 ->
forall s: symbol,
In s s1 ->
exists s2' s2'' s3: sf, 
exists n': nat,
derives6 g n' [s] s3 /\
s2 = s2' ++ s3 ++ s2'' /\
n' <= n.
Proof.
intros g s1 s2 n H1 s H2.
apply in_split in H2.
destruct H2 as [l1 [l2 H2]].
subst.
apply derives6_split in H1.
destruct H1 as [s1' [s2' [n1 [n2 [H2 [H3 [H4 H5]]]]]]].
change (s :: l2) with ([s] ++ l2) in H5.
apply derives6_split in H5.
destruct H5 as [s1'0 [s2'0 [n0 [n3 [H6 [H7 [H8 H9]]]]]]].
rewrite H2.
rewrite H6.
exists s1', s2'0, s1'0, n0.
split.
- exact H8.
- split.
  + reflexivity.
  + omega.
Qed.

Lemma derives2_equiv_derives7:
forall g: cfg _ _,
forall s1 s2: sf,
derives2 g s1 s2 <-> exists n: nat, derives7 g n s1 s2.
Proof.
intros g s1 s2.
split.
- intros H.
  induction H.
  + exists 0.
    apply derives7_0.
  + destruct IHderives2 as [n H1].
    exists (S n).
    inversion H1.
    * {
      apply derives7_sum with (left:= left).
      - apply derives7_0.
      - exact H0.
      }
    * {
      apply derives7_sum with (left:=left0).
      - apply derives7_sum_aux with (right:=right).
        + exact H0.
        + exact H2.
      - exact H3.
      }
- intros H.
  destruct H as [n H].
  induction H.
  + apply derives2_refl.
  + inversion IHderives7.
    * {
      apply derives2_step with (right:=right).
      - apply derives2_refl.
      - exact H0.
      }
    * {
      apply derives2_step with (left:=left0) in H1.
      - apply derives2_trans with (s2:=(s2 ++ [inl left] ++ s3)).
        + exact H1.
        + apply derives2_step with (right:=right).
          * apply derives2_refl.
          * exact H0.
      - exact H2.
      }
Qed.  

(* --------------------------------------------------------------------- *)
(* GRAMMARS - LEMMAS AND THEOREMS                                        *)
(* --------------------------------------------------------------------- *)

Lemma lt2_sflist:
forall g: cfg _ _,
forall l: list sf,
length l < 2 -> sflist g l.
Proof.
intros g l H.
destruct l as [|s l].
- apply sflist_empty.
- replace (s::l) with ([s]++l) in H.
  + rewrite app_length in H.
    simpl in H.
    assert (H1: length l = 0) by omega.
    apply length_zero in H1.
    subst.
    apply sflist_start.
  + simpl.
    reflexivity.
Qed.

Lemma sflist_rules':
forall g: cfg _ _,
forall n: nat,
forall l: list sf,
length l = n ->
length l >= 2-> (sflist g l -> 
                (forall i: nat,
                 i <= (length l)-2 ->
                 exists left: non_terminal,
                 exists right s s': sf,
                 nth i l [] = s++inl left::s' /\
                 nth (S i) l [] = s++right++s' /\
                 rules g left right)).
Proof.
intros g n.
induction n.
- intros l H1 H2.
  rewrite H1 in H2.
  apply le_Sn_0 in H2.
  contradiction.
- intros l H1 H2 H3 i H4.
  inversion H3.
  + subst.
    simpl in H1. 
    apply O_S in H1.
    contradiction.
  + subst.
    simpl in H2.
    apply le_S_n in H2.
    inversion H2.
  + specialize (IHn l0).
    rewrite <- H6 in H1.
    rewrite app_length in H1.
    simpl in H1.
    rewrite <- plus_n_Sm in H1.
    rewrite plus_0_r in H1.
    inversion H1.
    specialize (IHn H8).
    assert (H10: length l0 >= 2 \/ length l0 < 2).
      { 
      apply le_or_lt.
      }
    destruct H10.
    * specialize (IHn H7 H i).
      assert (H11: i <= length l0 -2 \/ i > length l0 - 2).
        { 
        apply le_or_lt.
        }
      {
      destruct H11.
      - specialize (IHn H9).
        destruct IHn as [left1 [right1 [s [s' [H15 [H16 H17]]]]]].
        exists left1, right1, s, s'.
        split. 
        + rewrite app_nth1.
          * exact H15.
          * omega. 
        + split.
          * {
            rewrite app_nth1.
            - exact H16.
            - omega.
            }
          * exact H17. 
      - rewrite app_removelast_last with (l:=l0) (d:=[]).
        + rewrite <- app_assoc.
          assert (H23: length (removelast l0) = length l0 - 1).
            {
            rewrite app_removelast_last with (l:=l0) (d:=[]) at 2.
            - rewrite app_length.
              simpl. 
              omega.
            - apply not_eq_sym.
              apply length_not_zero.
              omega.
            }
          assert (H21: i - length (removelast l0) >= 0).
            {
            omega.
            }
          assert (H22: i - length (removelast l0) <= 0).
            {
            subst.
            rewrite app_length in H4.
            simpl in H4.
            rewrite H23.
            omega.
            }
          assert (H20: i - length (removelast l0) = 0).
            { 
            omega. 
            }
          rewrite app_nth2.
          * exists left, right, s2, s3.
            {
            split. 
            - rewrite H0.
              rewrite H20.
              simpl.   
              reflexivity.
            - rewrite app_nth2.
              + split. 
                * rewrite H0.
                  assert (H24: (S i - Datatypes.length (removelast l0) = 1)).
                    { 
                    rewrite <- minus_Sn_m.
                    - apply eq_S in H20.
                      exact H20.
                    - omega.
                    }
                  rewrite H24.
                  simpl.
                  reflexivity.  
                * exact H5.
              + omega.
            }
          * rewrite H23.
            omega.
        + apply not_eq_sym.
          apply length_not_zero.
          omega.
      }
    * exists left, right, s2, s3.
      assert (H10: l0 = [s2 ++ inl left :: s3]).
        { 
        destruct l0 as [|s l0]. 
        - inversion H0.
          destruct s2. 
          + simpl in H10.
            inversion H10.
          + inversion H10.
        - assert (H12: length l0 = 0).
            { 
            simpl in H7.
            apply lt_S_n in H7.
            omega.
            }
          assert (H13: l0 = []).
            { 
            destruct l0.
            - reflexivity.
            - simpl in H12.
              symmetry in H12. 
              apply O_S in H12.
              contradiction.
            }
          subst. 
          simpl in H0.
          rewrite H0.
          reflexivity.
        }
      rewrite H10.
      assert (H12: length l = 2).
        { 
        rewrite <- H6.
        rewrite H10.
        simpl.
        reflexivity.
        }
      assert (H11: i = 0).
        {
        rewrite H12 in H4.
        simpl in H4.
        omega.
        }
      rewrite H11.
      {
      split. 
      - simpl. 
        reflexivity.
      - split. 
        + simpl.
          reflexivity.
        + exact H5.  
      }
Qed.

Lemma sflist_rules'':
forall g: cfg _ _,
forall n: nat,
forall l: list sf,
length l = n ->
length l >= 2-> (forall i: nat,
                 i <= (length l)-2 ->
                 exists left: non_terminal,
                 exists right s s': sf,
                 nth i l [] = s++inl left::s' /\
                 nth (S i) l [] = s++right++s' /\
                 rules g left right) -> sflist g l.
Proof.
intros g n.
induction n.
- intros l H0 H1 H2.
  assert (EMPTY: l = []).
    {
    destruct l as [|s l].
    - reflexivity.
    - simpl in H0.
      symmetry in H0.
      apply O_S in H0.
      contradiction.
    }
  subst.
  apply sflist_empty.
- intros l H0 H1 H2.
  rewrite app_removelast_last with (d:=[]).
  + specialize (IHn (removelast l)).
    assert (H3: length (removelast l) = n).
      {
      rewrite app_removelast_last with (l:=l) (d:=[]) in H0.
      - rewrite app_length in H0.
        simpl in H0.
        omega.
      - destruct l as [|s l].
        + simpl in H1.
          apply le_Sn_0 in H1.
          contradiction.
        + apply not_eq_sym. 
          apply nil_cons.
      }
    specialize (IHn H3).
    assert (H4: length (removelast l) >= 2 \/ length (removelast l) < 2).
      {
      apply le_or_lt.
      }
    destruct H4 as [H | H].
    * specialize (IHn H).
      {
      rewrite app_removelast_last with (l:=l) (d:=[]) in H2.
      - assert (H4: sflist g (removelast l)).
          {
          apply IHn.
          intros i H4.
          specialize (H2 i).
          rewrite app_length in H2.
          simpl in H2.
          assert (H20:= H4).
          apply le_trans with (n:=i)(m:=Datatypes.length (removelast l) - 2)(p:=Datatypes.length (removelast l) + 1 - 2) in H4.
          + specialize (H2 H4).
            destruct H2 as [left [right [s [s' [H7 [H8 H9]]]]]].
            exists left, right, s, s'.
            split.
            * assert (H10: i < length (removelast l)).
                {
                omega.
                }
              {
              rewrite app_nth1 in H7.
              - rewrite H7.
                reflexivity.
              - exact H10.
              }
            * {
              split.
              - assert (H10: S i < length (removelast l)).
                  {
                  omega.
                  }
                rewrite app_nth1 in H8.
                + rewrite H8.
                  reflexivity.
                + exact H10.
              - exact H9.
              } 
          + omega.
          }
        specialize (H2 ((S n) - 2)).
        assert (H5: S n - 2 <= Datatypes.length (removelast l ++ [last l []]) - 2).
          {
          rewrite app_length.
          simpl.
          omega.
          }
        specialize (H2 H5).
        destruct H2 as [left [right [s [s' [H6 [H7 H8]]]]]].
        apply sflist_step with (s2:=s)(s3:=s')(left:=left)(right:=right) in H4.
        + assert (H9: nth (S (S n - 2)) (removelast l ++ [last l []]) [] = last l []).
            {
            simpl.
            rewrite app_nth2.
            - assert (H9: S (n - 1) - length (removelast l) = 0).
                {
                omega.
                }
              rewrite H9.
              simpl.
              reflexivity.
            - omega.
            }
          rewrite H9 in H7.
          rewrite <- H7 in H4.
          exact H4.
        + assert (H9: nth (S n - 2) (removelast l ++ [last l []]) [] = last (removelast l) []).
            {
            assert (H10: S n - 2 = length (removelast l) - 1). 
              {
              omega.
              }
            rewrite H10.
            rewrite list_last.
            * reflexivity.
            * {
              destruct l as [|s0 l].
              - simpl in H1.
                apply le_Sn_0 in H1.
                contradiction.
              - apply not_eq_sym.
                apply length_not_zero.
                omega.
              }
            }
          rewrite H9 in H6.
          rewrite H6.
          reflexivity.
        + exact H8.
      - destruct l.
        + simpl in H1.
          apply le_Sn_0 in H1.
          contradiction.
        + apply not_eq_sym. 
          apply nil_cons.
      }
    * 
      specialize (H2 (length l - 2)).
      assert (H4: Datatypes.length l - 2 <= Datatypes.length l - 2).
        {
        omega.
        }
      specialize (H2 H4).
      clear H4.
      destruct H2 as [left [right [s [s' [H6 [H7 H8]]]]]].
      assert (H5: nth (S (Datatypes.length l - 2)) l [] = last l []).
        {
        assert (H11: S (Datatypes.length l - 2) = length l - 1).
          {
          omega.
          }
        rewrite H11.
        rewrite app_removelast_last with (l:=l) (d:=[]).
        - rewrite app_length.
          simpl.
          rewrite app_nth2.
          + assert (H12: (Datatypes.length (removelast l) + 1 - 1 - Datatypes.length (removelast l)=0)).
              {
              omega.
              }
            rewrite H12.
            simpl.
            symmetry.
            apply last_last.
          + omega.
        - apply not_eq_sym.
          apply length_not_zero.
          omega.
        }
      rewrite H5 in H7.
      assert (H9: removelast l = [s ++ inl left :: s']).
        {
        rewrite app_removelast_last with (l:=l)(d:=[]) in H6.
        - rewrite app_nth1 in H6.
          + rewrite app_length in H6.
            simpl in H6.
            assert (H13: length (removelast l) + 1 - 2 = 0).
              {
              omega.
              }
            rewrite H13 in H6.
            assert (H14: length (removelast l) = 1).
              {
              omega. 
              }
            apply list_single in H6.
            * exact H6.
            * exact H14.
          + rewrite app_length.
            simpl. 
            omega.
        - apply not_eq_sym.
          apply length_not_zero.
          omega.
        }
(*      unfold sf in H7.*)
      rewrite H7.
(*      unfold sf in H9.*)
      rewrite H9.
      {
      apply sflist_step with (left:=left).
      - apply sflist_start.
      - simpl.
        reflexivity.
      - exact H8.
      }
  + destruct l.
    * simpl in H1.
      apply le_Sn_0 in H1.
      contradiction.
    * apply not_eq_sym. 
      apply nil_cons.
Qed.

Lemma sflist_rules''':
forall g: cfg _ _,
forall n: nat,
forall l: list sf,
length l = n ->
length l >= 2-> (sflist g l <-> 
                (forall i: nat,
                 i <= (length l)-2 ->
                 exists left: non_terminal,
                 exists right s s': sf,
                 nth i l [] = s++inl left::s' /\
                 nth (S i) l [] = s++right++s' /\
                 rules g left right)).
Proof.
intros g n l H H0.
split.
- generalize g n l H H0.
  apply sflist_rules'.
- generalize g n l H H0.
  apply sflist_rules''.
Qed.

Lemma sflist_rules:
forall g: cfg _ _,
forall l: list sf,
length l >= 2-> (sflist g l <-> 
                (forall i: nat,
                 i <= (length l)-2 ->
                 exists left: non_terminal,
                 exists right s s': sf,
                 nth i l [] = s++inl left::s' /\
                 nth (S i) l [] = s++right++s' /\
                 rules g left right)).
Proof.
intros g l.
apply (@sflist_rules''' g (length l) l).
reflexivity.
Qed.

Lemma not_sflist:
forall g: cfg _ _,
forall l: list sf,
l <> [] ->
~ sflist g ([] :: l).
Proof.
intros g l H1 H2.
assert (H3: length ([] :: l) >=2 \/ length ([] :: l) < 2) by omega.
destruct H3 as [H3 | H3].
- apply sflist_rules with (g:=g) in H3.
  destruct H3 as [H3 _].
  assert (H4: 0 <= Datatypes.length ([] :: l) - 2).
    {
    apply le_0_n.
    }  
  specialize (H3 H2 0 H4).
  destruct H3 as [left [right [s [s' [H5 [H6 H7]]]]]].
  simpl in H5.
  destruct s.
  + simpl in H5.
    inversion H5.
  + inversion H5.
- assert (H4: l = []).
    {
    replace ([] :: l) with ([[]] ++ l) in H3.
    - rewrite app_length in H3.
      simpl in H3.
      apply lt_S_n in H3.
      apply length_zero.
      apply lt_1_eq_0. 
      exact H3.
    - simpl. 
      reflexivity.
    }
  destruct H1.
  exact H4.
Qed.

Lemma sflist_split:
forall g: cfg _ _,
forall l: list sf,
sflist g l ->
length l >= 2 ->
exists s1 s2: sf,
exists l': list sf,
hd [] l = s1 /\
last l [] = s2 /\
l = [s1] ++ l' ++ [s2].
Proof.
intros g l H1 H2. 
assert (H5: length l > 2 \/ length l = 2) by omega.
destruct H5 as [H5 | H5].
- apply (exists_length_gt_2 sf [] l) in H5.
  destruct H5 as [s0 [s3 [l' H6]]].
  exists s0, s3, l'.
  split.
  + rewrite H6. 
    simpl. 
    reflexivity.
  + split. 
    * rewrite H6. 
      rewrite app_assoc. 
      apply last_last.
    * exact H6.
- apply exists_length_eq_2 in H5.
  destruct H5 as [s1 [s2 H6]].
  exists s1, s2, [].
  split. 
  + rewrite H6.
    simpl. 
    reflexivity.
  + split. 
    * rewrite H6. 
      simpl.
      reflexivity.
    * exact H6.
Qed.

Lemma sflist_elim_first:
forall g: cfg _ _,
forall s: sf,
forall l : list sf,
sflist g (s::l) -> sflist g l.
Proof.
intros g s l H.
destruct l as [|s0 l].
- apply sflist_empty.
- assert (LEN: length (s::s0::l) >= 2). 
  { simpl. 
    apply Le.le_n_S.
    apply Le.le_n_S.
    apply Le.le_0_n. }
  apply sflist_rules with (g:=g) in LEN.
  destruct LEN as [H1 H2].
  clear H2.
  specialize (H1 H).
  destruct l as [|s1 l].
  + apply sflist_start.
  + apply sflist_rules.
    assert (LEN1: length (s0::s1::l) >= 2). 
    { simpl. 
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n. }
    exact LEN1.
    intro i.
    specialize (H1 (S i)).
    assert (LEN2: S i <= length (s :: s0 :: s1 :: l) - 2 <->
                  i <= length (s0 :: s1 :: l) - 2).
    { split.
      - intro H2.
        simpl. 
        simpl in H2.
        apply le_S_n in H2.
        rewrite <- Minus.minus_n_O.
        exact H2.
      - intro H2.
        simpl.
        simpl in H2. 
        rewrite <- Minus.minus_n_O in H2.
        apply Le.le_n_S in H2.
        exact H2. }
    repeat rewrite nth_S in H1.
    rewrite LEN2 in H1.
    exact H1.
Qed.

Lemma sflist_elim_last:
forall g: cfg _ _,
forall s: sf,
forall l : list sf,
sflist g (l++[s]) -> sflist g l.
Proof.
intros g s l H.
inversion H.
- symmetry in H1. 
  apply app_eq_nil in H1.
  destruct H1 as [H2 H3].
  subst.
  apply sflist_empty.
- destruct l.
  + apply sflist_empty.
  + inversion H1.
    symmetry in H3. 
    apply app_eq_nil in H3.
    destruct H3 as [H4 H5].
    subst.
    apply sflist_start.
- apply app_inj_tail in H0.
  destruct H0 as [H4 H5].
  subst.
  exact H1.
Qed.

Lemma sflist_tail:
forall g: cfg _ _,
forall l : list sf,
sflist g l -> sflist g (tl l).
Proof.
intros g l H.
destruct l.
- simpl. 
  apply sflist_empty.
- simpl.
  apply sflist_elim_first in H.
  exact H.
Qed.

Lemma sflist_app_r:
forall g: cfg _ _,
forall l1 l2: list sf,
sflist g (l1++l2) -> sflist g l1.
Proof.
intros g l1 l2 H.
destruct l1 as [|s l1]. 
+ apply sflist_empty. 
+ destruct l1 as [|s0 l1]. 
  * apply sflist_start. 
  * assert (LEN: length ((s :: s0 :: l1) ++ l2) >= 2).
    { simpl.
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n. 
    }
    apply sflist_rules with (g:=g) in LEN.
    destruct LEN as [H1 H2].
    clear H2.
    specialize (H1 H). 
    {
    apply sflist_rules. 
    - assert (LEN: length (s :: s0 :: l1) >= 2).
      { simpl.
        apply Le.le_n_S.
        apply Le.le_n_S.
        apply Le.le_0_n. }
      exact LEN.
    - intro i.
      specialize (H1 i).
      intro H3.
      assert (i <= Datatypes.length (s :: s0 :: l1) - 2 -> 
              i <= Datatypes.length ((s :: s0 :: l1) ++ l2) - 2).
      { intro H4.
        assert (length (s :: s0 :: l1) - 2 <= length ((s :: s0 :: l1) ++ l2) - 2).
        { destruct l2.
          - rewrite app_nil_r.
            apply le_n.
          - apply Minus.minus_le_compat_r.
            simpl. 
            apply Le.le_n_S.
            apply Le.le_n_S.
            rewrite app_length.
            apply Plus.le_plus_l. 
        }
        apply Le.le_trans with (m:=Datatypes.length (s :: s0 :: l1) - 2).
        + exact H3.
        + exact H0. 
      }
      specialize (H1 (H0 H3)).
      destruct H1 as [left [right [s1 [s' [H4 [H5 H6]]]]]]. 
      assert (H1: forall l' l'': list sf,
                  forall s' s'': sf,
                  forall i: nat,
                  i <= Datatypes.length (s' :: s'' :: l') - 1 ->
                  nth i (s' :: s'' :: l') [] = nth i ((s' :: s'' :: l')++l'') []).
                  { intros l' l'' s'0 s'' i0 H7.
                    rewrite app_nth1.
                    - reflexivity.
                    - simpl. 
                      simpl in H7. 
                      apply Lt.le_lt_n_Sm in H7.
                      exact H7.
                  }
      exists left, right, s1, s'.
      split. 
      + rewrite H1 with (s':=s)(s'':=s0)(l':=l1)(l'':=l2).
        * exact H4.
        * simpl in H3.
          rewrite <- Minus.minus_n_O in H3. 
          simpl.
          apply le_S in H3.
          exact H3.
      + rewrite H1 with (s':=s)(s'':=s0)(l':=l1)(l'':=l2).
        * { split.
            - exact H5.
            - exact H6. 
          }
        * simpl.
          apply Le.le_n_S.
          simpl in H3.
          rewrite <- Minus.minus_n_O in H3. 
          exact H3.
    }
Qed.

Lemma sflist_app_l:
forall g: cfg _ _,
forall l1 l2: list sf,
sflist g (l1++l2) -> sflist g l2.
Proof.
intros g l1 l2 H.
destruct l2 as [|s l2].
- apply sflist_empty.
- destruct l2 as [|s0 l2].
  + apply sflist_start.
  + assert (LEN: length (l1 ++ s :: s0 :: l2) >= 2).
    { rewrite app_length.
      simpl. 
      rewrite Plus.plus_comm.
      assert (forall i j: nat, S (S i) >= 2 -> S (S i) + j >= 2).
         { intros i j.
           omega.
         }
      apply H0.
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n. 
    }
    apply sflist_rules with (g:=g) in LEN.
    destruct LEN as [H1 H2].
    clear H2.
    specialize (H1 H). 
    apply sflist_rules.
    assert (LEN: length (s :: s0 :: l2) >= 2).
    { simpl.
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n. 
    }
    exact LEN.
    intro i.
    specialize (H1 (i + length l1)).
    intro H3.
    assert (i <= Datatypes.length (s :: s0 :: l2) - 2 -> 
            i <= Datatypes.length (l1 ++ (s :: s0 :: l2)) - 2).
      { intro H4.
        assert (length (s :: s0 :: l2) - 2 <= length (l1 ++ (s :: s0 :: l2)) - 2).
        { destruct l1.
          - rewrite app_nil_l.
            apply le_n.
          - apply Minus.minus_le_compat_r.
            simpl. 
            apply Le.le_n_S.
            rewrite app_length.
            simpl.
            rewrite <- plus_n_Sm.
            apply Le.le_n_S.
            apply Le.le_trans with (m:=S (Datatypes.length l2)).
            + apply Le.le_n_Sn.
            + apply Plus.le_plus_r.
        }
        apply Le.le_trans with (m:= Datatypes.length (s :: s0 :: l2) - 2).
        + exact H3.
        + exact H0.
      }
    assert (H3':=H3).
    apply Plus.plus_le_compat_l with (p:=length l1) in H3.
    rewrite Plus.plus_comm in H3.
    rewrite app_length in H1.
    assert (PLUS_MINUS: forall a b c: nat,
            b >= c -> a + b - c = a + (b - c)).
       { intros a b c.
         omega. 
       }
    rewrite <- PLUS_MINUS in H3. 
    * specialize (H1 H3).
      destruct H1 as [left [right [s1 [s' [H4 [H5 H6]]]]]].
      assert (H1: forall l' l'': list sf,
                  forall s' s'': sf,
                  forall i: nat,
                  i <= Datatypes.length (s' :: s'' :: l'') - 1 ->
                  nth i (s' :: s'' :: l'') [] = nth (i+length l') (l' ++ s' :: s'' :: l'') []).
                  { intros l' l'' s'0 s'' i0 H7.
                    rewrite app_nth2.
                    - rewrite Plus.plus_comm.
                      rewrite Minus.minus_plus.
                      reflexivity. 
                    - apply Plus.le_plus_r.
                  }
      exists left, right, s1, s'. {
      split. 
      - rewrite H1 with (s':=s)(s'':=s0)(l':=l1)(l'':=l2).
        + exact H4.
        + apply le_S in H3'.
          simpl in H3'.
          simpl. 
          rewrite <- Minus.minus_n_O in H3'.
          exact H3'.
      - rewrite H1 with (s':=s)(s'':=s0)(l':=l1)(l'':=l2).
        + split.
          * exact H5.
          * exact H6.
        + simpl.
          apply Le.le_n_S.
          simpl in H3'.
          rewrite <- Minus.minus_n_O in H3'.
          exact H3'. }
    * simpl.
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n.
Qed.

Lemma sflist_app_l_aux:
forall g: cfg _ _,
forall s: sf,
forall l: list sf,
sflist g (s::l) -> sflist g l.
Proof.
intros g s l H.
replace (s :: l) with ([s] ++ l) in H.
- apply sflist_app_l in H.
  exact H.
- simpl. 
  reflexivity.
Qed.

Lemma sflist_app:
forall g: cfg _ _,
forall l1 l2: list sf,
sflist g (l1++l2) -> sflist g l1 /\ sflist g l2.
Proof.
intros g l1 l2 H.
split.
- apply sflist_app_r in H.
  exact H.
- apply sflist_app_l in H.
  exact H.
Qed.

Lemma sflist_cat:
forall g: cfg _ _,
forall l1 l2: list sf,
forall s: sf,
sflist g (l1 ++ [s]) /\
sflist g ([s] ++ l2) ->
sflist g (l1 ++ [s] ++ l2).
Proof.
intros g l1 l2 s [H1 H2].
assert (H3: length (l1 ++ [s] ++ l2) >= 2 \/
            length (l1 ++ [s] ++ l2) < 2).
  {
  omega.
  }
destruct H3 as [H4 | H5].
- (* length (l1 ++ [s] ++ l2) >= 2 *) 
  apply sflist_rules.
  + exact H4.
  + intros i H5.
    assert (H1':= H1).
    apply sflist_app_r in H1.
    assert (H8: length l1 >= 2 \/
                length l1 <  2).
      {
      omega.
      }
    destruct H8 as [H9 | H9].
    * (* length l1 >= 2 *) 
      assert (H9':= H9).
      apply sflist_rules with (g:=g) in H9.
      destruct H9 as [H10 _].
      specialize (H10 H1 i).
      assert (H11: i <= length l1 - 2 \/
                   i >  length l1 - 2).
        {
        omega.
        }
      {
      destruct H11 as [H12 | H12].
      - (* i <= length l1 - 2 *)
        specialize (H10 H12).
        destruct H10 as [left [right [s0 [s' [H20 [H21 H22]]]]]].
        exists left, right, s0, s'.
        split.
        + rewrite app_nth1.
          * exact H20.
          * omega.
        + split.
          * {
            rewrite app_nth1.
            - exact H21.
            - apply le_n_S in H12.
              omega.
            }
          * exact H22.
      - (* i > length l1 - 2 *)
        assert (H13: i >= length l1 \/
                     i < length l1).
          {
          omega.
          }
        destruct H13 as [H14 | H14].
        + (* i >= length l1 *)
          assert (H16: length ([s] ++ l2) >= 2 \/
                       length ([s] ++ l2) <  2).
            {
            omega.
            }
          destruct H16 as [H17 | H17].
          * (* length ([s] ++ l2) >= 2 *)
            apply sflist_rules with (g:=g) in H17.
            destruct H17 as [H17 _].
            specialize (H17 H2).
            specialize (H17 (i-length l1)).
            assert (H18: i - length l1 <= length ([s] ++ l2) - 2).
              {
              rewrite app_length.
              simpl.
              repeat rewrite app_length in H5.
              simpl in H5.
              omega.
              }
            specialize (H17 H18).
            destruct H17 as [left [right [s0 [s' [H20 [H21 H22]]]]]].
            exists left, right, s0, s'.
            {
            split.
            - rewrite app_nth2.
              + exact H20.
              + omega.
            - rewrite app_nth2.
              + split.
                * {
                  rewrite minus_Sn_m in H21.
                  - exact H21.
                  - omega.
                  }
                * exact H22.  
              + omega.
            }
          * (* length ([s] ++ l2) < 2 *)
            assert (H18: l2 = []).
              {
              rewrite app_length in H17.
              simpl in H17. 
              apply lt_S_n in H17.
              apply length_lt_1 in H17.
              exact H17.
              }
            rewrite H18.
            simpl.
            rewrite H18 in H4.
            simpl in H4.
            apply sflist_rules with (g:=g) in H4.
            destruct H4 as [H4 _].
            specialize (H4 H1').
            specialize (H4 i).
            assert (H19: i <= length (l1 ++ [s]) - 2).
              {
              rewrite app_length.
              simpl.
              subst.
              simpl in *.
              rewrite app_length in H5.
              simpl in H5.
              exact H5.
              }
            specialize (H4 H19).
            exact H4.
        + (* i < length l1 *)
          assert (H15: i = length l1 - 1). 
            { 
            omega.
            }
          assert (H16: length (l1 ++ [s]) >= 2 \/
                       length (l1 ++ [s]) <  2).
            {
            omega.
            }
          destruct H16 as [H17 | H17].
          * (* length (l1 ++ [s]) >= 2 *)
            apply sflist_rules with (g:=g) in H17.
            destruct H17 as [H17 _].
            specialize (H17 H1').
            specialize (H17 (length l1 - 1)).
            assert (H18: length l1 - 1 <= length (l1 ++ [s]) - 2).
              {
              rewrite app_length.
              simpl.
              omega.
              }
            specialize (H17 H18).
            destruct H17 as [left [right [s0 [s' [H21 [H22 H23]]]]]].
            exists left, right, s0, s'.
            {
            split.
            - rewrite H15.
              rewrite app_nth1.
              + rewrite app_nth1 in H21.
                * exact H21.
                * omega.
              + omega.
            - split.
              + rewrite H15.
                rewrite app_nth2.
                * {
                  rewrite app_nth1.
                  - rewrite app_nth2 in H22.
                    + exact H22.
                    + omega. 
                  - rewrite minus_Sn_m.
                    + simpl. 
                      omega. 
                    + omega. 
                  }
                * omega. 
              + exact H23. 
            } 
          * (* length (l1 ++ [s]) < 2 *) 
            assert (H18: l1 = []).
              { 
              rewrite app_length in H17.
              simpl in H17.
              rewrite plus_comm in H17.
              rewrite plus_Sn_m in H17.
              rewrite plus_O_n in H17.
              apply lt_S_n in H17.
              apply length_lt_1 in H17.
              exact H17.
              }
            subst.
            simpl in H9'.
            apply le_Sn_0 in H9'.
            contradiction.
      }
    * (* length l1 < 2 *)
      {
      destruct l1 as [|s0 l1].
      - repeat rewrite app_nil_l.
        repeat rewrite app_nil_l in H4.
        apply sflist_rules with (g:=g) in H4.
        destruct H4 as [H4 _].
        specialize (H4 H2 i).
        rewrite app_nil_l in H5.
        specialize (H4 H5).
        exact H4. 
      - assert (H10: l1 = []).
          {
          replace (s0::l1) with ([s0]++l1) in H9.
          + rewrite app_length in H9.
            simpl in H9.
            apply lt_S_n in H9.
            apply length_lt_1 in H9.
            exact H9.
          + simpl.
            reflexivity.
          }
        subst.
        clear H1 H9.
        assert (H7: length ([s0]++[s]) >= 2).
          {
          simpl. 
          auto.
          }
        apply sflist_rules with (g:=g) in H7.
        destruct H7 as [H7 _].
        specialize (H7 H1' 0).
        assert (H8: 0 <= length ([s0] ++ [s]) - 2).
          {
          omega.
          }
        specialize (H7 H8).
        assert (H6: i = 0 \/ i = 1 \/ i >= 2).
          {
          omega.
          }
        destruct H6 as [H6 | H6].
        + rewrite H6.
          exact H7. 
        + destruct H6 as [H6 | H6].
          * rewrite H6.
            assert (H9: length ([s] ++ l2) >= 2 \/
                        length ([s] ++ l2) < 2).
              {
              omega.
              }
            {
            destruct H9 as [H9 | H9].
            - apply sflist_rules with (g:=g) in H9.
              destruct H9 as [H9 _].
              specialize (H9 H2 0).
              assert (H10: 0 <= length ([s] ++ l2) - 2).
                {
                omega.
                }
              specialize (H9 H10).
              destruct H9 as [left [right [s1 [s' [H20 [H21 H22]]]]]].
              exists left, right, s1, s'.
              split. 
              + rewrite app_nth2.
                * simpl.
                  simpl in H20.
                  exact H20.
                * simpl.
                  auto.
              + split.
                * {
                  rewrite app_nth2.
                  - simpl.
                    simpl in H21.
                    exact H21.
                  - simpl. 
                    auto.
                  }
                * exact H22.
            - assert (H10: l2 = []).
                {
                rewrite app_length in H9.
                simpl in H9.
                apply lt_S_n in H9.
                apply length_lt_1 in H9.
                exact H9.
                }
              subst.
              simpl in H5.
              apply le_Sn_0 in H5.
              contradiction.
            }
          * apply sflist_app_l in H2.
            assert (H9: length l2 >= 2 \/
                        length l2 < 2).
              {
              omega.
              }
            {
            destruct H9 as [H9 | H9].
            - apply sflist_rules with (g:=g) in H9.
              destruct H9 as [H9 _].
              specialize (H9 H2 (i-2)).
              assert (H10: i - 2 <= length l2 - 2).
                {
                repeat rewrite app_length in H5.
                simpl in H5.
                omega.
                }
              specialize (H9 H10).
              destruct H9 as [left [right [s1 [s' [H20 [H21 H22]]]]]].
              exists left, right, s1, s'.
              split.
              + rewrite app_assoc.
                rewrite app_nth2.
                * simpl.
                  exact H20.
                * simpl. 
                  exact H6.
              + split.
                * rewrite app_assoc.
                  {
                  rewrite app_nth2.
                  - rewrite minus_Sn_m in H21.
                    + replace (length ([s0] ++ [s])) with 2.
                      * exact H21.
                      * simpl.
                        reflexivity.
                    + exact H6.
                  - simpl.
                    omega.
                  }
                * exact H22.
            - destruct l2 as [|s1 l2].
              + simpl in H9.
                repeat rewrite app_length in H5.
                simpl in H5.
                omega.
              + assert (H10: l2 = []).
                  {
                  replace (s1::l2) with ([s1]++l2) in H9.
                  - rewrite app_length in H9.
                    simpl in H9.
                    apply lt_S_n in H9.
                    apply length_lt_1 in H9.
                    exact H9.
                  - simpl.
                    reflexivity.
                  }
                subst.
                repeat rewrite app_length in H5.
                simpl in H5.
                omega.
            }
      }
- (* length (l1 ++ [s] ++ l2) < 2) *)
  rewrite app_length in H5.
  simpl in H5.
  rewrite <- plus_n_Sm in H5.
  apply lt_S_n in H5.
  assert (H6: length l1 + length l2 = 0).
    {
    omega.
    }
  assert (H7: length l1 = 0 /\ length l2 = 0).
    {
    omega.
    }
  destruct H7 as [H8 H9].
  apply length_zero in H8.
  apply length_zero in H9.
  subst.
  simpl.
  apply sflist_start.
Qed.

Lemma sflist_cat_rule:
forall g: cfg _ _,
forall l1 l2: list sf,
forall left: non_terminal,
forall s s' right: sf,
sflist g (l1 ++ [s++inl left::s']) /\
sflist g ([s++right++s']++l2) /\
rules g left right ->
sflist g (l1 ++ [s++inl left::s']++[s++right++s']++l2).
Proof.
intros g l1 l2 left s s' right [H1 [H2 H3]].
apply sflist_step with (s2:=s) (s3:=s') (left:=left) (right:=right) in H1.
- rewrite app_assoc.
  apply sflist_cat.
  split.
  + exact H1.
  + exact H2.
- rewrite last_last. 
  reflexivity.
- exact H3.
Qed.

Lemma derives_sflist:
forall g: cfg _ _,
forall s1 s2: sf,
derives g s1 s2 <->
exists l: list sf,
sflist g l /\
hd [] l = s1 /\
last l [] = s2.
Proof.
intros g s1 s2.
split.
- intro H.
  induction H.
  + exists [s].
    split.
    * apply sflist_start.
    * { split.
        - simpl.
          reflexivity.
        - simpl.
          reflexivity. } 
  + destruct IHderives as [l [H1 [H2 H3]]].
    exists (l++[s2 ++ right ++ s3]).
    split.
    * { apply sflist_step with (left:=left).
        - exact H1.
        - exact H3.
        - exact H0. }
    * { split.
        - subst.
          destruct l as [|s l].
          + simpl.
            destruct s2.
            * inversion H3. 
            * inversion H3.
          + simpl.
            reflexivity.
        - apply last_last. }
- intro H.
  destruct H as [l [H1 [H2 H3]]].
  revert H3.
  generalize s2.
  induction H1.
  + simpl in H2. 
    intros l H1.
    simpl in H1.
    subst.
    apply derives_refl.
  + intros l H. simpl in H2. rewrite <- H2. simpl in H. rewrite H. apply derives_refl.
  + intros l0 H3.
    rewrite <- H3.
    rewrite last_last.
    apply derives_step with (left:=left).
    * apply IHsflist.   
      destruct l.
      simpl in H.
      destruct s0.
      inversion H.
      inversion H. 
      simpl in H2.
      simpl.
      exact H2.
      exact H.
    * exact H0.
Qed.   

Lemma derives_sflist_not_nil:
forall g: cfg _ _,
forall s1 s2: sf,
derives g s1 s2 ->
exists l: list sf,
sflist g l /\
hd [] l = s1 /\
last l [] = s2 /\
l <> [].
Proof.
intros g s1 s2.
intro H.
induction H.
- exists [s].
  split.
  + apply sflist_start.
  + split.
    * simpl.
      reflexivity.
    * simpl.
      {
      split.
      - reflexivity.
      - apply not_eq_sym. 
        apply nil_cons.
      } 
- destruct IHderives as [l [H1 [H2 H3]]].
  exists (l++[s2 ++ right ++ s3]).
  split.
  + apply sflist_step with (left:=left).
    * exact H1.
    * destruct H3 as [H4 H5]. 
      exact H4.
    * exact H0. 
  + split.
    * subst.
      {
      destruct l.
      - simpl.
        destruct s2.
        + destruct H3 as [H4 H5]. 
          destruct H5.
          reflexivity. 
        + destruct H3 as [H4 H5].
          destruct H5.
          reflexivity.
      - simpl. 
        reflexivity.
      }
    * {
      split.
      - apply last_last.
      - destruct l. 
        + simpl. 
          apply not_eq_sym. 
          apply nil_cons.
        + apply not_eq_sym. 
          apply nil_cons.
      }
Qed.

Lemma sflist_equiv_sflist2:
forall g: cfg _ _,
forall l: list sf,
sflist g l -> sflist2 g l.
Proof.
intros g l H.
induction H.
- apply sflist2_empty.
- apply sflist2_start.
- apply sflist2_step with (s1:=s2 ++ inl left :: s3).
  + destruct l.  
    * simpl in H0.
      {
      destruct s2.
      - inversion H0.
      - inversion H0.
      }
    * apply not_eq_sym. 
      apply nil_cons. 
  + exact IHsflist.
  + exact H0.
  + apply derives_rule.
    exact H1.
Qed.

Lemma sflist2_equiv_sflist:
forall g: cfg _ _,
forall l2: list sf,
sflist2 g l2 -> 
exists l: list sf,
sflist g l /\
hd [] l = hd [] l2 /\
last l [] = last l2 [].
Proof.
intros g l2 H.
induction H as [ | s | l s1 s2 H0 H1 IH H2 H3].
- exists [].
  split.
  + apply sflist_empty.
  + simpl. 
    auto.
- exists [s].
  split.
  + apply sflist_start.
  + simpl. 
    auto.
- destruct IH as [l0 [H4 [H5 H6]]].
  apply derives_sflist_not_nil in H3.
  destruct H3 as [l1 [H7 [H8 [H9 H10]]]].
  assert (H30: length l0 > 1 \/ length l0 <= 1) by omega.
  destruct H30 as [H30 | H30].
  + (* length l0 > 1 *) 
    rewrite app_removelast_last with (d:=[]) in H4.
    * assert (H20: sflist g (removelast l0 ++ l1)).
        {
        destruct l1. 
        - apply sflist_app_r in H4. 
          rewrite app_nil_r.
          exact H4.
        - simpl in H8. 
          rewrite H8. 
          apply sflist_cat.
          split. 
          + rewrite H2 in H6. 
            rewrite <- H6.
            exact H4.
          + rewrite H8 in H7.
            exact H7.
        }
      exists (removelast l0 ++ l1).
      {
      split.
      - exact H20.
      - split.
        + assert (H40: length l > 0).
            {
            apply not_nil in H0.
            omega.
            }
          destruct l as [|s0 l].
          * simpl in H40.
            apply lt_n_0 in H40. 
            contradiction.
          * simpl.
            simpl in H5.
            rewrite <- H5.
            {
            destruct l0 as [|s l0].
            - simpl in H30.
              apply lt_n_0 in H30. 
              contradiction. 
            - rewrite hd_removelast.
              + simpl.  
                reflexivity.
              + simpl in H30.
                apply gt_S_n in H30.
                apply length_not_zero in H30.
                apply not_eq_sym. 
                exact H30. 
            }
        + rewrite app_removelast_last with (d:=[]) (l:=l1).
          * rewrite H9.
            rewrite last_last.
            rewrite app_assoc.
            rewrite last_last. 
            reflexivity.
          * exact H10.
      }
    * apply not_eq_sym. 
      apply length_not_zero.
      apply gt_any_gt_0 with (j:=1).
      exact H30. 
  + assert (H50: length l0 = 1 \/ length l0 = 0) by omega.
    destruct H50 as [H50 | H50].
    * (* length l0 = 1 *)
      exists l1.
      {
      split. 
      - exact H7.
      - split.
        + rewrite H8.
          destruct l.
          * destruct H0.
            reflexivity.
          * simpl.
            {
            destruct l0 as [|s0 l0].
            - simpl in H5.
              subst.
              rewrite <- H2.
              rewrite <- H6.
              simpl. 
              reflexivity.              
            - subst.
              rewrite <- H6.
              destruct l0 as [|s1 l0].
              + simpl in H5. 
                simpl. 
                exact H5.
              + replace (s0 :: s1 :: l0) with ([s0] ++ [s1] ++ l0) in H50.
                * repeat rewrite app_length in H50. 
                  simpl in H50.
                  apply eq_add_S in H50.
                  symmetry in H50.
                  apply O_S in H50.
                  contradiction. 
                * simpl. 
                  reflexivity.
            }
        + rewrite <- H9.
          rewrite last_last.
          reflexivity.
        }
    * (* length l0 = 0 *)
      exists l1. 
      {
      split. 
      - exact H7.
      - split.
        + rewrite H8.
          destruct l as [|s l].
          * destruct H0.
            reflexivity.
          * simpl.
            {
            destruct l0 as [|s0 l0].
            - simpl in H5.
              subst.
              rewrite <- H2.
              rewrite <- H6.
              simpl. 
              reflexivity.
            - replace (s0 :: l0) with ([s0] ++ l0) in H50.
              + rewrite app_length in H50.
                simpl in H50.
                symmetry in H50.
                apply O_S in H50.
                contradiction.
              + simpl. 
                reflexivity.
            }
        + rewrite <- H9.
          rewrite last_last.
          reflexivity.
        }
Qed.

Lemma exists_rule:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sentence,
derives g [inl n] (map term_lift s) ->
rules g n (map term_lift s) \/
exists right: sf, rules g n right /\ derives g right (map term_lift s).
Proof.
intros g n s H.
apply derives_sflist in H.
destruct H as [l [H1 [H2 H3]]].
assert (H4: length l = 2 \/ length l > 2).
  {
  assert (GE2: length l >= 2).
    {
    destruct l as [|s0 l].
    - simpl in H2.
      inversion H2.
    - simpl in H2.
      assert (NE: l <> []).
        {
        subst.
        simpl in H3.
        destruct l; [|discriminate].
        destruct s; inversion H3.
        }
      apply exists_last in NE.
      destruct NE as [l' [a0 LAST]].
      rewrite LAST.
      replace (s0 :: l' ++ [a0]) with ([s0] ++ l' ++ [a0]).
      + repeat rewrite app_length.
        simpl.
        omega.
      + simpl. 
        reflexivity.
    }
  omega.
  }
inversion H1.
- subst.
  simpl in H2.
  inversion H2.
- clear H s0.
  destruct H4.
  + assert (H5: length l >= 2).
      {
      omega.
      }
    apply sflist_rules with (g:=g) in H5.
    destruct H5 as [H6 H7].
    clear H7.
    specialize (H6 H1).
    specialize (H6 0).
    assert (H7: 0 <= Datatypes.length l - 2).
      {
      omega.
      }
    specialize (H6 H7).
    clear H7.
    destruct H6 as [left [right [s0 [s' [H7 [H8 H9]]]]]].
    left.
    assert (H20: [inl n] = s0 ++ inl left :: s').
      {
      rewrite <- H2.
      rewrite <- H7.
      apply hd_nth0.
      }
    assert (H21: map term_lift s = s0 ++ right ++ s').
      {
      rewrite <- H3.
      rewrite <- H8.
      apply last_nth1.
      exact H.
      }
    destruct s0.
    * simpl in H20.
      inversion H20.
      rewrite <- H5 in H21.
      rewrite app_nil_l in H21.
      rewrite app_nil_r in H21.
      rewrite H21.
      exact H9.
    * inversion H20.
      {
      destruct s1.
      - simpl in H5. 
        inversion H5.
      - inversion H5.
      }
  + assert (H5: length l >= 2).
      {
      omega.
      }
    apply sflist_rules with (g:=g) in H5.
    destruct H5 as [H6 H7].
    clear H7.
    specialize (H6 H1).
    specialize (H6 0).
    assert (H7: 0 <= Datatypes.length l - 2).
      {
      omega.
      }
    specialize (H6 H7).
    clear H7.
    destruct H6 as [left [right [s0 [s' [H7 [H8 H9]]]]]].
    assert (H10: [inl n] = (s0 ++ inl left :: s')).
      {
      rewrite <- H2.
      rewrite <- H7.
      apply hd_nth0.
      }
    destruct s0.
    * simpl in H10.
      inversion H10.
      rewrite <- H4.
      right.
      rewrite <- H4 in H9.
      exists right.
      {
      split.
      - exact H9.
      - rewrite <- H5 in H8.
        rewrite app_nil_l in H8.
        rewrite app_nil_r in H8.
        apply derives_sflist.
        exists (tl l).
        split.
        + apply sflist_tail.
          exact H1.
        + split.
          * assert (H11: hd [] (tl l) = right).
              {
              rewrite <- H8.
              apply hd_tl_nth1.
              exact H.
              }
            exact H11.
          * assert (H12: last (tl l) [] = map term_lift s).
              {
              rewrite <- H3.
              apply last_tl_last.
              exact H.
              }
            exact H12.
      }
    * inversion H10.
      {
      destruct s1.
      - inversion H5.
      - inversion H5.
      }
- destruct H4.
  + assert (H5': length l >= 2).
      {
      omega.
      }
    apply sflist_rules with (g:=g) in H5'.
    destruct H5' as [H6' H7'].
    clear H7'.
    specialize (H6' H1).
    specialize (H6' 0).
    assert (H7: 0 <= Datatypes.length l - 2).
      {
      omega.
      }
    specialize (H6' H7).
    clear H7.
    destruct H6' as [left' [right' [s0 [s' [H7 [H8 H9]]]]]].
    left.
    assert (H20: [inl n] = s0 ++ inl left' :: s').
      {
      rewrite <- H2.
      rewrite <- H7.
      apply hd_nth0.
      }
    assert (H21: map term_lift s = s0 ++ right' ++ s').
      {
      rewrite <- H3.
      rewrite <- H8.
      apply last_nth1.
      exact H4.
      }
    destruct s0.
    * simpl in H20.
      inversion H20.
      rewrite <- H12 in H21.
      rewrite app_nil_l in H21.
      rewrite app_nil_r in H21.
      rewrite H21.
      exact H9.
    * inversion H20.
      {
      destruct s1.
      - simpl in H12. 
        inversion H12.
      - inversion H12.
      }
  + assert (H5': length l >= 2).
      {
      omega.
      }
    apply sflist_rules with (g:=g) in H5'.
    destruct H5' as [H6' H7'].
    clear H7'.
    specialize (H6' H1).
    specialize (H6' 0).
    assert (H7': 0 <= Datatypes.length l - 2).
      {
      omega.
      }
    specialize (H6' H7').
    clear H7'.
    destruct H6' as [left' [right' [s0' [s'' [H7' [H8' H9']]]]]].
    assert (H10': [inl n] = (s0' ++ inl left' :: s'')).
      {
      rewrite <- H2.
      rewrite <- H7'.
      apply hd_nth0.
      }
    destruct s0'.
    * simpl in H10'.
      inversion H10'.
      rewrite <- H8.
      right.
      rewrite <- H8 in H9'.
      exists right'.
      {
      split.
      - exact H9'.
      - rewrite <- H9 in H8'.
        rewrite app_nil_l in H8'.
        rewrite app_nil_r in H8'.
        apply derives_sflist.
        exists (tl l).
        split.
        + apply sflist_tail.
          exact H1.
        + split.
          * assert (H11': hd [] (tl l) = right').
              {
              rewrite <- H8'.
              apply hd_tl_nth1.
              exact H4.
              }
            exact H11'.
          * assert (H12': last (tl l) [] = map term_lift s).
              {
              rewrite <- H3.
              apply last_tl_last.
              exact H4.
              }
            exact H12'.
      }
    * inversion H10'.
      {
      destruct s0'.
      - inversion H9.
      - inversion H9.
      }
Qed.

Lemma exists_rule'_aux:
forall g: cfg _ _,
forall s: sf,
forall n: non_terminal,
forall c: non_terminal + terminal,
derives g [inl n] s ->
In c s ->
s = [inl n] \/
exists left: non_terminal, 
exists right: sf, 
rules g left right /\ In c right.
Proof.
intros g s n c H1 H2.
remember [inl n] as s0.
induction H1.
- left.
  reflexivity.
- subst.
  specialize (IHderives eq_refl).
  repeat rewrite in_app_iff in H2.
  destruct H2 as [H2 | [H2 | H2]].
  + assert (H3: In c (s2 ++ inl left :: s3)).
      {
      repeat rewrite in_app_iff.
      left.
      exact H2.
      }
    specialize (IHderives H3).
    destruct IHderives as [IHderives | IHderives].
    * {
      destruct s2.
      - simpl in H2.
        contradiction.
      - inversion IHderives.
        destruct s2.
        + inversion H5.
        + inversion H5.
      }
    * right.
      exact IHderives.
  + right.
    exists left, right.
    split.
    * exact H.
    * exact H2.
  + assert (H3: In c (s2 ++ inl left :: s3)).
      {
      repeat rewrite in_app_iff.
      right.
      simpl.
      right.
      exact H2.
      }
    specialize (IHderives H3).
    destruct IHderives as [IHderives | IHderives].
    * {
      destruct s3.
      - simpl in H2.
        contradiction.
      - inversion IHderives.
        destruct s2.
        + inversion H4.
        + inversion H4.
          destruct s2.
          * inversion H6.
          * inversion H6.
      }
    * right.
      exact IHderives.
Qed.

Lemma exists_rule':
forall g: cfg _ _,
forall s1 s2: sf,
forall n: non_terminal,
forall s: non_terminal + terminal,
derives g [inl n] (s1 ++ s :: s2) -> 
s = (inl n) /\ s1 = [] /\ s2 = [] \/
exists left: non_terminal,
exists right: sf,
rules g left right /\ In s right.
Proof.
intros g s1 s2 n s H.
apply exists_rule'_aux with (c:=s) in H.
- destruct H as [H | H].
  + left.
    split.
    * {
      destruct s1.
      - inversion H.
        reflexivity.
      - inversion H.
        destruct s1.
        + inversion H2.
        + inversion H2.
      }
    * {
      split.
      - destruct s1.
        + reflexivity.
        + inversion H.
          subst.
          destruct s1.
          * inversion H2.
          * inversion H2.
      - destruct s1.
        + inversion H.
          reflexivity.
        + inversion H.
          destruct s1.
          * subst.
            rewrite H2.
            inversion H.
          * rewrite H2.
            inversion H2.
      }
  + destruct H as [left [right [H2 H3]]].
    right.
    exists left, right.
    split.
    * exact H2.
    * exact H3.
- apply in_app_iff.
  right.
  replace (s :: s2) with ([s] ++ s2).
  + apply in_app_iff.
    left.
    simpl.
    left.
    reflexivity.
  + simpl.
    reflexivity.
Qed.

Lemma exists_rule''':
forall g: cfg _ _,
forall s1 s2: sf,
derives g s1 s2 -> 
s1 = s2 \/
exists s': sf,
exists s'': sf,
exists left: non_terminal,
exists right: sf,
s1 = s' ++ [inl left] ++ s'' /\
rules g left right /\
derives g (s' ++ right ++ s'') s2.
Proof.
intros g s1 s2.
rewrite derives_equiv_derives2.
intros H.
inversion H.
- left.
  reflexivity.
- right.
  exists s0, s3, left, right.
  split.
  + reflexivity.
  + split.
    * exact H1.
    * rewrite derives_equiv_derives2.
      exact H0.  
Qed.

Lemma g_equiv_sym:
forall g1: cfg non_terminal1 terminal,
forall g2: cfg non_terminal2 terminal,
g_equiv g1 g2 -> g_equiv g2 g1.
Proof.
unfold g_equiv.
intros g1 g2 H.
intro s.
specialize (H s).
destruct H as [H1 H2].
split.
- exact H2.
- exact H1.
Qed.

Lemma g_equiv_refl:
forall g: cfg non_terminal terminal,
g_equiv g g.
Proof.
intros g.
unfold g_equiv.
intros s.
split.
- intros H.
  exact H.
- intros H.
  exact H.
Qed.

Lemma exists_rule_derives3_aux:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sentence,
derives3_aux g [inl n] s ->
rules g n (map term_lift s) \/
exists right: sf, rules g n right /\ derives3_aux g right s.
Proof.
intros g n s.
rewrite <- derives_equiv_derives3_aux.
intros H.
apply exists_rule in H.
destruct H as [H | H].
- left. 
  exact H.
- right. 
  destruct H as [right [H1 H2]].
  exists right.
  split. 
  + exact H1.
  + rewrite <- derives_equiv_derives3_aux.
    exact H2. 
Qed.

Lemma exists_rule_derives3:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sentence,
derives3 g n s ->
rules g n (map term_lift s) \/
exists right: sf, rules g n right /\ derives3_aux g right s.
Proof.
intros g n s.
rewrite <- derives_equiv_derives3.
intros H.
apply exists_rule in H.
destruct H as [H | H].
- left. 
  exact H.
- right. 
  destruct H as [right [H1 H2]].
  exists right.
  split. 
  + exact H1.
  + rewrite <- derives_equiv_derives3_aux.
    exact H2. 
Qed.

Lemma nt_not_t:
forall l1 l2: sf,
forall n: non_terminal,
forall s: sentence,
~ l1 ++ inl n :: l2 = map term_lift s.
Proof.
intros l1 l2 n s H.
apply map_expand in H.
destruct H as [s1' [s2' [H1 [H2 H3]]]].
destruct s2'.
+ simpl in H3.
  inversion H3.
+ simpl in H3.
  inversion H3.
Qed.

Lemma not_derives:
forall g: cfg _ _,
forall s: sf,
s <> [] ->
~ derives g [] s.
Proof.
intros g s H1 H2.
inversion H2.
- destruct s. 
  + destruct H1. 
    reflexivity. 
  + inversion H0.
- rewrite derives_equiv_derives2 in H.
  inversion H.
  + destruct s2. 
    * inversion H7.
    * inversion H7.
  + destruct s0. 
    * inversion H5.
    * inversion H5.
Qed.

Lemma derives_not_empty:
forall g: cfg _ _,
forall s1 s2: sf,
derives g s1 s2 ->
s2 <> [] ->
s1 <> [].
Proof.
intros g s1 s2 H1 H2.
inversion H1.
- exact H2.
- apply exists_rule''' in H.
  destruct H as [H | H].
  + destruct s3.
    * simpl in H.
      rewrite H.
      apply not_eq_sym.
      apply nil_cons.
    * {
      destruct s1.
      - inversion H.
      - apply not_eq_sym.
        apply nil_cons.
      }
  + destruct H as [s' [s'' [left0 [right0 [H5 [H6 H7]]]]]].
    destruct s'.
    * simpl in H5.
      rewrite H5.
      apply not_eq_sym.
      apply nil_cons.
    * rewrite H5.
      apply not_eq_sym.
      apply nil_cons.
Qed.

Lemma sudkamp_315_v1:
forall g: cfg _ _,
forall v w: sf,
forall n: nat,
derives6 g n v w ->
forall A: non_terminal,
In (inl A) v ->
exists p: sf,
exists t: nat,
(derives6 g t [inl A] p) 
/\
(exists v1 v2: sf,
 v = v1 ++ [inl A] ++ v2) 
/\
(exists w1 w2: sf,
 w = w1 ++ p ++ w2).
Proof.
intros g v w n H1 A H2.
assert (H3: exists n: nat, derives6 g n v w).
  {
  exists n.
  exact H1.
  }
rewrite <- derives_equiv_derives6 in H3.
apply derives_nt_sf with (n:=A) in H3.
- destruct H3 as [s1' [s1'' [s2' [s2'' [beta [H4 [H5 H6]]]]]]].
  rewrite derives_equiv_derives4 in H6.
  rewrite derives4_equiv_derives5 in H6.
  destruct H6 as [n0 H7].
  rewrite derives5_equiv_derives6 in H7.
  exists beta, n0.
  split.
  + exact H7.
  + split.
    * exists s1', s1''.
      exact H4.
    * exists s2', s2''.
      exact H5.
- exact H2.  
Qed.

Lemma sudkamp_315_v1':
forall g: cfg _ _,
forall v w: sf,
forall n: nat,
derives6 g n v w ->
forall A: non_terminal,
In (inl A) v ->
exists p: sf,
(derives g [inl A] p) 
/\
(exists v1 v2: sf,
 v = v1 ++ [inl A] ++ v2) 
/\
(exists w1 w2: sf,
 w = w1 ++ p ++ w2).
Proof.
intros g v w n H1 A H2.
assert (H3: exists n: nat, derives6 g n v w).
  {
  exists n.
  exact H1.
  }
rewrite <- derives_equiv_derives6 in H3.
apply derives_nt_sf with (n:=A) in H3.
- destruct H3 as [s1' [s1'' [s2' [s2'' [beta [H4 [H5 H6]]]]]]].
  exists beta.
  split.
  + exact H6.
  + split.
    * exists s1', s1''.
      exact H4.
    * exists s2', s2''.
      exact H5.
- exact H2.  
Qed.

Lemma not_nt_in_sentence:
forall n: non_terminal,
forall s1 s2: sf,
forall s: sentence,
~ (s1 ++ [inl n] ++ s2) = map term_lift s.
Proof.
intros n s1 s2 s H.
apply map_expand in H.
destruct H as [s1' [s2' [H1 [H2 H3]]]].
symmetry in H3. 
apply map_expand in H3.
destruct H3 as [s1'0 [s2'0 [H4 [H5 H6]]]].
destruct s1'0.
- simpl in H5.
  inversion H5.
- simpl in H5.
  inversion H5.
Qed.

Lemma derives_t_left_v1:
forall g: cfg _ _,
forall t: terminal,
forall s: sf,
s <> [inr t] ->
~ derives g [inr t] s.
Proof.
intros g t s H1 H2.
rewrite derives_equiv_derives2 in H2.
inversion H2.
- destruct H1. 
  symmetry. 
  exact H0.
- destruct s1.
  + inversion H.
  + inversion H.
    apply app_eq_nil in H7.
    destruct H7 as [_ H7].
    inversion H7. 
Qed.

Lemma derives_t_left_v2:
forall g: cfg _ _,
forall t: terminal,
forall s: sf,
derives g [inr t] s -> s = [inr t].
Proof.
intros g t s H.
rewrite derives_equiv_derives2 in H.
inversion H.
- reflexivity. 
- destruct s1.
  + inversion H0.
  + inversion H0.
    apply app_eq_nil in H6.
    destruct H6 as [_ H6].
    inversion H6. 
Qed.

Lemma derives6_t_left:
forall g: cfg _ _,
forall n: nat,
forall t: terminal,
forall s: sf,
derives6 g n [inr t] s -> s = [inr t].
Proof.
intros g n t s H.
assert (H1: exists n, derives6 g n [inr t] s).
  {
  exists n.
  exact H.
  }
rewrite <- derives_equiv_derives6 in H1.
rewrite derives_equiv_derives2 in H1.
inversion H1.
- reflexivity. 
- destruct s1.
  + inversion H0.
  + inversion H0.
    apply app_eq_nil in H7.
    destruct H7 as [_ H7].
    inversion H7. 
Qed.

Lemma derives6_t_left_n:
forall g: cfg _ _,
forall n: nat,
forall t: terminal,
forall s: sf,
derives6 g n [inr t] s -> n = 0.
Proof.
intros g n t s H.
assert (H':= H).
apply derives6_t_left in H.
subst.
inversion H'.
- reflexivity.
- apply app_eq_unit in H.
  destruct H as [H | H].
  + destruct H as [_ H].
    inversion H.
  + destruct H as [_ H].
    inversion H.
Qed.

Lemma derives_empty:
forall g: cfg _ _,
forall s: sf,
derives g [] s -> s = [].
Proof.
intros g s H.
inversion H.
- reflexivity.
- apply not_derives in H0.
  + contradiction.
  + apply not_eq_sym.
  apply app_cons_not_nil.
Qed.

Lemma derives_sentence_left:
forall g: cfg _ _,
forall s1: sentence,
forall s2: sf,
derives g (map term_lift s1) s2 -> s2 = map term_lift s1.
Proof.
intros g s1 s2 H.
rewrite derives_equiv_derives2 in H.
inversion H.
- reflexivity.
- apply map_expand in  H0.
  destruct H0 as [_ [S2' [_ [_ H4]]]].
  symmetry in H4.
  replace (inl left :: s3) with ([inl left] ++ s3) in H4.
  + apply map_expand in H4.
    destruct H4 as [s1' [_  [_ [H5 _]]]].
    destruct s1'.
    * inversion H5.
    * simpl in H5.
      inversion H5.
  + simpl. 
    reflexivity.
Qed.

Lemma derives6_sentence_left:
forall g: cfg _ _,
forall n: nat,
forall s1: sentence,
forall s2: sf,
derives6 g n (map term_lift s1) s2 -> s2 = map term_lift s1.
Proof.
intros g n s1 s2 H.
inversion H.
- reflexivity.
- replace (s0 ++ inl left :: s3) with (s0 ++ [inl left] ++ s3) in H0. 
  + apply not_nt_in_sentence in H0.
    contradiction.
  + simpl. 
    reflexivity.
Qed.

Lemma derives_t_nt:
forall g: cfg _ _,
forall t: terminal,
forall n: non_terminal,
forall s1 s2: sf,
~ derives g ((inr t) :: s1) ((inl n) :: s2).
Proof.
intros g t n s1 s2 H.
replace (inr t :: s1) with ([inr t] ++ s1) in H.
- apply derives_split in H.
  destruct H as [s1' [s2' [H1 [H2 _]]]].
  destruct s1'.
  + apply derives_t_left_v2 in H2.
    inversion H2.
  + apply derives_t_left_v2 in H2.
    rewrite H2 in H1.
    inversion H1.
- simpl. 
  reflexivity.
Qed.

Lemma derives_t_t:
forall g: cfg _ _,
forall t: terminal,
forall s1 s2: sf,
derives g ((inr t) :: s1) ((inr t) :: s2) -> derives g s1 s2.
Proof.
intros g t s1 s2 H.
replace (inr t :: s1) with ([inr t] ++ s1) in H.
- apply derives_split in H.
  destruct H as [s1' [s2' [H1 [H2 H3]]]].
  apply derives_t_left_v2 in H2.
  subst.
  inversion H1.
  exact H3.
- simpl. 
  reflexivity.
Qed.

Lemma derives6_t_t:
forall g: cfg _ _,
forall n: nat,
forall t: terminal,
forall s1 s2: sf,
derives6 g n ((inr t) :: s1) ((inr t) :: s2) -> derives6 g n s1 s2.
Proof.
intros g n t s1 s2 H.
replace (inr t :: s1) with ([inr t] ++ s1) in H.
- apply derives6_split in H.
  destruct H as [s1' [s2' [n1 [n2 [H1 [H2 [H3 H4]]]]]]].
  assert (H3':= H3).
  apply derives6_t_left in H3.
  subst.
  apply derives6_t_left_n in H3'.
  inversion H1.
  subst. 
  rewrite plus_O_n. 
  exact H4.
- simpl. 
  reflexivity.
Qed.

Lemma derives_tl_tl:
forall g: cfg _ _,
forall s: sentence,
forall s1 s2: sf,
derives g ((map term_lift s) ++ s1) ((map term_lift s) ++ s2) -> derives g s1 s2.
Proof.
intros g s s1 s2 H.
apply derives_split in H.
destruct H as [s1' [s2' [H1 [H2 H3]]]].
apply derives_sentence_left in H2.
rewrite H2 in H1.
apply app_inv_head in H1.
rewrite <- H1 in H3.
exact H3.
Qed.

Lemma derives6_tl_tl:
forall g: cfg _ _,
forall n: nat,
forall s: sentence,
forall s1 s2: sf,
derives6 g n ((map term_lift s) ++ s1) ((map term_lift s) ++ s2) -> derives6 g n s1 s2.
Proof.
intros g n s s1 s2 H.
induction s.
- simpl in H.
  exact H.
- simpl in H. 
  apply derives6_t_t in H.
  specialize (IHs H).
  exact IHs.
Qed.

Lemma derives_t_symbol_left:
forall g: cfg _ _,
forall s1 s2: sf,
forall t: terminal,
derives g (inr t :: s1) s2 ->
exists s2': sf, 
s2 = (inr t) :: s2'.
Proof.
intros g s1 s2 t H1.
replace (inr t :: s1) with ([inr t] ++ s1) in H1.
- apply derives_split in H1.
  destruct H1 as [s1' [s2' [H2 [H3 H4]]]].
  exists s2'.
  apply derives_t_left_v2 in H3.
  rewrite H3 in H2.
  simpl in H2.
  exact H2.
- simpl. 
  reflexivity.
Qed.

Lemma derives_t_list_left:
forall g: cfg _ _,
forall s1 s2: sf,
forall s: sentence,
derives g ((map term_lift s) ++ s1) s2 ->
exists s2': sf,
s2 = ((map term_lift s) ++ s2').
Proof.
intros g s1 s2 s H.
apply derives_split in H.
destruct H as [s1' [s2' [H1 [H2 H3]]]].
apply derives_sentence_left in H2.
rewrite H2 in H1.
exists s2'.
exact H1.
Qed.

Lemma derives6_t_list_left:
forall g: cfg _ _,
forall n: nat,
forall s1 s2: sf,
forall s: sentence,
derives6 g n ((map term_lift s) ++ s1) s2 ->
exists s2': sf,
s2 = ((map term_lift s) ++ s2').
Proof.
intros g n s1 s2 s H.
assert (H1: exists n: nat, derives6 g n (map term_lift s ++ s1) s2).
  {
  exists n.
  exact H.
  }
rewrite <- derives_equiv_derives6 in H1.
apply derives_split in H1.
destruct H1 as [s1' [s2' [H2 [H3 H4]]]].
apply derives_sentence_left in H3.
rewrite H3 in H2.
exists s2'.
exact H2.
Qed.

Lemma sudkamp_315_v2:
forall g: cfg _ _,
forall v w: sf,
forall n: nat,
derives6 g n v w ->
forall A: non_terminal,
forall v': sentence,
forall v'': sf,
v = (map term_lift v') ++ [inl A] ++ v'' ->
exists t1 t2: nat,
exists p w'': sf,
derives6 g t1 [inl A] p
/\
derives6 g t2 v'' w'' 
/\
w = (map term_lift v') ++ p ++ w''
/\
n = t1 + t2.
Proof.
intros g v w n H1 A v' v'' H2.
rewrite H2 in H1.
assert (H1':= H1).
apply derives6_t_list_left in H1.
destruct H1 as [s2' H3].
rewrite H3 in H1'.
apply derives6_tl_tl in H1'.
apply derives6_split in H1'.
destruct H1' as [s1' [s2'0 [n1 [n2 [H4 [H5 [H6 H7]]]]]]].
exists n1, n2, s1', s2'0.
split.
- exact H6.
- split.
  + exact H7.
  + split.
    * rewrite H4 in H3.
      exact H3.
    * exact H5.
Qed.

Lemma terminal_lift_inj:
forall l1 l2: sentence,
map term_lift l1 = map term_lift l2 ->
l1 = l2.
Proof.
induction l1, l2.
- simpl. auto.
- simpl. 
  intro H.
  inversion H.
- simpl. 
  intro H.
  inversion H.
- simpl. 
  intro H.
  inversion H.
  rewrite H1 in H.
  inversion H.
  specialize (IHl1  l2 H3).
  rewrite IHl1.
  reflexivity.
Qed.

Lemma sudkamp_315_v3:
forall g: cfg _ _,
forall v: sf,
forall w: sentence,
forall n: nat,
derives6 g n v (map term_lift w) ->
forall A: non_terminal,
forall v': sentence,
forall v'': sf,
v = (map term_lift v') ++ [inl A] ++ v'' ->
exists t1 t2: nat,
exists p w'': sentence,
derives6 g t1 [inl A] (map term_lift p)
/\
derives6 g t2 v'' (map term_lift w'') 
/\
w = v' ++ p ++ w''
/\
n = t1 + t2.
Proof.
intros g v w n H1 A v' v'' H2.
rewrite H2 in H1.
assert (H1':= H1).
apply derives6_t_list_left in H1.
destruct H1 as [s2' H3].
rewrite H3 in H1'.
apply derives6_tl_tl in H1'.
apply derives6_split in H1'.
destruct H1' as [s1' [s2'0 [n1 [n2 [H4 [H5 [H6 H7]]]]]]].
symmetry in H3.
apply map_expand in H3.
destruct H3 as [s3 [s4 [H11 [H12 H13]]]].
rewrite H4 in H13.
symmetry in H13.
apply map_expand in H13.
destruct H13 as [s5 [s6 [H14 [H15 H16]]]].
rewrite <- H15 in H6.
rewrite <- H16 in H7.
exists n1, n2, s5, s6.
split.
- exact H6.
- split.
  + exact H7.
  + split.
    * apply terminal_lift_inj in H12.
      rewrite H12 in H11. 
      rewrite H14 in H11.
      exact H11.
    * exact H5.
Qed.

Lemma sf_struct:
forall s: sf,
( exists w1: sentence,
  exists X: non_terminal,
  exists w2: sf,
  s = map term_lift w1 ++ [inl X] ++ w2) \/
( exists w: sentence,
  s = map term_lift w).
Proof.
induction s.
- right.
  exists [].
  simpl. 
  reflexivity.
- destruct IHs as [IHs | IHs].
  + destruct IHs as [w1 [X0 [w2 H]]].
    destruct a.
    * left.
      exists [], n, ((map term_lift w1) ++ [inl X0] ++ w2).
      simpl. 
      rewrite H.
      reflexivity.
    * left.
      exists (t :: w1), X0, w2.
      rewrite H.
      simpl. 
      reflexivity.
  + destruct IHs as [w H].
    destruct a.
    * left.
      rewrite H.
      exists [], n, (map term_lift w).
      simpl. 
      reflexivity.
    * right.
      rewrite H.
      exists (t :: w).
      simpl. 
      reflexivity.
Qed.

Lemma sflist_nt_sf:
forall g: cfg _ _,
forall s1 s2: sf,
forall l: list sf,
sflist g ([s1] ++ l ++ [s2]) ->
forall n: non_terminal,
In (inl n) s1 ->
exists s1' s1'' s2' s2'' beta: sf,
exists l': list sf,
s1 = s1' ++ [inl n] ++ s1'' ->
s2 = s2' ++ beta ++ s2'' ->
[inl n] <> beta ->
sflist g ([[inl n]] ++ l' ++ [beta]).
Proof.
intros g s1 s2 l H1 n H2.
apply in_split in H2.
destruct H2 as [l1 [l2 H3]].
assert (H4: exists l: list sf, sflist g l /\ hd [] l = s1 /\ last l [] = s2).
  { 
  exists ([s1] ++ l ++ [s2]).
  split.
  - exact H1.
  - split.
    + simpl. 
      reflexivity.
    + rewrite app_assoc. 
      rewrite last_last.
      reflexivity.
  }
apply derives_sflist in H4.
apply derives_nt_sf with (n:=n) in H4.
- destruct H4 as [s1' [s1'' [s2' [s2'' [beta [H5 [H6 H7]]]]]]].
  apply derives_sflist in H7.
  destruct H7 as [l0 [H8 [H9 H10]]].
  assert (H8':=H8).
  assert (H20: length l0 >= 2 \/ length l0 < 2) by omega.
  destruct H20 as [H20 | H20].
  + apply sflist_split in H8.
    * destruct H8 as [s0 [s3 [l' [H11 [H12 H13]]]]].
      exists s1', s1'', s2', s2'', beta, l'.
      intros H14 H15.
      rewrite H11 in H9.
      rewrite H12 in H10.
      rewrite H9 in H13.
      rewrite H10 in H13.
      rewrite H13 in H8'.
      intros _.
      exact H8'.
    * exact H20.
  + assert (H21: length l0 = 1 \/ length l0 = 0) by omega.
    destruct H21 as [H21 | H21].
    * exists s1', s1'', s2', s2'', [inl n], [].
      intros H11 H12 H13.
      destruct H13.
      reflexivity.
    * apply length_zero in H21.
      rewrite H21 in H9.
      simpl in H9.
      inversion H9.
- apply in_out with (s1:=l1) (s2:=l2).
  exact H3.
Qed.

Lemma no_nt_derives:
forall g: cfg _ _,
forall s1 s2: sf,
forall s: sentence,
derives g s1 s2 -> s1 = (map term_lift s) ->
s2 = (map term_lift s).
Proof.
intros g s1 s2 s H1.
generalize dependent s.
induction H1.
- auto.
- intros s H3.
  specialize (IHderives s H3).
  change (s2 ++ inl left :: s3) with (s2 ++ [inl left] ++ s3) in IHderives.
  apply not_nt_in_sentence in IHderives.
  contradiction.
Qed.

Lemma sf_eq_1: 
forall s: sf,
length s = 1 ->
(exists t: terminal, s = [inr t]) \/
(exists n: non_terminal, s = [inl n]).
Proof.
intros s H.
destruct s.
- simpl in H.
  omega.
- destruct s0.
  + destruct s. 
    * right. 
      exists n. 
      reflexivity.
    * left. 
      exists t. 
      reflexivity.
  + simpl in H.
    omega.
Qed. 

Lemma sf_ge_2:
forall s: sf,
length s >= 2 ->
exists s1 s2: symbol,
exists s': sf,
s = s1 :: s2 :: s'.
Proof.
intros s H.
destruct s.
- simpl in H; omega.
- destruct s0.
  + simpl in H; omega.
  + exists s, s0, s1.
    reflexivity.
Qed.

End ContextFreeGrammars_Lemmas.

Section ContextFreeGrammars_Lemmas_2.

Variables non_terminal non_terminal' non_terminal'' terminal: Type.

Notation sentence:= (list terminal).
Notation sf:= (list (non_terminal + terminal)).
Notation slist:= (list sf).
Notation term_lift:= ((terminal_lift non_terminal) terminal).

Lemma g_equiv_trans:
forall g1: cfg non_terminal terminal,
forall g2: cfg non_terminal' terminal,
forall g3: cfg non_terminal'' terminal,
g_equiv g1 g2 /\ g_equiv g2 g3 -> g_equiv g1 g3.
Proof.
unfold g_equiv.
intros g1 g2 g3 [H1 H2] s.
specialize (H1 s).
specialize (H2 s).
destruct H1 as [H3 H4].
destruct H2 as [H5 H6].
split.
- intros H7.
  apply H5.
  apply H3.
  exact H7.
- intros H7.
  apply H4.
  apply H6.
  exact H7.
Qed.

Lemma g_equiv_without_empty_trans:
forall g1: cfg non_terminal terminal,
forall g2: cfg non_terminal' terminal,
forall g3: cfg non_terminal'' terminal,
g_equiv_without_empty g1 g2 /\ g_equiv_without_empty g2 g3 -> g_equiv_without_empty g1 g3.
Proof.
unfold g_equiv_without_empty.
intros g1 g2 g3 [H1 H2] s H3.
specialize (H1 s H3).
specialize (H2 s H3).
destruct H1 as [H4 H5].
destruct H2 as [H6 H7].
split.
- intros H8.
  apply H6.
  apply H4.
  exact H8.
- intros H8.
  apply H5.
  apply H7.
  exact H8.
Qed.

Lemma g_equiv_split:
forall g1: cfg non_terminal' terminal,
forall g2: cfg non_terminal'' terminal,
g_equiv g1 g2 <->
((produces g1 [] <-> produces g2 []) /\ (g_equiv_without_empty g1 g2)). 
Proof.
intros g1 g2.
split.
- intros H.
  split.
  + apply H.
  + unfold g_equiv in H.
    unfold g_equiv_without_empty.
    intros s H1.
    specialize (H s).
    exact H.
- intros H.
  destruct H as [H1 H2].
  unfold g_equiv_without_empty in H2.
  unfold g_equiv.
  intros s.
  destruct s.
  + exact H1.
  + apply H2.
    apply not_eq_sym.
    apply nil_cons.
Qed.

Lemma not_derives_start_symbol:
forall g: cfg non_terminal terminal,
start_symbol_not_in_rhs g ->
forall s: sf,
derives g [inl (start_symbol g)] s ->
s <> [inl (start_symbol g)] ->
~ In (inl (start_symbol g)) s.
Proof.
intros g H1 s H2 H3 H4.
apply in_split in H4.
destruct H4 as [l1 [l2 H4]].
subst.
apply exists_rule' in H2.
destruct H2 as [H2 | H2].
- destruct H2 as [H2 [H4 H5]].
  subst.
  simpl in H3.
  destruct H3.
  reflexivity.
- destruct H2 as [left [right [H2 H5]]].
  specialize (H1 left right H2).
  contradiction.
Qed.

End ContextFreeGrammars_Lemmas_2.
