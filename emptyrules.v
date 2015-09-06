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
(* SIMPLIFICATION - EMPTY RULES                                          *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.
Require Import Decidable.

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
(* SIMPLIFICATION - EMPTY RULES - DEFINITIONS                            *)
(* --------------------------------------------------------------------- *)

Section EmptyRules_1_Definitions.

Variables non_terminal terminal: Type.

Inductive non_terminal': Type:=
| Lift_nt: non_terminal -> non_terminal'
| New_ss. 

Notation symbol:= (non_terminal + terminal)%type.
Notation symbol':= (non_terminal' + terminal)%type.
Notation nlist:= (list non_terminal).
Notation nlist':= (list non_terminal').
Notation tlist:= (list terminal).
Notation sentence := (list terminal).
Notation sf := (list (non_terminal + terminal)).
Notation sf' := (list (non_terminal' + terminal)).
Notation term_lift:= ((terminal_lift non_terminal) terminal).

Definition symbol_lift (s: symbol): symbol':=
match s with
| inl n => inl (Lift_nt n)
| inr t => inr t
end.

Lemma symbol_lift_inj:
injective _ _ symbol_lift.
Proof.
unfold injective.
intros e1 e2 H.
destruct e1, e2.
- simpl in H.
  inversion H.
  reflexivity.
- simpl in H.
  inversion H.
- simpl in H.
  inversion H.
- simpl in H.
  inversion H.
  reflexivity.
Qed.

Lemma symbol_lift_equiv_terminal_lift:
forall s: sentence,
(map symbol_lift (map term_lift s)) = (map (@terminal_lift _ _) s).
Proof.
induction s.
- simpl. 
  reflexivity.
- simpl. 
  rewrite IHs.
  change (terminal_lift non_terminal' a) with (inr non_terminal' a).
  reflexivity.
Qed.

Definition sf_lift (s: sf): sf':=
map symbol_lift s.

Definition sf_list_lift (l: list sf): list sf':=
map sf_lift l.

Lemma symbol_lift_exists:
forall a': symbol', 
a' <> (inl New_ss) ->
exists a: symbol,
a' = symbol_lift a.
Proof.
intros a'.
destruct a'.
- destruct n.
  + exists (inl n).  
    simpl.
    reflexivity.
  + intros H. 
    destruct H. 
    reflexivity. 
- exists (inr t).
  simpl. 
  reflexivity. 
Qed.

Lemma sf_lift_exists:
forall s': sf',
~ In (inl New_ss) s' ->
exists s: sf,
s' = sf_lift s.
Proof.
intros s' H.
induction s'.
- exists [].
  simpl.
  reflexivity.
- assert (H1: ~ In (inl New_ss) s'). 
    {
    intros H1. 
    apply H. 
    apply in_cons. 
    exact H1. 
    }
  specialize (IHs' H1). 
  destruct IHs' as [s H2].
  assert (H3: a <> (inl New_ss) -> exists b: symbol, a = symbol_lift b).
    {
    intros H3. 
    apply symbol_lift_exists.
    exact H3.
    }
  simpl in H.
  apply not_or in H.
  destruct H as [H _].
  specialize (H3 H).
  destruct H3 as [b H3].
  exists (b :: s).
  simpl. 
  rewrite <- H3.
  apply app_eq.
  exact H2.
Qed.

Inductive g_emp_rules (g: cfg _ _): non_terminal' -> sf' -> Prop :=
| Lift_direct : 
       forall left: non_terminal,
       forall right: sf,
       right <> [] -> rules g left right ->
       g_emp_rules g (Lift_nt left) (map symbol_lift right)
| Lift_indirect:
       forall left: non_terminal,
       forall right: sf,
       g_emp_rules g (Lift_nt left) (map symbol_lift right)->
       forall s1 s2: sf, 
       forall s: non_terminal,
       right = s1 ++ (inl s) :: s2 ->
       empty g (inl s) ->
       s1 ++ s2 <> [] ->
       g_emp_rules g (Lift_nt left) (map symbol_lift (s1 ++ s2))
| Lift_start_emp: 
       g_emp_rules g New_ss [inl (Lift_nt (start_symbol g))]. 

Lemma g_emp_finite:
forall g: cfg _ _,
exists n: nat,
exists ntl: nlist',
exists tl: tlist,
In New_ss ntl /\
forall left: non_terminal',
forall right: sf',
g_emp_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal', In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
intros g.
destruct (rules_finite g) as [n [ntl [tl H1]]].
exists (S n), (New_ss :: map Lift_nt ntl), tl.
split.
- destruct H1 as [H1 _].
  simpl. 
  left. 
  reflexivity. 
- intros left right H2.
  destruct H1 as [H1' H1].
  induction H2.
  + specialize (H1 left right H0).
    destruct H1 as [H4 [H5 H6]].
    split.
    * apply length_map_le.
      omega. 
    * {
      split.
      - simpl. 
        right. 
        apply in_map. 
        exact H5.
      - split. 
        + intros s HH.
          destruct s.
          * simpl. 
            right.
            apply in_map.
            apply H6.
            apply in_map_iff in HH.
            destruct HH as [x [HH1 HH2]].
            {
            destruct x.
            - simpl in HH1.
              inversion HH1.
              subst.
              exact HH2.
            - simpl in HH1.
              inversion HH1.
            }
          * simpl. 
            left. 
            reflexivity. 
        + intros s HH.
          apply H6.
          apply in_map_iff in HH.
          destruct HH as [x [HH1 HH2]].
          destruct x.
          * simpl in HH1.
            inversion HH1.
          * simpl in HH1.
            inversion HH1.
            subst.
            exact HH2.
      }
  + subst.
    destruct IHg_emp_rules as [H4 [H5 H6]].
    split.
    * apply length_map_le. 
      rewrite map_app in H4.
      simpl in H4.
      apply length_cons_le in H4.
      {
      replace (map symbol_lift s1 ++ map symbol_lift s2) with (map symbol_lift (s1 ++ s2)) in H4.
      - apply length_map_le_inv in H4.
        exact H4.
      - apply map_app.
      }
    * {
      split.
      - exact H5.
      - split.
        + intros s0 H7.
          apply H6.
          rewrite map_app in H7.
          apply in_app_or in H7.
          rewrite map_app. 
          apply in_or_app.
          destruct H7 as [H7 | H7].
          * left.
            exact H7.
          * right.
            simpl.
            right. 
            exact H7.
        + destruct H6 as [_ H6].
          intros s0 H7.
          apply H6.
          rewrite map_app in H7.
          apply in_app_or in H7.
          rewrite map_app. 
          apply in_or_app.
          destruct H7 as [H7 | H7].
          * left.
            exact H7.
          * right.
            simpl.
            right. 
            exact H7.
      }
  + split.
    * simpl.
      omega.
    * {
      split.
      - simpl.
        left.
        reflexivity.
      - split.
        + intros s H2.
          simpl in H2.
          destruct H2 as [H2 | H2].
          * inversion H2.
            simpl.
            right.
            apply in_map.
            exact H1'.
          * contradiction.
        + intros s H. 
          simpl in H.
          destruct H as [H | H].
          * inversion H.
          * contradiction.
      }
Qed.

Definition g_emp (g: cfg non_terminal terminal): cfg non_terminal' terminal := {|
start_symbol:= New_ss;
rules:= g_emp_rules g;
rules_finite:= g_emp_finite g
|}.

End EmptyRules_1_Definitions.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY RULES - LEMMAS AND THEOREMS                    *)
(* --------------------------------------------------------------------- *)

Section EmptyRules_1_Lemmas.

Variables non_terminal non_terminal1 non_terminal2 terminal: Type.

Notation symbol:= (non_terminal + terminal)%type.
Notation symbol':= (non_terminal' + terminal)%type.
Notation nlist:= (list non_terminal).
Notation nlist':= (list non_terminal' _).
Notation tlist:= (list terminal).
Notation sentence := (list terminal).
Notation sf := (list (non_terminal + terminal)).
Notation sf' := (list ((non_terminal' non_terminal) + terminal)).
Notation term_lift:= ((terminal_lift non_terminal) terminal).

Lemma produces_non_empty_equiv_non_empty:
forall g: cfg non_terminal terminal,
produces_non_empty g -> non_empty g.
Proof.
intros g H.
unfold non_empty. 
unfold useful.
unfold produces_non_empty in H.
destruct H as [s [H1 H2]].
exists s.
exact H1.
Qed.

Lemma non_empty_equiv_or:
forall g: cfg non_terminal terminal,
non_empty g -> (produces_empty g \/ produces_non_empty g).
Proof.
intros g H.
unfold non_empty in H.
unfold useful in H.
destruct H as [s H1].
assert (H2: s = [] \/ s <> []).
  {
  apply nil_not_nil.
  }
destruct H2 as [H2 | H2].
- subst.
  left.
  exact H1.
- right.
  exists s.
  exact (conj H1 H2).
Qed.

Lemma start_symbol_not_in_rhs_g_emp: 
forall g: cfg non_terminal terminal,
start_symbol_not_in_rhs (g_emp g).
Proof.
intros g.
unfold start_symbol_not_in_rhs.
intros left right H1 H2.
inversion H1.
- subst. 
  simpl in H2. 
  apply in_split in H2. 
  destruct H2 as [l1 [l2 H2]].
  symmetry in H2. 
  apply map_expand in H2.
  destruct H2 as [s1' [s2' [H3 [H4 H5]]]].
  destruct s2'.
  + inversion H5.
  + simpl in H5.
    inversion H5.
    destruct s.
    * simpl in H6.
      inversion H6.
    * simpl in H6.
      inversion H6.
- subst.
  simpl in H2. 
  apply in_split in H2. 
  destruct H2 as [l1 [l2 H2]].
  symmetry in H2. 
  apply map_expand in H2.
  destruct H2 as [s1' [s2' [H5 [H6 H7]]]].
  destruct s2'.
  + inversion H7.
  + simpl in H7.
    inversion H7.
    destruct s0.
    * simpl in H2.
      inversion H2.
    * simpl in H2.
      inversion H2.
- rewrite <- H0 in H2. 
  simpl in H2.
  destruct H2 as [H2 | H2].
  + inversion H2.
  + contradiction.
Qed.

Lemma g_emp_not_derives_empty:
forall g: cfg non_terminal terminal,
forall n: (non_terminal' _),
~ derives (g_emp g) [inl n] [].
Proof.
intros g n H.
inversion H.
clear H.
subst.
simpl in H3.
inversion H3.
- subst.
  apply app_eq_nil in H0.
  destruct H0 as [_ H0].
  apply app_eq_nil in H0.
  destruct H0 as [H0 _].
  apply map_eq_nil in H0. 
  contradiction.
- subst.
  apply app_eq_nil in H0.
  destruct H0 as [_ H0].
  apply app_eq_nil in H0.
  destruct H0 as [H0 _].
  rewrite H0 in H3.
  inversion H3.
  + subst.
    apply map_eq_nil in H6.
    contradiction. 
  + apply map_eq_nil in H6.
    contradiction. 
- subst.
  destruct s2.
  + inversion H0.
  + inversion H0.
Qed.

Lemma g_emp_has_no_empty_rules:
forall g: cfg non_terminal terminal,
has_no_empty_rules (g_emp g).
Proof.
intros g.
unfold has_no_empty_rules.
intros left right H.
inversion H.
- apply map_not_nil_inv. 
  exact H0.
- apply map_not_nil_inv. 
  exact H3.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma in_left_not_empty:
forall g: cfg non_terminal terminal,
forall x: non_terminal' _,
forall right: sf',
rules (g_emp g) x right -> ~ empty (g_emp g) (inl x).
Proof.
intros g x right H1 H2.
simpl in H1.
inversion H1.
- clear H1.
  subst.
  apply g_emp_not_derives_empty in H2.
  contradiction.
- clear H1. 
  subst.
  apply g_emp_not_derives_empty in H2.
  contradiction.
- subst.
  apply g_emp_not_derives_empty in H2.
  contradiction.
Qed.

Lemma in_right_not_empty:
forall g: cfg non_terminal terminal,
forall x n: non_terminal' _,
forall right: sf',
rules (g_emp g) x right -> In (inl n) right -> ~ empty (g_emp g) (inl n).
Proof.
intros g x n right H1 H2 H3.
simpl in H1.
inversion H1.
- clear H1.
  subst.
  apply g_emp_not_derives_empty in H3.
  contradiction.
- clear H1. 
  subst.
  apply g_emp_not_derives_empty in H3.
  contradiction.
- subst.
  apply g_emp_not_derives_empty in H3.
  contradiction.
Qed.

Lemma g_emp_has_no_nullable_symbols:
forall g: cfg non_terminal terminal,
has_no_nullable_symbols (g_emp g).
Proof.
intros g.
unfold has_no_nullable_symbols.
intros s H1.
destruct s as [nt | t].
- apply g_emp_not_derives_empty in H1.
  contradiction.
- unfold empty in H1.
  inversion H1.
  apply app_eq_nil in H.
  destruct H as [_ H].
  apply app_eq_nil in H.
  destruct H as [H _].
  subst.
  apply g_emp_has_no_empty_rules in H3.
  destruct H3.
  reflexivity.
Qed.  

Lemma rules_g_emp_g:
forall g: cfg non_terminal terminal,
forall left: non_terminal,
forall right: sf,
rules (g_emp g) (Lift_nt left) (map (@symbol_lift _ _) right) ->
rules g left right \/ derives g [inl left] right.
Proof.
intros g left right H.
simpl in H.
remember (Lift_nt left) as w1.
remember (map (symbol_lift (terminal:=terminal)) right) as w2.
(*
move left after H.
move right after H.
*)
generalize left right Heqw1 Heqw2. 
clear left right Heqw1 Heqw2.
induction H.
- intros left0 right0 Heqw1 Heqw2.
  inversion Heqw1.
  apply map_eq in Heqw2.
  + subst.
    left.
    exact H0.
  + apply symbol_lift_inj.
- intros left0 right0 Heqw1 Heqw2.
  inversion Heqw1.
  apply map_eq in Heqw2.
  + subst.
    specialize (IHg_emp_rules left0 (s1 ++ inl s :: s2)).   
    specialize (IHg_emp_rules (eq_refl (Lift_nt left0))).
    specialize (IHg_emp_rules (eq_refl (map (symbol_lift (terminal:=terminal)) (s1 ++ inl s :: s2)))).
    destruct IHg_emp_rules as [HH | HH].
    * right.
      {
      replace (s1 ++ s2) with (s1 ++ [] ++ s2).
      - apply derives_subs with (s3:=[inl s]).
        + apply derives_start.
          exact HH.
        + exact H1. 
      - simpl.   
        reflexivity.
      }
    * right.
      {       
      replace (s1 ++ s2) with (s1 ++ [] ++ s2).
      - apply derives_subs with (s3:=[inl s]).
        + exact HH.
        + exact H1.
      - simpl.
        reflexivity.
      }
  + apply symbol_lift_inj.  
- intros left right H1 H2.
  inversion H1.
Qed.

Lemma derives_g_emp_g:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sf,
derives (g_emp g) [inl (Lift_nt n)] (map (@symbol_lift _ _) s) -> derives g [inl n] s.
Proof.
intros g n s H.
remember [inl (Lift_nt n)] as w1. 
remember (map (symbol_lift (terminal:=terminal)) s) as w2.
generalize n s Heqw1 Heqw2.
clear s n Heqw1 Heqw2.
induction H.
- intros n0 s1 Heqw1 Heqw2. 
  subst.
  destruct s1.
  + simpl in Heqw2.
    inversion Heqw2.
  + destruct s.
    * simpl in Heqw2. 
      inversion Heqw2.
      symmetry in H1.
      apply map_eq_nil in H1.
      subst.
      apply derives_refl.
    * simpl in Heqw2.
      inversion Heqw2.
- intros n s Heqw1 Heqw2.
  destruct left.
  + assert (H1: exists r: sf, right = sf_lift r). 
      {
      apply sf_lift_exists.
      intros H7.
      apply in_split in H7.
      destruct H7 as [l1 [l2 H7]].
      subst.
      apply map_expand in Heqw2.
      destruct Heqw2 as [s1' [s2' [_ [_ H1]]]].
      symmetry in H1.
      apply map_expand in H1.
      destruct H1 as [s1'0 [s2'0 [H1 [H2 H3]]]].
      symmetry in H2.
      apply map_expand in H2.
      destruct H2 as [s1'1 [s2'1 [H4 [H5 H6]]]].
      destruct s2'1.
      - inversion H6.
      - destruct s0. 
        + inversion H6.
        + inversion H6.
      }
    destruct H1 as [r H1].
    subst.
    apply map_expand in Heqw2.
    destruct Heqw2 as [s1' [s2' [H1 [H2 H3]]]].
    symmetry in H3.
    apply map_expand in H3.
    destruct H3 as [s1'0 [s2'0 [H4 [H5 H6]]]].
    rewrite H1.
    rewrite H4.
    apply rules_g_emp_g in H0.
    destruct H0 as [H0 | H0].
    * specialize (IHderives n).
      unfold sf_lift in H5.
      {
      apply map_eq in H5.
      - subst. 
        specialize (IHderives (s1' ++ (inl n0) :: s2'0)).
        apply derives_step with (left:= n0).
        + apply IHderives.
          * reflexivity.
          * change (s1' ++ inl n0 :: s2'0) with (s1' ++ [inl n0] ++ s2'0).
            repeat rewrite map_app.
            reflexivity.
        + exact H0.
      - apply symbol_lift_inj.
      }
    * specialize (IHderives n).
      unfold sf_lift in H5.
      {
      apply map_eq in H5.
      - subst. 
        specialize (IHderives (s1' ++ (inl n0) :: s2'0)).
        apply derives_subs with (s3:= [inl n0]).
        + apply IHderives.
          * reflexivity.
          * change (s1' ++ inl n0 :: s2'0) with (s1' ++ [inl n0] ++ s2'0).
            repeat rewrite map_app.
            reflexivity.
        + exact H0.
      - apply symbol_lift_inj.
      }
  + rewrite Heqw1 in H. 
    apply exists_rule' in H.
    destruct H as [H | H].
    * destruct H as [H _].
      inversion H.
    * destruct H as [left [right0 [H H1]]].
      apply start_symbol_not_in_rhs_g_emp in H.
      simpl in H.
      contradiction.
Qed.

Lemma rules_g_g_emp:
forall g: cfg _ _, 
forall left: non_terminal,
forall right: sf,
right <> [] ->
rules g left right ->
rules (g_emp g) (Lift_nt left) (map (@symbol_lift _ _) right).
Proof.
intros g left right H.
simpl.
apply Lift_direct.
exact H.
Qed.

Inductive sfmatch g: sf -> list sf -> Prop :=
| sfmatch_nil: 
    sfmatch g [] []
| sfmatch_term: 
    forall t xs xxs,
    sfmatch g xs xxs -> sfmatch g (inr t :: xs) ([inr t] :: xxs)
| sfmatch_nonterm: 
   forall nt xs xxs p,
    (p = [] -> empty g (inl nt)) ->
    (p <> [] -> derives (g_emp g) [inl (Lift_nt nt)] (map (@symbol_lift _ _) p)) ->
    sfmatch g xs xxs -> sfmatch g (inl nt :: xs) (p :: xxs).

Fixpoint flatten (l: list sf): sf :=
match l with
| [] => []
| x :: xs => x ++ flatten xs
end.

Fixpoint elim_emp (l: sf) (ll: list sf): sf :=
match l with
| [] => []
| (x :: xs) => match ll with
               | [] => l
               | [] :: ll' => elim_emp xs ll'
               | p :: ll' => x :: elim_emp xs ll'
               end
end.

Lemma sfmatch_left_nil:
forall g: cfg _ _,
forall l: list sf,
sfmatch g [] l ->
l = [].
Proof.
intros g l H.
inversion H.
reflexivity.
Qed.

Lemma elim_emp_not_nil:
forall right: sf,
forall split: list sf,
elim_emp right split <> [] ->
right <> [].
Proof.
intros right split H.
destruct right.
- simpl in H.
  destruct H.
  reflexivity.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma flatten_map:
forall x: list sf,
forall y: sentence,
flatten x = map term_lift y ->
y <> [] ->
x <> [].
Proof.
intros x y H1 H2.
destruct x.
- simpl in H1.
  symmetry in H1. 
  apply map_eq_nil in H1.
  subst.
  destruct H2.
  reflexivity.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma flatten_not_nil:
forall x: sf,
flatten [x] <> [] ->
x <> [].
intros x H.
destruct x.
- simpl in H.
  destruct H.
  reflexivity.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma flatten_not_nil_exists:
forall x: list sf,
flatten x <> [] ->
exists x1 x3: list sf,
exists x2: sf,
x = x1 ++ [x2] ++ x3 /\
x2 <> [].
Proof.
induction x.
- intro H.
  simpl in H.
  destruct H.
  reflexivity.
- intro H.
  simpl in H.
  apply app_not_nil in H.
  destruct H as [H | H].
  + exists [], x, a.
    split. 
    * simpl.  
      reflexivity.
    * exact H.
  + specialize (IHx H).
    destruct IHx as [x1 [x3 [x2 [H1 H2]]]].
    subst.
    exists (a :: x1), x3, x2.
    split. 
    * simpl. 
      reflexivity.
    * exact H2. 
Qed.

Lemma sfmatch_derives:
forall g: cfg _ _,
forall l1 l2: sf,
forall l: list sf,
forall x: non_terminal + terminal,
sfmatch g (l1 ++ [x] ++ l2) l ->
exists p: sf,
exists l3 l4: list sf,
l = l3 ++ [p] ++ l4 /\
sfmatch g l1 l3 /\
derives g [x] p /\
sfmatch g l2 l4.
Proof.
intros g l1.
induction l1.
- intros l2 l x H.
  simpl in H.
  inversion H.
  + (* terminal *)
    subst.
    exists [inr t], [], xxs.
    split.
    * simpl. 
      reflexivity.
    * {
      split.
      - constructor.
      - split.
        + constructor.
        + exact H3.
      }
  + (* non-terminal *)
    subst.
    exists p, [], xxs.
    split.
    * simpl.
      reflexivity.
    * {
      split. 
      - constructor. 
      - split. 
        + assert (H6: p = [] \/ p <> []).
            {
            apply nil_not_nil.
            }
          destruct H6 as [H6 | H6].
          * subst. 
            specialize (H2 (eq_refl [])).
            exact H2.
          * apply derives_g_emp_g.
            apply H3.
            exact H6.
        + exact H5.
      } 
- intros l2 l x H.
  inversion H.
  clear H. 
  + (* terminal *)
    subst.
    specialize (IHl1 l2 xxs x H3).
    destruct IHl1 as [p [l3 [l4 [H11 [H12 [H13 H14]]]]]].
    exists p, ([inr t] :: l3), l4.
    split. 
    * simpl.
      rewrite H11.
      reflexivity.
    * {
      split. 
      - apply sfmatch_term.
        exact H12.
      - split.
        + exact H13.
        + exact H14.
      }
  + (* non-terminal *)
    subst. 
    specialize (IHl1 l2 xxs x H5).
    destruct IHl1 as [p' [l3 [l4 [H11 [H12 [H13 H14]]]]]].
    exists p', ([p] ++ l3), l4.
    split.
    * simpl. 
      rewrite H11.
      reflexivity.
    * {
      split.
      - apply sfmatch_nonterm.
        + exact H2.
        + exact H3.
        + exact H12.
      - split. 
        + exact H13.
        + exact H14.
      }
Qed.

Lemma sfmatch_derives_inv:
forall g: cfg _ _,
forall l: sf,
forall l3 l4: list sf,
forall p: sf,
sfmatch g l (l3 ++ [p] ++ l4) ->
exists x: non_terminal + terminal,
exists l1 l2: sf,
l = l1 ++ [x] ++ l2 /\
sfmatch g l1 l3 /\
sfmatch g [x] [p] /\
sfmatch g l2 l4.
Proof.
intros g l l3 l4 p H.
remember (l3 ++ [p] ++ l4) as w.
generalize dependent l4.
generalize dependent l3.
generalize dependent p.
induction H.
- (* empty *)
  intros p l3 l4 H. 
  destruct l3.
  + inversion H.
  + inversion H.
- (* terminal *)
  intros p l3 l4 H1. 
  destruct l3.
  + simpl in H1.
    inversion H1.
    exists (inr t), [], xs.
    split. 
    * simpl. 
      reflexivity.
    * {
      split.
      - constructor.
      - split.
        + constructor.
          constructor.
        + rewrite <- H3.
          exact H.
      }
  + inversion H1.
    clear H1.
    subst.
    specialize (IHsfmatch p l3 l4 (eq_refl (l3 ++ p :: l4))).
    destruct IHsfmatch as [x [l1 [l2 [H1 [H2 [H3 H4]]]]]].
    rewrite H1. 
    exists x, (inr t :: l1), l2.
    split.
    * simpl. 
      reflexivity.
    * {
      split.
      - apply sfmatch_term.
        exact H2.
      - split.
        + exact H3.
        + exact H4.
      }
- (* non-terminal *)
  intros p0 l3 l4 H2.
  destruct l3.
  inversion H2.
  clear H2.
  subst.
  + assert (H5: p0 = [] \/ p0 <> []).
      {
      apply nil_not_nil.
      }
    destruct H5 as [H5 | H5].
    * subst. 
      exists (inl nt), [], xs.
      {
      split. 
      - simpl. 
        reflexivity.
      - split.
        + constructor.
        + split.
          * {
            constructor.
            - exact H.
            - exact H0.
            - constructor.
            }
          * exact H1.
      }
    * exists (inl nt), [], xs.
      {
      split. 
      - simpl. 
        reflexivity.
      - split.
        + constructor.
        + split.
          * {
            constructor.
            - exact H.
            - exact H0.
            - constructor.
            }
          * exact H1.
      }
  + assert (H5: p = [] \/ p <> []).
      {
      apply nil_not_nil.
      }
    destruct H5 as [H5 | H5].
    * inversion H2. 
      subst. 
      rewrite <- H4 in H2. 
      rewrite <- H4.
      clear H2 H4. 
      specialize (IHsfmatch p0 l3 l4).
      specialize (IHsfmatch (eq_refl (l3 ++ p0 :: l4))).
      destruct IHsfmatch as [x [l1 [l2 [H2 [H3 [H4 H5]]]]]].
      rewrite H2.
      exists x, (inl nt :: l1), l2.
      {
      split. 
      - simpl. 
        reflexivity.
      - split.
        + apply sfmatch_nonterm.
          * exact H.
          * exact H0.
          * exact H3.
        + split.
          * exact H4.
          * exact H5.
      }
    * inversion H2.
      clear H2.
      subst.
      specialize (IHsfmatch p0 l3 l4).
      specialize (IHsfmatch (eq_refl (l3 ++ p0 :: l4))).
      destruct IHsfmatch as [x [l1 [l2 [H2 [H3 [H4 H6]]]]]].
      rewrite H2.
      exists x, (inl nt :: l1), l2.
      {
      split. 
      - simpl. 
        reflexivity.
      - split.
        + apply sfmatch_nonterm.
          * exact H.
          * exact H0.
          * exact H3.
        + split.
          * exact H4.
          * exact H6.
      }
Qed.

Lemma sfmatch_elim_emp_not_nil:
forall g: cfg _ _,
forall x: non_terminal + terminal,
forall p: sf,
sfmatch g [x] [p] ->
p <> [] ->
elim_emp [x] [p] <> [].
Proof.
intros g x p H1 H2.
inversion H1.
- simpl.
  apply not_eq_sym. 
  apply nil_cons.
- subst.
  destruct p.
  + destruct H2.
    reflexivity.
  + simpl.
    apply not_eq_sym.
    apply nil_cons.
Qed. 

Lemma sfmatch_combine:
forall g: cfg _ _,
forall l1 l3: sf,
forall l2 l4: list sf,
sfmatch g l1 l2 ->
sfmatch g l3 l4 ->
sfmatch g (l1 ++ l3) (l2 ++ l4).
Proof.
intros g l1 l3 l2 l4 H1.
induction H1.
- simpl. 
  auto.
- intros H2.
  specialize (IHsfmatch H2).
  apply sfmatch_term with (t:= t) in IHsfmatch.
  exact IHsfmatch.
- intros H2.
  specialize (IHsfmatch H2).
  assert (H3: p = [] \/ p <> []).
    {
    apply nil_not_nil.
    }
  destruct H3 as [H3 | H3].
  + specialize (H H3).
    apply sfmatch_nonterm with (nt:= nt) (p:= p) in IHsfmatch.
    * exact IHsfmatch.
    * intros _.
      exact H.
    * exact H0.
  + specialize (H0 H3).
    apply sfmatch_nonterm with (nt:= nt) (p:= p) in IHsfmatch.
    * exact IHsfmatch.
    * exact H.
    * intros _.
      exact H0.
Qed.

Lemma elim_emp_split:
forall g: cfg _ _,
forall l1 l3: sf,
forall l2 l4: list sf,
sfmatch g l1 l2 ->
sfmatch g l3 l4 ->
elim_emp (l1 ++ l3) (l2 ++ l4) = (elim_emp l1 l2) ++ (elim_emp l3 l4).
Proof.
intros g l1 l3 l2 l4 H.
generalize dependent l4.
generalize dependent l3.
induction H.
- subst.
  intros. 
  simpl. 
  reflexivity.
- intros. 
  simpl.
  apply app_eq.
  apply IHsfmatch.
  exact H0.
- intros l3 l4 H2.
  assert (H3: p = [] \/ p <> []).
    {
    apply nil_not_nil.
    }
  destruct H3 as [H3 | H3].
  + subst.
    simpl.
    apply IHsfmatch.
    exact H2.
  + destruct p. 
    * destruct H3. 
      reflexivity.
    * simpl. 
      apply app_eq.
      apply IHsfmatch.
      exact H2.
Qed.

Lemma elim_emp_not_nil_add_left:
forall g: cfg _ _,
forall l1 l1': sf,
forall l2 l2': list sf,
sfmatch g l1 l2 ->
elim_emp l1 l2 <> [] ->
sfmatch g l1' l2' ->
elim_emp (l1' ++ l1) (l2' ++ l2) <> [].
Proof.
intros g l1 l1' l2 l2' H.
generalize dependent l2'.
generalize dependent l1'.
inversion H.
- intros.
  simpl in H2.
  destruct H2.
  reflexivity.
- intros.
  rewrite elim_emp_split with (g:= g).
  + apply app_not_nil_inv.
    right.
    exact H3.
  + exact H4.
  + apply sfmatch_term.
    exact H0.
- intros.
  rewrite elim_emp_split with (g:= g).
  + apply app_not_nil_inv.
    right.
    exact H5.
  + exact H6.
  + apply sfmatch_nonterm.
    * exact H0.
    * exact H1.
    * exact H2.
Qed.

Lemma elim_emp_not_nil_add_right:
forall g: cfg _ _,
forall l1 l1': sf,
forall l2 l2': list sf,
sfmatch g l1 l2 ->
elim_emp l1 l2 <> [] ->
sfmatch g l1' l2' ->
elim_emp (l1 ++ l1') (l2 ++ l2') <> [].
Proof.
intros g l1 l1' l2 l2' H.
generalize dependent l2'.
generalize dependent l1'.
inversion H.
- intros.
  simpl in H2.
  destruct H2.
  reflexivity.
- intros.
  rewrite elim_emp_split with (g:= g).
  + apply app_not_nil_inv.
    left.
    exact H3.
  + rewrite H1. 
    rewrite H2. 
    exact H.
  + exact H4.
- intros.
  rewrite elim_emp_split with (g:= g).
  + apply app_not_nil_inv.
    left.
    exact H5.
  + rewrite H3. 
    rewrite H4. 
    exact H.
  + exact H6. 
Qed.

Lemma elim_emp_not_emp:
forall g: cfg _ _,
forall l1 l2: sf,
forall x: non_terminal + terminal,
forall l3 l4: list sf,
forall p: sf,
sfmatch g l1 l3 ->
sfmatch g [x] [p] ->
sfmatch g l2 l4 ->
p <> [] ->
elim_emp (l1 ++ [x] ++ l2) (l3 ++ [p] ++ l4) <> [].
Proof.
intros g l1 l2 x l3 l4 p H2 H3 H4 H5.
destruct x.
- (* non-terminal *)
  assert (H3':= H3). 
  apply sfmatch_elim_emp_not_nil in H3.
  + assert (H3'':= H3').
    apply elim_emp_not_nil_add_left with (l1':= l1) (l2':= l3) in H3'.
    * {
      apply elim_emp_not_nil_add_right with (g:= g) (l1':= l2) (l2':= l4) in H3'.
      - repeat rewrite <- app_assoc in H3'. 
        exact H3'.
      - apply sfmatch_combine.
        + exact H2.
        + exact H3''. 
      - exact H4.
      }
    * exact H3.
    * exact H2.
  + exact H5.
- (* terminal *)
  assert (H3':= H3).
  apply sfmatch_elim_emp_not_nil in H3.
  + assert (H3'':= H3').
    apply elim_emp_not_nil_add_left with (g:= g) (l1':= l1) (l2':= l3) in H3'.
    * {
      apply elim_emp_not_nil_add_right with (g:= g) (l1':= l2) (l2':= l4) in H3'.
      - repeat rewrite <- app_assoc in H3'. 
        exact H3'.
      - apply sfmatch_combine.
        + exact H2.
        + exact H3''. 
      - exact H4.
      }
    * exact H3.
    * exact H2.
  + exact H5.
Qed.

Lemma flatten_elim_emp:
forall x: sf,
forall y: list sf,
forall g: cfg _ _,
sfmatch g x y ->
flatten y <> [] ->
elim_emp x y  <> [].
Proof.
intros x y g H3 H4.
apply flatten_not_nil_exists in H4.
destruct H4 as [x1 [x2 [x3 [H5 H6]]]].
assert (H3':= H3).
rewrite H5 in H3. 
apply sfmatch_derives_inv in H3.
destruct H3 as [x0 [l1 [l2 [H11 [H12 [H13 H14]]]]]].
subst.
apply elim_emp_not_emp with (g:= g).
- exact H12.
- exact H13.
- exact H14.
- exact H6.
Qed.

Lemma sfmatch_derives_first:
forall g: cfg _ _,
forall l1: sf,
forall l2: list sf,
sfmatch g l1 l2 ->
(l1 = [] /\ l2 = []) \/
(exists a1: non_terminal + terminal,
 exists l1': sf,
 exists a2: sf,
 exists l2': list sf,
 l1 = a1 :: l1' /\
 l2 = a2 :: l2' /\
 derives g [a1] a2 /\ sfmatch g l1' l2').
Proof.
intros g l1 l2 H.
assert (H1: l1 = [] \/ l1 <> []).
  {
  apply nil_not_nil.
  }
destruct H1 as [H1 | H1].
- left.
  subst.
  inversion H.
  auto.
- right.
  destruct l1.
  + destruct H1.
    reflexivity.
  + clear H1.
    change (s :: l1) with ([] ++ [s] ++ l1) in H.
    apply sfmatch_derives in H.
    destruct H as [p [l3 [l4 [H2 [H3 [H4 H5]]]]]].
    apply sfmatch_left_nil in H3.
    exists s, l1, p, l4.
    split. 
    * reflexivity.
    * {
      split.
      - rewrite H3 in H2.
        exact H2.
      - split.
        + exact H4.
        + exact H5.
      }
Qed.  

Lemma right_emp_prop_aux:
forall g left r2 rl2,
sfmatch g r2 rl2 ->
forall r1 rl1,
sfmatch g r1 rl1 ->
elim_emp (r1 ++ r2) (rl1 ++ rl2) <> [] ->
rules (g_emp g) (Lift_nt left) (map (@symbol_lift _ _) r1 ++ map (@symbol_lift _ _) r2) ->
rules (g_emp g) (Lift_nt left) (map (@symbol_lift _ _) r1 ++ map (@symbol_lift _ _) (elim_emp r2 rl2)).
Proof.
intros g left r2 rl2 HH.
elim HH.
- (* empty *)
  intros.
  rewrite app_nil_r in *. 
  auto.
- (* terminal *)
  intros.
  simpl.
  replace (r1 ++ inr t :: elim_emp xs xxs) with ((r1 ++ [inr t]) ++ elim_emp xs xxs).
  + change (map (symbol_lift (terminal:=terminal)) r1 ++  inr t ::  map (symbol_lift (terminal:=terminal)) (elim_emp xs xxs)) with
           (map (symbol_lift (terminal:=terminal)) r1 ++ [inr t] ++ map (symbol_lift (terminal:=terminal)) (elim_emp xs xxs)).
    rewrite app_assoc.
   
    specialize (H0 (r1 ++ [inr t]) (rl1 ++ [[inr t]])).
    rewrite map_app in H0. 
    apply H0.
    * apply sfmatch_combine. 
      auto.
      constructor.
      constructor.
    * repeat rewrite <- app_assoc. 
      simpl. 
      auto.
    * rewrite <- app_assoc. 
      auto.
  + repeat rewrite <- app_assoc. 
    simpl. 
    auto.
- (* non-terminal *)
  intros.
  simpl.
  destruct p.
  + (* empty *)
    apply H2 with rl1. 
    * auto.
    * {
      rewrite elim_emp_split with (g:=g) in H4. 
      - simpl in H4.
        rewrite <- elim_emp_split with (g:=g) in H4; auto.
      - auto.
      - constructor.
        + auto.
        + auto.
        + auto.
      }
    * simpl. 
      { 
      replace (map (symbol_lift (terminal:=terminal)) r1 ++ map (symbol_lift (terminal:=terminal)) xs) with
             (map (symbol_lift (terminal:=terminal)) (r1 ++ xs)).
      - econstructor 2.   
        + replace (map (symbol_lift (terminal:=terminal)) r1 ++ map (symbol_lift (terminal:=terminal)) (inl nt :: xs)) with
                  (map (symbol_lift (terminal:=terminal)) (r1 ++ inl nt :: xs)) in H5.
          * exact H5.
          * rewrite map_app.
            reflexivity.
        + reflexivity.
        + apply H. 
          auto.
        + red.
          intros.
          apply app_eq_nil in H6. 
          destruct H6. 
          subst.
          elim H4. 
          simpl.
          inversion_clear H3. 
          reflexivity.
      - rewrite map_app.
        reflexivity.
      }
  + (* not empty *)
    simpl. 
    replace (map (symbol_lift (terminal:=terminal)) r1 ++  inl (Lift_nt nt) ::  map (symbol_lift (terminal:=terminal)) (elim_emp xs xxs)) with
            (map (symbol_lift (terminal:=terminal)) (r1 ++ [inl nt]) ++ map (symbol_lift (terminal:=terminal)) (elim_emp xs xxs)).
    * {
      specialize (H2 (r1 ++ [inl nt]) (rl1 ++ [s :: p])). 
      apply H2.
      - apply sfmatch_combine. 
        + auto.
        + constructor. 
          * auto.
          * auto. 
          * constructor.
      - repeat rewrite <- app_assoc. 
        simpl. 
        auto.
      - rewrite map_app.
        simpl in H5.
        change (map (symbol_lift (terminal:=terminal)) r1 ++  inl (Lift_nt nt) ::  map (symbol_lift (terminal:=terminal)) xs) with
               (map (symbol_lift (terminal:=terminal)) r1 ++ [inl (Lift_nt nt)] ++ map (symbol_lift (terminal:=terminal)) xs) in H5.
        simpl. 
        rewrite <- app_assoc.
        exact H5.
      }
    * repeat rewrite map_app. 
      simpl. 
      change (map (symbol_lift (terminal:=terminal)) r1 ++  inl (Lift_nt nt) ::  map (symbol_lift (terminal:=terminal)) (elim_emp xs xxs)) with
             (map (symbol_lift (terminal:=terminal)) r1 ++ [inl (Lift_nt nt)] ++ map (symbol_lift (terminal:=terminal)) (elim_emp xs xxs)).
      rewrite <- app_assoc. 
      reflexivity.
Qed.

Lemma right_emp_prop:
forall (g: cfg _ _),
forall left: non_terminal,
forall right: sf,
forall right_list: list sf,
rules g left right ->
sfmatch g right right_list ->
elim_emp right right_list <> [] ->
rules (g_emp g) (Lift_nt left) (map (@symbol_lift _ _) (elim_emp right right_list)).
Proof.
intros.
assert (Hemp: rules (g_emp g) (Lift_nt left) (map (@symbol_lift _ _) right)).
  { 
  apply rules_g_g_emp.
  - apply elim_emp_not_nil with (split:= right_list).
    exact H1.
  - exact H.
  }
change (map (symbol_lift (terminal:=terminal)) (elim_emp right right_list)) with (map (symbol_lift (terminal:=terminal)) [] ++ map (symbol_lift (terminal:=terminal)) (elim_emp right right_list)).
apply right_emp_prop_aux with [].
- auto.
- constructor.
- assumption.
- assumption.
Qed.

Lemma derives_g_g_emp:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sentence,
s <> [] ->
derives g [inl n] (map term_lift s) -> derives (g_emp g) [inl (Lift_nt n)] (map (@symbol_lift _ _) (map term_lift s)).
Proof.
intros g n s H1 H2.
rewrite derives_equiv_derives6 in H2.
destruct H2 as [i H3].
generalize dependent n.
generalize dependent s.
generalize (le_refl i). 
generalize i at 1 3 as i'.
induction i.
- intros i' Hi' s H1 n H2. 
  apply le_n_0_eq in Hi'. 
  subst.
  apply derives6_0_eq in H2. 
  destruct s.
  + simpl in H2.
    inversion H2.
  + simpl in H2.
    inversion H2.
- intros i' Hi' s H1 n H2.
  inversion H2.
  + apply derives_refl.
  + assert (H10: s1 = [] /\ s2 = []).
      {  
      destruct s1.
      - split.
        + reflexivity.    
        + inversion H.   
          reflexivity.
      - inversion H.
        destruct s1.
        + inversion H8.
        + inversion H8.
      }
    destruct H10 as [H11 H12].
    subst.
    rewrite app_nil_l in H.
    rewrite <- H in H2.
    simpl in H4.
    rewrite app_nil_r in H4.
    clear H2.
    (* estrutura intermédia que particiona as derivações do rhs da regra *)
    assert (H10: exists right2: list sf,
                 sfmatch g right right2 /\
                 flatten right2 = map term_lift s).
      {
      apply le_S_n in Hi'.
      generalize i0 Hi' s H4. 
      clear i0 Hi' H4 H0 s H1.
      elim right.
      - (* nil case *)
        intros.
        inversion H4.
        + symmetry in H3.  
          apply map_eq_nil in H3.
          subst.
          exists []. 
          split. 
          * constructor.
          * simpl. 
            reflexivity.
        + apply app_eq_nil in H0.
          destruct H0 as [_ H0]. 
          inversion H0.
      - (* cons case *)
        intros.
        destruct a.
        + (* non_terminal *)
          change (inl n0 :: l) with ([inl n0] ++ l) in H4.
          generalize H4. 
          intros H4'.
          apply derives6_split in H4'.
          destruct H4' as [s1' [s2' [n1 [n2 [HH1 [HH2 [HH3 HH4]]]]]]].
          symmetry in HH1. 
          apply map_expand in HH1. 
          destruct HH1 as [s0a [s0b [? [? ?]]]]. 
          subst.
          assert (Hn2: n2 <= i) by omega.
          specialize (H0 n2 Hn2 s0b HH4). 
          destruct H0 as [right2' [H1 H2]].
          exists ((map term_lift s0a) :: right2').
          simpl.
          rewrite H2.
          simpl. 
          split.
          * assert (H20: s0a = [] \/ s0a <> []).
              {
              apply nil_not_nil.
              }
            {
            constructor.
            - destruct H20 as [H20 | H20].
              + subst. 
                simpl.
                intros _.
                assert (H5: exists n1: nat, derives6 g n1 [inl n0] (map term_lift [])).
                  {
                  exists n1.
                  exact HH3.
                  }
                rewrite <- derives_equiv_derives6 in H5.
                exact H5.
              + intros. 
                apply map_eq_nil in H0.
                rewrite H0 in H20. 
                destruct H20.
                reflexivity.
            - destruct H20 as [H20 | H20].
              + intros.
                rewrite H20 in H0.
                simpl in H0.
                destruct H0.
                reflexivity.
              + intros.
                assert (H10: n1 <= i).  
                  {
                  omega. 
                  }
              specialize (IHi n1 H10 s0a H20 n0 HH3). 
              exact IHi.
            - exact H1.
            }
          * rewrite map_app. 
            reflexivity.
        + (* terminal *)
          generalize H4.
          change (inr t :: l) with ((map term_lift [t]) ++ l).
          intros H4'. 
          apply derives6_t_list_left in H4'.
          destruct H4' as [s' Hs'].
          rewrite Hs' in H4.
          replace (inr t :: l) with (map term_lift [t] ++ l) in H4; [|reflexivity]. 
          apply derives6_tl_tl in H4.
          generalize Hs'.
          apply map_map_app in Hs'. 
          destruct Hs' as [s'' Hs''].
          rewrite Hs'' in H4.
          specialize (@H0 _ Hi' s'' H4). 
          destruct H0 as [right2' [HH1 HH2]].
          intros.
          exists ([inr t] :: right2').
          simpl.
          rewrite Hs'. 
          unfold terminal_lift. 
          split. 
          * apply sfmatch_term.
            exact HH1.
          * simpl. 
            rewrite Hs''.
            rewrite <- HH2.
            reflexivity.
      }
    clear IHi. 
    destruct H10 as [right2 [HH1 HH2]].
    pose (right':= map (@symbol_lift _ _) (elim_emp right right2)).
    assert (H11: rules (g_emp g) (Lift_nt n) right').
      { 
      apply right_emp_prop. 
      - inversion H. 
        rewrite <- H3. 
        exact H0.
      - exact HH1. 
      - apply flatten_elim_emp with (g:= g). 
        + exact HH1.
        + rewrite HH2. 
          apply map_not_nil_inv. 
          exact H1. 
      }
    apply derives_trans with (s2:= right').
    * apply derives_start. 
      exact H11.
    * (* indução sobre right..., usando [sfmatch] para lidar com não terminais *)
      unfold right'.
      generalize s right2 HH1 HH2. 
      clear s H1 right2 HH1 HH2 right' H11 H4 H0.
      {
      elim right.
      - simpl. 
        intros.
        inversion HH1.
        subst. 
        simpl in HH2.
        inversion HH2.
        constructor.
      - simpl. 
        intros.
        inversion HH1.
        + (* terminal *)
          subst. 
          simpl in HH2.
          destruct s. 
          * inversion HH2.
          * simpl.
            change (inr t :: elim_emp l xxs) with ([inr t]++elim_emp l xxs).
            change (term_lift t0 :: map term_lift s) with ([inr t0]++ map term_lift s).
            inversion HH2.
            rewrite <- H2.
            change ((inr t :: map (symbol_lift (terminal:=terminal)) (elim_emp l xxs))) with (([inr t] ++ map (symbol_lift (terminal:=terminal)) (elim_emp l xxs))).
            change ((inr t :: map (symbol_lift (terminal:=terminal)) (flatten xxs))) with (([inr t] ++ map (symbol_lift (terminal:=terminal)) (flatten xxs))).
            apply derives_context_free_add_left.
            rewrite H3.
            {
            apply H0.
            - exact H4.
            - exact H3.
            }
        + (* non_terminal *)
          destruct p.
          * (* nullable *)
            subst.
            {
            apply H0.
            - exact H6. 
            - exact HH2.
            }
          * (* non-nullable *)
            subst. 
            apply map_expand in HH2.
            destruct HH2 as [sa [sb [Hs [Hs1 Hs2]]]]; subst s.
            rewrite map_app.
            change (inl nt :: elim_emp l xxs) with ([inl nt] ++ elim_emp l xxs).
            repeat rewrite map_app.
            apply derives_combine.
            {
            split. 
            - rewrite Hs1.
              apply H4.
              apply not_eq_sym.
              apply nil_cons.
            - apply H0 with (right2:= xxs) (s:= sb).
              + exact H6.
              + symmetry.
                fold flatten in Hs2.
                exact Hs2.
            }
      }
Qed.

Theorem g_emp_correct: 
forall g: cfg non_terminal terminal,
g_equiv_without_empty (g_emp g) g /\
has_no_empty_rules (g_emp g) /\
start_symbol_not_in_rhs (g_emp g).
Proof.
intro g.
split.
- unfold g_equiv_without_empty.
  intros s H.
  unfold produces.
  unfold generates.
  split.
  + simpl.
    intros H2.
    apply exists_rule in H2.
    destruct H2 as [H2 | H2].
    * {
      inversion H2.
      destruct s.
      - inversion H0.
      - simpl in H0.
        inversion H0.        
      }
    * destruct H2 as [right [H2 H3]].
      inversion H2.
      {
      destruct right.
      - inversion H1.
      - inversion H1.
        destruct s0. 
        + inversion H4.
          subst.
          apply derives_g_emp_g.
          rewrite symbol_lift_equiv_terminal_lift.
          exact H3.
        + inversion H4. 
      }
  + simpl.
    intros H2. 
    apply derives_trans with (s2:= [inl (Lift_nt (start_symbol g))]).
    * apply derives_start.
      apply Lift_start_emp.
    * rewrite <- symbol_lift_equiv_terminal_lift.
      {
      apply derives_g_g_emp.
      - exact H.
      - exact H2.
      }
- split.
  + unfold has_no_empty_rules.
    intros left right H.
    destruct right.
    * {
      inversion H.
      - apply map_eq_nil in H0.
        contradiction.
      - apply map_eq_nil in H0.
        contradiction.
      }
    * apply not_eq_sym.
      apply nil_cons.
  + apply start_symbol_not_in_rhs_g_emp.
Qed.

End EmptyRules_1_Lemmas.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY RULES - DEFINITIONS TO INCLUDE EMPTY STRING    *)
(* --------------------------------------------------------------------- *)

Section EmptyRules_2_Definitions.

Variables non_terminal terminal: Type.

Notation symbol:= (non_terminal + terminal)%type.
Notation symbol':= (non_terminal' + terminal)%type.
Notation nlist:= (list non_terminal).
Notation nlist':= (list (non_terminal' non_terminal)).
Notation tlist:= (list terminal).
Notation sentence := (list terminal).
Notation sf := (list (non_terminal + terminal)).
Notation sf' := (list ((non_terminal' non_terminal) + terminal)).
Notation term_lift:= ((terminal_lift non_terminal) terminal).

Inductive g_emp'_rules (g: cfg _ _): non_terminal' non_terminal -> sf' -> Prop :=
| Lift_all:
       forall left: non_terminal' _,
       forall right: sf',
       rules (g_emp g) left right ->
       g_emp'_rules g left right
| Lift_empty:
       empty g (inl (start_symbol g)) -> g_emp'_rules g (start_symbol (g_emp g)) [].

Lemma in_inl_map_exists:
forall s': non_terminal' _,
forall l: sf,
In (inl s') (map (@symbol_lift _ _) l) ->
exists s: non_terminal,
s' = Lift_nt s /\
In (inl s) l.
Proof.
intros s' l H.
apply in_split in H.
destruct H as [l1 [l2 H]].
symmetry in H.
apply map_expand in H.
destruct H as [s1' [s2' [H1 [H2 H3]]]].
change (inl s' :: l2) with ([inl s'] ++ l2) in H3.
symmetry in H3.
apply map_expand in H3.
destruct H3 as [s1'0 [s2'0 [H4 [H5 H6]]]].
destruct s1'0.
- inversion H5.
- inversion H5.
  destruct s.
  + simpl in H0. 
    inversion H0. 
    exists n.
    split. 
    * reflexivity.
    * rewrite H1. 
      apply in_or_app.
      right.
      rewrite H4.
      apply in_or_app.
      left.
      simpl. 
      left.
      reflexivity.
  + simpl in H0.
    inversion H0.
Qed.

Lemma in_inr_map_exists:
forall s': terminal,
forall l: sf,
In (inr s') (map (@symbol_lift _ _) l) ->
exists s: terminal,
s' = s /\
In (inr s) l.
Proof.
intros s' l H.
apply in_split in H.
destruct H as [l1 [l2 H]].
symmetry in H.
apply map_expand in H.
destruct H as [s1' [s2' [H1 [H2 H3]]]].
change (inr s' :: l2) with ([inr s'] ++ l2) in H3.
symmetry in H3.
apply map_expand in H3.
destruct H3 as [s1'0 [s2'0 [H4 [H5 H6]]]].
destruct s1'0.
- inversion H5.
- inversion H5.
  destruct s.
  + simpl in H0. 
    inversion H0.
  + exists t.
    split. 
    * simpl in H0. 
      inversion H0. 
      reflexivity.
    * simpl in H5.
      inversion H5.
      subst.
      apply in_or_app.
      right.
      simpl. 
      left.
      reflexivity.
Qed.

Lemma in_lift_map:
forall n: non_terminal,
forall ntl: nlist,
In n ntl ->
In (Lift_nt n) (map (@Lift_nt _) ntl).
Proof.
intros n ntl H.
induction ntl.
- simpl in H.
  contradiction.
- simpl. 
  simpl in H.
  destruct H as [H | H].
  + left.
    subst.
    reflexivity.
  + right.
    apply IHntl.
    exact H.
Qed.

Lemma g_emp_length_min:
forall g: cfg _ _,
forall left : non_terminal' _,
forall right : sf',
g_emp_rules g left right ->
length right >= 1.
Proof.
intros g left right H.
inversion H.
- subst. 
  apply not_nil in H0.
  rewrite map_length. 
  omega.
- subst.
  destruct s1, s2.
  + destruct H3.
    reflexivity.
  + subst. 
    simpl. 
    omega.
  + subst. 
    simpl. 
    omega.
  + subst. 
    simpl.
    omega.
- simpl. 
  omega.
Qed.

Lemma g_emp'_finite:
forall g: cfg _ _,
exists n: nat,
exists ntl: nlist',
exists tl: tlist,
In (New_ss _) ntl /\
forall left: non_terminal' _,
forall right: sf',
g_emp'_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal' _, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
intros g.
destruct (rules_finite (g_emp g)) as [n [ntl [tl H1]]].
destruct H1 as [H H1].
exists (S n), (New_ss _ :: ntl), tl.
split.
- simpl; left; reflexivity.
- intros left right H2.
  inversion H2.
  + subst. 
    specialize (H1 left right H0).
    destruct H1 as [H3 [H4 H5]].
    split. 
    * omega.
    * {
      split.
      - apply in_cons.
        exact H4.
      - split.
        + destruct H5 as [H5 _].
          intros s' H6.
          apply in_cons.
          apply H5.
          exact H6.
        + destruct H5 as [_ H5].
          intros s H6.
          apply H5.
          exact H6.
      } 
  + subst.
    split.
    * simpl. 
      omega.
    * {
      split. 
      - simpl. 
        left. 
        reflexivity.
      - split.
        + intros s H3.
          simpl in H3.
          contradiction.
        + intros s H3.
          simpl in H3.
          contradiction.
      }
Qed.

Definition g_emp' (g: cfg non_terminal terminal): cfg (non_terminal' _) terminal := {|
start_symbol:= New_ss _;
rules:= g_emp'_rules g;
rules_finite:= g_emp'_finite g
|}.

Definition New_ss_not_in_sf (s: sf'): Prop:=
~ In (inl (New_ss _)) s.

Definition New_ss_not_in_sflist (l': list sf'): Prop:=
forall s': sf',
In s' l' ->
New_ss_not_in_sf s'.

End EmptyRules_2_Definitions.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY RULES - LEMMAS TO INCLUDE EMPTY STRING         *)
(* --------------------------------------------------------------------- *)

Section EmptyRules_2_Lemmas.

Variables non_terminal terminal: Type.

Notation symbol:= (non_terminal + terminal)%type.
Notation symbol':= ((non_terminal' _) + terminal)%type.
Notation nlist:= (list non_terminal).
Notation nlist':= (list (non_terminal' non_terminal)).
Notation tlist:= (list terminal).
Notation sentence := (list terminal).
Notation sf := (list (non_terminal + terminal)).
Notation sf' := (list ((non_terminal' non_terminal) + terminal)).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation term_lift':= ((terminal_lift (non_terminal' non_terminal)) terminal).

Lemma start_symbol_not_in_rhs_g_emp': 
forall g: cfg non_terminal terminal,
start_symbol_not_in_rhs (g_emp' g).
Proof.
intros g.
unfold start_symbol_not_in_rhs.
intros left right H1 H2.
simpl in H2. 
inversion H1. 
- subst.
  assert (H3: start_symbol_not_in_rhs (g_emp g)).
    {
    apply start_symbol_not_in_rhs_g_emp.
    }
  specialize (H3 left right H).
  apply H3.
  simpl.
  exact H2.
- subst.
  simpl in H2.
  contradiction.
Qed.

Lemma New_ss_not_in_right_g_emp'_v1:
forall g: cfg _ _,
forall left: non_terminal' _,
forall s1 s2: sf',
~ rules (g_emp' g) left (s1 ++ [inl (start_symbol (g_emp' g))] ++ s2).
Proof.
intros g left s1 s2 H.
inversion H.
clear H.
- simpl in H0.  
  assert (H3: start_symbol_not_in_rhs (g_emp g)).
    {
    apply start_symbol_not_in_rhs_g_emp.
    }
  specialize (H3 left (s1 ++ inl (New_ss non_terminal) :: s2) H0).
  apply H3.
  simpl. 
  apply in_or_app.
  right. 
  simpl. 
  left.
  reflexivity.
- destruct s1.
  + inversion H0.
  + inversion H0.
Qed.

Lemma New_ss_not_in_right_g_emp'_v2:
forall g: cfg _ _,
forall left: non_terminal' _,
forall right: sf',
rules (g_emp' g) left right ->
New_ss_not_in_sf right.
Proof.
intros g left right H1 H2.
apply in_split in H2.
destruct H2 as [l1 [l2 H3]].
rewrite H3 in H1.
change ((l1 ++ inl (New_ss _) :: l2)) with ((l1 ++ [inl (New_ss _)] ++ l2)) in H1.
apply New_ss_not_in_right_g_emp'_v1 in H1.
contradiction.
Qed.

Lemma hd_lift_equiv_lift_hd:
forall l: list sf,
hd [] (sf_list_lift l) = sf_lift (hd [] l).
Proof.
destruct l.
- simpl. 
  reflexivity.
- simpl. 
  reflexivity.
Qed.

Lemma last_lift_equiv_lift_last:
forall l: list sf,
last (sf_list_lift l) [] = sf_lift (last l []).
Proof.
induction l.
- simpl. 
  reflexivity.
- simpl sf_list_lift.
  assert (H: l = [] \/ l <> []).
    {
    apply nil_not_nil.
    }
  destruct H as [H | H].
  + subst.
    simpl. 
    reflexivity.
  + assert (H2: sf_list_lift l <> []).
      {
      destruct l.
      - destruct H.
        reflexivity.
      - simpl. 
        apply not_eq_sym.
        apply nil_cons.
      }
    repeat rewrite last_cons.
    * exact IHl.
    * exact H.
    * exact H2.
Qed.

Lemma map_lift_equiv_lift_map:
forall s: sentence,
sf_lift (map term_lift s) =
map term_lift' s.
Proof.
intros s.
induction s.
- simpl. 
  reflexivity.
- simpl map.
  simpl sf_lift. 
  change (term_lift' a) with (@inr (non_terminal' non_terminal) terminal a).
  apply app_eq.
  exact IHs.
Qed.

Lemma sf_lift_app_distrib:
forall s1 s2: sf,
sf_lift (s1 ++ s2) = sf_lift s1 ++ sf_lift s2.
Proof.
induction s1.
- intros s2.
  simpl. 
  reflexivity.
- intros s2.
  simpl. 
  apply app_eq.
  apply IHs1.
Qed.

Lemma sf_lift_eq_nil:
forall l: sf,
sf_lift l = [] -> l = [].
Proof.
destruct l.
- simpl. 
  auto.
- simpl. 
  intros H.
  change (symbol_lift s :: sf_lift l) with ([symbol_lift s] ++ sf_lift l) in H.
  apply app_eq_nil in H.
  destruct H as [H _].
  inversion H.
Qed.

Lemma sf_list_lift_eq_nil:
forall l: list sf,
sf_list_lift l = [] -> l = [].
Proof.
destruct l.
- simpl. 
  auto.
- simpl. 
  intros H.
  change (sf_lift l :: sf_list_lift l0) with ([sf_lift l] ++ sf_list_lift l0) in H.
  apply app_eq_nil in H.
  destruct H as [H _].
  inversion H.
Qed.

Lemma symbol_lift_eq:
forall a b: symbol,
symbol_lift a = symbol_lift b ->
a = b.
Proof.
intros a b H.
destruct a, b.
- simpl in H.
  inversion H.
  reflexivity. 
- simpl in H. 
  inversion H.
- simpl in H. 
  inversion H.
- simpl in H.
  inversion H.
  reflexivity. 
Qed.

Lemma sf_lift_eq:
forall l1 l2: sf,
sf_lift l1 = sf_lift l2 ->
l1 = l2.
Proof.
induction l1.
- intros l2 H. 
  simpl in H. 
  symmetry in H. 
  apply sf_lift_eq_nil in H. 
  symmetry. 
  assumption. 
- intros l2 H.
  simpl in H.
  destruct l2.
  + inversion H.
  + simpl in H.
    inversion H.
    specialize (IHl1 l2 H2).
    rewrite IHl1.
    apply symbol_lift_eq with (b:= s) in H1.
    rewrite H1.
    reflexivity.
Qed.

Lemma sf_list_lift_eq:
forall l1 l2: list sf,
sf_list_lift l1 = sf_list_lift l2 ->
l1 = l2.
Proof.
induction l1, l2.
- auto. 
- simpl.
  intros H.
  symmetry in H.
  change (sf_lift l :: sf_list_lift l2) with ([sf_lift l] ++ sf_list_lift l2) in H.
  apply app_eq_nil in H. 
  destruct H as [H1 _]. 
  inversion H1.
- simpl.
  intros H.
  change (sf_lift a :: sf_list_lift l1) with ([sf_lift a] ++ sf_list_lift l1) in H.
  apply app_eq_nil in H. 
  destruct H as [H1 _]. 
  inversion H1.
- intros H.
  simpl in H.
  inversion H. 
  specialize (IHl1 l2 H2).
  rewrite IHl1.
  apply sf_lift_eq in H1.
  rewrite H1.
  reflexivity.
Qed.

Lemma derives_g_emp'_or:
forall g: cfg _ _,
forall s: sentence,
derives (g_emp' g) [inl (start_symbol (g_emp' g))] (map term_lift' s) ->
s = [] \/
derives (g_emp' g) [inl (start_symbol (g_emp g))] (map term_lift' s).
Proof.
intros g s H.
destruct s.
- left.
  reflexivity.
- right.
  apply exists_rule in H.
  destruct H.
  + inversion H.
    inversion H0.
  + destruct H as [right [H1 H2]].
    inversion H1.
    * subst.
      { 
      apply derives_trans with (s2:= right).
      - apply derives_start.
        exact H1.
      - exact H2. 
      }
    * subst.
      {
      apply not_derives in H2.
      - contradiction.
      - simpl. 
        apply not_eq_sym. 
        apply nil_cons. 
      }
Qed.

Lemma derives_g_emp'_empty:
forall g: cfg non_terminal terminal,
derives (g_emp' g) [inl (start_symbol (g_emp' g))] [] ->
rules (g_emp' g) (start_symbol (g_emp' g)) [].
Proof.
intros g H.
change [] with (map term_lift' []) in H.
apply exists_rule in H.
destruct H as [H | H].
- exact H.
- destruct H as [right [H1 H2]].
  inversion H2.
  + simpl in H0. 
    subst.
    exact H1.
  + apply app_eq_nil in H.
    destruct H as [H H5].
    apply app_eq_nil in H5.
    destruct H5 as [H5 H6].
    subst.
    simpl.
    inversion H4.
    * subst.
      apply g_emp_has_no_empty_rules in H.
      destruct H.
      reflexivity.
    * apply Lift_empty. 
      exact H.
Qed.

Lemma hd_lift_hd:
forall n: non_terminal,
forall l': list sf',
forall l: list sf,
hd [] l' = [inl (Lift_nt n)] ->
l' = sf_list_lift l ->
hd [] l = [inl n].
Proof.
intros n l' l H1 H2.
rewrite H2 in H1.
rewrite hd_lift_equiv_lift_hd in H1.
change [inl (Lift_nt n)] with (sf_lift ([inl terminal n])) in H1.
apply sf_lift_eq in H1.
exact H1.
Qed.  

Lemma last_lift_last:
forall l': list sf',
forall l: list sf,
forall s: sentence,
last l' [] = map term_lift' s ->
l' = sf_list_lift l ->
last l [] = map term_lift s.
Proof.
intros l' l s H1 H2.
rewrite H2 in H1.
clear H2 l'.
rewrite last_lift_equiv_lift_last in H1.
rewrite <- map_lift_equiv_lift_map in H1.
apply sf_lift_eq in H1.
exact H1.
Qed.

Lemma New_ss_not_in_sf_cat:
forall l1 l2: sf',
New_ss_not_in_sf l1 ->
New_ss_not_in_sf l2 ->
New_ss_not_in_sf (l1 ++ l2).
Proof.
intros l1.
destruct l1.
- intros l2 H1 H2.
  simpl. 
  exact H2.
- intros l2 H1 H2.
  unfold New_ss_not_in_sf.
  intros H3. 
  apply in_app_or in H3.
  destruct H3 as [H3 | H3].
  + specialize (H1 H3).
    contradiction.
  + specialize (H2 H3).
    contradiction.
Qed.

Lemma New_ss_not_in_sf_split:
forall l1 l2: sf',
New_ss_not_in_sf (l1 ++ l2) ->
New_ss_not_in_sf l1 /\
New_ss_not_in_sf l2.
Proof.
intros l1.
destruct l1.
- intros l2 H.
  split.
  + unfold New_ss_not_in_sf.
    simpl.
    auto.
  + exact H.
- intros l2 H1.
  split.
  + intros H2. 
    unfold New_ss_not_in_sf in H1.
    simpl in H1.
    apply H1.
    change (s :: l1) with ([s] ++ l1) in H2.
    apply in_app_or in H2.
    destruct H2 as [H2 | H2].
    * left.
      simpl in H2. 
      {
      destruct H2 as [H2 | H2].
      - exact H2.
      - contradiction.
      }
    * right.
      apply in_or_app.
      left.
      exact H2.
  + unfold New_ss_not_in_sf in H1. 
    unfold New_ss_not_in_sf.
    intros H2.
    apply H1.
    apply in_or_app.
    right.
    exact H2.
Qed.

Lemma New_ss_not_in_sflist_cat:
forall l1 l2: list sf',
New_ss_not_in_sflist l1 ->
New_ss_not_in_sflist l2 ->
New_ss_not_in_sflist (l1 ++ l2).
Proof.
intros l1.
destruct l1.
- intros l2 H1 H2.
  simpl. 
  exact H2.
- intros l2 H1 H2.
  unfold New_ss_not_in_sflist.
  intros s' H3. 
  apply in_app_or in H3.
  destruct H3 as [H3 | H3].
  + specialize (H1 s' H3).
    exact H1.
  + specialize (H2 s' H3).
    exact H2.
Qed.

Lemma New_ss_not_in_sflist_split:
forall l1 l2: list sf',
New_ss_not_in_sflist (l1 ++ l2) ->
New_ss_not_in_sflist l1 /\
New_ss_not_in_sflist l2.
Proof.
intros l1.
destruct l1.
- intros l2 H.
  split.
  + unfold New_ss_not_in_sflist.
    intros s' H1.
    simpl in H1.
    contradiction.
  + exact H.
- intros l2 H1.
  split.
  + intros s' H2. 
    unfold New_ss_not_in_sflist in H1.
    simpl in H1.
    apply H1.
    change (l :: l1) with ([l] ++ l1) in H2.
    apply in_app_or in H2.
    destruct H2 as [H2 | H2].
    * left.
      simpl in H2. 
      {
      destruct H2 as [H2 | H2].
      - exact H2.
      - contradiction.
      }
    * right.
      apply in_or_app.
      left.
      exact H2.
  + unfold New_ss_not_in_sflist in H1. 
    unfold New_ss_not_in_sflist.
    intros s' H2.
    apply H1.
    apply in_or_app.
    right.
    exact H2.
Qed.

Lemma New_ss_not_in_map:
forall s: sf,
New_ss_not_in_sf (sf_lift s).
Proof.
intros s.
induction s.
- simpl.
  unfold New_ss_not_in_sf.
  simpl.
  auto.
- simpl.
  unfold New_ss_not_in_sf.
  intros H.
  change (symbol_lift a :: sf_lift s) with ([symbol_lift a] ++ sf_lift s) in H.
  apply in_app_or in H.
  destruct H as [H | H].
  + simpl in H.
    destruct H as [H | H].
    * {
      destruct a.
      - simpl in H.
        discriminate H.
      - simpl in H.
        inversion H.
      }
    * contradiction.
  + apply IHs.
    exact H. 
Qed.

Lemma sf_lift_cat:
forall l: sf,
forall l1 l2: sf',
sf_lift l = l1 ++ l2 ->
exists l1' l2',
l = l1' ++ l2' /\
l1 = sf_lift l1' /\
l2 = sf_lift l2'.
Proof.
induction l, l1.
- intros l2 H.
  exists [], [].
  auto. 
- intros l2 H.
  simpl in H.
  inversion H.
- intros l2 H. 
  simpl in H.
  destruct l2. 
  + inversion H.
  + inversion H.
    specialize (IHl [] l2 H2).
    destruct IHl as [l1' [l2' [H3 [H4 H5]]]].
    exists [], (a :: l).
    split.
    * reflexivity.
    * {
      split. 
      - reflexivity.
      - simpl.
        reflexivity.
      }
- intros l2 H.
  simpl in H.
  inversion H.
  specialize (IHl l1 l2 H2).
  destruct IHl as [l1' [l2' [H3 [H4 H5]]]].
  exists (a :: l1'), l2'.
  split.
  + rewrite H3.
    reflexivity.
  + split.
    * simpl.
      rewrite H4.
      reflexivity.
    * exact H5.
Qed.

Lemma sf_lift_eq_nt:
forall l: sf,
forall a: non_terminal' _,
sf_lift l = [inl a] ->
exists b: non_terminal,
l = [inl b].
Proof.
intros l a H.
destruct l.
- simpl in H.
  inversion H.
- simpl in H.
  inversion H.
  apply sf_lift_eq_nil in H2.
  rewrite H2.
  destruct s. 
  + exists n.
    reflexivity.
  + inversion H1.
Qed.

Lemma sflist_g_emp_g_emp':
forall g: cfg non_terminal terminal,
forall l: _,
sflist (g_emp g) l ->
sflist (g_emp' g) l.
Proof.
intros g l. 
induction l.
- intros H. 
  simpl.
  apply sflist_empty.
- intros H.
  assert (H':= H).
  apply sflist_tail in H.
  simpl in H.
  specialize (IHl H).
  simpl.
  rewrite sflist_equiv_sflist6.
  change (a :: l) with ([a] ++ l).
  destruct l.
  + simpl. 
    apply sflist6_start.
  + apply sflist6_step with (s2:= l).
    * rewrite sflist_equiv_sflist6 in IHl. 
      exact IHl. 
    * simpl. 
      reflexivity.
    * rewrite sflist_equiv_sflist6 in H'.
      inversion H'.
      simpl in H3.
      rewrite <- H3 in H4.
      clear H0 H1 H2 H3.
      unfold derives_direct in H4.
      destruct H4 as [s' [s'' [left [right [H6 [H7 H8]]]]]].
      unfold derives_direct.
      exists s'.
      exists s''.
      exists left.
      exists right.
      {
      split.
      - rewrite H6.
        reflexivity.
      - split. 
        + rewrite H7.
          reflexivity.
        + apply Lift_all.
          exact H8.
      }
Qed.

Lemma New_ss_not_in_rhs:
forall g: cfg non_terminal terminal,
forall s1 s2: sf',
s1 ++ s2 <> [] ->
~ derives (g_emp' g) [inl (start_symbol (g_emp' g))] (s1 ++ inl (start_symbol (g_emp' g)) :: s2).
Proof.
intros g.
assert (H: start_symbol_not_in_rhs (g_emp' g)).
  {
  apply start_symbol_not_in_rhs_g_emp'.
  }
intros s1 s2 H1 H2.
apply exists_rule' in H2.
destruct H2 as [H2 | H2].
- destruct H2 as [_ [H3 H4]].
  subst.
  destruct H1.
  reflexivity.
- destruct H2 as [left [right [H3 H4]]].
  specialize (H left right H3).
  simpl in H.
  contradiction.
Qed.

Lemma g_emp_equiv_g_emp'_aux_1:
forall g: cfg _ _,
forall s: sf',
s <> [] ->
derives (g_emp' g) [inl (start_symbol (g_emp' g))] s ->
derives (g_emp g) [inl (start_symbol (g_emp g))] s.
Proof.
simpl.
intros g s H1 H2.
remember [inl (New_ss non_terminal)] as w.
induction H2.
- apply derives_refl.
- apply derives_trans with (s2:= (s2 ++ inl left :: s3)).
  + apply IHderives.
    * apply not_eq_sym.
      apply app_cons_not_nil.
    * exact Heqw.
  + inversion H. 
    * apply derives_rule.
      exact H0.
    * subst.
      simpl in H2.
      {
      apply New_ss_not_in_rhs in H2. 
      - contradiction.
      - exact H1.
      }
Qed.

Lemma g_emp_equiv_g_emp'_aux_2:
forall g: cfg _ _,
forall s: sf',
derives (g_emp g) [inl (start_symbol (g_emp g))] s ->
derives (g_emp' g) [inl (start_symbol (g_emp' g))] s.
Proof.
simpl.
intros g s H.
remember [inl (New_ss non_terminal)] as w1. 
induction H.
- apply derives_refl.
- apply derives_trans with (s2:= (s2 ++ inl left :: s3)).
  + apply IHderives.
    exact Heqw1.
  + apply derives_rule.
    apply Lift_all.
    exact H0.
Qed.

Lemma g_emp_equiv_g_emp':
forall g: cfg _ _,
forall s: sentence,
(s <> [] -> 
 derives (g_emp' g) [inl (start_symbol (g_emp' g))] (map term_lift' s) ->
 derives (g_emp  g) [inl (start_symbol (g_emp  g))] (map term_lift' s)) 
/\
(derives (g_emp  g) [inl (start_symbol (g_emp  g))] (map term_lift' s) ->
 derives (g_emp' g) [inl (start_symbol (g_emp' g))] (map term_lift' s)).
Proof.
intros g s.
split.
- intros H1 H2. 
  apply derives_g_emp'_or in H2.
  destruct H2 as [H2 | H2].
  + subst.
    destruct H1.
    reflexivity.
  + apply g_emp_equiv_g_emp'_aux_1.
    * apply map_not_nil_inv. 
      exact H1.
    * exact H2.
- intros H.
  apply g_emp_equiv_g_emp'_aux_2.
  exact H.
Qed.

Lemma lift_terminal_lift:
forall s: sentence,
sf_lift (map term_lift s) = map term_lift' s.
Proof.
intros s.
induction s.
-simpl. 
 reflexivity.
- simpl.
  apply app_eq.
  exact IHs.
Qed.

Lemma g_emp'_has_one_empty_rule:
forall g: cfg non_terminal terminal,
generates_empty g -> has_one_empty_rule (g_emp' g).
Proof.
unfold generates_empty.
intros g H1.
unfold has_one_empty_rule.
intros left right H2.
inversion H2.
- subst.
  right.
  apply g_emp_has_no_empty_rules in H.
  exact H.
- left.
  subst.
  simpl.
  auto.
Qed.

Lemma g_emp'_has_no_empty_rules:
forall g: cfg non_terminal terminal,
~ generates_empty g -> has_no_empty_rules (g_emp' g).
Proof.
unfold generates_empty.
intros g H.
intros left right H1.
inversion H1.
- inversion H0.
  + apply map_not_nil_inv.
    exact H4.
  + apply map_not_nil_inv.
    exact H7.
  + apply not_eq_sym.
    apply nil_cons.
- subst.
  contradiction.
Qed.

Theorem g_emp'_correct: 
forall g: cfg non_terminal terminal,
g_equiv (g_emp' g) g /\
(generates_empty g -> has_one_empty_rule (g_emp' g)) /\ 
(~ generates_empty g -> has_no_empty_rules (g_emp' g)) /\
start_symbol_not_in_rhs (g_emp' g).
Proof.
intros g.
split.
- unfold g_equiv.
  intros s.
  unfold produces.
  unfold generates.
  split.
  + intros H.
    assert (H0: s = [] \/ s <> []). 
      {
      apply nil_not_nil.
      }
    destruct H0 as [H0 | H0].
    * subst.
      inversion H.
      apply app_eq_nil in H0.
      destruct H0 as [_ H0].
      apply app_eq_nil in H0.
      destruct H0 as [H0 _].
      subst.
      {
      inversion H3.
      - apply g_emp_has_no_empty_rules in H0.
        destruct H0.
        reflexivity.
      - exact H0.
      }
    * {
      apply g_emp_equiv_g_emp' in H.
      - apply derives_g_emp_g.
        apply exists_rule in H.
        destruct H as [H | H].
        + simpl in H.
          inversion H. 
          destruct s. 
          * inversion H1.
          * inversion H1. 
        + destruct H as [right [H1 H2]].  
          inversion H1. 
          destruct right.
          * inversion H3.
          * inversion H3.
            subst.
            rewrite symbol_lift_equiv_terminal_lift.
            exact H2.
      - exact H0.
      }
  + intros H.
    assert (H0: s = [] \/ s <> []). 
      {
      apply nil_not_nil.
      }
    destruct H0 as [H0 | H0].
    * subst.
      simpl.
      apply derives_start.
      apply Lift_empty.
      exact H.
    * {
      apply derives_g_g_emp in H.
      - apply g_emp_equiv_g_emp'.
        simpl.
        apply derives_trans with (s2:= [inl (Lift_nt (start_symbol g))]).
        + apply derives_start.
          apply Lift_start_emp.
        + rewrite symbol_lift_equiv_terminal_lift in H.
          exact H.
      - exact H0.
      }
- split.
  + (* g does generate empty *)
    apply g_emp'_has_one_empty_rule.
  + split. 
    * (* g does not generate empty *)
      apply g_emp'_has_no_empty_rules.
    * apply start_symbol_not_in_rhs_g_emp'.
Qed.

Variables non_terminal' non_terminal'': Type.

Lemma remove_empty:
forall g1: cfg non_terminal' terminal,
forall g2: cfg non_terminal'' terminal,
g_equiv g1 g2 ->
g_equiv_without_empty g1 g2.
Proof.
intros g1 g2 H1.
unfold g_equiv in H1.
unfold g_equiv_without_empty.
intros s H2.
apply H1.
Qed.

End EmptyRules_2_Lemmas.

Section EmptyRules_3_Lemmas.

Variables non_terminal terminal: Type.

Lemma no_empty_rules_no_empty:
forall g: cfg non_terminal terminal,
has_no_empty_rules g ->
~ derives g [inl (start_symbol g)] [].
Proof.
intros g H1 H2.
unfold has_no_empty_rules in H1.
inversion H2.
apply app_eq_nil in H.
destruct H as [_ H].
apply app_eq_nil in H.
destruct H as [H _].
subst.
specialize (H1 left [] H4).
destruct H1.
reflexivity.
Qed.

End EmptyRules_3_Lemmas.

Section EmptyRules_4_Lemmas.

Variables non_terminal non_terminal' non_terminal'' terminal: Type.

Notation sf:= (list (non_terminal + terminal))%type.

Lemma with_without_empty:
forall g1: cfg non_terminal' terminal,
forall g2: cfg non_terminal'' terminal,
has_no_empty_rules g1 ->
has_no_empty_rules g2 ->
(g_equiv g1 g2 <-> g_equiv_without_empty g1 g2).
Proof.
intros g1 g2 H1 H2.
split.
- intros H3.
  apply remove_empty.
  exact H3.
- intros H3.
  unfold g_equiv_without_empty in H3.
  unfold g_equiv.
  intros s.
  unfold produces.
  unfold generates.
  destruct s.
  + split.
    * intros H4.
      apply no_empty_rules_no_empty in H1.
      specialize (H1 H4).
      contradiction.
    * intros H4.
      apply no_empty_rules_no_empty in H2.
      specialize (H2 H4).
      contradiction.
  + apply H3.
    apply not_eq_sym.
    apply nil_cons. 
Qed.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY RULES - ALTERNATIVE DEFINITION                 *)
(* --------------------------------------------------------------------- *)

Inductive nullable (g: cfg non_terminal terminal): list (non_terminal + terminal) -> Prop:=
| null_1: forall left: non_terminal,
          rules g left [] -> nullable g [inl left]
| null_2: forall left: non_terminal,
          forall right: sf,
          rules g left right ->
          nullable g right -> nullable g ((inl left) :: right).

Inductive empty' (g: cfg non_terminal terminal): non_terminal -> Prop:=
| empty'_rule n: rules g n [] -> empty' g n
| empty'_step: forall left: non_terminal,
               forall right: sf,
               rules g left right ->
               empty'_list g right -> empty' g left
with empty'_list (g: cfg non_terminal terminal): sf -> Prop:=
| empty'_list_1: empty'_list g []
| empty'_list_2: forall s: sf,
                 forall n: non_terminal,
                 empty'_list g s ->
                 empty' g n ->
                 empty'_list g (inl n :: s). 

Scheme empty'_ind2:=
Minimality for empty' Sort Prop
with empty'_list_ind2:=
Minimality for empty'_list Sort Prop.

Inductive empty'' (g: cfg non_terminal terminal): non_terminal + terminal -> Prop:=
| empty_direct: forall left: non_terminal,   
                rules g left [] -> empty'' g (inl left)
| empty_step: forall left: non_terminal,
              forall right: sf,
              rules g left right ->
              (forall s: non_terminal + terminal, In s right -> empty'' g s) ->
              empty'' g (inl left).

Lemma empty_equiv_empty':
forall g: cfg _ _,
forall n: non_terminal,
empty g (inl n) -> empty' g n.
Proof.
intros g n H.
unfold empty in H.
remember [inl n] as w1.
remember [] as w2.
rewrite Heqw2 in Heqw1.
revert Heqw2.
revert Heqw1.
revert n.
induction H.
- admit. (* eee *)
- admit. (* eee *)
Qed.

Lemma empty'_equiv_empty:
forall g: cfg _ _,
forall n: non_terminal,
empty' g n -> empty g (inl n).
Proof.
intros g n H.
induction H using empty'_ind2 with
(P:= fun n: non_terminal => derives g [inl n] [])
(P0:= fun s: sf => derives g s []).
- apply derives_start.
  exact H.
- apply derives_trans with (s2:= right).
  + apply derives_start.
    exact H.
  + exact IHempty'.
- apply derives_refl.
- rewrite <- app_nil_r.
  change (inl n :: s) with ([inl n] ++ s).
  apply derives_combine.
  split. 
  + exact IHempty'0.
  + exact IHempty'.
Qed.

Lemma empty_empty':
forall g: cfg _ _,
forall n: non_terminal,
empty g (inl n) <-> empty' g n.
Proof.
intros g n.
split.
- apply empty_equiv_empty'.
- apply empty'_equiv_empty.
Qed.

Lemma empty_equiv_empty'':
forall g: cfg _ _,
forall n: non_terminal,
empty g (inl n) -> empty'' g (inl n).
Proof.
intros g n H.
unfold empty in H.
remember [inl n] as w1.
remember [] as w2.
rewrite Heqw2 in Heqw1.
revert Heqw2.
revert Heqw1.
revert n.
induction H.
- intros n H1 H2.
  subst.
  inversion H2.
- intros n H1 H2.
  admit. (* eee *)
 Qed.

Lemma empty''_equiv_empty:
forall g: cfg _ _,
forall n: non_terminal,
empty'' g (inl n) -> empty g (inl n).
Proof.
intros g n H.
induction H.
- apply derives_start. 
  exact H.
- apply derives_trans with (s2:= right).
  + apply derives_start.
    exact H.
  + clear left n H H0.
    revert H1.
    induction right.
    * intros _. 
      apply derives_refl.
    * intros H.
      change (a :: right) with ([a] ++ right).
      rewrite <- app_nil_r.
      apply derives_combine.
      {   
      split.
      - specialize (H a).
        assert (H2: empty g a).
          {
          apply H.
          simpl.
          left.
          reflexivity.
          }
        exact H2.
      - apply IHright.
        intros s H1.
        apply H.
        simpl. 
        right. 
        exact H1.
      }
Qed.

Lemma empty_empty'':
forall g: cfg _ _,
forall n: non_terminal,
empty g (inl n) <-> empty'' g (inl n).
Proof.
intros g n.
split.
- apply empty_equiv_empty''.
- apply empty''_equiv_empty.
Qed.

(* --------------------------------------------------------------------- *)
(* DECIDABILITY                                                          *)
(* --------------------------------------------------------------------- *)

Lemma empty_dec:
forall g: cfg non_terminal terminal,
forall n: non_terminal,
empty g (inl n) \/ ~ empty g (inl n).
Proof.
intros g n.
destruct g.
admit. (* eee *)
Qed.

Lemma empty_rule_dec:
forall g: cfg non_terminal terminal,
(rules (g_emp' g) (start_symbol (g_emp' g)) []) \/ (~ rules (g_emp' g) (start_symbol (g_emp' g)) []).
Proof.
intros g.
destruct (g_emp' g).
destruct rules_finite as [n [ntl [tl rdf]]].
unfold rules_finite_def in rdf.
admit. (* eee *)
Qed.

Lemma produces_empty_dec:
forall g: cfg non_terminal terminal,
(produces_empty g) \/ (~ produces_empty g).
Proof.
intros g.
assert (H: g_equiv (g_emp' g) g).
  {
  apply g_emp'_correct.
  }
assert (H1: (rules (g_emp' g) (start_symbol (g_emp' g)) []) \/ (~ rules (g_emp' g) (start_symbol (g_emp' g)) [])).
  { 
  apply empty_rule_dec.
  }
destruct H1 as [H1 | H1].
- left. 
  assert (H2: produces (g_emp' g) []). 
    {
    apply derives_start.
    exact H1.
    }
  apply H.
  exact H2.
- right.
  intros H2.
  specialize (H []).
  unfold produces_empty in H2.
  destruct H as [_ H].
  specialize (H H2).
  clear H2.
  apply derives_g_emp'_empty in H.
  contradiction.
Qed.

Lemma produces_non_empty_dec:
forall g: cfg non_terminal terminal,
(produces_non_empty g) + (~ produces_non_empty g).
Proof.
admit. (* eee *)
Qed.

Lemma non_empty_dec:
forall g: cfg non_terminal terminal,
(non_empty g) + (~ non_empty g).
Proof.
admit. (* eee *)
Qed.

End EmptyRules_4_Lemmas.
