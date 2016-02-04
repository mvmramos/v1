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
(* EXAMPLE FOR SECTION 6.5.1                                             *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.
Require Import union.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

Inductive non_terminal1: Type:=
| S1 
| X1.

Inductive non_terminal2: Type:=
| S2 
| X2.

Inductive terminal: Type:=
| a
| b
| c.

Inductive rs1: non_terminal1 -> list (non_terminal1 + terminal) -> Prop:=
| r11: rs1 S1 [inr a; inl X1]
| r12: rs1 X1 [inr a; inl X1]
| r13: rs1 X1 [inr b].

Lemma rs1_finite: 
exists n: nat,
exists ntl: list non_terminal1,
exists tl: list terminal,
In S1 ntl /\
forall left: non_terminal1,
forall right: list (non_terminal1 + terminal),
rs1 left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal1, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
exists 2, [S1;X1], [a;b;c].
split.
- simpl. auto.
- intros left right H.
  split.
  inversion H.
  + simpl. auto.
  + simpl. auto.
  + simpl. auto. 
  + split. 
    inversion H.
    * simpl. auto.
    * simpl. auto. 
    * simpl. auto. 
    * {
      split.
      - intros s H1.
        inversion H.
        + subst.
          simpl in H1.
          destruct H1 as [H1 | [H1 | H1]].
          * inversion H1.
          * inversion H1.
            simpl. auto.
          * contradiction. 
        + subst.
          simpl in H1.
          destruct H1 as [H1 | [H1 | H1]].
          * inversion H1.
          * inversion H1.
            simpl. auto.
          * contradiction. 
        + subst.
          simpl in H1.
          destruct H1 as [H1 | H1].
          * inversion H1.
          * contradiction.
      - intros s H1.
        inversion H.
        + subst.
          simpl in H1.
          destruct H1 as [H1 | [H1 | H1]].
          * inversion H1.
            simpl. auto.
          * inversion H1.
          * contradiction. 
        + subst.
          simpl in H1.
          destruct H1 as [H1 | [H1 | H1]].
          * inversion H1.
            simpl. auto.
          * inversion H1.
          * contradiction. 
        + subst.
          simpl in H1.
          destruct H1 as [H1 | H1].
          * inversion H1.
            simpl. right. left. reflexivity.
          * contradiction.
      }
Qed.

Definition g1: cfg non_terminal1 terminal := {|
start_symbol:= S1;
rules:= rs1;
rules_finite:= rs1_finite |}.

Inductive rs2: non_terminal2 -> list (non_terminal2 + terminal) -> Prop:=
| r21: rs2 S2 [inr a; inl X2]
| r22: rs2 X2 [inr a; inl X2]
| r23: rs2 X2 [inr c].

Lemma rs2_finite: 
exists n: nat,
exists ntl: list non_terminal2,
exists tl: list terminal,
In S2 ntl /\
forall left: non_terminal2,
forall right: list (non_terminal2 + terminal),
rs2 left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal2, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
exists 2, [S2;X2], [a;b;c].
split.
- simpl. auto.
- intros left right H.
  split.
  inversion H.
  + simpl. auto.
  + simpl. auto.
  + simpl. auto. 
  + split. 
    inversion H.
    * simpl. auto.
    * simpl. auto. 
    * simpl. auto. 
    * {
      split.
      - intros s H1.
        inversion H.
        + subst.
          simpl in H1.
          destruct H1 as [H1 | [H1 | H1]].
          * inversion H1.
          * inversion H1.
            simpl. auto.
          * contradiction. 
        + subst.
          simpl in H1.
          destruct H1 as [H1 | [H1 | H1]].
          * inversion H1.
          * inversion H1.
            simpl. auto.
          * contradiction. 
        + subst.
          simpl in H1.
          destruct H1 as [H1 | H1].
          * inversion H1.
          * contradiction.
      - intros s H1.
        inversion H.
        + subst.
          simpl in H1.
          destruct H1 as [H1 | [H1 | H1]].
          * inversion H1.
            simpl. auto.
          * inversion H1.
          * contradiction. 
        + subst.
          simpl in H1.
          destruct H1 as [H1 | [H1 | H1]].
          * inversion H1.
            simpl. auto.
          * inversion H1.
          * contradiction. 
        + subst.
          simpl in H1.
          destruct H1 as [H1 | H1].
          * inversion H1.
            simpl. right. right. left. reflexivity.
          * contradiction.
      }
Qed.

Definition g2: cfg non_terminal2 terminal := {|
start_symbol:= S2;
rules:= rs2;
rules_finite:= rs2_finite |}.

Definition g3:= g_uni g1 g2.
