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
(* EXAMPLE FOR SECTION 6.2.2                                             *)
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

Inductive nt: Type:= | S' | A | B.
Inductive t: Type:= | a | b.
Inductive rs: nt -> list (nt + t) -> Prop:=
  r1: rs S' [inr a; inl S']
| r2: rs S' [inr b].

Notation sf:= (list (nt + t)).
Notation nlist:= (list nt).
Notation tlist:= (list t).

Lemma rs_finite:
exists n: nat,
exists ntl: nlist,
exists tl: tlist,
In S' ntl /\
forall left: nt,
forall right: sf,
rs left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: nt, In (inl s) right -> In s ntl) /\
(forall s: t, In (inr s) right -> In s tl).
Proof.
exists 2, [S'], [a; b].
split.
- simpl; left; reflexivity.
- intros left right H.
  inversion H.
  + simpl. 
    split.
    * omega.
    * {
      split.
      - left; reflexivity.
      - split.
        + intros s H2.
          destruct H2 as [H2 | H2].
          * inversion H2.
          * {
            destruct H2 as [H2 | H2].
            - left; inversion H2. reflexivity.
            - contradiction.
            }
        + intros s H2.
          destruct H2 as [H2 | H2].
          * inversion H2. left; reflexivity.
          * {
            destruct H2 as [H2 | H2].
            - inversion H2.
            - contradiction.
            }
      }
  + simpl. split.
    * omega.
    * {
      split.
      - left; reflexivity.
      - split.
        + intros s H2. destruct H2 as [H2 | H2].
          * inversion H2.
          * contradiction.
        + intros s H2.
          destruct H2 as [H2 | H2].
          * inversion H2. right; left; reflexivity.
          * contradiction.
      }
Qed.

Definition g: cfg nt t:= {|
start_symbol:= S'; 
rules:= rs;
rules_finite:= rs_finite |}.

Lemma l1: derives g [inr a; inl S'] [inr a; inr b]. Admitted.
Lemma l2: generates g [inr a; inl S']. Admitted.
Lemma l3: produces g [a; b]. Admitted.

Lemma derives_g_aab:
derives g [inl S'] [inr a; inr a; inr b].
Proof.
apply derives_step with (s2:=[inr a; inr a])(left:=S')(right:=[inr b]).
apply derives_step with (s2:=[inr a])(left:=S')(right:=[inr a;inl S']).
apply derives_start with (left:=S')(right:=[inr a;inl S']).
apply r1.
apply r1.
apply r2.
Qed.
