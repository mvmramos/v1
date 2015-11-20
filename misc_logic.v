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
   
(* --------------------------------------------------------------------- *)
(* BASIC LEMMAS                                                          *)
(* --------------------------------------------------------------------- *)

Lemma sig_weak {A: Type} {P P': A -> Prop} (H: forall x: A, P x -> P' x) (a: {x | P x}): {x | P' x}.
Proof.
destruct a as [x H0].
exists x.
apply H.
exact H0.
Qed.

Lemma contrap:
forall P1 P2: Prop,
(P1 -> P2) -> (~ P2 -> ~ P1).
Proof.
intros P1 P2 H1 H2 H3.
apply H2.
apply H1.
exact H3.
Qed.
