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
