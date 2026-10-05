(* The actual isotropic PSD sphere width has normalized limit 1/2. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import GoeDefinitions GoePairs
  PaperMainGaussianFeatureCoordinates PaperMainGaussianPsdWidth.
Open Scope R_scope.

Lemma paper_main_symmetric_dimension_real n :
  INR (paper_main_symmetric_dimension n) = INR (S n) * (INR (S n)+1)/2.
Proof.
pose proof (goe_pairs_length_twice n) as H.
rewrite <- goe_vector_dimension in H.
apply (f_equal INR) in H.
rewrite !mult_INR in H.
change (2*INR (paper_main_symmetric_dimension n) = INR (S n)*INR (S (S n))) in H.
rewrite (S_INR (S n)) in H; lra.
Qed.
