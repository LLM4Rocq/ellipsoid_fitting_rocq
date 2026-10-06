(* Algebra of polynomial bounds and of suffix marginals. A polynomial bound
   on F (finite_polynomial_bound) holds for any function equal to F on the
   lists of length d (finite_polynomial_bound_ext), and for the sections
   xs |-> F (prefix ++ xs) and xs |-> F (x :: xs), with the constant
   multiplied by the weight of the fixed coordinates
   (finite_polynomial_bound_prefix, finite_polynomial_bound_head). The
   suffix marginal over no coordinate is F (gaussian_suffix_marginal_zero),
   and the one over n + 1 coordinates is the suffix marginal over n
   coordinates of the last marginal (gaussian_suffix_marginal_succ). *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Gaussian.Iterated.SuffixMarginalDefinitions Gaussian.Iterated.LastIntegration
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.Coordinate.WeightDefinitions Gaussian.Coordinate.Weights
  Analysis.CoordinatePermutationDefinitions.
Import ListNotations.
Open Scope R_scope.

Lemma finite_polynomial_bound_ext d C p F G :
  (forall xs, length xs = d -> F xs = G xs) ->
  finite_polynomial_bound d C p F -> finite_polynomial_bound d C p G.
Proof.
  intros He [HC HB]; split; [exact HC|].
  intros xs Hxs; rewrite <- He by exact Hxs; apply HB, Hxs.
Qed.

Lemma finite_polynomial_bound_prefix d C p F prefix :
  finite_polynomial_bound (length prefix+d) C p F ->
  finite_polynomial_bound d (C*gaussian_coordinate_product_weight p prefix) p
    (fun xs => F (prefix++xs)).
Proof.
  intros [HC HB]; split.
  - pose proof (gaussian_coordinate_product_weight_nonnegative p prefix); nra.
  - intros xs Hxs.
    specialize (HB (prefix++xs) ltac:(rewrite length_app,Hxs; reflexivity)).
    rewrite gaussian_coordinate_product_weight_append in HB.
    rewrite Rmult_assoc; exact HB.
Qed.

Lemma finite_polynomial_bound_head d C p F x :
  finite_polynomial_bound (S d) C p F ->
  finite_polynomial_bound d (C*gaussian_coordinate_weight p x) p
    (fun xs => F (x::xs)).
Proof.
  intro HB.
  pose proof (finite_polynomial_bound_prefix d C p F [x] HB) as H.
  change (finite_polynomial_bound d (C*(gaussian_coordinate_weight p x*1)) p
    (fun xs => F (x::xs))) in H.
  rewrite Rmult_1_r in H; exact H.
Qed.

Lemma gaussian_suffix_marginal_zero F xs : gaussian_suffix_marginal 0 F xs = F xs.
Proof. unfold gaussian_suffix_marginal; simpl; rewrite app_nil_r; reflexivity. Qed.

Lemma gaussian_suffix_marginal_succ n F xs :
  gaussian_suffix_marginal (S n) F xs =
    gaussian_suffix_marginal n (gaussian_last_marginal F) xs.
Proof.
  unfold gaussian_suffix_marginal; rewrite gaussian_iterated_last_expectation.
  apply gaussian_iterated_expectation_ext; intros ys Hys.
  unfold gaussian_last_marginal.
  apply (f_equal gaussian_expectation); apply functional_extensionality; intro t.
  rewrite app_assoc; reflexivity.
Qed.
