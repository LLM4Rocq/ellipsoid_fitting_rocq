(* Port of theories/GaussianCoordinateSuffixAlgebra.v from Coquelicot to
   MathComp-Analysis.

   Every lemma keeps its name, its arguments in the same order and its text.
   The only change to the file is that the Coquelicot import line is
   dropped: no statement or proof here names a Coquelicot notion. The
   predicate finite_polynomial_bound and the weights come from the ported
   GaussianCoordinateWeightDefinitions, the marginals from the ported
   GaussianLastDefinitions and the iterated expectation from the ported
   GaussianProductDefinitions. The texts of these definitions are the
   original ones, and the Gaussian expectation underneath is the Lebesgue
   integral over the line (difference 4 of analysis/README.md).

   Meaning. The first three lemmas are statements about pointwise bounds
   and do not involve an integral. The last four are equalities of iterated
   expectations. Three hold by unfolding the definitions, with app_nil_r for
   gaussian_suffix_marginal_zero. gaussian_suffix_marginal_succ follows from
   gaussian_iterated_last_expectation and gaussian_iterated_expectation_ext
   of the ported GaussianLastIntegration and GaussianProduct, which are
   unfoldings too. None of them depends on which integral is used, so each
   one says what the original said.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So ++, length, the %nat scope and the operations on R are
   Stdlib's, as in the original, and the proofs are the original ones, word
   for word. The proof of gaussian_suffix_marginal_succ uses Stdlib's
   functional_extensionality, whose axiom functional_extensionality_dep is
   one of the seven of analysis/README.md. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct
  GaussianLastDefinitions GaussianLastIntegration GaussianCoordinateDefinitions
  GaussianCoordinateTopology GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCoordinatePermutationDefinitions.
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

Lemma gaussian_suffix_marginal_head n F x xs :
  gaussian_suffix_marginal n F (x::xs) =
    gaussian_suffix_marginal n (fun ys => F (x::ys)) xs.
Proof. reflexivity. Qed.

Lemma gaussian_suffix_marginal_swap_head n F x y :
  gaussian_suffix_marginal n (fun xs => F (swap_adjacent 0 xs)) [x;y] =
    gaussian_suffix_marginal n F [y;x].
Proof. reflexivity. Qed.
