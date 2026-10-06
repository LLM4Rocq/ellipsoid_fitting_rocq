From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import GaussianDefinitions GaussianIntegration
  GaussianProductDefinitions GaussianProduct GaussianLastDefinitions GaussianLastIntegration
  GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianCoordinateMarginals.
Import ListNotations.
Open Scope R_scope.

(* Stein's identities in the last coordinate of the iterated Gaussian
   expectation E = gaussian_iterated_expectation (S d). Let x_d be the last
   coordinate List.nth d xs 0, and let F and its derivatives in x_d be
   bounded by constants times polynomials (finite_polynomial_bound).
   - gaussian_iterated_last_first_stein: E DF = E (x_d * F), when DF is the
     derivative of F in x_d and is jointly continuous.
   - gaussian_iterated_last_second_stein: E DDF = E ((x_d ^ 2 - 1) * F),
     when DF and DDF are the first and second derivatives of F in x_d and
     DDF is jointly continuous.
   The proofs apply the one-dimensional identities gaussian_first_stein and
   gaussian_second_stein of GaussianIntegration to the sections
   t |-> F (xs ++ [t]), whose polynomial bounds come from
   gaussian_last_section_scalar_bound.

   The derivatives are MathComp's is_derive at t in the direction 1, the
   ordinary derivative of a function R -> R. With ssreflect loaded, the
   statements write (xs ++ [t])%list and List.nth for Stdlib's app and nth.
   The one-dimensional expectations are Lebesgue integrals against the
   Gaussian kernel. *)

Lemma gaussian_last_section_scalar_bound d F C p xs :
  finite_polynomial_bound (S d) C p F -> length xs = d ->
  forall t, Rabs (F (xs++[t])%list) <=
    (C*gaussian_coordinate_product_weight p xs*2^p)*(1+Rabs t^p).
Proof.
  intros Hb Hxs t.
  eapply Rle_trans; [apply (gaussian_last_section_polynomial_bound d F C p xs Hb Hxs)|].
  replace (C*gaussian_coordinate_product_weight p xs*2^p*(1+Rabs t^p)) with
    ((C*gaussian_coordinate_product_weight p xs)*(2^p*(1+Rabs t^p))) by ring.
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos; [exact (proj1 Hb)|apply gaussian_coordinate_product_weight_nonnegative].
  - apply gaussian_coordinate_weight_polynomial_bound.
Qed.

Theorem gaussian_iterated_last_first_stein d F DF C p D q :
  finite_joint_continuous (S d) DF ->
  finite_polynomial_bound (S d) C p F ->
  finite_polynomial_bound (S d) D q DF ->
  (forall xs : list R, length xs = d -> forall t : R,
    @is_derive R R^o R^o t 1 (fun u => F (xs++[u])%list) (DF (xs++[t])%list)) ->
  gaussian_iterated_expectation (S d) DF =
  gaussian_iterated_expectation (S d) (fun xs => List.nth d xs 0 * F xs).
Proof.
  intros HC HF HDF HD.
  rewrite !gaussian_iterated_last_expectation.
  apply gaussian_iterated_expectation_ext; intros xs Hxs.
  pose proof (gaussian_first_stein (fun t => F (xs++[t])%list) (fun t => DF (xs++[t])%list)
    (C*gaussian_coordinate_product_weight p xs*2^p) p
    (D*gaussian_coordinate_product_weight q xs*2^q) q
    (HD xs Hxs)
    (finite_joint_continuous_last_section d DF xs HC Hxs)
    (gaussian_last_section_scalar_bound d F C p xs HF Hxs)
    (gaussian_last_section_scalar_bound d DF D q xs HDF Hxs)) as HS.
  repeat match type of HS with _ /\ _ => apply proj2 in HS end.
  rename HS into HE.
  unfold gaussian_last_marginal.
  etransitivity; [exact HE|].
  apply (f_equal gaussian_expectation); apply functional_extensionality; intro t.
  rewrite <- Hxs; rewrite nth_middle; reflexivity.
Qed.

Theorem gaussian_iterated_last_second_stein d F DF DDF C p D q E r :
  finite_joint_continuous (S d) DDF ->
  finite_polynomial_bound (S d) C p F ->
  finite_polynomial_bound (S d) D q DF ->
  finite_polynomial_bound (S d) E r DDF ->
  (forall xs : list R, length xs = d -> forall t : R,
    @is_derive R R^o R^o t 1 (fun u => F (xs++[u])%list) (DF (xs++[t])%list)) ->
  (forall xs : list R, length xs = d -> forall t : R,
    @is_derive R R^o R^o t 1 (fun u => DF (xs++[u])%list) (DDF (xs++[t])%list)) ->
  gaussian_iterated_expectation (S d) DDF =
  gaussian_iterated_expectation (S d)
    (fun xs => (List.nth d xs 0*List.nth d xs 0-1)*F xs).
Proof.
  intros HC HF HDF HDDF HD HDD.
  rewrite !gaussian_iterated_last_expectation.
  apply gaussian_iterated_expectation_ext; intros xs Hxs.
  pose proof (gaussian_second_stein (fun t => F (xs++[t])%list)
    (fun t => DF (xs++[t])%list) (fun t => DDF (xs++[t])%list)
    (C*gaussian_coordinate_product_weight p xs*2^p) p
    (D*gaussian_coordinate_product_weight q xs*2^q) q
    (E*gaussian_coordinate_product_weight r xs*2^r) r
    (HD xs Hxs) (HDD xs Hxs)
    (finite_joint_continuous_last_section d DDF xs HC Hxs)
    (gaussian_last_section_scalar_bound d F C p xs HF Hxs)
    (gaussian_last_section_scalar_bound d DF D q xs HDF Hxs)
    (gaussian_last_section_scalar_bound d DDF E r xs HDDF Hxs)) as HS.
  repeat match type of HS with _ /\ _ => apply proj2 in HS end.
  rename HS into HE.
  unfold gaussian_last_marginal.
  etransitivity; [exact HE|].
  apply (f_equal gaussian_expectation); apply functional_extensionality; intro t.
  rewrite <- Hxs; rewrite nth_middle; reflexivity.
Qed.
