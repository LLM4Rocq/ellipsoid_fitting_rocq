(* The soft minimax at quadratic data features and at GOE features, compared
   under the Gaussian product law. Let d = n + 1 and N = m + 1.
   multirow_quadratic_value and multirow_goe_value are the soft minimax
   lower_block_phi at the N quadratic data features (x_i x_i^T - I) / sqrt d
   of the rows x_i of a list of coordinates, and at the N GOE matrices built
   from the rows of a list of coordinates. Under the Gaussian product law
   the rows are independent standard Gaussian vectors, and the GOE matrices
   are independent.
   - paper_main_soft_endpoint_laws: both values are integrable under
     gaussian_product_law, and their integrals are the iterated Gaussian
     expectations (paper_main_soft_domain_law, with the continuity of
     paper_main_soft_endpoint_continuous).
   - paper_main_soft_public_comparison: if the dual vectors y z are unit
     vectors with entries at most theta / sqrt d, and the B s are symmetric
     with operator norm at most k, the two integrals differ by at most
       (40/3) k^3 (beta + gamma)^2 theta (d + 2 sqrt (d ln N) + 2 ln N) / d^2.
     This is the bound paper_multirow_integrated_bound_results, proved by
     interpolation between the two arrays, transported to the integrals of
     gaussian_product_law.
   - paper_main_soft_comparison_coarse: when 0 <= ln N <= d, this bound is
     at most (200/3) k^3 (beta + gamma)^2 theta / d. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import MatrixDefinitions SoftDefinitions OperatorDefinitions
  TensorDefinitions GaussianProductDefinitions JointDefinitions GoeDefinitions
  RowTimeDefinitions MultirowEndpointDefinitions MaximumRadiusDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianProbabilityProductDefinitions GaussianProbabilityProductIntegrals
  GaussianProbabilityProductContinuity MultirowExpectationBounds
  MultirowExpectationMarginal MultirowExpectationAssembly MultirowIntegratedBoundResults.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_soft_endpoint_continuous n m beta gamma y B Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  finite_joint_continuous (Nat.mul (Datatypes.S m) (Datatypes.S (goe_vector_index n)))
    (multirow_goe_value n m beta gamma y B Y S) /\
  finite_joint_continuous (Nat.mul (Datatypes.S m) (Datatypes.S n))
    (multirow_quadratic_value n m beta gamma y B Y S).
Proof.
move=> Hb Hg HY HS; split.
- apply: (finite_joint_continuous_ext _
    (fun zs => gaussian_array_value n m beta gamma y B Y S 0
      (mexp_goe_lift (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) zs))).
  + move=> zs HL; exact: mexp_value_zero_lift.
  + apply: mexp_goe_lift_continuous; exact: mexp_value_continuous.
- apply: (finite_joint_continuous_ext _
    (fun xs => gaussian_array_value n m beta gamma y B Y S 1
      (mexp_quadratic_lift (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) xs))).
  + move=> xs HL; exact: mexp_value_one_lift.
  + apply: mexp_quadratic_lift_continuous; exact: mexp_value_continuous.
Qed.

Lemma paper_main_soft_domain_law d F :
  finite_joint_continuous d F -> gaussian_list_domain d F ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (F (tval x))%:E =
    (gaussian_iterated_expectation d F)%:E)%E.
Proof.
move=> HC [HI [HA _]].
apply: gpp_all_sections HI HA.
apply/measurable_EFinP; exact: gpp_joint_measurable.
Qed.

Theorem paper_main_soft_endpoint_laws n m beta gamma y B Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  ((gaussian_product_law (Nat.mul (Datatypes.S m) (Datatypes.S (goe_vector_index n)))).-integrable
    setT (fun x => (multirow_goe_value n m beta gamma y B Y S (tval x))%:E) /\
   (\int[gaussian_product_law (Nat.mul (Datatypes.S m) (Datatypes.S (goe_vector_index n)))]_x
      (multirow_goe_value n m beta gamma y B Y S (tval x))%:E =
      (gaussian_iterated_expectation (Nat.mul (Datatypes.S m) (Datatypes.S (goe_vector_index n)))
        (multirow_goe_value n m beta gamma y B Y S))%:E)%E) /\
  ((gaussian_product_law (Nat.mul (Datatypes.S m) (Datatypes.S n))).-integrable
    setT (fun x => (multirow_quadratic_value n m beta gamma y B Y S (tval x))%:E) /\
   (\int[gaussian_product_law (Nat.mul (Datatypes.S m) (Datatypes.S n))]_x
      (multirow_quadratic_value n m beta gamma y B Y S (tval x))%:E =
      (gaussian_iterated_expectation (Nat.mul (Datatypes.S m) (Datatypes.S n))
        (multirow_quadratic_value n m beta gamma y B Y S))%:E)%E).
Proof.
move=> Hb Hg HY HS.
have [CG CW] := paper_main_soft_endpoint_continuous n m beta gamma y B Y S Hb Hg HY HS.
have [DG [DW _]] := mexp_clause_endpoints n m beta gamma y B Y S Hb Hg HY HS.
split; exact: paper_main_soft_domain_law.
Qed.

Theorem paper_main_soft_public_comparison n m beta gamma theta k y B Y S :
  0 < beta -> 0 < gamma -> 0 < theta -> 0 <= k -> Y <> [] -> S <> [] ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  let d := INR (Datatypes.S n) in
  let N := Datatypes.S m in
  let DG := Nat.mul N (Datatypes.S (goe_vector_index n)) in
  let DW := Nat.mul N (Datatypes.S n) in
  let EG := (\int[gaussian_product_law DG]_x
    (multirow_goe_value n m beta gamma y B Y S (tval x))%:E)%E in
  let EW := (\int[gaussian_product_law DW]_x
    (multirow_quadratic_value n m beta gamma y B Y S (tval x))%:E)%E in
  Rabs (fine EW - fine EG) <= (40/3) * k^3 * (beta+gamma)^2 * theta *
    (d + 2*sqrt (d*Rpower.ln (INR N)) + 2*Rpower.ln (INR N)) / d^2.
Proof.
move=> Hb Hg Htheta Hk HY HS Hunit Hlow Hsym Hop.
cbv zeta.
have [[_ EG] [_ EW]] := paper_main_soft_endpoint_laws n m beta gamma y B Y S Hb Hg HY HS.
rewrite EG EW /=.
have [_ [_ H]] := paper_multirow_integrated_bound_results.
exact: (proj2 (proj2 (proj2 (H n m beta gamma theta k y B Y S
  Hb Hg Htheta Hk HY HS Hunit Hlow Hsym Hop)))).
Qed.

Lemma paper_main_soft_radius_coarse d l :
  0 < d -> 0 <= l <= d -> d + 2*sqrt (d* l) + 2* l <= 5*d.
Proof.
move=> Hd [Hl Hld].
have HS := pow2_sqrt (d* l) ltac:(nra).
have HP := sqrt_pos (d* l).
have HB : d* l <= d*d by nra.
have HR : sqrt (d* l) <= d by nra.
nra.
Qed.

Lemma paper_main_soft_comparison_coarse d k beta gamma theta l :
  0 < d -> 0 <= k -> 0 <= theta -> 0 <= l <= d ->
  (40/3)*k^3*(beta+gamma)^2*theta *
    (d+2*sqrt (d* l)+2* l)/d^2 <= (200/3)*k^3*(beta+gamma)^2*theta/d.
Proof.
move=> Hd Hk Htheta Hl.
have HB := paper_main_soft_radius_coarse d l Hd Hl.
have HC : 0 <= (40/3)*k^3*(beta+gamma)^2*theta.
{ apply Rmult_le_pos; last exact Htheta.
  apply Rmult_le_pos; last apply pow2_ge_0.
  apply Rmult_le_pos; nra. }
have HM := Rmult_le_compat_l _ _ _ HC HB.
have HD : 0 <= /d^2 by apply Rlt_le,Rinv_0_lt_compat; nra.
have HH := Rmult_le_compat_r _ _ _ HD HM.
eapply Rle_trans; first exact HH.
right; field; lra.
Qed.
