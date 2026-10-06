(* Explicit dimension-uniform constants for the coarse Gaussian estimate. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Goe.Definitions Goe.IndexPairs
  Gordon.Entropy Gaussian.FeatureCoordinates Gaussian.FeatureTail
  Gaussian.JointFeature.
Open Scope R_scope.

Lemma paper_main_symmetric_dimension_upper n :
  (paper_main_symmetric_dimension n <= S n*S n)%nat.
Proof.
unfold paper_main_symmetric_dimension; rewrite goe_vector_dimension.
pose proof (goe_pairs_length_twice n); nia.
Qed.

Lemma paper_main_gaussian_joint_width_upper n :
  INR(paper_main_gaussian_joint_width n) <= 2*(INR(S n))^2.
Proof.
pose proof (le_INR _ _ (paper_main_symmetric_dimension_upper n)) as HD.
rewrite mult_INR in HD.
unfold paper_main_gaussian_joint_width; rewrite plus_INR.
assert (Hp : 1 <= INR(S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
nra.
Qed.
