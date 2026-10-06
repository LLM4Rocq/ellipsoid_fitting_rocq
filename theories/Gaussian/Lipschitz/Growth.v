(* Growth and integrability of a Euclidean-Lipschitz test F on lists of
   length d, for every d (including d = 0) and every L >= 0 (including
   L = 0). With the zero list paper_main_gaussian_zero_list d,
   |F xs| <= |F 0| + L |xs| (paper_main_gaussian_lipschitz_linear_growth),
   so F has a polynomial bound of degree 2 with the constant
   paper_main_gaussian_growth_constant d F L
   (paper_main_gaussian_lipschitz_polynomial_bound), and F is integrable
   at every level of the iterated Gaussian expectation
   (paper_main_gaussian_lipschitz_domain). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Soft.Definitions
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Gaussian.Iterated.Definitions
  Gaussian.Iterated.Expectation Gaussian.Iterated.PolynomialDomain
  Gaussian.Coordinate.Weights Gaussian.Coordinate.PolynomialContinuity
  Gaussian.Iterated.ParameterContinuity Analysis.FiniteSumAlgebra
  Gaussian.Smooth.Calculus Gaussian.Smooth.Test Gordon.Lipschitz
  Gaussian.Lipschitz.EuclideanNorm Gaussian.Lipschitz.Clip.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_zero_list d : list R :=
  map (fun _ => 0) (List.seq 0 d).

Lemma paper_main_gaussian_zero_list_length d :
  List.length (paper_main_gaussian_zero_list d) = d.
Proof. unfold paper_main_gaussian_zero_list; apply length_map_seq. Qed.

Lemma paper_main_gaussian_distance_zero d xs :
  List.length xs = d ->
  paper_main_gordon_distance d xs (paper_main_gaussian_zero_list d) =
    paper_main_gaussian_norm xs.
Proof.
intros Hxs; unfold paper_main_gordon_distance, paper_main_gaussian_norm.
f_equal; rewrite <- (paper_main_gaussian_squares_coordinates d xs Hxs).
apply finite_sum_ext; intros k Hk; apply in_seq in Hk.
unfold paper_main_gaussian_zero_list.
rewrite (nth_map_seq (fun _ => 0) d k ltac:(lia)); ring.
Qed.

Lemma paper_main_gaussian_lipschitz_linear_growth d F L xs :
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  List.length xs = d ->
  Rabs (F xs) <=
    Rabs (F (paper_main_gaussian_zero_list d)) + L * paper_main_gaussian_norm xs.
Proof.
intros HLip Hxs.
pose proof (HLip xs (paper_main_gaussian_zero_list d) Hxs
  (paper_main_gaussian_zero_list_length d)) as H.
rewrite (paper_main_gaussian_distance_zero d xs Hxs) in H.
pose proof (Rabs_triang_inv (F xs) (F (paper_main_gaussian_zero_list d))) as Ht.
lra.
Qed.

Definition paper_main_gaussian_growth_constant d (F : list R -> R) L : R :=
  Rabs (F (paper_main_gaussian_zero_list d)) + L * (1 + INR d).

Lemma paper_main_gaussian_growth_constant_nonnegative d F L :
  0 <= L -> 0 <= paper_main_gaussian_growth_constant d F L.
Proof.
intros HL; unfold paper_main_gaussian_growth_constant.
apply Rplus_le_le_0_compat; [apply Rabs_pos|].
apply Rmult_le_pos; [exact HL|pose proof (pos_INR d); lra].
Qed.

Theorem paper_main_gaussian_lipschitz_polynomial_bound d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  finite_polynomial_bound d (paper_main_gaussian_growth_constant d F L) 2 F.
Proof.
intros HL HLip; split; [exact (paper_main_gaussian_growth_constant_nonnegative d F L HL)|].
intros xs Hxs.
pose proof (paper_main_gaussian_lipschitz_linear_growth d F L xs HLip Hxs) as Hg.
destruct (paper_main_gaussian_norm_polynomial d) as [_ Hn].
pose proof (Hn xs Hxs) as Hnb.
pose proof (gaussian_coordinate_product_weight_at_least_one 2 xs) as Hw.
pose proof (paper_main_gaussian_norm_nonnegative xs) as Hn0.
rewrite (Rabs_pos_eq _ Hn0) in Hnb.
pose proof (Rabs_pos (F (paper_main_gaussian_zero_list d))) as HF0.
pose proof (pos_INR d) as Hd.
unfold paper_main_gaussian_growth_constant; nra.
Qed.

Theorem paper_main_gaussian_lipschitz_domain d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_integrable d F /\ gaussian_iterated_absolutely_integrable d F.
Proof.
intros HL HLip.
destruct (gaussian_coordinate_polynomial_domain d F _ 2
  (paper_main_gaussian_lipschitz_continuous d F L HL HLip)
  (paper_main_gaussian_lipschitz_polynomial_bound d F L HL HLip)) as [HI [HA _]].
split; [exact HI|exact HA].
Qed.
