(* Coordinate calculus and polynomial regularity of quadratic projections. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.CovarianceLinearImages Gaussian.FiniteSums
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateWeights Analysis.CoordinateTopology
  Gaussian.CoordinateDerivativeDefinitions
  Analysis.CoordinatePermutationDefinitions
  Gaussian.CoordinatePolynomialContinuity Gaussian.CoordinateSuffixAlgebra
  Data.FeatureMomentsCoordinates Gaussian.SmoothCalculus Projection.Stein.
Open Scope R_scope.

Lemma paper_main_projection_delta_sum d i f : (i<d)%coq_nat ->
  finite_sum (fun k => pmdf_kron i k*f k) (List.seq 0 d)=f i.
Proof.
intro Hi; rewrite <- (finite_sum_delta d i (f i) Hi).
apply finite_sum_ext; intros k Hk; unfold pmdf_kron.
rewrite Nat.eqb_sym; destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; subst k|]; ring.
Qed.

Lemma paper_main_projection_entry_derive d i j k : (k<d)%coq_nat ->
  finite_coordinate_derivative d k (paper_main_projection_entry i j)
    (fun xs => pmdf_kron k i*List.nth j xs 0+List.nth i xs 0*pmdf_kron k j).
Proof.
intro Hk; unfold paper_main_projection_entry.
apply (paper_main_coordinate_derivative_value_ext d k _
  (fun xs => (pmdf_kron k i*List.nth j xs 0+List.nth i xs 0*pmdf_kron k j)+0)).
- unfold Rminus.
  apply paper_main_coordinate_derivative_add.
  + apply pmdf_derivative_mult; apply pmdf_derivative_nth; exact Hk.
  + apply paper_main_coordinate_derivative_const.
- intros xs Hxs; ring.
Qed.

Lemma paper_main_projection_derivative_sum d k I F DF :
  (forall i, In i I -> finite_coordinate_derivative d k (F i) (DF i)) ->
  finite_coordinate_derivative d k (fun xs => finite_sum (fun i => F i xs) I)
    (fun xs => finite_sum (fun i => DF i xs) I).
Proof.
intro HD; intros xs Hxs.
apply (is_derive_finite_sum (fun i t => F i (replace_coordinate k t xs))
  (fun i _ => DF i xs) I (List.nth k xs 0)).
intros i Hi; exact(HD i Hi xs Hxs).
Qed.

Theorem paper_main_projection_quadratic_derive d A k : (k<d)%coq_nat ->
  finite_coordinate_derivative d k (paper_main_projection_quadratic d A)
    (linear_form d (fun j => A k j+A j k)).
Proof.
intro Hk; unfold paper_main_projection_quadratic.
apply (paper_main_coordinate_derivative_value_ext d k _
  (fun xs => finite_sum (fun i => finite_sum (fun j => A i j*
    (pmdf_kron k i*List.nth j xs 0+List.nth i xs 0*pmdf_kron k j))
    (List.seq 0 d)) (List.seq 0 d))).
- apply paper_main_projection_derivative_sum; intros i Hi.
  apply paper_main_projection_derivative_sum; intros j Hj.
  apply paper_main_coordinate_derivative_scale; apply paper_main_projection_entry_derive; exact Hk.
- intros xs Hxs.
  transitivity (finite_sum (fun i => pmdf_kron k i*linear_form d (A i) xs+
    List.nth i xs 0*A i k) (List.seq 0 d)).
  + apply finite_sum_ext; intros i Hi.
    transitivity (finite_sum (fun j => (pmdf_kron k i)*(A i j*List.nth j xs 0)+
      List.nth i xs 0*(pmdf_kron k j*A i j)) (List.seq 0 d)).
    * apply finite_sum_ext; intros j Hj; ring.
    * rewrite finite_sum_plus !finite_sum_scale (paper_main_projection_delta_sum d k (A i) Hk).
      reflexivity.
  + rewrite finite_sum_plus (paper_main_projection_delta_sum d k _ Hk).
    unfold linear_form; rewrite <- finite_sum_plus; apply finite_sum_ext; intros j Hj; ring.
Qed.

Corollary paper_main_projection_quadratic_symmetric_derive d A k :
  (k<d)%coq_nat -> (forall i j, (i<d)%coq_nat -> (j<d)%coq_nat -> A i j=A j i) ->
  finite_coordinate_derivative d k (paper_main_projection_quadratic d A)
    (fun xs => 2*linear_form d (A k) xs).
Proof.
intros Hk HA; apply (paper_main_coordinate_derivative_value_ext d k _
  (linear_form d (fun j => A k j+A j k)) (fun xs => 2*linear_form d (A k) xs)
  (paper_main_projection_quadratic_derive d A k Hk)).
intros xs Hxs; unfold linear_form; rewrite <- finite_sum_scale; apply finite_sum_ext.
intros j Hj; apply in_seq in Hj; rewrite (HA j k ltac:(lia) Hk); ring.
Qed.

Theorem paper_main_projection_quadratic_regular d A :
  finite_joint_continuous d (paper_main_projection_quadratic d A) /\
  exists C, finite_polynomial_bound d C 2 (paper_main_projection_quadratic d A).
Proof.
assert (HC : forall i j, (i<d)%coq_nat -> (j<d)%coq_nat ->
  finite_joint_continuous d (paper_main_projection_entry i j)).
{ intros i j Hi Hj; apply (finite_joint_continuous_ext d
    (fun xs => paper_main_projection_entry i j xs*1)).
  - intros xs Hxs; ring.
  - apply paper_main_projection_entry_continuous; try assumption; apply finite_joint_continuous_constant. }
assert (HB : forall i j, (i<d)%coq_nat -> (j<d)%coq_nat ->
  finite_polynomial_bound d (Rabs 1) 2 (paper_main_projection_entry i j)).
{ intros i j Hi Hj; apply (finite_polynomial_bound_ext d (Rabs 1) 2
    (fun xs => paper_main_projection_entry i j xs*1)).
  - intros xs Hxs; ring.
  - apply (paper_main_projection_entry_bound d i j (fun _ => 1) (Rabs 1) 0 Hi Hj).
    apply finite_polynomial_bound_constant. }
split; unfold paper_main_projection_quadratic.
- apply finite_joint_continuous_sum; intros i Hi.
  apply finite_joint_continuous_sum; intros j Hj.
  apply finite_joint_continuous_scale; apply HC; apply in_seq in Hi,Hj; lia.
- apply finite_polynomial_bound_sum; intros i Hi.
  apply finite_polynomial_bound_sum; intros j Hj.
  exists (Rabs(A i j)*Rabs 1).
  apply finite_polynomial_bound_scale; apply HB; apply in_seq in Hi,Hj; lia.
Qed.
