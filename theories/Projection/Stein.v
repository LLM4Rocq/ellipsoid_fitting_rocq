(* First Gaussian integration by parts for a centered quadratic entry. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.Iterated.FiniteSums
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.Coordinate.WeightDefinitions Gaussian.Coordinate.Weights
  Gaussian.Coordinate.DerivativeDefinitions
  Analysis.CoordinatePermutationDefinitions Analysis.CoordinatePermutations
  Gaussian.Coordinate.ProductDerivative
  Gaussian.Coordinate.PolynomialContinuity Gaussian.Iterated.SuffixAlgebra
  Gaussian.Iterated.Stein Gaussian.Iterated.PolynomialDomain
  Gaussian.Smooth.Calculus.
Open Scope R_scope.

Definition paper_main_projection_entry i j (xs : list R) :=
  List.nth i xs 0*List.nth j xs 0-(if Nat.eqb i j then 1 else 0).

Lemma paper_main_projection_entry_continuous d i j F :
  (i<d)%coq_nat -> (j<d)%coq_nat -> finite_joint_continuous d F ->
  finite_joint_continuous d (fun xs => paper_main_projection_entry i j xs*F xs).
Proof.
intros Hi Hj HF; unfold paper_main_projection_entry.
destruct (Nat.eqb i j) eqn:E.
- apply Nat.eqb_eq in E; subst j.
  apply finite_joint_continuous_times_centered_square; assumption.
- apply (finite_joint_continuous_ext d (fun xs => (List.nth i xs 0*List.nth j xs 0)*F xs)).
  + intros xs Hxs; ring.
  + apply finite_joint_continuous_times_two_coordinates; assumption.
Qed.

Lemma paper_main_projection_entry_bound d i j F C p :
  (i<d)%coq_nat -> (j<d)%coq_nat -> finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C (S(S p)) (fun xs => paper_main_projection_entry i j xs*F xs).
Proof.
intros Hi Hj HF; unfold paper_main_projection_entry.
destruct (Nat.eqb i j) eqn:E.
- apply Nat.eqb_eq in E; subst j.
  apply finite_polynomial_bound_times_centered_square; assumption.
- apply (finite_polynomial_bound_ext d C (S(S p))
    (fun xs => (List.nth i xs 0*List.nth j xs 0)*F xs)).
  + intros xs Hxs; ring.
  + apply finite_polynomial_bound_times_two_coordinates; assumption.
Qed.

Lemma paper_main_projection_coordinate_product_derive d i F DF :
  (i<d)%coq_nat -> finite_coordinate_derivative d i F DF ->
  finite_coordinate_derivative d i (fun xs => List.nth i xs 0*F xs)
    (fun xs => F xs+List.nth i xs 0*DF xs).
Proof.
intros Hi HD xs Hxs.
apply (is_derive_ext (fun t => t*F(replace_coordinate i t xs))).
- intro t; rewrite (replace_coordinate_nth_same i t xs ltac:(lia)); reflexivity.
- pose proof (is_derive_mult (fun t => t) (fun t => F(replace_coordinate i t xs))
    (List.nth i xs 0) 1 (DF xs) (is_derive_id_R _) (HD xs Hxs)) as HH.
  rewrite replace_coordinate_self Rmult_1_l in HH; exact HH.
Qed.

Theorem paper_main_projection_entry_stein n i j F DF C p :
  (i<=n)%coq_nat -> (j<=n)%coq_nat ->
  finite_joint_continuous (S n) F -> finite_joint_continuous (S n) DF ->
  finite_polynomial_bound (S n) C p F -> finite_polynomial_bound (S n) C p DF ->
  finite_coordinate_derivative (S n) i F DF ->
  gaussian_iterated_integrable (S n) (fun xs => paper_main_projection_entry i j xs*F xs) /\
  gaussian_iterated_integrable (S n) (fun xs => List.nth j xs 0*DF xs) /\
  gaussian_iterated_expectation (S n) (fun xs => paper_main_projection_entry i j xs*F xs) =
    gaussian_iterated_expectation (S n) (fun xs => List.nth j xs 0*DF xs).
Proof.
intros Hi Hj HF HDF HBF HBDF HD.
assert (HCj : finite_joint_continuous (S n) (fun xs => List.nth j xs 0*F xs)).
{ apply finite_joint_continuous_times_coordinate; [exact HF|lia]. }
assert (HBj : finite_polynomial_bound (S n) C (S p) (fun xs => List.nth j xs 0*F xs)).
{ apply finite_polynomial_bound_times_coordinate; [exact HBF|lia]. }
assert (HCDj : finite_joint_continuous (S n) (fun xs => List.nth j xs 0*DF xs)).
{ apply finite_joint_continuous_times_coordinate; [exact HDF|lia]. }
assert (HBDj : finite_polynomial_bound (S n) C (S p) (fun xs => List.nth j xs 0*DF xs)).
{ apply finite_polynomial_bound_times_coordinate; [exact HBDF|lia]. }
assert (HID : gaussian_iterated_integrable (S n) (fun xs => List.nth j xs 0*DF xs)).
{ exact(proj1(gaussian_coordinate_polynomial_domain _ _ _ _ HCDj HBDj)). }
split.
- apply (proj1 (gaussian_coordinate_polynomial_domain _ _ C (S(S p))
    (paper_main_projection_entry_continuous (S n) i j F ltac:(lia) ltac:(lia) HF)
    (paper_main_projection_entry_bound (S n) i j F C p ltac:(lia) ltac:(lia) HBF))).
- split; [exact HID|].
  destruct (Nat.eq_dec i j) as [E|E].
  + subst j.
    assert (HC : finite_joint_continuous (S n) (fun xs => F xs+List.nth i xs 0*DF xs)).
    { apply finite_joint_continuous_add; assumption. }
    assert (HB : finite_polynomial_bound (S n) (C+C) (S p) (fun xs => F xs+List.nth i xs 0*DF xs)).
    { apply finite_polynomial_bound_add; [|exact HBDj].
      apply (finite_polynomial_bound_degree_monotone _ _ p); [exact HBF|lia]. }
    pose proof (gaussian_iterated_coordinate_first_stein n i _ _ C (S p) (C+C) (S p)
      Hi HCj HC HBj HB (paper_main_projection_coordinate_product_derive (S n) i F DF ltac:(lia) HD)) as HS.
    assert (HIF : gaussian_iterated_integrable (S n) F).
    { exact(proj1(gaussian_coordinate_polynomial_domain _ _ _ _ HF HBF)). }
    rewrite (proj2(gaussian_iterated_add (S n) _ _ HIF HID)) in HS.
    assert (HIT : gaussian_iterated_integrable (S n) (fun xs => List.nth i xs 0*(List.nth i xs 0*F xs))).
    { exact (proj1(gaussian_coordinate_polynomial_domain _ _ C (S(S p))
        (finite_joint_continuous_times_coordinate (S n)
          (fun xs => List.nth i xs 0*F xs) i HCj ltac:(lia))
        (finite_polynomial_bound_times_coordinate (S n) C (S p)
          (fun xs => List.nth i xs 0*F xs) i HBj ltac:(lia)))). }
    destruct (gaussian_iterated_scale (S n) F (-1) HIF) as [HIN EN].
    transitivity (gaussian_iterated_expectation (S n)
      (fun xs => List.nth i xs 0*(List.nth i xs 0*F xs)+(-1)*F xs)).
    * apply gaussian_iterated_expectation_ext; intros xs Hxs.
      unfold paper_main_projection_entry; rewrite Nat.eqb_refl; ring.
    * rewrite (proj2(gaussian_iterated_add (S n) _ _ HIT HIN)) EN; lra.
  + pose proof (gaussian_iterated_coordinate_first_stein n i _ _ C (S p) C (S p)
      Hi HCj HCDj HBj HBDj (finite_coordinate_derivative_times_other (S n) i j F DF E HD)) as HS.
    rewrite HS; apply gaussian_iterated_expectation_ext; intros xs Hxs.
    unfold paper_main_projection_entry; rewrite (proj2(Nat.eqb_neq i j) E); ring.
Qed.

Lemma paper_main_projection_sum_expectation d I F G :
  (forall i, In i I -> gaussian_iterated_integrable d (F i) /\
    gaussian_iterated_integrable d (G i) /\
    gaussian_iterated_expectation d (F i)=gaussian_iterated_expectation d (G i)) ->
  gaussian_iterated_integrable d (fun xs => finite_sum (fun i => F i xs) I) /\
  gaussian_iterated_integrable d (fun xs => finite_sum (fun i => G i xs) I) /\
  gaussian_iterated_expectation d (fun xs => finite_sum (fun i => F i xs) I)=
    gaussian_iterated_expectation d (fun xs => finite_sum (fun i => G i xs) I).
Proof.
intro H.
destruct (gaussian_iterated_finite_sum d I F (fun i Hi => proj1(H i Hi))) as [HIF EF].
destruct (gaussian_iterated_finite_sum d I G (fun i Hi => proj1(proj2(H i Hi)))) as [HIG EG].
split; [exact HIF|]; split; [exact HIG|].
rewrite EF EG; apply finite_sum_ext; intros i Hi; exact(proj2(proj2(H i Hi))).
Qed.

Definition paper_main_projection_quadratic d (A : nat -> nat -> R) xs :=
  finite_sum (fun i => finite_sum (fun j => A i j*paper_main_projection_entry i j xs)
    (List.seq 0 d)) (List.seq 0 d).
Definition paper_main_projection_contraction d (A : nat -> nat -> R)
  (DF : nat -> list R -> R) xs :=
  finite_sum (fun i => finite_sum (fun j => A i j*(List.nth j xs 0*DF i xs))
    (List.seq 0 d)) (List.seq 0 d).

Theorem paper_main_projection_quadratic_stein n A F DF C p :
  finite_joint_continuous (S n) F -> finite_polynomial_bound (S n) C p F ->
  (forall i, (i<=n)%coq_nat -> finite_joint_continuous (S n) (DF i)) ->
  (forall i, (i<=n)%coq_nat -> finite_polynomial_bound (S n) C p (DF i)) ->
  (forall i, (i<=n)%coq_nat -> finite_coordinate_derivative (S n) i F (DF i)) ->
  gaussian_iterated_integrable (S n) (fun xs => paper_main_projection_quadratic (S n) A xs*F xs) /\
  gaussian_iterated_integrable (S n) (paper_main_projection_contraction (S n) A DF) /\
  gaussian_iterated_expectation (S n) (fun xs => paper_main_projection_quadratic (S n) A xs*F xs)=
    gaussian_iterated_expectation (S n) (paper_main_projection_contraction (S n) A DF).
Proof.
intros HF HBF HDF HBDF HD.
set (L := fun xs => finite_sum (fun i => finite_sum
  (fun j => A i j*(paper_main_projection_entry i j xs*F xs)) (List.seq 0 (S n))) (List.seq 0 (S n))).
assert (HL : forall xs, L xs=paper_main_projection_quadratic (S n) A xs*F xs).
{ intro xs; unfold L,paper_main_projection_quadratic.
  rewrite <- finite_sum_scale_r; apply finite_sum_ext; intros i Hi.
  rewrite <- finite_sum_scale_r; apply finite_sum_ext; intros j Hj; ring. }
assert (HS : gaussian_iterated_integrable (S n) L /\
  gaussian_iterated_integrable (S n) (paper_main_projection_contraction (S n) A DF) /\
  gaussian_iterated_expectation (S n) L=
    gaussian_iterated_expectation (S n) (paper_main_projection_contraction (S n) A DF)).
{ unfold L,paper_main_projection_contraction.
  apply paper_main_projection_sum_expectation; intros i Hi.
  apply in_seq in Hi; assert (Hin : (i<=n)%coq_nat) by lia.
  apply paper_main_projection_sum_expectation; intros j Hj.
  apply in_seq in Hj; assert (Hjn : (j<=n)%coq_nat) by lia.
  destruct (paper_main_projection_entry_stein n i j F (DF i) C p Hin Hjn
    HF (HDF i Hin) HBF (HBDF i Hin) (HD i Hin)) as [HI [HJ HE]].
  destruct (gaussian_iterated_scale (S n) _ (A i j) HI) as [HIL EL].
  destruct (gaussian_iterated_scale (S n) _ (A i j) HJ) as [HIR ER].
  split; [exact HIL|]; split; [exact HIR|]; rewrite EL ER HE; reflexivity. }
destruct HS as [HIL [HIR HE]].
split.
- apply (gaussian_iterated_integrable_ext (S n) L); [intros xs Hxs; apply HL|exact HIL].
- split; [exact HIR|].
  transitivity (gaussian_iterated_expectation (S n) L); [|exact HE].
  apply gaussian_iterated_expectation_ext; intros xs Hxs; symmetry; apply HL.
Qed.
