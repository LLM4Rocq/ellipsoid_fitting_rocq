(* Polynomial regularity packaging for actual projection integration by parts. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.CovarianceLinearImages Gaussian.FiniteSums
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateWeights Gaussian.CoordinateDerivativeDefinitions
  Gaussian.CoordinateStein Gaussian.CoordinatePolynomialContinuity
  Data.FeatureMomentsCoordinates Gaussian.SmoothCalculus Projection.Stein
  Projection.Quadratic Projection.Image Projection.Mix.
Open Scope R_scope.

Lemma paper_main_projection_regular_uniform d I (F : nat -> list R -> R) :
  (forall i, In i I -> pmdf_regular d (F i)) ->
  exists C p, 0<=C /\ forall i, In i I -> finite_polynomial_bound d C p (F i).
Proof.
induction I as [|i I IH]; intro H.
- exists 0,0%nat; split; [lra|intros j Hj; contradiction].
- destruct (H i ltac:(left; reflexivity)) as [_ [C [p HC]]].
  destruct (IH ltac:(intros j Hj; apply H; right; exact Hj)) as [D [q [HD HB]]].
  exists (C+D),(Nat.max p q); split; [pose proof(proj1 HC); lra|].
  intros j [->|Hj].
  + apply (paper_main_projection_bound_enlarge d C); [|lra].
    apply (finite_polynomial_bound_degree_monotone d C p); [exact HC|apply Nat.le_max_l].
  + apply (paper_main_projection_bound_enlarge d D); [|pose proof(proj1 HC); lra].
    apply (finite_polynomial_bound_degree_monotone d D q); [apply HB; exact Hj|apply Nat.le_max_r].
Qed.

Lemma paper_main_projection_regular_sum d I (F : nat -> list R -> R) :
  (forall i, In i I -> pmdf_regular d (F i)) ->
  pmdf_regular d (fun xs => finite_sum (fun i => F i xs) I).
Proof.
induction I as [|i I IH]; intro H; simpl.
- apply pmdf_regular_const.
- apply pmdf_regular_add.
  + apply H; left; reflexivity.
  + apply IH; intros j Hj; apply H; right; exact Hj.
Qed.

Lemma paper_main_projection_regular_linear d c : pmdf_regular d (linear_form d c).
Proof.
unfold linear_form; apply paper_main_projection_regular_sum; intros i Hi.
apply pmdf_regular_scale; apply pmdf_regular_nth; apply in_seq in Hi; lia.
Qed.

Lemma paper_main_projection_regular_quadratic d A :
  pmdf_regular d (paper_main_projection_quadratic d A).
Proof.
destruct(paper_main_projection_quadratic_regular d A) as [HC [C HB]].
split; [exact HC|exists C,2%nat; exact HB].
Qed.

Lemma paper_main_projection_regular_image d K U F C :
  (forall a, (a<K)%coq_nat -> pmdf_regular d (U a)) ->
  finite_joint_continuous K F -> finite_polynomial_bound K C 0 F ->
  pmdf_regular d (fun xs => F(paper_main_projection_image K U xs)).
Proof.
intros HU HF HB; split.
- apply paper_main_projection_image_continuous; [|exact HF].
  intros a Ha; exact(proj1(HU a Ha)).
- exists C,0%nat; apply paper_main_projection_image_bounded; exact HB.
Qed.

Theorem paper_main_projection_regular_first_stein n i F DF :
  (i<=n)%coq_nat -> pmdf_regular (S n) F -> pmdf_regular (S n) DF ->
  finite_coordinate_derivative (S n) i F DF ->
  gaussian_iterated_expectation (S n) (fun xs => List.nth i xs 0*F xs)=
    gaussian_iterated_expectation (S n) DF.
Proof.
intros Hi [HF [C [p HB]]] [HDF [D [q HDB]]] HD.
symmetry; exact(gaussian_iterated_coordinate_first_stein n i F DF C p D q Hi HF HDF HB HDB HD).
Qed.

Theorem paper_main_projection_regular_quadratic_stein n A F DF :
  pmdf_regular (S n) F ->
  (forall i, (i<=n)%coq_nat -> pmdf_regular (S n) (DF i)) ->
  (forall i, (i<=n)%coq_nat -> finite_coordinate_derivative (S n) i F (DF i)) ->
  gaussian_iterated_integrable (S n) (fun xs => paper_main_projection_quadratic (S n) A xs*F xs) /\
  gaussian_iterated_integrable (S n) (paper_main_projection_contraction (S n) A DF) /\
  gaussian_iterated_expectation (S n) (fun xs => paper_main_projection_quadratic (S n) A xs*F xs)=
    gaussian_iterated_expectation (S n) (paper_main_projection_contraction (S n) A DF).
Proof.
intros [HF [C [p HB]]] HDF HD.
destruct(paper_main_projection_regular_uniform (S n) (List.seq 0 (S n)) DF
  ltac:(intros i Hi; apply HDF; apply in_seq in Hi; lia)) as [D [q [HD0 HDB]]].
apply (paper_main_projection_quadratic_stein n A F DF (C+D) (Nat.max p q)); try assumption.
- apply (paper_main_projection_bound_enlarge (S n) C); [|lra].
  apply (finite_polynomial_bound_degree_monotone (S n) C p); [exact HB|apply Nat.le_max_l].
- intros i Hi; exact(proj1(HDF i Hi)).
- intros i Hi; apply (paper_main_projection_bound_enlarge (S n) D); [|pose proof(proj1 HB); lra].
  apply (finite_polynomial_bound_degree_monotone (S n) D q); [|apply Nat.le_max_r].
  apply HDB; apply in_seq; lia.
Qed.

Theorem paper_main_projection_regular_linear_stein n c F DF :
  pmdf_regular (S n) F ->
  (forall i, (i<=n)%coq_nat -> pmdf_regular (S n) (DF i)) ->
  (forall i, (i<=n)%coq_nat -> finite_coordinate_derivative (S n) i F (DF i)) ->
  gaussian_iterated_integrable (S n) (fun xs => linear_form (S n) c xs*F xs) /\
  gaussian_iterated_integrable (S n) (fun xs => finite_sum (fun i => c i*DF i xs) (List.seq 0 (S n))) /\
  gaussian_iterated_expectation (S n) (fun xs => linear_form (S n) c xs*F xs)=
    gaussian_iterated_expectation (S n) (fun xs => finite_sum (fun i => c i*DF i xs) (List.seq 0 (S n))).
Proof.
intros HF HDF HD.
assert (HE : forall xs, finite_sum (fun i => c i*(List.nth i xs 0*F xs)) (List.seq 0 (S n))=
    linear_form (S n) c xs*F xs).
{ intro xs; unfold linear_form; rewrite <- finite_sum_scale_r; apply finite_sum_ext; intros; ring. }
assert (HS : gaussian_iterated_integrable (S n)
  (fun xs => finite_sum (fun i => c i*(List.nth i xs 0*F xs)) (List.seq 0 (S n))) /\
  gaussian_iterated_integrable (S n) (fun xs => finite_sum (fun i => c i*DF i xs) (List.seq 0 (S n))) /\
  gaussian_iterated_expectation (S n) (fun xs => finite_sum (fun i => c i*(List.nth i xs 0*F xs)) (List.seq 0 (S n)))=
  gaussian_iterated_expectation (S n) (fun xs => finite_sum (fun i => c i*DF i xs) (List.seq 0 (S n)))).
{ apply paper_main_projection_sum_expectation; intros i Hi.
  apply in_seq in Hi; assert (Hin : (i<=n)%coq_nat) by lia.
  assert (HI : gaussian_iterated_integrable (S n) (fun xs => List.nth i xs 0*F xs)).
  { apply pmdf_regular_integrable; apply pmdf_regular_mult; [apply pmdf_regular_nth; lia|exact HF]. }
  destruct(gaussian_iterated_scale (S n) _ (c i) HI) as [HIL EL].
  destruct(gaussian_iterated_scale (S n) _ (c i) (pmdf_regular_integrable(HDF i Hin))) as [HIR ER].
  split; [exact HIL|]; split; [exact HIR|].
  rewrite EL ER (paper_main_projection_regular_first_stein n i F (DF i) Hin HF (HDF i Hin) (HD i Hin)); reflexivity. }
destruct HS as [HI [HJ HS]].
split.
- apply (gaussian_iterated_integrable_ext (S n) _ _ (fun xs _ => HE xs) HI).
- split; [exact HJ|].
  rewrite <- HS; apply gaussian_iterated_expectation_ext; intros xs Hxs; symmetry; apply HE.
Qed.
