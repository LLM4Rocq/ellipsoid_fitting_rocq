(* Exponential moments of the finite bilinear Gaussian matrix tests. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions GaussianDefinitions GaussianProductDefinitions
  GaussianProduct GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCoordinateDefinitions
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonLipschitz
  PaperMainGordonBilinear PaperMainGordonWidth PaperMainGordonContinuity
  PaperMainGaussianLinearMGF.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gaussian_dot_scale_left d a b t :
  paper_main_gordon_dot d (fun i => t*a i) b = t*paper_main_gordon_dot d a b.
Proof.
unfold paper_main_gordon_dot; rewrite <- finite_sum_scale.
apply finite_sum_ext; intros; ring.
Qed.

Theorem paper_main_gaussian_scaled_vector_mgf d a t :
  gaussian_covariance_domain d (fun xs =>
    exp (t*paper_main_gordon_dot d a (fun i => List.nth i xs 0))) /\
  gaussian_iterated_expectation d (fun xs =>
    exp (t*paper_main_gordon_dot d a (fun i => List.nth i xs 0))) =
    exp (t^2*paper_main_gordon_dot d a a/2).
Proof.
destruct (paper_main_gaussian_vector_mgf d (fun i => t*a i)) as [HI HV].
pose proof (paper_main_gaussian_vector_mgf_absolute d (fun i => t*a i)) as HA.
assert (HE : (fun xs => exp(paper_main_gordon_dot d (fun i => t*a i) (fun i => nth i xs 0))) =
  (fun xs => exp(t*paper_main_gordon_dot d a (fun i => nth i xs 0)))).
{ apply functional_extensionality; intros xs; rewrite paper_main_gaussian_dot_scale_left; reflexivity. }
rewrite HE in HI, HV, HA; rewrite paper_main_gordon_dot_scale in HV.
split; [|exact HV].
split; [exact HI|]; split; [exact HA|]; split;
  apply gaussian_iterated_has_expectation_correct; assumption.
Qed.

Lemma paper_main_gaussian_scaled_vector_continuous d a t :
  finite_joint_continuous d (fun xs =>
    exp (t*paper_main_gordon_dot d a (fun i => List.nth i xs 0))).
Proof.
apply paper_main_gordon_joint_exp.
assert (HE : (fun xs => t*paper_main_gordon_dot d a (fun i => nth i xs 0)) =
  (fun xs => paper_main_gordon_dot d (fun i => t*a i) (fun i => nth i xs 0))).
{ apply functional_extensionality; intros xs; symmetry; apply paper_main_gaussian_dot_scale_left. }
rewrite HE; apply paper_main_gordon_dot_continuous.
Qed.

Theorem paper_main_gaussian_matrix_mgf N M u v t :
  gaussian_covariance_domain (N*M) (fun xs =>
    exp (t*paper_main_gordon_matrix_value N M u v xs)) /\
  gaussian_iterated_expectation (N*M) (fun xs =>
    exp (t*paper_main_gordon_matrix_value N M u v xs)) =
    exp (t^2*paper_main_gordon_dot N u u*paper_main_gordon_dot M v v/2).
Proof.
set (P := paper_main_gordon_matrix_loading N M (fun _ => u) (fun _ => v)).
destruct (paper_main_gaussian_scaled_vector_mgf (N*M) (P 0%nat) t) as [HD HV].
assert (HE : (fun xs => exp(t*paper_main_gordon_dot (N*M) (P 0%nat) (fun i => nth i xs 0))) =
  (fun xs => exp(t*paper_main_gordon_matrix_value N M u v xs))).
{ apply functional_extensionality; intros xs; f_equal; f_equal.
  change (gaussian_covariance_row (N*M) P 0 xs = paper_main_gordon_matrix_value N M u v xs).
  unfold P; apply paper_main_gordon_raw_matrix_row. }
rewrite HE in HD, HV.
assert (HC : paper_main_gordon_dot (N*M) (P 0%nat) (P 0%nat) =
  paper_main_gordon_dot N u u*paper_main_gordon_dot M v v).
{ change (gaussian_covariance_entry (N*M) P 0 0 = paper_main_gordon_dot N u u*paper_main_gordon_dot M v v).
  unfold P; apply paper_main_gordon_raw_matrix_covariance. }
rewrite HC in HV; split; [exact HD|].
rewrite HV; f_equal; field.
Qed.

Lemma paper_main_gaussian_matrix_exponential_continuous N M u v t :
  finite_joint_continuous (N*M) (fun xs =>
    exp (t*paper_main_gordon_matrix_value N M u v xs)).
Proof.
set (P := paper_main_gordon_matrix_loading N M (fun _ => u) (fun _ => v)).
assert (HE : (fun xs => exp(t*paper_main_gordon_matrix_value N M u v xs)) =
  (fun xs => exp(t*paper_main_gordon_dot (N*M) (P 0%nat) (fun i => nth i xs 0)))).
{ apply functional_extensionality; intros xs; f_equal; f_equal; symmetry.
  change (gaussian_covariance_row (N*M) P 0 xs = paper_main_gordon_matrix_value N M u v xs).
  unfold P; apply paper_main_gordon_raw_matrix_row. }
rewrite HE; apply paper_main_gaussian_scaled_vector_continuous.
Qed.

Corollary paper_main_gaussian_unit_matrix_mgf N M u v t :
  paper_main_gordon_dot N u u = 1 -> paper_main_gordon_dot M v v = 1 ->
  gaussian_covariance_domain (N*M) (fun xs => exp (t*paper_main_gordon_matrix_value N M u v xs)) /\
  gaussian_iterated_expectation (N*M) (fun xs => exp (t*paper_main_gordon_matrix_value N M u v xs)) =
    exp (t^2/2).
Proof.
intros Hu Hv; destruct (paper_main_gaussian_matrix_mgf N M u v t) as [HD HE].
split; [exact HD|].
rewrite HE, Hu, Hv; f_equal; field.
Qed.
