(* Linear exponential moments for independent standard Gaussian coordinates. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianExpectation GaussianProductDefinitions
  GaussianProduct SoftDefinitions GaussianCovarianceSums PaperMainGordonProcessCovariance
  PaperMainGaussianLinearDensity.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gaussian_linear_mgf t :
  gaussian_integral_exists (fun x => exp (t*x)) /\
  gaussian_absolutely_integrable (fun x => exp (t*x)) /\
  gaussian_expectation (fun x => exp (t*x)) = exp (t^2/2).
Proof.
destruct (paper_main_gaussian_from_density (fun x => exp(t*x)) (exp(t^2/2))
  (paper_main_gaussian_linear_density_integral t)) as [HI HE].
split; [exact HI|]; split; [|exact HE].
unfold gaussian_absolutely_integrable.
apply gaussian_integral_exists_ext with (f := fun x => exp(t*x)); [|exact HI].
intros x; rewrite Rabs_pos_eq by (left; apply exp_pos); reflexivity.
Qed.

Lemma paper_main_gaussian_linear_cons d a x xs :
  paper_main_gordon_dot (S d) a (fun i => List.nth i (x::xs) 0) =
  a 0%nat*x + paper_main_gordon_dot d (fun i => a (S i)) (fun i => List.nth i xs 0).
Proof.
unfold paper_main_gordon_dot.
change (a 0%nat*x + finite_sum (fun i => a i * nth i (x::xs) 0) (List.seq 1 d) =
  a 0%nat*x + finite_sum (fun i => a (S i)*nth i xs 0) (List.seq 0 d)).
rewrite finite_sum_seq_shift; reflexivity.
Qed.

Lemma paper_main_gaussian_variance_cons d a :
  paper_main_gordon_dot (S d) a a =
  (a 0%nat)^2 + paper_main_gordon_dot d (fun i => a (S i)) (fun i => a (S i)).
Proof.
unfold paper_main_gordon_dot.
change (a 0%nat*a 0%nat + finite_sum (fun i => a i*a i) (List.seq 1 d) =
  (a 0%nat)^2 + finite_sum (fun i => a (S i)*a (S i)) (List.seq 0 d)).
rewrite (finite_sum_seq_shift (fun i => a i*a i) 1 d).
change (a 0%nat*a 0%nat + finite_sum (fun i => a (S i)*a (S i)) (List.seq 0 d) =
  (a 0%nat)^2 + finite_sum (fun i => a (S i)*a (S i)) (List.seq 0 d)).
ring.
Qed.

Theorem paper_main_gaussian_vector_mgf d a :
  gaussian_iterated_integrable d (fun xs =>
    exp (paper_main_gordon_dot d a (fun i => List.nth i xs 0))) /\
  gaussian_iterated_expectation d (fun xs =>
    exp (paper_main_gordon_dot d a (fun i => List.nth i xs 0))) =
    exp (paper_main_gordon_dot d a a / 2).
Proof.
revert a; induction d as [|d IH]; intros a.
- change (True /\ exp 0 = exp (0/2)); split; [exact I|f_equal; field].
- destruct (IH (fun i => a (S i))) as [HI HV].
  destruct (paper_main_gaussian_linear_mgf (a 0%nat)) as [H0 [HA0 HV0]].
  assert (HC : forall x, (fun xs => exp (paper_main_gordon_dot (S d) a (fun i => nth i (x::xs) 0))) =
    (fun xs => exp (a 0%nat*x)*exp (paper_main_gordon_dot d (fun i => a (S i)) (fun i => nth i xs 0)))).
  { intros x; apply functional_extensionality; intros xs.
    rewrite paper_main_gaussian_linear_cons, exp_plus; reflexivity. }
  assert (HS : forall x,
    gaussian_iterated_integrable d (fun xs => exp (paper_main_gordon_dot (S d) a (fun i => nth i (x::xs) 0))) /\
    gaussian_iterated_expectation d (fun xs => exp (paper_main_gordon_dot (S d) a (fun i => nth i (x::xs) 0))) =
      exp(a 0%nat*x)*exp(paper_main_gordon_dot d (fun i => a(S i)) (fun i => a(S i))/2)).
  { intros x; rewrite HC.
    destruct (gaussian_iterated_scale d _ (exp(a 0%nat*x)) HI) as [HJ HE].
    split; [exact HJ|rewrite HE, HV; reflexivity]. }
  assert (HE : (fun x => gaussian_iterated_expectation d (fun xs =>
    exp(paper_main_gordon_dot (S d) a (fun i => nth i (x::xs) 0)))) =
    (fun x => exp(paper_main_gordon_dot d (fun i => a(S i)) (fun i => a(S i))/2)*exp(a 0%nat*x))).
  { apply functional_extensionality; intros x; rewrite (proj2 (HS x)); ring. }
  split.
  + change ((forall x, gaussian_iterated_integrable d (fun xs =>
      exp(paper_main_gordon_dot (S d) a (fun i => nth i (x::xs) 0)))) /\
      gaussian_integral_exists (fun x => gaussian_iterated_expectation d (fun xs =>
      exp(paper_main_gordon_dot (S d) a (fun i => nth i (x::xs) 0))))).
    split; [intros x; apply HS|].
    rewrite HE; apply gaussian_integral_exists_scale; exact H0.
  + change (gaussian_expectation (fun x => gaussian_iterated_expectation d (fun xs =>
      exp(paper_main_gordon_dot (S d) a (fun i => nth i (x::xs) 0)))) =
      exp(paper_main_gordon_dot (S d) a a/2)).
    rewrite HE, gaussian_expectation_scale by exact H0.
    rewrite HV0, paper_main_gaussian_variance_cons, <-exp_plus; f_equal; field.
Qed.

Lemma paper_main_gaussian_vector_mgf_absolute d a :
  gaussian_iterated_absolutely_integrable d (fun xs =>
    exp (paper_main_gordon_dot d a (fun i => List.nth i xs 0))).
Proof.
unfold gaussian_iterated_absolutely_integrable.
eapply gaussian_iterated_integrable_ext; [|exact (proj1 (paper_main_gaussian_vector_mgf d a))].
intros xs Hxs; rewrite Rabs_pos_eq by (left; apply exp_pos); reflexivity.
Qed.
