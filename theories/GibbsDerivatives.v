From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights.
Import ListNotations.
Open Scope R_scope.

Lemma gibbs_sum_derivative (F : nat -> R -> R) (D : nat -> R) I x :
  (forall i, In i I -> derivable_pt_lim (F i) x (D i)) ->
  derivable_pt_lim (fun t => finite_sum (fun i => F i t) I) x (finite_sum D I).
Proof.
  induction I as [|i I IH]; intros HD; simpl.
  - apply derivable_pt_lim_const.
  - apply (derivable_pt_lim_plus (F i) (fun t => finite_sum (fun j => F j t) I)).
    + apply HD; simpl; auto.
    + apply IH; intros; apply HD; simpl; auto.
Qed.

Lemma gibbs_exponential_derivative c f x d :
  derivable_pt_lim f x d ->
  derivable_pt_lim (fun t => exp (c * f t)) x (exp (c * f x) * (c * d)).
Proof.
  intros HD.
  apply (derivable_pt_lim_comp (fun t => c * f t) exp x (c * d)).
  - apply derivable_pt_lim_scal; exact HD.
  - apply derivable_pt_lim_exp.
Qed.

Lemma gibbs_partition_derivative c F D I x :
  I <> [] -> (forall i, In i I -> derivable_pt_lim (F i) x (D i)) ->
  derivable_pt_lim (fun t => partition c (fun i => F i t) I) x
    (c * partition c (fun i => F i x) I * gibbs_average c (fun i => F i x) I D).
Proof.
  intros HI HD.
  assert (HZ : partition c (fun i => F i x) I <> 0).
  { pose proof (partition_positive c (fun i => F i x) I HI); lra. }
  assert (HE : finite_sum (fun i => exp (c * F i x) * (c * D i)) I =
    c * partition c (fun i => F i x) I * gibbs_average c (fun i => F i x) I D).
  { transitivity (c * finite_sum (fun i => exp (c * F i x) * D i) I).
    - rewrite <- gibbs_sum_scale; apply gibbs_sum_ext; intros; ring.
    - rewrite gibbs_average_ratio; field; exact HZ. }
  rewrite <- HE; unfold partition.
  apply gibbs_sum_derivative; intros i Hi.
  apply gibbs_exponential_derivative, HD; exact Hi.
Qed.

Theorem gibbs_weight_derivative c F D I x i :
  I <> [] -> In i I ->
  (forall j, In j I -> derivable_pt_lim (F j) x (D j)) ->
  derivable_pt_lim (fun t => gibbs_weight c (fun j => F j t) I i) x
    (c * gibbs_weight c (fun j => F j x) I i *
      (D i - gibbs_average c (fun j => F j x) I D)).
Proof.
  intros HI Hi HD.
  assert (HZ : partition c (fun j => F j x) I <> 0).
  { pose proof (partition_positive c (fun j => F j x) I HI); lra. }
  unfold gibbs_weight.
  replace (c * (exp (c * F i x) / partition c (fun j => F j x) I) *
    (D i - gibbs_average c (fun j => F j x) I D)) with
    ((exp (c * F i x) * (c * D i) * partition c (fun j => F j x) I -
      (c * partition c (fun j => F j x) I * gibbs_average c (fun j => F j x) I D) *
      exp (c * F i x)) / Rsqr (partition c (fun j => F j x) I)).
  - apply (derivable_pt_lim_div (fun t => exp (c * F i t))
      (fun t => partition c (fun j => F j t) I)).
    + apply gibbs_exponential_derivative, HD; exact Hi.
    + apply gibbs_partition_derivative; assumption.
    + exact HZ.
  - unfold Rsqr; field; exact HZ.
Qed.

Theorem gibbs_average_derivative c F D U V I x :
  I <> [] ->
  (forall i, In i I -> derivable_pt_lim (F i) x (D i)) ->
  (forall i, In i I -> derivable_pt_lim (U i) x (V i)) ->
  derivable_pt_lim (fun t => gibbs_average c (fun i => F i t) I (fun i => U i t)) x
    (gibbs_average c (fun i => F i x) I V +
     c * gibbs_covariance c (fun i => F i x) I (fun i => U i x) D).
Proof.
  intros HI HD HU.
  set (w := gibbs_weight c (fun i => F i x) I).
  set (m := gibbs_average c (fun i => F i x) I D).
  assert (HE : finite_sum (fun i => c * w i * (D i - m) * U i x + w i * V i) I =
    gibbs_average c (fun i => F i x) I V +
    c * gibbs_covariance c (fun i => F i x) I (fun i => U i x) D).
  { transitivity (finite_sum (fun i =>
      w i * V i + c * (w i * (U i x * D i)) + (- c * m) * (w i * U i x)) I).
    - apply gibbs_sum_ext; intros; ring.
    - rewrite !gibbs_sum_add, !gibbs_sum_scale.
      unfold m, w; unfold gibbs_covariance, gibbs_average; ring. }
  rewrite <- HE; unfold gibbs_average.
  apply gibbs_sum_derivative; intros i Hi.
  apply (derivable_pt_lim_mult (fun t => gibbs_weight c (fun j => F j t) I i) (U i)).
  - apply gibbs_weight_derivative; assumption.
  - apply HU; exact Hi.
Qed.

Theorem soft_max_curve_derivative c F D I x :
  c <> 0 -> I <> [] ->
  (forall i, In i I -> derivable_pt_lim (F i) x (D i)) ->
  derivable_pt_lim (fun t => soft_max c (fun i => F i t) I) x
    (gibbs_average c (fun i => F i x) I D).
Proof.
  intros Hc HI HD.
  assert (HZ : 0 < partition c (fun i => F i x) I)
    by (apply partition_positive; exact HI).
  unfold soft_max; change (derivable_pt_lim
    (fun t => ln (partition c (fun i => F i t) I) / c) x
    (gibbs_average c (fun i => F i x) I D)).
  replace (gibbs_average c (fun i => F i x) I D) with
    ((/ partition c (fun i => F i x) I *
      (c * partition c (fun i => F i x) I * gibbs_average c (fun i => F i x) I D)) / c).
  - apply derivable_pt_lim_div_scal.
    apply (derivable_pt_lim_comp (fun t => partition c (fun i => F i t) I) ln).
    + apply gibbs_partition_derivative; assumption.
    + apply derivable_pt_lim_ln; exact HZ.
  - field; split; lra.
Qed.

(* The signed temperature gives exactly the soft minimum used in the paper. *)
Lemma soft_min_signed_identity beta f I :
  beta <> 0 -> soft_min beta f I = soft_max (- beta) f I.
Proof.
  intros Hbeta; unfold soft_min, soft_max.
  assert (HE : finite_sum (fun i => exp (beta * - f i)) I =
    finite_sum (fun i => exp (- beta * f i)) I).
  { apply gibbs_sum_ext; intros; f_equal; ring. }
  rewrite HE; field; exact Hbeta.
Qed.

Theorem soft_min_curve_derivative beta F D I x :
  beta <> 0 -> I <> [] ->
  (forall i, In i I -> derivable_pt_lim (F i) x (D i)) ->
  derivable_pt_lim (fun t => soft_min beta (fun i => F i t) I) x
    (gibbs_average (- beta) (fun i => F i x) I D).
Proof.
  intros Hbeta HI HD.
  apply (derivable_pt_lim_ext (fun t => soft_max (- beta) (fun i => F i t) I)).
  - intros t; symmetry; apply soft_min_signed_identity; exact Hbeta.
  - apply soft_max_curve_derivative; try assumption; lra.
Qed.
