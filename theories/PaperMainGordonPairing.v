(* The coordinate Hessian pairing is exactly the Gibbs covariance contraction. *)
From Stdlib Require Import Reals List Lra FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights Cumulants
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  PaperMainGordonCovariance PaperMainGordonCalculus PaperMainGordonCoordinates.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_covariance_ext c f I u v u' v' :
  (forall i, In i I -> u i = u' i) ->
  (forall i, In i I -> v i = v' i) ->
  gibbs_covariance c f I u v = gibbs_covariance c f I u' v'.
Proof.
intros Hu Hv.
unfold gibbs_covariance.
rewrite (gibbs_average_ext c f I u u' Hu), (gibbs_average_ext c f I v v' Hv).
f_equal; apply gibbs_average_ext; intros i Hi; rewrite (Hu i Hi), (Hv i Hi); reflexivity.
Qed.

Lemma paper_main_gordon_covariance_sum_left c f I A (U : nat -> nat -> R) v :
  finite_sum (fun a => gibbs_covariance c f I (U a) v) A =
  gibbs_covariance c f I (fun i => finite_sum (fun a => U a i) A) v.
Proof.
unfold gibbs_covariance.
rewrite paper_main_gordon_sum_sub, finite_sum_scale_r, !paper_main_gordon_average_sum.
f_equal; apply gibbs_average_ext; intros i Hi; apply finite_sum_scale_r.
Qed.

Lemma paper_main_gordon_hessian_ext beta gamma H U V U' V' Y S :
  (forall y s, In y Y -> In s S -> U y s = U' y s) ->
  (forall y s, In y Y -> In s S -> V y s = V' y s) ->
  paper_main_gordon_hessian beta gamma H U V Y S =
  paper_main_gordon_hessian beta gamma H U' V' Y S.
Proof.
intros HU HV.
unfold paper_main_gordon_hessian, paper_main_gordon_outer, paper_main_gordon_inner.
f_equal.
- f_equal; apply gibbs_average_ext; intros y Hy.
  apply paper_main_gordon_covariance_ext; intros s Hs; [apply HU|apply HV]; assumption.
- f_equal; apply paper_main_gordon_covariance_ext; intros y Hy;
    apply gibbs_average_ext; intros s Hs; [apply HU|apply HV]; assumption.
Qed.

Lemma paper_main_gordon_hessian_sym beta gamma H U V Y S :
  paper_main_gordon_hessian beta gamma H U V Y S =
  paper_main_gordon_hessian beta gamma H V U Y S.
Proof.
unfold paper_main_gordon_hessian, paper_main_gordon_outer, paper_main_gordon_inner.
f_equal.
- f_equal; apply gibbs_average_ext; intros y Hy; apply gibbs_covariance_sym.
- f_equal; apply gibbs_covariance_sym.
Qed.

Lemma paper_main_gordon_hessian_scale_left beta gamma H U V Y S c :
  paper_main_gordon_hessian beta gamma H (fun y s => c * U y s) V Y S =
  c * paper_main_gordon_hessian beta gamma H U V Y S.
Proof.
unfold paper_main_gordon_hessian, paper_main_gordon_outer, paper_main_gordon_inner.
assert (HE : (fun y => gibbs_covariance gamma (H y) S (fun s => c * U y s) (V y)) =
  (fun y => c * gibbs_covariance gamma (H y) S (U y) (V y))).
{ extensionality y; apply gibbs_covariance_scale_left. }
assert (HM : (fun y => gibbs_average gamma (H y) S (fun s => c * U y s)) =
  (fun y => c * gibbs_average gamma (H y) S (U y))).
{ extensionality y; apply gibbs_average_scale. }
rewrite HE, HM, gibbs_average_scale, gibbs_covariance_scale_left; ring.
Qed.

Lemma paper_main_gordon_hessian_scale_right beta gamma H U V Y S c :
  paper_main_gordon_hessian beta gamma H U (fun y s => c * V y s) Y S =
  c * paper_main_gordon_hessian beta gamma H U V Y S.
Proof.
rewrite (paper_main_gordon_hessian_sym beta gamma H U (fun y s => c * V y s) Y S).
rewrite paper_main_gordon_hessian_scale_left.
rewrite (paper_main_gordon_hessian_sym beta gamma H V U Y S); reflexivity.
Qed.

Lemma paper_main_gordon_hessian_sum_left beta gamma H (U : nat -> nat -> nat -> R)
    V Y S A :
  finite_sum (fun a => paper_main_gordon_hessian beta gamma H (U a) V Y S) A =
  paper_main_gordon_hessian beta gamma H
    (fun y s => finite_sum (fun a => U a y s) A) V Y S.
Proof.
unfold paper_main_gordon_hessian, paper_main_gordon_outer, paper_main_gordon_inner.
rewrite paper_main_gordon_sum_sub, !finite_sum_scale.
f_equal.
- f_equal; rewrite paper_main_gordon_average_sum.
  apply gibbs_average_ext; intros y Hy; apply paper_main_gordon_covariance_sum_left.
- f_equal; rewrite paper_main_gordon_covariance_sum_left.
  apply paper_main_gordon_covariance_ext.
  + intros y Hy; apply paper_main_gordon_average_sum.
  + intros y Hy; reflexivity.
Qed.

Lemma paper_main_gordon_hessian_sum_right beta gamma H U (V : nat -> nat -> nat -> R)
    Y S B :
  finite_sum (fun b => paper_main_gordon_hessian beta gamma H U (V b) Y S) B =
  paper_main_gordon_hessian beta gamma H U
    (fun y s => finite_sum (fun b => V b y s) B) Y S.
Proof.
transitivity (finite_sum (fun b => paper_main_gordon_hessian beta gamma H (V b) U Y S) B).
- apply finite_sum_ext; intros b Hb; apply paper_main_gordon_hessian_sym.
- rewrite paper_main_gordon_hessian_sum_left; apply paper_main_gordon_hessian_sym.
Qed.

Lemma paper_main_gordon_hessian_bilinear beta gamma H U V Y S A B c e :
  finite_sum (fun a => finite_sum (fun b =>
    c a * e b * paper_main_gordon_hessian beta gamma H (U a) (V b) Y S) B) A =
  paper_main_gordon_hessian beta gamma H
    (fun y s => finite_sum (fun a => c a * U a y s) A)
    (fun y s => finite_sum (fun b => e b * V b y s) B) Y S.
Proof.
rewrite <- paper_main_gordon_hessian_sum_left.
apply finite_sum_ext; intros a Ha.
rewrite <- paper_main_gordon_hessian_sum_right.
apply finite_sum_ext; intros b Hb.
rewrite paper_main_gordon_hessian_scale_left, paper_main_gordon_hessian_scale_right; ring.
Qed.

Lemma paper_main_gordon_delta_sum K J y s c :
  (J y s < K)%nat ->
  finite_sum (fun a => c a * paper_main_gordon_delta J a y s) (List.seq 0 K) = c (J y s).
Proof.
intros HJ.
transitivity (finite_sum (fun a => if Nat.eqb a (J y s) then c (J y s) else 0) (List.seq 0 K)).
- apply finite_sum_ext; intros a Ha; unfold paper_main_gordon_delta.
  destruct (Nat.eq_dec (J y s) a) as [Heq|Hne].
  + subst a; simpl; rewrite Nat.eqb_refl; ring.
  + assert (E : Nat.eqb a (J y s) = false) by (apply Nat.eqb_neq; congruence).
    rewrite E; simpl; ring.
- apply finite_sum_delta; exact HJ.
Qed.

Lemma paper_main_gordon_gram_pairing K p P beta gamma H J Y S :
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  finite_sum (fun a => finite_sum (fun b => gaussian_covariance_entry p P a b *
    paper_main_gordon_hessian beta gamma H
      (paper_main_gordon_delta J a) (paper_main_gordon_delta J b) Y S)
    (List.seq 0 K)) (List.seq 0 K) =
  paper_main_gordon_contraction beta gamma H Y S
    (paper_main_gordon_gram (fun y s k => P (J y s) k) (List.seq 0 p)).
Proof.
intros HJ.
transitivity (finite_sum (fun a => finite_sum (fun k => finite_sum (fun b =>
  P a k * P b k * paper_main_gordon_hessian beta gamma H
    (paper_main_gordon_delta J a) (paper_main_gordon_delta J b) Y S)
  (List.seq 0 K)) (List.seq 0 p)) (List.seq 0 K)).
- apply finite_sum_ext; intros a Ha.
  rewrite finite_sum_swap.
  apply finite_sum_ext; intros b Hb.
  unfold gaussian_covariance_entry; symmetry; apply finite_sum_scale_r.
- rewrite finite_sum_swap.
  transitivity (finite_sum (fun k => paper_main_gordon_hessian beta gamma H
    (fun y s => P (J y s) k) (fun y s => P (J y s) k) Y S) (List.seq 0 p)).
  + apply finite_sum_ext; intros k Hk.
    rewrite paper_main_gordon_hessian_bilinear.
    apply paper_main_gordon_hessian_ext;
      intros y s Hy Hs; apply paper_main_gordon_delta_sum; apply HJ; assumption.
  + transitivity (finite_sum (fun k => nested_gibbs_curvature beta gamma H
      (fun y s => P (J y s) k) Y S 0) (List.seq 0 p)).
    * apply finite_sum_ext; intros k Hk; apply paper_main_gordon_hessian_diagonal.
    * apply paper_main_gordon_hessian_gram.
Qed.

Theorem paper_main_gordon_pairing_identity K p q P Q beta gamma J Y S xs :
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  gaussian_covariance_pairing K p q P Q
    (fun a b => paper_main_gordon_second beta gamma J Y S a b xs) =
  paper_main_gordon_contraction beta gamma (paper_main_gordon_scores J xs) Y S
    (paper_main_gordon_gram (fun y s k => P (J y s) k) (List.seq 0 p)) -
  paper_main_gordon_contraction beta gamma (paper_main_gordon_scores J xs) Y S
    (paper_main_gordon_gram (fun y s k => Q (J y s) k) (List.seq 0 q)).
Proof.
intros HJ.
unfold gaussian_covariance_pairing, paper_main_gordon_second.
rewrite <- (paper_main_gordon_gram_pairing K p P beta gamma
  (paper_main_gordon_scores J xs) J Y S HJ).
rewrite <- (paper_main_gordon_gram_pairing K q Q beta gamma
  (paper_main_gordon_scores J xs) J Y S HJ).
rewrite <- finite_sum_minus.
apply finite_sum_ext; intros a Ha; rewrite <- finite_sum_minus.
apply finite_sum_ext; intros b Hb; ring.
Qed.
