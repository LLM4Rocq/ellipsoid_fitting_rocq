(* Finite covariance algebra for Gordon's Gaussian min-max comparison.
   The score, weights and curvature are the already differentiated Gibbs
   functions. No Gaussian comparison or concentration theorem is assumed. *)
From Stdlib Require Import Reals List Lra FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights
  GibbsNested GibbsMomentBounds Cubic.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_sum_sub (f g : nat -> R) (I : list nat) :
  finite_sum (fun i => f i - g i) I = finite_sum f I - finite_sum g I.
Proof. induction I as [|i I IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma paper_main_gordon_average_sum (c : R) (f : nat -> R)
    (I K : list nat) (h : nat -> nat -> R) :
  finite_sum (fun k => gibbs_average c f I (h k)) K =
  gibbs_average c f I (fun i => finite_sum (fun k => h k i) K).
Proof.
unfold gibbs_average.
rewrite cubic_sum_swap.
apply gibbs_sum_ext; intros i Hi.
rewrite gibbs_sum_scale; reflexivity.
Qed.

Lemma paper_main_gordon_average_product (c e : R) (f g : nat -> R)
    (I J : list nat) (u v : nat -> R) :
  gibbs_average c f I u * gibbs_average e g J v =
  gibbs_average c f I (fun i =>
    gibbs_average e g J (fun j => u i * v j)).
Proof.
transitivity (gibbs_average c f I (fun i => gibbs_average e g J v * u i)).
- rewrite gibbs_average_scale; ring.
- apply gibbs_average_ext; intros i Hi.
  rewrite gibbs_average_scale; ring.
Qed.

Lemma paper_main_gordon_average_sub (c : R) (f : nat -> R)
    (I : list nat) (u v : nat -> R) :
  gibbs_average c f I (fun i => u i - v i) =
  gibbs_average c f I u - gibbs_average c f I v.
Proof.
unfold gibbs_average.
rewrite <- paper_main_gordon_sum_sub.
apply gibbs_sum_ext; intros i Hi; ring.
Qed.

Lemma paper_main_gordon_covariance_sum (c : R) (f : nat -> R)
    (I K : list nat) (B : nat -> nat -> R) :
  finite_sum (fun k => gibbs_covariance c f I (B k) (B k)) K =
  gibbs_average c f I (fun i => finite_sum (fun k => B k i * B k i) K) -
  gibbs_average c f I (fun i => gibbs_average c f I
    (fun j => finite_sum (fun k => B k i * B k j) K)).
Proof.
unfold gibbs_covariance.
rewrite paper_main_gordon_sum_sub.
f_equal.
- apply paper_main_gordon_average_sum.
- transitivity (finite_sum (fun k => gibbs_average c f I (fun i =>
    gibbs_average c f I (fun j => B k i * B k j))) K).
  + apply gibbs_sum_ext; intros k Hk; apply paper_main_gordon_average_product.
  + rewrite paper_main_gordon_average_sum.
    apply gibbs_average_ext; intros i Hi.
    apply paper_main_gordon_average_sum.
Qed.

Definition paper_main_gordon_outer (beta gamma : R) (H : nat -> nat -> R)
    (Y S : list nat) (f : nat -> R) : R :=
  gibbs_average (-beta) (fun y => soft_max gamma (H y) S) Y f.

Definition paper_main_gordon_inner (gamma : R) (H : nat -> nat -> R)
    (S : list nat) (y : nat) (f : nat -> R) : R :=
  gibbs_average gamma (H y) S f.

Definition paper_main_gordon_kernel_average (gamma : R) (H : nat -> nat -> R)
    (S : list nat) (C : nat -> nat -> nat -> nat -> R) (y z : nat) : R :=
  paper_main_gordon_inner gamma H S y (fun s =>
    paper_main_gordon_inner gamma H S z (fun t => C y s z t)).

Definition paper_main_gordon_contraction (beta gamma : R) (H : nat -> nat -> R)
    (Y S : list nat) (C : nat -> nat -> nat -> nat -> R) : R :=
  gamma * paper_main_gordon_outer beta gamma H Y S
    (fun y => paper_main_gordon_inner gamma H S y (fun s => C y s y s)) -
  (gamma + beta) * paper_main_gordon_outer beta gamma H Y S
    (fun y => paper_main_gordon_kernel_average gamma H S C y y) +
  beta * paper_main_gordon_outer beta gamma H Y S
    (fun y => paper_main_gordon_outer beta gamma H Y S
      (fun z => paper_main_gordon_kernel_average gamma H S C y z)).

Definition paper_main_gordon_gram (B : nat -> nat -> nat -> R)
    (K : list nat) (y s z t : nat) : R :=
  finite_sum (fun k => B y s k * B z t k) K.

Lemma paper_main_gordon_averaged_gram (gamma : R) (H : nat -> nat -> R)
    (S K : list nat) (B : nat -> nat -> nat -> R) (y z : nat) :
  finite_sum (fun k =>
    paper_main_gordon_inner gamma H S y (fun s => B y s k) *
    paper_main_gordon_inner gamma H S z (fun t => B z t k)) K =
  paper_main_gordon_kernel_average gamma H S (paper_main_gordon_gram B K) y z.
Proof.
unfold paper_main_gordon_inner, paper_main_gordon_kernel_average,
  paper_main_gordon_gram.
unfold paper_main_gordon_inner.
transitivity (finite_sum (fun k => gibbs_average gamma (H y) S (fun s =>
  gibbs_average gamma (H z) S (fun t => B y s k * B z t k))) K).
- apply gibbs_sum_ext; intros k Hk; apply paper_main_gordon_average_product.
- rewrite paper_main_gordon_average_sum.
  apply gibbs_average_ext; intros s Hs.
  apply paper_main_gordon_average_sum.
Qed.

Lemma paper_main_gordon_curvatureE (beta gamma : R) (H b : nat -> nat -> R)
    (Y S : list nat) :
  nested_gibbs_curvature beta gamma H b Y S 0 =
  gamma * paper_main_gordon_outer beta gamma H Y S
    (fun y => gibbs_covariance gamma (H y) S (b y) (b y)) -
  beta * gibbs_covariance (-beta) (fun y => soft_max gamma (H y) S) Y
    (fun y => paper_main_gordon_inner gamma H S y (b y))
    (fun y => paper_main_gordon_inner gamma H S y (b y)).
Proof.
assert (H0 : affine_scores H b 0 = H).
{ extensionality y; extensionality s; unfold affine_scores; ring. }
unfold nested_gibbs_curvature, inner_scores, inner_variances, inner_means,
  paper_main_gordon_outer, paper_main_gordon_inner, gibbs_variance.
rewrite H0; reflexivity.
Qed.

Lemma paper_main_gordon_contraction_mono (beta gamma : R) (H : nat -> nat -> R)
    (Y S : list nat) (C D : nat -> nat -> nat -> nat -> R) :
  0 <= beta -> Y <> [] -> S <> [] ->
  (forall y s t, In y Y -> In s S -> In t S -> C y s y t = D y s y t) ->
  (forall y z s t, In y Y -> In z Y -> In s S -> In t S ->
    y <> z -> D y s z t <= C y s z t) ->
  paper_main_gordon_contraction beta gamma H Y S D <=
  paper_main_gordon_contraction beta gamma H Y S C.
Proof.
intros Hb HY HS Hsame Hcross.
assert (Hdiag : paper_main_gordon_outer beta gamma H Y S
  (fun y => paper_main_gordon_inner gamma H S y (fun s => D y s y s)) =
  paper_main_gordon_outer beta gamma H Y S
  (fun y => paper_main_gordon_inner gamma H S y (fun s => C y s y s))).
{ unfold paper_main_gordon_outer, paper_main_gordon_inner.
  apply gibbs_average_ext; intros y Hy.
  apply gibbs_average_ext; intros s Hs; symmetry; apply Hsame; assumption. }
assert (Hwithin : paper_main_gordon_outer beta gamma H Y S
  (fun y => paper_main_gordon_kernel_average gamma H S D y y) =
  paper_main_gordon_outer beta gamma H Y S
  (fun y => paper_main_gordon_kernel_average gamma H S C y y)).
{ unfold paper_main_gordon_outer, paper_main_gordon_kernel_average,
    paper_main_gordon_inner.
  apply gibbs_average_ext; intros y Hy.
  apply gibbs_average_ext; intros s Hs.
  apply gibbs_average_ext; intros t Ht; symmetry; apply Hsame; assumption. }
unfold paper_main_gordon_contraction; rewrite Hdiag, Hwithin.
apply Rplus_le_compat_l; apply Rmult_le_compat_l; [exact Hb|].
unfold paper_main_gordon_outer, paper_main_gordon_kernel_average,
  paper_main_gordon_inner.
apply gibbs_average_monotone; [exact HY|]; intros y Hy.
apply gibbs_average_monotone; [exact HY|]; intros z Hz.
apply gibbs_average_monotone; [exact HS|]; intros s Hs.
apply gibbs_average_monotone; [exact HS|]; intros t Ht.
destruct (Nat.eq_dec y z) as [->|Hneq].
- rewrite Hsame by assumption; apply Rle_refl.
- apply Hcross; assumption.
Qed.

Lemma paper_main_gordon_hessian_gram (beta gamma : R) (H : nat -> nat -> R)
    (Y S K : list nat) (B : nat -> nat -> nat -> R) :
  finite_sum (fun k => nested_gibbs_curvature beta gamma H
    (fun y s => B y s k) Y S 0) K =
  paper_main_gordon_contraction beta gamma H Y S (paper_main_gordon_gram B K).
Proof.
assert (HI : finite_sum (fun k => paper_main_gordon_outer beta gamma H Y S
  (fun y => gibbs_covariance gamma (H y) S (fun s => B y s k)
    (fun s => B y s k))) K =
  paper_main_gordon_outer beta gamma H Y S
    (fun y => paper_main_gordon_inner gamma H S y
      (fun s => paper_main_gordon_gram B K y s y s)) -
  paper_main_gordon_outer beta gamma H Y S
    (fun y => paper_main_gordon_kernel_average gamma H S (paper_main_gordon_gram B K) y y)).
{ unfold paper_main_gordon_outer.
  rewrite paper_main_gordon_average_sum.
  transitivity (gibbs_average (-beta) (fun y => soft_max gamma (H y) S) Y
    (fun y => paper_main_gordon_inner gamma H S y
      (fun s => paper_main_gordon_gram B K y s y s) -
      paper_main_gordon_kernel_average gamma H S (paper_main_gordon_gram B K) y y)).
  - apply gibbs_average_ext; intros y Hy.
    unfold paper_main_gordon_kernel_average, paper_main_gordon_inner,
      paper_main_gordon_gram; apply paper_main_gordon_covariance_sum.
  - apply paper_main_gordon_average_sub. }
assert (HO : finite_sum (fun k => gibbs_covariance (-beta)
  (fun y => soft_max gamma (H y) S) Y
  (fun y => paper_main_gordon_inner gamma H S y (fun s => B y s k))
  (fun y => paper_main_gordon_inner gamma H S y (fun s => B y s k))) K =
  paper_main_gordon_outer beta gamma H Y S
    (fun y => paper_main_gordon_kernel_average gamma H S (paper_main_gordon_gram B K) y y) -
  paper_main_gordon_outer beta gamma H Y S
    (fun y => paper_main_gordon_outer beta gamma H Y S
      (fun z => paper_main_gordon_kernel_average gamma H S (paper_main_gordon_gram B K) y z))).
{ rewrite paper_main_gordon_covariance_sum.
  unfold paper_main_gordon_outer; f_equal.
  - apply gibbs_average_ext; intros y Hy; apply paper_main_gordon_averaged_gram.
  - apply gibbs_average_ext; intros y Hy.
    apply gibbs_average_ext; intros z Hz; apply paper_main_gordon_averaged_gram. }
transitivity (finite_sum (fun k =>
  gamma * paper_main_gordon_outer beta gamma H Y S
    (fun y => gibbs_covariance gamma (H y) S (fun s => B y s k) (fun s => B y s k)) -
  beta * gibbs_covariance (-beta) (fun y => soft_max gamma (H y) S) Y
    (fun y => paper_main_gordon_inner gamma H S y (fun s => B y s k))
    (fun y => paper_main_gordon_inner gamma H S y (fun s => B y s k))) K).
- apply gibbs_sum_ext; intros k Hk; apply paper_main_gordon_curvatureE.
- rewrite paper_main_gordon_sum_sub, !gibbs_sum_scale, HI, HO.
  unfold paper_main_gordon_contraction; ring.
Qed.

Lemma paper_main_gordon_hessian_compare (beta gamma : R) (H : nat -> nat -> R)
    (Y S K L : list nat) (B A : nat -> nat -> nat -> R) :
  0 <= beta -> Y <> [] -> S <> [] ->
  (forall y s t, In y Y -> In s S -> In t S ->
    paper_main_gordon_gram B K y s y t = paper_main_gordon_gram A L y s y t) ->
  (forall y z s t, In y Y -> In z Y -> In s S -> In t S -> y <> z ->
    paper_main_gordon_gram A L y s z t <= paper_main_gordon_gram B K y s z t) ->
  finite_sum (fun k => nested_gibbs_curvature beta gamma H
    (fun y s => A y s k) Y S 0) L <=
  finite_sum (fun k => nested_gibbs_curvature beta gamma H
    (fun y s => B y s k) Y S 0) K.
Proof.
intros Hb HY HS Hsame Hcross.
rewrite !paper_main_gordon_hessian_gram.
apply paper_main_gordon_contraction_mono; assumption.
Qed.
