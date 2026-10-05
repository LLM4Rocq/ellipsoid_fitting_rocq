(* Finite nets approximate the genuine support function and Gaussian width. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianProductDefinitions GaussianProduct
  GaussianCovarianceDefinitions GaussianCovarianceSums PaperMainGordonProcessCovariance
  PaperMainGordonScalar PaperMainGaussianNorm PaperMainGordonWidth
  PaperMainGordonSoftMargin PaperMainGordonSetWidth.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_finite_net d (T : (nat -> R) -> Prop)
    (v : nat -> nat -> R) S eps :=
  (forall t, In t S -> T (v t)) /\
  (forall u, T u -> exists t, In t S /\
    paper_main_gordon_dot d (fun i => u i - v t i) (fun i => u i - v t i) <= eps^2).

Lemma paper_main_gordon_net_nonempty d T v S eps :
  (exists u, T u) -> paper_main_gordon_finite_net d T v S eps -> S <> [].
Proof.
intros [u Hu] [_ Hcover] HE.
destruct (Hcover u Hu) as [t [Ht _]]; rewrite HE in Ht; contradiction.
Qed.

Lemma paper_main_gordon_dot_coefficient_difference d u v xs eps :
  List.length xs = d -> 0 <= eps ->
  paper_main_gordon_dot d (fun i => u i - v i) (fun i => u i - v i) <= eps^2 ->
  Rabs (paper_main_gordon_dot d u (fun i => List.nth i xs 0) -
    paper_main_gordon_dot d v (fun i => List.nth i xs 0)) <= eps * paper_main_gaussian_norm xs.
Proof.
intros Hxs He HC.
pose proof (paper_main_gordon_coefficient_dot_bound d (fun i => u i - v i) xs eps Hxs He HC) as H.
assert (HE : paper_main_gordon_dot d (fun i => u i - v i) (fun i => List.nth i xs 0) =
  paper_main_gordon_dot d u (fun i => List.nth i xs 0) -
  paper_main_gordon_dot d v (fun i => List.nth i xs 0)).
{ unfold paper_main_gordon_dot; rewrite <- finite_sum_minus.
  apply finite_sum_ext; intros; ring. }
rewrite HE in H; exact H.
Qed.

Lemma paper_main_gordon_support_subset d T v S xs :
  List.length xs = d -> S <> [] ->
  (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  (forall t, In t S -> T (v t)) ->
  paper_main_gordon_support d v S xs <= paper_main_gordon_set_support d T xs.
Proof.
intros Hxs HS HU HV; unfold paper_main_gordon_support.
apply finite_max_upper; [exact HS|].
intros t Ht; apply paper_main_gordon_set_support_member; [exact Hxs|apply HV; exact Ht|exact HU].
Qed.

Theorem paper_main_gordon_net_support_error d T v S eps xs :
  List.length xs = d -> 0 <= eps -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  paper_main_gordon_finite_net d T v S eps ->
  0 <= paper_main_gordon_set_support d T xs - paper_main_gordon_support d v S xs <=
    eps * paper_main_gaussian_norm xs.
Proof.
intros Hxs He HT HU Hnet.
pose proof (paper_main_gordon_net_nonempty d T v S eps HT Hnet) as HS.
destruct Hnet as [HV Hcover].
pose proof (paper_main_gordon_support_subset d T v S xs Hxs HS HU HV) as HL.
split; [lra|].
assert (HB : paper_main_gordon_set_support d T xs <=
  paper_main_gordon_support d v S xs + eps * paper_main_gaussian_norm xs).
{ apply paper_main_gordon_set_support_le; try assumption.
  intros u Hu; destruct (Hcover u Hu) as [t [Ht HC]].
  pose proof (paper_main_gordon_dot_coefficient_difference d u (v t) xs eps Hxs He HC) as H.
  pose proof (Rle_abs (paper_main_gordon_dot d u (fun i => List.nth i xs 0) -
    paper_main_gordon_dot d (v t) (fun i => List.nth i xs 0))) as HA.
  pose proof (finite_max_member (fun t => paper_main_gordon_dot d (v t) (fun i => List.nth i xs 0))
    S t Ht) as HM.
  unfold paper_main_gordon_support; lra. }
lra.
Qed.

Theorem paper_main_gordon_net_width_error d T v S eps :
  0 <= eps -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  paper_main_gordon_finite_net d T v S eps ->
  0 <= paper_main_gordon_set_width d T - paper_main_gordon_width d v S <= eps * sqrt (INR d).
Proof.
intros He HT HU Hnet.
pose proof (paper_main_gordon_net_nonempty d T v S eps HT Hnet) as HS.
assert (HV : forall t, In t S -> paper_main_gordon_dot d (v t) (v t) = 1).
{ intros t Ht; apply HU; apply (proj1 Hnet); exact Ht. }
pose proof (proj1 (paper_main_gordon_support_domain d v S HS HV)) as HFI.
pose proof (proj1 (paper_main_gordon_set_support_domain d T HT HU)) as HTI.
pose proof (proj1 (paper_main_gaussian_norm_domain d)) as HNI.
assert (HP : forall xs, List.length xs = d ->
  0 <= paper_main_gordon_set_support d T xs - paper_main_gordon_support d v S xs <=
  eps * paper_main_gaussian_norm xs).
{ intros xs Hxs; apply paper_main_gordon_net_support_error; assumption. }
pose proof (gaussian_iterated_monotone d (paper_main_gordon_support d v S)
  (paper_main_gordon_set_support d T) HFI HTI
  ltac:(intros xs Hxs; specialize (HP xs Hxs); lra)) as HL.
destruct (gaussian_iterated_scale d paper_main_gaussian_norm eps HNI) as [Hscale HscaleE].
destruct (gaussian_iterated_add d (paper_main_gordon_support d v S)
  (fun xs => eps * paper_main_gaussian_norm xs) HFI Hscale) as [Hadd HaddE].
pose proof (gaussian_iterated_monotone d (paper_main_gordon_set_support d T)
  (fun xs => paper_main_gordon_support d v S xs + eps * paper_main_gaussian_norm xs)
  HTI Hadd ltac:(intros xs Hxs; specialize (HP xs Hxs); lra)) as HB.
rewrite HaddE, HscaleE in HB.
pose proof (Rmult_le_compat_l eps _ _ He (proj2 (paper_main_gaussian_norm_expectation d))) as Hmean.
unfold paper_main_gordon_set_width, paper_main_gordon_width; split; lra.
Qed.

Theorem paper_main_gordon_net_width_margin r s N M z T v eps :
  (0 < r)%nat -> 0 <= eps -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot M u u = 1) ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  paper_main_gordon_finite_net M T v (List.seq 0 s) eps ->
  gaussian_covariance_domain (N * M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) /\
  paper_main_gordon_set_width M T - eps * sqrt (INR M) - sqrt (INR N) <=
  gaussian_iterated_expectation (N * M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr He HT HU Hz Hnet.
pose proof (paper_main_gordon_net_nonempty M T v (List.seq 0 s) eps HT Hnet) as HS.
assert (Hs : (0 < s)%nat) by (destruct s; [contradiction HS; reflexivity|lia]).
assert (HV : forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1).
{ intros t Ht; apply HU; apply (proj1 Hnet); apply lt_in_seq; exact Ht. }
destruct (paper_main_gordon_finite_width_margin r s N M z v Hr Hs Hz HV) as [HD HM].
split; [exact HD|].
pose proof (paper_main_gordon_net_width_error M T v (List.seq 0 s) eps He HT HU Hnet) as HB.
lra.
Qed.

Theorem paper_main_gordon_net_soft_margin r s N M z T v eps beta gamma :
  (0 < r)%nat -> 0 <= eps -> 0 < beta -> 0 < gamma -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot M u u = 1) ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  paper_main_gordon_finite_net M T v (List.seq 0 s) eps ->
  gaussian_covariance_domain (N * M) (fun xs => soft_minimax beta gamma
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) /\
  paper_main_gordon_set_width M T - eps * sqrt (INR M) - sqrt (INR N) - Rpower.ln (INR r) / beta <=
  gaussian_iterated_expectation (N * M) (fun xs => soft_minimax beta gamma
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr He Hb Hg HT HU Hz Hnet.
pose proof (paper_main_gordon_net_nonempty M T v (List.seq 0 s) eps HT Hnet) as HS.
assert (Hs : (0 < s)%nat) by (destruct s; [contradiction HS; reflexivity|lia]).
assert (HV : forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1).
{ intros t Ht; apply HU; apply (proj1 Hnet); apply lt_in_seq; exact Ht. }
destruct (paper_main_gordon_soft_width_margin r s N M z v beta gamma Hr Hs Hb Hg Hz HV) as [HD HM].
split; [exact HD|].
pose proof (paper_main_gordon_net_width_error M T v (List.seq 0 s) eps He HT HU Hnet) as HB.
lra.
Qed.
