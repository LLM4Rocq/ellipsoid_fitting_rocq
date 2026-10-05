(* Independent and identical Gaussian pairs for covariance estimates.
   The independent loading is the identity on 2d coordinates. The coupled
   loading sends a d-vector x to (x,x). *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions
  GaussianProductDefinitions GaussianProduct GaussianLastDefinitions
  GaussianLastIntegration GaussianCovarianceDefinitions GaussianCovarianceSums
  GaussianCovarianceLinear GaussianCovarianceEndpoints
  PaperMainGaussianCovarianceMarginals.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_fold (d a : nat) : nat :=
  if Nat.ltb a d then a else (a - d)%coq_nat.

Definition paper_main_gaussian_duplicate (d a k : nat) : R :=
  paper_main_gaussian_identity (paper_main_gaussian_fold d a) k.

Definition paper_main_gaussian_coupling_difference (d a b : nat) : R :=
  gaussian_covariance_entry d (paper_main_gaussian_duplicate d) a b -
  gaussian_covariance_entry (d + d)%coq_nat paper_main_gaussian_identity a b.

Lemma paper_main_gaussian_fold_left d a :
  (a < d)%coq_nat -> paper_main_gaussian_fold d a = a.
Proof.
intros Ha; unfold paper_main_gaussian_fold.
destruct (Nat.ltb a d) eqn:E; [reflexivity|apply Nat.ltb_ge in E; lia].
Qed.

Lemma paper_main_gaussian_fold_right d a :
  paper_main_gaussian_fold d (d + a)%coq_nat = a.
Proof.
unfold paper_main_gaussian_fold.
destruct (Nat.ltb (d + a)%coq_nat d) eqn:E; [apply Nat.ltb_lt in E; lia|lia].
Qed.

Lemma paper_main_gaussian_fold_bound d a :
  Nat.lt a (Nat.add d d) -> (paper_main_gaussian_fold d a < d)%coq_nat.
Proof.
intros Ha; unfold paper_main_gaussian_fold.
destruct (Nat.ltb a d) eqn:E; [apply Nat.ltb_lt in E; exact E|apply Nat.ltb_ge in E; lia].
Qed.

Lemma paper_main_gaussian_identity_sum d a (v : nat -> R) :
  (a < d)%coq_nat ->
  finite_sum (fun b => paper_main_gaussian_identity b a * v b) (List.seq 0 d) = v a.
Proof.
intros Ha; unfold paper_main_gaussian_identity.
transitivity (finite_sum (fun b => if Nat.eqb b a then v a else 0) (List.seq 0 d)).
- apply finite_sum_ext; intros b Hb; rewrite Nat.eqb_sym.
  destruct (Nat.eqb b a) eqn:E; [apply Nat.eqb_eq in E; subst b; ring|ring].
- apply finite_sum_delta; exact Ha.
Qed.

Lemma paper_main_gaussian_duplicate_image d xs :
  List.length xs = d ->
  gaussian_covariance_image (d + d)%coq_nat d (paper_main_gaussian_duplicate d) xs =
  (xs ++ xs)%list.
Proof.
intros Hxs; apply (nth_ext _ _ 0 0).
- unfold gaussian_covariance_image; rewrite length_map_seq length_app Hxs; reflexivity.
- intros a Ha; unfold gaussian_covariance_image in *; rewrite length_map_seq in Ha.
  rewrite (nth_map_seq _ _ _ Ha).
  change (gaussian_covariance_row d paper_main_gaussian_identity
    (paper_main_gaussian_fold d a) xs = List.nth a (xs ++ xs)%list 0).
  rewrite (paper_main_gaussian_identity_row d _ xs (paper_main_gaussian_fold_bound d a Ha)).
  destruct (Nat.lt_ge_cases a d) as [Had|Had].
  + rewrite (paper_main_gaussian_fold_left d a Had).
    rewrite app_nth1; [rewrite Hxs; exact Had|reflexivity].
  + unfold paper_main_gaussian_fold.
    assert (E : Nat.ltb a d = false) by (apply Nat.ltb_ge; exact Had).
    rewrite E; rewrite app_nth2; [rewrite Hxs; exact Had|rewrite Hxs; reflexivity].
Qed.

Lemma paper_main_gaussian_duplicate_covariance d a b :
  Nat.lt a (Nat.add d d) ->
  gaussian_covariance_entry d (paper_main_gaussian_duplicate d) a b =
  paper_main_gaussian_identity (paper_main_gaussian_fold d b) (paper_main_gaussian_fold d a).
Proof.
intros Ha.
exact (paper_main_gaussian_identity_covariance d (paper_main_gaussian_fold d a)
  (paper_main_gaussian_fold d b) (paper_main_gaussian_fold_bound d a Ha)).
Qed.

Lemma paper_main_gaussian_coupling_left d a b :
  (a < d)%coq_nat -> (b < d)%coq_nat ->
  paper_main_gaussian_coupling_difference d a b = 0.
Proof.
intros Ha Hb; unfold paper_main_gaussian_coupling_difference.
rewrite (paper_main_gaussian_duplicate_covariance d a b ltac:(lia)).
rewrite (paper_main_gaussian_fold_left d a Ha) (paper_main_gaussian_fold_left d b Hb).
rewrite (paper_main_gaussian_identity_covariance (d + d)%coq_nat a b ltac:(lia)); ring.
Qed.

Lemma paper_main_gaussian_coupling_right d a b :
  (a < d)%coq_nat -> (b < d)%coq_nat ->
  paper_main_gaussian_coupling_difference d (d + a)%coq_nat (d + b)%coq_nat = 0.
Proof.
intros Ha Hb; unfold paper_main_gaussian_coupling_difference.
rewrite (paper_main_gaussian_duplicate_covariance d (d + a)%coq_nat (d + b)%coq_nat ltac:(lia)).
rewrite !paper_main_gaussian_fold_right.
rewrite (paper_main_gaussian_identity_covariance (d + d)%coq_nat (d + a)%coq_nat (d + b)%coq_nat ltac:(lia)).
unfold paper_main_gaussian_identity.
destruct (Nat.eqb a b) eqn:E.
- apply Nat.eqb_eq in E; subst b; rewrite Nat.eqb_refl; ring.
- assert (E' : Nat.eqb (d + a)%coq_nat (d + b)%coq_nat = false) by (apply Nat.eqb_neq; apply Nat.eqb_neq in E; lia).
  rewrite E'; ring.
Qed.

Lemma paper_main_gaussian_coupling_cross_left d a b :
  (a < d)%coq_nat -> (b < d)%coq_nat ->
  paper_main_gaussian_coupling_difference d a (d + b)%coq_nat =
  paper_main_gaussian_identity b a.
Proof.
intros Ha Hb; unfold paper_main_gaussian_coupling_difference.
rewrite (paper_main_gaussian_duplicate_covariance d a (d + b)%coq_nat ltac:(lia)).
rewrite (paper_main_gaussian_fold_left d a Ha) paper_main_gaussian_fold_right.
rewrite (paper_main_gaussian_identity_covariance (d + d)%coq_nat a (d + b)%coq_nat ltac:(lia)).
unfold paper_main_gaussian_identity.
assert (E : Nat.eqb a (d + b)%coq_nat = false) by (apply Nat.eqb_neq; lia).
rewrite E; ring.
Qed.

Lemma paper_main_gaussian_coupling_cross_right d a b :
  (a < d)%coq_nat -> (b < d)%coq_nat ->
  paper_main_gaussian_coupling_difference d (d + a)%coq_nat b =
  paper_main_gaussian_identity b a.
Proof.
intros Ha Hb; unfold paper_main_gaussian_coupling_difference.
rewrite (paper_main_gaussian_duplicate_covariance d (d + a)%coq_nat b ltac:(lia)).
rewrite (paper_main_gaussian_fold_left d b Hb) paper_main_gaussian_fold_right.
rewrite (paper_main_gaussian_identity_covariance (d + d)%coq_nat (d + a)%coq_nat b ltac:(lia)).
unfold paper_main_gaussian_identity.
assert (E : Nat.eqb (d + a)%coq_nat b = false) by (apply Nat.eqb_neq; lia).
rewrite E; ring.
Qed.

Theorem paper_main_gaussian_coupling_pairing d H :
  gaussian_covariance_pairing (d + d)%coq_nat d (d + d)%coq_nat
    (paper_main_gaussian_duplicate d) paper_main_gaussian_identity H =
  finite_sum (fun a => H a (d + a)%coq_nat + H (d + a)%coq_nat a) (List.seq 0 d).
Proof.
unfold gaussian_covariance_pairing.
change (finite_sum (fun a => finite_sum (fun b =>
  paper_main_gaussian_coupling_difference d a b * H a b) (List.seq 0 (d + d)%coq_nat))
  (List.seq 0 (d + d)%coq_nat) =
  finite_sum (fun a => H a (d + a)%coq_nat + H (d + a)%coq_nat a) (List.seq 0 d)).
rewrite finite_sum_seq_split finite_sum_plus.
f_equal.
- apply finite_sum_ext; intros a Ha; apply in_seq_lt in Ha.
  rewrite finite_sum_seq_split.
  assert (HL : finite_sum (fun b => paper_main_gaussian_coupling_difference d a b * H a b)
    (List.seq 0 d) = 0).
  { transitivity (finite_sum (fun _ => 0) (List.seq 0 d)); [|apply finite_sum_zero].
    apply finite_sum_ext; intros b Hb; apply in_seq_lt in Hb.
    rewrite (paper_main_gaussian_coupling_left d a b Ha Hb); ring. }
  rewrite HL Rplus_0_l.
  transitivity (finite_sum (fun b => paper_main_gaussian_identity b a * H a (d + b)%coq_nat)
    (List.seq 0 d)).
  + apply finite_sum_ext; intros b Hb; apply in_seq_lt in Hb.
    rewrite (paper_main_gaussian_coupling_cross_left d a b Ha Hb); reflexivity.
  + exact (paper_main_gaussian_identity_sum d a (fun b => H a (d + b)%coq_nat) Ha).
- apply finite_sum_ext; intros a Ha; apply in_seq_lt in Ha.
  rewrite finite_sum_seq_split.
  assert (HR : finite_sum (fun b => paper_main_gaussian_coupling_difference d
    (d + a)%coq_nat (d + b)%coq_nat * H (d + a)%coq_nat (d + b)%coq_nat)
    (List.seq 0 d) = 0).
  { transitivity (finite_sum (fun _ => 0) (List.seq 0 d)); [|apply finite_sum_zero].
    apply finite_sum_ext; intros b Hb; apply in_seq_lt in Hb.
    rewrite (paper_main_gaussian_coupling_right d a b Ha Hb); ring. }
  rewrite HR Rplus_0_r.
  transitivity (finite_sum (fun b => paper_main_gaussian_identity b a * H (d + a)%coq_nat b)
    (List.seq 0 d)).
  + apply finite_sum_ext; intros b Hb; apply in_seq_lt in Hb.
    rewrite (paper_main_gaussian_coupling_cross_right d a b Ha Hb); reflexivity.
  + exact (paper_main_gaussian_identity_sum d a (fun b => H (d + a)%coq_nat b) Ha).
Qed.

Lemma paper_main_gaussian_independent_product d (f g : list R -> R) :
  gaussian_iterated_integrable d f ->
  gaussian_iterated_integrable d g ->
  gaussian_iterated_expectation (d + d)%coq_nat
    (fun zs => f (List.firstn d zs) * g (List.skipn d zs)) =
  gaussian_iterated_expectation d f * gaussian_iterated_expectation d g.
Proof.
intros Hf Hg; rewrite gaussian_iterated_suffix_expectation.
transitivity (gaussian_iterated_expectation d
  (fun xs => gaussian_iterated_expectation d g * f xs)).
- apply gaussian_iterated_expectation_ext; intros xs Hxs.
  unfold gaussian_suffix_marginal.
  transitivity (gaussian_iterated_expectation d (fun ys => f xs * g ys)).
  + apply gaussian_iterated_expectation_ext; intros ys Hys.
    rewrite <- Hxs; rewrite firstn_app_exact skipn_app_exact; reflexivity.
  + rewrite (proj2 (gaussian_iterated_scale d g (f xs) Hg)); ring.
- rewrite (proj2 (gaussian_iterated_scale d f (gaussian_iterated_expectation d g) Hf)); ring.
Qed.
