(* Gaussian expected soft margin with constructed nets and explicit entropy. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianProductDefinitions
  GaussianCovarianceDefinitions PaperMainGordonProcessCovariance
  PaperMainGordonScalar PaperMainGordonSetWidth PaperMainGordonNets
  PaperMainGordonEntropy.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_entropy_constant_positive eps :
  0 < eps -> 0 < paper_main_gordon_entropy_constant eps.
Proof.
intros He; unfold paper_main_gordon_entropy_constant.
assert (Hln : 0 < ln 2).
{ pose proof (ln_increasing 1 2 ltac:(lra) ltac:(lra)) as H; rewrite ln_1 in H; exact H. }
pose proof (Rinv_0_lt_compat eps He) as Hinv.
unfold Rdiv; apply Rmult_lt_0_compat; lra.
Qed.

Theorem paper_main_gordon_constructed_soft_margin N M Y T eps beta gamma :
  0 < eps -> 0 < beta -> 0 < gamma ->
  (exists z, Y z) -> (exists u, T u) ->
  (forall z, Y z -> paper_main_gordon_dot N z z = 1) ->
  (forall u, T u -> paper_main_gordon_dot M u u = 1) ->
  let r := List.length (paper_main_gordon_entropy_grid N eps) in
  let s := List.length (paper_main_gordon_entropy_grid M eps) in
  (0 < r)%nat /\ (0 < s)%nat /\ exists z v,
    paper_main_gordon_finite_net N Y z (List.seq 0 r) eps /\
    paper_main_gordon_finite_net M T v (List.seq 0 s) eps /\
    ln (INR r) + ln (INR s) <=
      paper_main_gordon_entropy_constant eps * (INR N + INR M) /\
    gaussian_covariance_domain (N * M) (fun xs => soft_minimax beta gamma
      (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
      (List.seq 0 r) (List.seq 0 s)) /\
    paper_main_gordon_set_width M T - eps * sqrt (INR M) - sqrt (INR N) -
      paper_main_gordon_entropy_constant eps * INR N / beta <=
    gaussian_iterated_expectation (N * M) (fun xs => soft_minimax beta gamma
      (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
      (List.seq 0 r) (List.seq 0 s)).
Proof.
intros He Hb Hg HY HT HUY HUT r s.
destruct (paper_main_gordon_entropy_net_fixed N Y eps He HY HUY) as [Hr [z [HNz Hrz]]].
destruct (paper_main_gordon_entropy_net_fixed M T eps He HT HUT) as [Hs [v [HNv Hsv]]].
fold r in Hr, HNz, Hrz; fold s in Hs, HNv, Hsv.
split; [exact Hr|]; split; [exact Hs|].
exists z, v; split; [exact HNz|]; split; [exact HNv|]; split; [nra|].
assert (HZ : forall y, (y<r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1).
{ intros y Hy; apply HUY; apply (proj1 HNz); apply in_seq; lia. }
destruct (paper_main_gordon_net_soft_margin r s N M z T v eps beta gamma
  Hr ltac:(lra) Hb Hg HT HUT HZ HNv) as [HD HM].
split; [exact HD|].
pose proof (Rinv_0_lt_compat beta Hb) as Hinv.
pose proof (Rmult_le_compat_r (/beta) _ _ ltac:(lra) Hrz) as HE.
unfold Rdiv in *; lra.
Qed.
