(* Gaussian expected soft margin with constructed nets and explicit entropy. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Gaussian.IteratedExpectationDefinitions Gaussian.CovarianceDefinitions
  Gordon.ProcessCovariance Gordon.Scalar Gordon.SetWidth Gordon.Nets
  Gordon.Entropy.
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
