From Stdlib Require Import Reals List Lia Lra Psatz.
Open Scope R_scope.

(* Port of the inner module JointCancellationAlgebra of
   theories/InterpolationProofs.v (also copied in JointProofs.v) from
   Coquelicot to MathComp-Analysis, as a standalone module.

   The original imported Coquelicot but used nothing from it: the statement
   and the proof are real arithmetic of Stdlib (sqrt, INR, field, lra). The
   import of Coquelicot is dropped, no MathComp module is loaded, and the
   text below is the original, unchanged. *)

Theorem joint_stein_cancellation n t EP EQ ED ER :
  0 < t < 1 ->
  EP = (2 * sqrt t / INR (S n)) * ED +
    (t / (INR (S n) * sqrt (INR (S n)))) * ER ->
  EQ = (2 * sqrt (1-t) / INR (S n)) * ED ->
  EP / (2 * sqrt t) - EQ / (2 * sqrt (1-t)) =
    (sqrt t / (2 * INR (S n) * sqrt (INR (S n)))) * ER.
Proof.
  intros Ht HP HQ.
  assert (Hd : 0 < INR (S n)) by (apply lt_0_INR; lia).
  assert (Hds : 0 < sqrt (INR (S n))) by (apply sqrt_lt_R0; exact Hd).
  assert (Hs : 0 < sqrt t) by (apply sqrt_lt_R0; lra).
  assert (Hs1 : 0 < sqrt (1-t)) by (apply sqrt_lt_R0; lra).
  pose proof (sqrt_def t ltac:(lra)) as Hsquare.
  assert (Hc : t / (INR (S n) * sqrt (INR (S n))) =
    (sqrt t * sqrt t) / (INR (S n) * sqrt (INR (S n)))).
  { rewrite Hsquare; reflexivity. }
  rewrite HP, HQ, Hc; field; repeat split; lra.
Qed.

