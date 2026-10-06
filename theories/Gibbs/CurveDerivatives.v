From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.Weights.
Import ListNotations.
Open Scope R_scope.

(* The soft minimum with parameter beta <> 0 is the soft maximum with
   parameter - beta (soft_min_signed_identity). *)

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
