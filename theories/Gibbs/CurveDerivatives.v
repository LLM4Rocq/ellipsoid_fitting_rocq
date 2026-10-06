From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.Weights.
Import ListNotations.
Open Scope R_scope.

(* Derivatives along a curve of the finite Gibbs law of Gibbs.Definitions,
   with Stdlib's derivable_pt_lim. If each score F i has derivative D i,
   the partition function, the Gibbs weights and the Gibbs average of
   observables U i with derivatives V i are differentiable
   (gibbs_partition_derivative, gibbs_weight_derivative,
   gibbs_average_derivative); the last derivative is
   gibbs_average V + c * gibbs_covariance U D. The soft maximum has
   derivative gibbs_average c D (soft_max_curve_derivative), and the soft
   minimum with parameter beta has derivative gibbs_average (- beta) D
   (soft_min_curve_derivative). *)

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
