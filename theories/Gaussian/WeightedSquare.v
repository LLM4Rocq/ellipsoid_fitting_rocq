(* Weighted centered Gaussian squares. For real coefficients a_i of either
   sign on d coordinates,
     Q d a xs = sum_(i < d) a_i * (x_i ^ 2 - 1),  x_i = nth i xs 0
   (paper_main_weighted_square); paper_main_weighted_square_cons splits off
   the first term. The tails of Q under the Gaussian product law are in
   Gaussian.WeightedSquareLaw. *)
From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra.
Open Scope R_scope.

Definition paper_main_weighted_square d (a : nat -> R) (xs : list R) : R :=
  finite_sum (fun i => a i * (List.nth i xs 0 ^ 2 - 1)) (List.seq 0 d).

Lemma paper_main_weighted_square_cons k (a : nat -> R) x xs :
  paper_main_weighted_square (S k) a (x :: xs) =
  a 0%nat * (x ^ 2 - 1) + paper_main_weighted_square k (fun i => a (S i)) xs.
Proof.
rewrite /paper_main_weighted_square.
change (List.seq 0 (S k)) with (0%nat :: List.seq 1 k).
rewrite /= (finite_sum_seq_shift _ 1 k).
reflexivity.
Qed.
