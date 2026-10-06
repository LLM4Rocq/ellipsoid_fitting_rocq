From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Matrix.Definitions
  Soft.MinimaxDerivativeDefinitions Row.ArrayDefinitions Joint.TimeVelocity.

(* The time derivative and the value along the multirow interpolation.
   gaussian_array_velocity n m t xs is the block array of the time
   derivatives joint_time_velocity of the m + 1 rows read from xs, that is
   the time derivative of gaussian_row_array n m t xs for 0 < t < 1
   (gaussian_array_time_derivative in Multirow.ArrayTimeCalculus). It is a tuple of
   matrix_NormedModule n, which is block_array n m by conversion, with the
   Euclidean norm of the Frobenius norms of the blocks.
   gaussian_array_value is the block soft minimax lower_block_phi of the
   array gaussian_row_array n m t xs. *)

Definition gaussian_array_velocity n m t (xs : list R) :=
  tuple_build (matrix_NormedModule n) m (fun i =>
    joint_time_velocity n t (fst (gaussian_row_pair n i xs)) (snd (gaussian_row_pair n i xs))).

Definition gaussian_array_value n m beta gamma y B Y S t (xs : list R) : R :=
  lower_block_phi n m beta gamma y B Y S (gaussian_row_array n m t xs).
