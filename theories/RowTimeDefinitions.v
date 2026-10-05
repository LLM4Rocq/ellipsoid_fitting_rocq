From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions LowerDefinitions RowArrayDefinitions TimeDefinitions.

(* Port of theories/RowTimeDefinitions.v from Coquelicot to MathComp-Analysis.

   The original imports Coquelicot but writes no Coquelicot notion itself. Its
   only Coquelicot content came through tuple_build and matrix_NormedModule of
   MatrixDefinitions, block_array and lower_block_phi of LowerDefinitions,
   gaussian_row_pair and gaussian_row_array of RowArrayDefinitions, and
   joint_time_velocity of TimeDefinitions. Their ports keep the names,
   arguments, values and nested-pair representation, so the two definitions
   below keep the text of the original. The only change is the removed
   Coquelicot import.

   gaussian_array_velocity n m t xs is a tuple of the normed module
   matrix_NormedModule n of the port, which is block_array n m of
   LowerDefinitions by conversion, as in the original. Its norm is still the
   Euclidean norm of the blocks measured with the Frobenius norm. The pairs
   gaussian_row_pair n i xs are now elements of euclidean_product (the joint
   vectors of JointDefinitions); fst and snd act on them as on pairs, as
   before.

   No MathComp module is imported here, and none of the imports re-exports
   one, so the lists and the arithmetic are Stdlib's. As in the original, no
   scope is opened. *)

Definition gaussian_array_velocity n m t (xs : list R) :=
  tuple_build (matrix_NormedModule n) m (fun i =>
    joint_time_velocity n t (fst (gaussian_row_pair n i xs)) (snd (gaussian_row_pair n i xs))).

Definition gaussian_array_value n m beta gamma y B Y S t (xs : list R) : R :=
  lower_block_phi n m beta gamma y B Y S (gaussian_row_array n m t xs).
