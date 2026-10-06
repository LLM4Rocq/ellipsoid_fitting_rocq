From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Soft.MinimaxDerivativeDefinitions Soft.LowerThirdDefinitions
  Row.ArrayDefinitions Goe.Definitions Joint.Definitions
  Chaos.SecondOrderDefinitions.
Open Scope R_scope.

(* Two observables of row i of the array A = gaussian_row_array n m t xs,
   whose block i is sqrt t * joint_quadratic_input n x plus
   sqrt (1-t) * goe_matrix n z for the row (x, z). gaussian_row_velocity
   is the derivative lower_block_first of the soft minimax at A along the
   first part, divided by 2 * sqrt t, minus that along the second part,
   divided by 2 * sqrt (1-t): the contribution of row i to the derivative
   in t. gaussian_row_remainder is chaos_contraction, at x, of the
   third-order term lower_block_third at A in directions of block i. The
   local function inject has the body of block_inject of
   Matrix.BlockInjection, so importers can fold it into block_inject. *)

Definition gaussian_row_velocity n m beta gamma y B Y S t i (xs : list R) : R :=
  let pair := gaussian_row_pair n i xs in
  let A := gaussian_row_array n m t xs in
  let inject := fun U : matrix n => tuple_build (matrix_NormedModule n) m
    (fun j => if Nat.eqb j i then U else 0%R) in
  lower_block_first n m beta gamma y B Y S A (inject (joint_quadratic_input n (fst pair))) /
    (2 * sqrt t) -
  lower_block_first n m beta gamma y B Y S A (inject (goe_matrix n (snd pair))) /
    (2 * sqrt (1-t)).

Definition gaussian_row_remainder n m beta gamma y B Y S t i (xs : list R) : R :=
  let pair := gaussian_row_pair n i xs in
  let A := gaussian_row_array n m t xs in
  let inject := fun U : matrix n => tuple_build (matrix_NormedModule n) m
    (fun j => if Nat.eqb j i then U else 0%R) in
  chaos_contraction n (fun U V W =>
    lower_block_third n m beta gamma y B Y S A (inject U) (inject V) (inject W)) (fst pair).
