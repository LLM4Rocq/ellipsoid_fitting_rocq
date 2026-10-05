From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions LowerDefinitions FullThirdDefinitions
  RowArrayDefinitions GoeDefinitions JointDefinitions SecondChaosDefinitions.
Open Scope R_scope.

(* Port of theories/RowObservableDefinitions.v from Coquelicot to
   MathComp-Analysis.

   The only Coquelicot notion written here is zero, the zero of the normed
   module matrix_NormedModule n, in the local function inject that places a
   matrix U in block i of a block array and 0 in the other blocks. It becomes
   MathComp's 0 of that space, written 0%R, as in block_inject of the port of
   BlockOperatorDefinitions. It is the matrix whose entries are all 0, as
   before. The body of inject is, token for token, the body of block_inject
   of that port, so that importers can still fold inject into
   block_inject n m i U.

   Everything else keeps the text of the original. lower_block_first and
   lower_block_third (LowerDefinitions, FullThirdDefinitions),
   gaussian_row_pair and gaussian_row_array (RowArrayDefinitions), goe_matrix
   (GoeDefinitions), joint_quadratic_input (JointDefinitions) and
   chaos_contraction (SecondChaosDefinitions) keep their names, arguments and
   values in their ports. gaussian_row_pair n i xs is now an element of
   euclidean_product, the joint vectors of JointDefinitions, and fst and snd
   act on it as on a pair, as before.

   MathComp is imported for the notation 0%R and the normed module structure
   of matrix_NormedModule n, with the same imports as the port of
   BlockOperatorDefinitions. R_scope is opened after the imports, so the
   division, the product 2 * sqrt t, the difference 1 - t and sqrt are
   Stdlib's, as before. The test Nat.eqb j i is Stdlib's boolean equality on
   nat, as before. The meaning of both definitions is unchanged. *)

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
