From Stdlib Require Import Reals List Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions MatrixDefinitions OperatorDefinitions
  LowerDefinitions LowerNormBounds LowerFrechet LowerBounds
  FullThirdDefinitions FullThirdBounds.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* A uniform bound on lower_block_third, the third-order term of
   FullThirdDefinitions for the soft minimax of a block array. For positive
   beta and gamma, nonempty Y and S, unit vectors y z and matrices B s of
   operator norm at most k, lower_block_third_bound gives
     Rabs (lower_block_third n m beta gamma y B Y S A U V W) <=
       8 * (sqrt (INR (S n)) * k) ^ 3 * (beta + gamma) ^ 2 *
       `|U| * `|V| * `|W|,
   where the norm of a block array is the Euclidean norm of its entries. *)

(* No symmetry, coordinate restriction or low-influence hypothesis is
   needed for this uniform bound. *)
Theorem lower_block_third_bound n m beta gamma y B Y S
    (A U V W : block_array n m) k :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= k ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  Rabs (lower_block_third n m beta gamma y B Y S A U V W) <=
    8 * (sqrt (INR (Datatypes.S n)) * k) ^ 3 * (beta + gamma) ^ 2 *
      (`|U|)%R * (`|V|)%R * (`|W|)%R.
Proof.
  intros Hb Hg HY HS Hk Hunit HB; apply lower_third_uniform_bound; try assumption.
  - apply Rmult_le_pos; [apply sqrt_pos|exact Hk].
  - intros z s Hz Hs P; apply (lower_block_score_bound n m y B S k z s P); try assumption.
    apply Hunit; exact Hz.
Qed.
