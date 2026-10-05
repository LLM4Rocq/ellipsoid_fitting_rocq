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

(* Port of theories/FullThirdBlock.v from Coquelicot to MathComp-Analysis.

   Every theorem of the original keeps its name and its arguments, in the
   same order. No lemma is added. The statements change form in the ways of
   the ports of LowerFrechet, LowerBounds, FullThirdFrechet,
   FullThirdContinuity and FullThirdBounds, which this module imports, and
   of the restated challenge ellipsoid_full_third in analysis/challenges.

   1. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis: f is differentiable at A and its
      differential 'd f A is l. Both say that l is linear and continuous and
      that f (A + H) = f A + l H + o(H) as H tends to 0. The real-valued maps
      are typed into R^o, the normed module view of R, which is R by
      definition, so the maps are the same.

   2. Pointwise continuity. Coquelicot's continuous f A, continuity of f at
      the one point A, becomes {for A, continuous f} (analysis/README.md,
      difference 5).

   3. Norms. Coquelicot's norm U becomes MathComp's norm (`|U|)%R. On
      block_array n m it is the norm of LowerDefinitions, the square root of
      the sum of the squared Frobenius norms of the blocks, as in the
      original, because the port of MatrixDefinitions nests
      euclidean_product of MatrixEuclideanProduct and keeps Coquelicot's
      product norm. So the constant
      8 * (sqrt (INR (S n)) * k) ^ 3 * (beta + gamma) ^ 2 is stated against
      the same norm as before. The comparison, the products and the powers
      around the norms are Stdlib's.

   4. Lists. With ssreflect loaded, the bare name seq means MathComp's type
      of sequences, so Stdlib's seq 0 (S m) is written List.seq 0 (S m), as
      in the port of LowerDefinitions. The list is the same.

   The proofs keep their steps. *)

(* The Euclidean product norm on the complete matrix block space appears
   here. No symmetry, coordinate restriction, or low-influence hypothesis
   is needed for this uniform bound. *)
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
