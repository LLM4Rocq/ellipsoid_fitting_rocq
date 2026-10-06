From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Matrix.Definitions Soft.MatrixDefinitions.
Open Scope R_scope.

(* The soft minimax of scores F z s : E -> R on a normed module E, and its
   first two derivatives.
   - lower_inner_value: the soft maximum over S, at inverse temperature
     gamma, of the scores F z s A.
   - lower_inner_first and lower_inner_covariance: the mean of the scores
     in a direction U, and the covariance of the scores in two directions U
     and V, under the inner Gibbs law over S.
   - lower_first and lower_second: their combinations under the outer Gibbs
     law over Y, at inverse temperature - beta.
   When every F z s is linear and bounded, 0 < beta, 0 < gamma and Y and S
   are nonempty, lower_first and lower_second are the first and second
   derivatives of the soft minimax at A (Soft.MinimaxFrechet).

   The block versions take for E the space block_array n m of the tuples of
   m + 1 matrices of matrix n, with the Euclidean norm of all entries (the
   square root of the sum of the squared Frobenius norms of the blocks).
   Their scores lower_block_scores n m y B z s A are the sums over the
   blocks i of y z i * trace_pair n (B s) A_i, over the index list
   List.seq 0 (S m) = [0; ...; m]. lower_block_phi is the soft minimax of
   these scores. *)

Definition block_NormedModule (n m : nat) : normedModType R :=
  tuple_NormedModule (matrix_NormedModule n) m.
Definition block_array (n m : nat) : Type := block_NormedModule n m.
Definition block_entry n m (A : block_array n m) i : matrix n :=
  tuple_entry (matrix_NormedModule n) m i A.

Definition lower_inner_value {E : normedModType R} gamma
    (F : nat -> nat -> E -> R) S (A : E) z : R :=
  soft_max gamma (fun s => F z s A) S.
Definition lower_inner_first {E : normedModType R} gamma
    (F : nat -> nat -> E -> R) S (A U : E) z : R :=
  gibbs_average gamma (fun s => F z s A) S (fun s => F z s U).
Definition lower_inner_covariance {E : normedModType R} gamma
    (F : nat -> nat -> E -> R) S (A U V : E) z : R :=
  gibbs_covariance gamma (fun s => F z s A) S (fun s => F z s U) (fun s => F z s V).
Definition lower_first {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U : E) : R :=
  gibbs_average (- beta) (lower_inner_value gamma F S A) Y (lower_inner_first gamma F S A U).
Definition lower_second {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U V : E) : R :=
  gamma * gibbs_average (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_covariance gamma F S A U V) -
  beta * gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_first gamma F S A U) (lower_inner_first gamma F S A V).

Definition lower_block_scores n m y B z s (A : block_array n m) : R :=
  soft_matrix_scores n y B (List.seq 0 (S m)) (block_entry n m A) z s.
Definition lower_block_phi n m beta gamma y B Y S (A : block_array n m) : R :=
  soft_matrix_phi n beta gamma y B (List.seq 0 (Datatypes.S m)) Y S (block_entry n m A).
Definition lower_block_first n m beta gamma y B Y S (A U : block_array n m) : R :=
  lower_first beta gamma (lower_block_scores n m y B) Y S A U.
Definition lower_block_second n m beta gamma y B Y S (A U V : block_array n m) : R :=
  lower_second beta gamma (lower_block_scores n m y B) Y S A U V.
