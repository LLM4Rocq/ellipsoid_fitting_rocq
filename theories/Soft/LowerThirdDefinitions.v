From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Gibbs.Definitions
  Gibbs.CumulantDefinitions Soft.MinimaxDerivativeDefinitions.
Open Scope R_scope.

(* The third-order term of the nested soft minimax of Soft.MinimaxDerivativeDefinitions,
   after lower_first and lower_second. The outer Gibbs weights have
   parameter - beta over Y, the inner ones parameter gamma over S.
   lower_third combines the outer average of the inner third cumulants
   (lower_inner_cumulant), three outer covariances between inner
   covariances and inner averages, and the outer third cumulant of the
   inner averages. For scores F z s linear in A, this is the third
   derivative of the nested soft minimax in the directions U, V and W;
   Gibbs.MatrixThirdDerivative proves the matrix form of this fact, which
   Row.BlockDirectionDerivatives relates to lower_block_third along one block.
   lower_block_third specializes lower_third to the block scores
   lower_block_scores.

   The space E is any normedModType R and serves only as the type of the
   points A, U, V and W. MathComp is imported only for normedModType;
   R_scope is opened after it, so the arithmetic is Stdlib's. *)

Definition lower_inner_cumulant {E : normedModType R} gamma
    (F : nat -> nat -> E -> R) S (A U V W : E) z : R :=
  gibbs_cumulant3 gamma (fun s => F z s A) S
    (fun s => F z s U) (fun s => F z s V) (fun s => F z s W).

Definition lower_third {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U V W : E) : R :=
  gamma ^ 2 * gibbs_average (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_cumulant gamma F S A U V W) -
  beta * gamma * (
    gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A U V) (lower_inner_first gamma F S A W) +
    gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A U W) (lower_inner_first gamma F S A V) +
    gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A V W) (lower_inner_first gamma F S A U)) +
  beta ^ 2 * gibbs_cumulant3 (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_first gamma F S A U) (lower_inner_first gamma F S A V)
    (lower_inner_first gamma F S A W).

Definition lower_block_third n m beta gamma y B Y S (A U V W : block_array n m) : R :=
  lower_third beta gamma (lower_block_scores n m y B) Y S A U V W.
