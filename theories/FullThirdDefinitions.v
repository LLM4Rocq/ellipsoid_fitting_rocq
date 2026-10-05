From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import GibbsDefinitions ThirdDefinitions LowerDefinitions.
Open Scope R_scope.

(* Port of theories/FullThirdDefinitions.v from Coquelicot to
   MathComp-Analysis.

   The generic definitions lower_inner_cumulant and lower_third take the
   space E as an implicit normedModType R, where the original took an
   implicit NormedModule R_AbsRing. This matches the port of
   LowerDefinitions, whose lower_inner_value, lower_inner_first and
   lower_inner_covariance take the same implicit E. E is used only as the
   type of the points A, U, V and W, so the values are those of the
   original.

   lower_block_third is stated on block_array n m of the port of
   LowerDefinitions, which keeps the Euclidean norm of the original. Its
   value does not depend on that norm.

   The text of the three definitions is the original's. MathComp is
   imported only for normedModType; R_scope is opened after it, so the
   arithmetic, including the powers gamma ^ 2 and beta ^ 2, the products,
   the sums, the difference and the minus sign of - beta, is Stdlib's, as
   before. *)

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
