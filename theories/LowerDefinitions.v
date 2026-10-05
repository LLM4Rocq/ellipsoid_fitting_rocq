From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions MatrixDefinitions SoftMatrixDefinitions.
Open Scope R_scope.

(* Port of theories/LowerDefinitions.v from Coquelicot to MathComp-Analysis.

   Coquelicot's NormedModule R_AbsRing becomes normedModType R, as in the
   port of MatrixDefinitions. block_NormedModule n m is built from
   tuple_NormedModule and matrix_NormedModule of that port, whose products
   are euclidean_product of MatrixEuclideanProduct and keep Coquelicot's
   product norm. A block array therefore still carries the Euclidean norm of
   all its entries, the square root of the sum of the squared Frobenius norms
   of its blocks, as in the original. Its ball is the norm ball, as
   MatrixDefinitions explains, and its topology is the one of the original.

   The generic definitions lower_inner_value to lower_second take the space
   E as an implicit normedModType R, where the original took an implicit
   NormedModule R_AbsRing. E is used only as the type of the points A, U, V,
   so their values are those of the original.

   One change of notation. With ssreflect loaded, the bare name seq means
   MathComp's type of sequences, so lower_block_scores and lower_block_phi
   write List.seq, the function of Stdlib's List that the original used. The
   index list is List.seq 0 (S m) = [0; ...; m], as before. MathComp is
   imported only for normedModType; R_scope is opened after it, so the
   arithmetic, including the products, the difference and the minus sign of
   - beta, is Stdlib's, as before. *)

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
