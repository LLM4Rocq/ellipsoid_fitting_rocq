From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.matrix Require Import euclidean opnorm nets.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.

(**md**************************************************************************)
(* # Norms of random vectors and matrices with subgaussian coordinates        *)
(*                                                                            *)
(* The coordinates are independent (a tuple of law tuple_prod mu n),          *)
(* centered and subgaussian with constant K (subgaussian.v).                  *)
(*                                                                            *)
(* Planned results (phase 5, stage 1), with explicit numerical constants:     *)
(* - concentration of the norm (Vershynin, Theorem 3.1.1): if moreover        *)
(*   E x_i^2 = 1, then P(|frobenius x - sqrt n| >= t) <= 2 exp (- c t^2 / K^4)*)
(*   for the row vector x of the coordinates, from Bernstein's inequality for *)
(*   the centered subexponential variables x_i^2 - 1;                         *)
(* - the operator norm of a matrix with independent entries (Vershynin,       *)
(*   Theorem 4.4.5): for an m x n matrix A whose entries are the coordinates  *)
(*   of a tuple of law tuple_prod mu (m * n), centered and subgaussian with   *)
(*   constant K, P(opnorm A > C K (sqrt m + sqrt n + t)) <= 2 exp (- t^2),    *)
(*   by nets of the unit spheres (nets.v) and Hoeffding's inequality.         *)
(******************************************************************************)
