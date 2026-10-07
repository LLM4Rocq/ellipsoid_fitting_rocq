From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.

(**md**************************************************************************)
(* # Subgaussian and subexponential random variables                          *)
(*                                                                            *)
(* A real random variable X on a probability space P is subgaussian with      *)
(* constant K > 0 when E exp (X^2 / K^2) <= 2, and subexponential with        *)
(* constant L > 0 when E exp (|X| / L) <= 2. The least such constants are     *)
(* the norms psi_2 and psi_1 of Vershynin, High-Dimensional Probability,      *)
(* sections 2.5 and 2.7. Independent variables are functions f_i (x_i) of     *)
(* the coordinates of a tuple x of law tuple_prod mu n (lindeberg.v).         *)
(*                                                                            *)
(* ```                                                                        *)
(*    subgaussian P X K == 0 < K, X is measurable and E exp (X^2 / K^2) <= 2  *)
(* subexponential P X L == 0 < L, X is measurable and E exp (|X| / L) <= 2    *)
(*        psi2_norm P X == the infimum of the K with subgaussian P X K        *)
(* ```                                                                        *)
(*                                                                            *)
(* Planned results (phase 5, stage 1), with explicit constants; names come    *)
(* with the proofs:                                                           *)
(* - the infimum is attained: if X is subgaussian with some constant, then    *)
(*   subgaussian P X K for every K > 0 with psi2_norm P X <= K (monotone      *)
(*   convergence);                                                            *)
(* - tails and moments: P(|X| >= t) <= 2 exp (- t^2 / K^2) and                *)
(*   E X^(2k) <= 2 k! K^(2k), so every power of X is integrable;              *)
(* - the moment generating function of a centered X: if E X = 0, then         *)
(*   E exp (l X) <= exp (l^2 K^2) for every real l; conversely, if            *)
(*   E exp (l X) <= exp (l^2 s^2) for every l, then X is subgaussian with     *)
(*   constant 4 s / sqrt 3 (by integrating against a standard normal law);    *)
(* - Hoeffding's inequality: for x of law tuple_prod mu n and centered        *)
(*   f_i (x_i), subgaussian with constants K_i, the sum                       *)
(*   \sum_i a_i f_i (x_i) has moment generating function at most              *)
(*   exp (l^2 \sum_i a_i^2 K_i^2) and is subgaussian with constant            *)
(*   4 / sqrt 3 (\sum_i a_i^2 K_i^2)^(1/2); for laws nu j on the line with    *)
(*   mean 0 and E exp (x^2 / K^2) <= 2, and every a,                          *)
(*   E exp ((\sum_j a_j x_j)^2 / (16 / 3 K^2 \sum_j a_j^2)) <= 2 under        *)
(*   tuple_prod nu d (the left side is 1 when a = 0);                         *)
(* - X^2 is subexponential with constant K^2, X Y with constant K L for X, Y  *)
(*   subgaussian with constants K, L, and Y - E Y with constant 3 L for Y     *)
(*   subexponential with constant L;                                          *)
(* - the moment generating function of a centered subexponential Y:           *)
(*   E exp (l Y) <= exp (8 l^2 L^2) for |l| <= 1 / (2 L);                     *)
(* - Bernstein's inequality: for x of law tuple_prod mu n and centered        *)
(*   f_i (x_i), subexponential with constants L_i, and reals a_i,             *)
(*   P(|\sum_i a_i f_i (x_i)| >= t) <= 2 exp (- min (t^2 / (32 s^2),          *)
(*   t / (4 M))), where s^2 = \sum_i a_i^2 L_i^2 and M = \max_i |a_i| L_i;    *)
(*   in particular, if every f_i has constant L, then                         *)
(*   P(|\sum_(i < n) f_i (x_i)| >= t) <=                                      *)
(*   2 exp (- min (t^2 / (32 n L^2), t / (4 L))).                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section subgaussian.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition subgaussian (X : T -> R) (K : R) : Prop :=
  [/\ 0 < K, measurable_fun [set: T] X &
      ('E_P[fun t => expR (X t ^+ 2 / K ^+ 2)] <= 2%:E)%E].

Definition subexponential (Y : T -> R) (L : R) : Prop :=
  [/\ 0 < L, measurable_fun [set: T] Y &
      ('E_P[fun t => expR (`|Y t| / L)] <= 2%:E)%E].

Definition psi2_norm (X : T -> R) : R := inf [set K | subgaussian X K].

End subgaussian.
