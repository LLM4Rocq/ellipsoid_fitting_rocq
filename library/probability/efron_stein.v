From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral hoelder probability.
From GaussianAnalysis.probability Require Import lindeberg.

(**md**************************************************************************)
(* # The Efron-Stein inequality and moment bounds for product laws            *)
(*                                                                            *)
(* For x of law tuple_prod mu n (lindeberg.v), x^(i) is x with its coordinate *)
(* i replaced by an independent t of law mu i: tuple_set x i t.               *)
(*                                                                            *)
(* Planned results (phase 5, stage 1); names come with the proofs:            *)
(* - Fubini at one coordinate: for i < n and F : n.-tuple T -> \bar R,        *)
(*   \int[tuple_prod mu n]_x F x is                                           *)
(*   \int[tuple_prod mu n]_x \int[mu i]_t F (tuple_set x i t)                 *)
(*   when F is measurable and nonnegative, and when F is integrable; the      *)
(*   inner integral is a measurable function of x (it does not depend on      *)
(*   x_i) and, for F integrable, t |-> F (tuple_set x i t) is integrable for  *)
(*   almost every x;                                                          *)
(* - the Efron-Stein inequality, in the conditional form: for F in            *)
(*   Lfun (tuple_prod mu n) 2,                                                *)
(*   'V_(tuple_prod mu n)[F] <= \sum_(i < n) \int[tuple_prod mu n]_x V i x,   *)
(*   where V i x = 'V_(mu i)[fun t => F (tuple_set x i t)],                   *)
(*   and in the resampled form Var F <= 1/2 \sum_i E (F (x) - F (x^(i)))^2;   *)
(*   first for bounded F, by induction on n and the law of total variance,    *)
(*   then by truncation;                                                      *)
(* - moments from Efron-Stein (Koehler and Sohn, the L^p recursion in the     *)
(*   proof of their Proposition 2.6): for p = 2^(k+1) and F in L^p,           *)
(*   ||F - E F||_p^2 <= c_k \sum_i ||F (x) - F (x^(i))||_p^2, with c_0 = 1/2, *)
(*   c_1 = 17/2, c_2 = 81/2 and c_(k+1) = 2^(2k+3) + c_k, by Efron-Stein for  *)
(*   |F - E F|^(p/2) and Hoelder's inequality.                                *)
(******************************************************************************)
