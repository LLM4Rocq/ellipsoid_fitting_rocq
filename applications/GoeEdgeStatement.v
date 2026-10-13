From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import opnorm lambda_max.
From GaussianAnalysis.random_matrix Require Import goe.

(**md**************************************************************************)
(* # Sharp upper edge of the GOE: the statement                               *)
(*                                                                            *)
(* Target T3 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The statement of a Rocq formalization   *)
(* of the credited argument of 'Cutoff throughout the high-temperature        *)
(* Sherrington-Kirkpatrick phase' (family 227 of the OpenAI math collection,  *)
(* revision 1581d4cbd): the lemma 'Gaussian concentration and comparison' and *)
(* the first part of the proof of the proposition 'Good disorder'             *)
(* (appendices/entropy.tex). This file holds the statement only. The Lean     *)
(* counterparts, in lean/OAI/Probability/SKRatio of the collection:           *)
(* Lean: goe_expected_top (Matrices/DiagonalTMemLp.lean, line 93)             *)
(* Lean: goe_norm_tail (Matrices/GoeMatrixQuadCoeff.lean, line 115)           *)
(*                                                                            *)
(* Setting. R is any realType and d >= 1. a has law gauss (d * d), the        *)
(* standard Gaussian measure on 'rV[R]_(d * d) (gaussian/gauss.v), and W =    *)
(* goe_mx a is the GOE matrix (A + A^T) / sqrt (2 d) of random_matrix/goe.v,  *)
(* A = vec_mx a: its entries W_ij, i <= j, are independent centered normal,   *)
(* of variance 1 / d off the diagonal and 2 / d on it. lambda_max is the      *)
(* supremum of x^T W x over the unit vectors x (matrix/lambda_max.v), opnorm  *)
(* the operator norm (matrix/opnorm.v). Probabilities are values of gauss (d  *)
(* * d), extended reals; E is the integral against it.                        *)
(*                                                                            *)
(* goe_edge_statement, for every R and every d >= 1:                          *)
(*                                                                            *)
(* (a) a |-> lambda_max (goe_mx a) is measurable and integrable against gauss *)
(* (d * d);                                                                   *)
(*                                                                            *)
(* (b) E lambda_max W <= 2;                                                   *)
(*                                                                            *)
(* (c) for every t >= 0, P(lambda_max W >= 2 + t) <= exp (- d t^2 / 4), and   *)
(* P(lambda_max (- W) >= 2 + t) <= exp (- d t^2 / 4);                         *)
(*                                                                            *)
(* (d) for every t >= 0, P(opnorm W >= 2 + t) <= 2 exp (- d t^2 / 4).         *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - (b) bounds the expectation of lambda_max W, not of opnorm W, as the      *)
(*   candidates review asks; opnorm W = max (lambda_max W, lambda_max (- W))  *)
(*   for symmetric W (opnorm_lambda_max), which gives (d) from (c).           *)
(*                                                                            *)
(* - The tail constant d / 4 is the sharp one of Gaussian concentration for   *)
(*   the sqrt (2 / d)-Lipschitz function a |-> lambda_max (goe_mx a). The TeX *)
(*   states its concentration lemma with the constant pi^2 / 8 of the Maurey- *)
(*   Pisier argument, and the second Lean theorem cited above bounds the tail *)
(*   of the norm by 2 exp (- eps^2 d / (pi^2 j)) at the scale j of its        *)
(*   matrices. The statement here is stronger than both.                      *)
(*                                                                            *)
(* - The manuscript writes the bound for the matrix beta W of its coupling;   *)
(*   the statement is at beta = 1, the library normalization of goe_mx, and   *)
(*   the scaling to beta W is linear.                                         *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition goe_edge_statement : Prop :=
  forall (R : realType) (d : nat), (0 < d)%N ->
  [/\ measurable_fun [set: 'rV[R]_(d * d)] (fun a : 'rV[R]_(d * d) => lambda_max (goe_mx a)) /\
      (gauss (d * d)).-integrable [set: 'rV[R]_(d * d)]
        (EFin \o (fun a : 'rV[R]_(d * d) => lambda_max (goe_mx a))),
      \int[gauss (d * d)]_a lambda_max (goe_mx a) <= (2 : R),
      forall t : R, 0 <= t ->
        (gauss (d * d) [set a | (2 + t <= lambda_max (goe_mx a))%R] <=
           (expR (- (d%:R * t ^+ 2 / 4)))%:E)%E /\
        (gauss (d * d) [set a | (2 + t <= lambda_max (- goe_mx a))%R] <=
           (expR (- (d%:R * t ^+ 2 / 4)))%:E)%E &
      forall t : R, 0 <= t ->
        (gauss (d * d) [set a | (2 + t <= opnorm (goe_mx a))%R] <=
           (2 * expR (- (d%:R * t ^+ 2 / 4)))%:E)%E].
