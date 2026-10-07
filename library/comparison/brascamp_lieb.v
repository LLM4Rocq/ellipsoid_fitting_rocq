From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals ereal exp.
From mathcomp Require Import measure lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import numfun measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss lebesgue_rV.
From GaussianAnalysis.matrix Require Import euclidean.

(**md**************************************************************************)
(* # The Brascamp-Lieb inequality in geometric form                           *)
(*                                                                            *)
(* Ball's geometric form of the Brascamp-Lieb inequality. Let u_1, ..., u_n   *)
(* be unit vectors of 'rV[R]_m and c_1, ..., c_n positive weights such that   *)
(* sum_i c_i u_i^T u_i is the identity matrix of size m. For measurable       *)
(* F_1, ..., F_n : R -> [0, +oo],                                             *)
(*                                                                            *)
(*   int_{R^m} prod_i F_i(<x, u_i>)^{c_i} dx <= prod_i (int_R F_i)^{c_i}.     *)
(*                                                                            *)
(* Values are extended reals, the powers are poweR, and the products follow   *)
(* the conventions of MathComp-Analysis (0 * +oo = 0). The frame condition    *)
(* gives sum_i c_i = m and sum_i c_i <x, u_i>^2 = |x|^2.                      *)
(*                                                                            *)
(* The proof goes through the Gaussian form, the same inequality with         *)
(* gauss m on the left and normal_prob 0 1 on the right: for bounded          *)
(* f_i >= delta > 0, the integral against gauss m of                          *)
(* prod_i (mehler r f_i)(<x, u_i>)^{c_i} is nonincreasing in r on [0, 1]      *)
(* (ornstein_uhlenbeck.v), by Gaussian integration by parts along each u_i    *)
(* and a weighted Cauchy-Schwarz inequality; at r = 1 it is the left side     *)
(* and at r = 0 the right side. The Lebesgue form follows with                *)
(* f_i(t) = F_i(t) sqrt (2 pi) exp (t^2 / 2), since gauss m has the density   *)
(* gauss_pdf with respect to lebesgue_rV m.                                   *)
(*                                                                            *)
(* Work in progress: the statement below is proved in this file once the      *)
(* Gaussian form is done; until then it stands here as a comment.             *)
(*                                                                            *)
(* ```                                                                        *)
(* Theorem brascamp_lieb m n (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R)           *)
(*     (F : 'I_n -> R -> \bar R) :                                            *)
(*   (forall i, mxdot (u i) (u i) = 1) -> (forall i, 0 < c i) ->              *)
(*   \sum_i c i *: ((u i)^T *m u i) = 1%:M ->                                 *)
(*   (forall i, measurable_fun [set: R] (F i)) ->                             *)
(*   (forall i t, 0 <= F i t)%E ->                                            *)
(*   (\int[lebesgue_rV m]_x \prod_i F i (mxdot x (u i)) `^ c i <=             *)
(*    \prod_i (\int[lebesgue_measure]_t F i t) `^ c i)%E.                     *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
