From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral.
From GaussianAnalysis.gaussian Require Import gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import gauss_interpolation gauss_moments.
From GaussianAnalysis.matrix Require Import euclidean opnorm nets.
From GaussianAnalysis.comparison Require Import gauss_concentration gordon.
From GaussianAnalysis.comparison Require Import escape.
From GaussianAnalysis.convex Require Import moreau.

(**md**************************************************************************)
(* # The convex Gaussian min-max theorem, in mean and concentration form      *)
(*                                                                            *)
(* Theorem 5.3 of Koehler and Sohn (arXiv 2608.27372, lines 4972-4990;        *)
(* Thrampoulidis, Oymak and Hassibi, Theorem 3), in a self-contained form     *)
(* that suffices for the paper's limits. Let A be an n x D matrix of          *)
(* independent standard normal entries (A = vec_mx a, a of law gauss (n * D)) *)
(* and g, h independent with laws gauss n and gauss D. For a nonempty compact *)
(* set K of 'cV[R]_D with |x| <= rho on K, let                                *)
(*   Phi(K) = inf_(x in K) |A x|,                                             *)
(*   phi(K) = inf_(x in K) (|g| |x| - <h, x>)_+.                              *)
(*                                                                            *)
(* Planned results (stage 2 of phase 5; names come with the proofs):          *)
(* - Gordon's comparison for compact index sets: for K and a compact set L    *)
(*   of 'cV[R]_n, E min_(x in K) max_(y in L) (y^T A x + gamma |x| |y|) is    *)
(*   at least E min_(x in K) max_(y in L) (|x| <g, y> + |y| <h, x>), from the *)
(*   finite case (gordon.v) by nets, with gamma an independent standard       *)
(*   normal.                                                                  *)
(* - The lower bound: E Phi(K) >= E phi(K) - rho, by removing the term in     *)
(*   gamma (E |gamma| <= 1) with L the unit ball.                             *)
(* - The upper bound for K convex: E Phi(K) <= E phi(K) + rho, by the         *)
(*   minimax exchange min_(x in K) |A x| = max_(|y| <= 1) min_(x in K)        *)
(*   <y, A x>, which follows from the projection of 0 onto the compact convex *)
(*   set A K (moreau.v), then the same comparison with the roles of x and y   *)
(*   exchanged.                                                               *)
(* - Concentration: Phi(K) is rho-Lipschitz in A and phi(K) is                *)
(*   (sqrt 2 rho)-Lipschitz in (g, h), so they deviate from their means by    *)
(*   more than t with probability at most 2 exp (- t^2 / (2 rho^2)) and       *)
(*   2 exp (- t^2 / (4 rho^2)) (gauss_concentration.v).                       *)
(* Together, for K compact and convex, Phi(K) and phi(K) are within           *)
(* rho + O(rho t) of the same number with probability 1 - O(exp (- t^2 / 4)), *)
(* which gives the comparisons (eq:cgmt-comparisons) of the paper up to an    *)
(* error rho that vanishes after its normalization by d^(3/2).                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
