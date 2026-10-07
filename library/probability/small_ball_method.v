From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg moments.
From GaussianAnalysis.probability Require Import symmetrization.

(**md**************************************************************************)
(* # The small-ball method                                                    *)
(*                                                                            *)
(* Mendelson's small-ball method, in the form of Koltchinskii and Mendelson   *)
(* (2015, Theorem 2.1), cited by Koehler and Sohn (arXiv 2608.27372, lines    *)
(* 4764-4779): a uniform lower bound for the empirical second moments of a    *)
(* class of functions, from a lower bound on its small-ball probabilities     *)
(* and an upper bound on its Rademacher complexity. The deviation of the      *)
(* empirical process is controlled in expectation, by symmetrization and      *)
(* contraction (symmetrization.v), and then by Markov's inequality, so the    *)
(* probability of failure is of the order of the complexity: this suffices    *)
(* for limits in probability when the scale grows, and no bounded             *)
(* differences inequality is needed. The class is a sequence; uncountable     *)
(* classes are reached through countable dense subclasses.                    *)
(*                                                                            *)
(* Main results to prove (stage 1 of phase 5; names come with the proofs),    *)
(* for X_1, ..., X_n independent with laws mu_1, ..., mu_n (tuple_prod),      *)
(* n > 0:                                                                     *)
(* - The small-ball method: for a sequence f_j of measurable functions,       *)
(*   u > 0 and q with mu_k(|f_j| >= 2 u) >= q for all j and k, and r with     *)
(*     E rademacher_mean (max_(j < J) |(1/n) sum_k eps_k f_j(X_k)|) <= r      *)
(*   for every J, the probability that some f_j has                           *)
(*   #{k : |f_j(X_k)| >= u} < n q / 2 is at most 8 r / (u q). Proof: the      *)
(*   1/u-Lipschitz ramp between u and 2 u, symmetrization and contraction     *)
(*   for the finite initial segments, monotone convergence and Markov's       *)
(*   inequality.                                                              *)
(* - If E f^2 = 1 and E f^4 <= C, then mu(|f| >= 1/2) >= 9 / (16 C)           *)
(*   (Paley-Zygmund, paley_zygmund_sqr).                                      *)
(* - Every set of row vectors has a countable dense subset.                   *)
(* - Linear classes: let Z_1, ..., Z_n be independent random vectors of       *)
(*   'rV[R]_N, D a set of vectors and N a measurable function with            *)
(*   |<z, theta>| <= N(z) for all z and all theta in D, where <., .> is       *)
(*   mxdot. Assume E <Z_k, theta> = 0, E <Z_k, theta>^2 = v(theta) and        *)
(*   E <Z_k, theta>^4 <= K v(theta)^2 for theta in D, and                     *)
(*     E rademacher_mean (N ((1/n) sum_k eps_k Z_k)) <= rho.                  *)
(*   Then for s > 0 there is a measurable event of probability at most        *)
(*   C (rho / s + 1 / sqrt n) outside of which                                *)
(*     (1/n) sum_k (<Z_k, theta> - b)^2 >= c (v(theta) + b^2)                 *)
(*   for every theta in D and every real b with v(theta) + b^2 >= s^2, with   *)
(*   c and C depending only on K. Removing the ridge (Lemma 2.12) uses it     *)
(*   with D the positive semidefinite matrices of trace d and                 *)
(*   N(z) = d opnorm (sym (vec_mx z)), with s^2 of order ln d.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
