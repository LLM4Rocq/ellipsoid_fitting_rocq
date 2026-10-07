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
(* and an upper bound on its Rademacher complexity. The class is finite,      *)
(* then a sequence; uncountable classes are reached through countable dense   *)
(* subclasses, so no supremum over an uncountable class is integrated.        *)
(*                                                                            *)
(* Main results to prove (stage 1 of phase 5; names come with the proofs),    *)
(* for X_1, ..., X_n independent with laws mu_1, ..., mu_n (tuple_prod),      *)
(* n > 0:                                                                     *)
(* - The small-ball method: for a finite class f_i of measurable functions,   *)
(*   u > 0, q with mu_k(|f_i| >= 2 u) >= q for all i and k, and r bounding    *)
(*   the Rademacher complexity,                                               *)
(*     E rademacher_mean (max_i |(1/n) sum_k eps_k f_i(X_k)|) <= r,           *)
(*   for every t >= 0, with probability at least 1 - exp (- n t^2 / 2),       *)
(*   every f_i satisfies #{k : |f_i(X_k)| >= u} >= n (q - 4 r / u - t), hence *)
(*   (1/n) sum_k f_i(X_k)^2 >= u^2 (q - 4 r / u - t). Proof: the              *)
(*   1/u-Lipschitz ramp between u and 2 u, the bounded differences            *)
(*   inequality for the supremum of the empirical process of the ramps,       *)
(*   symmetrization and contraction (symmetrization.v).                       *)
(* - The same for a sequence of functions f_i, i : nat, when the Rademacher   *)
(*   bound holds for every finite initial segment.                            *)
(* - If E f^2 = 1 and E f^4 <= C, then mu(|f| >= 1/2) >= 9 / (16 C)           *)
(*   (Paley-Zygmund, paley_zygmund_sqr).                                      *)
(* - Every set of real matrices has a countable dense subset.                 *)
(* - Linear classes: let Z_1, ..., Z_n be independent random matrices of      *)
(*   'M[R]_(p, q) with laws P_k, D a set of matrices, N a function with       *)
(*   |<Z, theta>| <= N(Z) for all Z and all theta in D, where <., .> is the   *)
(*   Frobenius product mxdot. Assume E <Z_k, theta> = 0 and                   *)
(*   E <Z_k, theta>^4 <= K v(theta)^2 for theta in D, where                   *)
(*   v(theta) = E <Z_k, theta>^2 does not depend on k, and                    *)
(*     E rademacher_mean (N ((1/n) sum_k eps_k Z_k)) <= rho.                  *)
(*   Let q0 = 9 / (128 max(K, 1)). If rho / s + 1 / sqrt n <= q0 / 64, there  *)
(*   is a measurable event of probability at least 1 - exp (- n q0^2 / 32)    *)
(*   on which                                                                 *)
(*     (1/n) sum_k (<Z_k, theta> - b)^2 >= (q0 / 32) (v(theta) + b^2)         *)
(*   for every theta in D and every real b with v(theta) + b^2 >= s^2.        *)
(*   Removing the ridge (Lemma 2.12) uses it with D the positive              *)
(*   semidefinite matrices of trace at most tau and N(Z) = tau opnorm Z.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
