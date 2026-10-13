From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import opnorm.
From GaussianApplications Require Import SKGapDefinitions SKGapStatement.
From GaussianApplications.SKGap Require Import Disorder Poincare.

(**md**************************************************************************)
(* # The spectral gap of the SK heat-bath dynamics: the theorem               *)
(*                                                                            *)
(* Proves sk_gap_statement (target T4 of phase 12, AGENTS.md, section Phase   *)
(* 12) of applications/SKGapStatement.v. A Rocq formalization of the credited *)
(* argument of 'Cutoff throughout the high-temperature Sherrington-           *)
(* Kirkpatrick phase' (family 227 of the OpenAI math collection, revision     *)
(* 1581d4cbd, appendices/entropy.tex): the proposition 'Good disorder', the   *)
(* lemma 'Uniform two-spin inequality' and the proposition 'Gap and           *)
(* covariance under scaled interactions and fields'. The Lean counterparts,   *)
(* in lean/OAI/Probability/SKRatio of the collection:                         *)
(* Lean: exists_uniform_gap_tolerance (Variational/UniformGap.lean)           *)
(* Lean: uniform_gap_high_probability (Gaussian/GaussianEvents.lean)          *)
(*                                                                            *)
(* For 0 <= beta < 1/2 the events are E_n = sk_good_disorder n beta delta of  *)
(* applications/SKGap/Disorder.v, with the explicit tolerance delta =         *)
(* sk_gap_tol beta = min (1/2000) ((1 - 2 beta) / 400000) of                  *)
(* applications/SKGap/Poincare.v: opnorm J <= 2 beta + delta, sum_j J_ij^2 <= *)
(* beta^2 + delta for every row and |J_ij| <= delta, for J = sk_coupling beta *)
(* a. They are measurable and their probability under gauss (n * n) tends to  *)
(* one (sk_good_disorder_measurable, sk_good_disorder_prob); on them, for     *)
(* every s in [0, 1] and every field theta, kappa Var_nu(f) <= E(f) for every *)
(* f and opnorm Cov_nu(x) <= 1 / kappa, with kappa = (1 - 2 beta) / 2         *)
(* (sk_gap_deterministic). The manuscript states the gap for all large n; the *)
(* tolerance here works for every n.                                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Theorem sk_gap_theorem : sk_gap_statement.
Proof.
move=> R beta b0 b1.
have d0 : 0 < sk_gap_tol beta := sk_gap_tol_gt0 b1.
exists (fun n => sk_good_disorder n beta (sk_gap_tol beta)); split.
- by move=> n; exact: sk_good_disorder_measurable.
- exact: (sk_good_disorder_prob beta (sk_gap_tol beta) b0 d0).
- move=> n a [hop hrow hent] s theta s0 s1.
  exact: (sk_gap_deterministic theta b0 b1 d0 (lexx _) (sk_coupling_sym beta a)
    (sk_coupling_diag beta a) hop hrow hent s0 s1).
Qed.
