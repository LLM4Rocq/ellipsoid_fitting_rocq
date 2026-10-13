From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import opnorm.
From GaussianApplications Require Import SKGapDefinitions.

(**md**************************************************************************)
(* # The spectral gap of the SK heat-bath dynamics: the statement             *)
(*                                                                            *)
(* Target T4 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The statement of a Rocq formalization   *)
(* of the credited argument of 'Cutoff throughout the high-temperature        *)
(* Sherrington-Kirkpatrick phase' (family 227 of the OpenAI math collection,  *)
(* revision 1581d4cbd, appendices/entropy.tex): the proposition 'Good         *)
(* disorder', the lemma 'Uniform two-spin inequality' and the proposition     *)
(* 'Gap and covariance under scaled interactions and fields'. This file holds *)
(* the statement only; its definitions are those of SKGapDefinitions.v. The   *)
(* Lean counterparts, in lean/OAI/Probability/SKRatio of the collection:      *)
(* Lean: exists_uniform_gap_tolerance (Variational/UniformGap.lean)           *)
(* Lean: uniform_gap_high_probability (Gaussian/GaussianEvents.lean)          *)
(*                                                                            *)
(* Setting. R is any realType, 0 <= beta < 1/2 and kappa = (1 - 2 beta) / 2.  *)
(* For a in 'rV[R]_(n * n), J = sk_coupling beta a, and for s in [0, 1] and a *)
(* field theta, nu is the Ising law of the interaction s J and the field      *)
(* theta, with weights exp (s x^T J x / 2 + <theta, x>). E is its Dirichlet   *)
(* form ising_dirichlet, the sum over the sites i of nu[v_i (d_i f)^2].       *)
(*                                                                            *)
(* sk_gap_statement, for every R and every 0 <= beta < 1/2: there are sets    *)
(* E_n of 'rV[R]_(n * n) such that                                            *)
(*                                                                            *)
(* (a) every E_n is measurable;                                               *)
(*                                                                            *)
(* (b) gauss (n * n) (E_n) tends to 1: for every eps > 0, it is at least 1 -  *)
(* eps for every large n;                                                     *)
(*                                                                            *)
(* (c) for every n, every a in E_n, every s in [0, 1] and every field theta,  *)
(* with nu the law above: kappa Var_nu(f) <= E(f) for every real function f   *)
(* on the cube, and opnorm (Cov_nu(x)) <= 1 / kappa for the covariance matrix *)
(* of the spins.                                                              *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - The good-disorder form, accepted by the user: the inequality is          *)
(*   deterministic on E_n, which is measurable and of probability tending to  *)
(*   one, and uniform over s, theta and f. The manuscript defines E_n by      *)
(*   three matrix bounds (opnorm J <= 2 beta + delta_n, row sums of J_ij^2 at *)
(*   most beta^2 + delta_n, entries at most delta_n) and states the gap for   *)
(*   all large n; here E_n is any measurable set with these properties, and   *)
(*   it may be empty for small n.                                             *)
(* - The normalization of the user's acceptance: rate one at every site, so   *)
(*   that kappa is a lower bound on the spectral gap of the heat-bath         *)
(*   generator; the inequality kappa Var_nu(f) <= E(f) is the manuscript's    *)
(*   variance bound Var_nu(f) <= kappa^(-1) sum_i nu[v_i (d_i f)^2].          *)
(* - The interaction s J is applied once, in one Ising law; s = 0 is the      *)
(*   product law of the field.                                                *)
(* - The covariance bound is the case of the linear functions f(x) = <c, x>,  *)
(*   for which d_i f = c_i and nu[v_i] <= 1; it is a conjunct of (c).         *)
(* - The manuscript's constant kappa = (1 - 2 beta) / 2 is explicit here; the *)
(*   Lean theorems state the existence of a positive constant and of a        *)
(*   tolerance delta.                                                         *)
(* - The disorder: J = beta (W - Diag W) with W = goe_mx a, so its off-       *)
(*   diagonal entries are those of the manuscript (independent, centered      *)
(*   normal, variance beta^2 / n), on the probability space of gauss (n * n)  *)
(*   used by the GOE of the library; the Lean disorder is indexed by the      *)
(*   edges i < j.                                                             *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition sk_gap_statement : Prop :=
  forall (R : realType) (beta : R), 0 <= beta -> beta < 1 / 2 ->
  exists E : forall n : nat, set 'rV[R]_(n * n),
  [/\ forall n, measurable (E n),
      forall eps : R, 0 < eps -> exists N : nat, forall n, (N <= n)%N ->
        ((1 - eps)%:E <= gauss (n * n) (E n))%E &
      forall n (a : 'rV[R]_(n * n)), E n a ->
      forall (s : R) (theta : 'cV[R]_n), 0 <= s -> s <= 1 ->
      (forall f : {ffun 'I_n -> bool} -> R,
         (1 - 2 * beta) / 2 * ising_var (s *: sk_coupling beta a) theta f <=
         ising_dirichlet (s *: sk_coupling beta a) theta f) /\
      opnorm (ising_cov (s *: sk_coupling beta a) theta) <=
        ((1 - 2 * beta) / 2)^-1].
