From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals ereal measure.
From mathcomp Require Import lebesgue_integral binomial_distribution.
From GaussianAnalysis.probability Require Import finite_mean.

(**md**************************************************************************)
(* # Binomial means                                                           *)
(*                                                                            *)
(* For m : nat, p in a numDomainType R and f : nat -> R, binomial_mean m p f  *)
(* is the expectation of f J for J binomial with m trials of success          *)
(* probability p, written as the finite sum over j <= m of f j times the      *)
(* binomial weight C(m, j) p^j (1-p)^(m-j). The definition makes sense for    *)
(* every p; the order statements assume 0 <= p <= 1.                          *)
(*                                                                            *)
(* The general statements of this file are compiled Prop definitions, for     *)
(* review with batch 1 of phase 13; their proofs follow their acceptance.     *)
(*                                                                            *)
(* - The recursion on the first trial and the value at m = 0                  *)
(*   (binomial_meanS_statement, binomial_mean0_statement), extensionality on  *)
(*   j <= m (eq_binomial_mean_statement), constants, additivity and           *)
(*   homogeneity (binomial_mean_cst_statement, binomial_meanD_statement,      *)
(*   binomial_meanZ_statement).                                               *)
(* - Monotonicity in f (ler_binomial_mean_statement), the mean m p and the    *)
(*   variance m p (1 - p) (binomial_mean_id_statement,                        *)
(*   binomial_mean_sqr_dev_statement), Chebyshev's inequality                 *)
(*   (binomial_chebyshev_statement), the event that every trial succeeds      *)
(*   (binomial_mean_last_statement), and monotonicity in the number of trials *)
(*   for a nondecreasing f (binomial_mean_trials_statement).                  *)
(* - Over a realFieldType, the exchange with the uniform mean of a finite     *)
(*   type (unif_mean_binomial_mean_statement, unif_mean of finite_mean.v).    *)
(* - Over a realType, the bridge to the binomial law of MathComp-Analysis:    *)
(*   the weights are binomial_pmf m p (binomial_meanE_statement), and the     *)
(*   integral of any f : nat -> R against binomial_prob m p is binomial_mean  *)
(*   m p f when p is in [0, 1] (integral_binomial_mean_statement).            *)
(*                                                                            *)
(* This file is part of target T9 of phase 13: a Rocq formalization of the    *)
(* binomial means of the credited argument of 'A limiting satisfiability      *)
(* threshold for every fixed clause size' (family 235 of the OpenAI math      *)
(* collection, revision 1581d4cbd). The manuscript compares Poisson numbers   *)
(* of clauses (source/sections/convergence.tex, the lemmas 'Auxiliary product *)
(* inequality' and 'Proper-clause transfer', with Chebyshev's inequality for  *)
(* a Poisson count); here, as in the Lean development of the collection       *)
(* (lean/OAI/Probability/RandomSAT), the numbers of clauses are fixed and the *)
(* comparisons are binomial mixtures. The Lean development defines its        *)
(* binomial mean by the recursion on the first trial; here the closed form is *)
(* the definition and the recursion is a statement.                           *)
(* Lean: binomialMean (Binomial.lean, line 17)                                *)
(* Lean: binomialMean_congr (Binomial.lean, line 22)                          *)
(* Lean: binomialMean_const (Binomial.lean, line 30)                          *)
(* Lean: binomialMean_add (Binomial.lean, line 35)                            *)
(* Lean: binomialMean_const_mul (Binomial.lean, line 53)                      *)
(* Lean: binomialMean_mono (Binomial.lean, line 64)                           *)
(* Lean: binomialMean_id (Binomial.lean, line 77)                             *)
(* Lean: binomialMean_monotone_trials (Binomial.lean, line 86)                *)
(* Lean: uniformMean_binomialMean (Binomial.lean, line 95)                    *)
(* Lean: binomialMean_centered_square (Transfer.lean, line 345)               *)
(* Lean: binomialMean_all_success (Transfer.lean, line 361)                   *)
(*                                                                            *)
(* ```                                                                        *)
(*   binomial_mean m p f == \sum_(j < m.+1) p ^+ j * (1 - p) ^+ (m - j)       *)
(*                          *+ 'C(m, j) * f j, the mean of f under the        *)
(*                          binomial law of m trials of probability p         *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section binomial_mean.
Context {R : numDomainType}.

Definition binomial_mean (m : nat) (p : R) (f : nat -> R) : R :=
  \sum_(j < m.+1) (p ^+ j * (1 - p) ^+ (m - j) *+ 'C(m, j)) * f j.

End binomial_mean.

(* The general statements, for review. *)

(* No trial: the value at 0. *)
Definition binomial_mean0_statement : Prop :=
  forall (R : numDomainType) (p : R) (f : nat -> R),
  binomial_mean 0 p f = f 0%N.

(* The recursion on the first trial: it fails with probability 1 - p, and
   succeeds with probability p, which shifts the count by one. *)
Definition binomial_meanS_statement : Prop :=
  forall (R : numDomainType) (m : nat) (p : R) (f : nat -> R),
  binomial_mean m.+1 p f =
  (1 - p) * binomial_mean m p f + p * binomial_mean m p (fun j => f j.+1).

(* Only the values of f at j <= m count. *)
Definition eq_binomial_mean_statement : Prop :=
  forall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R),
  (forall j, (j <= m)%N -> f j = g j) ->
  binomial_mean m p f = binomial_mean m p g.

(* The weights sum to one, for every p. *)
Definition binomial_mean_cst_statement : Prop :=
  forall (R : numDomainType) (m : nat) (p c : R),
  binomial_mean m p (fun=> c) = c.

Definition binomial_meanD_statement : Prop :=
  forall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R),
  binomial_mean m p (fun j => f j + g j) =
  binomial_mean m p f + binomial_mean m p g.

Definition binomial_meanZ_statement : Prop :=
  forall (R : numDomainType) (m : nat) (p c : R) (f : nat -> R),
  binomial_mean m p (fun j => c * f j) = c * binomial_mean m p f.

(* Monotonicity: for p in [0, 1] the weights are nonnegative. *)
Definition ler_binomial_mean_statement : Prop :=
  forall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R),
  0 <= p <= 1 -> (forall j, (j <= m)%N -> f j <= g j) ->
  binomial_mean m p f <= binomial_mean m p g.

(* The mean of the number of successes. *)
Definition binomial_mean_id_statement : Prop :=
  forall (R : numDomainType) (m : nat) (p : R),
  binomial_mean m p (fun j => j%:R) = m%:R * p.

(* The variance of the number of successes. *)
Definition binomial_mean_sqr_dev_statement : Prop :=
  forall (R : numDomainType) (m : nat) (p : R),
  binomial_mean m p (fun j => (j%:R - m%:R * p) ^+ 2) = m%:R * p * (1 - p).

(* Chebyshev's inequality for the number of successes. *)
Definition binomial_chebyshev_statement : Prop :=
  forall (R : realFieldType) (m : nat) (p t : R),
  0 <= p <= 1 -> 0 < t ->
  binomial_mean m p (fun j => (t <= `|j%:R - m%:R * p|)%R%:R) <=
  m%:R * p * (1 - p) / t ^+ 2.

(* Keeping only the event that all m trials succeed, of probability
   p ^+ m. *)
Definition binomial_mean_last_statement : Prop :=
  forall (R : numDomainType) (m : nat) (p : R) (f : nat -> R),
  0 <= p <= 1 -> (forall j, (j <= m)%N -> 0 <= f j) ->
  p ^+ m * f m <= binomial_mean m p f.

(* More trials give more successes: the mean of a nondecreasing f is
   nondecreasing in the number of trials. *)
Definition binomial_mean_trials_statement : Prop :=
  forall (R : numDomainType) (m m' : nat) (p : R) (f : nat -> R),
  0 <= p <= 1 -> {homo f : i j / (i <= j)%N >-> i <= j} -> (m <= m')%N ->
  binomial_mean m p f <= binomial_mean m' p f.

(* Fubini with the uniform law of a finite type. *)
Definition unif_mean_binomial_mean_statement : Prop :=
  forall (R : realFieldType) (T : finType) (m : nat) (p : R)
         (f : nat -> T -> R),
  unif_mean (fun x => binomial_mean m p (fun j => f j x)) =
  binomial_mean m p (fun j => unif_mean (f j)).

(* The bridge to MathComp-Analysis: the weights are those of binomial_pmf,
   and binomial_mean is the integral against the binomial law
   binomial_prob, which is the Dirac mass at 0 when p is not in [0, 1]. *)
Definition binomial_meanE_statement : Prop :=
  forall (R : realType) (m : nat) (p : R) (f : nat -> R),
  binomial_mean m p f = \sum_(j < m.+1) binomial_pmf m p j * f j.

Definition integral_binomial_mean_statement : Prop :=
  forall (R : realType) (m : nat) (p : R) (f : nat -> R),
  0 <= p <= 1 ->
  (\int[binomial_prob m p]_j (f j)%:E = (binomial_mean m p f)%:E)%E.
