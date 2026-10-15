From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals ereal measure numfun.
From mathcomp Require Import lebesgue_integral binomial_distribution.
From mathcomp Require Import ring_tactic.
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
(* The lemmas below prove the general statements of this file. Each statement *)
(* is also a compiled Prop definition, named after its lemma with the suffix  *)
(* _statement, for review with batch 1 of phase 13; these definitions go once *)
(* the statements are accepted.                                               *)
(*                                                                            *)
(* - The recursion on the first trial and the value at m = 0 (binomial_meanS, *)
(*   binomial_mean0), extensionality on j <= m (eq_binomial_mean), constants, *)
(*   additivity and homogeneity (binomial_mean_cst, binomial_meanD,           *)
(*   binomial_meanZ).                                                         *)
(* - Monotonicity and nonnegativity (ler_binomial_mean, binomial_mean_ge0),   *)
(*   the mean m p, the second moment and the variance m p (1 - p)             *)
(*   (binomial_mean_id, binomial_mean_sqr, binomial_mean_sqr_dev),            *)
(*   Chebyshev's inequality (binomial_chebyshev), the event that every trial  *)
(*   succeeds (binomial_mean_last), and monotonicity in the number of trials  *)
(*   for a nondecreasing f (binomial_mean_trialsS, binomial_mean_trials).     *)
(* - Over a realFieldType, the exchange with the uniform mean of a finite     *)
(*   type (unif_mean_binomial_mean, with unif_mean of finite_mean.v).         *)
(* - Over a realType, the bridge to the binomial law of MathComp-Analysis:    *)
(*   the weights are binomial_pmf m p (binomial_meanE), and the integral of   *)
(*   any f : nat -> R against binomial_prob m p is binomial_mean m p f when p *)
(*   is in [0, 1] (integral_binomial_mean). The example                       *)
(*   binomial_prob_mean_var gives the mean m p and the variance m p (1 - p)   *)
(*   of binomial_prob, which MathComp-Analysis does not state.                *)
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

Import Order.TTheory GRing.Theory Num.Theory.
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

Section binomial_mean_theory.
Context {R : numDomainType}.
Implicit Types (m : nat) (p c : R) (f g : nat -> R).

Lemma binomial_mean0 p f : binomial_mean 0 p f = f 0%N.
Proof. by rewrite /binomial_mean big_ord1 !expr0 mul1r bin0 mulr1n mul1r. Qed.

(* The recursion on the first trial. *)
Lemma binomial_meanS m p f :
  binomial_mean m.+1 p f =
  (1 - p) * binomial_mean m p f + p * binomial_mean m p (fun j => f j.+1).
Proof.
rewrite /binomial_mean big_ord_recl /=.
under eq_bigr => i _ do rewrite /bump /= add1n subSS binS mulrnDr mulrDl.
rewrite big_split /= addrA; congr (_ + _); last first.
  by rewrite mulr_sumr; apply: eq_bigr => i _; rewrite exprS; ring.
rewrite big_ord_recr /= [in X in _ + (_ + X)]bin_small // mulr0n mul0r addr0.
rewrite [in RHS]big_ord_recl mulrDr /=.
congr (_ + _); first by rewrite !expr0 !subn0 !bin0 !mulr1n exprS; ring.
rewrite mulr_sumr; apply: eq_bigr => i _; rewrite /bump /= add1n.
by rewrite -(subnSK (ltn_ord i)) [(1 - p) ^+ _.+1]exprS; ring.
Qed.

Lemma eq_binomial_mean m p f g :
  (forall j, (j <= m)%N -> f j = g j) ->
  binomial_mean m p f = binomial_mean m p g.
Proof. by move=> fg; apply: eq_bigr => j _; rewrite fg // -ltnS. Qed.

(* The weights sum to one, for every p. *)
Lemma binomial_mean_cst m p c : binomial_mean m p (fun=> c) = c.
Proof.
elim: m => [|m IH]; first by rewrite binomial_mean0.
by rewrite binomial_meanS IH; ring.
Qed.

Lemma binomial_meanD m p f g :
  binomial_mean m p (fun j => f j + g j) =
  binomial_mean m p f + binomial_mean m p g.
Proof.
by rewrite /binomial_mean -big_split; apply: eq_bigr => j _; rewrite mulrDr.
Qed.

Lemma binomial_meanZ m p c f :
  binomial_mean m p (fun j => c * f j) = c * binomial_mean m p f.
Proof.
by rewrite /binomial_mean mulr_sumr; apply: eq_bigr => j _; rewrite mulrCA.
Qed.

(* Monotonicity, for p in [0, 1]. *)
Lemma ler_binomial_mean m p f g :
  0 <= p <= 1 -> (forall j, (j <= m)%N -> f j <= g j) ->
  binomial_mean m p f <= binomial_mean m p g.
Proof.
case/andP => p0 p1 fg; apply: ler_sum => j _.
apply: ler_wpM2l; last by rewrite fg // -ltnS.
by rewrite mulrn_wge0 // mulr_ge0 // exprn_ge0 // subr_ge0.
Qed.

Lemma binomial_mean_ge0 m p f :
  0 <= p <= 1 -> (forall j, (j <= m)%N -> 0 <= f j) ->
  0 <= binomial_mean m p f.
Proof.
by move=> p01 f0; rewrite -(binomial_mean_cst m p 0); apply: ler_binomial_mean.
Qed.

(* The mean, the second moment and the variance of the number of
   successes. *)
Lemma binomial_mean_id m p : binomial_mean m p (fun j => j%:R) = m%:R * p.
Proof.
elim: m => [|m IH]; first by rewrite binomial_mean0 mul0r.
rewrite binomial_meanS IH.
have -> : binomial_mean m p (fun j => j.+1%:R) =
    binomial_mean m p (fun j => 1 + j%:R).
  by apply: eq_binomial_mean => j _; rewrite -nat1r.
by rewrite binomial_meanD binomial_mean_cst IH -nat1r; ring.
Qed.

Lemma binomial_mean_sqr m p :
  binomial_mean m p (fun j => j%:R ^+ 2) =
  m%:R * p * (1 - p) + (m%:R * p) ^+ 2.
Proof.
elim: m => [|m IH]; first by rewrite binomial_mean0 !mul0r expr0n addr0.
rewrite binomial_meanS IH.
have -> : binomial_mean m p (fun j => j.+1%:R ^+ 2) =
    binomial_mean m p (fun j => j%:R ^+ 2 + (2 * j%:R + 1)).
  by apply: eq_binomial_mean => j _; rewrite -nat1r; ring.
rewrite binomial_meanD binomial_meanD binomial_meanZ binomial_mean_id.
by rewrite binomial_mean_cst IH -nat1r; ring.
Qed.

Lemma binomial_mean_sqr_dev m p :
  binomial_mean m p (fun j => (j%:R - m%:R * p) ^+ 2) = m%:R * p * (1 - p).
Proof.
transitivity (binomial_mean m p (fun j => j%:R ^+ 2 +
    ((- (2 * (m%:R * p))) * j%:R + (m%:R * p) ^+ 2))).
  by apply: eq_binomial_mean => j _; ring.
rewrite !binomial_meanD binomial_meanZ binomial_mean_cst binomial_mean_sqr.
by rewrite binomial_mean_id; ring.
Qed.

(* Keeping only the event that all m trials succeed. *)
Lemma binomial_mean_last m p f :
  0 <= p <= 1 -> (forall j, (j <= m)%N -> 0 <= f j) ->
  p ^+ m * f m <= binomial_mean m p f.
Proof.
move=> p01; case/andP: (p01) => p0 p1.
elim: m f => [|m IH] f f0; first by rewrite expr0 mul1r binomial_mean0.
rewrite binomial_meanS exprS -mulrA.
have h1 : 0 <= (1 - p) * binomial_mean m p f.
  rewrite mulr_ge0 ?subr_ge0 // binomial_mean_ge0 // => j jm.
  by rewrite f0 // ltnW.
have h2 : p ^+ m * f m.+1 <= binomial_mean m p (fun j => f j.+1).
  by apply: (IH (fun j => f j.+1)) => j jm; rewrite f0.
by rewrite -[p * _]add0r lerD // ler_wpM2l.
Qed.

(* More trials give more successes. *)
Lemma binomial_mean_trialsS m p f :
  0 <= p <= 1 -> {homo f : i j / (i <= j)%N >-> i <= j} ->
  binomial_mean m p f <= binomial_mean m.+1 p f.
Proof.
move=> p01 hf; case/andP: (p01) => p0 p1; rewrite binomial_meanS.
have h : binomial_mean m p f <= binomial_mean m p (fun j => f j.+1).
  by apply: ler_binomial_mean => // j _; apply: hf.
have e : binomial_mean m p f =
    (1 - p) * binomial_mean m p f + p * binomial_mean m p f by ring.
by rewrite {1}e lerD2l ler_wpM2l.
Qed.

Lemma binomial_mean_trials m m' p f :
  0 <= p <= 1 -> {homo f : i j / (i <= j)%N >-> i <= j} -> (m <= m')%N ->
  binomial_mean m p f <= binomial_mean m' p f.
Proof.
move=> p01 hf; elim: m' => [|m' IH]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP[/eqP -> //|]; rewrite ltnS => mm.
exact: le_trans (IH mm) (binomial_mean_trialsS _ p01 hf).
Qed.

End binomial_mean_theory.

Section binomial_mean_real.
Context {R : realFieldType}.

(* Chebyshev's inequality for the number of successes. *)
Lemma binomial_chebyshev m (p t : R) :
  0 <= p <= 1 -> 0 < t ->
  binomial_mean m p (fun j => (t <= `|j%:R - m%:R * p|)%R%:R) <=
  m%:R * p * (1 - p) / t ^+ 2.
Proof.
move=> p01 t0; rewrite ler_pdivlMr ?exprn_gt0 // -binomial_mean_sqr_dev.
rewrite mulrC -binomial_meanZ; apply: ler_binomial_mean => // j _.
case: (lerP t `|j%:R - m%:R * p|) => h; rewrite ?mulr1 ?mulr0 ?sqr_ge0 //.
rewrite -[(j%:R - m%:R * p) ^+ 2]real_normK ?num_real //.
by rewrite lerXn2r // ?nnegrE ?normr_ge0 // ltW.
Qed.

(* Fubini with the uniform law of a finite type. *)
Lemma unif_mean_binomial_mean (T : finType) m (p : R) (f : nat -> T -> R) :
  unif_mean (fun x => binomial_mean m p (fun j => f j x)) =
  binomial_mean m p (fun j => unif_mean (f j)).
Proof.
rewrite /binomial_mean unif_mean_sum; apply: eq_bigr => j _.
exact: unif_meanZ.
Qed.

End binomial_mean_real.

Section binomial_mean_bridge.
Context {R : realType}.

(* The weights are those of binomial_pmf, and binomial_mean is the integral
   against binomial_prob for p in [0, 1]. *)
Lemma binomial_meanE m (p : R) (f : nat -> R) :
  binomial_mean m p f = \sum_(j < m.+1) binomial_pmf m p j * f j.
Proof. by []. Qed.

Lemma integral_binomial_mean m (p : R) (f : nat -> R) :
  0 <= p <= 1 ->
  (\int[binomial_prob m p]_j (f j)%:E = (binomial_mean m p f)%:E)%E.
Proof.
case/andP => p0 p1; have p1' : (NngNum p0)%:num <= 1 := p1.
rewrite integralE (integral_binomial _ p1' (funepos_ge0 _)).
rewrite (integral_binomial _ p1' (funeneg_ge0 _)).
under eq_bigr do rewrite funeposE -EFin_max -EFinM.
under [X in (_ - X)%E]eq_bigr do
  rewrite funenegE -EFinN -EFin_max -EFinM.
rewrite !sumEFin -EFinB; congr EFin.
rewrite -sumrB /binomial_mean; apply: eq_bigr => k _; rewrite -mulrBr /=.
congr (_ * _); have [h|h] := leP 0 (f k).
  by rewrite (max_idPr _) ?subr0 // oppr_le0.
by rewrite (max_idPl _) ?sub0r ?opprK // oppr_ge0 ltW.
Qed.

End binomial_mean_bridge.

(* An example: the mean and the variance of the binomial law binomial_prob
   of MathComp-Analysis. *)
Example binomial_prob_mean_var (R : realType) m (p : R) : 0 <= p <= 1 ->
  (\int[binomial_prob m p]_j (j%:R)%:E = (m%:R * p)%:E)%E /\
  (\int[binomial_prob m p]_j ((j%:R - m%:R * p) ^+ 2)%:E =
   (m%:R * p * (1 - p))%:E)%E.
Proof.
move=> p01; rewrite !integral_binomial_mean //.
by rewrite binomial_mean_id binomial_mean_sqr_dev.
Qed.
