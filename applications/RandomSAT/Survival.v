From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import arithmetic_tactic ring_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
From GaussianApplications.RandomSAT Require Import Model Pivotal.
From GaussianApplications Require Import SatVarianceDefinitions.
From GaussianApplications Require Import SatThresholdDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: the satisfiability probability as a survival probability   *)
(*                                                                            *)
(* Part of target T9 of phase 13 (AGENTS.md, section Phase 13; the plan       *)
(* notes/phase13-plan.md, section 2). A Rocq formalization of the first steps *)
(* of the credited argument of 'A Limiting Satisfiability Threshold for Every *)
(* Fixed Clause Size' (family 235 of the OpenAI math collection, revision     *)
(* 1581d4cbd), following the Lean development of the collection               *)
(* (lean/OAI/Probability/RandomSAT):                                          *)
(* Lean: survival_eq_mean (ClauseProcess.lean, line 164)                      *)
(* Lean: properSATProbability_eq_survival (ClauseProcess.lean, line 179)      *)
(* Lean: survival_antitone (ClauseProcess.lean, line 213)                     *)
(* Lean: properSATProbability_antitone (ClauseProcess.lean, line 223)         *)
(* Lean: properSATProbability_le_one (Clauses.lean, line 115)                 *)
(* Lean: lifetime_tail_probability (Concentration.lean, line 118)             *)
(* Lean: properSATProbability_eq_lifetime_tail (Concentration.lean, line 156) *)
(*                                                                            *)
(* The clauses have size k and n variables. P_n(m) = sat_prob R n k m is the  *)
(* probability of satisfiability of SatThresholdDefinitions.v.                *)
(*                                                                            *)
(* - sat_probE: P_n(m) is survival k m [set: _] of Pivotal.v, the probability *)
(*   that the set of all assignments keeps a solution after m independent     *)
(*   uniform clauses.                                                         *)
(* - sat_prob_ge0, sat_prob_le1, and sat_prob0: the empty formula is          *)
(*   satisfiable.                                                             *)
(* - For k <= n, survival_antitone and sat_prob_le: one more clause can only  *)
(*   remove solutions, so P_n(m) is nonincreasing in m.                       *)
(* - survival_tail and sat_prob_tail: for k <= n and m <= M, P_n(m) is the    *)
(*   probability that the longest satisfiable prefix of M independent uniform *)
(*   clauses (sat_prefix_len) has length at least m. For M = sat_cap k n this *)
(*   is the survival identity P_n(m) = P(V_n >= m) of the manuscript          *)
(*   (source/sections/forcing.tex, equation eq:survival); here M is any cap   *)
(*   at least m, as for the general caps of source/sections/convergence.tex   *)
(*   (equation eq:general-cap-survival).                                      *)
(*                                                                            *)
(* The Lean development proves the identity by induction on m along the       *)
(* survival recursion; so does survival_tail, for every set S of assignments, *)
(* through the lifetime life S t of Model.v.                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section survival.
Context {R : realType} (n k : nat).
Local Notation asg := {ffun 'I_n -> bool}.
Local Notation C := (clause n k).

(* The mean over M-tuples of clauses is the uniform mean of finite_mean.v. *)
Lemma sat_meanE M (F : M.-tuple C -> R) : sat_mean F = unif_mean F.
Proof. by []. Qed.

(* P_n(m) is the probability that the full solution set survives m
   clauses. *)
Lemma sat_probE m : sat_prob R n k m = survival k m [set: asg].
Proof.
rewrite /sat_prob sat_meanE /survival /tuple_avg; apply: eq_unif_mean => t.
by rewrite prefix_satE take_oversize ?size_tuple.
Qed.

Lemma sat_prob_ge0 m : 0 <= sat_prob R n k m.
Proof. by rewrite sat_probE; exact: survival_ge0. Qed.

Lemma sat_prob_le1 m : sat_prob R n k m <= 1.
Proof.
rewrite /sat_prob sat_meanE; have [T0|T0] := posnP #|{: m.-tuple C}|.
  by rewrite /unif_mean T0 invr0 mul0r ler01.
by apply: unif_mean_le => // t; case: (prefix_sat t m).
Qed.

(* The empty formula is satisfiable. *)
Lemma sat_prob0 : sat_prob R n k 0 = 1.
Proof. by rewrite /sat_prob sat_meanE unif_mean_tuple0 prefix_sat0. Qed.

Hypothesis kn : (k <= n)%N.
Let C0 : (0 < #|{: C}|)%N. Proof. exact: card_clause_gt0. Qed.

(* One more clause can only remove solutions. *)
Lemma survival_antitone m (S : {set asg}) :
  survival k m.+1 S <= survival k m S :> R.
Proof.
rewrite /survival tuple_avgS /clause_avg.
rewrite -[X in _ <= X](unif_mean_cst (tuple_avg k m alive S) C0).
by apply: ler_unif_mean => c; apply: survival_mono; exact: add_clause_sub.
Qed.

Lemma sat_prob_le m m' : (m <= m')%N -> sat_prob R n k m' <= sat_prob R n k m.
Proof.
move=> mm; rewrite !sat_probE; elim: m' mm => [|m' IH].
  by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP[/eqP -> //|]; rewrite ltnS => mm.
exact: le_trans (survival_antitone _ _) (IH mm).
Qed.

(* The survival of S after m clauses is the probability that S is not empty
   and that its lifetime along M >= m clauses is at least m. *)
Lemma survival_tail m M (S : {set asg}) : (m <= M)%N ->
  unif_mean (fun t : M.-tuple C =>
    ((S != set0) && (m%:R <= life S t :> R))%:R : R) = survival k m S.
Proof.
elim: m M S => [|m IH] M S mM.
  rewrite /survival tuple_avg0 (eq_unif_mean (g := fun=> alive S)).
    by move=> t; rewrite life_ge0 andbT.
  by rewrite unif_mean_cst // card_tuple expn_gt0 C0.
case: M mM => // M mM.
rewrite unif_mean_tuple_cons /survival tuple_avgS /clause_avg.
apply: eq_unif_mean => c.
have := IH M (add_clause S c) mM; rewrite /survival => <-.
apply: eq_unif_mean => t /=.
case: (eqVneq (add_clause S c) set0) => [Sc0|Sc0].
  by rewrite Sc0 alive0 add0r life0 (lt_geF (ltr0Sn _ m)) andbF.
have S0 : S != set0.
  apply: contra_neq Sc0 => S0; apply/eqP; rewrite -subset0 -S0.
  exact: add_clause_sub.
by rewrite S0 /alive Sc0 /= -nat1r lerD2l.
Qed.

(* P_n(m) = P(V >= m), with V the longest satisfiable prefix of M >= m
   clauses. *)
Lemma sat_prob_tail m M : (m <= M)%N ->
  sat_prob R n k m =
  sat_mean (fun t : M.-tuple C => (m <= sat_prefix_len t)%N%:R).
Proof.
move=> mM; rewrite sat_probE -(survival_tail [set: asg] mM) sat_meanE.
apply: eq_unif_mean => t.
have -> : [set: asg] != set0 by apply/set0Pn; exists [ffun=> true].
by rewrite -sat_prefix_lenE ler_nat.
Qed.

End survival.
