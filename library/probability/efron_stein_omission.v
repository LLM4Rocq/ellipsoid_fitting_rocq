From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg efron_stein.

(**md**************************************************************************)
(* # The omission form of the Efron-Stein inequality                          *)
(*                                                                            *)
(* Let x have law tuple_prod mu n (lindeberg.v): its coordinates are          *)
(* independent, of laws mu 0, ..., mu (n - 1). Let F be an integrable real    *)
(* function of x, and for each i let G i be a measurable function of x that   *)
(* does not depend on the coordinate i: G i (tuple_set x i t) = G i x for all *)
(* x and t. Then Var F <= \sum_i E (G i - F)^2 (efron_stein_omission), with   *)
(* the variance and the expectations in [0, +oo] as in efron_stein.v. For a   *)
(* statistic F of independent data, G i is typically the same statistic       *)
(* computed without the datum i; this is the form of Steele, written by       *)
(* Boucheron, Bousquet, Lugosi and Massart (Concentration inequalities,       *)
(* Section 3.2, equation (3.6)). efron_stein_omission_bounded is the case of  *)
(* a bounded measurable F.                                                    *)
(*                                                                            *)
(* The proof bounds the variance in the coordinate i, the others being fixed, *)
(* by the second moment about the value G i x, which does not depend on that  *)
(* coordinate (variance_le_sqr_dev). The Efron-Stein inequality               *)
(* (efron_stein_integrable) sums these bounds, and Fubini at one coordinate   *)
(* (ge0_integral_tuple_prod_set) integrates the coordinate i back.            *)
(*                                                                            *)
(* This file is a Rocq formalization, in general form, of the lemma 'Deletion *)
(* variance bound' of 'A limiting satisfiability threshold for every fixed    *)
(* clause size' (family 235 of the OpenAI math collection, revision           *)
(* 1581d4cbd, source/sections/concentration.tex), where F is the last         *)
(* satisfiable prefix length V of a random formula, capped, and G i is        *)
(* V^(-i), the same length with the clause i omitted. The manuscript proves   *)
(* the lemma with the martingale differences of the clauses revealed one at a *)
(* time; the proof here goes through the Efron-Stein inequality instead. The  *)
(* Lean development of the collection (lean/OAI/Probability/RandomSAT) bounds *)
(* the variance of its statistic by a recursion over the clauses, and this    *)
(* file follows no Lean module.                                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section omission.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* The omission form of the Efron-Stein inequality: for F integrable and
   G i measurable and independent of the coordinate i,
   Var F <= \sum_i E (G i - F)^2. *)
Theorem efron_stein_omission (mu : nat -> probability T R) n
    (F : n.-tuple T -> R) (G : 'I_n -> n.-tuple T -> R) :
  (tuple_prod mu n).-integrable setT (EFin \o F) ->
  (forall i, measurable_fun setT (G i)) ->
  (forall i x t, G i (tuple_set x i t) = G i x) ->
  'V_(tuple_prod mu n)[F] <=
    \sum_(i < n) \int[tuple_prod mu n]_x ((G i x - F x) ^+ 2)%:E.
Proof.
move=> iF mG GiE.
have mF : measurable_fun setT F.
  by apply/measurable_EFinP; exact: measurable_int iF.
apply: le_trans (efron_stein_integrable iF) _.
apply: lee_sum => i _.
have mH : measurable_fun setT (fun x => ((G i x - F x) ^+ 2)%:E).
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_funB.
have H0 x : 0 <= ((G i x - F x) ^+ 2)%:E by rewrite lee_fin sqr_ge0.
rewrite (ge0_integral_tuple_prod_set mu i mH H0).
apply: ge0_le_integral => //.
- by move=> x _; exact: variance_ge0.
- exact: measurable_variance_tuple_set.
- exact: (measurable_tuple_set_integral mu i mH H0).
move=> x _.
have mFx : measurable_fun setT (fun t => F (tuple_set x i t)).
  exact: measurableT_comp mF (measurable_tuple_set x i).
apply: le_trans (variance_le_sqr_dev (mu i) (G i x) mFx) _.
rewrite le_eqVlt; apply/orP; left; apply/eqP; apply: eq_integral => t _.
by rewrite GiE -opprB sqrrN.
Qed.

(* The same for a bounded measurable F. *)
Corollary efron_stein_omission_bounded (mu : nat -> probability T R) n
    (F : n.-tuple T -> R) (G : 'I_n -> n.-tuple T -> R) (C : R) :
  measurable_fun setT F -> (forall x, `|F x| <= C)%R ->
  (forall i, measurable_fun setT (G i)) ->
  (forall i x t, G i (tuple_set x i t) = G i x) ->
  'V_(tuple_prod mu n)[F] <=
    \sum_(i < n) \int[tuple_prod mu n]_x ((G i x - F x) ^+ 2)%:E.
Proof.
move=> mF FC mG GiE.
have iF : (tuple_prod mu n).-integrable setT (EFin \o F).
  have iC := finite_measure_integrable_cst (tuple_prod mu n) C
    (@measurableT _ (n.-tuple T)).
  apply: (le_integrable measurableT _ _ iC); first exact/measurable_EFinP.
  by move=> x _; rewrite /comp lee_fin (le_trans (FC x)) // ler_norm.
exact: (efron_stein_omission iF mG GiE).
Qed.

End omission.
