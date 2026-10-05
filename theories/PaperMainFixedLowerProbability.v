(* The actual lower spectral law at the fixed subcritical count (A41).

   1. Bridge: the MathComp hypotheses 0 < beta and beta < 1 / 4%:R of the
      final statements give the Stdlib pair (0 < beta)%Rcoq and
      (beta < 1/4)%Rcoq used by the count lemmas.
   2. Endpoint: for 0 < beta < 1/4 and N = paper_main_fixed_count beta there
      are actual measurable events E_d with probability tending to 0 such
      that for all large d (Stdlib Nat.le threshold) every sample outside
      E_d has raw-feature coercivity with constant d^2 / 128. These are the
      three event premises of paper_main_conditioned_from_lower_exists.
      Route: paper_main_fixed_subcritical_counts and
      paper_main_fixed_subcritical_density (c = beta / 2), then the A40
      law paper_main_squarefree_lower_probability. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainFixedDensity PaperMainGeometryHeadCoefficients PaperMainFeatureGramBlocks
  PaperMainFixedSubcriticalCounts PaperMainSquarefreeLowerProbability.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. The beta hypotheses in Stdlib form. *)
Lemma paper_main_fixed_beta_coq (beta : R) :
  0 < beta -> beta < 1 / 4%:R -> (0 < beta)%Rcoq /\ (beta < 1/4)%Rcoq.
Proof.
move=> Hb0 Hb1; split; first by apply/RltP.
by move/RltP: Hb1; rewrite -RdivE -INRE INR_IZR_INZ.
Qed.

(* 2. The fixed-beta endpoint. *)
Theorem paper_main_fixed_lower_probability (beta : R) :
  0 < beta -> beta < 1 / 4%:R ->
  exists E : forall d, set (paper_main_sample (paper_main_fixed_count beta d) d),
    (forall d, measurable (E d)) /\
    paper_main_tends_to (fun d => paper_main_probability (paper_main_fixed_count beta d) d (E d)) 0 /\
    exists D, forall d, Nat.le D d -> forall x, ~ E d x ->
      paper_main_head_coercive (paper_main_feature_gram (paper_main_fixed_count beta d) d x)
        ((1/128) * d%:R ^+ 2)%R.
Proof.
move=> Hb0 Hb1.
have [Hb0' Hb1'] := paper_main_fixed_beta_coq beta Hb0 Hb1.
have [c1 [D HD]] := paper_main_fixed_subcritical_counts beta Hb0' Hb1'.
have Hdens := paper_main_fixed_subcritical_density beta Hb0' Hb1'.
have Hc : 0 < (beta / 2)%Rcoq by apply/RltP; apply: Rdiv_lt_0_compat => //; Stdlib.micromega.Lra.lra.
have [E [mE [lE [D' HD']]]] :=
  paper_main_squarefree_lower_probability (paper_main_fixed_count beta) (beta / 2)%Rcoq c1 Hc Hdens
    (ex_intro _ D HD).
exists E; split => //; split => //.
exists D' => d /ssrnat.leP Hd x Hx.
exact: HD' d Hd x Hx.
Qed.
