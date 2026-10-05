(* The fixed-density conditioned limit from a lower coercivity bound.

   The lower spectral bound is a hypothesis: measurable events E d with
   P(E d) -> 0, outside which, eventually, the raw feature Gram matrix of
   the sample of N d = floor(beta d^2) points is coercive with constant
   d^2/128.
   - paper_main_conditioned_from_lower: for 0 < beta < 1/4 and such E, the
     conditioned event with lm = ((kappa+1/2)/(1-1/2))^-1 and
     lp = (kappa+1/2)/(1-1/2) has probability tending to 1, for the
     kappa >= 1 of paper_main_subcritical_raw_spectral_reduction; and
     0 < lm <= lp (pmcfls_bounds of PaperMainConditionedFromLowerScalars).
     The upper bound raw Gram <= 109 d^2 I holds outside the vanishing
     event of paper_main_feature_upper_edge; the counts satisfy
     N d <= beta d^2 and, eventually, 0 < N d <= d^2 and
     density >= beta/2 (PaperMainFixedCountBounds); the exceptional set is
     the union of E with the upper event.
   - paper_main_conditioned_from_lower_exists: the same with lm and lp
     existential. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions
  PaperMainAsymptotics PaperMainFixedDensity PaperMainFixedCountBounds
  PaperMainGeometryHeadCoefficients PaperMainFeatureGramBlocks PaperMainHeadRegularProbability
  PaperMainFeatureUpperProbability PaperMainSubcriticalSpectralReduction
  PaperMainConditionedFromLowerScalars.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.

Theorem paper_main_conditioned_from_lower (beta : R)
    (E : forall d, set (paper_main_sample (paper_main_fixed_count beta d) d)) :
  (0 < beta)%Rcoq -> (beta < 1/4)%Rcoq ->
  (forall d, measurable (E d)) ->
  paper_main_tends_to (fun d => paper_main_probability (paper_main_fixed_count beta d) d (E d)) 0 ->
  (exists D, forall d, Nat.le D d -> forall x, ~ E d x ->
    paper_main_head_coercive (paper_main_feature_gram (paper_main_fixed_count beta d) d x)
      ((1/128) * d%:R ^+ 2)%R) ->
  exists kappa, (1 <= kappa)%Rcoq /\
    (0 < ((kappa+1/2)/(1-1/2))^-1)%R /\
    (((kappa+1/2)/(1-1/2))^-1 <= (kappa+1/2)/(1-1/2))%R /\
    paper_main_tends_to (fun d => paper_main_probability (paper_main_fixed_count beta d) d
      (paper_main_conditioned_event (paper_main_fixed_count beta d) d
        (((kappa+1/2)/(1-1/2))^-1)%R (((kappa+1/2)/(1-1/2)))%R)) 1.
Proof.
move=> Hb0 Hb1 mE HE [DE HDE].
set N := paper_main_fixed_count beta.
have Hb0' : (0 <= beta)%Rcoq by exact: Rlt_le.
have Hb1' : (beta <= 1)%Rcoq by Stdlib.micromega.Lra.lra.
have [kappa [Hk HK]] := paper_main_subcritical_raw_spectral_reduction beta Hb0' Hb1.
have [Hlm Hlp] := pmcfls_bounds kappa Hk.
exists kappa; split; first exact: Hk.
split; first exact: Hlm.
split; first exact: Hlp.
(* The counts: N d <= beta d^2, and eventually 0 < N d <= d^2. *)
have [DN HDN] := paper_main_fixed_count_density_bounds beta Hb0 Hb1'.
have Hlow := paper_main_fixed_count_eventually_lower beta Hb0 Hb1'.
have Hup : exists D, forall d, (D <= d)%N -> (0 < N d)%N /\ (N d <= d ^ 2)%N.
  exists DN => d Hd.
  by have [_ [H1 [H2 _]]] := HDN d (elimT ssrnat.leP Hd).
have HNa : exists D, forall d, Nat.le D d -> (INR (N d) <= beta * (INR d) ^ 2)%Rcoq.
  by exists 0%N => d _; have [_ H] := paper_main_fixed_count_error beta d Hb0'.
(* The upper event of the raw feature Gram matrix. *)
have Hc' : (0 < beta / 2)%Rcoq by Stdlib.micromega.Lra.lra.
have Hc : (0 < (beta / 2)%Rcoq)%R by apply/RltP.
have [U [mU [HU HUb]]] := paper_main_feature_upper_edge N (beta / 2)%Rcoq Hc Hlow Hup.
apply: (HK 109%:R (1/128)%R _ _ N HNa (fun d => E d `|` U d)).
- by apply/RleP; exact: ler0n.
- by apply/RltP; apply: divr_gt0; [exact: ltr01 | rewrite ltr0n].
- by move=> d; apply: measurableU; [exact: mE | exact: mU].
- exact: (paper_main_head_exception_union_limit N E U mE mU HE HU).
- exists (Nat.max DE DN) => n Hn x Hx.
  have HnE : ~ E n.+1 x by move=> H; apply: Hx; left.
  have HnU : ~ U n.+1 x by move=> H; apply: Hx; right.
  have [_ [_ [HNn _]]] := HDN n.+1 ltac:(lia).
  split; first exact: (HDE n.+1 ltac:(lia) x HnE).
  exact: (HUb n.+1 x (ltn0Sn n) HNn HnU).
Qed.

Corollary paper_main_conditioned_from_lower_exists (beta : R)
    (E : forall d, set (paper_main_sample (paper_main_fixed_count beta d) d)) :
  (0 < beta)%Rcoq -> (beta < 1/4)%Rcoq ->
  (forall d, measurable (E d)) ->
  paper_main_tends_to (fun d => paper_main_probability (paper_main_fixed_count beta d) d (E d)) 0 ->
  (exists D, forall d, Nat.le D d -> forall x, ~ E d x ->
    paper_main_head_coercive (paper_main_feature_gram (paper_main_fixed_count beta d) d x)
      ((1/128) * d%:R ^+ 2)%R) ->
  exists lm lp : R, (0 < lm)%R /\ (lm <= lp)%R /\
    paper_main_tends_to (fun d => paper_main_probability (paper_main_fixed_count beta d) d
      (paper_main_conditioned_event (paper_main_fixed_count beta d) d lm lp)) 1.
Proof.
move=> Hb0 Hb1 mE HE HC.
have [kappa [_ [Hlm [Hlp H]]]] := paper_main_conditioned_from_lower beta E Hb0 Hb1 mE HE HC.
by exists (((kappa+1/2)/(1-1/2))^-1)%R, ((kappa+1/2)/(1-1/2))%R.
Qed.
