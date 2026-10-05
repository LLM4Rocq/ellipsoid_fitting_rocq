(* The subcritical conditioned limit from spectral bounds on the features.

   paper_main_event_from_vanishing_exception: if, eventually, every sample
   outside a measurable event E d lies in a measurable event F d, and
   P(E d) -> 0, then P(F d) -> 1.
   paper_main_subcritical_spectral_reduction: for 0 <= alpha < 1/4 there is
   kappa >= 1 with the following property, for every L >= 0, c > 0 and
   N(d) <= alpha d^2 eventually. If, outside measurable events B d with
   P(B d) -> 0, the head Gram matrix is eventually coercive with constant
   c d and the head section operator is bounded by L sqrt(d), then the
   conditioned event with lm = ((kappa+1/2)/(1-1/2))^-1 and
   lp = (kappa+1/2)/(1-1/2) has probability tending to 1. It combines
   these bounds with the exceptional events of
   paper_main_head_subcritical_fit_exception.
   paper_main_subcritical_raw_spectral_reduction: the same with the
   hypotheses stated on the raw feature Gram matrix: coercive with constant
   c d^2 and bounded above by C d^2 I, for C >= 0. The spectral bounds are
   hypotheses of both theorems. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainAsymptotics
  PaperMainFixedDensity PaperMainBalancedProbability PaperMainBalancedSupercritical
  PaperMainMeasurabilityConditioned PaperMainGeometryPsd PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadFeature PaperMainHeadSectionApprox
  PaperMainHeadRegularProbability PaperMainFeatureGramBlocks PaperMainFeatureSpectralBridge
  PaperMainHeadSubcriticalFit.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_event_from_vanishing_exception (N : nat -> nat)
    (F E : forall d, set (paper_main_sample (N d) d)) :
  (forall d, measurable (F d)) -> (forall d, measurable (E d)) ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 ->
  (exists D, forall d, Nat.le D d -> forall x, ~ E d x -> F d x) ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d (F d)) 1.
Proof.
move=> mF mE HE [D HD].
apply: (paper_main_tends_to_one_squeeze_eventually
  (fun d => (1-paper_main_probability (N d) d (E d))%E) _ D).
- move=> d Hd; rewrite -(paper_main_probability_complement (N d) d (E d) (mE d)).
  apply: paper_main_probability_mono.
  + apply: measurableC; exact: mE.
  + exact: mF.
  +
  move=> x Hx; exact: HD d (elimT ssrnat.leP Hd) x Hx.
- move=> d; have /andP [_ HH] := paper_main_probability_bounds (N d) d (F d) (mF d).
  exact HH.
- exact: paper_main_tends_to_complement_one.
Qed.

Theorem paper_main_subcritical_spectral_reduction alpha :
  0 <= alpha -> alpha < 1/4 ->
  exists kappa, 1 <= kappa /\ forall L c, 0 <= L -> 0 < c -> forall N : nat -> nat,
    (exists DN, forall d, Nat.le DN d -> INR (N d) <= alpha*(INR d)^2) ->
    forall B : forall d, set (paper_main_sample (N d) d),
      (forall d, measurable (B d)) ->
      paper_main_tends_to (fun d => paper_main_probability (N d) d (B d)) 0 ->
      (exists D, forall n, Nat.le D n -> forall x, ~ B (S n) x ->
        paper_main_head_coercive
          (paper_main_head_gram (fun i : 'I_(N (S n)) => paper_main_head_feature x i))
          (c*INR (S n)) /\
        paper_main_head_section_operator_bound (N (S n)) (fun i => paper_main_head_feature x i)
          (L*sqrt(INR (S n)))) ->
      paper_main_tends_to (fun d => paper_main_probability (N d) d
        (paper_main_conditioned_event (N d) d
          (((kappa+1/2)/(1-1/2))^-1)%R (((kappa+1/2)/(1-1/2)))%R)) 1.
Proof.
move=> Ha Hab.
have [kappa [Hk HK]] := paper_main_head_subcritical_fit_exception alpha Ha Hab.
exists kappa; split; first exact Hk.
move=> L c HL Hc N HN B mB HB [DB HDB].
have [A [mA [HA [DA HDA]]]] := HK L c HL Hc N HN.
apply: (paper_main_event_from_vanishing_exception N _ (fun d => A d `|` B d)).
- move=> d; exact: pm_conditioned_event_measurable.
- move=> d; apply: measurableU; [exact: mA|exact: mB].
- exact: paper_main_head_exception_union_limit N A B mA mB HA HB.
- exists (S (Nat.max DA DB)) => d Hd.
  case: d Hd => [|n] Hd; first lia.
  move=> x Hx.
  have Hna : ~ A (S n) x by move=> H; apply Hx; left.
  have Hnb : ~ B (S n) x by move=> H; apply Hx; right.
  have [HG Hop] := HDB n ltac:(lia) x Hnb.
  exact: HDA n ltac:(lia) x Hna HG Hop.
Qed.

Corollary paper_main_subcritical_raw_spectral_reduction alpha :
  0 <= alpha -> alpha < 1/4 ->
  exists kappa, 1 <= kappa /\ forall C c, 0 <= C -> 0 < c -> forall N : nat -> nat,
    (exists DN, forall d, Nat.le DN d -> INR (N d) <= alpha*(INR d)^2) ->
    forall B : forall d, set (paper_main_sample (N d) d),
      (forall d, measurable (B d)) ->
      paper_main_tends_to (fun d => paper_main_probability (N d) d (B d)) 0 ->
      (exists D, forall n, Nat.le D n -> forall x, ~ B (S n) x ->
        paper_main_head_coercive (paper_main_feature_gram (N (S n)) (S n) x)
          (c*(S n)%:R^+2)%R /\
        paper_main_loewner_le (paper_main_feature_gram (N (S n)) (S n) x)
          (((C*(S n)%:R^+2) *: 1%:M)%R)) ->
      paper_main_tends_to (fun d => paper_main_probability (N d) d
        (paper_main_conditioned_event (N d) d
          (((kappa+1/2)/(1-1/2))^-1)%R (((kappa+1/2)/(1-1/2)))%R)) 1.
Proof.
move=> Ha Hab.
have [kappa [Hk HK]] := paper_main_subcritical_spectral_reduction alpha Ha Hab.
exists kappa; split; first exact Hk.
move=> C c HC Hc N HN B mB HB [D HD].
apply: (HK (sqrt C) c (sqrt_pos C) Hc N HN B mB HB _).
exists D => n Hn x Hx.
have [HG HU] := HD n Hn x Hx; split.
- have HH := paper_main_raw_feature_coercive (N (S n)) (S n) x c (ltn0Sn n) HG.
  by rewrite -INRE in HH.
- exact: paper_main_raw_feature_operator (N (S n)) (S n) x C (ltn0Sn n) HC HU.
Qed.
