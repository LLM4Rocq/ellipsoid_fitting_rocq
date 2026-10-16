(* Symmetric mixture samples above the PSD threshold. A single positive
   margin is fixed from the density and averaged fourth moment before
   the component laws or sample-size sequence are chosen. Outside Borel
   exceptional covers, the lower error bound holds for every translation
   and all nonzero PSD quadrics are excluded. We do not assert that the
   existential quadric-fitting event itself is Borel.
   Source: doc/shifted-gaussian.tex, the symmetric reserve certificate. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean psd_part quadric_certificate.
From GaussianAnalysis.probability Require Import symmetric_shift independent_row_signs.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions CountableMixtureDefinitions.
From EllipsoidUniversality.Gaussian Require Import InProbability Threshold.
From EllipsoidUniversality.Shifted Require Import MainMoment MixtureRows ResidualLaws.
From EllipsoidUniversality.Shifted Require Import ConditionTranslation TranslationError.
From EllipsoidUniversality.Shifted Require Import ReserveModel ReserveLimit ReserveApplications ErrorCurve SampleSplit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition symmetric_quadric_beta (kappa alpha : RR) : RR :=
  (alpha+universality_alpha_star kappa)/2%:R.
Definition symmetric_quadric_margin (kappa alpha : RR) : RR :=
  (symmetric_quadric_beta kappa alpha/alpha)*
    universality_e_star (symmetric_quadric_beta kappa alpha) kappa/2%:R.

Lemma symmetric_quadric_beta_spec (kappa alpha : R) :
  1 < kappa -> universality_alpha_star kappa < alpha ->
  0 < symmetric_quadric_beta kappa alpha /\
  universality_alpha_star kappa < symmetric_quadric_beta kappa alpha /\
  symmetric_quadric_beta kappa alpha < alpha.
Proof.
move=> k1 aa.
have a0 := universality_alpha_star_gt0 kappa k1.
have alpha0 := lt_trans a0 aa.
rewrite /symmetric_quadric_beta ?RdivE ?RplusE; split.
- by rewrite divr_gt0 // addr_gt0.
- split.
  + rewrite ltr_pdivlMr //; nra.
  + rewrite ltr_pdivrMr //; nra.
Qed.

Lemma symmetric_quadric_energy_gt0 (kappa alpha : R) :
  1 < kappa -> universality_alpha_star kappa < alpha ->
  0 < universality_e_star (symmetric_quadric_beta kappa alpha) kappa.
Proof.
move=> k1 aa; have [b0 [ab ba]] := symmetric_quadric_beta_spec k1 aa.
by rewrite universality_e_star_gt0.
Qed.

Lemma symmetric_quadric_margin_gt0 (kappa alpha : R) :
  1 < kappa -> universality_alpha_star kappa < alpha ->
  0 < symmetric_quadric_margin kappa alpha.
Proof.
move=> k1 aa; have [b0 [ab ba]] := symmetric_quadric_beta_spec k1 aa.
have a0 := lt_trans b0 ba.
have e0 := symmetric_quadric_energy_gt0 k1 aa.
by rewrite /symmetric_quadric_margin ?RdivE ?RmultE divr_gt0 // mulr_gt0 // divr_gt0.
Qed.

Lemma symmetric_quadric_margin_lt (kappa alpha : R) :
  1 < kappa -> universality_alpha_star kappa < alpha ->
  symmetric_quadric_margin kappa alpha <
    (symmetric_quadric_beta kappa alpha/alpha)*
      universality_e_star (symmetric_quadric_beta kappa alpha) kappa.
Proof.
move=> k1 aa.
have pos := symmetric_quadric_margin_gt0 k1 aa.
rewrite /symmetric_quadric_margin ?RdivE ?RmultE in pos *; lra.
Qed.

Definition symmetric_quadric_good n d (eta : R) (x : paper_main_sample n d) : Prop :=
  eta <= translation_fitting_error n d x /\
  forall (Q : 'M[RR]_d) (v : 'cV[RR]_d) (c : R),
    psdmx Q -> Q != 0 ->
    ~ (forall i : 'I_n, quadric_eval Q v c (paper_main_point x i) = 0).

Section matrix_cover.
Variables N k : nat -> nat.
Variable P : forall d, probability 'M[RR]_(N d+k d,d) RR.
Variables beta gamma e eta : R.
Hypotheses (beta0 : 0 < beta) (gamma0 : 0 < gamma) (ep : 0 < e).
Hypotheses (hN : universality_density_tends_to N beta)
  (hk : universality_density_tends_to k gamma).
Hypothesis bad_probability : forall eps delta : R,
  0 < eps -> 0 < delta -> exists D : nat, forall d, (D <= d)%N ->
    (P d (@reserve_model_bad (N d) (k d) d delta) <= eps%:E)%E.
Hypothesis main_error_limit : cvg_prob P
  (fun d H => universality_fitting_error (N d) d (matrix_sample (usubmx H))) e.
Hypothesis etaL : eta < beta/(beta+gamma)*e.

Lemma symmetric_quadric_matrix_bad_negligible :
  negligible P (fun d => [set H |
    ~ symmetric_quadric_good eta (matrix_sample H)]).
Proof.
have hlow := @reserve_matrix_translation_lower_tail N k P beta gamma e
  beta0 gamma0 (ltW ep) hN hk bad_probability main_error_limit eta etaL.
have hquad := @reserve_matrix_quadric_bad_negligible N k P beta gamma e
  beta0 gamma0 (ltW ep) hN hk bad_probability main_error_limit ep.
apply: negligibleW (negligibleU hlow hquad) _.
exists 0%N=>d _ H /= hbad.
have [small|large] := leP (translation_fitting_error (N d+k d) d (matrix_sample H)) eta.
  by left.
right.
have [yes|no] := pselect (exists (Q : 'M[RR]_d) (v : 'cV[RR]_d) (c : R),
  psdmx Q /\ Q != 0 /\ forall i : 'I_(N d+k d),
  quadric_eval Q v c (paper_main_point (matrix_sample H) i) = 0).
  exact: yes.
exfalso; apply: hbad; split; first exact: ltW large.
move=> Q v c Qpsd Qnz fit; apply: no.
by exists Q,v,c.
Qed.

End matrix_cover.

Lemma symmetric_quadric_sample_cover n d (P : probability 'M[RR]_(n,d) RR)
    (pi : set (paper_main_sample n d) -> \bar R) (eta eps : R)
    (A : set 'M[RR]_(n,d)) :
  (forall E, measurable E -> P ((@matrix_sample n d) @^-1` E) = pi E) ->
  measurable A -> (P A <= eps%:E)%E ->
  [set H | ~ symmetric_quadric_good eta (matrix_sample H)] `<=` A ->
  exists E : set (paper_main_sample n d),
    [/\ measurable E, (pi E <= eps%:E)%E &
      forall x, ~ E x -> symmetric_quadric_good eta x].
Proof.
move=> law mA PA cover.
pose E := (@sample_point_matrix n d) @^-1` A.
have mE : measurable E.
  by rewrite -[X in measurable X]setTI; exact: measurable_sample_point_matrix.
exists E; split=> //.
- rewrite -(law E mE).
  have -> : (@matrix_sample n d) @^-1` E = A.
    by apply/funext=>H; rewrite /E /= matrix_sample_matrixK.
  exact: PA.
- move=> x nx.
  have [good|bad] := pselect (symmetric_quadric_good eta x); first exact: good.
  exfalso; apply: nx; apply: cover.
  by rewrite /= sample_matrix_sampleK.
Qed.

Theorem finite_symmetric_quadric (kappa alpha K : R)
    (components : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : mixture_family K components w mu) :
  1 < kappa -> universality_alpha_star kappa < alpha -> 0 < K ->
  (forall d, row_symmetric_law (finite_row_law hfam d)) ->
  mixture_fourth_moment kappa components w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d),
    [/\ measurable E,
      (mixture_probability (components d) (w d) (mu d) (n d) d E <= eps%:E)%E &
      forall x, ~ E x -> symmetric_quadric_good (symmetric_quadric_margin kappa alpha) x].
Proof.
move=> k1 aa K0 symmetric fourth n hn eps eps0.
pose beta := symmetric_quadric_beta kappa alpha.
have [beta0 [ab ba]] := symmetric_quadric_beta_spec k1 aa.
have ep := symmetric_quadric_energy_gt0 k1 aa.
have gamma0 : 0 < alpha-beta by rewrite subr_gt0.
have [N [k [hnk [hN hk]]]] := @sample_split_density n alpha beta beta0 ba hn.
have en : n = (fun d => N d+k d)%N by apply/funext=>d; exact: esym (hnk d).
rewrite en.
have hbad := @finite_reserve_model_converges K components w mu hfam N k beta
  (alpha-beta) K0 beta0 gamma0 symmetric hN hk.
have herr := @finite_main_matrix_error_cvg K components w mu hfam N k beta kappa
  k1 K0 beta0 fourth hN.
have etaL : symmetric_quadric_margin kappa alpha <
    beta/(beta+(alpha-beta))*universality_e_star beta kappa.
  have he : beta+(alpha-beta) = alpha by ring.
  rewrite he; exact: symmetric_quadric_margin_lt k1 aa.
have hmat := @symmetric_quadric_matrix_bad_negligible N k
  (fun d=>independent_row_matrix_law (fun=>finite_row_law hfam d) (N d+k d))
  beta (alpha-beta) (universality_e_star beta kappa)
  (symmetric_quadric_margin kappa alpha) beta0 gamma0 ep hN hk hbad herr etaL.
have [D hD] := hmat eps eps0.
exists D=>d dD; have [A [mA PA cover]] := hD d dD.
exact: symmetric_quadric_sample_cover
  (@finite_matrix_sample_law K components w mu hfam (N d+k d) d) mA PA cover.
Qed.

Theorem countable_symmetric_quadric (kappa alpha K : R)
    (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : countable_mixture_family K w mu) :
  1 < kappa -> universality_alpha_star kappa < alpha -> 0 < K ->
  (forall d, row_symmetric_law (countable_row_law hfam d)) ->
  countable_fourth_moment kappa w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d),
    [/\ measurable E,
      (countable_mixture_probability (w d) (mu d) (n d) d E <= eps%:E)%E &
      forall x, ~ E x -> symmetric_quadric_good (symmetric_quadric_margin kappa alpha) x].
Proof.
move=> k1 aa K0 symmetric fourth n hn eps eps0.
pose beta := symmetric_quadric_beta kappa alpha.
have [beta0 [ab ba]] := symmetric_quadric_beta_spec k1 aa.
have ep := symmetric_quadric_energy_gt0 k1 aa.
have gamma0 : 0 < alpha-beta by rewrite subr_gt0.
have [N [k [hnk [hN hk]]]] := @sample_split_density n alpha beta beta0 ba hn.
have en : n = (fun d => N d+k d)%N by apply/funext=>d; exact: esym (hnk d).
rewrite en.
have hbad := @countable_reserve_model_converges K w mu hfam N k beta
  (alpha-beta) K0 beta0 gamma0 symmetric hN hk.
have herr := @countable_main_matrix_error_cvg K w mu hfam N k beta kappa
  k1 K0 beta0 fourth hN.
have etaL : symmetric_quadric_margin kappa alpha <
    beta/(beta+(alpha-beta))*universality_e_star beta kappa.
  have he : beta+(alpha-beta) = alpha by ring.
  rewrite he; exact: symmetric_quadric_margin_lt k1 aa.
have hmat := @symmetric_quadric_matrix_bad_negligible N k
  (fun d=>independent_row_matrix_law (fun=>countable_row_law hfam d) (N d+k d))
  beta (alpha-beta) (universality_e_star beta kappa)
  (symmetric_quadric_margin kappa alpha) beta0 gamma0 ep hN hk hbad herr etaL.
have [D hD] := hmat eps eps0.
exists D=>d dD; have [A [mA PA cover]] := hD d dD.
exact: symmetric_quadric_sample_cover
  (@countable_matrix_sample_law K w mu hfam (N d+k d) d) mA PA cover.
Qed.
