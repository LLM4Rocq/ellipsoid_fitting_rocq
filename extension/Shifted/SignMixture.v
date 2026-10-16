(* Exact sign-mixture transfer for centered quadratic fitting observables.
   The base point law is centrally symmetric; its coordinates may depend.
   Independent samples from any mixture of its +m and -m translations
   give the same Fit(C) probabilities and the same laws of the optimal
   condition number and frozen fitting error as the single shift +m.
   Weights 0 and 1 are included. No statement here transfers arbitrary
   linear terms or an infimum over further translations. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import gauss measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows mixture symmetrization.
From GaussianAnalysis.probability Require Import symmetric_shift independent_row_signs sign_shift_sample.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidFitting.Measurability Require Import Fit.
From EllipsoidUniversality Require Import UniversalityDefinitions ConditionDefinitions.
From EllipsoidUniversality.Gaussian Require Import Limit InProbability Threshold.
From EllipsoidUniversality.Unsat Require Import FourthMomentThree.
From mathcomp Require Import arithmetic_tactic.
From EllipsoidUniversality.Model Require Import Measurability.
Require Import EllipsoidUniversality.Condition.Theorem.
From EllipsoidUniversality.Shifted Require Import GaussianRows Translations
  GaussianExistence GaussianCondition GaussianError GaussianBounds.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition row_sample_map n d :
    {mfun n.-tuple 'rV[RR]_d >-> paper_main_sample n d} :=
  HB.pack (@sample_of_row_tuple n d)
    (isMeasurableFun.Build _ _ _ _ _ (@measurable_sample_of_row_tuple n d)).

Definition iid_row_sample_law d (P : probability 'rV[RR]_d RR) n :
    probability (paper_main_sample n d) RR :=
  distribution (tuple_prod (fun=>P) n) (row_sample_map n d).

Definition shifted_iid_sample_law d (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) n := iid_row_sample_law (row_shift_law P m^T) n.

Definition sign_mixture_sample_law d (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) w (hw : 0 <= w <= 1) n :=
  iid_row_sample_law (sign_shift_law P m^T hw) n.

Lemma iid_row_sample_lawE d (P : probability 'rV[RR]_d RR) n A :
  iid_row_sample_law P n A =
    tuple_prod (fun=>P) n (@sample_of_row_tuple n d @^-1` A).
Proof. by []. Qed.

Definition sample_row_sign n d (s : n.-tuple bool) (x : paper_main_sample n d) :=
  sample_of_row_tuple (tuple_row_sign s (sample_row_tuple x)).

Lemma sample_of_rows_point n d (x : n.-tuple 'rV[RR]_d) (i : 'I_n) :
  paper_main_point (sample_of_row_tuple x) i = (tnth x i)^T.
Proof.
have h := congr1 (fun z : n.-tuple 'rV[RR]_d => tnth z i)
  (sample_of_row_tupleK x).
rewrite /sample_row_tuple tnth_mktuple in h.
by move: (congr1 trmx h); rewrite trmxK.
Qed.

Lemma sample_row_sign_point n d (s : n.-tuple bool)
    (x : paper_main_sample n d) (i : 'I_n) :
  paper_main_point (sample_row_sign s x) i =
    rademacher (nth true s i) *: paper_main_point x i.
Proof.
rewrite /sample_row_sign sample_of_rows_point /tuple_row_sign /tuple_map tnth_mktuple.
by rewrite /sample_row_tuple tnth_mktuple linearZ /= trmxK.
Qed.

Lemma quadratic_rademacher d (S : 'M[R]_d) (v : 'cV[R]_d) (b : bool) :
  paper_main_quadratic_form S (rademacher b *: v) =
    paper_main_quadratic_form S v.
Proof.
case: b; rewrite /rademacher ?scale1r // scaleN1r !paper_quadratic_mxdot.
by rewrite mulmxN mxdotNl mxdotNr opprK.
Qed.

Lemma sample_row_sign_quadratic n d (s : n.-tuple bool)
    (x : paper_main_sample n d) (S : 'M[R]_d) (i : 'I_n) :
  paper_main_quadratic_form S (paper_main_point (sample_row_sign s x) i) =
    paper_main_quadratic_form S (paper_main_point x i).
Proof. by rewrite sample_row_sign_point quadratic_rademacher. Qed.

Lemma conditioned_fit_row_sign n d (s : n.-tuple bool)
    (x : paper_main_sample n d) (C : R) :
  universality_conditioned_fit_event n d C (sample_row_sign s x) =
    universality_conditioned_fit_event n d C x.
Proof.
apply/propext; split; move=> [S [l [l0 [hlo [hhi hfit]]]]];
  exists S, l; split => //; split => //; split => // i.
- by move: (hfit i); rewrite sample_row_sign_quadratic.
- by rewrite sample_row_sign_quadratic; exact: hfit.
Qed.

Lemma pd_fit_row_sign n d (s : n.-tuple bool) (x : paper_main_sample n d) :
  universality_pd_fit_event n d (sample_row_sign s x) =
    universality_pd_fit_event n d x.
Proof.
apply/propext; split; move=> [S [Sp hfit]]; exists S; split => // i.
- by move: (hfit i); rewrite sample_row_sign_quadratic.
- by rewrite sample_row_sign_quadratic; exact: hfit.
Qed.

Lemma psd_fit_row_sign n d (s : n.-tuple bool) (x : paper_main_sample n d) :
  paper_main_fit_event n d (sample_row_sign s x) = paper_main_fit_event n d x.
Proof.
apply/propext; split; move=> [S [Sp hfit]]; exists S; split => // i.
- by move: (hfit i); rewrite sample_row_sign_quadratic.
- by rewrite sample_row_sign_quadratic; exact: hfit.
Qed.

Lemma condition_number_row_sign n d (s : n.-tuple bool)
    (x : paper_main_sample n d) :
  data_condition_number n d (sample_row_sign s x) = data_condition_number n d x.
Proof.
rewrite /data_condition_number; congr (ereal_inf _).
congr (image _ _); apply/funext => C.
exact: conditioned_fit_row_sign.
Qed.

Lemma fitting_error_row_sign n d (s : n.-tuple bool)
    (x : paper_main_sample n d) :
  universality_fitting_error n d (sample_row_sign s x) =
    universality_fitting_error n d x.
Proof.
rewrite /universality_fitting_error; congr (inf _).
apply/funext => z; apply/propext; split;
  move=> [S [r [Sp [St [r0 hz]]]]]; exists S, r;
  split => //; split => //; split => //.
- move: hz; by under eq_bigr do rewrite sample_row_sign_quadratic.
- rewrite hz; symmetry; by under eq_bigr do rewrite sample_row_sign_quadratic.
Qed.

Lemma symmetric_sign_sample_event d (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) w (hw : 0 <= w <= 1) n (A : set (paper_main_sample n d)) :
  row_symmetric_law P -> measurable A ->
  (forall s x, A (sample_row_sign s x) = A x) ->
  sign_mixture_sample_law P m hw n A = shifted_iid_sample_law P m n A.
Proof.
move=> symP mA evenA; rewrite /sign_mixture_sample_law /shifted_iid_sample_law
  !iid_row_sample_lawE.
apply: symmetric_sign_shift_sample => //.
- by rewrite -[X in measurable X]setTI; exact: measurable_sample_of_row_tuple.
- move=> s x; rewrite /preimage /= -(evenA s (sample_of_row_tuple x)).
  by rewrite /sample_row_sign sample_of_row_tupleK.
Qed.

Theorem sign_mixture_conditioned_probability d (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) w (hw : 0 <= w <= 1) n (C : R) :
  row_symmetric_law P ->
  sign_mixture_sample_law P m hw n (universality_conditioned_fit_event n d C) =
    shifted_iid_sample_law P m n (universality_conditioned_fit_event n d C).
Proof.
move=> symP; apply: symmetric_sign_sample_event => //.
- exact: measurable_conditioned_fit_event.
- by move=> s x; exact: conditioned_fit_row_sign.
Qed.

Theorem sign_mixture_pd_probability d (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) w (hw : 0 <= w <= 1) n : row_symmetric_law P ->
  sign_mixture_sample_law P m hw n (universality_pd_fit_event n d) =
    shifted_iid_sample_law P m n (universality_pd_fit_event n d).
Proof.
move=> symP; apply: symmetric_sign_sample_event => //.
- exact: measurable_pd_fit_event.
- by move=> s x; exact: pd_fit_row_sign.
Qed.

Theorem sign_mixture_psd_probability d (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) w (hw : 0 <= w <= 1) n : row_symmetric_law P ->
  sign_mixture_sample_law P m hw n (paper_main_fit_event n d) =
    shifted_iid_sample_law P m n (paper_main_fit_event n d).
Proof.
move=> symP; apply: symmetric_sign_sample_event => //.
- exact: pm_fit_event_measurable.
- by move=> s x; exact: psd_fit_row_sign.
Qed.

Theorem sign_mixture_condition_number_law d (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) w (hw : 0 <= w <= 1) n (A : set (\bar R)) :
  row_symmetric_law P -> measurable A ->
  sign_mixture_sample_law P m hw n ((data_condition_number n d) @^-1` A) =
    shifted_iid_sample_law P m n ((data_condition_number n d) @^-1` A).
Proof.
move=> symP mA; apply: symmetric_sign_sample_event => //.
- by rewrite -[X in measurable X]setTI; exact: measurable_data_condition_number.
- by move=> s x; rewrite /preimage /= condition_number_row_sign.
Qed.

Theorem sign_mixture_fitting_error_law d (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) w (hw : 0 <= w <= 1) n (A : set RR) :
  row_symmetric_law P -> measurable A ->
  sign_mixture_sample_law P m hw n ((universality_fitting_error n d) @^-1` A) =
    shifted_iid_sample_law P m n ((universality_fitting_error n d) @^-1` A).
Proof.
move=> symP mA; apply: symmetric_sign_sample_event => //.
- by rewrite -[X in measurable X]setTI; exact: measurable_fitting_error.
- by move=> s x; rewrite /preimage /= fitting_error_row_sign.
Qed.

Lemma sample_of_rows_shift n d (m : 'cV[R]_d) (x : n.-tuple 'rV[RR]_d) :
  sample_of_row_tuple (tuple_row_shift m^T x) =
    sample_translate m (sample_of_row_tuple x).
Proof.
apply: (can_inj (@sample_row_tupleK n d)).
rewrite sample_of_row_tupleK; apply: eq_from_tnth => i.
rewrite /tuple_row_shift /tuple_map tnth_mktuple /sample_row_tuple tnth_mktuple
  sample_translate_point sample_of_rows_point.
by rewrite linearD /= trmxK.
Qed.

Lemma shifted_iid_sample_lawE d (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) n (A : set (paper_main_sample n d)) : measurable A ->
  shifted_iid_sample_law P m n A =
    iid_row_sample_law P n (sample_translate m @^-1` A).
Proof.
move=> mA.
have mB : measurable (@sample_of_row_tuple n d @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_sample_of_row_tuple.
rewrite /shifted_iid_sample_law !iid_row_sample_lawE
  (@tuple_row_shift_law RR d P m^T n _ mB).
congr (tuple_prod _ _ _); apply/funext => x /=.
by rewrite sample_of_rows_shift.
Qed.

Lemma gaussian_shifted_sample_law n d (m : 'cV[R]_d)
    (A : set (paper_main_sample n d)) : measurable A ->
  shifted_iid_sample_law (gauss d) m n A =
    gaussian_product_law (n*d) (sample_translate m @^-1` A).
Proof.
move=> mA; rewrite shifted_iid_sample_lawE // iid_row_sample_lawE
  gaussian_row_tuple_flat_law //.
by rewrite -[X in measurable X]setTI; exact: measurable_sample_translate.
Qed.

Lemma gaussian_sign_sample_event n d (m : 'cV[R]_d) w (hw : 0 <= w <= 1)
    (A : set (paper_main_sample n d)) :
  measurable A -> (forall s x, A (sample_row_sign s x) = A x) ->
  sign_mixture_sample_law (gauss d) m hw n A =
    gaussian_product_law (n*d) (sample_translate m @^-1` A).
Proof.
move=> mA evenA.
rewrite (@symmetric_sign_sample_event d (gauss d) m w hw n A
  gauss_row_symmetric mA evenA).
exact: gaussian_shifted_sample_law.
Qed.

Corollary gaussian_sign_conditioned_probability n d (m : 'cV[R]_d)
    w (hw : 0 <= w <= 1) (C : R) :
  sign_mixture_sample_law (gauss d) m hw n (universality_conditioned_fit_event n d C) =
    gaussian_product_law (n*d)
      (sample_translate m @^-1` universality_conditioned_fit_event n d C).
Proof.
apply: gaussian_sign_sample_event.
- exact: measurable_conditioned_fit_event.
- by move=> s x; exact: conditioned_fit_row_sign.
Qed.

Corollary gaussian_sign_error_probability n d (m : 'cV[R]_d)
    w (hw : 0 <= w <= 1) (e eps : R) :
  sign_mixture_sample_law (gauss d) m hw n (universality_error_event n d e eps) =
    gaussian_product_law (n*d)
      (sample_translate m @^-1` universality_error_event n d e eps).
Proof.
apply: gaussian_sign_sample_event.
- exact: measurable_error_event.
- by move=> s x; rewrite /universality_error_event /= fitting_error_row_sign.
Qed.

Corollary gaussian_sign_optimal_tail_probability n d (m : 'cV[R]_d)
    w (hw : 0 <= w <= 1) (c eps : R) :
  sign_mixture_sample_law (gauss d) m hw n
    [set x | (eps%:E < `|data_condition_number n d x-c%:E|)%E] =
    gaussian_product_law (n*d) [set x : paper_main_sample n d |
      (eps%:E < `|data_condition_number n d (sample_translate m x)-c%:E|)%E].
Proof.
apply: gaussian_sign_sample_event.
- have h := @measurable_gaussian_shift_optimal_tail n d (0 : 'cV[R]_d) c eps.
  have E : [set x : paper_main_sample n d |
      (eps%:E < `|data_condition_number n d (sample_translate 0 x)-c%:E|)%E] =
      [set x : paper_main_sample n d |
      (eps%:E < `|data_condition_number n d x-c%:E|)%E].
    by apply/funext=>x; rewrite /= sample_translate0.
  by rewrite E in h.
- by move=> s x; rewrite /= condition_number_row_sign.
Qed.

Theorem gaussian_sign_condition_threshold (alpha C : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (w : nat -> R) (hw : forall d, 0 <= w d <= 1) :
  1 < C -> 0 < alpha -> universality_density_tends_to N alpha ->
  gaussian_small_shift m ->
  (alpha < condition_alpha C ->
    paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
      (N d) (universality_conditioned_fit_event (N d) d C)) 1) /\
  (condition_alpha C < alpha ->
    paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
      (N d) (universality_conditioned_fit_event (N d) d C)) 0).
Proof.
move=> C1 a0 hN hm.
have [hlo hhi] := gaussian_shift_condition_threshold C1 a0 hN hm.
split=> h eps eps0.
- have [D hD] := hlo h eps eps0; exists D => d dD.
  by rewrite gaussian_sign_conditioned_probability; exact: hD.
- have [D hD] := hhi h eps eps0; exists D => d dD.
  by rewrite gaussian_sign_conditioned_probability; exact: hD.
Qed.

Theorem gaussian_sign_optimal_tail (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (w : nat -> R) (hw : forall d, 0 <= w d <= 1) :
  0 < alpha -> alpha < 4%:R^-1 ->
  universality_density_tends_to N alpha -> gaussian_small_shift m ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
    (N d) [set x | (eps%:E < `|data_condition_number (N d) d x-
      (condition_star alpha)%:E|)%E]) 0.
Proof.
move=> a0 a4 hN hm eps e0.
have h := gaussian_shift_optimal_tail a0 a4 hN hm e0.
move=> delta dl0; have [D hD] := h delta dl0; exists D => d dD.
by rewrite gaussian_sign_optimal_tail_probability; exact: hD.
Qed.

Theorem gaussian_sign_arbitrary_shift_exists (alpha : R) :
  0 < alpha -> alpha < 4%:R^-1 ->
  exists K : R, 0 < K /\
  forall (N : nat -> nat) (m : forall d, 'cV[R]_d)
    (w : nat -> R) (hw : forall d, 0 <= w d <= 1),
  universality_density_tends_to N alpha ->
  paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
    (N d) (universality_conditioned_fit_event (N d) d
      (K*(1+frobenius (m d)/Num.sqrt d%:R)))) 1.
Proof.
move=> a0 a4; have [K [K0 hK]] := gaussian_arbitrary_shift_exists a0 a4.
exists K; split => // N m w hw hN eps e0.
have [D hD] := hK N m hN eps e0; exists D => d dD.
by rewrite gaussian_sign_conditioned_probability; exact: hD.
Qed.

Theorem gaussian_sign_error_limit (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (w : nat -> R) (hw : forall d, 0 <= w d <= 1) :
  0 < alpha -> universality_density_tends_to N alpha ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
    (N d) (universality_error_event (N d) d (universality_e_star alpha 3%:R) eps)) 0.
Proof.
move=> a0 hN eps e0.
have h := @gaussian_shift_error_limit alpha N m a0 hN eps e0.
move=> delta dl0; have [D hD] := h delta dl0; exists D => d dD.
by rewrite gaussian_sign_error_probability; exact: hD.
Qed.


Definition condition_bounds_event n d (lo hi : R) : set (paper_main_sample n d) :=
  [set x | universality_conditioned_fit_event n d hi x /\
    (lo%:E <= data_condition_number n d x <= hi%:E)%E].
Arguments condition_bounds_event n d lo hi : clear implicits.

Lemma measurable_condition_bounds_event n d (lo hi : R) :
  measurable (condition_bounds_event n d lo hi).
Proof.
have mf := measurable_data_condition_number n d.
have ml : measurable [set x : paper_main_sample n d |
    (lo%:E <= data_condition_number n d x)%E].
  rewrite -[X in measurable X]setTI.
  exact: (@emeasurable_fun_c_infty _ _ RR setT _ measurableT mf lo%:E).
have mh : measurable [set x : paper_main_sample n d |
    (data_condition_number n d x <= hi%:E)%E].
  rewrite -[X in measurable X]setTI.
  exact: (@emeasurable_fun_infty_c _ _ RR setT _ measurableT mf hi%:E).
have E : condition_bounds_event n d lo hi =
    universality_conditioned_fit_event n d hi `&`
      ([set x | (lo%:E <= data_condition_number n d x)%E] `&`
       [set x | (data_condition_number n d x <= hi%:E)%E]).
  apply/funext=>x; apply/propext; rewrite /condition_bounds_event /=.
  by split=>[[f /andP[hl hh]]|[f [hl hh]]]; split=>//; apply/andP.
rewrite E; apply: measurableI; first exact: measurable_conditioned_fit_event.
exact: measurableI ml mh.
Qed.

Lemma condition_bounds_event_row_sign n d lo hi (s : n.-tuple bool)
    (x : paper_main_sample n d) :
  condition_bounds_event n d lo hi (sample_row_sign s x) =
    condition_bounds_event n d lo hi x.
Proof.
by rewrite /condition_bounds_event /= conditioned_fit_row_sign condition_number_row_sign.
Qed.

Theorem gaussian_sign_arbitrary_shift_condition_bounds (alpha : R) :
  0 < alpha -> alpha < 4%:R^-1 ->
  exists c C : R, [/\ 0 < c, c <= C &
  forall (N : nat -> nat) (m : forall d, 'cV[R]_d)
    (w : nat -> R) (hw : forall d, 0 <= w d <= 1),
    universality_density_tends_to N alpha ->
    forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    exists E : set (paper_main_sample (N d) d),
      [/\ measurable E,
        (sign_mixture_sample_law (gauss d) (m d) (hw d) (N d) E <= eps%:E)%E &
        forall x, ~ E x ->
        universality_conditioned_fit_event (N d) d
          (C*(1+frobenius (m d)/Num.sqrt d%:R)) x /\
        ((c*(1+frobenius (m d)/Num.sqrt d%:R))%:E <=
          data_condition_number (N d) d x <=
          (C*(1+frobenius (m d)/Num.sqrt d%:R))%:E)%E]].
Proof.
move=> a0 a4.
have [c [C [c0 cC hC]]] := gaussian_arbitrary_shift_condition_bounds a0 a4.
exists c,C; split=> // N m w hw hN eps e0.
have [D hD] := hC N m hN eps e0.
exists D=>d dD; have [F [mF PF good]] := hD d dD.
pose rate := 1+frobenius (m d)/Num.sqrt d%:R.
pose A := condition_bounds_event (N d) d (c*rate) (C*rate).
have mA : measurable A := @measurable_condition_bounds_event (N d) d _ _.
exists (~` A); split; first exact: measurableC mA.
- have evenA : forall s x, (~` A) (sample_row_sign s x) = (~` A) x.
    by move=>s x; rewrite /setC /A /= condition_bounds_event_row_sign.
  rewrite (@gaussian_sign_sample_event (N d) d (m d) (w d) (hw d)
    (~` A) (measurableC mA) evenA).
  have mB : measurable (sample_translate (m d) @^-1` (~` A)).
    rewrite -[X in measurable X]setTI.
    exact: measurable_sample_translate (measurableC mA).
  apply: le_trans _ PF; apply: le_measure; rewrite ?inE //.
  move=>x nx; apply: contrapT=>nF.
  apply: nx; exact: good.
- by move=>x nx; apply: contrapT=>nA; apply: nx.
Qed.


(* Centered PSD fits are separately even, so this consequence also holds
   for the sign mixture. No claim about arbitrary-center quadrics is made. *)
Theorem gaussian_sign_psd_nonexistence (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (w : nat -> R) (hw : forall d, 0 <= w d <= 1) :
  4%:R^-1 < alpha -> universality_density_tends_to N alpha ->
  paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
    (N d) (paper_main_fit_event (N d) d)) 0.
Proof.
move=> a4 hN.
have q0 : (0 : RR) < 4%:R^-1 by rewrite invr_gt0 ltr0n.
have a0 := lt_trans q0 a4.
have k31 : (1 : RR) < 3%:R by rewrite ltr1n.
pose e := universality_e_star alpha 3%:R.
have e0 : 0 < e.
  by rewrite /e universality_e_star_gt0 // universality_alpha_star3.
have e20 : 0 < e/2 by rewrite divr_gt0.
have h := @gaussian_sign_error_limit alpha N m w hw a0 hN (e/2) e20.
move=> eps ep0; have [D hD] := h eps ep0.
exists (maxn D 1) =>d; rewrite geq_max=>/andP[dD d0].
have inclusion : paper_main_fit_event (N d) d `<=`
    universality_error_event (N d) d e (e/2).
  move=>x fx; have ferr := fit_fitting_error (N d) d x d0 fx.
  rewrite /universality_error_event /= distrC.
  have qe : 0 <= e-universality_fitting_error (N d) d x by lra.
  rewrite (ger0_norm qe).
  change (is_true ((e/2 : RR) < e-universality_fitting_error (N d) d x)).
  clear -e0 ferr; lra.
have bound : (sign_mixture_sample_law (gauss d) (m d) (hw d) (N d)
    (paper_main_fit_event (N d) d) <=
    sign_mixture_sample_law (gauss d) (m d) (hw d) (N d)
    (universality_error_event (N d) d e (e/2)))%E.
  apply: le_measure; rewrite ?inE //.
  - exact: pm_fit_event_measurable.
  - exact: measurable_error_event.
rewrite sube0 gee0_abs ?measure_ge0 //.
have he := hD d dD.
rewrite sube0 gee0_abs ?measure_ge0 // in he.
exact: le_lt_trans bound he.
Qed.
