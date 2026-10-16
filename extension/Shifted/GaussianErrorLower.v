(* Uniform lower bounds for shifted Gaussian fitting error. The reserve
   certificate gives one measurable high-probability event that works for
   every translation; above the PSD threshold it excludes every nonzero
   positive semidefinite quadric, including arbitrary linear terms. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part quadric_certificate.
From GaussianAnalysis.probability Require Import independent_row_signs.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import InProbability Threshold.
From EllipsoidUniversality.Shifted Require Import GaussianRows MainMoment ResidualLaws.
From EllipsoidUniversality.Shifted Require Import ConditionTranslation TranslationError ReserveLimit.
From EllipsoidUniversality.Shifted Require Import ReserveApplications ErrorCurve SampleSplit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma measurable_empty_sample_function n d (f : paper_main_sample n d -> RR) :
  (n*d = 0)%N -> measurable_fun setT f.
Proof.
move=> nd0.
pose x0 : paper_main_sample n d := [tuple (0:R) | i < n*d].
have ex (x : paper_main_sample n d) : x = x0.
  apply: eq_from_tnth => i.
  have hi := leq_trans (ltn_ord i) (eq_leq nd0).
  by rewrite ltn0 in hi.
have -> : f = (fun _ => f x0).
  by apply/funext=>x; rewrite (ex x).
exact: measurable_cst.
Qed.

Lemma measurable_translation_fitting_error_all n d :
  measurable_fun [set: paper_main_sample n d]
    (fun x => translation_fitting_error n d x : RR).
Proof.
case: (posnP n)=>[->|n0].
  by apply: measurable_empty_sample_function; rewrite mul0n.
case: (posnP d)=>[->|d0].
  by apply: measurable_empty_sample_function; rewrite muln0.
exact: measurable_translation_fitting_error.
Qed.

Lemma measurable_translation_error_sublevel n d (t : R) :
  measurable [set x : paper_main_sample n d | translation_fitting_error n d x <= t].
Proof.
have mf := @measurable_translation_fitting_error_all n d.
have mc : measurable_fun [set: paper_main_sample n d] (fun _ => t : RR).
  exact: measurable_cst.
have mb := measurable_fun_ler mf mc.
have mt : measurable ([set true] : set bool) by [].
by have h := mb measurableT _ mt; rewrite setTI preimage_true in h.
Qed.

Lemma gaussian_sample_matrix_row_law n d (A : set 'M[RR]_(n,d)) :
  measurable A ->
  gaussian_product_law (n*d) ((@sample_point_matrix n d) @^-1` A) =
  independent_row_matrix_law (fun=>gauss d) n A.
Proof.
move=> mA.
have mB : measurable ((@sample_point_matrix n d) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_sample_point_matrix.
rewrite -(gaussian_matrix_sample_law mB).
congr (independent_row_matrix_law _ _ _); apply/funext=> H /=.
by rewrite matrix_sample_matrixK.
Qed.

Lemma gaussian_sample_matrix_negligible (n : nat -> nat)
    (E : forall d, set 'M[RR]_(n d,d)) :
  negligible (fun d => independent_row_matrix_law (fun=>gauss d) (n d)) E ->
  negligible (fun d => gaussian_product_law (n d*d))
    (fun d => (@sample_point_matrix (n d) d) @^-1` E d).
Proof.
move=> h eps eps0; have [D hD] := h eps eps0.
exists D=>d dD; have [A [mA PA EA]] := hD d dD.
exists ((@sample_point_matrix (n d) d) @^-1` A); split.
- by rewrite -[X in measurable X]setTI; exact: measurable_sample_point_matrix.
- by rewrite gaussian_sample_matrix_row_law.
- by move=>x /= hx; exact: EA.
Qed.

Lemma negligible_probability_tends_to {disp : measure_display}
    {T : nat -> measurableType disp} (P : forall d, probability (T d) RR)
    (E : forall d, set (T d)) :
  (forall d, measurable (E d)) -> negligible P E ->
  paper_main_tends_to (fun d => P d (E d)) 0.
Proof.
move=> mE h eps eps0.
have eps20 : 0 < eps/2 by rewrite divr_gt0.
have [D hD] := h _ eps20; exists D=>d dD.
have [A [mA PA EA]] := hD d dD.
rewrite sube0 gee0_abs ?measure_ge0 //.
apply: le_lt_trans (le_measure (P d) (mem_set (mE d)) (mem_set mA) EA) _.
apply: le_lt_trans PA _; rewrite lte_fin.
by rewrite ltr_pdivrMr //; lra.
Qed.


Theorem gaussian_split_translation_error_negligible
    (N k : nat -> nat) (beta gamma t : R) :
  0 < beta -> 0 < gamma ->
  universality_density_tends_to N beta -> universality_density_tends_to k gamma ->
  t < beta/(beta+gamma)*universality_e_star beta 3%:R ->
  negligible (fun d => gaussian_product_law ((N d+k d)*d))
    (fun d => [set x : paper_main_sample (N d+k d) d |
      translation_fitting_error (N d+k d) d x <= t]).
Proof.
move=> beta0 gamma0 hN hk tl.
have e0 := @shifted_e_star_ge0 beta 3%:R beta0.
have hbad := @gaussian_reserve_model_converges N k beta gamma beta0 gamma0 hN hk.
have herr := @gaussian_main_matrix_error_cvg N k beta beta0 hN.
have hmat := @reserve_matrix_translation_lower_tail N k
  (fun d => independent_row_matrix_law (fun=>gauss d) (N d+k d))
  beta gamma (universality_e_star beta 3%:R) beta0 gamma0 e0 hN hk
  hbad herr t tl.
apply: negligibleW (gaussian_sample_matrix_negligible hmat) _.
by exists 0%N =>d _ x /=; rewrite sample_matrix_sampleK.
Qed.

Theorem gaussian_split_quadric_negligible (N k : nat -> nat) (beta gamma : R) :
  4%:R^-1 < beta -> 0 < gamma ->
  universality_density_tends_to N beta -> universality_density_tends_to k gamma ->
  negligible (fun d => gaussian_product_law ((N d+k d)*d))
    (fun d => [set x : paper_main_sample (N d+k d) d |
      exists (Q : 'M[RR]_d) (v : 'cV[RR]_d) (c : R),
        psdmx Q /\ Q != 0 /\ forall i : 'I_(N d+k d),
          quadric_eval Q v c (paper_main_point x i) = 0]).
Proof.
move=> b4 gamma0 hN hk.
have q0 : (0:RR) < 4%:R^-1 by rewrite invr_gt0.
have beta0 : 0 < beta := lt_trans q0 b4.
have k31 : (1:RR) < 3%:R by rewrite ltr1n.
have ep : 0 < universality_e_star beta 3%:R.
  by rewrite universality_e_star_gt0 // universality_alpha_star3.
have hbad := @gaussian_reserve_model_converges N k beta gamma beta0 gamma0 hN hk.
have herr := @gaussian_main_matrix_error_cvg N k beta beta0 hN.
have hmat := @reserve_matrix_quadric_bad_negligible N k
  (fun d => independent_row_matrix_law (fun=>gauss d) (N d+k d))
  beta gamma (universality_e_star beta 3%:R) beta0 gamma0 (ltW ep) hN hk
  hbad herr ep.
apply: negligibleW (gaussian_sample_matrix_negligible hmat) _.
by exists 0%N =>d _ x /=; rewrite sample_matrix_sampleK.
Qed.


Theorem gaussian_translation_error_lower_tail (alpha : R) (n : nat -> nat) (t : R) :
  0 < alpha -> universality_density_tends_to n alpha ->
  t < universality_e_star alpha 3%:R ->
  paper_main_tends_to (fun d => gaussian_product_law (n d*d)
    [set x : paper_main_sample (n d) d | translation_fitting_error (n d) d x <= t]) 0.
Proof.
move=> alpha0 hn tl.
have k31 : (1:RR) < 3%:R by rewrite ltr1n.
have [beta [beta0 [ba tb]]] := @shifted_e_star_left_approx alpha 3%:R t alpha0 k31 tl.
have [N [k [hnk [hN hk]]]] := @sample_split_density n alpha beta beta0 ba hn.
have en : n = (fun d => N d+k d)%N by apply/funext=>d; exact: esym (hnk d).
rewrite en; apply: negligible_probability_tends_to.
- move=>d; exact: measurable_translation_error_sublevel.
- apply: gaussian_split_translation_error_negligible beta0 _ hN hk _.
  + by rewrite subr_gt0.
  + have he : beta+(alpha-beta) = alpha by ring.
    by rewrite he.
Qed.

Theorem gaussian_quadric_bad_negligible (alpha : R) (n : nat -> nat) :
  4%:R^-1 < alpha -> universality_density_tends_to n alpha ->
  negligible (fun d => gaussian_product_law (n d*d))
    (fun d => [set x : paper_main_sample (n d) d |
      exists (Q : 'M[RR]_d) (v : 'cV[RR]_d) (c : R),
        psdmx Q /\ Q != 0 /\ forall i : 'I_(n d),
          quadric_eval Q v c (paper_main_point x i) = 0]).
Proof.
move=> a4 hn.
pose beta : RR := (alpha+4%:R^-1)/2.
have q0 : (0:RR) < 4%:R^-1 by rewrite invr_gt0.
have beta0 : 0 < beta by rewrite /beta divr_gt0 // addr_gt0 //; exact: lt_trans q0 a4.
have b4 : 4%:R^-1 < beta by rewrite /beta; lra.
have ba : beta < alpha by rewrite /beta; lra.
have [N [k [hnk [hN hk]]]] := @sample_split_density n alpha beta beta0 ba hn.
have en : n = (fun d => N d+k d)%N by apply/funext=>d; exact: esym (hnk d).
rewrite en; apply: gaussian_split_quadric_negligible b4 _ hN hk.
by rewrite subr_gt0.
Qed.

Theorem gaussian_quadric_good_events (alpha : R) (n : nat -> nat) :
  4%:R^-1 < alpha -> universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [ /\ measurable E,
    (gaussian_product_law (n d*d) E <= eps%:E)%E &
    forall x, ~ E x -> forall (Q : 'M[RR]_d) (v : 'cV[RR]_d) (c : R),
      psdmx Q -> Q != 0 ->
      ~ (forall i : 'I_(n d), quadric_eval Q v c (paper_main_point x i) = 0)].
Proof.
move=> a4 hn eps eps0.
have [D hD] := @gaussian_quadric_bad_negligible alpha n a4 hn eps eps0.
exists D=>d dD; have [E [mE PE hE]] := hD d dD.
exists E; split=> // x nx Q v c Qpsd Qnz hfit.
apply: nx; apply: hE; by exists Q,v,c; split=> //; split.
Qed.
