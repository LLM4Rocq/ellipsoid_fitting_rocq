(* Centered fitting errors on actual iid matrix samples and their main
   blocks. The law identifications are exact in every dimension. The
   reserve size is arbitrary in the main-block limit: no density condition
   on that block, and no independence of main-sample weights, is used. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.probability Require Import independent_row_signs independent_matrix_blocks.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions MixtureStatement MixtureTheorem.
From EllipsoidUniversality Require Import CountableMixtureDefinitions CountableMixtureStatement CountableTheorem.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Gaussian Require Import InProbability.
From EllipsoidUniversality.Shifted Require Import MainMoment MixtureRows GaussianExports.
From EllipsoidUniversality.Shifted Require Import ReserveCertificate GaussianRows ConditionTranslation.
From GaussianAnalysis.probability Require Import lindeberg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma reserve_sample_matrix_blocks n k d (H : 'M[RR]_(n+k,d)) :
  reserve_sample (matrix_sample (usubmx H)) (dsubmx H) = matrix_sample H.
Proof.
rewrite /reserve_sample /matrix_sample sample_of_row_tupleK.
congr sample_of_row_tuple; apply: eq_from_tnth => i.
rewrite -[i]splitK; case: (fintype.split i)=>j /=;
  rewrite ?tnth_lshift ?tnth_rshift !tnth_mktuple;
  apply/rowP=> h; by rewrite !mxE.
Qed.

Lemma independent_main_matrix_law n k d (P : nat -> probability 'rV[RR]_d RR)
    (A : set 'M[RR]_(n,d)) : measurable A ->
  independent_row_matrix_law P (n+k) (usubmx @^-1` A) =
  independent_row_matrix_law P n A.
Proof.
move=> mA.
have h := @independent_matrix_block_events RR d P n k setT A measurableT mA.
have e : [set H : 'M[RR]_(n+k,d) | setT (dsubmx H) /\ A (usubmx H)] = usubmx @^-1` A.
  by apply/seteqP; split=> H /=; [case|split].
by move: h; rewrite e /= probability_setT mul1e.
Qed.

Lemma independent_main_statistic_law n k d (P : nat -> probability 'rV[RR]_d RR)
    (f : 'M[RR]_(n,d) -> RR) (A : set RR) :
  measurable_fun setT f -> measurable A ->
  independent_row_matrix_law P (n+k) ((fun H => f (usubmx H)) @^-1` A) =
  independent_row_matrix_law P n (f @^-1` A).
Proof.
move=> mf mA; apply: independent_main_matrix_law.
by rewrite -[X in measurable X]setTI; exact: mf.
Qed.

Lemma independent_main_statistic_cvg (n k : nat -> nat)
    (P : forall d, nat -> probability 'rV[RR]_d RR)
    (f : forall d, 'M[RR]_(n d,d) -> RR) l :
  (forall d, measurable_fun setT (f d)) ->
  cvg_prob (fun d => independent_row_matrix_law (P d) (n d)) f l ->
  cvg_prob (fun d => independent_row_matrix_law (P d) (n d+k d))
    (fun d H => f d (usubmx H)) l.
Proof.
move=> mf hf.
apply: (@cvg_prob_law _ _ _ _
  (fun d => independent_row_matrix_law (P d) (n d+k d))
  (fun d => independent_row_matrix_law (P d) (n d))
  (fun d H => f d (usubmx H)) f l) => //.
- move=> d; apply: measurableT_comp (mf d) _; exact: measurable_usubmx.
- exists 0%N=> d _ A mA; exact: independent_main_statistic_law (mf d) mA.
Qed.

Lemma measurable_matrix_fitting_error n d :
  measurable_fun [set: 'M[RR]_(n,d)]
    (fun H => universality_fitting_error n d (matrix_sample H) : RR).
Proof.
apply: measurableT_comp (measurable_fitting_error n d) _.
exact: measurable_matrix_sample.
Qed.

Lemma matrix_sample_law_of_rows n d (P : probability 'rV[RR]_d RR)
    (pi : set (paper_main_sample n d) -> \bar R) :
  (forall A, measurable A -> pi (sample_row_tuple @^-1` A) =
    tuple_prod (fun=>P) n A) ->
  forall A : set (paper_main_sample n d), measurable A ->
  independent_row_matrix_law (fun=>P) n ((@matrix_sample n d) @^-1` A) = pi A.
Proof.
move=> h A mA.
have mB : measurable ((@matrix_sample n d) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_matrix_sample.
have mC : measurable (row_tuple_matrix n @^-1` ((@matrix_sample n d) @^-1` A)).
  exact (measurable_funPTI (row_tuple_matrix n) mB).
rewrite independent_row_matrix_lawE -(h _ mC).
congr pi; apply/funext=> x /=.
change (A (matrix_sample (sample_point_matrix x)) = A x).
by rewrite sample_matrix_sampleK.
Qed.

Lemma gaussian_matrix_sample_law n d (A : set (paper_main_sample n d)) :
  measurable A ->
  independent_row_matrix_law (fun=>gauss d) n ((@matrix_sample n d) @^-1` A) =
  gaussian_product_law (n*d) A.
Proof.
apply: matrix_sample_law_of_rows => B mB.
exact: gaussian_sample_row_tuple_law.
Qed.

Lemma matrix_error_cvg_of_tails (n : nat -> nat)
    (Q : forall d, probability 'M[RR]_(n d,d) RR) (l : R) :
  (forall eta : R, 0 < eta -> paper_main_tends_to
    (fun d => Q d ((@matrix_sample (n d) d) @^-1`
      universality_error_event (n d) d l eta)) 0) ->
  cvg_prob Q (fun d H => universality_fitting_error (n d) d (matrix_sample H)) l.
Proof.
move=> h eta eta0 eps eps0.
have eta20 : 0 < eta/2 by rewrite divr_gt0.
have [D hD] := h _ eta20 eps eps0.
exists D => d dD.
exists ((@matrix_sample (n d) d) @^-1`
  universality_error_event (n d) d l (eta/2)); split.
- rewrite -[X in measurable X]setTI.
  exact: measurable_matrix_sample measurableT _ (measurable_error_event _ _ _ _).
- have hd := hD d dD.
  rewrite sube0 gee0_abs ?measure_ge0 // in hd.
  exact: ltW hd.
- move=> H /= hH; rewrite /universality_error_event /=.
  have eta2lt : eta/2 < eta by rewrite ltr_pdivrMr //; lra.
  exact: lt_le_trans eta2lt hH.
Qed.

Theorem gaussian_matrix_error_cvg (n : nat -> nat) (alpha : R) :
  0 < alpha -> universality_density_tends_to n alpha ->
  cvg_prob (fun d => independent_row_matrix_law (fun=>gauss d) (n d))
    (fun d H => universality_fitting_error (n d) d (matrix_sample H))
    (universality_e_star alpha 3%:R).
Proof.
move=> alpha0 hn; apply: matrix_error_cvg_of_tails => eta eta0.
have [_ h] := gaussian_fitting_error_holds alpha alpha0.
have he := h n hn eta eta0.
move=> eps eps0; have [D hD] := he eps eps0.
exists D=>d dD.
rewrite gaussian_matrix_sample_law.
- exact: measurable_error_event.
- exact: hD d dD.
Qed.

Corollary gaussian_main_matrix_error_cvg (n k : nat -> nat) (alpha : R) :
  0 < alpha -> universality_density_tends_to n alpha ->
  cvg_prob (fun d => independent_row_matrix_law (fun=>gauss d) (n d+k d))
    (fun d H => universality_fitting_error (n d) d (matrix_sample (usubmx H)))
    (universality_e_star alpha 3%:R).
Proof.
move=> alpha0 hn.
apply: (@independent_main_statistic_cvg n k (fun d _=>gauss d)
  (fun d H => universality_fitting_error (n d) d (matrix_sample H)) _).
- move=> d; exact: measurable_matrix_fitting_error.
- exact: gaussian_matrix_error_cvg.
Qed.

Section finite_errors.
Variables (K : R) (N : nat -> nat) (w : nat -> nat -> R).
Variable mu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Hypothesis hfam : mixture_family K N w mu.

Lemma finite_matrix_sample_law n d (A : set (paper_main_sample n d)) :
  measurable A ->
  independent_row_matrix_law (fun=>finite_row_law hfam d) n
    ((@matrix_sample n d) @^-1` A) =
  mixture_probability (N d) (w d) (mu d) n d A.
Proof.
apply: matrix_sample_law_of_rows => B mB.
exact: finite_sample_row_tuple_law.
Qed.

Theorem finite_matrix_error_cvg (n : nat -> nat) (alpha kappa : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> mixture_fourth_moment kappa N w mu ->
  universality_density_tends_to n alpha ->
  cvg_prob (fun d => independent_row_matrix_law (fun=>finite_row_law hfam d) (n d))
    (fun d H => universality_fitting_error (n d) d (matrix_sample H))
    (universality_e_star alpha kappa).
Proof.
move=> kappa1 K0 alpha0 hfourth hn.
apply: matrix_error_cvg_of_tails => eta eta0.
have [hm _] := mixture_theorem.
have [_ _ [_ h]] := hm kappa K alpha kappa1 K0 alpha0.
have he := h N w mu hfam hfourth n hn eta eta0.
move=> eps eps0; have [D hD] := he eps eps0.
exists D=>d dD.
rewrite finite_matrix_sample_law.
- exact: measurable_error_event.
- exact: hD d dD.
Qed.

Corollary finite_main_matrix_error_cvg (n k : nat -> nat) (alpha kappa : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> mixture_fourth_moment kappa N w mu ->
  universality_density_tends_to n alpha ->
  cvg_prob (fun d => independent_row_matrix_law (fun=>finite_row_law hfam d) (n d+k d))
    (fun d H => universality_fitting_error (n d) d (matrix_sample (usubmx H)))
    (universality_e_star alpha kappa).
Proof.
move=> kappa1 K0 alpha0 hfourth hn.
apply: (@independent_main_statistic_cvg n k (fun d _=>finite_row_law hfam d)
  (fun d H => universality_fitting_error (n d) d (matrix_sample H)) _).
- move=> d; exact: measurable_matrix_fitting_error.
- exact: finite_matrix_error_cvg.
Qed.

End finite_errors.

Section countable_errors.
Variables (K : R) (w : nat -> nat -> R).
Variable mu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Hypothesis hfam : countable_mixture_family K w mu.

Lemma countable_matrix_sample_law n d (A : set (paper_main_sample n d)) :
  measurable A ->
  independent_row_matrix_law (fun=>countable_row_law hfam d) n
    ((@matrix_sample n d) @^-1` A) =
  countable_mixture_probability (w d) (mu d) n d A.
Proof.
apply: matrix_sample_law_of_rows => B mB.
exact: countable_sample_row_tuple_law.
Qed.

Theorem countable_matrix_error_cvg (n : nat -> nat) (alpha kappa : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> countable_fourth_moment kappa w mu ->
  universality_density_tends_to n alpha ->
  cvg_prob (fun d => independent_row_matrix_law (fun=>countable_row_law hfam d) (n d))
    (fun d H => universality_fitting_error (n d) d (matrix_sample H))
    (universality_e_star alpha kappa).
Proof.
move=> kappa1 K0 alpha0 hfourth hn.
apply: matrix_error_cvg_of_tails => eta eta0.
have [hm _] := countable_theorem.
have [_ _ [_ h]] := hm kappa K alpha kappa1 K0 alpha0.
have he := h w mu hfam hfourth n hn eta eta0.
move=> eps eps0; have [D hD] := he eps eps0.
exists D=>d dD.
rewrite countable_matrix_sample_law.
- exact: measurable_error_event.
- exact: hD d dD.
Qed.

Corollary countable_main_matrix_error_cvg (n k : nat -> nat) (alpha kappa : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> countable_fourth_moment kappa w mu ->
  universality_density_tends_to n alpha ->
  cvg_prob (fun d => independent_row_matrix_law (fun=>countable_row_law hfam d) (n d+k d))
    (fun d H => universality_fitting_error (n d) d (matrix_sample (usubmx H)))
    (universality_e_star alpha kappa).
Proof.
move=> kappa1 K0 alpha0 hfourth hn.
apply: (@independent_main_statistic_cvg n k (fun d _=>countable_row_law hfam d)
  (fun d H => universality_fitting_error (n d) d (matrix_sample H)) _).
- move=> d; exact: measurable_matrix_fitting_error.
- exact: countable_matrix_error_cvg.
Qed.

End countable_errors.
