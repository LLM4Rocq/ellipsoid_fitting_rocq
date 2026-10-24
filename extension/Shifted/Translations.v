(* Translation of the frozen flat sample layout. The same moment-cancelling
   certificate controls the fitting error at every translation; the proof
   makes no measurable choice of a translation or a fitting matrix. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.matrix Require Import euclidean psd_part quadric_certificate.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import tuple_rows.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Gaussian Require Import Limit Representation.
From EllipsoidUniversality.Shifted Require Import GaussianRows ResidualCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition sample_translate n d (m : 'cV[RR]_d)
    (x : paper_main_sample n d) : paper_main_sample n d :=
  sample_of_row_tuple
    (tuple_map (fun _ (z : 'rV[RR]_d) => z + m^T) (sample_row_tuple x)).

Lemma sample_translate_point n d (m : 'cV[RR]_d)
    (x : paper_main_sample n d) (i : 'I_n) :
  paper_main_point (sample_translate m x) i = paper_main_point x i + m.
Proof.
have hi := congr1 (fun z : n.-tuple 'rV[RR]_d => tnth z i)
  (sample_of_row_tupleK
    (tuple_map (fun _ (z : 'rV[RR]_d) => z + m^T) (sample_row_tuple x))).
have ht : (paper_main_point (sample_translate m x) i)^T =
    (paper_main_point x i)^T + m^T.
  by move: hi; rewrite /sample_row_tuple /tuple_map !tnth_mktuple.
by move: (congr1 trmx ht); rewrite linearD /= !trmxK.
Qed.

Lemma sample_translate_entry n d (m : 'cV[RR]_d)
    (x : paper_main_sample n d) (k : 'I_(n*d)) :
  tnth (sample_translate m x) k = tnth x k + m (sample_flat_col k) 0.
Proof.
rewrite -{1 2}(sample_flat_indicesK k) -!sample_row_tuple_entry.
rewrite /sample_row_tuple !tnth_mktuple sample_translate_point !mxE.
done.
Qed.

Lemma sample_translate0 n d (x : paper_main_sample n d) :
  sample_translate 0 x = x.
Proof.
by apply: eq_from_tnth => k; rewrite sample_translate_entry mxE addr0.
Qed.

Lemma sample_translate_add n d (m h : 'cV[RR]_d)
    (x : paper_main_sample n d) :
  sample_translate m (sample_translate h x) = sample_translate (m+h) x.
Proof.
apply: eq_from_tnth => k; rewrite !sample_translate_entry mxE.
by rewrite -addrA [h _ _ + m _ _]addrC.
Qed.

Lemma sample_translateK n d (m : 'cV[RR]_d) :
  cancel (@sample_translate n d m) (sample_translate (-m)).
Proof. by move=> x; rewrite sample_translate_add addNr sample_translate0. Qed.

Lemma measurable_sample_translate_joint n d :
  measurable_fun [set: 'cV[RR]_d * paper_main_sample n d]
    (fun p => sample_translate p.1 p.2).
Proof.
apply/measurable_fun_tnthP => k.
rewrite /comp /=.
under eq_fun do rewrite sample_translate_entry.
apply: measurable_funD.
- exact: measurableT_comp (measurable_tnth k) measurable_snd.
- exact: measurableT_comp (measurable_mxentry _ _) measurable_fst.
Qed.

Lemma measurable_sample_translate n d (m : 'cV[RR]_d) :
  measurable_fun [set: paper_main_sample n d] (sample_translate m).
Proof.
apply/measurable_fun_tnthP => k.
rewrite /comp /=.
under eq_fun do rewrite sample_translate_entry.
by apply: measurable_funD; [exact: measurable_tnth | exact: measurable_cst].
Qed.

Lemma sample_translate_moment n d (m : 'cV[RR]_d)
    (x : paper_main_sample n d) (w : 'I_n -> R) :
  \sum_i w i = 0 -> \sum_i w i *: paper_main_point x i = 0 ->
  \sum_i w i *: paper_main_point (sample_translate m x) i = 0.
Proof.
move=> w0 wx0.
under eq_bigr do rewrite sample_translate_point scalerDr.
by rewrite big_split /= wx0 add0r -scaler_suml w0 scale0r.
Qed.

Theorem translated_sample_certificate_error n d (x : paper_main_sample n d)
    (w : 'I_n -> R) (t : R) :
  (0 < n)%N -> (0 < d)%N -> 0 <= t ->
  0 < \sum_i (w i)^+2 ->
  \sum_i w i = 0 -> \sum_i w i *: paper_main_point x i = 0 ->
  psdmx (weighted_outer w (fun i : 'I_n => paper_main_point x i) - t%:M) ->
  forall m : 'cV[RR]_d,
    d%:R*t^+2 / (n%:R * \sum_i (w i)^+2) <=
      universality_fitting_error n d (sample_translate m x).
Proof.
move=> n0 d0 t0 w2 w0 wx0 H m.
apply: (@sample_certificate_error n d (sample_translate m x) w t n0 d0 t0 w2 w0).
- exact: sample_translate_moment w0 wx0.
- have -> : (fun i : 'I_n => paper_main_point (sample_translate m x) i) =
      (fun i => paper_main_point x i + m).
    by apply/funext => i; rewrite sample_translate_point.
  by rewrite weighted_outer_translate.
Qed.

Corollary translated_sample_certificate_no_fit n d (x : paper_main_sample n d)
    (w : 'I_n -> R) (t : R) :
  \sum_i w i = 0 -> \sum_i w i *: paper_main_point x i = 0 ->
  0 < t ->
  psdmx (weighted_outer w (fun i : 'I_n => paper_main_point x i) - t%:M) ->
  forall (m : 'cV[RR]_d) (Q : 'M[RR]_d) (c : R),
    paper_main_psd Q -> Q != 0 ->
    ~ (forall i : 'I_n,
      paper_main_quadratic_form Q (paper_main_point (sample_translate m x) i) = c).
Proof.
move=> w0 wx0 t0 H m Q c Qp Q0 hfit.
have Qp' : psdmx Q by exact/paper_psdP.
apply: (@quadric_certificate_no_translated_fit RR _ d w
  (fun i => paper_main_point x i) t w0 wx0 t0 H m Q c Qp' Q0).
move=> i.
by rewrite -sample_translate_point -paper_quadratic_mxdot; exact: hfit.
Qed.
