(* The fitting error minimized over all translations. Continuity is stated
   in row coordinates for the frozen flat sample layout. The infimum over
   translations has open strict sublevel sets and is measurable; no
   minimizing translation or continuity of that infimum is asserted. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.analysis Require Import infimum_measurability.
From GaussianAnalysis.matrix Require Import euclidean real_spectral centered_correction.
From GaussianAnalysis.convex Require Import psd_residual.
From GaussianAnalysis.probability Require Import tuple_rows.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting.Gaussian.Law Require Import LibraryBridge.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Shifted Require Import GaussianRows ProjectionCertificate Translations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition translation_fitting_error n d (x : paper_main_sample n d) : R :=
  inf [set universality_fitting_error n d (sample_translate m x)
       | m in [set: 'cV[RR]_d]].
Arguments translation_fitting_error n d x : clear implicits.

Lemma fitting_error_nonnegative n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N -> 0 <= universality_fitting_error n d x.
Proof.
by move=> n0 d0; rewrite (sample_residual_gamma x n0 d0) sqr_ge0.
Qed.

Lemma translation_error_values_nonempty n d (x : paper_main_sample n d) :
  [set universality_fitting_error n d (sample_translate m x)
       | m in [set: 'cV[RR]_d]] !=set0.
Proof.
by exists (universality_fitting_error n d x), (0 : 'cV[RR]_d);
  rewrite ?sample_translate0.
Qed.

Lemma translation_error_values_lbound n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N ->
  has_lbound [set universality_fitting_error n d (sample_translate m x)
       | m in [set: 'cV[RR]_d]].
Proof.
move=> n0 d0; exists 0 => _ [m _ <-].
exact: fitting_error_nonnegative.
Qed.

Lemma translation_fitting_error_lower_bound n d (x : paper_main_sample n d)
    (c : R) :
  (forall m : 'cV[RR]_d,
    c <= universality_fitting_error n d (sample_translate m x)) ->
  c <= translation_fitting_error n d x.
Proof.
move=> hc; apply: lb_le_inf; first exact: translation_error_values_nonempty.
by move=> _ [m _ <-]; exact: hc.
Qed.

Lemma translation_fitting_error_nonnegative n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N -> 0 <= translation_fitting_error n d x.
Proof.
move=> n0 d0; apply: translation_fitting_error_lower_bound => m.
exact: fitting_error_nonnegative.
Qed.

Lemma translation_fitting_error_le n d (x : paper_main_sample n d)
    (m : 'cV[RR]_d) :
  (0 < n)%N -> (0 < d)%N ->
  translation_fitting_error n d x <=
    universality_fitting_error n d (sample_translate m x).
Proof.
move=> n0 d0; apply: ge_inf.
- exact: translation_error_values_lbound.
- by exists m.
Qed.

Lemma tuple_row_sampleK n d (x : paper_main_sample n d) :
  tuple_of_row (row_of_tuple (n*d) x) = x.
Proof.
by apply: eq_from_tnth => i; rewrite tnth_tuple_of_row row_of_tupleE.
Qed.

Lemma sample_point_flat_rowE n d (a : 'rV[RR]_(n*d)) (i : 'I_n) (j : 'I_d) :
  paper_main_point (tuple_of_row a) i j 0 = a 0 (row_index i j).
Proof.
have := sample_row_tuple_entry (tuple_of_row a) i j.
by rewrite /sample_row_tuple tnth_mktuple mxE tnth_tuple_of_row.
Qed.

Lemma continuous_sample_residual_coef_row n d :
  continuous (fun a : 'rV[RR]_(n*d) => sample_residual_coef (tuple_of_row a)).
Proof.
have cW : continuous (fun a : 'rV[RR]_(n*d) =>
    (restricted_isometry.tuple_mx (unsat_features n d (tuple_of_row a)))^T).
  apply: continuous_mxP => k i.
  case/mxvec_indexP: k => j l.
  have -> : (fun a : 'rV[RR]_(n*d) =>
      (restricted_isometry.tuple_mx (unsat_features n d (tuple_of_row a)))^T
        (mxvec_index j l) i) =
      (fun a => (Num.sqrt d%:R)^-1 *
        (a 0 (row_index i j) * a 0 (row_index i l) - (j == l)%:R)).
    apply/funext => a.
    rewrite /restricted_isometry.tuple_mx mxE mxE /unsat_features tnth_mktuple
      /unsat_feature mxvecE mxE mxE mxE big_ord1 mxE mxE.
    have hj := @sample_point_flat_rowE n d a i j.
    rewrite /paper_main_point mxE in hj.
    by rewrite !sample_point_flat_rowE hj !mxE.
  move=> a.
  apply: (continuousM (s := fun _ : 'rV[RR]_(n*d) => (Num.sqrt d%:R)^-1)
    (t := fun a : 'rV[RR]_(n*d) =>
      a 0 (row_index i j) * a 0 (row_index i l) - (j == l)%:R)).
  - exact: cst_continuous.
  apply: (continuousB (f := fun a : 'rV[RR]_(n*d) =>
    a 0 (row_index i j) * a 0 (row_index i l))
    (g := fun _ : 'rV[RR]_(n*d) => (j == l)%:R)).
  - apply: (continuousM (s := fun a : 'rV[RR]_(n*d) => a 0 (row_index i j))
      (t := fun a : 'rV[RR]_(n*d) => a 0 (row_index i l))).
    + exact: coord_continuous.
    + exact: coord_continuous.
  - exact: cst_continuous.
have cP : continuous (fun a : 'rV[RR]_(n*d) =>
  (restricted_isometry.tuple_mx (unsat_features n d (tuple_of_row a)))^T *m
    centered_correction.centering_mx n).
  move=> a; apply: (@continuous_comp _ _ _
    (fun a : 'rV[RR]_(n*d) =>
      (restricted_isometry.tuple_mx (unsat_features n d (tuple_of_row a)))^T)
    (fun W => W *m centered_correction.centering_mx n)).
  - exact: cW.
  - exact: continuous_mulmxr.
apply: continuous_mxP => k i a.
rewrite /sample_residual_coef.
have -> : (fun a : 'rV[RR]_(n*d) =>
  ((Num.sqrt n%:R)^-1 *:
   ((restricted_isometry.tuple_mx (unsat_features n d (tuple_of_row a)))^T *m
    centered_correction.centering_mx n)) k i) =
  (fun a => (Num.sqrt n%:R)^-1 *
   ((restricted_isometry.tuple_mx (unsat_features n d (tuple_of_row a)))^T *m
    centered_correction.centering_mx n) k i).
  by apply/funext => b; rewrite mxE.
apply: (continuousM (s := fun _ : 'rV[RR]_(n*d) => (Num.sqrt n%:R)^-1)
  (t := fun a : 'rV[RR]_(n*d) =>
   ((restricted_isometry.tuple_mx (unsat_features n d (tuple_of_row a)))^T *m
    centered_correction.centering_mx n) k i)).
- exact: cst_continuous.
apply: (@continuous_comp _ _ _
  (fun a : 'rV[RR]_(n*d) =>
   (restricted_isometry.tuple_mx (unsat_features n d (tuple_of_row a)))^T *m
    centered_correction.centering_mx n)
  (fun W : 'M[RR]_(d*d,n) => W k i)).
- exact: cP.
- exact: coord_continuous.
Qed.

Lemma continuous_sample_residual_projection_row n d : (0 < d)%N ->
  continuous (fun a : 'rV[RR]_(n*d) => sample_residual_projection (tuple_of_row a)).
Proof.
move=> d0 a; apply: (@continuous_comp _ _ _
  (fun a : 'rV[RR]_(n*d) => sample_residual_coef (tuple_of_row a))
  (psd_residual_projection d%:R)).
- exact: continuous_sample_residual_coef_row.
- exact: (@psd_residual_projection_continuous RR d n d%:R d0 (ler0n _ d)).
Qed.

Lemma continuous_fitting_error_row n d : (0 < n)%N -> (0 < d)%N ->
  continuous (fun a : 'rV[RR]_(n*d) => universality_fitting_error n d (tuple_of_row a)).
Proof.
move=> n0 d0.
have -> : (fun a : 'rV[RR]_(n*d) => universality_fitting_error n d (tuple_of_row a)) =
    (fun a => mxdot (sample_residual_projection (tuple_of_row a))
      (sample_residual_projection (tuple_of_row a))).
  by apply/funext => a; rewrite sample_residual_gamma // frobenius_sqr.
move=> a; apply: (@continuous_comp _ _ _
  (fun a : 'rV[RR]_(n*d) => sample_residual_projection (tuple_of_row a))
  (fun z : 'rV[RR]_n => mxdot z z)).
- exact: (@continuous_sample_residual_projection_row n d d0).
- exact: continuous_mxdot.
Qed.

Definition translated_flat_row n d (m : 'cV[RR]_d) (a : 'rV[RR]_(n*d)) :=
  a + \row_k m (sample_flat_col k) 0.
Lemma translated_flat_rowE n d (m : 'cV[RR]_d) (a : 'rV[RR]_(n*d)) :
  tuple_of_row (translated_flat_row m a) = sample_translate m (tuple_of_row a).
Proof.
apply: eq_from_tnth => k.
by rewrite tnth_tuple_of_row /translated_flat_row !mxE
  sample_translate_entry tnth_tuple_of_row.
Qed.
Lemma continuous_translated_flat_row n d (m : 'cV[RR]_d) :
  continuous (@translated_flat_row n d m).
Proof. by move=> a; apply: continuousD; [exact: cvg_id | exact: cst_continuous]. Qed.

Lemma continuous_translated_fitting_error_row n d (m : 'cV[RR]_d) :
  (0 < n)%N -> (0 < d)%N ->
  continuous (fun a : 'rV[RR]_(n*d) =>
    universality_fitting_error n d (sample_translate m (tuple_of_row a))).
Proof.
move=> n0 d0.
have -> : (fun a : 'rV[RR]_(n*d) =>
      universality_fitting_error n d (sample_translate m (tuple_of_row a))) =
    (fun a => universality_fitting_error n d (tuple_of_row (translated_flat_row m a))).
  by apply/funext => a; rewrite translated_flat_rowE.
move=> a; apply: (@continuous_comp _ _ _ (translated_flat_row m)
  (fun a : 'rV[RR]_(n*d) => universality_fitting_error n d (tuple_of_row a))).
- exact: continuous_translated_flat_row.
- exact: (@continuous_fitting_error_row n d n0 d0).
Qed.


Lemma translation_fitting_error_open_sublevel_row n d (t : R) :
  (0 < n)%N -> (0 < d)%N ->
  open [set a : 'rV[RR]_(n*d) |
    translation_fitting_error n d (tuple_of_row a) < t].
Proof.
move=> n0 d0; apply: open_infimum_sublevel.
- by exists (0 : 'cV[RR]_d).
- move=> m _; exact: continuous_translated_fitting_error_row.
- move=> a; exact: translation_error_values_lbound.
Qed.

Lemma measurable_translation_fitting_error_row n d :
  (0 < n)%N -> (0 < d)%N ->
  measurable_fun [set: 'rV[RR]_(n*d)]
    (fun a => translation_fitting_error n d (tuple_of_row a) : RR).
Proof.
move=> n0 d0; apply: measurable_infimum_mx.
- by exists (0 : 'cV[RR]_d).
- move=> m _; exact: continuous_translated_fitting_error_row.
- move=> a; exact: translation_error_values_lbound.
Qed.

Theorem measurable_translation_fitting_error n d :
  (0 < n)%N -> (0 < d)%N ->
  measurable_fun [set: paper_main_sample n d]
    (fun x => translation_fitting_error n d x : RR).
Proof.
move=> n0 d0.
apply: (eq_measurable_fun (fun x : paper_main_sample n d =>
  translation_fitting_error n d (tuple_of_row (row_of_tuple (n*d) x)) : RR)).
  by move=> x _; rewrite tuple_row_sampleK.
exact: measurableT_comp (measurable_translation_fitting_error_row n0 d0)
  (measurable_row_of_tuple (n*d)).
Qed.
