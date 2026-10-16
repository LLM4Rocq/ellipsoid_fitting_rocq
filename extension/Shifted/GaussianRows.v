(* Exact bridges from the frozen flat Gaussian sample to row tuples and
   Gaussian matrices. The row order is the order of paper_main_point; no
   identification with MathComp's matrix vectorization is implicit.
   Deterministic right isometries act separately on every sample row.
   The one-point bridge is reused from Gaussian/Law/LibraryBridge. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From GaussianAnalysis.comparison Require Import gauss_law gauss_matrix_law.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
From EllipsoidFitting.Gaussian.Law Require Import LibraryBridge.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Model Require Import Rows.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition sample_row_tuple {n d : nat} (x : paper_main_sample n d) :
    n.-tuple 'rV[RR]_d :=
  [tuple (paper_main_point x i)^T | i < n].

Lemma sample_row_tupleE n d (x : paper_main_sample n d) :
  sample_row_tuple x =
  tuple_map (fun=> row_of_tuple d) (tuple_rows n d x).
Proof.
apply: eq_from_tnth => i.
rewrite /sample_row_tuple !tnth_mktuple paper_main_point_row.
by apply/matrixP => j k; rewrite /tuple_point /row_of_tuple !mxE
  /tuple_rows !tnth_mktuple.
Qed.

Lemma measurable_sample_row_tuple n d :
  measurable_fun [set: paper_main_sample n d] (@sample_row_tuple n d).
Proof.
apply: (eq_measurable_fun
  (fun x => tuple_map (fun=> row_of_tuple d) (tuple_rows n d x))).
  by move=> x _; rewrite sample_row_tupleE.
apply: measurableT_comp; last exact: measurable_tuple_rows.
by apply: measurable_tuple_map => i; exact: measurable_row_of_tuple.
Qed.

Lemma gaussian_sample_row_tuple_law n d
    (A : set (n.-tuple 'rV[RR]_d)) : measurable A ->
  gaussian_product_law (n * d) (sample_row_tuple @^-1` A) =
  tuple_prod (fun=> gauss d) n A.
Proof.
move=> mA; rewrite gaussian_sample_lawE.
have -> : sample_row_tuple @^-1` A =
    (fun x => tuple_map (fun=> row_of_tuple d) (tuple_rows n d x)) @^-1` A.
  by apply/funext => x; rewrite /= sample_row_tupleE.
apply: (@sample_map_law (fun=> gaussian_law_probability) n d _ _
  (gauss d) (row_of_tuple d) A) => //.
by move=> B mB; rewrite gauss_gaussian_product_law //
  gaussian_product_law_tuple_prod.
Qed.

Lemma gaussian_sample_observation_law n d e (U : measurableType e)
    (mu : probability U R) (f : 'rV[RR]_d -> U)
    (A : set (n.-tuple U)) :
  measurable_fun setT f ->
  (forall B, measurable B -> mu B = gauss d (f @^-1` B)) ->
  measurable A ->
  gaussian_product_law (n * d)
    ((fun x => tuple_map (fun=> f) (sample_row_tuple x)) @^-1` A) =
  tuple_prod (fun=> mu) n A.
Proof.
move=> mf hf mA.
have mT : measurable_fun setT (@tuple_map _ _ _ _ (fun=> f) n).
  by apply: measurable_tuple_map => i.
have mTA : measurable (tuple_map (fun=> f) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: mT.
transitivity (tuple_prod (fun=> gauss d) n (tuple_map (fun=> f) @^-1` A)).
  exact: gaussian_sample_row_tuple_law mTA.
symmetry; exact: (tuple_prod_map (fun _ => mf) (fun _ => hf) mA).
Qed.

Lemma gaussian_sample_right_isometry_law n d p (J : 'M[RR]_(d, p))
    (A : set (n.-tuple 'rV[RR]_p)) :
  J^T *m J = 1%:M -> measurable A ->
  gaussian_product_law (n * d)
    ((fun x => tuple_map (fun _ (z : 'rV[RR]_d) => z *m J)
      (sample_row_tuple x)) @^-1` A) =
  tuple_prod (fun=> gauss p) n A.
Proof.
move=> JJ mA; apply: gaussian_sample_observation_law => //.
  by apply: measurable_mulmx => //; exact: measurable_cst.
by move=> B mB; symmetry; exact: gauss_orthogonal_law.
Qed.

Lemma gaussian_sample_matrix_law n d (A : set 'M[RR]_(n, d)) :
  measurable A ->
  gaussian_product_law (n * d)
    ((fun x => tuple_mx (sample_row_tuple x)) @^-1` A) =
  gauss (n * d) [set a | A (vec_mx a)].
Proof.
move=> mA.
have mT : measurable (@tuple_mx RR n d @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_tuple_mx.
rewrite -(@gauss_tuple_mx RR n d A mA).
exact: gaussian_sample_row_tuple_law mT.
Qed.

(* Joint coordinate blocks, including their independence within each row.
   Together with tuple_prod this retains the full sample joint law. *)
Lemma gaussian_row_coordinate_split_law p q
    (A : set ('rV[RR]_p * 'rV[RR]_q)) : measurable A ->
  gauss (p + q)
    ((fun z : 'rV[RR]_(p + q) => (lsubmx z, rsubmx z)) @^-1` A) =
  (gauss p \x gauss q)%E A.
Proof.
move=> mA.
have ms : measurable_fun setT
    (fun z : 'rV[RR]_(p + q) => (lsubmx z, rsubmx z)).
  by apply: measurable_fun_pair; [exact: measurable_lsubmx |
    exact: measurable_rsubmx].
have msA : measurable
    ((fun z : 'rV[RR]_(p + q) => (lsubmx z, rsubmx z)) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: ms.
rewrite (gauss_row_mx msA); congr ((gauss p \x gauss q)%E _).
by apply/funext => -[u v]; rewrite /= row_mxKl row_mxKr.
Qed.

Lemma gaussian_sample_coordinate_split_law n p q
    (A : set (n.-tuple ('rV[RR]_p * 'rV[RR]_q))) : measurable A ->
  gaussian_product_law (n * (p + q))
    ((fun x => tuple_map
      (fun _ (z : 'rV[RR]_(p + q)) => (lsubmx z, rsubmx z))
      (sample_row_tuple x)) @^-1` A) =
  tuple_prod (fun=> (gauss p \x gauss q)%E) n A.
Proof.
move=> mA; apply: gaussian_sample_observation_law => //.
  by apply: measurable_fun_pair; [exact: measurable_lsubmx |
    exact: measurable_rsubmx].
by move=> B mB; symmetry; exact: gaussian_row_coordinate_split_law.
Qed.

(* Independent blocks of sample rows, for the main and reserve samples. *)
Definition gaussian_row_tuple_split a b d
    (x : (a + b).-tuple 'rV[RR]_d) :=
  ([tuple tnth x (lshift b i) | i < a],
   [tuple tnth x (rshift a i) | i < b]).

Lemma measurable_gaussian_row_tuple_split a b d :
  measurable_fun setT (@gaussian_row_tuple_split a b d).
Proof.
apply: measurable_fun_pair.
- apply/measurable_fun_tnthP => i.
  apply: (eq_measurable_fun
    (fun x : (a + b).-tuple 'rV[RR]_d => tnth x (lshift b i))).
    by move=> x _; rewrite /gaussian_row_tuple_split /= tnth_mktuple.
  exact: measurable_tnth.
- apply/measurable_fun_tnthP => i.
  apply: (eq_measurable_fun
    (fun x : (a + b).-tuple 'rV[RR]_d => tnth x (rshift a i))).
    by move=> x _; rewrite /gaussian_row_tuple_split /= tnth_mktuple.
  exact: measurable_tnth.
Qed.

Lemma gaussian_row_tuple_split_cat a b d
    (u : a.-tuple 'rV[RR]_d) (v : b.-tuple 'rV[RR]_d) :
  gaussian_row_tuple_split [tuple of u ++ v] = (u, v).
Proof.
rewrite /gaussian_row_tuple_split; congr pair;
  apply: eq_from_tnth => i; rewrite tnth_mktuple.
- exact: tnth_lshift.
- exact: tnth_rshift.
Qed.

Lemma gaussian_row_tuple_cat_law a b d
    (A : set ((a + b).-tuple 'rV[RR]_d)) : measurable A ->
  tuple_prod (fun=> gauss d) (a + b) A =
  (tuple_prod (fun=> gauss d) a \x tuple_prod (fun=> gauss d) b)%E
    ((fun p : a.-tuple 'rV[RR]_d * b.-tuple 'rV[RR]_d =>
      [tuple of p.1 ++ p.2]) @^-1` A).
Proof.
move=> mA.
have mF : measurable_fun setT
    (fun z : (a + b).-tuple 'rV[RR]_d => (\1_A z : R)%:E).
  by apply/measurable_EFinP; exact: measurable_indic.
have F0 z : (0 <= (\1_A z : R)%:E)%E by rewrite lee_fin indicE.
have mFc : measurable_fun setT
    (fun p : a.-tuple 'rV[RR]_d * b.-tuple 'rV[RR]_d =>
      (\1_A [tuple of p.1 ++ p.2] : R)%:E).
  apply: measurableT_comp mF _; exact: measurable_tuple_cat.
have mCA : measurable
    ((fun p : a.-tuple 'rV[RR]_d * b.-tuple 'rV[RR]_d =>
      [tuple of p.1 ++ p.2]) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_tuple_cat.
transitivity (\int[tuple_prod (fun=> gauss d) (a + b)]_z (\1_A z)%:E)%E.
  by rewrite integral_indic // setIT.
rewrite ge0_integral_tuple_prod_cat //.
transitivity (\int[tuple_prod (fun=> gauss d) a \x
    tuple_prod (fun=> gauss d) b]_p
      (\1_A [tuple of p.1 ++ p.2])%:E)%E.
  symmetry; exact: (fubini_tonelli1 _ mFc (fun p => F0 _)).
have -> : (fun p : a.-tuple 'rV[RR]_d * b.-tuple 'rV[RR]_d =>
    (\1_A [tuple of p.1 ++ p.2] : R)%:E) =
    (fun p => (\1_((fun q : a.-tuple 'rV[RR]_d * b.-tuple 'rV[RR]_d =>
      [tuple of q.1 ++ q.2]) @^-1` A) p : R)%:E).
  by apply/funext => p; rewrite !indicE.
by rewrite integral_indic // setIT.
Qed.

Lemma gaussian_sample_row_split_law a b d
    (A : set (a.-tuple 'rV[RR]_d * b.-tuple 'rV[RR]_d)) : measurable A ->
  gaussian_product_law ((a + b) * d)
    ((fun x => gaussian_row_tuple_split (sample_row_tuple x)) @^-1` A) =
  (tuple_prod (fun=> gauss d) a \x tuple_prod (fun=> gauss d) b)%E A.
Proof.
move=> mA.
have msA : measurable (@gaussian_row_tuple_split a b d @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_gaussian_row_tuple_split.
transitivity (tuple_prod (fun=> gauss d) (a + b)
    (@gaussian_row_tuple_split a b d @^-1` A)).
  exact: gaussian_sample_row_tuple_law msA.
rewrite gaussian_row_tuple_cat_law //.
congr ((tuple_prod (fun=> gauss d) a \x tuple_prod (fun=> gauss d) b)%E _).
by apply/funext => -[u v]; rewrite /= gaussian_row_tuple_split_cat.
Qed.

(* The inverse uses the frozen row-major layout k = i*d+j explicitly. *)
Lemma sample_flat_dimension_pos n d (k : 'I_(n * d)) : (0 < d)%N.
Proof.
have h : (0 < n * d)%N := leq_ltn_trans (leq0n k) (ltn_ord k).
by move: h; rewrite muln_gt0 => /andP[_].
Qed.

Lemma sample_flat_row_bound n d (k : 'I_(n * d)) : (k %/ d < n)%N.
Proof. by rewrite ltn_divLR ?(sample_flat_dimension_pos k) //; exact: ltn_ord. Qed.

Lemma sample_flat_col_bound n d (k : 'I_(n * d)) : (k %% d < d)%N.
Proof. by rewrite ltn_mod; exact: (sample_flat_dimension_pos k). Qed.

Definition sample_flat_row n d (k : 'I_(n * d)) : 'I_n :=
  Ordinal (sample_flat_row_bound k).
Definition sample_flat_col n d (k : 'I_(n * d)) : 'I_d :=
  Ordinal (sample_flat_col_bound k).

Lemma sample_flat_rowK n d (i : 'I_n) (j : 'I_d) :
  sample_flat_row (row_index i j) = i.
Proof.
apply: val_inj => /=.
have d0 : (0 < d)%N := sample_flat_dimension_pos (row_index i j).
by rewrite divnMDl // divn_small ?ltn_ord // addn0.
Qed.

Lemma sample_flat_colK n d (i : 'I_n) (j : 'I_d) :
  sample_flat_col (row_index i j) = j.
Proof. by apply: val_inj => /=; rewrite modnMDl modn_small. Qed.

Lemma sample_flat_indicesK n d (k : 'I_(n * d)) :
  row_index (sample_flat_row k) (sample_flat_col k) = k.
Proof. by apply: val_inj => /=; rewrite -divn_eq. Qed.

Definition sample_of_row_tuple n d (x : n.-tuple 'rV[RR]_d) :
    paper_main_sample n d :=
  [tuple tnth x (sample_flat_row k) 0 (sample_flat_col k) | k < n * d].

Lemma sample_row_tuple_entry n d (x : paper_main_sample n d)
    (i : 'I_n) (j : 'I_d) :
  tnth (sample_row_tuple x) i 0 j = tnth x (row_index i j).
Proof.
by rewrite /sample_row_tuple tnth_mktuple paper_main_point_row
  /tuple_point /tuple_rows !mxE !tnth_mktuple.
Qed.

Lemma sample_of_row_tupleK n d (x : n.-tuple 'rV[RR]_d) :
  sample_row_tuple (sample_of_row_tuple x) = x.
Proof.
apply: eq_from_tnth => i; apply/rowP => j.
by rewrite sample_row_tuple_entry /sample_of_row_tuple tnth_mktuple
  sample_flat_rowK sample_flat_colK.
Qed.

Lemma sample_row_tupleK n d (x : paper_main_sample n d) :
  sample_of_row_tuple (sample_row_tuple x) = x.
Proof.
by apply: eq_from_tnth => k; rewrite /sample_of_row_tuple tnth_mktuple
  sample_row_tuple_entry sample_flat_indicesK.
Qed.

Lemma measurable_sample_of_row_tuple n d :
  measurable_fun [set: n.-tuple 'rV[RR]_d] (@sample_of_row_tuple n d).
Proof.
apply/measurable_fun_tnthP => k.
apply: (eq_measurable_fun (fun x : n.-tuple 'rV[RR]_d =>
  tnth x (sample_flat_row k) 0 (sample_flat_col k))).
  by move=> x _; rewrite /sample_of_row_tuple /= tnth_mktuple.
have me : measurable_fun [set: 'rV[RR]_d]
    (fun z => z 0 (sample_flat_col k)) := measurable_mxentry _ _.
exact: measurableT_comp me (measurable_tnth (sample_flat_row k)).
Qed.

Lemma gaussian_row_tuple_flat_law n d (A : set (paper_main_sample n d)) :
  measurable A ->
  tuple_prod (fun=> gauss d) n (@sample_of_row_tuple n d @^-1` A) =
  gaussian_product_law (n * d) A.
Proof.
move=> mA.
have miA : measurable (@sample_of_row_tuple n d @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_sample_of_row_tuple.
rewrite -(gaussian_sample_row_tuple_law miA).
congr (gaussian_product_law (n * d) _).
by apply/funext => x; rewrite /= sample_row_tupleK.
Qed.

Definition sample_right_isometry n d p (J : 'M[RR]_(d, p))
    (x : paper_main_sample n d) : paper_main_sample n p :=
  sample_of_row_tuple
    (tuple_map (fun _ (z : 'rV[RR]_d) => z *m J) (sample_row_tuple x)).

Lemma sample_right_isometry_point n d p (J : 'M[RR]_(d, p))
    (x : paper_main_sample n d) (i : 'I_n) :
  (paper_main_point (sample_right_isometry J x) i)^T =
  (paper_main_point x i)^T *m J.
Proof.
have hi := congr1 (fun z : n.-tuple 'rV[RR]_p => tnth z i)
  (sample_of_row_tupleK
    (tuple_map (fun _ (z : 'rV[RR]_d) => z *m J) (sample_row_tuple x))).
move: hi.
by rewrite /sample_row_tuple /tuple_map !tnth_mktuple.
Qed.

Lemma measurable_sample_right_isometry n d p (J : 'M[RR]_(d, p)) :
  measurable_fun [set: paper_main_sample n d] (sample_right_isometry J).
Proof.
apply: measurableT_comp; first exact: measurable_sample_of_row_tuple.
apply: measurableT_comp; last exact: measurable_sample_row_tuple.
apply: measurable_tuple_map => i.
by apply: measurable_mulmx => //; exact: measurable_cst.
Qed.

Lemma gaussian_flat_right_isometry_law n d p (J : 'M[RR]_(d, p))
    (A : set (paper_main_sample n p)) :
  J^T *m J = 1%:M -> measurable A ->
  gaussian_product_law (n * d) (sample_right_isometry J @^-1` A) =
  gaussian_product_law (n * p) A.
Proof.
move=> JJ mA.
have miA : measurable (@sample_of_row_tuple n p @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_sample_of_row_tuple.
rewrite -(gaussian_row_tuple_flat_law mA).
exact: gaussian_sample_right_isometry_law JJ miA.
Qed.
