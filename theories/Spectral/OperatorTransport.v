(* Transport of public bilinear and Loewner bounds to the internal operator
   norm matrix_operator_norm of Matrix.OperatorDefinitions, for the public matrices
   'M[R]_N, N = n + 1, through paper_main_matrix_from_public.

   - Box to bilinear bound (paper_main_cone_opnorm_of_loewner). For symmetric
     Z with -b I <= Z <= b I and b >= 0, (u^T Z v)^2 <= b^2 |u|^2 |v|^2
     (paper_main_cone_opnorm_le Z b), by opnorm_symP of
     GaussianAnalysis.matrix.opnorm.
   - Vector transport. pmmo_column x is the public column of the internal
     vector x : vector n. Its squared norm is |x|^2 (pmmo_column_norm), and
     the internal action of paper_main_matrix_from_public n B is B times the
     column (pmmo_column_action).
   - Operator norm (paper_main_matrix_operator_transport). If
     paper_main_cone_opnorm_le B b and b >= 0, then
     matrix_operator_norm n (paper_main_matrix_from_public n B) <= b. Proof:
     Matrix.OperatorNorm.matrix_operator_norm_upper, with y = B x tested against x.
   - Consequences:
     - the Loewner box gives the same bound
       (paper_main_matrix_operator_loewner);
     - a unit-Frobenius B in paper_main_head_cone_sphere kappa, 1 <= kappa,
       has internal operator norm at most kappa / sqrt (INR N), through the
       Loewner box of Geometry.HeadSpectral
       (paper_main_matrix_operator_cone_sphere).
   This is a deterministic bridge, not a probabilistic estimate. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ring_tactic arithmetic_tactic sesquilinear.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Matrix.Definitions Matrix.EntriesAndLinearMaps Matrix.OperatorDefinitions
  Matrix.OperatorNorm PaperMainDefinitions Geometry.Psd Geometry.Gram
  Geometry.Homogeneous Geometry.Separation Geometry.HeadFrobenius
  Geometry.HeadCorrection Geometry.HeadCoefficients Geometry.HeadFeature
  Geometry.HeadSpectral Geometry.HeadWidth Spectral.Transport
  Gordon.ProcessCovariance Gaussian.FeatureCoordinates
  Spectral.SymmetricBilinear Cone.ConditionOperator
  Spectral.SymmetricDiagonalization.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Bilinear.
Variable d : nat.
Implicit Types (Z : 'M[R]_d).

(* -b I <= Z <= b I gives the bilinear bound. *)
Theorem paper_main_cone_opnorm_of_loewner Z (b : R) :
  paper_main_symmetric Z -> 0 <= b ->
  paper_main_loewner_le ((- b) *: 1%:M) Z -> paper_main_loewner_le Z (b *: 1%:M) ->
  paper_main_cone_opnorm_le Z b.
Proof.
move=> _ Hb Hlo Hup; apply/paper_main_cone_opnorm_leP; rewrite ger0_norm //.
have [Zs Zb] := proj1 (paper_main_loewner_boxP Z b) (conj Hlo Hup).
exact/(opnorm_symP Zs Hb).
Qed.

End Bilinear.

Section Transport.
Variable n : nat.
Local Notation N := (S n).

(* The public column of an internal vector. *)
Definition pmmo_column (x : vector n) : 'cV[R]_N :=
  paper_main_symmetric_column n (vector_entry n x).

Lemma pmmo_column_norm (x : vector n) :
  ((pmmo_column x)^T *m pmmo_column x) 0 0 = `|x| ^+ 2.
Proof.
rewrite /pmmo_column paper_main_symmetric_column_norm -RpowE vector_norm_squared.
rewrite paper_main_feature_coordinate_sum /paper_main_gordon_dot.
by apply: finite_sum_ext => i _; rewrite RpowE expr2 RmultE.
Qed.

Lemma pmmo_column_action (B : 'M[R]_N) (x : vector n) :
  pmmo_column (matrix_action n (paper_main_matrix_from_public n B) x) = B *m pmmo_column x.
Proof.
apply/matrixP => i j; rewrite [j]ord1 !mxE.
have Hi : (i <= n)%coq_nat by have /ssrnat.ltP := ltn_ord i; lia.
rewrite (matrix_action_entry _ _ _ _ Hi) paper_main_matrix_coordinate_sum.
by apply: eq_bigr => k _; rewrite paper_main_matrix_from_public_entry !mxE RmultE.
Qed.

(* The bilinear bound bounds the internal operator norm. *)
Theorem paper_main_matrix_operator_transport (B : 'M[R]_N) (b : R) :
  0 <= b -> paper_main_cone_opnorm_le B b ->
  matrix_operator_norm n (paper_main_matrix_from_public n B) <= b.
Proof.
move=> Hb HB; apply/RleP; apply: matrix_operator_norm_upper => x /RleP Hx.
apply/RleP.
set X := pmmo_column x.
set Y := pmmo_column (matrix_action n (paper_main_matrix_from_public n B) x).
have HY : (Y^T *m Y) 0 0 = `|matrix_action n (paper_main_matrix_from_public n B) x| ^+ 2.
  exact: pmmo_column_norm.
have HX : (X^T *m X) 0 0 = `|x| ^+ 2 by exact: pmmo_column_norm.
have HYB : Y = B *m X by rewrite /Y pmmo_column_action.
have H := HB Y X.
have HYY : (Y^T *m B *m X) 0 0 = (Y^T *m Y) 0 0 by rewrite -mulmxA -HYB.
rewrite HYY HX HY in H.
set r := `|matrix_action n (paper_main_matrix_from_public n B) x| in H *.
have Hr0 : 0 <= r by exact: normr_ge0.
have Hx0 : 0 <= `|x| by exact: normr_ge0.
have Hx1 : `|x| <= 1 by exact: Hx.
have Hx2 : `|x| ^+ 2 <= 1 by nra.
case: (eqVneq r 0) => Hr; first by rewrite Hr.
have Hrp : 0 < r ^+ 2 by rewrite exprn_gt0 // lt0r Hr.
have Hr2 : r ^+ 2 <= b ^+ 2.
  have HB2 : 0 <= b ^+ 2 by exact: sqr_ge0.
  have H3 : b ^+ 2 * (r ^+ 2 * `|x| ^+ 2) <= b ^+ 2 * r ^+ 2.
    apply: ler_wpM2l => //; rewrite -[X in _ <= X]mulr1.
    by apply: ler_wpM2l => //; exact: ltW.
  have H4 := le_trans H H3.
  rewrite expr2 (mulrC (b ^+ 2)) in H4.
  by rewrite (ler_pM2l Hrp) in H4.
have := ler_wsqrtr Hr2.
by rewrite !sqrtr_sqr (ger0_norm Hr0) (ger0_norm Hb).
Qed.

Corollary paper_main_matrix_operator_loewner (B : 'M[R]_N) (b : R) :
  paper_main_symmetric B -> 0 <= b ->
  paper_main_loewner_le ((- b) *: 1%:M) B -> paper_main_loewner_le B (b *: 1%:M) ->
  matrix_operator_norm n (paper_main_matrix_from_public n B) <= b.
Proof.
move=> HB Hb Hlo Hup; apply: paper_main_matrix_operator_transport => //.
exact: paper_main_cone_opnorm_of_loewner.
Qed.

(* A PSD matrix is above -b I for every b >= 0. *)
Lemma pmmo_psd_lower (B : 'M[R]_N) (b : R) :
  paper_main_psd B -> 0 <= b -> paper_main_loewner_le ((- b) *: 1%:M) B.
Proof.
move=> [HBs HB] Hb; split.
  apply: pmh_symmetricB => //.
  by apply: paper_main_symmetric_scale; exact: pmh_symmetric_id.
move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id.
have := HB v; have := pmh_vec_sqr_ge0 _ v; nra.
Qed.

(* A unit element of the bounded-condition cone. *)
Theorem paper_main_matrix_operator_cone_sphere (kappa : R) (B : 'M[R]_N) :
  1 <= kappa -> paper_main_head_cone_sphere kappa B ->
  matrix_operator_norm n (paper_main_matrix_from_public n B) <= kappa / Num.sqrt N%:R.
Proof.
move=> Hk [Hcond HF].
have [Hlow Hup] := paper_main_head_condition_box N B kappa (ltn0Sn n) Hcond HF.
have Hs : 0 < Num.sqrt (N%:R : R) by rewrite sqrtr_gt0 ltr0n.
have Hk0 : 0 < kappa by apply: lt_le_trans Hk; exact: ltr01.
have Hb : 0 <= kappa / Num.sqrt N%:R by rewrite divr_ge0 // ltW.
have HBs : paper_main_symmetric B.
  case: Hup => HS _ i j; have := HS i j; rewrite !mxE (eq_sym j i); lra.
have Hlo : paper_main_loewner_le ((- (kappa / Num.sqrt N%:R)) *: 1%:M) B.
  split.
    apply: pmh_symmetricB => //.
    by apply: paper_main_symmetric_scale; exact: pmh_symmetric_id.
  move=> v; case: Hlow => _ /(_ v).
  rewrite !pms_formB !paper_main_form_scale !pmh_form_id => H.
  have Hv := pmh_vec_sqr_ge0 _ v.
  have Hc : 0 <= (kappa * Num.sqrt N%:R)^-1 by rewrite invr_ge0 mulr_ge0 // ltW.
  nra.
exact: (paper_main_matrix_operator_loewner B _ HBs Hb Hlo Hup).
Qed.

(* The same bound in Stdlib form, as in the operator premise of the public
   feature comparison. *)
Corollary paper_main_matrix_operator_cone_sphere_INR (kappa : R) (B : 'M[R]_N) :
  Rle 1 kappa -> paper_main_head_cone_sphere kappa B ->
  Rle (matrix_operator_norm n (paper_main_matrix_from_public n B)) (Rdiv kappa (sqrt (INR N))).
Proof.
move=> /RleP Hk HB; apply/RleP; rewrite RdivE RsqrtE INRE.
exact: paper_main_matrix_operator_cone_sphere.
Qed.

End Transport.
