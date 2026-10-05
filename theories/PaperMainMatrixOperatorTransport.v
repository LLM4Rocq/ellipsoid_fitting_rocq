(* Transport of public bilinear and Loewner bounds to the internal operator
   norm matrix_operator_norm of OperatorDefinitions, for the public matrices
   'M[R]_N, N = n + 1, through paper_main_matrix_from_public.

   - Box to bilinear bound (paper_main_cone_opnorm_of_loewner). For symmetric
     Z with -b I <= Z <= b I and b >= 0, (u^T Z v)^2 <= b^2 |u|^2 |v|^2
     (paper_main_cone_opnorm_le Z b). For every lam, the two Loewner bounds
     at lam u + v and -lam u + v give 0 <= b |u|^2 lam^2 - 2 (u^T Z v) lam +
     b |v|^2, and this quadratic in lam forces the bound. No eigenvalues.
   - Vector transport. pmmo_column x is the public column of the internal
     vector x : vector n. Its squared norm is |x|^2 (pmmo_column_norm), and
     the internal action of paper_main_matrix_from_public n B is B times the
     column (pmmo_column_action).
   - Operator norm (paper_main_matrix_operator_transport). If
     paper_main_cone_opnorm_le B b and b >= 0, then
     matrix_operator_norm n (paper_main_matrix_from_public n B) <= b. Proof:
     OperatorBounds.matrix_operator_norm_upper, with y = B x tested against x.
   - Consequences:
     - the Loewner box gives the same bound
       (paper_main_matrix_operator_loewner);
     - a PSD B with |B|_F = 1 has internal operator norm at most 1
       (paper_main_matrix_operator_psd_frobenius);
     - a unit-Frobenius B in paper_main_head_cone_sphere kappa, 1 <= kappa,
       has internal operator norm at most kappa / sqrt (INR N), through the
       Loewner box of PaperMainGeometryHeadSpectral
       (paper_main_matrix_operator_cone_sphere).
   This is a deterministic bridge, not a probabilistic estimate. Nothing
   from the paper is assumed. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums MatrixDefinitions MatrixCoordinates
  OperatorDefinitions OperatorBounds PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryGram PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadCoefficients PaperMainGeometryHeadFeature
  PaperMainGeometryHeadSpectral PaperMainGeometryHeadWidth PaperMainMatrixTransport
  PaperMainGordonProcessCovariance PaperMainGaussianFeatureCoordinates
  PaperMainSymmetricBilinear PaperMainConeConditionOperator.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Bilinear.
Variable d : nat.
Implicit Types (Z : 'M[R]_d) (u v x y : 'cV[R]_d).

Lemma pmmo_bilinD_l Z x x' y :
  ((x + x')^T *m Z *m y) 0 0 = (x^T *m Z *m y) 0 0 + (x'^T *m Z *m y) 0 0.
Proof. by rewrite [(x + x')^T]linearD /= !mulmxDl mxE. Qed.

Lemma pmmo_bilinD_r Z x y y' :
  (x^T *m Z *m (y + y')) 0 0 = (x^T *m Z *m y) 0 0 + (x^T *m Z *m y') 0 0.
Proof. by rewrite mulmxDr mxE. Qed.

Lemma pmmo_bilinZ_l Z (c : R) x y :
  ((c *: x)^T *m Z *m y) 0 0 = c * (x^T *m Z *m y) 0 0.
Proof. by rewrite [(c *: x)^T]linearZ /= -!scalemxAl mxE. Qed.

Lemma pmmo_bilinZ_r Z (c : R) x y :
  (x^T *m Z *m (c *: y)) 0 0 = c * (x^T *m Z *m y) 0 0.
Proof. by rewrite -scalemxAr mxE. Qed.

Lemma pmmo_form_comb Z u v (lam : R) :
  ((lam *: u + v)^T *m Z *m (lam *: u + v)) 0 0 =
  lam * lam * (u^T *m Z *m u) 0 0 + lam * (u^T *m Z *m v) 0 0 +
  lam * (v^T *m Z *m u) 0 0 + (v^T *m Z *m v) 0 0.
Proof.
rewrite pmmo_bilinD_l !pmmo_bilinD_r !pmmo_bilinZ_l !pmmo_bilinZ_r; ring.
Qed.

Lemma pmmo_norm_comb u v (lam : R) :
  ((lam *: u + v)^T *m (lam *: u + v)) 0 0 =
  lam * lam * (u^T *m u) 0 0 + 2%:R * lam * (u^T *m v) 0 0 + (v^T *m v) 0 0.
Proof.
have := pmmo_form_comb 1%:M u v lam; rewrite !mulmx1 => ->.
by rewrite (paper_main_inner_sym _ v u); ring.
Qed.

(* -b I <= Z <= b I gives the bilinear bound. *)
Theorem paper_main_cone_opnorm_of_loewner Z (b : R) :
  paper_main_symmetric Z -> 0 <= b ->
  paper_main_loewner_le ((- b) *: 1%:M) Z -> paper_main_loewner_le Z (b *: 1%:M) ->
  paper_main_cone_opnorm_le Z b.
Proof.
move=> HZ Hb [_ Hlo] [_ Hup] u v.
have HZt : Z^T = Z by exact/paper_main_symmetricP.
have Ha := pmh_vec_sqr_ge0 _ u; have Hc := pmh_vec_sqr_ge0 _ v.
have Hcross := paper_main_cross_sym _ Z v u HZt.
have Hq : forall lam : R, 0 <= b * (u^T *m u) 0 0 * (lam * lam) -
    2%:R * (u^T *m Z *m v) 0 0 * lam + b * (v^T *m v) 0 0.
  move=> lam.
  have H1 := Hup (lam *: u + v).
  have H2 := Hlo ((- lam) *: u + v).
  rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE in H1.
  rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE in H2.
  rewrite pmmo_form_comb pmmo_norm_comb Hcross in H1.
  rewrite pmmo_form_comb pmmo_norm_comb Hcross in H2.
  lra.
set a := (u^T *m u) 0 0 in Ha Hq *; set c := (v^T *m v) 0 0 in Hc Hq *.
set p := (u^T *m Z *m v) 0 0 in Hq *.
have Hbc : 0 <= b ^+ 2 * (a * c) by rewrite mulr_ge0 ?sqr_ge0 ?mulr_ge0.
case: (eqVneq (b * a) 0) => Hba.
  have Hp : p = 0.
    apply/eqP; apply/negP => /negP Hp0.
    have H2p : 2%:R * p != 0 by rewrite mulf_neq0 // pnatr_eq0.
    have := Hq ((b * c + 1) / (2%:R * p)).
    rewrite Hba mul0r add0r.
    have -> : 2%:R * p * ((b * c + 1) / (2%:R * p)) = b * c + 1.
      by rewrite mulrCA (mulfV H2p) mulr1.
    lra.
  by rewrite Hp expr0n /=.
have Hba' : 0 < b * a by rewrite lt0r Hba mulr_ge0.
have Hl : b * a * (p / (b * a)) = p by rewrite mulrCA (mulfV Hba) mulr1.
have H0 := Hq (p / (b * a)).
set l := p / (b * a) in Hl H0.
have H1 : 0 <= b * a * (b * a * (l * l) - 2%:R * p * l + b * c).
  by apply: mulr_ge0 => //; exact: ltW.
have E : b * a * (b * a * (l * l) - 2%:R * p * l + b * c) =
    (b * a * l) * (b * a * l) - 2%:R * p * (b * a * l) + b ^+ 2 * (a * c) by ring.
rewrite E Hl in H1; lra.
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

(* A PSD B with |B|_F = 1 is below I. *)
Lemma pmmo_psd_frobenius_upper (B : 'M[R]_N) :
  paper_main_psd B -> paper_main_frobenius B = 1 -> paper_main_loewner_le B (1 *: 1%:M).
Proof.
move=> [HBs HB] HF; split.
  apply: pmh_symmetricB => //.
  by apply: paper_main_symmetric_scale; exact: pmh_symmetric_id.
move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id mul1r subr_ge0.
have H := pmh_pairing_frobenius_bound _ B (v *m v^T).
rewrite paper_main_pairing_outer HF mul1r in H.
have HF2 : paper_main_frobenius (v *m v^T) = (v^T *m v) 0 0.
  rewrite /paper_main_frobenius pmsb_pairing_outer_outer -expr2 sqrtr_sqr.
  by rewrite ger0_norm //; exact: pmh_vec_sqr_ge0.
by rewrite HF2 in H; apply: le_trans (ler_norm _) H.
Qed.

Theorem paper_main_matrix_operator_psd_frobenius (B : 'M[R]_N) :
  paper_main_psd B -> paper_main_frobenius B = 1 ->
  matrix_operator_norm n (paper_main_matrix_from_public n B) <= 1.
Proof.
move=> HB HF; apply: paper_main_matrix_operator_loewner => //.
- by case: HB.
- exact: pmmo_psd_lower.
- exact: pmmo_psd_frobenius_upper.
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
