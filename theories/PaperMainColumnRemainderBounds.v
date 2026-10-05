(* Column rank-one and diagonal energy bounds for the NB remainder. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryGram PaperMainGeometryHomogeneous
  PaperMainGeometryHeadCoefficients PaperMainGeometryHeadFrobenius PaperMainConeConditionOperator
  PaperMainOrthogonalMatrixBounds PaperMainSquarefreeEdgeLower PaperMainColumnRemainder
  PaperMainMatrixFamilyCauchy PaperMainMatrixFamilyCauchyPowers.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma pmcr_rankone_outer N (C : finType) (X : 'I_N -> C -> R) c :
  pmcr_rankone N C X c = (\col_i X i c) *m (\col_i X i c)^T.
Proof. apply/matrixP=>i j; by rewrite /pmcr_rankone !mxE big_ord1 !mxE. Qed.

Lemma pmcr_rankone_symmetric N (C : finType) (X : 'I_N -> C -> R) c :
  (pmcr_rankone N C X c)^T = pmcr_rankone N C X c.
Proof. apply/matrixP=>i j; by rewrite /pmcr_rankone !mxE mulrC. Qed.

Lemma pmcr_diagonal_symmetric N (C : finType) (X : 'I_N -> C -> R) c :
  (pmcr_diagonal N C X c)^T = pmcr_diagonal N C X c.
Proof. exact: tr_diag_mx. Qed.

Lemma pmcr_rankone_positive N (C : finType) (X : 'I_N -> C -> R) c (u : 'cV[R]_N) :
  0 <= (u^T *m pmcr_rankone N C X c *m u) 0 0.
Proof.
rewrite pmcr_rankone_outer -paper_main_quadratic_formE.
exact: (proj2 (paper_main_psd_rank1 N (\col_i X i c))).
Qed.

Lemma pmcr_column_norm_nonnegative N (C : finType) (X : 'I_N -> C -> R) c :
  0 <= pmcr_column_norm N C X c.
Proof. apply: sumr_ge0=>i _; exact: sqr_ge0. Qed.

Lemma pmcr_rankone_action N (C : finType) (X : 'I_N -> C -> R) c (u : 'cV[R]_N) :
  ((pmcr_rankone N C X c *m u)^T *m (pmcr_rankone N C X c *m u)) 0 0 =
  pmcr_column_norm N C X c * (u^T *m pmcr_rankone N C X c *m u) 0 0.
Proof.
rewrite trmx_mul pmcr_rankone_symmetric !mulmxA.
rewrite -(mulmxA u^T (pmcr_rankone N C X c) (pmcr_rankone N C X c)) pmcr_rankone_square -scalemxAr -scalemxAl mxE.
by [].
Qed.

Theorem pmcr_rankone_energy_bound N (C : finType) (X : 'I_N -> C -> R) U :
  0 <= U -> (forall c, pmcr_column_norm N C X c <= U) ->
  (forall u : 'cV[R]_N, (u^T *m (\sum_c pmcr_rankone N C X c) *m u) 0 0 <= U*(u^T *m u) 0 0) ->
  pmfc_energy_bound C N (pmcr_rankone N C X) U.
Proof.
move=>HU HQ HG; split=>// u.
apply: le_trans (_ : U*(u^T *m (\sum_c pmcr_rankone N C X c) *m u) 0 0 <= _).
- rewrite /pmfc_energy mulmx_sumr mulmx_suml summxE mulr_sumr.
  apply: ler_sum=>c _; rewrite pmcr_rankone_action.
  apply: ler_wpM2r; first exact: pmcr_rankone_positive.
  exact: HQ.
- rewrite expr2 -mulrA; apply: ler_wpM2l=>//; exact: HG.
Qed.

Theorem pmcr_diagonal_opbound N (C : finType) (X : 'I_N -> C -> R) c m :
  0 <= m -> (forall i, (X i c)^+2 <= m) ->
  pmlo_opb N (pmcr_diagonal N C X c) m.
Proof.
move=>Hm HX; apply: paper_main_opnorm_to_action=>//.
apply: paper_main_diagonal_opnorm=>// i.
by rewrite mxE ger0_norm ?sqr_ge0 //; exact: HX.
Qed.

Lemma pmcr_rankone_form_upper N (C : finType) (X : 'I_N -> C -> R) c (u : 'cV[R]_N) :
  (u^T *m pmcr_rankone N C X c *m u) 0 0 <=
  pmcr_column_norm N C X c*(u^T *m u) 0 0.
Proof.
rewrite pmcr_rankone_outer paper_main_form_rank1E.
have H := pmco_vec_cauchy_schwarz N u (\col_i X i c).
have E : (((\col_i X i c) : 'cV[R]_N)^T *m (\col_i X i c)) 0 0 = pmcr_column_norm N C X c.
{ rewrite pmh_vec_dot /pmcr_column_norm; apply: eq_bigr=>i _; by rewrite !mxE expr2. }
by rewrite E mulrC in H.
Qed.

Theorem pmcr_rankone_opbound N (C : finType) (X : 'I_N -> C -> R) c U :
  0 <= U -> pmcr_column_norm N C X c <= U -> pmlo_opb N (pmcr_rankone N C X c) U.
Proof.
move=>HU HQ; split=>// u; rewrite pmcr_rankone_action.
have HQ0 := pmcr_column_norm_nonnegative N C X c.
apply: le_trans (_ : pmcr_column_norm N C X c*(pmcr_column_norm N C X c*(u^T *m u) 0 0) <= _).
- apply: ler_wpM2l=>//; exact: pmcr_rankone_form_upper.
- rewrite mulrA -expr2; apply: ler_wpM2r; first exact: pmh_vec_sqr_ge0.
  by rewrite ler_sqr ?nnegrE.
Qed.

Lemma pmcr_diagonal_energy_formula N (C : finType) (X : 'I_N -> C -> R) (u : 'cV[R]_N) :
  pmfc_energy C N (pmcr_diagonal N C X) u =
  \sum_(i<N) (\sum_c ((X i c)^+2)^+2)*(u i 0)^+2.
Proof.
rewrite /pmfc_energy.
have E c : ((pmcr_diagonal N C X c *m u)^T *m (pmcr_diagonal N C X c *m u)) 0 0 =
  \sum_(i<N) ((X i c)^+2)^+2*(u i 0)^+2.
{ rewrite pmh_vec_dot; apply: eq_bigr=>i _.
  rewrite /pmcr_diagonal paper_main_diagonal_vector_entry mxE; ring. }
under eq_bigr do rewrite E.
rewrite exchange_big; apply: eq_bigr=>i _; by rewrite mulr_suml.
Qed.

Theorem pmcr_diagonal_energy_bound N (C : finType) (X : 'I_N -> C -> R) m U b :
  0 <= m -> 0 <= b -> m*U <= b^+2 ->
  (forall i c, (X i c)^+2 <= m) -> (forall i, \sum_c (X i c)^+2 <= U) ->
  pmfc_energy_bound C N (pmcr_diagonal N C X) b.
Proof.
move=>Hm Hb Hmb HX HD; split=>// u.
rewrite pmcr_diagonal_energy_formula pmh_vec_dot mulr_sumr.
apply: ler_sum=>i _; rewrite -expr2.
apply: ler_wpM2r; first exact: sqr_ge0.
apply: le_trans (_ : m*(\sum_c (X i c)^+2) <= _).
- rewrite mulr_sumr; apply: ler_sum=>c _.
  rewrite [leLHS]expr2; apply: ler_wpM2r; first exact: sqr_ge0.
  exact: HX.
- apply: le_trans (_ : m*U <= _)=>//.
  by apply: ler_wpM2l.
Qed.

Theorem pmcr_column_base_bounds N (C : finType) (X : 'I_N -> C -> R) U m b :
  0 <= U -> 0 <= m -> 0 <= b -> m <= U -> b <= U -> m*U <= b^+2 ->
  (forall c, pmcr_column_norm N C X c <= U) ->
  (forall i c, (X i c)^+2 <= m) ->
  (forall i, \sum_c (X i c)^+2 <= U) ->
  (forall u : 'cV[R]_N, (u^T *m (\sum_c pmcr_rankone N C X c) *m u) 0 0 <= U*(u^T *m u) 0 0) ->
  (forall c, pmlo_opb N (pmcr_rankone N C X c) U /\
     pmlo_opb N (pmcr_diagonal N C X c) m /\
     pmlo_opb N (pmcr_rankone N C X c-pmcr_diagonal N C X c) (2*U)) /\
  pmfc_energy_bound C N (pmcr_rankone N C X) U /\
  pmfc_energy_bound C N (pmcr_diagonal N C X) b /\
  pmfc_energy_bound C N (fun c => pmcr_rankone N C X c-pmcr_diagonal N C X c) (2*U).
Proof.
move=>HU Hm Hb HmU HbU Hmb HQ HX HD HG.
have HR := pmcr_rankone_energy_bound N C X U HU HQ HG.
have HE := pmcr_diagonal_energy_bound N C X m U b Hm Hb Hmb HX HD.
split.
- move=>c; have HRc := pmcr_rankone_opbound N C X c U HU (HQ c).
  have HDc := pmcr_diagonal_opbound N C X c m Hm (fun i => HX i c).
  split=>//; split=>//.
  have Hneg := pmlo_opb_scale N (pmcr_diagonal N C X c) m (-1) HDc.
  rewrite normrN normr1 mul1r scaleN1r in Hneg.
  apply: (pmlo_opb_le N _ (U+m) (2*U) (pmlo_opb_add N _ _ _ _ HRc Hneg)).
  clear -HmU; apply/RleP; move/RleP: HmU=>HmU.
  change (Rle (Rplus U m) (Rmult (IZR 2) U)).
  Stdlib.micromega.Lra.lra.
- split=>//; split=>//.
  apply: (pmfc_energy_bound_sub C N _ _ U b (2*U) HR HE).
  + clear -HU; apply/RleP; move/RleP: HU=>HU.
    change (Rle R0 (Rmult (IZR 2) U)).
    change (Rle R0 U) in HU.
    Stdlib.micromega.Lra.nra.
  + clear -HU Hb HbU; apply/RleP; move/RleP: HU=>HU; move/RleP: Hb=>Hb; move/RleP: HbU=>HbU.
    change (Rle R0 U) in HU.
    change (Rle R0 b) in Hb.
    rewrite -!RpowE.
    change (Rle (Rplus (Rmult (IZR 2) (pow U 2)) (Rmult (IZR 2) (pow b 2))) (pow (Rmult (IZR 2) U) 2)).
    Stdlib.micromega.Lra.nra.
Qed.
