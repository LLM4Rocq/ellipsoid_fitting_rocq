(* An operator bound on Z bounds its PSD projection: 0 <= P <= b I, without
   the spectral theorem, discharging the explicit hypothesis of
   Cone.Condition (manuscript lem:widthcone, the shifted positive
   part).

   The operator bound is bilinear and squared:
   (u^T Z v)^2 <= b^2 |u|^2 |v|^2 for all u, v (paper_main_cone_opnorm_le).
   For symmetric Z it gives -b I <= Z <= b I.
   With P = paper_main_psd_projection Z and N = P - Z:
   - N P = 0 (paper_main_psd_negative_mul_projection): <P, N> = 0, P is a
     sum of w_i w_i^T, so each w_i^T N w_i = 0 and N w_i = 0
     (paper_main_psd_form_eq0);
   - P^2 = Z P;
   - |P v|^2 = v^T Z (P v) <= b |v| |P v|, so |P v| <= b |v|, and by vector
     Cauchy-Schwarz v^T P v <= b |v|^2, that is P <= b I
     (paper_main_psd_projection_opnorm). There is no loss in b.
   paper_main_cone_shift_opnorm_scaled combines this with the shifted
   candidate: under the operator bound the
   candidate lies in K_kappa \cap S_F with kappa = (b + t) / t, and the
   support bound holds. The operator-norm probability is not proved here. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Gram Geometry.Homogeneous Geometry.Separation Geometry.HeadFrobenius
  Geometry.HeadCorrection Geometry.HeadCoefficients Geometry.HeadFeature
  Geometry.HeadSpectral Geometry.HeadWidth Cone.Projection Cone.Condition.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

#[local] Arguments paper_main_psd_projection {d} Z.
#[local] Arguments paper_main_psd_negative_part {d} Z.

(* The bilinear operator bound |u^T Z v| <= b |u| |v|, squared. *)
Definition paper_main_cone_opnorm_le {d : nat} (Z : 'M[R]_d) (b : R) : Prop :=
  forall u v : 'cV[R]_d,
    ((u^T *m Z *m v) 0 0) ^+ 2 <= b ^+ 2 * ((u^T *m u) 0 0 * (v^T *m v) 0 0).

Section ConeConditionOperator.
Variable d : nat.
Implicit Types (P N S Z : 'M[R]_d) (u v w : 'cV[R]_d).

(* Vector Cauchy-Schwarz from the matrix one, through rank-one matrices. *)
Lemma pmco_vec_cauchy_schwarz u w :
  ((u^T *m w) 0 0) ^+ 2 <= (u^T *m u) 0 0 * (w^T *m w) 0 0.
Proof.
have CS := pmh_pairing_cauchy_schwarz _ (u *m u^T) (w *m w^T).
rewrite !paper_main_pairing_outer !paper_main_quadratic_formE !paper_main_form_rank1E in CS.
rewrite (paper_main_inner_sym _ w u) -exprMn in CS.
have Ha := pmh_vec_sqr_ge0 _ u.
have Hb := pmh_vec_sqr_ge0 _ w.
have Hab := mulr_ge0 Ha Hb.
have Hc := sqr_ge0 ((u^T *m w) 0 0).
move: CS Hc; set A := (u^T *m w) 0 0 ^+ 2 => CS Hc.
nra.
Qed.

(* N P = 0 and P^2 = Z P. *)
Theorem paper_main_psd_negative_mul_projection Z :
  paper_main_symmetric Z ->
  paper_main_psd_negative_part Z *m paper_main_psd_projection Z = 0.
Proof.
move=> HZ.
have [HP HN _ Horth] := paper_main_psd_moreau _ _ HZ.
set P := paper_main_psd_projection Z in HP Horth *.
set N := paper_main_psd_negative_part Z in HN Horth *.
have [m [w E]] := paper_main_psd_decomp d P HP.
have Hsum : \sum_(i < m) paper_main_quadratic_form N (w i) = paper_main_pairing P N.
  rewrite [in RHS]E.
  have -> : \sum_(i < m) w i *m (w i)^T = \sum_(i < m) 1 *: (w i *m (w i)^T).
    by apply: eq_bigr => i _; rewrite scale1r.
  rewrite paper_main_pairingC paper_main_pairing_sum.
  by apply: eq_bigr => i _; rewrite mul1r paper_main_pairing_outer.
rewrite Horth in Hsum.
have Hnn : forall i, true -> 0 <= paper_main_quadratic_form N (w i).
  by move=> i _; case: HN => _; apply.
have Hz := psumr_eq0P Hnn Hsum.
rewrite E mulmx_sumr big1 // => i _.
rewrite mulmxA (paper_main_psd_form_eq0 _ _ _ HN (Hz i isT)) mul0mx.
done.
Qed.

Lemma pmco_projection_sqr Z :
  paper_main_symmetric Z ->
  paper_main_psd_projection Z *m paper_main_psd_projection Z =
  Z *m paper_main_psd_projection Z.
Proof.
move=> HZ.
have [_ _ HZd _] := paper_main_psd_moreau _ _ HZ.
have HNP := paper_main_psd_negative_mul_projection _ HZ.
have -> : Z *m paper_main_psd_projection Z =
    (paper_main_psd_projection Z - paper_main_psd_negative_part Z) *m paper_main_psd_projection Z.
  by rewrite -HZd.
by rewrite mulmxBl HNP subr0.
Qed.

(* 0 <= P <= b I from the operator bound. *)
Theorem paper_main_psd_projection_opnorm Z (b : R) :
  paper_main_symmetric Z -> 0 <= b -> paper_main_cone_opnorm_le Z b ->
  paper_main_psd (paper_main_psd_projection Z) /\
  paper_main_loewner_le (paper_main_psd_projection Z) (b *: 1%:M).
Proof.
move=> HZ Hb HO.
have HP := paper_main_psd_projection_psd _ Z.
split => //.
have Hsq := pmco_projection_sqr _ HZ.
set P := paper_main_psd_projection Z in HP Hsq *.
have HPs : P^T = P by apply/paper_main_symmetricP; case: HP.
split; first by apply: pmh_symmetricB => //; [move=> i j; rewrite !mxE eq_sym | case: HP].
move=> v.
rewrite pms_formB paper_main_form_scale pmh_form_id subr_ge0 paper_main_quadratic_formE.
set u := P *m v.
have Huu : (u^T *m u) 0 0 = (v^T *m Z *m u) 0 0.
  by rewrite /u trmx_mul HPs -!mulmxA (mulmxA P P) Hsq !mulmxA.
have Hv := pmh_vec_sqr_ge0 _ v.
have Hu := pmh_vec_sqr_ge0 _ u.
have HOv := HO v u.
rewrite -Huu in HOv.
have Hub : (u^T *m u) 0 0 <= b ^+ 2 * (v^T *m v) 0 0.
  have Hbv : 0 <= b ^+ 2 * (v^T *m v) 0 0 by rewrite mulr_ge0 ?sqr_ge0.
  have [Hu0|Hu0] := eqVneq ((u^T *m u) 0 0) 0; first by rewrite Hu0.
  have Hup : 0 < (u^T *m u) 0 0 by rewrite lt0r Hu0.
  nra.
have Hcs := pmco_vec_cauchy_schwarz v u.
have -> : (v^T *m P *m v) 0 0 = (v^T *m u) 0 0 by rewrite /u mulmxA.
have Hvu : ((v^T *m u) 0 0) ^+ 2 <= (b * (v^T *m v) 0 0) ^+ 2.
  rewrite exprMn; apply: le_trans Hcs _.
  by have := ler_wpM2l Hv Hub; lra.
have Hbv : 0 <= b * (v^T *m v) 0 0 by exact: mulr_ge0.
have := ler_norm ((v^T *m u) 0 0).
nra.
Qed.

Corollary paper_main_cone_shift_opnorm_scaled Z (C s b t kappa : R) :
  (0 < d)%N -> paper_main_symmetric Z -> 0 < s -> 0 <= C ->
  b = C * Num.sqrt d%:R -> t = s * Num.sqrt d%:R -> kappa = (C + s) / s ->
  paper_main_cone_opnorm_le Z b ->
  paper_main_head_cone_sphere kappa (paper_main_cone_shift Z t) /\
  paper_main_frobenius (paper_main_psd_projection Z) - s * d%:R -
    `|paper_main_trace Z| / Num.sqrt d%:R <=
  paper_main_head_support Z (paper_main_head_cone_sphere kappa).
Proof.
move=> Hd HZ Hs HC Hbd Ht Hk HO.
have Hsd : 0 < Num.sqrt d%:R :> R by rewrite sqrtr_gt0 ltr0n.
have Hb : 0 <= b by rewrite Hbd mulr_ge0 // ltW.
have [_ HPb] := paper_main_psd_projection_opnorm _ _ HZ Hb HO.
rewrite Hbd in HPb.
exact: (paper_main_cone_shift_scaled _ Z C s t kappa Hd HZ Hs HC Ht Hk HPb).
Qed.

End ConeConditionOperator.
