(* Transfer of the support on the cone sphere to the support on the head
   section, from an approximate maximizer.
   - paper_main_head_width_transfer_approx: if P maximizes <Z, .> on the
     cone sphere of parameter kappa0 up to eps |Z|_F, and Pt lies in the
     head section of parameter kappa1 with <Z, P> - 2 eta |Z|_F <= <Z, Pt>,
     then the support of Z on the head section is at least its support on
     the cone sphere minus (eps + 2 eta) |Z|_F.
   - paper_main_head_width_transfer_features_approx: the same for the head
     features W_k = paper_main_head_feature x (s k) of a sample, with Pt the
     corrected and normalized matrix of paper_main_head_correction_bounds_cone,
     under the scalar hypotheses of that theorem (coercivity of the Gram
     matrix, bounds on the diagonal and off-diagonal pairings and on the
     residuals <W_k, P>, and a Loewner bound on the head data Gram matrix).
   - paper_main_residual_joint_good: outside the joint residual event of
     Gaussian.Sample.ResidualJoint, every residual |<W_i, P(z)>| is at
     most r. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadFrobenius Geometry.HeadCorrection
  Geometry.HeadCoefficients Geometry.HeadFeature Geometry.HeadSpectral
  Geometry.HeadWidth Gaussian.Sample.ResidualJoint
  GaussianProbabilityProductDefinitions Gaussian.Symmetric.Coordinates
  Gaussian.Symmetric.PublicLaw Cone.ApproxSelectorResidual.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Theorem paper_main_head_width_transfer_approx d m (W : 'I_m -> 'M[R]_d)
    (P Pt Z : 'M[R]_d) (kappa0 kappa1 eps eta : R) :
  paper_main_head_support Z (paper_main_head_cone_sphere kappa0) -
    eps * paper_main_frobenius Z <= paper_main_pairing Z P ->
  paper_main_head_section kappa1 W Pt ->
  paper_main_pairing Z P - 2 * eta * paper_main_frobenius Z <= paper_main_pairing Z Pt ->
  paper_main_head_support Z (paper_main_head_cone_sphere kappa0) -
    (eps + 2 * eta) * paper_main_frobenius Z <=
  paper_main_head_support Z (paper_main_head_section kappa1 W).
Proof.
move=> Happrox HPt Hcorr.
have Hge : paper_main_pairing Z Pt <= paper_main_head_support Z (paper_main_head_section kappa1 W).
{ by apply: pmh_support_ge => // S [_ [HS _]]. }
rewrite mulrDl; lra.
Qed.

Theorem paper_main_head_width_transfer_features_approx n d m (x : paper_main_sample n d)
    (s : 'I_m -> 'I_n) (P Z : 'M[R]_d)
    (mu q0 q1 Rd lam eta A_1 A_inf delta kappa0 kappa eps : R) :
  (0 < d)%N -> injective s -> 0 < mu ->
  paper_main_head_coercive
    (paper_main_head_gram (fun i : 'I_n => paper_main_head_feature x i)) mu ->
  0 < q0 ->
  (forall k : 'I_m, q0 <= paper_main_pairing (paper_main_head_feature x (s k))
                              (paper_main_head_feature x (s k))) ->
  0 <= q1 ->
  (forall k l : 'I_m, l != k ->
     `|paper_main_pairing (paper_main_head_feature x (s k))
                          (paper_main_head_feature x (s l))| <= q1) ->
  0 <= Rd ->
  (forall k : 'I_m, `|paper_main_pairing (paper_main_head_feature x (s k)) P| <= Rd) ->
  paper_main_loewner_le (paper_main_head_data_gram x s) (lam *: 1%:M) ->
  m%:R * Rd ^+ 2 <= mu * eta ^+ 2 -> 0 <= eta -> eta < 1 ->
  m%:R * Rd <= mu * A_1 -> Rd + q1 * A_1 <= q0 * A_inf ->
  (Num.sqrt d%:R)^-1 * (A_inf * lam + A_1) <= delta ->
  delta < (kappa0 * Num.sqrt d%:R)^-1 ->
  kappa0 / Num.sqrt d%:R + delta <= kappa * ((kappa0 * Num.sqrt d%:R)^-1 - delta) ->
  paper_main_head_cone_sphere kappa0 P ->
  paper_main_head_support Z (paper_main_head_cone_sphere kappa0) -
    eps * paper_main_frobenius Z <= paper_main_pairing Z P ->
  paper_main_head_support Z (paper_main_head_cone_sphere kappa0) -
    (eps + 2 * eta) * paper_main_frobenius Z <=
  paper_main_head_support Z
    (paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature x (s k))).
Proof.
move=> Hd Hs Hmu HG Hq0 Hdiag Hq1 Hoff HRd0 HRd Hlam Heta2 Heta0 Heta HA1 HAinf Hdel
  Hlm Hk [HC HP] Happrox.
have [_ [C U K _ T]] := paper_main_head_correction_bounds_cone _ _ _ _ _ _ Z _ _ _ _ _ _ _ _ _ _ _
  Hd Hs Hmu HG Hq0 Hdiag Hq1 Hoff HRd0 HRd Hlam Heta2 Heta0 Heta HA1 HAinf Hdel Hlm Hk HC HP.
apply: (paper_main_head_width_transfer_approx _ _ _ _ _ _ _ _ _ _ Happrox _ T).
split => //; split => // k.
by rewrite paper_main_head_feature_pairing K subrr mulr0.
Qed.

Local Notation RT := (measurableTypeR R).

Lemma paper_main_residual_joint_good D N d (P : D.-tuple RT -> 'M[R]_d) r
    (z : D.-tuple RT) (x : paper_main_sample N d) :
  ~ paper_main_gaussian_residual_joint_set D N d P r (z,x) ->
  forall i : 'I_N, `|paper_main_pairing (paper_main_head_feature x i) (P z)| <= r.
Proof.
move=> Hgood i.
have Hnot : ~ Rle r (Rabs (paper_main_pairing (paper_main_head_feature x i) (P z))).
{ move=> H; apply: Hgood; exists (nat_of_ord i); split; last exact H.
  exact: (elimT ssrnat.ltP (ltn_ord i)). }
have Hlt := Rnot_le_lt _ _ Hnot.
apply/RleP; rewrite -RabsE; exact: Rlt_le Hlt.
Qed.
