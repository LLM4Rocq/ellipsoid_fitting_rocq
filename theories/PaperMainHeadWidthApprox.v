(* Head-section support transfer from an approximate measurable maximizer. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadFeature PaperMainGeometryHeadSpectral
  PaperMainGeometryHeadWidth PaperMainGaussianResidualJoint
  GaussianProbabilityProductDefinitions PaperMainGaussianFeatureCoordinates
  PaperMainGaussianSymmetricLawPublic PaperMainConeApproxSelectorResidual.
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

Theorem paper_main_head_width_selector N n (kappa0 eps r : R) :
  1 <= kappa0 -> 0 < eps -> 0 < r ->
  exists P : (paper_main_symmetric_dimension n).-tuple RT -> 'M[R]_(S n),
    (forall a b, measurable_fun [set: (paper_main_symmetric_dimension n).-tuple RT]
      ((fun z => P z a b) : _ -> RT)) /\
    measurable (paper_main_gaussian_residual_joint_event (paper_main_symmetric_dimension n) N (S n) P r) /\
    (gaussian_product_law (Nat.add (paper_main_symmetric_dimension n) (N*S n)%N)
      (paper_main_gaussian_residual_joint_event (paper_main_symmetric_dimension n) N (S n) P r) <=
      (Rmult (INR N) (Rmult 2 (exp (Rdiv (Ropp (Rmult (INR (S n)) (pow r 2)))
        (Rplus 4 (Rmult (Rmult 4 kappa0) r))))))%:E)%E /\
    forall (z : (paper_main_symmetric_dimension n).-tuple RT) (x : paper_main_sample N (S n)),
      ~ paper_main_gaussian_residual_joint_set (paper_main_symmetric_dimension n) N (S n) P r (z,x) ->
      forall m (s : 'I_m -> 'I_N) (mu q0 q1 lam eta A_1 A_inf delta kappa : R),
        injective s -> 0 < mu ->
        paper_main_head_coercive
          (paper_main_head_gram (fun i : 'I_N => paper_main_head_feature x i)) mu ->
        0 < q0 ->
        (forall k : 'I_m, q0 <= paper_main_pairing (paper_main_head_feature x (s k))
          (paper_main_head_feature x (s k))) ->
        0 <= q1 ->
        (forall k l : 'I_m, l != k ->
          `|paper_main_pairing (paper_main_head_feature x (s k))
            (paper_main_head_feature x (s l))| <= q1) ->
        paper_main_loewner_le (paper_main_head_data_gram x s) (lam *: 1%:M) ->
        m%:R * r ^+ 2 <= mu * eta ^+ 2 -> 0 <= eta -> eta < 1 ->
        m%:R * r <= mu * A_1 -> r + q1 * A_1 <= q0 * A_inf ->
        (Num.sqrt (S n)%:R)^-1 * (A_inf * lam + A_1) <= delta ->
        delta < (kappa0 * Num.sqrt (S n)%:R)^-1 ->
        kappa0 / Num.sqrt (S n)%:R + delta <=
          kappa * ((kappa0 * Num.sqrt (S n)%:R)^-1 - delta) ->
        paper_main_head_support (paper_main_public_symmetric_gaussian n (tval z))
            (paper_main_head_cone_sphere kappa0) -
          (eps + 2 * eta) * paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval z)) <=
        paper_main_head_support (paper_main_public_symmetric_gaussian n (tval z))
          (paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature x (s k))).
Proof.
move=> Hk He Hr.
have [P [mP [HP [mE HB]]]] := paper_main_cone_selector_residual N n kappa0 eps r Hk He Hr.
exists P; split; first exact mP.
split; first exact mE.
split; first exact HB.
move=> z x Hgood m s mu q0 q1 lam eta A_1 A_inf delta kappa
  Hs Hmu HG Hq0 Hdiag Hq1 Hoff Hlam Heta2 Heta0 Heta HA1 HAinf Hdel Hlm Hkk.
have [Hcone Happ Hupper] := HP z.
have HRd := paper_main_residual_joint_good (paper_main_symmetric_dimension n) N (S n) P r z x Hgood.
exact: (paper_main_head_width_transfer_features_approx N (S n) m x s (P z)
  (paper_main_public_symmetric_gaussian n (tval z)) mu q0 q1 r lam eta A_1 A_inf delta
  kappa0 kappa eps (ltn0Sn n) Hs Hmu HG Hq0 Hdiag Hq1 Hoff (ltW Hr)
  (fun k => HRd (s k)) Hlam Heta2 Heta0 Heta HA1 HAinf Hdel Hlm Hkk Hcone Happ).
Qed.
