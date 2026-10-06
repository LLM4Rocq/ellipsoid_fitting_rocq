(* The head-section width is close to the Gaussian condition width.

   paper_main_head_width_actual_transfer: let Z be the Gaussian symmetric
   matrix, of dimension D = paper_main_symmetric_dimension n. If, outside a
   measurable set A of probability at most p, the support of the head
   section at Z is at least the condition support at Z minus e |Z|_F, then
   the condition width exceeds the head-section width by at most
   e sqrt D + D/a + a p. paper_main_head_width_actual_polynomial takes
   a = d^2 and p = 1/d^4, where d = S n, and gets e d + 1 + 1/d^2.
   paper_main_head_width_actual_selected applies this to a head h formed by
   distinct points s of a sample x. Given a measurable choice P(Z) of near
   maximizers on the cone sphere, and a sample outside the residual event
   paper_main_residual_conditional_event, the bound holds with
   e = eps + 2 eta under the deterministic conditions of
   paper_main_head_width_transfer_features_approx on the Gram matrices of
   the head and data features. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix numfun.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import AnalysisBridge GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainGeometryHomogeneous
  PaperMainGeometryHeadWidth PaperMainGaussianFeatureCoordinates
  PaperMainGaussianSymmetricLawPublic PaperMainGaussianConditionWidth
  PaperMainHeadSectionMeasurable PaperMainHeadSectionWidthLaw PaperMainHeadWidthExpectation
  PaperMainGeometryPsd PaperMainGeometryHeadCorrection PaperMainGeometryHeadFeature PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadSpectral PaperMainHeadWidthApprox PaperMainResidualConditional
  PaperMainGaussianResidualJoint.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

Theorem paper_main_head_width_actual_transfer n m kappa0 kappa
    (h : paper_main_sample m (S n))
    (A : set ((paper_main_symmetric_dimension n).-tuple T)) e a p :
  1 <= kappa0 -> 1 <= kappa -> 0 <= e -> 0 < a -> measurable A ->
  (forall z, ~ A z -> paper_main_gaussian_condition_support n kappa0 (tval z) -
    e*paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval z)) <=
    paper_main_head_section_support_value n m kappa h z) ->
  (gaussian_product_law (paper_main_symmetric_dimension n) A <= p%:E)%E ->
  paper_main_gaussian_condition_width n kappa0 - fine (paper_main_head_section_width n m kappa h) <=
    e*sqrt(INR (paper_main_symmetric_dimension n))+INR (paper_main_symmetric_dimension n)/a+a * p.
Proof.
move=> Hk0 Hk He Ha mA Hgood Hp.
have HkMC : (1 <= kappa)%R by exact/RleP.
have IG := paper_main_head_section_value_integrable n m kappa h HkMC.
have Hfin := paper_main_head_section_width_fin n m kappa h HkMC.
have EG : (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_z
    (paper_main_head_section_support_value n m kappa h z)%:E =
    (fine (paper_main_head_section_width n m kappa h))%:E)%E.
{ exact: esym (fineK Hfin). }
apply: (paper_main_head_width_expectation_transfer n kappa0 _ A e a p _ Hk0 He Ha mA _ Hgood IG EG Hp).
move=> z; rewrite RabsE; apply/RleP.
exact: paper_main_head_section_support_bound.
Qed.

Corollary paper_main_head_width_actual_polynomial n m kappa0 kappa
    (h : paper_main_sample m (S n))
    (A : set ((paper_main_symmetric_dimension n).-tuple T)) e :
  1 <= kappa0 -> 1 <= kappa -> 0 <= e -> measurable A ->
  (forall z, ~ A z -> paper_main_gaussian_condition_support n kappa0 (tval z) -
    e*paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval z)) <=
    paper_main_head_section_support_value n m kappa h z) ->
  (gaussian_product_law (paper_main_symmetric_dimension n) A <= ((1/(INR (S n))^4)%Rcoq)%:E)%E ->
  paper_main_gaussian_condition_width n kappa0 - fine (paper_main_head_section_width n m kappa h) <=
    e*INR (S n)+1+1/(INR (S n))^2.
Proof.
move=> Hk0 Hk He mA Hgood Hp.
have Hd : 0 < INR (S n) by apply lt_0_INR; lia.
have Ha : 0 < (INR (S n))^2 by nra.
have HB := paper_main_head_width_actual_transfer n m kappa0 kappa h A e
  ((INR (S n))^2) (1/(INR (S n))^4) Hk0 Hk He Ha mA Hgood Hp.
exact: Rle_trans HB (paper_main_head_width_exceptional_scale n e He).
Qed.

Local Open Scope ring_scope.

Theorem paper_main_head_width_actual_selected N n m
    (x : paper_main_sample N (S n)) (h : paper_main_sample m (S n)) (s : 'I_m -> 'I_N)
    (P : (paper_main_symmetric_dimension n).-tuple T -> 'M[R]_(S n))
    (mu q0 q1 r lam eta A1 Ainf delta kappa0 kappa eps : R) :
  1 <= kappa0 -> 1 <= kappa -> 0 <= eps ->
  (forall a b, measurable_fun [set: (paper_main_symmetric_dimension n).-tuple T]
    ((fun z => P z a b) : _ -> T)) ->
  (forall z, paper_main_head_cone_sphere kappa0 (P z) /\
    paper_main_head_support (paper_main_public_symmetric_gaussian n (tval z))
      (paper_main_head_cone_sphere kappa0) -
      eps*paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval z)) <=
    paper_main_pairing (paper_main_public_symmetric_gaussian n (tval z)) (P z)) ->
  (forall k : 'I_m, paper_main_head_feature h k = paper_main_head_feature x (s k)) ->
  injective s -> 0 < mu ->
  paper_main_head_coercive (paper_main_head_gram (fun i : 'I_N => paper_main_head_feature x i)) mu ->
  0 < q0 ->
  (forall k, q0 <= paper_main_pairing (paper_main_head_feature x (s k)) (paper_main_head_feature x (s k))) ->
  0 <= q1 ->
  (forall k l : 'I_m, l != k ->
    `|paper_main_pairing (paper_main_head_feature x (s k)) (paper_main_head_feature x (s l))| <= q1) ->
  0 <= r -> paper_main_loewner_le (paper_main_head_data_gram x s) (lam *: 1%:M) ->
  m%:R*r^+2 <= mu*eta^+2 -> 0 <= eta -> eta < 1 ->
  m%:R*r <= mu*A1 -> r+q1*A1 <= q0*Ainf ->
  (Num.sqrt (S n)%:R)^-1*(Ainf*lam+A1) <= delta ->
  delta < (kappa0*Num.sqrt (S n)%:R)^-1 ->
  kappa0/Num.sqrt (S n)%:R+delta <= kappa*((kappa0*Num.sqrt (S n)%:R)^-1-delta) ->
  ~ paper_main_residual_conditional_event (paper_main_symmetric_dimension n) N (S n) P r
    ((1/(INR (S n))^4)%Rcoq) x ->
  (paper_main_gaussian_condition_width n kappa0 - fine (paper_main_head_section_width n m kappa h) <=
    (eps+2*eta)*INR (S n)+1+1/(INR (S n))^2)%Rcoq.
Proof.
move=> Hk0 Hk He mP HP Hrow Hs Hmu HG Hq0 Hdiag Hq1 Hoff Hr0 Hlam Heta2 Heta0 Heta
  HA1 HAinf Hdelta Hslack Hcone Hdata.
pose A := ysection (paper_main_gaussian_residual_joint_set (paper_main_symmetric_dimension n) N (S n) P r) x.
have mA : measurable A.
{ apply: measurable_ysection; exact: paper_main_gaussian_residual_joint_set_measurable. }
have Hprob := paper_main_residual_conditional_good _ N (S n) P r ((1/(INR (S n))^4)%Rcoq) x Hdata.
have Hk0R : (1 <= kappa0)%Rcoq by exact/RleP.
have HkR : (1 <= kappa)%Rcoq by exact/RleP.
have HeR : (0 <= eps+2*eta)%Rcoq.
{ have H : 0 <= eps+2*eta by apply: addr_ge0 => //; apply: mulr_ge0 => //.
  exact/RleP. }
apply: (paper_main_head_width_actual_polynomial n m kappa0 kappa h A
  (eps+2*eta) Hk0R HkR HeR mA _ (ltW Hprob)).
move=> z Hz.
have Hjoint : ~ paper_main_gaussian_residual_joint_set (paper_main_symmetric_dimension n) N (S n) P r (z,x).
{ move=> Hj; apply: Hz; exact/ysectionP. }
have Hres := paper_main_residual_joint_good _ N (S n) P r z x Hjoint.
have [HC Happrox] := HP z.
have HB := paper_main_head_width_transfer_features_approx N (S n) m x s (P z)
  (paper_main_public_symmetric_gaussian n (tval z)) mu q0 q1 r lam eta A1 Ainf delta kappa0 kappa eps
  isT Hs Hmu HG Hq0 Hdiag Hq1 Hoff Hr0 (fun k => Hres (s k)) Hlam
  Heta2 Heta0 Heta HA1 HAinf Hdelta Hslack Hcone HC Happrox.
have HW : (fun k : 'I_m => paper_main_head_feature x (s k)) = (fun k : 'I_m => paper_main_head_feature h k).
{ apply/funext => k; exact: esym (Hrow k). }
rewrite HW in HB.
apply/RleP; exact HB.
Qed.
