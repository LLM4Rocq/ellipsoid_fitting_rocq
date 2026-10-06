(* The section width of regular selected heads, uniformly outside one
   residual exception.

   For d = S n, paper_main_head_regular N n m x s K c c0 Q L says that the
   head s : 'I_m -> 'I_N is injective with m <= K d ln d, that the Gram
   matrix of the N features of x is at least c d I, that every selected
   feature has squared norm at least c0 d, that two distinct selected
   features have a pairing at most Q ln d in absolute value, and that
   X_J X_J^T <= L d (ln d)^2 I.
   - paper_main_head_width_regular_transfer: let P be a measurable selector
     of near-maximizers of the Gaussian support on the cone sphere. For all
     large d, if x is outside the residual conditional event of P
     (paper_main_residual_conditional_event), then every head h with the
     features of a regular head of x has section width, for the cone
     parameter 2 kappa^2, at least the Gaussian condition width minus eps d.
     It combines paper_main_head_width_actual_selected with the parameters
     of paper_main_head_correction_eventual.
   - paper_main_head_width_regular_event_fixed: if the Gaussian condition
     width for k0 is eventually at least (1/2 - eps/2) d, then for all large
     d and every N there is a measurable event of probability at most
     2 N d^4 exp(-sqrt d / 2) outside which every such head has section
     width at least (1/2 - eps) d. The selector and the event come from
     paper_main_cone_selector_conditional. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix numfun.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import Analysis.CalculusBridge
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  PaperMainDefinitions Geometry.Homogeneous Geometry.HeadWidth
  Gaussian.Symmetric.Coordinates Gaussian.Symmetric.PublicLaw
  Gaussian.Width.Condition Head.SectionMeasurable Head.SectionWidthLaw
  Head.WidthExpectation Geometry.Psd Geometry.HeadCorrection
  Geometry.HeadFeature Geometry.HeadCoefficients Geometry.HeadSpectral
  Head.WidthApprox Clipping.ResidualConditional Gaussian.Sample.ResidualJoint
  Head.WidthActual Head.CorrectionScale Head.CorrectionLimits
  Clipping.ResidualRates Gaussian.Width.ConditionBound Cone.ApproxSelector.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

Local Open Scope ring_scope.

Definition paper_main_head_regular N n m (x : paper_main_sample N (S n))
    (s : 'I_m -> 'I_N) (K c c0 Q L : R) : Prop :=
  let d := (S n)%:R : R in
  injective s /\ m%:R <= K*d*Rpower.ln (INR (S n)) /\
  paper_main_head_coercive (paper_main_head_gram (fun i : 'I_N => paper_main_head_feature x i)) (c*d) /\
  (forall k : 'I_m, c0*d <= paper_main_pairing (paper_main_head_feature x (s k)) (paper_main_head_feature x (s k))) /\
  (forall k l : 'I_m, l != k ->
    `|paper_main_pairing (paper_main_head_feature x (s k)) (paper_main_head_feature x (s l))| <= Q*Rpower.ln (INR (S n))) /\
  paper_main_loewner_le (paper_main_head_data_gram x s)
    ((L*d*(Rpower.ln (INR (S n)))^+2) *: 1%:M).

Theorem paper_main_head_width_regular_transfer K c c0 Q L kappa eps :
  (0 <= K)%Rcoq -> (0 < c)%Rcoq -> (0 < c0)%Rcoq ->
  (0 <= Q)%Rcoq -> (0 <= L)%Rcoq -> (1 <= kappa)%Rcoq -> (0 < eps)%Rcoq ->
  exists D : nat, forall n, Nat.le D n -> forall N m
    (x : paper_main_sample N (S n)) (h : paper_main_sample m (S n)) (s : 'I_m -> 'I_N)
    (P : (paper_main_symmetric_dimension n).-tuple T -> 'M[R]_(S n)),
    paper_main_head_regular N n m x s K c c0 Q L ->
    (forall k : 'I_m, paper_main_head_feature h k = paper_main_head_feature x (s k)) ->
    (forall a b, measurable_fun [set: (paper_main_symmetric_dimension n).-tuple T]
      ((fun z => P z a b) : _ -> T)) ->
    (forall z, paper_main_head_cone_sphere kappa (P z) /\
      paper_main_head_support (paper_main_public_symmetric_gaussian n (tval z))
        (paper_main_head_cone_sphere kappa) -
        (eps/2)%Rcoq*paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval z)) <=
      paper_main_pairing (paper_main_public_symmetric_gaussian n (tval z)) (P z)) ->
    ~ paper_main_residual_conditional_event (paper_main_symmetric_dimension n) N (S n) P
      (paper_main_residual_threshold kappa (INR (S n))) ((1/(INR (S n))^4)%Rcoq) x ->
    (paper_main_gaussian_condition_width n kappa -
      fine (paper_main_head_section_width n m (2*kappa^2)%Rcoq h) <= eps*INR (S n))%Rcoq.
Proof.
move=> HK Hc Hc0 HQ HL Hk Heps.
pose a := sqrt(4+4*kappa)%Rcoq.
have Ha : (0 <= a)%Rcoq by exact: sqrt_pos.
have [E [A [B [F [D1 [HE [HA [HB [HF Hall]]]]]]]]] :=
  paper_main_head_correction_eventual K a c c0 Q L kappa HK Ha Hc Hc0 HQ HL Hk.
have [D2 Herror] := paper_main_head_width_error_large E (eps/2) ltac:(lra) ltac:(lra).
exists (Nat.max D1 D2) => n Hn N m x h s P Hreg Hrow mP HP Hdata.
have Hd1 : (1 <= INR (S n))%Rcoq by rewrite S_INR; have := pos_INR n; lra.
pose d := INR (S n).
pose t := paper_main_head_scale d.
have Hd : (0 < d)%Rcoq by unfold d; apply lt_0_INR; lia.
have Hcast : (S n)%:R = d :> R by rewrite /d INRE.
have [Hs [Hm [HG [Hdiag [Hoff Hlam]]]]] := Hreg.
have HmR : (INR m <= K*d*Rpower.ln d)%Rcoq.
{ apply/RleP; rewrite /d !RmultE !INRE; rewrite !INRE in Hm; exact Hm. }
have Hall' := Hall (S n) ltac:(lia) (INR m) (Q*Rpower.ln d)%Rcoq
  (L*d*(Rpower.ln d)^2)%Rcoq HmR (Rle_refl _) (Rle_refl _).
fold d t in Hall'.
have [_ [Ht [Hfro [[Heta0 Heta] [Hl1 [Hinf [Hop [Hslack Hcone]]]]]]]] := Hall'.
have HrE : paper_main_residual_threshold kappa d = (a/t^8)%Rcoq.
{ exact: paper_main_head_scale_residual Hd1. }
pose r := paper_main_residual_threshold kappa d.
pose eta := (E/t^7)%Rcoq.
pose A1 := (A/t^7)%Rcoq.
pose Ainf := (B/(d*t^6))%Rcoq.
pose delta := (F/(sqrt d*t^4))%Rcoq.
have HkMC : 1 <= kappa by exact/RleP.
have Hk2 : 1 <= (2*kappa^2)%Rcoq by apply/RleP; change (1 <= 2*kappa^2)%Rcoq; nra.
have He : 0 <= (eps/2)%Rcoq by apply/RleP; change (0 <= eps/2)%Rcoq; lra.
have Hmu : 0 < c*(S n)%:R by apply/RltP; rewrite -RmultE Hcast; change (0 < c*d)%Rcoq; nra.
have Hq0 : 0 < c0*(S n)%:R by apply/RltP; rewrite -RmultE Hcast; change (0 < c0*d)%Rcoq; nra.
have Hlog := paper_main_head_scale_log d Hd1.
have Hq1 : 0 <= Q*Rpower.ln d by apply/RleP; rewrite -RmultE; change (0 <= Q*Rpower.ln d)%Rcoq; nra.
have Hr : 0 <= r.
{ apply/RleP; exact: Rlt_le (proj1 (paper_main_residual_threshold_scale kappa d ltac:(lra) Hd)). }
have HFMC : m%:R*r^+2 <= (c*(S n)%:R)*eta^+2.
{ apply/RleP; rewrite -!RmultE -!RpowE -!INRE /r HrE; exact Hfro. }
have HE0 : 0 <= eta by apply/RleP; exact Heta0.
have HE1 : eta < 1 by apply/RltP; exact Heta.
have H1MC : m%:R*r <= (c*(S n)%:R)*A1.
{ apply/RleP; rewrite -!RmultE -!INRE /r HrE; exact Hl1. }
have HIMC : r+(Q*Rpower.ln d)*A1 <= (c0*(S n)%:R)*Ainf.
{ apply/RleP; rewrite -!RmultE -RplusE -!INRE /r HrE; exact Hinf. }
have HOMC : (Num.sqrt (S n)%:R)^-1*(Ainf*(L*(S n)%:R*(Rpower.ln d)^+2)+A1) <= delta.
{ apply/RleP; rewrite -!RmultE -RplusE -RinvE -RsqrtE -!INRE -RpowE.
  change ((/sqrt d)*(Ainf*(L*d*(Rpower.ln d)^2)+A1) <= delta)%Rcoq.
  change ((Ainf*(L*d*(Rpower.ln d)^2)+A1)/sqrt d <= delta)%Rcoq in Hop.
  unfold Rdiv in Hop; nra. }
have HSMC : delta < (kappa*Num.sqrt (S n)%:R)^-1.
{ apply/RltP; rewrite -RinvE -RmultE -RsqrtE -!INRE; change (delta < /(kappa*sqrt d))%Rcoq.
  change (delta < 1/(kappa*sqrt d))%Rcoq in Hslack; lra. }
have HCMC : kappa/Num.sqrt (S n)%:R+delta <=
    (2*kappa^2)%Rcoq*((kappa*Num.sqrt (S n)%:R)^-1-delta).
{ apply/RleP; rewrite -!RmultE -RplusE -RminusE -!RinvE -RsqrtE -!INRE.
  change ((kappa/sqrt d+delta) <= (2*kappa^2)*(/(kappa*sqrt d)-delta))%Rcoq.
  change ((kappa/sqrt d+delta) <= (2*kappa^2)*(1/(kappa*sqrt d)-delta))%Rcoq in Hcone.
  lra. }
have Hwidth := paper_main_head_width_actual_selected N n m x h s P
  (c*(S n)%:R) (c0*(S n)%:R) (Q*Rpower.ln d) r (L*(S n)%:R*(Rpower.ln d)^+2)
  eta A1 Ainf delta kappa (2*kappa^2)%Rcoq (eps/2)%Rcoq
  HkMC Hk2 He mP HP Hrow Hs Hmu HG Hq0 Hdiag Hq1 Hoff Hr Hlam
  HFMC HE0 HE1 H1MC HIMC HOMC HSMC HCMC Hdata.
have [_ Herr] := Herror (S n) ltac:(lia).
fold d t in Herr.
change (2*eta*d+1+1/d^2 <= (eps/2)*d)%Rcoq in Herr.
change (paper_main_gaussian_condition_width n kappa - fine (paper_main_head_section_width n m (2*kappa^2)%Rcoq h) <= (eps/2+2*eta)*d+1+1/d^2)%Rcoq in Hwidth.
change (paper_main_gaussian_condition_width n kappa - fine (paper_main_head_section_width n m (2*kappa^2)%Rcoq h) <= eps*d)%Rcoq.
lra.
Qed.

Theorem paper_main_head_width_regular_event_fixed K c c0 Q L k0 eps :
  (0 <= K)%Rcoq -> (0 < c)%Rcoq -> (0 < c0)%Rcoq ->
  (0 <= Q)%Rcoq -> (0 <= L)%Rcoq -> (0 < eps)%Rcoq ->
  (1 <= k0)%Rcoq ->
  (exists D0, forall n, Nat.le D0 n ->
    ((1/2-eps/2)*INR (S n) <= paper_main_gaussian_condition_width n k0)%Rcoq) ->
  exists D : nat, forall n, Nat.le D n -> forall N,
    exists A : set (paper_main_sample N (S n)), measurable A /\
      (paper_main_probability N (S n) A <=
        (2*INR N*(INR (S n))^4*exp(-sqrt(INR (S n))/2))%Rcoq%:E)%E /\
      forall x, ~ A x -> forall m (h : paper_main_sample m (S n)) (s : 'I_m -> 'I_N),
        paper_main_head_regular N n m x s K c c0 Q L ->
        (forall k : 'I_m, paper_main_head_feature h k = paper_main_head_feature x (s k)) ->
        ((1/2-eps)*INR (S n) <= fine (paper_main_head_section_width n m (2*k0^2)%Rcoq h))%Rcoq.
Proof.
move=> HK Hc Hc0 HQ HL Heps Hk0 [D0 HD0].
have [D1 HD1] := paper_main_head_width_regular_transfer K c c0 Q L k0 (eps/2)%Rcoq
  HK Hc Hc0 HQ HL Hk0 ltac:(lra).
have [D2 HD2] := INR_unbounded ((4+4*k0)^2)%Rcoq.
exists (Nat.max D0 (Nat.max D1 D2)) => n Hn N.
pose d := INR (S n).
pose r := paper_main_residual_threshold k0 d.
pose tau := (1/d^4)%Rcoq.
have Hd : (0 < d)%Rcoq by unfold d; apply lt_0_INR; lia.
have HkMC : 1 <= k0 by exact/RleP.
have He : 0 < (eps/2/2)%Rcoq by apply/RltP; change (0 < eps/2/2)%Rcoq; lra.
have HrR := proj1 (paper_main_residual_threshold_scale k0 d ltac:(lra) Hd).
have Hr : 0 < r by exact/RltP.
have HtauR : (0 < tau)%Rcoq by unfold tau; apply Rdiv_lt_0_compat; [lra|apply pow_lt; exact Hd].
have Htau : 0 < tau by exact/RltP.
have [P [mP [HP [mA HB]]]] := paper_main_cone_selector_conditional N n k0 (eps/2/2)%Rcoq r tau HkMC He Hr Htau.
exists (paper_main_residual_conditional_event (paper_main_symmetric_dimension n) N (S n) P r tau).
split; first exact mA.
split.
- apply: le_trans HB _; rewrite -EFinM lee_fin; apply/RleP.
  rewrite -RmultE -RinvE.
  have Hlarge : ((4+4*k0)^2 <= d)%Rcoq.
  { have := le_INR D2 (S n) ltac:(lia); unfold d; lra. }
  have HE := paper_main_residual_exponential_rate k0 d ltac:(lra) Hd Hlarge.
  have Hinv : (/tau = d^4)%Rcoq by unfold tau; field; lra.
  rewrite Hinv.
  change (d^4*(INR N*(2*exp(-(d*r^2)/(4+4*k0*r)))) <=
    2*INR N*d^4*exp(-sqrt d/2))%Rcoq.
  have HC : (0 <= 2*INR N*d^4)%Rcoq by have := pos_INR N; have := pow_le d 4 ltac:(lra); nra.
  have HM := Rmult_le_compat_l (2*INR N*d^4)%Rcoq _ _ HC HE.
  fold r in HM; rewrite Ropp_mult_distr_l; nra.
- move=> x Hgood m h s Hreg Hrow.
  have HW := HD1 n ltac:(lia) N m x h s P Hreg Hrow mP HP Hgood.
  have Hbase := HD0 n ltac:(lia).
  nra.
Qed.
