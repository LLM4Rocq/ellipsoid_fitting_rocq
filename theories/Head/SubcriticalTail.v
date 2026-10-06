(* Exponential lower tail of the head-section minimax below density 1/4.

   paper_main_head_subcritical_clipped_tail: let 0 <= alpha < 1/4,
   g = 1/2 - sqrt alpha, kappa >= 1 and L >= 0. There are eps, A, theta and
   c > 0 such that the following holds for every large d = S n, every head h
   with head-section width at least (1/2 - g/16) d, every set Y of unit
   weight vectors with |y_i| <= theta / sqrt d, and S q <= alpha d^2 tail
   points. A measurable event E on which the tail features clipped at
   d^(1/4) have operator bound L sqrt d and the minimax over Y is at most
   (g/4) sqrt d has probability at most exp(-c d sqrt d).
   The proof takes eps, A and theta from paper_main_soft_parameters and
   applies paper_main_head_compact_clipped_tail with the inverse
   temperatures beta = gamma = A d sqrt d, after checking that the compact
   level is at least (g/4) sqrt d (paper_main_soft_scaled_margin).
   paper_main_subcritical_sample_log gives ln N <= d for 0 < N <= alpha d^2,
   alpha <= 1 and d >= 16. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From EllipsoidFitting Require Import Analysis.CalculusBridge
  Analysis.ContinuousTupleMeasurability PaperMainDefinitions
  Geometry.HeadFeature Geometry.HeadWidth Gaussian.FeatureCoordinates
  Gaussian.PsdWidthLimit Gordon.ProcessCovariance Gordon.Entropy
  Head.SectionMinimax Head.SectionApprox Head.SectionApproxWidth
  Head.SectionWidthLaw Head.SoftTail Head.CompactTail Data.Clipped
  Data.SoftScale Data.SoftConcentration Soft.ParameterChoice Clipping.Rates
  Goe.Definitions.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_subcritical_sample_log N d alpha :
  0 < N -> 16 <= d -> alpha <= 1 -> N <= alpha*d^2 -> Rpower.ln N <= d.
Proof.
move=> HN Hd Ha Hbound.
have Hd0 : 0 < d by lra.
have HNd : N <= d^2 by nra.
have Hlog : Rpower.ln N <= Rpower.ln(d^2).
{ case: (Rle_lt_or_eq_dec _ _ HNd) => [Hlt|Heq].
  - left; exact: ln_increasing HN Hlt.
  - rewrite Heq; exact: Rle_refl. }
rewrite (ln_pow d Hd0 2) in Hlog.
change (Rpower.ln N <= 2*Rpower.ln d) in Hlog.
have Hs := sqrt_lt_R0 d Hd0.
have Hsq := pow2_sqrt d (Rlt_le _ _ Hd0).
have HE := exp_ineq1_le (Rpower.ln(sqrt d)).
rewrite (exp_ln _ Hs) in HE.
have Hln := ln_pow (sqrt d) Hs 2.
rewrite Hsq in Hln; change (Rpower.ln d = 2*Rpower.ln(sqrt d)) in Hln.
have Hs4 : 4 <= sqrt d by nra.
have Hsd : 4*sqrt d <= d by nra.
nra.
Qed.

Theorem paper_main_head_subcritical_clipped_tail alpha kappa L :
  0 <= alpha -> alpha < 1/4 -> 1 <= kappa -> 0 <= L ->
  let g := 1/2-sqrt alpha in
  exists eps A theta c, 0 < eps /\ 0 < A /\ 0 < theta /\ 0 < c /\
  exists D, forall n, Nat.le D n -> forall m q
    (h : paper_main_sample m (S n)) (Y : (nat -> R) -> Prop)
    (E : set (paper_main_sample (S q) (S n))),
    INR (S q) <= alpha*(INR (S n))^2 ->
    (exists y, Y y) -> (forall y, Y y -> paper_main_gordon_dot (S q) y y = 1) ->
    (forall y i, Y y -> (i <= q)%coq_nat -> Rabs(y i) <= theta/sqrt(INR (S n))) ->
    (1/2-g/16)*INR (S n) <= fine (paper_main_head_section_width n m kappa h) ->
    measurable E ->
    (forall x, E x ->
      paper_main_head_section_operator_bound (S q)
        (fun i => paper_main_data_clipped_feature (sqrt(sqrt(INR (S n)))) n i (tval x))
        (L*sqrt(INR (S n))) /\
      paper_main_head_section_minimax kappa (S q) Y
        (fun k : 'I_m => paper_main_head_feature h k)
        (fun i => paper_main_data_clipped_feature (sqrt(sqrt(INR (S n)))) n i (tval x)) <=
          (g/4)*sqrt(INR (S n))) ->
    (paper_main_probability (S q) (S n) E <=
      (exp(-c*INR (S n)*sqrt(INR (S n))))%:E)%E.
Proof.
move=> Ha Hab Hk HL g.
have Hg : 0 < g by exact: paper_main_soft_subcritical_gap.
have [eps [A [theta [He [HA [Ht [Hep [HLe [HErr HTErr]]]]]]]]] :=
  paper_main_soft_parameters alpha kappa L Ha Hab Hk HL.
fold g in Hep,HLe,HErr,HTErr.
pose H := paper_main_gordon_entropy_constant eps.
have HH : 0 <= H.
{ rewrite /H /paper_main_gordon_entropy_constant.
  have Hln : 0 < Rpower.ln 2 by rewrite -ln_1; apply ln_increasing; lra.
  have Hdiv : 0 < 4/eps by apply Rdiv_lt_0_compat; lra.
  nra. }
have [DC HDC] := paper_main_data_soft_scaled_clipping_large kappa A alpha H (g/8) HA Ha HH ltac:(lra).
pose c := (g/8)^2/(8*kappa^2).
have Hc : 0 < c.
{ unfold c; apply Rdiv_lt_0_compat; nra. }
exists eps,A,theta,c; split; first exact He; split; first exact HA; split; first exact Ht; split; first exact Hc.
exists (Nat.max DC 16) => n Hn m q h Y E HN HY Hunit Hcap Hwidth mE HE.
pose d := INR (S n).
have Hd1 : 1 <= d by rewrite /d S_INR; have := pos_INR n; lra.
have Hd : 0 < d by lra.
have Hd16 : 16 <= d.
{ have HH16 := le_INR 16 (S n) ltac:(lia).
  have E16 : INR 16 = 16 by simpl; ring.
  rewrite E16 in HH16; exact HH16. }
have Hsqrt := sqrt_lt_R0 d Hd.
have HU : 0 < sqrt(sqrt d) by exact: sqrt_lt_R0.
have Hbeta : 0 < A*d*sqrt d by repeat apply Rmult_lt_0_compat.
have Hu : 0 < (g/8)*sqrt d by nra.
have Ha6 : 0 < d^6 by apply pow_lt; exact Hd.
have HkMC : (1 <= kappa)%R by exact/RleP.
have HeMC : (0 < eps)%R by exact/RltP.
have Hsection : exists P, paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k) P.
{ apply: paper_main_head_section_width_positive.
  apply/RltP; change (0 < fine (paper_main_head_section_width n m kappa h)).
  have Hsa := sqrt_pos alpha.
  fold d in Hwidth; unfold g in Hwidth; nra. }
have [Hr [Hs [y [B [Hy [HB [Hlr [Hls _]]]]]]]] :=
  paper_main_head_section_approx_width_exists n m kappa (S q) Y h eps HkMC HeMC HY Hunit Hsection.
pose r := List.length (paper_main_gordon_entropy_grid (S q) eps).
pose s := List.length (paper_main_gordon_entropy_grid (paper_main_symmetric_dimension n) eps).
fold r s in Hr,Hs,Hlr,Hls.
have HrN : (0 < r)%coq_nat by exact: (elimT ssrnat.ltP Hr).
have HsN : (0 < s)%coq_nat by exact: (elimT ssrnat.ltP Hs).
have HlrR : Rpower.ln(INR r) <= H*INR (S q).
{ apply/RleP; rewrite RmultE; exact Hlr. }
have HlsR : Rpower.ln(INR s) <= H*INR (paper_main_symmetric_dimension n).
{ apply/RleP; rewrite RmultE; exact Hls. }
have Hclip := HDC n ltac:(lia) (S q) r s HrN HsN HN HlrR HlsR.
fold d in Hclip.
have HD : INR (paper_main_symmetric_dimension n) <= d^2.
{ rewrite paper_main_symmetric_dimension_real; fold d; nra. }
have Hscale : 1 <= goe_scale n*sqrt d.
{ exact: paper_main_soft_gaussian_scale Hd. }
have Hscale0 : 0 < goe_scale n.
{ rewrite /goe_scale; fold d; apply sqrt_lt_R0,Rdiv_lt_0_compat; lra. }
have Hmargin := paper_main_soft_scaled_margin alpha kappa L eps A theta d
  (INR (paper_main_symmetric_dimension n)) (INR (S q))
  (fine (paper_main_head_section_width n m kappa h)) (Rpower.ln(INR r))
  (H*INR (paper_main_symmetric_dimension n)) (goe_scale n)
  Ha Hab Hk HL Hd (pos_INR _) HD (pos_INR _) HN He HA Ht Hep HLe HErr HTErr
  HlrR (Rle_refl _) Hwidth Hscale0 Hscale.
fold g H in Hmargin.
have Hlevel : (g/4)*sqrt d <=
  paper_main_head_compact_level (sqrt(sqrt d)) n m q (A*d*sqrt d) (A*d*sqrt d)
    theta kappa h eps (L*sqrt d) (d^6) ((g/8)*sqrt d).
{ rewrite /paper_main_head_compact_level /paper_main_head_soft_level.
  fold r s d H.
  lra. }
have Hlog : Rpower.ln(INR (S q)) <= INR (S n).
{ exact: paper_main_subcritical_sample_log (INR (S q)) d alpha ltac:(apply lt_0_INR; lia) Hd16 ltac:(lra) HN. }
have Htail := paper_main_head_compact_clipped_tail (sqrt(sqrt d)) n m q
  (A*d*sqrt d) (A*d*sqrt d) theta kappa h eps (L*sqrt d) (d^6) ((g/8)*sqrt d) Y E
  Hbeta Hbeta Ht Hk HU He Ha6 Hu HY Hunit Hcap Hsection Hlog mE.
have Hprob : (paper_main_probability (S q) (S n) E <=
  (exp(-((g/8)*sqrt d)^2/(2*(2*(kappa/sqrt d)*sqrt(sqrt d))^2)))%:E)%E.
{ apply: Htail => x Hx; have [Hop Hvalue] := HE x Hx; split; first exact Hop.
  fold d in Hvalue; exact (Rle_trans _ _ _ Hvalue Hlevel). }
have Hexp := paper_main_clipped_concentration_scale d kappa (g/8) Hd ltac:(lra).
have HX : -((g/8)*sqrt d)^2/(2*(2*(kappa/sqrt d)*sqrt(sqrt d))^2) = -c*d*sqrt d.
{ replace (-((g/8)*sqrt d)^2/(2*(2*(kappa/sqrt d)*sqrt(sqrt d))^2))
    with (- (((g/8)*sqrt d)^2/(2*(2*(kappa/sqrt d)*sqrt(sqrt d))^2))) by (unfold Rdiv; ring).
  rewrite Hexp; unfold c,Rdiv; ring. }
rewrite HX in Hprob; exact Hprob.
Qed.
