(* Lower tail of the head-section minimax over a compact set of weights, for
   a fixed head and the clipped tail features.

   paper_main_head_compact_clipped_tail: fix a head sample h of m points of
   R^d (d = S n) with a nonempty head section, and a set Y of unit weight
   vectors y with |y_i| <= theta / sqrt d. Let E be a measurable event of
   tail samples of S q points on which the tail features clipped at U have
   operator bound L and the head-section minimax over Y is at most
   paper_main_head_compact_level: the soft level minus the clipping loss,
   u, an entropy term and L eps. Then E has probability at most
   exp(-u^2 / (2 (2 kappa U / sqrt d)^2)).
   The proof takes finite nets of weights and of cone points that depend on
   the head only (paper_main_head_section_approx_width_exists), bounds the
   clipped soft minimax over the nets by the minimax over Y plus the
   entropy and L eps terms, and applies the tail bound
   paper_main_head_soft_clipped_lower_tail. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import AnalysisBridge GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity SoftDefinitions PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature
  PaperMainGeometryHeadWidth PaperMainMatrixDuality PaperMainGordonSoftMargin
  PaperMainGordonProcessCovariance PaperMainGordonNets PaperMainGordonEntropy PaperMainGaussianFeatureCoordinates
  PaperMainHeadSectionMinimax PaperMainHeadSectionApprox PaperMainHeadSectionApproxWidth
  PaperMainHeadSectionWidthLaw PaperMainHeadSoftTail PaperMainSoftPublicFeatures
  PaperMainDataClipped PaperMainDataClippedSoft PaperMainDataClippedMoments
  PaperMainDataSoftConeTail PaperMainDataSoftConcentration.
Import GRing.Theory Num.Theory Order.TTheory ListNotations.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma paper_main_head_combination_score d q (y : nat -> R) (V : nat -> 'M[R]_d) P :
  paper_main_pairing (paper_main_head_section_combination q y V) P =
    finite_sum (fun i => (y i*paper_main_pairing (V i) P)%Rcoq) (List.seq 0 q).
Proof.
rewrite /paper_main_head_section_combination pmh_pairing_suml paper_main_finite_sum_public.
by apply: eq_bigr => i _; rewrite RmultE.
Qed.

Lemma paper_main_head_clipped_combination U n q beta gamma y B Y Q xs :
  soft_minimax beta gamma
    (fun a t => paper_main_pairing (paper_main_head_section_combination q (y a)
      (fun i => paper_main_data_clipped_feature U n i xs)) (B t)) Y Q =
  paper_main_data_clipped_soft U n q beta gamma (fun _ t => B t) (fun a _ => y a) Y Q xs.
Proof.
apply: paper_main_gordon_soft_minimax_ext => a t Ha Ht.
exact: paper_main_head_combination_score.
Qed.

Local Close Scope ring_scope.
Open Scope R_scope.

Definition paper_main_head_compact_level U n m q beta gamma theta kappa
    (h : paper_main_sample m (S n)) eps L a u :=
  let r := List.length (paper_main_gordon_entropy_grid (S q) eps) in
  let s := List.length (paper_main_gordon_entropy_grid (paper_main_symmetric_dimension n) eps) in
  paper_main_head_soft_level n m q r beta gamma theta kappa h eps -
  paper_main_data_soft_clipping_loss U n (S q) (kappa/sqrt(INR (S n))) beta gamma
    (List.seq 0 r) (List.seq 0 s) a - u -
  paper_main_gordon_entropy_constant eps*INR (paper_main_symmetric_dimension n)/gamma-L*eps.

Theorem paper_main_head_compact_clipped_tail U n m q beta gamma theta kappa
    (h : paper_main_sample m (S n)) eps L a u (Y : (nat -> R) -> Prop)
    (E : set (paper_main_sample (S q) (S n))) :
  0 < beta -> 0 < gamma -> 0 < theta -> 1 <= kappa ->
  0 < U -> 0 < eps -> 0 < a -> 0 < u ->
  (exists y, Y y) -> (forall y, Y y -> paper_main_gordon_dot (S q) y y = 1) ->
  (forall y i, Y y -> (i <= q)%coq_nat -> Rabs(y i) <= theta/sqrt(INR (S n))) ->
  (exists P, paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k) P) ->
  Rpower.ln(INR (S q)) <= INR (S n) -> measurable E ->
  (forall x, E x ->
    paper_main_head_section_operator_bound (S q)
      (fun i => paper_main_data_clipped_feature U n i (tval x)) L /\
    paper_main_head_section_minimax kappa (S q) Y
      (fun k : 'I_m => paper_main_head_feature h k)
      (fun i => paper_main_data_clipped_feature U n i (tval x)) <=
        paper_main_head_compact_level U n m q beta gamma theta kappa h eps L a u) ->
  (paper_main_probability (S q) (S n) E <=
    (exp(-u^2/(2*(2*(kappa/sqrt(INR (S n)))*U)^2)))%:E)%E.
Proof.
move=> Hb Hg Htheta Hk HU He Ha Hu HY Hunit Hcap Hsection Hlog mE HE.
have HkMC : (1 <= kappa)%R by exact/RleP.
have HeMC : (0 < eps)%R by exact/RltP.
have HbMC : (0 < beta)%R by exact/RltP.
have HgMC : (0 < gamma)%R by exact/RltP.
have [Hr [Hs [y [B [Hy [HB [Hlr [Hls [Hw Hall]]]]]]]]] :=
  paper_main_head_section_approx_width_exists n m kappa (S q) Y h eps
    HkMC HeMC HY Hunit Hsection.
pose r := List.length (paper_main_gordon_entropy_grid (S q) eps).
pose s := List.length (paper_main_gordon_entropy_grid (paper_main_symmetric_dimension n) eps).
fold r s in Hr,Hs,Hy,HB,Hlr,Hls,Hw,Hall.
have HrN : (0 < r)%coq_nat by exact: (elimT ssrnat.ltP Hr).
have HsN : (0 < s)%coq_nat by exact: (elimT ssrnat.ltP Hs).
have Hyin z : (z < r)%coq_nat -> Y (y z).
{ move=> Hz; apply: (proj1 Hy z); apply List.in_seq; lia. }
have Hyunit z : (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 (S q)) = 1.
{ move=> Hz; exact: paper_main_head_section_euclidean_unit (Hunit _ (Hyin z Hz)). }
have Hylow z i : (z < r)%coq_nat -> (i <= q)%coq_nat ->
  Rabs(y z i) <= theta/sqrt(INR (S n)).
{ move=> Hz Hi; exact: Hcap _ _ (Hyin z Hz) Hi. }
have Htail := paper_main_head_soft_clipped_lower_tail U n m q r s beta gamma theta kappa h y B eps a u
  HrN HsN Hb Hg Htheta Hk HU Ha Hu Hyunit Hylow HB Hlog.
pose b := paper_main_head_soft_level n m q r beta gamma theta kappa h eps -
  paper_main_data_soft_clipping_loss U n (S q) (kappa/sqrt(INR (S n))) beta gamma
    (List.seq 0 r) (List.seq 0 s) a-u.
pose F := paper_main_data_clipped_soft U n (S q) beta gamma (fun _ t => B t) (fun z _ => y z)
  (List.seq 0 r) (List.seq 0 s).
have Hsqrt : 0 < sqrt(INR (S n)) by apply sqrt_lt_R0,lt_0_INR; lia.
have HK : 0 <= kappa/sqrt(INR (S n)) by apply Rmult_le_pos; [lra|apply Rlt_le,Rinv_0_lt_compat; exact Hsqrt].
have HBcone j : (j < s)%coq_nat -> paper_main_head_cone_sphere kappa (B j).
{ move=> Hj; have HjMC : (j < s)%N by exact/ssrnat.ltP.
  have [HC [HF _]] := (proj1 HB) j HjMC; by split. }
have Had := paper_main_data_cone_soft_admissible n (S q) r s kappa y B Hk Hyunit HBcone.
have Hrne : List.seq 0 r <> [] by exact: paper_main_head_section_seq_ne.
have Hsne : List.seq 0 s <> [] by exact: paper_main_head_section_seq_ne.
have mF : measurable [set x : paper_main_sample (S q) (S n) | Rle (F (tval x)) b].
{ exact: paper_main_data_clipped_soft_le_measurable U n (S q) (kappa/sqrt(INR (S n)))
    beta gamma (fun _ t => B t) (fun z _ => y z) (List.seq 0 r) (List.seq 0 s) b
    (Rlt_le _ _ HU) HK Hb Hg Hrne Hsne Had. }
apply: le_trans _ Htail.
apply: le_measure; rewrite ?inE; [exact mE|exact mF|].
move=> x Hx.
have [Hop Hbad] := HE x Hx.
have [Hbridge _] := Hall (fun i => paper_main_data_clipped_feature U n i (tval x)) L beta gamma Hop HbMC HgMC.
rewrite paper_main_head_clipped_combination in Hbridge.
have HbrR := elimT RleP Hbridge.
rewrite -!RminusE -RdivE -!RmultE in HbrR.
change (F (tval x) <= b).
rewrite /paper_main_head_compact_level in Hbad; fold r s in Hbad.
fold F b in Hbad,HbrR.
apply (Rplus_le_reg_r (- (paper_main_gordon_entropy_constant eps*INR (paper_main_symmetric_dimension n)/gamma))).
apply (Rplus_le_reg_r (- (L*eps))).
exact (Rle_trans _ _ _ HbrR Hbad).
Qed.
