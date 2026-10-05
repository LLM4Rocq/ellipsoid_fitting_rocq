(* Lower bounds for the data soft minimax expressed through the
   head-section width paper_main_head_section_width.
   - paper_main_head_section_width_empty and
     paper_main_head_section_width_positive: the width of an empty section
     is 0, so a positive width gives a nonempty section.
   - paper_main_head_soft_level: the level of PaperMainDataSoftConeTail
     with the Gordon width of a net replaced by the head-section width
     minus eps sqrt D, D = paper_main_symmetric_dimension n. It is at most
     the level of an eps-net B of the section
     (paper_main_head_soft_level_le).
   - paper_main_head_soft_expectation: the level is at most the iterated
     Gaussian expectation of the raw data soft minimax over the net B.
   - paper_main_head_soft_clipped_lower_tail: the soft minimax clipped at
     level U is at most the level minus the clipping loss
     (paper_main_data_soft_clipping_loss) minus u with probability at most
     exp(-u^2 / (2 (2 k U)^2)), k = kappa / sqrt d. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions
  PaperMainGeometryHeadWidth PaperMainGeometryHeadFeature
  PaperMainHeadSectionMeasurable PaperMainHeadSectionWidthLaw PaperMainGaussianFeatureCoordinates
  PaperMainHeadSectionApprox PaperMainHeadSectionApproxWidth
  SoftDefinitions GoeDefinitions GoeSynthesis GaussianProductDefinitions OperatorDefinitions
  PaperMainConeGaussianCoordinates PaperMainGordonWidth PaperMainMatrixTransport
  PaperMainSoftPublicFeatures PaperMainDataClippedSoft PaperMainDataClippedMoments
  PaperMainDataSoftConeTail PaperMainDataSoftConcentration.
Import GRing.Theory Num.Theory Order.TTheory ListNotations.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma paper_main_head_section_width_empty n m kappa (h : paper_main_sample m (S n)) :
  ~ (exists P, paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k) P) ->
  paper_main_head_section_width n m kappa h = 0%E.
Proof.
move=> HE; rewrite /paper_main_head_section_width.
transitivity (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_z 0)%E;
  last exact: integral0.
apply: eq_integral => z _.
by rewrite /paper_main_head_section_support_value paper_main_head_section_support_empty.
Qed.

Lemma paper_main_head_section_width_positive n m kappa (h : paper_main_sample m (S n)) :
  0 < fine (paper_main_head_section_width n m kappa h) ->
  exists P, paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k) P.
Proof.
move=> Hpos; case: (pselect (exists P, paper_main_head_section kappa
  (fun k : 'I_m => paper_main_head_feature h k) P)) => H; first exact H.
by move: Hpos; rewrite (paper_main_head_section_width_empty n m kappa h H) /= ltxx.
Qed.

Local Close Scope ring_scope.
Open Scope R_scope.

Definition paper_main_head_soft_level n m q r beta gamma theta kappa
    (h : paper_main_sample m (S n)) eps :=
  let d := INR (S n) in
  goe_scale n *
    (fine (paper_main_head_section_width n m kappa h) -
      eps*sqrt(INR (paper_main_symmetric_dimension n))-sqrt(INR (S q))) -
    Rpower.ln (INR r)/beta - (200/3)*kappa^3*(beta+gamma)^2*theta/(d^2*sqrt d).

Lemma paper_main_head_soft_level_le n m q r s beta gamma theta kappa
    (h : paper_main_sample m (S n)) B eps :
  1 <= kappa -> (0 < s)%coq_nat ->
  paper_main_head_section_net kappa (fun k : 'I_m => paper_main_head_feature h k) B s eps ->
  paper_main_head_soft_level n m q r beta gamma theta kappa h eps <=
    paper_main_data_soft_cone_level n q r s beta gamma theta kappa B.
Proof.
move=> Hk Hs Hnet.
have HkMC : (1 <= kappa)%R by exact/RleP.
have HsMC : (0 < s)%N by exact/ssrnat.ltP.
have [w [Hw [_ HB]]] := paper_main_head_section_net_width n m kappa h B s eps HkMC HsMC Hnet.
have HBR : w <= paper_main_gordon_width (paper_main_symmetric_dimension n)
  (fun t => paper_main_cone_code n (B t)) (List.seq 0 s) +
  eps*sqrt(INR (paper_main_symmetric_dimension n)).
{ apply/RleP; rewrite RplusE RmultE; exact HB. }
rewrite /paper_main_head_soft_level Hw /paper_main_data_soft_cone_level.
change (goe_scale n*(w-eps*sqrt(INR (paper_main_symmetric_dimension n))-sqrt(INR (S q)))-
  Rpower.ln(INR r)/beta-(200/3)*kappa^3*(beta+gamma)^2*theta/((INR (S n))^2*sqrt(INR (S n))) <=
  goe_scale n*(paper_main_gordon_width (paper_main_symmetric_dimension n)
    (fun t => paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B t))) (List.seq 0 s)-sqrt(INR (S q)))-
  Rpower.ln(INR r)/beta-(200/3)*kappa^3*(beta+gamma)^2*theta/((INR (S n))^2*sqrt(INR (S n)))).
have Hscale := goe_scale_positive n.
rewrite /paper_main_cone_code in HBR.
nra.
Qed.

Theorem paper_main_head_soft_expectation n m q r s beta gamma theta kappa
    (h : paper_main_sample m (S n)) y B eps :
  (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  0 < beta -> 0 < gamma -> 0 < theta -> 1 <= kappa ->
  (forall z, (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 (S q)) = 1) ->
  (forall z i, (z < r)%coq_nat -> (i <= q)%coq_nat ->
    Rabs (y z i) <= theta/sqrt(INR (S n))) ->
  paper_main_head_section_net kappa (fun k : 'I_m => paper_main_head_feature h k) B s eps ->
  Rpower.ln (INR (S q)) <= INR (S n) ->
  paper_main_head_soft_level n m q r beta gamma theta kappa h eps <=
    gaussian_iterated_expectation ((S q)*(S n))
      (paper_main_data_raw_soft n (S q) beta gamma (fun _ t => B t) (fun z _ => y z)
        (List.seq 0 r) (List.seq 0 s)).
Proof.
move=> Hr Hs Hb Hg Htheta Hk Hy Hlow Hnet Hlog.
have HB : forall j, (j < s)%coq_nat -> paper_main_head_cone_sphere kappa (B j).
{ move=> j Hj; have HjMC : (j < s)%N by exact/ssrnat.ltP.
  have [HC [HF _]] := (proj1 Hnet) j HjMC.
  by split. }
have Hmean := paper_main_data_cone_soft_expectation n q r s beta gamma theta kappa y B
  Hr Hs Hb Hg Htheta Hk Hy Hlow HB Hlog.
have Hlevel := paper_main_head_soft_level_le n m q r s beta gamma theta kappa h B eps Hk Hs Hnet.
lra.
Qed.

Theorem paper_main_head_soft_clipped_lower_tail U n m q r s beta gamma theta kappa
    (h : paper_main_sample m (S n)) y B eps a u :
  (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  0 < beta -> 0 < gamma -> 0 < theta -> 1 <= kappa -> 0 < U -> 0 < a -> 0 < u ->
  (forall z, (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 (S q)) = 1) ->
  (forall z i, (z < r)%coq_nat -> (i <= q)%coq_nat ->
    Rabs (y z i) <= theta/sqrt(INR (S n))) ->
  paper_main_head_section_net kappa (fun k : 'I_m => paper_main_head_feature h k) B s eps ->
  Rpower.ln (INR (S q)) <= INR (S n) ->
  let k := kappa/sqrt(INR (S n)) in
  (paper_main_probability (S q) (S n)
    [set x | Rle (paper_main_data_clipped_soft U n (S q) beta gamma (fun _ q => B q) (fun z _ => y z)
      (List.seq 0 r) (List.seq 0 s) (tval x))
      (paper_main_head_soft_level n m q r beta gamma theta kappa h eps-
       paper_main_data_soft_clipping_loss U n (S q) k beta gamma (List.seq 0 r) (List.seq 0 s) a-u)] <=
    (exp(-u^2/(2*(2*k*U)^2)))%:E)%E.
Proof.
move=> Hr Hs Hb Hg Htheta Hk HU Ha Hu Hy Hlow Hnet Hlog; cbv zeta.
have HY : List.seq 0 r <> [].
{ move=> H; have HH := congr1 (@List.length nat) H; rewrite List.length_seq /= in HH; lia. }
have HQ : List.seq 0 s <> [].
{ move=> H; have HH := congr1 (@List.length nat) H; rewrite List.length_seq /= in HH; lia. }
have Hsqrt : 0 < sqrt(INR (S n)) by apply sqrt_lt_R0,lt_0_INR; lia.
have HK : 0 < kappa/sqrt(INR (S n)).
{ apply Rmult_lt_0_compat; first lra; apply Rinv_0_lt_compat; exact Hsqrt. }
have HB : forall j, (j < s)%coq_nat -> paper_main_head_cone_sphere kappa (B j).
{ move=> j Hj; have HjMC : (j < s)%N by exact/ssrnat.ltP.
  have [HC [HF _]] := (proj1 Hnet) j HjMC.
  by split. }
have Had := paper_main_data_cone_soft_admissible n (S q) r s kappa y B Hk Hy HB.
have Hmean := paper_main_head_soft_expectation n m q r s beta gamma theta kappa h y B eps
  Hr Hs Hb Hg Htheta Hk Hy Hlow Hnet Hlog.
exact: (paper_main_data_soft_clipped_lower_margin U n (S q) (kappa/sqrt(INR (S n)))
  beta gamma (fun _ q => B q) (fun z _ => y z) (List.seq 0 r) (List.seq 0 s) a
  (paper_main_head_soft_level n m q r beta gamma theta kappa h eps) u
  HU HK Hb Hg HY HQ Ha Hu Had Hmean).
Qed.
