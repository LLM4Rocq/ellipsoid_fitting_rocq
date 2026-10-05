(* Explicit concentration of quadratic data soft functionals under their actual law. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  GaussianCoordinateDefinitions GaussianProductDefinitions GaussianProbabilityProductDefinitions
  OperatorDefinitions PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHeadFeature
  PaperMainGordonLipschitz PaperMainGordonSoftMargin PaperMainMatrixTransport
  PaperMainDataFeatureMoments PaperMainDataSampleTail PaperMainDataClipped
  PaperMainDataClippedSoft PaperMainDataClippedGrowth PaperMainDataClippedMoments
  PaperMainSoftPublicFeatures PaperMainDataSoftClipping PaperMainGaussianClippingTransfer PaperMainGaussianGordonTail.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_data_soft_second_bound n N k beta gamma Y Q :=
  2*(k/sqrt(INR (S n)))^2*(4*INR (N*S n)^2+2*INR (N*S n))+
  2*paper_main_data_soft_entropy beta gamma Y Q^2.

Lemma paper_main_data_raw_clipped_soft_eq U n N beta gamma Bf yf Y Q
    (x : paper_main_sample N (S n)) :
  ~ paper_main_data_coordinate_event N (S n) U x ->
  paper_main_data_raw_soft n N beta gamma Bf yf Y Q (tval x) =
  paper_main_data_clipped_soft U n N beta gamma Bf yf Y Q (tval x).
Proof.
move=> Hx; apply: paper_main_gordon_soft_minimax_ext => z q Hz Hq.
have H := paper_main_data_clipped_score_head U n N (Bf z q) (yf z q) x
  (paper_main_data_coordinate_good N n U x Hx).
exact (Logic.eq_sym H).
Qed.

Theorem paper_main_data_soft_clipping_mean U n N k beta gamma Bf yf Y Q a :
  0 < U -> 0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] -> 0 < a ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  gaussian_iterated_expectation (N*S n) (paper_main_data_raw_soft n N beta gamma Bf yf Y Q) -
  gaussian_iterated_expectation (N*S n) (paper_main_data_clipped_soft U n N beta gamma Bf yf Y Q) <=
    paper_main_data_soft_second_bound n N k beta gamma Y Q/a +
    a*(2*INR N*INR (S n)*exp(-U^2/2)).
Proof.
move=> HU Hk Hb Hg HY HQ Ha Had.
pose F := paper_main_data_raw_soft n N beta gamma Bf yf Y Q.
pose G := paper_main_data_clipped_soft U n N beta gamma Bf yf Y Q.
pose V := paper_main_data_soft_second_bound n N k beta gamma Y Q.
have [IF [EF [IF2 [EF2 HVF]]]] :=
  paper_main_data_raw_soft_square_law n N k beta gamma Bf yf Y Q Hk Hb Hg HY HQ Had.
have [IG [EG [IG2 [EG2 HVG]]]] :=
  paper_main_data_clipped_soft_square_law U n N k beta gamma Bf yf Y Q
    (Rlt_le _ _ HU) Hk Hb Hg HY HQ Had.
have [mA Hp] := paper_main_data_coordinate_tail N (S n) U HU.
have Heq : forall x, ~ paper_main_data_coordinate_event N (S n) U x -> F (tval x) = G (tval x).
{ move=> x Hx; exact: paper_main_data_raw_clipped_soft_eq Hx. }
have HM := paper_main_gaussian_clipping_mean_loss (N*S n) F G
  (paper_main_data_coordinate_event N (S n) U) (2*INR N*INR (S n)*exp(-U^2/2)) a
  (gaussian_iterated_expectation (N*S n) F) (gaussian_iterated_expectation (N*S n) G)
  (gaussian_iterated_expectation (N*S n) (fun xs => F xs*F xs))
  (gaussian_iterated_expectation (N*S n) (fun xs => G xs*G xs))
  Ha mA Heq IF IG IF2 IG2 EF EG EF2 EG2 Hp.
change (gaussian_iterated_expectation (N*S n) (fun xs => F xs*F xs) <= V) in HVF.
change (gaussian_iterated_expectation (N*S n) (fun xs => G xs*G xs) <= V) in HVG.
have HV : (gaussian_iterated_expectation (N*S n) (fun xs => F xs*F xs)+
    gaussian_iterated_expectation (N*S n) (fun xs => G xs*G xs))/(2*a) <= V/a.
{ apply (Rmult_le_reg_r (2*a)); first lra.
  replace ((gaussian_iterated_expectation (N*S n) (fun xs => F xs*F xs)+
    gaussian_iterated_expectation (N*S n) (fun xs => G xs*G xs))/(2*a)*(2*a))
    with (gaussian_iterated_expectation (N*S n) (fun xs => F xs*F xs)+
    gaussian_iterated_expectation (N*S n) (fun xs => G xs*G xs)) by (field; lra).
  replace (V/a*(2*a)) with (2*V) by (field; lra).
  lra. }
change (gaussian_iterated_expectation (N*S n) F - gaussian_iterated_expectation (N*S n) G <=
  V/a+a*(2*INR N*INR (S n)*exp(-U^2/2))).
change (gaussian_iterated_expectation (N*S n) F - gaussian_iterated_expectation (N*S n) G <=
  (gaussian_iterated_expectation (N*S n) (fun xs => F xs*F xs)+
   gaussian_iterated_expectation (N*S n) (fun xs => G xs*G xs))/(2*a)+
  a*(2*INR N*INR (S n)*exp(-U^2/2))) in HM.
lra.
Qed.

Definition paper_main_data_soft_clipping_loss U n N k beta gamma Y Q a :=
  paper_main_data_soft_second_bound n N k beta gamma Y Q/a +
  a*(2*INR N*INR (S n)*exp(-U^2/2)).

Lemma paper_main_data_soft_clipped_mean_margin U n N k beta gamma Bf yf Y Q a b :
  0 < U -> 0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] -> 0 < a ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  b <= gaussian_iterated_expectation (N*S n) (paper_main_data_raw_soft n N beta gamma Bf yf Y Q) ->
  b-paper_main_data_soft_clipping_loss U n N k beta gamma Y Q a <=
    gaussian_iterated_expectation (N*S n) (paper_main_data_clipped_soft U n N beta gamma Bf yf Y Q).
Proof.
move=> HU Hk Hb Hg HY HQ Ha Had Hmean.
have HM := paper_main_data_soft_clipping_mean U n N k beta gamma Bf yf Y Q a HU Hk Hb Hg HY HQ Ha Had.
rewrite /paper_main_data_soft_clipping_loss; lra.
Qed.

Theorem paper_main_data_soft_clipped_lower_margin U n N k beta gamma Bf yf Y Q a b u :
  0 < U -> 0 < k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] -> 0 < a -> 0 < u ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  b <= gaussian_iterated_expectation (N*S n) (paper_main_data_raw_soft n N beta gamma Bf yf Y Q) ->
  (gaussian_product_law (N*S n)
    [set x | Rle (paper_main_data_clipped_soft U n N beta gamma Bf yf Y Q (tval x))
      (b-paper_main_data_soft_clipping_loss U n N k beta gamma Y Q a-u)] <=
    (exp(-u^2/(2*(2*k*U)^2)))%:E)%E.
Proof.
move=> HU Hk Hb Hg HY HQ Ha Hu Had Hmean.
have HM := paper_main_data_soft_clipped_mean_margin U n N k beta gamma Bf yf Y Q a b
  HU (Rlt_le _ _ Hk) Hb Hg HY HQ Ha Had Hmean.
have HL : 0 < 2*k*U by apply Rmult_lt_0_compat => //; apply Rmult_lt_0_compat => //; lra.
apply: (paper_main_gaussian_lipschitz_lower_margin (N*S n)
  (paper_main_data_clipped_soft U n N beta gamma Bf yf Y Q) (2*k*U)
  (b-paper_main_data_soft_clipping_loss U n N k beta gamma Y Q a) u HL _ HM Hu).
move=> xs ys _ _.
exact: (paper_main_data_clipped_soft_lipschitz U n N k beta gamma Bf yf Y Q xs ys
  (Rlt_le _ _ HU) (Rlt_le _ _ Hk) Hb Hg HY HQ Had).
Qed.

Theorem paper_main_data_raw_soft_public_mean n N k beta gamma y B Y Q :
  0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  paper_main_data_clipped_admissible n N k (fun _ q => B q) (fun z _ => y z) Y Q ->
  fine (\int[paper_main_probability N (S n)]_x
    (paper_main_public_soft_minimax (S n) N beta gamma y B Y Q (paper_main_head_feature x))%:E)%E =
  gaussian_iterated_expectation (N*S n)
    (paper_main_data_raw_soft n N beta gamma (fun _ q => B q) (fun z _ => y z) Y Q).
Proof.
move=> Hk Hb Hg HY HQ Had.
have [_ [HE _]] := paper_main_data_raw_soft_square_law n N k beta gamma
  (fun _ q => B q) (fun z _ => y z) Y Q Hk Hb Hg HY HQ Had.
change (fine (\int[gaussian_product_law (N*S n)]_x
  (paper_main_data_raw_soft n N beta gamma (fun _ q => B q) (fun z _ => y z) Y Q (tval x))%:E)%E =
  gaussian_iterated_expectation (N*S n)
    (paper_main_data_raw_soft n N beta gamma (fun _ q => B q) (fun z _ => y z) Y Q)).
by rewrite HE.
Qed.
