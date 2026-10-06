(* Means of the finite-prior data and hybrid soft losses on full rows.

   With the row losses and the normalized soft losses Z_data, Z_goe of
   PaperMainHybridFiniteArray:
   1. One row (head g, bulk y or z): for every f, the expected soft minima
      of f j + data loss and of f j + hybrid loss differ by at most
      2 eta + C eps S. paper_main_loss_conditional_suffix_comparison
      integrates the head block g of the row. For fixed g the offsets
      a_j = g^T H_j g - Tr H_j - b_j are fixed numbers, so the one-row
      comparison applies with T j = B_j. C depends only on beta and eta.
   2. Repeated row replacement (PaperMainLossReplacement) and the entropy
      shift give |E Z_data - E Z_goe| <= 2 eta + C eps S for every N >= 1,
      all head and bulk dimensions, every finite prior and all offsets.
   3. Off the joint event of PaperMainHybridAssembly, moved to the row
      layout by the permutation law, every admissible state has hybrid risk
      at least e, so Z_goe >= e. paper_main_loss_expected_gap gives
      E Z_goe >= e (1 - exp (- c d^2)).
   4. Hence E Z_data >= e (1 - exp (- c d^2)) - (2 eta + C eps S). *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCovarianceLinear
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  MaximumRadiusMoments
  PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainConeConditionOperator
  PaperMainGaussianFeatureCoordinates PaperMainDataFeatureMomentsCoordinates
  PaperMainDataFeatureMoments PaperMainProjectionPublic PaperMainTranslatedLoss
  PaperMainLossArray PaperMainLossRowIncrement PaperMainLossSoftCost PaperMainLossBlockComparison
  PaperMainLossReplacement PaperMainLossNormalizedArray PaperMainLossExpectedGap
  PaperMainHeadLaw PaperMainHybridResidual PaperMainHybridLoss PaperMainHybridAssembly
  PaperMainHybridFiniteArray.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. One row: head integration and the uniform one-row comparison. *)

Theorem paper_main_hybrid_finite_row_comparison (beta eta : R) :
  (0 < beta)%Rcoq -> (0 < eta)%Rcoq ->
  exists C, (0 <= C)%Rcoq /\
  forall r mi (f : nat -> R) (I : list nat) Hs bs (Bs : nat -> 'M[R]_(S mi)) (eps Sf : R)
    (i : nat),
    I <> nil -> (0 <= eps)%Rcoq -> (0 <= Sf)%Rcoq ->
    (forall j, In j I -> paper_main_symmetric (Bs j)) ->
    (forall j, In j I -> paper_main_cone_opnorm_le (Bs j) eps) ->
    (forall j, In j I -> (paper_main_frobenius (Bs j) ^ 2 <= Sf ^ 2)%Rcoq) ->
    (Rabs (gaussian_iterated_expectation (r + S mi)%coq_nat
       (fun row => soft_min beta
          (fun j => f j + paper_main_hybrid_finite_data_loss r mi Hs bs Bs i j row) I) -
     gaussian_iterated_expectation (r + paper_main_symmetric_dimension mi)%coq_nat
       (fun row => soft_min beta
          (fun j => f j + paper_main_hybrid_finite_goe_loss r mi Hs bs Bs i j row) I))
     <= 2 * eta + C * eps * Sf)%Rcoq.
Proof.
move=> Hb He.
have [C [HC HH]] := paper_main_loss_row_value_comparison beta eta Hb He.
exists C; split => // r mi f I Hs bs Bs eps Sf i HI Heps HS HT HO HN.
apply: (paper_main_loss_conditional_suffix_comparison r (S mi)
  (paper_main_symmetric_dimension mi)).
- apply: (paper_main_loss_soft_regular _ _ _ _ _ 1) => //; first lra.
    by move=> j _; exact: paper_main_hybrid_finite_data_loss_continuous.
  move=> j xs _ _.
  have [H0 H1] := paper_main_hybrid_finite_data_loss_bounds r mi Hs bs Bs i j xs.
  by rewrite Rabs_right; lra.
- apply: (paper_main_loss_soft_regular _ _ _ _ _ 1) => //; first lra.
    by move=> j _; exact: paper_main_hybrid_finite_goe_loss_continuous.
  move=> j xs _ _.
  have [H0 H1] := paper_main_hybrid_finite_goe_loss_bounds r mi Hs bs Bs i j xs.
  by rewrite Rabs_right; lra.
move=> xs Hxs.
set a := fun j => paper_main_hybrid_finite_offset r Hs bs j xs.
have EQ : gaussian_iterated_expectation (S mi) (fun ys => soft_min beta (fun j =>
      (f j + paper_main_hybrid_finite_data_loss r mi Hs bs Bs i j (xs ++ ys)%list)%Rcoq) I) =
    gaussian_iterated_expectation (S mi)
      (paper_main_loss_row_value beta f I a (fun j => pmdf_quad mi (Bs j))).
  apply: gaussian_iterated_expectation_ext => ys _.
  rewrite /paper_main_loss_row_value /paper_main_hybrid_finite_data_loss /a
    /paper_main_hybrid_finite_offset.
  by rewrite paper_main_hybrid_finite_head_app // maximum_radius_skipn_append.
have EG : gaussian_iterated_expectation (paper_main_symmetric_dimension mi) (fun ys =>
      soft_min beta (fun j =>
      (f j + paper_main_hybrid_finite_goe_loss r mi Hs bs Bs i j (xs ++ ys)%list)%Rcoq) I) =
    gaussian_iterated_expectation (paper_main_symmetric_dimension mi)
      (paper_main_loss_row_value beta f I a (fun j =>
        linear_form (paper_main_symmetric_dimension mi)
          (paper_main_projection_goe_loading mi (Bs j)))).
  apply: gaussian_iterated_expectation_ext => ys _.
  rewrite /paper_main_loss_row_value /paper_main_hybrid_finite_goe_loss /a
    /paper_main_hybrid_finite_offset.
  by rewrite paper_main_hybrid_finite_head_app // maximum_radius_skipn_append.
rewrite EQ EG.
exact: (HH mi f I a Bs eps Sf HI Heps HS HT HO HN).
Qed.

(* 2. N rows: |E Z_data - E Z_goe| <= 2 eta + C eps S. *)

Theorem paper_main_hybrid_finite_mean_comparison (beta eta : R) :
  (0 < beta)%Rcoq -> (0 < eta)%Rcoq ->
  exists C, (0 <= C)%Rcoq /\
  forall N r mi (I : list nat) Hs bs (Bs : nat -> 'M[R]_(S mi)) (eps Sf : R),
    (0 < N)%coq_nat -> I <> nil -> (0 <= eps)%Rcoq -> (0 <= Sf)%Rcoq ->
    (forall j, In j I -> paper_main_symmetric (Bs j)) ->
    (forall j, In j I -> paper_main_cone_opnorm_le (Bs j) eps) ->
    (forall j, In j I -> (paper_main_frobenius (Bs j) ^ 2 <= Sf ^ 2)%Rcoq) ->
    (Rabs (gaussian_iterated_expectation (N * (r + S mi))%coq_nat
       (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs) -
     gaussian_iterated_expectation (N * (r + paper_main_symmetric_dimension mi))%coq_nat
       (paper_main_hybrid_finite_goe N r mi beta I Hs bs Bs))
     <= 2 * eta + C * eps * Sf)%Rcoq.
Proof.
move=> Hb He.
have [C [HC HR]] := paper_main_hybrid_finite_row_comparison beta eta Hb He.
exists C; split => // N r mi I Hs bs Bs eps Sf HN HI Heps HS HT HO HF.
set p := (r + S mi)%coq_nat.
set q := (r + paper_main_symmetric_dimension mi)%coq_nat.
set ellQ := paper_main_hybrid_finite_data_loss r mi Hs bs Bs.
set ellG := paper_main_hybrid_finite_goe_loss r mi Hs bs Bs.
have HQC : forall i j, (i < N)%coq_nat -> In j I -> finite_joint_continuous p (ellQ i j).
  by move=> i j _ _; exact: paper_main_hybrid_finite_data_loss_continuous.
have HQB : forall i j xs, (i < N)%coq_nat -> In j I -> length xs = p ->
    (0 <= ellQ i j xs <= 1)%Rcoq.
  by move=> i j xs _ _ _; exact: paper_main_hybrid_finite_data_loss_bounds.
have HGC : forall i j, (i < N)%coq_nat -> In j I -> finite_joint_continuous q (ellG i j).
  by move=> i j _ _; exact: paper_main_hybrid_finite_goe_loss_continuous.
have HGB : forall i j xs, (i < N)%coq_nat -> In j I -> length xs = q ->
    (0 <= ellG i j xs <= 1)%Rcoq.
  by move=> i j xs _ _ _; exact: paper_main_hybrid_finite_goe_loss_bounds.
have HA := paper_main_loss_array_comparison p q N beta I ellQ ellG (2 * eta + C * eps * Sf)%Rcoq
  HI Hb HQC HQB HGC HGB (fun i f _ => HR r mi f I Hs bs Bs eps Sf i HI Heps HS HT HO HF)
  (fun _ => 0%Rcoq).
have IQ := pmdf_regular_integrable
  (paper_main_loss_array_soft_regular p N beta (fun _ => 0%Rcoq) I ellQ HI Hb HQC HQB).
have IG := pmdf_regular_integrable
  (paper_main_loss_array_soft_regular q N beta (fun _ => 0%Rcoq) I ellG HI Hb HGC HGB).
rewrite /paper_main_hybrid_finite_data /paper_main_hybrid_finite_goe
  /paper_main_loss_normalized_array -/p -/q -/ellQ -/ellG.
rewrite (paper_main_loss_entropy_shift_expectation _ N beta I _ IQ)
  (paper_main_loss_entropy_shift_expectation _ N beta I _ IG).
have HNpos : (0 < INR N)%Rcoq by apply: lt_0_INR.
have Hinv : (0 < / INR N)%Rcoq by apply: Rinv_0_lt_compat.
have key : forall A B L Bd : R, (Rabs (A - B) <= INR N * Bd)%Rcoq ->
    (Rabs (/ INR N * (A + L) - / INR N * (B + L)) <= Bd)%Rcoq.
  move=> A B L Bd H.
  have -> : (/ INR N * (A + L) - / INR N * (B + L) = / INR N * (A - B))%Rcoq by ring.
  have Hr : Rabs (/ INR N) = / INR N by apply: Rabs_right; lra.
  rewrite Rabs_mult Hr.
  have H2 := Rmult_le_compat_l _ _ _ (Rlt_le _ _ Hinv) H.
  have E : (/ INR N * (INR N * Bd) = Bd)%Rcoq by field; lra.
  lra.
exact: key.
Qed.

(* 3. The hybrid mean from the joint event of PaperMainHybridAssembly and
   paper_main_loss_expected_gap. The density tolerance is shrunk to at most
   gamma / 2, so that N >= 1. *)

Lemma paper_main_hybrid_finite_density_pos (gamma kappa : R) (d N : nat) :
  (0 < gamma)%Rcoq -> (kappa <= gamma / 2)%Rcoq -> (0 < d)%N ->
  (Rabs (INR N - gamma * INR d ^ 2) <= kappa * INR d ^ 2)%Rcoq -> (0 < N)%coq_nat.
Proof.
move=> Hg Hk Hd HN.
have HdR : (1 <= INR d)%Rcoq by apply: (le_INR 1); apply/ssrnat.leP.
have Hd2 : (0 <= INR d ^ 2)%Rcoq by apply: pow2_ge_0.
apply: INR_lt; rewrite /=.
have H1 := Rle_abs (- (INR N - gamma * INR d ^ 2)); rewrite Rabs_Ropp in H1.
have : (gamma / 2 * INR d ^ 2 <= gamma * INR d ^ 2 - kappa * INR d ^ 2)%Rcoq.
  by have := Rmult_le_compat_r _ _ _ Hd2 Hk; lra.
have : (0 < gamma / 2 * INR d ^ 2)%Rcoq.
  apply: Rmult_lt_0_compat; first lra.
  by apply: pow_lt; lra.
lra.
Qed.

Theorem paper_main_hybrid_finite_goe_mean (gamma : R) :
  (1 / 4 < gamma)%Rcoq ->
  exists (kappa e c : R) (d0 : nat),
    (0 < kappa)%Rcoq /\ (kappa <= gamma / 2)%Rcoq /\ (0 < e)%Rcoq /\ (0 < c)%Rcoq /\
    forall (d N r mi : nat) (beta : R) (I : list nat) (Hs : nat -> 'M[R]_r) (bs : nat -> R)
      (Bs : nat -> 'M[R]_(S mi)),
      (d0 <= d)%N ->
      (Rabs (INR N - gamma * INR d ^ 2) <= kappa * INR d ^ 2)%Rcoq ->
      (INR r <= sqrt (INR d) + 1)%Rcoq -> (r + mi + 1 <= d)%N ->
      I <> nil -> (0 < beta)%Rcoq ->
      (forall j, In j I -> paper_main_symmetric (Hs j)) ->
      (forall j, In j I -> paper_main_psd (Bs j)) ->
      (forall j, In j I ->
         (1 / 4 <= paper_main_frobenius (Hs j) ^ 2 + paper_main_frobenius (Bs j) ^ 2)%Rcoq) ->
      (e * (1 - exp (- c * INR d ^ 2)) <=
       gaussian_iterated_expectation (N * (r + paper_main_symmetric_dimension mi))%coq_nat
         (paper_main_hybrid_finite_goe N r mi beta I Hs bs Bs))%Rcoq.
Proof.
move=> Hg.
have [kappa [e [c [d0 [Hk [He [Hc Hall]]]]]]] := paper_main_hybrid_gap_event_joint gamma Hg.
have Hg0 : (0 < gamma)%Rcoq by lra.
exists (Rmin kappa (gamma / 2)), e, c, d0.
split; first by apply: Rmin_glb_lt; lra.
split; first exact: Rmin_r.
split => //; split => //.
move=> d N r mi beta I Hs bs Bs Hd HN Hr Hmi HI Hb HHs HBs Hn.
have Hk1 : (Rmin kappa (gamma / 2) <= kappa)%Rcoq by apply: Rmin_l.
have Hd2 : (0 <= INR d ^ 2)%Rcoq by apply: pow2_ge_0.
have HN' : (Rabs (INR N - gamma * INR d ^ 2) <= kappa * INR d ^ 2)%Rcoq.
  by apply: Rle_trans HN _; apply: Rmult_le_compat_r.
have [E [mE [PE HE]]] := Hall d N r mi Hd HN' Hr Hmi.
have Hd1 : (0 < d)%N by apply: leq_trans Hmi; rewrite addn1.
have HNpos := paper_main_hybrid_finite_density_pos gamma _ d N Hg0 (Rmin_r _ _) Hd1 HN.
set D := paper_main_symmetric_dimension mi.
set A := paper_main_hybrid_finite_split N r D @^-1` E.
have mA : measurable A.
  have := paper_main_hybrid_finite_split_measurable N r D measurableT E mE.
  by rewrite setTI.
have PA : (gaussian_product_law (N * (r + D)) A <= ((exp (- c * INR d ^ 2))%Rcoq)%:E)%E.
  by rewrite /A paper_main_hybrid_finite_split_law.
apply: (paper_main_loss_expected_gap (N * (r + D)) _ A e (exp (- c * INR d ^ 2))
  _ mA (Rlt_le _ _ He) _ _ PA).
- exact: paper_main_hybrid_finite_goe_regular.
- move=> x; have hx : length (tval x) = (N * (r + D))%coq_nat := size_tuple x.
  by have [H0 _] := paper_main_hybrid_finite_goe_bounds N r mi beta I Hs bs Bs (tval x)
    HNpos HI Hb hx.
- move=> x HAx.
  apply: (paper_main_hybrid_finite_goe_gap N r mi beta I Hs bs Bs x e HNpos HI Hb).
    by move=> j Hj; exact: (proj1 (HBs j Hj)).
  move=> j Hj.
  exact: (HE (paper_main_hybrid_finite_split N r D x) HAx (Hs j) (bs j) (Bs j)
    (HHs j Hj) (HBs j Hj) (Hn j Hj)).
Qed.

(* 4. The data mean: E Z_data >= e (1 - exp (- c d^2)) - (2 eta + C eps S).
   C depends only on beta and eta; kappa, e, c and d0 only on gamma. *)
