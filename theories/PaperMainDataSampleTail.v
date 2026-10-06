(* Coordinate and pair-coherence events for the Gaussian data sample
   (lem:data of the paper, eq:coord-max and eq:coherence).

   The sample x : paper_main_sample n d of n points of R^d has the law
   paper_main_probability n d, the measure gaussian_product_law (n * d). Its
   points are x_i = paper_main_point x i, with coordinates x_ia.
   1. Coordinates (paper_main_data_coordinate_tail): for u > 0, the event
      that u <= |x_ia| for some i < n and a < d is measurable with
      probability at most 2 n d exp(-u^2/2). Each coordinate is the unit
      linear form with a Kronecker coefficient vector
      (paper_main_gaussian_unit_linear_absolute_tail), then a union bound
      (paper_main_gaussian_union_bound).
   2. Pairs (paper_main_data_pair_tail): for i < j < n and A, B > 0, the
      event that |x_i|^2 <= A^2 and B <= |<x_i, x_j>| is measurable with
      probability at most 2 exp(-B^2/(2 A^2)). The sample splits before row
      j (paper_main_split_points, after the cast n = j + (n - j)). x_i lies
      in the first part and x_j is the first point of the second part. For
      each fixed first part, with v = x_i, the section is empty when
      |v|^2 > A^2 or v = 0. Otherwise it is the event B/|v| <= |<c, z>| for
      the unit vector c = v/|v| padded with zeros. Its probability is then
      at most 2 exp(-B^2/(2|v|^2)) <= 2 exp(-B^2/(2 A^2)). The bound for the
      whole event is paper_main_split_points_section_bound
      (PaperMainHeadLawBounds).
   3. Coherence. <W_i, W_j> = ((x_i^T x_j)^2 - |x_i|^2 - |x_j|^2 + d) / d
      (paper_main_data_feature_pairing_formula). It holds for every d; for
      d = 0 both sides are 0, since division by 0 gives 0. The exceptional
      event paper_main_data_coherence_event n d B is the union over
      i < j < n of the pair events with A^2 = 4 d. For d > 0 and B > 0 it is
      measurable with probability at most n^2 2 exp(-B^2/(8 d))
      (paper_main_data_coherence_tail). Since <x_i, x_j> and <W_i, W_j> are
      symmetric in i and j, the pairs i < j suffice. If every row has
      |x_k|^2 <= 4 d, as paper_main_data_radius_good gives outside the
      radius event, and x is outside the coherence event, then
      |<W_i, W_j>| <= B^2/d + 9 for all distinct i, j < n
      (paper_main_data_coherence_good). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  GaussianCoordinateDefinitions GaussianCoordinatePolynomialContinuity GaussianFiniteSums
  GaussianProbabilityProductDefinitions GaussianProbabilityProductMeasure
  GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryGram PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCoefficients PaperMainGeometryHeadFeature PaperMainMatrixDuality
  PaperMainGordonProcessCovariance PaperMainGordonLipschitz PaperMainGaussianLinearLaw
  PaperMainGaussianTails
  PaperMainGaussianUnion PaperMainSampling PaperMainHeadLaw PaperMainHeadLawBounds
  PaperMainSymmetricBilinear PaperMainDataFeatureMomentsCoordinates.
From EllipsoidFitting Require Import RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* Coordinates of the sample points. *)
Lemma pmds_point_entry n d (x : paper_main_sample n d) (i : nat) (a : 'I_d) :
  paper_main_point x i a ord0 = List.nth (i * d + a)%N (tval x) 0.
Proof. by rewrite /paper_main_point mxE. Qed.

(* sum_l delta_kl f l = f k. *)
Lemma pmds_kron_sum D k (f : nat -> R) : (k < D)%coq_nat ->
  finite_sum (fun l => pmdf_kron k l * f l) (List.seq 0 D) = f k.
Proof.
elim: D => [|D IH] Hk; first lia.
rewrite finite_sum_seq_S.
case: (Nat.eq_dec k D) => [->|Hne].
- rewrite pmdf_kron_refl.
  have -> : finite_sum (fun l => pmdf_kron D l * f l) (List.seq 0 D) = 0.
    rewrite -(finite_sum_zero (List.seq 0 D)); apply: finite_sum_ext => l Hl.
    apply List.in_seq in Hl.
    by rewrite /pmdf_kron (proj2 (Nat.eqb_neq D l) ltac:(lia)); ring.
  ring.
- rewrite (IH ltac:(lia)).
  by rewrite /pmdf_kron (proj2 (Nat.eqb_neq k D) Hne); ring.
Qed.

(* One coordinate: a unit linear form. *)
Definition pmds_coordinate_set D k (u : R) : set (D.-tuple T) :=
  [set x | Rle u (Rabs (List.nth k (tval x) 0))].

Lemma pmds_coordinate_tail D k u : (k < D)%coq_nat -> 0 < u ->
  measurable (pmds_coordinate_set D k u) /\
  (gaussian_product_law D (pmds_coordinate_set D k u) <= (2 * exp (- u ^ 2 / 2))%:E)%E.
Proof.
move=> Hk Hu.
have E : pmds_coordinate_set D k u =
    [set x | Rle u (Rabs (paper_main_gaussian_linear_random D (pmdf_kron k) x))].
  by apply/seteqP; split => x /=;
    rewrite /paper_main_gaussian_linear_random /paper_main_gordon_dot pmds_kron_sum.
rewrite E; split; first exact: paper_main_gaussian_linear_absolute_measurable.
apply: paper_main_gaussian_unit_linear_absolute_tail => //.
by rewrite /paper_main_gordon_dot pmds_kron_sum // pmdf_kron_refl.
Qed.

(* 1. The coordinate union event. *)
Definition paper_main_data_coordinate_event n d (u : R) : set (paper_main_sample n d) :=
  [set x | exists (i : 'I_n) (a : 'I_d), Rle u (Rabs (paper_main_point x i a ord0))].

Lemma pmds_index_lt n d (i : 'I_n) (a : 'I_d) : (i * d + a < n * d)%coq_nat.
Proof.
have /ssrnat.ltP Hi := ltn_ord i; have /ssrnat.ltP Ha := ltn_ord a.
rewrite -!multE -!plusE; nia.
Qed.

Theorem paper_main_data_coordinate_tail n d u :
  0 < u ->
  measurable (paper_main_data_coordinate_event n d u) /\
  (paper_main_probability n d (paper_main_data_coordinate_event n d u) <=
    (2 * INR n * INR d * exp (- u ^ 2 / 2))%:E)%E.
Proof.
move=> Hu.
pose E := fun k => pmds_coordinate_set (n * d) k u.
have HS : forall k, List.In k (List.seq 0 (n * d)) -> (k < n * d)%coq_nat.
  by move=> k /List.in_seq; lia.
have HE : paper_main_data_coordinate_event n d u =
    paper_main_finite_event_union (List.seq 0 (n * d)) E.
  apply/seteqP; split => x.
  - move=> [i [a H]]; apply/paper_main_finite_event_union_member.
    exists (i * d + a)%N; split; last by move: H; rewrite pmds_point_entry.
    by apply/List.in_seq; split; [lia | have := pmds_index_lt n d i a; lia].
  - move/paper_main_finite_event_union_member => [k [Hk H]].
    have /ssrnat.ltP Hk' := HS k Hk.
    have Hd : (0 < d)%N by rewrite lt0n; apply/eqP => Hd0; move: Hk'; rewrite Hd0 muln0 ltn0.
    have Hq : (k %/ d < n)%N by rewrite ltn_divLR.
    exists (Ordinal Hq).
    exists (Ordinal (ltn_pmod k Hd)).
    by rewrite pmds_point_entry /= -divn_eq.
have HM : forall k, List.In k (List.seq 0 (n * d)) -> measurable (E k).
  by move=> k Hk; exact: (pmds_coordinate_tail (n * d) k u (HS k Hk) Hu).1.
rewrite HE; split; first exact: paper_main_gaussian_union_measurable.
apply: le_trans.
  apply: (paper_main_gaussian_union_bound (n * d) _ E (2 * exp (- u ^ 2 / 2)) HM).
  by move=> k Hk; exact: (pmds_coordinate_tail (n * d) k u (HS k Hk) Hu).2.
by rewrite List.length_seq -multE mult_INR lee_fin RmultE mulrCA !mulrA.
Qed.

(* 3. The coherence formula for the head features. *)
Theorem paper_main_data_feature_pairing_formula n d (x : paper_main_sample n d) i j :
  paper_main_pairing (paper_main_head_feature x i) (paper_main_head_feature x j) =
  ((((paper_main_point x i)^T *m paper_main_point x j) ord0 ord0)%R ^ 2 -
   (((paper_main_point x i)^T *m paper_main_point x i) ord0 ord0)%R -
   (((paper_main_point x j)^T *m paper_main_point x j) ord0 ord0)%R + INR d) / INR d.
Proof.
set u := paper_main_point x i; set v := paper_main_point x j.
have HI : paper_main_pairing (1%:M : 'M[R]_d) 1%:M = (d%:R)%R.
  rewrite pmh_pairing_id /paper_main_trace.
  under eq_bigr do rewrite mxE eqxx.
  by rewrite sumr_const card_ord.
have Hs : ((Num.sqrt (d%:R))^-1 * (Num.sqrt (d%:R))^-1 = (d%:R)^-1 :> R)%R.
  by rewrite -invfM -expr2 sqr_sqrtr // ler0n.
rewrite /paper_main_head_feature -/u -/v !paper_main_pairing_scale pmh_pairingZl.
rewrite pmh_pairingBl !pmh_pairingBr pmsb_pairing_outer_outer.
rewrite (paper_main_pairingC _ (u *m u^T)) !pmsb_pairing_outer !mulmx1 HI.
rewrite (paper_main_inner_sym _ v u) INRE RdivE RpowE RplusE !RminusE.
rewrite mulrA Hs.
by rewrite mulrC expr2 opprB addrA addrAC.
Qed.

(* 2. Pairs of rows. *)
Lemma pmds_exp_le x y : x <= y -> exp x <= exp y.
Proof.
move=> H; case: (Rle_lt_or_eq_dec x y H) => [Hlt|->]; last exact: Rle_refl.
exact: Rlt_le _ _ (exp_increasing _ _ Hlt).
Qed.

Lemma pmds_sum_prefix D d (f : nat -> R) : (d <= D)%coq_nat ->
  (forall k, (d <= k)%coq_nat -> f k = 0) ->
  finite_sum f (List.seq 0 D) = finite_sum f (List.seq 0 d).
Proof.
move=> Hd Hf.
have -> : D = Nat.add d (Nat.sub D d) by lia.
rewrite finite_sum_seq_split.
have -> : finite_sum (fun k => f (Nat.add d k)) (List.seq 0 (Nat.sub D d)) = 0.
  rewrite -(finite_sum_zero (List.seq 0 (Nat.sub D d))); apply: finite_sum_ext => k _.
  by apply: Hf; lia.
ring.
Qed.

(* The section tail: for fixed coordinates vf of x_i and z of law
   gaussian_product_law (r * d), r > 0, with Q = sum_a vf_a^2. *)
Definition pmds_section_set r d (vf : nat -> R) (A B : R) : set (paper_main_sample r d) :=
  [set z | Rle (finite_sum (fun a => vf a * vf a) (List.seq 0 d)) (A ^ 2) /\
     Rle B (Rabs (finite_sum (fun a => vf a * List.nth a (tval z) 0) (List.seq 0 d)))].

Lemma pmds_linear_section_tail r d (vf : nat -> R) A B :
  (0 < r)%N -> 0 < A -> 0 < B ->
  (paper_main_probability r d (pmds_section_set r d vf A B) <=
    (2 * exp (- B ^ 2 / (2 * A ^ 2)))%:E)%E.
Proof.
move=> Hr HA HB; rewrite /pmds_section_set.
set Q := finite_sum (fun a => vf a * vf a) (List.seq 0 d).
have HQ0 : 0 <= Q by apply: finite_sum_nonneg => a _; nra.
have Hp : (0%:E <= (2 * exp (- B ^ 2 / (2 * A ^ 2)))%:E)%E.
  rewrite lee_fin; apply: mulr_ge0 => //; apply/RleP; exact: Rlt_le _ _ (exp_pos _).
have Hrd : (d <= r * d)%coq_nat.
  have /ssrnat.ltP Hr' := Hr; rewrite -multE; nia.
case: (Rle_dec Q (A ^ 2)) => HQA; last first.
  have -> : [set z : paper_main_sample r d |
      Rle Q (A ^ 2) /\ Rle B (Rabs (finite_sum (fun a => vf a * List.nth a (tval z) 0)
        (List.seq 0 d)))] = set0.
    by apply/seteqP; split => z //= [H _].
  by rewrite /paper_main_probability measure0.
case: (Req_dec Q 0) => HQ.
  have -> : [set z : paper_main_sample r d |
      Rle Q (A ^ 2) /\ Rle B (Rabs (finite_sum (fun a => vf a * List.nth a (tval z) 0)
        (List.seq 0 d)))] = set0.
    apply/seteqP; split => z //= [_ H].
    have CS := paper_main_gordon_sum_cauchy vf (fun a => List.nth a (tval z) 0) (List.seq 0 d).
    have EQ : finite_sum (fun i => vf i ^ 2) (List.seq 0 d) = Q.
      by apply: finite_sum_ext => a _; ring.
    rewrite EQ HQ Rmult_0_l in CS.
    set S := finite_sum (fun a => vf a * List.nth a (tval z) 0) (List.seq 0 d) in H CS.
    have HS : S = 0 by nra.
    by move: H; rewrite HS Rabs_R0; lra.
  by rewrite /paper_main_probability measure0.
have HQp : 0 < Q by lra.
set s := sqrt Q.
have Hs : 0 < s by exact: sqrt_lt_R0.
have Hs2 : s * s = Q by exact: sqrt_sqrt.
pose c := fun k => (if Nat.ltb k d then vf k else 0) / s.
have Hc0 : forall k, (d <= k)%coq_nat -> c k = 0.
  by move=> k Hk; rewrite /c (proj2 (Nat.ltb_ge k d) Hk); field; lra.
have Hcc : forall k, (d <= k)%coq_nat -> c k * c k = 0.
  by move=> k Hk; rewrite (Hc0 k Hk); ring.
have Hc : paper_main_gordon_dot (r * d) c c = 1.
  rewrite /paper_main_gordon_dot (pmds_sum_prefix _ _ _ Hrd Hcc).
  transitivity (Q / (s * s)); last by rewrite Hs2; field; lra.
  rewrite /Rdiv -finite_sum_scale_r; apply: finite_sum_ext => a /List.in_seq Ha.
  by rewrite /c (proj2 (Nat.ltb_lt a d) ltac:(lia)); field; lra.
have Hlin : forall z : (r * d)%N.-tuple T,
    paper_main_gaussian_linear_random (r * d) c z =
    finite_sum (fun a => vf a * List.nth a (tval z) 0) (List.seq 0 d) / s.
  move=> z; rewrite /paper_main_gaussian_linear_random /paper_main_gordon_dot.
  have Hcz : forall k, (d <= k)%coq_nat -> c k * List.nth k (tval z) 0 = 0.
    by move=> k Hk; rewrite (Hc0 k Hk); ring.
  rewrite (pmds_sum_prefix _ _ _ Hrd Hcz).
  rewrite /Rdiv -finite_sum_scale_r; apply: finite_sum_ext => a /List.in_seq Ha.
  by rewrite /c (proj2 (Nat.ltb_lt a d) ltac:(lia)); field; lra.
have -> : [set z : paper_main_sample r d |
    Rle Q (A ^ 2) /\ Rle B (Rabs (finite_sum (fun a => vf a * List.nth a (tval z) 0)
      (List.seq 0 d)))] =
  [set z | Rle (B / s) (Rabs (paper_main_gaussian_linear_random (r * d) c z))].
  have Hsi : 0 <= / s by apply: Rlt_le; exact: Rinv_0_lt_compat.
  apply/seteqP; split => z /=;
    rewrite Hlin /Rdiv Rabs_mult (Rabs_pos_eq (/ s) Hsi).
  - by move=> [_ H]; exact: Rmult_le_compat_r.
  - move=> H; split => //.
    have := Rmult_le_compat_r s _ _ (Rlt_le _ _ Hs) H.
    by rewrite !Rmult_assoc (Rinv_l s ltac:(lra)) !Rmult_1_r.
apply: le_trans.
  apply: (paper_main_gaussian_unit_linear_absolute_tail (r * d) c (B / s) Hc).
  by apply: Rdiv_lt_0_compat.
rewrite lee_fin; apply: ler_wpM2l => //; apply/RleP; apply: pmds_exp_le.
have HQinv : / (2 * A ^ 2) <= / (2 * Q).
  apply: Rinv_le_contravar; lra.
have HB2 : 0 <= B ^ 2 by nra.
have -> : (B / s) ^ 2 = B ^ 2 / Q by rewrite -Hs2; field; lra.
rewrite /Rdiv.
have := Rmult_le_compat_l _ _ _ HB2 HQinv.
have -> : B ^ 2 * / (2 * Q) = B ^ 2 * / Q * / 2 by field; lra.
lra.
Qed.

(* Points of cast and split samples. *)
Lemma pmds_point_dot2 k r d (h : paper_main_sample k d) (z : paper_main_sample r d) (i j : nat) :
  (((paper_main_point h i)^T *m paper_main_point z j) ord0 ord0)%R =
  finite_sum (fun a => List.nth (i * d + a)%N (tval h) 0 * List.nth (j * d + a)%N (tval z) 0)
    (List.seq 0 d).
Proof.
rewrite finite_sum_seqE pmh_vec_dot.
by apply: eq_bigr => a _; rewrite !pmds_point_entry.
Qed.

Lemma pmds_point_tcast n m d (h : (n * d)%N = (m * d)%N) (x : paper_main_sample n d) i :
  paper_main_point (tcast h x : paper_main_sample m d) i = paper_main_point x i.
Proof. by apply/matrixP => a b; rewrite !mxE val_tcast. Qed.

Lemma pmds_take_nth k m (x : (Nat.add k m).-tuple T) l :
  (l < k)%coq_nat ->
  List.nth l (tval (paper_main_take_coordinates k m x)) 0 = List.nth l (tval x) 0.
Proof.
elim: k x l => [|k IH] x l Hl; first lia.
case: l Hl => [|l] Hl.
- change (tnth x ord0 = List.nth 0 (tval x) 0).
  by rewrite gpp_nthE (tnth_nth 0%R).
- change (List.nth l (tval (paper_main_take_coordinates k m
    (paper_main_tail_coordinate (Nat.add k m) x))) 0 = List.nth (S l) (tval x) 0).
  rewrite (IH _ l ltac:(lia)).
  change (List.nth l (behead (tval x)) 0 = List.nth (S l) (tval x) 0).
  by case: (tval x) => [|a xs] //=; case: l {IH Hl}.
Qed.

Lemma pmds_take_point k r d (y : paper_main_sample (k + r) d) i :
  (i < k)%N -> paper_main_point (paper_main_take_points k r d y) i = paper_main_point y i.
Proof.
move=> Hi; apply/matrixP => a b; rewrite !mxE /paper_main_take_points.
have Hl : (i * d + a < k * d)%coq_nat.
  have /ssrnat.ltP Hi' := Hi; have /ssrnat.ltP Ha := ltn_ord a.
  rewrite -!multE -!plusE; nia.
by rewrite (pmds_take_nth _ _ _ _ Hl) val_tcast.
Qed.

(* The pair event on the split sample. *)
Definition pmds_pair_product k r d (A B : R) (i : nat) :
    set (paper_main_sample k d * paper_main_sample r d) :=
  [set p | Rle (((paper_main_point p.1 i)^T *m paper_main_point p.1 i) ord0 ord0)%R (A ^ 2) /\
     Rle B (Rabs (((paper_main_point p.1 i)^T *m paper_main_point p.2 0) ord0 ord0)%R)].

Lemma pmds_pair_product_measurable k r d A B i :
  (i < k)%N -> (0 < r)%N -> measurable (pmds_pair_product k r d A B i).
Proof.
move=> Hi Hr.
pose f1 := fun p : paper_main_sample k d * paper_main_sample r d =>
  (\sum_(a < d) List.nth (i * d + a)%N (tval p.1) 0 * List.nth (i * d + a)%N (tval p.1) 0)%R.
pose f2 := fun p : paper_main_sample k d * paper_main_sample r d =>
  (\sum_(a < d) List.nth (i * d + a)%N (tval p.1) 0 * List.nth (0 * d + a)%N (tval p.2) 0)%R.
have Mc1 : forall l, (l < k * d)%N -> measurable_fun [set: paper_main_sample k d *
    paper_main_sample r d] (fun p => List.nth l (tval p.1) 0 : measurableTypeR R).
  by move=> l Hl; exact: measurableT_comp (gpp_coordinate_measurable _ _ Hl) measurable_fst.
have Mc2 : forall l, (l < r * d)%N -> measurable_fun [set: paper_main_sample k d *
    paper_main_sample r d] (fun p => List.nth l (tval p.2) 0 : measurableTypeR R).
  by move=> l Hl; exact: measurableT_comp (gpp_coordinate_measurable _ _ Hl) measurable_snd.
have Hia : forall a : 'I_d, (i * d + a < k * d)%N.
  move=> a; apply/ssrnat.ltP; have /ssrnat.ltP Hi' := Hi; have /ssrnat.ltP Ha := ltn_ord a.
  rewrite -!multE -!plusE; nia.
have Hza : forall a : 'I_d, (0 * d + a < r * d)%N.
  move=> a; apply/ssrnat.ltP; have /ssrnat.ltP Hr' := Hr; have /ssrnat.ltP Ha := ltn_ord a.
  rewrite -!multE -!plusE; nia.
have M1 : measurable_fun setT f1.
  by apply: measurable_sum => a; apply: measurable_funM; apply: Mc1; exact: Hia.
have M2 : measurable_fun setT f2.
  by apply: measurable_sum => a; apply: measurable_funM; [apply: Mc1; exact: Hia |
    apply: Mc2; exact: Hza].
have E : pmds_pair_product k r d A B i =
    [set p | (f1 p <= A ^ 2)%R] `&` [set p | (B <= `|f2 p|)%R].
  apply/seteqP; split => p /=; rewrite /pmds_pair_product /= !pmds_point_dot2
    !finite_sum_seqE.
  - by move=> [H1 H2]; split; [apply/RleP | apply/RleP; rewrite -RabsE].
  - by move=> [/RleP H1 /RleP H2]; split => //; rewrite RabsE.
rewrite E -preimage_itvNyc -(preimage_itvcy (fun p => `|f2 p|%R)).
apply: measurableI.
- by rewrite -[f1 @^-1` _]setTI; exact: M1 measurableT _ (measurable_itv _).
- have Mn := measurableT_comp (@normr_measurable _ _) M2.
  by rewrite -[(fun p => _) @^-1` _]setTI; exact: Mn measurableT _ (measurable_itv _).
Qed.

Definition paper_main_data_pair_event n d (A B : R) (i j : nat) : set (paper_main_sample n d) :=
  [set x | Rle (((paper_main_point x i)^T *m paper_main_point x i) ord0 ord0)%R (A ^ 2) /\
     Rle B (Rabs (((paper_main_point x i)^T *m paper_main_point x j) ord0 ord0)%R)].

Theorem paper_main_data_pair_tail n d A B i j :
  (i < j)%N -> (j < n)%N -> 0 < A -> 0 < B ->
  measurable (paper_main_data_pair_event n d A B i j) /\
  (paper_main_probability n d (paper_main_data_pair_event n d A B i j) <=
    (2 * exp (- B ^ 2 / (2 * A ^ 2)))%:E)%E.
Proof.
move=> Hij Hjn HA HB.
pose r := (n - j)%N.
have Hr : (0 < r)%N by rewrite subn_gt0.
have hd : (n * d)%N = ((j + r) * d)%N by rewrite /r subnKC // ltnW.
have HE : paper_main_data_pair_event n d A B i j =
    (fun x : paper_main_sample n d => paper_main_split_points j r d (tcast hd x)) @^-1`
      pmds_pair_product j r d A B i.
  apply/seteqP; split => x /=; rewrite /pmds_pair_product /=;
    rewrite (pmds_take_point _ _ _ _ _ Hij) paper_main_drop_points_point addn0 !pmds_point_tcast;
    by [].
have Mpp := pmds_pair_product_measurable j r d A B i Hij Hr.
have Mf : measurable_fun setT
    (fun x : paper_main_sample n d => paper_main_split_points j r d (tcast hd x)).
  exact: measurableT_comp (paper_main_split_points_measurable j r d)
    (paper_main_tcast_measurable _ _ hd).
rewrite HE; split.
  by have := Mf measurableT _ Mpp; rewrite setTI.
have -> : (fun x : paper_main_sample n d => paper_main_split_points j r d (tcast hd x)) @^-1`
    pmds_pair_product j r d A B i =
  tcast hd @^-1` (paper_main_split_points j r d @^-1` pmds_pair_product j r d A B i) by [].
rewrite /paper_main_probability paper_main_tcast_law.
apply: (paper_main_split_points_section_bound j r d _ _ Mpp) => h.
have -> : xsection (pmds_pair_product j r d A B i) h =
    pmds_section_set r d (fun a => List.nth (i * d + a)%N (tval h) 0) A B.
  apply/seteqP; split => z; rewrite /xsection /= in_setE /pmds_pair_product /pmds_section_set /=;
    rewrite !pmds_point_dot2 mul0n; by [].
exact: pmds_linear_section_tail.
Qed.

(* 3. The coherence exceptional event: pairs i < j with |x_i|^2 <= 4 d. *)
Definition paper_main_data_coherence_event n d (B : R) : set (paper_main_sample n d) :=
  [set x | exists i j, (i < j)%N /\ (j < n)%N /\
     paper_main_data_pair_event n d (2 * sqrt (INR d)) B i j x].

Lemma pmds_radius_sqr d : (2 * sqrt (INR d)) ^ 2 = 4 * INR d.
Proof. by rewrite -[INR d in RHS](sqrt_sqrt _ (pos_INR d)); ring. Qed.

Theorem paper_main_data_coherence_tail n d B :
  (0 < d)%N -> 0 < B ->
  measurable (paper_main_data_coherence_event n d B) /\
  (paper_main_probability n d (paper_main_data_coherence_event n d B) <=
    (2 * INR n * INR n * exp (- B ^ 2 / (8 * INR d)))%:E)%E.
Proof.
move=> Hd HB.
have HD : 0 < INR d by apply: lt_0_INR; apply/ssrnat.ltP.
have HA : 0 < 2 * sqrt (INR d) by have := sqrt_lt_R0 _ HD; lra.
have HA8 : 2 * (2 * sqrt (INR d)) ^ 2 = 8 * INR d by rewrite pmds_radius_sqr; ring.
pose E := fun k => if (k %/ n < k %% n)%N
  then paper_main_data_pair_event n d (2 * sqrt (INR d)) B (k %/ n) (k %% n) else set0.
have Hnk : forall k, List.In k (List.seq 0 (n * n)) -> (0 < n)%N.
  move=> k /List.in_seq [_ Hk]; rewrite lt0n; apply/eqP => Hn0.
  by move: Hk; rewrite Hn0 muln0; lia.
have HE : paper_main_data_coherence_event n d B =
    paper_main_finite_event_union (List.seq 0 (n * n)) E.
  apply/seteqP; split => x.
  - move=> [i [j [Hij [Hjn H]]]]; apply/paper_main_finite_event_union_member.
    have Hn : (0 < n)%N by apply: leq_ltn_trans Hjn.
    exists (i * n + j)%N; split.
      apply/List.in_seq; split; first lia.
      have /ssrnat.ltP Hi := ltn_trans Hij Hjn; have /ssrnat.ltP Hj := Hjn.
      rewrite -!multE -!plusE; nia.
    rewrite /E (divnMDl _ _ Hn) divn_small // addn0 modnMDl modn_small //.
    by rewrite Hij.
  - move/paper_main_finite_event_union_member => [k [Hk H]].
    have Hn := Hnk k Hk.
    move: H; rewrite /E; case: ifP => [Hlt H | _ []].
    by exists (k %/ n), (k %% n); split => //; split => //; exact: ltn_pmod.
have HM : forall k, List.In k (List.seq 0 (n * n)) -> measurable (E k).
  move=> k Hk; rewrite /E; case: ifP => H; last exact: measurable0.
  exact: (paper_main_data_pair_tail n d _ B _ _ H (ltn_pmod k (Hnk k Hk)) HA HB).1.
have HP : forall k, List.In k (List.seq 0 (n * n)) ->
    (gaussian_product_law (n * d) (E k) <= (2 * exp (- B ^ 2 / (8 * INR d)))%:E)%E.
  move=> k Hk; rewrite /E; case: ifP => H.
    rewrite -HA8.
    exact: (paper_main_data_pair_tail n d _ B _ _ H (ltn_pmod k (Hnk k Hk)) HA HB).2.
  rewrite measure0 lee_fin; apply: mulr_ge0 => //; apply/RleP.
  exact: Rlt_le _ _ (exp_pos _).
rewrite HE; split; first exact: paper_main_gaussian_union_measurable.
apply: le_trans.
  exact: (paper_main_gaussian_union_bound (n * d) _ E _ HM HP).
by rewrite List.length_seq -multE mult_INR lee_fin RmultE mulrCA !mulrA.
Qed.

(* Outside the coherence event, with all |x_k|^2 <= 4 d, every distinct
   feature pairing is at most B^2/d + 9 in absolute value. *)
Theorem paper_main_data_coherence_good n d (x : paper_main_sample n d) B :
  (0 < d)%N ->
  (forall k, Nat.lt k n ->
    Rle (((paper_main_point x k)^T *m paper_main_point x k) ord0 ord0)%R (4 * INR d)) ->
  ~ paper_main_data_coherence_event n d B x ->
  forall i j, Nat.lt i n -> Nat.lt j n -> i <> j ->
    Rle (Rabs (paper_main_pairing (paper_main_head_feature x i) (paper_main_head_feature x j)))
      (B ^ 2 / INR d + 9).
Proof.
move=> Hd Hrad Hgood.
have HD : 0 < INR d by apply: lt_0_INR; apply/ssrnat.ltP.
have key : forall i j, (i < j)%N -> (j < n)%N ->
    Rle (Rabs (paper_main_pairing (paper_main_head_feature x i) (paper_main_head_feature x j)))
      (B ^ 2 / INR d + 9).
  move=> i j Hij Hjn.
  have Hin : Nat.lt i n by apply/ssrnat.ltP; exact: ltn_trans Hij Hjn.
  have Hjn' : Nat.lt j n by apply/ssrnat.ltP.
  rewrite paper_main_data_feature_pairing_formula.
  have HP := Hrad i Hin; have HQ := Hrad j Hjn'.
  have HP0 : 0 <= (((paper_main_point x i)^T *m paper_main_point x i) ord0 ord0)%R.
    by apply/RleP; exact: pmh_vec_sqr_ge0.
  have HQ0 : 0 <= (((paper_main_point x j)^T *m paper_main_point x j) ord0 ord0)%R.
    by apply/RleP; exact: pmh_vec_sqr_ge0.
  set s := (((paper_main_point x i)^T *m paper_main_point x j) ord0 ord0)%R.
  set P := (((paper_main_point x i)^T *m paper_main_point x i) ord0 ord0)%R in HP HP0 *.
  set Q := (((paper_main_point x j)^T *m paper_main_point x j) ord0 ord0)%R in HQ HQ0 *.
  have Hs : Rabs s < B.
    apply: Rnot_le_lt => HsB; apply: Hgood.
    exists i, j; split => //; split => //; split => //.
    by rewrite pmds_radius_sqr.
  have Hs2 : s ^ 2 <= B ^ 2.
    have := Rabs_pos s; rewrite -(pow2_abs s); nra.
  have HX : Rabs (s ^ 2 - P - Q + INR d) <= B ^ 2 + 9 * INR d.
    apply: Rabs_le; split; nra.
  rewrite /Rdiv Rabs_mult (Rabs_pos_eq (/ INR d) (Rlt_le _ _ (Rinv_0_lt_compat _ HD))).
  apply: Rle_trans (Rmult_le_compat_r _ _ _ (Rlt_le _ _ (Rinv_0_lt_compat _ HD)) HX) _.
  by right; field; lra.
move=> i j Hi Hj Hij.
case: (Nat.lt_total i j) => [H|[H|H]].
- by apply: key; apply/ssrnat.ltP.
- by case: Hij.
- rewrite paper_main_pairingC; apply: key; by apply/ssrnat.ltP.
Qed.
