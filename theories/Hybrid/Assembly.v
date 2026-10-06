(* Probabilistic assembly of the hybrid risk gap.

   Hybrid sample: head coordinates h (N rows of dimension r) and bulk
   coordinates x (N rows of D = paper_main_symmetric_dimension mi GOE
   coordinates), with the product of the two Gaussian laws.
   1. Operator event in the N x D layout: the GOE feature event at
      t = N / 2 and duality give ||R(B)|| <= C(rho) sqrt N ||B||_F off an
      event of probability at most 2 exp (- N / 2), when
      rho (mi + 1)^2 <= N (the threshold arithmetic of Gaussian.Forward, with
      the threshold monotone in the column count).
   2. The exceptional event is the union of the head small-ball event of
      Head.SmallBallUniform (r >= 1; none for r = 0), the bulk
      event of Hybrid.Bulk for the actual head matrix, and the
      operator event. Off it the deterministic risk gap of
      Hybrid.Loss holds for every symmetric H, PSD B with
      ||H||_F^2 + ||B||_F^2 >= 1/4 and every b. The union has probability at
      most exp (- c d^2) for d >= d0; e, c and d0 depend only on gamma. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous Spectral.Duality
  Gordon.Bilinear Gaussian.FeatureCoordinates Gaussian.FeatureTail
  Gaussian.JointFeature Gaussian.PublicFeature Gaussian.Forward Head.Law
  Head.SmallBallNet Head.SmallBallUniform Projected.BulkEscape
  Projected.BulkComplement Projected.BulkConditional Hybrid.Density Hybrid.Bulk
  Hybrid.Residual Hybrid.Loss.
From EllipsoidFitting Require Import Analysis.RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. The operator event in the N x D layout. *)

Lemma paper_main_hybrid_operator_event mi N (rho : R) :
  (0 < rho)%Rcoq -> (0 < N)%N -> (rho * INR (S mi) ^ 2 <= INR N)%Rcoq ->
  exists E : set ((N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R)),
    measurable E /\
    (gaussian_product_law (N * paper_main_symmetric_dimension mi) E <=
      ((2 * exp (- (INR N / 2)))%Rcoq)%:E)%E /\
    forall x, ~ E x -> forall B : 'M[R]_(S mi), paper_main_symmetric B ->
      (paper_main_projected_norm (paper_main_hybrid_bulk_value N mi x B) <=
       paper_main_gaussian_forward_constant rho * sqrt (INR N) * paper_main_frobenius B)%Rcoq.
Proof.
move=> Hr HN Hratio.
have HN' : Nat.lt 0 N by apply/ssrnat.ltP.
have HNR : (0 < INR N)%Rcoq by apply: lt_0_INR.
have [E [mE [PE HE]]] := paper_main_public_gaussian_feature_exceptional_event mi N (INR N / 2)
  HN' ltac:(lra).
exists E; split => //; split; first exact: PE.
move=> x Hx B HB.
set L := (2 * sqrt 2 * paper_main_gaussian_operator_threshold N
  (paper_main_symmetric_dimension mi) (INR N / 2))%Rcoq.
have HL : (L <= paper_main_gaussian_forward_constant rho * sqrt (INR N))%Rcoq.
  apply: Rle_trans (paper_main_gaussian_forward_threshold mi N rho Hr HN' Hratio).
  have H2 : (0 <= 2 * sqrt 2)%Rcoq by have := sqrt_pos 2; lra.
  rewrite /L; apply: Rmult_le_compat_l => //.
  rewrite /paper_main_gaussian_operator_threshold; apply: sqrt_le_1_alt.
  have HC := paper_main_gaussian_entropy_positive.
  have HD : (INR (paper_main_symmetric_dimension mi) <=
      INR (paper_main_gaussian_joint_width mi))%Rcoq.
    by apply: le_INR; rewrite /paper_main_gaussian_joint_width; lia.
  nra.
set u := fun i : nat => (sqrt (INR (S mi)) *
  paper_main_pairing (paper_main_public_gaussian_row mi i (tval x)) B)%Rcoq.
have Hb := HE x Hx u B HB.
have Hpair : (sqrt (INR (S mi)) * paper_main_public_gaussian_pairing mi N u B (tval x) =
    squared_norm u (List.seq 0 N))%Rcoq.
  rewrite /paper_main_public_gaussian_pairing -finite_sum_scale /squared_norm.
  apply: finite_sum_ext => i _; rewrite /u /=; ring.
rewrite Hpair -/L in Hb.
have Hnorm : paper_main_projected_norm (paper_main_hybrid_bulk_value N mi x B) =
    euclidean_norm u (List.seq 0 N).
  rewrite /paper_main_projected_norm /euclidean_norm; congr sqrt.
  rewrite /squared_norm finite_sum_seqE /paper_main_projected_sqnorm mxE.
  apply: eq_bigr => i _; rewrite !mxE /u /=.
  by rewrite -RmultE Rmult_1_r.
rewrite Hnorm.
have Hs0 : (0 <= squared_norm u (List.seq 0 N))%Rcoq.
  by apply: Soft.Extrema.finite_sum_nonnegative => i _; apply: pow2_ge_0.
set nu := euclidean_norm u (List.seq 0 N) in Hb *.
have Hnu0 : (0 <= nu)%Rcoq by apply: sqrt_pos.
have Hnu2 : (squared_norm u (List.seq 0 N) = nu * nu)%Rcoq.
  by rewrite /nu /euclidean_norm sqrt_sqrt.
rewrite Hnu2 Rabs_right in Hb; first by apply: Rle_ge; nra.
have Hf := paper_main_frobenius_nonnegative _ B.
have HL0 : (0 <= L)%Rcoq.
  rewrite /L; apply: Rmult_le_pos; first by have := sqrt_pos 2; lra.
  exact: sqrt_pos.
have Hnu : (nu <= L * paper_main_frobenius B)%Rcoq.
  case: (Rle_lt_or_eq_dec _ _ Hnu0) => Hp; last by rewrite -Hp; nra.
  apply: (Rmult_le_reg_l nu) => //; nra.
apply: Rle_trans Hnu _.
by apply: Rmult_le_compat_r.
Qed.

(* 2. The head event: the small-ball event of Head.SmallBallUniform
   for r >= 1 and the empty event for r = 0, where the 0 x 0 head bound is
   deterministic. *)

Lemma paper_main_hybrid_head_event N r :
  (r = 0%N \/ (306432 * (INR r + 1) ^ 3 <= INR N)%Rcoq) ->
  exists Bh : set (paper_main_sample N r),
    measurable Bh /\
    (gaussian_product_law (N * r) Bh <=
      ((exp (- ((2 * ln 2 - 1) / 2432) * INR N))%Rcoq)%:E)%E /\
    forall h, ~ Bh h -> forall (H : 'M[R]_r) (b : R) (J : {set 'I_N}),
      paper_main_symmetric H -> ((1 - 1 / 1216) * INR N <= INR #|J|)%Rcoq ->
      (INR N / 4864 * paper_main_head_small_ball_sigma2 H b <=
       paper_main_head_small_ball_energy H b J h)%Rcoq.
Proof.
case: r => [|n] Hr.
  exists set0; split; first exact: measurable0.
  split; first by rewrite measure0 lee_fin; apply/RleP; apply: Rlt_le; apply: exp_pos.
  move=> h _ H b J _ HJ.
  have HJN : (#|J| <= N)%N by rewrite -[X in (_ <= X)%N](card_ord N) max_card.
  apply: (paper_main_hybrid_head_energy_zero N (N - #|J|) h); last by rewrite subKn.
  rewrite subKn //.
  have HN := pos_INR N.
  lra.
have Hpoly : (306432 * (INR n + 2) ^ 3 <= INR N)%Rcoq.
  case: Hr => // Hr.
  have -> : (INR n + 2 = INR n.+1 + 1)%Rcoq by rewrite S_INR; ring.
  exact: Hr.
exact: (paper_main_head_small_ball_uniform_poly n N Hpoly).
Qed.

(* 3. The hybrid risk gap outside an event of probability exp (- c d^2). *)

Theorem paper_main_hybrid_gap_event (gamma : R) :
  (1 / 4 < gamma)%Rcoq ->
  exists (eta e c : R) (d0 : nat),
    (0 < eta)%Rcoq /\ (0 < e)%Rcoq /\ (0 < c)%Rcoq /\
    forall (d N r mi : nat), (d0 <= d)%N ->
      (Rabs (INR N - gamma * INR d ^ 2) <= eta * INR d ^ 2)%Rcoq ->
      (INR r <= sqrt (INR d) + 1)%Rcoq -> (r + mi + 1 <= d)%N ->
      exists E : set (paper_main_sample N r *
          (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R)),
        measurable E /\
        ((gaussian_product_law (N * r) \x
            gaussian_product_law (N * paper_main_symmetric_dimension mi))%E E <=
          ((exp (- c * INR d ^ 2))%Rcoq)%:E)%E /\
        forall p, ~ E p ->
          forall (H : 'M[R]_r) (b : R) (B : 'M[R]_(S mi)),
            paper_main_symmetric H -> paper_main_psd B ->
            (1 / 4 <= paper_main_frobenius H ^ 2 + paper_main_frobenius B ^ 2)%Rcoq ->
            (e <= paper_main_hybrid_risk N
               (paper_main_hybrid_residual N r mi p.1 p.2 H b B))%Rcoq.
Proof.
move=> Hg.
have [eta [delta [t [cb [c2 [d0b [Heta [Hdelta [Hdelta' [Ht [Hcb [Hc2 Hbulk]]]]]]]]]]]] :=
  paper_main_hybrid_bulk_event gamma Hg.
set eta' := Rmin eta ((gamma - 1 / 4) / 2).
have Heta' : (0 < eta')%Rcoq by apply: Rmin_glb_lt => //; lra.
have Heta'1 : (eta' <= eta)%Rcoq by apply: Rmin_l.
have Heta'2 : (eta' <= (gamma - 1 / 4) / 2)%Rcoq by apply: Rmin_r.
set a := (gamma - eta')%Rcoq.
set A := (gamma + eta')%Rcoq.
have Ha : (1 / 4 < a)%Rcoq by rewrite /a; lra.
have HA : (0 < A)%Rcoq by rewrite /A; lra.
set beta := (cb / sqrt A)%Rcoq.
have HsA : (0 < sqrt A)%Rcoq by apply: sqrt_lt_R0.
have Hbeta : (0 < beta)%Rcoq by apply: Rdiv_lt_0_compat.
set C0 := paper_main_gaussian_forward_constant a.
have HC0 : (0 < C0)%Rcoq by apply: paper_main_gaussian_forward_constant_positive; lra.
set c4 := paper_main_hybrid_gap_constant beta C0.
have Hc4 := paper_main_hybrid_gap_constant_pos beta C0 Hbeta HC0.
set e := (exp (-1) * Rmin delta (c4 ^ 2))%Rcoq.
have He : (0 < e)%Rcoq.
  apply: Rmult_lt_0_compat; first exact: exp_pos.
  by apply: Rmin_glb_lt => //; apply: pow_lt.
set ch := ((2 * ln 2 - 1) / 2432)%Rcoq.
have Hch : (0 < ch)%Rcoq.
  rewrite /ch; apply: Rdiv_lt_0_compat; last lra.
  have := paper_main_head_small_ball_ln2_gt; lra.
set c3 := Rmin (ch * a) (Rmin c2 (a / 2)).
have Hc3 : (0 < c3)%Rcoq.
  apply: Rmin_glb_lt; first by apply: Rmult_lt_0_compat; lra.
  by apply: Rmin_glb_lt; lra.
set M := Rmax 1 (Rmax ((8273664 / a) ^ 2) (2 * ln 4 / c3)).
have [dM HdM] := INR_unbounded M.
have HM1 : (1 <= M)%Rcoq by apply: Rmax_l.
have HM2 : ((8273664 / a) ^ 2 <= M)%Rcoq by apply: Rle_trans (Rmax_r _ _); apply: Rmax_l.
have HM3 : (2 * ln 4 / c3 <= M)%Rcoq by apply: Rle_trans (Rmax_r _ _); apply: Rmax_r.
exists eta', e, (c3 / 2)%Rcoq, (maxn d0b dM).
split => //; split => //; split; first lra.
move=> d N r mi Hd HN Hr Hmi.
have Hd0b : (d0b <= d)%N by apply: leq_trans Hd; exact: leq_maxl.
have HdMd : (dM <= d)%N by apply: leq_trans Hd; exact: leq_maxr.
have HdR : (M < INR d)%Rcoq.
  by apply: Rlt_le_trans HdM _; apply: le_INR; apply/ssrnat.leP.
have Hd1 : (1 < INR d)%Rcoq by lra.
have HN1 := Rle_abs (INR N - gamma * INR d ^ 2).
have HN2 := Rle_abs (- (INR N - gamma * INR d ^ 2)); rewrite Rabs_Ropp in HN2.
have Hd2 : (0 <= INR d ^ 2)%Rcoq by apply: pow2_ge_0.
have HNa : (a * INR d ^ 2 <= INR N)%Rcoq.
  have -> : (a * INR d ^ 2 = gamma * INR d ^ 2 - eta' * INR d ^ 2)%Rcoq by rewrite /a; ring.
  lra.
have HNA : (INR N <= A * INR d ^ 2)%Rcoq.
  have -> : (A * INR d ^ 2 = gamma * INR d ^ 2 + eta' * INR d ^ 2)%Rcoq by rewrite /A; ring.
  lra.
have HNeta : (Rabs (INR N - gamma * INR d ^ 2) <= eta * INR d ^ 2)%Rcoq.
  apply: Rle_trans HN _; apply: Rmult_le_compat_r => //.
have Hsd1 : (1 <= sqrt (INR d))%Rcoq by rewrite -sqrt_1; apply: sqrt_le_1_alt; lra.
have Hsd2 : (sqrt (INR d) * sqrt (INR d) = INR d)%Rcoq by apply: sqrt_sqrt; lra.
have HsdM : (8273664 / a <= sqrt (INR d))%Rcoq.
  have Hq0 : (0 <= 8273664 / a)%Rcoq by apply: Rlt_le; apply: Rdiv_lt_0_compat; lra.
  rewrite -(sqrt_pow2 (8273664 / a)) //; apply: sqrt_le_1_alt; lra.
have Hpoly : (306432 * (INR r + 1) ^ 3 <= INR N)%Rcoq.
  have H1 : (INR r + 1 <= 3 * sqrt (INR d))%Rcoq by lra.
  have H0 := pos_INR r.
  have H2 : ((INR r + 1) ^ 3 <= 27 * (INR d * sqrt (INR d)))%Rcoq.
    have : ((INR r + 1) ^ 3 <= (3 * sqrt (INR d)) ^ 3)%Rcoq by apply: pow_incr; lra.
    have -> : ((3 * sqrt (INR d)) ^ 3 =
        27 * (sqrt (INR d) * sqrt (INR d)) * sqrt (INR d))%Rcoq by ring.
    rewrite Hsd2; lra.
  have H3 : (8273664 <= a * sqrt (INR d))%Rcoq.
    have := Rmult_le_compat_l a _ _ (ltac:(lra) : (0 <= a)%Rcoq) HsdM.
    have -> : (a * (8273664 / a) = 8273664)%Rcoq by field; lra.
    by [].
  have H4 : (8273664 * (INR d * sqrt (INR d)) <= a * INR d ^ 2)%Rcoq.
    have -> : (a * INR d ^ 2 = a * sqrt (INR d) * (INR d * sqrt (INR d)))%Rcoq.
      transitivity (a * INR d * (sqrt (INR d) * sqrt (INR d)))%Rcoq.
        by rewrite Hsd2 /=; ring.
      by ring.
    apply: Rmult_le_compat_r => //.
    by apply: Rmult_le_pos; lra.
  lra.
have HNpos : (0 < INR N)%Rcoq.
  have : (0 < a * INR d ^ 2)%Rcoq by apply: Rmult_lt_0_compat; [lra | apply: pow_lt; lra].
  lra.
have HN0 : (0 < N)%N by apply/ssrnat.ltP; apply: INR_lt; rewrite /=; lra.
have Hratio : (a * INR (S mi) ^ 2 <= INR N)%Rcoq.
  have Hm : (INR (S mi) <= INR d)%Rcoq.
    apply: le_INR; apply/ssrnat.leP.
    by apply: leq_trans Hmi; rewrite -addn1 -addnA leq_addl.
  have Hm0 := pos_INR (S mi).
  have : (INR (S mi) ^ 2 <= INR d ^ 2)%Rcoq by apply: pow_incr; lra.
  nra.
have [k [Hk1 Hk2]] := paper_main_hybrid_floor (delta * INR N) ltac:(nra).
have Hq : (INR (r * r + 1)%N <= INR r * INR r + 1)%Rcoq.
  by rewrite -plusE -multE plus_INR mult_INR /=; lra.
have [mEb [_ [PEb HEb]]] := Hbulk (N * r)%N d N r mi (r * r + 1)%N k
  (paper_main_hybrid_head_matrix N r) Hd0b HNeta Hr Hmi Hq Hk1 Hk2
  (fun a0 i => paper_main_hybrid_head_matrix_measurable N r a0 i).
have [Bh [mBh [PBh HBh]]] := paper_main_hybrid_head_event N r (or_intror Hpoly).
have [Eo [mEo [PEo HEo]]] := paper_main_hybrid_operator_event mi N a ltac:(lra) HN0 Hratio.
set Eb := [set p : paper_main_sample N r *
    (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R) |
  paper_main_projected_bad N (paper_main_symmetric_dimension mi) (r * r + 1)%N k
    (paper_main_hybrid_head_matrix N r p.1) p.2 (paper_main_projected_psd_set mi)
    (sqrt (INR (paper_main_symmetric_dimension mi) / 2) + t * INR d)%Rcoq].
exists ((Bh `*` setT) `|` Eb `|` (setT `*` Eo)).
have mA1 : measurable (Bh `*` [set: (N * paper_main_symmetric_dimension mi).-tuple
    (measurableTypeR R)]) by apply: measurableX.
have mA3 : measurable ([set: paper_main_sample N r] `*` Eo) by apply: measurableX.
split; first by apply: measurableU => //; apply: measurableU.
split.
  have mA12 := measurableU _ _ mA1 mEb.
  apply: le_trans (measureU2 _ mA12 mA3) _.
  apply: le_trans (leeD (measureU2 _ mA1 mEb) (lexx _)) _.
  have R1 : ((gaussian_product_law (N * r) \x
      gaussian_product_law (N * paper_main_symmetric_dimension mi))%E
      (Bh `*` [set: (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R)]) =
      gaussian_product_law (N * r) Bh)%E.
    rewrite product_measure1E //.
    have Hm := Gaussian.ProductLawBasics.gpp_mass (N * paper_main_symmetric_dimension mi).
    transitivity (gaussian_product_law (N * r) Bh * 1)%E; last exact: mule1.
    congr (_ * _)%E.
    exact: Hm.
  have R3 : ((gaussian_product_law (N * r) \x
      gaussian_product_law (N * paper_main_symmetric_dimension mi))%E
      ([set: paper_main_sample N r] `*` Eo) =
      gaussian_product_law (N * paper_main_symmetric_dimension mi) Eo)%E.
    rewrite product_measure1E //.
    have Hm := Gaussian.ProductLawBasics.gpp_mass (N * r).
    transitivity (1 * gaussian_product_law (N * paper_main_symmetric_dimension mi) Eo)%E;
      last exact: mul1e.
    congr (_ * _)%E.
    exact: Hm.
  have E1 : ((gaussian_product_law (N * r) \x
      gaussian_product_law (N * paper_main_symmetric_dimension mi))%E
      (Bh `*` [set: (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R)]) <=
      ((exp (- ch * INR N))%Rcoq)%:E)%E.
    by rewrite R1.
  have E3 : ((gaussian_product_law (N * r) \x
      gaussian_product_law (N * paper_main_symmetric_dimension mi))%E
      ([set: paper_main_sample N r] `*` Eo) <= ((2 * exp (- (INR N / 2)))%Rcoq)%:E)%E.
    by rewrite R3.
  apply: le_trans (leeD (leeD E1 PEb) E3) _.
  rewrite -!EFinD lee_fin; apply/RleP.
  rewrite -!RplusE.
  have Hexp_le : forall x y : R, (x <= y)%Rcoq -> (exp x <= exp y)%Rcoq.
    by move=> x y [Hxy|->]; [apply: Rlt_le; apply: exp_increasing | right].
  have Hc3a : (c3 <= ch * a)%Rcoq by apply: Rmin_l.
  have Hc3b : (c3 <= c2)%Rcoq by apply: Rle_trans (Rmin_r _ _) _; apply: Rmin_l.
  have Hc3c : (c3 <= a / 2)%Rcoq by apply: Rle_trans (Rmin_r _ _) _; apply: Rmin_r.
  set D2 := (INR d ^ 2)%Rcoq in Hd2 HNa *.
  have X1 : (exp (- ch * INR N) <= exp (- c3 * D2))%Rcoq.
    apply: Hexp_le.
    have : (c3 * D2 <= ch * a * D2)%Rcoq by apply: Rmult_le_compat_r.
    have : (ch * a * D2 <= ch * INR N)%Rcoq.
      by rewrite Rmult_assoc; apply: Rmult_le_compat_l; lra.
    lra.
  have X2 : (exp (- c2 * D2) <= exp (- c3 * D2))%Rcoq.
    apply: Hexp_le.
    have : (c3 * D2 <= c2 * D2)%Rcoq by apply: Rmult_le_compat_r.
    lra.
  have X3 : (exp (- (INR N / 2)) <= exp (- c3 * D2))%Rcoq.
    apply: Hexp_le.
    have : (c3 * D2 <= a / 2 * D2)%Rcoq by apply: Rmult_le_compat_r.
    lra.
  have X4 : (4 * exp (- c3 * D2) <= exp (- (c3 / 2) * D2))%Rcoq.
    have Hd2d : (INR d <= D2)%Rcoq by rewrite /D2 /= Rmult_1_r; nra.
    have Hbig : (2 * ln 4 / c3 < INR d)%Rcoq by lra.
    have Hc3D : (ln 4 <= c3 * D2 / 2)%Rcoq.
      have H5 : (2 * ln 4 < c3 * INR d)%Rcoq.
        have := Rmult_lt_compat_l c3 _ _ Hc3 Hbig.
        have -> : (c3 * (2 * ln 4 / c3) = 2 * ln 4)%Rcoq by field; lra.
        by [].
      have : (c3 * INR d <= c3 * D2)%Rcoq by apply: Rmult_le_compat_l; lra.
      lra.
    have H4 : (4 <= exp (c3 * D2 / 2))%Rcoq.
      have H5 := Hexp_le _ _ Hc3D.
      rewrite exp_ln in H5; first lra.
      exact: H5.
    have -> : (exp (- (c3 / 2) * D2) = exp (c3 * D2 / 2) * exp (- c3 * D2))%Rcoq.
      by rewrite -exp_plus; congr exp; field.
    have := exp_pos (- c3 * D2).
    nra.
  lra.
move=> p Hp H b B HH HB Hn.
have HpA1 : ~ Bh p.1 by move=> H1; apply: Hp; left; left; split.
have HpEb : ~ Eb p by move=> H1; apply: Hp; left; right.
have HpEo : ~ Eo p.2 by move=> H1; apply: Hp; right; split.
have HbN : (beta * sqrt (INR N) <= cb * INR d)%Rcoq.
  have H1 : (sqrt (INR N) <= sqrt A * INR d)%Rcoq.
    rewrite -(sqrt_pow2 (INR d)); first exact: pos_INR.
    rewrite -sqrt_mult; [lra | exact: pow2_ge_0 |].
    by apply: sqrt_le_1_alt.
  rewrite /beta.
  have -> : (cb * INR d = cb / sqrt A * (sqrt A * INR d))%Rcoq by field; lra.
  apply: Rmult_le_compat_l => //.
  by apply: Rlt_le; apply: Rdiv_lt_0_compat.
apply: (paper_main_hybrid_risk_gap N r mi k p.1 p.2 beta C0 delta HN0 Hbeta HC0 Hk2) => //.
- move=> H' b' J HH' HJ.
  apply: (HBh p.1 HpA1) => //.
  exact: (proj1 (HEb p HpEb J HJ)).
- move=> J HJ v c Hv.
  have := (proj2 (HEb p HpEb J HJ)) v c Hv.
  lra.
- move=> B' HB'.
  exact: (HEo p.2 HpEo B' HB').
Qed.

(* The same bound for the (N r + N D)-dimensional standard Gaussian vector
   whose first N r coordinates are the head sample and whose last N D
   coordinates are the bulk array. *)

Corollary paper_main_hybrid_gap_event_joint (gamma : R) :
  (1 / 4 < gamma)%Rcoq ->
  exists (eta e c : R) (d0 : nat),
    (0 < eta)%Rcoq /\ (0 < e)%Rcoq /\ (0 < c)%Rcoq /\
    forall (d N r mi : nat), (d0 <= d)%N ->
      (Rabs (INR N - gamma * INR d ^ 2) <= eta * INR d ^ 2)%Rcoq ->
      (INR r <= sqrt (INR d) + 1)%Rcoq -> (r + mi + 1 <= d)%N ->
      exists E : set (paper_main_sample N r *
          (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R)),
        measurable E /\
        (gaussian_product_law (Nat.add (N * r) (N * paper_main_symmetric_dimension mi))
          (paper_main_split_coordinates (N * r) (N * paper_main_symmetric_dimension mi) @^-1` E)
          <= ((exp (- c * INR d ^ 2))%Rcoq)%:E)%E /\
        forall p, ~ E p ->
          forall (H : 'M[R]_r) (b : R) (B : 'M[R]_(S mi)),
            paper_main_symmetric H -> paper_main_psd B ->
            (1 / 4 <= paper_main_frobenius H ^ 2 + paper_main_frobenius B ^ 2)%Rcoq ->
            (e <= paper_main_hybrid_risk N
               (paper_main_hybrid_residual N r mi p.1 p.2 H b B))%Rcoq.
Proof.
move=> Hg.
have [eta [e [c [d0 [Heta [He [Hc Hall]]]]]]] := paper_main_hybrid_gap_event gamma Hg.
exists eta, e, c, d0; split => //; split => //; split => //.
move=> d N r mi Hd HN Hr Hmi.
have [E [mE [PE HE]]] := Hall d N r mi Hd HN Hr Hmi.
exists E; split => //; split => //.
by rewrite paper_main_split_coordinates_law.
Qed.
