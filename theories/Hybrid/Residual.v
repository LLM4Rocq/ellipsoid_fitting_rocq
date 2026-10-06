(* The deterministic hybrid residual gap.

   Head sample h with N rows of dimension r, bulk array x with N rows of
   D = paper_main_symmetric_dimension mi coordinates (bulk matrices of size
   mi + 1). The hybrid residual of (H, b, B) is u = K(H, b) + R(B) with
     K(H, b)_i = g_i^T H g_i - tr H - b,  g_i the i-th head point,
     R(B)_i = sqrt (mi + 1) * <G_i, B>,  G_i the GOE row of x.
   1. The head coefficient map: K(H, b) = F(h) c(H, b) for the N x (r r + 1)
      head matrix F(h) with rows (vec (g_i g_i^T - I), -1) and
      c(H, b) = (vec H, b). The entries of F are measurable in h. For r = 0
      this is the genuine 0 x 0 head with K(H, b) = - b 1.
   2. R(B) = sqrt 2 * the projected bulk vector of the PSD code of B.
   3. Homogeneity: the projected bulk bound for unit PSD codes gives
      ||S_J (K + R(B))|| >= sqrt 2 * beta * sqrt N * ||B||_F for every PSD B.
   4. The gap: with the head energy bound, the projected bulk bound and the
      operator bound ||R(B)|| <= C0 sqrt N ||B||_F, every symmetric H,
      PSD B with ||H||_F^2 + ||B||_F^2 >= 1/4, every b and every kept set J
      give ||S_J u|| >= c4 sqrt N, with c4 depending only on beta and C0. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finset binomial.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous Spectral.Transport
  Spectral.Duality Gaussian.Symmetric.Coordinates
  Gaussian.Symmetric.PublicFeature Cone.GaussianCoordinates Head.SmallBallNet
  Head.SmallBallPZ Head.SmallBallUniform Projected.BulkEscape
  Projected.BulkComplement Projected.BulkConditional.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. The head coefficient map. *)

Definition paper_main_hybrid_head_value N r (h : paper_main_sample N r) (H : 'M[R]_r)
    (b : R) : 'cV[R]_N :=
  \col_(i < N) paper_main_head_small_ball_value H b (paper_main_point h i).

Definition paper_main_hybrid_head_row r (g : 'cV[R]_r) : 'rV[R]_(r * r + 1) :=
  row_mx (mxvec (g *m g^T - 1%:M)) (- 1)%:M.

Definition paper_main_hybrid_head_matrix N r (h : paper_main_sample N r) :
    'M[R]_(N, r * r + 1) :=
  \matrix_(i < N, j < r * r + 1) paper_main_hybrid_head_row r (paper_main_point h i) 0 j.

Definition paper_main_hybrid_head_coef r (H : 'M[R]_r) (b : R) : 'cV[R]_(r * r + 1) :=
  col_mx (mxvec H)^T b%:M.

Lemma paper_main_hybrid_head_row_coef r (g : 'cV[R]_r) (H : 'M[R]_r) (b : R) :
  (paper_main_hybrid_head_row r g *m paper_main_hybrid_head_coef r H b) 0 0 =
  paper_main_head_small_ball_value H b g.
Proof.
rewrite /paper_main_hybrid_head_row /paper_main_hybrid_head_coef mul_row_col mxE.
rewrite /paper_main_head_small_ball_value.
have Hc : (((-1)%:M : 'M[R]_1) *m b%:M) 0 0 = - b.
  by rewrite mul_scalar_mx mxE mxE eqxx mulr1n mulN1r.
rewrite Hc.
have Hsplit : (mxvec (g *m g^T - 1%:M) *m (mxvec H)^T) 0 0 =
    (mxvec (g *m g^T) *m (mxvec H)^T) 0 0 - (mxvec (1%:M : 'M[R]_r) *m (mxvec H)^T) 0 0.
  have Hsub : forall A B : 'M[R]_1, (A - B) 0 0 = A 0 0 - B 0 0 by move=> A B; rewrite !mxE.
  have -> : mxvec (g *m g^T - 1%:M) = mxvec (g *m g^T) - mxvec (1%:M : 'M[R]_r).
    exact: linearB.
  by rewrite mulmxBl Hsub.
have Hq : (mxvec (g *m g^T) *m (mxvec H)^T) 0 0 = paper_main_quadratic_form H g.
  have E := mxvec_dotmul H g^T g^T.
  rewrite trmxK in E.
  rewrite E /paper_main_quadratic_form mxE.
  rewrite exchange_big /=; apply: eq_bigr => j _.
  rewrite mxE mulr_suml; apply: eq_bigr => i _.
  by rewrite !mxE.
have Ht : (mxvec (1%:M : 'M[R]_r) *m (mxvec H)^T) 0 0 = paper_main_trace H.
  rewrite mx1_sum_delta linear_sum mulmx_suml summxE /paper_main_trace.
  apply: eq_bigr => i _.
  change ((mxvec (delta_mx i i : 'M[R]_r) *m (mxvec H)^T) 0 0 = H i i).
  by rewrite mxvec_delta -rowE mxE mxE mxvecE.
by rewrite Hsplit Hq Ht -!RminusE.
Qed.

Lemma paper_main_hybrid_head_matrix_coef N r (h : paper_main_sample N r) (H : 'M[R]_r)
    (b : R) :
  paper_main_hybrid_head_matrix N r h *m paper_main_hybrid_head_coef r H b =
  paper_main_hybrid_head_value N r h H b.
Proof.
apply/colP => i.
rewrite /paper_main_hybrid_head_value [RHS]mxE -paper_main_hybrid_head_row_coef [LHS]mxE.
rewrite [RHS]mxE.
by apply: eq_bigr => k _; rewrite mxE.
Qed.

Lemma paper_main_hybrid_head_matrix_measurable N r (a : 'I_N) (k : 'I_(r * r + 1)) :
  measurable_fun [set: paper_main_sample N r]
    ((fun h => paper_main_hybrid_head_matrix N r h a k) : _ -> measurableTypeR R).
Proof.
case: (splitP k) => j Hj.
  have -> : k = lshift 1 j by apply/val_inj.
  case/mxvec_indexP: j {Hj} => a1 b1.
  have -> : (fun h : paper_main_sample N r =>
      paper_main_hybrid_head_matrix N r h a (lshift 1 (mxvec_index a1 b1))) =
    (fun h => List.nth (a * r + a1) (tval h) 0 * List.nth (a * r + b1) (tval h) 0 -
      (a1 == b1)%:R).
    apply/funext => h.
    rewrite /paper_main_hybrid_head_matrix /paper_main_hybrid_head_row mxE row_mxEl mxvecE.
    by rewrite !mxE big_ord1 !mxE.
  apply: measurable_funB; last exact: measurable_cst.
  apply: measurable_funM.
    exact: (paper_main_head_small_ball_coord_measurable (N * r) (a * r + a1)).
  exact: (paper_main_head_small_ball_coord_measurable (N * r) (a * r + b1)).
have -> : k = rshift (r * r) j by apply/val_inj.
have -> : (fun h : paper_main_sample N r =>
    paper_main_hybrid_head_matrix N r h a (rshift (r * r) j)) = (fun _ => - 1).
  apply/funext => h.
  rewrite /paper_main_hybrid_head_matrix /paper_main_hybrid_head_row mxE row_mxEr.
  by rewrite !mxE (ord1 j) eqxx mulr1n.
exact: measurable_cst.
Qed.

(* 2. The bulk value R(B)_i = sqrt (mi + 1) * <G_i, B> and the projected
   bulk vector of the PSD code. *)

Definition paper_main_hybrid_bulk_value N mi
    (x : (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R))
    (B : 'M[R]_(S mi)) : 'cV[R]_N :=
  \col_(i < N) (sqrt (INR (S mi)) *
    paper_main_pairing (paper_main_public_gaussian_row mi i (tval x)) B)%Rcoq.

Lemma paper_main_hybrid_bulk_value_code N mi
    (x : (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R))
    (B : 'M[R]_(S mi)) :
  paper_main_symmetric B ->
  paper_main_hybrid_bulk_value N mi x B =
  (sqrt 2)%Rcoq *: paper_main_projected_bulk_vector N (paper_main_symmetric_dimension mi) x
    (paper_main_cone_code mi B).
Proof.
move=> HB.
apply/colP => i.
rewrite /paper_main_hybrid_bulk_value /paper_main_projected_bulk_vector !mxE.
rewrite /paper_main_public_gaussian_row.
rewrite -{1}(paper_main_matrix_public_roundtrip mi B).
rewrite -paper_main_matrix_public_pairing; first exact: paper_main_matrix_internal_symmetric.
rewrite -paper_main_symmetric_coordinate_pairing;
  [exact: paper_main_gaussian_feature_row_symmetric |
   exact: paper_main_matrix_internal_symmetric |].
rewrite /Gordon.ProcessCovariance.paper_main_gordon_dot -finite_sum_scale.
rewrite -RmultE -finite_sum_scale.
apply: finite_sum_ext => k Hk.
have HkD : (k < paper_main_symmetric_dimension mi)%coq_nat.
  by have := proj2 (proj1 (List.in_seq _ _ _) Hk); lia.
rewrite paper_main_gaussian_feature_row_coordinate //.
rewrite /paper_main_cone_code -(paper_main_gaussian_feature_scale mi) -RmultE.
have -> : ((i * paper_main_symmetric_dimension mi)%coq_nat + k)%coq_nat =
  (i * paper_main_symmetric_dimension mi + k)%N by [].
have E : forall a b c d : R, (a * (b * c * d) = a * b * (d * c))%Rcoq.
  by move=> a b c d; ring.
exact: E.
Qed.

(* 3. Homogeneity: scaling of codes, bulk vectors and norms, and the unit
   PSD sphere. *)

Lemma paper_main_hybrid_code_scale mi (B : 'M[R]_(S mi)) (a : R) (k : nat) :
  paper_main_symmetric B ->
  paper_main_cone_code mi (a *: B) k = (a * paper_main_cone_code mi B k)%Rcoq.
Proof.
move=> HB.
rewrite paper_main_cone_code_basis; first exact: paper_main_symmetric_scale.
by rewrite paper_main_cone_code_basis // paper_main_pairing_scale -RmultE.
Qed.

Lemma paper_main_hybrid_bulk_vector_scale N D (x : (N * D).-tuple (measurableTypeR R))
    (v : nat -> R) (a : R) :
  paper_main_projected_bulk_vector N D x (fun j => (a * v j)%Rcoq) =
  a *: paper_main_projected_bulk_vector N D x v.
Proof.
apply/colP => i; rewrite !mxE -RmultE -finite_sum_scale.
apply: finite_sum_ext => j _.
have E : forall p q s : R, (p * q * s = p * (q * s))%Rcoq by move=> p q s; ring.
exact: E.
Qed.

Lemma paper_main_hybrid_norm_scale {m : nat} (a : R) (w : 'cV[R]_m) :
  paper_main_projected_norm (a *: w) = (Rabs a * paper_main_projected_norm w)%Rcoq.
Proof.
rewrite /paper_main_projected_norm.
have Hs : paper_main_projected_sqnorm (a *: w) = (a * a * paper_main_projected_sqnorm w)%Rcoq.
  rewrite /paper_main_projected_sqnorm !mxE !RmultE mulr_sumr.
  apply: eq_bigr => i _; rewrite !mxE.
  by rewrite mulrACA.
have H0 := paper_main_projected_sqnorm_ge0 w.
move/RleP: H0 => H0.
rewrite Hs sqrt_mult; [nra | exact: H0 |].
by rewrite -/(Rsqr a) sqrt_Rsqr_abs.
Qed.

Lemma paper_main_hybrid_frobenius_scale {d : nat} (c : R) (S : 'M[R]_d) :
  (0 <= c)%Rcoq -> paper_main_frobenius (c *: S) = (c * paper_main_frobenius S)%Rcoq.
Proof.
move=> Hc.
have H1 := paper_main_frobenius_squared d (c *: S).
have H2 := paper_main_frobenius_squared d S.
have Hp : paper_main_pairing (c *: S) (c *: S) = (c * c * paper_main_pairing S S)%Rcoq.
  rewrite paper_main_pairing_scale paper_main_pairingC paper_main_pairing_scale.
  by rewrite !RmultE mulrA.
have Hf1 := paper_main_frobenius_nonnegative d (c *: S).
have Hf2 := paper_main_frobenius_nonnegative d S.
apply: Rsqr_inj => //; first by apply: Rmult_le_pos.
rewrite /Rsqr.
have E1 : (paper_main_frobenius (c *: S) * paper_main_frobenius (c *: S) =
    paper_main_pairing (c *: S) (c *: S))%Rcoq by rewrite -H1; ring.
have E2 : (paper_main_frobenius S * paper_main_frobenius S = paper_main_pairing S S)%Rcoq.
  by rewrite -H2; ring.
rewrite E1 Hp -E2; ring.
Qed.

Lemma paper_main_hybrid_psd_unit mi (B : 'M[R]_(S mi)) :
  paper_main_psd B -> (0 < paper_main_frobenius B)%Rcoq ->
  paper_main_projected_psd_set mi
    (paper_main_cone_code mi ((/ paper_main_frobenius B)%Rcoq *: B)).
Proof.
move=> HB Hf.
have Hi : (0 < / paper_main_frobenius B)%Rcoq by apply: Rinv_0_lt_compat.
exists ((/ paper_main_frobenius B)%Rcoq *: B); split; last by [].
split; first by apply: paper_main_psd_scale => //; apply/RleP; apply: Rlt_le.
rewrite paper_main_hybrid_frobenius_scale; first exact: Rlt_le.
by rewrite Rinv_l //; lra.
Qed.

Lemma paper_main_hybrid_bulk_homogeneous N mi q (J : {set 'I_N}) (F : 'M[R]_(N, q))
    (x : (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R)) (beta : R) :
  (0 <= beta)%Rcoq ->
  (forall (v : nat -> R) (c : 'cV[R]_q), paper_main_projected_psd_set mi v ->
     (beta < paper_main_projected_norm (paper_main_projected_residual N
       (paper_main_symmetric_dimension mi) q J (paper_main_projected_selector J *m F)
       x v c))%Rcoq) ->
  forall (B : 'M[R]_(S mi)) (c : 'cV[R]_q), paper_main_psd B ->
    (sqrt 2 * beta * paper_main_frobenius B <=
     paper_main_projected_norm (paper_main_projected_selector J *m
       (paper_main_hybrid_bulk_value N mi x B + F *m c)))%Rcoq.
Proof.
move=> Hb Hbulk B c HB.
have [Hs Hpos] := HB.
have Hf0 := paper_main_frobenius_nonnegative _ B.
case: (Rle_lt_or_eq_dec _ _ Hf0) => Hf; last first.
  rewrite -Hf Rmult_0_r; exact: sqrt_pos.
set rho := paper_main_frobenius B in Hf *.
set v := paper_main_cone_code mi ((/ rho)%Rcoq *: B).
have Hv := paper_main_hybrid_psd_unit mi B HB Hf.
have Hcode : paper_main_cone_code mi B = (fun j => (rho * v j)%Rcoq).
  apply/funext => j; rewrite /v paper_main_hybrid_code_scale //; field; lra.
set s2 := (sqrt 2 * rho)%Rcoq.
have H2 : (0 < sqrt 2)%Rcoq by apply: sqrt_lt_R0; lra.
have Hs2 : (0 < s2)%Rcoq by apply: Rmult_lt_0_compat.
have Heq : paper_main_projected_selector J *m (paper_main_hybrid_bulk_value N mi x B + F *m c) =
    s2 *: paper_main_projected_residual N (paper_main_symmetric_dimension mi) q J
      (paper_main_projected_selector J *m F) x v ((/ s2)%Rcoq *: c).
  rewrite paper_main_hybrid_bulk_value_code // Hcode paper_main_hybrid_bulk_vector_scale.
  rewrite scalerA mulmxDr -scalemxAr mulmxA.
  rewrite /paper_main_projected_residual scalerDr -scalemxAr scalerA.
  have -> : (s2 * / s2)%R = 1 by rewrite -RmultE Rinv_r //; lra.
  by rewrite scale1r /s2 RmultE.
rewrite Heq paper_main_hybrid_norm_scale Rabs_right; first by apply: Rle_ge; lra.
have Hlt := Hbulk v ((/ s2)%Rcoq *: c) Hv.
have -> : (sqrt 2 * beta * rho = s2 * beta)%Rcoq by rewrite /s2; ring.
apply: Rmult_le_compat_l; first lra.
exact: Rlt_le.
Qed.

(* 4. Selected norms. *)

Lemma paper_main_hybrid_selector_sqnorm {n : nat} (J : {set 'I_n}) (w : 'cV[R]_n) :
  paper_main_projected_sqnorm (paper_main_projected_selector J *m w) =
  (\sum_(i in J) w i 0 ^+ 2)%R.
Proof.
rewrite /paper_main_projected_sqnorm mxE (big_enum_val (fun i => w i 0 ^+ 2)) /=.
apply: eq_bigr => k _.
by rewrite mxE paper_main_projected_selector_apply expr2.
Qed.

Lemma paper_main_hybrid_selector_norm_le {n : nat} (J : {set 'I_n}) (w : 'cV[R]_n) :
  (paper_main_projected_norm (paper_main_projected_selector J *m w) <=
   paper_main_projected_norm w)%Rcoq.
Proof.
rewrite /paper_main_projected_norm; apply: sqrt_le_1_alt.
rewrite paper_main_hybrid_selector_sqnorm.
have -> : paper_main_projected_sqnorm w = (\sum_i w i 0 ^+ 2)%R.
  by rewrite /paper_main_projected_sqnorm mxE; apply: eq_bigr => i _; rewrite mxE expr2.
apply/RleP.
rewrite [X in (_ <= X)%R](bigID (fun i => i \in J)) /= lerDl.
by apply: sumr_ge0 => i _; rewrite sqr_ge0.
Qed.

Lemma paper_main_hybrid_norm_opp {m : nat} (w : 'cV[R]_m) :
  paper_main_projected_norm (- w) = paper_main_projected_norm w.
Proof.
rewrite /paper_main_projected_norm /paper_main_projected_sqnorm; congr sqrt.
rewrite !mxE; apply: eq_bigr => i _.
by rewrite !mxE mulrNN.
Qed.

(* 5. The deterministic gap. Only the lower bound
   ||H||_F^2 + ||B||_F^2 >= 1/4 is used. *)

Definition paper_main_hybrid_residual N r mi (h : paper_main_sample N r)
    (x : (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R))
    (H : 'M[R]_r) (b : R) (B : 'M[R]_(S mi)) : 'cV[R]_N :=
  paper_main_hybrid_head_value N r h H b + paper_main_hybrid_bulk_value N mi x B.

Definition paper_main_hybrid_head_floor : R := sqrt (3 / 38912).

Definition paper_main_hybrid_theta (C0 : R) : R :=
  Rmin (1 / 4) (paper_main_hybrid_head_floor / (2 * C0)).

Definition paper_main_hybrid_gap_constant (beta C0 : R) : R :=
  Rmin (sqrt 2 * beta * paper_main_hybrid_theta C0) (paper_main_hybrid_head_floor / 2).

Lemma paper_main_hybrid_gap_constant_pos (beta C0 : R) :
  (0 < beta)%Rcoq -> (0 < C0)%Rcoq -> (0 < paper_main_hybrid_gap_constant beta C0)%Rcoq.
Proof.
move=> Hb HC.
have Ha : (0 < paper_main_hybrid_head_floor)%Rcoq by apply: sqrt_lt_R0; lra.
have Ht : (0 < paper_main_hybrid_theta C0)%Rcoq.
  by apply: Rmin_glb_lt; [lra | apply: Rdiv_lt_0_compat; lra].
have H2 : (0 < sqrt 2)%Rcoq by apply: sqrt_lt_R0; lra.
apply: Rmin_glb_lt; last lra.
by apply: Rmult_lt_0_compat => //; apply: Rmult_lt_0_compat.
Qed.

Theorem paper_main_hybrid_residual_gap N r mi k (h : paper_main_sample N r)
    (x : (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R)) (beta C0 : R) :
  (0 < beta)%Rcoq -> (0 < C0)%Rcoq ->
  (forall (H : 'M[R]_r) (b : R) (J : {set 'I_N}), paper_main_symmetric H ->
     (N - k <= #|J|)%N ->
     (INR N / 4864 * paper_main_head_small_ball_sigma2 H b <=
      paper_main_head_small_ball_energy H b J h)%Rcoq) ->
  (forall J : {set 'I_N}, (N - k <= #|J|)%N ->
     forall (v : nat -> R) (c : 'cV[R]_(r * r + 1)), paper_main_projected_psd_set mi v ->
     (beta * sqrt (INR N) < paper_main_projected_norm (paper_main_projected_residual N
        (paper_main_symmetric_dimension mi) (r * r + 1) J
        (paper_main_projected_selector J *m paper_main_hybrid_head_matrix N r h) x v c))%Rcoq) ->
  (forall B : 'M[R]_(S mi), paper_main_symmetric B ->
     (paper_main_projected_norm (paper_main_hybrid_bulk_value N mi x B) <=
      C0 * sqrt (INR N) * paper_main_frobenius B)%Rcoq) ->
  forall (H : 'M[R]_r) (b : R) (B : 'M[R]_(S mi)) (J : {set 'I_N}),
    paper_main_symmetric H -> paper_main_psd B ->
    (1 / 4 <= paper_main_frobenius H ^ 2 + paper_main_frobenius B ^ 2)%Rcoq ->
    (N - k <= #|J|)%N ->
    (paper_main_hybrid_gap_constant beta C0 * sqrt (INR N) <=
     paper_main_projected_norm (paper_main_projected_selector J *m
       paper_main_hybrid_residual N r mi h x H b B))%Rcoq.
Proof.
move=> Hbeta HC0 Hhead Hbulk Hop H b B J HH HB Hnorm HJ.
set a0 := paper_main_hybrid_head_floor.
set th := paper_main_hybrid_theta C0.
have Ha0 : (0 < a0)%Rcoq by apply: sqrt_lt_R0; lra.
have Hth1 : (th <= 1 / 4)%Rcoq by apply: Rmin_l.
have Hth2 : (th <= a0 / (2 * C0))%Rcoq by apply: Rmin_r.
have Hth0 : (0 < th)%Rcoq.
  rewrite /th /paper_main_hybrid_theta.
  by apply: Rmin_glb_lt; [lra | apply: Rdiv_lt_0_compat; [exact: Ha0 | lra]].
have Hc1 : (paper_main_hybrid_gap_constant beta C0 <= sqrt 2 * beta * th)%Rcoq by apply: Rmin_l.
have Hc2 : (paper_main_hybrid_gap_constant beta C0 <= a0 / 2)%Rcoq by apply: Rmin_r.
have HN0 : (0 <= sqrt (INR N))%Rcoq by apply: sqrt_pos.
have H20 : (0 < sqrt 2)%Rcoq by apply: sqrt_lt_R0; lra.
set Kv := paper_main_hybrid_head_value N r h H b.
set Rb := paper_main_hybrid_bulk_value N mi x B.
have HK : Kv = paper_main_hybrid_head_matrix N r h *m paper_main_hybrid_head_coef r H b.
  by rewrite paper_main_hybrid_head_matrix_coef.
rewrite /paper_main_hybrid_residual -/Kv -/Rb.
have Hf0 := paper_main_frobenius_nonnegative _ B.
case: (Rle_lt_dec th (paper_main_frobenius B)) => Hcase.
  have Hb' : (0 <= beta * sqrt (INR N))%Rcoq by apply: Rmult_le_pos; lra.
  have H1 := paper_main_hybrid_bulk_homogeneous N mi (r * r + 1) J
    (paper_main_hybrid_head_matrix N r h) x (beta * sqrt (INR N)) Hb' (Hbulk J HJ) B
    (paper_main_hybrid_head_coef r H b) HB.
  rewrite -HK addrC in H1.
  apply: (Rle_trans _ _ _ _ H1).
  have E1 : (paper_main_hybrid_gap_constant beta C0 * sqrt (INR N) <=
      sqrt 2 * beta * th * sqrt (INR N))%Rcoq by apply: Rmult_le_compat_r.
  have E2 : (sqrt 2 * beta * th * sqrt (INR N) <=
      sqrt 2 * (beta * sqrt (INR N)) * paper_main_frobenius B)%Rcoq.
    have -> : (sqrt 2 * (beta * sqrt (INR N)) * paper_main_frobenius B =
        sqrt 2 * beta * sqrt (INR N) * paper_main_frobenius B)%Rcoq by ring.
    have -> : (sqrt 2 * beta * th * sqrt (INR N) = sqrt 2 * beta * sqrt (INR N) * th)%Rcoq.
      by ring.
    apply: Rmult_le_compat_l => //.
    by apply: Rmult_le_pos => //; apply: Rmult_le_pos; lra.
  lra.
have HBsq : (paper_main_frobenius B ^ 2 < th ^ 2)%Rcoq by rewrite /= !Rmult_1_r; nra.
have HHsq : (3 / 16 <= paper_main_frobenius H ^ 2)%Rcoq.
  have : (th ^ 2 <= 1 / 16)%Rcoq by rewrite /= Rmult_1_r; nra.
  lra.
rewrite /paper_main_head_small_ball_sigma2 in Hhead.
have Hen := Hhead H b J HH HJ.
rewrite -(paper_main_frobenius_squared _ H) in Hen.
have Hb2 := pow2_ge_0 b.
have HN := pos_INR N.
have HKsq : paper_main_projected_sqnorm (paper_main_projected_selector J *m Kv) =
    paper_main_head_small_ball_energy H b J h.
  rewrite paper_main_hybrid_selector_sqnorm /paper_main_head_small_ball_energy.
  by apply: eq_bigr => i _; rewrite mxE.
have HKn : (a0 * sqrt (INR N) <=
    paper_main_projected_norm (paper_main_projected_selector J *m Kv))%Rcoq.
  rewrite /paper_main_projected_norm HKsq /a0 /paper_main_hybrid_head_floor -sqrt_mult;
    [lra | exact: HN |].
  apply: sqrt_le_1_alt.
  have : (INR N / 4864 * (3 / 8) <=
      INR N / 4864 * (2 * paper_main_frobenius H ^ 2 + b ^ 2))%Rcoq.
    by apply: Rmult_le_compat_l; lra.
  lra.
have HRn : (paper_main_projected_norm (paper_main_projected_selector J *m Rb) <=
    a0 / 2 * sqrt (INR N))%Rcoq.
  apply: Rle_trans (paper_main_hybrid_selector_norm_le J Rb) _.
  apply: Rle_trans (Hop B (proj1 HB)) _.
  have H3 : (C0 * paper_main_frobenius B <= a0 / 2)%Rcoq.
    have H4 : (C0 * paper_main_frobenius B <= C0 * (a0 / (2 * C0)))%Rcoq.
      by apply: Rmult_le_compat_l; lra.
    have -> : (a0 / 2 = C0 * (a0 / (2 * C0)))%Rcoq by field; lra.
    exact: H4.
  have -> : (C0 * sqrt (INR N) * paper_main_frobenius B =
      C0 * paper_main_frobenius B * sqrt (INR N))%Rcoq by ring.
  by apply: Rmult_le_compat_r.
have Hrev := paper_main_projected_norm_reverse (paper_main_projected_selector J *m Kv)
  (paper_main_projected_selector J *m (Kv + Rb)).
have Hdiff : paper_main_projected_selector J *m Kv -
    paper_main_projected_selector J *m (Kv + Rb) = - (paper_main_projected_selector J *m Rb).
  by rewrite mulmxDr opprD addrA subrr add0r.
rewrite Hdiff paper_main_hybrid_norm_opp in Hrev.
have : (paper_main_hybrid_gap_constant beta C0 * sqrt (INR N) <= a0 / 2 * sqrt (INR N))%Rcoq.
  by apply: Rmult_le_compat_r.
lra.
Qed.

(* The case r = 0: the head is the genuine 0 x 0 head, K(H, b) = - b 1, and
   the head energy bound holds deterministically. *)

Lemma paper_main_hybrid_head_energy_zero N k (h : paper_main_sample N 0) :
  (INR N / 4864 <= INR (N - k)%nat)%Rcoq ->
  forall (H : 'M[R]_0) (b : R) (J : {set 'I_N}), (N - k <= #|J|)%N ->
    (INR N / 4864 * paper_main_head_small_ball_sigma2 H b <=
     paper_main_head_small_ball_energy H b J h)%Rcoq.
Proof.
move=> HNk H b J HJ.
have Hval : forall i : 'I_N,
    paper_main_head_small_ball_value H b (paper_main_point h i) = (- b)%Rcoq.
  move=> i; rewrite /paper_main_head_small_ball_value.
  rewrite /paper_main_quadratic_form /paper_main_trace !big_ord0.
  have E : forall z : R, (0 - 0 - z = - z)%Rcoq by move=> z; ring.
  exact: E.
have Hen : paper_main_head_small_ball_energy H b J h = (INR #|J| * b ^ 2)%Rcoq.
  rewrite /paper_main_head_small_ball_energy.
  under eq_bigr => i _ do rewrite Hval.
  rewrite sumr_const.
  by rewrite RmultE INRE RpowE RoppE sqrrN mulr_natl.
have Hsig : paper_main_head_small_ball_sigma2 H b = (b ^ 2)%Rcoq.
  rewrite /paper_main_head_small_ball_sigma2 /paper_main_pairing big_ord0.
  have E : forall z : R, (2 * 0 + z = z)%Rcoq by move=> z; ring.
  exact: E.
rewrite Hen Hsig.
have HJr : (INR (N - k)%nat <= INR #|J|)%Rcoq by apply: le_INR; apply/ssrnat.leP.
have Hb2 := pow2_ge_0 b.
apply: Rmult_le_compat_r => //.
lra.
Qed.
