(* The Gaussian model: Lemma 5.14, Proposition 5.15 (the shifted
   cone-projection limit), Lemma 5.16 and Proposition 1.4 (ii) of Koehler and
   Sohn (arXiv 2608.27372, lines 5880-6220 of arxiv_v1.tex), at Stdlib's R.
   Item G8 of stage 2 of phase 5 (lane C), with library/matrix/psd_part.v.

   Notation. For a symmetric G of size d > 0 with eigenvalues spec G 0 i in
   decreasing order (library/matrix/von_neumann.v): g_i = gval G i =
   spec G 0 i / sqrt d, nu_d = empirical_fun (gval G) their empirical law,
   m_d(w) and s_d(w) its upper partial moments (upper_moment nu_d 1 w and
   upper_moment nu_d 2 w, library/probability/variational.v),
   c = cone_shift kappa = (kappa - 3) / 2, V_d = spec_value kappa zeta G =
   upper_value nu_d c zeta (the value of Lemma 5.7 for nu_d),
   Z = shift_mx kappa zeta G = G + zeta sqrt d sqrt (2 / (kappa - 1)) I (the
   paper's G_{d,kappa}(zeta)), and e = cone_excess kappa =
   sqrt ((kappa - 1) / 2) - 1, so that T_kappa G = G + e diag G
   (cone_map_excess).

   Proved here.
   - Deterministic part of Lemma 5.14 and Proposition 5.15, for
     kappa >= 3. cone_proj_kappa_le: |proj_{S^d_kappa} z| <= g if and only
     if <z, T_kappa S> <= g |T_kappa S| for every S >= 0 (cone_proj_le of
     Gaussian/Representation). pairing_spec_le: <G, S> + zeta sqrt d Tr S
     <= d sqrt V_d (|S|^2 + c (Tr S)^2 / d)^(1/2) for S >= 0, by von
     Neumann's inequality (mxdot_spec_le) and the finite form of Lemma 5.7
     (empirical_variational_le). cone_proj_upper: |proj Z| <=
     d sqrt V_d + e |diag G|. cone_proj_lower: for every w, with
     R_w = psd_part (G - sqrt d w I), d^2 (s_d(w) + (w + zeta) m_d(w)) <=
     (|proj Z| + e |diag G|) |T R_w|, and (cone_map_shifted_part)
     |T R_w|^2 = d^2 (s_d(w) + c m_d(w)^2) + c d diag_var R_w.
   - The Gaussian matrix. For a of law gauss (d * d), G = goe_part (vec_mx a)
     = sqrt (d / 2) W with W = goe_mx a (goe_partE), so
     g_i = spec W 0 i / sqrt 2 (gval_goe) and m_d, s_d are the statistics
     goe_stat of W of the functions (x / sqrt 2 - w)_+^k
     (upper_moment_goe); against semicircle_prob 2 these integrate to the
     upper moments of threshold_law (semicircle_upper_moment).
     goe_upper_moment_cvg: m_d(w) and s_d(w) converge in probability
     (InProbability.cvg_prob) to m(w) and s(w), by Wigner's law
     (goe_stat_cvg, from wigner of random_matrix/wigner.v).
     goe_diag_cvg: |diag G| / d -> 0, by Markov's inequality and
     E |diag G|^2 = d. goe_diag_var_cvg: diag_var (psd_part (W - x I)) -> 0,
     by Lemma 5.13 (goe_diag_var_tail of random_matrix/goe_rotation.v) and
     P(opnorm W >= 3) -> 0 (goe_opnorm_tail_small).
   - Proposition 5.15 for kappa >= 3 (shifted_cone_proj_cvg3): with w the
     cutoff of the limit law, Pi_upper and Pi_lower bound |proj Z| / d
     between two functions of m_d(w), s_d(w), |diag G| / d and the
     diagonal variance that converge to sqrt chi_kappa(zeta) (the bound of
     Lemma 5.8, stab_bound, tends to 0: stab_bound_cvg). The paper takes
     the cutoff of nu_d instead, which would need the measurability of a
     random cutoff; Lemma 5.8 (upper_value_stability) only needs m_d and s_d
     at the cutoff of the limit law.
   - Proposition 5.15 for 1 < kappa < 3 and its final form
     (shifted_cone_proj_cvg): for every kappa > 1 and zeta,
     |proj_{S^d_kappa} G_{d,kappa}(zeta)|_F / d converges in probability to
     sqrt chi_kappa(zeta), chi_kappa(zeta) = upper_value threshold_law
     (cone_shift kappa) zeta. cone_proj_moreau: for Z symmetric,
     |proj_{S_kappa} Z|^2 + |proj_{S_kappa'} (- Z)|^2 = |Z|^2 with
     kappa' = kappa_dual kappa (Moreau's decomposition and the dual cone
     of Lemma 5.2); shift_mx_dual: - G_{d,kappa}(zeta) =
     G'_{d,kappa'}(zeta') with G' = - G and zeta' = - 2 zeta / (kappa - 1);
     goe_sqnorm_cvg: |G_{d,kappa}(zeta)|^2 / d^2 -> 1/2 + 2 zeta^2 /
     (kappa - 1), by Wigner's law for x and x^2; then the kappa' > 3 case at
     - a (gauss is invariant, cvg_prob_gaussN) and the scalar identity
     universality_value_dual.

   Still to come (names come with the proofs).
   - Lemma 5.16: phihat_d -> zeta_{alpha,kappa} and Phi_d ->
     (zeta_{alpha,kappa})_+ in probability, from Lemma 5.6 (aux_value_ge of
     Gaussian/Representation), Proposition 5.15 at zeta_{alpha,kappa} +- eps,
     |g| / d -> sqrt alpha, and the CGMT in mean and concentration form
     (library/comparison/cgmt.v).
   - Proposition 1.4 (ii), the form that Unsat/Universality (U10, lane A)
     uses: for Z of law tuple_prod (fun=> gaussian_feature_law kappa d)
     (n d) and every eps > 0, the event that
     2 * unsat_value (n d) d Z is farther than eps from
     universality_e_star alpha kappa lies, for every large d, in a
     measurable event of probability at most eps. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets interval reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability realfun.
From GaussianAnalysis Require Import euclidean real_spectral opnorm.
From GaussianAnalysis Require Import least_squares logdet_barrier moreau.
From GaussianAnalysis Require Import psd_part measurable_matrix von_neumann.
From GaussianAnalysis Require Import variational goe_rotation gauss.
From GaussianAnalysis Require Import gauss_moments gauss_smoothing goe wigner.
From GaussianAnalysis Require Import semicircle_law.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.
From EllipsoidUniversality.Gaussian Require Import Representation InProbability.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Unsat Require Import LeastSquares.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* The notions of the frozen definitions and those of the library. *)

Lemma pairing_mxdot d (A B : 'M[R]_d) : paper_main_pairing A B = mxdot A B.
Proof. by []. Qed.

Lemma paper_symmetricP d (S : 'M[R]_d) :
  paper_main_symmetric S <-> S \is symmetricmx.
Proof.
split => [h|/symmetricmxP h i j].
  by apply/symmetricmxP/matrixP => i j; rewrite mxE h.
by rewrite -{1}h mxE.
Qed.

Lemma paper_quadratic_mxdot d (S : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form S v = mxdot v (S *m v).
Proof.
rewrite /paper_main_quadratic_form /mxdot; apply: eq_bigr => i _.
rewrite big_ord1 !mxE mulr_sumr; apply: eq_bigr => j _.
by rewrite mulrA.
Qed.

Lemma paper_psdP d (S : 'M[R]_d) : paper_main_psd S <-> psdmx S.
Proof.
rewrite /paper_main_psd /psdmx paper_symmetricP.
by split => -[Ss h]; split => // v;
  [rewrite -paper_quadratic_mxdot|rewrite paper_quadratic_mxdot].
Qed.

Lemma paper_traceE d (S : 'M[R]_d) : paper_main_trace S = \tr S.
Proof. by []. Qed.

(* The projection on S^d_kappa through its support function. *)

(* S^d_kappa in the mxvec coordinates is a closed convex cone. *)
Lemma kappa_cone_rV0 (kappa : R) d : kappa_cone_rV kappa d 0.
Proof.
rewrite /kappa_cone_rV /= linear0 -(scale0r (cone_map kappa 1%:M)).
by apply: kappa_coneZ => //; exists 1%:M => //; case: (psd_trace_slice1 d).
Qed.

Lemma kappa_cone_rV_convex (kappa : R) d (x y : 'rV[RR]_(d * d)) (t : R) :
  kappa_cone_rV kappa d x -> kappa_cone_rV kappa d y -> 0 <= t <= 1 ->
  kappa_cone_rV kappa d (x + t *: (y - x)).
Proof.
move=> Cx Cy /andP[t0 t1].
have -> : x + t *: (y - x) = (1 - t) *: x + t *: y.
  by apply/rowP => i; rewrite !mxE; ring.
rewrite /kappa_cone_rV /= linearD !linearZ /=.
by apply: kappa_coneD; apply: kappa_coneZ => //; rewrite subr_ge0.
Qed.

Lemma kappa_cone_rV_cone (kappa : R) d (y : 'rV[RR]_(d * d)) (a : R) :
  kappa_cone_rV kappa d y -> 0 <= a -> kappa_cone_rV kappa d (a *: y).
Proof.
by move=> Cy a0; rewrite /kappa_cone_rV /= linearZ /=; exact: kappa_coneZ.
Qed.

Lemma cone_proj_kappa_le (kappa : R) d (z : 'rV[RR]_(d * d)) (g : R) :
  1 < kappa -> 0 <= g ->
  frobenius (proj (kappa_cone_rV kappa d) z) <= g <->
  forall S, psdmx S ->
    mxdot z (mxvec (cone_map kappa S)) <= g * frobenius (cone_map kappa S).
Proof.
move=> k1 g0.
rewrite (cone_proj_le _ _ _ _ (kappa_cone_rV_closed _ _ k1)
  (kappa_cone_rV0 kappa d) (@kappa_cone_rV_convex kappa d)
  (@kappa_cone_rV_cone kappa d) g0).
have fm (A : 'M[R]_d) : frobenius (mxvec A) = frobenius A.
  by rewrite /frobenius mxdot_mxvec.
split => h.
  move=> S Sp; rewrite -fm; apply: h.
  by rewrite /kappa_cone_rV /= mxvecK; exists S => //; exact/paper_psdP.
move=> y [S Sp E].
have -> : y = mxvec (cone_map kappa S) by rewrite E vec_mxK.
by rewrite fm; apply: h; exact/paper_psdP.
Qed.

(* T_kappa and the diagonal. *)

Lemma cone_map_excess (kappa : R) d (S : 'M[R]_d) :
  cone_map kappa S = S + (Num.sqrt ((kappa - 1) / 2%:R) - 1) *: diag_part S.
Proof.
apply/matrixP => i j; rewrite cone_mapE !mxE.
have [->|ij] := eqVneq i j; first by rewrite /=; ring.
by rewrite mulr0 addr0.
Qed.

Lemma mxdot_diag_partl d (A B : 'M[R]_d) :
  mxdot (diag_part A) B = \sum_i A i i * B i i.
Proof.
rewrite /mxdot; apply: eq_bigr => i _.
rewrite (bigD1 i) //= mxE eqxx.
rewrite big1 ?addr0 // => j ji.
by rewrite mxE eq_sym (negPf ji) mul0r.
Qed.

Lemma mxdot_diag_part2 d (A : 'M[R]_d) :
  mxdot (diag_part A) (diag_part A) = \sum_i A i i ^+ 2.
Proof.
by rewrite mxdot_diag_partl; apply: eq_bigr => i _; rewrite mxE eqxx expr2.
Qed.

Lemma pairing_diag_part_abs d (A B : 'M[R]_d) :
  `|mxdot (diag_part A) B| <= frobenius (diag_part A) * frobenius (diag_part B).
Proof.
have -> : mxdot (diag_part A) B = mxdot (diag_part A) (diag_part B).
  by rewrite !mxdot_diag_partl; apply: eq_bigr => i _; rewrite mxE eqxx.
exact: mxdot_le.
Qed.

Lemma pairing_diag_part_le d (A B : 'M[R]_d) :
  mxdot (diag_part A) B <= frobenius (diag_part A) * frobenius (diag_part B).
Proof. exact: le_trans (ler_norm _) (pairing_diag_part_abs _ A B). Qed.

Lemma frobenius_diag_part_le (kappa : R) d (S : 'M[R]_d) : 3%:R <= kappa ->
  frobenius (diag_part S) <= frobenius (cone_map kappa S).
Proof.
move=> k3.
have k1 : 1 <= kappa by apply: le_trans k3; rewrite ler1n.
have c0 : 0 <= cone_shift kappa by rewrite cone_shiftE divr_ge0 // subr_ge0.
have e : mxdot (cone_map kappa S) (cone_map kappa S) =
    mxdot S S + cone_shift kappa * \sum_i S i i * S i i.
  exact: pairing_cone_map.
rewrite /frobenius ler_sqrt ?mxdot_ge0 // e mxdot_diag_part2.
apply: le_trans (diag_sqr_le S) _; rewrite lerDl.
by apply: mulr_ge0 => //; apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
Qed.

(* (tr S)^2 <= d sum_i S_ii^2. *)
Lemma trace_sqr_diag d (S : 'M[R]_d) : \tr S ^+ 2 <= d%:R * \sum_i S i i ^+ 2.
Proof.
have h := sum_cauchy_schwarz (fun i : 'I_d => 1) (fun i => S i i).
have e1 : \sum_(i < d) (1 : R) * 1 = d%:R.
  by under eq_bigr do rewrite mulr1; rewrite sumr_const card_ord.
have e2 : \sum_(i < d) (1 : R) * S i i = \tr S.
  by rewrite /mxtrace; apply: eq_bigr => i _; rewrite mul1r.
rewrite e1 e2 in h; apply: le_trans h _.
by rewrite ler_wpM2l ?ler0n //; apply: ler_sum => i _; rewrite expr2.
Qed.

(* The value of the spectral problem. *)

Definition gval {d : nat} (G : 'M[R]_d) (i : 'I_d) : R :=
  spec G 0 i / Num.sqrt d%:R.

Definition spec_value (kappa zeta : R) {d : nat} (G : 'M[R]_d) : R :=
  upper_value (empirical_fun (gval G)) (cone_shift kappa) zeta.

Definition shift_mx (kappa zeta : R) {d : nat} (G : 'M[R]_d) : 'M[R]_d :=
  G + (zeta * Num.sqrt d%:R * Num.sqrt (2%:R / (kappa - 1))) *: 1%:M.

Definition cone_excess (kappa : R) : R := Num.sqrt ((kappa - 1) / 2%:R) - 1.

Arguments spec_value kappa%_ring_scope zeta%_ring_scope {d} G.
Arguments shift_mx kappa%_ring_scope zeta%_ring_scope {d} G.
Arguments cone_excess kappa%_ring_scope.

Lemma gvalE d (G : 'M[R]_d) i : gval G i = spec G 0 i / Num.sqrt d%:R.
Proof. by rewrite /gval RdivE. Qed.

Lemma cone_excessE (kappa : R) :
  cone_excess kappa = Num.sqrt ((kappa - 1) / 2%:R) - 1.
Proof. by rewrite /cone_excess RminusE R1E. Qed.

Section spectral_bounds.
Variables (kappa zeta : R) (d : nat) (G : 'M[R]_d).
Hypotheses (k3 : 3%:R <= kappa) (d0 : (0 < d)%N) (Gs : G \is symmetricmx).

Lemma cone_shift_ge0 : 0 <= cone_shift kappa.
Proof. by rewrite cone_shiftE divr_ge0 // subr_ge0. Qed.

(* Lemma 5.14, upper bound: von Neumann's inequality and the finite form of
   Lemma 5.7. *)
Lemma pairing_spec_le (S : 'M[R]_d) : psdmx S ->
  mxdot G S + zeta * Num.sqrt d%:R * \tr S <=
  d%:R * Num.sqrt (spec_value kappa zeta G) *
  Num.sqrt (mxdot S S + cone_shift kappa * \tr S ^+ 2 / d%:R).
Proof.
move=> Sp; have Ss := Sp.1.
set sd := Num.sqrt d%:R.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have dn : d%:R != 0 :> R by rewrite gt_eqF.
have sd0 : 0 < sd by rewrite sqrtr_gt0.
have sdn : sd != 0 by rewrite gt_eqF.
have mu0 i : 0 <= spec S 0 i by exact: spec_psd_ge0.
have key := empirical_variational_le (gval G) d0 zeta cone_shift_ge0 mu0.
rewrite (sum_spec_trace Ss) -(mxdot_spec Ss) -/(spec_value kappa zeta G) in key.
have e1 : \sum_i (gval G i + zeta) * spec S 0 i =
    sd^-1 * (\sum_i spec G 0 i * spec S 0 i) + zeta * \tr S.
  rewrite -(sum_spec_trace Ss) !mulr_sumr -big_split /=.
  apply: eq_bigr => i _; rewrite gvalE -/sd mulrDl; congr (_ + _).
  by rewrite mulrAC mulrC.
have e2 (a t : R) : d%:R^-1 * a + cone_shift kappa * (d%:R^-1 * t) ^+ 2 =
    d%:R^-1 * (a + cone_shift kappa * t ^+ 2 / d%:R).
  by field.
rewrite e1 e2 sqrtrM ?invr_ge0 ?ler0n // sqrtrV ?ler0n // -/sd in key.
have vN := mxdot_spec_le Gs Ss.
set L := \sum_i spec G 0 i * spec S 0 i in e1 key vN.
set Y := mxdot S S + cone_shift kappa * \tr S ^+ 2 / d%:R in key *.
set W := Num.sqrt (spec_value kappa zeta G) in key *.
apply: le_trans (_ : L + zeta * sd * \tr S <= _); first by rewrite lerD2r.
have -> : L + zeta * sd * \tr S =
    (d%:R * sd) * (d%:R^-1 * (sd^-1 * L + zeta * \tr S)).
  by clearbody sd L; field.
apply: le_trans (ler_wpM2l _ key) _; first by rewrite mulr_ge0 // ltW.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; clearbody sd W Y; field.
Qed.

Lemma cone_excess_ge0 : 0 <= cone_excess kappa.
Proof.
rewrite cone_excessE subr_ge0 -[X in X <= _]sqrtr1 ler_sqrt.
  apply: divr_ge0; last by rewrite ler0n.
  by rewrite subr_ge0; apply: le_trans k3; rewrite ler1n.
by rewrite ler_pdivlMr ?ltr0n // mul1r lerBrDr; move: k3; lra.
Qed.

Lemma frobenius_cone_map_ge (S : 'M[R]_d) :
  Num.sqrt (mxdot S S + cone_shift kappa * \tr S ^+ 2 / d%:R) <=
  frobenius (cone_map kappa S).
Proof.
have k1 : 1 <= kappa by apply: le_trans k3; rewrite ler1n.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have e : mxdot (cone_map kappa S) (cone_map kappa S) =
    mxdot S S + cone_shift kappa * \sum_i S i i * S i i.
  exact: pairing_cone_map.
rewrite /frobenius ler_sqrt ?mxdot_ge0 // e lerD2l -mulrA.
rewrite ler_wpM2l ?cone_shift_ge0 // ler_pdivrMr // mulrC.
apply: le_trans (trace_sqr_diag _ S) _.
by rewrite ler_wpM2l ?ler0n //; apply: ler_sum => i _; rewrite expr2.
Qed.

(* Lemma 5.14 and Proposition 5.15, upper bound: the norm of the projection
   of the shifted G is at most d sqrt V_d + e |diag G|. *)
Lemma cone_proj_upper :
  frobenius (proj (kappa_cone_rV kappa d) (mxvec (shift_mx kappa zeta G))) <=
  d%:R * Num.sqrt (spec_value kappa zeta G) +
  cone_excess kappa * frobenius (diag_part G).
Proof.
have k1 : 1 < kappa by apply: lt_le_trans k3; rewrite ltr1n.
have e0 := cone_excess_ge0.
have g0 : 0 <= d%:R * Num.sqrt (spec_value kappa zeta G) +
    cone_excess kappa * frobenius (diag_part G).
  by rewrite addr_ge0 ?mulr_ge0 ?ler0n ?sqrtr_ge0 ?frobenius_ge0.
apply/(cone_proj_kappa_le kappa d _ _ k1 g0) => S Sp.
rewrite mxdot_mxvec /shift_mx mxdotDl mxdotZl.
(* zeta sqrt d sqrt (2 / (kappa - 1)) <I, T S> = zeta sqrt d Tr S *)
have tc := trace_cone_map kappa d S k1.
rewrite paper_traceE pairing_mxdot in tc.
rewrite -[_ * mxdot 1%:M _]mulrA -tc.
(* <G, T S> = <T G, S> = <G, S> + e <diag G, S> *)
have -> : mxdot G (cone_map kappa S) =
    mxdot G S + cone_excess kappa * mxdot (diag_part G) S.
  rewrite -pairing_mxdot -cone_map_pairing pairing_mxdot cone_map_excess.
  by rewrite mxdotDl mxdotZl cone_excessE.
rewrite addrAC [X in _ <= X]mulrDl; apply: lerD.
  apply: le_trans (pairing_spec_le S Sp) _.
  by rewrite ler_wpM2l ?mulr_ge0 ?ler0n ?sqrtr_ge0 // frobenius_cone_map_ge.
rewrite -mulrA ler_wpM2l //.
apply: le_trans (pairing_diag_part_le _ G S) _.
by rewrite ler_wpM2l ?frobenius_ge0 // frobenius_diag_part_le.
Qed.

Section shifted_part.
Variable w : R.

Local Notation sd := (Num.sqrt (d%:R : R)).
Local Notation Rw := (psd_part (G - (Num.sqrt d%:R * w)%:M)).
Local Notation nu := (empirical_fun (gval G)).

Lemma spec_shiftE (i : 'I_d) :
  Num.max (spec G 0 i - sd * w) 0 = sd * Num.max (gval G i - w) 0.
Proof.
have sd0 : 0 < sd by rewrite sqrtr_gt0 ltr0n.
have sdn : sd != 0 by rewrite gt_eqF.
rewrite gvalE maxr_pMr ?ltW // mulr0; congr (Num.max _ 0).
by rewrite mulrBr mulrCA mulfV // mulr1.
Qed.

Lemma trace_shifted_part :
  \tr Rw = sd * d%:R * upper_moment nu 1 w.
Proof.
rewrite trace_psd_part_shift // (upper_moment_empirical_fun _ d0).
under eq_bigr do rewrite spec_shiftE.
rewrite -mulr_sumr -mulrA; congr (_ * _).
rewrite mulrA mulfV ?gt_eqF ?ltr0n // mul1r.
by apply: eq_bigr => i _; rewrite expr1.
Qed.

Lemma mxdot_shifted_part :
  mxdot Rw Rw = d%:R ^+ 2 * upper_moment nu 2 w.
Proof.
have dn : d%:R != 0 :> R by rewrite gt_eqF ?ltr0n.
rewrite -frobenius_sqr frobenius_psd_part_shift //.
rewrite (upper_moment_empirical_fun _ d0).
under eq_bigr do rewrite spec_shiftE exprMn sqr_sqrtr ?ler0n //.
rewrite -mulr_sumr mulrA; congr (_ * _).
by rewrite expr2 -mulrA mulfV // mulr1.
Qed.

Lemma pairing_shifted_part :
  mxdot G Rw + zeta * sd * \tr Rw =
  d%:R ^+ 2 * (upper_moment nu 2 w + (w + zeta) * upper_moment nu 1 w).
Proof.
have dn : d%:R != 0 :> R by rewrite gt_eqF ?ltr0n.
have sd0 : 0 < sd by rewrite sqrtr_gt0 ltr0n.
have sdn : sd != 0 by rewrite gt_eqF.
have sdE : sd * sd = d%:R by rewrite -expr2 sqr_sqrtr ?ler0n.
(* x (x - w)_+ = (x - w)_+^2 + w (x - w)_+ *)
have pt (x : R) :
    x * Num.max (x - w) 0 = Num.max (x - w) 0 ^+ 2 + w * Num.max (x - w) 0.
  case: (leP 0 (x - w)) => h; first by ring.
  by rewrite !mulr0 expr0n /= addr0.
have lE i : spec G 0 i = sd * gval G i by rewrite gvalE mulrCA mulfV ?mulr1.
rewrite (mxdot_psd_part_shift _ Gs) trace_shifted_part.
rewrite !(upper_moment_empirical_fun _ d0).
under eq_bigr do rewrite spec_shiftE [spec G 0 _]lE mulrACA sdE pt.
have e1 : \sum_i maxr (gval G i - w) 0 ^+ 1 = \sum_i maxr (gval G i - w) 0.
  by apply: eq_bigr => i _; rewrite expr1.
rewrite e1 -mulr_sumr big_split /= -mulr_sumr.
move: (\sum_i maxr (gval G i - w) 0 ^+ 2) (\sum_i maxr (gval G i - w) 0).
move=> P2 P1; move: sdE; move: (Num.sqrt d%:R) => s sE.
have -> : zeta * s * (s * d%:R * (d%:R^-1 * P1)) = zeta * (s * s) * P1.
  by field.
by rewrite sE; field.
Qed.

Lemma cone_map_shifted_part :
  mxdot (cone_map kappa Rw) (cone_map kappa Rw) =
  d%:R ^+ 2 *
    (upper_moment nu 2 w + cone_shift kappa * upper_moment nu 1 w ^+ 2)
  + cone_shift kappa * d%:R * diag_var Rw.
Proof.
have k1 : 1 <= kappa by apply: le_trans k3; rewrite ler1n.
have dn : d%:R != 0 :> R by rewrite gt_eqF ?ltr0n.
have sdE : sd * sd = d%:R by rewrite -expr2 sqr_sqrtr ?ler0n.
have e : mxdot (cone_map kappa Rw) (cone_map kappa Rw) =
    mxdot Rw Rw + cone_shift kappa * \sum_i Rw i i * Rw i i.
  exact: pairing_cone_map.
have dv := diag_varE Rw.
rewrite trace_shifted_part in dv.
have sq : \sum_i Rw i i * Rw i i = d%:R * (diag_var Rw +
    (sd * d%:R * upper_moment nu 1 w / d%:R) ^+ 2).
  by rewrite dv; under eq_bigr do rewrite -expr2; field.
rewrite e mxdot_shifted_part sq.
move: (diag_var Rw) (upper_moment nu 1 w) (upper_moment nu 2 w) => D m s2.
move: sdE; move: (Num.sqrt d%:R) => s sE.
have -> : (s * d%:R * m / d%:R) ^+ 2 = (s * s) * m ^+ 2 by field.
by rewrite sE; field.
Qed.

(* Lemma 5.14 and Proposition 5.15, lower bound: the test matrix
   R_w = psd_part (G - sqrt d w I). *)
Lemma cone_proj_lower :
  d%:R ^+ 2 * (upper_moment nu 2 w + (w + zeta) * upper_moment nu 1 w) <=
  (frobenius (proj (kappa_cone_rV kappa d) (mxvec (shift_mx kappa zeta G))) +
   cone_excess kappa * frobenius (diag_part G)) *
  frobenius (cone_map kappa Rw).
Proof.
have k1 : 1 < kappa by apply: lt_le_trans k3; rewrite ltr1n.
have e0 := cone_excess_ge0.
set Z := mxvec (shift_mx kappa zeta G).
have p0 := frobenius_ge0 (proj (kappa_cone_rV kappa d) Z).
(* <Z, T R_w> <= |proj Z| |T R_w| *)
have h := (cone_proj_kappa_le kappa d _ _ k1 p0).1 (lexx _) Rw (psd_part_psd _).
set P := frobenius (proj (kappa_cone_rV kappa d) Z) in h *.
rewrite mxdot_mxvec /shift_mx mxdotDl mxdotZl in h.
have tc := trace_cone_map kappa d Rw k1.
rewrite paper_traceE pairing_mxdot in tc.
rewrite -[_ * mxdot 1%:M _]mulrA -tc in h.
have eG : mxdot G (cone_map kappa Rw) =
    mxdot G Rw + cone_excess kappa * mxdot (diag_part G) Rw.
  rewrite -pairing_mxdot -cone_map_pairing pairing_mxdot cone_map_excess.
  by rewrite mxdotDl mxdotZl cone_excessE.
rewrite eG addrAC pairing_shifted_part in h.
(* the diagonal term *)
have hd : - (cone_excess kappa * mxdot (diag_part G) Rw) <=
    cone_excess kappa * frobenius (diag_part G) * frobenius (cone_map kappa Rw).
  rewrite -mulrN -mulrA ler_wpM2l //.
  apply: le_trans (_ : `|mxdot (diag_part G) Rw| <= _).
    by rewrite -normrN ler_norm.
  apply: le_trans (pairing_diag_part_abs _ G _) _.
  by rewrite ler_wpM2l ?frobenius_ge0 // frobenius_diag_part_le.
rewrite [X in _ <= X]mulrDl.
apply: le_trans _ (lerD h hd).
by rewrite addrK.
Qed.

End shifted_part.

End spectral_bounds.

(* The spectrum of the Gaussian matrix of the paper. *)

Lemma goe_partE d (a : 'rV[RR]_(d * d)) : (0 < d)%N ->
  goe_part (vec_mx a) = Num.sqrt (d%:R / 2%:R) *: goe_mx a.
Proof.
move=> d0; rewrite /goe_part /goe_mx scalerA; congr (_ *: _).
have dn : d%:R != 0 :> R by rewrite gt_eqF ?ltr0n.
rewrite -sqrtrV ?mulr_ge0 ?ler0n // -sqrtrM ?divr_ge0 ?ler0n //.
have -> : d%:R / 2%:R * (2 * d%:R)^-1 = (2%:R ^-1) ^+ 2 :> R by field.
by rewrite sqrtr_sqr ger0_norm // invr_ge0 ler0n.
Qed.

Lemma gval_goe d (a : 'rV[RR]_(d * d)) (i : 'I_d) : (0 < d)%N ->
  gval (goe_part (vec_mx a)) i = spec (goe_mx a) 0 i / Num.sqrt 2%:R.
Proof.
move=> d0; rewrite gvalE goe_partE //.
have Ws : goe_mx a \is symmetricmx by apply: goe_mx_symmetric.
rewrite (spec_scale Ws (sqrtr_ge0 _)) mxE sqrtrM ?ler0n // sqrtrV ?ler0n //.
have sd : 0 < Num.sqrt (d%:R : R) by rewrite sqrtr_gt0 ltr0n.
have s2 : 0 < Num.sqrt (2%:R : R) by rewrite sqrtr_gt0 ltr0n.
move: sd s2; move: (Num.sqrt (d%:R : R)) (Num.sqrt (2%:R : R)) => p q p0 q0.
have pn : p != 0 by rewrite gt_eqF.
have qn : q != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma upper_moment_goe d (a : 'rV[RR]_(d * d)) k (w : R) : (0 < d)%N ->
  upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) k w =
  goe_stat (fun x => Num.max (x / Num.sqrt 2%:R - w) 0 ^+ k) a.
Proof.
move=> d0; rewrite (upper_moment_empirical_fun _ d0) /goe_stat mulrC.
by congr (_ * _); apply: eq_bigr => i _; rewrite gval_goe.
Qed.

Lemma semicircle_upper_moment k (w : R) :
  \int[semicircle_prob 2]_x (Num.max ((x : R) / Num.sqrt 2%:R - w) 0 ^+ k) =
  upper_moment threshold_law k w.
Proof.
rewrite /upper_moment /Rintegral.
have s2 : 0 < (Num.sqrt (2%:R : R))^-1 by rewrite invr_gt0 sqrtr_gt0 ltr0n.
have := @ge0_integral_semicircle_scale RR 2 (Num.sqrt 2%:R)^-1
  (fun y => (Num.max (y - w) 0 ^+ k)%:E) (ltr0n RR 2) s2.
have q2 : (Num.sqrt (2%:R : R))^-1 * 2 = Num.sqrt 2%:R.
  have e : Num.sqrt (2%:R : R) ^+ 2 = 2 by rewrite sqr_sqrtr ?ler0n.
  by rewrite -{2}e expr2 mulrA mulVf ?mul1r // gt_eqF ?sqrtr_gt0 ?ltr0n.
rewrite q2 => h; rewrite -h.
- move=> y; rewrite lee_fin.
  by apply: exprn_ge0; rewrite le_max lexx orbT.
- apply/measurable_EFinP; apply: measurable_funX.
  apply: measurable_maxr; last exact: measurable_cst.
  by apply: measurable_funB; [exact: measurable_id|exact: measurable_cst].
- by congr fine; apply: eq_integral => x _; rewrite mulrC.
Qed.

Lemma measurable_ge_continuous n (F : 'rV[RR]_n -> R) (c : R) :
  continuous F -> measurable [set a | c <= F a].
Proof.
move=> cF; have mI : measurable [set x : RR | c <= x].
  have -> : [set x : RR | c <= x] = [set` Interval (BLeft c) (BInfty _ false)].
    by apply/seteqP; split => x /=; rewrite in_itv /= andbT.
  exact: measurable_itv.
have := (continuous_measurable_mx cF) measurableT _ mI.
by rewrite setTI.
Qed.

(* Wigner's law in the form of convergence in probability. *)
Lemma goe_stat_cvg (f : R -> R) (L : R) : continuous f ->
  (forall x y : R, -3 <= x <= 3 -> -3 <= y <= 3 ->
     `|f x - f y| <= L * `|x - y|) ->
  cvg_prob (fun d => gauss (d * d)) (fun d a => goe_stat f a)
    (\int[semicircle_prob 2]_x f x).
Proof.
move=> cf fL eta e0 eps p0.
have m0 : 0 < Num.min eta eps by rewrite lt_min e0.
have [D hD] := wigner cf fL m0.
exists D => d dD.
exists [set a | Num.min eta eps <=
  `|goe_stat f a - \int[semicircle_prob 2]_x f x|]; split.
- apply: measurable_ge_continuous => a.
  apply: (continuous_comp (continuousB (@continuous_goe_stat _ d _ cf a)
    (@cst_continuous _ _ _ a))).
  exact: norm_continuous.
- by apply: le_trans (hD d dD) _; rewrite lee_fin ge_min lexx orbT.
- by move=> a /= h; apply: le_trans h; rewrite ge_min lexx.
Qed.

Lemma upper_part_lipschitz (w x y : R) :
  `|Num.max (x - w) 0 - Num.max (y - w) 0| <= `|x - y|.
Proof.
case: (leP 0 (x - w)) => hx; case: (leP 0 (y - w)) => hy.
- by rewrite opprB addrA subrK.
- rewrite subr0 ger0_norm // ler_normr; apply/orP; left.
  by move: hy; lra.
- rewrite sub0r normrN ger0_norm // ler_normr; apply/orP; right.
  by move: hx; lra.
- by rewrite subrr normr0 normr_ge0.
Qed.

Lemma scaled_upper_lipschitz k (w x y : R) : (k <= 2)%N ->
  -3 <= x <= 3 -> -3 <= y <= 3 ->
  `|Num.max (x / Num.sqrt 2%:R - w) 0 ^+ k -
    Num.max (y / Num.sqrt 2%:R - w) 0 ^+ k| <= 2 * (3 + `|w|) * `|x - y|.
Proof.
move=> k2 /andP[x1 x2] /andP[y1 y2].
have s0 : 0 < Num.sqrt (2%:R : R) by rewrite sqrtr_gt0 ltr0n.
have s1 : 1 <= Num.sqrt (2%:R : R).
  by rewrite -[X in X <= _]sqrtr1 ler_sqrt ?ler0n // ler1n.
have dxy : `|x / Num.sqrt 2%:R - y / Num.sqrt 2%:R| <= `|x - y|.
  rewrite -mulrBl normrM.
  have i0 : 0 <= (Num.sqrt (2%:R : R))^-1 by rewrite invr_ge0 ltW.
  by rewrite (ger0_norm i0) ler_pdivrMr // ler_peMr // normr_ge0.
have pq : `|Num.max (x / Num.sqrt 2%:R - w) 0 -
    Num.max (y / Num.sqrt 2%:R - w) 0| <= `|x - y|.
  exact: le_trans (upper_part_lipschitz _ _ _) dxy.
have bnd (z : R) : -3 <= z <= 3 ->
    Num.max (z / Num.sqrt 2%:R - w) 0 <= 3 + `|w|.
  move=> /andP[z1 z2]; rewrite ge_max addr_ge0 ?ler0n ?normr_ge0 // andbT.
  have zs : z / Num.sqrt 2%:R <= 3.
    case: (leP z 0) => z0.
      apply: le_trans (_ : z / Num.sqrt 2%:R <= 0) _; last by rewrite ler0n.
      by apply: mulr_le0_ge0 => //; rewrite invr_ge0 ltW.
    by rewrite ler_pdivrMr // (le_trans z2) // ler_peMr.
  by have := ler_norm (- w); rewrite normrN; lra.
have pB : Num.max (x / Num.sqrt 2%:R - w) 0 <= 3 + `|w|.
  by apply: bnd; rewrite x1 x2.
have qB : Num.max (y / Num.sqrt 2%:R - w) 0 <= 3 + `|w|.
  by apply: bnd; rewrite y1 y2.
have p0 : 0 <= Num.max (x / Num.sqrt 2%:R - w) 0 by rewrite le_max lexx orbT.
have q0 : 0 <= Num.max (y / Num.sqrt 2%:R - w) 0 by rewrite le_max lexx orbT.
move: pq pB qB p0 q0.
move: (Num.max (x / Num.sqrt 2%:R - w) 0) (Num.max (y / Num.sqrt 2%:R - w) 0).
move=> p q pq pB qB p0 q0.
have L1 : 1 <= 2 * (3 + `|w|) by have := normr_ge0 w; lra.
case: k k2 => [|[|[|k]]] // _.
- by rewrite !expr0 subrr normr0 mulr_ge0 // mulr_ge0 // addr_ge0.
- by rewrite !expr1; apply: le_trans pq _; rewrite ler_peMl // normr_ge0.
- rewrite subr_sqr normrM mulrC.
  apply: ler_pM; rewrite ?normr_ge0 //.
  by rewrite ger0_norm ?addr_ge0 //; lra.
Qed.

Lemma goe_upper_moment_cvg k (w : R) : (k <= 2)%N ->
  cvg_prob (fun d => gauss (d * d))
    (fun d a => upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) k w)
    (upper_moment threshold_law k w).
Proof.
move=> k2.
have cf : continuous (fun x : R => Num.max (x / Num.sqrt 2%:R - w) 0 ^+ k).
  move=> x; apply: (@continuous_comp _ _ _ (fun x : R => x / Num.sqrt 2%:R)
    (fun y => Num.max (y - w) 0 ^+ k)); last exact: continuous_upper_part.
  by apply: cvgM; [exact: cvg_id|exact: cvg_cst].
have h := goe_stat_cvg _ (2 * (3 + `|w|)) cf
  (fun x y => scaled_upper_lipschitz k w x y k2).
rewrite semicircle_upper_moment in h.
move=> eta e0; apply: negligibleW; first exact: (h eta e0).
by exists 1%N => d d1 a /=; rewrite upper_moment_goe.
Qed.

(* |diag G| / d tends to 0, by Markov's inequality: E |diag G|^2 = d. *)
Lemma diag_goe_part d (a : 'rV[RR]_(d * d)) :
  mxdot (diag_part (goe_part (vec_mx a))) (diag_part (goe_part (vec_mx a))) =
  \sum_i a 0 (mxvec_index i i) ^+ 2.
Proof.
rewrite mxdot_diag_part2; apply: eq_bigr => i _; congr (_ ^+ 2).
by rewrite /goe_part !mxE; move: (a 0 _) => t; field.
Qed.

Lemma gauss_coord_sqr n (j : 'I_n) : \int[@gauss RR n]_x (x 0 j ^+ 2) = 1.
Proof.
rewrite /Rintegral.
under eq_integral do rewrite expr2.
by rewrite gauss_cov eqxx.
Qed.

Lemma goe_diag_cvg :
  cvg_prob (fun d => gauss (d * d))
    (fun d a => frobenius (diag_part (goe_part (vec_mx a))) / d%:R) 0.
Proof.
move=> eta e0 eps p0.
exists (archimedean.Num.truncn ((eta ^+ 2 * eps)^-1)).+1 => d dD.
have d0 : (0 < d)%N by apply: leq_trans dD.
have dR : 0 < d%:R :> R by rewrite ltr0n.
pose f (a : 'rV[RR]_(d * d)) := \sum_i a 0 (mxvec_index i i) ^+ 2.
have pc (i : 'I_d) :
    polyfun (fun x : 'rV[RR]_(d * d) => x 0 (mxvec_index i i) ^+ 2).
  have -> : (fun x : 'rV[RR]_(d * d) => x 0 (mxvec_index i i) ^+ 2) =
      (fun x => x 0 (mxvec_index i i) * x 0 (mxvec_index i i)).
    by apply/funext => x; rewrite expr2.
  by apply: polyfunM; exact: polyfun_coord.
have pf : polyfun f by apply: polyfun_sum.
(* E f = d *)
have Ef : \int[gauss (d * d)]_x f x = d%:R.
  rewrite /f Rintegral_polyfun_sum //.
  have e (i : 'I_d) :
      \int[gauss (d * d)]_x (x : 'rV[RR]_(d * d)) 0 (mxvec_index i i) ^+ 2 = 1.
    exact: gauss_coord_sqr.
  by under eq_bigr do rewrite e; rewrite sumr_const card_ord.
have c0 : 0 < eta ^+ 2 * d%:R ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
exists [set a | eta ^+ 2 * d%:R ^+ 2 <= f a]; split.
- by apply: measurable_ge_continuous; exact: pf.1.
- apply: le_trans (gauss_markov c0 _ _ (integrable_polyfun pf)) _.
  + exact: continuous_measurable_mx pf.1.
  + by move=> a; apply: sumr_ge0 => i _; exact: sqr_ge0.
  rewrite lee_fin Ef.
  have hd : (eta ^+ 2 * eps)^-1 < d%:R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  have pe : 0 < eta ^+ 2 * eps by rewrite mulr_gt0 // exprn_gt0.
  have h1 : 1 < eta ^+ 2 * eps * d%:R by rewrite -ltr_pdivrMl // mulr1.
  rewrite mulrC ler_pdivrMr //.
  have -> : eps * (eta ^+ 2 * d%:R ^+ 2) = d%:R * (eta ^+ 2 * eps * d%:R).
    by rewrite expr2; ring.
  by rewrite -[X in X <= _]mulr1 ler_pM2l // ltW.
- move=> a /= h.
  have h' : eta <= frobenius (diag_part (goe_part (vec_mx a))) / d%:R.
    apply: le_trans h _.
    rewrite subr0 ger0_norm //.
    by rewrite divr_ge0 ?frobenius_ge0 ?ler0n.
  rewrite ler_pdivlMr // in h'.
  rewrite /f -diag_goe_part -frobenius_sqr -exprMn.
  by rewrite ler_pXn2r // ?nnegrE ?mulr_ge0 ?frobenius_ge0 // ltW.
Qed.

(* Lemma 5.13: the diagonal of psd_part (W - x I) is nearly constant. *)
Lemma psd_part_shift_equivariant d (x : R) :
  conj_equivariant (fun W : 'M[RR]_d => psd_part (W - x%:M)).
Proof.
move=> Q W Qo Ws.
have -> : Q *m W *m Q^T - x%:M = Q *m (W - x%:M) *m Q^T.
  rewrite mulmxBr mulmxBl; congr (_ - _).
  by rewrite mul_mx_scalar -scalemxAl (orthogonalmxP _ Qo) scalemx1.
apply: psd_part_conj => //.
apply/symmetricmxP; rewrite linearB /= tr_scalar_mx.
by move/symmetricmxP: Ws => ->.
Qed.

Lemma goe_diag_var_cvg (x : R) :
  cvg_prob (fun d => gauss (d * d))
    (fun d a => diag_var (psd_part (goe_mx a - x%:M))) 0.
Proof.
move=> eta e0 eps p0.
have C0 : 0 < (3 + `|x|) ^+ 2 by rewrite exprn_gt0 // ltr_wpDr // ltr0n.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have s3 : 2 * Num.sqrt 2 < 3 :> R.
  have s2 : Num.sqrt 2 < 3 / 2 :> R.
    rewrite -(@ltr_pXn2r _ 2) ?nnegrE ?sqrtr_ge0 ?divr_ge0 // sqr_sqrtr //.
    by rewrite expr_div_n; lra.
  by lra.
have [D1 h1] := goe_opnorm_tail_small s3 e2.
exists (maxn D1
  (archimedean.Num.truncn (4 * (3 + `|x|) ^+ 2 / (eta * eps))).+1) => d.
rewrite geq_max => /andP[d1 d2].
have d0 : (0 < d)%N by apply: leq_trans d2.
have Fsym (W : 'M[RR]_d) :
    W \is symmetricmx -> psd_part (W - x%:M) \is symmetricmx.
  by move=> _; have [] := psd_part_psd (W - x%:M).
have sx (W : 'M[RR]_d) : W \is symmetricmx -> W - x%:M \is symmetricmx.
  move=> Ws; apply/symmetricmxP; rewrite linearB /= tr_scalar_mx.
  by move/symmetricmxP: Ws => ->.
have FL (a b : 'rV[RR]_(d * d)) :
    frobenius (psd_part (goe_mx a - x%:M) - psd_part (goe_mx b - x%:M)) <=
    Num.sqrt (2 / d%:R) * frobenius (a - b).
  apply: le_trans (psd_part_nonexpansive (sx _ (goe_mx_symmetric a))
    (sx _ (goe_mx_symmetric b))) _.
  by rewrite opprB addrA subrK -goe_mxB frobenius_goe_mx.
have Fm : measurable_fun [set: 'rV[RR]_(d * d)]
    (fun a => psd_part (goe_mx a - x%:M)).
  apply/measurable_fun_mxP => i j; apply: continuous_measurable_mx.
  apply: (@lipschitz_frobenius_continuous _ _ _ (Num.sqrt (2 / d%:R))) => a b.
  apply: le_trans (FL a b).
  have := frobenius_entry
    (psd_part (goe_mx a - x%:M) - psd_part (goe_mx b - x%:M)) i j.
  by rewrite !mxE.
(* Lemma 5.13 *)
have tail := @goe_diag_var_tail RR d (fun W => psd_part (W - x%:M))
  (psd_part_shift_equivariant d x) Fsym Fm _ _ (ltW C0) e0.
have mX (i j : 'I_d) : measurable_fun [set: 'rV[RR]_(d * d)]
    (fun a => psd_part (goe_mx a - x%:M) i j).
  exact: (measurable_fun_mxP _).1 Fm i j.
have mdv : measurable_fun [set: 'rV[RR]_(d * d)]
    (fun a => diag_var (psd_part (goe_mx a - x%:M))).
  rewrite /diag_var; apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_sum => j; apply: measurableT_comp (exprn_measurable 2) _.
  apply: measurable_funB => //; apply: measurable_funM => //.
  by rewrite /mxtrace; apply: measurable_sum => i.
have mN2 : measurable_fun [set: 'rV[RR]_(d * d)]
    (fun a => mxdot (psd_part (goe_mx a - x%:M)) (psd_part (goe_mx a - x%:M))).
  rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
  exact: measurable_funM.
have mge (c : R) (f : 'rV[RR]_(d * d) -> RR) :
    measurable_fun [set: 'rV[RR]_(d * d)] f -> measurable [set a | c <= f a].
  move=> mf; have mI : measurable [set y : RR | c <= y].
    have -> : [set y : RR | c <= y] =
        [set` Interval (BLeft c) (BInfty _ false)].
      by apply/seteqP; split => y /=; rewrite in_itv /= andbT.
    exact: measurable_itv.
  by have := mf measurableT _ mI; rewrite setTI.
have mgt (c : R) (f : 'rV[RR]_(d * d) -> RR) :
    measurable_fun [set: 'rV[RR]_(d * d)] f -> measurable [set a | c < f a].
  move=> mf; have mI : measurable [set y : RR | c < y].
    have -> : [set y : RR | c < y] =
        [set` Interval (BRight c) (BInfty _ false)].
      by apply/seteqP; split => y /=; rewrite in_itv /= andbT.
    exact: measurable_itv.
  by have := mf measurableT _ mI; rewrite setTI.
have mop : measurable_fun [set: 'rV[RR]_(d * d)]
    (fun a => opnorm (goe_mx a) : RR).
  apply: continuous_measurable_mx.
  exact: lipschitz_frobenius_continuous (@goe_opnorm_lipschitz RR d).
(* off opnorm W >= 3, |psd_part (W - x I)|^2 <= d (3 + |x|)^2 *)
have sub : [set a : 'rV[RR]_(d * d) | (3 + `|x|) ^+ 2 * d%:R <
    mxdot (psd_part (goe_mx a - x%:M)) (psd_part (goe_mx a - x%:M))] `<=`
    [set a | 3 <= opnorm (goe_mx a)].
  move=> a /=; apply: contraPP => /negP; rewrite -ltNge => ho.
  apply/negP; rewrite -leNgt.
  have Ws : goe_mx a \is symmetricmx by apply: goe_mx_symmetric.
  rewrite -frobenius_sqr (frobenius_psd_part_shift _ Ws).
  have -> : (3 + `|x|) ^+ 2 * d%:R = \sum_(i < d) (3 + `|x|) ^+ 2.
    by rewrite sumr_const card_ord mulr_natr.
  apply: ler_sum => i _.
  have sb := spec_le_opnorm i Ws.
  rewrite ler_sqr ?nnegrE ?le_max ?lexx ?orbT ?addr_ge0 ?normr_ge0 //.
  rewrite ge_max addr_ge0 ?ler0n ?normr_ge0 // andbT.
  have := ler_norm (spec (goe_mx a) 0 i); have := ler_norm (- x).
  by rewrite normrN; move: sb ho; lra.
exists [set a | eta <= diag_var (psd_part (goe_mx a - x%:M))]; split.
- exact: mge.
- apply: le_trans tail _.
  rewrite [eps]splitr EFinD; apply: leeD.
    rewrite lee_fin.
    have dR : 0 < d%:R :> R by rewrite ltr0n.
    have hd : 4 * (3 + `|x|) ^+ 2 / (eta * eps) < d%:R.
      apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
      by rewrite ler_nat.
    have pe : 0 < eta * eps by rewrite mulr_gt0.
    rewrite ler_pdivrMr ?mulr_gt0 ?addr_gt0 //.
    rewrite ltr_pdivrMr // in hd.
    by move: hd C0; nra.
  apply: le_trans (le_measure _ _ _ sub) (h1 d d1).
  + by rewrite inE; exact: mgt.
  + by rewrite inE; exact: mge.
- move=> a /= h; apply: le_trans h _.
  rewrite subr0 ger0_norm //.
  exact: diag_var_ge0.
Qed.

Lemma diag_varZ n (c : R) (A : 'M[RR]_n) :
  diag_var (c *: A) = c ^+ 2 * diag_var A.
Proof.
rewrite /diag_var mulrCA; congr (_ * _); rewrite mulr_sumr.
by apply: eq_bigr => j _; rewrite mxE mxtraceZ -mulrA -mulrBr exprMn.
Qed.

Lemma shifted_part_goe d (a : 'rV[RR]_(d * d)) (w : R) : (0 < d)%N ->
  psd_part (goe_part (vec_mx a) - (Num.sqrt d%:R * w)%:M) =
  Num.sqrt (d%:R / 2%:R) *: psd_part (goe_mx a - (Num.sqrt 2%:R * w)%:M).
Proof.
move=> d0.
have Ws : goe_mx a - (Num.sqrt 2%:R * w)%:M \is symmetricmx.
  apply/symmetricmxP; rewrite linearB /= tr_scalar_mx.
  by move/symmetricmxP: (goe_mx_symmetric a) => ->.
rewrite -psd_partZ ?sqrtr_ge0 //; congr psd_part.
rewrite goe_partE // scalerBr scale_scalar_mx; congr (_ - _%:M).
rewrite mulrA -sqrtrM ?divr_ge0 ?ler0n //.
by rewrite mulfVK // pnatr_eq0.
Qed.

Section prop515.
Variables (kappa zeta : R).
Hypothesis k3 : 3%:R <= kappa.

Local Notation c := (cone_shift kappa).
Local Notation w := (upper_cutoff threshold_law (cone_shift kappa) zeta).
Local Notation m := (upper_moment threshold_law 1 w).
Local Notation s := (upper_moment threshold_law 2 w).
Local Notation chi := (upper_value threshold_law (cone_shift kappa) zeta).
Local Notation k := (`|cone_shift kappa| / Num.min 1 (1 + cone_shift kappa)).

(* The bound of Lemma 5.8 at the cutoff of the limit law. *)
Definition stab_bound (x y : R) : R :=
  `|y - s| + `|c| * `|x ^+ 2 - m ^+ 2| +
  2 * (1 + `|c|) * (x + k * `|x - m|) * (k * `|x - m|).

Lemma Pi_upper d (a : 'rV[RR]_(d * d)) : (0 < d)%N ->
  frobenius (proj (kappa_cone_rV kappa d)
    (mxvec (shift_mx kappa zeta (goe_part (vec_mx a))))) / d%:R <=
  Num.sqrt (chi + stab_bound
    (upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 1 w)
    (upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 2 w)) +
  cone_excess kappa * (frobenius (diag_part (goe_part (vec_mx a))) / d%:R).
Proof.
move=> d0.
have Gs : goe_part (vec_mx a) \is symmetricmx.
  rewrite goe_partE //; apply/symmetricmxP; rewrite linearZ /=.
  by move/symmetricmxP: (goe_mx_symmetric a) => ->.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have k1 : 1 < kappa by apply: lt_le_trans k3; rewrite ltr1n.
have h := cone_proj_upper kappa zeta d (goe_part (vec_mx a)) k3 d0 Gs.
(* V_d <= chi + the bound of Lemma 5.8 *)
have hV : spec_value kappa zeta (goe_part (vec_mx a)) <= chi +
    stab_bound (upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 1 w)
      (upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 2 w).
  rewrite -lerBlDl; apply: le_trans (ler_norm _) _.
  exact: (upper_value_stability
    (empirical_fun_sqr (gval (goe_part (vec_mx a))) d0)
    threshold_law2 zeta (cone_shift_gtN1 _ k1)).
rewrite ler_pdivrMr //; apply: le_trans h _.
rewrite [X in _ <= X]mulrDl [X in _ <= _ + X]mulrAC -[X in _ <= _ + X]mulrA.
rewrite [d%:R * (_ / _)]mulrC divfK ?gt_eqF // lerD2r mulrC.
by rewrite ler_pM2r // ler_wsqrtr.
Qed.

Lemma Pi_lower d (a : 'rV[RR]_(d * d)) : (0 < d)%N ->
  (upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 2 w +
   (w + zeta) * upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 1 w) /
  Num.sqrt (upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 2 w +
    c * upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 1 w ^+ 2 +
    c / 2%:R * diag_var (psd_part (goe_mx a - (Num.sqrt 2%:R * w)%:M))) -
  cone_excess kappa * (frobenius (diag_part (goe_part (vec_mx a))) / d%:R) <=
  frobenius (proj (kappa_cone_rV kappa d)
    (mxvec (shift_mx kappa zeta (goe_part (vec_mx a))))) / d%:R.
Proof.
move=> d0.
have Gs : goe_part (vec_mx a) \is symmetricmx.
  rewrite goe_partE //; apply/symmetricmxP; rewrite linearZ /=.
  by move/symmetricmxP: (goe_mx_symmetric a) => ->.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have dn : d%:R != 0 :> R by rewrite gt_eqF.
have e0 : 0 <= cone_excess kappa by exact: cone_excess_ge0.
have h := cone_proj_lower kappa zeta d (goe_part (vec_mx a)) k3 d0 Gs w.
have hT := cone_map_shifted_part kappa d (goe_part (vec_mx a)) k3 d0 Gs w.
(* diag_var R_w = d / 2 diag_var (psd_part (W - sqrt 2 w I)) *)
have dvE : diag_var (psd_part (goe_part (vec_mx a) - (Num.sqrt d%:R * w)%:M)) =
    d%:R / 2%:R * diag_var (psd_part (goe_mx a - (Num.sqrt 2%:R * w)%:M)).
  by rewrite shifted_part_goe // diag_varZ sqr_sqrtr // divr_ge0 ?ler0n.
rewrite dvE -frobenius_sqr in hT; clear dvE.
have P0 := frobenius_ge0 (proj (kappa_cone_rV kappa d)
  (mxvec (shift_mx kappa zeta (goe_part (vec_mx a))))).
have D0 := frobenius_ge0 (diag_part (goe_part (vec_mx a))).
move: h hT P0 D0 (frobenius_ge0 (cone_map kappa
  (psd_part (goe_part (vec_mx a) - (Num.sqrt d%:R * w)%:M)))).
move: (frobenius (cone_map kappa _)) => T.
move: (frobenius (proj _ _)) => P.
move: (frobenius (diag_part _)) => Dd.
move: (upper_moment _ 2 w) (upper_moment _ 1 w) (diag_var _) => S M DV.
move=> h hT P0 D0 T0.
move: h; move: (upper_cutoff _ c zeta + zeta) => wz h.
move: h e0; move: (cone_excess kappa) => e h e0.
(* |T R_w| = d sqrt B *)
have hB : T ^+ 2 = d%:R ^+ 2 * (S + c * M ^+ 2 + c / 2 * DV).
  by rewrite hT; field.
have B0 : 0 <= S + c * M ^+ 2 + c / 2 * DV.
  have : 0 <= d%:R ^+ 2 * (S + c * M ^+ 2 + c / 2 * DV) by rewrite -hB sqr_ge0.
  by rewrite pmulr_rge0 // exprn_gt0.
have TE : T = d%:R * Num.sqrt (S + c * M ^+ 2 + c / 2 * DV).
  rewrite -[T]ger0_norm // -sqrtr_sqr hB sqrtrM ?exprn_ge0 ?ler0n //.
  by rewrite sqrtr_sqr ger0_norm ?ler0n.
rewrite TE in h; clear hT hB TE.
move: B0 h; move: (S + c * M ^+ 2 + c / 2 * DV) => B B0 h.
move: h; move: (S + wz * M) => A h.
have sB0 := sqrtr_ge0 B.
case: (eqVneq (Num.sqrt B) 0) => sB.
  rewrite sB invr0 mulr0 sub0r.
  apply: le_trans (_ : 0 <= _); last by rewrite divr_ge0 ?ler0n.
  by rewrite oppr_le0 mulr_ge0 // divr_ge0 ?ler0n.
have sBp : 0 < Num.sqrt B by rewrite lt_def sB sB0.
rewrite lerBlDr ler_pdivrMr //.
have -> : (P / d%:R + e * (Dd / d%:R)) * Num.sqrt B =
    ((P + e * Dd) * (d%:R * Num.sqrt B)) / d%:R ^+ 2.
  by move: (Num.sqrt B) => q; field.
by rewrite ler_pdivlMr ?exprn_gt0 // mulrC.
Qed.

Local Notation P := (fun d => @gauss RR (d * d)).
Local Notation Md := (fun d (a : 'rV[RR]_(d * d)) =>
  upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 1 w).
Local Notation Sd := (fun d (a : 'rV[RR]_(d * d)) =>
  upper_moment (empirical_fun (gval (goe_part (vec_mx a)))) 2 w).

Lemma stab_bound_cvg :
  cvg_prob P (fun d a => stab_bound (Md d a) (Sd d a)) 0.
Proof.
have hM := goe_upper_moment_cvg 1 w (isT : (1 <= 2)%N).
have hS := goe_upper_moment_cvg 2 w (isT : (2 <= 2)%N).
have hM0 : cvg_prob P (fun d a => `|Md d a - m|) 0.
  have := cvg_prob_norm (cvg_probB hM (cvg_prob_cst P m)).
  by rewrite subrr normr0.
have hS0 : cvg_prob P (fun d a => `|Sd d a - s|) 0.
  have := cvg_prob_norm (cvg_probB hS (cvg_prob_cst P s)).
  by rewrite subrr normr0.
have hM2 : cvg_prob P (fun d a => `|Md d a ^+ 2 - m ^+ 2|) 0.
  have := cvg_prob_norm (cvg_probB (cvg_probM hM hM) (cvg_prob_cst P (m * m))).
  rewrite subrr normr0; apply: cvg_prob_eq.
  by exists 0%N => d _ a; rewrite !expr2.
have hk : cvg_prob P (fun d a => k * `|Md d a - m|) 0.
  have := cvg_probM (cvg_prob_cst P k) hM0; rewrite mulr0.
  by apply: cvg_prob_eq; exists 0%N.
have := cvg_probD (cvg_probD hS0 (cvg_probM (cvg_prob_cst P `|c|) hM2))
  (cvg_probM (cvg_probM (cvg_prob_cst P (2 * (1 + `|c|)))
    (cvg_probD hM hk)) hk).
rewrite !mulr0 !addr0.
by apply: cvg_prob_eq; exists 0%N.
Qed.

(* Proposition 5.15 for kappa >= 3. *)
Theorem shifted_cone_proj_cvg3 :
  cvg_prob P
    (fun d a => frobenius (proj (kappa_cone_rV kappa d)
       (mxvec (shift_mx kappa zeta (goe_part (vec_mx a))))) / d%:R)
    (Num.sqrt chi).
Proof.
have k1 : 1 < kappa by apply: lt_le_trans k3; rewrite ltr1n.
have c1 : -1 < c := cone_shift_gtN1 _ k1.
have hD := goe_diag_cvg.
have hU : cvg_prob P (fun d a => Num.sqrt (chi + stab_bound (Md d a) (Sd d a)) +
    cone_excess kappa * (frobenius (diag_part (goe_part (vec_mx a))) / d%:R))
    (Num.sqrt chi).
  have := cvg_probD
    (cvg_prob_sqrt (cvg_probD (cvg_prob_cst P chi) stab_bound_cvg))
    (cvg_probM (cvg_prob_cst P (cone_excess kappa)) hD).
  by rewrite addr0 mulr0 addr0.
have chi0 : 0 <= chi := upper_value_ge0 threshold_law2 zeta c1.
have [chiz|chin] := eqVneq chi 0.
  apply: (cvg_prob_squeeze (L := fun _ _ => 0) _ _ hU).
  - exists 1%N => d d1 a; rewrite divr_ge0 ?frobenius_ge0 ?ler0n //=.
    exact: Pi_upper.
  - by rewrite chiz sqrtr0; exact: cvg_prob_cst.
have hM := goe_upper_moment_cvg 1 w (isT : (1 <= 2)%N).
have hS := goe_upper_moment_cvg 2 w (isT : (2 <= 2)%N).
have hV := goe_diag_var_cvg (Num.sqrt 2%:R * w : RR).
have chiE : chi = s + c * m ^+ 2 by [].
have wE : w + zeta = c * m := upper_cutoffE threshold_law2 zeta c1.
have limA : s + (w + zeta) * m = chi.
  by rewrite wE chiE -mulrA -expr2.
have hA : cvg_prob P (fun d a => Sd d a + (w + zeta) * Md d a) chi.
  have := cvg_probD hS (cvg_probM (cvg_prob_cst P (w + zeta)) hM).
  by rewrite limA.
have limB : s + c * (m * m) + c / 2%:R * 0 = chi.
  by rewrite mulr0 addr0 -expr2.
have hB : cvg_prob P (fun d a => Sd d a + c * Md d a ^+ 2 +
    c / 2%:R * diag_var (psd_part (goe_mx a - (Num.sqrt 2%:R * w)%:M))) chi.
  have := cvg_probD
    (cvg_probD hS (cvg_probM (cvg_prob_cst P c) (cvg_probM hM hM)))
    (cvg_probM (cvg_prob_cst P (c / 2%:R)) hV).
  rewrite limB.
  by apply: cvg_prob_eq; exists 0%N => d _ a; rewrite expr2.
have sc : Num.sqrt chi != 0 by rewrite sqrtr_eq0 -ltNge lt_def chin chi0.
have hL := cvg_probB (cvg_probM hA (cvg_probV sc (cvg_prob_sqrt hB)))
  (cvg_probM (cvg_prob_cst P (cone_excess kappa)) hD).
have limL : chi * (Num.sqrt chi)^-1 - cone_excess kappa * 0 = Num.sqrt chi.
  by rewrite mulr0 subr0 -{1}(sqr_sqrtr chi0) expr2 mulfK.
rewrite limL in hL.
apply: (cvg_prob_squeeze _ hL hU).
exists 1%N => d d1 a; apply/andP; split; first exact: Pi_lower.
exact: Pi_upper.
Qed.

End prop515.

(* Moreau's decomposition for S^d_kappa and its dual cone: for Z symmetric,
   |proj_{S_kappa} Z|^2 + |proj_{S_kappa'} (- Z)|^2 = |Z|^2. *)
Lemma cone_proj_moreau (kappa : R) d (Z : 'M[RR]_d) : 1 < kappa ->
  Z \is symmetricmx ->
  frobenius (proj (kappa_cone_rV kappa d) (mxvec Z)) ^+ 2 +
  frobenius (proj (kappa_cone_rV (kappa_dual kappa) d) (mxvec (- Z))) ^+ 2 =
  frobenius Z ^+ 2.
Proof.
move=> k1 Zs; have kd1 := kappa_dual_gt1 _ k1.
pose C := kappa_cone_rV kappa d; pose C' := kappa_cone_rV (kappa_dual kappa) d.
have Cc : closed C := kappa_cone_rV_closed _ _ k1.
have Cc' : closed C' := kappa_cone_rV_closed _ _ kd1.
have Cn : C !=set0 by exists 0; exact: kappa_cone_rV0.
have [Cp _] := projP Cc Cn (@kappa_cone_rV_convex kappa d) (mxvec Z).
set p := proj C (mxvec Z) in Cp *.
have [pq0 pq] := (cone_projP Cc (kappa_cone_rV0 kappa d)
  (@kappa_cone_rV_convex kappa d) (@kappa_cone_rV_cone kappa d) (mxvec Z) Cp).1
  erefl.
have dualE := kappa_cone_dual d kappa k1.
(* - (Z - p) is in the dual cone S_kappa' *)
have Cq : C' (p - mxvec Z).
  rewrite /C' /kappa_cone_rV /= -dualE; split.
    have := kappa_cone_sym d kappa _ Cp.
    have /paper_symmetricP Zs' := Zs.
    move=> ps i j; rewrite linearB /= mxvecK !mxE.
    by have := ps i j; rewrite !mxE => ->; rewrite Zs'.
  move=> S CS; rewrite pairing_mxdot.
  have yC : C (mxvec S) by rewrite /C /kappa_cone_rV /= mxvecK.
  have := pq0 _ yC.
  by move=> h; rewrite -mxdot_mxvec vec_mxK -opprB mxdotNl oppr_ge0.
(* and it is the projection of - Z on S_kappa' *)
have E : proj C' (mxvec (- Z)) = p - mxvec Z.
  apply/(cone_projP Cc' (kappa_cone_rV0 _ d) (@kappa_cone_rV_convex _ d)
    (@kappa_cone_rV_cone _ d) (mxvec (- Z)) Cq).
  have -> : mxvec (- Z) - (p - mxvec Z) = - p.
    clearbody p; apply/rowP => k; rewrite !mxE.
    have -> : mxvec (- Z) 0 k = - mxvec Z 0 k by rewrite linearN /= mxE.
    by move: (p 0 k) (mxvec Z 0 k) => t u; ring.
  split.
    move=> y Cy; rewrite mxdotNl oppr_le0.
    move: Cy; rewrite /C' /kappa_cone_rV /= -dualE => -[_ hy].
    have := hy (vec_mx p) Cp; rewrite pairing_mxdot.
    by move=> h; rewrite mxdotC -[y]vec_mxK -[p]vec_mxK mxdot_mxvec.
  by rewrite mxdotNl -opprB mxdotNr opprK mxdotC pq.
rewrite -/C' E !frobenius_sqr -[in RHS]mxdot_mxvec.
have -> : p - mxvec Z = - (mxvec Z - p) by rewrite opprB.
rewrite mxdotNl mxdotNr opprK.
have pq' : mxdot (mxvec Z - p) p = 0 := pq.
have e (u v : 'rV[RR]_(d * d)) :
    mxdot u u = mxdot v v + mxdot (u - v) (u - v) + 2 * mxdot (u - v) v.
  rewrite !mxdotBl !mxdotBr (mxdotC v u).
  by move: (mxdot u u) (mxdot u v) (mxdot v v) => x y z; ring.
by rewrite [RHS](e _ p) pq' mulr0 addr0.
Qed.

(* - G_{d,kappa}(zeta) = G'_{d,kappa'}(zeta') for G' = - G. *)
Lemma shift_mx_dual (kappa zeta : R) d (G : 'M[RR]_d) : 1 < kappa ->
  - shift_mx kappa zeta G =
  shift_mx (kappa_dual kappa) (- 2%:R * zeta / (kappa - 1)) (- G).
Proof.
move=> k1; rewrite /shift_mx opprD -scaleNr; congr (_ + _ *: _).
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have hs := cone_factor_dual kappa k1.
have s0 : 0 < Num.sqrt ((kappa - 1) / 2%:R) by rewrite sqrtr_gt0 divr_gt0.
have e1 : Num.sqrt (2%:R / (kappa - 1)) = (Num.sqrt ((kappa - 1) / 2%:R))^-1.
  by rewrite -sqrtrV ?divr_ge0 ?ltW // invf_div.
have kd0 : 0 <= (kappa_dual kappa - 1) / 2%:R.
  by rewrite divr_ge0 // subr_ge0 ltW // kappa_dual_gt1.
have e2 : Num.sqrt (2%:R / (kappa_dual kappa - 1)) =
    Num.sqrt ((kappa - 1) / 2%:R).
  rewrite -[2%:R / _]invf_div sqrtrV //.
  have an : Num.sqrt ((kappa_dual kappa - 1) / 2%:R) != 0.
    apply/eqP => h0; move: hs; rewrite h0 mul0r => /eqP.
    by rewrite eq_sym oner_eq0.
  by apply: (mulfI an); rewrite mulfV // hs.
have sq : kappa - 1 = 2%:R * Num.sqrt ((kappa - 1) / 2%:R) ^+ 2.
  by rewrite sqr_sqrtr ?divr_ge0 ?ltW // mulrC divfK ?pnatr_eq0.
rewrite e1 e2.
move: s0 sq; move: (Num.sqrt ((kappa - 1) / 2%:R)) => t t0 sq.
rewrite sq; have tn : t != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma goe_part_opp d (a : 'rV[RR]_(d * d)) :
  goe_part (vec_mx (- a)) = - goe_part (vec_mx a).
Proof.
by rewrite /goe_part linearN /= linearN /= -opprD scalerN.
Qed.

(* |G_{d,kappa}(zeta)|^2 / d^2 through the spectrum of W = goe_mx a. *)
Lemma shift_sqnorm_goe (kappa zeta : R) d (a : 'rV[RR]_(d * d)) :
  1 < kappa -> (0 < d)%N ->
  frobenius (shift_mx kappa zeta (goe_part (vec_mx a))) ^+ 2 / d%:R ^+ 2 =
  goe_stat (fun x => x ^+ 2) a / 2%:R +
  2%:R * zeta * Num.sqrt (2%:R / (kappa - 1)) * Num.sqrt (2%:R^-1) *
    goe_stat (fun x => x) a +
  zeta ^+ 2 * (2%:R / (kappa - 1)).
Proof.
move=> k1 d0.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have Ws : goe_mx a \is symmetricmx by apply: goe_mx_symmetric.
have m1 (A : 'M[RR]_d) : mxdot A 1%:M = \tr A.
  by rewrite mxdot_trace trmx1 mulmx1.
rewrite goe_partE // /shift_mx /goe_stat.
move: (goe_mx a) Ws => W Ws.
rewrite frobenius_sqr mxdotDl !mxdotDr !mxdotZl !mxdotZr.
rewrite (mxdotC 1%:M) !m1 mxtrace1 (mxdot_spec Ws) -(sum_spec_trace Ws).
rewrite sqrtrM ?ler0n //.
have u2 : Num.sqrt (d%:R : R) ^+ 2 = d%:R by rewrite sqr_sqrtr ?ler0n.
have v2 : Num.sqrt (2%:R^-1 : R) ^+ 2 = 2%:R^-1.
  by rewrite sqr_sqrtr // invr_ge0 ler0n.
have q2 : Num.sqrt (2%:R / (kappa - 1)) ^+ 2 = 2%:R / (kappa - 1).
  by rewrite sqr_sqrtr // divr_ge0 ?ler0n // subr_ge0 ltW.
have u0 : 0 < Num.sqrt (d%:R : R) by rewrite sqrtr_gt0.
move: (\sum_i spec W 0 i ^+ 2) (\sum_i spec W 0 i) => s2 s1.
move: u2 v2 q2 u0; move: (Num.sqrt (d%:R : R)) (Num.sqrt (2%:R^-1 : R)).
move: (Num.sqrt (2%:R / (kappa - 1))) => q u v u2 v2 q2 u0.
rewrite -u2 -v2 -q2; have un : u != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma goe_sqnorm_cvg (kappa zeta : R) : 1 < kappa ->
  cvg_prob (fun d => gauss (d * d))
    (fun d a => frobenius (shift_mx kappa zeta (goe_part (vec_mx a))) ^+ 2 /
       d%:R ^+ 2)
    (2%:R^-1 + 2%:R * zeta ^+ 2 / (kappa - 1)).
Proof.
move=> k1.
have c2 : continuous (fun x : R => x ^+ 2) by move=> x; exact: exprn_continuous.
have L2 (x y : R) : -3 <= x <= 3 -> -3 <= y <= 3 ->
    `|x ^+ 2 - y ^+ 2| <= 6%:R * `|x - y|.
  move=> /andP[x1 x2] /andP[y1 y2]; rewrite subr_sqr normrM mulrC.
  apply: ler_wpM2r; first exact: normr_ge0.
  by rewrite ler_norml; apply/andP; split; lra.
have c1 : continuous (fun x : R => x) by move=> x; exact: cvg_id.
have L1 (x y : R) : -3 <= x <= 3 -> -3 <= y <= 3 ->
    `|x - y| <= 1 * `|x - y| by move=> _ _; rewrite mul1r.
have h2 := goe_stat_cvg _ _ c2 L2.
have h1 := goe_stat_cvg _ _ c1 L1.
(* the moments of the semicircle law of radius 2 *)
have m2 : \int[semicircle_prob 2]_x ((x : R) ^+ 2) = 1.
  by rewrite semicircle_moment2 ?pnatr_eq0 //; field.
have m1 : \int[semicircle_prob 2]_x (x : R) = 0.
  by apply: semicircle_moment1; rewrite pnatr_eq0.
rewrite m2 in h2; rewrite m1 in h1.
have := cvg_probD (cvg_probD (cvg_probM h2 (cvg_prob_cst _ 2%:R^-1))
  (cvg_probM (cvg_prob_cst _ (2%:R * zeta * Num.sqrt (2%:R / (kappa - 1)) *
    Num.sqrt (2%:R^-1))) h1))
  (cvg_prob_cst _ (zeta ^+ 2 * (2%:R / (kappa - 1)))).
have e : zeta ^+ 2 * (2%:R / (kappa - 1)) = 2%:R * zeta ^+ 2 / (kappa - 1).
  by rewrite mulrA [zeta ^+ 2 * _]mulrC.
rewrite mul1r mulr0 addr0 e.
apply: cvg_prob_eq; exists 1%N => d d1 a.
by rewrite (shift_sqnorm_goe kappa zeta d a k1 d1) e.
Qed.

Lemma shift_mx_sym (kappa zeta : R) d (G : 'M[RR]_d) :
  G \is symmetricmx -> shift_mx kappa zeta G \is symmetricmx.
Proof.
move/symmetricmxP => Gs; apply/symmetricmxP.
by rewrite /shift_mx linearD /= linearZ /= trmx1 Gs.
Qed.

Lemma goe_part_sym d (a : 'rV[RR]_(d * d)) :
  goe_part (vec_mx a) \is symmetricmx.
Proof.
apply/symmetricmxP; rewrite /goe_part linearZ /= linearD /= trmxK.
by rewrite addrC.
Qed.

(* Proposition 5.15: for kappa > 1 and zeta real,
   |proj_{S^d_kappa} G_{d,kappa}(zeta)|_F / d -> sqrt chi_kappa(zeta). *)
Theorem shifted_cone_proj_cvg (kappa zeta : R) : 1 < kappa ->
  cvg_prob (fun d => gauss (d * d))
    (fun d a => frobenius (proj (kappa_cone_rV kappa d)
       (mxvec (shift_mx kappa zeta (goe_part (vec_mx a))))) / d%:R)
    (Num.sqrt (upper_value threshold_law (cone_shift kappa) zeta)).
Proof.
move=> k1; have [k3|k3] := leP 3%:R kappa.
  exact: shifted_cone_proj_cvg3.
have kd1 := kappa_dual_gt1 _ k1.
have kd3 : 3%:R <= kappa_dual kappa by apply: ltW; exact: kappa_dual_gt3.
(* the case kappa' = kappa_dual kappa > 3, at - a *)
have h' : cvg_prob (fun d => gauss (d * d))
    (fun d a => frobenius (proj (kappa_cone_rV (kappa_dual kappa) d)
       (mxvec (shift_mx (kappa_dual kappa) (- 2%:R * zeta / (kappa - 1))
         (goe_part (vec_mx a))))) / d%:R)
    (Num.sqrt (upper_value threshold_law (cone_shift (kappa_dual kappa))
       (- 2%:R * zeta / (kappa - 1)))).
  exact: (shifted_cone_proj_cvg3 _ _ kd3).
have hN := goe_sqnorm_cvg kappa zeta k1.
have h2 := cvg_probM (cvg_prob_gaussN h') (cvg_prob_gaussN h').
have h3 := cvg_prob_sqrt (cvg_probB hN h2).
have c1 := cone_shift_gtN1 _ kd1.
have chi0 := upper_value_ge0 threshold_law2 (- 2%:R * zeta / (kappa - 1)) c1.
rewrite -expr2 (sqr_sqrtr chi0) in h3.
rewrite -(universality_value_dual kappa zeta k1) addrK in h3.
(* Moreau: |proj_{S_kappa} Z|^2 = |Z|^2 - |proj_{S_kappa'} (- Z)|^2 *)
apply: (cvg_prob_eq _ h3); exists 1%N => d d1 a.
have Zs := shift_mx_sym kappa zeta _ _ (goe_part_sym _ a).
rewrite goe_part_opp -(shift_mx_dual kappa zeta d _ k1).
have M := cone_proj_moreau kappa d _ k1 Zs.
have P0 := frobenius_ge0 (proj (kappa_cone_rV kappa d)
  (mxvec (shift_mx kappa zeta (goe_part (vec_mx a))))).
move: M P0; move: (frobenius (proj (kappa_cone_rV kappa d) _)).
move: (frobenius (proj (kappa_cone_rV (kappa_dual kappa) d) _)).
move: (frobenius (shift_mx kappa zeta _)) => N P' P M P0.
have dn : d%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
have -> : N ^+ 2 / d%:R ^+ 2 - P' / d%:R * (P' / d%:R) = (P / d%:R) ^+ 2.
  by rewrite -M; field.
by rewrite sqrtr_sqr ger0_norm // divr_ge0 ?ler0n.
Qed.
