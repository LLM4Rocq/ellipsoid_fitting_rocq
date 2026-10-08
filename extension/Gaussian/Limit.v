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

   Proved here: the deterministic part of Lemma 5.14 and Proposition 5.15,
   for kappa >= 3.
   - cone_proj_kappa_le: |proj_{S^d_kappa} z| <= g if and only if
     <z, T_kappa S> <= g |T_kappa S| for every S >= 0 (cone_proj_le of
     Gaussian/Representation for the closed convex cone S^d_kappa).
   - pairing_spec_le: <G, S> + zeta sqrt d Tr S <=
     d sqrt V_d (|S|^2 + c (Tr S)^2 / d)^(1/2) for S >= 0, by von Neumann's
     inequality (mxdot_spec_le) and the finite form of Lemma 5.7
     (empirical_variational_le).
   - cone_proj_upper: |proj_{S^d_kappa} Z| <= d sqrt V_d + e |diag G|: the
     diagonal rescaling costs e |diag G| |T_kappa S|, and
     |S|^2 + c (Tr S)^2 / d <= |T_kappa S|^2 (frobenius_cone_map_ge).
   - cone_proj_lower: for every w, with R_w = psd_part (G - sqrt d w I),
     d^2 (s_d(w) + (w + zeta) m_d(w)) <= (|proj Z| + e |diag G|) |T R_w|,
     and (cone_map_shifted_part) |T R_w|^2 = d^2 (s_d(w) + c m_d(w)^2) +
     c d diag_var R_w. At the cutoff w of the limit law,
     s(w) + (w + zeta) m(w) = s(w) + c m(w)^2 = chi_kappa(zeta), and
     diag_var R_w / d tends to 0 by Lemma 5.13; this gives the lower bound
     of Proposition 5.15. The paper takes the cutoff of nu_d instead, which
     would need the measurability of a random cutoff; the deterministic one
     suffices because Lemma 5.8 (upper_value_stability) only needs m_d and
     s_d at the cutoff of the limit law.

   Still to come (names come with the proofs).
   - Proposition 5.15 in probability for kappa >= 3. G = goe_part (vec_mx a)
     for a of law gauss (d * d) is sqrt (d / 2) goe_mx a, so
     g_i = spec (goe_mx a) 0 i / sqrt 2 (spec_scale of psd_part.v); m_d(w)
     and s_d(w) at the cutoff w of threshold_law converge by Wigner's law
     (wigner of random_matrix/wigner.v, ge0_integral_semicircle_scale), V_d
     by Lemma 5.8, |diag G| / d tends to 0 by Markov's inequality, and
     diag_var (psd_part (goe_mx a - sqrt 2 w I)) by Lemma 5.13
     (goe_diag_var_tail of random_matrix/goe_rotation.v).
   - Proposition 5.15 for 1 < kappa < 3: Moreau's decomposition
     (moreau_norm of library/convex/moreau.v), the polar cone of S^d_kappa
     (kappa_cone_polar of Gaussian/Cones), the symmetry of gauss,
     - shift_mx kappa zeta G = shift_mx kappa' zeta' (- G) for
     kappa' = kappa_dual kappa and zeta' = - 2 zeta / (kappa - 1),
     |G|^2 / d^2 -> 1/2 by Wigner's law, and the scalar identity
     universality_value_dual of Gaussian/Threshold.
   - Lemma 5.16: phihat_d -> zeta_{alpha,kappa} and Phi_d ->
     (zeta_{alpha,kappa})_+ in probability, from Lemma 5.6 (aux_value_ge of
     Gaussian/Representation), |g| / d -> sqrt alpha, and the CGMT in mean
     and concentration form (library/comparison/cgmt.v).
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
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis Require Import euclidean real_spectral opnorm.
From GaussianAnalysis Require Import least_squares logdet_barrier moreau.
From GaussianAnalysis Require Import psd_part measurable_matrix von_neumann.
From GaussianAnalysis Require Import variational goe_rotation.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd.
From EllipsoidUniversality.Gaussian Require Import Cones Representation.
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

Lemma cone_proj_kappa_le (kappa : R) d (z : 'rV[RR]_(d * d)) (g : R) :
  1 < kappa -> 0 <= g ->
  frobenius (proj (kappa_cone_rV kappa d) z) <= g <->
  forall S, psdmx S ->
    mxdot z (mxvec (cone_map kappa S)) <= g * frobenius (cone_map kappa S).
Proof.
move=> k1 g0.
have C0 : kappa_cone_rV kappa d 0.
  rewrite /kappa_cone_rV /= linear0 -(scale0r (cone_map kappa 1%:M)).
  by apply: kappa_coneZ => //; exists 1%:M => //; case: (psd_trace_slice1 d).
have Ccvx (x y : 'rV[RR]_(d * d)) (t : R) : kappa_cone_rV kappa d x ->
    kappa_cone_rV kappa d y -> 0 <= t <= 1 ->
    kappa_cone_rV kappa d (x + t *: (y - x)).
  move=> Cx Cy /andP[t0 t1].
  have -> : x + t *: (y - x) = (1 - t) *: x + t *: y.
    by apply/rowP => i; rewrite !mxE; ring.
  rewrite /kappa_cone_rV /= linearD !linearZ /=.
  by apply: kappa_coneD; apply: kappa_coneZ => //; rewrite subr_ge0.
have Ccone (y : 'rV[RR]_(d * d)) (a : R) : kappa_cone_rV kappa d y -> 0 <= a ->
    kappa_cone_rV kappa d (a *: y).
  by move=> Cy a0; rewrite /kappa_cone_rV /= linearZ /=; exact: kappa_coneZ.
rewrite (cone_proj_le _ _ _ _ (kappa_cone_rV_closed _ _ k1) C0 Ccvx Ccone g0).
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
