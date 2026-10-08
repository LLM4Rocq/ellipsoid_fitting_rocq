(* The Gaussian fitting error: Lemma 5.4 in law, the set of Lemma 5.5,
   Lemma 5.16 and Proposition 1.4 (ii) of Koehler and Sohn (arXiv
   2608.27372, lines 4992-5076 and 6070-6220 of arxiv_v1.tex), at Stdlib's
   R. Item G8 of stage 2 of phase 5 (lane C), after Proposition 5.15
   (Gaussian/Limit).

   Notation: R_d = psd_trace_slice d, T_kappa = cone_map kappa,
   K = cone_slice kappa d = {mxvec (T_kappa S) | S in R_d}, N = n - 1, and
   zeta = zeta_{alpha,kappa} = cone_shift kappa * m(omega) - omega with
   omega = universality_level_cutoff alpha kappa.

   Proved here.
   - Lemma 5.4 in law. centering_mx k is made of the last k columns of a
     Householder reflection that sends e_0 to the unit vector
     1 / sqrt (k + 1): an orthonormal basis of the orthogonal of 1
     (centering_mx_orth, centering_mx_proj), so that centered_sq v =
     |v Q|^2 (centered_sq_centering). centering_lin k m, the matrix of
     A |-> Q^T A on the (k + 1) x m matrices in the mxvec coordinates, has
     orthonormal columns (centering_lin_orth), so a |-> a *m centering_lin
     maps gauss ((k + 1) m) to gauss (k m) (gauss_orthogonal_law of
     library/comparison/gauss_law.v). gaussian_features kappa n d a, the
     Gaussian features of the rows of vec_mx a, are independent of law
     gaussian_feature_law kappa d when a has law gauss (n d^2)
     (gaussian_features_law, by Model/Rows and Gaussian/Law/LibraryBridge).
     unsat_value_gaussian_features: twice the least squares value of these
     features is 2 / (n d) Phi^2, Phi the escape infimum over tr_set K of
     the k x d^2 matrix Q^T vec_mx a (unsat_value_closed and
     gaussian_feature_vec_dot of Gaussian/Representation, inf_scale_sqr).
     unsat_value_gaussian_law: so 2 unsat_value of k + 1 independent
     features of law gaussian_feature_law kappa d has the law of
     2 / (n d) Phi^2 for a k x d^2 standard Gaussian matrix.
   - Lemma 5.5 in the form of library/comparison/cgmt.v: K is nonempty,
     bounded by cone_radius kappa * d with cone_radius kappa =
     max (1, sqrt ((kappa - 1) / 2)), closed and convex (cone_slice_neq0,
     cone_slice_bounded, cone_slice_closed, cone_slice_convex; cone_sliceE
     writes K as S^d_kappa cut by the hyperplane
     <I, y> = sqrt ((kappa - 1) / 2) d), and the auxiliary value of the
     CGMT on K is (aux_value)_+ (cgmt_aux_cone_slice, by inf_max0).
   - Lemma 5.16, for n / d^2 -> alpha > 0 and kappa > 1. aux_value_cvg:
     phihat_d = d^(-3/2) aux_value (G, |g|) tends to zeta in probability,
     by the crossing of Lemma 5.6 (aux_value_ge_shift), Proposition 5.15
     at zeta +- eps (proj_cvg) and |g| / d -> sqrt alpha (gnorm_cvg,
     gauss_sqnorm_cvg, by the centered chi-square tail). cgmt_aux_cvg: the
     CGMT auxiliary value tends to zeta_+. cgmt_aux_mean_cvg: so does its
     mean at the scale d^(3/2), by concentration (cgmt_aux_tail,
     cvg_prob_concentration and cvg_prob_center of Gaussian/InProbability).
     escape_inf_cvg: Phi_d = d^(-3/2) Phi tends to zeta_+, by the CGMT in
     mean (cgmt_lower and cgmt_upper: the two means differ by at most
     cone_radius kappa * d) and concentration (cgmt_escape_tail).
   - Proposition 1.4 (ii). gaussian_fitting_error_cvg: for
     n(d) / d^2 -> alpha > 0 and kappa > 1, 2 unsat_value (n d) d Z, Z of law
     tuple_prod (fun=> gaussian_feature_law kappa d) (n d), tends to
     universality_e_star alpha kappa in probability, by Lemma 5.4 in law
     (cvg_prob_law) and 2 (d^2 / n) Phi_d^2 -> (2 / alpha) zeta_+^2
     (universality_e_starE of Gaussian/Threshold).
     gaussian_fitting_error_gap: above the threshold, e* > 0
     (universality_e_star_gt0) and the event 2 unsat_value <= e* / 2 is
     negligible. gaussian_fitting_error_limit states the limit in the
     form that Unsat/Universality (U10, lane A) takes as its hypothesis. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets interval reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability realfun exp.
From GaussianAnalysis Require Import euclidean real_spectral measurable_matrix.
From GaussianAnalysis Require Import gauss gauss_law gordon escape cgmt.
From GaussianAnalysis Require Import lindeberg tuple_rows variational goe.
From GaussianAnalysis Require Import goe_rotation semicircle_law chi_square.
From GaussianAnalysis Require Import logdet_barrier moreau.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
From EllipsoidFitting Require Import Gaussian.Law.LibraryBridge.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.
From EllipsoidUniversality.Gaussian Require Import Representation InProbability.
From EllipsoidUniversality.Gaussian Require Import Limit.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares Regularized.
From EllipsoidUniversality.Model Require Import Rows.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

Section centering.
Variable k : nat.

(* The unit vector 1 / sqrt (k + 1) of 'cV_(k + 1). *)
Definition unit_ones : 'cV[R]_(1 + k) := (Num.sqrt k.+1%:R)^-1 *: const_mx 1.

(* A Householder reflection H with H e_0 = unit_ones; its last k columns are
   an orthonormal basis of the orthogonal of 1. *)
Definition centering_householder : 'M[R]_(1 + k) :=
  householder (delta_mx 0 0 - unit_ones).

Definition centering_mx : 'M[R]_(k.+1, k) := rsubmx centering_householder.

Lemma centering_mx_orth : centering_mx^T *m centering_mx = 1%:M.
Proof.
set H := centering_householder.
have HH : H^T *m H = 1%:M by rewrite /H householder_tr householderK.
apply/matrixP => i j; rewrite !mxE.
have := congr1 (fun M : 'M[R]_(1 + k) => M (rshift 1 i) (rshift 1 j)) HH.
rewrite /= !mxE eq_rshift => <-.
by apply: eq_bigr => l _; rewrite !mxE.
Qed.

Lemma centering_mx_proj :
  centering_mx *m centering_mx^T = 1%:M - unit_ones *m unit_ones^T.
Proof.
set H := centering_householder.
have HH : H *m H^T = 1%:M by rewrite /H householder_tr householderK.
have n1 : mxdot (const_mx 1 : 'cV[R]_(1 + k)) (const_mx 1) = k.+1%:R.
  rewrite /mxdot (eq_bigr (fun=> 1)).
    by move=> i _; rewrite big_ord1 !mxE mulr1.
  by rewrite sumr_const card_ord.
have u1 : mxdot (delta_mx 0 0 : 'cV[R]_(1 + k)) (delta_mx 0 0) =
    mxdot unit_ones unit_ones.
  rewrite mxdot_delta mxE !eqxx /= /unit_ones mxdotZl mxdotZr n1.
  by rewrite mulrA -expr2 exprVn sqr_sqrtr ?ler0n // mulVf.
have Hu : H *m delta_mx 0 0 = unit_ones by rewrite /H householder_swap.
have lH : lsubmx H = unit_ones.
  rewrite -Hu -colE; apply/matrixP => i j.
  rewrite [LHS]mxE [RHS]mxE (ord1 j); congr (H i _); exact: val_inj.
have E : H *m H^T = lsubmx H *m (lsubmx H)^T + rsubmx H *m (rsubmx H)^T.
  rewrite -[X in X *m _]hsubmxK -[X in _ *m X^T]hsubmxK.
  by rewrite tr_row_mx mul_row_col.
rewrite /centering_mx -/H; move: E; rewrite HH lH => ->.
by rewrite addrC addKr.
Qed.

Lemma centered_sq_centering (v : 'rV[R]_k.+1) :
  centered_sq v = frobenius (v *m centering_mx) ^+ 2.
Proof.
set S := \sum_(i < k.+1) v 0 i.
have nR : (k.+1%:R : R) != 0 by rewrite pnatr_eq0.
have c1 : centered_sq v = \sum_(i < k.+1) v 0 i ^+ 2 - S ^+ 2 / k.+1%:R.
  rewrite /centered_sq -/S.
  rewrite (eq_bigr (fun i => v 0 i ^+ 2 - 2 * (S / k.+1%:R) * v 0 i +
    (S / k.+1%:R) ^+ 2)).
    by move=> i _; ring.
  rewrite !big_split /= -mulr_sumr -/S sumr_const card_ord.
  rewrite sumrN -mulr_sumr -/S -mulr_natr.
  by field.
rewrite c1 frobenius_sqr mxdot_rowE trmx_mul mulmxA -[v *m _ *m _]mulmxA.
rewrite centering_mx_proj mulmxBr mulmx1 mulmxBl mxE.
have e1 : (v *m v^T) 0 0 = \sum_(i < k.+1) v 0 i ^+ 2.
  by rewrite mxE; apply: eq_bigr => i _; rewrite mxE expr2.
have e2 : (v *m unit_ones) 0 0 = S / Num.sqrt k.+1%:R.
  rewrite mxE /S mulr_suml; apply: eq_bigr => i _.
  by rewrite !mxE mulr1 mulrC.
have e3 : (v *m (unit_ones *m unit_ones^T) *m v^T) 0 0 = S ^+ 2 / k.+1%:R.
  rewrite mulmxA -[v *m unit_ones *m _ *m _]mulmxA -trmx_mul mxE big_ord1.
  rewrite [(v *m unit_ones)^T _ _]mxE.
  change ((v *m unit_ones) 0 0 * (v *m unit_ones) 0 0 = S ^+ 2 / k.+1%:R).
  by rewrite e2 -expr2 expr_div_n sqr_sqrtr.
by rewrite [X in _ = _ + X]mxE e1 e3.
Qed.

End centering.

Section centering_lin.
Variables (k m : nat).

(* The matrix of a |-> mxvec (Q^T vec_mx a), Q = centering_mx k, on the
   (k + 1) x m matrices written as rows. *)
Definition centering_lin : 'M[R]_(k.+1 * m, k * m) :=
  lin_mx (mulmx (centering_mx k)^T).

Lemma centering_linE (a : 'rV[R]_(k.+1 * m)) :
  a *m centering_lin = mxvec ((centering_mx k)^T *m vec_mx a).
Proof. by rewrite /centering_lin mul_rV_lin. Qed.

Lemma tr_centering_lin : centering_lin^T = lin_mx (mulmx (centering_mx k)).
Proof.
apply/matrixP => i j; rewrite /centering_lin !mxE /=.
case/mxvec_indexP: i => a b; case/mxvec_indexP: j => c e.
rewrite !vec_mx_delta !mxvecE !mxE.
rewrite (bigD1 c) //= big1 ?addr0.
  by move=> l lc; rewrite [delta_mx _ _ _ _]mxE (negPf lc) mulr0.
rewrite (bigD1 a) //= big1 ?addr0.
  by move=> l la; rewrite [delta_mx _ _ _ _]mxE (negPf la) mulr0.
by rewrite [(centering_mx k)^T _ _]mxE ![delta_mx _ _ _ _]mxE !eqxx /= eq_sym.
Qed.

(* Its columns are orthonormal. *)
Lemma centering_lin_orth : centering_lin^T *m centering_lin = 1%:M.
Proof.
apply/row_matrixP => i; rewrite row_mul row1 rowE tr_centering_lin.
rewrite mul_rV_lin.
by rewrite mul_rV_lin /= mxvecK mulmxA centering_mx_orth mul1mx vec_mxK.
Qed.

End centering_lin.

Section gaussian_features.
Variables (kappa : R) (n d : nat).

(* The Gaussian features of the n rows of the n x d^2 matrix vec_mx a. *)
Definition gaussian_features (a : 'rV[RR]_(n * (d * d))) :
    n.-tuple 'rV[RR]_(d * d) :=
  [tuple gaussian_feature_vec kappa d (row i (vec_mx a : 'M[RR]_(n, d * d)))
   | i < n].

Lemma measurable_gaussian_features :
  measurable_fun [set: 'rV[RR]_(n * (d * d))] gaussian_features.
Proof.
apply/measurable_fun_tnthP => i.
apply: (eq_measurable_fun (fun a : 'rV[RR]_(n * (d * d)) =>
  gaussian_feature_vec kappa d (row i (vec_mx a : 'M[RR]_(n, d * d))))).
  by move=> a _; rewrite /= /gaussian_features tnth_mktuple.
apply: measurableT_comp; first exact: measurable_gaussian_feature_vec.
apply/measurable_fun_mxP => p j.
apply: (eq_measurable_fun (fun a : 'rV[RR]_(n * (d * d)) =>
  a 0 (mxvec_index i j))).
  by move=> a _; rewrite !mxE.
exact: measurable_mxentry.
Qed.

(* The rows of vec_mx a are the rows of the tuple of its coordinates. *)
Lemma gaussian_features_rows (x : (n * (d * d)).-tuple (measurableTypeR R)) :
  gaussian_features (row_of_tuple (n * (d * d)) x) =
  tuple_map (fun=> fun t => gaussian_feature_vec kappa d
    (row_of_tuple (d * d) t)) (tuple_rows n (d * d) x).
Proof.
apply: eq_from_tnth => i; rewrite /gaussian_features /tuple_map !tnth_mktuple.
congr (gaussian_feature_vec kappa d _); apply/rowP => j.
rewrite !mxE tnth_mktuple; congr (tnth x _); apply: val_inj.
change (nat_of_ord (mxvec_index i j) = nat_of_ord (row_index i j)).
by rewrite mxvec_index_val.
Qed.

(* For a of law gauss (n * d^2) they are n independent features of law
   gaussian_feature_law kappa d. *)
Lemma gaussian_features_law (S : set (n.-tuple 'rV[RR]_(d * d))) :
  measurable S ->
  tuple_prod (fun=> gaussian_feature_law kappa d) n S =
  gauss (n * (d * d)) (gaussian_features @^-1` S).
Proof.
move=> mS.
pose g (t : (d * d).-tuple (measurableTypeR R)) :=
  gaussian_feature_vec kappa d (row_of_tuple (d * d) t).
have mg : measurable_fun setT g.
  exact: measurableT_comp (measurable_gaussian_feature_vec kappa d)
    (measurable_row_of_tuple (d * d)).
have mFS : measurable (gaussian_features @^-1` S).
  by rewrite -[X in measurable X]setTI; exact: measurable_gaussian_features.
rewrite gauss_gaussian_product_law // gaussian_sample_lawE.
have -> : row_of_tuple (n * (d * d)) @^-1` (gaussian_features @^-1` S) =
    (fun x => tuple_map (fun=> g) (tuple_rows n (d * d) x)) @^-1` S.
  by apply/seteqP; split => x /=; rewrite gaussian_features_rows.
rewrite (sample_map_law _ n (d * d) _ _ (gaussian_feature_law kappa d) g S mg
  _ mS) //.
move=> B mB.
have mBG : measurable (gaussian_feature_vec kappa d @^-1` B).
  rewrite -[X in measurable X]setTI.
  exact: measurable_gaussian_feature_vec.
rewrite -gaussian_product_law_tuple_prod.
exact: (gauss_gaussian_product_law (d * d) _ mBG).
Qed.

End gaussian_features.

(* The image K of R_d under T_kappa in the mxvec coordinates: the compact
   convex set of the CGMT. *)
Definition cone_slice (kappa : R) d : set 'rV[RR]_(d * d) :=
  [set mxvec (cone_map kappa S) | S in psd_trace_slice d].

Definition cone_radius (kappa : R) : R :=
  Num.max 1 (Num.sqrt ((kappa - 1) / 2%:R)).

Arguments cone_slice kappa%_ring_scope d.
Arguments cone_radius kappa%_ring_scope.

Lemma cone_slice_neq0 (kappa : R) d : cone_slice kappa d !=set0.
Proof.
exists (mxvec (cone_map kappa 1%:M)); exists 1%:M => //.
exact: psd_trace_slice1.
Qed.

Lemma frobenius_cone_map_le (kappa : R) d (S : 'M[R]_d) : 1 <= kappa ->
  frobenius (cone_map kappa S) <= cone_radius kappa * frobenius S.
Proof.
move=> k1.
have e : mxdot (cone_map kappa S) (cone_map kappa S) =
    mxdot S S + cone_shift kappa * \sum_i S i i * S i i.
  exact: pairing_cone_map.
have r0 : 0 <= cone_radius kappa by rewrite le_max ler01.
rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 //.
rewrite exprMn !frobenius_sqr e.
have hd : \sum_i S i i * S i i <= mxdot S S.
  apply: le_trans (diag_sqr_le S); rewrite le_eqVlt; apply/orP; left.
  by apply/eqP; apply: eq_bigr => i _; rewrite expr2.
have h0 : 0 <= \sum_i S i i * S i i.
  by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
have S0 := mxdot_ge0 S.
have [c0|c0] := leP 0 (cone_shift kappa).
  (* |T S|^2 <= (1 + c) |S|^2 = (kappa - 1)/2 |S|^2 *)
  apply: le_trans (_ : mxdot S S + cone_shift kappa * mxdot S S <= _).
    by rewrite lerD2l ler_wpM2l.
  rewrite -[X in X + _]mul1r -mulrDl cone_shiftD1 ler_wpM2r //.
  have q0 : 0 <= (kappa - 1) / 2%:R by rewrite divr_ge0 // subr_ge0.
  rewrite -(sqr_sqrtr q0) ler_sqr ?nnegrE ?sqrtr_ge0 //.
  by rewrite le_max lexx orbT.
(* c < 0: |T S|^2 <= |S|^2 *)
apply: le_trans (_ : mxdot S S <= _).
  by rewrite gerDl mulr_le0_ge0 // ltW.
rewrite -[X in X <= _]mul1r ler_wpM2r // -(expr1n _ 2) ler_sqr ?nnegrE //.
by rewrite le_max lexx.
Qed.

Lemma cone_slice_bounded (kappa : R) d (x : 'rV[RR]_(d * d)) : 1 <= kappa ->
  cone_slice kappa d x -> frobenius x <= cone_radius kappa * d%:R.
Proof.
move=> k1 [S [Sp St] <-]; rewrite frobenius_mxvec.
apply: le_trans (frobenius_cone_map_le kappa d S k1) _.
rewrite ler_wpM2l ?le_max ?ler01 // -St.
exact: frobenius_le_trace.
Qed.

Lemma cone_sliceE (kappa : R) d : 1 < kappa ->
  cone_slice kappa d = kappa_cone_rV kappa d `&`
    [set y | mxdot (mxvec 1%:M) y = Num.sqrt ((kappa - 1) / 2%:R) * d%:R].
Proof.
move=> k1.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have s0 : 0 < Num.sqrt ((kappa - 1) / 2%:R) by rewrite sqrtr_gt0 divr_gt0.
have key (S : 'M[R]_d) : mxdot (mxvec 1%:M) (mxvec (cone_map kappa S)) =
    Num.sqrt ((kappa - 1) / 2%:R) * \tr S.
  rewrite mxdot_mxvec.
  have := trace_cone_map kappa d S k1; rewrite paper_traceE pairing_mxdot => ->.
  rewrite mulrA -sqrtrM ?divr_ge0 ?ltW //.
  have -> : (kappa - 1) / 2%:R * (2%:R / (kappa - 1)) = 1.
    by rewrite mulrC mulrA divfK ?gt_eqF // mulfV // pnatr_eq0.
  by rewrite sqrtr1 mul1r.
apply/seteqP; split.
  move=> _ [S [Sp St] <-]; split.
    by rewrite /kappa_cone_rV /= mxvecK; exists S.
  by rewrite /= key -paper_traceE St.
move=> y [[S Sp E] hy]; exists S; last by rewrite E vec_mxK.
split => //.
move: hy; rewrite /= -[y]vec_mxK -E key paper_traceE.
have sn : Num.sqrt ((kappa - 1) / 2%:R) != 0 by rewrite gt_eqF.
by move/(mulfI sn).
Qed.

Lemma cone_slice_closed (kappa : R) d : 1 < kappa ->
  closed (cone_slice kappa d).
Proof.
move=> k1; rewrite cone_sliceE //; apply: closedI.
  exact: kappa_cone_rV_closed.
pose u := mxvec (1%:M : 'M[RR]_d).
apply: (@preimage_closed _ _ (fun y : 'rV[RR]_(d * d) => mxdot u y)
  [set Num.sqrt ((kappa - 1) / 2%:R) * d%:R]); last exact: closed_eq.
move=> y _.
have -> : (fun y : 'rV[RR]_(d * d) => mxdot u y) = (fun y => (y *m u^T) 0 0).
  by apply/funext => z; rewrite mxdotC mxdot_rowE.
apply: (@continuous_comp _ _ _ (fun w : 'rV[RR]_(d * d) => w *m u^T)
  (fun M : 'M[RR]_1 => M 0 0)); first exact: continuous_mulmxr.
exact: matrix_normedtype.coord_continuous.
Qed.

Lemma cone_slice_convex (kappa : R) d (x y : 'rV[RR]_(d * d)) (t : R) :
  1 < kappa -> cone_slice kappa d x -> cone_slice kappa d y -> 0 <= t <= 1 ->
  cone_slice kappa d (x + t *: (y - x)).
Proof.
move=> k1; rewrite !cone_sliceE // => -[Cx hx] [Cy hy] t01; split.
  exact: kappa_cone_rV_convex.
by rewrite /= mxdotDr mxdotZr mxdotBr hx hy subrr mulr0 addr0.
Qed.

(* inf (F x)_+ = (inf F)_+ on a nonempty set where F is bounded below. *)
Lemma inf_max0 (T : Type) (A : set T) (F : T -> R) :
  A !=set0 -> has_lbound (F @` A) ->
  inf [set Num.max 0 (F x) | x in A] = Num.max 0 (inf (F @` A)).
Proof.
move=> An Ab.
have Fn : F @` A !=set0 by case: An => x Ax; exists (F x), x.
have Sn : [set Num.max 0 (F x) | x in A] !=set0.
  by case: An => x Ax; exists (Num.max 0 (F x)), x.
have Sb : has_lbound [set Num.max 0 (F x) | x in A].
  by exists 0 => _ [x _ <-]; rewrite le_max lexx.
apply/le_anti/andP; split.
  apply/ler_addgt0Pr => e e0.
  have [_ [x Ax <-] hx] := inf_adherent e0 (conj Fn Ab).
  apply: le_trans (ge_inf Sb (ex_intro2 _ _ x Ax erefl)) _.
  exact: max0_leD (ltW e0) (ltW hx).
apply: lb_le_inf Sn _ => _ [x Ax <-].
rewrite ge_max le_max lexx /=.
apply: le_trans (ge_inf Ab (ex_intro2 _ _ x Ax erefl)) _.
by rewrite le_max lexx orbT.
Qed.

(* The auxiliary value of the CGMT on K = tr_set (cone_slice kappa d) is
   (aux_value)_+ at G = goe_part (vec_mx h) and |g|. *)
Lemma cgmt_aux_cone_slice (kappa : R) d N (g : 'rV[RR]_N)
    (h : 'rV[RR]_(d * d)) :
  cgmt_aux (tr_set (cone_slice kappa d)) g h =
  Num.max 0 (aux_value kappa d (goe_part (vec_mx h)) (frobenius g)).
Proof.
rewrite cgmt_aux_tr_set /aux_value.
set G := goe_part (vec_mx h).
pose F (S : 'M[R]_d) := frobenius g * frobenius (cone_map kappa S) -
  paper_main_pairing G (cone_map kappa S).
have FE (S : 'M[R]_d) : psd_trace_slice d S ->
    frobenius g * frobenius (mxvec (cone_map kappa S)) -
    mxdot h (mxvec (cone_map kappa S)) = F S.
  move=> [[Ss _] _]; rewrite /F frobenius_mxvec /G pairing_goe_part.
    exact: cone_map_sym.
  by rewrite -[h in mxdot h _]vec_mxK mxdot_mxvec.
have -> : [set Num.max 0 (frobenius g * frobenius x - mxdot h x) |
    x in cone_slice kappa d] = [set Num.max 0 (F S) | S in psd_trace_slice d].
  apply/seteqP; split.
    by move=> _ [_ [S HS <-] <-]; exists S => //; rewrite FE.
  move=> _ [S HS <-]; exists (mxvec (cone_map kappa S)); first by exists S.
  by rewrite FE.
rewrite inf_max0 //; first by exists 1%:M; exact: psd_trace_slice1.
exists (- (frobenius (cone_map kappa G) * d%:R)) => _ [S [Sp St] <-].
rewrite /F -cone_map_pairing.
have h1 : paper_main_pairing (cone_map kappa G) S <=
    frobenius (cone_map kappa G) * d%:R.
  apply: le_trans (ler_mxdot _ _) _.
  by rewrite -St ler_wpM2l ?frobenius_ge0 // frobenius_le_trace.
have h2 : 0 <= frobenius g * frobenius (cone_map kappa S).
  by rewrite mulr_ge0 ?frobenius_ge0.
lra.
Qed.

(* inf (c f^2) = c (inf f)^2 for c >= 0 and f >= 0. *)
Lemma inf_scale_sqr (T : Type) (A : set T) (f : T -> R) (c : R) :
  A !=set0 -> 0 <= c -> (forall x, A x -> 0 <= f x) ->
  inf [set c * f x ^+ 2 | x in A] = c * inf (f @` A) ^+ 2.
Proof.
move=> An c0 f0.
have Fn : f @` A !=set0 by case: An => x Ax; exists (f x), x.
have Fb : has_lbound (f @` A) by exists 0 => _ [x Ax <-]; exact: f0.
have Sn : [set c * f x ^+ 2 | x in A] !=set0.
  by case: An => x Ax; exists (c * f x ^+ 2), x.
have Sb : has_lbound [set c * f x ^+ 2 | x in A].
  by exists 0 => _ [x Ax <-]; rewrite mulr_ge0 // sqr_ge0.
set m := inf (f @` A).
have m0 : 0 <= m by apply: lb_le_inf Fn _ => _ [x Ax <-]; exact: f0.
have mf x : A x -> m <= f x.
  by move=> Ax; exact: (ge_inf Fb (ex_intro2 _ _ x Ax erefl)).
have St x : A x -> inf [set c * f x ^+ 2 | x in A] <= c * f x ^+ 2.
  by move=> Ax; exact: (ge_inf Sb (ex_intro2 _ _ x Ax erefl)).
apply/le_anti/andP; split; last first.
  apply: lb_le_inf Sn _ => _ [x Ax <-].
  apply: ler_wpM2l => //.
  by rewrite !expr2 ler_pM // mf.
set t := inf _.
have [c00|cn] := eqVneq c 0.
  by case: An => x Ax; apply: le_trans (St x Ax) _; rewrite c00 !mul0r.
have cp : 0 < c by rewrite lt0r cn c0.
(* if c m^2 < t, some f x is below sqrt (t / c), and c f(x)^2 < t *)
rewrite leNgt; apply/negP => ht.
have t0 : 0 <= t.
  by apply: lb_le_inf Sn _ => _ [x Ax <-]; rewrite mulr_ge0 // sqr_ge0.
have tc : 0 <= t / c by rewrite divr_ge0 // ltW.
have hm : m < Num.sqrt (t / c).
  rewrite -ltr_sqr ?nnegrE ?sqrtr_ge0 // (sqr_sqrtr tc).
  by rewrite ltr_pdivlMr // mulrC.
have e0 : 0 < Num.sqrt (t / c) - m by rewrite subr_gt0.
have [_ [x Ax <-] hx] := inf_adherent e0 (conj Fn Fb).
rewrite -/m addrC subrK in hx.
have : c * f x ^+ 2 < t.
  rewrite -ltr_pdivlMl // mulrC.
  have fx0 := f0 x Ax.
  rewrite -(sqr_sqrtr tc).
  by rewrite ltr_sqr ?nnegrE ?sqrtr_ge0.
by rewrite ltNge St.
Qed.

(* Lemma 5.4: twice the least squares value of the Gaussian features of the
   rows of vec_mx a is 2 / (n d) Phi^2, Phi the escape infimum of the
   (n - 1) x d^2 matrix Q^T vec_mx a over K = cone_slice kappa d. *)
Lemma unsat_value_gaussian_features (kappa : R) k d
    (a : 'rV[RR]_(k.+1 * (d * d))) : 1 < kappa -> (0 < d)%N ->
  2 * unsat_value k.+1 d (gaussian_features kappa k.+1 d a) =
  2%:R / (k.+1%:R * d%:R) * escape_inf (tr_set (cone_slice kappa d))
    (vec_mx (a *m centering_lin k (d * d)) : 'M[RR]_(k, d * d)) ^+ 2.
Proof.
move=> k1 d0.
set A := vec_mx a : 'M[RR]_(k.+1, d * d).
set B := vec_mx (a *m centering_lin k (d * d)) : 'M[RR]_(k, d * d).
have BE : B = (centering_mx k)^T *m A by rewrite /B centering_linE mxvecK.
have dR : 0 < d%:R :> R by rewrite ltr0n.
rewrite unsat_value_closed // escape_inf_tr_set.
(* the centered squares of the features at S *)
have key (S : 'M[R]_d) : psd_trace_slice d S ->
    centered_sq (feature_row (gaussian_features kappa k.+1 d a) S) =
    2%:R / d%:R * frobenius (B *m (mxvec (cone_map kappa S))^T) ^+ 2.
  move=> [[Ss _] _].
  set x := mxvec (cone_map kappa S).
  have fr : feature_row (gaussian_features kappa k.+1 d a) S =
      Num.sqrt (2%:R / d%:R) *: (A *m x^T)^T.
    apply/rowP => i; rewrite /feature_row /gaussian_features.
    rewrite [LHS]mxE tnth_mktuple gaussian_feature_vec_dot //.
    rewrite [mxvec (_ *: _)]linearZ /= mxdotZr mxdot_rowE.
    by rewrite [RHS]mxE [(_ ^T) 0 i]mxE -row_mul [row _ _ _ _]mxE.
  rewrite fr centered_sq_centering -scalemxAl frobeniusZ exprMn.
  rewrite ger0_norm ?sqrtr_ge0 // sqr_sqrtr ?divr_ge0 ?ler0n //.
  by rewrite -frobenius_trmx trmx_mul trmxK BE mulmxA.
have -> : [set centered_sq (feature_row (gaussian_features kappa k.+1 d a) S)
    | S in psd_trace_slice d] =
    [set 2%:R / d%:R * frobenius (B *m x^T) ^+ 2 | x in cone_slice kappa d].
  apply/seteqP; split.
    move=> _ [S HS <-]; exists (mxvec (cone_map kappa S)); first by exists S.
    by rewrite key.
  by move=> _ [_ [S HS <-] <-]; exists S => //; rewrite key.
rewrite inf_scale_sqr.
- exact: cone_slice_neq0.
- by rewrite divr_ge0 ?ler0n.
- by move=> y _; exact: frobenius_ge0.
by rewrite mulrA; congr (_ * _); rewrite invfM mulrCA mulrA.
Qed.

(* Lemma 5.4 in law: for n = k + 1 independent Gaussian features, twice the
   least squares value has the law of 2 / (n d) Phi^2, Phi the escape
   infimum over K of a k x d^2 standard Gaussian matrix. *)
Lemma unsat_value_gaussian_law (kappa : R) k d (B : set RR) :
  1 < kappa -> (0 < d)%N -> measurable B ->
  tuple_prod (fun=> gaussian_feature_law kappa d) k.+1
    [set Z | B (2 * unsat_value k.+1 d Z)] =
  gauss (k * (d * d)) [set b | B (2%:R / (k.+1%:R * d%:R) *
    escape_inf (tr_set (cone_slice kappa d))
      (vec_mx b : 'M[RR]_(k, d * d)) ^+ 2)].
Proof.
move=> k1 d0 mB.
pose G (b : 'rV[RR]_(k * (d * d))) := 2%:R / (k.+1%:R * d%:R) *
  escape_inf (tr_set (cone_slice kappa d)) (vec_mx b : 'M[RR]_(k, d * d)) ^+ 2.
have K0 := tr_set_neq0 (cone_slice_neq0 kappa d).
have Kb := tr_set_bounded (fun x => cone_slice_bounded kappa d x (ltW k1)).
have mG : measurable_fun setT G.
  apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_funX.
  exact: (@measurable_escape_inf RR k (d * d) _ _ K0 Kb).
have mGB : measurable [set b | B (G b)].
  by rewrite -[X in measurable X]setTI; exact: mG.
have mU : measurable_fun setT
    (fun Z : k.+1.-tuple 'rV[RR]_(d * d) => 2 * unsat_value k.+1 d Z : RR).
  apply: measurable_funM; first exact: measurable_cst.
  exact: measurable_unsat_value.
have mS : measurable
    [set Z : k.+1.-tuple 'rV[RR]_(d * d) | B (2 * unsat_value k.+1 d Z)].
  by rewrite -[X in measurable X]setTI; exact: mU.
rewrite gaussian_features_law //.
have -> : gaussian_features kappa k.+1 d @^-1`
    [set Z | B (2 * unsat_value k.+1 d Z)] =
    [set a | [set b | B (G b)] (a *m centering_lin k (d * d))].
  by apply/seteqP; split => a /=; rewrite unsat_value_gaussian_features.
exact: (gauss_orthogonal_law (centering_lin_orth k (d * d)) mGB).
Qed.

(* |g|^2 / d^2 -> alpha for g of law gauss (N d) with N d / d^2 -> alpha. *)
Lemma centered_chi2_ones n (x : 'rV[RR]_n) :
  centered_chi2 (const_mx 1) x = frobenius x ^+ 2 - n%:R.
Proof.
rewrite /centered_chi2 frobenius_sqr /mxdot big_ord1.
have -> : n%:R = \sum_(j < n) (1 : RR) by rewrite sumr_const card_ord.
by rewrite -sumrB; apply: eq_bigr => i _; rewrite mxE mul1r expr2.
Qed.

Lemma gauss_sqnorm_cvg (N : nat -> nat) (alpha : R) :
  (forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
     `|(N d)%:R / d%:R ^+ 2 - alpha| < eps) ->
  cvg_prob (fun d => gauss (N d)) (fun d g => frobenius g ^+ 2 / d%:R ^+ 2)
    alpha.
Proof.
move=> hN eta e0 eps p0.
have e2 : 0 < eta / 2 by rewrite divr_gt0.
have [D1 h1] := hN _ e2.
have [D2 h2] := hN 1 ltr01.
have k0 : 0 < eta ^+ 2 / (16%:R * (`|alpha| + 1) + 8%:R * eta).
  by rewrite divr_gt0 ?exprn_gt0 // addr_gt0 // mulr_gt0 // ltr_wpDl.
move: k0; set k := eta ^+ 2 / _ => k0.
exists (maxn (maxn D1 D2) (archimedean.Num.truncn (2 / (k * eps))).+1) => d.
rewrite !geq_max => /andP[/andP[d1 d2] d3].
have dR : 0 < d%:R :> R by rewrite ltr0n (leq_trans _ d3).
have hd1 := h1 d d1; have hd2 := h2 d d2.
set u := eta / 2 * d%:R ^+ 2.
have u0 : 0 < u by rewrite mulr_gt0 // exprn_gt0.
exists [set g : 'rV[RR]_(N d) | u <= `|centered_chi2 (const_mx 1) g|]; split.
- have mf : measurable_fun [set: 'rV[RR]_(N d)]
      (fun g => `|centered_chi2 (const_mx 1) g| : RR).
    apply: measurableT_comp; first exact: normr_measurable.
    exact: measurable_centered_chi2.
  have mI : measurable [set y : RR | u <= y].
    have -> : [set y : RR | u <= y] =
        [set` Interval (BLeft u) (BInfty _ false)].
      by apply/seteqP; split => y /=; rewrite in_itv /= andbT.
    exact: measurable_itv.
  by have := mf measurableT _ mI; rewrite setTI.
- have aL (i : 'I_(N d)) : `|(const_mx 1 : 'rV[RR]_(N d)) 0 i| <= 1.
    by rewrite mxE normr1.
  have a2 : mxdot (const_mx 1 : 'rV[RR]_(N d)) (const_mx 1) = (N d)%:R.
    have -> : (N d)%:R = \sum_(j < N d) (1 : RR).
      by rewrite sumr_const card_ord.
    by rewrite /mxdot big_ord1; apply: eq_bigr => i _; rewrite !mxE mulr1.
  have vu : 0 < mxdot (const_mx 1 : 'rV[RR]_(N d)) (const_mx 1) + 1 * u.
    by rewrite a2 mul1r ltr_wpDl ?ler0n.
  apply: le_trans (gauss_centered_chi2_abs_tail ler01 aL u0 vu) _.
  rewrite lee_fin a2 mul1r.
  have d2R : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0.
  (* N d <= (|alpha| + 1) d^2 *)
  have Nb : (N d)%:R <= (`|alpha| + 1) * d%:R ^+ 2.
    rewrite -ler_pdivrMr //; apply: le_trans (_ : alpha + 1 <= _).
      move: hd2; rewrite ltr_norml => /andP[_].
      by rewrite ltrBlDr addrC => /ltW.
    by rewrite lerD2r ler_norm.
  (* the exponent is at least k d^2 *)
  have hx : k * d%:R ^+ 2 <= u ^+ 2 / (4 * ((N d)%:R + u)).
    have pos : 0 < 4 * ((N d)%:R + u) by rewrite mulr_gt0 // ltr_wpDl ?ler0n.
    rewrite ler_pdivlMr //.
    apply: le_trans (_ : k * d%:R ^+ 2 *
      (4 * ((`|alpha| + 1) * d%:R ^+ 2 + u)) <= _).
      apply: ler_wpM2l; first by rewrite mulr_ge0 // ltW.
      by apply: ler_wpM2l; [rewrite ler0n | rewrite lerD2r].
    rewrite /k /u le_eqVlt; apply/orP; left; apply/eqP.
    have hn : 16%:R * (`|alpha| + 1) + 8%:R * eta != 0 :> R.
      by rewrite gt_eqF // addr_gt0 // mulr_gt0 // ltr_wpDl.
    by field.
  have hd : 2 < d%:R * (k * eps).
    have kp : 0 < k * eps by rewrite mulr_gt0.
    rewrite -(ltr_pdivrMr _ _ kp).
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  have dd : d%:R <= d%:R ^+ 2 :> R.
    by rewrite expr2 ler_peMl ?ler0n // ler1n (leq_trans _ d3).
  have h3 : 2 / eps < k * d%:R ^+ 2.
    rewrite ltr_pdivrMr // mulrAC; apply: lt_le_trans hd _.
    by rewrite mulrC ler_pM2l // mulr_gt0.
  (* 2 exp (- k d^2) <= 2 / (k d^2) <= eps *)
  rewrite mulNr.
  apply: le_trans (_ : 2 * sequences.expR (- (k * d%:R ^+ 2)) <= _).
    by rewrite ler_wpM2l ?ler0n // ler_expR lerN2.
  have ey : 2 / eps < sequences.expR (k * d%:R ^+ 2).
    apply: lt_le_trans h3 _; apply: le_trans (expR_ge1Dx _).
    by rewrite lerDr.
  rewrite expRN -[2 * _]/(2 / _) ler_pdivrMr ?expR_gt0 //.
  by rewrite ltr_pdivrMr // mulrC in ey; exact: ltW.
- move=> x /= h; rewrite centered_chi2_ones.
  have t := ler_distD ((N d)%:R / d%:R ^+ 2) (frobenius x ^+ 2 / d%:R ^+ 2)
    alpha.
  have e : `|frobenius x ^+ 2 / d%:R ^+ 2 - (N d)%:R / d%:R ^+ 2| =
      `|frobenius x ^+ 2 - (N d)%:R| / d%:R ^+ 2.
    rewrite -mulrBl normrM; congr (_ * _).
    by rewrite ger0_norm // invr_ge0 exprn_ge0 // ltW.
  rewrite e in t.
  have h' : eta / 2 <= `|frobenius x ^+ 2 - (N d)%:R| / d%:R ^+ 2.
    move: t h hd1; move: (`|frobenius x ^+ 2 / d%:R ^+ 2 - alpha|) => p.
    move: (`|(N d)%:R / d%:R ^+ 2 - alpha|) => q.
    move: (`|frobenius x ^+ 2 - (N d)%:R| / d%:R ^+ 2) => r.
    by move=> t h hq; clear -t h hq; lra.
  by rewrite ler_pdivlMr ?exprn_gt0 // in h'.
Qed.

(* Lemma 5.6 with the shift written as in shift_mx. *)
Lemma aux_value_ge_shift (kappa t : R) d (G : 'M[R]_d) (g : R) :
  1 < kappa -> (0 < d)%N -> 0 <= g ->
  t * (d%:R * Num.sqrt d%:R) <= aux_value kappa d G g <->
  frobenius (proj (kappa_cone_rV kappa d) (mxvec (shift_mx kappa t G))) <= g.
Proof.
move=> k1 d0 g0; rewrite (aux_value_ge kappa d G g _ k1 d0 g0) /shift_mx.
have dn : d%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
have -> : t * (d%:R * Num.sqrt d%:R) / d%:R = t * Num.sqrt d%:R.
  by rewrite [d%:R * _]mulrC mulrA mulfK.
by [].
Qed.



(* Lemma 5.16 and Proposition 1.4 (ii), for n(d) / d^2 -> alpha > 0 and
   kappa > 1. *)
Section fitting_error_limit.
Variables (alpha kappa : R) (n : nat -> nat).
Hypotheses (a0 : 0 < alpha) (k1 : 1 < kappa).
Hypothesis hn : universality_density_tends_to n alpha.

Local Notation N := (fun d => (n d).-1).
Local Notation P := (fun d => @gauss RR ((n d).-1 + d * d)).
Local Notation zs := (cone_shift kappa *
  universality_m (universality_level_cutoff alpha kappa) -
  universality_level_cutoff alpha kappa).
Local Notation chi := (upper_value threshold_law (cone_shift kappa)).

Lemma sample_density_cvg (eps : R) : 0 < eps -> exists D : nat, forall d,
  (D <= d)%N -> `|(N d)%:R / d%:R ^+ 2 - alpha| < eps.
Proof.
move=> e0; have e2 : 0 < eps / 2 by rewrite divr_gt0.
have [D h] := hn _ e2.
exists (maxn D (archimedean.Num.truncn (2 / eps)).+1) => d.
rewrite geq_max => /andP[dD d1].
have dR : 0 < d%:R :> R by rewrite ltr0n (leq_trans _ d1).
have d2R : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0.
have hd := h d dD; rewrite /paper_main_density RdivE in hd.
have hN1 : ((n d).-1)%:R <= (n d)%:R :> R by rewrite ler_nat leq_pred.
have hN2 : (n d)%:R <= ((n d).-1)%:R + 1 :> R.
  have := leqSpred (n d); rewrite -(ler_nat RR) => h'.
  by apply: le_trans h' _; rewrite -addn1 natrD.
(* 1 / d^2 < eps / 2 *)
have hd1 : 1 / d%:R ^+ 2 < eps / 2.
  have h2 : 2 / eps < d%:R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  have dd : d%:R <= d%:R ^+ 2 :> R.
    by rewrite expr2 ler_peMl ?ler0n // ler1n (leq_trans _ d1).
  rewrite ltr_pdivrMr // mulrC.
  apply: lt_le_trans (_ : 1 < d%:R * (eps / 2)) _; last first.
    by rewrite ler_pM2r // divr_gt0.
  by rewrite -ltr_pdivrMr ?divr_gt0 // invf_div mul1r.
have t := ler_distD ((n d)%:R / d%:R ^+ 2) ((n d).-1%:R / d%:R ^+ 2) alpha.
apply: le_lt_trans t _.
have e1 : `|(n d).-1%:R / d%:R ^+ 2 - (n d)%:R / d%:R ^+ 2| <=
    (1 / d%:R ^+ 2 : RR).
  have i0 : 0 < (d%:R ^+ 2)^-1 :> R by rewrite invr_gt0.
  rewrite -mulrBl normrM (ger0_norm (ltW i0)) ler_pM2r //.
  by rewrite distrC ger0_norm ?subr_ge0 // lerBlDr addrC.
move: e1 hd hd1.
move: (`|(n d).-1%:R / d%:R ^+ 2 - (n d)%:R / d%:R ^+ 2|) => p.
move: (`|(n d)%:R / d%:R ^+ 2 - alpha|) (1 / d%:R ^+ 2) => q r.
by move=> h1 h2 h3; clear -h1 h2 h3; lra.
Qed.

Lemma gnorm_cvg : cvg_prob P (fun d z => frobenius (lsubmx z) / d%:R)
  (Num.sqrt alpha).
Proof.
have h := cvg_prob_sqrt (gauss_sqnorm_cvg N alpha sample_density_cvg).
have h3 := @cvg_prob_gauss_lsubmx (fun d => d * d) N _ _ h.
apply: cvg_prob_eq h3; exists 1%N => d d1 z /=.
have dR : 0 < d%:R :> R by rewrite ltr0n.
by rewrite -expr_div_n sqrtr_sqr ger0_norm // divr_ge0 ?frobenius_ge0 ?ler0n.
Qed.

Lemma proj_cvg (zeta : R) : cvg_prob P
  (fun d z => frobenius (proj (kappa_cone_rV kappa d)
     (mxvec (shift_mx kappa zeta (goe_part (vec_mx (rsubmx z)))))) / d%:R)
  (Num.sqrt (chi zeta)).
Proof.
exact: (@cvg_prob_gauss_rsubmx (fun d => d * d) N _ _
  (shifted_cone_proj_cvg kappa zeta k1)).
Qed.

(* phihat_d = d^(-3/2) aux_value -> zeta_{alpha,kappa}. *)
Theorem aux_value_cvg : cvg_prob P
  (fun d z => aux_value kappa d (goe_part (vec_mx (rsubmx z)))
     (frobenius (lsubmx z)) / (d%:R * Num.sqrt d%:R))
  zs.
Proof.
have c1 := cone_shift_gtN1 _ k1.
have chiz : chi zs = alpha := universality_level_value alpha kappa a0 k1.
have chi0 (z : R) : 0 <= chi z := upper_value_ge0 threshold_law2 z c1.
have hG := gnorm_cvg.
have sa0 : 0 < Num.sqrt alpha by rewrite sqrtr_gt0.
apply/cvg_probP; split => t lt.
  (* t > zeta: then chi t > alpha, and |proj G(t)| <= |g| is unlikely *)
  have chit : alpha < chi t.
    rewrite -chiz; apply: (upper_value_incr threshold_law2 c1 lt).
    by rewrite chiz.
  have sa : Num.sqrt alpha < Num.sqrt (chi t).
    by rewrite ltr_sqrt // (lt_trans a0 chit).
  have s1 : Num.sqrt alpha < (Num.sqrt alpha + Num.sqrt (chi t)) / 2.
    by rewrite ltr_pdivlMr // mulrDr mulr1 ltrD2l.
  have s2 : (Num.sqrt alpha + Num.sqrt (chi t)) / 2 < Num.sqrt (chi t).
    by rewrite ltr_pdivrMr // mulrDr mulr1 ltrD2r.
  move: s1 s2; set s := (Num.sqrt alpha + Num.sqrt (chi t)) / 2 => s1 s2.
  have n1 := (cvg_probP.1 (proj_cvg t)).2 s s2.
  have n2 := (cvg_probP.1 hG).1 s s1.
  apply: negligibleW; first exact: (negligibleU n1 n2).
  exists 1%N => d d1 z /= h.
  have dR : 0 < d%:R :> R by rewrite ltr0n.
  have dd : 0 < d%:R * Num.sqrt d%:R :> R by rewrite mulr_gt0 // sqrtr_gt0.
  rewrite ler_pdivlMr // in h.
  have hp := (aux_value_ge_shift kappa t d (goe_part (vec_mx (rsubmx z)))
    (frobenius (lsubmx z)) k1 d1 (frobenius_ge0 _)).1 h.
  case: (leP (frobenius (proj (kappa_cone_rV kappa d)
    (mxvec (shift_mx kappa t (goe_part (vec_mx (rsubmx z)))))) / d%:R) s).
    by left.
  move=> hs; right; apply: le_trans (ltW hs) _.
  by rewrite ler_pM2r // invr_gt0.
(* t < zeta: at t' between them chi t' < alpha, and |g| < |proj G(t')| is
   unlikely *)
have t1 : t < (t + zs) / 2 by rewrite ltr_pdivlMr // mulrDr mulr1 ltrD2l.
have t2 : (t + zs) / 2 < zs by rewrite ltr_pdivrMr // mulrDr mulr1 ltrD2r.
move: t1 t2; set t' := (t + zs) / 2 => t1 t2.
have chit : chi t' < alpha.
  have [h0|h0] := eqVneq (chi t') 0; first by rewrite h0.
  rewrite -chiz; apply: (upper_value_incr threshold_law2 c1 t2).
  by rewrite lt_def h0 chi0.
have sa : Num.sqrt (chi t') < Num.sqrt alpha by rewrite ltr_sqrt.
have s1 : Num.sqrt (chi t') < (Num.sqrt (chi t') + Num.sqrt alpha) / 2.
  by rewrite ltr_pdivlMr // mulrDr mulr1 ltrD2l.
have s2 : (Num.sqrt (chi t') + Num.sqrt alpha) / 2 < Num.sqrt alpha.
  by rewrite ltr_pdivrMr // mulrDr mulr1 ltrD2r.
move: s1 s2; set s := (Num.sqrt (chi t') + Num.sqrt alpha) / 2 => s1 s2.
have n1 := (cvg_probP.1 (proj_cvg t')).1 s s1.
have n2 := (cvg_probP.1 hG).2 s s2.
apply: negligibleW; first exact: (negligibleU n1 n2).
exists 1%N => d d1 z /= h.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have dd : 0 < d%:R * Num.sqrt d%:R :> R by rewrite mulr_gt0 // sqrtr_gt0.
have hn' : ~ (t' * (d%:R * Num.sqrt d%:R) <= aux_value kappa d
    (goe_part (vec_mx (rsubmx z))) (frobenius (lsubmx z))).
  rewrite -ler_pdivlMr //; apply/negP; rewrite -ltNge.
  exact: le_lt_trans h t1.
have hp : ~ (frobenius (proj (kappa_cone_rV kappa d)
    (mxvec (shift_mx kappa t' (goe_part (vec_mx (rsubmx z)))))) <=
    frobenius (lsubmx z)).
  by move=> hq; apply: hn'; apply/(aux_value_ge_shift _ _ _ _ _ k1 d1
    (frobenius_ge0 _)).
move/negP: hp; rewrite -ltNge => hp.
case: (leP (frobenius (lsubmx z) / d%:R) s) => hs; first by right.
left; apply: le_trans (ltW hs) _.
by rewrite ler_pM2r ?invr_gt0 // ltW.
Qed.



(* The CGMT auxiliary value phi_d = d^(-3/2) cgmt_aux K_d (g, h) with
   K_d = tr_set (cone_slice kappa d) tends to (zeta_{alpha,kappa})_+. *)
Lemma cgmt_aux_cvg : cvg_prob P
  (fun d z => cgmt_aux (tr_set (cone_slice kappa d)) (lsubmx z) (rsubmx z) /
     (d%:R * Num.sqrt d%:R))
  (Num.max 0 zs).
Proof.
have L (a b : RR) : `|Num.max 0 a - Num.max 0 b| <= 1 * `|a - b|.
  rewrite mul1r.
  have [ha|ha] := leP a 0; have [hb|hb] := leP b 0.
  - by rewrite subrr normr0 normr_ge0.
  - rewrite sub0r normrN gtr0_norm // distrC.
    by apply: le_trans (ler_norm _); lra.
  - rewrite subr0 gtr0_norm //.
    by apply: le_trans (ler_norm _); lra.
  - by [].
have h := cvg_prob_lipschitz (fun x : RR => Num.max 0 x) 1 ltr01 L
  aux_value_cvg.
apply: (cvg_prob_eq _ h); exists 0%N => d _ z /=.
rewrite cgmt_aux_cone_slice maxr_pMl.
  by rewrite invr_ge0 mulr_ge0 ?sqrtr_ge0.
by rewrite mul0r.
Qed.

(* Its mean, at the same scale, tends to (zeta_{alpha,kappa})_+ as well. *)
Lemma cgmt_aux_mean_cvg (eta : R) : 0 < eta -> exists D : nat, forall d,
  (D <= d)%N ->
  `|(\int[P d]_z cgmt_aux (tr_set (cone_slice kappa d)) (lsubmx z) (rsubmx z))
     / (d%:R * Num.sqrt d%:R) - Num.max 0 zs| < eta.
Proof.
pose K d := tr_set (cone_slice kappa d).
have K0 d : K d !=set0 := tr_set_neq0 (cone_slice_neq0 kappa d).
have Kb d : forall x, K d x -> frobenius x <= cone_radius kappa * d%:R.
  exact: tr_set_bounded (fun x => cone_slice_bounded kappa d x (ltW k1)).
have r1 : 1 <= cone_radius kappa by rewrite le_max lexx.
pose c4 := 4 * cone_radius kappa ^+ 2.
have c0 : 0 < c4.
  by rewrite mulr_gt0 // exprn_gt0 // (lt_le_trans ltr01 r1).
pose X d (z : 'rV[RR]_((n d).-1 + d * d)) :=
  cgmt_aux (K d) (lsubmx z) (rsubmx z).
pose m d := \int[P d]_z X d z.
have hc : cvg_prob P (fun d z => (X d z - m d) / (d%:R * Num.sqrt d%:R)) 0.
  apply: (cvg_prob_concentration P X m c4 c0).
    move=> d.
    exact: (@measurable_cgmt_aux RR ((n d).-1) (d * d) (K d) _ (K0 d) (Kb d)).
  move=> d u u0.
  have h := @cgmt_aux_tail RR ((n d).-1) (d * d) (K d) _ (K0 d) (Kb d) u u0.
  by rewrite exprMn mulrA in h.
apply: (@cvg_prob_center _ _ P _ (fun d => m d / (d%:R * Num.sqrt d%:R)) _
  cgmt_aux_cvg).
apply: (cvg_prob_eq _ hc); exists 0%N => d _ z /=.
by rewrite mulrBl.
Qed.

(* Lemma 5.16: Phi_d = d^(-3/2) inf_(S in R_d) |A mxvec (T_kappa S)| tends to
   (zeta_{alpha,kappa})_+, for A an (n - 1) x d^2 standard Gaussian
   matrix. *)
Theorem escape_inf_cvg : cvg_prob (fun d => @gauss RR ((n d).-1 * (d * d)))
  (fun d a => escape_inf (tr_set (cone_slice kappa d))
     (vec_mx a : 'M[RR]_((n d).-1, d * d)) / (d%:R * Num.sqrt d%:R))
  (Num.max 0 zs).
Proof.
pose K d := tr_set (cone_slice kappa d).
have K0 d : K d !=set0 := tr_set_neq0 (cone_slice_neq0 kappa d).
have Kb d : forall x, K d x -> frobenius x <= cone_radius kappa * d%:R.
  exact: tr_set_bounded (fun x => cone_slice_bounded kappa d x (ltW k1)).
have r1 : 1 <= cone_radius kappa by rewrite le_max lexx.
have r0 : 0 < cone_radius kappa := lt_le_trans ltr01 r1.
pose c2 := 2 * cone_radius kappa ^+ 2.
have c0 : 0 < c2 by rewrite mulr_gt0 // exprn_gt0.
pose Q := fun d => @gauss RR ((n d).-1 * (d * d)).
pose X d (a : 'rV[RR]_((n d).-1 * (d * d))) :=
  escape_inf (K d) (vec_mx a : 'M[RR]_((n d).-1, d * d)).
pose M d := \int[Q d]_a X d a.
pose m d := \int[P d]_z cgmt_aux (K d) (lsubmx z) (rsubmx z).
(* Phi_d concentrates around its mean at the scale d *)
have hc : cvg_prob Q (fun d a => (X d a - M d) / (d%:R * Num.sqrt d%:R)) 0.
  apply: (cvg_prob_concentration Q X M c2 c0).
    move=> d.
    exact: (@measurable_escape_inf RR ((n d).-1) (d * d) (K d) _ (K0 d) (Kb d)).
  move=> d u u0.
  have h := @cgmt_escape_tail RR ((n d).-1) (d * d) (K d) _ (K0 d) (Kb d) u u0.
  by rewrite exprMn mulrA in h.
(* its mean is within rho = r d of that of phi_d, by the CGMT *)
have hM (eta : R) : 0 < eta -> exists D : nat, forall d, (D <= d)%N ->
    `|M d / (d%:R * Num.sqrt d%:R) - Num.max 0 zs| < eta.
  move=> e0.
  have e2 : 0 < eta / 2 by rewrite divr_gt0.
  have [D1 h1] := cgmt_aux_mean_cvg _ e2.
  have [D2 h2] := sample_density_cvg _ a0.
  exists (maxn (maxn D1 D2)
    (archimedean.Num.truncn ((2 * cone_radius kappa / eta) ^+ 2)).+1) => d.
  rewrite !geq_max => /andP[/andP[d1 d2] d3].
  have dR : 0 < d%:R :> R by rewrite ltr0n (leq_trans _ d3).
  have N0 : (0 < (n d).-1)%N.
    have := h2 d d2; rewrite ltr_norml => /andP[hl _].
    rewrite ltrBrDr addNr pmulr_lgt0 ?invr_gt0 ?exprn_gt0 // ltr0n in hl.
    exact: hl.
  have hl := @cgmt_lower RR ((n d).-1) (d * d) (K d) _ (K0 d) (Kb d) N0.
  have hu := @cgmt_upper RR ((n d).-1) (d * d) (K d) _ (K0 d) (Kb d)
    (closed_tr_set (cone_slice_closed kappa d k1))
    (convex_tr_set (fun x y t => cone_slice_convex kappa d x y t k1)).
  have hl' : m d - cone_radius kappa * d%:R <= M d := hl.
  have hu' : M d <= m d + cone_radius kappa * d%:R := hu.
  set s := d%:R * Num.sqrt d%:R.
  have s0 : 0 < s by rewrite mulr_gt0 // sqrtr_gt0.
  have hMm : `|M d - m d| <= cone_radius kappa * d%:R.
    by rewrite ler_norml; apply/andP; split; lra.
  have hsd : 2 * cone_radius kappa / eta < Num.sqrt d%:R.
    rewrite -ltr_sqr ?nnegrE ?sqrtr_ge0 ?divr_ge0 ?mulr_ge0 ?ltW //.
    rewrite sqr_sqrtr ?ler0n //.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  have hrs : cone_radius kappa * d%:R / s < eta / 2.
    have -> : cone_radius kappa * d%:R / s = cone_radius kappa / Num.sqrt d%:R.
      by rewrite /s invfM mulrA mulfK ?gt_eqF.
    rewrite ltr_pdivrMr ?sqrtr_gt0 //.
    rewrite ltr_pdivrMr // in hsd.
    lra.
  have hMs : `|M d / s - m d / s| <= cone_radius kappa * d%:R / s.
    by rewrite -mulrBl normrM normfV (gtr0_norm s0) ler_pM2r ?invr_gt0.
  have hm : `|m d / s - Num.max 0 zs| < eta / 2 := h1 d d1.
  have t := ler_distD (m d / s) (M d / s) (Num.max 0 zs).
  apply: le_lt_trans t _.
  rewrite [eta]splitr; apply: ltrD => //.
  exact: le_lt_trans hMs hrs.
have h := cvg_probD hc (cvg_prob_seq Q (fun d => M d / (d%:R * Num.sqrt d%:R))
  (Num.max 0 zs) hM).
rewrite add0r in h.
apply: (cvg_prob_eq _ h); exists 0%N => d _ a /=.
by rewrite -mulrDl subrK.
Qed.

Lemma density_cvg (eps : R) : 0 < eps -> exists D : nat, forall d,
  (D <= d)%N -> `|(n d)%:R / d%:R ^+ 2 - alpha| < eps.
Proof.
move=> e0; have [D h] := hn _ e0; exists D => d dD.
by have := h d dD; rewrite /paper_main_density RdivE.
Qed.

(* Proposition 1.4 (ii): the optimal squared fitting error of n(d) Gaussian
   features, Gamma_{G,kappa} = 2 unsat_value, tends to e*(alpha, kappa) in
   probability. *)
Theorem gaussian_fitting_error_cvg : cvg_prob
  (fun d => tuple_prod (fun=> gaussian_feature_law kappa d) (n d))
  (fun d Z => 2 * unsat_value (n d) d Z) (universality_e_star alpha kappa).
Proof.
pose X2 d (b : 'rV[RR]_((n d).-1 * (d * d))) := 2%:R / ((n d)%:R * d%:R) *
  escape_inf (tr_set (cone_slice kappa d))
    (vec_mx b : 'M[RR]_((n d).-1, d * d)) ^+ 2.
(* the law of 2 unsat_value is that of X2 (Lemma 5.4 in law) *)
have law N d : (0 < N)%N -> (0 < d)%N -> forall B : set RR, measurable B ->
    tuple_prod (fun=> gaussian_feature_law kappa d) N
      [set Z | B (2 * unsat_value N d Z)] =
    gauss (N.-1 * (d * d)) [set b | B (2%:R / (N%:R * d%:R) *
      escape_inf (tr_set (cone_slice kappa d))
        (vec_mx b : 'M[RR]_(N.-1, d * d)) ^+ 2)].
  by case: N => [//|k] _ d0 B mB; exact: unsat_value_gaussian_law.
apply: (cvg_prob_law _ (fun d => @gauss RR ((n d).-1 * (d * d))) _ X2).
- move=> d; apply: measurable_funM; first exact: measurable_cst.
  exact: measurable_unsat_value.
- move=> d; apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_funX.
  exact: (@measurable_escape_inf RR _ (d * d) _ _
    (tr_set_neq0 (cone_slice_neq0 kappa d))
    (tr_set_bounded (fun x => cone_slice_bounded kappa d x (ltW k1)))).
- have [D hD] := density_cvg _ a0.
  exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1] B mB.
  have n0 : (0 < n d)%N.
    have := hD d dD; rewrite ltr_norml => /andP[hl _].
    by rewrite ltrBrDr addNr pmulr_lgt0 ?invr_gt0 ?exprn_gt0 ?ltr0n // in hl.
  exact: (law (n d) d n0 d1 B mB).
(* X2 = 2 (n / d^2)^-1 Phi_d^2 -> (2 / alpha) (zeta_{alpha,kappa})_+^2 *)
have hP := escape_inf_cvg.
have h2 := cvg_probM hP hP.
have hd : cvg_prob (fun d => @gauss RR ((n d).-1 * (d * d)))
    (fun d _ => ((n d)%:R / d%:R ^+ 2)^-1) alpha^-1.
  apply: cvg_probV; first by rewrite gt_eqF.
  exact: (cvg_prob_seq _ (fun d => (n d)%:R / d%:R ^+ 2) alpha density_cvg).
have h3 := cvg_probM (cvg_prob_cst _ 2) (cvg_probM hd h2).
have -> : universality_e_star alpha kappa =
    2 * (alpha^-1 * (Num.max 0 zs * Num.max 0 zs)).
  by rewrite universality_e_starE maxC expr2 mulrA.
have [D hD] := density_cvg _ a0.
apply: (cvg_prob_eq _ h3); exists (maxn D 1) => d.
rewrite geq_max => /andP[dD d1] a /=.
have n0 : (0 < n d)%N.
  have := hD d dD; rewrite ltr_norml => /andP[hl _].
  by rewrite ltrBrDr addNr pmulr_lgt0 ?invr_gt0 ?exprn_gt0 ?ltr0n // in hl.
have nR : (n d)%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
rewrite /X2; move: (escape_inf _ _) => E.
have q0 : Num.sqrt d%:R != 0 :> R.
  by apply: lt0r_neq0; rewrite sqrtr_gt0 ltr0n.
have dq : d%:R = Num.sqrt d%:R ^+ 2 :> R by rewrite sqr_sqrtr ?ler0n.
move: q0 dq; move: (Num.sqrt d%:R) => q q0 dq.
rewrite dq.
by field.
Qed.

(* Proposition 1.4 (ii), last part: above the threshold, e* > 0 and the
   fitting error of the Gaussian features is at least e* / 2 with
   probability tending to one. *)
Corollary gaussian_fitting_error_gap : universality_alpha_star kappa < alpha ->
  0 < universality_e_star alpha kappa /\
  negligible (fun d => tuple_prod (fun=> gaussian_feature_law kappa d) (n d))
    (fun d => [set Z | 2 * unsat_value (n d) d Z <=
                       universality_e_star alpha kappa / 2]).
Proof.
move=> ha.
have e0 : 0 < universality_e_star alpha kappa.
  by rewrite universality_e_star_gt0.
split => //.
have e2 : 0 < universality_e_star alpha kappa / 2 by rewrite divr_gt0.
apply: negligibleW; first exact: (gaussian_fitting_error_cvg _ e2).
exists 0%N => d _ Z /= h.
by rewrite distrC; apply: le_trans (ler_norm _); lra.
Qed.

End fitting_error_limit.

(* Proposition 1.4 (ii) in the form that Unsat/Universality takes as its
   hypothesis: for every eps > 0 and every large d, the event
   |2 unsat_value - e*| > eps lies in a measurable event of probability at
   most eps. *)
Theorem gaussian_fitting_error_limit (alpha kappa : R) :
  0 < alpha -> 1 < kappa ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
    [set Z | eps < `|2 * unsat_value (n d) d Z -
       universality_e_star alpha kappa|] `<=` E].
Proof.
move=> a0 k1 n hn eps e0.
have [D hD] := gaussian_fitting_error_cvg alpha kappa n a0 k1 hn eps e0 eps e0.
exists D => d dD; have [A [mA PA EA]] := hD d dD.
by exists A; split => // Z /= hZ; apply: EA; exact: ltW.
Qed.
