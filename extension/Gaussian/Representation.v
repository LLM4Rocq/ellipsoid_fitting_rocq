(* The Gaussian feature model as an i.i.d. Gaussian matrix acting on the cone
   S^d_kappa: Lemmas 5.4 to 5.6 of Koehler and Sohn (arXiv 2608.27372,
   lines 4992-5076 of arxiv_v1.tex), at Stdlib's R. Item G4 of stage 2 of
   phase 5 (lane C).

   Notation: R_d = psd_trace_slice d = {S >= 0, Tr S = d}, T_kappa =
   cone_map kappa, S^d_kappa = kappa_cone kappa d (Gaussian/Cones).

   Proved here.
   - unsat_value_closed: the least squares value of the statement over the
     closed slice, 2 unsat_value n d Z = (1/n) inf_{S in R_d}
     |P_{1^perp} (<Z_i, mxvec S>)_i|^2, the projection being written
     centered_sq (the sum of the squared deviations from the mean); the
     infimum over the open slice of the statement equals the one over the
     closed slice, by the segment from S to the identity.
   - gaussian_feature_vec_dot, the identity behind Lemma 5.4: for S
     symmetric, <Z(a), mxvec S> = <a, mxvec (sqrt (2/d) T_kappa S)> for the
     Gaussian feature Z(a) of a in 'rV_(d * d). So the vector
     (<Z_i, mxvec S>)_i is sqrt (2/d) M mxvec (T_kappa S) exactly, M being
     the n x (d * d) matrix of rows a_i; no identification of S^d with
     R^(d (d + 1)/2) is needed.
   - aux_value_ge, Lemma 5.6 in crossing form: for 0 <= g, with
     aux_value kappa d G g = inf_{S in R_d} (g |T_kappa S|_F -
     <G, T_kappa S>) (the paper's phihat_d is d^(-3/2) times this value at
     g = |g|), c <= aux_value kappa d G g if and only if the projection of
     G + (c / d) sqrt (2 / (kappa - 1)) I on S^d_kappa (in the mxvec
     coordinates, kappa_cone_rV) has Frobenius norm at most g. The steps
     are those of the paper: positive homogeneity, Tr S =
     sqrt (2 / (kappa - 1)) <I, T_kappa S> (trace_cone_map), and the
     support function of the projection on a closed convex cone
     (cone_proj_le, from cone_proj_support of library/convex/moreau.v).
     The infimum is finite because |<G, T_kappa S>| <= |T_kappa G|_F
     |S|_F and |S|_F <= Tr S for S >= 0 (frobenius_le_trace).

   Lemma 5.4 in law and the set K = {mxvec (T_kappa S) | S in R_d} of
   Lemma 5.5, with its mean and concentration form for the CGMT of
   library/comparison/cgmt.v, are in Gaussian/FittingError, which also
   proves Lemma 5.16 and Proposition 1.4 (ii). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import measure lebesgue_measure probability.
From GaussianAnalysis Require Import euclidean real_spectral opnorm.
From GaussianAnalysis Require Import least_squares logdet_barrier moreau psd_part.
From GaussianAnalysis Require Import measurable_matrix.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd.
From EllipsoidUniversality.Gaussian Require Import Cones.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Unsat Require Import LeastSquares.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* The closed slice R_d = {S >= 0, tr S = d}. *)
Definition psd_trace_slice d : set 'M[R]_d :=
  [set S | paper_main_psd S /\ paper_main_trace S = d%:R].

(* |P_{1^perp} v|^2 = sum_i (v_i - mean v)^2. *)
Definition centered_sq n (v : 'rV[R]_n) : R :=
  \sum_(i < n) (v 0 i - (\sum_(j < n) v 0 j) / n%:R) ^+ 2.

(* The row (<Z_i, mxvec S>)_i of the features at S. *)
Definition feature_row n d (Z : n.-tuple 'rV[R]_(d * d)) (S : 'M[R]_d) : 'rV[R]_n :=
  \row_i mxdot (tnth Z i) (mxvec S).

Arguments centered_sq {n} v.
Arguments feature_row {n d} Z S.

Lemma psd_trace_slice1 d : psd_trace_slice d 1%:M.
Proof.
split; last exact: trace1.
apply: posdef_paper_psd; split; first by apply/symmetricmxP; rewrite trmx1.
by move=> x x0; rewrite mulmx1 mxdot_gt0.
Qed.

Section least_squares_value.

Lemma centered_sq_le n (v : 'rV[R]_n) (b : R) : (0 < n)%N ->
  centered_sq v <= \sum_(i < n) (b - v 0 i) ^+ 2.
Proof.
move=> n0; rewrite /centered_sq; set m := (\sum_(j < n) v 0 j) / n%:R.
have nne : n%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
have sm : \sum_(i < n) (m - v 0 i) = 0.
  rewrite sumrB sumr_const card_ord -mulr_natl /m mulrC mulfVK //.
  by rewrite subrr.
(* sum_i (b - v_i)^2 = n (b - m)^2 + sum_i (v_i - m)^2 *)
have e : \sum_(i < n) (b - v 0 i) ^+ 2 =
    n%:R * (b - m) ^+ 2 + \sum_(i < n) (v 0 i - m) ^+ 2.
  have -> : \sum_(i < n) (b - v 0 i) ^+ 2 = \sum_(i < n)
      ((b - m) ^+ 2 + 2 * (b - m) * (m - v 0 i) + (v 0 i - m) ^+ 2).
    by apply: eq_bigr => i _; ring.
  rewrite !big_split /=.
  rewrite -[\sum_(i < n) 2 * (b - m) * (m - v 0 i)]mulr_sumr sm mulr0 addr0.
  by rewrite sumr_const card_ord mulr_natl.
by rewrite e lerDr mulr_ge0 // ?ler0n ?sqr_ge0.
Qed.

Lemma centered_sqE n (v : 'rV[R]_n) : (0 < n)%N ->
  centered_sq v = \sum_(i < n) ((\sum_(j < n) v 0 j) / n%:R - v 0 i) ^+ 2.
Proof.
by move=> n0; apply: eq_bigr => i _; rewrite -sqrrN opprB.
Qed.

(* eq:unregularized-affine-energy-value for features: 2 Phi_Z(R_d^o) is
   (1/n) inf_{S in R_d} |P_{1^perp} (<Z_i, S>)_i|^2, over the closed slice. *)
Theorem unsat_value_closed n d (Z : n.-tuple 'rV[R]_(d * d)) :
  (0 < n)%N -> (0 < d)%N ->
  2 * unsat_value n d Z =
  n%:R^-1 * inf [set centered_sq (feature_row Z S) | S in psd_trace_slice d].
Proof.
move=> n0 d0.
have nR : 0 < n%:R :> R by rewrite ltr0n.
have nne : n%:R != 0 :> R by rewrite gt_eqF.
have nn2 : 0 < n%:R *+ 2 :> R by rewrite mulrn_wgt0.
pose F (S : 'M[R]_d) := centered_sq (feature_row Z S).
have F0 S : 0 <= F S by apply: sumr_ge0 => i _; exact: sqr_ge0.
set V := inf _.
have hV : has_lbound [set F S | S in psd_trace_slice d].
  by exists 0 => _ [S _ <-]; exact: F0.
have I1 := psd_trace_slice1 d.
(* the objective without regularization *)
pose O (th : 'rV[R]_(d * d)) (b : R) := ls_objective Z 0 0 th b.
have OE th b : O th b =
    (n%:R *+ 2)^-1 * \sum_(i < n) (b - mxdot (tnth Z i) th) ^+ 2.
  by rewrite /O /ls_objective !mul0r addr0.
have hU : has_lbound [set O th b | th in unsat_domain d & b in [set: R]].
  exists 0 => _ [th _ [b _ <-]]; rewrite OE.
  apply: mulr_ge0; first by rewrite invr_ge0 ltW.
  by apply: sumr_ge0 => i _; exact: sqr_ge0.
have D1 : unsat_domain d (mxvec 1%:M).
  rewrite /unsat_domain /pd_slice /= mxvecK mxtrace1; split => //.
  split; first by apply/symmetricmxP; rewrite trmx1.
  by move=> x x0; rewrite mulmx1 mxdot_gt0.
have U0 : [set O th b | th in unsat_domain d & b in [set: R]] !=set0.
  by exists (O (mxvec 1%:M) 0); exists (mxvec 1%:M) => //; exists 0.
have FS th : unsat_domain d th -> psd_trace_slice d (vec_mx th).
  by move=> [Pd tr]; split; [exact: posdef_paper_psd | exact: tr].
have frE th : feature_row Z (vec_mx th) = \row_i mxdot (tnth Z i) th.
  by apply/rowP => i; rewrite !mxE vec_mxK.
have UE : unsat_value n d Z =
    inf [set O th b | th in unsat_domain d & b in [set: R]] by [].
(* V <= 2 n Phi: the best b is the mean *)
have ge : V <= n%:R *+ 2 * unsat_value n d Z.
  rewrite mulrC -ler_pdivrMr // UE; apply: lb_le_inf U0 _.
  move=> _ [th Dth [b _ <-]].
  rewrite OE ler_pdivrMr // mulrC mulrA mulfV ?mul1r ?gt_eqF //.
  have h1 : V <= F (vec_mx th).
    by apply: (ge_inf hV); exists (vec_mx th) => //; exact: FS.
  apply: le_trans h1 _.
  have := centered_sq_le _ (feature_row Z (vec_mx th)) b n0.
  by rewrite /F frE; under eq_bigr do rewrite mxE.
(* 2 n Phi <= F S for S in the closed slice: S_t = (1 - t) S + t I *)
pose mu (v : 'rV[R]_n) := (\sum_(j < n) v 0 j) / n%:R.
have cq (u w : 'rV[R]_n) (t : R) : centered_sq (u + t *: w) =
    centered_sq u + t * (2 * \sum_(i < n) (u 0 i - mu u) * (w 0 i - mu w)) +
    t ^+ 2 * centered_sq w.
  have mE : mu (u + t *: w) = mu u + t * mu w.
    rewrite /mu (eq_bigr (fun j => u 0 j + t * w 0 j)).
      by move=> j _; rewrite !mxE.
    by rewrite big_split /= -mulr_sumr mulrDl mulrA.
  rewrite /centered_sq -/(mu (u + t *: w)) -/(mu u) -/(mu w) mE.
  rewrite (eq_bigr (fun i => (u 0 i - mu u) ^+ 2 +
      t * (2 * ((u 0 i - mu u) * (w 0 i - mu w))) +
      t ^+ 2 * (w 0 i - mu w) ^+ 2)).
    by move=> i _; rewrite !mxE; ring.
  by rewrite !big_split /= -!mulr_sumr.
have le_all S : psd_trace_slice d S -> n%:R *+ 2 * unsat_value n d Z <= F S.
  move=> [Sp Str].
  pose u := feature_row Z S; pose w := feature_row Z 1%:M - u.
  apply: (le_quad_lim _ _ (2 * \sum_(i < n) (u 0 i - mu u) * (w 0 i - mu w))
    (centered_sq w)) => t /andP[t0 t1].
  pose St := (1 - t) *: S + t *: 1%:M.
  have Dt : unsat_domain d (mxvec St).
    rewrite /unsat_domain /pd_slice /= mxvecK; split.
      by apply: psd_shift_posdef => //; rewrite t0 t1.
    rewrite linearD !linearZ /= mxtrace1.
    have -> : \tr S = d%:R by rewrite -Str.
    by rewrite -mulrDl subrK mul1r.
  have frSt : feature_row Z St = u + t *: w.
    apply/rowP => i; rewrite !mxE /St linearD !linearZ /= mxdotDr !mxdotZr.
    by ring.
  have hO : unsat_value n d Z <= O (mxvec St) (mu (feature_row Z St)).
    rewrite UE; apply: (ge_inf hU); exists (mxvec St) => //.
    by exists (mu (feature_row Z St)).
  rewrite OE in hO.
  have e : \sum_(i < n) (mu (feature_row Z St) -
      mxdot (tnth Z i) (mxvec St)) ^+ 2 = centered_sq (feature_row Z St).
    by rewrite (centered_sqE _ _ n0); apply: eq_bigr => i _; rewrite mxE.
  rewrite e frSt cq in hO.
  apply: le_trans (ler_wpM2l (ltW nn2) hO) _.
  by rewrite mulVKf ?gt_eqF.
have le : n%:R *+ 2 * unsat_value n d Z <= V.
  apply: lb_le_inf => [|_ [S HS <-]]; last exact: le_all.
  by exists (F 1%:M); exists 1%:M.
have eq2 : n%:R *+ 2 * unsat_value n d Z = V by apply/le_anti; rewrite le ge.
by rewrite -eq2 mulr2n; field.
Qed.

End least_squares_value.

Section gaussian_features.

(* <G(a), S> = <a, sqrt (2/d) T_kappa S> for the Gaussian feature of a and S
   symmetric: the identity behind Lemma 5.4. *)
Lemma gaussian_feature_vec_dot (kappa : R) d (a : 'rV[RR]_(d * d)) (S : 'M[R]_d) :
  paper_main_symmetric S ->
  mxdot (gaussian_feature_vec kappa d a) (mxvec S) =
  mxdot a (mxvec (Num.sqrt (2%:R / d%:R) *: cone_map kappa S)).
Proof.
move=> Ss.
rewrite /gaussian_feature_vec gaussian_feature_mxE mxdot_mxvec.
have -> : mxdot (gaussian_feature kappa (vec_mx a)) S =
    paper_main_pairing (gaussian_feature kappa (vec_mx a)) S by [].
rewrite gaussian_feature_pairing //.
by rewrite -[a in RHS]vec_mxK mxdot_mxvec.
Qed.

End gaussian_features.

Section crossing.

(* The trace bounds the Frobenius norm of a positive semidefinite matrix. *)
Lemma frobenius_le_trace d (S : 'M[R]_d) :
  paper_main_psd S -> frobenius S <= paper_main_trace S.
Proof.
move=> [Ss Sp].
have Ssym : S \is symmetricmx by apply/symmetricmxP; exact/paper_main_symmetricP.
have [P Po [dv SE]] := symmetric_spectral Ssym.
have form x : mxdot x (S *m x) = paper_main_quadratic_form S x.
  by rewrite quadratic_form_mxdot [RHS]mxdotC mxdot_outer mxdot_colE mulmxA.
have d0 i : 0 <= dv 0 i by apply: (spectral_psd Po SE).1 => x; rewrite form.
have -> : paper_main_trace S = \sum_i dv 0 i by rewrite -(spectral_trace Po SE).
rewrite /frobenius (spectral_mxdot Po SE).
have s0 : 0 <= \sum_i dv 0 i by apply: sumr_ge0 => i _.
rewrite -(ger0_norm s0) -sqrtr_sqr; apply: ler_wsqrtr.
rewrite expr2 mulr_suml; apply: ler_sum => i _.
rewrite mulr_sumr (bigD1 i) //= expr2 lerDl.
by apply: sumr_ge0 => j _; exact: mulr_ge0.
Qed.

Lemma psdZ d (a : R) (S : 'M[R]_d) :
  0 <= a -> paper_main_psd S -> paper_main_psd (a *: S).
Proof.
move=> a0 [Ss Sp]; split; first by move=> i j; rewrite !mxE Ss.
move=> v; have := mulr_ge0 a0 (Sp v).
rewrite /paper_main_quadratic_form mulr_sumr; congr (_ <= _).
apply: eq_bigr => i _; rewrite mulr_sumr; apply: eq_bigr => j _.
by rewrite mxE; ring.
Qed.

(* The cone S^d_kappa in the mxvec coordinates. *)
Definition kappa_cone_rV (kappa : R) d : set 'rV[RR]_(d * d) :=
  [set v | kappa_cone kappa d (vec_mx v)].

Lemma kappa_cone_rV_closed (kappa : R) d : 1 < kappa -> closed (kappa_cone_rV kappa d).
Proof.
move=> k1.
have cv : continuous (@vec_mx RR d d).
  apply: continuous_mxP => i j; rewrite /vec_mx.
  under eq_fun do rewrite mxE.
  exact: matrix_normedtype.coord_continuous.
have := (continuous_closedP (@vec_mx RR d d)).1 cv; apply.
exact: kappa_cone_closed.
Qed.

(* The norm of the projection on a closed convex cone, by its support
   function (cone_proj_support). *)
Lemma cone_proj_le N (C : set 'rV[RR]_N) (z : 'rV[RR]_N) (g : R) :
  closed C -> C 0 ->
  (forall x y (t : R), C x -> C y -> 0 <= t <= 1 -> C (x + t *: (y - x))) ->
  (forall y (a : R), C y -> 0 <= a -> C (a *: y)) -> 0 <= g ->
  frobenius (proj C z) <= g <-> forall y, C y -> mxdot z y <= g * frobenius y.
Proof.
move=> Cc C0 Ccvx Ccone g0.
rewrite -(cone_proj_support Cc C0 Ccvx Ccone z).
set S := [set _ | _ in _].
have Sn : S !=set0.
  by exists (mxdot z 0), 0 => //; split => //; rewrite mxdot0l.
have Su : has_ubound S.
  exists (frobenius z) => _ [y [Cy y1] <-].
  apply: le_trans (ler_mxdot z y) _.
  have fy : frobenius y <= 1 by rewrite /frobenius -sqrtr1 ler_sqrt.
  by rewrite -[X in _ <= X]mulr1 ler_wpM2l // frobenius_ge0.
split => [Hs y Cy|H]; last first.
  apply: ge_sup => // _ [y [Cy y1] <-].
  apply: le_trans (H y Cy) _.
  have fy : frobenius y <= 1 by rewrite /frobenius -sqrtr1 ler_sqrt.
  by rewrite -[X in _ <= X]mulr1 ler_wpM2l.
have [->|y0] := eqVneq y 0; first by rewrite mxdot0r frobenius0 mulr0.
have fp : 0 < frobenius y by rewrite frobenius_gt0.
(* y / |y| is in C and in the unit ball *)
have Sy : S ((frobenius y)^-1 * mxdot z y).
  exists ((frobenius y)^-1 *: y); last by rewrite mxdotZr.
  split; first by apply: Ccone Cy _; rewrite invr_ge0 ltW.
  rewrite mxdotZl mxdotZr -frobenius_sqr mulrA -expr2 -exprMn mulVf ?gt_eqF //.
  by rewrite expr1n.
have := le_trans (ub_le_sup Su Sy) Hs.
by rewrite ler_pdivrMl // mulrC.
Qed.

(* Tr S = sqrt (2 / (kappa - 1)) <I, T_kappa S>. *)
Lemma trace_cone_map (kappa : R) d (S : 'M[R]_d) : 1 < kappa ->
  paper_main_trace S =
  Num.sqrt (2%:R / (kappa - 1)) * paper_main_pairing 1%:M (cone_map kappa S).
Proof.
move=> k1.
have -> : paper_main_pairing 1%:M (cone_map kappa S) =
    Num.sqrt ((kappa - 1) / 2%:R) * paper_main_trace S.
  rewrite /paper_main_pairing /paper_main_trace mulr_sumr.
  apply: eq_bigr => i _.
  rewrite (bigD1 i) //= big1 ?addr0.
    by move=> j ji; rewrite mxE eq_sym (negPf ji) mul0r.
  by rewrite mxE eqxx mul1r cone_mapE eqxx.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
rewrite mulrA -sqrtrM; first by rewrite divr_ge0 // ltW.
have -> : 2%:R / (kappa - 1) * ((kappa - 1) / 2%:R) = 1 :> R.
  by rewrite mulrC mulrA divfK ?gt_eqF // mulfV // gt_eqF.
by rewrite sqrtr1 mul1r.
Qed.

(* phihat without its normalization: inf over R_d of g |T S| - <G, T S>. *)
Definition aux_value (kappa : R) d (G : 'M[R]_d) (g : R) : R :=
  inf [set g * frobenius (cone_map kappa S) -
           paper_main_pairing G (cone_map kappa S) | S in psd_trace_slice d].

(* Lemma 5.6: c <= aux_value iff the projection of the shifted G on the cone
   has norm at most g. *)
Theorem aux_value_ge (kappa : R) d (G : 'M[R]_d) (g c : R) :
  1 < kappa -> (0 < d)%N -> 0 <= g ->
  c <= aux_value kappa d G g <->
  frobenius (proj (kappa_cone_rV kappa d)
    (mxvec (G + (c / d%:R * Num.sqrt (2%:R / (kappa - 1))) *: 1%:M))) <= g.
Proof.
move=> k1 d0 g0.
set s := Num.sqrt (2%:R / (kappa - 1)).
set Z := G + (c / d%:R * s) *: 1%:M.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have [I1p I1t] := psd_trace_slice1 d.
(* mxvec S^d_kappa is a closed convex cone *)
have C0 : kappa_cone_rV kappa d 0.
  rewrite /kappa_cone_rV /= linear0 -(scale0r (cone_map kappa 1%:M)).
  by apply: kappa_coneZ => //; exists 1%:M.
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
(* <Z, T S> <= g |T S| iff (c/d) Tr S <= g |T S| - <G, T S> *)
pose F (S : 'M[R]_d) := g * frobenius (cone_map kappa S) -
  paper_main_pairing G (cone_map kappa S).
have key (S : 'M[R]_d) :
    (mxdot (mxvec Z) (mxvec (cone_map kappa S)) <=
       g * frobenius (mxvec (cone_map kappa S))) <->
    (c / d%:R * paper_main_trace S <= F S).
  rewrite /frobenius !mxdot_mxvec /Z mxdotDl mxdotZl.
  rewrite (trace_cone_map _ _ _ k1) /F lerBrDl.
  have -> : mxdot G (cone_map kappa S) =
    paper_main_pairing G (cone_map kappa S) by [].
  have -> : mxdot 1%:M (cone_map kappa S) =
    paper_main_pairing 1%:M (cone_map kappa S) by [].
  by rewrite mulrA.
have -> : (forall y : 'rV[RR]_(d * d), kappa_cone_rV kappa d y ->
    mxdot (mxvec Z) y <= g * frobenius y) <->
    (forall S, paper_main_psd S -> c / d%:R * paper_main_trace S <= F S).
  split => [H S Sp|H y [S Sp TSy]].
    by apply/key; apply: H; rewrite /kappa_cone_rV /= mxvecK; exists S.
  by rewrite -[y]vec_mxK -TSy; apply/key; exact: H.
(* positive homogeneity *)
have FZ (t : R) S : 0 <= t -> F (t *: S) = t * F S.
  move=> t0; rewrite /F cone_mapZ frobeniusZ ger0_norm //.
  have -> : paper_main_pairing G (t *: cone_map kappa S) =
      t * paper_main_pairing G (cone_map kappa S).
    change (mxdot G (t *: cone_map kappa S) = t * mxdot G (cone_map kappa S)).
    by rewrite mxdotZr.
  by rewrite mulrBr mulrCA.
have trZ (t : R) (S : 'M[R]_d) :
    paper_main_trace (t *: S) = t * paper_main_trace S.
  by rewrite /paper_main_trace mulr_sumr; apply: eq_bigr => i _; rewrite mxE.
(* F is bounded below on R_d *)
have Flb S : psd_trace_slice d S ->
    - (frobenius (cone_map kappa G) * d%:R) <= F S.
  move=> [Sp St]; rewrite /F.
  have -> : paper_main_pairing G (cone_map kappa S) =
    mxdot (cone_map kappa G) S by rewrite -cone_map_pairing.
  have h1 : mxdot (cone_map kappa G) S <= frobenius (cone_map kappa G) * d%:R.
    apply: le_trans (ler_mxdot _ _) _.
    by rewrite -St ler_wpM2l ?frobenius_ge0 // frobenius_le_trace.
  have h2 : 0 <= g * frobenius (cone_map kappa S).
    by rewrite mulr_ge0 ?frobenius_ge0.
  lra.
have -> : aux_value kappa d G g = inf [set F S | S in psd_trace_slice d] by [].
set E := [set F S | S in psd_trace_slice d].
have En : E !=set0 by exists (F 1%:M), 1%:M.
have Elb : has_lbound E.
  by exists (- (frobenius (cone_map kappa G) * d%:R)) => _ [S HS <-]; exact: Flb.
split => [cE S Sp|H]; last first.
  apply: lb_le_inf En _ => _ [S [Sp St] <-].
  by have := H S Sp; rewrite St mulfVK ?gt_eqF.
have [S0|Sn0] := eqVneq S 0.
  have F0 : F 0 = 0 by have := FZ 0 0 (lexx 0); rewrite scale0r mul0r.
  have tr0 : paper_main_trace (0 : 'M[R]_d) = 0.
    by have := trZ 0 0; rewrite scale0r mul0r.
  by rewrite S0 F0 tr0 mulr0.
(* rescale S to trace d *)
have tS : 0 < paper_main_trace S.
  have h := frobenius_le_trace _ _ Sp.
  have h2 : 0 < frobenius S by rewrite frobenius_gt0.
  exact: lt_le_trans h2 h.
pose t := d%:R / paper_main_trace S.
have t0 : 0 < t by rewrite divr_gt0.
have hS : psd_trace_slice d (t *: S).
  split; first exact: psdZ (ltW t0) Sp.
  by rewrite trZ /t divfK ?gt_eqF.
have := le_trans cE (ge_inf Elb (ex_intro2 _ _ (t *: S) hS erefl)).
rewrite FZ ?(ltW t0) // /t => h.
have e : c / d%:R * paper_main_trace S = (d%:R / paper_main_trace S)^-1 * c.
  by rewrite invf_div [RHS]mulrC mulrA mulrAC.
by rewrite e ler_pdivrMl.
Qed.

End crossing.
