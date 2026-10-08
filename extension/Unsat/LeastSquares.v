(* The least squares problem of the unsatisfiable phase of Koehler and Sohn,
   "Universality and sharp thresholds for ellipsoid fitting" (arXiv
   2608.27372, section 2.2, lines 1004-1086), at Stdlib's R: the quadratic
   features of a sample, their covariance Sigma_kappa, the domain
   R_d^o = {R > 0, Tr R = d}, and the values Phi_Z(R_d^o; beta) and
   Phi_Z(R_d^o) of the library's least squares problem
   (convex/least_squares.v) for a tuple Z of features.

   Matrices are row vectors of size d * d through mxvec, so that the
   Frobenius product <A, B> is mxdot (mxvec A) (mxvec B). The feature of a
   point x is W(x) = (x x^T - I) / sqrt d; the features of a sample are
   W(x_1), ..., W(x_n). Their covariance is
   C_kappa(A, B) = (1/d) (2 <A, B> + (kappa - 3) <diag A, diag B>) on
   symmetric matrices (paper, lines 268-280); on all matrices it is
   C_kappa of the symmetric parts, and unsat_cov is its matrix in the mxvec
   coordinates. The ridge regularization uses
   lambda = opnorm (unsat_cov kappa d), the operator norm of Sigma_kappa.

   Proved:
   - unsat_fitting_error: for d >= 1 and every sample x of n points of
     R^d, universality_fitting_error n d x = 2 * unsat_value (unsat_features
     x) (eq:unregularized-affine-energy-value, lines 1054-1058). The
     constraint r >= 0 of Gamma_X is inactive because x_i^T S x_i >= 0, and
     the infimum over S >= 0 of trace d is the infimum over S > 0 of trace
     d: (1 - t) S + t I is positive definite for 0 < t <= 1, and the
     objective at it is a polynomial in t (le_quad_lim).
   - unsat_feature_dot: <W(x), theta> = (x^T S x - tr S) / sqrt d for
     S = vec_mx theta; the quadratic form and the trace of the paper as
     Frobenius products (quadratic_form_mxdot, trace_mxdot).
   R_d^o is convex and relatively open, and -ln det is a d-self-concordant
   barrier on it, nonnegative and zero at the identity: convex/logdet_barrier.v
   (rel_open_convex_pd_slice, logdet_sc_barrier, logdet_barrier_ge0,
   logdet_barrier_one). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis Require Import euclidean opnorm real_spectral.
From GaussianAnalysis Require Import least_squares.
From GaussianAnalysis Require Import logdet_barrier.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.

Local Open Scope ring_scope.

(* The quadratic feature W(x) = (x x^T - I) / sqrt d of a point x of R^d,
   as a row vector of size d * d. *)
Definition unsat_feature d (x : 'cV[R]_d) : 'rV[R]_(d * d) :=
  mxvec ((Num.sqrt d%:R)^-1 *: (x *m x^T - 1%:M)).

(* The features W(x_1), ..., W(x_n) of a sample. *)
Definition unsat_features n d (x : paper_main_sample n d) :
    n.-tuple 'rV[R]_(d * d) :=
  [tuple unsat_feature d (paper_main_point x i) | i < n].

(* C_kappa of the symmetric parts of A and B. *)
Definition unsat_cov_form (kappa : R) d (A B : 'M[R]_d) : R :=
  d%:R^-1 * (mxdot A B + mxdot A B^T +
             (kappa - 3%:R) * \sum_(j < d) A j j * B j j).

(* Sigma_kappa, the matrix of C_kappa in the mxvec coordinates. *)
Definition unsat_cov (kappa : R) d : 'M[R]_(d * d) :=
  \matrix_(p, q)
    unsat_cov_form kappa d (vec_mx (delta_mx 0 p : 'rV[R]_(d * d)))
                           (vec_mx (delta_mx 0 q : 'rV[R]_(d * d))).

(* The paper's lambda, the operator norm of Sigma_kappa. *)
Definition unsat_lambda (kappa : R) d : R := opnorm (unsat_cov kappa d).

(* R_d^o = {R > 0, Tr R = d}. *)
Definition unsat_domain d : set 'rV[R]_(d * d) := pd_slice d d%:R.

(* Phi_Z(R_d^o; beta), with the ridge weight unsat_lambda kappa d. *)
Definition unsat_ridge_value (kappa : R) n d (beta : R)
    (Z : n.-tuple 'rV[R]_(d * d)) : R :=
  ls_value Z (unsat_lambda kappa d) beta (unsat_domain d).

(* Phi_Z(R_d^o), without regularization. *)
Definition unsat_value n d (Z : n.-tuple 'rV[R]_(d * d)) : R :=
  ls_value Z 0 0 (unsat_domain d).

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Section fitting_error.

(* A bound that holds for every small t > 0 holds at t = 0. *)
Lemma le_quad_lim (v a g h : R) :
  (forall t : R, 0 < t <= 1 -> v <= a + t * g + t ^+ 2 * h) -> v <= a.
Proof.
move=> hv; rewrite leNgt; apply/negP => va.
have del0 : 0 < v - a by rewrite subr_gt0.
have c0 : 0 < `|g| + `|h| + 1 by rewrite ltr_wpDl // addr_ge0.
pose t := Num.min 1 ((v - a) / (2 * (`|g| + `|h| + 1))).
have t0 : 0 < t by rewrite lt_min ltr01 divr_gt0 // mulr_gt0.
have t1 : t <= 1 by rewrite ge_min lexx.
have tc : t * (`|g| + `|h| + 1) <= (v - a) / 2.
  have : t <= (v - a) / (2 * (`|g| + `|h| + 1)) by rewrite ge_min lexx orbT.
  rewrite ler_pdivlMr ?mulr_gt0 // => h1.
  by rewrite ler_pdivlMr //; lra.
have t01 : 0 < t <= 1 by rewrite t0 t1.
have hvt := hv t t01.
have hg : t * g <= t * `|g| by apply: ler_wpM2l; [exact: ltW|exact: ler_norm].
have hh : t ^+ 2 * h <= t * `|h|.
  apply: le_trans (_ : t ^+ 2 * `|h| <= _).
    by apply: ler_wpM2l; [exact: exprn_ge0 (ltW t0)|exact: ler_norm].
  rewrite expr2 -mulrA; apply: ler_piMl => //.
  by apply: mulr_ge0; [exact: ltW|exact: normr_ge0].
have : t * `|g| + t * `|h| <= (v - a) / 2.
  by apply: le_trans tc; rewrite !mulrDr lerDl mulr1; exact: ltW.
lra.
Qed.

(* The quadratic form and the trace as Frobenius products. *)
Lemma quadratic_form_mxdot d (S : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form S v = mxdot (v *m v^T) S.
Proof.
rewrite /paper_main_quadratic_form /mxdot.
apply: eq_bigr => i _; apply: eq_bigr => j _.
by rewrite !mxE big_ord1 !mxE mulrAC.
Qed.

Lemma quadratic_form_row d (S : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form S v = mxdot v^T (v^T *m S).
Proof.
rewrite /paper_main_quadratic_form /mxdot big_ord1 exchange_big /=.
apply: eq_bigr => j _; rewrite !mxE mulr_sumr.
by apply: eq_bigr => i _; rewrite !mxE; ring.
Qed.

Lemma trace_mxdot d (S : 'M[R]_d) : paper_main_trace S = mxdot 1%:M S.
Proof.
rewrite /paper_main_trace /mxdot; apply: eq_bigr => i _.
rewrite (bigD1 i) //= big1 ?addr0.
  by move=> j ji; rewrite mxE eq_sym (negbTE ji) mul0r.
by rewrite mxE eqxx mul1r.
Qed.

Lemma trace1 d : paper_main_trace (1%:M : 'M[R]_d) = d%:R.
Proof.
rewrite /paper_main_trace.
by under eq_bigr do rewrite mxE eqxx; rewrite sumr_const card_ord.
Qed.

(* <W(x), theta> = (x^T S x - tr S) / sqrt d for S = vec_mx theta. *)
Lemma unsat_feature_dot d (x : 'cV[R]_d) (th : 'rV[R]_(d * d)) :
  mxdot (unsat_feature d x) th =
  (paper_main_quadratic_form (vec_mx th) x - paper_main_trace (vec_mx th)) /
  Num.sqrt d%:R.
Proof.
rewrite /unsat_feature -[th in LHS]vec_mxK mxdot_mxvec mxdotZl mxdotBl.
by rewrite -quadratic_form_mxdot -trace_mxdot mulrC.
Qed.

(* A positive definite matrix is positive semidefinite. *)
Lemma posdef_paper_psd d (S : 'M[R]_d) : posdefmx S -> paper_main_psd S.
Proof.
move=> [/symmetricmxP Ss Sp]; split.
  by move=> i j; rewrite -{1}Ss mxE.
move=> v; rewrite quadratic_form_row.
have [->|v0] := eqVneq v^T 0; first by rewrite mul0mx mxdot0l.
exact: ltW (Sp _ v0).
Qed.

(* (1 - t) S + t I is positive definite for S >= 0 and 0 < t <= 1. *)
Lemma psd_shift_posdef d (S : 'M[R]_d) (t : R) : paper_main_psd S ->
  0 < t <= 1 -> posdefmx ((1 - t) *: S + t *: 1%:M).
Proof.
move=> [Ss Sp] /andP[t0 t1]; split.
  apply/symmetricmxP; rewrite linearD !linearZ /= tr_scalar_mx.
  congr (_ *: _ + _); apply/matrixP => i j; rewrite mxE.
  exact: Ss.
move=> y y0.
rewrite mulmxDr -!scalemxAr mulmx1 mxdotDr !mxdotZr.
have := Sp y^T; rewrite quadratic_form_row trmxK => hS.
have hy : 0 < mxdot y y by rewrite mxdot_gt0.
have t10 : 0 <= 1 - t by rewrite subr_ge0.
by rewrite ltr_wpDl // ?mulr_ge0 // mulr_gt0.
Qed.

(* eq:unregularized-affine-energy-value: Gamma_X = 2 Phi_W(X)(R_d^o). *)
Theorem unsat_fitting_error n d (x : paper_main_sample n d) : (0 < d)%N ->
  universality_fitting_error n d x =
  2 * unsat_value n d (unsat_features n d x).
Proof.
move=> d0.
pose s := Num.sqrt (d%:R : R).
have s0 : 0 < s by rewrite sqrtr_gt0 ltr0n.
have ss : d%:R / s = s.
  by rewrite -{1}(sqr_sqrtr (ler0n _ d)) -/s expr2 mulfK // gt_eqF.
pose q (S : 'M[R]_d) (i : 'I_n) :=
  paper_main_quadratic_form S (paper_main_point x i).
pose J (S : 'M[R]_d) (r : R) := (\sum_(i < n) (q S i / s - r) ^+ 2) / n%:R.
have J0 S r : 0 <= J S r.
  by rewrite divr_ge0 // sumr_ge0 // => i _; exact: sqr_ge0.
(* twice the objective at theta of trace d, with b = r - sqrt d *)
have hobj th b : paper_main_trace (vec_mx th) = d%:R ->
    2 * ls_objective (unsat_features n d x) 0 0 th b = J (vec_mx th) (b + s).
  move=> htr; rewrite /ls_objective /J !mul0r addr0.
  have -> : \sum_(i < n) (b - mxdot (tnth (unsat_features n d x) i) th) ^+ 2
      = \sum_(i < n) (q (vec_mx th) i / s - (b + s)) ^+ 2.
    apply: eq_bigr => i _.
    rewrite tnth_mktuple unsat_feature_dot htr -/s -sqrrN.
    by congr (_ ^+ 2); rewrite mulrBl ss /q; ring.
  have n2 : 2 * (n%:R *+ 2)^-1 = (n%:R : R)^-1.
    by rewrite -[n%:R *+ 2]mulr_natr invfM mulrCA mulfV ?mulr1 // pnatr_eq0.
  by rewrite mulrA n2 mulrC.
rewrite /universality_fitting_error /unsat_value /ls_value.
pose F1 := [set v : R | exists (S : 'M[R]_d) (r : R), paper_main_psd S /\
  paper_main_trace S = d%:R /\ 0 <= r /\ v = J S r]%classic.
pose F2 := [set ls_objective (unsat_features n d x) 0 0 th b |
  th in unsat_domain d & b in [set: R]]%classic.
change (inf F1 = 2 * inf F2).
have F1lb : has_lbound F1 by exists 0 => _ [S [r [_ [_ [_ ->]]]]]; exact: J0.
have F1n : (F1 !=set0)%classic.
  exists (J 1%:M 0), 1%:M, 0; split.
    split; first by move=> i j; rewrite !mxE eq_sym.
    by move=> v; rewrite quadratic_form_row mulmx1 mxdot_ge0.
  by split; [exact: trace1|split].
have F2lb : has_lbound F2.
  exists 0 => _ [th _ [b _ <-]]; rewrite /ls_objective !mul0r addr0.
  rewrite mulr_ge0 ?invr_ge0 ?mulrn_wge0 // sumr_ge0 // => i _.
  exact: sqr_ge0.
have F2n : (F2 !=set0)%classic.
  exists (ls_objective (unsat_features n d x) 0 0 (mxvec 1%:M) 0),
    (mxvec 1%:M); first exact: pd_slice_one.
  by exists 0.
have two0 : (0 : R) < 2 by [].
apply/eqP; rewrite eq_le; apply/andP; split.
  (* Gamma_X <= 2 Phi: a value of Phi gives a value of Gamma_X with r >= 0,
     since the quadratic forms are nonnegative *)
  rewrite mulrC -ler_pdivrMr //.
  apply: lb_le_inf F2n _ => _ [th [Sp Str] [b _ <-]].
  rewrite ler_pdivrMr // mulrC hobj //.
  have Spsd := posdef_paper_psd _ _ Sp.
  have [r0|r0] := leP 0 (b + s).
    apply: ge_inf; first exact: F1lb.
    by exists (vec_mx th), (b + s); split => //; split.
  apply: le_trans (_ : J (vec_mx th) 0 <= _).
    apply: ge_inf; first exact: F1lb.
    by exists (vec_mx th), 0; split => //; split.
  apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  apply: ler_sum => i _.
  have a0 : 0 <= q (vec_mx th) i / s.
    by apply: divr_ge0; [exact: Spsd.2|exact: ltW].
  rewrite subr0 ler_sqr ?nnegrE //; last first.
    by rewrite lerDl oppr_ge0 ltW.
  lra.
(* 2 Phi <= Gamma_X: a fit S >= 0 is the limit of (1 - t) S + t I > 0 *)
apply: lb_le_inf F1n _ => _ [S [r [Spsd [Str [r0 ->]]]]].
pose a i := q S i / s.
pose c i := q 1%:M i / s.
apply: (le_quad_lim _ _ (2 * (\sum_(i < n) (a i - r) * (c i - a i)) / n%:R)
  ((\sum_(i < n) (c i - a i) ^+ 2) / n%:R)) => t t01.
have /andP[t0 t1] := t01.
pose St := (1 - t) *: S + t *: (1%:M : 'M[R]_d).
have Stpd := psd_shift_posdef _ _ _ Spsd t01.
have Sttr : paper_main_trace St = d%:R.
  rewrite /St !trace_mxdot mxdotDr !mxdotZr -!trace_mxdot Str trace1.
  by ring.
have hV : inf F2 <=
    ls_objective (unsat_features n d x) 0 0 (mxvec St) (r - s).
  apply: ge_inf; first exact: F2lb.
  exists (mxvec St); last by exists (r - s).
  by rewrite /unsat_domain /pd_slice /= mxvecK; split.
apply: le_trans (ler_wpM2l (ltW two0) hV) _.
rewrite hobj ?mxvecK // subrK.
have hq i : q St i / s = (1 - t) * a i + t * c i.
  rewrite /q /St quadratic_form_mxdot mxdotDr !mxdotZr.
  by rewrite -!quadratic_form_mxdot /a /c /q mulrDl !mulrA.
rewrite /J.
under eq_bigr do rewrite hq.
apply: le_trans (_ : (\sum_(i < n) (a i - r) ^+ 2 +
    t * (2 * \sum_(i < n) (a i - r) * (c i - a i)) +
    t ^+ 2 * \sum_(i < n) (c i - a i) ^+ 2) / n%:R <= _).
  rewrite le_eqVlt; apply/orP; left; apply/eqP; congr (_ / _).
  rewrite mulr_sumr mulr_sumr mulr_sumr -!big_split /=.
  by apply: eq_bigr => i _; ring.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
rewrite /a.
move: (\sum_(i < n) (q S i / s - r) ^+ 2)
  (\sum_(i < n) (q S i / s - r) * (c i - q S i / s))
  (\sum_(i < n) (c i - q S i / s) ^+ 2) => A B C.
move: (n%:R : R) => m.
have e (A' B' C' m' t' : (R : realType)) :
    (A' + t' * (2 * B') + t' ^+ 2 * C') / m' =
    A' / m' + t' * (2 * B' / m') + t' ^+ 2 * (C' / m') by ring.
exact: e.
Qed.

End fitting_error.
