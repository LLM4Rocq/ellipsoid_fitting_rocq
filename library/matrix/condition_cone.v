From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals topology.
From mathcomp Require Import normedtype ring_tactic field_tactic.
From mathcomp Require Import arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.matrix Require Import von_neumann psd_part nuclear.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.convex Require Import moreau.

(**md**************************************************************************)
(* # The cone of matrices of bounded condition number                         *)
(*                                                                            *)
(* For C >= 1, cond_cone C is the set of the real symmetric n x n matrices Q  *)
(* with t I <= Q <= C t I for some t >= 0: the positive semidefinite          *)
(* matrices of condition number at most C, and 0. It is a closed convex cone. *)
(* Its distance to a symmetric matrix H and its support function are         *)
(* computed from the spectrum of H: the nearest point of the cone clips the   *)
(* eigenvalues of H to an interval [t, C t] (Tanaka and Nakata, Optim. Lett.  *)
(* 8 (2014)). The optimal t is not needed in closed form: the distance is an  *)
(* infimum over t >= 0 of a sum over the eigenvalues, which is what a limit   *)
(* theorem for random spectra can handle.                                     *)
(*                                                                            *)
(* - itv_dist a b x, clamp a b x: the distance from x to [a, b] and the       *)
(*   nearest point; itv_dist_clamp, itv_dist_le (the distance to any point of *)
(*   [a, b] is larger), itv_dist_lipschitz (1-Lipschitz in x), itv_dist_shift *)
(*   (Lipschitz in the endpoints).                                            *)
(* - cond_coneP: for Q symmetric, Q is in the cone iff its eigenvalues lie in *)
(*   some [t, C t] with t >= 0; cond_cone_quad: for C >= 0, iff Q is          *)
(*   symmetric, positive semidefinite and |y|^2 x^T Q x <= C |x|^2 y^T Q y    *)
(*   for all x, y; cond_cone0, cond_cone1, cond_coneZ, cond_cone_convex.      *)
(* - cond_cone_vec C, the cone in the coordinates of mxvec:                   *)
(*   cond_cone_vec_closed, cond_cone_vec0, cond_cone_vec_convex,              *)
(*   cond_cone_vecZ, the hypotheses of the cone projection of                 *)
(*   convex/moreau.v.                                                         *)
(* - cond_cone_dist: for H symmetric and C >= 1, the squared Frobenius        *)
(*   distance from H to the cone is cond_dist C H, the infimum over t >= 0 of *)
(*   cond_energy C t H = sum_i dist(lambda_i(H), [t, C t])^2.                 *)
(*   cond_energy_le (Hoffman-Wielandt) gives the lower bound, cond_clip and   *)
(*   cond_clip_energy (the eigenvalues of H clipped to [t, C t]) the upper    *)
(*   bound.                                                                   *)
(* - cond_support C A, the supremum of <A, Q> over the Q of the cone with     *)
(*   |Q|_F <= 1: cond_support_proj, it is the norm of the projection of A     *)
(*   onto the cone; cond_support_sqr, for H symmetric and C >= 1,             *)
(*   cond_support C H ^ 2 = |H|_F^2 - cond_dist C H (Moreau's decomposition); *)
(*   cond_support_sym, only the symmetric part of A matters; cond_supportZ,   *)
(*   cond_energyZ, cond_distZ, the scalings.                                  *)
(* - cond_energy_mono, cond_dist_itv: when the eigenvalues of H are at most   *)
(*   T >= 0, the energy increases on [T, oo) and the infimum may be taken     *)
(*   over [0, T].                                                             *)
(* - cond_slice C, the trace slice {Q in the cone | tr Q = n}, a compact      *)
(*   convex base of the cone: cond_slice1, cond_slice_spec (eigenvalues in    *)
(*   [1/C, C]), cond_slice_t (between t I and C t I with t in [1/C, 1]),      *)
(*   cond_slice_form, cond_slice_frobenius                                    *)
(*   (n <= |Q|_F^2 <= C n), cond_cone_slice (every nonzero point of the cone  *)
(*   has a positive multiple in the slice); cond_slice_vec, the slice in the  *)
(*   coordinates of mxvec: cond_slice_vec_closed, cond_slice_vec_convex,      *)
(*   cond_slice_vec_frobenius, cond_cone_vec_slice.                           *)
(*                                                                            *)
(* ```                                                                        *)
(*    itv_dist a b x == the distance from x to the interval [a, b]            *)
(*       clamp a b x == the nearest point of [a, b] to x                      *)
(*       cond_cone C == the symmetric Q with t I <= Q <= C t I, some t >= 0   *)
(*   cond_cone_vec C == the same cone in the coordinates of mxvec             *)
(* cond_energy C t H == sum_i itv_dist t (C t) (spec H 0 i) ^ 2               *)
(*     cond_dist C H == the infimum of cond_energy C t H over t >= 0          *)
(*   cond_clip C t H == H with its eigenvalues clipped to [t, C t]            *)
(*  cond_support C A == sup of <A, Q> over the Q of the cone with |Q|_F <= 1  *)
(*      cond_slice C == the Q of the cone with trace n                        *)
(*  cond_slice_vec C == the same slice in the coordinates of mxvec            *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section interval_distance.
Variable R : realType.
Implicit Types a b x y : R.

(* The distance from x to the interval [a, b], for a <= b. *)
Definition itv_dist a b x : R := Num.max (a - x) 0 + Num.max (x - b) 0.

(* The nearest point of [a, b] to x, for a <= b. *)
Definition clamp a b x : R := Num.max a (Num.min b x).

Lemma itv_dist_ge0 a b x : 0 <= itv_dist a b x.
Proof. by rewrite /itv_dist addr_ge0 // le_max lexx orbT. Qed.

Lemma clamp_itv a b x : a <= b -> a <= clamp a b x <= b.
Proof. by move=> ab; rewrite /clamp le_max lexx /= ge_max ab ge_min lexx. Qed.

Lemma itv_dist_clamp a b x : a <= b -> itv_dist a b x = `|x - clamp a b x|.
Proof.
move=> ab; rewrite /itv_dist /clamp.
have [xb|bx] := leP x b.
  have [ax|xa] := leP a x.
    by rewrite subrr normr0 !max_r ?addr0 // ?subr_le0.
  rewrite max_l ?subr_ge0 ?(ltW xa) // [maxr (x - b) 0]max_r ?subr_le0 //.
  by rewrite addr0 distrC ger0_norm // subr_ge0 ltW.
rewrite (max_r ab) [maxr (a - x) 0]max_r ?subr_le0 ?(le_trans ab (ltW bx)) //.
by rewrite add0r max_l ?subr_ge0 ?(ltW bx) // ger0_norm // subr_ge0 ltW.
Qed.

Lemma itv_dist_le a b x y : a <= y <= b -> itv_dist a b x <= `|x - y|.
Proof.
move=> /andP[ay yb]; rewrite /itv_dist.
have [xy|yx] := leP x y.
  rewrite distrC ger0_norm ?subr_ge0 //.
  rewrite [maxr (x - b) 0]max_r ?subr_le0 ?(le_trans xy yb) //.
  by rewrite addr0 ge_max subr_ge0 xy andbT; lra.
rewrite ger0_norm ?subr_ge0 ?(ltW yx) //.
rewrite [maxr (a - x) 0]max_r ?subr_le0 ?(le_trans ay (ltW yx)) //.
by rewrite add0r ge_max subr_ge0 (ltW yx) andbT; lra.
Qed.

Lemma itv_dist_lipschitz a b x y : a <= b ->
  `|itv_dist a b x - itv_dist a b y| <= `|x - y|.
Proof.
move=> ab.
have h u v : itv_dist a b u <= `|u - v| + itv_dist a b v.
  rewrite [X in _ <= _ + X](itv_dist_clamp v ab).
  apply: le_trans (itv_dist_le u (clamp_itv v ab)) _.
  have -> : u - clamp a b v = (u - v) + (v - clamp a b v).
    by rewrite addrA subrK.
  exact: ler_normD.
rewrite ler_norml; apply/andP; split.
  by have := h y x; rewrite distrC; lra.
by have := h x y; lra.
Qed.

Lemma itv_dist_shift a b a' b' x :
  `|itv_dist a b x - itv_dist a' b' x| <= `|a - a'| + `|b - b'|.
Proof.
have h (u v : R) : `|Num.max u 0 - Num.max v 0| <= `|u - v|.
  case: (leP u 0); case: (leP v 0) => vh uh; rewrite ?subrr ?normr0 //.
    by rewrite sub0r normrN distrC (gtr0_norm vh) ger0_norm; lra.
  by rewrite subr0 (gtr0_norm uh) ger0_norm; lra.
rewrite /itv_dist.
have -> : Num.max (a - x) 0 + Num.max (x - b) 0 -
    (Num.max (a' - x) 0 + Num.max (x - b') 0) =
  (Num.max (a - x) 0 - Num.max (a' - x) 0) +
  (Num.max (x - b) 0 - Num.max (x - b') 0) by ring.
apply: le_trans (ler_normD _ _) _; apply: lerD.
  apply: le_trans (h _ _) _.
  by rewrite (_ : a - x - (a' - x) = a - a') //; ring.
apply: le_trans (h _ _) _.
have -> : x - b - (x - b') = - (b - b') by ring.
by rewrite normrN.
Qed.

End interval_distance.

Section condition_cone.
Variable R : realType.
Variable n : nat.
Implicit Types (A H Q : 'M[R]_n) (C t : R).

(* The cone of the symmetric matrices Q with t I <= Q <= C t I for some
   t >= 0: the positive semidefinite matrices of condition number at most C,
   and 0. *)
Definition cond_cone C : set 'M[R]_n :=
  [set Q | Q \is symmetricmx /\ exists2 t : R, 0 <= t &
     forall x : 'cV[R]_n,
       t * mxdot x x <= mxdot x (Q *m x) <= C * t * mxdot x x].

Lemma cond_coneP C Q : Q \is symmetricmx ->
  cond_cone C Q <-> exists2 t : R, 0 <= t & forall i, t <= spec Q 0 i <= C * t.
Proof.
move=> Qs; have [P Po QE] := spec_decomposition Qs.
split => [[_ [t t0 ht]]|[t t0 ht]].
  exists t => // i; apply/andP; split.
    by apply: (spectral_form_ge t Po QE).1 => x; case/andP: (ht x).
  by apply: (spectral_form_le (C * t) Po QE).1 => x; case/andP: (ht x).
split => //; exists t => // x; apply/andP; split.
  by apply: (spectral_form_ge t Po QE).2 => i; case/andP: (ht i).
by apply: (spectral_form_le (C * t) Po QE).2 => i; case/andP: (ht i).
Qed.

Lemma cond_cone0 C : cond_cone C 0.
Proof.
split; first by apply/symmetricmxP; rewrite trmx0.
by exists 0 => // x; rewrite mul0mx mxdot0r !mulr0 !mul0r lexx.
Qed.

Lemma cond_cone1 C : 1 <= C -> cond_cone C 1%:M.
Proof.
move=> C1; split; first by apply/symmetricmxP; rewrite trmx1.
exists 1 => // x; rewrite mul1mx mul1r lexx /= mulr1.
by rewrite ler_peMl // mxdot_ge0.
Qed.

Lemma cond_coneZ C (a : R) Q : 0 <= a -> cond_cone C Q -> cond_cone C (a *: Q).
Proof.
move=> a0 [Qs [t t0 ht]]; split.
  by apply/symmetricmxP; rewrite linearZ /=; move/symmetricmxP: Qs => ->.
exists (a * t); first exact: mulr_ge0.
move=> x; rewrite -scalemxAl mxdotZr; case/andP: (ht x) => h1 h2.
apply/andP; split; first by rewrite -mulrA ler_wpM2l.
by rewrite [C * (a * t)]mulrCA -mulrA ler_wpM2l.
Qed.

Lemma cond_cone_convex C Q1 Q2 (s : R) : cond_cone C Q1 -> cond_cone C Q2 ->
  0 <= s <= 1 -> cond_cone C (Q1 + s *: (Q2 - Q1)).
Proof.
move=> [Q1s [t1 t10 h1]] [Q2s [t2 t20 h2]] /andP[s0 s1]; split.
  apply/symmetricmxP; rewrite linearD linearZ linearB /=.
  by move/symmetricmxP: Q1s => ->; move/symmetricmxP: Q2s => ->.
exists ((1 - s) * t1 + s * t2).
  by rewrite addr_ge0 // mulr_ge0 // subr_ge0.
move=> x; rewrite mulmxDl mxdotDr -scalemxAl mxdotZr mulmxBl mxdotBr.
case/andP: (h1 x) => a1 b1; case/andP: (h2 x) => a2 b2.
have m0 : 0 <= mxdot x x := mxdot_ge0 x.
move: (mxdot x x) (mxdot x (Q1 *m x)) (mxdot x (Q2 *m x)) m0 a1 b1 a2 b2.
move=> m q1 q2 m0 a1 b1 a2 b2.
have e1 : 0 <= (1 - s) * (q1 - t1 * m) by rewrite mulr_ge0 // subr_ge0.
have e2 : 0 <= s * (q2 - t2 * m) by rewrite mulr_ge0 // subr_ge0.
have e3 : 0 <= (1 - s) * (C * t1 * m - q1) by rewrite mulr_ge0 // subr_ge0.
have e4 : 0 <= s * (C * t2 * m - q2) by rewrite mulr_ge0 // subr_ge0.
by apply/andP; split; nra.
Qed.

Lemma cond_cone_quad C Q : 0 <= C ->
  cond_cone C Q <-> [/\ Q \is symmetricmx,
    forall x : 'cV[R]_n, 0 <= mxdot x (Q *m x) &
    forall x y : 'cV[R]_n,
      mxdot y y * mxdot x (Q *m x) <= C * mxdot x x * mxdot y (Q *m y)].
Proof.
move=> C0; split.
  move=> [Qs [t t0 ht]]; split => // [x|x y].
    case/andP: (ht x) => h _; apply: le_trans h.
    by rewrite mulr_ge0 // mxdot_ge0.
  case/andP: (ht x) => _ hx; case/andP: (ht y) => hy _.
  have mx0 : 0 <= mxdot x x := mxdot_ge0 x.
  have my0 : 0 <= mxdot y y := mxdot_ge0 y.
  have e1 : mxdot y y * mxdot x (Q *m x) <= mxdot y y * (C * t * mxdot x x).
    by rewrite ler_wpM2l.
  apply: le_trans e1 _.
  have h3 : 0 <= C * mxdot x x * (mxdot y (Q *m y) - t * mxdot y y).
    by rewrite !mulr_ge0 // subr_ge0.
  nra.
move=> [Qs psd pair]; apply/(cond_coneP C Qs).
have [P Po QE] := spec_decomposition Qs.
have sp0 i : 0 <= spec Q 0 i by move: i; apply/(spectral_psd Po QE).
have ev i : mxdot (row i P)^T (Q *m (row i P)^T) = spec Q 0 i.
  rewrite (spectral_eigenvector _ Po QE) mxdotZr orthogonalmx_row_unit //.
  by rewrite mulr1.
have unit i : mxdot (row i P)^T (row i P)^T = 1 by exact: orthogonalmx_row_unit.
have [i0 _|none] := pickP (fun i : 'I_n => true); last first.
  by exists 0 => // i; have := none i.
have n0 : (0 < n)%N := leq_ltn_trans (leq0n _) (ltn_ord i0).
have ln : (n.-1 < n)%N by rewrite ltn_predL.
pose l := Ordinal ln.
exists (spec Q 0 l); first exact: sp0.
move=> i; apply/andP; split.
  by apply: spec_decr; rewrite /= -ltnS prednK ?ltn_ord.
have := pair (row i P)^T (row l P)^T.
by rewrite ev ev !unit !mul1r mulr1.
Qed.

(* The cone in the coordinates of mxvec, where moreau.v applies. *)
Definition cond_cone_vec C : set 'rV[R]_(n * n) :=
  [set v | cond_cone C (vec_mx v)].

Lemma mxdot_quad_vec (x : 'cV[R]_n) (v : 'rV[R]_(n * n)) :
  mxdot x (vec_mx v *m x) = mxdot v (mxvec (x *m x^T)).
Proof.
by rewrite [RHS]mxdotC -mxdot_vec_mxr [RHS]mxdotC mxdot_outer mxdot_colE mulmxA.
Qed.

Lemma continuous_mxdotv (c : 'rV[R]_(n * n)) :
  continuous (fun v : 'rV[R]_(n * n) => mxdot v c).
Proof.
move=> v; have -> : (fun v : 'rV[R]_(n * n) => mxdot v c) =
    (fun N : 'M[R]_(1, 1) => N 0 0) \o (fun v => v *m c^T).
  by apply/funext => w /=; rewrite mxdot_rowE.
apply: continuous_comp; first exact: continuous_mulmxr.
exact: matrix_normedtype.coord_continuous.
Qed.

Lemma cond_cone_vec_closed C : 0 <= C -> closed (cond_cone_vec C).
Proof.
move=> C0.
have hs (c : 'rV[R]_(n * n)) :
    closed [set v : 'rV[R]_(n * n) | 0 <= mxdot v c].
  exact: ((continuous_closedP (fun v : 'rV[R]_(n * n) => mxdot v c)).1
    (@continuous_mxdotv c) _ (@closed_ge R 0)).
pose E (ij : 'I_n * 'I_n) : 'M[R]_n := delta_mx ij.1 ij.2 - delta_mx ij.2 ij.1.
have pE v ij : mxdot v (mxvec (E ij)) = vec_mx v ij.1 ij.2 - vec_mx v ij.2 ij.1.
  by rewrite mxdotC -mxdot_vec_mxr mxdotC mxdotBr !mxdot_delta.
pose F (xy : 'cV[R]_n * 'cV[R]_n) : 'rV[R]_(n * n) :=
  (C * mxdot xy.1 xy.1) *: mxvec (xy.2 *m xy.2^T) -
  mxdot xy.2 xy.2 *: mxvec (xy.1 *m xy.1^T).
have pF v xy : mxdot v (F xy) =
    C * mxdot xy.1 xy.1 * mxdot xy.2 (vec_mx v *m xy.2) -
    mxdot xy.2 xy.2 * mxdot xy.1 (vec_mx v *m xy.1).
  by rewrite mxdotBr !mxdotZr -!mxdot_quad_vec.
have -> : cond_cone_vec C =
    (\bigcap_(ij in [set: 'I_n * 'I_n])
       ([set v | 0 <= mxdot v (mxvec (E ij))] `&`
        [set v | 0 <= mxdot v (- mxvec (E ij))])) `&`
    (\bigcap_(x in [set: 'cV[R]_n])
       [set v | 0 <= mxdot v (mxvec (x *m x^T))]) `&`
    (\bigcap_(xy in [set: 'cV[R]_n * 'cV[R]_n]) [set v | 0 <= mxdot v (F xy)]).
  apply/seteqP; split => v.
    move/(cond_cone_quad _ C0) => [vs psd pair]; split; first split.
    - move=> ij _; rewrite /= mxdotNr pE; have /symmetricmxP Ve := vs.
      have := congr1 (fun A : 'M[R]_n => A ij.2 ij.1) Ve; rewrite mxE => ->.
      by rewrite subrr oppr0 lexx.
    - by move=> x _; rewrite /= -mxdot_quad_vec.
    - by move=> xy _; rewrite /= pF subr_ge0.
  move=> [[HE Hx] Hxy]; apply/(cond_cone_quad _ C0); split.
  - apply/symmetricmxP/matrixP => i j; rewrite mxE.
    have [h1 h2] := HE (j, i) I; move: h1 h2; rewrite /= mxdotNr pE /=.
    rewrite oppr_ge0 subr_ge0 subr_le0 => h1 h2.
    by apply/eqP; rewrite eq_le h1 h2.
  - by move=> x; rewrite mxdot_quad_vec; exact: Hx x I.
  - by move=> x y; have := Hxy (x, y) I; rewrite /= pF subr_ge0.
apply: closedI; first apply: closedI.
- by apply: closed_bigI => ij _; apply: closedI; exact: hs.
- by apply: closed_bigI => x _; exact: hs.
- by apply: closed_bigI => xy _; exact: hs.
Qed.

Lemma cond_cone_vec0 C : cond_cone_vec C 0.
Proof. by rewrite /cond_cone_vec /= linear0; exact: cond_cone0. Qed.

Lemma cond_cone_vec_convex C (x y : 'rV[R]_(n * n)) (s : R) :
  cond_cone_vec C x -> cond_cone_vec C y -> 0 <= s <= 1 ->
  cond_cone_vec C (x + s *: (y - x)).
Proof.
move=> hx hy hs; rewrite /cond_cone_vec /= linearD linearZ linearB /=.
exact: cond_cone_convex.
Qed.

Lemma cond_cone_vecZ C (y : 'rV[R]_(n * n)) (a : R) :
  cond_cone_vec C y -> 0 <= a -> cond_cone_vec C (a *: y).
Proof.
by move=> hy a0; rewrite /cond_cone_vec /= linearZ /=; exact: cond_coneZ.
Qed.

(* The energy of t: the squared distances from the eigenvalues of H to the
   interval [t, C t], summed. *)
Definition cond_energy C t H : R :=
  \sum_i itv_dist t (C * t) (spec H 0 i) ^+ 2.

(* Its infimum over t >= 0, the squared distance from H to cond_cone C
   (cond_cone_dist). *)
Definition cond_dist C H : R :=
  inf [set cond_energy C t H | t in [set t : R | 0 <= t]].

(* The matrix H with its eigenvalues clipped to [t, C t]. *)
Definition cond_clip C t H : 'M[R]_n :=
  (sym_spectralmx H)^T *m
  diag_mx (\row_i clamp t (C * t) (sym_spectral_diag H 0 i)) *m
  sym_spectralmx H.

Lemma cond_energy_ge0 C t H : 0 <= cond_energy C t H.
Proof. by apply: sumr_ge0 => i _; exact: sqr_ge0. Qed.

Lemma cond_dist_le C t H : 0 <= t -> cond_dist C H <= cond_energy C t H.
Proof.
move=> t0; apply: ge_inf; last by exists t.
by exists 0 => _ [s _ <-]; exact: cond_energy_ge0.
Qed.

Lemma cond_dist_ge C H (r : R) :
  (forall t, 0 <= t -> r <= cond_energy C t H) -> r <= cond_dist C H.
Proof.
move=> h; apply: lb_le_inf; first by exists (cond_energy C 0 H), 0 => //=.
by move=> _ [t t0 <-]; exact: h.
Qed.

Lemma cond_dist_ge0 C H : 0 <= cond_dist C H.
Proof. by apply: cond_dist_ge => t _; exact: cond_energy_ge0. Qed.

Lemma cond_clip_cone C t H : 1 <= C -> 0 <= t -> cond_cone C (cond_clip C t H).
Proof.
move=> C1 t0.
set P := sym_spectralmx H.
set d := \row_i clamp t (C * t) (sym_spectral_diag H 0 i).
have Po : P \is orthogonalmx := sym_spectralmx_orthogonal H.
have tC : t <= C * t by rewrite ler_peMl.
have dE i : t <= d 0 i <= C * t by rewrite mxE; exact: clamp_itv.
split.
  rewrite /cond_clip -/P -/d -{2}[P]trmxK symmetricmx_conj //.
  by apply/symmetricmxP; rewrite tr_diag_mx.
exists t => // x; apply/andP; split.
  by apply: (spectral_form_ge t Po (erefl _)).2 => i; case/andP: (dE i).
by apply: (spectral_form_le (C * t) Po (erefl _)).2 => i; case/andP: (dE i).
Qed.

Lemma cond_clip_energy C t H : 1 <= C -> 0 <= t -> H \is symmetricmx ->
  mxdot (H - cond_clip C t H) (H - cond_clip C t H) = cond_energy C t H.
Proof.
move=> C1 t0 Hs.
set P := sym_spectralmx H; set D := sym_spectral_diag H.
set d := \row_i clamp t (C * t) (D 0 i).
have Po : P \is orthogonalmx := sym_spectralmx_orthogonal H.
have E : H - cond_clip C t H = P^T *m diag_mx (D - d) *m P.
  rewrite {1}(sym_spectralE Hs) /cond_clip -/P -/D -/d -mulmxBl -mulmxBr.
  by congr (_ *m _ *m _); rewrite linearB.
rewrite E (spectral_mxdot Po (erefl _)) /cond_energy.
rewrite (sum_spec H (fun x => itv_dist t (C * t) x ^+ 2)) -/D.
apply: eq_bigr => i _; rewrite !mxE (itv_dist_clamp _ (ler_peMl t0 C1)).
by rewrite real_normK //; exact: num_real.
Qed.

Lemma cond_energy_le C H Q : H \is symmetricmx -> cond_cone C Q ->
  exists2 t : R, 0 <= t & cond_energy C t H <= mxdot (H - Q) (H - Q).
Proof.
move=> Hs [Qs QK]; have [t t0 ht] := (cond_coneP C Qs).1 (conj Qs QK).
exists t => //; apply: le_trans (hoffman_wielandt Hs Qs).
apply: ler_sum => i _.
have h := itv_dist_le (spec H 0 i) (ht i).
by rewrite -[X in _ <= X]real_normK ?num_real // ler_sqr ?nnegrE ?itv_dist_ge0.
Qed.

(* The squared distance from H to the cone. *)
Theorem cond_cone_dist C H : 1 <= C -> H \is symmetricmx ->
  inf [set mxdot (H - Q) (H - Q) | Q in cond_cone C] = cond_dist C H.
Proof.
move=> C1 Hs; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: cond_dist_ge => t t0; apply: ge_inf.
    by exists 0 => _ [Q _ <-]; exact: mxdot_ge0.
  by exists (cond_clip C t H); [exact: cond_clip_cone|exact: cond_clip_energy].
apply: lb_le_inf.
  by exists (mxdot (H - 0) (H - 0)), 0; first exact: cond_cone0.
move=> _ [Q QK <-]; have [t t0 ht] := cond_energy_le Hs QK.
exact: le_trans (cond_dist_le _ _ t0) ht.
Qed.

Lemma mxdot_vec_mx (u v : 'rV[R]_(n * n)) :
  mxdot (vec_mx u) (vec_mx v) = mxdot u v.
Proof. by rewrite mxdot_vec_mxr vec_mxK. Qed.

(* The support function of the cone on the Frobenius unit ball. *)
Definition cond_support C A : R :=
  sup [set mxdot A Q | Q in [set Q | cond_cone C Q /\ mxdot Q Q <= 1]].

Lemma cond_support_vec C (h : 'rV[R]_(n * n)) :
  sup [set mxdot h v | v in [set v | cond_cone_vec C v /\ mxdot v v <= 1]] =
  cond_support C (vec_mx h).
Proof.
rewrite /cond_support; congr sup; apply/seteqP; split => _ [x [Kx x1] <-].
  exists (vec_mx x); first by split; rewrite // mxdot_vec_mx.
  by rewrite mxdot_vec_mx.
exists (mxvec x).
  by split; rewrite /cond_cone_vec /= ?mxvecK // -mxdot_vec_mx !mxvecK.
by rewrite -mxdot_vec_mx mxvecK.
Qed.

(* The support function is the norm of the projection onto the cone. *)
Lemma cond_support_proj C (h : 'rV[R]_(n * n)) : 0 <= C ->
  cond_support C (vec_mx h) = frobenius (proj (cond_cone_vec C) h).
Proof.
move=> C0; rewrite -cond_support_vec.
exact: (cone_proj_support (cond_cone_vec_closed C0) (cond_cone_vec0 C)
  (@cond_cone_vec_convex C) (@cond_cone_vecZ C)).
Qed.

Lemma cond_support_ge0 C A : 0 <= C -> 0 <= cond_support C A.
Proof.
by move=> C0; rewrite -[A]mxvecK cond_support_proj //; exact: frobenius_ge0.
Qed.

(* The support function in terms of the spectrum: by Moreau's
   decomposition, its square is |H|^2 minus the squared distance from H to
   the cone, and by cond_cone_dist that distance is cond_dist C H. *)
Theorem cond_support_sqr C H : 1 <= C -> H \is symmetricmx ->
  cond_support C H ^+ 2 = mxdot H H - cond_dist C H.
Proof.
move=> C1 Hs.
have C0 : 0 <= C := le_trans ler01 C1.
have Kc := cond_cone_vec_closed C0.
have K0 := cond_cone_vec0 C.
have Kn : cond_cone_vec C !=set0 by exists 0.
have Kcvx := @cond_cone_vec_convex C.
have Kcone := @cond_cone_vecZ C.
set z := mxvec H.
have Hz : H = vec_mx z by rewrite mxvecK.
rewrite {1}Hz cond_support_proj // frobenius_sqr.
set p := proj (cond_cone_vec C) z.
have [Kp hv] := projP Kc Kn Kcvx z.
have hmin := (proj_variational Kcvx z Kp).2 hv.
have hn := moreau_norm Kc K0 Kcvx Kcone z.
have [ez oz] := moreau Kc K0 Kcvx Kcone z.
rewrite -/p in Kp hv hmin hn ez oz.
set q := proj (polar (cond_cone_vec C)) z in hn ez oz.
have qE : q = z - p by apply/eqP; rewrite eq_sym subr_eq addrC -ez.
(* the squared distance from z to the cone is cond_dist C H *)
have dist : mxdot (z - p) (z - p) = cond_dist C H.
  apply/eqP; rewrite eq_le; apply/andP; split.
    apply: cond_dist_ge => t t0.
    have Kt : cond_cone_vec C (mxvec (cond_clip C t H)).
      by rewrite /cond_cone_vec /= mxvecK; exact: cond_clip_cone.
    apply: le_trans (hmin _ Kt) _.
    by rewrite -mxdot_vec_mx !linearB /= mxvecK -Hz cond_clip_energy.
  have [t t0 ht] := cond_energy_le Hs Kp.
  apply: le_trans (cond_dist_le _ _ t0) (le_trans ht _).
  by rewrite Hz -linearB /= mxdot_vec_mx.
have zH : mxdot z z = mxdot H H by rewrite [in RHS]Hz mxdot_vec_mx.
by rewrite -zH hn qE dist; lra.
Qed.

(* Only the symmetric part of A matters. *)
Lemma cond_support_sym C A :
  cond_support C A = cond_support C (2^-1 *: (A + A^T)).
Proof.
rewrite /cond_support; congr sup; apply/seteqP; split => _ [Q [[Qs QK] Q1] <-];
  exists Q => //; have /symmetricmxP QT := Qs;
  have e : mxdot A^T Q = mxdot A Q by rewrite -[in LHS]QT mxdot_trmx.
  by rewrite mxdotZl mxdotDl e; field.
by rewrite mxdotZl mxdotDl e; field.
Qed.

Lemma cond_supportZ C (c : R) A : 0 <= C -> 0 <= c ->
  cond_support C (c *: A) = c * cond_support C A.
Proof.
move=> C0 c0.
have Kc := cond_cone_vec_closed C0.
have Kn : cond_cone_vec C !=set0 by exists 0; exact: cond_cone_vec0.
have Kcvx := @cond_cone_vec_convex C.
have Kcone := @cond_cone_vecZ C.
rewrite -[A]mxvecK -linearZ /= !cond_support_proj //.
set z := mxvec A.
have [Kp hv] := projP Kc Kn Kcvx z.
set p := proj (cond_cone_vec C) z in Kp hv *.
(* the projection onto a cone commutes with nonnegative scalings *)
have -> : proj (cond_cone_vec C) (c *: z) = c *: p.
  apply: (proj_eq Kc Kn Kcvx); first exact: Kcone.
  move=> y Ky; have [->|cn0] := eqVneq c 0.
    by rewrite !scale0r subrr mxdot0l.
  have cp : 0 < c by rewrite lt0r cn0.
  rewrite -scalerBr mxdotZl.
  have -> : y - c *: p = c *: (c^-1 *: y - p).
    by rewrite scalerBr scalerA mulfV // scale1r.
  rewrite mxdotZr mulrA; apply: mulr_ge0_le0; first exact: mulr_ge0.
  by apply: hv; apply: Kcone => //; rewrite invr_ge0 ltW.
by rewrite frobeniusZ ger0_norm.
Qed.

Lemma cond_energyZ C (c t : R) H : 0 <= c -> H \is symmetricmx ->
  cond_energy C (c * t) (c *: H) = c ^+ 2 * cond_energy C t H.
Proof.
move=> c0 Hs; rewrite /cond_energy (spec_scale Hs c0) mulr_sumr.
apply: eq_bigr => i _; rewrite mxE.
have -> : itv_dist (c * t) (C * (c * t)) (c * spec H 0 i) =
    c * itv_dist t (C * t) (spec H 0 i).
  by rewrite /itv_dist mulrDr !maxr_pMr // mulr0 !mulrBr [C * (c * t)]mulrCA.
by rewrite exprMn.
Qed.

Lemma cond_distZ C (c : R) H : 0 < c -> H \is symmetricmx ->
  cond_dist C (c *: H) = c ^+ 2 * cond_dist C H.
Proof.
move=> c0 Hs; have c2 : 0 < c ^+ 2 by rewrite exprn_gt0.
apply/eqP; rewrite eq_le; apply/andP; split.
  have h : cond_dist C (c *: H) / c ^+ 2 <= cond_dist C H.
    apply: cond_dist_ge => t t0; rewrite ler_pdivrMr //.
    apply: le_trans (cond_dist_le _ _ (mulr_ge0 (ltW c0) t0)) _.
    by rewrite (cond_energyZ _ _ (ltW c0) Hs) mulrC.
  by move: h; rewrite ler_pdivrMr // mulrC.
apply: cond_dist_ge => s s0.
have -> : s = c * (c^-1 * s) by rewrite mulrA mulfV ?gt_eqF // mul1r.
rewrite (cond_energyZ _ _ (ltW c0) Hs) ler_pM2l //; apply: cond_dist_le.
by rewrite mulr_ge0 // invr_ge0 ltW.
Qed.

(* Beyond the largest eigenvalue the energy increases, so the infimum may
   be taken over a compact interval. *)
Lemma cond_energy_mono C H t s : 1 <= C -> 0 <= t ->
  (forall i, spec H 0 i <= t) -> t <= s ->
  cond_energy C t H <= cond_energy C s H.
Proof.
move=> C1 t0 hH ts; apply: ler_sum => i _.
have hi := hH i; have s0 := le_trans t0 ts; have hs := le_trans hi ts.
have e (u : R) : 0 <= u -> spec H 0 i <= u ->
    itv_dist u (C * u) (spec H 0 i) = u - spec H 0 i.
  move=> u0 hu; rewrite /itv_dist max_l ?subr_ge0 //.
  rewrite [Num.max (_ - C * u) 0]max_r ?addr0 // subr_le0.
  by apply: le_trans hu _; rewrite ler_peMl.
by rewrite !e // ler_sqr ?nnegrE ?subr_ge0 ?lerD2r.
Qed.

Lemma cond_dist_itv C H (T : R) : 1 <= C -> 0 <= T ->
  (forall i, spec H 0 i <= T) ->
  cond_dist C H = inf [set cond_energy C t H | t in [set t | 0 <= t <= T]].
Proof.
move=> C1 T0 hT.
have lbB : has_lbound [set cond_energy C t H | t in [set t | 0 <= t <= T]].
  by exists 0 => _ [t _ <-]; exact: cond_energy_ge0.
have inB t : 0 <= t <= T ->
    inf [set cond_energy C t H | t in [set t | 0 <= t <= T]] <=
    cond_energy C t H.
  by move=> tT; apply: ge_inf => //; exists t.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: lb_le_inf.
    by exists (cond_energy C 0 H), 0 => //=; rewrite lexx T0.
  by move=> _ [t /andP[t0 _] <-]; exact: cond_dist_le.
apply: cond_dist_ge => t t0.
have [tT|Tt] := leP t T; first by apply: inB; rewrite t0 tT.
apply: le_trans (inB T _) _; first by rewrite T0 lexx.
by apply: cond_energy_mono => //; exact: ltW.
Qed.

(* The trace slice: a compact convex base of the cone. *)
Definition cond_slice C : set 'M[R]_n :=
  [set Q | cond_cone C Q /\ \tr Q = n%:R].

Lemma cond_slice1 C : 1 <= C -> cond_slice C 1%:M.
Proof. by move=> C1; split; [exact: cond_cone1 | rewrite mxtrace1]. Qed.

(* A matrix of the slice is between t I and C t I for some t in [1/C, 1]. *)
Lemma cond_slice_t C Q : 0 < C -> (0 < n)%N -> cond_slice C Q ->
  exists2 t : R, C^-1 <= t <= 1 &
    forall x : 'cV[R]_n, t * mxdot x x <= mxdot x (Q *m x) <= C * t * mxdot x x.
Proof.
move=> C0 n0 [[Qs QK] trQ].
have [t t0 ht] := (cond_coneP C Qs).1 (conj Qs QK).
have Ssum : \sum_j spec Q 0 j = n%:R by rewrite sum_spec_trace.
have nR : 0 < n%:R :> R by rewrite ltr0n.
have h1 : n%:R * t <= n%:R.
  have St : \sum_(j < n) t = n%:R * t by rewrite sumr_const card_ord mulr_natl.
  rewrite -St -[X in _ <= X]Ssum; apply: ler_sum => j _.
  by case/andP: (ht j).
have h2 : n%:R <= n%:R * (C * t).
  have St : \sum_(j < n) (C * t) = n%:R * (C * t).
    by rewrite sumr_const card_ord mulr_natl.
  rewrite -St -[X in X <= _]Ssum; apply: ler_sum => j _.
  by case/andP: (ht j).
exists t.
  apply/andP; split; last by rewrite -(ler_pM2l nR) mulr1.
  by rewrite -(ler_pM2l C0) mulfV ?gt_eqF // -(ler_pM2l nR) mulr1.
have [P Po QE] := spec_decomposition Qs.
move=> x; apply/andP; split.
  by move: x; apply/(spectral_form_ge t Po QE) => i; case/andP: (ht i).
by move: x; apply/(spectral_form_le (C * t) Po QE) => i; case/andP: (ht i).
Qed.

Lemma cond_slice_spec C Q : 0 < C -> cond_slice C Q ->
  forall i, C^-1 <= spec Q 0 i <= C.
Proof.
move=> C0 [[Qs QK] trQ] i.
have [t t0 ht] := (cond_coneP C Qs).1 (conj Qs QK).
have Ssum : \sum_j spec Q 0 j = n%:R by rewrite sum_spec_trace.
have n0 : (0 < n)%N := leq_ltn_trans (leq0n _) (ltn_ord i).
have nR : 0 < n%:R :> R by rewrite ltr0n.
have h1 : n%:R * t <= n%:R.
  have St : \sum_(j < n) t = n%:R * t by rewrite sumr_const card_ord mulr_natl.
  rewrite -St -[X in _ <= X]Ssum; apply: ler_sum => j _.
  by case/andP: (ht j).
have h2 : n%:R <= n%:R * (C * t).
  have St : \sum_(j < n) (C * t) = n%:R * (C * t).
    by rewrite sumr_const card_ord mulr_natl.
  rewrite -St -[X in X <= _]Ssum; apply: ler_sum => j _.
  by case/andP: (ht j).
have t1 : t <= 1 by rewrite -(ler_pM2l nR) mulr1.
have Ct1 : 1 <= C * t by rewrite -(ler_pM2l nR) mulr1.
case/andP: (ht i) => hti hiC; apply/andP; split.
  by apply: le_trans hti; rewrite -(ler_pM2l C0) mulfV ?gt_eqF.
by apply: le_trans hiC _; rewrite -[X in _ <= X]mulr1 ler_pM2l.
Qed.

Lemma cond_slice_form C Q : 0 < C -> cond_slice C Q ->
  forall x : 'cV[R]_n, C^-1 * mxdot x x <= mxdot x (Q *m x) <= C * mxdot x x.
Proof.
move=> C0 SQ x; have [[Qs _] _] := SQ.
have [P Po QE] := spec_decomposition Qs.
have hi := cond_slice_spec C0 SQ.
apply/andP; split.
  by move: x; apply/(spectral_form_ge _ Po QE) => i; case/andP: (hi i).
by move: x; apply/(spectral_form_le _ Po QE) => i; case/andP: (hi i).
Qed.

Lemma cond_slice_frobenius C Q : 0 < C -> cond_slice C Q ->
  n%:R <= mxdot Q Q <= C * n%:R.
Proof.
move=> C0 SQ; have [[Qs _] trQ] := SQ.
have hi := cond_slice_spec C0 SQ.
have Ssum : \sum_j spec Q 0 j = n%:R by rewrite sum_spec_trace.
rewrite mxdot_spec //; apply/andP; split; last first.
  rewrite -Ssum mulr_sumr; apply: ler_sum => i _; case/andP: (hi i) => h1 h2.
  have l0 : 0 <= spec Q 0 i by apply: le_trans h1; rewrite invr_ge0 ltW.
  by rewrite expr2 ler_wpM2r.
(* Cauchy-Schwarz: (sum_i spec Q 0 i)^2 <= n sum_i spec Q 0 i ^ 2 *)
have cs := sum_cauchy_schwarz (fun=> 1 : R) (fun j => spec Q 0 j).
have e1 : \sum_i 1 * spec Q 0 i = n%:R.
  by under eq_bigr do rewrite mul1r; exact: Ssum.
have e2 : \sum_(i < n) (1 * 1 : R) = n%:R by rewrite mulr1 sumr_const card_ord.
have e3 : \sum_i spec Q 0 i * spec Q 0 i = \sum_i spec Q 0 i ^+ 2.
  by apply: eq_bigr => i _; rewrite expr2.
rewrite e1 e2 e3 in cs.
have [n0|n0] := posnP n.
  by rewrite {1}n0 sumr_ge0 // => i _; exact: sqr_ge0.
have nR : 0 < n%:R :> R by rewrite ltr0n.
by rewrite -(ler_pM2l nR) -expr2.
Qed.

(* Every nonzero point of the cone has a positive multiple in the slice. *)
Lemma cond_cone_slice C Q : cond_cone C Q -> Q != 0 ->
  0 < \tr Q /\ cond_slice C ((n%:R / \tr Q) *: Q).
Proof.
move=> KQ Q0; have [Qs QK] := KQ.
have [t t0 ht] := (cond_coneP C Qs).1 KQ.
have [P Po QE] := spec_decomposition Qs.
have sp0 i : 0 <= spec Q 0 i by apply: le_trans t0 _; case/andP: (ht i).
have trE : \tr Q = \sum_i spec Q 0 i by rewrite sum_spec_trace.
have tr0 : 0 < \tr Q.
  have S0 : 0 <= \sum_i spec Q 0 i by apply: sumr_ge0 => i _; exact: sp0.
  rewrite lt0r trE S0 andbT.
  apply/negP => /eqP /psumr_eq0P h; move/eqP: Q0; apply.
  have h0 := h (fun j _ => sp0 j).
  rewrite QE.
  have -> : spec Q = 0 by apply/rowP => i; rewrite [RHS]mxE; exact: h0.
  by rewrite linear0 mulmx0 mul0mx.
split => //; split.
  by apply: cond_coneZ => //; rewrite divr_ge0 // ltW.
by rewrite mxtraceZ mulfVK // gt_eqF.
Qed.

(* The slice in the coordinates of mxvec. *)
Definition cond_slice_vec C : set 'rV[R]_(n * n) :=
  [set v | cond_slice C (vec_mx v)].

Lemma cond_slice_vec_closed C : 0 <= C -> closed (cond_slice_vec C).
Proof.
move=> C0.
have trE v : \tr (vec_mx v) = mxdot v (mxvec (1%:M : 'M[R]_n)).
  by rewrite mxdotC -mxdot_vec_mxr mxdotC mxdot_trace trmx1 mulmx1.
have -> : cond_slice_vec C = cond_cone_vec C `&`
    ([set v | n%:R <= mxdot v (mxvec (1%:M : 'M[R]_n))] `&`
     [set v | mxdot v (mxvec (1%:M : 'M[R]_n)) <= n%:R]).
  apply/seteqP; split => v.
    by move=> [Kv trv]; split => //; rewrite /= -trE trv lexx.
  move=> [Kv [/= h1 h2]]; split => //.
  by rewrite trE; apply/eqP; rewrite eq_le h1 h2.
apply: closedI; first exact: cond_cone_vec_closed.
apply: closedI.
  exact: ((continuous_closedP
    (fun v : 'rV[R]_(n * n) => mxdot v (mxvec (1%:M : 'M[R]_n)))).1
    (@continuous_mxdotv _) _ (@closed_ge R _)).
exact: ((continuous_closedP
  (fun v : 'rV[R]_(n * n) => mxdot v (mxvec (1%:M : 'M[R]_n)))).1
  (@continuous_mxdotv _) _ (@closed_le R _)).
Qed.

Lemma cond_slice_vec_convex C (x y : 'rV[R]_(n * n)) (s : R) :
  cond_slice_vec C x -> cond_slice_vec C y -> 0 <= s <= 1 ->
  cond_slice_vec C (x + s *: (y - x)).
Proof.
move=> [Kx trx] [Ky try] s01; split; first exact: cond_cone_vec_convex.
rewrite linearD /= linearZ /= linearB /= mxtraceD mxtraceZ raddfB /=.
by rewrite trx try subrr mulr0 addr0.
Qed.

Lemma cond_slice_vec_frobenius C (v : 'rV[R]_(n * n)) : 0 < C ->
  cond_slice_vec C v -> n%:R <= mxdot v v <= C * n%:R.
Proof.
by move=> C0 Sv; rewrite -mxdot_vec_mx; exact: cond_slice_frobenius.
Qed.

Lemma cond_cone_vec_slice C (v : 'rV[R]_(n * n)) :
  cond_cone_vec C v -> v != 0 ->
  exists2 a : R, 0 < a & cond_slice_vec C (a *: v).
Proof.
move=> Kv v0.
have Q0 : vec_mx v != 0.
  by apply: contra v0 => /eqP h; apply/eqP; rewrite -[v]vec_mxK h linear0.
have [tr0 S] := cond_cone_slice Kv Q0.
have [n0|n0] := posnP n.
  exfalso; move/eqP: v0; apply; apply/rowP => i.
  by exfalso; case: i => k; rewrite n0.
exists (n%:R / \tr (vec_mx v)); first by rewrite divr_gt0 // ltr0n.
by rewrite /cond_slice_vec /= linearZ.
Qed.

End condition_cone.
