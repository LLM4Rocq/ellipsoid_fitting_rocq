From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import interval boolp classical_sets functions reals.
From mathcomp Require Import set_interval topology normedtype derive realfun.
From mathcomp Require Import exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import euclidean real_spectral measurable_matrix.
From GaussianAnalysis Require Import self_concordant logdet_barrier.
From GaussianAnalysis Require Import least_squares.

(**md**************************************************************************)
(* # Minimizers of least squares objectives with a barrier                    *)
(*                                                                            *)
(* The convex analysis that the Lindeberg argument of Koehler and Sohn        *)
(* (arXiv 2608.27372, Theorem 2.9) needs, for the objective                   *)
(*   F(theta, b) = s sum_(i in P) (b - <Z_i, theta>)^2                        *)
(*                 + beta (lambda |theta|^2 + b^2) + gamma B theta            *)
(* on D x R (ls_barrier_objective of least_squares.v), where D is relatively  *)
(* open and convex with directions V (rel_open_convex), B >= 0 is a           *)
(* self-concordant function on D (sc_function), s >= 0 and lambda, beta,      *)
(* gamma > 0. D need not be bounded: the ridge term makes F coercive.         *)
(*                                                                            *)
(* ```                                                                        *)
(*      ls_grad Z P s lambda beta theta b h c == the first variation of the   *)
(*                      ridge objective at (theta, b) in the direction (h, c) *)
(*         ls_bopt Z P s beta theta == the b that minimizes the ridge         *)
(*                      objective for a fixed theta                           *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - vspace_orthonormal: every subspace V of 'rV[R]_N is the row space of a   *)
(*   matrix E with orthonormal rows (E E^T = I, of \dim V rows);              *)
(*   closed_vspace: V is closed.                                              *)
(* - rel_open_convex_closure: for z in D and y in the closure of D, y - z is  *)
(*   in V and z + t (y - z) is in D for 0 <= t < 1.                           *)
(* - sc_sublevel_closed, sc_minimizer: for g continuous, convex on D and      *)
(*   nonnegative, the sublevel sets of g + gamma B in D are closed (the       *)
(*   barrier tends to +oo at the relative boundary); if moreover              *)
(*   g z >= kappa |z|^2 with kappa > 0, then g + gamma B attains its          *)
(*   minimum on D.                                                            *)
(* - ls_barrier_minimizer: F attains its minimum on D x R.                    *)
(* - ls_first_order: at a minimizer (theta, b), the derivative of F along     *)
(*   every direction (h, c) of V x R is 0.                                    *)
(* - ls_taylor (paper, (2.17)-(2.18)): at a minimizer, for h in V,            *)
(*   F (theta + h) (b + c) - F theta b = ridge(h, c)                          *)
(*     + gamma bregman_div B (theta + h) theta,                               *)
(*   ridge being the quadratic part of F.                                     *)
(* - quad_response (paper, (2.19)): for H symmetric positive definite, a row  *)
(*   vector a and nn > 0, the infimum over u of                               *)
(*   u H u^T / 2 + (r + <a, u>)^2 / (2 nn) is r^2 / (2 (nn + l)) with         *)
(*   l = a H^-1 a^T, attained at u0 = - (r / (nn + l)) a H^-1, where          *)
(*   u0 H u0^T = l r^2 / (nn + l)^2; and 2 <a, u> - u H u^T <= l for all u.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section orthonormal_basis.
Context {R : realType} {N : nat}.

(* A subspace V of 'rV[R]_N is the row space of a matrix with orthonormal
   rows: the basis vbasis V made orthonormal by G^(-1/2), G its Gram
   matrix. *)
Lemma vspace_orthonormal (V : {vspace 'rV[R]_N}) :
  exists E : 'M[R]_(\dim V, N),
    E *m E^T = 1%:M /\ forall v, v \in V <-> exists y, v = y *m E.
Proof.
set k := \dim V.
pose E0 : 'M[R]_(k, N) := \matrix_(i < k) (vbasis V)`_i.
have rowE0 i : row i E0 = (vbasis V)`_i by rewrite rowK.
have E0sum (y : 'rV[R]_k) : y *m E0 = \sum_i y 0 i *: (vbasis V)`_i.
  by rewrite mulmx_sum_row; apply: eq_bigr => i _; rewrite rowE0.
have E0V (y : 'rV[R]_k) : y *m E0 \in V.
  rewrite E0sum; apply: memv_suml => i _; apply: memvZ; apply: vbasis_mem.
  by apply: mem_nth; rewrite size_tuple.
have E0free (y : 'rV[R]_k) : y *m E0 = 0 -> y = 0.
  move=> y0; apply/rowP => i; rewrite mxE.
  have := (freeP (basis_free (vbasisP V))) (fun i => y 0 i).
  by rewrite -E0sum => /(_ y0 i).
(* the Gram matrix G0 of the basis is positive definite *)
pose G0 := E0 *m E0^T.
have G0pd : posdefmx G0.
  split; first by apply/symmetricmxP; rewrite /G0 trmx_mul trmxK.
  move=> y y0; rewrite /G0 mulmxA mxdotC mxdot_mulmxr trmxK mxdot_gt0.
  by apply: contra y0 => /eqP /E0free ->.
have [P Po [d G0E dpos]] := posdefmx_spectral G0pd.
have PP : P *m P^T = 1%:M by apply/orthogonalmxP.
have PtP : P^T *m P = 1%:M by exact: orthogonalmxT.
have sd0 i : Num.sqrt (d 0 i) != 0 by rewrite sqrtr_eq0 -ltNge dpos.
pose M := P^T *m diag_mx (\row_i (Num.sqrt (d 0 i))^-1) *m P.
pose Mi := P^T *m diag_mx (\row_i Num.sqrt (d 0 i)) *m P.
have diag1 (c : 'rV[R]_k) : (forall i, c 0 i = 1) -> diag_mx c = 1%:M.
  move=> c1; apply/matrixP => i j; rewrite !mxE c1.
  by case: (i == j).
have MiM : Mi *m M = 1%:M.
  rewrite /Mi /M !mulmxA -(mulmxA _ P) PP mulmx1 -(mulmxA _ (diag_mx _)).
  rewrite !mulmxA -(mulmxA P^T) mulmx_diag diag1 ?mulmx1 ?PtP // => i.
  by rewrite !mxE mulfV.
exists (M *m E0); split.
  have MT : M^T = M by rewrite /M !trmx_mul trmxK tr_diag_mx mulmxA.
  rewrite trmx_mul MT mulmxA -(mulmxA M E0) -/G0 G0E /M.
  rewrite !mulmxA -(mulmxA _ P P^T) PP mulmx1 -(mulmxA _ P P^T) PP mulmx1.
  rewrite -(mulmxA P^T) mulmx_diag -(mulmxA P^T) mulmx_diag.
  rewrite diag1 ?mulmx1 ?PtP // => i.
  rewrite !mxE -{2}(sqr_sqrtr (ltW (dpos i))) expr2.
  by field; exact: sd0.
move=> v; split => [vV|[y ->]]; last by rewrite mulmxA; exact: E0V.
exists ((\row_i coord (vbasis V) i v) *m Mi).
rewrite -mulmxA (mulmxA Mi) MiM mul1mx E0sum {1}(coord_vbasis vV).
by apply: eq_bigr => i _; rewrite mxE.
Qed.

End orthonormal_basis.

Section sublevel.
Context {R : realType} {N : nat}.
Implicit Types (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N).

Lemma closed_vspace V : closed [set v : 'rV[R]_N | v \in V].
Proof.
have [E [EE EV]] := vspace_orthonormal V.
have -> : [set v : 'rV[R]_N | v \in V] =
    (fun v : 'rV[R]_N => v *m (E^T *m E) - v) @^-1` [set 0].
  apply/seteqP; split => v /=.
    by move=> /EV [y ->]; rewrite !mulmxA -(mulmxA y) EE mulmx1 subrr.
  move=> /eqP; rewrite subr_eq0 => /eqP <-; apply/EV.
  by exists (v *m E^T); rewrite mulmxA.
apply: preimage_closed.
  move=> v _; apply: (continuousB (f := fun v : 'rV[R]_N => v *m (E^T *m E))
    (g := id)); [exact: continuous_mulmxr | exact: cvg_id].
exact: (accessible_closed_set1 (hausdorff_accessible (@norm_hausdorff _ _))).
Qed.

(* The points of the closure of D are in z + V, and the segment from a
   point of D to them stays in D up to its end. *)
Lemma rel_open_convex_closure V D z y : rel_open_convex V D -> D z ->
  closure D y ->
  y - z \in V /\ forall t : R, 0 <= t < 1 -> D (z + t *: (y - z)).
Proof.
move=> [cvx dir op] Dz Dy.
have yzV : y - z \in V.
  have cl : closed [set w : 'rV[R]_N | w - z \in V].
    apply: (preimage_closed (f := fun w : 'rV[R]_N => w - z)
      (D := [set v | v \in V])); last exact: closed_vspace.
    by move=> w _; exact: (continuousD (@cvg_id _ _) (cvg_cst _)).
  apply: cl; apply: closureS Dy => w Dw; exact: dir.
split => // t /andP[t0 t1].
have [e e0 he] := op z Dz.
have t1' : 0 < 1 - t by rewrite subr_gt0.
have tp : 0 < t + 1 by rewrite ltr_wpDl.
(* y is the limit of points w of D; z + t (y - z) = q + t (w - q) with
   q = z + t / (1 - t) (y - w) in D *)
pose eps := e * (1 - t) / (t + 1).
have eps0 : 0 < eps by rewrite /eps divr_gt0 // mulr_gt0.
have nb : nbhs y [set w | `|y - w| < eps].
  by apply/(@nbhs_normP R 'rV[R]_N y); exists eps.
have [w [Dw yw]] := Dy _ nb.
have ywV : y - w \in V.
  have -> : y - w = (y - z) - (w - z) by rewrite opprB addrA subrK.
  by apply: rpredB => //; exact: dir.
pose q := z + (t / (1 - t)) *: (y - w).
have Dq : D q.
  apply: he; first exact: memvZ.
  rewrite normrZ ger0_norm ?divr_ge0 ?(ltW t1') //.
  have hle : t / (1 - t) * `|y - w| <= t / (1 - t) * eps.
    by apply: ler_wpM2l; [rewrite divr_ge0 // ltW | exact: ltW].
  apply: le_lt_trans hle _; rewrite /eps.
  have t1'' : 1 - t != 0 by rewrite gt_eqF.
  have tp' : t + 1 != 0 by rewrite gt_eqF.
  have -> : t / (1 - t) * (e * (1 - t) / (t + 1)) = e * (t / (t + 1)).
    by field.
  by rewrite gtr_pMr // ltr_pdivrMr // mul1r ltrDl ltr01.
have tt : 0 <= t <= 1 by rewrite t0 ltW.
have := cvx q w t Dq Dw tt.
have -> // : q + t *: (w - q) = z + t *: (y - z).
apply/rowP => j; rewrite !mxE /q.
have t1'' : 1 - t != 0 by rewrite gt_eqF.
by field.
Qed.

(* If B is a self-concordant function on D and g is continuous and convex
   on D, then the sublevel sets of g + gamma B in D are closed. *)
Lemma sc_sublevel_closed V D (B g : 'rV[R]_N -> R) (gamma c : R) :
  rel_open_convex V D -> sc_function V D B -> 0 < gamma -> continuous g ->
  (forall z y (t : R), D z -> D y -> 0 <= t <= 1 ->
     g (z + t *: (y - z)) <= (1 - t) * g z + t * g y) ->
  (forall z, D z -> 0 <= B z) -> (forall z, 0 <= g z) ->
  closed [set z | D z /\ g z + gamma * B z <= c].
Proof.
move=> DV scB g0 gc gcvx B0 gnn y Sy.
set S := [set z | D z /\ g z + gamma * B z <= c] in Sy *.
set f := fun z => g z + gamma * B z.
(* f is continuous at the points of D, for the points of D *)
have lsc p : D p -> forall e : R, 0 < e ->
    exists2 dl : R, 0 < dl & forall w, D w -> `|w - p| < dl -> f p < f w + e.
  move=> Dp e e0.
  have e2 : 0 < e / 2 by rewrite divr_gt0.
  have [d1 d10 hd1] := sc_function_continuous DV scB Dp (divr_gt0 e2 g0).
  have := gc p; move=> /cvgrPdist_lt /(_ _ e2).
  move=> /(@nbhs_normP R 'rV[R]_N p) [d2 d20 hd2].
  exists (Num.min d1 d2); first by rewrite lt_min d10 d20.
  move=> w Dw; rewrite lt_min => /andP[w1 w2].
  have := hd1 w Dw w1; rewrite ltr_pdivlMr // => hB.
  have := hd2 w; rewrite /ball_ /= distrC => /(_ w2) hg.
  have n1 : gamma * (B p - B w) <= `|B w - B p| * gamma.
    by rewrite mulrC ler_wpM2r ?(ltW g0) // distrC ler_norm.
  have n2 : g p - g w <= `|g p - g w| := ler_norm _.
  by rewrite /f; lra.
have le_lim p : D p -> closure S p -> f p <= c.
  move=> Dp Sp; rewrite leNgt; apply/negP => cp.
  have e0 : 0 < f p - c by rewrite subr_gt0.
  have [dl dl0 hdl] := lsc p Dp _ e0.
  have nb : nbhs p [set w | `|p - w| < dl].
    by apply/(@nbhs_normP R 'rV[R]_N p); exists dl.
  have [w [[Dw wc] pw]] := Sp _ nb.
  move: pw; rewrite /= distrC => pw.
  by have := hdl w Dw pw; rewrite /f in wc *; lra.
have [z0 [Dz0 z0c]] : exists z0, S z0.
  by have [z0 [Sz0 _]] := Sy setT filterT; exists z0.
have Dcl : closure D y.
  by apply: closureS Sy => z [].
have [yzV seg] := rel_open_convex_closure DV Dz0 Dcl.
(* f <= c on the segment from z0 to y, by convexity and continuity *)
have segS t : 0 <= t < 1 -> f (z0 + t *: (y - z0)) <= c.
  move=> /andP[t0 t1]; apply: le_lim; first by apply: seg; rewrite t0 t1.
  move=> U /(@nbhs_normP R 'rV[R]_N) [dl dl0 hU].
  have nb : nbhs y [set w | `|y - w| < dl].
    by apply/(@nbhs_normP R 'rV[R]_N y); exists dl.
  have [w [[Dw wc] yw]] := Sy _ nb.
  have tt : 0 <= t <= 1 by rewrite t0 ltW.
  exists (z0 + t *: (w - z0)); split.
    split; first by have [cvx _ _] := DV; exact: cvx.
    have hg := gcvx z0 w t Dz0 Dw tt.
    have hB := sc_function_convex DV scB Dz0 Dw tt.
    have := ler_wpM2l (ltW g0) hB.
    by move: z0c wc; rewrite /f; nra.
  apply: hU; move: yw; rewrite /ball_ /= => yw.
  have -> : z0 + t *: (y - z0) - (z0 + t *: (w - z0)) = t *: (y - w).
    by apply/rowP => j; rewrite !mxE; ring.
  rewrite normrZ ger0_norm //; apply: le_lt_trans yw.
  by rewrite ler_piMl ?normr_ge0 // ltW.
(* so B is bounded on the segment, which excludes the blow-up at y *)
have Dy : D y.
  apply: contrapT => nDy.
  have [_ _ _ _ bar] := scB.
  have nD : ~ D (z0 + (y - z0)) by rewrite addrC subrK.
  have hb := bar z0 (y - z0) Dz0 yzV seg nD.
  move/cvgryPgt: hb => /(_ (c / gamma)) hM.
  have PF := at_left_proper_filter (1 : R).
  have := filterI hM (filterI (nbhs_left_gt ltr01) (nbhs_left_lt (1 : R))).
  move=> /(_ PF PF) hF.
  have [s [Ms [s0 s1]]] := @filter_ex _ _ PF _ hF.
  have := segS s; rewrite (ltW s0) s1 => /(_ isT).
  rewrite /f => fs; move: Ms; rewrite ltr_pdivrMr //.
  by have := gnn (z0 + s *: (y - z0)); rewrite mulrC; lra.
by split => //; apply: le_lim.
Qed.

(* Existence of a minimizer of g + gamma B on D, for g continuous, convex
   on D and coercive, and B >= 0 a self-concordant function on D. *)
Lemma sc_minimizer V D (B g : 'rV[R]_N -> R) (gamma kappa : R) :
  rel_open_convex V D -> sc_function V D B -> 0 < gamma -> 0 < kappa ->
  continuous g ->
  (forall z y (t : R), D z -> D y -> 0 <= t <= 1 ->
     g (z + t *: (y - z)) <= (1 - t) * g z + t * g y) ->
  (forall z, D z -> 0 <= B z) -> (forall z, kappa * mxdot z z <= g z) ->
  D !=set0 ->
  exists2 zm, D zm & forall z, D z -> g zm + gamma * B zm <= g z + gamma * B z.
Proof.
move=> DV scB g0 k0 gc gcvx B0 gk [z0 Dz0].
(* the sublevel set S of z0 is compact, and g + gamma B is continuous on it *)
pose c := g z0 + gamma * B z0.
pose S := [set z | D z /\ g z + gamma * B z <= c].
have gnn z : 0 <= g z.
  by apply: le_trans (gk z); rewrite mulr_ge0 ?mxdot_ge0 ?ltW.
have Scl : closed S := sc_sublevel_closed (c := c) DV scB g0 gc gcvx B0 gnn.
have Sb : bounded_set S.
  exists (Num.sqrt (c / kappa)); split; first exact: num_real.
  move=> M cM z [Dz zc]; apply: le_trans (ltW cM).
  rewrite [leLHS]/Num.Def.normr /= (le_trans (mx_norm_le_frobenius z)) //.
  rewrite /frobenius ler_wsqrtr // ler_pdivlMr // mulrC.
  apply: le_trans (gk z) _; apply: le_trans zc.
  by rewrite lerDl mulr_ge0 ?B0 ?ltW.
have Sc : compact S := bounded_closed_compact Sb Scl.
have S0 : S !=set0 by exists z0; split.
have fc : {within S, continuous (fun z => g z + gamma * B z)}.
  apply/subspace_continuousP => p [Dp _].
  apply/cvgrPdist_lt => e e0.
  have e2 : 0 < e / 2 by rewrite divr_gt0.
  have [d1 d10 hd1] := sc_function_continuous DV scB Dp (divr_gt0 e2 g0).
  have := gc p; move=> /cvgrPdist_lt /(_ _ e2).
  move=> /(@nbhs_normP R 'rV[R]_N p) [d2 d20 hd2].
  rewrite near_withinE; apply/(@nbhs_normP R 'rV[R]_N p).
  exists (Num.min d1 d2); first by rewrite /= lt_min d10 d20.
  move=> w /=; rewrite /ball_ /= lt_min => /andP[w1 w2] [Dw _].
  have := hd1 w Dw; rewrite distrC => /(_ w1); rewrite ltr_pdivlMr // => hB.
  have := hd2 w w2 => hg.
  rewrite /from_subspace opprD addrACA -mulrBr.
  apply: le_lt_trans (ler_normD _ _) _.
  rewrite normrM gtr0_norm // -normrN opprB.
  by move: hB hg; rewrite [`|B w - _|]distrC [`|g p - _|]distrC mulrC; lra.
have [zm Szm hzm] := EVT_min_rV S0 Sc fc.
move: Szm; rewrite inE => -[Dzm zmc].
exists zm => // z Dz.
have [zc|zc] := leP (g z + gamma * B z) c.
  by apply: hzm; rewrite inE.
by apply: le_trans zmc (ltW zc).
Qed.

End sublevel.

Section ls_expansion.
Context {R : realType} {N : nat}.
Variables (n : nat) (Z : n.-tuple 'rV[R]_N) (P : pred 'I_n).
Variables (s lambda beta : R).

(* The first variation of the ridge least squares objective at (theta, b)
   in the direction (h, c). *)
Definition ls_grad (theta : 'rV[R]_N) (b : R) (h : 'rV[R]_N) (c : R) : R :=
  2 * s * \sum_(i < n | P i)
    (b - mxdot (tnth Z i) theta) * (c - mxdot (tnth Z i) h) +
  2 * beta * (lambda * mxdot theta h + b * c).

(* The objective is quadratic: its expansion along a line is exact. *)
Lemma ls_ridge_expand (t : R) theta b h c :
  ls_ridge Z P s lambda beta (theta + t *: h) (b + t * c) =
  ls_ridge Z P s lambda beta theta b + t * ls_grad theta b h c +
  t ^+ 2 * ls_ridge Z P s lambda beta h c.
Proof.
rewrite /ls_ridge /ls_grad /ls_loss.
have E i : (b + t * c - mxdot (tnth Z i) (theta + t *: h)) ^+ 2 =
    (b - mxdot (tnth Z i) theta) ^+ 2 +
    t * (2 * ((b - mxdot (tnth Z i) theta) * (c - mxdot (tnth Z i) h))) +
    t ^+ 2 * (c - mxdot (tnth Z i) h) ^+ 2.
  by rewrite mxdotDr mxdotZr; ring.
under eq_bigr do rewrite E.
rewrite !big_split /= -!mulr_sumr.
rewrite mxdotDl !mxdotDr !mxdotZl !mxdotZr [mxdot h theta]mxdotC.
move: (\sum_(i < n | P i) _) (\sum_(i < n | P i) _) (\sum_(i < n | P i) _).
by move=> S1 S2 S3; ring.
Qed.

Definition ls_bopt (theta : 'rV[R]_N) : R :=
  s * (\sum_(i < n | P i) mxdot (tnth Z i) theta) / (s * #|P|%:R + beta).

Lemma ls_ridge_bopt theta b : 0 <= s -> 0 < beta ->
  ls_ridge Z P s lambda beta theta b =
  ls_ridge Z P s lambda beta theta (ls_bopt theta) +
  (s * #|P|%:R + beta) * (b - ls_bopt theta) ^+ 2.
Proof.
move=> s0 b0.
have A0 : 0 < s * #|P|%:R + beta by rewrite ltr_wpDl // mulr_ge0.
have A0' : s * #|P|%:R + beta != 0 by rewrite gt_eqF.
set b' := ls_bopt theta.
have hb' : (s * #|P|%:R + beta) * b' =
    s * \sum_(i < n | P i) mxdot (tnth Z i) theta.
  by rewrite /b' /ls_bopt; field.
have := ls_ridge_expand 1 theta b' 0 (b - b').
rewrite scale1r addr0 mul1r addrC subrK expr1n mul1r => ->.
congr (_ + _).
  (* the first variation vanishes at b' *)
  rewrite /ls_grad /ls_ridge /ls_loss.
  rewrite -[RHS]addr0; congr (_ + _).
  under eq_bigr do rewrite mxdot0r subr0.
  rewrite mxdot0r mulr0 add0r -mulr_suml sumrB sumr_const.
  move: hb'; move: (\sum_(i | P i) _) => S hb'.
  rewrite -[b' *+ #|P|]mulr_natr; move: hb'; move: (#|P|%:R : R) => k hb'.
  have -> : 2 * s * ((b' * k - S) * (b - b')) + 2 * beta * (b' * (b - b')) =
      2 * (b - b') * ((s * k + beta) * b' - s * S) by ring.
  by rewrite hb' subrr mulr0.
rewrite /ls_ridge /ls_loss mxdot0r mulr0 add0r.
under eq_bigr do rewrite mxdot0r subr0.
by rewrite sumr_const -[_ *+ #|P|]mulr_natr; ring.
Qed.

End ls_expansion.

Section ls_minimizer.
Context {R : realType} {N : nat}.
Variables (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) (B : 'rV[R]_N -> R).
Variables (n : nat) (Z : n.-tuple 'rV[R]_N) (P : pred 'I_n).
Variables (s lambda beta gamma : R).
Hypotheses (DV : rel_open_convex V D) (scB : sc_function V D B).
Hypotheses (B0 : forall z, D z -> 0 <= B z).
Hypotheses (s0 : 0 <= s) (l0 : 0 < lambda) (b0 : 0 < beta) (g0 : 0 < gamma).

Local Notation ridge := (ls_ridge Z P s lambda beta).
Local Notation F := (ls_barrier_objective Z P s lambda beta gamma B).
Local Notation bopt := (ls_bopt Z P s beta).
Local Notation grad := (ls_grad Z P s lambda beta).

Lemma ls_ridge_ge0 theta b : 0 <= ridge theta b.
Proof.
rewrite /ls_ridge; apply: addr_ge0.
  by apply: mulr_ge0 => //; apply: sumr_ge0 => i _; exact: sqr_ge0.
by apply: mulr_ge0 (ltW b0) _; apply: addr_ge0 (sqr_ge0 _);
  rewrite mulr_ge0 ?mxdot_ge0 ?ltW.
Qed.

Lemma ls_ridge_coercive theta b :
  beta * lambda * mxdot theta theta <= ridge theta b.
Proof.
rewrite /ls_ridge -mulrA; apply: ler_wpDl.
  by apply: mulr_ge0 => //; apply: sumr_ge0 => i _; exact: sqr_ge0.
by rewrite ler_wpM2l ?(ltW b0) // lerDl sqr_ge0.
Qed.

Lemma ls_bopt_linear (c : R) (u v : 'rV[R]_N) :
  bopt (c *: u + v) = c * bopt u + bopt v.
Proof.
rewrite /ls_bopt.
under eq_bigr do rewrite mxdotDr mxdotZr.
by rewrite big_split /= -mulr_sumr; ring.
Qed.

(* The reduced objective theta |-> ridge theta (bopt theta) is a quadratic
   form, hence continuous. *)
Lemma continuous_ls_reduced :
  continuous (fun theta => ridge theta (bopt theta)).
Proof.
pose Q (u v : 'rV[R]_N) := s * \sum_(i < n | P i)
    (bopt u - mxdot (tnth Z i) u) * (bopt v - mxdot (tnth Z i) v) +
  beta * (lambda * mxdot u v + bopt u * bopt v).
have Q1 (c : R) (u v w : 'rV[R]_N) : Q (c *: u + v) w = c * Q u w + Q v w.
  rewrite /Q ls_bopt_linear mxdotDl mxdotZl.
  have E i : (c * bopt u + bopt v - mxdot (tnth Z i) (c *: u + v)) *
      (bopt w - mxdot (tnth Z i) w) =
    c * ((bopt u - mxdot (tnth Z i) u) * (bopt w - mxdot (tnth Z i) w)) +
    (bopt v - mxdot (tnth Z i) v) * (bopt w - mxdot (tnth Z i) w).
    by rewrite mxdotDr mxdotZr; ring.
  under eq_bigr do rewrite E.
  rewrite big_split /= -mulr_sumr.
  move: (\sum_(i < n | P i) _) (\sum_(i < n | P i) _) => S1 S2.
  by ring.
have Qs u v : Q u v = Q v u.
  rewrite /Q mxdotC [bopt u * _]mulrC; congr (s * _ + _).
  by apply: eq_bigr => i _; rewrite mulrC.
have Q2 (c : R) (u v w : 'rV[R]_N) : Q w (c *: u + v) = c * Q w u + Q w v.
  by rewrite Qs Q1 (Qs u) (Qs v).
have -> : (fun theta => ridge theta (bopt theta)) =
    (fun theta => (theta *m (\matrix_(i, j) Q (delta_mx 0 i) (delta_mx 0 j))^T
                   *m theta^T) 0 0).
  apply/funext => theta.
  rewrite -mulmxA -trmx_mul -mxdot_rowE -(bilin_form_mx Q1 Q2) /Q /ls_ridge.
  by rewrite /ls_loss -expr2; congr (s * _ + beta * (_ + _)).
exact: continuous_form.
Qed.

Lemma convex_ls_reduced z y (t : R) : 0 <= t <= 1 ->
  ridge (z + t *: (y - z)) (bopt (z + t *: (y - z))) <=
  (1 - t) * ridge z (bopt z) + t * ridge y (bopt y).
Proof.
move=> /andP[t0 t1].
set bz := bopt z; set by_ := bopt y.
apply: le_trans (_ : ridge (z + t *: (y - z)) (bz + t * (by_ - bz)) <= _).
  rewrite [X in _ <= X]ls_ridge_bopt //.
  by rewrite lerDl mulr_ge0 ?sqr_ge0 // addr_ge0 ?mulr_ge0 // ltW.
rewrite ls_ridge_expand.
have := ls_ridge_expand Z P s lambda beta 1 z bz (y - z) (by_ - bz).
rewrite scale1r mul1r expr1n mul1r addrC subrK addrC subrK => ->.
have := ls_ridge_ge0 (y - z) (by_ - bz).
move: (ridge z bz) (grad z bz (y - z) (by_ - bz)) (ridge (y - z) (by_ - bz)).
move=> a b c c0; rewrite mul1r.
have : 0 <= t * (1 - t) * c by rewrite mulr_ge0 // mulr_ge0 // subr_ge0.
by rewrite expr2; nra.
Qed.

(* Existence of a minimizer of the objective on D x R. *)
Lemma ls_barrier_minimizer : D !=set0 ->
  exists theta : 'rV[R]_N, exists b : R,
    D theta /\ forall theta' b', D theta' -> F theta b <= F theta' b'.
Proof.
move=> D0.
have k0 : 0 < beta * lambda by rewrite mulr_gt0.
have := @sc_minimizer R N V D B (fun theta => ridge theta (bopt theta)) gamma
  (beta * lambda) DV scB g0 k0 continuous_ls_reduced.
move=> /(_ _ B0 _ D0) [].
- by move=> z y t _ _ tt; exact: convex_ls_reduced.
- by move=> z; exact: ls_ridge_coercive.
move=> zm Dzm hzm; exists zm, (bopt zm); split => // theta' b' Dt.
apply: le_trans (hzm theta' Dt) _; rewrite /ls_barrier_objective lerD2r.
rewrite [X in _ <= X]ls_ridge_bopt //.
by rewrite lerDl mulr_ge0 ?sqr_ge0 // addr_ge0 ?mulr_ge0 // ltW.
Qed.

Section at_minimizer.
Variables (theta : 'rV[R]_N) (b : R).
Hypotheses (Dtheta : D theta)
  (thmin : forall theta' b', D theta' -> F theta b <= F theta' b').

(* The first order condition. *)
Lemma ls_first_order h c : h \in V ->
  grad theta b h c + gamma * 'D_h B theta = 0.
Proof.
move=> hV.
have [e e0 De] := rel_open_convex_line DV Dtheta hV.
pose phi t := F (theta + t *: h) (b + t * c).
have phiE : phi = fun t => ridge theta b + t * grad theta b h c +
    t ^+ 2 * ridge h c + gamma * B (theta + t *: h).
  by apply/funext => t; rewrite /phi /ls_barrier_objective ls_ridge_expand.
have dphi (t : R) : `|t| < e -> is_derive t 1 phi
    (grad theta b h c + 2 * t * ridge h c + gamma * 'D_h B (theta + t *: h)).
  move=> te.
  have [sd _ _ _ _] := scB.
  have [dB _ _] := sd _ _ (De t te) hV.
  have dl : is_derive t 1 (fun s => B (theta + s *: h))
      ('D_h B (theta + t *: h)) by exact: is_derive_line.
  rewrite phiE; apply: is_derive_eq.
  by rewrite add0r mul1r !scaler0 !add0r /GRing.scale /=; ring.
(* phi has a minimum at 0, so its derivative there is 0 *)
have ee : - e <= e by have := ltW e0; lra.
have inI t : t \in `]- e, e[ -> `|t| < e.
  by rewrite in_itv /= => /andP[t1 t2]; rewrite ltr_norml t1 t2.
have dmin := @derive1_at_min R phi (- e) e 0 ee
  (fun t tI => let: DeriveDef d _ := dphi t (inI t tI) in d).
have d0 : is_derive (0 : R) 1 phi 0.
  apply: dmin; first by rewrite in_itv /= oppr_lt0 e0.
  move=> t tI; rewrite /phi scale0r addr0 mul0r addr0.
  by apply: thmin; apply: De; exact: inI.
have e00 : `|0 : R| < e by rewrite normr0.
have [_ v0] := d0.
have [_ v1] := dphi 0 e00.
by move: v1; rewrite v0 mulr0 mul0r addr0 scale0r addr0 => /esym.
Qed.

(* Taylor's formula at the minimizer: the objective is quadratic up to
   the Bregman divergence of the barrier (paper, (2.17)-(2.18)). *)
Lemma ls_taylor h c : h \in V ->
  F (theta + h) (b + c) - F theta b =
  ridge h c + gamma * bregman_div B (theta + h) theta.
Proof.
move=> hV; have fo := ls_first_order c hV.
have := ls_ridge_expand Z P s lambda beta 1 theta b h c.
rewrite scale1r mul1r expr1n mul1r => E.
rewrite /ls_barrier_objective E /bregman_div.
have -> : theta + h - theta = h by rewrite addrAC subrr add0r.
have -> : grad theta b h c = - (gamma * 'D_h B theta).
  by apply/eqP; rewrite -addr_eq0 fo.
by ring.
Qed.

End at_minimizer.

End ls_minimizer.

Section quadratic_response.
Context {R : realType} {k : nat}.
Implicit Types (H : 'M[R]_k) (a u v w : 'rV[R]_k).

Lemma posdefmx_unit H : posdefmx H -> H \in unitmx.
Proof.
move=> Hpd; have [P Po [d HE dpos]] := posdefmx_spectral Hpd.
have PtP : P^T *m P = 1%:M by exact: orthogonalmxT.
have dP : \det P ^+ 2 = 1.
  by rewrite expr2 -{1}det_tr -det_mulmx PtP det1.
rewrite unitmxE HE det_congruence dP mul1r unitfE.
have [p0 _] := ln_prod dpos.
by rewrite gt_eqF.
Qed.

(* For H symmetric positive definite, a row vector a and nn > 0, the
   quadratic problem inf_u { u H u^T / 2 + (r + <a, u>)^2 / (2 nn) } has
   value r^2 / (2 (nn + l)), l = a H^-1 a^T, attained at
   u0 = - (r / (nn + l)) a H^-1 (paper, (2.19)); and
   l = sup_u (2 <a, u> - u H u^T). *)
Lemma quad_response H a (r nn : R) : posdefmx H -> 0 < nn ->
  let l := mxdot a (a *m invmx H) in
  let u0 := (- (r / (nn + l))) *: (a *m invmx H) in
  [/\ 0 <= l, forall u, 2 * mxdot a u - mxdot u (u *m H) <= l,
      forall u, r ^+ 2 / (2 * (nn + l)) <=
        mxdot u (u *m H) / 2 + (r + mxdot a u) ^+ 2 / (2 * nn),
      mxdot u0 (u0 *m H) / 2 + (r + mxdot a u0) ^+ 2 / (2 * nn) =
        r ^+ 2 / (2 * (nn + l)) &
      mxdot u0 (u0 *m H) = l * r ^+ 2 / (nn + l) ^+ 2].
Proof.
move=> Hpd nn0 l u0.
have [Hs Hp] := Hpd.
have HT : H^T = H by apply/symmetricmxP.
have Hu := posdefmx_unit Hpd.
pose G := invmx H.
have GH : G *m H = 1%:M by rewrite mulVmx.
have HG : H *m G = 1%:M by rewrite mulmxV.
have GT : G^T = G by rewrite /G trmx_inv HT.
pose w := a *m G.
have wH : w *m H = a by rewrite -mulmxA GH mulmx1.
have Hsym (x y : 'rV[R]_k) : mxdot x (y *m H) = mxdot y (x *m H).
  by rewrite mxdotC mxdot_mulmxr HT.
have Hge0 (x : 'rV[R]_k) : 0 <= mxdot x (x *m H).
  have [->|x0] := eqVneq x 0; first by rewrite mxdot0l.
  by apply: ltW; exact: Hp.
have lw : l = mxdot w (w *m H) by rewrite wH mxdotC.
have l0 : 0 <= l by rewrite lw.
have nl0 : 0 < nn + l by rewrite ltr_wpDr.
have aw (x : 'rV[R]_k) : mxdot a x = mxdot x (w *m H) by rewrite wH mxdotC.
have nn0' : nn != 0 by rewrite gt_eqF.
have nl0' : nn + l != 0 by rewrite gt_eqF.
set t := r / (nn + l).
have hu0 : u0 = (- t) *: w by [].
have u0H : mxdot u0 (u0 *m H) = t ^+ 2 * l.
  by rewrite hu0 -scalemxAl mxdotZl mxdotZr -lw; ring.
have au0 : r + mxdot a u0 = nn * t.
  by rewrite hu0 mxdotZr aw -lw /t; field.
split => //.
- (* l - 2 <a, u> + u H u^T = (u - w) H (u - w)^T *)
  move=> u; have := Hge0 (u - w).
  rewrite mulmxBl !mxdotBl !mxdotBr (Hsym w u) -aw -lw.
  by lra.
- (* the objective at u0 + v exceeds its value at u0 by a square *)
  move=> u.
  have [v ->] : exists v, u = u0 + v by exists (u - u0); rewrite addrC subrK.
  have c1 : mxdot u0 (v *m H) = - t * mxdot a v.
    by rewrite hu0 mxdotZl Hsym -aw.
  have e1 : mxdot (u0 + v) ((u0 + v) *m H) =
      t ^+ 2 * l - 2 * t * mxdot a v + mxdot v (v *m H).
    by rewrite mulmxDl !mxdotDl !mxdotDr u0H (Hsym v u0) c1; ring.
  have e2 : r + mxdot a (u0 + v) = nn * t + mxdot a v.
    by rewrite mxdotDr addrA au0.
  rewrite e1 e2.
  have -> : r ^+ 2 / (2 * (nn + l)) = t ^+ 2 * (nn + l) / 2.
    by rewrite /t; field.
  have -> : (t ^+ 2 * l - 2 * t * mxdot a v + mxdot v (v *m H)) / 2 +
      (nn * t + mxdot a v) ^+ 2 / (2 * nn) =
      t ^+ 2 * (nn + l) / 2 +
      (mxdot v (v *m H) / 2 + mxdot a v ^+ 2 / (2 * nn)) by field.
  rewrite lerDl addr_ge0 // divr_ge0 ?sqr_ge0 ?Hge0 //.
  by rewrite mulr_ge0 // ltW.
- by rewrite u0H au0 /t; field.
by rewrite u0H /t; field.
Qed.

End quadratic_response.
