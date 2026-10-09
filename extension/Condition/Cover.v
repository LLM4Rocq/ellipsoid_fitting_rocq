(* The finite cover by two-sided slices, at Stdlib's R: item Q5 of phase 8
   (notes/three-extensions-plan.md, sections 1.4 (c) and 5.2; the note
   notes/phase6-three-extensions.md, (22)).

   For 1 <= C0 < C1 there are finitely many slices pd_slice2 d a_j b_j,
   j < J, with 0 < a_j < 1 < b_j and b_j < C1 a_j, all independent of d,
   such that every trace-d matrix of the cone of condition number C0
   (cond_slice C0 of library/matrix/condition_cone.v) lies in one of them
   with a spectral margin h > 0, so that its barrier logdet_barrier2 is at
   most d B, B independent of d (cond_cover). Conversely each such slice
   lies in the trace slice of the cone of condition number C1
   (slice2_cond_slice).

   The construction: with L = 1/C0 and h = (C1 - C0) L / (2 (C1 + C0 + 1)),
   the centers u_k = L + k h, k <= K = floor((1 - L) / h), and the slices
   a_k = u_k - h, b_k = C0 (u_k + h) + h. A trace-d matrix S of the cone
   has t I <= S <= C0 t I for some t in [L, 1] (cond_slice_t); with
   k = floor((t - L) / h), u_k <= t < u_k + h, so a_k + h <= S <= b_k - h,
   and slice2_witness of Sat/ApproximateFit bounds its barrier. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences exp.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From GaussianAnalysis.matrix Require Import von_neumann condition_cone.
From GaussianAnalysis.convex Require Import logdet_barrier.
From EllipsoidUniversality.Sat Require Import ApproximateFit.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* The quadratic form of a symmetric matrix on rows and on columns. *)
Lemma mxdot_row_col (d : nat) (S : 'M[R]_d) (v : 'rV[R]_d) :
  S \is symmetricmx -> mxdot v (v *m S) = mxdot v^T (S *m v^T).
Proof. by move=> /symmetricmxP Ss; rewrite -mxdot_trmx trmx_mul Ss. Qed.

(* Each slice with b <= C1 a lies in the trace slice of the cone of
   condition number C1. *)
Lemma slice2_cond_slice (C1 a b : R) (d : nat) (x : 'rV[R]_(d * d)) :
  0 < a -> b <= C1 * a -> pd_slice2 d a b x -> cond_slice_vec C1 x.
Proof.
move=> a0 bC hx; have [p1 [p2 xtr]] := hx.
have [P Po [l XE lb]] := slice2_spectral d a b x hx.
have Xs : vec_mx x \is symmetricmx.
  rewrite XE -{2}[P]trmxK symmetricmx_conj //.
  by apply/symmetricmxP; rewrite tr_diag_mx.
split => //; split => //; exists a; first exact: ltW.
move=> v; apply/andP; split.
  move: v; apply/(spectral_form_ge a Po XE) => i.
  by case/andP: (lb i) => h _; exact: ltW.
move: v; apply/(spectral_form_le (C1 * a) Po XE) => i.
by case/andP: (lb i) => _ h; exact: le_trans (ltW h) bC.
Qed.

(* The finite cover (22). *)
Theorem cond_cover (C0 C1 : R) : 1 <= C0 -> C0 < C1 ->
  exists (J : nat) (a b : nat -> R) (B : R),
  (forall j, (j < J)%N -> [/\ 0 < a j, a j < 1, 1 < b j & b j < C1 * a j]) /\
  forall (d : nat) (S : 'M[R]_d), (0 < d)%N -> cond_slice C0 S ->
  exists2 j, (j < J)%N &
    pd_slice2 d (a j) (b j) (mxvec S) /\
    logdet_barrier2 d (a j) (b j) (mxvec S) <= d%:R * B.
Proof.
move=> C01 C01'.
have C0p : 0 < C0 := lt_le_trans ltr01 C01.
pose L := C0^-1.
have L0 : 0 < L by rewrite invr_gt0.
have CL : C0 * L = 1 by rewrite mulfV // gt_eqF.
have L1 : L <= 1 by rewrite -[X in _ <= X]CL ler_peMl // ltW.
pose den := 2 * (C1 + C0 + 1).
have den0 : 0 < den by rewrite /den mulr_gt0 //; lra.
pose h := (C1 - C0) * L / den.
have h0 : 0 < h by rewrite divr_gt0 // mulr_gt0 // subr_gt0.
have hE : den * h = (C1 - C0) * L by rewrite mulrC divfK // gt_eqF.
have hL : h < L.
  have : (C1 - C0) * L < den * L by rewrite ltr_pM2r // /den; lra.
  by rewrite -hE ltr_pM2l.
(* the centers u k = L + k h, k <= K *)
pose K := archimedean.Num.truncn ((1 - L) / h).
have KL0 : 0 <= (1 - L) / h by rewrite divr_ge0 ?subr_ge0 // ltW.
have Kh : K%:R * h <= 1 - L.
  have := archimedean.Num.Theory.truncn_le ((1 - L) / h); rewrite KL0 => hk.
  by rewrite -ler_pdivlMr.
pose u (k : nat) := L + k%:R * h.
have prop j : (j <= K)%N -> [/\ 0 < u j - h, u j - h < 1,
    1 < C0 * (u j + h) + h & C0 * (u j + h) + h < C1 * (u j - h)].
  move=> jK.
  have jh : j%:R * h <= 1 - L.
    by apply: le_trans Kh; rewrite ler_pM2r // ler_nat.
  have j0 : 0 <= j%:R * h by rewrite mulr_ge0 // ltW.
  have e1 : C0 * (u j + h) = 1 + C0 * (j%:R * h + h) by rewrite /u -CL; ring.
  have e2 : 0 < C0 * (j%:R * h + h) by rewrite mulr_gt0 //; lra.
  have e3 : 0 <= (C1 - C0) * (j%:R * h) by rewrite mulr_ge0 // subr_ge0 ltW.
  rewrite e1 /u; split; [lra | lra | lra | ].
  have e4 : 0 < (C1 + C0 + 1) * h by rewrite mulr_gt0 //; lra.
  by rewrite /den in hE; rewrite -[X in X + _ + _ < _]CL; nra.
exists K.+1, (fun k => u k - h), (fun k => C0 * (u k + h) + h),
  (ln ((1 + h) * (C0 * (1 + h) + h)) - 2 * ln h).
split; first by move=> j; rewrite ltnS; exact: prop.
move=> d S d0 SS.
have [t /andP[Lt t1] ht] := cond_slice_t C0p d0 SS.
rewrite -/L in Lt.
(* the slice of S: u k <= t < u k + h *)
have tL0 : 0 <= (t - L) / h by rewrite divr_ge0 ?subr_ge0 // ltW.
pose k := archimedean.Num.truncn ((t - L) / h).
have kt : u k <= t.
  have := archimedean.Num.Theory.truncn_le ((t - L) / h); rewrite tL0 => hk.
  by rewrite /u -lerBrDl -ler_pdivlMr.
have tk : t < u k + h.
  have := archimedean.Num.Theory.truncnS_gt ((t - L) / h) => hk.
  by move: hk; rewrite ltr_pdivrMr // -/k -natr1 mulrDl mul1r /u; lra.
have kK : (k <= K)%N.
  apply: archimedean.Num.Theory.le_truncn.
  by rewrite ler_pM2r ?invr_gt0 //; lra.
exists k; first by rewrite ltnS.
have [[Ss _] trS] := SS.
have [a0 a1 b1 bC] := prop k kK.
have hS (v : 'rV[R]_d) :
    u k * mxdot v v <= mxdot v (v *m S) <= C0 * (u k + h) * mxdot v v.
  rewrite mxdot_row_col // -[mxdot v v]mxdot_trmx.
  case/andP: (ht v^T) => h1 h2; have m0 := mxdot_ge0 v^T.
  apply/andP; split.
    by apply: le_trans h1; rewrite ler_wpM2r.
  by apply: le_trans h2 _; rewrite ler_wpM2r // ler_wpM2l ?(ltW C0p) // ltW.
have mM : u k - h < 1 < C0 * (u k + h) + h by rewrite a1 b1.
have lo : u k - h < u k by rewrite ltrBlDr ltrDl.
have hi : C0 * (u k + h) < C0 * (u k + h) + h by rewrite ltrDl.
have [H1 H2] := slice2_witness d (u k - h) (C0 * (u k + h) + h) (u k)
  (C0 * (u k + h)) S mM lo hi Ss trS hS.
split => //; apply: le_trans H2 _; rewrite ler_wpM2l ?ler0n //.
have -> : u k - (u k - h) = h by rewrite opprB addrC subrK.
have -> : C0 * (u k + h) + h - C0 * (u k + h) = h by rewrite addrC addKr.
(* the barrier bound, uniformly in k *)
have uk0 : 0 <= u k by apply: le_trans (ltW a0) _; rewrite lerBlDr lerDl ltW.
have uk1 : u k <= 1 := le_trans kt t1.
have x1 : 0 < 1 - (u k - h) by rewrite subr_gt0.
have x2 : 0 < C0 * (u k + h) + h - 1 by rewrite subr_gt0.
have y2 : C0 * (u k + h) + h - 1 <= C0 * (1 + h) + h.
  have : C0 * (u k + h) <= C0 * (1 + h).
    by rewrite ler_wpM2l ?(ltW C0p) // lerD2r.
  lra.
have XY : (1 - (u k - h)) * (C0 * (u k + h) + h - 1) <=
    (1 + h) * (C0 * (1 + h) + h).
  by apply: ler_pM; [exact: ltW | exact: ltW | lra | exact: y2].
have Y0 : 0 < (1 + h) * (C0 * (1 + h) + h).
  by apply: lt_le_trans XY; rewrite mulr_gt0.
have : ln ((1 - (u k - h)) * (C0 * (u k + h) + h - 1)) <=
    ln ((1 + h) * (C0 * (1 + h) + h)).
  by rewrite ler_ln // posrE ?mulr_gt0.
lra.
Qed.
