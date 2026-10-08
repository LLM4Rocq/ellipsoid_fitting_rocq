From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive realfun exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import euclidean self_concordant least_squares.

(**md**************************************************************************)
(* # Removing the barrier                                                     *)
(*                                                                            *)
(* Lemma 2.11 of Koehler and Sohn (arXiv 2608.27372, lines 1386-1441): the    *)
(* cost of a theta-self-concordant barrier B >= 0 in the least squares value  *)
(* is controlled by the contraction toward a reference point. Below, D is     *)
(* convex and relatively open with directions V, B is a theta-self-concordant *)
(* barrier on D with theta >= 0 and B >= 0 on D, theta_ref is in D, b_ref is  *)
(* real, lambda, beta >= 0, gamma > 0 and 0 < eps < 1. F_Z is ls_objective,   *)
(* Phi_Z(D; beta) is ls_value and Phi_Z(D, B; beta, gamma) is                 *)
(* ls_barrier_value (least_squares.v).                                        *)
(*                                                                            *)
(* - ls_objective_convex: F_Z is convex in (theta, b).                        *)
(* - barrier_removal, Lemma 2.11: for every n-tuple of features Z,            *)
(*     0 <= Phi_Z(D, B; beta, gamma) - Phi_Z(D; beta)                         *)
(*       <= eps F_Z(theta_ref, b_ref; beta) + gamma B theta_ref               *)
(*          + gamma theta ln (1 / eps).                                       *)
(* - barrier_removal_compare, (2.15): for two tuples W and G,                 *)
(*     |Phi_W(D; beta) - Phi_G(D; beta)|                                      *)
(*       <= |Phi_W(D, B; beta, gamma) - Phi_G(D, B; beta, gamma)|             *)
(*          + eps (F_W + F_G)(theta_ref, b_ref; beta) + 2 gamma B theta_ref   *)
(*          + 2 gamma theta ln (1 / eps).                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ls_convexity.
Context {R : realType} {N : nat}.

Lemma sqr_convex (a c t : R) : 0 <= t <= 1 ->
  ((1 - t) * a + t * c) ^+ 2 <= (1 - t) * a ^+ 2 + t * c ^+ 2.
Proof.
move=> /andP[t0 t1]; rewrite -subr_ge0.
have -> : (1 - t) * a ^+ 2 + t * c ^+ 2 - ((1 - t) * a + t * c) ^+ 2 =
    t * (1 - t) * (a - c) ^+ 2 by ring.
by rewrite mulr_ge0 ?sqr_ge0 // mulr_ge0 // subr_ge0.
Qed.

Lemma mxdot_convex (u v : 'rV[R]_N) (t : R) : 0 <= t <= 1 ->
  mxdot ((1 - t) *: u + t *: v) ((1 - t) *: u + t *: v) <=
  (1 - t) * mxdot u u + t * mxdot v v.
Proof.
move=> /andP[t0 t1]; rewrite -subr_ge0.
have -> : (1 - t) * mxdot u u + t * mxdot v v -
    mxdot ((1 - t) *: u + t *: v) ((1 - t) *: u + t *: v) =
    t * (1 - t) * mxdot (u - v) (u - v).
  rewrite !mxdotDl !mxdotDr !mxdotNl !mxdotNr !mxdotZl !mxdotZr (mxdotC v u).
  by ring.
by rewrite mulr_ge0 ?mxdot_ge0 // mulr_ge0 // subr_ge0.
Qed.

(* F_Z is convex in (theta, b). *)
Lemma ls_objective_convex n (Z : n.-tuple 'rV[R]_N) (lambda beta t : R)
    (th th' : 'rV[R]_N) (b b' : R) :
  0 <= lambda -> 0 <= beta -> 0 <= t <= 1 ->
  ls_objective Z lambda beta ((1 - t) *: th + t *: th') ((1 - t) * b + t * b')
  <= (1 - t) * ls_objective Z lambda beta th b +
     t * ls_objective Z lambda beta th' b'.
Proof.
move=> l0 b0 t01; have /andP[t0 t1] := t01.
have s0 : 0 <= ((n%:R *+ 2)^-1 : R) by rewrite invr_ge0 mulrn_wge0 ?ler0n.
rewrite /ls_objective.
set s := (n%:R *+ 2)^-1.
have hsum : \sum_(i < n) ((1 - t) * b + t * b' -
    mxdot (tnth Z i) ((1 - t) *: th + t *: th')) ^+ 2 <=
    (1 - t) * \sum_(i < n) (b - mxdot (tnth Z i) th) ^+ 2 +
    t * \sum_(i < n) (b' - mxdot (tnth Z i) th') ^+ 2.
  rewrite !mulr_sumr -big_split /=; apply: ler_sum => i _.
  have -> : (1 - t) * b + t * b' - mxdot (tnth Z i) ((1 - t) *: th + t *: th')
      = (1 - t) * (b - mxdot (tnth Z i) th) +
        t * (b' - mxdot (tnth Z i) th').
    by rewrite mxdotDr !mxdotZr; ring.
  exact: sqr_convex.
have hth := mxdot_convex th th' t01.
have hb := sqr_convex b b' t01.
have h1 := ler_wpM2l s0 hsum.
have h2 := ler_wpM2l l0 hth.
have h3 := ler_wpM2l b0 (lerD h2 hb).
apply: le_trans (lerD h1 h3) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; rewrite /s; ring.
Qed.

End ls_convexity.

Section barrier_removal.
Context {R : realType} {N : nat}.
Variables (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) (theta : R)
  (B : 'rV[R]_N -> R).
Hypotheses (DV : rel_open_convex V D) (scB : sc_barrier V D theta B).
Hypotheses (theta0 : 0 <= theta) (B0 : forall z, D z -> 0 <= B z).

(* Lemma 2.11. *)
Lemma barrier_removal n (Z : n.-tuple 'rV[R]_N) (lambda beta gamma eps : R)
    (thr : 'rV[R]_N) (br : R) :
  D thr -> 0 <= lambda -> 0 <= beta -> 0 < gamma -> 0 < eps < 1 ->
  0 <= ls_barrier_value Z lambda beta D gamma B - ls_value Z lambda beta D <=
  eps * ls_objective Z lambda beta thr br + gamma * B thr +
    gamma * theta * ln eps^-1.
Proof.
move=> Dthr l0 b0 g0 e01; have /andP[e0 e1] := e01.
set F := ls_objective Z lambda beta.
have F0 th b : 0 <= F th b := ls_objective_ge0 Z th b l0 b0.
rewrite /ls_barrier_value /ls_value -/F.
set S1 := [set _ | _ in _ & _ in _]; set S0 := [set _ | _ in _ & _ in _].
have S0lb : has_lbound S0 by exists 0 => _ [th Dth [b _ <-]]; exact: F0.
have S1lb : has_lbound S1.
  exists 0 => _ [th Dth [b _ <-]].
  by rewrite addr_ge0 ?F0 // mulr_ge0 ?B0 // ltW.
have S0n : S0 !=set0 by exists (F thr br), thr => //; exists br.
have S1n : S1 !=set0.
  by exists (F thr br + gamma * B thr), thr => //; exists br.
apply/andP; split.
  rewrite subr_ge0; apply: lb_le_inf S1n _ => _ [th Dth [b _ <-]].
  apply: le_trans (ge_inf S0lb _) _; first by exists th => //; exists b.
  by rewrite lerDl mulr_ge0 ?B0 // ltW.
(* contract every (theta, b) toward the reference point *)
set c := eps * F thr br + gamma * B thr + gamma * theta * ln eps^-1.
suff : inf S1 - c <= inf S0 by lra.
apply: lb_le_inf S0n _ => _ [th Dth [b _ <-]].
rewrite lerBlDr.
pose th' := (1 - eps) *: th + eps *: thr.
pose b' := (1 - eps) * b + eps * br.
have e01' : 0 <= eps <= 1 by rewrite ltW // ltW.
have Dth' : D th'.
  have [cvx _ _] := DV.
  have := cvx th thr eps Dth Dthr e01'.
  have -> : th + eps *: (thr - th) = th'.
    by rewrite /th' scalerBr scalerBl scale1r addrA [_ - _ + _]addrAC.
  by [].
apply: le_trans (ge_inf S1lb _) _; first by exists th' => //; exists b'.
have hF := ls_objective_convex Z th thr b br l0 b0 e01'.
have hB := sc_barrier_contraction DV scB theta0 Dthr Dth e01.
have hFr := F0 thr br; have hFt := F0 th b.
have hBg := ler_wpM2l (ltW g0) hB.
rewrite -/F -/th' -/b' in hF.
rewrite /c.
have : (1 - eps) * F th b <= F th b by rewrite ler_piMl // lerBlDr lerDl ltW.
lra.
Qed.

(* (2.15): the comparison of the values without barrier. *)
Lemma barrier_removal_compare n (W G : n.-tuple 'rV[R]_N)
    (lambda beta gamma eps : R) (thr : 'rV[R]_N) (br : R) :
  D thr -> 0 <= lambda -> 0 <= beta -> 0 < gamma -> 0 < eps < 1 ->
  `|ls_value W lambda beta D - ls_value G lambda beta D| <=
  `|ls_barrier_value W lambda beta D gamma B -
    ls_barrier_value G lambda beta D gamma B| +
  eps * (ls_objective W lambda beta thr br + ls_objective G lambda beta thr br)
  + 2 * gamma * B thr + 2 * gamma * theta * ln eps^-1.
Proof.
move=> Dthr l0 b0 g0 e01.
have /andP[hW1 hW2] := barrier_removal W br Dthr l0 b0 g0 e01.
have /andP[hG1 hG2] := barrier_removal G br Dthr l0 b0 g0 e01.
set uW := ls_value W lambda beta D in hW1 hW2 *.
set uG := ls_value G lambda beta D in hG1 hG2 *.
set vW := ls_barrier_value W lambda beta D gamma B in hW1 hW2 *.
set vG := ls_barrier_value G lambda beta D gamma B in hG1 hG2 *.
have dv := ler_norm (vW - vG); have dv' := ler_norm (vG - vW).
rewrite distrC in dv'.
rewrite ler_norml; apply/andP; split; lra.
Qed.

End barrier_removal.
