From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import interval boolp classical_sets functions reals.
From mathcomp Require Import set_interval topology normedtype derive realfun.
From mathcomp Require Import exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import euclidean real_spectral.
From GaussianAnalysis Require Import self_concordant logdet_barrier.
From GaussianAnalysis Require Import least_squares.
From GaussianAnalysis Require Import minimizers lindeberg.

(**md**************************************************************************)
(* # Inserting one feature in a barrier-regularized least squares problem     *)
(*                                                                            *)
(* The deterministic part of the Lindeberg argument of Koehler and Sohn       *)
(* (arXiv 2608.27372, proof of Theorem 2.9, lines 1637-2116 and 3809-4225).   *)
(* Fix features x_1, ..., x_n in 'rV[R]_N and an index i, a convex set D      *)
(* that is relatively open with directions V, a self-concordant function      *)
(* B >= 0 on D, and lambda, beta, gamma > 0. The leave-one-out objective is   *)
(*   F^(i)(theta, b) = (2 n)^-1 sum_(j <> i) (b - <x_j, theta>)^2             *)
(*                     + beta (lambda |theta|^2 + b^2) + gamma B theta,       *)
(* with a minimizer (theta_m, b_m) on D x R (ls_barrier_minimizer).           *)
(* Inserting a feature z at the place i gives the value of the full           *)
(* problem (ls_barrier_value of tuple_set x i z), and the insertion cost is   *)
(* Delta(z) = that value minus F^(i)(theta_m, b_m). Directions of V x R are   *)
(* written in coordinates w = (c, y) in 'rV[R]_(1 + k), for a matrix E whose  *)
(* k rows form an orthonormal basis of V: the direction is (y E, c).          *)
(*                                                                            *)
(* ```                                                                        *)
(*       ins_alpha E z == the row (1, - z E^T): <ins_alpha E z, w> is         *)
(*                        c - <z, y E>, the change of the residual of z       *)
(*  ins_hform ... w w' == the Hessian of F^(i) at the minimizer, as a         *)
(*                        bilinear form of the coordinates                    *)
(*     ins_hessian ... == its matrix H^(i)                                    *)
(*       ins_ell ... z == l_i(z) = <alpha(z), H^-1 alpha(z)>                  *)
(*         ins_r ... z == r_i(z) = b_m - <z, theta_m>, the residual           *)
(*      ins_cost ... z == Delta_i(z), the insertion cost                      *)
(* ins_c0, ins_v, ins_T == the coefficients of l_i as a quadratic polynomial  *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - ins_hessian_pd (Lemma 4.1): H^(i) is positive definite, with             *)
(*   w H w^T >= 2 beta (lambda |y|^2 + c^2); ins_form_le: for a linear form   *)
(*   w |-> c c_w + <y, h_w>, its squared H^-1 norm is at most                 *)
(*   c^2 / (2 beta) + |y|^2 / (2 beta lambda).                                *)
(* - ins_taylor: the inserted objective at (theta_m + h_w, b_m + c_w)         *)
(*   exceeds F^(i)(theta_m, b_m) by w H w^T / 2 + (r + <alpha, w>)^2 / (2 n)  *)
(*   plus gamma times the third order remainder of B.                         *)
(* - ins_cost_bounds (2.20): 0 <= Delta(z) <= r(z)^2 / (2 n).                 *)
(* - ins_cost_upper, ins_cost_lower (Lemma 4.2): if 36 <= n gamma and         *)
(*   r(z)^2 <= sqrt (n gamma), then Delta(z) differs from                     *)
(*   r(z)^2 / (2 (n + l(z))) by at most 2 |r(z)|^3 / (n sqrt (n gamma)).      *)
(* - ins_cost_quadratic (Proposition 2.14, (2.23), pointwise): if             *)
(*   36 <= n gamma, then for every z,                                         *)
(*     |Delta(z) - r(z)^2 / (2 (n + l(z)))|                                   *)
(*       <= (2 + 3 r(z)^4) / (n sqrt (n gamma)).                              *)
(* - ins_ell_quadratic, ins_c0_bounds, ins_v_bound, ins_T_bounds, ins_T_sym,  *)
(*   ins_T_frobenius (the structure behind Proposition 2.16):                 *)
(*   l(z) = c0 - 2 <v, z> + z T z^T with T symmetric,                         *)
(*   0 <= c0 <= 1 / (2 beta), |v|^2 <= k / (4 beta^2 lambda),                 *)
(*   0 <= z T z^T <= |z|^2 / (2 beta lambda) and                              *)
(*   |T|_F^2 <= k / (4 beta^2 lambda^2).                                      *)
(* - ins_size_le (Proposition 2.14, (2.21)): for theta_ref in D,              *)
(*   beta (lambda |theta_m|^2 + b_m^2) <=                                     *)
(*   (2 n)^-1 sum_(j <> i) <x_j, theta_ref>^2 + beta lambda |theta_ref|^2     *)
(*   + gamma B theta_ref.                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section mxdot_blocks.
Context {R : realType}.

Lemma mxdot_row_mx m n1 n2 (a c : 'M[R]_(m, n1)) (b d : 'M[R]_(m, n2)) :
  mxdot (row_mx a b) (row_mx c d) = mxdot a c + mxdot b d.
Proof. by rewrite !mxdot_trace tr_row_mx mul_row_col mxtraceD. Qed.

End mxdot_blocks.

Section insertion_defs.
Context {R : realType} {N : nat}.
Variables (n : nat) (x : n.-tuple 'rV[R]_N) (i : 'I_n).
Variables (lambda beta gamma : R) (M : 'M[R]_N) (k : nat) (E : 'M[R]_(k, N)).

Definition ins_alpha (z : 'rV[R]_N) : 'rV[R]_(1 + k) :=
  row_mx (1%:M : 'M[R]_1) (- (z *m E^T)).

(* The direction (h, c) of V x R of the coordinates w = (c, y): h = y E. *)
Definition ins_c (w : 'rV[R]_(1 + k)) : R := lsubmx w 0 0.
Definition ins_h (w : 'rV[R]_(1 + k)) : 'rV[R]_N := rsubmx w *m E.

Definition ins_hform (w w' : 'rV[R]_(1 + k)) : R :=
  2 * (n%:R *+ 2)^-1 * \sum_(j < n | j != i)
    mxdot (ins_alpha (tnth x j)) w * mxdot (ins_alpha (tnth x j)) w' +
  2 * beta * (lambda * mxdot (ins_h w) (ins_h w') + ins_c w * ins_c w') +
  gamma * mxdot (ins_h w) (ins_h w' *m M).

Definition ins_hessian : 'M[R]_(1 + k) :=
  \matrix_(p, q) ins_hform (delta_mx 0 p) (delta_mx 0 q).

Definition ins_ell (z : 'rV[R]_N) : R :=
  mxdot (ins_alpha z) (ins_alpha z *m invmx ins_hessian).

Lemma ins_alphaE z w : mxdot (ins_alpha z) w = ins_c w - mxdot z (ins_h w).
Proof.
rewrite -[w in LHS]hsubmxK mxdot_row_mx mxdotNl mxdot_mulmxr trmxK.
by rewrite /ins_c /ins_h /mxdot !big_ord1 !mxE eqxx mul1r.
Qed.

Lemma ins_c_linear (c : R) w w' : ins_c (c *: w + w') = c * ins_c w + ins_c w'.
Proof. by rewrite /ins_c linearD linearZ /= !mxE. Qed.

Lemma ins_h_linear (c : R) w w' : ins_h (c *: w + w') = c *: ins_h w + ins_h w'.
Proof. by rewrite /ins_h linearD linearZ /= mulmxDl scalemxAl. Qed.

Lemma ins_hform_linearl (c : R) w w' w'' :
  ins_hform (c *: w + w') w'' = c * ins_hform w w'' + ins_hform w' w''.
Proof.
rewrite /ins_hform ins_c_linear ins_h_linear mxdotDl mxdotZl mxdotDl mxdotZl.
have E1 j : mxdot (ins_alpha (tnth x j)) (c *: w + w') *
    mxdot (ins_alpha (tnth x j)) w'' =
    c * (mxdot (ins_alpha (tnth x j)) w * mxdot (ins_alpha (tnth x j)) w'') +
    mxdot (ins_alpha (tnth x j)) w' * mxdot (ins_alpha (tnth x j)) w''.
  by rewrite mxdotDr mxdotZr; ring.
under eq_bigr do rewrite E1.
rewrite big_split /= -mulr_sumr.
move: (\sum_(j < n | j != i) _) (\sum_(j < n | j != i) _) => S1 S2.
by ring.
Qed.

Lemma ins_hformC w w' : M \is symmetricmx -> ins_hform w w' = ins_hform w' w.
Proof.
move=> /symmetricmxP MT.
rewrite /ins_hform [mxdot (ins_h w) (ins_h w')]mxdotC [ins_c w * _]mulrC.
rewrite [mxdot (ins_h w) (ins_h w' *m M)]mxdotC.
rewrite [mxdot (ins_h w' *m M) _]mxdot_mulmxr MT.
congr (_ * _ + _ + _); apply: eq_bigr => j _; exact: mulrC.
Qed.

Lemma ins_hessianE w : M \is symmetricmx ->
  mxdot w (w *m ins_hessian) = ins_hform w w.
Proof.
move=> Ms; rewrite (bilin_form_mx (@ins_hform_linearl) _ w) //.
by move=> c u v w'; rewrite !(ins_hformC w') // ins_hform_linearl.
Qed.

End insertion_defs.

Section insertion.
Context {R : realType} {N : nat}.
Variables (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) (B : 'rV[R]_N -> R).
Hypotheses (DV : rel_open_convex V D) (scB : sc_function V D B).
Hypothesis B0 : forall z, D z -> 0 <= B z.
Variables (n : nat) (x : n.-tuple 'rV[R]_N) (i : 'I_n).
Variables (lambda beta gamma : R).
Hypotheses (l0 : 0 < lambda) (b0 : 0 < beta) (g0 : 0 < gamma).
Variables (k : nat) (E : 'M[R]_(k, N)).
Hypothesis EE : E *m E^T = 1%:M.
Hypothesis EV : forall v, v \in V <-> exists y, v = y *m E.
Variables (thm : 'rV[R]_N) (bm : R) (M : 'M[R]_N).
Hypothesis Dthm : D thm.
Hypothesis thmin : forall theta b, D theta ->
  ls_barrier_objective x (fun j => j != i) (n%:R *+ 2)^-1 lambda beta gamma B
    thm bm <=
  ls_barrier_objective x (fun j => j != i) (n%:R *+ 2)^-1 lambda beta gamma B
    theta b.
Hypothesis Msym : M \is symmetricmx.
Hypothesis HM : forall h, h \in V -> 'D_h ('D_h B) thm = mxdot h (h *m M).

Local Notation s := ((n%:R *+ 2)^-1 : R).
Local Notation P := (fun j : 'I_n => j != i).
Local Notation F := (ls_barrier_objective x P s lambda beta gamma B).
Local Notation ridge := (ls_ridge x P s lambda beta).
Local Notation H := (ins_hessian x i lambda beta gamma M E).
Local Notation hform := (ins_hform x i lambda beta gamma M E).
Local Notation alpha := (ins_alpha E).
Local Notation ell := (ins_ell x i lambda beta gamma M E).
Local Notation hw := (ins_h E).
Local Notation cw := (@ins_c R k).

(* The residual of z at the minimizer, and the insertion cost of z. *)
Definition ins_r (z : 'rV[R]_N) : R := bm - mxdot z thm.

Definition ins_cost (z : 'rV[R]_N) : R :=
  ls_barrier_value (tuple_set x i z) lambda beta D gamma B - F thm bm.

(* The remainder of the quadratic expansion along the direction w. *)
Definition ins_rem (w : 'rV[R]_(1 + k)) : R :=
  gamma * (bregman_div B (thm + hw w) thm - 'D_(hw w) ('D_(hw w) B) thm / 2).

Lemma ins_n_gt0 : (0 < n)%N.
Proof. by case: i => j /= /(leq_ltn_trans (leq0n j)). Qed.

Lemma ins_nR_gt0 : 0 < (n%:R : R).
Proof. by rewrite ltr0n ins_n_gt0. Qed.

Lemma ins_s_eq : s = (2 * n%:R)^-1.
Proof. by rewrite -mulr_natl mulrC. Qed.

Lemma ins_hV w : hw w \in V.
Proof. by apply/EV; exists (rsubmx w). Qed.

Lemma ins_norm_h w : mxdot (hw w) (hw w) = mxdot (rsubmx w) (rsubmx w).
Proof. by rewrite /ins_h mxdot_mulmxr -mulmxA EE mulmx1. Qed.

Lemma ins_D2B_ge0 w : 0 <= 'D_(hw w) ('D_(hw w) B) thm.
Proof. by have [_ _ psd _ _] := scB; apply: psd => //; exact: ins_hV. Qed.

Lemma ins_hform_ridge w :
  hform w w = 2 * ridge (hw w) (cw w) + gamma * 'D_(hw w) ('D_(hw w) B) thm.
Proof.
rewrite HM ?ins_hV // /ins_hform /ls_ridge /ls_loss.
under eq_bigr do rewrite ins_alphaE -expr2.
by rewrite expr2; ring.
Qed.

Lemma ins_ridge_ge h c : beta * (lambda * mxdot h h + c ^+ 2) <= ridge h c.
Proof.
rewrite /ls_ridge lerDr; apply: mulr_ge0.
  by rewrite invr_ge0 mulrn_wge0 // ler0n.
by apply: sumr_ge0 => j _; exact: sqr_ge0.
Qed.

Lemma ins_hform_ge w :
  2 * beta * (lambda * mxdot (rsubmx w) (rsubmx w) + cw w ^+ 2) <= hform w w.
Proof.
rewrite ins_hform_ridge -ins_norm_h -mulrA.
apply: ler_wpDr; first by rewrite mulr_ge0 ?ins_D2B_ge0 // ltW.
by rewrite ler_pM2l ?ltr0n // ins_ridge_ge.
Qed.

(* Lemma 4.1: the Hessian at the minimizer is positive definite. *)
Lemma ins_hessian_pd : posdefmx H.
Proof.
split.
  apply/symmetricmxP/matrixP => p q; rewrite !mxE.
  exact: ins_hformC.
move=> w w0; rewrite ins_hessianE //.
apply: lt_le_trans (ins_hform_ge w).
apply: mulr_gt0; first by rewrite mulr_gt0.
have [y0|y0] := eqVneq (rsubmx w) 0.
  rewrite y0 mxdot0l mulr0 add0r exprn_even_gt0 //=.
  apply: contra w0 => /eqP c0; rewrite -[w]hsubmxK y0.
  apply/eqP/rowP => j; rewrite !mxE.
  case: splitP => [j' _|j' _]; last by rewrite mxE.
  by rewrite (ord1 j'); move: c0; rewrite /ins_c.
apply: ltr_wpDr; first exact: sqr_ge0.
by rewrite mulr_gt0 // mxdot_gt0.
Qed.

(* Every point of D x R is (thm + h, bm + c) for some coordinates w. *)
Lemma ins_dir theta b : D theta ->
  exists w, theta = thm + hw w /\ b = bm + cw w.
Proof.
move=> Dt; have [_ dir _] := DV.
have [y ye] := (EV (theta - thm)).1 (dir _ _ Dthm Dt).
exists (row_mx ((b - bm)%:M : 'M[R]_1) y); split.
  by rewrite /ins_h row_mxKr -ye addrC subrK.
by rewrite /ins_c row_mxKl mxE eqxx mulr1n addrC subrK.
Qed.

(* The objective of the full problem, with z at the place i. *)
Lemma ins_objective z theta b :
  ls_objective (tuple_set x i z) lambda beta theta b + gamma * B theta =
  F theta b + s * (b - mxdot z theta) ^+ 2.
Proof.
rewrite /ls_objective /ls_barrier_objective /ls_ridge /ls_loss.
rewrite (bigD1 i) //= tnth_mktuple eqxx.
have -> : \sum_(j < n | j != i)
    (b - mxdot (tnth (tuple_set x i z) j) theta) ^+ 2 =
    \sum_(j < n | j != i) (b - mxdot (tnth x j) theta) ^+ 2.
  by apply: eq_bigr => j ji; rewrite tnth_mktuple (negbTE ji).
by ring.
Qed.

(* Taylor's formula for the inserted problem around the minimizer. *)
Lemma ins_taylor z w :
  F (thm + hw w) (bm + cw w) + s * (bm + cw w - mxdot z (thm + hw w)) ^+ 2 -
    F thm bm =
  mxdot w (w *m H) / 2 + ins_rem w +
  (ins_r z + mxdot (alpha z) w) ^+ 2 / (2 * n%:R).
Proof.
have := ls_taylor DV scB Dthm thmin (cw w) (ins_hV w).
rewrite ins_hessianE // ins_hform_ridge ins_alphaE /ins_rem /ins_r.
rewrite mxdotDr ins_s_eq.
have n0 : (n%:R : R) != 0 by rewrite gt_eqF // ins_nR_gt0.
by move=> T; rewrite addrAC T; field.
Qed.

Lemma ins_s_ge0 : 0 <= s.
Proof. by rewrite invr_ge0 mulrn_wge0 // ler0n. Qed.

Lemma ins_cost_set z : ins_cost z =
  inf [set F theta b + s * (b - mxdot z theta) ^+ 2 |
       theta in D & b in [set: R]] - F thm bm.
Proof.
rewrite /ins_cost /ls_barrier_value; congr (inf _ - _).
by apply/seteqP; split => _ [theta Dt [b _ <-]];
  exists theta => //; exists b => //; rewrite ins_objective.
Qed.

(* (2.20): 0 <= Delta(z) <= r(z)^2 / (2 n). *)
Lemma ins_cost_bounds z : 0 <= ins_cost z <= ins_r z ^+ 2 / (2 * n%:R).
Proof.
rewrite ins_cost_set.
set S := [set _ | _ in D & _ in _].
have Slb y : S y -> F thm bm <= y.
  move=> [theta Dt [b _ <-]]; apply: le_trans (thmin b Dt) _.
  by rewrite lerDl mulr_ge0 ?sqr_ge0 ?ins_s_ge0.
have S0 : S (F thm bm + s * ins_r z ^+ 2) by exists thm => //; exists bm.
have hS : has_lbound S by exists (F thm bm).
rewrite subr_ge0 (lb_le_inf (ex_intro _ _ S0) Slb) /=.
rewrite lerBlDl -ins_s_eq [X in _ <= X]addrC.
apply: le_trans (ge_inf hS S0) _.
by rewrite addrC mulrC.
Qed.

Lemma ins_rem_le w : sc_norm B thm (hw w) <= 2^-1 ->
  D (thm + hw w) /\
  `|ins_rem w| <= gamma * (2 * sc_norm B thm (hw w) ^+ 3 / 3%:R).
Proof.
move=> hle; have [Dh hb] := sc_taylor3 DV scB Dthm (ins_hV w) hle.
split => //.
have sq : sc_norm B thm (hw w) ^+ 2 = 'D_(hw w) ('D_(hw w) B) thm.
  by rewrite /sc_norm sqr_sqrtr // ins_D2B_ge0.
rewrite /ins_rem /bregman_div.
have -> : thm + hw w - thm = hw w by rewrite addrAC subrr add0r.
by rewrite -sq normrM gtr0_norm // ler_pM2l.
Qed.

Lemma ins_sqrt_ge6 : 36 <= n%:R * gamma -> 6 <= Num.sqrt (n%:R * gamma).
Proof.
move=> h36; rewrite -[6]ger0_norm ?ler0n // -sqrtr_sqr.
by rewrite ler_wsqrtr // (le_trans _ h36) // expr2 -natrM.
Qed.

(* Lemma 4.2 for the optimizer of the quadratic problem: the upper bound
   on the insertion cost. *)
Lemma ins_cost_upper z : 36 <= n%:R * gamma ->
  ins_r z ^+ 2 <= Num.sqrt (n%:R * gamma) ->
  ins_cost z <= ins_r z ^+ 2 / (2 * (n%:R + ell z)) +
    `|ins_r z| ^+ 3 / (n%:R * Num.sqrt (n%:R * gamma)).
Proof.
move=> n36 rsq.
set r := ins_r z; set nn := (n%:R : R).
have nn0 : 0 < nn := ins_nR_gt0.
have nn0' : nn != 0 by rewrite gt_eqF.
have g0' : gamma != 0 by rewrite gt_eqF.
have ng0 : 0 < nn * gamma by rewrite mulr_gt0.
set sq := Num.sqrt (nn * gamma).
have sq6 : 6 <= sq := ins_sqrt_ge6 n36.
have sq0 : 0 < sq by apply: lt_le_trans sq6; rewrite ltr0n.
have sq0' : sq != 0 by rewrite gt_eqF.
have sqsq : sq ^+ 2 = nn * gamma by rewrite sqr_sqrtr // ltW.
have [l0' _ _ val u0H] := quad_response (alpha z) r ins_hessian_pd nn0.
set l := ell z.
(* the optimizer w0 of the quadratic problem *)
pose w0 := (- (r / (nn + l))) *: (alpha z *m invmx H).
have hf : hform w0 w0 = l * r ^+ 2 / (nn + l) ^+ 2 by rewrite -ins_hessianE.
pose rho := `|r| / (2 * sq).
have rho0 : 0 <= rho by rewrite divr_ge0 // mulr_ge0 // ltW.
have nl0 : 0 < nn + l by rewrite ltr_wpDr.
have lq : l * r ^+ 2 / (nn + l) ^+ 2 <= r ^+ 2 / (4 * nn).
  rewrite ler_pdivrMr ?exprn_gt0 // -subr_ge0.
  have -> : r ^+ 2 / (4 * nn) * (nn + l) ^+ 2 - l * r ^+ 2 =
      r ^+ 2 * (nn - l) ^+ 2 / (4 * nn) by field.
  by apply: divr_ge0; [rewrite mulr_ge0 ?sqr_ge0 | rewrite mulr_ge0 // ltW].
(* its local norm is at most rho <= 1/2 *)
have D2 : 'D_(hw w0) ('D_(hw w0) B) thm <= rho ^+ 2.
  have := ins_hform_ridge w0; rewrite hf => hfe.
  have r0 := ls_ridge_ge0 x P ins_s_ge0 l0 b0 (hw w0) (cw w0).
  have h : gamma * 'D_(hw w0) ('D_(hw w0) B) thm <=
      l * r ^+ 2 / (nn + l) ^+ 2 by rewrite hfe lerDr mulr_ge0.
  rewrite -(ler_pM2l g0); apply: le_trans h _; apply: le_trans lq _.
  rewrite /rho expr_div_n -normrX ger0_norm ?sqr_ge0 // exprMn sqsq.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have snle : sc_norm B thm (hw w0) <= rho.
  rewrite /sc_norm -(ger0_norm rho0) -sqrtr_sqr; exact: ler_wsqrtr.
have rho2 : rho <= 2^-1.
  have rs : `|r| <= sq.
    rewrite -(ger0_norm (ltW sq0)) -ler_sqr ?nnegrE ?normr_ge0 //.
    rewrite real_normK ?num_real //; apply: le_trans rsq _.
    rewrite -/nn -/sq ger0_norm ?(ltW sq0) // expr2 -{1}[sq]mulr1.
    by rewrite ler_pM2l // (le_trans _ sq6) // ler1n.
  rewrite /rho ler_pdivrMr ?mulr_gt0 //.
  by rewrite mulrA mulVf ?mul1r // pnatr_eq0.
have [Dh rem] := ins_rem_le (le_trans snle rho2).
have val' : mxdot w0 (w0 *m H) / 2 + (r + mxdot (alpha z) w0) ^+ 2 / (2 * nn) =
  r ^+ 2 / (2 * (nn + l)) := val.
(* the insertion cost is at most the value at w0 *)
rewrite ins_cost_set.
set S := [set _ | _ in D & _ in _].
have Slb y : S y -> F thm bm <= y.
  move=> [theta Dt [b _ <-]]; apply: le_trans (thmin b Dt) _.
  by rewrite lerDl mulr_ge0 ?sqr_ge0 ?ins_s_ge0.
have hS : has_lbound S by exists (F thm bm).
have Sw : S (F (thm + hw w0) (bm + cw w0) +
    s * (bm + cw w0 - mxdot z (thm + hw w0)) ^+ 2).
  by exists (thm + hw w0) => //; exists (bm + cw w0).
rewrite lerBlDr; apply: le_trans (ge_inf hS Sw) _.
rewrite -lerBlDr ins_taylor -/r -/nn.
rewrite addrAC val' lerD2l; apply: le_trans (ler_norm _) _.
apply: le_trans rem _.
have r3 : sc_norm B thm (hw w0) ^+ 3 <= rho ^+ 3.
  by rewrite lerXn2r ?nnegrE ?sqrtr_ge0.
apply: le_trans (_ : gamma * (2 * rho ^+ 3 / 3%:R) <= _).
  by rewrite ler_pM2l // ler_pM2r ?invr_gt0 ?ltr0n // ler_pM2l.
rewrite /rho expr_div_n !exprMn.
have -> : sq ^+ 3 = sq * (nn * gamma) by rewrite -sqsq exprS.
have -> : gamma * (2 * (`|r| ^+ 3 / (2 ^+ 3 * (sq * (nn * gamma)))) / 3%:R) =
    `|r| ^+ 3 / (nn * sq) / 12%:R by field.
rewrite ler_pdivrMr ?ltr0n // ler_peMr ?ler1n //.
by rewrite divr_ge0 ?exprn_ge0 ?normr_ge0 // mulr_ge0 // ltW.
Qed.

(* Lemma 4.2 for the optimizer of the exact problem: the lower bound on
   the insertion cost. *)
Lemma ins_cost_lower z : 36 <= n%:R * gamma ->
  ins_r z ^+ 2 <= Num.sqrt (n%:R * gamma) ->
  ins_r z ^+ 2 / (2 * (n%:R + ell z)) -
    2 * `|ins_r z| ^+ 3 / (n%:R * Num.sqrt (n%:R * gamma)) <= ins_cost z.
Proof.
move=> n36 rsq.
set r := ins_r z; set nn := (n%:R : R).
have nn0 : 0 < nn := ins_nR_gt0.
have nn0' : nn != 0 by rewrite gt_eqF.
have g0' : gamma != 0 by rewrite gt_eqF.
have ng0 : 0 < nn * gamma by rewrite mulr_gt0.
set sq := Num.sqrt (nn * gamma).
have sq6 : 6 <= sq := ins_sqrt_ge6 n36.
have sq0 : 0 < sq by apply: lt_le_trans sq6; rewrite ltr0n.
have sq0' : sq != 0 by rewrite gt_eqF.
have sqsq : sq ^+ 2 = nn * gamma by rewrite sqr_sqrtr // ltW.
have [l0' _ low _ _] := quad_response (alpha z) r ins_hessian_pd nn0.
set l := ell z.
have nl0 : 0 < nn + l by rewrite ltr_wpDr.
set q := r ^+ 2 / (2 * (nn + l)).
have q0 : q <= r ^+ 2 / (2 * nn).
  rewrite /q ler_wpM2l ?sqr_ge0 // lef_pV2 ?posrE ?mulr_gt0 //.
  by rewrite ler_pM2l // lerDl.
set err := 2 * `|r| ^+ 3 / (nn * sq).
have err0 : 0 <= err.
  by rewrite divr_ge0 ?mulr_ge0 ?exprn_ge0 // ltW // mulr_gt0.
have low' u : q <= mxdot u (u *m H) / 2 +
    (r + mxdot (alpha z) u) ^+ 2 / (2 * nn) := low u.
(* every value of the inserted problem is at least q - err *)
rewrite ins_cost_set lerBrDr.
set S := [set _ | _ in D & _ in _].
apply: lb_le_inf.
  by exists (F thm bm + s * ins_r z ^+ 2); exists thm => //; exists bm.
move=> _ [theta Dt [b _ <-]].
have [w [tE bE]] := ins_dir b Dt.
rewrite tE in Dt; rewrite tE bE.
rewrite -lerBrDr ins_taylor -/r -/nn.
set G := _ + _ + _.
have hG : G = ridge (hw w) (cw w) + gamma * bregman_div B (thm + hw w) thm +
    s * (bm + cw w - mxdot z (thm + hw w)) ^+ 2.
  rewrite /G -ins_taylor -(ls_taylor DV scB Dthm thmin (cw w) (ins_hV w)).
  by ring.
have [Gbig|Gsmall] := leP (r ^+ 2 / (2 * nn)) G.
  by apply: le_trans Gbig; apply: le_trans q0; rewrite lerBlDr lerDl.
(* a small value forces a small Bregman divergence, hence a small local
   norm and a small remainder (Lemma 2.15) *)
have rg0 := ls_ridge_ge0 x P ins_s_ge0 l0 b0 (hw w) (cw w).
have sq2 : 0 <= s * (bm + cw w - mxdot z (thm + hw w)) ^+ 2.
  by rewrite mulr_ge0 ?sqr_ge0 ?ins_s_ge0.
have bg : bregman_div B (thm + hw w) thm * gamma < r ^+ 2 / (2 * nn).
  by apply: le_lt_trans Gsmall; rewrite hG mulrC; lra.
have breg : bregman_div B (thm + hw w) thm <= 12%:R^-1.
  apply: ltW; apply: lt_le_trans (_ : r ^+ 2 / (2 * nn) / gamma <= _).
    by rewrite ltr_pdivlMr.
  have -> : r ^+ 2 / (2 * nn) / gamma = r ^+ 2 / (2 * sq ^+ 2).
    by rewrite sqsq; field.
  apply: le_trans (_ : sq / (2 * sq ^+ 2) <= _).
    by rewrite ler_pM2r ?invr_gt0 ?mulr_gt0 ?exprn_gt0 //; exact: rsq.
  have -> : sq / (2 * sq ^+ 2) = (2 * sq)^-1 by field.
  rewrite lef_pV2 ?posrE ?mulr_gt0 ?ltr0n //.
  by apply: le_trans (ler_wpM2l _ sq6); rewrite ?ler0n // -natrM.
have om : 12%:R^-1 <= sc_omega (2^-1 : R).
  have h2 : (0 : R) <= 2^-1 by rewrite invr_ge0 ler0n.
  have := sc_omega_ge h2 (lexx _).
  suff -> : (2^-1 : R) ^+ 2 / 3%:R = 12%:R^-1 by [].
  by field.
have [sn12 snb] :=
  sc_bregman_small DV scB Dthm (ins_hV w) Dt (le_trans breg om).
have [_ rem] := ins_rem_le sn12.
pose rho := 5%:R * `|r| / (4 * sq).
have rho0 : 0 <= rho.
  by rewrite /rho divr_ge0 ?mulr_ge0 ?ler0n // ltW // mulr_gt0.
have sn2 : sc_norm B thm (hw w) ^+ 2 <= rho ^+ 2.
  have h1 : sc_norm B thm (hw w) ^+ 2 <=
      3%:R * bregman_div B (thm + hw w) thm.
    by move: snb; rewrite ler_pdivrMr ?ltr0n // mulrC.
  apply: le_trans h1 _.
  have h2 : bregman_div B (thm + hw w) thm <= r ^+ 2 / (2 * sq ^+ 2).
    rewrite sqsq; apply: ltW; move: bg.
    have -> : r ^+ 2 / (2 * (nn * gamma)) = r ^+ 2 / (2 * nn) / gamma.
      by field.
    by move=> h; rewrite ltr_pdivlMr.
  apply: le_trans (ler_wpM2l (ler0n _ 3) h2) _.
  rewrite /rho expr_div_n !exprMn -normrX ger0_norm ?sqr_ge0 //.
  have -> : 3%:R * (r ^+ 2 / (2 * sq ^+ 2)) =
      r ^+ 2 / sq ^+ 2 * (3%:R / 2) by field.
  have -> : 5%:R ^+ 2 * r ^+ 2 / (4 ^+ 2 * sq ^+ 2) =
      r ^+ 2 / sq ^+ 2 * (25%:R / 16%:R) by field.
  rewrite ler_wpM2l ?divr_ge0 ?sqr_ge0 //.
  rewrite ler_pdivrMr ?ltr0n // mulrAC ler_pdivlMr ?ltr0n //.
  by rewrite -!natrM ler_nat.
have snle : sc_norm B thm (hw w) <= rho.
  by rewrite -ler_sqr ?nnegrE ?sqrtr_ge0.
have remle : `|ins_rem w| <= err.
  apply: le_trans rem _.
  have r3 : sc_norm B thm (hw w) ^+ 3 <= rho ^+ 3.
    by rewrite lerXn2r ?nnegrE ?sqrtr_ge0.
  apply: le_trans (_ : gamma * (2 * rho ^+ 3 / 3%:R) <= _).
    by rewrite ler_pM2l // ler_pM2r ?invr_gt0 ?ltr0n // ler_pM2l.
  rewrite /rho /err expr_div_n !exprMn.
  have -> : sq ^+ 3 = sq * (nn * gamma) by rewrite -sqsq exprS.
  have -> : gamma * (2 * (5%:R ^+ 3 * `|r| ^+ 3 /
      (4 ^+ 3 * (sq * (nn * gamma)))) / 3%:R) =
      `|r| ^+ 3 / (nn * sq) * (250%:R / 192%:R) by field.
  have -> : 2 * `|r| ^+ 3 / (nn * sq) = `|r| ^+ 3 / (nn * sq) * 2 by field.
  rewrite ler_wpM2l //.
    by rewrite divr_ge0 ?exprn_ge0 ?normr_ge0 // mulr_ge0 // ltW.
  by rewrite ler_pdivrMr ?ltr0n // -natrM ler_nat.
have := low' w.
have : - err <= ins_rem w.
  by rewrite lerNl; apply: le_trans remle; rewrite -normrN ler_norm.
by rewrite /G; lra.
Qed.

Lemma cube_le_quart (a : R) : 0 <= a -> a ^+ 3 <= 1 + a ^+ 4.
Proof.
move=> a0; have [a1|a1] := leP a 1.
  apply: le_trans (_ : 1 <= _); first by rewrite exprn_ile1.
  by rewrite lerDl exprn_ge0.
apply: le_trans (_ : a ^+ 4 <= _); last by rewrite lerDr.
by rewrite (exprS a 3) ler_peMl ?exprn_ge0 // ltW.
Qed.

(* Proposition 2.14, (2.23), pointwise: if 36 <= n gamma, then
   |Delta(z) - r(z)^2 / (2 (n + l(z)))|
     <= (2 + 3 r(z)^4) / (n sqrt (n gamma)). *)
Lemma ins_cost_quadratic z : 36 <= n%:R * gamma ->
  `|ins_cost z - ins_r z ^+ 2 / (2 * (n%:R + ell z))| <=
    (2 + 3%:R * ins_r z ^+ 4) / (n%:R * Num.sqrt (n%:R * gamma)).
Proof.
move=> n36.
set r := ins_r z; set nn := (n%:R : R).
have nn0 : 0 < nn := ins_nR_gt0.
have ng0 : 0 < nn * gamma by rewrite mulr_gt0.
set sq := Num.sqrt (nn * gamma).
have sq6 : 6 <= sq := ins_sqrt_ge6 n36.
have sq0 : 0 < sq by apply: lt_le_trans sq6; rewrite ltr0n.
have nsq0 : 0 < nn * sq by rewrite mulr_gt0.
set l := ell z.
have l0' : 0 <= l by have [] := quad_response (alpha z) r ins_hessian_pd nn0.
have nl0 : 0 < nn + l by rewrite ltr_wpDr.
set q := r ^+ 2 / (2 * (nn + l)).
have q0 : 0 <= q by rewrite divr_ge0 ?sqr_ge0 // mulr_ge0 // ltW.
have q1 : q <= r ^+ 2 / (2 * nn).
  rewrite /q ler_wpM2l ?sqr_ge0 // lef_pV2 ?posrE ?mulr_gt0 //.
  by rewrite ler_pM2l // lerDl.
have [d0 d1] := andP (ins_cost_bounds z).
have r4 : 0 <= 3%:R * r ^+ 4 by rewrite mulr_ge0 ?ler0n // exprn_even_ge0.
have [rs|rs] := leP (r ^+ 2) sq.
  (* small residual: Lemma 4.2 *)
  have up := ins_cost_upper n36 rs.
  have lo := ins_cost_lower n36 rs.
  have c3 : `|r| ^+ 3 <= 1 + r ^+ 4.
    have := cube_le_quart (normr_ge0 r).
    have e4 : `|r| ^+ 4 = r ^+ 4.
      by rewrite -normrX ger0_norm // exprn_even_ge0.
    by rewrite e4.
  rewrite -/r -/nn -/sq -/l -/q in up lo.
  have e1 : `|ins_cost z - q| <= 2 * `|r| ^+ 3 / (nn * sq).
    rewrite ler_norml; apply/andP; split.
      by move: lo; rewrite -mulrA; lra.
    have : 0 <= `|r| ^+ 3 / (nn * sq) by rewrite divr_ge0 ?exprn_ge0 // ltW.
    by move: up; rewrite -mulrA; lra.
  apply: le_trans e1 _.
  by rewrite ler_pM2r ?invr_gt0 //; lra.
(* large residual: both quantities are in [0, r^2 / (2 n)] *)
apply: le_trans (_ : r ^+ 2 / (2 * nn) <= _).
  rewrite -/r -/nn in d1.
  by rewrite ler_norml; apply/andP; split; lra.
apply: le_trans (_ : r ^+ 4 / (nn * sq) <= _); last first.
  by rewrite ler_pM2r ?invr_gt0 //; lra.
rewrite ler_pdivrMr ?mulr_gt0 // -mulrA mulrCA ler_pdivlMl ?mulr_gt0 //.
have e4 : r ^+ 4 = r ^+ 2 * r ^+ 2 by rewrite -exprD.
rewrite e4.
have r20 : 0 <= r ^+ 2 := sqr_ge0 r.
have h : 0 <= nn * (r ^+ 2 - sq) * r ^+ 2.
  by rewrite mulr_ge0 // mulr_ge0 ?subr_ge0 ?ltW.
have h' : 0 <= nn * r ^+ 2 * r ^+ 2 by rewrite mulr_ge0 // mulr_ge0 // ltW.
by nra.
Qed.

(* Proposition 2.14, (2.21): the size of the minimizer. *)
Lemma ins_size_le theta_ref : D theta_ref ->
  beta * (lambda * mxdot thm thm + bm ^+ 2) <=
  s * \sum_(j < n | j != i) mxdot (tnth x j) theta_ref ^+ 2 +
  beta * lambda * mxdot theta_ref theta_ref + gamma * B theta_ref.
Proof.
move=> Dr; have := thmin 0 Dr.
rewrite /ls_barrier_objective /ls_ridge /ls_loss.
have -> : \sum_(j < n | j != i) (0 - mxdot (tnth x j) theta_ref) ^+ 2 =
    \sum_(j < n | j != i) mxdot (tnth x j) theta_ref ^+ 2.
  by apply: eq_bigr => j _; rewrite sub0r sqrrN.
rewrite expr0n /= addr0 mulrA => h; apply: le_trans h.
have h1 : 0 <= s * \sum_(j < n | j != i) (bm - mxdot (tnth x j) thm) ^+ 2.
  by rewrite mulr_ge0 ?ins_s_ge0 // sumr_ge0 // => j _; exact: sqr_ge0.
have h2 : 0 <= gamma * B thm by rewrite mulr_ge0 ?B0 // ltW.
by lra.
Qed.

(* The quadratic structure of l (proof of Proposition 2.16). *)
Definition ins_c0 : R := ulsubmx (invmx H) 0 0.
Definition ins_v : 'rV[R]_N := ursubmx (invmx H) *m E.
Definition ins_T : 'M[R]_N := E^T *m drsubmx (invmx H) *m E.

Lemma ins_inv_sym : (invmx H)^T = invmx H.
Proof.
have [/symmetricmxP HT _] := ins_hessian_pd.
by rewrite trmx_inv HT.
Qed.

Lemma ins_ell_quadratic z :
  ell z = ins_c0 - 2 * mxdot ins_v z + mxdot z (z *m ins_T).
Proof.
rewrite /ins_ell /ins_alpha.
have GT := ins_inv_sym.
set G := invmx H.
have dl : dlsubmx G = (ursubmx G)^T by rewrite trmx_ursub GT.
have GE : G = block_mx (ulsubmx G) (ursubmx G) (dlsubmx G) (drsubmx G).
  by rewrite submxK.
rewrite {1}GE mul_row_block mxdot_row_mx dl !mul1mx.
have e1 (A : 'M[R]_1) : mxdot 1%:M A = A 0 0.
  by rewrite /mxdot !big_ord1 mxE mul1r.
rewrite e1 mxdotNl mxdotDr !mulNmx mxdotNr !mxE.
have e2 : \sum_j (z *m E^T) 0 j * (ursubmx G)^T j 0 =
    mxdot (z *m E^T) (ursubmx G) by rewrite mxdot_rowE mxE.
have e3 : mxdot (z *m E^T) (ursubmx G) = mxdot ins_v z.
  by rewrite mxdot_mulmxr trmxK mxdotC.
have e4 : mxdot (z *m E^T) (z *m E^T *m drsubmx G) = mxdot z (z *m ins_T).
  by rewrite mxdot_mulmxr trmxK /ins_T !mulmxA.
rewrite e2 e3 e4 /ins_c0 !mxE /G.
by ring.
Qed.

(* The variational bound behind Lemma 4.1: for a linear form
   w |-> c c_w + <y, h_w>, its squared H^-1 norm is at most
   c^2 / (2 beta) + |y|^2 / (2 beta lambda). *)
Lemma ins_form_le (a : 'rV[R]_(1 + k)) (c : R) (y : 'rV[R]_N) :
  (forall w, mxdot a w = c * cw w + mxdot y (hw w)) ->
  mxdot a (a *m invmx H) <=
  c ^+ 2 / (2 * beta) + mxdot y y / (2 * beta * lambda).
Proof.
move=> aE.
have Hu := posdefmx_unit ins_hessian_pd.
set w := a *m invmx H.
have wH : w *m H = a by rewrite -mulmxA mulVmx ?mulmx1.
have la : mxdot a w = 2 * mxdot a w - mxdot w (w *m H).
  by rewrite wH mxdotC; ring.
rewrite la aE ins_hessianE //.
have hg := ins_hform_ge w; rewrite -ins_norm_h in hg.
set X := cw w; set h := hw w.
have b0' : beta != 0 by rewrite gt_eqF.
have l0' : lambda != 0 by rewrite gt_eqF.
have A : c ^+ 2 / (2 * beta) - 2 * c * X + 2 * beta * X ^+ 2 =
    (c - 2 * beta * X) ^+ 2 / (2 * beta) by field.
have A0 : 0 <= (c - 2 * beta * X) ^+ 2 / (2 * beta).
  by rewrite divr_ge0 ?sqr_ge0 // mulr_ge0 // ltW.
have Bq : mxdot y y / (2 * beta * lambda) - 2 * mxdot y h +
    2 * beta * lambda * mxdot h h =
    mxdot (y - (2 * beta * lambda) *: h) (y - (2 * beta * lambda) *: h) /
      (2 * beta * lambda).
  rewrite !mxdotBl !mxdotBr !mxdotZl !mxdotZr [mxdot h y]mxdotC.
  by field.
have B0' : 0 <= mxdot (y - (2 * beta * lambda) *: h)
    (y - (2 * beta * lambda) *: h) / (2 * beta * lambda).
  apply: divr_ge0; first exact: mxdot_ge0.
  by rewrite !mulr_ge0 // ltW.
rewrite -/X -/h in hg.
by lra.
Qed.

Lemma ins_ell_ge0 z : 0 <= ell z.
Proof. by have [] := quad_response (alpha z) 0 ins_hessian_pd ins_nR_gt0. Qed.

Lemma ins_c0_bounds : 0 <= ins_c0 <= (2 * beta)^-1.
Proof.
have e0 : ell 0 = ins_c0.
  by rewrite ins_ell_quadratic mxdot0r mxdot0l mulr0 !subr0 addr0.
rewrite -e0 ins_ell_ge0 /=.
have := @ins_form_le (alpha 0) 1 0.
rewrite expr1n mxdot0l mul0r addr0 div1r; apply => w.
by rewrite ins_alphaE !mxdot0l mul1r subr0 addr0.
Qed.

Lemma ins_T_bounds (z : 'rV[R]_N) :
  0 <= mxdot z (z *m ins_T) <= mxdot z z / (2 * beta * lambda).
Proof.
pose a : 'rV[R]_(1 + k) := row_mx 0 (z *m E^T).
have GT := ins_inv_sym.
set G := invmx H.
have GE : G = block_mx (ulsubmx G) (ursubmx G) (dlsubmx G) (drsubmx G).
  by rewrite submxK.
have aG : mxdot a (a *m G) = mxdot z (z *m ins_T).
  rewrite {1}GE /a mul_row_block mxdot_row_mx.
  by rewrite !mul0mx !add0r mxdot0l add0r mxdot_mulmxr trmxK /ins_T !mulmxA.
rewrite -aG; apply/andP; split.
  by have [] := quad_response a 0 ins_hessian_pd ins_nR_gt0.
have := @ins_form_le a 0 z; rewrite expr0n /= mul0r add0r; apply => w.
rewrite /a -[w in LHS]hsubmxK mxdot_row_mx mxdot0l add0r mul0r add0r.
by rewrite mxdot_mulmxr trmxK.
Qed.

Lemma ins_T_sym : ins_T \is symmetricmx.
Proof.
apply/symmetricmxP.
by rewrite /ins_T !trmx_mul trmxK trmx_drsub ins_inv_sym mulmxA.
Qed.

Lemma ins_v_bound : mxdot ins_v ins_v <= k%:R / (4 * beta ^+ 2 * lambda).
Proof.
have [k0|kpos] := posnP k.
  have u0 : ursubmx (invmx H) = 0.
    apply/rowP => j; exfalso; have := ltn_ord j.
    by move: (nat_of_ord j) => jj; rewrite k0.
  by rewrite /ins_v u0 mul0mx mxdot0l k0 mul0r.
(* 0 <= l(t v) = c0 - 2 t |v|^2 + t^2 v T v^T with t = 2 beta lambda *)
have [c0 c1] := andP ins_c0_bounds.
set v := ins_v; set t := 2 * beta * lambda.
have t0 : 0 < t by rewrite !mulr_gt0.
have := ins_ell_ge0 (t *: v).
rewrite ins_ell_quadratic mxdotZr -scalemxAl !mxdotZl mxdotZr.
have [_] := andP (ins_T_bounds v); rewrite -/t => hT h.
rewrite -/v in h.
have h2 : t * (t * mxdot v (v *m ins_T)) <= t * mxdot v v.
  by rewrite ler_pM2l //; move: hT; rewrite ler_pdivlMr // mulrC.
have tv : t * mxdot v v <= (2 * beta)^-1 by lra.
apply: le_trans (_ : (2 * beta)^-1 / t <= _).
  by rewrite ler_pdivlMr // mulrC.
rewrite /t -invfM.
have -> : 2 * beta * (2 * beta * lambda) = 4 * beta ^+ 2 * lambda.
  by rewrite expr2; ring.
rewrite -[X in X <= _]mul1r ler_pM2r ?invr_gt0 ?mulr_gt0 ?exprn_gt0 //.
by rewrite ler1n.
Qed.

Lemma ins_T_frobenius :
  mxdot ins_T ins_T <= k%:R / (4 * beta ^+ 2 * lambda ^+ 2).
Proof.
set c := (2 * beta * lambda)^-1.
have c0 : 0 < c by rewrite invr_gt0 !mulr_gt0.
have TT : ins_T^T = ins_T by apply/symmetricmxP; exact: ins_T_sym.
have colE (y : 'cV[R]_N) : mxdot y (ins_T *m y) = mxdot y^T (y^T *m ins_T).
  by rewrite -mxdot_trmx trmx_mul TT.
(* the eigenvalues d_j of T are in [0, c] *)
have [P Po [d TE]] := symmetric_spectral ins_T_sym.
have dge0 : forall j, 0 <= d 0 j.
  apply/(spectral_psd Po TE) => y; rewrite colE.
  by have [] := andP (ins_T_bounds y^T).
have dle : forall j, d 0 j <= c.
  apply/(spectral_form_le c Po TE) => y; rewrite colE -mxdot_trmx mulrC.
  rewrite mxdot_trmx; have [_ h] := andP (ins_T_bounds y^T).
  by rewrite mxdot_trmx in h.
(* and their sum, the trace of T = E^T Q E, is at most k c *)
set dr := drsubmx (invmx H).
have drE : dr = E *m ins_T *m E^T.
  by rewrite /ins_T !mulmxA EE mul1mx -mulmxA EE mulmx1.
have rowd (A1 A2 : 'M[R]_(k, N)) j :
    (A1 *m A2^T) j j = mxdot (row j A1) (row j A2).
  by rewrite mxE /mxdot big_ord1; apply: eq_bigr => p _; rewrite !mxE.
have trT : \tr ins_T <= k%:R * c.
  have -> : \tr ins_T = \tr dr.
    by rewrite /ins_T mxtrace_mulC mulmxA EE mul1mx.
  rewrite /mxtrace -[k in k%:R]card_ord -sumr_const.
  rewrite mulr_suml; apply: ler_sum => j _.
  rewrite drE rowd row_mul mxdotC.
  have [_ h] := andP (ins_T_bounds (row j E)).
  apply: le_trans h _.
  have -> : mxdot (row j E) (row j E) = 1.
    by rewrite -rowd EE mxE eqxx.
  by rewrite mul1r.
rewrite (spectral_mxdot Po TE).
apply: le_trans (_ : \sum_j c * d 0 j <= _).
  by apply: ler_sum => j _; rewrite expr2 ler_wpM2r.
rewrite -mulr_sumr -(spectral_trace Po TE).
apply: le_trans (ler_wpM2l (ltW c0) trT) _.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
have b0' : beta != 0 by rewrite gt_eqF.
have l0' : lambda != 0 by rewrite gt_eqF.
by rewrite /c; field.
Qed.

End insertion.
