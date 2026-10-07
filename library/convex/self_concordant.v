From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import interval boolp classical_sets functions reals.
From mathcomp Require Import set_interval topology normedtype derive realfun.
From mathcomp Require Import exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import euclidean real_spectral.

(**md**************************************************************************)
(* # Self-concordant functions and barriers                                   *)
(*                                                                            *)
(* Self-concordant functions and barriers in the sense of Nesterov and        *)
(* Nemirovskii (Interior-point polynomial algorithms, Definition 2.3.1), on a *)
(* convex set D of 'rV[R]_N that is open in its affine hull z + V, with V a   *)
(* subspace. Derivatives are taken along the directions h of V, with          *)
(* MathComp's directional derivative 'D_h. A self-concordant function is      *)
(* convex, three times differentiable along V, its first and second           *)
(* derivatives are a linear and a quadratic form, it tends to +oo at the      *)
(* relative boundary of D, and                                                *)
(*   (SC)  |D^3 B(z)[h, h, h]| <= 2 (D^2 B(z)[h, h])^(3/2),                   *)
(* written (D^3 B(z)[h, h, h])^2 <= 4 (D^2 B(z)[h, h])^3. A theta-self-       *)
(* concordant barrier satisfies moreover                                      *)
(*   (BP)  (D B(z)[h])^2 <= theta D^2 B(z)[h, h].                             *)
(* These are the notions of Koehler and Sohn, Universality and sharp          *)
(* thresholds for ellipsoid fitting (arXiv 2608.27372), Definition 2.7.       *)
(*                                                                            *)
(* ```                                                                        *)
(*    rel_open_convex V D == D is convex, y - z is in V for y, z in D, and    *)
(*                           around each z of D, D contains the points z + h  *)
(*                           with h in V and `|h| < e for some e > 0: D is    *)
(*                           relatively open in its affine hull z + V         *)
(*      sc_function V D B == B is a self-concordant function on D with        *)
(*                           directions V: three times differentiable along   *)
(*                           V, with a gradient vector and a Hessian matrix,  *)
(*                           convex, (SC), and B (z + t h) tends to +oo when  *)
(*                           t tends to 1 from the left, if z + t h is in D   *)
(*                           for 0 <= t < 1 and z + h is not                  *)
(* sc_barrier V D theta B == B is a theta-self-concordant barrier: a          *)
(*                           self-concordant function with (BP)               *)
(*          sc_norm B z h == the local norm sqrt (D^2 B(z)[h, h])             *)
(*      bregman_div B y z == the Bregman divergence B y - B z - D B(z)[y - z] *)
(*             sc_omega r == r - ln (1 + r)                                   *)
(*        sc_omega_star r == - r - ln (1 - r)                                 *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results, for D relatively open and convex with directions V, B a      *)
(* self-concordant function on D, z in D, h in V and r = sc_norm B z h:       *)
(* - sc_hessian_line_ge, sc_hessian_line_le: for t >= 0 with z + t h in D,    *)
(*   r^2 / (1 + t r)^2 <= D^2 B(z + t h)[h, h], and D^2 B(z + t h)[h, h] is   *)
(*   at most r^2 / (1 - t r)^2 when moreover t r < 1 (Koehler-Sohn, proof of  *)
(*   Lemma 2.15); the one-dimensional comparison is sc_ode_ge, sc_ode_le.     *)
(* - sc_dikin: the Dikin ellipsoid: if r < 1, then z + h is in D              *)
(*   (Nesterov-Nemirovskii, Theorem 2.1.1).                                   *)
(* - sc_bregman_ge, sc_bregman_le: sc_omega r <= bregman_div B (z + h) z when *)
(*   z + h is in D, and bregman_div B (z + h) z <= sc_omega_star r when       *)
(*   r < 1.                                                                   *)
(* - sc_bregman_small (Lemma 2.15 (i)): if z + h is in D and                  *)
(*   bregman_div B (z + h) z <= sc_omega (1/2), then r <= 1/2 and             *)
(*   r^2 / 3 <= bregman_div B (z + h) z.                                      *)
(* - sc_taylor3 (Lemma 2.15 (ii)): if r <= 1/2, then z + h is in D and        *)
(*   |B (z + h) - B z - D B(z)[h] - r^2 / 2| <= 2 r^3 / 3.                    *)
(* - sc_function_convex, sc_function_continuous: B is convex on D, and        *)
(*   continuous at every point of D for the points of D.                      *)
(* - sc_barrier_grad_le (Lemma 2.10, Nesterov Theorem 4.2.4): for a           *)
(*   theta-self-concordant barrier with theta >= 0 and y, z in D,             *)
(*   D B(z)[y - z] <= theta.                                                  *)
(* - sc_barrier_contraction (Lemma 2.10): for x0, x in D and 0 < eps < 1,     *)
(*   B ((1 - eps) x + eps x0) <= B x0 + theta ln (1 / eps).                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section self_concordant_definitions.
Context {R : realType} {N : nat}.
Implicit Types (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N)
  (B : 'rV[R]_N -> R).

Definition rel_open_convex V D :=
  [/\ forall z y (t : R), D z -> D y -> 0 <= t <= 1 -> D (z + t *: (y - z)),
      forall z y, D z -> D y -> y - z \in V &
      forall z, D z -> exists2 e : R, 0 < e &
        forall h, h \in V -> `|h| < e -> D (z + h)].

Definition sc_function V D B :=
  [/\ forall z h, D z -> h \in V ->
        [/\ derivable B z h, derivable ('D_h B) z h &
            derivable ('D_h ('D_h B)) z h],
      forall z, D z -> exists (g : 'rV[R]_N) (M : 'M[R]_N),
        forall h, h \in V ->
          'D_h B z = mxdot g h /\ 'D_h ('D_h B) z = mxdot h (h *m M),
      forall z h, D z -> h \in V -> 0 <= 'D_h ('D_h B) z,
      forall z h, D z -> h \in V ->
        ('D_h ('D_h ('D_h B)) z) ^+ 2 <= 4%:R * ('D_h ('D_h B) z) ^+ 3 &
      forall z h, D z -> h \in V ->
        (forall t, 0 <= t < 1 -> D (z + t *: h)) -> ~ D (z + h) ->
        B (z + t *: h) @[t --> (1 : R)^'-] --> +oo].

Definition sc_barrier V D (theta : R) B :=
  sc_function V D B /\
  forall z h, D z -> h \in V -> ('D_h B z) ^+ 2 <= theta * 'D_h ('D_h B) z.

Definition sc_norm B (z h : 'rV[R]_N) : R := Num.sqrt ('D_h ('D_h B) z).

Definition bregman_div B (y z : 'rV[R]_N) : R := B y - B z - 'D_(y - z) B z.

Definition sc_omega (r : R) : R := r - ln (1 + r).

Definition sc_omega_star (r : R) : R := - r - ln (1 - r).

End self_concordant_definitions.

Section one_dimensional.
Context {R : realType}.
Implicit Types (f df : R -> R) (a b : R).

(* A function with a nonnegative derivative on [a, b] is nondecreasing on
   [a, b]. *)
Lemma derive_ge0_le f df a b : a <= b ->
  (forall x, a <= x <= b -> is_derive x 1 f (df x)) ->
  (forall x, a <= x <= b -> 0 <= df x) -> f a <= f b.
Proof.
move=> ab fd dfge0.
have cf : {within `[a, b], continuous f}.
  apply: continuous_subspace_itv => x; rewrite in_itv /= => xab.
  have [d _] := fd x xab.
  exact/differentiable_continuous/derivable1_diffP.
have fd' x : x \in `]a, b[ -> is_derive x 1 f (df x).
  by rewrite in_itv /= => /andP[ax xb]; apply: fd; rewrite !ltW.
have [c] := MVT_segment ab fd' cf.
rewrite in_itv /= => cab; move/eqP; rewrite subr_eq => /eqP ->.
by rewrite lerDr mulr_ge0 ?subr_ge0 // dfge0.
Qed.

(* A function with a nonpositive derivative on [a, b] is nonincreasing on
   [a, b]. *)
Lemma derive_le0_le f df a b : a <= b ->
  (forall x, a <= x <= b -> is_derive x 1 f (df x)) ->
  (forall x, a <= x <= b -> df x <= 0) -> f b <= f a.
Proof.
move=> ab fd dfle0; rewrite -lerN2.
apply: (@derive_ge0_le (fun x => - f x) (fun x => - df x)) => // x xab.
  exact: is_deriveN (fd x xab).
by rewrite oppr_ge0 dfle0.
Qed.

(* A function whose second derivative is nonnegative on [a, b] lies above
   its tangents there. *)
Lemma derive2_ge0_tangent f f1 f2 a b s t :
  (forall x, a <= x <= b -> is_derive x 1 f (f1 x)) ->
  (forall x, a <= x <= b -> is_derive x 1 f1 (f2 x)) ->
  (forall x, a <= x <= b -> 0 <= f2 x) ->
  a <= s <= b -> a <= t <= b -> f t + f1 t * (s - t) <= f s.
Proof.
move=> fd f1d f2ge0 /andP[aS sb] /andP[aT tb].
pose w x := f x - (f t + f1 t * (x - t)).
have wd x : a <= x <= b -> is_derive x 1 w (f1 x - f1 t).
  move=> xab; have := fd x xab => fx; apply: is_derive_eq.
  by rewrite add0r mul1r subr0 [_ *: _]mulr1.
suff : 0 <= w s by rewrite subr_ge0.
have wt : w t = 0 by rewrite /w subrr mulr0 addr0 subrr.
have f1le x y : a <= x -> x <= y -> y <= b -> f1 x <= f1 y.
  move=> ax xy yb; apply: (derive_ge0_le xy) => [z /andP[xz zy]|z /andP[xz zy]].
    by apply: f1d; rewrite (le_trans ax xz) (le_trans zy yb).
  by apply: f2ge0; rewrite (le_trans ax xz) (le_trans zy yb).
case: (leP t s) => [ts|st].
  rewrite -wt; apply: (@derive_ge0_le w (fun x => f1 x - f1 t) _ _ ts).
    move=> z /andP[tz zs]; apply: wd.
    by rewrite (le_trans aT tz) (le_trans zs sb).
  move=> z /andP[tz zs].
  by rewrite subr_ge0; apply: f1le => //; rewrite (le_trans zs sb).
rewrite -wt; apply: (@derive_le0_le w (fun x => f1 x - f1 t) _ _ (ltW st)).
  move=> z /andP[sz zt]; apply: wd.
  by rewrite (le_trans aS sz) (le_trans zt tb).
move=> z /andP[sz zt].
by rewrite subr_le0; apply: f1le => //; rewrite (le_trans aS sz).
Qed.

(* The comparison behind Lemma 2.15 of Koehler and Sohn: let psi >= 0 have
   the derivative dpsi on [0, T] with dpsi^2 <= 4 psi^3. Then for e > 0,
   t |-> 1 / sqrt (psi t + e) has a derivative of absolute value at most 1
   on [0, T]. *)
Lemma sc_ode_inv (psi dpsi : R -> R) (T e : R) : 0 <= T -> 0 < e ->
  (forall x, 0 <= x <= T -> is_derive x 1 psi (dpsi x)) ->
  (forall x, 0 <= x <= T -> 0 <= psi x) ->
  (forall x, 0 <= x <= T -> dpsi x ^+ 2 <= 4%:R * psi x ^+ 3) ->
  (Num.sqrt (psi T + e))^-1 - T <= (Num.sqrt (psi 0 + e))^-1 <=
    (Num.sqrt (psi T + e))^-1 + T.
Proof.
move=> T0 e0 pd pge0 sc.
pose q x := Num.sqrt (psi x + e).
have pe x : 0 <= x <= T -> 0 < psi x + e by move=> xT; rewrite ltr_wpDl // pge0.
have qgt0 x : 0 <= x <= T -> 0 < q x by move=> xT; rewrite sqrtr_gt0 pe.
have qd x : 0 <= x <= T -> is_derive x 1 q ((2 * q x)^-1 * dpsi x).
  move=> xT; have hs := is_derive1_sqrt (pe x xT).
  have hg : is_derive x 1 (fun y => psi y + e) (dpsi x).
    apply: is_derive_eq.
      exact: is_deriveD (pd x xT) (is_derive_cst e x 1).
    by rewrite addr0.
  exact: (@is_derive1_comp R Num.sqrt (fun y => psi y + e) x _ _ hs hg).
have q2 x : 0 <= x <= T -> q x ^+ 2 = psi x + e.
  by move=> xT; rewrite sqr_sqrtr // ltW // pe.
have dle x : 0 <= x <= T -> `|dpsi x| <= 2 * q x ^+ 3.
  move=> xT; have q0 : 0 <= 2 * q x ^+ 3.
    by rewrite mulr_ge0 ?exprn_ge0 // ltW // qgt0.
  rewrite -(@ler_pXn2r _ 2) ?nnegrE ?normr_ge0 // real_normK ?num_real //.
  have q6 : q x ^+ 3 ^+ 2 = (psi x + e) ^+ 3 by rewrite -exprM mulnC exprM q2.
  have h4 : 2 ^+ 2 = 4 :> R by rewrite expr2 -natrM.
  rewrite exprMn q6 h4; apply: (le_trans (sc x xT)).
  rewrite ler_pM2l ?ltr0n // lerXn2r ?nnegrE ?pge0 // ?(ltW (pe x xT)) //.
  by rewrite lerDl ltW.
have qVd x : 0 <= x <= T ->
    is_derive x 1 (fun y => (q y)^-1) (- dpsi x / (2 * q x ^+ 3)).
  move=> xT; have := is_deriveV (lt0r_neq0 (qgt0 x xT)) (qd x xT).
  move=> h; apply: is_derive_eq h _.
  have qx0 : q x != 0 by rewrite lt0r_neq0 // qgt0.
  by rewrite /GRing.scale /=; field.
have dbound x : 0 <= x <= T -> `|- dpsi x / (2 * q x ^+ 3)| <= 1.
  move=> xT; have q3 : 0 < 2 * q x ^+ 3 by rewrite mulr_gt0 ?exprn_gt0 ?qgt0.
  rewrite normrM normrN normfV [`|2 * _|]gtr0_norm // ler_pdivrMr // mul1r.
  exact: dle.
apply/andP; split.
  have := @derive_le0_le (fun y => (q y)^-1 - y)
    (fun x => - dpsi x / (2 * q x ^+ 3) - 1) 0 T T0.
  rewrite subr0; apply => x xT.
    by have := is_deriveB (qVd x xT) (is_derive_id x 1).
  by rewrite subr_le0; apply: le_trans (ler_norm _) (dbound x xT).
have := @derive_ge0_le (fun y => (q y)^-1 + y)
  (fun x => - dpsi x / (2 * q x ^+ 3) + 1) 0 T T0.
rewrite addr0; apply => x xT.
  by have := is_deriveD (qVd x xT) (is_derive_id x 1).
by move: (dbound x xT); rewrite ler_norml => /andP[h _]; lra.
Qed.

(* Then r^2 / (1 + t r)^2 <= psi t, and psi t <= r^2 / (1 - t r)^2 when
   t r < 1, for t = T and r^2 = psi 0. *)
Lemma sc_ode_ge (psi dpsi : R -> R) (T : R) : 0 <= T ->
  (forall x, 0 <= x <= T -> is_derive x 1 psi (dpsi x)) ->
  (forall x, 0 <= x <= T -> 0 <= psi x) ->
  (forall x, 0 <= x <= T -> dpsi x ^+ 2 <= 4%:R * psi x ^+ 3) ->
  psi 0 / (1 + T * Num.sqrt (psi 0)) ^+ 2 <= psi T.
Proof.
move=> T0 pd pge0 sc; apply/ler_addgt0Pr => e e0.
have /andP[kle _] := sc_ode_inv T0 e0 pd pge0 sc.
have T0T : (0:R) <= 0 <= T by rewrite lexx T0.
have TTT : 0 <= T <= T by rewrite T0 lexx.
have pe x : 0 <= x <= T -> 0 < psi x + e by move=> xT; rewrite ltr_wpDl // pge0.
set r := Num.sqrt (psi 0); set rho := Num.sqrt (psi 0 + e).
set a := Num.sqrt (psi T + e) in kle *.
have r0 : 0 <= r := sqrtr_ge0 _.
have rho0 : 0 < rho by rewrite sqrtr_gt0 pe.
have a0 : 0 < a by rewrite sqrtr_gt0 pe.
have rrho : r <= rho by rewrite ler_sqrt ?lerDl ?ltW // pe.
have psi0 : psi 0 = r ^+ 2 by rewrite sqr_sqrtr // pge0.
have k2 : rho <= a + a * rho * T.
  have ainv : a^-1 <= rho^-1 + T by move: kle; rewrite lerBlDr.
  have := ler_wpM2l (ltW (mulr_gt0 a0 rho0)) ainv.
  rewrite mulrAC mulfV ?lt0r_neq0 // mul1r mulrDr.
  by rewrite -[a * rho * rho^-1]mulrA mulfV ?lt0r_neq0 // mulr1.
have Tr0 : 0 < 1 + T * r by rewrite ltr_wpDr // mulr_ge0.
have ra : r / (1 + T * r) <= a.
  by rewrite ler_pdivrMr //; have [aT1|aT1] := leP (a * T) 1; nra.
have ra0 : 0 <= r / (1 + T * r) by rewrite divr_ge0 // ltW.
have aE : psi T + e = a ^+ 2 by rewrite sqr_sqrtr // ltW // pe.
by rewrite psi0 aE -expr_div_n lerXn2r ?nnegrE //; exact: ltW.
Qed.

Lemma sc_ode_le (psi dpsi : R -> R) (T : R) : 0 <= T ->
  (forall x, 0 <= x <= T -> is_derive x 1 psi (dpsi x)) ->
  (forall x, 0 <= x <= T -> 0 <= psi x) ->
  (forall x, 0 <= x <= T -> dpsi x ^+ 2 <= 4%:R * psi x ^+ 3) ->
  T * Num.sqrt (psi 0) < 1 ->
  psi T <= psi 0 / (1 - T * Num.sqrt (psi 0)) ^+ 2.
Proof.
move=> T0 pd pge0 sc.
set r := Num.sqrt (psi 0) => Tr1.
have r0 : 0 <= r := sqrtr_ge0 _.
have psi0 : psi 0 = r ^+ 2 by rewrite sqr_sqrtr // pge0 // lexx T0.
have key rho : r < rho -> T * rho < 1 -> psi T <= rho ^+ 2 / (1 - T * rho) ^+ 2.
  move=> rrho Trho.
  have rho0 : 0 < rho by apply: le_lt_trans rrho.
  pose e := rho ^+ 2 - psi 0.
  have e0 : 0 < e by rewrite subr_gt0 psi0 ltrXn2r // nnegrE ltW.
  have /andP[_ kge] := sc_ode_inv T0 e0 pd pge0 sc.
  have rhoE : Num.sqrt (psi 0 + e) = rho.
    by rewrite /e addrC subrK sqrtr_sqr gtr0_norm.
  rewrite rhoE in kge; set a := Num.sqrt (psi T + e) in kge.
  have pTe : 0 < psi T + e by rewrite ltr_wpDl // pge0 // T0 lexx.
  have a0 : 0 < a by rewrite sqrtr_gt0.
  have aE : psi T + e = a ^+ 2 by rewrite sqr_sqrtr // ltW.
  have Trho0 : 0 < 1 - T * rho by rewrite subr_gt0.
  have arho : a <= rho / (1 - T * rho).
    rewrite ler_pdivlMr //.
    have ainv : rho^-1 - T <= a^-1 by rewrite lerBlDr.
    have := ler_wpM2l (ltW (mulr_gt0 a0 rho0)) ainv.
    rewrite mulrBr -[a * rho * rho^-1]mulrA mulfV ?lt0r_neq0 // mulr1.
    by rewrite [a * rho / a]mulrAC mulfV ?lt0r_neq0 // mul1r => h; nra.
  apply: (@le_trans _ _ (a ^+ 2)); first by rewrite -aE lerDl ltW.
  have rt0 : 0 <= rho / (1 - T * rho) by rewrite divr_ge0 // ltW.
  by rewrite -expr_div_n lerXn2r ?nnegrE //; exact: ltW.
rewrite leNgt; apply/negP => Y.
set x := Num.sqrt (psi T).
have x0 : 0 <= x := sqrtr_ge0 _.
have xE : psi T = x ^+ 2 by rewrite sqr_sqrtr // pge0 // T0 lexx.
have Tr0 : 0 < 1 - T * r by rewrite subr_gt0.
have rT0 : 0 <= r / (1 - T * r) by rewrite divr_ge0 // ltW.
have rx : r / (1 - T * r) < x.
  move: Y; rewrite psi0 xE -expr_div_n.
  by set q := r / (1 - T * r) in rT0 *; move=> h; nra.
have Tx0 : 0 < 1 + T * x by rewrite ltr_wpDr // mulr_ge0.
pose rs := x / (1 + T * x).
have rrs : r < rs.
  by rewrite ltr_pdivlMr //; move: rx; rewrite ltr_pdivrMr //; nra.
pose rho := (r + rs) / 2.
have r_rho : r < rho by rewrite /rho ltr_pdivlMr //; lra.
have rho_rs : rho < rs by rewrite /rho ltr_pdivrMr //; lra.
have Trs : T * rs < 1 by rewrite /rs mulrA ltr_pdivrMr // mul1r ltrDr.
have Trho : T * rho < 1 by apply: le_lt_trans Trs; rewrite ler_wpM2l // ltW.
have := key rho r_rho Trho; apply/negP; rewrite -ltNge xE.
have Trho0 : 0 < 1 - T * rho by rewrite subr_gt0.
have rho0 : 0 <= rho / (1 - T * rho).
  by rewrite divr_ge0 ?ltW // (le_lt_trans r0).
have rhox : rho / (1 - T * rho) < x.
  by rewrite ltr_pdivrMr //; move: rho_rs; rewrite /rs ltr_pdivlMr //; nra.
by rewrite -expr_div_n; set q := rho / (1 - T * rho) in rho0 rhox *; nra.
Qed.

(* The derivatives of omega and omega_star, and of the functions
   t |-> omega (t r) and t |-> omega_star (t r) of the Bregman bounds. *)
Lemma is_derive_sc_omega (x : R) : -1 < x ->
  is_derive x 1 sc_omega (x / (1 + x)).
Proof.
move=> x1; have x0 : 0 < 1 + x by rewrite -ltrBlDl sub0r.
have hg : is_derive x 1 (fun y : R => 1 + y) 1.
  by apply: is_derive_eq; rewrite add0r mulr1.
have hc := @is_derive1_comp R (@ln R) (fun y : R => 1 + y) x _ _
  (is_derive1_ln x0) hg.
have := is_deriveB (is_derive_id x 1) hc.
have -> : sc_omega = id - (@ln R \o (fun y : R => 1 + y)) by [].
move=> h; apply: is_derive_eq h _.
have x0' : 1 + x != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma is_derive_sc_omega_star (x : R) : x < 1 ->
  is_derive x 1 sc_omega_star (x / (1 - x)).
Proof.
move=> x1; have x0 : 0 < 1 - x by rewrite subr_gt0.
have hg : is_derive x 1 (fun y : R => 1 - y) (-1).
  by apply: is_derive_eq; rewrite add0r mul1r.
have hc := @is_derive1_comp R (@ln R) (fun y : R => 1 - y) x _ _
  (is_derive1_ln x0) hg.
have := is_deriveB (is_deriveNid x 1) hc.
have -> : sc_omega_star = -%R - (@ln R \o (fun y : R => 1 - y)) by [].
move=> h; apply: is_derive_eq h _.
have x0' : 1 - x != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma is_derive_omega_line (r t : R) : 0 < 1 + t * r ->
  is_derive t 1 (fun s => s * r - ln (1 + s * r)) (r - r / (1 + t * r)).
Proof.
move=> tr0.
have hg : is_derive t 1 (fun s : R => 1 + s * r) r.
  by apply: is_derive_eq; rewrite add0r mul1r scaler0 add0r [_%:A]mulr1.
have hm : is_derive t 1 (fun s : R => s * r) r.
  by apply: is_derive_eq; rewrite scaler0 add0r [_%:A]mulr1.
have hc := @is_derive1_comp R (@ln R) (fun s : R => 1 + s * r) t _ _
  (is_derive1_ln tr0) hg.
have := is_deriveB hm hc.
have -> : (fun s => s * r - ln (1 + s * r)) =
  (fun s : R => s * r) - (@ln R \o (fun s : R => 1 + s * r)) by [].
move=> h; apply: is_derive_eq h _.
by rewrite mulrC.
Qed.

Lemma is_derive_omega_line1 (r t : R) : 0 < 1 + t * r ->
  is_derive t 1 (fun s => r - r / (1 + s * r)) (r ^+ 2 / (1 + t * r) ^+ 2).
Proof.
move=> tr0.
have hg : is_derive t 1 (fun s : R => 1 + s * r) r.
  by apply: is_derive_eq; rewrite add0r mul1r scaler0 add0r [_%:A]mulr1.
have tr0' : 1 + t * r != 0 by rewrite gt_eqF.
have hv := @is_deriveV R (fun s : R => 1 + s * r) t r 1 tr0' hg.
have := is_deriveB (is_derive_cst r t 1) (is_deriveZ r hv).
have -> : (fun s => r - r / (1 + s * r)) =
  cst r - r *: (fun s : R => (1 + s * r)^-1) by [].
move=> h; apply: is_derive_eq h _.
by rewrite /GRing.scale /=; field.
Qed.

Lemma is_derive_omega_star_line (r t : R) : 0 < 1 - t * r ->
  is_derive t 1 (fun s => - (s * r) - ln (1 - s * r)) (r / (1 - t * r) - r).
Proof.
move=> tr0.
have hg : is_derive t 1 (fun s : R => 1 - s * r) (- r).
  by apply: is_derive_eq; rewrite add0r mul1r scaler0 add0r [_%:A]mulr1.
have hm : is_derive t 1 (fun s : R => - (s * r)) (- r).
  by apply: is_derive_eq; rewrite scaler0 add0r [_%:A]mulr1.
have hc := @is_derive1_comp R (@ln R) (fun s : R => 1 - s * r) t _ _
  (is_derive1_ln tr0) hg.
have := is_deriveB hm hc.
have -> : (fun s => - (s * r) - ln (1 - s * r)) =
  (fun s : R => - (s * r)) - (@ln R \o (fun s : R => 1 - s * r)) by [].
move=> h; apply: is_derive_eq h _.
have tr0' : 1 - t * r != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma is_derive_omega_star_line1 (r t : R) : 0 < 1 - t * r ->
  is_derive t 1 (fun s => r / (1 - s * r) - r) (r ^+ 2 / (1 - t * r) ^+ 2).
Proof.
move=> tr0.
have hg : is_derive t 1 (fun s : R => 1 - s * r) (- r).
  by apply: is_derive_eq; rewrite add0r mul1r scaler0 add0r [_%:A]mulr1.
have tr0' : 1 - t * r != 0 by rewrite gt_eqF.
have hv := @is_deriveV R (fun s : R => 1 - s * r) t (- r) 1 tr0' hg.
have := is_deriveB (is_deriveZ r hv) (is_derive_cst r t 1).
have -> : (fun s => r / (1 - s * r) - r) =
  r *: (fun s : R => (1 - s * r)^-1) - cst r by [].
move=> h; apply: is_derive_eq h _.
by rewrite /GRing.scale /=; field.
Qed.

Lemma sc_omega0 : sc_omega (0 : R) = 0.
Proof. by rewrite /sc_omega addr0 ln1 subr0. Qed.

Lemma sc_omega_star0 : sc_omega_star (0 : R) = 0.
Proof. by rewrite /sc_omega_star -[X in ln X]/(1 - 0 : R) subr0 ln1; lra. Qed.

Lemma sc_omega_ge0 (r : R) : 0 <= r -> 0 <= sc_omega r.
Proof.
move=> r0; rewrite -sc_omega0.
apply: (@derive_ge0_le sc_omega (fun x => x / (1 + x)) 0 r r0) => x /andP[x0 _].
  by apply: is_derive_sc_omega; lra.
by rewrite divr_ge0 // addr_ge0.
Qed.

(* r^2 / 3 <= omega r <= r^2 / 2 for 0 <= r <= 1/2, and the Taylor bounds
   of order 3 that the second part of Lemma 2.15 uses. *)
Lemma sc_omega_ge (r : R) : 0 <= r -> r <= 2^-1 -> r ^+ 2 / 3%:R <= sc_omega r.
Proof.
move=> r0 r2; rewrite -subr_ge0.
have -> : 0 = sc_omega 0 - (0 : R) ^+ 2 / 3%:R.
  by rewrite sc_omega0 expr0n /= mul0r subrr.
apply: (@derive_ge0_le (fun x => sc_omega x - x ^+ 2 / 3%:R)
  (fun x => x / (1 + x) - 2 * x / 3%:R) 0 r r0) => x /andP[x0 xr].
  have hq : is_derive x 1 (fun x : R => x ^+ 2 / 3%:R) (2 * x / 3%:R).
    by apply: is_derive_eq; rewrite ?scaler0 ?add0r /GRing.scale /=; field.
  have hw : is_derive x 1 sc_omega (x / (1 + x)).
    by apply: is_derive_sc_omega; lra.
  exact: is_deriveB hw hq.
have x1 : 1 + x != 0 by rewrite gt_eqF // ltr_wpDr.
have -> : x / (1 + x) - 2 * x / 3%:R = x * (1 - 2 * x) / (3%:R * (1 + x)).
  by field.
have h2 : 2 * x <= 1.
  by move: (le_trans xr r2); rewrite -[2^-1]mul1r ler_pdivlMr // => h; lra.
apply: divr_ge0; last by rewrite mulr_ge0 // addr_ge0.
by rewrite mulr_ge0 // subr_ge0.
Qed.

Lemma sc_omega_le (r : R) : 0 <= r -> sc_omega r <= r ^+ 2 / 2.
Proof.
move=> r0; rewrite -subr_ge0.
have -> : 0 = (0 : R) ^+ 2 / 2 - sc_omega 0.
  by rewrite sc_omega0 expr0n /= mul0r subrr.
apply: (@derive_ge0_le (fun x => x ^+ 2 / 2 - sc_omega x)
  (fun x => x - x / (1 + x)) 0 r r0) => x /andP[x0 _].
  have hq : is_derive x 1 (fun x : R => x ^+ 2 / 2) x.
    by apply: is_derive_eq; rewrite ?scaler0 ?add0r /GRing.scale /=; field.
  have hw : is_derive x 1 sc_omega (x / (1 + x)).
    by apply: is_derive_sc_omega; lra.
  exact: is_deriveB hq hw.
have x1 : 1 + x != 0 by rewrite gt_eqF // ltr_wpDr.
have -> : x - x / (1 + x) = x ^+ 2 / (1 + x) by field.
by rewrite divr_ge0 ?sqr_ge0 // addr_ge0.
Qed.

Lemma sc_omega_taylor (r : R) : 0 <= r ->
  r ^+ 2 / 2 - r ^+ 3 / 3%:R <= sc_omega r.
Proof.
move=> r0; rewrite -subr_ge0.
have -> : 0 = sc_omega 0 - ((0 : R) ^+ 2 / 2 - (0 : R) ^+ 3 / 3%:R).
  by rewrite sc_omega0 !expr0n /= !mul0r subrr subrr.
apply: (@derive_ge0_le (fun x => sc_omega x - (x ^+ 2 / 2 - x ^+ 3 / 3%:R))
  (fun x => x / (1 + x) - (x - x ^+ 2)) 0 r r0) => x /andP[x0 _].
  have hq : is_derive x 1 (fun x : R => x ^+ 2 / 2 - x ^+ 3 / 3%:R)
      (x - x ^+ 2).
    apply: is_derive_eq.
    by rewrite ?scaler0 ?add0r ?addr0 /GRing.scale /=; field.
  have hw : is_derive x 1 sc_omega (x / (1 + x)).
    by apply: is_derive_sc_omega; lra.
  exact: is_deriveB hw hq.
have x1 : 1 + x != 0 by rewrite gt_eqF // ltr_wpDr.
have -> : x / (1 + x) - (x - x ^+ 2) = x ^+ 3 / (1 + x) by field.
by rewrite divr_ge0 ?exprn_ge0 // addr_ge0.
Qed.

Lemma sc_omega_star_taylor (r : R) : 0 <= r -> r <= 2^-1 ->
  sc_omega_star r <= r ^+ 2 / 2 + 2 * r ^+ 3 / 3%:R.
Proof.
move=> r0 r2; rewrite -subr_ge0.
have -> : 0 = (0 : R) ^+ 2 / 2 + 2 * (0 : R) ^+ 3 / 3%:R - sc_omega_star 0.
  by rewrite sc_omega_star0 !expr0n /= !mul0r mulr0 mul0r addr0 subrr.
apply: (@derive_ge0_le
  (fun x => x ^+ 2 / 2 + 2 * x ^+ 3 / 3%:R - sc_omega_star x)
  (fun x => x + 2 * x ^+ 2 - x / (1 - x)) 0 r r0) => x /andP[x0 xr].
  have hq : is_derive x 1 (fun x : R => x ^+ 2 / 2 + 2 * x ^+ 3 / 3%:R)
      (x + 2 * x ^+ 2).
    apply: is_derive_eq.
    by rewrite ?scaler0 ?add0r ?addr0 /GRing.scale /=; field.
  have hw : is_derive x 1 sc_omega_star (x / (1 - x)).
    by apply: is_derive_sc_omega_star; lra.
  exact: is_deriveB hq hw.
have x1 : 1 - x != 0 by rewrite gt_eqF // subr_gt0; lra.
have -> : x + 2 * x ^+ 2 - x / (1 - x) = x ^+ 2 * (1 - 2 * x) / (1 - x).
  by field.
by rewrite divr_ge0 ?mulr_ge0 ?sqr_ge0 // subr_ge0; lra.
Qed.

Lemma sc_omega_gt_half (r : R) : 2^-1 < r -> sc_omega 2^-1 < sc_omega r.
Proof.
move=> r2.
have h2 : (0 : R) < 2^-1 by rewrite invr_gt0.
suff : sc_omega 2^-1 - 2^-1 / 3%:R <= sc_omega r - r / 3%:R by lra.
apply: (@derive_ge0_le (fun x => sc_omega x - x / 3%:R)
  (fun x => x / (1 + x) - 3%:R^-1) _ _ (ltW r2)) => x /andP[x2 _].
  have hq : is_derive x 1 (fun x : R => x / 3%:R) 3%:R^-1.
    by apply: is_derive_eq; rewrite ?scaler0 ?add0r /GRing.scale /=; field.
  have hw : is_derive x 1 sc_omega (x / (1 + x)).
    by apply: is_derive_sc_omega; lra.
  exact: is_deriveB hw hq.
have x1 : 1 + x != 0 by rewrite gt_eqF //; lra.
have -> : x / (1 + x) - 3%:R^-1 = (2 * x - 1) / (3%:R * (1 + x)) by field.
by rewrite divr_ge0 ?mulr_ge0 //; lra.
Qed.

End one_dimensional.

Section line.
Context {R : realType} {N : nat}.
Implicit Types (f : 'rV[R]_N -> R) (a h : 'rV[R]_N).

(* The derivative of t |-> f (a + t h) at t is the derivative of f at
   a + t h along h. *)
Lemma is_derive_line f a h (t : R) : derivable f (a + t *: h) h ->
  is_derive t 1 (fun s => f (a + s *: h)) ('D_h f (a + t *: h)).
Proof.
move=> df.
have E : (fun s : R => s^-1 *: (((fun s => f (a + s *: h)) \o shift t) (s *: 1)
           - f (a + t *: h))) =
         (fun s : R => s^-1 *: ((f \o shift (a + t *: h)) (s *: h)
           - f (a + t *: h))).
  apply/funext => s /=; congr (_ *: (f _ - _)).
  by rewrite [s *: 1]mulr1 scalerDl addrCA addrC.
apply: DeriveDef; first by rewrite /derivable E.
by rewrite /derive E.
Qed.

End line.

Section sc_line.
Context {R : realType} {N : nat}.
Variables (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) (B : 'rV[R]_N -> R).
Hypothesis DV : rel_open_convex V D.

(* D contains the segment from z to z + t h. *)
Lemma rel_open_convex_segment z h (t s : R) : D z -> D (z + t *: h) ->
  0 <= s <= t -> D (z + s *: h).
Proof.
move=> Dz Dt /andP[s0 st].
have [cvx _ _] := DV.
have [t0|tpos] := eqVneq t 0.
  have -> : s = 0 by apply/eqP; rewrite eq_le s0 andbT -t0.
  by rewrite scale0r addr0.
have tgt0 : 0 < t by rewrite lt_neqAle eq_sym tpos (le_trans s0 st).
have st1 : 0 <= s / t <= 1.
  by rewrite divr_ge0 ?(ltW tgt0) //= ler_pdivrMr // mul1r.
have := cvx z (z + t *: h) (s / t) Dz Dt st1.
by rewrite (addrC z (t *: h)) addrK scalerA mulfVK ?gt_eqF.
Qed.

(* D contains z + t h for t near 0, when z is in D and h in V. *)
Lemma rel_open_convex_line z h : D z -> h \in V ->
  exists2 e : R, 0 < e & forall t, `|t| < e -> D (z + t *: h).
Proof.
move=> Dz hV; have [_ _ op] := DV.
have [e0 e0pos De] := op z Dz.
have h1 : 0 < `|h| + 1 by rewrite ltr_wpDl.
exists (e0 / (`|h| + 1)); first by rewrite divr_gt0.
move=> t te; apply: De; first exact: memvZ.
rewrite normrZ; apply: (le_lt_trans _ (_ : `|t| * (`|h| + 1) < e0)).
  by rewrite ler_wpM2l // lerDl.
by rewrite -ltr_pdivlMr.
Qed.

Hypothesis scB : sc_function V D B.

(* The derivatives of B along a line through D. *)
Lemma sc_line_derive z h (t : R) : D (z + t *: h) -> h \in V ->
  [/\ is_derive t 1 (fun s => B (z + s *: h)) ('D_h B (z + t *: h)),
      is_derive t 1 (fun s => 'D_h B (z + s *: h))
        ('D_h ('D_h B) (z + t *: h)) &
      is_derive t 1 (fun s => 'D_h ('D_h B) (z + s *: h))
        ('D_h ('D_h ('D_h B)) (z + t *: h))].
Proof.
move=> Dt hV; have [sd _ _ _ _] := scB.
have [d1 d2 d3] := sd _ _ Dt hV.
split; [exact: (is_derive_line d1) | exact: (is_derive_line d2) |
  exact: (is_derive_line d3)].
Qed.

(* The bounds of the proof of Lemma 2.15 of Koehler and Sohn on the second
   derivative along h, with r = sc_norm B z h. *)
Lemma sc_hessian_line_ge z h (t : R) : D z -> h \in V -> 0 <= t ->
  D (z + t *: h) ->
  sc_norm B z h ^+ 2 / (1 + t * sc_norm B z h) ^+ 2 <=
    'D_h ('D_h B) (z + t *: h).
Proof.
move=> Dz hV t0 Dt.
have Dl s : 0 <= s <= t -> D (z + s *: h).
  by move=> st; exact: rel_open_convex_segment Dz Dt st.
have [_ _ cvx sc _] := scB.
have nn : 0 <= 'D_h ('D_h B) z := cvx z h Dz hV.
have := @sc_ode_ge R (fun s => 'D_h ('D_h B) (z + s *: h))
  (fun s => 'D_h ('D_h ('D_h B)) (z + s *: h)) t t0.
rewrite /= scale0r addr0 /sc_norm (sqr_sqrtr nn).
apply => s st.
- by have [_ _ d] := sc_line_derive (Dl s st) hV.
- exact: cvx (Dl s st) hV.
- exact: sc (Dl s st) hV.
Qed.

Lemma sc_hessian_line_le z h (t : R) : D z -> h \in V -> 0 <= t ->
  D (z + t *: h) -> t * sc_norm B z h < 1 ->
  'D_h ('D_h B) (z + t *: h) <=
    sc_norm B z h ^+ 2 / (1 - t * sc_norm B z h) ^+ 2.
Proof.
move=> Dz hV t0 Dt tr1.
have Dl s : 0 <= s <= t -> D (z + s *: h).
  by move=> st; exact: rel_open_convex_segment Dz Dt st.
have [_ _ cvx sc _] := scB.
have nn : 0 <= 'D_h ('D_h B) z := cvx z h Dz hV.
have H1 s : 0 <= s <= t -> is_derive s 1 (fun s => 'D_h ('D_h B) (z + s *: h))
    ('D_h ('D_h ('D_h B)) (z + s *: h)).
  by move=> st; have [_ _ d] := sc_line_derive (Dl s st) hV.
have H2 s : 0 <= s <= t -> 0 <= 'D_h ('D_h B) (z + s *: h).
  by move=> st; exact: cvx (Dl s st) hV.
have H3 s : 0 <= s <= t ->
    'D_h ('D_h ('D_h B)) (z + s *: h) ^+ 2 <=
      4%:R * 'D_h ('D_h B) (z + s *: h) ^+ 3.
  by move=> st; exact: sc (Dl s st) hV.
have := sc_ode_le t0 H1 H2 H3; rewrite /= scale0r addr0 => /(_ tr1).
by rewrite /sc_norm (sqr_sqrtr nn).
Qed.

Lemma bregman_div_add z h :
  bregman_div B (z + h) z = B (z + h) - B z - 'D_h B z.
Proof. by rewrite /bregman_div (addrC z h) addrK. Qed.

(* B lies above its tangents along a segment of D, with an upper bound by the
   second derivative: on the segment from z to z + u h,
   B (z + u h) <= B z + u D B(z)[h] + u^2 K / 2 when D^2 B <= K there. *)
Lemma sc_line_taylor_le z h (u K : R) : D z -> h \in V -> 0 <= u ->
  D (z + u *: h) ->
  (forall v, 0 <= v <= u -> 'D_h ('D_h B) (z + v *: h) <= K) ->
  B (z + u *: h) <= B z + u * 'D_h B z + u ^+ 2 / 2 * K.
Proof.
move=> Dz hV u0 Du hK.
have Dl v : 0 <= v <= u -> D (z + v *: h).
  by move=> vu; exact: rel_open_convex_segment Dz Du vu.
pose d := 'D_h B z.
have H1 x : 0 <= x <= u -> is_derive x 1
    (fun v : R => B z + v * d + v ^+ 2 / 2 * K - B (z + v *: h))
    (d + x * K - 'D_h B (z + x *: h)).
  move=> xu; have [d1 _ _] := sc_line_derive (Dl x xu) hV.
  have hp : is_derive x 1 (fun v : R => B z + v * d + v ^+ 2 / 2 * K)
      (d + x * K).
    apply: is_derive_eq.
    by rewrite ?scaler0 ?add0r ?addr0 /GRing.scale /=; field.
  exact: is_deriveB hp d1.
have H2 x : 0 <= x <= u -> is_derive x 1
    (fun v : R => d + v * K - 'D_h B (z + v *: h))
    (K - 'D_h ('D_h B) (z + x *: h)).
  move=> xu; have [_ d2 _] := sc_line_derive (Dl x xu) hV.
  have hp : is_derive x 1 (fun v : R => d + v * K) K.
    apply: is_derive_eq.
    by rewrite ?scaler0 ?add0r ?addr0 /GRing.scale /=; field.
  exact: is_deriveB hp d2.
have H3 x : 0 <= x <= u -> 0 <= K - 'D_h ('D_h B) (z + x *: h).
  by move=> xu; rewrite subr_ge0 hK.
have uu : 0 <= u <= u by rewrite u0 lexx.
have u0u : (0 : R) <= 0 <= u by rewrite lexx u0.
have := derive2_ge0_tangent H1 H2 H3 uu u0u.
rewrite scale0r addr0 -/d expr0n /= !mul0r !addr0 subr0.
by rewrite !subrr mul0r addr0 subr_ge0.
Qed.

(* The Dikin ellipsoid (Nesterov and Nemirovskii, Theorem 2.1.1): if the local
   norm of h at z is less than 1, then z + h is in D. *)
Lemma sc_dikin z h : D z -> h \in V -> sc_norm B z h < 1 -> D (z + h).
Proof.
move=> Dz hV r1.
have [_ _ cvx _ bar] := scB.
set r := sc_norm B z h in r1.
have r0 : 0 <= r := sqrtr_ge0 _.
apply: contrapT => nDh.
(* tau is the exit time of the segment from z to z + h *)
pose S := [set t : R | 0 <= t <= 1 /\ D (z + t *: h)].
have S0 : S 0 by split; [rewrite lexx ler01 | rewrite scale0r addr0].
have Sub : ubound S 1 by move=> t [/andP[_ t1] _].
have hS : has_sup S by split; [exists 0 | exists 1].
pose tau := sup S.
have tau1 : tau <= 1 := ge_sup (ex_intro _ 0 S0) Sub.
have tau_ub t : S t -> t <= tau by move=> St; exact: sup_upper_bound hS _ St.
have Dlt t : 0 <= t -> t < tau -> D (z + t *: h).
  move=> t0 ttau.
  have e0 : 0 < tau - t by rewrite subr_gt0.
  have [s [/andP[s0 s1] Ds] ts] := sup_adherent e0 hS.
  rewrite -/tau opprB addrCA subrr addr0 in ts.
  have tsl : 0 <= t <= s by rewrite t0 ltW.
  exact: rel_open_convex_segment Dz Ds tsl.
have tau0 : 0 < tau.
  have [e e0 De] := rel_open_convex_line Dz hV.
  pose t := Num.min (e / 2) 1.
  have e2 : 0 < e / 2 by rewrite divr_gt0.
  have t0 : 0 < t by rewrite lt_min e2 ltr01.
  have St : S t.
    split; first by rewrite (ltW t0) ge_min lexx orbT.
    apply: De; rewrite gtr0_norm //.
    by rewrite /t gt_min ltr_pdivrMr // ltr_pMr // ltr1n.
  exact: lt_le_trans t0 (tau_ub t St).
have nDtau : ~ D (z + tau *: h).
  move=> Dtau.
  have [tau_eq1|tau_ne1] := eqVneq tau 1.
    by apply: nDh; rewrite -[h]scale1r -tau_eq1.
  have tau_lt1 : tau < 1 by rewrite lt_neqAle tau_ne1 tau1.
  have [e e0 De] := rel_open_convex_line Dtau hV.
  pose t := Num.min (e / 2) (1 - tau).
  have e2 : 0 < e / 2 by rewrite divr_gt0.
  have t0 : 0 < t by rewrite lt_min e2 subr_gt0 tau_lt1.
  have St : S (tau + t).
    split.
      rewrite addr_ge0 ?(ltW tau0) ?(ltW t0) //=.
      by rewrite -lerBrDl ge_min lexx orbT.
    rewrite scalerDl addrA; apply: De; rewrite gtr0_norm //.
    by rewrite /t gt_min ltr_pdivrMr // ltr_pMr // ltr1n.
  by have := tau_ub _ St; rewrite gerDl leNgt t0.
(* B tends to +oo at the exit point ... *)
have seg s : 0 <= s < 1 -> D (z + s *: (tau *: h)).
  move=> /andP[s0 s1]; rewrite scalerA; apply: Dlt.
    exact: mulr_ge0 s0 (ltW tau0).
  by rewrite -[X in _ < X]mul1r ltr_pM2r.
have hb := bar z (tau *: h) Dz (memvZ tau hV) seg nDtau.
(* ... but stays bounded before it, since D^2 B <= r^2 / (1 - r)^2 there *)
pose K := r ^+ 2 / (1 - r) ^+ 2.
have r1' : 0 < 1 - r by rewrite subr_gt0.
have K0 : 0 <= K by rewrite divr_ge0 ?sqr_ge0.
pose M := B z + `|'D_h B z| + K.
have bound u : 0 <= u -> u < tau -> B (z + u *: h) <= M.
  move=> u0 utau.
  have u1 : u <= 1 := le_trans (ltW utau) tau1.
  have Du := Dlt u u0 utau.
  have hK v : 0 <= v <= u -> 'D_h ('D_h B) (z + v *: h) <= K.
    move=> /andP[v0 vu].
    have v1 : v <= 1 := le_trans vu u1.
    have vr : v * r < 1 by apply: le_lt_trans r1; rewrite ler_piMl.
    have vrr : 0 < 1 - v * r by rewrite subr_gt0.
    apply: le_trans (sc_hessian_line_le Dz hV v0
      (Dlt v v0 (le_lt_trans vu utau)) vr) _.
    rewrite -/r /K ler_wpM2l ?sqr_ge0 // lef_pV2 ?posrE ?exprn_gt0 //.
    by rewrite lerXn2r ?nnegrE ?(ltW vrr) ?(ltW r1') // lerD2l lerN2 ler_piMl.
  apply: le_trans (sc_line_taylor_le Dz hV u0 Du hK) _.
  have h1 : u * 'D_h B z <= `|'D_h B z|.
    by apply: le_trans (ler_norm _) _; rewrite normrM ger0_norm // ler_piMl.
  have h2 : u ^+ 2 / 2 * K <= K.
    rewrite ler_piMl // ler_pdivrMr ?ltr0n // mul1r.
    have u2 : u ^+ 2 <= 1 by rewrite expr_le1.
    by apply: le_trans u2 _; rewrite ler1n.
  by rewrite /M; lra.
move/cvgryPgt: hb => /(_ M) hM.
have PF := at_left_proper_filter (1 : R).
have := filterI hM (filterI (nbhs_left_gt ltr01) (nbhs_left_lt (1 : R))).
move=> /(_ PF PF) hF.
have [s [Ms [s0 s1]]] := @filter_ex _ _ PF _ hF.
have st : s * tau < tau by rewrite -[X in _ < X]mul1r ltr_pM2r.
have := bound (s * tau) (mulr_ge0 (ltW s0) (ltW tau0)) st.
by rewrite -scalerA => /(lt_le_trans Ms); rewrite ltxx.
Qed.

(* The Bregman bounds of the proof of Lemma 2.15:
   sc_omega r <= D_B(z + h, z) <= sc_omega_star r, r = sc_norm B z h. *)
Lemma sc_bregman_ge z h : D z -> h \in V -> D (z + h) ->
  sc_omega (sc_norm B z h) <= bregman_div B (z + h) z.
Proof.
move=> Dz hV Dh; set r := sc_norm B z h.
have r0 : 0 <= r := sqrtr_ge0 _.
have Dh' : D (z + 1 *: h) by rewrite scale1r.
have Dl (v : R) : 0 <= v <= 1 -> D (z + v *: h).
  by move=> v1; exact: rel_open_convex_segment Dz Dh' v1.
have vr (v : R) : 0 <= v -> 0 < 1 + v * r.
  by move=> v0; rewrite ltr_wpDr // mulr_ge0.
have H1 (v : R) : 0 <= v <= 1 -> is_derive v 1
    (fun v : R => B (z + v *: h) - (v * r - ln (1 + v * r)))
    ('D_h B (z + v *: h) - (r - r / (1 + v * r))).
  move=> v1; have [d1 _ _] := sc_line_derive (Dl v v1) hV.
  have [v0 _] := andP v1.
  exact: is_deriveB d1 (is_derive_omega_line (vr v v0)).
have H2 (v : R) : 0 <= v <= 1 -> is_derive v 1
    (fun v : R => 'D_h B (z + v *: h) - (r - r / (1 + v * r)))
    ('D_h ('D_h B) (z + v *: h) - r ^+ 2 / (1 + v * r) ^+ 2).
  move=> v1; have [_ d2 _] := sc_line_derive (Dl v v1) hV.
  have [v0 _] := andP v1.
  exact: is_deriveB d2 (is_derive_omega_line1 (vr v v0)).
have H3 (v : R) : 0 <= v <= 1 ->
    0 <= 'D_h ('D_h B) (z + v *: h) - r ^+ 2 / (1 + v * r) ^+ 2.
  move=> v1; have [v0 _] := andP v1.
  by rewrite subr_ge0; exact: sc_hessian_line_ge Dz hV v0 (Dl v v1).
have h01 : 0 <= (1 : R) <= 1 by rewrite ler01 lexx.
have h00 : 0 <= (0 : R) <= 1 by rewrite lexx ler01.
have := derive2_ge0_tangent H1 H2 H3 h01 h00.
have e1 : z + 0 *: h = z by rewrite scale0r addr0.
have e2 : z + 1 *: h = z + h by rewrite scale1r.
have e3 : ln (1 + 0 * r) = 0 by rewrite mul0r addr0 ln1.
have e4 : r / (1 + 0 * r) = r by rewrite mul0r addr0 divr1.
have e5 : (1 : R) * r = r by rewrite mul1r.
by rewrite e1 e2 e3 e4 e5 bregman_div_add /sc_omega => h0; lra.
Qed.

Lemma sc_bregman_le z h : D z -> h \in V -> sc_norm B z h < 1 ->
  bregman_div B (z + h) z <= sc_omega_star (sc_norm B z h).
Proof.
move=> Dz hV r1; set r := sc_norm B z h in r1 *.
have r0 : 0 <= r := sqrtr_ge0 _.
have Dh : D (z + h) := sc_dikin Dz hV r1.
have Dh' : D (z + 1 *: h) by rewrite scale1r.
have Dl (v : R) : 0 <= v <= 1 -> D (z + v *: h).
  by move=> v1; exact: rel_open_convex_segment Dz Dh' v1.
have vr (v : R) : 0 <= v <= 1 -> 0 < 1 - v * r.
  move=> /andP[v0 v1]; rewrite subr_gt0; apply: le_lt_trans r1.
  by rewrite ler_piMl.
have H1 (v : R) : 0 <= v <= 1 -> is_derive v 1
    (fun v : R => (- (v * r) - ln (1 - v * r)) - B (z + v *: h))
    ((r / (1 - v * r) - r) - 'D_h B (z + v *: h)).
  move=> v1; have [d1 _ _] := sc_line_derive (Dl v v1) hV.
  exact: is_deriveB (is_derive_omega_star_line (vr v v1)) d1.
have H2 (v : R) : 0 <= v <= 1 -> is_derive v 1
    (fun v : R => (r / (1 - v * r) - r) - 'D_h B (z + v *: h))
    (r ^+ 2 / (1 - v * r) ^+ 2 - 'D_h ('D_h B) (z + v *: h)).
  move=> v1; have [_ d2 _] := sc_line_derive (Dl v v1) hV.
  exact: is_deriveB (is_derive_omega_star_line1 (vr v v1)) d2.
have H3 (v : R) : 0 <= v <= 1 ->
    0 <= r ^+ 2 / (1 - v * r) ^+ 2 - 'D_h ('D_h B) (z + v *: h).
  move=> v1; have [v0 _] := andP v1.
  have vr1 : v * r < 1 by rewrite -subr_gt0 vr.
  by rewrite subr_ge0; exact: sc_hessian_line_le Dz hV v0 (Dl v v1) vr1.
have h01 : 0 <= (1 : R) <= 1 by rewrite ler01 lexx.
have h00 : 0 <= (0 : R) <= 1 by rewrite lexx ler01.
have := derive2_ge0_tangent H1 H2 H3 h01 h00.
have e1 : z + 0 *: h = z by rewrite scale0r addr0.
have e2 : z + 1 *: h = z + h by rewrite scale1r.
have e3 : ln (1 - 0 * r) = 0 by rewrite mul0r subr0 ln1.
have e4 : r / (1 - 0 * r) = r by rewrite mul0r subr0 divr1.
have e5 : (1 : R) * r = r by rewrite mul1r.
by rewrite e1 e2 e3 e4 e5 bregman_div_add /sc_omega_star => h0; lra.
Qed.

(* Lemma 2.15 (i) of Koehler and Sohn: a small Bregman divergence bounds
   the local norm. *)
Lemma sc_bregman_small z h : D z -> h \in V -> D (z + h) ->
  bregman_div B (z + h) z <= sc_omega 2^-1 ->
  sc_norm B z h <= 2^-1 /\ sc_norm B z h ^+ 2 / 3%:R <= bregman_div B (z + h) z.
Proof.
move=> Dz hV Dh hB; have hge := sc_bregman_ge Dz hV Dh.
have r0 : 0 <= sc_norm B z h := sqrtr_ge0 _.
have r2 : sc_norm B z h <= 2^-1.
  rewrite leNgt; apply/negP => /sc_omega_gt_half h2.
  by have := le_trans hge hB; rewrite leNgt h2.
split => //; exact: le_trans (sc_omega_ge r0 r2) hge.
Qed.

(* Lemma 2.15 (ii): the Taylor expansion of order 2 with a remainder of
   order 3 in the local norm. *)
Lemma sc_taylor3 z h : D z -> h \in V -> sc_norm B z h <= 2^-1 ->
  D (z + h) /\
  `|B (z + h) - B z - 'D_h B z - sc_norm B z h ^+ 2 / 2| <=
    2 * sc_norm B z h ^+ 3 / 3%:R.
Proof.
move=> Dz hV r2; set r := sc_norm B z h in r2 *.
have r0 : 0 <= r := sqrtr_ge0 _.
have r1 : r < 1 by apply: le_lt_trans r2 _; rewrite invf_lt1 ?ltr1n.
have Dh := sc_dikin Dz hV r1.
split => //.
have hge := sc_bregman_ge Dz hV Dh; have hle := sc_bregman_le Dz hV r1.
rewrite bregman_div_add -/r in hge hle.
have t1 := sc_omega_taylor r0; have t2 := sc_omega_star_taylor r0 r2.
have r3 : 0 <= r ^+ 3 by rewrite exprn_ge0.
rewrite ler_norml; apply/andP; split; lra.
Qed.

(* B is convex on D. *)
Lemma sc_function_convex z y (t : R) : D z -> D y -> 0 <= t <= 1 ->
  B (z + t *: (y - z)) <= (1 - t) * B z + t * B y.
Proof.
move=> Dz Dy t01.
have [_ dir _] := DV; have hV : y - z \in V := dir z y Dz Dy.
have [_ _ cvx _ _] := scB.
set h := y - z.
have Dh' : D (z + 1 *: h) by rewrite scale1r /h addrC subrK.
have Dl (v : R) : 0 <= v <= 1 -> D (z + v *: h).
  by move=> v1; exact: rel_open_convex_segment Dz Dh' v1.
have H1 (v : R) : 0 <= v <= 1 -> is_derive v 1 (fun v : R => B (z + v *: h))
    ('D_h B (z + v *: h)).
  by move=> v1; have [d1 _ _] := sc_line_derive (Dl v v1) hV.
have H2 (v : R) : 0 <= v <= 1 ->
    is_derive v 1 (fun v : R => 'D_h B (z + v *: h))
    ('D_h ('D_h B) (z + v *: h)).
  by move=> v1; have [_ d2 _] := sc_line_derive (Dl v v1) hV.
have H3 (v : R) : 0 <= v <= 1 -> 0 <= 'D_h ('D_h B) (z + v *: h).
  by move=> v1; exact: cvx (Dl v v1) hV.
have h01 : 0 <= (1 : R) <= 1 by rewrite ler01 lexx.
have h00 : 0 <= (0 : R) <= 1 by rewrite lexx ler01.
have a0 := derive2_ge0_tangent H1 H2 H3 h00 t01.
have a1 := derive2_ge0_tangent H1 H2 H3 h01 t01.
have e1 : z + 0 *: h = z by rewrite scale0r addr0.
have e2 : z + 1 *: h = y by rewrite scale1r /h addrC subrK.
rewrite e1 in a0; rewrite e2 in a1.
have [t0 t1] := andP t01.
by nra.
Qed.

(* B is continuous on D. *)
Lemma sc_function_continuous z : D z -> forall e : R, 0 < e ->
  exists2 d : R, 0 < d & forall y, D y -> `|y - z| < d -> `|B y - B z| < e.
Proof.
move=> Dz e e0.
have [_ rep cvx _ _] := scB.
have [g [M gM]] := rep z Dz.
pose k := frobenius g + frobenius M + 1.
have k1 : 1 <= k by rewrite lerDr addr_ge0 ?frobenius_ge0.
have k0 : 0 < k := lt_le_trans ltr01 k1.
pose c : R := Num.sqrt (1 * N)%:R + 1.
have c0 : 0 < c by rewrite ltr_wpDl ?sqrtr_ge0.
pose delta := Num.min (k^-1 / 2) (e / (2 * k)).
have d0 : 0 < delta by rewrite lt_min !divr_gt0 ?invr_gt0 ?mulr_gt0.
exists (delta / c); first by rewrite divr_gt0.
move=> y Dy hy.
have [_ dir _] := DV; have hV : y - z \in V := dir z y Dz Dy.
set h := y - z in hV hy *.
set x := frobenius h.
have x0 : 0 <= x := frobenius_ge0 _.
have xd : x < delta.
  apply: le_lt_trans (frobenius_le_mx_norm h) _.
  apply: (@le_lt_trans _ _ (c * mx_norm h)).
    by rewrite ler_wpM2r ?lerDl // mx_normrE; apply/bigmax_geP; left.
  by rewrite mulrC -ltr_pdivlMr.
have xk : x <= k^-1 / 2 by apply: le_trans (ltW xd) _; rewrite ge_min lexx.
have [gE ME] := gM h hV.
have nn : 0 <= 'D_h ('D_h B) z := cvx z h Dz hV.
(* the local norm is at most sqrt k |h|_F *)
have r2 : sc_norm B z h ^+ 2 <= k * x ^+ 2.
  rewrite /sc_norm sqr_sqrtr // ME.
  apply: le_trans (ler_mxdot _ _) _.
  apply: (@le_trans _ _ (x * (x * frobenius M))).
    by rewrite ler_wpM2l // frobenius_mulmx.
  rewrite mulrA -expr2 mulrC ler_wpM2r ?sqr_ge0 //.
  by rewrite /k addrAC lerDr addr_ge0 ?frobenius_ge0.
have kx : k * x <= 2^-1.
  apply: le_trans (ler_wpM2l (ltW k0) xk) _.
  by rewrite mulrA mulfV ?gt_eqF // mul1r.
have x1 : x <= 1.
  apply: le_trans xk _; rewrite ler_pdivrMr ?ltr0n // mul1r.
  have ki : k^-1 <= 1 by rewrite invf_le1.
  by apply: le_trans ki _; rewrite ler1n.
have rhalf : sc_norm B z h <= 2^-1.
  have rn : 0 <= sc_norm B z h := sqrtr_ge0 _.
  rewrite -(@ler_pXn2r _ 2) ?nnegrE ?invr_ge0 ?ler0n //.
  apply: le_trans r2 _; rewrite expr2 mulrA.
  apply: le_trans (ler_wpM2r x0 kx) _.
  rewrite expr2 ler_wpM2l ?invr_ge0 ?ler0n //.
  apply: le_trans xk _; rewrite ler_pdivrMr ?ltr0n // mulVf ?pnatr_eq0 //.
  by rewrite invf_le1.
(* Lemma 2.15 (ii) and the gradient bound *)
have [_ tay] := sc_taylor3 Dz hV rhalf.
have yE : z + h = y by rewrite /h addrC subrK.
rewrite yE in tay.
set r := sc_norm B z h in tay r2 rhalf.
have r0 : 0 <= r := sqrtr_ge0 _.
have r3 : r ^+ 3 <= r ^+ 2 / 2.
  by rewrite exprSr; apply: ler_wpM2l; [exact: sqr_ge0 | exact: rhalf].
have hD : `|'D_h B z| <= k * x.
  rewrite gE; apply: le_trans (mxdot_le g h) _; rewrite ler_wpM2r //.
  by rewrite /k -addrA lerDl addr_ge0 ?frobenius_ge0.
have hxx : k * x ^+ 2 <= k * x.
  by rewrite ler_wpM2l ?(ltW k0) // expr2 ler_piMl.
have kxe : 2 * (k * x) < e.
  apply: (@lt_le_trans _ _ (2 * (k * delta))).
    by rewrite ltr_pM2l ?ltr0n // ltr_pM2l.
  have dl : delta <= e / (2 * k) by rewrite ge_min lexx orbT.
  by rewrite mulrA mulrC -ler_pdivlMr ?mulr_gt0 ?ltr0n.
move: tay hD; rewrite !ler_norml => /andP[t1 t2] /andP[d1 d2].
by rewrite ltr_norml; apply/andP; split; lra.
Qed.

End sc_line.

Section sc_barrier_lemmas.
Context {R : realType} {N : nat}.
Variables (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) (theta : R)
  (B : 'rV[R]_N -> R).
Hypothesis DV : rel_open_convex V D.
Hypothesis scB : sc_barrier V D theta B.
Hypothesis theta0 : 0 <= theta.

(* Lemma 2.10 of Koehler and Sohn, first part (Nesterov, Theorem 4.2.4):
   D B(z)[y - z] <= theta for z, y in D. *)
Lemma sc_barrier_grad_le z y : D z -> D y -> 'D_(y - z) B z <= theta.
Proof.
move=> Dz Dy.
have [scf bp] := scB.
have [_ _ cvx _ _] := scf.
have [_ dir _] := DV; have hV := dir z y Dz Dy.
set h := y - z in hV *.
have Dh' : D (z + 1 *: h) by rewrite scale1r /h addrC subrK.
have Dl (v : R) : 0 <= v <= 1 -> D (z + v *: h).
  by move=> v1; exact: (@rel_open_convex_segment R N V D DV z h 1 v Dz Dh' v1).
have f1d (v : R) : 0 <= v <= 1 -> is_derive v 1
    (fun v : R => 'D_h B (z + v *: h)) ('D_h ('D_h B) (z + v *: h)).
  move=> v1.
  by have [_ d2 _] := @sc_line_derive R N V D B scf z h v (Dl v v1) hV.
have f2ge (v : R) : 0 <= v <= 1 -> 0 <= 'D_h ('D_h B) (z + v *: h).
  by move=> v1; exact: cvx (Dl v v1) hV.
have e0 : z + 0 *: h = z by rewrite scale0r addr0.
have [d0|d0] := leP ('D_h B z) 0; first exact: le_trans d0 theta0.
(* the derivative along the segment is nondecreasing, hence positive *)
have f1ge (v : R) : 0 <= v <= 1 -> 'D_h B z <= 'D_h B (z + v *: h).
  move=> /andP[v0 v1]; rewrite -{1}e0.
  apply: (@derive_ge0_le R (fun v : R => 'D_h B (z + v *: h))
    (fun v : R => 'D_h ('D_h B) (z + v *: h)) 0 v v0) => w /andP[w0 wv].
    by apply: f1d; rewrite w0 (le_trans wv v1).
  by apply: f2ge; rewrite w0 (le_trans wv v1).
have f1pos (v : R) : 0 <= v <= 1 -> 0 < 'D_h B (z + v *: h).
  by move=> v1; exact: lt_le_trans d0 (f1ge v v1).
have tpos : 0 < theta.
  rewrite lt_neqAle theta0 andbT; apply/eqP => t0.
  have := bp z h Dz hV; rewrite -t0 mul0r.
  by rewrite leNgt exprn_gt0.
(* by (BP), 1 / D B + t / theta is nonincreasing along the segment *)
have qd (v : R) : 0 <= v <= 1 -> is_derive v 1
    (fun v : R => ('D_h B (z + v *: h))^-1 + v / theta)
    (- ('D_h B (z + v *: h)) ^- 2 * 'D_h ('D_h B) (z + v *: h) + theta^-1).
  move=> v1; have hv := is_deriveV (lt0r_neq0 (f1pos v v1)) (f1d v v1).
  have ht : is_derive v 1 (fun v : R => v / theta) theta^-1.
    have := is_deriveZ theta^-1 (is_derive_id v 1).
    have E : ( *%R^~ theta^-1) = theta^-1 \*: (@id R).
      by apply/funext => w; rewrite /= mulrC.
    rewrite E => h0; apply: is_derive_eq h0 _.
    by rewrite /GRing.scale /= mulr1.
  exact: is_deriveD hv ht.
have dq (v : R) : 0 <= v <= 1 ->
    - ('D_h B (z + v *: h)) ^- 2 * 'D_h ('D_h B) (z + v *: h) + theta^-1 <= 0.
  move=> v1; have f0 := f1pos v v1.
  have := bp _ h (Dl v v1) hV.
  set a := 'D_h B (z + v *: h); set b := 'D_h ('D_h B) (z + v *: h) => ab.
  have h1 : theta^-1 <= b / a ^+ 2.
    by rewrite ler_pdivlMr ?exprn_gt0 // mulrC ler_pdivrMr // mulrC.
  by rewrite mulNr mulrC addrC subr_le0.
have := @derive_le0_le R (fun v : R => ('D_h B (z + v *: h))^-1 + v / theta)
  (fun v : R => - ('D_h B (z + v *: h)) ^- 2 * 'D_h ('D_h B) (z + v *: h)
     + theta^-1) 0 1 ler01 qd dq.
rewrite e0 mul0r addr0 mul1r => q10.
have p1 : 0 < ('D_h B (z + 1 *: h))^-1.
  by rewrite invr_gt0 f1pos // ler01 lexx.
have : theta^-1 < ('D_h B z)^-1 by lra.
by rewrite ltf_pV2 ?posrE // => /ltW.
Qed.

(* Lemma 2.10: contracting toward x0 costs at most theta ln (1 / eps). *)
Lemma sc_barrier_contraction x0 x (eps : R) : D x0 -> D x -> 0 < eps < 1 ->
  B ((1 - eps) *: x + eps *: x0) <= B x0 + theta * ln eps^-1.
Proof.
move=> D0 Dx /andP[e0 e1].
have [scf bp] := scB.
have [_ rep _ _ _] := scf.
have [_ dir _] := DV; have hV := dir x0 x D0 Dx.
set h := x - x0 in hV *.
have Dh' : D (x0 + 1 *: h) by rewrite scale1r /h addrC subrK.
have Dl (v : R) : 0 <= v <= 1 -> D (x0 + v *: h).
  by move=> v1; exact: (@rel_open_convex_segment R N V D DV x0 h 1 v D0 Dh' v1).
have gd (v : R) : 0 <= v <= 1 -> is_derive v 1
    (fun v : R => B (x0 + v *: h)) ('D_h B (x0 + v *: h)).
  move=> v1.
  by have [d1 _ _] := @sc_line_derive R N V D B scf x0 h v (Dl v v1) hV.
(* (1 - v) D B(x_v)[h] = D B(x_v)[x - x_v] <= theta *)
have gle (v : R) : 0 <= v <= 1 -> (1 - v) * 'D_h B (x0 + v *: h) <= theta.
  move=> v1; have := sc_barrier_grad_le (Dl v v1) Dx.
  have [g [M {}gM]] := rep _ (Dl v v1).
  have xE : x - (x0 + v *: h) = (1 - v) *: h.
    by rewrite /h scalerBl scale1r opprD addrA.
  have hV' : (1 - v) *: h \in V := memvZ _ hV.
  by rewrite xE (gM _ hV').1 (gM _ hV).1 mxdotZr.
(* so B(x_v) + theta ln (1 - v) is nonincreasing on [0, 1 - eps] *)
have Gd (v : R) : 0 <= v <= 1 - eps -> is_derive v 1
    (fun v : R => B (x0 + v *: h) + theta * ln (1 - v))
    ('D_h B (x0 + v *: h) - theta / (1 - v)).
  move=> /andP[v0 v1].
  have v1' : 0 <= v <= 1 by rewrite v0 (le_trans v1) // lerBlDr lerDl ltW.
  have lv : 0 < 1 - v.
    by rewrite subr_gt0 (le_lt_trans v1) // ltrBlDr ltrDl.
  have hg : is_derive v 1 (fun y : R => 1 - y) (-1).
    by apply: is_derive_eq; rewrite add0r mul1r.
  have hc := @is_derive1_comp R (@ln R) (fun y : R => 1 - y) v _ _
    (is_derive1_ln lv) hg.
  have := is_deriveD (gd v v1') (is_deriveZ theta hc).
  have -> : (fun v : R => B (x0 + v *: h) + theta * ln (1 - v)) =
    (fun v : R => B (x0 + v *: h)) + theta *: (@ln R \o (fun y : R => 1 - y)).
    by [].
  move=> h0; apply: is_derive_eq h0 _.
  by rewrite /GRing.scale /= mulrN1 mulrN.
have dG (v : R) : 0 <= v <= 1 - eps ->
    'D_h B (x0 + v *: h) - theta / (1 - v) <= 0.
  move=> /andP[v0 v1].
  have v1' : 0 <= v <= 1 by rewrite v0 (le_trans v1) // lerBlDr lerDl ltW.
  have lv : 0 < 1 - v.
    by rewrite subr_gt0 (le_lt_trans v1) // ltrBlDr ltrDl.
  by rewrite subr_le0 ler_pdivlMr // mulrC gle.
have e1' : 0 <= 1 - eps by rewrite subr_ge0 ltW.
have := @derive_le0_le R (fun v : R => B (x0 + v *: h) + theta * ln (1 - v))
  (fun v : R => 'D_h B (x0 + v *: h) - theta / (1 - v)) 0 (1 - eps) e1' Gd dG.
have ea : x0 + 0 *: h = x0 by rewrite scale0r addr0.
have eb : (1 : R) - (1 - eps) = eps by rewrite opprB addrC subrK.
have ec : x0 + (1 - eps) *: h = (1 - eps) *: x + eps *: x0.
  rewrite /h scalerBr scalerBl scale1r scalerBl scale1r opprB addrCA.
  by congr (_ + _); rewrite addrC subrK.
have ef : (1 : R) - 0 = 1 := subr0 1.
rewrite ea eb ec ef ln1 mulr0 addr0.
by rewrite lnV ?posrE // mulrN; lra.
Qed.

End sc_barrier_lemmas.
