From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean nets.
From GaussianAnalysis.comparison Require Import gauss_concentration.
From GaussianAnalysis.comparison Require Import gauss_smoothing escape cgmt.
From GaussianAnalysis.convex Require Import moreau.

(**md**************************************************************************)
(* # The convex Gaussian min-max theorem on cones                             *)
(*                                                                            *)
(* Vectors x of R^M are column vectors 'cV[R]_M and h : 'rV[R]_M, as in      *)
(* cgmt.v; |x| is frobenius x and <h, x> is mxdot h^T x. Let K be a set of    *)
(* 'cV[R]_M that contains 0 and                                               *)
(*   sigma_K(h) = sup_(x in K, |x| <= 1) <h, x>              (cone_sup K h).  *)
(* - cone_sup_ub, cone_sup_le, cone_sup_ge0, cone_sup_le_norm: sigma_K(h) is  *)
(*   the least upper bound and lies in [0, |h|]; cone_sup_lipschitz: it is    *)
(*   1-Lipschitz in h; cone_sup_attained: for K closed the supremum is        *)
(*   attained (compactness); cone_sup_dot: for a cone K (a x is in K for x in *)
(*   K and a >= 0), <h, x> <= |x| sigma_K(h) on K.                            *)
(* - cone_sup_proj: for a closed convex cone K of row vectors,                *)
(*   sigma_(tr_set K)(h) = |proj K h| (cone_proj_support of moreau.v), and    *)
(*   cone_sup_tr_setE writes sigma_(tr_set K)(h) as a supremum over K.        *)
(*                                                                            *)
(* Let B be a set of 'cV[R]_M such that every nonzero point of K has a        *)
(* positive multiple in B (a base of K when B is in K and 0 is not in B). The *)
(* auxiliary value of the CGMT on B (cgmt.v),                                 *)
(*   phi(B) = cgmt_aux B g h = inf_(x in B) (|g| |x| - <h, x>)_+,             *)
(* is governed by the sign of |g| - sigma_K(h):                               *)
(* - cgmt_aux_cone_zero: for K closed, phi(B) = 0 when 0 < sigma_K(h) and     *)
(*   |g| <= sigma_K(h), in particular when 0 < |g| <= sigma_K(h) or           *)
(*   |g| < sigma_K(h) (cgmt_aux_cone_zero_lt): at a point x of K with         *)
(*   |x| <= 1 and <h, x> = sigma_K(h), the multiples a x with a > 0 have      *)
(*   |g| |a x| - <h, a x> <= 0;                                               *)
(* - cgmt_aux_cone_ge: for a cone K, B nonempty and in K, and r <= |x| on B,  *)
(*   phi(B) >= r (|g| - sigma_K(h))_+, since <h, x> <= |x| sigma_K(h) on K.   *)
(* cgmt_aux_tr_cone_zero and cgmt_aux_tr_cone_ge are the same statements for  *)
(* a closed convex cone K and a set B of row vectors, with |proj K h| in      *)
(* place of sigma_K(h); tr_set0, tr_set_cone, tr_set_base, tr_set_sub and     *)
(* tr_set_norm_ge carry the hypotheses from row vectors to tr_set.            *)
(*                                                                            *)
(* With the CGMT of cgmt.v: let a have law gauss (N * M), so that             *)
(* A = vec_mx a is an N x M matrix of independent standard normal entries,    *)
(* z have law gauss (N + M), g = lsubmx z and h = rsubmx z, N > 0, B be       *)
(* nonempty and |x| <= rho on B.                                              *)
(* - cone_escape_zero_tail: if rho > 0, K is closed, B is closed and convex  *)
(*   and P(|g| < sigma_K(h)) > 1/2, then inf_(x in B) |A x| is at least       *)
(*   rho (1 + 2 sqrt (ln 4)) + u with probability at most                     *)
(*   2 exp (- u^2 / (2 rho^2)) (cgmt_zero_tail): the kernel of A meets K      *)
(*   approximately.                                                           *)
(* - cone_escape_lower_tail: if K is a cone, B is in K and r <= |x| on B,     *)
(*   then inf_(x in B) |A x| is at most r E (|g| - sigma_K(h))_+ - rho - u    *)
(*   with probability at most 2 exp (- u^2 / (2 rho^2)) (cgmt_lower and       *)
(*   cgmt_escape_tail): the kernel of A stays away from B when |g| exceeds    *)
(*   sigma_K(h) in mean by more than (rho + u) / r.                           *)
(*                                                                            *)
(* ```                                                                        *)
(*   cone_sup K h == sup_(x in K, |x| <= 1) <h, x>, for h : 'rV[R]_M          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section cone_sup.
Context {R : realType} {M : nat}.
Variable K : set 'cV[R]_M.

(* sigma_K(h) = sup_(x in K, |x| <= 1) <h, x>. *)
Definition cone_sup (h : 'rV[R]_M) : R :=
  sup [set mxdot h^T x | x in [set x | K x /\ frobenius x <= 1]].

Let dot_le1 (h : 'rV[R]_M) (x : 'cV[R]_M) : frobenius x <= 1 ->
  mxdot h^T x <= frobenius h.
Proof.
move=> x1; apply: le_trans (ler_mxdot _ _) _; rewrite frobenius_trmx.
by rewrite -[X in _ <= X]mulr1 ler_wpM2l // frobenius_ge0.
Qed.

Lemma cone_sup_ub h x : K x -> frobenius x <= 1 -> mxdot h^T x <= cone_sup h.
Proof.
move=> Kx x1; apply: ub_le_sup; last by exists x.
by exists (frobenius h) => _ [y [_ y1] <-]; exact: dot_le1.
Qed.

Hypothesis K0 : K 0.

Lemma cone_sup_le h c :
  (forall x, K x -> frobenius x <= 1 -> mxdot h^T x <= c) -> cone_sup h <= c.
Proof.
move=> hc; apply: ge_sup; last by move=> _ [x [Kx x1] <-]; exact: hc.
exists (mxdot h^T 0), 0 => //.
by split => //; rewrite frobenius0 ler01.
Qed.

Lemma cone_sup_ge0 h : 0 <= cone_sup h.
Proof.
have := cone_sup_ub h K0; rewrite frobenius0 ler01 mxdot0r.
by apply.
Qed.

Lemma cone_sup_le_norm h : cone_sup h <= frobenius h.
Proof. by apply: cone_sup_le => x _; exact: dot_le1. Qed.

(* sigma_K is 1-Lipschitz. *)
Lemma cone_sup_lipschitz h h' :
  `|cone_sup h - cone_sup h'| <= frobenius (h - h').
Proof.
have key (a b : 'rV[R]_M) : cone_sup a <= cone_sup b + frobenius (a - b).
  apply: cone_sup_le => x Kx x1.
  have -> : mxdot a^T x = mxdot b^T x + mxdot (a - b)^T x.
    by rewrite linearB /= mxdotBl; ring.
  by apply: lerD; [exact: cone_sup_ub|exact: dot_le1].
rewrite ler_norml; have := key h h'; have := key h' h.
rewrite -frobeniusN opprB; lra.
Qed.

(* For K closed, the supremum is attained. *)
Lemma cone_sup_attained h : closed K ->
  exists x, [/\ K x, frobenius x <= 1 & mxdot h^T x = cone_sup h].
Proof.
move=> Kc.
pose A := K `&` [set x : 'cV[R]_M | frobenius x <= 1].
have cf : continuous (fun x : 'cV[R]_M => frobenius x).
  have e : (fun x : 'cV[R]_M => frobenius x) =
      (fun x => frobenius ((1%:M : 'M[R]_M) *m x)).
    by apply/funext => y; rewrite mul1mx.
  by rewrite e; exact: continuous_frobenius_mulmx.
have Ac : closed A.
  apply: closedI => //.
  exact: (continuous_closedP _).1 cf _ (@closed_le R 1).
have Acp := closed_bounded_compact_cV Ac (fun x (Ax : A x) => Ax.2).
have A0 : A !=set0 by exists 0; split => //; rewrite /= frobenius0 ler01.
have cd : continuous (fun x : 'cV[R]_M => mxdot h^T x).
  have L (y y' : 'rV[R]_M) :
      `|mxdot h y - mxdot h y'| <= frobenius h * frobenius (y - y').
    by rewrite -mxdotBr mxdot_le.
  have cr := lipschitz_frobenius_continuous L.
  have -> : (fun x : 'cV[R]_M => mxdot h^T x) =
      (fun y : 'rV[R]_M => mxdot h y) \o (fun x : 'cV[R]_M => x^T).
    by apply/funext => y /=; rewrite -[RHS]mxdot_trmx trmxK.
  move=> x; apply: continuous_comp; first exact: continuous_trmx.
  exact: cr.
have [x Ax xmax] := compact_EVT_max A0 Acp (continuous_subspaceT cd).
move: Ax; rewrite inE => -[Kx x1].
exists x; split => //; apply/eqP; rewrite eq_le (cone_sup_ub h Kx x1) /=.
apply: cone_sup_le => y Ky y1; apply: xmax.
by apply/mem_set; split.
Qed.

Hypothesis Kcone : forall x (a : R), K x -> 0 <= a -> K (a *: x).

(* On the cone, <h, x> <= |x| sigma_K(h). *)
Lemma cone_sup_dot h x : K x -> mxdot h^T x <= frobenius x * cone_sup h.
Proof.
move=> Kx; have [->|x0] := eqVneq x 0.
  by rewrite mxdot0r frobenius0 mul0r.
have fx : 0 < frobenius x by rewrite frobenius_gt0.
have Ku : K ((frobenius x)^-1 *: x).
  by apply: Kcone => //; rewrite invr_ge0 ltW.
have u1 : frobenius ((frobenius x)^-1 *: x) <= 1.
  by rewrite frobeniusZ ger0_norm ?invr_ge0 ?(ltW fx) // mulVf ?gt_eqF.
by have := cone_sup_ub h Ku u1; rewrite mxdotZr ler_pdivrMl.
Qed.

End cone_sup.

Section cone_sup_proj.
Context {R : realType} {M : nat}.
Variable K : set 'rV[R]_M.

Lemma cone_sup_tr_setE (h : 'rV[R]_M) :
  cone_sup (tr_set K) h =
  sup [set mxdot h y | y in [set y | K y /\ frobenius y <= 1]].
Proof.
rewrite /cone_sup; congr sup; apply/seteqP; split.
  move=> _ [_ [[y Ky <-] y1] <-]; exists y; last by rewrite mxdot_trmx.
  by split => //; rewrite -frobenius_trmx.
move=> _ [y [Ky y1] <-]; exists y^T; last by rewrite mxdot_trmx.
by split; [exists y|rewrite frobenius_trmx].
Qed.

Hypotheses (Kc : closed K) (K0 : K 0).
Hypothesis Kcvx : forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
  K (x + t *: (y - x)).
Hypothesis Kcone : forall y (a : R), K y -> 0 <= a -> K (a *: y).

(* For a closed convex cone, sigma is the norm of the projection. *)
Lemma cone_sup_proj (h : 'rV[R]_M) :
  cone_sup (tr_set K) h = frobenius (proj K h).
Proof.
rewrite cone_sup_tr_setE -(cone_proj_support Kc K0 Kcvx Kcone h).
congr sup; apply/seteqP; split => _ [y [Ky y1] <-]; exists y => //;
  split => //.
  by rewrite -frobenius_sqr exprn_ile1 // frobenius_ge0.
by rewrite /frobenius -sqrtr1 ler_sqrt.
Qed.

End cone_sup_proj.

Section tr_set_cone.
Context {R : realType} {M : nat}.
Variables (K B : set 'rV[R]_M).

Lemma tr_set0 : K 0 -> tr_set K 0.
Proof. by move=> K0; exists 0 => //; rewrite trmx0. Qed.

Lemma tr_set_cone : (forall y (a : R), K y -> 0 <= a -> K (a *: y)) ->
  forall x (a : R), tr_set K x -> 0 <= a -> tr_set K (a *: x).
Proof.
move=> Kcone _ a [y Ky <-] a0; exists (a *: y); first exact: Kcone.
by rewrite linearZ.
Qed.

Lemma tr_set_base :
  (forall y, K y -> y != 0 -> exists2 a : R, 0 < a & B (a *: y)) ->
  forall x, tr_set K x -> x != 0 -> exists2 a : R, 0 < a & tr_set B (a *: x).
Proof.
move=> Bbase _ [y Ky <-] y0.
have y0' : y != 0 by apply: (contra_neq _ y0) => ->; rewrite trmx0.
have [a a0 Bay] := Bbase y Ky y0'.
by exists a => //; exists (a *: y) => //; rewrite linearZ.
Qed.

Lemma tr_set_sub : (forall y, B y -> K y) ->
  forall x, tr_set B x -> tr_set K x.
Proof. by move=> BK _ [y By <-]; exists y => //; exact: BK. Qed.

Lemma tr_set_norm_ge (r : R) : (forall y, B y -> r <= frobenius y) ->
  forall x, tr_set B x -> r <= frobenius x.
Proof. by move=> Br _ [y By <-]; rewrite frobenius_trmx; exact: Br. Qed.

End tr_set_cone.

Section cone_aux.
Context {R : realType} {N M : nat}.
Variables (K B : set 'cV[R]_M).
Hypothesis K0 : K 0.

Section zero.
Hypothesis Kc : closed K.
Hypothesis Bbase : forall x, K x -> x != 0 -> exists2 a : R, 0 < a & B (a *: x).

(* phi(B) = 0 when 0 < sigma_K(h) and |g| <= sigma_K(h). *)
Lemma cgmt_aux_cone_zero (g : 'rV[R]_N) (h : 'rV[R]_M) :
  0 < cone_sup K h -> frobenius g <= cone_sup K h -> cgmt_aux B g h = 0.
Proof.
move=> s0 gs; have [x [Kx x1 hx]] := cone_sup_attained K0 h Kc.
have x0 : x != 0.
  by apply: contraTneq s0 => x0; rewrite -hx x0 mxdot0r ltxx.
have [a a0 Bax] := Bbase Kx x0.
have B0 : B !=set0 by exists (a *: x).
apply/eqP; rewrite eq_le cgmt_aux_ge0 // andbT.
apply: le_trans (cgmt_aux_le _ _ Bax) _.
rewrite ge_max lexx /= frobeniusZ mxdotZr gtr0_norm // hx subr_le0.
rewrite mulrCA ler_pM2l //; apply: (le_trans _ gs).
rewrite -[X in _ <= X]mulr1.
by apply: ler_wpM2l => //; exact: frobenius_ge0.
Qed.

Lemma cgmt_aux_cone_zero_lt (g : 'rV[R]_N) (h : 'rV[R]_M) :
  frobenius g < cone_sup K h -> cgmt_aux B g h = 0.
Proof.
move=> gs; apply: (cgmt_aux_cone_zero _ (ltW gs)).
exact: le_lt_trans (frobenius_ge0 g) gs.
Qed.

End zero.

Section lower.
Hypothesis Kcone : forall x (a : R), K x -> 0 <= a -> K (a *: x).
Hypothesis BK : forall x, B x -> K x.
Variable r : R.
Hypothesis Br : forall x, B x -> r <= frobenius x.

(* phi(B) >= r (|g| - sigma_K(h))_+. *)
Lemma cgmt_aux_cone_ge (g : 'rV[R]_N) (h : 'rV[R]_M) : B !=set0 ->
  r * Num.max 0 (frobenius g - cone_sup K h) <= cgmt_aux B g h.
Proof.
move=> B0; apply: cgmt_aux_ge => // x Bx.
have hx := cone_sup_dot Kcone h (BK Bx); have rx := Br Bx.
(* leP substitutes the two values of the maximum *)
have [hle|hlt] := leP (frobenius g - cone_sup K h) 0.
  by rewrite mulr0 le_max lexx.
rewrite le_max; apply/orP; right.
have hr : r * (frobenius g - cone_sup K h) <=
    frobenius x * (frobenius g - cone_sup K h) by rewrite ler_pM2r.
have e : frobenius x * (frobenius g - cone_sup K h) =
    frobenius g * frobenius x - frobenius x * cone_sup K h by ring.
by rewrite e in hr; lra.
Qed.

End lower.

End cone_aux.

Section cone_aux_rows.
Context {R : realType} {N M : nat}.
Variables (K B : set 'rV[R]_M).
Hypotheses (Kc : closed K) (K0 : K 0).
Hypothesis Kcvx : forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
  K (x + t *: (y - x)).
Hypothesis Kcone : forall y (a : R), K y -> 0 <= a -> K (a *: y).

(* (i) for row vectors: phi(B) = 0 when 0 < |g| <= |proj K h|. *)
Corollary cgmt_aux_tr_cone_zero (g : 'rV[R]_N) (h : 'rV[R]_M) :
  (forall y, K y -> y != 0 -> exists2 a : R, 0 < a & B (a *: y)) ->
  0 < frobenius g -> frobenius g <= frobenius (proj K h) ->
  cgmt_aux (tr_set B) g h = 0.
Proof.
move=> Bbase g0 gs; rewrite -(cone_sup_proj Kc K0 Kcvx Kcone) in gs.
apply: (cgmt_aux_cone_zero (tr_set0 K0) (closed_tr_set Kc)
  (tr_set_base Bbase) _ gs).
exact: lt_le_trans gs.
Qed.

(* (ii) for row vectors: phi(B) >= r (|g| - |proj K h|)_+. *)
Corollary cgmt_aux_tr_cone_ge (r : R) (g : 'rV[R]_N) (h : 'rV[R]_M) :
  B !=set0 -> (forall y, B y -> K y) -> (forall y, B y -> r <= frobenius y) ->
  r * Num.max 0 (frobenius g - frobenius (proj K h)) <=
  cgmt_aux (tr_set B) g h.
Proof.
move=> B0 BK Br; rewrite -(cone_sup_proj Kc K0 Kcvx Kcone).
apply: (cgmt_aux_cone_ge (tr_set_cone Kcone) (tr_set_sub BK)
  (tr_set_norm_ge Br)).
exact: tr_set_neq0.
Qed.

End cone_aux_rows.

Section cone_escape.
Context {R : realType} {N M : nat}.
Variables (K B : set 'cV[R]_M) (rho : R).
Hypotheses (K0 : K 0) (B0 : B !=set0).
Hypothesis Bb : forall x, B x -> frobenius x <= rho.

(* |g| - sigma_K(h) is a Lipschitz function of z = (g, h). *)
Let F (z : 'rV[R]_(N + M)) : R := frobenius (lsubmx z) - cone_sup K (rsubmx z).

Let F_lip (z z' : 'rV[R]_(N + M)) :
  `|F z - F z'| <= Num.sqrt 2 * frobenius (z - z').
Proof.
have h1 := ler_frobeniusB (lsubmx z) (lsubmx z').
have h2 := cone_sup_lipschitz K0 (rsubmx z) (rsubmx z').
have h3 := frobenius_hsub_add (z - z'); rewrite !linearB /= in h3.
have -> : F z - F z' = (frobenius (lsubmx z) - frobenius (lsubmx z')) -
    (cone_sup K (rsubmx z) - cone_sup K (rsubmx z')) by rewrite /F; ring.
apply: le_trans (ler_normB _ _) _; apply: (le_trans _ h3).
exact: lerD.
Qed.

Let F0_lip (z z' : 'rV[R]_(N + M)) :
  `|Num.max 0 (F z) - Num.max 0 (F z')| <= Num.sqrt 2 * frobenius (z - z').
Proof.
apply: (le_trans _ (F_lip z z')).
have k (a b : R) : Num.max 0 a <= Num.max 0 b + `|a - b|.
  by apply: max0_leD => //; have := ler_norm (a - b); lra.
rewrite ler_norml; apply/andP; split.
  by have := k (F z') (F z); rewrite distrC; lra.
by have := k (F z) (F z'); lra.
Qed.

Let mF : measurable_fun setT F.
Proof.
exact: continuous_measurable_mx (lipschitz_frobenius_continuous F_lip).
Qed.

Let mphi : measurable_fun setT
  (fun z : 'rV[R]_(N + M) => cgmt_aux B (lsubmx z) (rsubmx z)).
Proof. exact: (@measurable_cgmt_aux R N M B rho B0 Bb). Qed.

Let mPhi : measurable_fun setT
  (fun a : 'rV[R]_(N * M) => escape_inf B (vec_mx a : 'M[R]_(N, M))).
Proof. exact: (@measurable_escape_inf R N M B rho B0 Bb). Qed.

(* If |g| < sigma_K(h) with probability more than 1/2, the kernel of A
   meets K approximately: inf_(x in B) |A x| is at least
   rho (1 + 2 sqrt (ln 4)) + u with probability at most
   2 exp (- u^2 / (2 rho^2)). *)
Theorem cone_escape_zero_tail (u : R) : (0 < N)%N -> 0 < rho ->
  closed K ->
  (forall x, K x -> x != 0 -> exists2 a : R, 0 < a & B (a *: x)) ->
  closed B ->
  (forall x y (t : R), B x -> B y -> 0 <= t <= 1 -> B (x + t *: (y - x))) ->
  0 <= u ->
  ((2^-1)%:E <
    gauss (N + M) [set z | frobenius (lsubmx z) < cone_sup K (rsubmx z)]%R)%E ->
  (gauss (N * M) [set a | rho * (1 + 2 * Num.sqrt (ln 4)) + u <=
     escape_inf B (vec_mx a : 'M[R]_(N, M))]%R <=
   (2 * expR (- u ^+ 2 / (2 * rho ^+ 2)))%:E)%E.
Proof.
move=> N0 rho0 Kc Bbase Bc Bcvx u0 hp.
apply: (@cgmt_zero_tail R N M B rho B0 Bb u N0 rho0 Bc Bcvx u0).
apply: (lt_le_trans hp); apply: le_measure; rewrite ?inE.
- have := mF measurableT (measurable_itv `]-oo, (0 : R)[).
  rewrite setTI; congr (measurable _).
  by apply/seteqP; split => z /=; rewrite in_itv /= /F subr_lt0.
- have := mphi measurableT (measurable_set1 (0 : R)).
  by rewrite setTI.
- by move=> z /= hz; exact: (cgmt_aux_cone_zero_lt K0 Kc Bbase hz).
Qed.

(* The kernel of A stays away from B: inf_(x in B) |A x| is at most
   r E (|g| - sigma_K(h))_+ - rho - u with probability at most
   2 exp (- u^2 / (2 rho^2)). *)
Theorem cone_escape_lower_tail (r u : R) : (0 < N)%N ->
  (forall x (a : R), K x -> 0 <= a -> K (a *: x)) ->
  (forall x, B x -> K x) -> (forall x, B x -> r <= frobenius x) -> 0 <= u ->
  (gauss (N * M) [set a | escape_inf B (vec_mx a : 'M[R]_(N, M)) <=
     r * \int[gauss (N + M)]_z
       Num.max 0 (frobenius (lsubmx z) - cone_sup K (rsubmx z)) - rho - u]%R <=
   (2 * expR (- u ^+ 2 / (2 * rho ^+ 2)))%:E)%E.
Proof.
move=> N0 Kcone BK Br u0.
have hl := @cgmt_lower R N M B rho B0 Bb N0.
set EP := \int[gauss (N * M)]_a escape_inf B (vec_mx a : 'M[R]_(N, M)) in hl *.
set Ep := \int[gauss (N + M)]_z cgmt_aux B (lsubmx z) (rsubmx z) in hl.
set E := \int[gauss (N + M)]_z Num.max 0 (frobenius (lsubmx z) -
  cone_sup K (rsubmx z)).
have iF := integrable_gauss_lipschitz F0_lip.
have iF' : (gauss (N + M)).-integrable [set: 'rV[R]_(N + M)]
    (EFin \o (fun z => r * Num.max 0 (F z))).
  apply: (@integrable_gauss_lipschitz _ _ _ (`|r| * Num.sqrt 2)) => z z'.
  by rewrite -mulrBr normrM -mulrA ler_wpM2l // F0_lip.
have iphi := integrable_gauss_lipschitz (@cgmt_aux_lipschitz R N M B B0 rho Bb).
have hE : r * E <= Ep.
  rewrite /E /Ep -RintegralZl //; apply: le_Rintegral => //.
  by move=> z _; exact: (cgmt_aux_cone_ge Kcone BK Br _ _ B0).
apply: le_trans (@cgmt_escape_tail R N M B rho B0 Bb u u0).
apply: le_measure; rewrite ?inE.
- by have := mPhi measurableT (measurable_itv `]-oo, r * E - rho - u]);
    rewrite setTI.
- have mf : measurable_fun setT (fun a : 'rV[R]_(N * M) =>
      `|escape_inf B (vec_mx a : 'M[R]_(N, M)) - EP|).
    apply: measurableT_comp; first exact: normr_measurable.
    by apply: measurable_funB => //; exact: measurable_cst.
  have := mf measurableT _ (measurable_itv `[u, +oo[).
  rewrite setTI; congr (measurable _).
  by apply/seteqP; split => a /=; rewrite in_itv /= andbT.
- move=> a /= ha; rewrite -/EP distrC.
  apply: (le_trans _ (ler_norm _)); lra.
Qed.

End cone_escape.
