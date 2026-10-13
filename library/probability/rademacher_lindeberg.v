From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions interval reals.
From mathcomp Require Import ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral numfun measurable_realfun.
From mathcomp Require Import probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral.
From GaussianAnalysis.gaussian Require Import gauss gauss_moments.
From GaussianAnalysis.probability Require Import lindeberg.

(**md**************************************************************************)
(* # Lindeberg's replacement of uniform signs by Gaussians                    *)
(*                                                                            *)
(* For a bounded measurable F : 'rV[R]_n -> R whose third derivative along    *)
(* the coordinate j is at most c_j in absolute value, the average of F over   *)
(* the 2^n rows of signs and its integral against gauss n differ by at most   *)
(* (1/2) \sum_j c_j (rademacher_gauss_lindeberg). This is the                 *)
(* coordinate-replacement form of the Lindeberg principle (Chatterjee, 'A     *)
(* generalization of the Lindeberg principle', Ann. Probab. 34 (2006),        *)
(* Theorem 1.1) for uniform signs and standard Gaussians, which have the      *)
(* same first two moments.                                                    *)
(*                                                                            *)
(* Part of target T6 of phase 12: a Rocq formalization of the credited        *)
(* argument of the first paragraph of the proof of Theorem ext:sign of 'The   *)
(* free energy of the Ising random perceptron' (family 222 of the OpenAI math *)
(* collection, revision 1581d4cbd, sections/extensions.tex). The collection   *)
(* has no Lean version of it.                                                 *)
(*                                                                            *)
(* The coordinates are replaced one at a time, by induction on n: Fubini      *)
(* along rV_cons for gauss n.+1 (Rintegral_gauss_cons) and the                *)
(* decomposition of the rows of signs by their first coordinate               *)
(* (sum_sign_rowS). In one coordinate, Taylor's formula of order two and the  *)
(* first two moments give the constant (1 + E |g|^3) / 6 <= 1/2.              *)
(*                                                                            *)
(* Proved:                                                                    *)
(* - derive_le_cmp: |g b - g a| <= k b - k a when |g'| <= k' on [a, b];       *)
(*   taylor2_le: |f t - f 0 - f'(0) t - f''(0) t^2 / 2| <= c |t|^3 / 6 when   *)
(*   |f'''| <= c everywhere.                                                  *)
(* - Rintegral_normal_quadratic: E (a + b g + c g^2) = a + c, and             *)
(*   Rintegral_normal_abs3: E |g|^3 <= 2, for g of law N(0, 1).               *)
(* - rademacher_gauss_step: |(f 1 + f (-1)) / 2 - E f(g)| <= c / 2 when       *)
(*   |f'''| <= c everywhere.                                                  *)
(* - Rintegral_gauss_cons: for F bounded and measurable on 'rV[R]_n.+1, the   *)
(*   integral of F against gauss n.+1 is the integral against gauss n of      *)
(*   y |-> \int[N]_t F (rV_cons (t, y)).                                      *)
(* - rademacher_gauss_lindeberg: the comparison above.                        *)
(*                                                                            *)
(* ```                                                                        *)
(*    sign_row s == the row of the signs (if s i then 1 else -1) of           *)
(*                  s : {ffun 'I_n -> bool}                                   *)
(* ffun_cons b s == the function on 'I_n.+1 with value b at 0 and s on the    *)
(*                  other indices                                             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section taylor2.
Context {R : realType}.

Lemma is_derive_continuous (f f' : R -> R) :
  (forall u : R, is_derive u 1 f (f' u)) -> continuous f.
Proof.
move=> df u; apply: differentiable_continuous; apply/derivable1_diffP.
by case: (df u).
Qed.

(* The mean value inequality with a comparison function: if |g'| <= k' on
   [a, b], then |g b - g a| <= k b - k a. *)
Lemma derive_le_cmp (g g' k k' : R -> R) (a b : R) : a <= b ->
  (forall u : R, is_derive u 1 g (g' u)) ->
  (forall u : R, is_derive u 1 k (k' u)) ->
  (forall u, a <= u -> u <= b -> `|g' u| <= k' u) ->
  `|g b - g a| <= k b - k a.
Proof.
move=> ab dg dk hk.
have [->|ab'] := eqVneq a b; first by rewrite !subrr normr0.
have altb : a < b by rewrite lt_neqAle ab' ab.
have du1 (u : R) : is_derive u 1 (fun u => k u - g u) (k' u - g' u).
  exact: is_deriveB.
have du2 (u : R) : is_derive u 1 (fun u => k u + g u) (k' u + g' u).
  exact: is_deriveD.
have [c1 c1I E1] := MVT altb (fun u _ => du1 u)
  (continuous_subspaceT (is_derive_continuous du1)).
have [c2 c2I E2] := MVT altb (fun u _ => du2 u)
  (continuous_subspaceT (is_derive_continuous du2)).
move: c1I c2I; rewrite !in_itv /= => /andP[c1a c1b] /andP[c2a c2b].
have := hk c1 (ltW c1a) (ltW c1b); rewrite ler_norml => /andP[h1 h1'].
have := hk c2 (ltW c2a) (ltW c2b); rewrite ler_norml => /andP[h2 h2'].
have ba : 0 < b - a by rewrite subr_gt0.
have q1 : 0 <= k' c1 - g' c1 by lra.
have q2 : 0 <= k' c2 + g' c2 by lra.
have p1 := mulr_ge0 q1 (ltW ba).
have p2 := mulr_ge0 q2 (ltW ba).
rewrite ler_norml; apply/andP; split; lra.
Qed.

(* Taylor's formula of order two, with a bound c on the third derivative. *)
Lemma taylor2_le (f f1 f2 f3 : R -> R) (c : R) :
  (forall t : R, is_derive t 1 f (f1 t)) ->
  (forall t : R, is_derive t 1 f1 (f2 t)) ->
  (forall t : R, is_derive t 1 f2 (f3 t)) -> (forall t, `|f3 t| <= c) ->
  forall t, `|f t - f 0 - f1 0 * t - f2 0 * t ^+ 2 / 2| <= c * `|t| ^+ 3 / 6.
Proof.
move=> d0 d1 d2 c3 t.
have c0 : 0 <= c by apply: le_trans (c3 0); exact: normr_ge0.
pose g2 u := f1 u - f2 0 * u.
pose g3 u := f u - f1 0 * u - f2 0 * u ^+ 2 / 2.
have dlin (a u : R) : is_derive u 1 (fun u : R => a * u) a.
  by apply: is_derive_eq; rewrite /GRing.scale /= mulr1.
have dsq (a u : R) : is_derive u 1 (fun u : R => a * u ^+ 2 / 2) (a * u).
  by apply: is_derive_eq; rewrite /GRing.scale /=; field.
have dcube (a u : R) :
    is_derive u 1 (fun u : R => a * u ^+ 3 / 6) (a * u ^+ 2 / 2).
  by apply: is_derive_eq; rewrite /GRing.scale /=; field.
have dnsq (u : R) :
    is_derive u 1 (fun u : R => - (c * u ^+ 2 / 2)) (- (c * u)).
  exact: is_deriveN.
have dg2 (u : R) : is_derive u 1 g2 (f2 u - f2 0).
  by rewrite /g2; apply: is_derive_eq; rewrite /GRing.scale /=; ring.
have dg3 (u : R) : is_derive u 1 g3 (f1 u - f1 0 - f2 0 * u).
  by rewrite /g3; apply: is_derive_eq; rewrite /GRing.scale /=; field.
have z2 : (0 : R) ^+ 2 = 0 by rewrite expr2 mul0r.
have z3 : (0 : R) ^+ 3 = 0 by rewrite !exprS mul0r.
(* |f'' u - f'' 0| <= c |u| *)
have s1 u : `|f2 u - f2 0| <= c * `|u|.
  case: (leP 0 u) => u0.
    have := derive_le_cmp u0 d2 (dlin c) (fun s _ _ => c3 s).
    by rewrite (ger0_norm u0) mulr0 subr0.
  have := derive_le_cmp (ltW u0) d2 (dlin c) (fun s _ _ => c3 s).
  by rewrite distrC (ltr0_norm u0) mulr0 sub0r mulrN.
(* |f' s - f' 0 - f'' 0 s| <= c s^2 / 2 *)
have s2 s : `|g2 s - g2 0| <= c * s ^+ 2 / 2.
  case: (leP 0 s) => s0.
    have b u : 0 <= u -> u <= s -> `|f2 u - f2 0| <= c * u.
      by move=> u0 _; rewrite -[X in c * X](ger0_norm u0).
    have := derive_le_cmp s0 dg2 (dsq c) b.
    by rewrite z2 mulr0 mul0r subr0.
  have b u : s <= u -> u <= 0 -> `|f2 u - f2 0| <= - (c * u).
    by move=> _ u0; rewrite -mulrN -[X in c * X](ler0_norm u0).
  have := derive_le_cmp (ltW s0) dg2 dnsq b.
  by rewrite distrC z2 mulr0 mul0r oppr0 sub0r opprK.
have b3 u : `|f1 u - f1 0 - f2 0 * u| <= c * u ^+ 2 / 2.
  have := s2 u; rewrite /g2 mulr0 subr0.
  by have -> : f1 u - f2 0 * u - f1 0 = f1 u - f1 0 - f2 0 * u by ring.
have g30 : g3 0 = f 0 by rewrite /g3 mulr0 z2 mulr0 mul0r !subr0.
have -> : f t - f 0 - f1 0 * t - f2 0 * t ^+ 2 / 2 = g3 t - g3 0.
  by rewrite g30 /g3; ring.
case: (leP 0 t) => t0.
  have := derive_le_cmp t0 dg3 (dcube c) (fun u _ _ => b3 u).
  by rewrite z3 mulr0 mul0r subr0 (ger0_norm t0).
have := derive_le_cmp (ltW t0) dg3 (dcube c) (fun u _ _ => b3 u).
rewrite distrC z3 mulr0 mul0r sub0r (ltr0_norm t0).
by have -> : c * (- t) ^+ 3 / 6 = - (c * t ^+ 3 / 6) by ring.
Qed.

End taylor2.

Section rademacher_gauss_step.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma integrable_normal_affine (a b : R) :
  N.-integrable [set: R] (EFin \o (fun t => a + b * t)).
Proof.
apply: (integrable_normal_poly (C := `|a| + `|b|) (k := 1)) => [|t].
  by apply: measurable_funD => //; apply: measurable_funM.
rewrite expr1 (le_trans (ler_normD _ _)) // normrM.
by have := normr_ge0 a; have := normr_ge0 b; have := normr_ge0 t; nra.
Qed.

Lemma integrable_normal_sqr (a : R) :
  N.-integrable [set: R] (EFin \o (fun t => a * t ^+ 2)).
Proof.
apply: (integrable_normal_poly (C := `|a|) (k := 2)) => [|t].
  by apply: measurable_funM => //; apply: measurable_funX.
by rewrite normrM normrX; have := normr_ge0 a; have := sqr_ge0 `|t|; nra.
Qed.

(* E (a + b g + c g^2) = a + c for g of law N(0, 1). *)
Lemma Rintegral_normal_quadratic (a b c : R) :
  \int[N]_t (a + b * t + c * t ^+ 2) = a + c.
Proof.
have m1 : \int[N]_t t = 0 by rewrite /Rintegral normal_mean.
have m2 : \int[N]_t t ^+ 2 = 1.
  by rewrite /Rintegral (normal_moment_even 1) big_ord1.
have i0 : N.-integrable setT (EFin \o (fun=> a)).
  exact: finite_measure_integrable_cst.
have i1 : N.-integrable setT (EFin \o (fun t : R => t)).
  apply: (integrable_normal_poly (C := 1) (k := 1)) => // t.
  by rewrite expr1 mul1r lerDr.
have i2 : N.-integrable setT (EFin \o (fun t : R => t ^+ 2)).
  apply: (integrable_normal_poly (C := 1) (k := 2)) => [|t].
    exact: measurable_funX.
  by rewrite normrX mul1r lerDr.
have ib : N.-integrable setT (EFin \o (fun t : R => b * t)).
  apply: (integrable_normal_poly (C := `|b|) (k := 1)) => [|t].
    exact: measurable_funM.
  by rewrite normrM expr1 ler_wpM2l // lerDr.
have ia := integrable_normal_affine a b.
have ic := integrable_normal_sqr c.
rewrite RintegralD // RintegralD // Rintegral_cst // !RintegralZl // m1 m2.
by rewrite [X in a * fine X]probability_setT /= mulr1 mulr0 addr0 mulr1.
Qed.

(* E |g|^3 <= 2, from |t|^3 <= (t^2 + t^4) / 2. *)
Lemma Rintegral_normal_abs3 : \int[N]_t `|t| ^+ 3 <= 2.
Proof.
have p4 (t : R) : t ^+ 4 = (t ^+ 2) ^+ 2 by rewrite -exprM.
have n4 (t : R) : `|t| ^+ 4 = t ^+ 4 by rewrite -normrX ger0_norm // p4 sqr_ge0.
have i3 : N.-integrable setT (EFin \o (fun t : R => `|t| ^+ 3)).
  apply: (integrable_normal_poly (C := 1) (k := 3)) => [|t].
    by apply: measurable_funX; exact: normr_measurable.
  by rewrite normrX normr_id mul1r lerDr.
have i2 : N.-integrable setT (EFin \o (fun t : R => t ^+ 2)).
  apply: (integrable_normal_poly (C := 1) (k := 2)) => [|t].
    exact: measurable_funX.
  by rewrite normrX mul1r lerDr.
have i4 : N.-integrable setT (EFin \o (fun t : R => t ^+ 4)).
  apply: (integrable_normal_poly (C := 1) (k := 4)) => [|t].
    exact: measurable_funX.
  by rewrite normrX mul1r lerDr.
have i24 : N.-integrable setT (EFin \o (fun t : R => t ^+ 2 + t ^+ 4)).
  apply: (integrable_normal_poly (C := 2) (k := 4)) => [|t].
    by apply: measurable_funD; exact: measurable_funX.
  have h : 0 <= t ^+ 2 + t ^+ 4 by rewrite addr_ge0 // ?p4 sqr_ge0.
  rewrite n4 (ger0_norm h) p4.
  by have := sqr_ge0 (t ^+ 2 - 1); nra.
have i24h : N.-integrable setT (EFin \o (fun t : R => (t ^+ 2 + t ^+ 4) / 2)).
  apply: (integrable_normal_poly (C := 1) (k := 4)) => [|t].
    apply: measurable_funM => //.
    by apply: measurable_funD; exact: measurable_funX.
  have h : 0 <= (t ^+ 2 + t ^+ 4) / 2.
    by rewrite divr_ge0 // addr_ge0 // ?p4 sqr_ge0.
  rewrite n4 (ger0_norm h) p4.
  by have := sqr_ge0 (t ^+ 2 - 1); nra.
have m2 : \int[N]_t t ^+ 2 = 1.
  by rewrite /Rintegral (normal_moment_even 1) big_ord1.
have m4 : \int[N]_t t ^+ 4 = 3.
  by rewrite /Rintegral (normal_moment_even 2) !big_ord_recr big_ord0 /= !mul1r.
apply: le_trans (le_Rintegral measurableT i3 i24h _) _; last first.
  by rewrite RintegralZr // RintegralD // m2 m4; lra.
move=> t _ /=; rewrite -(n4 t) (_ : t ^+ 2 = `|t| ^+ 2).
  by rewrite -normrX ger0_norm // sqr_ge0.
have := mulr_ge0 (sqr_ge0 `|t|) (sqr_ge0 (`|t| - 1)).
by have := normr_ge0 t; move: `|t| => u u0 h; nra.
Qed.

(* One coordinate: if |f'''| <= c, then a uniform sign and a standard
   Gaussian give expectations of f within c / 2. *)
Lemma rademacher_gauss_step (f f1 f2 f3 : R -> R) (c : R) :
  (forall t : R, is_derive t 1 f (f1 t)) ->
  (forall t : R, is_derive t 1 f1 (f2 t)) ->
  (forall t : R, is_derive t 1 f2 (f3 t)) -> (forall t, `|f3 t| <= c) ->
  `|(f 1 + f (-1)) / 2 - \int[N]_t f t| <= c / 2.
Proof.
move=> d0 d1 d2 c3.
have c0 : 0 <= c by apply: le_trans (c3 0); exact: normr_ge0.
(* f = q + r, with q the Taylor polynomial of degree two at 0 *)
pose q t := f 0 + f1 0 * t + f2 0 / 2 * t ^+ 2.
pose r t := f t - q t.
have rb t : `|r t| <= c / 6 * `|t| ^+ 3.
  have -> : r t = f t - f 0 - f1 0 * t - f2 0 * t ^+ 2 / 2.
    by rewrite /r /q; ring.
  have -> : c / 6 * `|t| ^+ 3 = c * `|t| ^+ 3 / 6 by ring.
  exact: taylor2_le d0 d1 d2 c3 t.
have mf : measurable_fun setT f.
  exact: continuous_measurable_fun (is_derive_continuous d0).
have mq : measurable_fun setT q.
  apply: measurable_funD.
    by apply: measurable_funD => //; exact: measurable_funM.
  by apply: measurable_funM => //; exact: measurable_funX.
have mr : measurable_fun setT r by exact: measurable_funB.
have ir : N.-integrable setT (EFin \o r).
  apply: (integrable_normal_poly (C := c / 6) (k := 3)) => // t.
  apply: le_trans (rb t) _; apply: ler_wpM2l; first by rewrite divr_ge0.
  by rewrite lerDr.
have iq : N.-integrable setT (EFin \o q).
  apply: (integrable_normal_poly (C := `|f 0| + `|f1 0| + `|f2 0 / 2|)
    (k := 2)) => // t.
  rewrite /q (le_trans (ler_normD _ _)) //.
  rewrite (le_trans (lerD (ler_normD _ _) (lexx _))) //.
  rewrite (normrM (f1 0)) (normrM (f2 0 / 2)) normrX.
  have := normr_ge0 (f 0); have := normr_ge0 (f1 0).
  have := normr_ge0 (f2 0 / 2); have := normr_ge0 t.
  have := sqr_ge0 (`|t| - 1).
  by move: `|t| `|f 0| `|f1 0| `|f2 0 / 2| => u a b e *; nra.
(* E f(g) = f 0 + f''(0) / 2 + E r(g), and |E r(g)| <= c / 3 *)
have Ef : \int[N]_t f t = f 0 + f2 0 / 2 + \int[N]_t r t.
  have -> : \int[N]_t f t = \int[N]_t (q t + r t).
    by congr Rintegral; apply: funext => t; rewrite /r addrC subrK.
  by rewrite RintegralD // Rintegral_normal_quadratic.
have Er : `|\int[N]_t r t| <= c / 3.
  apply: le_trans (le_normr_Rintegral measurableT ir) _.
  have ia : N.-integrable setT (EFin \o (fun t : R => `|t| ^+ 3)).
    apply: (integrable_normal_poly (C := 1) (k := 3)) => [|t].
      by apply: measurable_funX; exact: normr_measurable.
    by rewrite normrX normr_id mul1r lerDr.
  have ib : N.-integrable setT (EFin \o (fun t : R => c / 6 * `|t| ^+ 3)).
    apply: (integrable_normal_poly (C := c / 6) (k := 3)) => [|t].
      apply: measurable_funM => //.
      by apply: measurable_funX; exact: normr_measurable.
    rewrite normrM normrX normr_id (ger0_norm (_ : 0 <= c / 6)) ?divr_ge0 //.
    by apply: ler_wpM2l; [rewrite divr_ge0 | rewrite lerDr].
  apply: le_trans (le_Rintegral measurableT (integrable_norm ir) ib
    (fun t _ => rb t)) _.
  rewrite RintegralZl //.
  have := Rintegral_normal_abs3.
  have c6 : 0 <= c / 6 by rewrite divr_ge0.
  move: (\int[N]_t `|t| ^+ 3) => m h.
  by have := ler_wpM2l c6 h; lra.
(* the average over the signs is f 0 + f''(0) / 2 + (r 1 + r (-1)) / 2 *)
have -> : (f 1 + f (-1)) / 2 = f 0 + f2 0 / 2 + (r 1 + r (-1)) / 2.
  by rewrite /r /q; field.
have key (A B I F0 F2 : R) : `|A| <= c / 6 -> `|B| <= c / 6 ->
    `|I| <= c / 3 -> `|F0 + F2 / 2 + (A + B) / 2 - (F0 + F2 / 2 + I)| <= c / 2.
  move=> hA hB hI; clear -c0 hA hB hI.
  move: hA hB hI; rewrite !ler_norml => /andP[? ?] /andP[? ?] /andP[? ?].
  by apply/andP; split; lra.
rewrite Ef; apply: key => //.
  by have := rb 1; rewrite normr1 expr1n mulr1.
by have := rb (-1); rewrite normrN normr1 expr1n mulr1.
Qed.

End rademacher_gauss_step.

Section rademacher_gauss.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

(* The row of the signs of s. *)
Definition sign_row n (s : {ffun 'I_n -> bool}) : 'rV[R]_n :=
  \row_i (if s i then 1 else -1).

(* A function on 'I_n.+1, from its value at 0 and a function on 'I_n. *)
Definition ffun_cons n (b : bool) (s : {ffun 'I_n -> bool}) :
  {ffun 'I_n.+1 -> bool} :=
  [ffun i => if unlift ord0 i is Some j then s j else b].

Lemma ffun_cons_bij n :
  bijective (fun p : bool * {ffun 'I_n -> bool} => ffun_cons p.1 p.2).
Proof.
exists (fun s : {ffun 'I_n.+1 -> bool} =>
  (s ord0, [ffun j => s (lift ord0 j)])).
  case=> b s /=; rewrite /ffun_cons ffunE unlift_none; congr pair.
  by apply/ffunP => j; rewrite !ffunE liftK.
move=> s; apply/ffunP => i; rewrite /ffun_cons ffunE /=.
by case: unliftP => [j ->|->] //; rewrite ffunE.
Qed.

Lemma sign_row_cons n b (s : {ffun 'I_n -> bool}) :
  sign_row (ffun_cons b s) = rV_cons ((if b then 1 else -1), sign_row s).
Proof.
apply/rowP => i; case: (unliftP ord0 i) => [j ->|->].
  by rewrite rV_consS /sign_row !mxE ffunE liftK.
by rewrite rV_cons0 /sign_row mxE ffunE unlift_none.
Qed.

Lemma sum_sign_rowS n (G : 'rV[R]_n.+1 -> R) :
  \sum_(s : {ffun 'I_n.+1 -> bool}) G (sign_row s) =
  \sum_(s : {ffun 'I_n -> bool})
    (G (rV_cons (1, sign_row s)) + G (rV_cons (-1, sign_row s))).
Proof.
rewrite (reindex (fun p : bool * {ffun 'I_n -> bool} => ffun_cons p.1 p.2))
  /=; first exact: onW_bij (ffun_cons_bij n).
rewrite -(pair_big xpredT xpredT (fun b s => G (sign_row (ffun_cons b s)))).
rewrite /= big_bool /= -big_split /=.
by apply: eq_bigr => s _; rewrite !sign_row_cons.
Qed.

Lemma rV_cons_line n (a t : R) (y : 'rV[R]_n) (j : 'I_n) :
  rV_cons (a, t *: delta_mx 0 j + y) =
  t *: delta_mx 0 (lift ord0 j) + rV_cons (a, y).
Proof.
apply/rowP => i; case: (unliftP ord0 i) => [k ->|->].
  rewrite (rV_consS (a, _) k) /= [RHS]mxE (rV_consS (a, y) k) /= !mxE.
  by rewrite (inj_eq (@lift_inj _ ord0)).
rewrite rV_cons0 [RHS]mxE rV_cons0 /= !mxE.
by rewrite (negbTE (neq_lift ord0 j)) andbF mulr0 add0r.
Qed.

Lemma rV_cons_line0 n (t : R) (y : 'rV[R]_n) :
  rV_cons (t, y) = t *: delta_mx 0 ord0 + rV_cons (0, y).
Proof.
apply/rowP => i; case: (unliftP ord0 i) => [k ->|->].
  rewrite (rV_consS (t, y) k) [RHS]mxE (rV_consS (0, y) k) /= !mxE.
  by rewrite eq_sym (negbTE (neq_lift ord0 k)) andbF mulr0 add0r.
by rewrite rV_cons0 [RHS]mxE rV_cons0 /= !mxE !eqxx mulr1 addr0.
Qed.

(* Fubini along the first coordinate, for a bounded measurable F. *)
Lemma Rintegral_gauss_cons n (F : 'rV[R]_n.+1 -> R) (C : R) :
  measurable_fun setT F -> (forall x, `|F x| <= C) ->
  \int[gauss n.+1]_x F x = \int[gauss n]_y \int[N]_t F (rV_cons (t, y)).
Proof.
move=> mF FC.
have mFc : measurable_fun setT (F \o @rV_cons R n).
  exact: measurableT_comp mF (@measurable_rV_cons R n).
have iFc : (N \x gauss n)%E.-integrable setT (EFin \o (F \o @rV_cons R n)).
  exact: (bounded_integrable _ mFc (fun p => FC _)).
have mFt (y : 'rV[R]_n) : measurable_fun setT (fun t : R => F (rV_cons (t, y))).
  exact: measurableT_comp mFc (pair2_measurable y).
have mG : measurable_fun setT (fun y => \int[N]_t F (rV_cons (t, y))).
  apply: (measurable_partial_Rintegral (gauss n) N
    (G := fun p => F (rV_cons (p.2, p.1))) (C := C)).
    exact: (measurableT_comp mFc (@measurable_swap _ _ _ _)).
  by move=> p; exact: FC.
have GC y : `|\int[N]_t F (rV_cons (t, y))| <= C.
  exact: (Rintegral_bounded N (mFt y) (fun t => FC _)).
apply: EFin_inj; rewrite (EFin_Rintegral_bounded (gauss n.+1) mF FC).
rewrite (EFin_Rintegral_bounded (gauss n) mG GC).
rewrite [LHS](@integral_distribution _ _ _ _ _ (N \x gauss n)%E
  (@rV_cons R n)); [exact: measurableT_comp mF|exact: iFc|].
rewrite -(integral21_prod_meas1 iFc) /=; apply: eq_integral => y _.
by rewrite (EFin_Rintegral_bounded N (mFt y) (fun t => FC _)).
Qed.

(* Lindeberg's replacement of uniform signs by Gaussians: if F is bounded
   and measurable and its third derivative along the coordinate j is at most
   c_j in absolute value, then the averages of F over the rows of signs and
   against gauss n differ by at most (1/2) \sum_j c_j. *)
Theorem rademacher_gauss_lindeberg n (F : 'rV[R]_n -> R) (C : R)
    (c : 'I_n -> R) :
  measurable_fun setT F -> (forall x, `|F x| <= C) ->
  (forall (j : 'I_n) (x : 'rV[R]_n), exists F1 F2 F3 : R -> R,
    [/\ forall t : R, is_derive t 1 (fun s => F (s *: delta_mx 0 j + x)) (F1 t),
        forall t : R, is_derive t 1 F1 (F2 t),
        forall t : R, is_derive t 1 F2 (F3 t) &
        forall t, `|F3 t| <= c j]) ->
  `|(2 ^+ n)^-1 * \sum_(s : {ffun 'I_n -> bool}) F (sign_row s) -
    \int[gauss n]_x F x| <= 2^-1 * \sum_j c j.
Proof.
elim: n F C c => [|n IH] F C c mF FC dF.
  (* in dimension 0, both averages are F 0 *)
  have -> : F = fun=> F 0.
    by apply: funext => x; congr F; apply/rowP => -[].
  rewrite big_ord0 mulr0 expr0 invr1 mul1r sumr_const card_ffun card_bool.
  rewrite card_ord expn0 Rintegral_cst //.
  by rewrite [X in F 0 * fine X]probability_setT /= mulr1 subrr normr0.
(* Fp averages F over the sign of the first coordinate *)
pose Fp (y : 'rV[R]_n) := (F (rV_cons (1, y)) + F (rV_cons (-1, y))) / 2.
have mFa (a : R) :
    measurable_fun setT (fun y : 'rV[R]_n => F (rV_cons (a, y))).
  apply: measurableT_comp mF _.
  exact: measurableT_comp (@measurable_rV_cons R n) (pair1_measurable a).
have mFp : measurable_fun setT Fp.
  by apply: measurable_funM => //; apply: measurable_funD; exact: mFa.
have FpC y : `|Fp y| <= C.
  rewrite /Fp normrM (ger0_norm (_ : 0 <= 2^-1)) ?invr_ge0 //.
  have := FC (rV_cons (1, y)); have := FC (rV_cons (-1, y)).
  have := ler_normD (F (rV_cons (1, y))) (F (rV_cons (-1, y))).
  by move: `|_ + _| `|F _| `|F _| => u v w *; lra.
have avg_derive (f g f' g' : R -> R) :
    (forall t : R, is_derive t 1 f (f' t)) ->
    (forall t : R, is_derive t 1 g (g' t)) ->
    forall t : R, is_derive t 1 (fun s => (f s + g s) / 2) ((f' t + g' t) / 2).
  move=> df dg t; apply: is_derive_eq.
  by rewrite /GRing.scale /=; ring.
have dFp (j : 'I_n) (y : 'rV[R]_n) : exists F1 F2 F3 : R -> R,
    [/\ forall t : R,
          is_derive t 1 (fun s => Fp (s *: delta_mx 0 j + y)) (F1 t),
        forall t : R, is_derive t 1 F1 (F2 t),
        forall t : R, is_derive t 1 F2 (F3 t) &
        forall t, `|F3 t| <= c (lift ord0 j)].
  have [A1 [A2 [A3 [a1 a2 a3 a4]]]] := dF (lift ord0 j) (rV_cons (1, y)).
  have [B1 [B2 [B3 [b1 b2 b3 b4]]]] := dF (lift ord0 j) (rV_cons (-1, y)).
  exists (fun t => (A1 t + B1 t) / 2), (fun t => (A2 t + B2 t) / 2),
    (fun t => (A3 t + B3 t) / 2); split.
  - move=> t; have -> : (fun s => Fp (s *: delta_mx 0 j + y)) =
        (fun s => (F (s *: delta_mx 0 (lift ord0 j) + rV_cons (1, y)) +
                   F (s *: delta_mx 0 (lift ord0 j) + rV_cons (-1, y))) / 2).
      by apply: funext => s; rewrite /Fp !rV_cons_line.
    exact: avg_derive.
  - exact: avg_derive.
  - exact: avg_derive.
  - move=> t; rewrite normrM (ger0_norm (_ : 0 <= 2^-1)) ?invr_ge0 //.
    have := a4 t; have := b4 t; have := ler_normD (A3 t) (B3 t).
    by move: `|_ + _| `|A3 t| `|B3 t| => u v w *; lra.
have IHp := IH Fp C (fun j => c (lift ord0 j)) mFp FpC dFp.
have Es : 2 ^- n.+1 * \sum_(s : {ffun 'I_n.+1 -> bool}) F (sign_row s) =
    2 ^- n * \sum_(s : {ffun 'I_n -> bool}) Fp (sign_row s).
  rewrite sum_sign_rowS /Fp -mulr_suml exprS invfM.
  by move: (\sum_s _) => S; rewrite mulrC [RHS]mulrC mulrA.
(* G integrates F against N in the first coordinate *)
pose G (y : 'rV[R]_n) := \int[N]_t F (rV_cons (t, y)).
have step y : `|Fp y - G y| <= c ord0 / 2.
  have [A1 [A2 [A3 [a1 a2 a3 a4]]]] := dF ord0 (rV_cons (0, y)).
  have := rademacher_gauss_step a1 a2 a3 a4.
  rewrite /Fp /G -(rV_cons_line0 1 y) -(rV_cons_line0 (-1) y).
  have -> // : (fun t => F (t *: delta_mx 0 ord0 + rV_cons (0, y))) =
      (fun t => F (rV_cons (t, y))).
  by apply: funext => t; rewrite (rV_cons_line0 t y).
have mFc : measurable_fun setT (F \o @rV_cons R n).
  exact: measurableT_comp mF (@measurable_rV_cons R n).
have mG : measurable_fun setT G.
  apply: (measurable_partial_Rintegral (gauss n) N
    (G := fun p => F (rV_cons (p.2, p.1))) (C := C)).
    exact: (measurableT_comp mFc (@measurable_swap _ _ _ _)).
  by move=> p; exact: FC.
have GC y : `|G y| <= C.
  apply: (Rintegral_bounded N _ (fun t => FC _)).
  exact: measurableT_comp mFc (pair2_measurable y).
have D : `|\int[gauss n]_y Fp y - \int[gauss n]_y G y| <= 2^-1 * c ord0.
  rewrite -RintegralB //; last 2 first.
      exact: (bounded_integrable _ mG GC).
    rewrite mulrC; apply: (Rintegral_bounded (gauss n) _ step).
    exact: measurable_funB.
  exact: (bounded_integrable _ mFp FpC).
rewrite Es (Rintegral_gauss_cons mF FC) -/G big_ord_recl.
apply: le_trans (ler_distD (\int[gauss n]_y Fp y) _ _) _.
by rewrite mulrDr addrC; apply: lerD.
Qed.

End rademacher_gauss.
