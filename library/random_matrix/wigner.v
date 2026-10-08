From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum poly matrix.
From mathcomp Require Import boolp classical_sets reals ereal.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.

(**md**************************************************************************)
(* # Wigner's semicircle law for the GOE                                      *)
(*                                                                            *)
(* Let W = goe_mx a for a of law gauss (d * d) (random_matrix/goe.v). The     *)
(* empirical law of its eigenvalues spec W (matrix/von_neumann.v) converges   *)
(* in probability to the semicircle law of radius 2. This is the form of the  *)
(* semicircle law that Lemma 5.14 of Koehler and Sohn (arXiv 2608.27372, line *)
(* 5905) cites from Anderson, Guionnet and Zeitouni. This file completes item *)
(* G7 of phase 5.                                                             *)
(*                                                                            *)
(* Proved:                                                                    *)
(*                                                                            *)
(* - weierstrass_lipschitz: Weierstrass's approximation theorem on a compact  *)
(*   interval for Lipschitz functions, by Bernstein polynomials (not in       *)
(*   MathComp-Analysis 1.16): bernstein_lipschitz, |B_n f (x) - f x| <= L /   *)
(*   (2 sqrt n) on [0, 1] for f L-Lipschitz, from the mean and the variance   *)
(*   of the binomial law (bernstein_mean, bernstein_var).                     *)
(*                                                                            *)
(* Planned results (phase 5, stage 2; names come with the proofs):            *)
(*                                                                            *)
(* - wigner: for every continuous f and eps > 0, the probability that |(1 /   *)
(*   d) \sum_i f (spec W i) - \int f d(semicircle_prob 2)| > eps tends to 0   *)
(*   as d tends to infinity: for polynomials from the moments and the         *)
(*   variance bound of goe.v and Chebyshev's inequality, then on the event    *)
(*   opnorm W < 3 by uniform approximation.                                   *)
(* - The same uniformly over a family f_t, t in a compact interval, with |f_t *)
(*   x - f_s x| <= L |t - s| for all x, as Lemma 5.14 needs for the functions *)
(*   (x - t)_+ and (x - t)_+^2.                                               *)
(* - In particular (1 / d) \tr (W^2) tends to 1 in probability.               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section bernstein.
Context {R : realType}.

(* The Bernstein basis C(n, k) x^k (1 - x)^(n - k). *)
Definition bernstein_basis (n k : nat) (x : R) : R :=
  'C(n, k)%:R * x ^+ k * (1 - x) ^+ (n - k).

Lemma bernstein_sum1 n x : \sum_(k < n.+1) bernstein_basis n k x = 1.
Proof.
have := exprDn (1 - x) x n; rewrite subrK expr1n => ->.
apply: eq_bigr => k _; rewrite /bernstein_basis -mulr_natl.
by rewrite mulr1 -[RHS]mulr_natl [(1 - x) ^+ _ * _]mulrC mulrA.
Qed.

(* k C(n + 1, k) = (n + 1) C(n, k - 1): the sums against k shift the
   degree. *)
Lemma bernstein_shift (g : nat -> R) m x :
  \sum_(k < m.+2) g k * k%:R * bernstein_basis m.+1 k x =
  m.+1%:R * x * \sum_(j < m.+1) g j.+1 * bernstein_basis m j x.
Proof.
rewrite big_ord_recl /= mulr0 mul0r add0r mulr_sumr; apply: eq_bigr => j _.
rewrite /bernstein_basis subSS exprS /bump /= add1n.
have := mul_bin_diag m.+1 j.
move=> /(congr1 (fun k => k%:R : R)); rewrite !natrM => hb.
transitivity (g j.+1 * (j.+1%:R * 'C(m.+1, j.+1)%:R) *
  (x * x ^+ j * (1 - x) ^+ (m - j))); first by ring.
by rewrite -hb; ring.
Qed.

(* The mean and the variance of the binomial law. *)
Lemma bernstein_mean n x :
  \sum_(k < n.+1) k%:R * bernstein_basis n k x = n%:R * x.
Proof.
case: n => [|m]; first by rewrite big_ord1 !mul0r.
have := bernstein_shift (fun=> 1) m x; under eq_bigr do rewrite mul1r.
by move=> ->; under eq_bigr do rewrite mul1r; rewrite bernstein_sum1 mulr1.
Qed.

Lemma bernstein_var n x :
  \sum_(k < n.+1) (k%:R - n%:R * x) ^+ 2 * bernstein_basis n k x =
  n%:R * x * (1 - x).
Proof.
case: n => [|m]; first by rewrite big_ord1 !mul0r subrr expr0n mul0r.
have h2 := bernstein_shift (fun k => k%:R) m x.
have hj : \sum_(j < m.+1) j.+1%:R * bernstein_basis m j x = m%:R * x + 1.
  under eq_bigr do rewrite -addn1 natrD mulrDl mul1r.
  by rewrite big_split /= bernstein_mean bernstein_sum1.
rewrite hj in h2; have hm1 := bernstein_mean m.+1 x.
have hs1 := bernstein_sum1 m.+1 x; set b := bernstein_basis m.+1.
have -> : \sum_(k < m.+2) (k%:R - m.+1%:R * x) ^+ 2 * b k x =
    \sum_(k < m.+2) k%:R * k%:R * b k x -
    2 * (m.+1%:R * x) * \sum_(k < m.+2) k%:R * b k x +
    (m.+1%:R * x) ^+ 2 * \sum_(k < m.+2) b k x.
  rewrite !mulr_sumr -sumrB -big_split /=; apply: eq_bigr => k _; ring.
by rewrite h2 hm1 hs1; ring.
Qed.

Lemma bernstein_basis_ge0 n k x : 0 <= x <= 1 -> 0 <= bernstein_basis n k x.
Proof.
case/andP => x0 x1.
by rewrite /bernstein_basis !mulr_ge0 ?ler0n ?exprn_ge0 // subr_ge0.
Qed.

(* The Bernstein polynomial of f of degree n. *)
Definition bernstein (f : R -> R) n (x : R) : R :=
  \sum_(k < n.+1) f (k%:R / n%:R) * bernstein_basis n k x.

(* For f L-Lipschitz on [0, 1], the Bernstein polynomial of degree n.+1 is
   within L / (2 sqrt (n + 1)) of f on [0, 1]. *)
Lemma bernstein_lipschitz (f : R -> R) (L : R) n x :
  (forall y z, 0 <= y <= 1 -> 0 <= z <= 1 -> `|f y - f z| <= L * `|y - z|) ->
  0 <= x <= 1 ->
  `|bernstein f n.+1 x - f x| <= L / (2 * Num.sqrt n.+1%:R).
Proof.
move=> hf hx.
have h01 : 0 <= (0 : R) <= 1 by rewrite lexx ler01.
have h11 : 0 <= (1 : R) <= 1 by rewrite lexx ler01.
have L0 : 0 <= L.
  have := hf 0 1 h01 h11; rewrite sub0r normrN normr1 mulr1; apply: le_trans.
  exact: normr_ge0.
set N := n.+1.
have b0 k : 0 <= bernstein_basis N k x by exact: bernstein_basis_ge0.
have -> : bernstein f N x - f x =
    \sum_(k < N.+1) (f (k%:R / N%:R) - f x) * bernstein_basis N k x.
  rewrite /bernstein -[f x in LHS]mulr1 -(bernstein_sum1 N x) mulr_sumr.
  by rewrite -sumrB; apply: eq_bigr => k _; rewrite mulrBl.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : \sum_(k < N.+1) L *
    (`|k%:R / N%:R - x| * bernstein_basis N k x) <= _).
  apply: ler_sum => k _; rewrite normrM (ger0_norm (b0 k)) [X in _ <= X]mulrA.
  apply: ler_wpM2r; first exact: b0.
  apply: hf => //.
  rewrite divr_ge0 ?ler0n //= ler_pdivrMr ?ltr0n // mul1r ler_nat.
  exact: (ltn_ord k).
rewrite -mulr_sumr; apply: (ler_wpM2l L0).
set s := Num.sqrt N%:R.
have N0 : (0 : R) < N%:R by rewrite ltr0n.
have s0 : 0 < s by rewrite sqrtr_gt0.
have sn : s != 0 by rewrite gt_eqF.
have sN : s ^+ 2 = N%:R by rewrite sqr_sqrtr // ltW.
(* |y| <= s y^2 + 1 / (4 s) *)
have amgm (y : R) : `|y| <= s * y ^+ 2 + (4%:R * s)^-1.
  rewrite -subr_ge0 -real_normK ?num_real //.
  have -> : s * `|y| ^+ 2 + (4%:R * s)^-1 - `|y| =
      s * (`|y| - (2%:R * s)^-1) ^+ 2 by field.
  by rewrite mulr_ge0 ?sqr_ge0 // ltW.
apply: le_trans (_ : \sum_(k < N.+1) (s * (k%:R / N%:R - x) ^+ 2 +
    (4%:R * s)^-1) * bernstein_basis N k x <= _).
  by apply: ler_sum => k _; apply: (ler_wpM2r (b0 k)); exact: amgm.
(* sum_k (k / N - x)^2 b_k = x (1 - x) / N *)
have hv : \sum_(k < N.+1) (k%:R / N%:R - x) ^+ 2 * bernstein_basis N k x =
    x * (1 - x) / N%:R.
  have Nn : (N%:R : R) != 0 by rewrite gt_eqF.
  have hvar := bernstein_var N x.
  transitivity (\sum_(k < N.+1)
      (k%:R - N%:R * x) ^+ 2 * bernstein_basis N k x / N%:R ^+ 2).
    by apply: eq_bigr => k _; field.
  by rewrite -mulr_suml hvar; field.
under eq_bigr do rewrite mulrDl -mulrA.
rewrite big_split /= -!mulr_sumr hv bernstein_sum1 mulr1.
have hx4 : x * (1 - x) <= 4%:R^-1.
  rewrite -subr_ge0 (_ : 4%:R^-1 - x * (1 - x) = (x - 2%:R^-1) ^+ 2).
    by field.
  exact: sqr_ge0.
apply: le_trans (_ : s * (4%:R^-1 / N%:R) + (4%:R * s)^-1 <= _).
  rewrite lerD2r; apply: (ler_wpM2l (ltW s0)).
  by apply: ler_wpM2r => //; rewrite invr_ge0 ltW.
by rewrite -sN le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

(* The Bernstein polynomial is a polynomial. *)
Lemma bernstein_polyE (f : R -> R) n : exists p : {poly R},
  forall x, bernstein f n x = p.[x].
Proof.
exists (\sum_(k < n.+1) (f (k%:R / n%:R) * 'C(n, k)%:R) *:
  ('X ^+ k * (1 - 'X) ^+ (n - k))).
move=> x; rewrite /bernstein horner_sum; apply: eq_bigr => k _.
by rewrite hornerZ hornerM !hornerE /bernstein_basis.
Qed.

(* Weierstrass's approximation theorem for Lipschitz functions on a
   compact interval, with an explicit degree. *)
Theorem weierstrass_lipschitz (f : R -> R) (L a b eps : R) :
  a < b -> 0 < eps ->
  (forall y z, a <= y <= b -> a <= z <= b -> `|f y - f z| <= L * `|y - z|) ->
  exists p : {poly R}, forall x, a <= x <= b -> `|p.[x] - f x| <= eps.
Proof.
move=> ab e0 hf; set c := b - a.
have c0 : 0 < c by rewrite subr_gt0.
have cn : c != 0 by rewrite gt_eqF.
(* g t = f (a + c t) is (L c)-Lipschitz on [0, 1] *)
pose g t := f (a + c * t).
have inI t : 0 <= t -> t <= 1 -> a <= a + c * t <= b.
  move=> t0 t1; apply/andP; split; first by rewrite lerDl mulr_ge0 // ltW.
  have ct : c * t <= c by rewrite ler_piMr // ltW.
  by rewrite -(subrK a b) [a + _]addrC lerD2r.
have hg y z : 0 <= y <= 1 -> 0 <= z <= 1 -> `|g y - g z| <= L * c * `|y - z|.
  move=> /andP[y0 y1] /andP[z0 z1].
  apply: le_trans (hf _ _ (inI _ y0 y1) (inI _ z0 z1)) _.
  by rewrite opprD addrACA subrr add0r -mulrBr normrM (gtr0_norm c0) mulrA.
(* the Bernstein polynomial of degree m + 1 >= (L c / (2 eps))^2 *)
pose m := archimedean.Num.truncn ((L * c / (2 * eps)) ^+ 2).
have [P hP] := bernstein_polyE g m.+1.
exists (P \Po (c^-1 *: ('X - a%:P))) => x /andP[xa xb].
set t := c^-1 * (x - a).
have t01 : 0 <= t <= 1.
  apply/andP; split; first by rewrite mulr_ge0 ?invr_ge0 ?subr_ge0 // ltW.
  by rewrite ler_pdivrMl // mulr1 lerD2r.
rewrite horner_comp hornerZ hornerD hornerN hornerX hornerC -/t -hP.
have -> : f x = g t by rewrite /g /t mulrA divff // mul1r addrC subrK.
apply: le_trans (bernstein_lipschitz m hg t01) _.
have [Lc0|Lc0] := leP (L * c) 0.
  apply: le_trans (ltW e0).
  by rewrite mulr_le0_ge0 // invr_ge0 mulr_ge0 ?sqrtr_ge0.
rewrite ler_pdivrMr ?mulr_gt0 ?sqrtr_gt0 ?ltr0n //.
set u := L * c / (2 * eps).
have u0 : 0 < u by rewrite divr_gt0 // mulr_gt0.
have hu : u ^+ 2 < m.+1%:R by exact: archimedean.Num.Theory.truncnS_gt.
have hs : u < Num.sqrt m.+1%:R.
  by rewrite -[u]ger0_norm ?ltW // -sqrtr_sqr ltr_sqrt ?ltr0n.
have -> : L * c = 2 * eps * u.
  by rewrite /u mulrCA divff ?mulr1 // mulf_neq0 // gt_eqF.
rewrite [X in _ <= X]mulrCA [X in _ <= X]mulrA.
by rewrite ler_pM2l ?mulr_gt0 // ltW.
Qed.

End bernstein.
