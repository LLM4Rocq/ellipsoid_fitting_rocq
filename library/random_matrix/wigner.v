From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum poly matrix.
From mathcomp Require Import boolp classical_sets functions interval reals ereal.
From mathcomp Require Import topology normedtype sequences derive realfun exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability ring_tactic field_tactic.
From mathcomp Require Import arithmetic_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.probability Require Import semicircle_law.
From GaussianAnalysis.gaussian Require Import gauss_ibp gauss_interpolation.
From GaussianAnalysis.comparison Require Import gauss_smoothing gauss_concentration.
From GaussianAnalysis.matrix Require Import euclidean opnorm von_neumann.
From GaussianAnalysis.random_matrix Require Import goe.

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
(* - segner: Segner's recurrence c_(n+1) = \sum_(i <= n) c_i c_(n-i) for a    *)
(*   sequence with c_0 = 1 and (i + 2) c_(i+1) = (4 i + 2) c_i, by sums       *)
(*   symmetric under i |-> n - i (the Catalan numbers, without generating     *)
(*   functions).                                                              *)
(* - semicircle_catalan: the moments m_k of semicircle_prob 2 satisfy the     *)
(*   recursion of the Schwinger-Dyson equation of goe.v in the limit, m_(k+1) *)
(*   = \sum_(r < k) m_r m_(k-1-r), from segner and the moment recursion and   *)
(*   the odd moments of semicircle_law.v.                                     *)
(* - goe_moment_cvg: for W = goe_mx a with a of law gauss (d * d), E tr W^k / *)
(*   d tends to the k-th moment of semicircle_prob 2 as d tends to infinity,  *)
(*   by induction on k with goe_tr_sd of goe.v, whose covariance terms tend   *)
(*   to 0 (goe_tr_cov_cvg, from goe_tr_var_small and Rintegral_cov_le); the   *)
(*   same holds for the eigenvalues clipped to [-3, 3] (goe_clip_cvg).        *)
(* - wigner: Wigner's semicircle law. For f continuous and L-Lipschitz on     *)
(*   [-3, 3], and eps > 0, P(|goe_stat f a - \int f dsigma| >= eps) <= eps    *)
(*   for every large d, where goe_stat f a = (1 / d) \sum_i f (spec W 0 i)    *)
(*   and sigma = semicircle_prob 2. Off the event opnorm W >= 3, whose        *)
(*   probability tends to 0 (goe_opnorm_tail_small), the statistic is that of *)
(*   f o clip 3, which is Lipschitz (clip_comp_lipschitz); its mean tends to  *)
(*   \int f dsigma by polynomial approximation on [-3, 3]                     *)
(*   (goe_stat_clip_mean_cvg, with goe_stat_poly_clip, semicircle_poly and    *)
(*   semicircle_clip), and it concentrates around its mean (goe_stat_conc:    *)
(*   goe_stat g is sqrt 2 L / d-Lipschitz in a, goe_stat_lipschitz).          *)
(*                                                                            *)
(* Planned results (phase 5, stage 2; names come with the proofs):            *)
(*                                                                            *)
(* - The same uniformly over a family f_t, t in a compact interval, with |f_t *)
(*   x - f_s x| <= L |t - s| for all x, as Lemma 5.14 needs for the functions *)
(*   (x - t)_+ and (x - t)_+^2.                                               *)
(*                                                                            *)
(* ```                                                                        *)
(*   goe_stat f a == (1 / d) \sum_i f (spec (goe_mx a) 0 i), the empirical    *)
(*                   mean of f over the spectrum of the GOE matrix goe_mx a   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
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

Section catalan.
Context {R : realFieldType}.

(* Segner's recurrence c_(n+1) = \sum_(i <= n) c_i c_(n-i) for a sequence
   with c_0 = 1 and (i + 2) c_(i+1) = (4 i + 2) c_i, such as the Catalan
   numbers and the even moments of the semicircle law of radius 2. *)
Lemma segner (c : nat -> R) : c 0%N = 1 ->
  (forall i, i.+2%:R * c i.+1 = (4 * i%:R + 2) * c i) ->
  forall n, \sum_(0 <= i < n.+1) c i * c (n - i)%N = c n.+1.
Proof.
move=> c0 cS.
pose S n := \sum_(0 <= i < n.+1) c i * c (n - i)%N.
(* \sum_i i c_i c_(n-i) = n S n / 2, by i |-> n - i *)
have Sw n : 2 * \sum_(0 <= i < n.+1) i%:R * (c i * c (n - i)%N) = n%:R * S n.
  rewrite mulr_natl mulr2n {2}big_nat_rev /= add0n.
  rewrite -big_split /= /S mulr_sumr; apply: eq_big_nat => i /andP[_ ilt].
  have iln : (i <= n)%N by rewrite -ltnS.
  rewrite subSS subKn // [c (n - i)%N * _]mulrC -mulrDl -natrD subnKC //.
have S0 : S 0%N = c 1%N.
  have := cS 0%N; rewrite c0 mulr0 add0r mulr1 => h.
  rewrite /S big_nat1 c0 mulr1.
  by apply: (mulfI (_ : 2%:R != 0 :> R)); rewrite ?pnatr_eq0 // h mulr1.
(* (n + 3) S (n + 1) = 2 c_(n+1) + (4 n + 4) S n *)
have Srec n : n.+3%:R * S n.+1 = 2 * c n.+1 + (4 * n%:R + 4) * S n.
  pose T := \sum_(0 <= i < n.+2) i.+1%:R * (c i * c (n.+1 - i)%N).
  have T1 : 2 * T = n.+3%:R * S n.+1.
    have -> : T = \sum_(0 <= i < n.+2) i%:R * (c i * c (n.+1 - i)%N) + S n.+1.
      rewrite /T /S -big_split /=; apply: eq_bigr => i _.
      by rewrite -natr1 mulrDl mul1r.
    by rewrite mulrDr Sw -mulrDl -natrD addn2.
  have T2 : T = c n.+1 +
      \sum_(0 <= i < n.+1) (4 * i%:R + 2) * (c i * c (n - i)%N).
    rewrite /T big_nat_recl // c0 mul1r mul1r subn0; congr (_ + _).
    by apply: eq_bigr => i _; rewrite subSS mulrA cS -mulrA.
  have T3 : \sum_(0 <= i < n.+1) (4 * i%:R + 2) * (c i * c (n - i)%N) =
      2 * (n%:R * S n) + 2 * S n.
    rewrite -Sw /S !mulr_sumr -big_split; apply: eq_bigr => i _ /=; ring.
  apply: (mulfI (_ : 2%:R != 0 :> R)); first by rewrite pnatr_eq0.
  by rewrite -T1 T2 T3; ring.
elim=> [|n ih]; first exact: S0.
apply: (mulfI (_ : n.+3%:R != 0 :> R)); first by rewrite pnatr_eq0.
have ihS : S n = c n.+1 := ih.
by rewrite -/(S n.+1) Srec ihS -[n.+3]/(n.+1.+2) cS; ring.
Qed.

End catalan.

Section semicircle_catalan.
Context {R : realType}.
Local Notation m k := (\int[semicircle_prob (2 : R)]_x ((x : R) ^+ k)).

(* A sum over r < 2 n + 1, split into even and odd r. *)
Lemma sum_parity (f : nat -> R) n :
  \sum_(r < n.*2.+1) f r =
  \sum_(i < n.+1) f i.*2 + \sum_(i < n) f i.*2.+1.
Proof.
elim: n => [|n ih]; first by rewrite !big_ord1 big_ord0 addr0.
rewrite doubleS [X in X = _]big_ord_recr /= [X in X + _ = _]big_ord_recr /= ih.
rewrite [X in _ = X + _]big_ord_recr [X in _ = _ + X]big_ord_recr /= doubleS.
set A := \sum_(i < n.+1) _; set B := \sum_(i < n) _.
by rewrite -!addrA; congr (_ + _); rewrite addrA addrC addrA.
Qed.

(* The moments of the semicircle law of radius 2 satisfy the recursion of
   the Schwinger-Dyson equation: m_(k+1) = \sum_(r < k) m_r m_(k-1-r). *)
Lemma semicircle_catalan k : m k.+1 = \sum_(r < k) m r * m (k.-1 - r)%N.
Proof.
have r0 : (2 : R) != 0 by rewrite pnatr_eq0.
have modd i : m i.*2.+1 = 0 := semicircle_moment_odd r0 i.
have mo j : odd j -> m j = 0.
  by move=> oj; rewrite -(odd_double_half j) oj add1n modd.
(* the even moments satisfy Segner's recurrence *)
have hS n : \sum_(0 <= i < n.+1) m i.*2 * m (n - i)%N.*2 = m n.+1.*2.
  apply: (segner (c := fun i => m i.*2)); first exact: semicircle_moment0.
  move=> i; rewrite doubleS (semicircle_momentS r0) /=.
  have e1 : (i.*2.+4)%:R = 2 * i.+2%:R :> R.
    by rewrite -[i.*2.+4]/((i.+2).*2) -mul2n natrM.
  have e2 : (i.*2.+1)%:R = 2 * i%:R + 1 :> R.
    by rewrite -addn1 natrD -mul2n natrM.
  have e3 : i.+2%:R = i%:R + 2 :> R by rewrite -addn2 natrD.
  have i2 : i%:R + 2 != 0 :> R by rewrite -e3 pnatr_eq0.
  by rewrite e1 e2 e3; field.
have := odd_double_half k; case: (odd k) => /= kE.
  (* k = 2 n + 1: the odd terms vanish, the even ones give Segner's sum *)
  rewrite -kE add1n /= -[(k./2).*2.+2]/((k./2).+1.*2) -hS big_mkord.
  rewrite (sum_parity (fun r => m r * m (k./2.*2 - r)%N)) /=.
  rewrite [X in _ = _ + X]big1 ?addr0; first by move=> i _; rewrite modd mul0r.
  by apply: eq_bigr => i _; rewrite doubleB.
(* k = 2 n: every term has an odd moment *)
rewrite -kE add0n modd; symmetry; apply: big1 => r _.
have [ro|re] := boolP (odd r); first by rewrite mo // mul0r.
apply/eqP; rewrite mulf_eq0; apply/orP; right; apply/eqP; apply: mo.
have rlt := ltn_ord r.
have h0 : (0 < k./2)%N by rewrite -double_gt0 (leq_ltn_trans (leq0n r) rlt).
rewrite oddB; first by rewrite -ltnS prednK // double_gt0.
have -> : odd (k./2.*2.-1) = true.
  by rewrite -(prednK h0) doubleS /= odd_double.
by rewrite (negbTE re).
Qed.

End semicircle_catalan.

Section goe_moment_limit.
Context {R : realType}.
Local Notation m k := (\int[semicircle_prob (2 : R)]_x ((x : R) ^+ k)).

Lemma cvg_nat_eps (u : nat -> R) (l : R) :
  (forall eps : R, 0 < eps ->
     exists D, forall d, (D <= d)%N -> `|l - u d| <= eps) ->
  u @ \oo --> l.
Proof.
move=> h; apply/cvgrPdist_le => e e0; have [D hD] := h e e0.
by exists D => // d /= Dd; exact: hD.
Qed.

Lemma cvg_sum_seq (I : Type) (s : seq I) (f : I -> nat -> R) (l : I -> R) :
  (forall i, f i @ \oo --> l i) ->
  (fun d => \sum_(i <- s) f i d) @ \oo --> \sum_(i <- s) l i.
Proof.
move=> h; elim: s => [|i s ih].
  by under eq_fun do rewrite big_nil; rewrite big_nil; exact: cvg_cst.
by under eq_fun do rewrite big_cons; rewrite big_cons; exact: cvgD.
Qed.

(* The covariances of the normalized traces tend to 0. *)
Lemma goe_tr_cov_cvg r q :
  (fun d => \int[@gauss R (d * d)]_a (goe_tr r a * goe_tr q a) -
    \int[@gauss R (d * d)]_a goe_tr r a * \int[@gauss R (d * d)]_a goe_tr q a)
  @ \oo --> 0.
Proof.
apply: cvg_nat_eps => e e0.
have [D1 h1] := goe_tr_var_small (R := R) r e0.
have [D2 h2] := goe_tr_var_small (R := R) q e0.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2]; rewrite sub0r normrN.
apply: le_trans (Rintegral_cov_le (@polyfun_goe_tr R d r)
  (@polyfun_goe_tr R d q)) _.
by have := h1 d d1; have := h2 d d2; lra.
Qed.

(* Wigner's moment limit: E tr W^k / d tends to the k-th moment of the
   semicircle law of radius 2. *)
Theorem goe_moment_cvg k :
  (fun d => \int[@gauss R (d * d)]_a goe_tr k a) @ \oo --> m k.
Proof.
have r0 : (2 : R) != 0 by rewrite pnatr_eq0.
elim/ltn_ind: k => k ih.
case: k ih => [|[|k]] ih.
- (* E t_0 = 1 for d >= 1 *)
  rewrite (@semicircle_moment0 R 2); apply: cvg_nat_eps => e e0.
  exists 1%N => d d1; have dn : d%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
  have -> : \int[@gauss R (d * d)]_a goe_tr 0 a = 1.
    under eq_Rintegral do rewrite /goe_tr expr0 mxtrace1 divff //.
    rewrite Rintegral_cst // -[X in fine X]/(@gauss R (d * d) setT).
    by rewrite probability_setT /= mulr1.
  by rewrite subrr normr0 ltW.
- (* E t_1 = 0 by the Schwinger-Dyson equation at k = 0 *)
  have -> : \int[semicircle_prob (2 : R)]_x (x : R) ^+ 1 = 0.
    exact: (semicircle_moment_odd r0 0).
  have E1 d : \int[@gauss R (d * d)]_a goe_tr 1 a = 0.
    under eq_Rintegral do rewrite /goe_tr mulrC.
    rewrite Rintegral_polyfunZ.
      exact: polyfun_trace (mx_polyfun_exp 1 (@mx_polyfun_goe R d)).
    by rewrite (goe_schwinger_dyson d 0) big_ord0 mul0r addr0 !mulr0.
  apply: cvg_nat_eps => e e0; exists 0%N => d _.
  by rewrite E1 subrr normr0 ltW.
(* E t_(k+2) = (k + 1) / d E t_k + \sum_(r <= k) E[t_r t_(k-r)] tends to
   \sum_(r <= k) m_r m_(k-r) = m_(k+2) *)
rewrite (semicircle_catalan k.+1) /=.
have -> : (fun d => \int[@gauss R (d * d)]_a goe_tr k.+2 a) =
    (fun d => k.+1%:R / d%:R * \int[@gauss R (d * d)]_a goe_tr k a +
      \sum_(r < k.+1)
        \int[@gauss R (d * d)]_a (goe_tr r a * goe_tr (k - r) a)).
  by apply/funext => d; exact: goe_tr_sd.
rewrite -[X in _ --> X]add0r; apply: cvgD.
  rewrite -(mul0r (\int[semicircle_prob (2 : R)]_x (x : R) ^+ k)).
  apply: cvgM; last by apply: ih; rewrite ltnS leqW.
  apply: cvg_nat_eps => e e0.
  exists (archimedean.Num.truncn (k.+1%:R / e)).+1 => d dk.
  have hd : k.+1%:R / e < d%:R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  have dR : 0 < d%:R :> R by apply: le_lt_trans hd; rewrite divr_ge0 // ltW.
  rewrite sub0r normrN ger0_norm ?divr_ge0 ?ler0n // ler_pdivrMr //.
  by rewrite mulrC -ler_pdivrMr // ltW.
apply: cvg_sum_seq => r.
have -> : (fun d => \int[@gauss R (d * d)]_a (goe_tr r a * goe_tr (k - r) a)) =
    (fun d => (\int[@gauss R (d * d)]_a (goe_tr r a * goe_tr (k - r) a) -
       \int[@gauss R (d * d)]_a goe_tr r a *
       \int[@gauss R (d * d)]_a goe_tr (k - r) a) +
      \int[@gauss R (d * d)]_a goe_tr r a *
      \int[@gauss R (d * d)]_a goe_tr (k - r) a).
  by apply/funext => d; rewrite subrK.
rewrite -[X in _ --> X]add0r; apply: cvgD; first exact: goe_tr_cov_cvg.
apply: cvgM; apply: ih; first by rewrite ltnS (leq_trans (ltnW (ltn_ord r))).
by rewrite ltnS (leq_trans (leq_subr _ _)).
Qed.

(* The moments of the eigenvalues clipped to [-3, 3] have the same limits. *)
Lemma goe_clip_cvg j :
  (fun d => \int[@gauss R (d * d)]_a goe_clip j a) @ \oo --> m j.
Proof.
(* E (t_j - goe_clip j) tends to 0 since its square is at most
   E (t_j - goe_clip j)^2 *)
have herr : (fun d => \int[@gauss R (d * d)]_a (goe_tr j a - goe_clip j a))
    @ \oo --> 0.
  apply: cvg_nat_eps => e e0.
  have e2 : 0 < e ^+ 2 by rewrite exprn_gt0.
  have [D hD] := goe_clip_err2_small (R := R) j e2.
  exists D => d dD; rewrite sub0r normrN.
  have hs := Rintegral_sqr_le (polyfunB (@polyfun_goe_tr R d j)
    (@polyfun_goe_clip R d j)).
  have h2 := le_trans hs (hD d dD).
  rewrite -real_normK ?num_real // in h2.
  have := normr_ge0 (\int[@gauss R (d * d)]_a (goe_tr j a - goe_clip j a)).
  by nra.
have -> : (fun d => \int[@gauss R (d * d)]_a goe_clip j a) =
    (fun d => \int[@gauss R (d * d)]_a goe_tr j a -
      \int[@gauss R (d * d)]_a (goe_tr j a - goe_clip j a)).
  apply/funext => d; rewrite [X in _ = _ - X]Rintegral_polyfunD.
  - exact: polyfun_goe_tr.
  - under eq_fun do rewrite -mulN1r.
    by apply: polyfunM; [exact: polyfun_cst | exact: polyfun_goe_clip].
  have -> : \int[@gauss R (d * d)]_x - goe_clip j x =
      - \int[@gauss R (d * d)]_x goe_clip j x.
    under eq_Rintegral do rewrite -mulN1r.
    by rewrite Rintegral_polyfunZ ?mulN1r //; exact: polyfun_goe_clip.
  by rewrite opprD addrA subrr add0r opprK.
rewrite -[X in _ --> X]subr0; apply: cvgB => //; exact: goe_moment_cvg.
Qed.

End goe_moment_limit.

Section wigner.
Context {R : realType}.
Local Notation sigma := (semicircle_prob (2 : R)).
Local Notation m k := (\int[sigma]_x ((x : R) ^+ k)).

(* The empirical mean (1 / d) \sum_i f (lambda_i) of f over the spectrum of
   W = goe_mx a. *)
Definition goe_stat d (f : R -> R) (a : 'rV[R]_(d * d)) : R :=
  (\sum_i f (spec (goe_mx a) 0 i)) / d%:R.

Lemma goe_stat_poly_clip d (p : {poly R}) (a : 'rV[R]_(d * d)) :
  goe_stat (fun x => p.[clip 3 x]) a =
  \sum_(j < size p) p`_j * goe_clip j a.
Proof.
rewrite /goe_stat /goe_clip; under eq_bigr do rewrite horner_coef.
rewrite exchange_big mulr_suml; apply: eq_bigr => j _.
by rewrite -mulr_sumr mulrA.
Qed.

Lemma integrable_semicircle_poly (p : {poly R}) :
  sigma.-integrable [set: R] (EFin \o horner p).
Proof.
apply: integrable_semicircle_continuous; first by rewrite pnatr_eq0.
exact: continuous_horner.
Qed.

Lemma semicircle_poly (p : {poly R}) :
  \int[sigma]_x p.[x] = \sum_(j < size p) p`_j * m j.
Proof.
have r0 : (2 : R) != 0 by rewrite pnatr_eq0.
under eq_Rintegral do rewrite horner_coef.
rewrite Rintegral_sum //.
  move=> j; apply: integrable_semicircle_continuous => // x.
  apply: (@continuousM _ _ (cst p`_j) (fun x : R => x ^+ j)).
    exact: cst_continuous.
  exact: exprn_continuous.
apply: eq_bigr => j _; rewrite RintegralZl //.
apply: integrable_semicircle_continuous => //; exact: exprn_continuous.
Qed.

Lemma continuous_clip (c : R) : continuous (clip c).
Proof.
move=> x; apply/cvgrPdist_le => e e0; near=> y.
by apply: le_trans (clip_lipschitz _ _ _) _; near: y; exact: cvgr_dist_le.
Unshelve. all: by end_near. Qed.

(* The semicircle law of radius 2 lives on [-2, 2]: clipping at 3 does not
   change its integrals. *)
Lemma semicircle_clip (h : R -> R) : continuous h ->
  \int[sigma]_x h (clip 3 x) = \int[sigma]_x h x.
Proof.
have r0 : (2 : R) != 0 by rewrite pnatr_eq0.
move=> ch; rewrite (Rintegral_semicircle r0).
  apply: integrable_semicircle_continuous => //.
  by move=> x; apply: continuous_comp; [exact: continuous_clip | exact: ch].
rewrite (Rintegral_semicircle r0); first exact: integrable_semicircle_continuous.
apply: eq_Rintegral => x; rewrite inE /= in_itv /= => /andP[x2 x2'].
rewrite clip_id // ler_norml; rewrite ger0_norm // in x2 x2'; lra.
Qed.

(* For g L-Lipschitz, goe_stat g is (sqrt 2 L / d)-Lipschitz in a. *)
Lemma goe_stat_lipschitz d (g : R -> R) (L : R) : 0 <= L ->
  (forall x y, `|g x - g y| <= L * `|x - y|) ->
  forall a b : 'rV[R]_(d * d),
  `|goe_stat g a - goe_stat g b| <= Num.sqrt 2 * L / d%:R * frobenius (a - b).
Proof.
move=> L0 gL a b; rewrite /goe_stat -mulrBl normrM.
have [dz|dn] := eqVneq (d%:R : R) 0.
  by rewrite dz !invr0 normr0 !mulr0 mul0r.
have d0 : 0 < d%:R :> R by rewrite lt0r dn ler0n.
rewrite [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n //.
have h := spec_stat_lipschitz (goe_mx_symmetric a) (goe_mx_symmetric b) gL.
rewrite ler_pdivrMr //; apply: le_trans h _; rewrite -goe_mxB.
apply: le_trans (_ : L * Num.sqrt d%:R *
    (Num.sqrt (2 / d%:R) * frobenius (a - b)) <= _).
  by apply: ler_wpM2l; [rewrite mulr_ge0 ?sqrtr_ge0 | exact: frobenius_goe_mx].
rewrite le_eqVlt; apply/orP; left; apply/eqP.
have sd : Num.sqrt d%:R != 0 :> R by rewrite gt_eqF // sqrtr_gt0.
by rewrite sqrtrM ?ler0n // sqrtrV ?ler0n //; field.
Qed.

(* A test function that is L-Lipschitz on [-3, 3], composed with clip 3, is
   L-Lipschitz and bounded. *)
Lemma clip_comp_lipschitz (f : R -> R) (L : R) :
  (forall x y : R, -3 <= x <= 3 -> -3 <= y <= 3 -> `|f x - f y| <= L * `|x - y|) ->
  0 <= L /\ forall x y : R, `|f (clip 3 x) - f (clip 3 y)| <= L * `|x - y|.
Proof.
move=> fL.
have c3 (x : R) : -3 <= clip 3 x <= 3.
  by have := @clip_bound R 3 x (ler0n R 3); rewrite ler_norml.
have L0 : 0 <= L.
  have := fL 1 0; rewrite !subr0 normr1 mulr1 => h.
  by apply: le_trans (h _ _); [exact: normr_ge0 | lra | lra].
split => // x y; apply: le_trans (fL _ _ (c3 x) (c3 y)) _.
by apply: ler_wpM2l => //; exact: clip_lipschitz.
Qed.

Lemma polyfun_goe_stat_clip d (f : R -> R) (L : R) :
  (forall x y : R, -3 <= x <= 3 -> -3 <= y <= 3 -> `|f x - f y| <= L * `|x - y|) ->
  polyfun (@goe_stat d (fun x => f (clip 3 x))).
Proof.
move=> fL; have [L0 gL] := clip_comp_lipschitz fL.
split; first exact: lipschitz_frobenius_continuous (goe_stat_lipschitz L0 gL).
exists (2 * (`|f 0| + 3 * L)), 0%N => a; rewrite expr0.
have z3 : -3 <= (0 : R) <= 3 by rewrite oppr_le0 !ler0n.
have gb x : `|f (clip 3 x)| <= `|f 0| + 3 * L.
  have c3 : -3 <= clip 3 x <= 3.
    by have := @clip_bound R 3 x (ler0n R 3); rewrite ler_norml.
  have hb := fL (clip 3 x) 0 c3 z3; rewrite subr0 in hb.
  have hc := @clip_bound R 3 x (ler0n R 3).
  have := ler_normD (f (clip 3 x) - f 0) (f 0); rewrite subrK.
  by have := ler_wpM2l L0 hc; lra.
have B0 : 0 <= `|f 0| + 3 * L by rewrite addr_ge0 // mulr_ge0.
apply: le_trans (_ : `|f 0| + 3 * L <= _).
  rewrite /goe_stat normrM.
  have [dz|dn] := eqVneq (d%:R : R) 0; first by rewrite dz invr0 normr0 mulr0.
  have dR : 0 < d%:R :> R by rewrite lt0r dn ler0n.
  rewrite [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n // ler_pdivrMr //.
  apply: le_trans (ler_norm_sum _ _ _) _.
  apply: le_trans (_ : \sum_(i < d) (`|f 0| + 3 * L) <= _).
    by apply: ler_sum => i _; exact: gb.
  by rewrite sumr_const card_ord mulr_natr.
by move: B0; set B := (`|f 0| + 3 * L); lra.
Qed.

(* The mean of the statistic of f o clip 3 tends to \int f dsigma, for f
   continuous and Lipschitz on [-3, 3]: by a polynomial p within eta of f
   on [-3, 3] (weierstrass_lipschitz), whose statistic is a combination of
   the clipped moments (goe_stat_poly_clip, goe_clip_cvg). *)
Theorem goe_stat_clip_mean_cvg (f : R -> R) (L : R) : continuous f ->
  (forall x y : R, -3 <= x <= 3 -> -3 <= y <= 3 -> `|f x - f y| <= L * `|x - y|) ->
  (fun d => \int[@gauss R (d * d)]_a goe_stat (fun x => f (clip 3 x)) a) @ \oo
    --> \int[sigma]_x f x.
Proof.
move=> cf fL; have [L0 gL] := clip_comp_lipschitz fL.
apply: cvg_nat_eps => e e0.
set eta := e / 3; have eta0 : 0 < eta by rewrite divr_gt0.
have m33 : (-3 : R) < 3 by lra.
have [p hp] := weierstrass_lipschitz m33 eta0 fL.
have hc (x : R) : -3 <= clip 3 x <= 3.
  by have := @clip_bound R 3 x (ler0n R 3); rewrite ler_norml.
have pc j d : polyfun (fun a : 'rV[R]_(d * d) => p`_j * goe_clip j a).
  by apply: polyfunM; [exact: polyfun_cst | exact: polyfun_goe_clip].
(* the mean of the statistic of p o clip 3 tends to \sum_j p_j m_j *)
have hP : (fun d => \int[@gauss R (d * d)]_a goe_stat (fun x => p.[clip 3 x]) a)
    @ \oo --> \sum_(j < size p) p`_j * m j.
  have -> : (fun d => \int[@gauss R (d * d)]_a
        goe_stat (fun x => p.[clip 3 x]) a) =
      (fun d => \sum_(j < size p) p`_j * \int[@gauss R (d * d)]_a goe_clip j a).
    apply/funext => d; under eq_Rintegral do rewrite goe_stat_poly_clip.
    rewrite Rintegral_polyfun_sum; first by move=> j; exact: pc.
    apply: eq_bigr => j _; rewrite Rintegral_polyfunZ //.
    exact: polyfun_goe_clip.
  by apply: cvg_sum_seq => j; apply: cvgM; [exact: cvg_cst | exact: goe_clip_cvg].
have [D _ hD] := (cvgrPdist_le _ _).1 hP eta eta0.
have r0 : (2 : R) != 0 by rewrite pnatr_eq0.
have cfc : continuous (fun x => f (clip 3 x)).
  by move=> x; apply: continuous_comp; [exact: continuous_clip | exact: cf].
have cpc : continuous (fun x => p.[clip 3 x]).
  move=> x; apply: continuous_comp; first exact: continuous_clip.
  exact: continuous_horner.
(* |\int f dsigma - \sum_j p_j m_j| <= eta, both integrals seeing [-3, 3]
   only *)
have hIP : `|\int[sigma]_x f x - \sum_(j < size p) p`_j * m j| <= eta.
  rewrite -semicircle_poly -(semicircle_clip cf).
  rewrite -(semicircle_clip (@continuous_horner R p)).
  rewrite -RintegralB //; [exact: integrable_semicircle_continuous |
    exact: integrable_semicircle_continuous |].
  apply: le_trans (le_normr_Rintegral _ _) _ => //.
    apply: integrable_semicircle_continuous => // x.
    exact: continuousB (cfc x) (cpc x).
  apply: le_trans (_ : \int[sigma]_x eta <= _).
    apply: le_Rintegral => //.
    - apply: integrable_semicircle_continuous => // x.
      apply: (continuous_comp (continuousB (cfc x) (cpc x))).
      exact: norm_continuous.
    - by apply: integrable_semicircle_continuous => //; exact: cst_continuous.
    by move=> x _; rewrite distrC; exact: hp.
  rewrite Rintegral_cst // -[X in fine X]/(sigma setT) probability_setT.
  by rewrite /= mulr1.
exists D => d dD.
have hEp := hD d dD; rewrite /= in hEp.
have ppc : polyfun (@goe_stat d (fun x => p.[clip 3 x])).
  have -> : @goe_stat d (fun x => p.[clip 3 x]) =
      (fun a => \sum_(j < size p) p`_j * goe_clip j a).
    by apply/funext => a; exact: goe_stat_poly_clip.
  by apply: polyfun_sum => j; exact: pc.
have pfc := @polyfun_goe_stat_clip d f L fL.
(* the statistics of p o clip 3 and f o clip 3 differ by at most eta *)
have hdiff (a : 'rV[R]_(d * d)) :
    `|goe_stat (fun x => p.[clip 3 x]) a - goe_stat (fun x => f (clip 3 x)) a|
    <= eta.
  rewrite /goe_stat -mulrBl -sumrB normrM.
  have [dz|dn] := eqVneq (d%:R : R) 0.
    by rewrite dz invr0 normr0 mulr0 ltW.
  have dR : 0 < d%:R :> R by rewrite lt0r dn ler0n.
  rewrite [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n // ler_pdivrMr //.
  apply: le_trans (ler_norm_sum _ _ _) _.
  apply: le_trans (_ : \sum_(i < d) eta <= _).
    by apply: ler_sum => i _; exact: hp.
  by rewrite sumr_const card_ord mulr_natr.
have hEg : `|\int[@gauss R (d * d)]_a goe_stat (fun x => p.[clip 3 x]) a -
    \int[@gauss R (d * d)]_a goe_stat (fun x => f (clip 3 x)) a| <= eta.
  rewrite -RintegralB //; [exact: integrable_polyfun |
    exact: integrable_polyfun |].
  apply: le_trans (le_normr_Rintegral _ _) _ => //.
    exact: integrable_polyfun (polyfunB ppc pfc).
  apply: le_trans (_ : \int[@gauss R (d * d)]_a eta <= _).
    apply: le_Rintegral => //.
    - apply: integrable_polyfun; split.
        move=> a; apply: (continuous_comp ((polyfunB ppc pfc).1 a)).
        exact: norm_continuous.
      have [_ [C [k hC]]] := polyfunB ppc pfc.
      by exists C, k => a; rewrite normr_id; exact: hC.
    - exact: integrable_polyfun (polyfun_cst _).
  rewrite Rintegral_cst // -[X in fine X]/(@gauss R (d * d) setT).
  by rewrite probability_setT /= mulr1.
have := ler_normD (\int[sigma]_x f x - \sum_(j < size p) p`_j * m j)
  (\sum_(j < size p) p`_j * m j -
   \int[@gauss R (d * d)]_a goe_stat (fun x => f (clip 3 x)) a).
rewrite addrA subrK => h1.
have := ler_normD (\sum_(j < size p) p`_j * m j -
   \int[@gauss R (d * d)]_a goe_stat (fun x => p.[clip 3 x]) a)
  (\int[@gauss R (d * d)]_a goe_stat (fun x => p.[clip 3 x]) a -
   \int[@gauss R (d * d)]_a goe_stat (fun x => f (clip 3 x)) a).
rewrite addrA subrK => h2.
apply: le_trans h1 _; apply: le_trans (lerD (lexx _) h2) _.
apply: le_trans (lerD hIP (lerD hEp hEg)) _.
rewrite le_eqVlt; apply/orP; left; apply/eqP; rewrite /eta.
by field.
Qed.

(* Concentration: for g L-Lipschitz, P(|goe_stat g - E goe_stat g| >= u)
   <= eps for every large d (gauss_concentration_abs_tail with the constant
   sqrt 2 (L + 1) / d). *)
Lemma goe_stat_conc (g : R -> R) (L u eps : R) : 0 <= L ->
  (forall x y, `|g x - g y| <= L * `|x - y|) -> 0 < u -> 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
  (@gauss R (d * d) [set a | (u <= `|goe_stat g a -
     \int[@gauss R (d * d)]_b goe_stat g b|)%R] <= eps%:E)%E.
Proof.
move=> L0 gL u0 e0.
set M := L + 1; have M0 : 0 < M by rewrite /M ltr_pwDr.
have gM x y : `|g x - g y| <= M * `|x - y|.
  by apply: le_trans (gL x y) _; apply: ler_wpM2r => //; rewrite lerDl.
exists (archimedean.Num.truncn (8 * M ^+ 2 / (u ^+ 2 * eps))).+1 => d dD.
have d0 : (0 < d)%N by apply: leq_trans dD.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have hd : 8 * M ^+ 2 / (u ^+ 2 * eps) < d%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
have FL := @goe_stat_lipschitz d g M (ltW M0) gM.
apply: le_trans (gauss_concentration_abs_tail FL (ltW u0)) _.
(* 2 exp (- x) <= 2 / x <= eps with x = u^2 d^2 / (4 M^2) *)
rewrite lee_fin.
set x := u ^+ 2 / (2 * (Num.sqrt 2 * M / d%:R) ^+ 2).
have q0 : 0 < 2 * (Num.sqrt 2 * M / d%:R) ^+ 2.
  by rewrite mulr_gt0 // exprn_gt0 // divr_gt0 // mulr_gt0 // sqrtr_gt0.
have x0 : 0 < x by rewrite divr_gt0 // exprn_gt0.
have hx : expR (- x) <= x^-1.
  rewrite expRN lef_pV2 ?posrE ?expR_gt0 //.
  by apply: le_trans (expR_ge1Dx x); rewrite lerDr.
have -> : - u ^+ 2 / (2 * (Num.sqrt 2 * M / d%:R) ^+ 2) = - x.
  by rewrite /x mulNr.
apply: le_trans (_ : 2 * x^-1 <= _); first by apply: ler_wpM2l.
have e2 : (Num.sqrt 2 * M / d%:R) ^+ 2 = 2 * M ^+ 2 / d%:R ^+ 2.
  by rewrite expr_div_n exprMn sqr_sqrtr.
have hd2 : 8 * M ^+ 2 <= d%:R ^+ 2 * (u ^+ 2 * eps).
  have : 8 * M ^+ 2 / (u ^+ 2 * eps) <= d%:R ^+ 2.
    by apply: le_trans (ltW hd) _; rewrite expr2 ler_peMl // ler1n.
  by rewrite ler_pdivrMr // mulr_gt0 // exprn_gt0.
rewrite ler_pdivrMr // /x e2.
have Mn : M != 0 by rewrite gt_eqF.
have dn : d%:R != 0 :> R by rewrite gt_eqF.
have -> : eps * (u ^+ 2 / (2 * (2 * M ^+ 2 / d%:R ^+ 2))) =
    d%:R ^+ 2 * (u ^+ 2 * eps) / (4 * M ^+ 2) by field.
rewrite ler_pdivlMr ?mulr_gt0 ?exprn_gt0 //.
by apply: le_trans hd2; rewrite mulrA -natrM.
Qed.

Lemma continuous_goe_stat d (f : R -> R) : continuous f ->
  continuous (@goe_stat d f).
Proof.
move=> cf; have sl (i : 'I_d) (a b : 'rV[R]_(d * d)) :
    `|spec (goe_mx a) 0 i - spec (goe_mx b) 0 i| <=
    Num.sqrt (2 / d%:R) * frobenius (a - b).
  apply: le_trans (spec_lipschitz _ (goe_mx_symmetric a) (goe_mx_symmetric b)) _.
  by rewrite -goe_mxB; exact: frobenius_goe_mx.
have cs (i : 'I_d) : continuous (fun a : 'rV[R]_(d * d) => f (spec (goe_mx a) 0 i)).
  move=> a; apply: continuous_comp; last exact: cf.
  exact: (@lipschitz_frobenius_continuous R (d * d)
    (fun a => spec (goe_mx a) 0 i) _ (sl i) a).
move=> a; apply: (@continuousM _ _ (fun a => \sum_i f (spec (goe_mx a) 0 i))
  (cst (d%:R^-1))); last exact: cst_continuous.
exact: continuous_sum.
Qed.

(* Wigner's semicircle law: for f continuous and Lipschitz on [-3, 3] and
   eps > 0, the probability that (1 / d) \sum_i f (lambda_i (W)) is farther
   than eps from \int f d(semicircle_prob 2) is at most eps for every large
   d. *)
Theorem wigner (f : R -> R) (L : R) : continuous f ->
  (forall x y : R, -3 <= x <= 3 -> -3 <= y <= 3 -> `|f x - f y| <= L * `|x - y|) ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  (@gauss R (d * d) [set a | (eps <= `|goe_stat f a - \int[sigma]_x f x|)%R]
     <= eps%:E)%E.
Proof.
move=> cf fL eps e0; have [L0 gL] := clip_comp_lipschitz fL.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have s3 : 2 * Num.sqrt 2 < 3 :> R.
  have s2 : Num.sqrt 2 < 3 / 2 :> R.
    rewrite -(@ltr_pXn2r _ 2) ?nnegrE ?sqrtr_ge0 ?divr_ge0 // sqr_sqrtr //.
    by rewrite expr_div_n; lra.
  by lra.
(* P(opnorm W >= 3) <= eps / 2, |E S - \int f| <= eps / 2 and
   P(|S - E S| >= eps / 2) <= eps / 2 for S the statistic of f o clip 3 *)
have [D1 h1] := goe_opnorm_tail_small s3 e2.
have [D2 _ h2] := (cvgrPdist_le _ _).1 (goe_stat_clip_mean_cvg cf fL) _ e2.
have [D3 h3] := goe_stat_conc L0 gL e2 e2.
exists (maxn D1 (maxn D2 D3)) => d; rewrite !geq_max => /andP[d1 /andP[d2 d3]].
have hm := h2 d d2; rewrite /= in hm.
have mclosed (F : 'rV[R]_(d * d) -> R) (c : R) : continuous F ->
    measurable [set a | (c <= F a)%R].
  move=> cF; have := (continuous_measurable_mx cF) measurableT _
    (measurable_itv `[c, +oo[).
  rewrite setTI; congr measurable; apply/seteqP.
  by split => a /=; rewrite in_itv /= andbT.
have mA : measurable [set a : 'rV[R]_(d * d) | (3 <= opnorm (goe_mx a))%R].
  apply: mclosed.
  exact: lipschitz_frobenius_continuous (@goe_opnorm_lipschitz R d).
set E := \int[@gauss R (d * d)]_b goe_stat (fun x => f (clip 3 x)) b.
set I := \int[sigma]_x f x.
have cfc : continuous (fun x => f (clip 3 x)).
  by move=> x; apply: continuous_comp; [exact: continuous_clip | exact: cf].
have mB : measurable [set a : 'rV[R]_(d * d) |
    (eps / 2 <= `|goe_stat (fun x => f (clip 3 x)) a - E|)%R].
  apply: mclosed => a; apply: (continuous_comp (continuousB
    (@continuous_goe_stat d _ cfc a) (@cst_continuous _ _ E a))).
  exact: norm_continuous.
have mT : measurable [set a : 'rV[R]_(d * d) | (eps <= `|goe_stat f a - I|)%R].
  apply: mclosed => a; apply: (continuous_comp (continuousB
    (@continuous_goe_stat d _ cf a) (@cst_continuous _ _ I a))).
  exact: norm_continuous.
(* off the event opnorm W >= 3 the statistics of f and of f o clip 3
   agree *)
have sub : [set a : 'rV[R]_(d * d) | (eps <= `|goe_stat f a - I|)%R] `<=`
    [set a | (3 <= opnorm (goe_mx a))%R] `|`
    [set a | (eps / 2 <= `|goe_stat (fun x => f (clip 3 x)) a - E|)%R].
  move=> a /= h; have [w3|w3] := leP 3 (opnorm (goe_mx a)); [by left | right].
  have eqS : goe_stat f a = goe_stat (fun x => f (clip 3 x)) a.
    rewrite /goe_stat; congr (_ / _); apply: eq_bigr => i _; rewrite clip_id //.
    exact: le_trans (spec_le_opnorm _ (goe_mx_symmetric a)) (ltW w3).
  rewrite eqS in h.
  have := ler_normD (goe_stat (fun x => f (clip 3 x)) a - E) (E - I).
  rewrite addrA subrK => ht.
  rewrite distrC -/E -/I in hm.
  move: h ht hm.
  move: (`|goe_stat (fun x => f (clip 3 x)) a - E|)
    (`|goe_stat (fun x => f (clip 3 x)) a - I|) (`|E - I|).
  by move=> p q r; lra.
apply: le_trans (le_measure _ _ _ sub) _.
- by rewrite inE.
- by rewrite inE; exact: measurableU.
apply: le_trans (measureU2 _ mA mB) _.
apply: le_trans (leeD (h1 d d1) (h3 d d3)) _.
by rewrite -EFinD -splitr.
Qed.

End wigner.
