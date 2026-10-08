From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum poly matrix.
From mathcomp Require Import boolp classical_sets reals ereal.
From mathcomp Require Import topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability ring_tactic field_tactic.
From mathcomp Require Import arithmetic_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.probability Require Import semicircle_law.
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
(*   to 0 (goe_tr_cov_cvg, from goe_tr_var_small and Rintegral_cov_le).       *)
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

End goe_moment_limit.
