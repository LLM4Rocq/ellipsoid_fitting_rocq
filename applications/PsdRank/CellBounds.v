From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals exp.
From mathcomp Require Import archimedean arithmetic_tactic ring_tactic.
From GaussianAnalysis.combinatorics Require Import binomial_bounds harmonic.

(**md**************************************************************************)
(* # PSD rank of shifted matching matrices: the estimates of the trace        *)
(*                                                                            *)
(* Item A2b of phase 14 (AGENTS.md, section Phase 14): the arithmetic         *)
(* estimates of the trace of K^2 that the local averaging (item A2,           *)
(* PsdRank/Cells.v) uses, independent of the cells. A Rocq formalization of   *)
(* the credited argument of the trace estimate in the proof of the lemma on   *)
(* local averaging of 'Exponential PSD rank of positively shifted matching    *)
(* matrices' (family 126 of the OpenAI math collection, revision 1581d4cbd),  *)
(* source/sections/local-averaging.tex, lines 155-189, with points 7 to 9 of  *)
(* the audit of the manuscript (reviews/phase13-psd-audit/trace.md). It       *)
(* follows no Lean module of the collection. The TeX writes O_d(...); the     *)
(* constants below are explicit.                                              *)
(*                                                                            *)
(* - central_ratio: C(2n, w)^2 <= 16^(n-h) 4 16^(T+1) (h+1) C(h, g)^4 for h   *)
(*   <= n, 6 T <= h, h <= 2 (g + T) and 2 g <= h + 2 T, the squared form of   *)
(*   the estimate local:central-ratio. With leq_bin_half and central_bin_le,  *)
(*   (3 n + 1) C(2n, w)^2 <= 16^n; with half_bin_ge and bin_near_half, 16^h   *)
(*   <= 4 (h+1)^2 16^(T+1) C(h, g)^4; the factor 3 n + 1 >= h + 1 absorbs one *)
(*   factor h + 1.                                                            *)
(* - pair_sum_bound: the sum of the trace formula local:trace-formula,        *)
(*   indexed by i = g - j, is at most 8 (1 + ln (h + 1)). The route of the    *)
(*   audit replaces the product of the two square-root bounds of the TeX by   *)
(*   the inequality x y <= (x^2 + y^2) / 2 (mul_le_half_sqr). With a_j = C(g, *)
(*   j)^2 / C(2g, 2j) and b_j = C(h-g, j)^2 / C(2(h-g), 2j), each term is at  *)
(*   most a_j b_j, since w >= 2 g and k - w >= 2 (h - g), and the terms with  *)
(*   j > h - g vanish. bin_sqr_ratio gives a_j^2 <= 4 (1/(j+1) + 1/(u-j+1))   *)
(*   for j <= u (bin_ratio_sqr), whose sum over j <= u is 8 H_(u+1)           *)
(*   (bin_ratio_sum); and H_(g+1), H_(h-g+1) <= H_(h+1) <= 1 + ln (h + 1)     *)
(*   (harmonic_mono, harmonic_ln).                                            *)
(* - root_ln_lim: C (1 + ln n) / sqrt n tends to 0, in epsilon form. From ln  *)
(*   y <= y - 1 at y = n^(1/4), ln n <= 4 n^(1/4), so the quotient is at most *)
(*   5 |C| / n^(1/4) for n >= 1.                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma central_ratio (n w h g T : nat) : (h <= n)%N -> (6 * T <= h)%N ->
  (h <= 2 * (g + T))%N -> (2 * g <= h + 2 * T)%N ->
  ('C(2 * n, w) ^ 2 <= 16 ^ (n - h) * 4 * 16 ^ T.+1 * h.+1 * 'C(h, g) ^ 4)%N.
Proof.
move=> hn hT hg gh.
have c1 : ('C(2 * n, w) <= 'C(2 * n, n))%N.
  by rewrite mul2n; have := leq_bin_half n.*2 w; rewrite doubleK.
have c2 := central_bin_le n.
have c3 := half_bin_ge h.
have c4 := bin_near_half hT hg gh.
have e16 j : (16 ^ j = (4 ^ j) ^ 2)%N by rewrite -expnM mulnC expnM.
have e2 j : ((2 ^ j) ^ 4 = 16 ^ j)%N by rewrite -expnM mulnC expnM.
rewrite -(leq_pmul2l (ltn0Sn (3 * n))).
apply: (@leq_trans ((3 * n).+1 * 'C(2 * n, n) ^ 2)%N).
  by rewrite leq_mul2l leq_exp2r // c1 orbT.
apply: (leq_trans c2).
rewrite -{1}(subnK hn) expnD.
have -> : ((3 * n).+1 * (16 ^ (n - h) * 4 * 16 ^ T.+1 * h.+1 * 'C(h, g) ^ 4) =
    16 ^ (n - h) * ((3 * n).+1 * 4 * 16 ^ T.+1 * h.+1 * 'C(h, g) ^ 4))%N.
  by ring.
rewrite leq_mul2l; apply/orP; right; rewrite e16.
apply: (@leq_trans ((2 * h.+1 * 'C(h, h./2) ^ 2) ^ 2)%N).
  by rewrite leq_exp2r.
apply: (@leq_trans ((2 * h.+1 * (2 ^ T.+1 * 'C(h, g)) ^ 2) ^ 2)%N).
  by rewrite leq_exp2r // leq_mul2l leq_exp2r // c4 orbT.
have -> : ((2 * h.+1 * (2 ^ T.+1 * 'C(h, g)) ^ 2) ^ 2 =
    h.+1 * (4 * (2 ^ T.+1) ^ 4 * h.+1 * 'C(h, g) ^ 4))%N by ring.
have -> : ((3 * n).+1 * 4 * 16 ^ T.+1 * h.+1 * 'C(h, g) ^ 4 =
    (3 * n).+1 * (4 * (2 ^ T.+1) ^ 4 * h.+1 * 'C(h, g) ^ 4))%N.
  by rewrite e2; ring.
rewrite leq_mul2r; apply/orP; right; rewrite ltnS.
by apply: leq_trans hn _; rewrite leq_pmull.
Qed.



Section cell_bounds.
Variable R : realType.

Local Notation H n := (\sum_(i < n) (i.+1%:R : R)^-1).

Lemma bin_ratio_sqr (u j : nat) : (j <= u)%N ->
  ('C(u, j)%:R ^+ 2 / 'C(u.*2, j.*2)%:R) ^+ 2 <=
  4 * ((j.+1%:R)^-1 + ((u - j).+1%:R)^-1) :> R.
Proof.
move=> ju.
have hb := bin_sqr_ratio ju; rewrite !mul2n in hb.
set c : R := 'C(u, j)%:R; set d : R := 'C(u.*2, j.*2)%:R.
set a : R := j.+1%:R; set b : R := (u - j).+1%:R.
have d0 : 0 < d by rewrite ltr0n bin_gt0 leq_double.
have a0 : 0 < a by rewrite ltr0n.
have b0 : 0 < b by rewrite ltr0n.
have key : c ^+ 4 * (a * b) <= 4 * (a + b) * d ^+ 2.
  have hab : (u.+1 <= j.+1 + (u - j).+1)%N.
    by rewrite addSn addnS subnKC.
  apply: (@le_trans _ _ (4 * u.+1%:R * d ^+ 2)).
    rewrite /c /a /b /d -!natrX -!natrM ler_nat.
    by rewrite mulnA.
  rewrite ler_wpM2r ?exprn_ge0 ?(ltW d0) // ler_wpM2l //.
  by rewrite /a /b -natrD ler_nat.
have -> : (a^-1 + b^-1) = (a + b) / (a * b).
  by rewrite -[a^-1]div1r -[b^-1]div1r addf_div ?gt_eqF // !mul1r addrC.
rewrite expr_div_n -exprM mulrA ler_pdivrMr ?exprn_gt0 // mulrAC.
by rewrite ler_pdivlMr ?mulr_gt0.
Qed.

Lemma sum_inv_rev (u : nat) :
  \sum_(j < u.+1) ((u - j).+1%:R : R)^-1 = H u.+1.
Proof.
rewrite (reindex_inj rev_ord_inj) /=; apply: eq_bigr => j _.
by rewrite subSS subKn // -ltnS.
Qed.

Lemma bin_ratio_sum (u : nat) :
  \sum_(j < u.+1) ('C(u, j)%:R ^+ 2 / 'C(u.*2, j.*2)%:R) ^+ 2 <=
  8 * H u.+1 :> R.
Proof.
apply: (@le_trans _ _ (\sum_(j < u.+1)
    4 * ((j.+1%:R : R)^-1 + ((u - j).+1%:R)^-1))).
  by apply: ler_sum => j _; apply: bin_ratio_sqr; rewrite -ltnS.
rewrite -mulr_sumr big_split /= sum_inv_rev; lra.
Qed.

Lemma harmonic_mono (m n : nat) : (m <= n)%N -> H m <= H n.
Proof.
move=> mn; rewrite (big_ord_widen n (fun i => (i.+1%:R : R)^-1) mn).
rewrite big_mkcond /=; apply: ler_sum => i _.
by case: ifP => _; rewrite // invr_ge0 ler0n.
Qed.

Lemma sum_tail_le (f : nat -> R) (m u : nat) : (forall j, 0 <= f j) ->
  (forall j, (u < j)%N -> f j = 0) ->
  \sum_(j < m) f j <= \sum_(j < u.+1) f j.
Proof.
move=> f0 fu; case: (leqP m u.+1) => hm.
  rewrite (big_ord_widen u.+1 f hm) big_mkcond /=; apply: ler_sum => i _.
  by case: ifP.
rewrite (bigID (fun j : 'I_m => (j < u.+1)%N)) /=.
have -> : \sum_(j < m | ~~ (j < u.+1)%N) f j = 0.
  by apply: big1 => j; rewrite -leqNgt => /fu.
by rewrite addr0 -(big_ord_widen m f (ltnW hm)).
Qed.

Lemma mul_le_half_sqr (x y : R) : x * y <= (x ^+ 2 + y ^+ 2) / 2.
Proof.
rewrite ler_pdivlMr // -subr_ge0.
have -> : x ^+ 2 + y ^+ 2 - x * y * 2 = (x - y) ^+ 2 by ring.
exact: sqr_ge0.
Qed.


Lemma pair_sum_bound (g h s w k : nat) : (g <= h)%N -> (s + g.*2 = w)%N ->
  ((h - g).*2 <= k - w)%N ->
  \sum_(i < g.+1) ('C(g, i) * 'C(h - g, g - i))%:R ^+ 2 /
    ('C(w, s + i.*2) * 'C(k - w, w - (s + i.*2)))%:R
  <= 8%:R * (1 + ln (h.+1%:R : R)).
Proof.
move=> gh hw hk; set u := (h - g)%N.
pose r (v j : nat) : R := 'C(v, j)%:R ^+ 2 / 'C(v.*2, j.*2)%:R.
have r0 v j : 0 <= r v j by rewrite /r divr_ge0 ?exprn_ge0 ?ler0n.
have w2 : (g.*2 <= w)%N by rewrite -hw leq_addl.
(* One term: with j = g - i, at most r g j r u j <= (r g j^2 + r u j^2) / 2. *)
have hterm (i : 'I_g.+1) :
    ('C(g, i) * 'C(u, g - i))%:R ^+ 2 /
      ('C(w, s + i.*2) * 'C(k - w, w - (s + i.*2)))%:R
    <= (r g (g - i)%N ^+ 2 + r u (g - i)%N ^+ 2) / 2.
  have ig : (i <= g)%N by rewrite -ltnS.
  set j := (g - i)%N.
  have jg : (j <= g)%N := leq_subr i g.
  have e1 : 'C(g, i) = 'C(g, j) by rewrite /j bin_sub.
  have e2 : (w - (s + i.*2) = j.*2)%N by rewrite -{1}hw subnDl /j doubleB.
  have e3 : 'C(w, s + i.*2) = 'C(w, j.*2).
    by rewrite -e2 bin_sub // -hw leq_add2l leq_double.
  rewrite e1 e2 e3; apply: le_trans (mul_le_half_sqr _ _).
  case: (leqP j u) => ju; last first.
    by rewrite (bin_small ju) muln0 expr0n /= mul0r mulr_ge0.
  have D0 : 0 < ('C(g.*2, j.*2) * 'C(u.*2, j.*2))%:R :> R.
    by rewrite ltr0n muln_gt0 !bin_gt0 !leq_double jg ju.
  have Dle : ('C(g.*2, j.*2) * 'C(u.*2, j.*2) <=
      'C(w, j.*2) * 'C(k - w, j.*2))%N.
    by apply: leq_mul; apply: leq_bin2l.
  apply: (@le_trans _ _ (('C(g, j) * 'C(u, j))%:R ^+ 2 /
      ('C(g.*2, j.*2) * 'C(u.*2, j.*2))%:R)).
    rewrite ler_wpM2l ?exprn_ge0 ?ler0n // lef_pV2 ?posrE ?ler_nat //.
    by apply: lt_le_trans D0 _; rewrite ler_nat.
  by rewrite /r !natrM exprMn invfM mulrACA.
apply: (@le_trans _ _ (\sum_(i < g.+1)
  (r g (g - i)%N ^+ 2 + r u (g - i)%N ^+ 2) / 2)).
  by apply: ler_sum => i _; exact: hterm.
rewrite -mulr_suml big_split /=.
have rev (F : nat -> R) :
    \sum_(i < g.+1) F (g - i)%N = \sum_(j < g.+1) F j.
  rewrite (reindex_inj rev_ord_inj) /=; apply: eq_bigr => j _.
  by rewrite subSS subKn // -ltnS.
have revg := rev (fun j => r g j ^+ 2); have revu := rev (fun j => r u j ^+ 2).
simpl in revg, revu; rewrite revg revu.
have sg : \sum_(j < g.+1) r g j ^+ 2 <= 8 * H g.+1 := bin_ratio_sum g.
have su : \sum_(j < g.+1) r u j ^+ 2 <= 8 * H u.+1.
  apply: le_trans (bin_ratio_sum u).
  apply: (@sum_tail_le (fun j => r u j ^+ 2)) => [j|j uj]; first exact: sqr_ge0.
  by rewrite /r bin_small // expr0n /= mul0r expr0n.
have hg : H g.+1 <= H h.+1 by apply: harmonic_mono.
have hu : H u.+1 <= H h.+1 by apply: harmonic_mono; rewrite ltnS leq_subr.
have hl := @harmonic_ln R h.+1 (ltn0Sn h).
move: sg su hg hu hl; rewrite (_ : (8%:R : R) = 8) //; lra.
Qed.

Lemma root_ln_lim (C e : R) : 0 < e -> exists n1 : nat, forall n : nat,
  (n1 <= n)%N -> C * (1 + ln (n%:R : R)) / Num.sqrt (n%:R) <= e.
Proof.
move=> e0; pose M : R := 5 * `|C| / e.
have M0 : 0 <= M by rewrite /M divr_ge0 ?mulr_ge0 ?normr_ge0 // ltW.
exists (Num.truncn (M ^+ 4)).+1 => n hn.
have n1 : 1 <= (n%:R : R) by rewrite ler1n; apply: leq_trans hn.
have n0 : 0 <= (n%:R : R) by apply: le_trans n1.
set q := Num.sqrt (Num.sqrt (n%:R : R)).
have s1 : 1 <= Num.sqrt (n%:R : R) by rewrite -[X in X <= _]sqrtr1 ler_sqrt.
have q1 : 1 <= q.
  by rewrite /q -[X in X <= _]sqrtr1 ler_sqrt // (le_trans ler01 s1).
have q0 : 0 < q by apply: lt_le_trans q1.
have q2 : q ^+ 2 = Num.sqrt (n%:R : R).
  by rewrite /q sqr_sqrtr // sqrtr_ge0.
have q4 : q ^+ 4 = n%:R.
  by rewrite (_ : 4 = 2 * 2)%N // exprM q2 sqr_sqrtr.
(* ln n = 4 ln q <= 4 (q - 1) *)
have lnq : ln (n%:R : R) <= 4 * q.
  have h : ln (1 + (q - 1)) <= q - 1 by apply: le_ln1Dx; lra.
  rewrite addrC subrK in h.
  rewrite -q4 lnXn // -mulr_natr; move: h.
  by rewrite (_ : (4%:R : R) = 4) //; lra.
have L0 : 0 <= 1 + ln (n%:R : R) by rewrite addr_ge0 ?ln_ge0.
have L5 : 1 + ln (n%:R : R) <= 5 * q by lra.
have Mq : M <= q.
  rewrite -(ler_pXn2r (isT : (0 < 4)%N)) ?nnegrE ?(ltW q0) // q4.
  apply: le_trans (ltW (truncnS_gt _)) _.
  by rewrite ler_nat.
apply: (@le_trans _ _ (`|C| * (1 + ln (n%:R : R)) / Num.sqrt (n%:R))).
  rewrite -!mulrA ler_wpM2r // ?ler_norm //.
  by rewrite divr_ge0 ?sqrtr_ge0.
rewrite -q2.
apply: (@le_trans _ _ (`|C| * (5 * q) / q ^+ 2)).
  rewrite ler_wpM2r ?invr_ge0 ?exprn_ge0 ?(ltW q0) //.
  by rewrite ler_wpM2l ?normr_ge0.
have E : `|C| * (5 * q) / q ^+ 2 = M * e / q.
  rewrite /M divfK ?gt_eqF // expr2 mulrA [`|C| * 5]mulrC invfM mulrA.
  by rewrite mulfK // gt_eqF.
rewrite E ler_pdivrMr // [e * q]mulrC ler_pM2r //.
Qed.

End cell_bounds.
