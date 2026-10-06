(* Density and deletion margins for the hybrid gap.

   For a lower density a > 1/4 and an upper density A >= a, constants are
   chosen in the order delta, t, c, c2, d0 (all from a and A, before d and
   r). For d >= d0, a d^2 <= N <= A d^2, a head dimension r <= sqrt d + 1,
   a bulk index mi with r + mi + 1 <= d (bulk dimension mi + 1), a head
   range dimension q <= r^2 + 1 (this covers r (r + 1) / 2 + 1), and
   k = floor (delta N):
   - k > 0 and k <= N;
   - the deletion entropy is dominated:
     k (1 + ln (N / k)) - (t d)^2 / 2 <= - c2 d^2;
   - every s >= N - k keeps (1 - 1/1216) N rows, and the projected PSD
     threshold of PaperMainProjectedBulkConditional is linear in d:
     c d <= sqrt (s - q - 1) - (sqrt (D_mi / 2) + t d).
   The gamma form takes a = (gamma + 1/4) / 2 and A = gamma + (gamma - 1/4) / 2. *)
From Stdlib Require Import Reals ZArith Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import PaperMainGaussianFeatureCoordinates.
Open Scope R_scope.

(* Elementary logarithm bounds. *)

Lemma paper_main_hybrid_ln_le (x : R) : 0 < x -> ln x <= x - 1.
Proof.
move=> Hx.
have H1 : x <= exp (x - 1).
  have := exp_ineq1_le (x - 1); lra.
case: H1 => H1.
  have H2 := ln_increasing _ _ Hx H1; rewrite ln_exp in H2; lra.
rewrite H1 ln_exp; lra.
Qed.

Lemma paper_main_hybrid_ln_div (x y : R) : 0 < x -> 0 < y -> ln (x / y) = ln x - ln y.
Proof.
move=> Hx Hy.
have Hy' : 0 < / y by apply: Rinv_0_lt_compat.
rewrite /Rdiv (ln_mult _ _ Hx Hy') ln_Rinv //; ring.
Qed.

(* x (1 + ln (N / x)) is nondecreasing on (0, N]. *)

Lemma paper_main_hybrid_entropy_mono (N x y : R) :
  0 < x -> x <= y -> y <= N ->
  x * (1 + ln (N / x)) <= y * (1 + ln (N / y)).
Proof.
move=> Hx Hxy HyN.
have Hy : 0 < y by lra.
have HN : 0 < N by lra.
rewrite !paper_main_hybrid_ln_div //.
have H1 : x * (ln y - ln x) <= y - x.
  have Hq : 0 < y / x by apply: Rdiv_lt_0_compat.
  have := paper_main_hybrid_ln_le _ Hq.
  rewrite paper_main_hybrid_ln_div // => H.
  have := Rmult_le_compat_l x _ _ (Rlt_le _ _ Hx) H.
  have -> : x * (y / x - 1) = y - x by field; lra.
  by [].
have H2 : ln y <= ln N.
  case: HyN => HyN; last by rewrite HyN; lra.
  by apply: Rlt_le; apply: ln_increasing.
nra.
Qed.

(* delta (1 + ln (1 / delta)) <= 2 sqrt delta on (0, 1]. *)

Lemma paper_main_hybrid_entropy_sqrt (delta : R) :
  0 < delta -> delta <= 1 -> delta * (1 + ln (1 / delta)) <= 2 * sqrt delta.
Proof.
move=> Hd Hd1.
set s := sqrt delta.
have Hs : 0 < s by apply: sqrt_lt_R0.
have Hs2 : s * s = delta by apply: sqrt_sqrt; lra.
have Hs1 : s <= 1.
  rewrite /s -sqrt_1; apply: sqrt_le_1_alt; lra.
have Hln : ln (1 / delta) = 2 * ln (1 / s).
  rewrite -Hs2.
  have -> : 1 / (s * s) = (1 / s) * (1 / s) by field; lra.
  rewrite ln_mult; try (apply: Rdiv_lt_0_compat; lra).
  ring.
have Hi : 0 < 1 / s by apply: Rdiv_lt_0_compat; lra.
have H1 := paper_main_hybrid_ln_le _ Hi.
have H2 : s * ln (1 / s) <= 1 - s.
  have := Rmult_le_compat_l s _ _ (Rlt_le _ _ Hs) H1.
  have -> : s * (1 / s - 1) = 1 - s by field; lra.
  by [].
rewrite Hln -Hs2.
nra.
Qed.

(* A floor witness. *)

Lemma paper_main_hybrid_floor (x : R) : 0 <= x -> exists k : nat, INR k <= x < INR k + 1.
Proof.
move=> Hx.
have [Hup1 Hup2] := archimed x.
have Hz : (1 <= up x)%Z.
  have : (0 < up x)%Z by apply: lt_IZR; rewrite /=; lra.
  lia.
exists (Z.to_nat (up x - 1)).
rewrite INR_IZR_INZ Z2Nat.id; first lia.
rewrite minus_IZR; lra.
Qed.

(* Dimension bounds. *)

Lemma paper_main_hybrid_sub_INR (s q : nat) : INR s - INR q <= INR (s - q)%nat.
Proof.
case: (Nat.le_gt_cases q s) => Hqs.
  by rewrite -minusE minus_INR //; lra.
have -> : (s - q)%nat = 0%nat by apply/eqP; rewrite subn_eq0; apply/ssrnat.leP; lia.
have := lt_INR _ _ Hqs; rewrite /=; lra.
Qed.

Lemma paper_main_hybrid_sqrt_dimension (mi d : nat) :
  (mi + 1 <= d)%nat ->
  sqrt (INR (paper_main_symmetric_dimension mi) / 2) <= INR d / 2 + 1 / 4.
Proof.
move/ssrnat.leP => Hd.
rewrite paper_main_symmetric_dimension_formula.
have H2 : (2 * (S mi * S (S mi) / 2) <= S mi * S (S mi))%coq_nat.
  by apply: Nat.Div0.mul_div_le.
have H3 := le_INR _ _ H2.
rewrite !mult_INR !S_INR in H3.
have Hm : INR mi + 1 <= INR d.
  have := le_INR _ _ Hd; rewrite plus_INR /=; lra.
have Hm0 := pos_INR mi.
set D := INR (S mi * S (S mi) / 2) in H3 *.
change (INR 0) with 0 in H3.
have HD : D / 2 <= (INR d / 2 + 1 / 4) * (INR d / 2 + 1 / 4) by nra.
have Hd0 : 0 <= INR d / 2 + 1 / 4 by have := pos_INR d; lra.
apply: Rle_trans (sqrt_le_1_alt _ _ HD) _.
by rewrite sqrt_square //; lra.
Qed.

Lemma paper_main_hybrid_head_dimension (d r q : nat) :
  (1 <= d)%nat -> INR r <= sqrt (INR d) + 1 ->
  INR q <= INR r * INR r + 1 -> INR q <= 3 * INR d + 2.
Proof.
move/ssrnat.leP => Hd Hr Hq.
have Hd1 : 1 <= INR d by have := le_INR _ _ Hd; rewrite /=; lra.
set s := sqrt (INR d) in Hr.
have Hs0 : 0 <= s by apply: sqrt_pos.
have Hs2 : s * s = INR d by apply: sqrt_sqrt; lra.
have Hsd : s <= INR d by nra.
have Hr0 := pos_INR r.
have : INR r * INR r <= (s + 1) * (s + 1) by nra.
nra.
Qed.

(* The density and deletion margin. *)

Theorem paper_main_hybrid_density_margin (a A : R) :
  1 / 4 < a -> a <= A ->
  exists (delta t c c2 : R) (d0 : nat),
    0 < delta /\ delta < 1 / 1216 /\ 0 < t /\ 0 < c /\ 0 < c2 /\
    forall (d N r mi q k : nat),
      (d0 <= d)%nat -> a * INR d ^ 2 <= INR N -> INR N <= A * INR d ^ 2 ->
      INR r <= sqrt (INR d) + 1 -> (r + mi + 1 <= d)%nat ->
      INR q <= INR r * INR r + 1 ->
      INR k <= delta * INR N -> delta * INR N < INR k + 1 ->
      (0 < k)%nat /\ (k <= N)%nat /\
      INR k * (1 + ln (INR N / INR k)) - (t * INR d) ^ 2 / 2 <= - c2 * INR d ^ 2 /\
      forall s : nat, (N - k <= s)%nat ->
        (1 - 1 / 1216) * INR N <= INR s /\
        c * INR d <= sqrt (INR (s - q)%nat - 1) -
          (sqrt (INR (paper_main_symmetric_dimension mi) / 2) + t * INR d).
Proof.
move=> Ha HaA.
have Hapos : 0 < a by lra.
have HAp : 0 < A by lra.
set a1 := (a + 1 / 4) / 2.
have Ha1 : 1 / 4 < a1 by rewrite /a1; lra.
have Ha1a : a1 < a by rewrite /a1; lra.
set delta1 := (a - a1) / a.
have Hd1 : 0 < delta1 by apply: Rdiv_lt_0_compat; lra.
have Hd1a : (1 - delta1) * a = a1 by rewrite /delta1; field; lra.
set sa := sqrt a1.
have Hsa2 : sa * sa = a1 by apply: sqrt_sqrt; lra.
have Hsa0 : 0 <= sa by apply: sqrt_pos.
have Hsa : 1 / 2 < sa by nra.
set rho := (sa + 1 / 2) / 2.
set t := (sa - 1 / 2) / 8.
have Ht : 0 < t by rewrite /t; lra.
have Hrho : rho - 1 / 2 = 4 * t by rewrite /rho /t; field.
have Hrho0 : 0 < rho by rewrite /rho; lra.
have Hrho2 : rho * rho < a1.
  have : rho < sa by rewrite /rho; lra.
  nra.
set delta2 := (t ^ 2 / (8 * A)) ^ 2.
have Hd2 : 0 < delta2.
  rewrite /delta2; apply: pow_lt; apply: Rdiv_lt_0_compat; [apply: pow_lt | ]; lra.
set delta := Rmin delta1 (Rmin (1 / 1217) delta2).
have Hdelta : 0 < delta.
  rewrite /delta; apply: Rmin_glb_lt => //; apply: Rmin_glb_lt => //; lra.
have Hdd1 : delta <= delta1 by apply: Rmin_l.
have Hdd2 : delta <= 1 / 1217 by rewrite /delta; apply: Rle_trans (Rmin_r _ _) _; apply: Rmin_l.
have Hdd3 : delta <= delta2 by rewrite /delta; apply: Rle_trans (Rmin_r _ _) _; apply: Rmin_r.
have Hent : A * (delta * (1 + ln (1 / delta))) <= t ^ 2 / 4.
  have H1 := paper_main_hybrid_entropy_sqrt delta Hdelta ltac:(lra).
  have Hq0 : 0 <= t ^ 2 / (8 * A).
    by apply: Rlt_le; apply: Rdiv_lt_0_compat; [apply: pow_lt | ]; lra.
  have Hsq : sqrt delta <= t ^ 2 / (8 * A).
    apply: Rle_trans (sqrt_le_1_alt _ _ Hdd3) _.
    by rewrite /delta2 sqrt_pow2 //; lra.
  have H2 : A * (2 * sqrt delta) <= t ^ 2 / 4.
    have := Rmult_le_compat_l (2 * A) _ _ (ltac:(lra) : 0 <= 2 * A) Hsq.
    have -> : 2 * A * (t ^ 2 / (8 * A)) = t ^ 2 / 4 by field; lra.
    lra.
  have := Rmult_le_compat_l A _ _ (Rlt_le _ _ HAp) H1.
  lra.
have Hgap : 0 < a1 - rho * rho by lra.
have [d0 Hd0] := INR_unbounded (Rmax 1 (Rmax (1 / (delta * a))
  (Rmax (6 / (a1 - rho * rho)) (1 / (4 * t))))).
exists delta, t, (2 * t), (t ^ 2 / 4), d0.
split; first exact: Hdelta.
split; first lra.
split; first exact: Ht.
split; first lra.
split; first by apply: Rdiv_lt_0_compat; [apply: pow_lt | ]; lra.
move=> d N r mi q k Hd HN1 HN2 Hr Hmi Hq Hk1 Hk2.
have Hdd : INR d0 <= INR d by apply: le_INR; apply/ssrnat.leP.
have HM1 := Rmax_l 1 (Rmax (1 / (delta * a)) (Rmax (6 / (a1 - rho * rho)) (1 / (4 * t)))).
have HM2 : 1 / (delta * a) <= Rmax 1 (Rmax (1 / (delta * a))
    (Rmax (6 / (a1 - rho * rho)) (1 / (4 * t)))).
  by apply: Rle_trans (Rmax_r _ _); apply: Rmax_l.
have HM3 : 6 / (a1 - rho * rho) <= Rmax 1 (Rmax (1 / (delta * a))
    (Rmax (6 / (a1 - rho * rho)) (1 / (4 * t)))).
  by apply: Rle_trans (Rmax_r _ _); apply: Rle_trans (Rmax_r _ _); apply: Rmax_l.
have HM4 : 1 / (4 * t) <= Rmax 1 (Rmax (1 / (delta * a))
    (Rmax (6 / (a1 - rho * rho)) (1 / (4 * t)))).
  by apply: Rle_trans (Rmax_r _ _); apply: Rle_trans (Rmax_r _ _); apply: Rmax_r.
set M := Rmax 1 (Rmax (1 / (delta * a)) (Rmax (6 / (a1 - rho * rho)) (1 / (4 * t))))
  in Hd0 HM1 HM2 HM3 HM4.
have HdR1 : 1 < INR d by lra.
have HdR2 : 1 / (delta * a) < INR d by lra.
have HdR3 : 6 / (a1 - rho * rho) < INR d by lra.
have HdR4 : 1 / (4 * t) < INR d by lra.
have Hda : 0 < delta * a by apply: Rmult_lt_0_compat.
have Hd2d : INR d <= INR d ^ 2 by rewrite /= Rmult_1_r; nra.
have HdN : 1 < delta * INR N.
  have H1 : 1 < delta * a * INR d.
    have := Rmult_lt_compat_l (delta * a) _ _ Hda HdR2.
    have -> : delta * a * (1 / (delta * a)) = 1 by field; lra.
    lra.
  have H2 : delta * a * INR d <= delta * (a * INR d ^ 2) by nra.
  have H3 : delta * (a * INR d ^ 2) <= delta * INR N by apply: Rmult_le_compat_l; lra.
  lra.
have Hk0 : 0 < INR k by lra.
have HN0 : 0 < INR N by nra.
have HkN : INR k <= INR N by nra.
split.
  by apply/ssrnat.ltP; apply: INR_lt; rewrite /=; lra.
split.
  by apply/ssrnat.leP; apply: INR_le.
split.
  have H1 := paper_main_hybrid_entropy_mono (INR N) (INR k) (delta * INR N) Hk0 Hk1
    ltac:(nra).
  have Hquo : INR N / (delta * INR N) = 1 / delta by field; lra.
  rewrite Hquo in H1.
  have Hln : 0 <= ln (1 / delta).
    have : 1 <= 1 / delta.
      apply: (Rmult_le_reg_r delta) => //.
      have -> : 1 / delta * delta = 1 by field; lra.
      lra.
    case=> H.
      by apply: Rlt_le; rewrite -ln_1; apply: ln_increasing; lra.
    by rewrite -H ln_1; lra.
  set h := delta * (1 + ln (1 / delta)) in Hent.
  have Hh0 : 0 <= h by rewrite /h; nra.
  have H2 : delta * INR N * (1 + ln (1 / delta)) = INR N * h by rewrite /h; ring.
  have H3 : INR N * h <= INR d ^ 2 * (t ^ 2 / 4).
    have := Rmult_le_compat_r h _ _ Hh0 HN2.
    have : INR d ^ 2 * (A * h) <= INR d ^ 2 * (t ^ 2 / 4).
      by apply: Rmult_le_compat_l => //; apply: pow_le; lra.
    lra.
  have -> : (t * INR d) ^ 2 = t ^ 2 * INR d ^ 2 by ring.
  lra.
move=> s Hs.
have Hs1 : INR N - INR k <= INR s.
  have H1 := paper_main_hybrid_sub_INR N k.
  have H2 : INR (N - k)%nat <= INR s by apply: le_INR; apply/ssrnat.leP.
  lra.
have HsN : (1 - delta) * INR N <= INR s by lra.
split.
  have : delta * INR N <= 1 / 1216 * INR N by apply: Rmult_le_compat_r; lra.
  lra.
have Hsa1 : a1 * INR d ^ 2 <= INR s.
  have H1 : (1 - delta1) * INR N <= (1 - delta) * INR N by apply: Rmult_le_compat_r; lra.
  have Hd1lt : delta1 < 1 by rewrite /delta1; apply: (Rmult_lt_reg_r a) => //;
    rewrite /Rdiv Rmult_assoc Rinv_l; lra.
  have H2 : (1 - delta1) * (a * INR d ^ 2) <= (1 - delta1) * INR N.
    by apply: Rmult_le_compat_l; lra.
  have H3 : (1 - delta1) * (a * INR d ^ 2) = a1 * INR d ^ 2.
    by rewrite -Hd1a; ring.
  lra.
have Hd0lt : (0 < d)%N.
  by apply/ssrnat.ltP; apply: INR_lt; rewrite /=; lra.
have Hq2 := paper_main_hybrid_head_dimension d r q Hd0lt Hr Hq.
have Hsq := paper_main_hybrid_sub_INR s q.
have HX : (rho * INR d) * (rho * INR d) <= INR (s - q)%nat - 1.
  have H5 : 6 < (a1 - rho * rho) * INR d.
    have := Rmult_lt_compat_l (a1 - rho * rho) _ _ Hgap HdR3.
    have -> : (a1 - rho * rho) * (6 / (a1 - rho * rho)) = 6 by field; lra.
    lra.
  have H6 : (a1 - rho * rho) * INR d * INR d >= 6 * INR d by nra.
  have -> : (rho * INR d) * (rho * INR d) = rho * rho * INR d ^ 2 by ring.
  have : INR d ^ 2 = INR d * INR d by ring.
  nra.
have Hrd : 0 <= rho * INR d by apply: Rmult_le_pos; [lra | exact: pos_INR].
have Hsqrt1 : rho * INR d <= sqrt (INR (s - q)%nat - 1).
  have := sqrt_le_1_alt _ _ HX.
  by rewrite sqrt_square.
have Hmi' : (mi + 1 <= d)%N.
  by apply: (leq_trans _ Hmi); rewrite -addnA leq_addl.
have Hdim := paper_main_hybrid_sqrt_dimension mi d Hmi'.
have H4t : 1 < 4 * t * INR d.
  have := Rmult_lt_compat_l (4 * t) _ _ ltac:(lra) HdR4.
  have -> : 4 * t * (1 / (4 * t)) = 1 by field; lra.
  lra.
have Hrho' : rho = 1 / 2 + 4 * t by lra.
rewrite Hrho' in Hsqrt1.
lra.
Qed.

(* The gamma form: N / d^2 within eta = (gamma - 1/4) / 2 of gamma. *)

Corollary paper_main_hybrid_density_margin_gamma (gamma : R) :
  1 / 4 < gamma ->
  exists (eta delta t c c2 : R) (d0 : nat),
    0 < eta /\ 0 < delta /\ delta < 1 / 1216 /\ 0 < t /\ 0 < c /\ 0 < c2 /\
    forall (d N r mi q k : nat),
      (d0 <= d)%nat -> Rabs (INR N - gamma * INR d ^ 2) <= eta * INR d ^ 2 ->
      INR r <= sqrt (INR d) + 1 -> (r + mi + 1 <= d)%nat ->
      INR q <= INR r * INR r + 1 ->
      INR k <= delta * INR N -> delta * INR N < INR k + 1 ->
      (0 < k)%nat /\ (k <= N)%nat /\
      INR k * (1 + ln (INR N / INR k)) - (t * INR d) ^ 2 / 2 <= - c2 * INR d ^ 2 /\
      forall s : nat, (N - k <= s)%nat ->
        (1 - 1 / 1216) * INR N <= INR s /\
        c * INR d <= sqrt (INR (s - q)%nat - 1) -
          (sqrt (INR (paper_main_symmetric_dimension mi) / 2) + t * INR d).
Proof.
move=> Hg.
set eta := (gamma - 1 / 4) / 2.
have Heta : 0 < eta by rewrite /eta; lra.
have [delta [t [c [c2 [d0 [Hd [Hd' [Ht [Hc [Hc2 Hall]]]]]]]]]] :=
  paper_main_hybrid_density_margin (gamma - eta) (gamma + eta) ltac:(rewrite /eta; lra)
    ltac:(lra).
exists eta, delta, t, c, c2, d0.
do 6 (split; first by []).
move=> d N r mi q k Hdd HN Hr Hmi Hq Hk1 Hk2.
have H1 := Rle_abs (INR N - gamma * INR d ^ 2).
have H2 := Rle_abs (- (INR N - gamma * INR d ^ 2)); rewrite Rabs_Ropp in H2.
apply: (Hall d N r mi q k) => //.
  have : (gamma - eta) * INR d ^ 2 = gamma * INR d ^ 2 - eta * INR d ^ 2 by ring.
  lra.
have : (gamma + eta) * INR d ^ 2 = gamma * INR d ^ 2 + eta * INR d ^ 2 by ring.
lra.
Qed.
