(* The fixed-density rate of the NB trace events (G16, lower edge, part 9).
   - pmnbr_fact: k^k <= 3^k k! (by expR and exp 1 <= 3); pmnbr_bin:
     'C(n, k) k^k <= (3 n)^k; pmnbr_F_le: F(p (m+1), p) <= (6 (m+2))^p for
     the coefficient F of PaperMainSquarefreeWalkNBMarks.
   - pmnbr_pow_le3: (1 + x)^n <= 3 when 0 <= x and n x <= 1.
   - pmnbr_term: one term of the bound of pmnbv_union_le, divided by t^p,
     is at most 3 (Lmax+1)^2 (3 N + N (1 + 13 c0^2)^2 + (4 Lmax)^4) / 2^p,
     when F 2^p <= t^p, L delta <= 1 and L theta (1 + K_L) <= 1.
   - The choices, with K = 2^(k+1): the exponent p = 2 L(d) (pmnbr_p, with
     L(d) = pmel_L d), t = 12 (K+1) (pmnbr_t), lam = (N 'C(d, 2))^(1/4)
     (pmnbr_lam), c0 = 4 c1, Lmax = p K and theta = 1 / (C Lmax^4)
     (pmnbr_theta, C = pmnbr_C c1).
   - pmnbr_rate: if 0 < N, 4 N <= d^2, d^2 <= c1 N, 2^9600 <= d and
     pmnbr_A c1 k L(d)^1178 <= d, the union of the NB trace events for
     T 1, ..., T K at exponent p and threshold t has probability at most
     1/d. The last premise is the only growth input (pmnbr_growth splits
     it into the four polynomial bounds used).
   No probability premise beyond those of PaperMainSquarefreeWalkNBEvent. *)
From Stdlib Require Import Reals Lia Rpower.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import topology normedtype derive realfun sequences exp Rstruct_topology.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions
  GaussianProbabilityProductDefinitions PaperMainDefinitions PaperMainSquarefreeEdgeUpperLimit
  PaperMainSquarefreeEdgeLower PaperMainSquarefreeWalkNB PaperMainSquarefreeWalkNBMarks
  PaperMainSquarefreeWalkNBMoment PaperMainSquarefreeWalkNBEvent.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope nat_scope.

(* 1. Factorial and binomial bounds. *)
Lemma pmnbr_exp_mono a b k : a <= b -> a ^ k <= b ^ k.
Proof.
by case: k => [|k] H; [rewrite !expn0 | rewrite leq_exp2r].
Qed.

Lemma pmnbr_ffact n k : n ^_ k <= n ^ k.
Proof.
elim: k n => [|k IH] n; first by rewrite ffactn0 expn0.
rewrite ffactnS expnS leq_mul2l; apply/orP; right.
apply: leq_trans (IH n.-1) _; exact: pmnbr_exp_mono (leq_pred n).
Qed.

Section Binomial.
Local Open Scope ring_scope.

Lemma pmnbr_expR1 : expR 1 <= 3%:R :> R.
Proof.
have H := exp_le_3; move/RleP: H; rewrite RexpE R1E IZRposE INRE; exact.
Qed.

Lemma pmnbr_fact k : (k ^ k <= 3 ^ k * k`!)%N.
Proof.
case: k => [//|k].
rewrite -(@ler_nat R) natrM !natrX.
have Hx : (0 : R) <= k.+1%:R by exact: ler0n.
have H := @expR_ge1Dxn R k.+1%:R k Hx.
have Hf : (0 : R) < k.+1`!%:R by rewrite ltr0n fact_gt0.
(* (k+1)^(k+1) / (k+1)! <= expR (k+1) = (expR 1)^(k+1) <= 3^(k+1). *)
have H1 : k.+1%:R ^+ k.+1 / k.+1`!%:R <= 3%:R ^+ k.+1 :> R.
  apply: le_trans (_ : expR k.+1%:R <= _).
    by apply: le_trans H; rewrite lerDr ler01.
  rewrite -[k.+1%:R]mulr1 expRM_natl; apply: lerXn2r; rewrite ?nnegrE ?expR_ge0 //.
  exact: pmnbr_expR1.
by rewrite -ler_pdivrMr.
Qed.

Lemma pmnbr_pow_le3 (x : R) n : 0 <= x -> n%:R * x <= 1 -> (1 + x) ^+ n <= 3%:R.
Proof.
move=> Hx Hn.
apply: (@le_trans _ _ (expR x ^+ n)).
  apply: lerXn2r; rewrite ?nnegrE ?expR_ge0 //; last exact: expR_ge1Dx.
  by apply: addr_ge0; [exact: ler01 | exact: Hx].
rewrite -expRM_natl; apply: le_trans pmnbr_expR1; rewrite ler_expR; exact: Hn.
Qed.

End Binomial.

Lemma pmnbr_bin n k : 'C(n, k) * k ^ k <= (3 * n) ^ k.
Proof.
apply: (@leq_trans ('C(n, k) * (3 ^ k * k`!))); first by rewrite leq_mul2l pmnbr_fact orbT.
rewrite mulnCA bin_ffact expnMn leq_mul2l; apply/orP; right; exact: pmnbr_ffact.
Qed.

Lemma pmnbr_F_le p m : pmnm_F (p * m.+1) p <= (6 * m.+2) ^ p.
Proof.
rewrite /pmnm_F.
have E : (p * m.+1 + p = p * m.+2)%N by rewrite [p * m.+2]mulnS addnC.
have E2 : (6 * m.+2 = 2 * (3 * m.+2))%N by rewrite mulnA.
rewrite E E2 expnMn leq_mul2l; apply/orP; right.
case: p {E} => [|p]; first by rewrite bin0 expn0.
have H := pmnbr_bin (p.+1 * m.+2) p.+1.
have E3 : (3 * (p.+1 * m.+2) = 3 * m.+2 * p.+1)%N by rewrite mulnCA mulnC.
by rewrite E3 expnMn leq_pmul2r ?expn_gt0 // in H.
Qed.

(* 2. One term of the union bound. *)
Section Term.
Local Open Scope ring_scope.

Lemma pmnbr_term (lam theta c0 t : R) (N d L p Lx : nat) :
  0 < lam -> 0 <= theta -> 0 <= c0 -> 0 < t -> (L <= Lx)%N ->
  (pmnm_F L p)%:R * 2%:R ^+ p <= t ^+ p ->
  L%:R * ((N * (2 * L * d * (4 * L) ^ 4))%:R * lam^-1 ^+ 4) <= 1 ->
  L%:R * (theta * (1 + ((2 * (L.-1 + 4))%:R + (L.-1 + 2)%:R * (c0 + (2 * L)%:R) ^+ 2))) <= 1 ->
  (pmnm_F L p)%:R * (L.+1 ^ 2)%:R * (1 + (N * (2 * L * d * (4 * L) ^ 4))%:R * lam^-1 ^+ 4) ^+ L *
  (N%:R * (1 + theta * (1 + ((2 * (L.-1 + 4))%:R +
    (L.-1 + 2)%:R * (c0 + (2 * L)%:R) ^+ 2))) ^+ L +
   N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2 + ((4 * L) ^ 4)%:R) / t ^+ p <=
  3%:R * (Lx.+1 ^ 2)%:R *
  (3%:R * N%:R + N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2 + ((4 * Lx) ^ 4)%:R) / 2%:R ^+ p.
Proof.
move=> Hl Hth Hc0 Ht HL HF Hd Hm.
set F := (pmnm_F L p)%:R.
set A := (L.+1 ^ 2)%:R.
set x := (N * (2 * L * d * (4 * L) ^ 4))%:R * lam^-1 ^+ 4.
set y := theta * (1 + ((2 * (L.-1 + 4))%:R + (L.-1 + 2)%:R * (c0 + (2 * L)%:R) ^+ 2)).
set c := N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2.
have Hx : 0 <= x by apply: mulr_ge0; [exact: ler0n | apply: exprn_ge0; rewrite invr_ge0 ltW].
have Hy : 0 <= y.
  apply: mulr_ge0 => //; apply: addr_ge0; first exact: ler01.
  apply: addr_ge0; first exact: ler0n.
  by apply: mulr_ge0; [exact: ler0n | apply: exprn_ge0; apply: addr_ge0; [exact: Hc0 | exact: ler0n]].
have Hc : 0 <= c by apply: mulr_ge0; [exact: ler0n | apply: exprn_ge0; apply: addr_ge0;
  [exact: ler01 | apply: mulr_ge0; [exact: ler0n | exact: exprn_ge0]]].
(* (1 + delta)^L <= 3 and mu^L <= 3. *)
have HD : (1 + x) ^+ L <= 3%:R := pmnbr_pow_le3 x L Hx Hd.
have HM : (1 + y) ^+ L <= 3%:R := pmnbr_pow_le3 y L Hy Hm.
have HT : N%:R * (1 + y) ^+ L + c + ((4 * L) ^ 4)%:R <= 3%:R * N%:R + c + ((4 * Lx) ^ 4)%:R.
  apply: lerD; first apply: lerD => //.
    by rewrite mulrC; apply: ler_wpM2r; [exact: ler0n | exact: HM].
  by rewrite ler_nat; apply: pmnbr_exp_mono; rewrite leq_mul2l HL orbT.
have HA : A <= (Lx.+1 ^ 2)%:R by rewrite ler_nat; apply: pmnbr_exp_mono.
have Htp : 0 < t ^+ p by exact: exprn_gt0.
have H2p : 0 < 2%:R ^+ p :> R by apply: exprn_gt0; rewrite ltr0n.
have HFt : F / t ^+ p <= (2%:R ^+ p)^-1.
  by rewrite ler_pdivrMr // -[X in _ <= X]mulrC ler_pdivlMr // mulrC.
set D := (1 + x) ^+ L.
set Th := N%:R * (1 + y) ^+ L + c + ((4 * L) ^ 4)%:R.
set Th' := 3%:R * N%:R + c + ((4 * Lx) ^ 4)%:R.
set A' := (Lx.+1 ^ 2)%:R.
have E1 : F * A * D * Th / t ^+ p = (F / t ^+ p) * (A * (D * Th)) by ring.
have E2 : 3%:R * A' * Th' / 2%:R ^+ p = (2%:R ^+ p)^-1 * (A' * (3%:R * Th')) by ring.
rewrite E1 E2.
have HD0 : 0 <= D by apply: exprn_ge0; apply: addr_ge0; [exact: ler01 | exact: Hx].
have HTh0 : 0 <= Th.
  apply: addr_ge0; last exact: ler0n.
  apply: addr_ge0 => //; apply: mulr_ge0; first exact: ler0n.
  by apply: exprn_ge0; apply: addr_ge0; [exact: ler01 | exact: Hy].
apply: ler_pM.
- by apply: divr_ge0; [exact: ler0n | exact: ltW].
- by apply: mulr_ge0; [exact: ler0n | exact: mulr_ge0].
- exact: HFt.
- apply: ler_pM; [exact: ler0n | exact: mulr_ge0 | exact: HA |].
  by apply: ler_pM.
Qed.

End Term.

(* 3. Growth: one premise A0 Lx^1178 <= d gives the four polynomial bounds
   used below. The constants stay abstract in the proof. *)
Lemma pmnbr_growth (a1 a2 a3 a4 Lx d : nat) : 0 < Lx ->
  (a1 + a2 + a3 + a4) * Lx ^ 1178 <= d ->
  [/\ a1 * Lx ^ 1178 <= d, a2 * Lx ^ 2 <= d, a3 * Lx ^ 6 <= d & a4 * Lx ^ 7 <= d].
Proof.
move=> HL H.
have HE j : (j <= 1178)%N -> Lx ^ j <= Lx ^ 1178 by move=> Hj; exact: leq_pexp2l.
have Hle a j : a <= a1 + a2 + a3 + a4 -> (j <= 1178)%N -> a * Lx ^ j <= d.
  by move=> Ha Hj; apply: leq_trans H; exact: leq_mul Ha (HE j Hj).
split.
- apply: Hle => //; apply: leq_trans (leq_addr a4 _); apply: leq_trans (leq_addr a3 _).
  exact: leq_addr.
- apply: Hle => //; apply: leq_trans (leq_addr a4 _); apply: leq_trans (leq_addr a3 _).
  exact: leq_addl.
- by apply: Hle => //; apply: leq_trans (leq_addr a4 _); exact: leq_addl.
- by apply: Hle => //; exact: leq_addl.
Qed.

(* 4. The parameters at fixed density, with K = 2^(k+1). *)
Definition pmnbr_p (d : nat) : nat := 2 ^ (pmel_k d).+4.
Definition pmnbr_C (c1 : nat) : nat := 9 + 2 * (4 * c1 + 2) ^ 2.
Definition pmnbr_A0 (c1 : nat) : nat :=
  64 * c1 * pmnbr_C c1 ^ 294 + 16 * 4 ^ 45 + 2048 + 12 * (259 + (1 + 13 * (4 * c1) ^ 2) ^ 2).
Definition pmnbr_A (c1 k : nat) : nat := pmnbr_A0 c1 * (2 * 2 ^ k.+1) ^ 1178.

Section Rate.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition pmnbr_t (k : nat) : R := (12 * (2 ^ k.+1).+1)%:R.
Definition pmnbr_lam (N d : nat) : R := Num.sqrt (Num.sqrt (N * 'C(d, 2))%:R).
Definition pmnbr_theta (c1 Lx : nat) : R := ((pmnbr_C c1 * Lx ^ 4)%:R)^-1.

Lemma pmnbr_bin2 d : (2 <= d)%N -> (d ^ 2 <= 4 * 'C(d, 2))%N.
Proof.
case: d => [|[|e]] // _.
have H := bin_ffact e.+2 2.
rewrite ffactnS ffactn1 /= in H.
rewrite -mulnn; move: H; set c := 'C(e.+2, 2) => H.
have H' : (c * 2 = e.+2 * e.+1)%coq_nat by rewrite -!multE in H.
apply/ssrnat.leP; rewrite -!multE; nia.
Qed.

Lemma pmnbr_lam_facts N d : (0 < N)%N -> (2 <= d)%N ->
  [/\ 0 < pmnbr_lam N d, pmnbr_lam N d ^+ 4 = (N * 'C(d, 2))%:R &
      pmnbr_lam N d ^+ 2 = Num.sqrt (N * 'C(d, 2))%:R].
Proof.
move=> HN Hd.
rewrite /pmnbr_lam; set X := (N * 'C(d, 2))%:R.
have HX : 0 < X by rewrite ltr0n muln_gt0 HN bin_gt0.
have H2 : Num.sqrt (Num.sqrt X) ^+ 2 = Num.sqrt X by rewrite sqr_sqrtr // sqrtr_ge0.
split.
- by rewrite !sqrtr_gt0.
- have -> : (4 = 2 * 2)%N by [].
  by rewrite exprM H2 sqr_sqrtr // ltW.
- exact: H2.
Qed.

Theorem pmnbr_rate (N d c1 k : nat) : (0 < N)%N -> (4 * N <= d ^ 2)%N ->
  (d ^ 2 <= c1 * N)%N -> (2 ^ 9600 <= d)%N -> (pmnbr_A c1 k * pmel_L d ^ 1178 <= d)%N ->
  (paper_main_probability N d (pmnbv_union N d ((pmnbr_lam N d)^-1 ^+ 2)%R (2 ^ k.+1)
     (pmnbr_p d) (pmnbr_t k)) <= (1 / d%:R)%:E)%E.
Proof.
move=> HN H4N Hc1 Hd HA.
have [F1 F2 F3] := pmel_L_facts d Hd.
have Hd0 : (0 < d)%N by apply: leq_trans Hd; rewrite expn_gt0.
have Hd2 : (2 <= d)%N by apply: leq_trans Hd; exact: (@leq_pexp2l 2 1 9600).
have HNd : (N <= d ^ 2)%N by apply: leq_trans H4N; exact: leq_pmull.
have Hc10 : (0 < c1)%N.
  rewrite lt0n; apply/eqP => Hc; move: Hc1; rewrite Hc mul0n leqn0 expn_eq0 => /andP [/eqP Hd00 _].
  by move: Hd0; rewrite Hd00.
(* The lengths: p = 2 L(d), Lmax = p K. *)
set K := (2 ^ k.+1)%N.
set P := pmel_L d.
have EP : pmnbr_p d = (2 * P)%N by rewrite /pmnbr_p /P /pmel_L expnS.
set p := pmnbr_p d in EP *.
have HK : (0 < K)%N by rewrite expn_gt0.
have HP : (0 < P)%N by apply: leq_trans F1.
have Hp : (0 < p)%N by rewrite EP muln_gt0 HP.
set Lx := (p * K)%N.
have HLx : (0 < Lx)%N by rewrite muln_gt0 Hp HK.
have E : (pmnbr_A0 c1 * Lx ^ 1178 = pmnbr_A c1 k * P ^ 1178)%N.
  by rewrite /pmnbr_A -mulnA -expnMn /Lx EP mulnAC.
have HA' : (pmnbr_A0 c1 * Lx ^ 1178 <= d)%N by rewrite E.
have [G1 G2 G3 G4] := pmnbr_growth (64 * c1 * pmnbr_C c1 ^ 294) (16 * 4 ^ 45) 2048
  (12 * (259 + (1 + 13 * (4 * c1) ^ 2) ^ 2)) Lx d HLx HA'.
(* lam = (N 'C(d, 2))^(1/4) and the premises of pmnct_moment_le. *)
have [Hl Hl4 Hl2] := pmnbr_lam_facts N d HN Hd2.
set lam := pmnbr_lam N d in Hl Hl4 Hl2 *.
have HNC : (N <= 'C(d, 2))%N.
  rewrite -(leq_pmul2l (isT : (0 < 4)%N)); exact: leq_trans H4N (pmnbr_bin2 d Hd2).
have E4 : (2 * 2 = 4)%N by [].
have HN2 : N%:R <= lam ^+ 2.
  have H : (N%:R : R) ^+ 2 <= (lam ^+ 2) ^+ 2.
    rewrite -exprM E4 Hl4 -natrX ler_nat.
    by rewrite -mulnn leq_mul2l HNC orbT.
  by move: H; rewrite ler_pXn2r // nnegrE ?ler0n // exprn_ge0 // ltW.
have Hdl : d%:R <= (4 * c1)%:R * lam.
  have H : (d%:R : R) ^+ 4 <= ((4 * c1)%:R * lam) ^+ 4.
    rewrite exprMn Hl4 -!natrX -natrM ler_nat.
    have Hd4 : (d ^ 4 = d ^ 2 * d ^ 2)%N by rewrite -expnD.
    rewrite Hd4; apply: (@leq_trans (c1 * N * (4 * 'C(d, 2)))).
      exact: leq_mul Hc1 (pmnbr_bin2 d Hd2).
    have -> : (c1 * N * (4 * 'C(d, 2)) = (4 * c1) * (N * 'C(d, 2)))%N.
      by rewrite mulnCA -!mulnA.
    rewrite leq_mul2r; apply/orP; right.
    by rewrite -{1}(expn1 (4 * c1)) leq_pexp2l // muln_gt0 Hc10.
  move: H; rewrite ler_pXn2r // nnegrE ?ler0n //.
  by apply: mulr_ge0; [exact: ler0n | exact: ltW].
(* theta = 1 / (C Lmax^4). *)
set C := pmnbr_C c1.
have HC : (0 < C)%N by rewrite /C /pmnbr_C addn_gt0.
set Z := (C * Lx ^ 4)%N.
have HZ : (0 < Z)%N by rewrite muln_gt0 HC expn_gt0 HLx.
set th := pmnbr_theta c1 Lx.
have Eth : th = (Z%:R)^-1 by [].
have Hth : 0 < th <= 1.
  rewrite Eth; apply/andP; split; first by rewrite invr_gt0 ltr0n.
  by rewrite invf_le1 ?ltr0n // ler1n.
set q := p.-1.
have Hq : q.+1 = p by rewrite /q prednK.
set j := (pmel_k d).+3.
have Hqj : q.+1 = (2 ^ j.+1)%N by rewrite Hq.
have Hc0 : (0 : R) < (4 * c1)%:R by rewrite ltr0n muln_gt0 Hc10.
have HB : ((4 * (q.+1 * K)) ^ 2)%:R <= lam * th ^+ 294.
  rewrite Hq -/Lx Eth exprVn ler_pdivlMr ?exprn_gt0 ?ltr0n //.
  rewrite -natrX -natrM -(ler_pM2l Hc0); apply: le_trans Hdl; rewrite -natrM ler_nat.
  apply: leq_trans G1; apply: eq_leq; rewrite /Z /C; ring.
have HB45 : ((4 * (q.+1 * K)) ^ 2 * 4 ^ 45 <= d)%N.
  rewrite Hq -/Lx; apply: leq_trans G2; apply: eq_leq; rewrite expnMn mulnAC; ring.
have Htp : 0 < pmnbr_t k by rewrite /pmnbr_t ltr0n muln_gt0.
have HNM : (N * 'C(d, 2))%:R <= lam ^+ 4 by rewrite Hl4.
(* The union bound of PaperMainSquarefreeWalkNBEvent. *)
have H := pmnbv_union_le lam th (4 * c1)%:R N d K q j (pmnbr_t k) Hqj HN Hd0 HNd Hl Hth
  (ltW Hc0) HNM HN2 Hdl HB HB45 Htp.
rewrite Hq in H; apply: le_trans H _; rewrite lee_fin.
(* Each term is at most Y 2^-p. *)
set c0 := (4 * c1)%:R : R.
set Y := 3%:R * (Lx.+1 ^ 2)%:R * (3%:R * N%:R + N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2 +
  ((4 * Lx) ^ 4)%:R) : R.
have EC : C = (9 + 2 * (4 * c1 + 2) ^ 2)%N by [].
have Hnat : forall l, (1 + (2 * (l + 4) + (l + 2) * (4 * c1 + 2 * l.+1) ^ 2) <= C * l.+1 ^ 3)%N.
  move=> l.
  have H1 : (1 + 2 * (l + 4) <= 9 * l.+1 ^ 3)%N.
    apply: (@leq_trans (9 * l.+1)).
      have -> : (9 * l.+1 = (1 + 2 * (l + 4)) + 7 * l)%N by ring.
      exact: leq_addr.
    by rewrite leq_mul2l -{1}(expn1 l.+1) leq_pexp2l ?orbT.
  have H2 : ((l + 2) * (4 * c1 + 2 * l.+1) ^ 2 <= 2 * (4 * c1 + 2) ^ 2 * l.+1 ^ 3)%N.
    apply: (@leq_trans (2 * l.+1 * ((4 * c1 + 2) * l.+1) ^ 2)).
      apply: leq_mul.
        have -> : (2 * l.+1 = (l + 2) + l)%N by ring.
        exact: leq_addr.
      apply: pmnbr_exp_mono.
      have -> : ((4 * c1 + 2) * l.+1 = (4 * c1 + 2 * l.+1) + 4 * c1 * l)%N by ring.
      exact: leq_addr.
    by apply: eq_leq; ring.
  rewrite addnA; apply: leq_trans (leq_add H1 H2) _.
  by rewrite EC mulnDl.
have Hterm m : (m < K)%N -> pmnbv_bound lam th c0 N d m q / pmnbr_t k ^+ p <= Y / 2%:R ^+ p.
  move=> Hm; rewrite -Hq /pmnbv_bound /Y.
  set L := (q.+1 * m.+1)%N.
  have HL1 : (0 < L)%N by rewrite muln_gt0.
  have HLL : (L <= Lx)%N by rewrite /L /Lx -Hq leq_mul2l Hm orbT.
  apply: pmnbr_term => //.
  - by case/andP: Hth => /ltW.
  - (* F(L, p) 2^p <= t^p. *)
    rewrite /pmnbr_t -!natrX -natrM ler_nat.
    apply: (@leq_trans ((6 * m.+2) ^ q.+1 * 2 ^ q.+1)); first by rewrite leq_mul2r pmnbr_F_le orbT.
    rewrite -expnMn; apply: pmnbr_exp_mono.
    have -> : (6 * m.+2 * 2 = 12 * m.+2)%N by rewrite mulnAC.
    by rewrite leq_mul2l ltnS Hm orbT.
  - (* L delta <= 1, from 2048 Lmax^6 <= d. *)
    rewrite exprVn Hl4 mulrA -natrM ler_pdivrMr ?ltr0n ?muln_gt0 ?HN ?bin_gt0 // mul1r ler_nat.
    rewrite mulnCA leq_mul2l; apply/orP; right.
    rewrite -(leq_pmul2l (isT : (0 < 4)%N)); apply: leq_trans _ (pmnbr_bin2 d Hd2).
    apply: (@leq_trans (2048 * Lx ^ 6 * d)).
      have -> : (4 * (L * (2 * L * d * (4 * L) ^ 4)) = 2048 * L ^ 6 * d)%N by ring.
      by rewrite leq_mul2r leq_mul2l pmnbr_exp_mono ?orbT.
    by rewrite -mulnn leq_mul2r G3 orbT.
  - (* L theta (1 + K_L) <= 1, from 1 + K_L <= C L^3. *)
    rewrite /c0 -natrD -natrX -natrM -natrD addrC natr1 Eth mulrCA -natrM mulrC.
    rewrite ler_pdivrMr ?ltr0n // mul1r ler_nat.
    apply: (@leq_trans (C * L ^ 4)).
      rewrite (expnS L 3) mulnCA leq_mul2l; apply/orP; right.
      have [l El] : exists l, L = l.+1 by exists L.-1; rewrite prednK.
      rewrite El; exact: Hnat l.
    by rewrite /Z leq_mul2l pmnbr_exp_mono ?orbT.
have EY : Y = (3 * Lx.+1 ^ 2 * (3 * N + N * ((1 + 13 * (4 * c1) ^ 2) ^ 2) + (4 * Lx) ^ 4))%:R.
  by rewrite /Y /c0 !(natrD, natrM, natrX, mulr1n).
(* The sum: K Y 2^-p <= 1/d. *)
apply: (@le_trans _ _ (\sum_(m < K) Y / 2%:R ^+ p)).
  by apply: ler_sum => m _; exact: Hterm m (ltn_ord m).
rewrite sumr_const card_ord -(mulr_natl (Y / 2%:R ^+ p) K) EY mulrA -natrM.
rewrite ler_pdivrMr ?exprn_gt0 ?ltr0n //.
rewrite div1r mulrC ler_pdivlMr ?ltr0n // -natrX -natrM ler_nat.
set c' := ((1 + 13 * (4 * c1) ^ 2) ^ 2)%N.
have HQ : (K * (3 * Lx.+1 ^ 2 * (3 + c' + (4 * Lx) ^ 4)) <= d)%N.
  apply: leq_trans G4.
  apply: (@leq_trans (Lx * (3 * (2 * Lx) ^ 2 * ((259 + c') * Lx ^ 4)))).
    apply: leq_mul; first by rewrite /Lx leq_pmull.
    apply: leq_mul.
      rewrite leq_mul2l; apply/orP; right; apply: pmnbr_exp_mono.
      exact: ltn_Pmull.
    have -> : ((259 + c') * Lx ^ 4 = (3 + c') * Lx ^ 4 + (4 * Lx) ^ 4)%N by ring.
    by rewrite leq_add2r -{1}(muln1 (3 + c')%N) leq_mul2l expn_gt0 HLx orbT.
  by apply: eq_leq; rewrite /c'; ring.
have HY : (3 * N + N * c' + (4 * Lx) ^ 4 <= d ^ 2 * (3 + c' + (4 * Lx) ^ 4))%N.
  rewrite !mulnDr; apply: leq_add; first apply: leq_add.
  - by rewrite mulnC leq_mul2r HNd orbT.
  - by rewrite leq_mul2r HNd orbT.
  - by apply: leq_pmull; rewrite expn_gt0 Hd0.
apply: (@leq_trans (K * (3 * Lx.+1 ^ 2 * (d ^ 2 * (3 + c' + (4 * Lx) ^ 4))) * d)).
  by rewrite leq_mul2r leq_mul2l leq_mul2l HY !orbT.
apply: (@leq_trans (d ^ 4)).
  have -> : (K * (3 * Lx.+1 ^ 2 * (d ^ 2 * (3 + c' + (4 * Lx) ^ 4))) * d =
    d ^ 3 * (K * (3 * Lx.+1 ^ 2 * (3 + c' + (4 * Lx) ^ 4))))%N by ring.
  by rewrite (expnSr d 3) leq_mul2l HQ orbT.
(* d^4 <= d^6 <= 2^p, since d^3 <= 2^L(d). *)
apply: (@leq_trans (d ^ 6)); first by apply: leq_pexp2l.
have -> : (d ^ 6 = (d ^ 3) ^ 2)%N by rewrite -expnM.
by rewrite EP mulnC expnM; apply: pmnbr_exp_mono; exact: F3.
Qed.

End Rate.
