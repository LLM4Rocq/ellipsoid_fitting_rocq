(* The sharp NB moment bound (G16, lower edge, part 7).
   With kap = lam^-2 and B = 4 L, where L = (q+1)(m+1) (pmnct_moment_le):
     E tr T(m+1)^(q+1) <= F(L, q+1) (L+1)^2 (1 + delta)^L Theta,
   where F(L, n) = 2^n binom(L + n, n) (pmnm_F), delta = 2 L d B^4 N lam^-4,
   and Theta = N mu^L + N (1 + 13 c0^2)^2 + B^4 with mu = 1 + theta (1 + K_L)
   and K_L = 2 (L + 3) + (L + 1) (c0 + 2 L)^2.
   The premises are deterministic: N 'C(d, 2) <= lam^4, N <= lam^2,
   d <= c0 lam, N <= d^2, B^2 <= lam theta^294 and B^2 4^45 <= d.
   - pmnct_tau: the largest terminal sum over all marks, at most Theta after
     normalization for every length up to L (pmnct_tau_le): by
     PaperMainSquarefreeWalkNBCoreSum for lengths >= 3, by the shape bound
     pmsb_T_le for lengths 1 and 2, and B^4 for the empty walk.
   - pmnct_Z_le: the explicit bound pmnm_Z of PaperMainSquarefreeWalkNBMarks
     is at most (L+1)^2 (1 + delta)^L Theta after normalization, since
     N lam^-2 <= 1 and N X lam^-4 <= 1 + delta.
   No probability premise beyond the expansion of the trace moment. *)
From Stdlib Require Import Reals Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions
  GaussianProbabilityProductDefinitions PaperMainSquarefreeWalkMoments
  PaperMainSquarefreeWalkExpansion PaperMainSquarefreeWalkCount PaperMainSquarefreeWalkExcess
  PaperMainSquarefreeWalkShapeOnce PaperMainSquarefreeWalkShapeBound
  PaperMainSquarefreeEdgeLower PaperMainSquarefreeWalkNB PaperMainSquarefreeWalkNBMarks
  PaperMainSquarefreeWalkNBCore PaperMainSquarefreeWalkNBCoreSum PaperMainSquarefreeWalkNBCount.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope nat_scope.

(* 1. The terminal bound: the largest terminal sum over all marks. *)
Definition pmnct_tau N d (q0 : 'I_d * 'I_d) B L : nat :=
  \max_(ms : L.-tuple bool) pmnm_T N d q0 B L ms.

Lemma pmnct_tau_ge N d (q0 : 'I_d * 'I_d) B L ms : size ms = L ->
  pmnm_T N d q0 B L ms <= pmnct_tau N d q0 B L.
Proof.
rewrite /pmnct_tau => Hs; have Hs' : size ms == L by rewrite Hs.
exact: (@leq_bigmax _ (fun t : L.-tuple bool => pmnm_T N d q0 B L t) (Tuple Hs')).
Qed.

Lemma pmnct_tau_attained N d (q0 : 'I_d * 'I_d) B L :
  exists ms : L.-tuple bool, pmnct_tau N d q0 B L = pmnm_T N d q0 B L ms.
Proof.
have Hc : 0 < #|[pred _ : L.-tuple bool | true]|.
  by apply/card_gt0P; exists [tuple of nseq L false].
have [ms _ Hms] := eq_bigmax_cond (fun t : L.-tuple bool => pmnm_T N d q0 B L t) Hc.
by exists ms; rewrite -Hms /pmnct_tau; apply: eq_bigl.
Qed.

(* The empty walk. *)
Lemma pmnct_T0 N d (q0 : 'I_d * 'I_d) B ms : pmnm_T N d q0 B 0 ms <= B ^ 4.
Proof.
rewrite /pmnm_T (big_pred1 ([tuple], [tuple])); last first.
  rewrite /= mul1n /pmnm_w.
  have -> : pmsc_e N d [::] [::] = 2.
    by rewrite /pmsc_e /pmsc_R /pmsc_C !eq_card0.
  by rewrite -[X in _ <= X]mul1n leq_mul2r leq_b1 orbT.
move=> [t1 t2]; apply/esym/eqP; congr (_, _); apply: val_inj.
  exact: size0nil (size_tuple _).
exact: size0nil (size_tuple _).
Qed.

(* Marked walks are among the walks of ShapeOnce. *)
Lemma pmnct_T_pmso N d (q0 : 'I_d * 'I_d) B L ms : pmnm_T N d q0 B L ms <= pmso_T N d B L L.
Proof.
rewrite /pmso_T leqnn /pmnm_T; apply: leq_sum => W _.
rewrite leq_mul2l; apply/orP; right.
rewrite /pmnm_w /pmso_w leq_mul2r; apply/orP; right.
by case: (pmso_valid _ _ _ _); case: (pmnm_nb _ _ _ _); case: (pmnm_incr _ _).
Qed.

(* 2. The normalized bounds. *)
Section Bound.
Local Open Scope ring_scope.

Lemma pmnct_Z_le (lam delta Theta : R) (N X : nat) (tau : nat -> nat) L :
  0 < lam -> N%:R * lam^-1 ^+ 2 <= 1 -> (N * X)%:R * lam^-1 ^+ 4 <= 1 + delta ->
  0 <= delta ->
  (forall L', (L' <= L)%N -> lam^-1 ^+ (2 * L') * (tau L')%:R <= Theta) ->
  lam^-1 ^+ (2 * L) * (pmnm_Z N X tau L)%:R <= (L.+1 ^ 2)%:R * (1 + delta) ^+ L * Theta.
Proof.
move=> Hl HN HX Hd HT.
have Hli : 0 < lam^-1 by rewrite invr_gt0.
have HT0 : 0 <= Theta.
  by apply: le_trans (HT 0%N (leq0n L)); rewrite expr0 mul1r ler0n.
have Hd1 : 1 <= 1 + delta by rewrite lerDl.
have Hd0 : 0 <= 1 + delta by apply: le_trans Hd1.
set c := (1 + delta) ^+ L * Theta.
have Hc0 : 0 <= c by apply: mulr_ge0 => //; exact: exprn_ge0.
have HA : lam^-1 ^+ 4 = (lam^-1 ^+ 2) ^+ 2 by rewrite -exprM.
(* Each term: lam^(-2L) = lam^(-2a) lam^(-4b) lam^(-2L'). *)
have Hterm a b : lam^-1 ^+ (2 * L) *
    (((a + 2 * b <= L) * (N ^ a * (N * X) ^ b * tau (L - a - 2 * b)))%N)%:R <= c.
  case: (leqP (a + 2 * b) L) => Hab; last by rewrite mul0n mulr0.
  rewrite mul1n.
  set L' := (L - a - 2 * b)%N.
  have EL : (2 * L = 2 * a + 2 * (2 * b) + 2 * L')%N.
    by rewrite /L' -subnDA -!mulnDr subnKC.
  have HbL : (b <= L)%N.
    apply: leq_trans Hab; rewrite (leq_trans _ (leq_addl _ _)) //.
    by rewrite -{1}[b]mul1n leq_mul2r orbT.
  rewrite EL exprD [lam^-1 ^+ (2 * a + _)]exprD natrM natrM natrX natrX.
  rewrite [lam^-1 ^+ (2 * a)]exprM [lam^-1 ^+ (2 * (2 * b))]exprM [_ ^+ (2 * b)]exprM.
  set A := lam^-1 ^+ 2.
  set Aa := A ^+ a; set A2b := (A ^+ 2) ^+ b; set T0 := lam^-1 ^+ (2 * L').
  set Na := N%:R ^+ a; set Yb := (N * X)%:R ^+ b; set t := (tau L')%:R.
  have E : Aa * A2b * T0 * (Na * Yb * t) = (Na * Aa) * (Yb * A2b) * (T0 * t).
    by rewrite mulrACA [Aa * A2b * _]mulrACA (mulrC Aa) (mulrC A2b).
  rewrite E.
  have HA0 : 0 <= A by apply: exprn_ge0; exact: ltW.
  apply: (@le_trans _ _ (1 * (1 + delta) ^+ b * Theta)).
    have H1 : 0 <= Na * Aa by apply: mulr_ge0; apply: exprn_ge0; [exact: ler0n | exact: HA0].
    have H2 : 0 <= Yb * A2b.
      by apply: mulr_ge0; apply: exprn_ge0; [exact: ler0n | exact: exprn_ge0].
    have H3 : 0 <= T0 * t by apply: mulr_ge0; [apply: exprn_ge0; exact: ltW | exact: ler0n].
    have B1 : Na * Aa <= 1.
      rewrite /Na /Aa -exprMn; apply: exprn_ile1; last exact: HN.
      by apply: mulr_ge0; [exact: ler0n | exact: HA0].
    have B2 : Yb * A2b <= (1 + delta) ^+ b.
      rewrite /Yb /A2b -exprMn; apply: lerXn2r.
      - by rewrite nnegrE; apply: mulr_ge0; [exact: ler0n | exact: exprn_ge0].
      - by rewrite nnegrE.
      - by rewrite /A -HA.
    have B3 : T0 * t <= Theta := HT L' (leq_trans (leq_subr _ _) (leq_subr _ _)).
    apply: ler_pM; [exact: mulr_ge0 | exact: H3 | | exact: B3].
    by apply: ler_pM.
  by rewrite mul1r /c; apply: ler_wpM2r => //; exact: ler_weXn2l.
(* (L+1)^2 terms. *)
rewrite /pmnm_Z natr_sum mulr_sumr.
apply: (@le_trans _ _ (\sum_(0 <= a < L.+1) \sum_(0 <= b < L.+1) c)).
  apply: ler_sum => a _; rewrite natr_sum mulr_sumr; apply: ler_sum => b _; exact: Hterm.
rewrite !sumr_const_nat subn0 -mulrnA -mulr_natl mulnn.
by rewrite mulr1 -mulrA -/c mulr_natl.
Qed.


(* The normalized terminal bound, for all lengths up to L0. *)
Lemma pmnct_tau_le (lam theta c0 : R) N d (q0 : 'I_d * 'I_d) B L0 L :
  (0 < N)%N -> (0 < d)%N -> (N <= d ^ 2)%N -> 0 < lam -> 0 < theta <= 1 -> 0 <= c0 ->
  (N * 'C(d, 2))%:R <= lam ^+ 4 -> N%:R <= lam ^+ 2 -> d%:R <= c0 * lam ->
  (B ^ 2)%:R <= lam * theta ^+ 294 -> (B ^ 2 * 4 ^ 45 <= d)%N -> (L <= L0)%N ->
  lam^-1 ^+ (2 * L) * (pmnct_tau N d q0 B L)%:R <=
  N%:R * (1 + theta * (1 + ((2 * (L0.-1 + 4))%:R +
    (L0.-1 + 2)%:R * (c0 + (2 * L0)%:R) ^+ 2))) ^+ L0 +
  N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2 + (B ^ 4)%:R.
Proof.
move=> HN Hd HNd Hl Ht Hc0 HNM HN2 Hdl HB HB45 HLL0.
have Hli : 0 < lam^-1 by rewrite invr_gt0.
have Ht0 : 0 < theta by case/andP: Ht.
set K0 := (2 * (L0.-1 + 4))%:R + (L0.-1 + 2)%:R * (c0 + (2 * L0)%:R) ^+ 2.
set mu := 1 + theta * (1 + K0).
have HK0 : 0 <= K0 by apply: addr_ge0; rewrite ?ler0n //; apply: mulr_ge0;
  rewrite ?ler0n ?exprn_ge0 // addr_ge0 ?ler0n.
have Hmu1 : 1 <= mu.
  rewrite /mu lerDl; apply: mulr_ge0; first exact: ltW.
  by apply: addr_ge0; [exact: ler01 | exact: HK0].
have Hmu0 : 0 <= mu := le_trans ler01 Hmu1.
have HA1 : 0 <= N%:R * mu ^+ L0 by apply: mulr_ge0; [exact: ler0n | exact: exprn_ge0].
have Hc13 : 0 <= 1 + 13%:R * c0 ^+ 2 :> R.
  by apply: addr_ge0; [exact: ler01 | apply: mulr_ge0; [exact: ler0n | exact: exprn_ge0]].
have HA2 : 0 <= N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2.
  by apply: mulr_ge0; [exact: ler0n | exact: exprn_ge0].
have HA3 : 0 <= (B ^ 4)%:R :> R by exact: ler0n.
have [ms Ems] := pmnct_tau_attained N d q0 B L.
rewrite Ems.
case: (ltnP 2 L) => HL3.
  (* L >= 3: the weighted terminal bound of NBCoreSum. *)
  have H := pmns_T_le R N d B L q0 ms lam theta c0 HN HL3 Hl Ht Hc0 HNM HN2 Hdl HB.
  apply: (@le_trans _ _ (N%:R * mu ^+ L0)).
    set KL := (2 * (L.-1 + 4))%:R + (L.-1 + 2)%:R * (c0 + (2 * L)%:R) ^+ 2.
    set muL := 1 + theta * (1 + KL).
    apply: (@le_trans _ _ (lam^-1 ^+ (2 * L) * (lam ^+ (2 * L) * N%:R * muL ^+ L))).
      by apply: ler_wpM2l; [apply: exprn_ge0; exact: ltW | exact: H].
    rewrite !mulrA -exprMn mulVf ?gt_eqF // expr1n mul1r.
    apply: ler_wpM2l; first exact: ler0n.
    have HL1 : (L.-1 <= L0.-1)%N by rewrite -!subn1 leq_sub2r.
    have HKL : KL <= K0.
      apply: lerD; first by rewrite ler_nat leq_mul2l leq_add2r HL1 orbT.
      apply: ler_pM; [exact: ler0n | apply: exprn_ge0; apply: addr_ge0;
        [exact: Hc0 | exact: ler0n] | |].
        by rewrite ler_nat leq_add2r.
      apply: lerXn2r; rewrite ?nnegrE.
      - by apply: addr_ge0; [exact: Hc0 | exact: ler0n].
      - by apply: addr_ge0; [exact: Hc0 | exact: ler0n].
      - by rewrite lerD2l ler_nat leq_mul2l HLL0 orbT.
    have HmuL : muL <= mu.
      by rewrite /muL /mu lerD2l; apply: ler_wpM2l; [exact: ltW | rewrite lerD2l].
    have HmuL0 : 0 <= muL.
      apply: addr_ge0; first exact: ler01.
      apply: mulr_ge0; first exact: ltW.
      apply: addr_ge0; first exact: ler01.
      apply: addr_ge0; first exact: ler0n.
      apply: mulr_ge0; first exact: ler0n.
      by apply: exprn_ge0; apply: addr_ge0; [exact: Hc0 | exact: ler0n].
    apply: (@le_trans _ _ (mu ^+ L)).
      by apply: lerXn2r; rewrite ?nnegrE.
    exact: (ler_weXn2l Hmu1 HLL0).
  by rewrite -addrA lerDl; apply: addr_ge0.
(* L <= 2: the crude count of PaperMainSquarefreeWalkMoments. *)
case: L HL3 HLL0 ms Ems => [|L1] HL3 HLL0 ms Ems.
  rewrite muln0 expr0 mul1r.
  apply: (@le_trans _ _ (B ^ 4)%:R); first by rewrite ler_nat pmnct_T0.
  by rewrite lerDr; apply: addr_ge0.
have HB' : (B ^ 2 * (2 * L1.+1) ^ 45 <= d)%N.
  apply: leq_trans HB45; rewrite leq_mul2l; apply/orP; right.
  by rewrite leq_exp2r // (_ : 4 = 2 * 2)%N // leq_mul2l HL3.
have Hsb := pmsb_T_le N d B L1.+1 L1.+1 HN Hd HNd (ltn0Sn _) HB'.
have Hpm := pmnct_T_pmso N d q0 B L1.+1 ms.
apply: (@le_trans _ _ (N%:R * mu ^+ L0 + N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2));
  last by rewrite lerDl.
apply: (@le_trans _ _ (N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2)); last by rewrite lerDr.
apply: (@le_trans _ _ (lam^-1 ^+ (2 * L1.+1) * (N * (13 * d ^ 2) ^ L1.+1)%:R)).
  apply: ler_wpM2l; first exact: exprn_ge0 (ltW Hli).
  by rewrite ler_nat (leq_trans Hpm Hsb).
rewrite natrM natrX exprM mulrCA -exprMn.
apply: ler_wpM2l; first exact: ler0n.
have Hl0 : lam != 0 := lt0r_neq0 Hl.
have Hdc : lam^-1 * d%:R <= c0.
  apply: (@le_trans _ _ (lam^-1 * (c0 * lam))).
    by apply: ler_wpM2l; [exact: ltW | exact: Hdl].
  by rewrite mulrCA (mulVf Hl0) mulr1.
have Hd2 : lam^-1 ^+ 2 * (13 * d ^ 2)%:R <= 1 + 13%:R * c0 ^+ 2.
  rewrite natrM natrX mulrCA -exprMn.
  apply: (@le_trans _ _ (13%:R * c0 ^+ 2)); last by rewrite lerDr ler01.
  apply: ler_wpM2l; first exact: ler0n.
  apply: lerXn2r.
  - by rewrite nnegrE; apply: mulr_ge0; [exact: ltW | exact: ler0n].
  - by rewrite nnegrE.
  - exact: Hdc.
apply: (@le_trans _ _ ((1 + 13%:R * c0 ^+ 2) ^+ L1.+1)).
  apply: lerXn2r.
  - by rewrite nnegrE; apply: mulr_ge0; [exact: exprn_ge0 (ltW Hli) | exact: ler0n].
  - by rewrite nnegrE.
  - exact: Hd2.
apply: ler_weXn2l; last exact: HL3.
by rewrite lerDl; apply: mulr_ge0; [exact: ler0n | exact: exprn_ge0].
Qed.

(* 3. The sharp NB moment, with kap = lam^-2 and B = 4 L, L = (q+1)(m+1). *)
Theorem pmnct_moment_le (lam theta c0 : R) N d m q :
  (0 < N)%N -> (0 < d)%N -> (N <= d ^ 2)%N -> 0 < lam -> 0 < theta <= 1 -> 0 <= c0 ->
  (N * 'C(d, 2))%:R <= lam ^+ 4 -> N%:R <= lam ^+ 2 -> d%:R <= c0 * lam ->
  ((4 * (q.+1 * m.+1)) ^ 2)%:R <= lam * theta ^+ 294 ->
  ((4 * (q.+1 * m.+1)) ^ 2 * 4 ^ 45 <= d)%N ->
  gaussian_iterated_expectation (N * d)
    (fun xs => \tr (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d xs) (lam^-1 ^+ 2) m.+1 ^+ q.+1)) <=
  (pmnm_F (q.+1 * m.+1) q.+1)%:R * ((q.+1 * m.+1).+1 ^ 2)%:R *
  (1 + (N * (2 * (q.+1 * m.+1) * d * (4 * (q.+1 * m.+1)) ^ 4))%:R * lam^-1 ^+ 4)
    ^+ (q.+1 * m.+1) *
  (N%:R * (1 + theta * (1 + ((2 * ((q.+1 * m.+1).-1 + 4))%:R +
    ((q.+1 * m.+1).-1 + 2)%:R * (c0 + (2 * (q.+1 * m.+1))%:R) ^+ 2))) ^+ (q.+1 * m.+1) +
   N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2 + ((4 * (q.+1 * m.+1)) ^ 4)%:R).
Proof.
move=> HN Hd HNd Hl Ht Hc0 HNM HN2 Hdl HB HB45.
have q0 : 'I_d * 'I_d := (Ordinal Hd, Ordinal Hd).
have r0 : 'I_N := Ordinal HN.
have Hli : 0 < lam^-1 by rewrite invr_gt0.
have Hl0 : lam != 0 := lt0r_neq0 Hl.
have Hk : 0 <= lam^-1 ^+ 2 by apply: exprn_ge0; exact: ltW.
apply: (le_trans (pmnct_moment_walk N d q0 (lam^-1 ^+ 2) m q Hk)).
rewrite -exprM.
set L := (q.+1 * m.+1)%N.
set B := (4 * L)%N.
set delta := (N * (2 * L * d * B ^ 4))%:R * lam^-1 ^+ 4.
(* The marked count of NBMarks, with the largest terminal sum as tau. *)
have Hcnt : count id (pmnct_ms0 m.+1 L) = q.+1 := pmnct_ms0_count m.+1 q.+1 (ltn0Sn _).
have Hc := pmnm_count N d r0 q0 B q.+1 ('C(d, 2) + 2 * L * d * B ^ 4) (pmnct_tau N d q0 B) L
  (leqnn _) (fun L' ms _ Hs _ => pmnct_tau_ge N d q0 B L' ms Hs)
  L (pmnct_ms0 m.+1 L) (leqnn _) (pmnct_ms0_size _ _) (eq_leq Hcnt).
rewrite Hcnt in Hc.
(* The premises of pmnct_Z_le. *)
have HN' : N%:R * lam^-1 ^+ 2 <= 1.
  apply: (@le_trans _ _ (lam ^+ 2 * lam^-1 ^+ 2)).
    by apply: ler_wpM2r; [apply: exprn_ge0; exact: ltW | exact: HN2].
  by rewrite -exprMn (mulfV Hl0) expr1n.
have HX' : (N * ('C(d, 2) + 2 * L * d * B ^ 4))%:R * lam^-1 ^+ 4 <= 1 + delta.
  rewrite mulnDr natrD mulrDl /delta lerD2r.
  apply: (@le_trans _ _ (lam ^+ 4 * lam^-1 ^+ 4)).
    by apply: ler_wpM2r; [apply: exprn_ge0; exact: ltW | exact: HNM].
  by rewrite -exprMn (mulfV Hl0) expr1n.
have Hdelta : 0 <= delta by apply: mulr_ge0; [exact: ler0n | apply: exprn_ge0; exact: ltW].
have HT' := fun L' (HL' : (L' <= L)%N) =>
  pmnct_tau_le lam theta c0 N d q0 B L L' HN Hd HNd Hl Ht Hc0 HNM HN2 Hdl HB HB45 HL'.
have HZ := pmnct_Z_le lam delta _ N ('C(d, 2) + 2 * L * d * B ^ 4) (pmnct_tau N d q0 B) L
  Hl HN' HX' Hdelta HT'.
apply: (@le_trans _ _ (lam^-1 ^+ (2 * L) *
  (pmnm_F L q.+1 * pmnm_Z N ('C(d, 2) + 2 * L * d * B ^ 4) (pmnct_tau N d q0 B) L)%:R)).
  by apply: ler_wpM2l; [apply: exprn_ge0; exact: ltW | rewrite ler_nat; exact: Hc].
rewrite natrM mulrCA -!mulrA.
apply: ler_wpM2l; first exact: ler0n.
rewrite mulrA; exact: HZ.
Qed.

End Bound.
