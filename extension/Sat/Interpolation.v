(* The small-residual interpolation: Theorem 2.3 (lines 878-893, proof
   lines 2464-2528, the shelling argument) and Theorem 1.9 (proof lines
   957-974) of Koehler and Sohn (arXiv 2608.27372), at Stdlib's R. Item S10
   of stage 3 of phase 5 (lane C).

   Proved here.
   - shelling: for lam in R^n, 0 <= s <= 1 and k, the set I of at most k
     largest coordinates of lam (|lam_j| <= |lam_i| for i in I, j not in
     I) can be chosen so that the tail t = lam off I is light,
     t_j^2 <= s |t|^2 for every j, or small, |t|^2 <= (1 - s)^k |lam|^2:
     while the tail is not light, moving its largest coordinate into I
     multiplies |t|^2 by at most 1 - s.
   - compatibility (Theorem 2.3, deterministic part): let N be a seminorm
     on R^n (N = nuclear o L_X^* below) with
       a |h|_1 <= N h for every h with at most k nonzero coordinates
         (Proposition 3.3, Sat/SparseLower),
       N z <= Cu D |z| for every z (Proposition 3.1 (iii), Sat/Apriori),
       gam D |t| <= N (h + t) whenever |I| <= k, h is supported in I, t
         is supported off I, K D t_i^2 <= |t|^2 for every i and
         |h|_1 <= r |t| (Proposition 3.4, Sat/LightTailBound of lane B),
     and (1 - 1/(K D))^k <= D^(-4), 2 Cu D <= a r, 4 Cu <= a D, D >= 2.
     Then every lam has a set I of at most k largest coordinates with
       a |lam_I|_1 + D |lam off I| <= (3 + (Cu + 1) / gam + 1 / Cu) N lam.
     The proof is the paper's: shelling with s = 1/(K D), then three
     cases (a light tail with a small head, a light tail with a large
     head, a small tail).
   - interpolation_dual (Theorem 1.9, deterministic part): with
     A_X = P_(1^perp) L_X, if |<lam, y>| <= M nuclear (L_X^* lam) for
     every lam with sum_i lam_i = 0, then some symmetric Delta with
     opnorm Delta <= M and some real b satisfy <W_i, Delta> = y_i + b for
     every i, that is A_X Delta = P_(1^perp) y: range_duality_sym of
     matrix/nuclear.v for the centered features W_i - (1/n) sum_j W_j.
   - interpolation_det (Theorem 1.9 on the event of Theorem 2.3): under the
     hypotheses of compatibility for N = nuclear o L_X^*, every y with
     |y_i| <= Y for every i is matched, <W_i, Delta> = y_i + b, by a
     symmetric Delta with
       opnorm Delta <= (3 + (Cu + 1) / gam + 1 / Cu) (Y / a + |y| / D),
     since |<lam, y>| <= |h|_1 Y + |t| |y|.

   - small_residual_interpolation_limit_flat (Theorem 1.9 with
     probability tending to one, for flat families of component laws,
     item X5 of phase 6): for 0 < K and 0 < alpha, from Proposition 3.4 in
     the form light_tail_bound_flat K alpha (constants K1, gam), there is
     C1 > 0 such that, for every n of density alpha and every eps > 0,
     there is D such that for every d >= D and every flat family of
     component laws with constant K, outside a measurable event of
     probability at most eps, every y with |y_i| <= Y is matched,
     <W_i, Delta> = y_i + b, by a symmetric Delta with
     opnorm Delta <= C1 ((ln d)^4 / sqrt d Y + |y| / d). The event is the
     union of those of adjoint_bound_limit_flat (Proposition 3.1 (iii),
     Cu = adj_const K 252 (alpha + 1)), sparse_lower_limit_flat
     (Proposition 3.3, a = sqrt d / (rate_CS K C0 (ln d)^4)) and
     light_tail_bound_flat, with C0 = 5 K1, k = floor (C0 d ln d) and
     D = r = d; on its complement interpolation_det applies, since
     (1 - 1/(K1 d))^k <= exp (- k/(K1 d)) <= d^(-4), and
     C1 = (3 + (Cu + 1) / gam + 1 / Cu) (rate_CS K C0 + 1).
     Sat/SmallResidual removes the hypothesis with light_tail_quotient_flat
     of Sat/LightTailBound (lane B). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import order sesquilinear boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.matrix Require Import nuclear.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality.Sat Require Import Apriori AprioriSparse.
From EllipsoidUniversality.Sat Require Import SparseLower.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import normedtype sequences exp.
From GaussianAnalysis.probability Require Import lindeberg.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Sat Require Import SparseLimit.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

(* 1. Shelling. *)

Section shelling.
Variable n : nat.
Implicit Types (lam : 'rV[R]_n) (I : {set 'I_n}).

(* The l1 norm, and the squared norm of the part of lam off I. *)
Definition l1_norm lam : R := \sum_i `|lam 0 i|.

Definition tail_sq lam I : R := \sum_(j | j \notin I) lam 0 j ^+ 2.

Lemma shelling lam (s : R) (k : nat) : 0 <= s <= 1 ->
  exists I : {set 'I_n}, [/\ (#|I| <= k)%N,
    forall i j, i \in I -> j \notin I -> `|lam 0 j| <= `|lam 0 i| &
    (forall j, j \notin I -> lam 0 j ^+ 2 <= s * tail_sq lam I) \/
    tail_sq lam I <= (1 - s) ^+ k * mxdot lam lam].
Proof.
move=> /andP[s0 s1].
have s1' : 0 <= 1 - s by rewrite subr_ge0.
elim: k => [|k [I [Ik Iord Ilt]]].
  exists (finset.set0 : {set 'I_n}); split => //; first by rewrite cards0.
    by move=> i j; rewrite inE.
  right; rewrite expr0 mul1r /tail_sq /mxdot big_ord1 le_eqVlt.
  apply/orP; left; apply/eqP.
  by apply: eq_big => [j|j _]; rewrite ?inE // expr2.
case: (boolP [forall j, (j \notin I) ==> (lam 0 j ^+ 2 <= s * tail_sq lam I)]).
  move=> /forallP hl; exists I; split => //; first exact: leqW.
  by left => j jI; have := hl j; rewrite jI.
(* the tail is not light: move its largest coordinate i into I *)
rewrite negb_forall => /existsP [j].
rewrite negb_imply -ltNge => /andP [jI hj].
have Ilt' : tail_sq lam I <= (1 - s) ^+ k * mxdot lam lam.
  by case: Ilt => // hl; have := hl j jI; rewrite leNgt hj.
pose i := [arg max_(i > j | i \notin I) `|lam 0 i|]%O.
have [ii imax] : i \notin I /\
    forall l, l \notin I -> `|lam 0 l| <= `|lam 0 i|.
  by rewrite /i; case: arg_maxP.
exists (i |: I); split.
- by rewrite cardsU1 ii add1n ltnS.
- move=> a b; rewrite !in_setU1 negb_or => /orP [/eqP -> | aI] /andP [_ bI].
    exact: imax.
  exact: Iord.
- right.
  have -> : tail_sq lam (i |: I) = tail_sq lam I - lam 0 i ^+ 2.
    rewrite /tail_sq [in RHS](bigD1 i) //= addrC addKr.
    by apply: eq_bigl => l; rewrite in_setU1 negb_or andbC.
  have hi : s * tail_sq lam I <= lam 0 i ^+ 2.
    apply: le_trans (ltW hj) _.
    rewrite -[lam 0 j ^+ 2]real_normK ?num_real //.
    rewrite -[lam 0 i ^+ 2]real_normK ?num_real //.
    by rewrite !expr2; apply: ler_pM; rewrite ?normr_ge0 ?imax.
  apply: le_trans (_ : (1 - s) * tail_sq lam I <= _).
    by rewrite mulrBl mul1r lerB.
  by rewrite exprS -mulrA ler_wpM2l.
Qed.

Lemma l1_norm_ge0 lam : 0 <= l1_norm lam.
Proof. by apply: sumr_ge0 => i _; exact: normr_ge0. Qed.

Lemma frobenius_le_l1 lam : frobenius lam <= l1_norm lam.
Proof.
rewrite -ler_sqr ?nnegrE ?frobenius_ge0 ?l1_norm_ge0 //.
rewrite frobenius_sqr /mxdot big_ord1 expr2 {1}/l1_norm mulr_suml.
apply: ler_sum => i _.
apply: le_trans (ler_norm _) _; rewrite normrM.
apply: ler_wpM2l; first exact: normr_ge0.
rewrite /l1_norm (bigD1 i) //= lerDl.
by apply: sumr_ge0 => j _; exact: normr_ge0.
Qed.

End shelling.

Arguments l1_norm {n}.
Arguments tail_sq {n}.

(* 2. Theorem 2.3, deterministic part. *)

Section compatibility.
Variables (n : nat) (N : 'rV[R]_n -> R).
Hypothesis ND : forall u v, N (u + v) <= N u + N v.
Hypothesis NN : forall u, N (- u) = N u.
Variables (k : nat) (a Cu gam K D r : R).
Hypotheses (a0 : 0 < a) (Cu0 : 0 < Cu) (gam0 : 0 < gam).
Hypotheses (D2 : 2 <= D) (KD1 : 1 <= K * D).
(* Proposition 3.3 *)
Hypothesis hh : forall h, (#|supp h| <= k)%N -> a * l1_norm h <= N h.
(* Proposition 3.1 (iii) *)
Hypothesis hz : forall z, N z <= Cu * D * frobenius z.
(* Proposition 3.4 *)
Hypothesis ht : forall (I : {set 'I_n}) (h t : 'rV[R]_n), (#|I| <= k)%N ->
  supported I h -> supported (~: I) t ->
  (forall i, K * D * t 0 i ^+ 2 <= mxdot t t) ->
  l1_norm h <= r * frobenius t -> gam * D * frobenius t <= N (h + t).
Hypothesis hk : (1 - (K * D)^-1) ^+ k <= (D ^+ 4)^-1.
Hypothesis hr : 2 * Cu * D <= a * r.
Hypothesis hD : 4 * Cu <= a * D.

Theorem compatibility (lam : 'rV[R]_n) :
  exists I : {set 'I_n}, [/\ (#|I| <= k)%N,
    forall i j, i \in I -> j \notin I -> `|lam 0 j| <= `|lam 0 i| &
    a * l1_norm (restr I lam) + D * frobenius (restr (~: I) lam) <=
    (3 + (Cu + 1) / gam + Cu^-1) * N lam].
Proof.
have D0 : 0 < D by apply: lt_le_trans D2.
have KD0 : 0 < K * D by apply: lt_le_trans KD1.
have s01 : 0 <= (K * D)^-1 <= 1.
  by rewrite invr_ge0 (ltW KD0) /= invf_le1.
have [I [Ik Iord Ilt]] := shelling _ lam _ k s01.
exists I; split => //.
set h := restr I lam; set t := restr (~: I) lam.
have lamE : lam = h + t.
  apply/rowP => i; rewrite mxE !restrE inE.
  by case: (i \in I); rewrite ?addr0 ?add0r.
have hI : supported I h by exact: supported_restrE.
have tI : supported (~: I) t by exact: supported_restrE.
(* N lam >= N h - N t >= a |h|_1 - Cu D |t| *)
have Nlam : a * l1_norm h - Cu * D * frobenius t <= N lam.
  rewrite lerBlDr; apply: le_trans (hh h (supported_card hI Ik)) _.
  have -> : h = lam + - t by rewrite lamE addrK.
  by apply: le_trans (ND _ _) _; rewrite NN lerD2l hz.
set C' := 3 + (Cu + 1) / gam + Cu^-1.
have T0 : 0 <= frobenius t := frobenius_ge0 t.
have A0 : 0 <= a * l1_norm h.
  by apply: mulr_ge0; [exact: ltW | exact: l1_norm_ge0].
have X0 : 0 <= (Cu + 1) / gam.
  by apply: divr_ge0; [rewrite addr_ge0 // ltW | exact: ltW].
have Y0 : 0 < Cu^-1 by rewrite invr_gt0.
(* when 2 Cu D |t| <= a |h|_1, the head absorbs the tail *)
have absorb : 2 * (Cu * D * frobenius t) <= a * l1_norm h ->
    a * l1_norm h + D * frobenius t <= C' * N lam.
  move=> h2.
  have hA : a * l1_norm h <= 2 * N lam.
    move: h2 Nlam; move: (a * l1_norm h) (Cu * D * frobenius t) (N lam).
    by move=> A P M h1 h3; lra.
  have M0 : 0 <= N lam by move: (le_trans A0 hA); rewrite pmulr_rge0.
  have hT : D * frobenius t <= Cu^-1 * N lam.
    have -> : D * frobenius t = Cu^-1 * (Cu * D * frobenius t).
      by rewrite !mulrA mulVf ?gt_eqF // mul1r.
    apply: ler_wpM2l; first exact: ltW.
    move: h2 hA; move: (a * l1_norm h) (Cu * D * frobenius t) (N lam).
    by move=> A P M h1 h3; lra.
  have XM : 0 <= (Cu + 1) / gam * N lam by rewrite mulr_ge0.
  move: hA hT XM M0; move: (a * l1_norm h) (D * frobenius t) (N lam).
  by rewrite /C'; move=> A P M h1 h3 h4 h5; lra.
have tsq : mxdot t t = tail_sq lam I.
  rewrite /mxdot big_ord1 /tail_sq [RHS]big_mkcond /=.
  apply: eq_bigr => i _.
  by rewrite /t !mxE inE; case: (i \in I) => /=; rewrite ?mul0r // expr2.
have ht0 : mxdot h t = 0.
  rewrite /mxdot big_ord1 big1 // => i _.
  by rewrite /h /t !mxE inE; case: (i \in I); rewrite ?mulr0 ?mul0r.
have lamsq : mxdot lam lam = mxdot h h + mxdot t t.
  by rewrite {1 2}lamE mxdotDl !mxdotDr ht0 mxdotC ht0 add0r addr0.
case: Ilt => [light | small].
  (* a light tail *)
  have tl i : K * D * t 0 i ^+ 2 <= mxdot t t.
    rewrite tsq /t mxE inE; case: ifP => iI /=.
      have := light i iI; rewrite -(ler_pM2l KD0) mulrA.
      have KDn : K * D != 0 by rewrite gt_eqF.
      by rewrite [X in _ <= X -> _]mulrA mulfV // mul1r.
    rewrite expr0n /= mulr0 /tail_sq.
    by apply: sumr_ge0 => j _; exact: sqr_ge0.
  case: (lerP (l1_norm h) (r * frobenius t)) => [hs | hb].
    (* and a small head: Proposition 3.4 *)
    have hg : gam * (D * frobenius t) <= N lam.
      by rewrite mulrA lamE; exact: (ht I h t Ik hI tI tl hs).
    have M0 : 0 <= N lam.
      by apply: le_trans hg; rewrite mulr_ge0 ?mulr_ge0 // ltW.
    have hP : (Cu + 1) * (D * frobenius t) <= (Cu + 1) / gam * N lam.
      rewrite -mulrA; apply: ler_wpM2l; first by rewrite addr_ge0 // ltW.
      by rewrite ler_pdivlMl.
    have YM : 0 <= Cu^-1 * N lam by rewrite mulr_ge0 // ltW.
    rewrite /C'; move: Nlam hP YM M0.
    rewrite -[Cu * D * _]mulrA.
    move: (a * l1_norm h) (D * frobenius t) (N lam) => A P M h1 h3 h4 h5.
    lra.
  (* and a large head *)
  apply: absorb; rewrite !mulrA.
  apply: le_trans (_ : a * r * frobenius t <= _).
    by apply: ler_wpM2r.
  by rewrite -mulrA ler_wpM2l ?ltW.
(* a small tail: |t| <= 2 |h| / D^2 *)
apply: absorb.
have H0 : 0 <= frobenius h := frobenius_ge0 h.
have hsq : D ^+ 4 * tail_sq lam I <= mxdot lam lam.
  have : tail_sq lam I <= (D ^+ 4)^-1 * mxdot lam lam.
    by apply: le_trans small _; apply: ler_wpM2r hk; exact: mxdot_ge0.
  have D4 : 0 < D ^+ 4 by rewrite exprn_gt0.
  rewrite -(ler_pM2l D4) mulrA mulfV ?gt_eqF // mul1r.
  done.
have D16 : 16 <= D ^+ 4.
  have -> : D ^+ 4 = D ^+ 2 * D ^+ 2 by rewrite -exprD.
  have D24 : 4 <= D ^+ 2.
    have -> : (4 = 2 * 2 :> R)%R by rewrite -natrM.
    by rewrite expr2; apply: ler_pM.
  have -> : (16 = 4 * 4 :> R)%R by rewrite -natrM.
  by apply: ler_pM.
have hDT : D ^+ 2 * frobenius t <= 2 * frobenius h.
  have L0 : 0 <= D ^+ 2 * frobenius t.
    by rewrite mulr_ge0 // exprn_ge0 // ltW.
  have R0 : 0 <= 2 * frobenius h by rewrite mulr_ge0.
  rewrite -(ler_sqr L0 R0).
  have e1 : (D ^+ 2 * frobenius t) ^+ 2 = D ^+ 4 * tail_sq lam I.
    by rewrite exprMn -exprM frobenius_sqr tsq.
  have e2 : (2 * frobenius h) ^+ 2 = 4 * mxdot h h.
    by rewrite exprMn frobenius_sqr -natrX.
  rewrite e1 e2.
  have h1 : D ^+ 4 * tail_sq lam I <= mxdot h h + tail_sq lam I.
    by apply: le_trans hsq _; rewrite lamsq tsq.
  have h2 : 16 * tail_sq lam I <= D ^+ 4 * tail_sq lam I.
    by apply: ler_wpM2r => //; rewrite -tsq mxdot_ge0.
  have h3 : 0 <= mxdot h h := mxdot_ge0 h.
  move: h1 h2 h3.
  move: (D ^+ 4 * tail_sq lam I) (tail_sq lam I) (mxdot h h).
  by move=> P X Y h1 h2 h3; lra.
apply: le_trans (_ : a * frobenius h <= _); last first.
  by apply: ler_wpM2l; [exact: ltW | exact: frobenius_le_l1].
rewrite -(ler_pM2l D0).
have -> : D * (2 * (Cu * D * frobenius t)) =
    2 * Cu * (D ^+ 2 * frobenius t).
  by rewrite expr2; ring.
apply: le_trans (_ : 2 * Cu * (2 * frobenius h) <= _).
  by apply: ler_wpM2l => //; rewrite mulr_ge0 // ltW.
have -> : 2 * Cu * (2 * frobenius h) = 4 * Cu * frobenius h.
  by rewrite mulrCA !mulrA -natrM.
rewrite mulrA [D * a]mulrC.
by apply: ler_wpM2r.
Qed.

End compatibility.

(* 3. Theorem 1.9, deterministic part. *)

Section interpolation_dual.
Variables (n d : nat) (x : paper_main_sample n d).

(* The centered features W_i - (1/n) sum_j W_j: their coefficient map is
   A_X = P_(1^perp) L_X. *)
Definition centered_W (i : 'I_n) : 'M[R]_d :=
  sample_W x i - n%:R^-1 *: \sum_j sample_W x j.

(* The centering of a row vector, l - mean(l) 1. *)
Definition center (l : 'rV[R]_n) : 'rV[R]_n :=
  l - (n%:R^-1 * \sum_j l 0 j) *: const_mx 1.

Lemma center_sum (l : 'rV[R]_n) : \sum_i center l 0 i = 0.
Proof.
rewrite /center; under eq_bigr do rewrite !mxE.
under eq_bigr do rewrite mulr1.
rewrite sumrB sumr_const card_ord.
clear x; case: n l => [|m] l; first by rewrite !big_ord0 subr0.
rewrite -mulrnAl.
have -> : m.+1%:R^-1 *+ m.+1 = 1 :> R.
  by rewrite -[m.+1%:R^-1 *+ m.+1]mulr_natr mulVf // pnatr_eq0.
by rewrite mul1r subrr.
Qed.

Lemma coef_adj_centered (l : 'rV[R]_n) :
  coef_adj centered_W l = sample_adj x (center l).
Proof.
rewrite /coef_adj /sample_adj /coef_adj /center.
under eq_bigr do rewrite /centered_W scalerBr.
rewrite sumrB.
under [in RHS]eq_bigr do rewrite !mxE mulr1 scalerBl.
rewrite [in RHS]sumrB; congr (_ - _).
by rewrite -[RHS]scaler_sumr -[LHS]scaler_suml scalerA [_ * n%:R^-1]mulrC.
Qed.

Theorem interpolation_dual (y : 'rV[R]_n) (M : R) : 0 <= M ->
  (forall lam : 'rV[R]_n, \sum_i lam 0 i = 0 ->
     `|mxdot lam y| <= M * nuclear (sample_adj x lam)) ->
  exists Delta : 'M[R]_d, [/\ Delta \is symmetricmx, opnorm Delta <= M &
    exists b : R, forall i, mxdot (sample_W x i) Delta = y 0 i + b].
Proof.
move=> M0 hy.
have Ws i : centered_W i \is symmetricmx.
  have WT j : (sample_W x j)^T = sample_W x j.
    by apply/symmetricmxP; rewrite -sample_adj_delta; exact: sample_adj_sym.
  apply/symmetricmxP; rewrite /centered_W linearB /= WT linearZ /=.
  rewrite linear_sum /=.
  by congr (_ - _ *: _); apply: eq_bigr => j _; exact: WT.
have one l : mxdot l (const_mx 1 : 'rV[R]_n) = \sum_j l 0 j.
  by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite mxE mulr1.
(* the hypothesis of range_duality_sym for the centered features *)
have hyc l : `|mxdot l (center y)| <= M * nuclear (coef_adj centered_W l).
  rewrite coef_adj_centered.
  have -> : mxdot l (center y) = mxdot (center l) y.
    rewrite /center mxdotBr mxdotBl mxdotZr mxdotZl.
    congr (_ - _); rewrite [mxdot (const_mx 1) y]mxdotC !one.
    exact: mulrAC.
  exact: hy (center l) (center_sum l).
have [D Ds [DM DE]] := range_duality_sym M0 Ws hyc.
exists D; split => //.
exists (mxdot (n%:R^-1 *: \sum_j sample_W x j) D -
  n%:R^-1 * \sum_j y 0 j) => i.
have := congr1 (fun v : 'rV[R]_n => v 0 i) DE.
rewrite /= !mxE mulr1 /centered_W mxdotBl => h.
rewrite -[LHS](subrK (mxdot (n%:R^-1 *: \sum_j sample_W x j) D)) h.
by rewrite addrA addrAC.
Qed.

End interpolation_dual.

(* 4. Theorem 1.9 on the event of Theorem 2.3. *)

Section interpolation_det.
Variables (n d : nat) (x : paper_main_sample n d).
Variables (k : nat) (a Cu gam K D r : R).
Hypotheses (a0 : 0 < a) (Cu0 : 0 < Cu) (gam0 : 0 < gam).
Hypotheses (D2 : 2 <= D) (KD1 : 1 <= K * D).
Hypothesis hh : forall h, (#|supp h| <= k)%N ->
  a * l1_norm h <= nuclear (sample_adj x h).
Hypothesis hz : forall z, nuclear (sample_adj x z) <= Cu * D * frobenius z.
Hypothesis ht : forall (I : {set 'I_n}) (h t : 'rV[R]_n), (#|I| <= k)%N ->
  supported I h -> supported (~: I) t ->
  (forall i, K * D * t 0 i ^+ 2 <= mxdot t t) ->
  l1_norm h <= r * frobenius t ->
  gam * D * frobenius t <= nuclear (sample_adj x (h + t)).
Hypothesis hk : (1 - (K * D)^-1) ^+ k <= (D ^+ 4)^-1.
Hypothesis hr : 2 * Cu * D <= a * r.
Hypothesis hD : 4 * Cu <= a * D.

Theorem interpolation_det (y : 'rV[R]_n) (Y : R) :
  0 <= Y -> (forall i, `|y 0 i| <= Y) ->
  exists Delta : 'M[R]_d, [/\ Delta \is symmetricmx,
    opnorm Delta <= (3 + (Cu + 1) / gam + Cu^-1) * (Y / a + frobenius y / D) &
    exists b : R, forall i, mxdot (sample_W x i) Delta = y 0 i + b].
Proof.
move=> Y0 hY.
set C' := 3 + (Cu + 1) / gam + Cu^-1.
have D0 : 0 < D by apply: lt_le_trans D2.
have C'0 : 0 <= C'.
  have X0 : 0 <= (Cu + 1) / gam.
    by apply: divr_ge0; [rewrite addr_ge0 // ltW | exact: ltW].
  have Y1 : 0 <= Cu^-1 by rewrite invr_ge0 ltW.
  rewrite /C'; move: X0 Y1; move: ((Cu + 1) / gam) (Cu^-1) => p q p0 q0.
  lra.
have M0 : 0 <= C' * (Y / a + frobenius y / D).
  apply: mulr_ge0 => //; apply: addr_ge0; apply: divr_ge0 => //;
    rewrite ?frobenius_ge0 ?ltW //.
apply: interpolation_dual M0 _ => lam _.
pose N (u : 'rV[R]_n) := nuclear (sample_adj x u).
have ND u v : N (u + v) <= N u + N v by rewrite /N sample_adjD nuclearD.
have NN u : N (- u) = N u by rewrite /N sample_adjN nuclearN.
have [I [Ik _ hI]] := @compatibility _ N ND NN _ _ _ _ _ _ _
  a0 Cu0 gam0 D2 KD1 hh hz ht hk hr hD lam.
set h := restr I lam; set t := restr (~: I) lam.
have lamE : lam = h + t.
  apply/rowP => i; rewrite mxE !restrE inE.
  by case: (i \in I); rewrite ?addr0 ?add0r.
(* |<lam, y>| <= |h|_1 Y + |t| |y| <= (Y / a + |y| / D) (a |h|_1 + D |t|) *)
have e1 : `|mxdot h y| <= l1_norm h * Y.
  rewrite /mxdot big_ord1 /l1_norm mulr_suml.
  apply: le_trans (ler_norm_sum _ _ _) _.
  by apply: ler_sum => i _; rewrite normrM ler_wpM2l ?normr_ge0.
have e2 : `|mxdot t y| <= frobenius t * frobenius y := mxdot_le t y.
rewrite lamE mxdotDl.
apply: le_trans (ler_normD _ _) _.
apply: le_trans (lerD e1 e2) _.
rewrite -lamE.
have F0 : 0 <= frobenius y := frobenius_ge0 y.
have H1 : 0 <= l1_norm h := l1_norm_ge0 _ h.
have T0 : 0 <= frobenius t := frobenius_ge0 t.
have an : a != 0 by rewrite gt_eqF.
have Dn : D != 0 by rewrite gt_eqF.
have key : l1_norm h * Y + frobenius t * frobenius y <=
    (Y / a + frobenius y / D) * (a * l1_norm h + D * frobenius t).
  rewrite mulrDl !mulrDr.
  have -> : Y / a * (a * l1_norm h) = l1_norm h * Y by field.
  have -> : frobenius y / D * (D * frobenius t) = frobenius t * frobenius y.
    by field.
  have c1 : 0 <= Y / a * (D * frobenius t).
    by rewrite mulr_ge0 ?divr_ge0 ?mulr_ge0 // ltW.
  have c2 : 0 <= frobenius y / D * (a * l1_norm h).
    by rewrite mulr_ge0 ?divr_ge0 ?mulr_ge0 // ltW.
  move: c1 c2.
  move: (Y / a * (D * frobenius t)) (frobenius y / D * (a * l1_norm h)).
  move: (l1_norm h * Y) (frobenius t * frobenius y) => p q u v u0 v0.
  lra.
apply: le_trans key _.
have S0 : 0 <= Y / a + frobenius y / D.
  by rewrite addr_ge0 // divr_ge0 // ltW.
apply: le_trans (ler_wpM2l S0 hI) _.
by rewrite mulrA [_ * C']mulrC.
Qed.

End interpolation_det.

(* 5. Theorem 1.9 with probability tending to one. *)

Local Open Scope classical_set_scope.

(* Proposition 3.4 for flat families of component laws (item S9,
   light_tail_quotient_flat of Sat/LightTailBound, lane B) in the form that
   Theorem 2.3 uses: there are K1 > 0 and gam > 0 such that for every
   C0 > 0, with probability tending to one, uniformly in the flat family,
   for every set I of at most C0 d ln d rows, every t vanishing on I with
   K1 d t_i^2 <= |t|^2 for every i, and every h vanishing off I with
   |h|_1 <= d |t|, gam d |t| <= nuclear (L_X^* (h + t)). *)
Definition light_tail_bound_flat (K alpha : R) : Prop :=
  exists K1 gam : R, [/\ 0 < K1, 0 < gam &
  forall C0 : R, 0 < C0 ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  forall lam : nat -> probability (measurableTypeR R) R,
    (forall k, (k < n d * d)%N -> mixture_component_law K (lam k)) ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (tuple_prod lam (n d * d) E <= eps%:E)%E &
    forall x, ~ E x -> forall (I : {set 'I_(n d)}) (h t : 'rV[R]_(n d)),
      #|I|%:R <= C0 * d%:R * ln (d%:R : R) ->
      supported I h -> supported (~: I) t ->
      (forall i, K1 * d%:R * t 0 i ^+ 2 <= mxdot t t) ->
      l1_norm h <= d%:R * frobenius t ->
      gam * d%:R * frobenius t <= nuclear (sample_adj x (h + t))]].

(* The last step of Theorem 1.9, with a clean context for lra. *)
Lemma lin_combine (c u v : R) : 0 <= c -> 0 <= u -> 0 <= v ->
  c * u + v <= (c + 1) * (u + v).
Proof.
move=> c0 u0 v0; have cv : 0 <= c * v by rewrite mulr_ge0.
by rewrite mulrDl !mulrDr mul1r; lra.
Qed.

(* Theorem 1.9 for flat families of component laws: with probability
   tending to one, uniformly in the flat family, every residual y is matched
   up to a shift, <W_i, Delta> = y_i + b for every i, by a symmetric Delta
   with opnorm Delta <= C1 ((ln d)^4 / sqrt d max_i |y_i| + |y| / d). *)
Theorem small_residual_interpolation_limit_flat (K alpha : R) :
  0 < K -> 0 < alpha -> light_tail_bound_flat K alpha ->
  exists C1 : R, 0 < C1 /\
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  forall lam : nat -> probability (measurableTypeR R) R,
    (forall k, (k < n d * d)%N -> mixture_component_law K (lam k)) ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (tuple_prod lam (n d * d) E <= eps%:E)%E &
    forall x, ~ E x -> forall (y : 'rV[R]_(n d)) (Y : R),
      (forall i, `|y 0 i| <= Y) ->
      exists (Delta : 'M[R]_d) (b : R), [/\ Delta \is symmetricmx,
        forall i, mxdot (sample_W x i) Delta = y 0 i + b &
        opnorm Delta <=
          C1 * (ln (d%:R : R) ^+ 4 / Num.sqrt d%:R * Y +
                frobenius y / d%:R)]].
Proof.
move=> K0 a0 [K1 [gam [K10 gam0 hLT]]].
pose C0 := 5 * K1.
have C00 : 0 < C0 by rewrite /C0 mulr_gt0.
pose Cu := adj_const K (252)%R (alpha + 1)%R.
have Cu0 : 0 < Cu.
  rewrite /Cu /adj_const /=; apply: mulr_gt0; rewrite sqrtr_gt0.
    apply: (@lt_le_trans _ _ 25); first exact: ltr0n.
    rewrite lerDr; apply: addr_ge0.
      exact: (mulr_ge0 (ler0n _ 256) (sqr_ge0 _)).
    apply: mulr_ge0; first exact: (mulr_ge0 (ler0n _ 32) (sqrtr_ge0 _)).
    apply: mulr_ge0; last by rewrite addr_ge0 // addr_ge0 // ltW.
    exact: (mulr_ge0 (mulr_ge0 (ler0n _ 2100) (ler0n _ 252)) (sqr_ge0 K)).
  by rewrite addr_gt0 // addr_gt0.
pose CS := rate_CS K C0.
have CS0 : 0 < CS := rate_CS_gt0 K C0 C00.
pose C' := 3 + (Cu + 1) / gam + Cu^-1.
have C'0 : 0 < C'.
  rewrite /C'; apply: addr_gt0; last by rewrite invr_gt0.
  by apply: addr_gt0 => //; rewrite divr_gt0 // addr_gt0.
exists (C' * (CS + 1)); split.
  by rewrite mulr_gt0 // addr_gt0.
move=> n hn eps e0.
pose e3 := eps / 3.
have e30 : 0 < e3 by rewrite divr_gt0.
have [D1 hD1] := adjoint_bound_limit_flat K alpha n a0 hn e3 e30.
have [D2 hD2] := sparse_lower_limit_flat K alpha C0 n K0 a0 hn C00 e3 e30.
have [D3 hD3] := hLT C0 C00 n hn e3 e30.
have p3 : 0 < 4 * Cu * CS + 1.
  apply: ltr_wpDl; last exact: ltr01.
  exact: (mulr_ge0 (mulr_ge0 (ler0n _ 4) (ltW Cu0)) (ltW CS0)).
have c3 := ln_pow_le_sqrt (4 * Cu * CS + 1) 4 p3.
have [D hD] := ev_and (density_ev _ _ a0 hn) (ev_and ev_ln_ge1 (ev_and c3
  (ev_and (ev_gt K1^-1) (ev_and (ev_ge 2) (ev_and (ev_ge D1)
  (ev_and (ev_ge D2) (ev_ge D3))))))).
exists D => d dD lam hlam.
have [[h1a h1b] [h2 [h3 [h4 [dd2 [dD1 [dD2 dD3]]]]]]] := hD d dD.
have [E1 [mE1 PE1 hE1]] := hD1 d dD1 lam hlam.
have [E2 [mE2 PE2 hE2]] := hD2 d dD2 lam hlam.
have [E3 [mE3 PE3 hE3]] := hD3 d dD3 lam hlam.
exists (E1 `|` E2 `|` E3); split.
- by apply: measurableU => //; apply: measurableU.
- have mE12 : measurable (E1 `|` E2) by apply: measurableU.
  apply: le_trans (measureU2 _ mE12 mE3) _.
  apply: le_trans (leeD (measureU2 _ mE1 mE2) PE3) _.
  apply: le_trans (leeD (leeD PE1 PE2) (lexx _)) _.
  by rewrite -!EFinD lee_fin /e3; lra.
move=> x nE y Y hY.
have xE1 : ~ E1 x by move=> h; apply: nE; left; left.
have xE2 : ~ E2 x by move=> h; apply: nE; left; right.
have xE3 : ~ E3 x by move=> h; apply: nE; right.
have [_ hadj] := hE1 x xE1.
have hz z : nuclear (sample_adj x z) <= Cu * d%:R * frobenius z.
  exact: nuclear_sample_adj_le (n d) d x Cu hadj z.
have d0 : (0 < d)%N by apply: leq_trans dd2.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have d2R : 2%:R <= d%:R :> R by rewrite ler_nat.
have KD1 : 1 <= K1 * d%:R.
  by move: h4; rewrite -(ltr_pM2l K10) mulfV ?gt_eqF // => /ltW.
have l1 : 1 <= ln (d%:R : R) := h2.
have l0 : 0 <= ln (d%:R : R) by apply: le_trans l1.
have l40 : 0 < ln (d%:R : R) ^+ 4 by rewrite exprn_gt0 // (lt_le_trans ltr01).
have sd0 : 0 < Num.sqrt (d%:R : R) by rewrite sqrtr_gt0.
have x0 : 0 <= C0 * d%:R * ln (d%:R : R) by rewrite !mulr_ge0 // ltW.
pose k := archimedean.Num.truncn (C0 * d%:R * ln (d%:R : R)).
pose a := Num.sqrt (d%:R : R) / (CS * ln (d%:R : R) ^+ 4).
have a0' : 0 < a by rewrite /a divr_gt0 // mulr_gt0.
have lpos : 0 < ln (d%:R : R) by apply: lt_le_trans l1; exact: ltr01.
have hh h : (#|supp h| <= k)%N -> a * l1_norm h <= nuclear (sample_adj x h).
  move=> hk.
  have hs : #|supp h|%:R <= C0 * d%:R * ln (d%:R : R).
    by move: hk; rewrite /k archimedean.Num.Theory.truncn_ge_nat.
  have H := hE2 x xE2 h hs.
  rewrite /a /l1_norm mulrAC ler_pdivrMr ?mulr_gt0 //.
  rewrite mulrC [X in _ <= X]mulrC.
  exact: H.
have ht (I : {set 'I_(n d)}) (h t : 'rV[R]_(n d)) : (#|I| <= k)%N ->
    supported I h -> supported (~: I) t ->
    (forall i, K1 * d%:R * t 0 i ^+ 2 <= mxdot t t) ->
    l1_norm h <= d%:R * frobenius t ->
    gam * d%:R * frobenius t <= nuclear (sample_adj x (h + t)).
  move=> hk; apply: hE3 => //.
  by move: hk; rewrite /k archimedean.Num.Theory.truncn_ge_nat.
have l4 : 0 <= ln (d%:R : R) ^+ 4 by rewrite exprn_ge0 // ltW.
have X0 : 0 <= Cu * CS * ln (d%:R : R) ^+ 4.
  exact: (mulr_ge0 (mulr_ge0 (ltW Cu0) (ltW CS0)) l4).
have hr : 2 * Cu * d%:R <= a * d%:R.
  apply: ler_wpM2r; first exact: ltW.
  rewrite /a ler_pdivlMr ?mulr_gt0 //.
  by move: h3 X0 l4; lra.
have hDc : 4 * Cu <= a * d%:R.
  apply: le_trans (_ : a <= _); last first.
    by apply: ler_peMr; [exact: ltW | rewrite ler1n].
  rewrite /a ler_pdivlMr ?mulr_gt0 //.
  by move: h3 X0 l4; lra.
have hk : (1 - (K1 * d%:R)^-1) ^+ k <= (d%:R ^+ 4)^-1.
  have KDp : 0 < K1 * d%:R by apply: lt_le_trans KD1; exact: ltr01.
  have w0 : 0 <= (K1 * d%:R)^-1 by rewrite invr_ge0 ltW.
  have w1 : (K1 * d%:R)^-1 <= 1 by rewrite invf_le1.
  have e1 : 1 - (K1 * d%:R)^-1 <= expR (- (K1 * d%:R)^-1).
    exact: expR_ge1Dx.
  have p0 : 0 <= 1 - (K1 * d%:R)^-1 by rewrite subr_ge0.
  apply: le_trans (_ : expR (- (K1 * d%:R)^-1) ^+ k <= _).
    by apply: lerXn2r => //; rewrite nnegrE ?expR_ge0.
  rewrite -expRM_natr.
  have -> : (d%:R ^+ 4)^-1 = expR (- (4%:R * ln (d%:R : R))).
    by rewrite expRN expRM_natl lnK // posrE.
  rewrite ler_expR mulNr lerN2.
  (* 4 ln d <= k / (K1 d) *)
  have hk1 := archimedean.Num.Theory.truncnS_gt (C0 * d%:R * ln (d%:R : R)).
  rewrite -/k in hk1.
  rewrite [_^-1 * _]mulrC ler_pdivlMr //.
  rewrite -[k.+1%:R]natr1 /C0 in hk1.
  have KDl := ler_pM ler01 ler01 KD1 l1; rewrite mul1r in KDl.
  by move: hk1 KDl; lra.
have np : (0 < n d)%N.
  have q0 : 0 < Num.min (alpha / 2) 1 by rewrite lt_min divr_gt0 // ltr01.
  rewrite -(ltr0n R); apply: lt_le_trans h1a.
  by rewrite mulr_gt0 // exprn_gt0.
have Y0 : 0 <= Y := le_trans (normr_ge0 _) (hY (Ordinal np)).
have [Delta [Ds DM [b hb]]] := interpolation_det (n d) d x k a Cu gam K1
  d%:R d%:R a0' Cu0 gam0 d2R KD1 hh hz ht hk hr hDc y Y Y0 hY.
exists Delta, b; split => //.
apply: le_trans DM _.
rewrite -mulrA; apply: ler_wpM2l; first exact: ltW.
clearbody CS.
have eY : Y / a = CS * (ln (d%:R : R) ^+ 4 / Num.sqrt (d%:R : R) * Y).
  by rewrite /a invf_div mulrC -!mulrA.
rewrite eY.
have u0 : 0 <= ln (d%:R : R) ^+ 4 / Num.sqrt (d%:R : R) * Y.
  by rewrite mulr_ge0 // divr_ge0 // ltW.
have v0 : 0 <= frobenius y / d%:R by rewrite divr_ge0 ?frobenius_ge0 // ltW.
exact: (lin_combine _ _ _ (ltW CS0) u0 v0).
Qed.

