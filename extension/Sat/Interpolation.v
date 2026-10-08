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
         |h|_1 <= r |t| (Proposition 3.4, Sat/LightTail of lane B),
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

   The probabilistic statements (the three hypotheses with probability
   tending to one, with a = c sqrt d / (ln d)^4, D = d and k = C0 d ln d)
   come next. *)

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
