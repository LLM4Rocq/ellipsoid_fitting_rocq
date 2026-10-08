(* Convergence in probability along a sequence of probability spaces, at
   Stdlib's R, for the limits in probability of the Gaussian model (item G8
   of stage 2 of phase 5, lane C): Proposition 5.15, Lemma 5.16 and
   Proposition 1.4 (ii) of Koehler and Sohn (arXiv 2608.27372). The
   statements are general; the Gaussian part is at the end.

   For probabilities P d on measurable types T d (d a natural number, the
   dimension), a family of events E d is negligible when for every eps > 0
   and every large d, E d lies in a measurable event of probability at most
   eps. Asking for a measurable cover rather than for the measurability of
   E d itself lets the events be defined by infima, suprema or projections
   whose measurability would be a separate proof; covers combine by unions
   (negligibleU) and inclusions (negligibleW). A real statistic X d
   converges in probability to l (cvg_prob P X l) when the events
   eta <= |X d - l| are negligible for every eta > 0.

   Results.
   - negligibleW, negligibleU, negligible_measurable.
   - cvg_probP: convergence in probability to l is the negligibility of the
     events t <= X d for every t > l and X d <= t for every t < l.
   - cvg_prob_eq (statistics that agree for every large d),
     cvg_prob_cst, cvg_probD, cvg_probN, cvg_probB, cvg_probM, cvg_probV
     (at a nonzero limit), cvg_prob_sqrt (by sqrt_dist_le,
     |sqrt a - sqrt b| <= sqrt |a - b| for all reals a, b), cvg_prob_norm,
     cvg_prob_squeeze (between two statistics with the same limit),
     cvg_prob_lipschitz (images under a Lipschitz map), cvg_prob_seq
     (deterministic sequences).
   - cvg_prob_center: if X d -> l in probability and X d - m d -> 0 in
     probability, then the deterministic m d tends to l (two events of
     probability at most 1/3 leave a point outside both); with m d the mean
     and a concentration inequality, this gives the convergence of means.
   - cvg_prob_concentration: if the deviations |X d - m d| >= u have
     probability at most 2 exp (- u^2 / (c d^2)), as for a function of
     Gaussian coordinates with Lipschitz constant of order d
     (library/comparison/gauss_concentration.v), then
     (X d - m d) / (d sqrt d) -> 0 in probability (expR_lin_small:
     2 exp (- d / c) <= eps for every large d).
   - cvg_prob_law: convergence in probability depends only on the laws of
     the measurable statistics X d, for every large d; it moves a limit
     from one sequence of probability spaces to another.
   - For the standard Gaussian vectors of library/gaussian/gauss.v:
     negligible_gaussN, the negligible events are still negligible after
     a |-> - a (gauss_orthogonal_law of library/comparison/gauss_law.v);
     negligible_gauss_lsubmx and negligible_gauss_rsubmx, events of a
     block of coordinates (gauss_lsubmx, gauss_rsubmx); and the same for
     cvg_prob. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import interval measurable_realfun probability exp.
From GaussianAnalysis Require Import measurable_matrix gauss gauss_law.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* 2 exp (- d / c) <= eps for every large d. *)
Lemma expR_lin_small (c eps : R) : 0 < c -> 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
  2 * sequences.expR (- (d%:R / c)) <= eps.
Proof.
move=> c0 e0.
exists (archimedean.Num.truncn (2 * c / eps)).+1 => d dD.
have hd : 2 * c / eps < d%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
have y0 : 2 / eps < d%:R / c by rewrite ltr_pdivlMr // mulrAC.
have ey : 2 / eps < sequences.expR (d%:R / c).
  apply: lt_le_trans y0 _; apply: le_trans (expR_ge1Dx _).
  by rewrite lerDr.
rewrite expRN -[2 * _]/(2 / _) ler_pdivrMr ?expR_gt0 //.
by rewrite ltr_pdivrMr // mulrC in ey; exact: ltW.
Qed.

Section in_probability.
Context {disp : measure_display} (T : nat -> measurableType disp)
  (P : forall d, probability (T d) RR).

(* E d is negligible: for every large d it lies in a measurable event of
   small probability. *)
Definition negligible (E : forall d, set (T d)) : Prop :=
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists A : set (T d), [/\ measurable A, (P d A <= eps%:E)%E & E d `<=` A].

Definition cvg_prob (X : forall d, T d -> RR) (l : RR) : Prop :=
  forall eta : R, 0 < eta ->
  negligible (fun d => [set x | eta <= `|X d x - l|]).

Lemma negligibleW {E F : forall d, set (T d)} : negligible F ->
  (exists D0 : nat, forall d, (D0 <= d)%N -> E d `<=` F d) -> negligible E.
Proof.
move=> hF [D0 EF] eps e0; have [D hD] := hF eps e0.
exists (maxn D0 D) => d; rewrite geq_max => /andP[d0 dD].
have [A [mA PA FA]] := hD d dD.
by exists A; split => //; exact: subset_trans (EF d d0) FA.
Qed.

Lemma negligibleU {E F : forall d, set (T d)} :
  negligible E -> negligible F -> negligible (fun d => E d `|` F d).
Proof.
move=> hE hF eps e0.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have [D1 h1] := hE _ e2; have [D2 h2] := hF _ e2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have [A [mA PA EA]] := h1 d d1; have [B [mB PB FB]] := h2 d d2.
exists (A `|` B); split; first exact: measurableU.
  apply: le_trans (measureU2 _ mA mB) _.
  by apply: le_trans (leeD PA PB) _; rewrite -EFinD -splitr.
by move=> x [/EA|/FB]; [left|right].
Qed.

Lemma negligible_measurable (E : forall d, set (T d)) :
  (forall d, measurable (E d)) ->
  (forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
     (P d (E d) <= eps%:E)%E) ->
  negligible E.
Proof.
move=> mE hE eps e0; have [D hD] := hE eps e0.
by exists D => d dD; exists (E d); split => //; exact: hD.
Qed.

Lemma cvg_probP (X : forall d, T d -> RR) (l : RR) :
  cvg_prob X l <->
  (forall t, l < t -> negligible (fun d => [set x | t <= X d x])) /\
  (forall t, t < l -> negligible (fun d => [set x | X d x <= t])).
Proof.
split => [h|[hu hl] eta e0].
  split => t lt.
    have h1 := h (t - l).
    apply: negligibleW; first by apply: h1; rewrite subr_gt0.
    exists 0%N => d _ x /= tx.
    by apply: le_trans (ler_norm _); rewrite lerD2r.
  have h1 := h (l - t).
  apply: negligibleW; first by apply: h1; rewrite subr_gt0.
  exists 0%N => d _ x /= xt.
  by rewrite distrC; apply: le_trans (ler_norm _); rewrite lerD2l lerN2.
have hu1 : negligible (fun d => [set x | l + eta <= X d x]).
  by apply: hu; rewrite ltrDl.
have hl1 : negligible (fun d => [set x | X d x <= l - eta]).
  by apply: hl; rewrite gtrDl oppr_lt0.
apply: negligibleW; first exact: (negligibleU hu1 hl1).
exists 0%N => d _ x /=; rewrite ler_normr => /orP[h|h]; [left|right].
  by rewrite addrC -lerBrDr.
by move: h; rewrite opprB lerBrDr addrC -lerBrDr.
Qed.

Lemma cvg_prob_eq (X Y : forall d, T d -> RR) (l : RR) :
  (exists D0 : nat, forall d, (D0 <= d)%N -> forall a, X d a = Y d a) ->
  cvg_prob X l -> cvg_prob Y l.
Proof.
move=> [D0 XY] hX eta e0; have nX := hX _ e0.
apply: negligibleW; first exact: nX.
by exists D0 => d dD a /=; rewrite XY.
Qed.

Lemma cvg_prob_cst (l : RR) : cvg_prob (fun _ _ => l) l.
Proof.
move=> eta e0 eps p0; exists 0%N => d _; exists set0; split => //.
  by rewrite measure0 lee_fin ltW.
by move=> x /=; rewrite subrr normr0 leNgt e0.
Qed.

Lemma cvg_probD {X Y : forall d, T d -> RR} {x y : RR} :
  cvg_prob X x -> cvg_prob Y y ->
  cvg_prob (fun d a => X d a + Y d a) (x + y).
Proof.
move=> hX hY eta e0.
have e2 : 0 < eta / 2 by rewrite divr_gt0.
have nX := hX _ e2; have nY := hY _ e2.
apply: negligibleW; first exact: (negligibleU nX nY).
exists 0%N => d _ a /= h.
have : eta <= `|X d a - x| + `|Y d a - y|.
  apply: le_trans h _; rewrite opprD addrACA; exact: ler_normD.
case: (leP (eta / 2) `|X d a - x|) => h1; first by left.
case: (leP (eta / 2) `|Y d a - y|) => h2; first by right.
by move=> h3; have := ltrD h1 h2; rewrite -splitr ltNge h3.
Qed.

Lemma cvg_probN {X : forall d, T d -> RR} {x : RR} :
  cvg_prob X x -> cvg_prob (fun d a => - X d a) (- x).
Proof.
move=> hX eta e0; have h1 := hX _ e0.
apply: negligibleW; first exact: h1.
by exists 0%N => d _ a /=; rewrite -opprD normrN.
Qed.

Lemma cvg_probB {X Y : forall d, T d -> RR} {x y : RR} :
  cvg_prob X x -> cvg_prob Y y ->
  cvg_prob (fun d a => X d a - Y d a) (x - y).
Proof. by move=> hX hY; apply: cvg_probD hX (cvg_probN hY). Qed.

Lemma cvg_probM {X Y : forall d, T d -> RR} {x y : RR} :
  cvg_prob X x -> cvg_prob Y y ->
  cvg_prob (fun d a => X d a * Y d a) (x * y).
Proof.
move=> hX hY eta e0.
have k0 : 0 < 1 + `|x| + `|y| by rewrite -addrA ltr_wpDr // addr_ge0.
have ep : 0 < Num.min 1 (eta / (1 + `|x| + `|y|)).
  by rewrite lt_min ltr01 divr_gt0.
have e1 : Num.min 1 (eta / (1 + `|x| + `|y|)) <= 1 by rewrite ge_min lexx.
have e2 : Num.min 1 (eta / (1 + `|x| + `|y|)) * (1 + `|x| + `|y|) <= eta.
  by rewrite -ler_pdivlMr // ge_min lexx orbT.
move: ep e1 e2; move: (Num.min 1 _) => e ep e1 e2.
have nX := hX _ ep; have nY := hY _ ep.
apply: negligibleW; first exact: (negligibleU nX nY).
exists 0%N => d _ a /= h.
case: (leP e `|X d a - x|) => h1; first by left.
case: (leP e `|Y d a - y|) => h2; first by right.
exfalso; move: h; apply/negP; rewrite -ltNge.
have -> : X d a * Y d a - x * y =
    (X d a - x) * (Y d a - y) + x * (Y d a - y) + y * (X d a - x) by ring.
move: h1 h2; move: (X d a - x) (Y d a - y) => u v hu hv.
apply: le_lt_trans (ler_normD _ _) _.
apply: le_lt_trans (lerD (ler_normD _ _) (lexx _)) _.
rewrite !normrM.
have uv : `|u| * `|v| < e.
  apply: le_lt_trans (_ : `|u| * `|v| <= `|v|) hv.
  by rewrite ler_piMl // (le_trans (ltW hu)).
have xv : `|x| * `|v| <= `|x| * e by rewrite ler_wpM2l // ltW.
have yu : `|y| * `|u| <= `|y| * e by rewrite ler_wpM2l // ltW.
apply: lt_le_trans e2.
rewrite mulrDr mulrDr mulr1 [e * `|x|]mulrC [e * `|y|]mulrC.
by apply: ltr_leD => //; apply: ltr_leD.
Qed.

Lemma cvg_probV {X : forall d, T d -> RR} {x : RR} : x != 0 ->
  cvg_prob X x -> cvg_prob (fun d a => (X d a)^-1) x^-1.
Proof.
move=> x0 hX eta e0.
have nx : 0 < `|x| by rewrite normr_gt0.
have ep : 0 < Num.min (`|x| / 2) (eta * `|x| ^+ 2 / 2).
  by rewrite lt_min !divr_gt0 // mulr_gt0 // exprn_gt0.
have e1 : Num.min (`|x| / 2) (eta * `|x| ^+ 2 / 2) <= `|x| / 2.
  by rewrite ge_min lexx.
have e2 : Num.min (`|x| / 2) (eta * `|x| ^+ 2 / 2) <= eta * `|x| ^+ 2 / 2.
  by rewrite ge_min lexx orbT.
move: ep e1 e2; move: (Num.min _ _) => e ep e1 e2.
have nX := hX _ ep.
apply: negligibleW; first exact: nX.
exists 0%N => d _ a /= h.
rewrite leNgt; apply/negP => hlt.
move: h; apply/negP; rewrite -ltNge.
(* |X| > |x| / 2 *)
have t := ler_normD (X d a) (x - X d a).
rewrite addrC subrK distrC in t.
have hX2 : `|x| / 2 < `|X d a|.
  by move: t hlt e1; move: `|X d a| `|X d a - x| => p q; lra.
have Xn : X d a != 0.
  by rewrite -normr_gt0; apply: lt_trans hX2; rewrite divr_gt0.
have -> : (X d a)^-1 - x^-1 = (x - X d a) / (X d a * x) by field.
have pX : 0 < `|X d a| * `|x| by rewrite mulr_gt0 // normr_gt0.
rewrite normrM normfV normrM distrC ltr_pdivrMr //.
apply: (lt_le_trans hlt); apply: (le_trans e2).
have -> : eta * `|x| ^+ 2 / 2 = eta * (`|x| / 2 * `|x|).
  by rewrite expr2; field.
by rewrite ler_pM2l // ler_pM2r // ltW.
Qed.

Lemma sqrt_dist_le (a b : RR) : `|Num.sqrt a - Num.sqrt b| <= Num.sqrt `|a - b|.
Proof.
wlog ba : a b / b <= a.
  move=> h; case: (leP b a) => ab; first exact: h.
  by rewrite distrC [`|a - b|]distrC; apply: h; exact: ltW.
have sab : Num.sqrt b <= Num.sqrt a by exact: ler_wsqrtr.
rewrite ger0_norm ?subr_ge0 // ger0_norm ?subr_ge0 // lerBlDl.
case: (leP 0 b) => b0; last first.
  rewrite (ler0_sqrtr (ltW b0)) add0r.
  by apply: ler_wsqrtr; move: b0; lra.
have ab0 : 0 <= a - b by move: ba; lra.
have a0 : 0 <= a by apply: le_trans ba.
rewrite -ler_sqr ?nnegrE ?addr_ge0 ?sqrtr_ge0 // sqrrD.
rewrite (sqr_sqrtr a0) (sqr_sqrtr b0) (sqr_sqrtr ab0).
have := mulr_ge0 (sqrtr_ge0 b) (sqrtr_ge0 (a - b)).
move: (Num.sqrt b * Num.sqrt (a - b)) => p p0.
by rewrite -[(_ *+ 2)]mulr_natr; lra.
Qed.

Lemma cvg_prob_sqrt {X : forall d, T d -> RR} {x : RR} :
  cvg_prob X x -> cvg_prob (fun d a => Num.sqrt (X d a)) (Num.sqrt x).
Proof.
move=> hX eta e0.
have e2 : 0 < eta ^+ 2 by rewrite exprn_gt0.
have nX := hX _ e2.
apply: negligibleW; first exact: nX.
exists 0%N => d _ a /= h.
have h2 := le_trans h (sqrt_dist_le _ _).
rewrite -(sqr_sqrtr (normr_ge0 (X d a - x))).
by rewrite ler_sqr // nnegrE ?sqrtr_ge0 // ltW.
Qed.

Lemma cvg_prob_norm {X : forall d, T d -> RR} {x : RR} :
  cvg_prob X x -> cvg_prob (fun d a => `|X d a|) `|x|.
Proof.
move=> hX eta e0; have h1 := hX _ e0.
apply: negligibleW; first exact: h1.
by exists 0%N => d _ a /= h; apply: le_trans h _; exact: ler_dist_dist.
Qed.

Lemma cvg_prob_squeeze {L X U : forall d, T d -> RR} {l : RR} :
  (exists D0 : nat, forall d, (D0 <= d)%N -> forall a,
     L d a <= X d a <= U d a) ->
  cvg_prob L l -> cvg_prob U l -> cvg_prob X l.
Proof.
move=> [D0 hD] hL hU; apply/cvg_probP.
have [_ hl] := (cvg_probP L l).1 hL; have [hu _] := (cvg_probP U l).1 hU.
split => t lt.
  apply: negligibleW; first exact: (hu t lt).
  exists D0 => d dD a /= tx.
  by have /andP[_ xU] := hD d dD a; exact: le_trans xU.
apply: negligibleW; first exact: (hl t lt).
exists D0 => d dD a /= xt.
by have /andP[Lx _] := hD d dD a; exact: le_trans xt.
Qed.

Lemma cvg_prob_lipschitz (f : RR -> RR) (L : RR) {X : forall d, T d -> RR}
    {x : RR} :
  0 < L -> (forall a b, `|f a - f b| <= L * `|a - b|) ->
  cvg_prob X x -> cvg_prob (fun d a => f (X d a)) (f x).
Proof.
move=> L0 fL hX eta e0.
have eL : 0 < eta / L by rewrite divr_gt0.
have nX := hX _ eL.
apply: negligibleW; first exact: nX.
exists 0%N => d _ a /= h.
by rewrite ler_pdivrMr // mulrC; apply: le_trans h (fL _ _).
Qed.

(* A deterministic sequence as a statistic. *)
Lemma cvg_prob_seq (m : nat -> RR) (l : RR) :
  (forall eta : R, 0 < eta -> exists D : nat, forall d, (D <= d)%N ->
     `|m d - l| < eta) ->
  cvg_prob (fun d _ => m d) l.
Proof.
move=> hm eta e0 eps p0; have [D hD] := hm _ e0.
exists D => d dD; exists set0; split => //.
  by rewrite measure0 lee_fin ltW.
by move=> a /=; rewrite leNgt hD.
Qed.

(* If X converges in probability to l and X - m d converges in probability
   to 0, then m d converges to l. *)
Lemma cvg_prob_center (X : forall d, T d -> RR) (m : nat -> RR) (l : RR) :
  cvg_prob X l -> cvg_prob (fun d a => X d a - m d) 0 ->
  forall eta : R, 0 < eta -> exists D : nat, forall d, (D <= d)%N ->
    `|m d - l| < eta.
Proof.
move=> hX hm eta e0.
have e2 : 0 < eta / 2 by rewrite divr_gt0.
have t3 : (0 : RR) < 3%:R^-1 by rewrite invr_gt0 ltr0n.
have [D1 h1] := hX _ e2 _ t3; have [D2 h2] := hm _ e2 _ t3.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have [A [mA PA XA]] := h1 d d1; have [B [mB PB XB]] := h2 d d2.
(* A `|` B is not the whole space, which has probability 1 *)
have : exists a, ~ (A `|` B) a.
  apply/not_existsP => hAB.
  have AB : A `|` B = setT.
    by apply/seteqP; split => // a _; have := hAB a; apply: contra_notP.
  have := measureU2 (P d) mA mB; rewrite AB => h.
  have e1 : (P d [set: T d] = 1)%E := probability_setT (P d).
  have h' : (1 <= P d A + P d B)%E.
    by rewrite -[X in (X <= _)%E]e1; exact: h.
  have := le_trans h' (leeD PA PB); rewrite -EFinD lee_fin.
  by apply/negP; rewrite -ltNge -mulr2n -mulr_natl; lra.
move=> [a /not_orP[nA nB]].
have hA : `|X d a - l| < eta / 2.
  by rewrite ltNge; apply/negP => h; apply: nA; exact: XA.
have hB : `|X d a - m d| < eta / 2.
  rewrite ltNge; apply/negP => h; apply: nB; apply: XB.
  by rewrite /= subr0.
have := ler_distD (X d a) (m d) l; rewrite distrC => t.
apply: le_lt_trans t _; rewrite [eta]splitr; apply: ltrD => //.
by rewrite distrC.
Qed.

(* A statistic that concentrates at scale d around m d, as Lipschitz
   functions of d^2 Gaussian coordinates of constant Lipschitz norm do,
   is close to m d at the scale d sqrt d. *)
Lemma cvg_prob_concentration (X : forall d, T d -> RR) (m : nat -> RR)
    (c : R) : 0 < c -> (forall d, measurable_fun setT (X d)) ->
  (forall d (u : R), 0 <= u ->
     (P d [set x | (u <= `|X d x - m d|)%R] <=
      (2 * sequences.expR (- u ^+ 2 / (c * d%:R ^+ 2)))%:E)%E) ->
  cvg_prob (fun d x => (X d x - m d) / (d%:R * Num.sqrt d%:R)) 0.
Proof.
move=> c0 mX hX eta e0.
apply: negligible_measurable.
  move=> d.
  have mf : measurable_fun setT (fun x : T d =>
      `|(X d x - m d) / (d%:R * Num.sqrt d%:R) - 0| : RR).
    apply: measurableT_comp; first exact: normr_measurable.
    apply: measurable_funB; last exact: measurable_cst.
    apply: measurable_funM; last exact: measurable_cst.
    by apply: measurable_funB; [exact: mX | exact: measurable_cst].
  have := mf measurableT _ (measurable_itv `[eta, +oo[%R).
  rewrite setTI; congr (measurable _).
  by apply/seteqP; split => x /=; rewrite in_itv /= andbT.
move=> eps p0.
have ec : 0 < c / eta ^+ 2 by rewrite divr_gt0 // exprn_gt0.
have [D hD] := expR_lin_small _ _ ec p0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1].
have dR : 0 < d%:R :> R by rewrite ltr0n.
set s := d%:R * Num.sqrt d%:R.
have s0 : 0 < s by rewrite mulr_gt0 // sqrtr_gt0.
have -> : [set x | eta <= `|(X d x - m d) / s - 0|] =
    [set x | (eta * s <= `|X d x - m d|)%R].
  apply/seteqP; split => x /=;
    by rewrite subr0 normrM normfV (gtr0_norm s0) ler_pdivlMr.
apply: le_trans (hX d (eta * s) _) _; first by rewrite mulr_ge0 // ltW.
rewrite lee_fin.
have e : (eta * s) ^+ 2 / (c * d%:R ^+ 2) = d%:R / (c / eta ^+ 2).
  rewrite /s !exprMn sqr_sqrtr ?ler0n //.
  have cn : c != 0 by rewrite gt_eqF.
  have en : eta != 0 by rewrite gt_eqF.
  have dn : d%:R != 0 :> R by rewrite gt_eqF.
  by field.
by rewrite mulNr e; exact: hD.
Qed.

End in_probability.

Arguments negligible {disp T} P E.
Arguments cvg_prob {disp T} P X l.
Arguments negligibleW {disp T P E F}.
Arguments negligibleU {disp T P E F}.
Arguments negligible_measurable {disp T P E}.
Arguments cvg_probP {disp T P X l}.
Arguments cvg_prob_eq {disp T P X Y l}.
Arguments cvg_prob_cst {disp T} P l.
Arguments cvg_probD {disp T P X Y x y}.
Arguments cvg_probN {disp T P X x}.
Arguments cvg_probB {disp T P X Y x y}.
Arguments cvg_probM {disp T P X Y x y}.
Arguments cvg_probV {disp T P X x}.
Arguments cvg_prob_sqrt {disp T P X x}.
Arguments cvg_prob_norm {disp T P X x}.
Arguments cvg_prob_squeeze {disp T P L X U l}.
Arguments cvg_prob_lipschitz {disp T P} f L {X x}.
Arguments cvg_prob_seq {disp T} P m l.
Arguments cvg_prob_center {disp T P X m l}.
Arguments cvg_prob_concentration {disp T} P X m c%_ring_scope.

Section law_transfer.
Context {disp1 disp2 : measure_display} (T1 : nat -> measurableType disp1)
  (T2 : nat -> measurableType disp2)
  (P1 : forall d, probability (T1 d) RR) (P2 : forall d, probability (T2 d) RR).

(* Convergence in probability depends only on the laws of the statistics
   for every large d. *)
Lemma cvg_prob_law (X1 : forall d, T1 d -> RR) (X2 : forall d, T2 d -> RR)
    (l : RR) :
  (forall d, measurable_fun setT (X1 d)) ->
  (forall d, measurable_fun setT (X2 d)) ->
  (exists D0 : nat, forall d, (D0 <= d)%N -> forall B : set RR, measurable B ->
     P1 d (X1 d @^-1` B) = P2 d (X2 d @^-1` B)) ->
  cvg_prob P2 X2 l -> cvg_prob P1 X1 l.
Proof.
move=> mX1 mX2 [D0 hL] h2 eta e0 eps p0.
have [D hD] := h2 eta e0 eps p0.
exists (maxn D0 D) => d; rewrite geq_max => /andP[d0 dD].
pose B := [set y : RR | eta <= `|y - l|].
have mB : measurable B.
  have mf : measurable_fun setT (fun y : RR => `|y - l|).
    apply: measurableT_comp; first exact: normr_measurable.
    by apply: measurable_funB; [exact: measurable_id | exact: measurable_cst].
  have := mf measurableT _ (measurable_itv `[eta, +oo[%R).
  rewrite setTI; congr (measurable _).
  by apply/seteqP; split => y /=; rewrite in_itv /= andbT.
have m1 : measurable (X1 d @^-1` B).
  by rewrite -[X in measurable X]setTI; exact: mX1.
have m2 : measurable (X2 d @^-1` B).
  by rewrite -[X in measurable X]setTI; exact: mX2.
exists (X1 d @^-1` B); split => //.
have [A [mA PA EA]] := hD d dD.
rewrite hL //; apply: le_trans PA.
by apply: le_measure => //; rewrite inE.
Qed.

End law_transfer.

Arguments cvg_prob_law {disp1 disp2 T1 T2} P1 P2 X1 X2 l.

(* The standard Gaussian vectors. *)

Section gauss_in_probability.
Variable m : nat -> nat.

Lemma negligible_gaussN (E : forall d, set 'rV[RR]_(m d)) :
  negligible (fun d => gauss (m d)) E ->
  negligible (fun d => gauss (m d)) (fun d => [set a | E d (- a)]).
Proof.
move=> hE eps e0; have [D hD] := hE eps e0.
exists D => d dD; have [A [mA PA EA]] := hD d dD.
have AE : [set a : 'rV[RR]_(m d) | A (- a)] = [set a | A (a *m (- 1%:M))].
  by apply/seteqP; split => a /=; rewrite mulmxN mulmx1.
exists [set a | A (- a)]; split.
- have mN : measurable_fun [set: 'rV[RR]_(m d)] (fun a => - a).
    by apply: measurable_oppmx; exact: measurable_id.
  by rewrite -[X in measurable X]setTI; exact: mN.
- rewrite AE (gauss_orthogonal_law _ mA) // mulmxN mulmx1.
  have -> : (- 1%:M : 'M[RR]_(m d))^T = - 1%:M.
    by apply/matrixP => i j; rewrite !mxE eq_sym.
  by rewrite opprK.
- by move=> a /= Ea; exact: EA.
Qed.

Lemma cvg_prob_gaussN (X : forall d, 'rV[RR]_(m d) -> RR) (l : RR) :
  cvg_prob (fun d => gauss (m d)) X l ->
  cvg_prob (fun d => gauss (m d)) (fun d a => X d (- a)) l.
Proof. by move=> hX eta e0; exact: (negligible_gaussN _ (hX eta e0)). Qed.

Variable n : nat -> nat.

Lemma negligible_gauss_rsubmx (E : forall d, set 'rV[RR]_(m d)) :
  negligible (fun d => gauss (m d)) E ->
  negligible (fun d => gauss (n d + m d)) (fun d => [set z | E d (rsubmx z)]).
Proof.
move=> hE eps e0; have [D hD] := hE eps e0.
exists D => d dD; have [A [mA PA EA]] := hD d dD.
exists (rsubmx @^-1` A); split.
- by rewrite -[X in measurable X]setTI; exact: measurable_rsubmx.
- by rewrite gauss_rsubmx.
- by move=> z /= Ez; exact: EA.
Qed.

Lemma negligible_gauss_lsubmx (E : forall d, set 'rV[RR]_(n d)) :
  negligible (fun d => gauss (n d)) E ->
  negligible (fun d => gauss (n d + m d)) (fun d => [set z | E d (lsubmx z)]).
Proof.
move=> hE eps e0; have [D hD] := hE eps e0.
exists D => d dD; have [A [mA PA EA]] := hD d dD.
exists (lsubmx @^-1` A); split.
- by rewrite -[X in measurable X]setTI; exact: measurable_lsubmx.
- by rewrite gauss_lsubmx.
- by move=> z /= Ez; exact: EA.
Qed.

Lemma cvg_prob_gauss_rsubmx (X : forall d, 'rV[RR]_(m d) -> RR) (l : RR) :
  cvg_prob (fun d => gauss (m d)) X l ->
  cvg_prob (fun d => gauss (n d + m d)) (fun d z => X d (rsubmx z)) l.
Proof. by move=> hX eta e0; exact: (negligible_gauss_rsubmx _ (hX eta e0)). Qed.

Lemma cvg_prob_gauss_lsubmx (X : forall d, 'rV[RR]_(n d) -> RR) (l : RR) :
  cvg_prob (fun d => gauss (n d)) X l ->
  cvg_prob (fun d => gauss (n d + m d)) (fun d z => X d (lsubmx z)) l.
Proof. by move=> hX eta e0; exact: (negligible_gauss_lsubmx _ (hX eta e0)). Qed.

End gauss_in_probability.

Arguments negligible_gaussN {m E}.
Arguments cvg_prob_gaussN {m X l}.
Arguments negligible_gauss_rsubmx {m n E}.
Arguments negligible_gauss_lsubmx {m n E}.
Arguments cvg_prob_gauss_rsubmx {m n X l}.
Arguments cvg_prob_gauss_lsubmx {m n X l}.
