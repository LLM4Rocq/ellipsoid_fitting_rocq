From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import matrix rat.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral hoelder probability.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.probability Require Import lindeberg moments.
From GaussianAnalysis.probability Require Import symmetrization efron_stein.

(**md**************************************************************************)
(* # The small-ball method                                                    *)
(*                                                                            *)
(* Mendelson's small-ball method, in the form of Koltchinskii and Mendelson   *)
(* (2015, Theorem 2.1), cited by Koehler and Sohn (arXiv 2608.27372, lines    *)
(* 4764-4779): a uniform lower bound for the empirical second moments of a    *)
(* class of functions, from a lower bound on its small-ball probabilities and *)
(* an upper bound on its Rademacher complexity. The deviation of the          *)
(* empirical process is controlled in expectation, by symmetrization and      *)
(* contraction (symmetrization.v), and then by Markov's inequality, so the    *)
(* probability of failure is of the order of the complexity: this suffices    *)
(* for limits in probability when the scale grows, and no bounded             *)
(* differences inequality is needed.                                          *)
(*                                                                            *)
(* Main results, for x of law tuple_prod mu n with n > 0:                     *)
(* - small_ball_method: for a sequence of measurable f_j, u > 0 and q > 0     *)
(*   with mu_k(|f_j| >= 2 u) >= q for all j and k < n, and r with             *)
(*     E rademacher_mean (max_(j < J) |(1/n) sum_k eps_k f_j(x_k)|) <= r      *)
(*   for every J, the event small_ball_event n f (n u^2 q / 2), that some     *)
(*   f_j has sum_k f_j(x_k)^2 < n u^2 q / 2, has probability at most          *)
(*   8 r / (u q). It is measurable (measurable_small_ball_event). Proof: the  *)
(*   ramp between u and 2 u, which is 1/u-Lipschitz (ramp_lipschitz),         *)
(*   symmetrization and contraction for the initial segment j < J, Markov's   *)
(*   inequality, and the continuity of measures along the union over J.       *)
(* - paley_zygmund_half: if E X^2 = 1 and E X^4 <= K, then                    *)
(*   P(|X| >= 1/2) >= 9 / (16 K) (paley_zygmund of moments.v for X^2).        *)
(* - dense_seq_rV: every nonempty set D of row vectors contains a sequence    *)
(*   that is dense in D, from rational approximations (rat_approx_rV).        *)
(* - small_ball_linear: let F : T -> 'rV[R]_N, S a square matrix, K > 0 and   *)
(*   D a set of row vectors such that, for p in D and k < n,                  *)
(*   E_k <F, p>^2 = p S p^T > 0 and E_k <F, p>^4 <= K (p S p^T)^2, where      *)
(*   <., .> is mxdot. If Psi is measurable in x, with                         *)
(*     |(1/n) sum_k eps_k <F(x_k), p>| <= sqrt (p S p^T) Psi(x, eps)          *)
(*   for p in D, and E rademacher_mean (Psi x) <= r, then there is a          *)
(*   measurable event of probability at most 512 K r / 9 outside of which     *)
(*     (1/n) sum_k <F(x_k), p>^2 >= 9 / (512 K) p S p^T                       *)
(*   for every p in D. Proof: small_ball_method for the normalized class on   *)
(*   a dense sequence of D, with u = 1/4 and q = 9 / (16 K) from              *)
(*   paley_zygmund_half, and the continuity of quadratic forms                *)
(*   (mxdot_form_lipschitz, mxdot_form_outer). Removing the ridge (Lemma      *)
(*   2.12) uses it with the features augmented by a constant coordinate       *)
(*   for the bias.                                                            *)
(* - Moments of affine images, used for the affine forms of Lemma 2.12:       *)
(*   integrable_pow4 (a finite fourth moment makes X and X^2 integrable),     *)
(*   integral_affine_sqr, E (X - b)^2 = E X^2 - 2 b E X + b^2,                *)
(*   integral_affine_pow4_le, E (X - b)^4 <= 8 (E X^4 + b^4), and             *)
(*   markov_ge0, P(Y > B) <= E Y / B for Y >= 0 and B > 0.                    *)
(*                                                                            *)
(* ```                                                                        *)
(*                    ramp u x == min 1 (max 0 (|x| / u - 1))                 *)
(*      small_ball_event n f c == the x : n.-tuple T for which some f_j has   *)
(*                                sum_k f_j(x_k)^2 < c                        *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ramp.
Context {R : realType}.

(* The ramp from 0 on [-u, u] to 1 outside ]-2 u, 2 u[. *)
Definition ramp (u x : R) : R := Num.min 1 (Num.max 0 (`|x| / u - 1)).

Lemma ramp_ge0 u x : 0 <= ramp u x.
Proof. by rewrite /ramp le_min ler01 le_max lexx. Qed.

Lemma ramp_le1 u x : ramp u x <= 1.
Proof. by rewrite /ramp ge_min lexx. Qed.

Lemma ramp0 u : ramp u 0 = 0.
Proof.
rewrite /ramp normr0 mul0r sub0r.
have -> : Num.max 0 (-1) = 0 :> R by apply/max_l; rewrite lerN10.
by apply/min_r; rewrite ler01.
Qed.

Lemma ramp1 u x : 0 < u -> 2 * u <= `|x| -> ramp u x = 1.
Proof.
move=> u0 hx; rewrite /ramp.
have h2 : 2 <= `|x| / u by rewrite ler_pdivlMr.
have -> : Num.max 0 (`|x| / u - 1) = `|x| / u - 1 by apply/max_r; lra.
by apply/min_l; lra.
Qed.

Lemma ramp_sqr u x : 0 < u -> u ^+ 2 * ramp u x <= x ^+ 2.
Proof.
move=> u0; have [xu|xu] := leP u `|x|.
  apply: (@le_trans _ _ (u ^+ 2)).
    by rewrite -[X in _ <= X]mulr1 ler_wpM2l ?sqr_ge0 ?ramp_le1.
  by rewrite -[x ^+ 2]real_normK ?num_real//; nra.
have h : `|x| / u - 1 < 0 by rewrite subr_lt0 ltr_pdivrMr// mul1r.
rewrite /ramp (max_l (ltW h)) (min_r ler01) mulr0.
exact: sqr_ge0.
Qed.

Lemma clamp01_lipschitz (a b : R) :
  `|Num.min 1 (Num.max 0 a) - Num.min 1 (Num.max 0 b)| <= `|a - b|.
Proof.
have cE (t : R) : Num.min 1 (Num.max 0 t) =
    (if t <= 0 then 0 else if t <= 1 then t else 1).
  case: (leP t 0) => t0; first by rewrite (min_r ler01).
  by case: (leP t 1).
have h1 : a - b <= `|a - b| := ler_norm _.
have h2 : b - a <= `|a - b| by rewrite distrC; exact: ler_norm.
rewrite !cE ler_norml.
by case: (leP a 0) => ha; case: (leP a 1) => ha1; case: (leP b 0) => hb;
  case: (leP b 1) => hb1; apply/andP; split; lra.
Qed.

Lemma ramp_lipschitz u x y : 0 < u ->
  `|ramp u x - ramp u y| <= u^-1 * `|x - y|.
Proof.
move=> u0; rewrite /ramp; apply: le_trans (clamp01_lipschitz _ _) _.
have -> : `|x| / u - 1 - (`|y| / u - 1) = (`|x| - `|y|) * u^-1.
  by rewrite mulrBl; ring.
have ui : 0 < u^-1 by rewrite invr_gt0.
rewrite normrM (gtr0_norm ui) mulrC.
by apply: ler_wpM2l; [exact: ltW|exact: ler_dist_dist].
Qed.

Lemma measurable_ramp u : measurable_fun [set: R] (ramp u).
Proof.
apply: measurable_minr; first exact: measurable_cst.
apply: measurable_maxr; first exact: measurable_cst.
apply: measurable_funB; last exact: measurable_cst.
by apply: measurable_funM; [exact: normr_measurable|exact: measurable_cst].
Qed.

End ramp.

Section small_ball_sequence.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* The event that some f_j has an empirical second moment below c / n. *)
Definition small_ball_event n (f : nat -> T -> R) (c : R) :=
  [set x : n.-tuple T | exists j, (\sum_(k < n) f j (tnth x k) ^+ 2 < c)%R].
Arguments small_ball_event : clear implicits.

Lemma measurable_small_ball_event n (f : nat -> T -> R) c :
  (forall j, measurable_fun [set: T] (f j)) ->
  measurable (small_ball_event n f c).
Proof.
move=> mf.
have mg j : measurable_fun [set: n.-tuple T]
    (fun x => \sum_(k < n) f j (tnth x k) ^+ 2)%R.
  apply: measurable_sum => k; apply: measurable_funX.
  exact: measurableT_comp (mf j) (measurable_tnth k).
have -> : small_ball_event n f c = \bigcup_j
    ((fun x : n.-tuple T => (\sum_(k < n) f j (tnth x k) ^+ 2)%R : R) @^-1`
      `]-oo, c[%classic).
  apply/seteqP; split => x /=.
    by case=> j h; exists j => //=; rewrite in_itv.
  by case=> j _ /=; rewrite in_itv /= => h; exists j.
apply: bigcupT_measurable => j; rewrite -[X in measurable X]setTI.
by apply: (mg j) => //; exact: measurable_itv.
Qed.

(* Mendelson's small-ball method in Markov form, for a sequence of
   functions. *)
Theorem small_ball_method (mu : nat -> probability T R) n
    (f : nat -> T -> R) (u q r : R) :
  (0 < n)%N -> (0 < u)%R -> (0 < q)%R ->
  (forall j, measurable_fun [set: T] (f j)) ->
  (forall j k, (k < n)%N -> q%:E <= mu k [set t | (2 * u <= `|f j t|)%R]) ->
  (forall J, \int[tuple_prod mu n]_x
     (rademacher_mean (fun s : n.-tuple bool => max_norm (fun j : 'I_J =>
        n%:R^-1 * \sum_(k < n) rademacher (tnth s k) * f j (tnth x k))))%:E
     <= r%:E) ->
  tuple_prod mu n (small_ball_event n f (n%:R * (u ^+ 2 * q / 2))) <=
    (8 * r / (u * q))%:E.
Proof.
move=> n0 u0 q0 mf fq fr.
set c := (n%:R * (u ^+ 2 * q / 2))%R.
have nR : (0 < n%:R :> R)%R by rewrite ltr0n.
(* the events for the initial segments of the sequence *)
pose A J := [set x : n.-tuple T |
  exists2 j, (j < J)%N & (\sum_(k < n) f j (tnth x k) ^+ 2 < c)%R].
have mg j : measurable_fun [set: n.-tuple T]
    (fun x => \sum_(k < n) f j (tnth x k) ^+ 2)%R.
  apply: measurable_sum => k; apply: measurable_funX.
  exact: measurableT_comp (mf j) (measurable_tnth k).
have mA J : measurable (A J).
  have -> : A J = \bigcup_(j in [set j | (j < J)%N])
      ((fun x : n.-tuple T => (\sum_(k < n) f j (tnth x k) ^+ 2)%R : R) @^-1`
        `]-oo, c[%classic).
    apply/seteqP; split => x /=.
      by case=> j jJ h; exists j => //=; rewrite in_itv.
    by case=> j /= jJ; rewrite in_itv /= => h; exists j.
  apply: bigcup_measurable => j _; rewrite -[X in measurable X]setTI.
  by apply: (mg j) => //; exact: measurable_itv.
have AJ J : tuple_prod mu n (A J) <= (8 * r / (u * q))%:E.
  (* the ramps h j of the f j, with E h j >= q *)
  pose h (j : 'I_J) : T -> R := ramp u \o f j.
  have mh j : measurable_fun [set: T] (h j).
    exact: measurableT_comp (measurable_ramp u) (mf j).
  have hi j k : (mu k).-integrable [set: T] (EFin \o h j).
    apply: (@bounded_integrable _ _ _ _ _ 1 (mh j)) => t.
    by rewrite /h /= ger0_norm ?ramp_ge0 ?ramp_le1.
  have Eh j k : (k < n)%N -> (q <= \int[mu k]_t h j t)%R.
    move=> kn.
    have mS : measurable [set t | (2 * u <= `|f j t|)%R].
      rewrite -[X in measurable X]setTI.
      exact: (measurable_fun_ler (measurable_cst (2 * u)%R)
        (measurableT_comp (@normr_measurable R setT) (mf j)) measurableT).
    have : q%:E <= \int[mu k]_t (h j t)%:E.
      apply: le_trans (fq j k kn) _.
      rewrite -[X in mu k X]setIT -integral_indic//.
      apply: ge0_le_integral => //.
      - exact/measurable_EFinP/measurable_indic.
      - exact/measurable_EFinP.
      - move=> t _; rewrite lee_fin indicE /h /=.
        case: (t \in _) / boolP => tS; last by rewrite ramp_ge0.
        by rewrite (ramp1 u0)//; move: tS; rewrite inE.
    move=> hq; rewrite /Rintegral -lee_fin fineK//.
    exact: integrable_fin_num (hi j k).
  (* the supremum of the empirical process of the h j *)
  pose D x := max_norm (fun j : 'I_J =>
    \sum_(k < n) (h j (tnth x k) - \int[mu k]_t h j t))%R.
  have mD : measurable_fun [set: n.-tuple T] D.
    apply: measurable_max_norm => j; apply: measurable_sum => k.
    apply: measurable_funB; last exact: measurable_cst.
    exact: measurableT_comp (mh j) (measurable_tnth k).
  have sym := @symmetrization _ _ _ mu n J h mh hi.
  have max_normZ m (v : 'I_m -> R) (a : R) : (0 <= a)%R ->
      max_norm (fun j => a * v j)%R = (a * max_norm v)%R.
    move=> a0; rewrite /max_norm -bigmax0_pM//.
    by apply: eq_bigr => j _; rewrite normrM (ger0_norm a0).
  pose G x := rademacher_mean (fun s : n.-tuple bool =>
    max_norm (fun j : 'I_J =>
      n%:R^-1 * \sum_(k < n) rademacher (tnth s k) * f j (tnth x k)))%R.
  have eG x : (rademacher_mean (fun s : n.-tuple bool =>
      max_norm (fun j : 'I_J =>
        \sum_(k < n) rademacher (tnth s k) * f j (tnth x k))) =
      n%:R * G x)%R.
    rewrite /G; under [in RHS]eq_fun do rewrite max_normZ ?invr_ge0//.
    by rewrite rademacher_meanZ mulrA mulfV ?mul1r// gt_eqF.
  (* contraction *)
  have ui : (0 < u^-1)%R by rewrite invr_gt0.
  have hG x : (rademacher_mean (fun s : n.-tuple bool =>
      max_norm (fun j : 'I_J =>
        \sum_(k < n) rademacher (tnth s k) * h j (tnth x k))) <=
      2 * u^-1 * (n%:R * G x))%R.
    rewrite -eG.
    exact: (@contraction R n J (fun j k => f j (tnth x k)) (fun=> ramp u) u^-1
      (ltW ui) (fun _ _ _ => ramp_lipschitz _ _ u0) (fun _ => ramp0 u)).
  have mG : measurable_fun [set: n.-tuple T] G.
    apply: measurable_rademacher_mean => s; apply: measurable_max_norm => j.
    apply: measurable_funM; first exact: measurable_cst.
    apply: measurable_sum => k.
    apply: measurable_funM; first exact: measurable_cst.
    exact: measurableT_comp (mf j) (measurable_tnth k).
  have G0 x : (0 <= G x)%R.
    by apply: rademacher_mean_ge0 => s; exact: max_norm_ge0.
  have mRh : measurable_fun [set: n.-tuple T] (fun x =>
      rademacher_mean (fun s : n.-tuple bool => max_norm (fun j : 'I_J =>
        \sum_(k < n) rademacher (tnth s k) * h j (tnth x k))))%R.
    apply: measurable_rademacher_mean => s; apply: measurable_max_norm => j.
    apply: measurable_sum => k.
    apply: measurable_funM; first exact: measurable_cst.
    exact: measurableT_comp (mh j) (measurable_tnth k).
  have ED : \int[tuple_prod mu n]_x (D x)%:E <= (4 / u * n%:R * r)%:E.
    apply: le_trans sym _.
    have k0 : (0 <= 2 / u * n%:R)%R by rewrite mulr_ge0// ?divr_ge0// ltW.
    apply: (@le_trans _ _
      (2%:E * \int[tuple_prod mu n]_x ((2 / u * n%:R) * G x)%:E)).
      apply: lee_wpmul2l => //; apply: ge0_le_integral => //.
      - move=> x _; rewrite lee_fin rademacher_mean_ge0// => s.
        exact: max_norm_ge0.
      - exact/measurable_EFinP.
      - by apply/measurable_EFinP; apply: measurable_funM.
      - by move=> x _; rewrite lee_fin -mulrA; exact: hG.
    under eq_integral do rewrite EFinM.
    rewrite ge0_integralZl_EFin//; first last.
    - apply: (@le_trans _ _ (2%:E * ((2 / u * n%:R)%:E * r%:E))).
        apply: lee_wpmul2l => //; apply: lee_wpmul2l; first by rewrite lee_fin.
        exact: fr J.
      by rewrite -!EFinM lee_fin; lra.
    - exact/measurable_EFinP.
    - by move=> x _; rewrite lee_fin.
  (* on A J, D is at least n q / 2 *)
  have DA x : A J x -> (n%:R * q / 2 <= D x)%R.
    case=> j jJ hj.
    apply: le_trans (ler_max_norm _ (Ordinal jJ)).
    set S1 := (\sum_(k < n) h (Ordinal jJ) (tnth x k))%R.
    set S2 := (\sum_(k < n) \int[mu k]_t h (Ordinal jJ) t)%R.
    have e1 : (u ^+ 2 * S1 <= \sum_(k < n) f j (tnth x k) ^+ 2)%R.
      by rewrite /S1 mulr_sumr; apply: ler_sum => k _; exact: ramp_sqr.
    have e2 : (n%:R * q <= S2)%R.
      have -> : (n%:R * q = \sum_(k < n) q)%R.
        by rewrite sumr_const card_ord mulr_natl.
      by apply: ler_sum => k _; exact: Eh (ltn_ord k).
    have e3 : (S1 < n%:R * q / 2)%R.
      rewrite -(ltr_pM2l (exprn_gt0 2 u0)); apply: le_lt_trans e1 _.
      apply: lt_le_trans hj _; rewrite /c le_eqVlt; apply/orP; left.
      by apply/eqP; ring.
    rewrite sumrB -/S1 -/S2 distrC.
    by apply: le_trans (ler_norm _); lra.
  (* Markov's inequality *)
  have mark : (n%:R * q / 2)%:E * tuple_prod mu n (A J) <=
      \int[tuple_prod mu n]_x (D x)%:E.
    rewrite -[X in _ * tuple_prod mu n X]setIT -integral_indic//.
    rewrite -ge0_integralZl_EFin//; first last.
    - apply: ge0_le_integral => //.
      + move=> x _; rewrite -EFinM lee_fin mulr_ge0 ?indicE//.
        by rewrite divr_ge0// mulr_ge0// ltW.
      + apply: emeasurable_funM; first exact: measurable_cst.
        exact/measurable_EFinP/measurable_indic.
      + exact/measurable_EFinP.
      + move=> x _; rewrite -EFinM lee_fin indicE.
        case: (x \in A J) / boolP => xA; last by rewrite mulr0 max_norm_ge0.
        by rewrite mulr1; apply: DA; rewrite inE in xA.
    - by rewrite divr_ge0// mulr_ge0// ltW.
    - exact/measurable_EFinP/measurable_indic.
  have hP := le_trans mark ED.
  have pfin : tuple_prod mu n (A J) \is a fin_num by apply: fin_num_measure.
  move: hP; rewrite -(fineK pfin) -EFinM !lee_fin.
  set p := fine (tuple_prod mu n (A J)) => hP.
  have une : u != 0%R by rewrite gt_eqF.
  have h1 : (u * (n%:R * q / 2 * p) <= u * (4 / u * n%:R * r))%R.
    by rewrite ler_pM2l.
  have e1 : (u * (n%:R * q / 2 * p) = n%:R / 2 * (p * (u * q)))%R by ring.
  have e2 : (u * (4 / u * n%:R * r) = n%:R / 2 * (8 * r))%R by field.
  rewrite e1 e2 ler_pM2l ?divr_gt0// in h1.
  by rewrite ler_pdivlMr// mulr_gt0.
(* the union of the increasing events *)
have -> : small_ball_event n f c = \bigcup_J A J.
  apply/seteqP; split => x /=.
    by case=> j h; exists j.+1 => //; exists j.
  by case=> J _ [j _ h]; exists j.
have ndA : nondecreasing_seq A.
  move=> J K JK; apply/subsetPset => x [j jJ h].
  by exists j => //; exact: leq_trans jJ JK.
have hc := nondecreasing_cvg_mu (mu := tuple_prod mu n) mA
  (bigcupT_measurable A mA) ndA.
rewrite -(cvg_lim _ hc)//.
apply: lime_le; first by apply/cvg_ex; eexists; exact: hc.
by apply: nearW => J; exact: AJ.
Qed.

End small_ball_sequence.
Arguments small_ball_event {d T R} n f c.

Section dense_subset.
Context {R : realType}.

Lemma rat_approx_rV N (x : 'rV[R]_N) (e : R) : 0 < e ->
  exists q : 'rV[rat]_N, frobenius (x - map_mx ratr q) < e.
Proof.
move=> e0; pose del := e / N.+1%:R.
have del0 : 0 < del by rewrite divr_gt0.
have hex i : exists q : rat, `|x 0 i - ratr q| < del.
  have xi : x 0 i - del < x 0 i + del by rewrite ltrD2l gtrN.
  have [q] := rat_in_itvoo xi; rewrite in_itv /= => /andP[h1 h2].
  by exists q; rewrite ltr_distlC h1 h2.
have [qf hq] := fin_all_exists hex.
exists (\row_i qf i).
rewrite /frobenius -[X in _ < X](ger0_norm (ltW e0)) -sqrtr_sqr.
rewrite ltr_sqrt ?exprn_gt0// /mxdot big_ord1.
apply: (@le_lt_trans _ _ (\sum_(j < N) del ^+ 2)).
  apply: ler_sum => j _; rewrite !mxE.
  have h := hq j; have h0 := normr_ge0 (x 0 j - ratr (qf j)).
  by rewrite -expr2 -real_normK ?num_real//; nra.
rewrite sumr_const card_ord -mulr_natl /del expr_div_n mulrA.
rewrite ltr_pdivrMr ?exprn_gt0 ?ltr0Sn// mulrC ltr_pM2l ?exprn_gt0//.
have n0 : (0 <= N%:R :> R) by [].
by rewrite -natr1; nra.
Qed.

(* Every nonempty set of row vectors has a dense sequence of its points. *)
Lemma dense_seq_rV N (D : set 'rV[R]_N) : D !=set0 ->
  exists p : nat -> 'rV[R]_N, (forall j, D (p j)) /\
    forall x, D x -> forall e, 0 < e -> exists j, frobenius (p j - x) < e.
Proof.
case=> p0 Dp0.
(* a point of D in the ball of center q and radius 1 / (m + 1), if any *)
pose c (qm : 'rV[rat]_N * nat) := xget p0
  [set y | D y /\ frobenius (y - map_mx ratr qm.1) < qm.2.+1%:R^-1].
pose p j := if unpickle j is Some qm then c qm else p0.
exists p; split.
  move=> j; rewrite /p; case: (unpickle j) => [qm|//].
  by rewrite /c; case: xgetP => [y _ []|].
move=> x Dx e e0.
pose m := archimedean.Num.truncn (2 / e).
have hm : 2 * m.+1%:R^-1 < e.
  rewrite ltr_pdivrMr ?ltr0Sn//.
  have := archimedean.Num.Theory.truncnS_gt (2 / e).
  by rewrite ltr_pdivrMr// mulrC.
have m0 : 0 < m.+1%:R^-1 :> R by rewrite invr_gt0 ltr0Sn.
have [q hq] := rat_approx_rV x m0.
exists (pickle (q, m)); rewrite /p pickleK /c.
have ex : exists y, [set y | D y /\
    frobenius (y - map_mx ratr (q, m).1) < (q, m).2.+1%:R^-1] y.
  by exists x; split => //; rewrite -frobeniusN opprB.
have [Dy hy] := xgetPex p0 ex.
set y := xget p0 _ in Dy hy *.
have -> : y - x = (y - map_mx ratr q) + (map_mx ratr q - x).
  by rewrite addrA subrK.
apply: le_lt_trans (frobeniusD _ _) _.
move: hq; rewrite -frobeniusN opprB => hq.
have hy' : frobenius (y - map_mx ratr q) < m.+1%:R^-1 := hy.
by have := ltrD hy' hq; move: hm; set a := m.+1%:R^-1; lra.
Qed.

(* Quadratic forms are Lipschitz on bounded sets. *)
Lemma mxdot_form_lipschitz N (Q : 'M[R]_N) (p p' : 'rV[R]_N) :
  `|mxdot (p *m Q) p - mxdot (p' *m Q) p'| <=
    frobenius Q * (frobenius p + frobenius p') * frobenius (p - p').
Proof.
have -> : mxdot (p *m Q) p - mxdot (p' *m Q) p' =
    mxdot ((p - p') *m Q) p + mxdot (p' *m Q) (p - p').
  by rewrite mulmxBl mxdotBl mxdotBr addrA subrK.
apply: le_trans (ler_normD _ _) _.
have h1 : `|mxdot ((p - p') *m Q) p| <=
    frobenius (p - p') * frobenius Q * frobenius p.
  apply: le_trans (mxdot_le _ _) _; rewrite ler_wpM2r ?frobenius_ge0//.
  exact: frobenius_mulmx.
have h2 : `|mxdot (p' *m Q) (p - p')| <=
    frobenius p' * frobenius Q * frobenius (p - p').
  apply: le_trans (mxdot_le _ _) _; rewrite ler_wpM2r ?frobenius_ge0//.
  exact: frobenius_mulmx.
apply: le_trans (lerD h1 h2) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

Lemma mxdot_form_outer N (a q : 'rV[R]_N) :
  mxdot (q *m (a^T *m a)) q = mxdot a q ^+ 2.
Proof.
rewrite mxdot_mulmxl.
have -> : a^T *m a = a^T *m (a^T)^T by rewrite trmxK.
have -> : q^T *m q = q^T *m (q^T)^T by rewrite trmxK.
by rewrite mxdot_outer2 mxdot_trmx expr2.
Qed.

End dense_subset.

Section small_ball_paley_zygmund.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* A small-ball probability from the second and fourth moments. *)
Lemma paley_zygmund_half (P : probability T R) (X : T -> R) (K : R) :
  measurable_fun [set: T] X -> (0 < K)%R ->
  \int[P]_t (X t ^+ 2)%:E = 1 -> \int[P]_t (X t ^+ 4)%:E <= K%:E ->
  (9 / (16 * K))%:E <= P [set t | (2^-1 <= `|X t|)%R].
Proof.
move=> mX K0 h2 h4.
pose Y t := (X t ^+ 2)%R.
have mY : measurable_fun [set: T] Y by apply: measurable_funX.
have eY2 t : (Y t ^+ 2 = X t ^+ 4)%R by rewrite /Y -exprM.
have iY2 : P.-integrable [set: T] (EFin \o (fun t => Y t ^+ 2)%R).
  apply/integrableP; split.
    by apply/measurable_EFinP; apply: measurable_funX.
  under eq_integral do rewrite /= eY2 ger0_norm ?exprn_even_ge0//.
  by apply: le_lt_trans h4 _; exact: ltry.
have Y2 : Y \in Lfun P 2%:E by apply: integrable_sqr_Lfun2.
have EY : 'E_P[Y] = 1 by rewrite unlock.
have EY2 : 'E_P[(Y ^+ 2)] = \int[P]_t (X t ^+ 4)%:E.
  by rewrite unlock; apply: eq_integral => t _; rewrite exprfctE eY2.
have m1 : (1 <= fine 'E_P[(Y ^+ 2)])%R.
  by have := expectation_sqr_le Y2; rewrite EY /= expr1n.
have mK : (fine 'E_P[(Y ^+ 2)] <= K)%R.
  rewrite EY2.
  have h0 : 0 <= \int[P]_t (X t ^+ 4)%:E.
    by apply: integral_ge0 => t _; rewrite lee_fin exprn_even_ge0.
  have fin : \int[P]_t (X t ^+ 4)%:E \is a fin_num.
    by rewrite ge0_fin_numE// (le_lt_trans h4)// ltry.
  by rewrite -lee_fin fineK.
(* Paley-Zygmund for X^2 at 1/4 *)
have q0 : (0 <= 4^-1 :> R)%R by rewrite invr_ge0.
have q1 : (4^-1)%:E < 'E_P[Y] by rewrite EY lte_fin invf_lt1// ltr1n.
have pz := @paley_zygmund _ _ _ P Y 4^-1 Y2 q0 q1.
have e4 : (4^-1 = (2^-1) ^+ 2 :> R)%R by field.
have hX t : (4^-1 <= X t ^+ 2)%R = (2^-1 <= `|X t|)%R.
  rewrite e4 -[(X t ^+ 2)%R]real_normK ?num_real//.
  by rewrite ler_sqr ?nnegrE ?invr_ge0.
have -> : [set t | (2^-1 <= `|X t|)%R] = [set x | (4^-1 <= Y x)%R].
  by apply/seteqP; split => t /=; rewrite /Y hX.
apply: le_trans pz; rewrite EY lee_fin /=.
set m4 := fine 'E_P[(Y ^+ 2)] in m1 mK *.
have m40 : (0 < m4)%R by apply: lt_le_trans m1; exact: ltr01.
have m4ne : m4 != 0%R by rewrite gt_eqF.
have Kne : K != 0%R by rewrite gt_eqF.
have -> : ((1 - 4^-1) ^+ 2 / m4 = 9 / 16 * m4^-1 :> R)%R by field.
have -> : (9 / (16 * K) = 9 / 16 * K^-1 :> R)%R by field.
by rewrite ler_wpM2l// lef_pV2// posrE.
Qed.

End small_ball_paley_zygmund.

Section small_ball_linear.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* The small-ball method for a linear class with comparable second and
   fourth moments. *)
Theorem small_ball_linear (mu : nat -> probability T R) (n N : nat)
    (F : T -> 'rV[R]_N) (S : 'M[R]_N) (D : set 'rV[R]_N) (K r : R)
    (Psi : n.-tuple T -> n.-tuple bool -> R) :
  (0 < n)%N -> (0 < K)%R -> (0 <= r)%R ->
  (forall p, measurable_fun [set: T] (fun t => mxdot (F t) p)) ->
  (forall p, D p -> 0 < mxdot (p *m S) p)%R ->
  (forall p k, D p -> (k < n)%N ->
     \int[mu k]_t (mxdot (F t) p ^+ 2)%:E = (mxdot (p *m S) p)%:E) ->
  (forall p k, D p -> (k < n)%N ->
     \int[mu k]_t (mxdot (F t) p ^+ 4)%:E <= (K * mxdot (p *m S) p ^+ 2)%:E) ->
  (forall s, measurable_fun [set: n.-tuple T] (Psi ^~ s)) ->
  (forall x s p, D p ->
     `|n%:R^-1 * \sum_(k < n) rademacher (tnth s k) * mxdot (F (tnth x k)) p|
       <= Num.sqrt (mxdot (p *m S) p) * Psi x s)%R ->
  \int[tuple_prod mu n]_x (rademacher_mean (Psi x))%:E <= r%:E ->
  exists E : set (n.-tuple T), [/\ measurable E,
    tuple_prod mu n E <= (512 * K * r / 9)%:E &
    forall x, ~ E x -> forall p, D p ->
      (9 / (512 * K) * mxdot (p *m S) p <=
       n%:R^-1 * \sum_(k < n) mxdot (F (tnth x k)) p ^+ 2)%R].
Proof.
move=> n0 K0 r0 mF Sp h2 h4 mPsi hPsi hr.
have [DN|DE] := pselect (D !=set0); last first.
  exists set0; split => //.
    rewrite measure0 lee_fin; apply: divr_ge0; last exact: ler0n.
    apply: mulr_ge0; last exact: r0.
    by apply: mulr_ge0; [exact: ler0n|exact: ltW].
  by move=> x _ p Dp; exfalso; apply: DE; exists p.
(* the class f j = <F, p_j> / sqrt (v p_j) on a dense sequence of D *)
have [pj [Dpj dense]] := dense_seq_rV DN.
pose v (p : 'rV[R]_N) := mxdot (p *m S) p.
have v0 j : (0 < v (pj j))%R by apply: Sp.
pose f j t := (mxdot (F t) (pj j) / Num.sqrt (v (pj j)))%R.
have mf j : measurable_fun [set: T] (f j).
  apply: measurable_funM; first exact: mF.
  exact: measurable_cst.
have vne j : (v (pj j) != 0)%R by rewrite gt_eqF.
have ef2 j t : (f j t ^+ 2 = (v (pj j))^-1 * mxdot (F t) (pj j) ^+ 2)%R.
  by rewrite /f expr_div_n sqr_sqrtr ?(ltW (v0 j))// mulrC.
have ef4 j t : (f j t ^+ 4 = (v (pj j) ^+ 2)^-1 * mxdot (F t) (pj j) ^+ 4)%R.
  rewrite /f expr_div_n mulrC; congr (_^-1 * _)%R.
  by rewrite (_ : 4%N = (2 * 2)%N)// exprM sqr_sqrtr ?(ltW (v0 j)).
have Ef2 j k : (k < n)%N -> \int[mu k]_t (f j t ^+ 2)%:E = 1.
  move=> kn; under eq_integral do rewrite ef2 EFinM.
  rewrite ge0_integralZl_EFin; first last.
  - by rewrite (h2 _ _ (Dpj j) kn) -EFinM mulVf.
  - by rewrite invr_ge0 ltW.
  - by apply/measurable_EFinP; apply: measurable_funX.
  - by move=> t _; rewrite lee_fin exprn_even_ge0.
  - exact: measurableT.
have Ef4 j k : (k < n)%N -> \int[mu k]_t (f j t ^+ 4)%:E <= K%:E.
  move=> kn; under eq_integral do rewrite ef4 EFinM.
  rewrite ge0_integralZl_EFin; first last.
  - apply: le_trans (lee_wpmul2l _ (h4 _ _ (Dpj j) kn)) _.
      by rewrite lee_fin invr_ge0 exprn_even_ge0.
    rewrite -EFinM lee_fin mulrCA mulVf ?mulr1//.
    by rewrite expf_neq0.
  - by rewrite invr_ge0 exprn_even_ge0.
  - by apply/measurable_EFinP; apply: measurable_funX.
  - by move=> t _; rewrite lee_fin exprn_even_ge0.
  - exact: measurableT.
(* the small-ball condition, by Paley-Zygmund *)
have fq j k : (k < n)%N ->
    (9 / (16 * K))%:E <= mu k [set t | (2 * 4^-1 <= `|f j t|)%R].
  move=> kn; have -> : (2 * 4^-1 = 2^-1 :> R)%R by field.
  exact: paley_zygmund_half (mf j) K0 (Ef2 j k kn) (Ef4 j k kn).
(* the Rademacher complexity of the initial segments *)
have [p0 Dp0] := DN.
have Psi0 x s : (0 <= Psi x s)%R.
  have sp : (0 < Num.sqrt (v p0))%R by rewrite sqrtr_gt0; exact: Sp.
  rewrite -(pmulr_rge0 _ sp).
  exact: le_trans (normr_ge0 _) (hPsi x s p0 Dp0).
have fj x s j :
    (`|n%:R^-1 * \sum_(k < n) rademacher (tnth s k) * f j (tnth x k)|
      <= Psi x s)%R.
  have sp : (0 < Num.sqrt (v (pj j)))%R by rewrite sqrtr_gt0.
  have -> : (n%:R^-1 * \sum_(k < n) rademacher (tnth s k) * f j (tnth x k) =
      (n%:R^-1 *
        \sum_(k < n) rademacher (tnth s k) * mxdot (F (tnth x k)) (pj j))
        / Num.sqrt (v (pj j)))%R.
    rewrite -mulrA mulr_suml; congr (_ * _)%R.
    by apply: eq_bigr => k _; rewrite mulrA.
  have spi : (0 < (Num.sqrt (v (pj j)))^-1)%R by rewrite invr_gt0.
  rewrite normrM (gtr0_norm spi) ler_pdivrMr// [X in (_ <= X)%R]mulrC.
  exact: hPsi.
have fr J : \int[tuple_prod mu n]_x (rademacher_mean (fun s : n.-tuple bool =>
    max_norm (fun j : 'I_J =>
      n%:R^-1 * \sum_(k < n) rademacher (tnth s k) * f j (tnth x k))))%:E
    <= r%:E.
  apply: le_trans hr; apply: ge0_le_integral.
  - exact: measurableT.
  - move=> x _; rewrite lee_fin; apply: rademacher_mean_ge0 => s.
    exact: max_norm_ge0.
  - apply/measurable_EFinP; apply: measurable_rademacher_mean => s.
    apply: measurable_max_norm => j.
    apply: measurable_funM; first exact: measurable_cst.
    apply: measurable_sum => k.
    apply: measurable_funM; first exact: measurable_cst.
    exact: measurableT_comp (mf j) (measurable_tnth k).
  - by apply/measurable_EFinP; apply: measurable_rademacher_mean.
  - move=> x _; rewrite lee_fin; apply: ler_rademacher_mean => s.
    rewrite /max_norm; apply: bigmax_le => [|j _]; first exact: Psi0.
    exact: fj.
(* the small-ball method for the sequence *)
have u0 : (0 < 4^-1 :> R)%R by rewrite invr_gt0.
have q0 : (0 < 9 / (16 * K) :> R)%R by rewrite divr_gt0// mulr_gt0.
have sb := small_ball_method n0 u0 q0 mf fq fr.
have Kne : K != 0%R by rewrite gt_eqF.
exists (small_ball_event n f (n%:R * ((4^-1) ^+ 2 * (9 / (16 * K)) / 2))).
split.
- exact: measurable_small_ball_event mf.
- apply: le_trans sb _; rewrite lee_fin le_eqVlt; apply/orP; left.
  by apply/eqP; field.
move=> x Ex p Dp.
set c' := (9 / (512 * K))%R.
have nR : (0 < n%:R :> R)%R by rewrite ltr0n.
have nne : (n%:R != 0 :> R)%R by rewrite gt_eqF.
have hj j : (c' * v (pj j) <=
    n%:R^-1 * \sum_(k < n) mxdot (F (tnth x k)) (pj j) ^+ 2)%R.
  have : ~ (\sum_(k < n) f j (tnth x k) ^+ 2 <
      n%:R * ((4^-1) ^+ 2 * (9 / (16 * K)) / 2))%R.
    by move=> h; apply: Ex; exists j.
  move/negP; rewrite -leNgt.
  under eq_bigr do rewrite ef2.
  rewrite -mulr_sumr => h.
  have := ler_wpM2l (ltW (divr_gt0 (v0 j) nR)) h.
  have e1 : (v (pj j) / n%:R * (n%:R * ((4^-1) ^+ 2 * (9 / (16 * K)) / 2)) =
      c' * v (pj j))%R by rewrite /c'; field.
  have e2 : (v (pj j) / n%:R * ((v (pj j))^-1 *
      \sum_(k < n) mxdot (F (tnth x k)) (pj j) ^+ 2) =
      n%:R^-1 * \sum_(k < n) mxdot (F (tnth x k)) (pj j) ^+ 2)%R by field.
  by rewrite e1 e2.
(* extension to D by density: the gap is a quadratic form *)
pose Q := (n%:R^-1 *: \sum_(k < n) ((F (tnth x k))^T *m F (tnth x k))
  - c' *: S)%R.
have gQ (q : 'rV[R]_N) : (n%:R^-1 * \sum_(k < n) mxdot (F (tnth x k)) q ^+ 2
    - c' * v q = mxdot (q *m Q) q)%R.
  rewrite /Q /v mulmxBr mxdotBl -!scalemxAr !mxdotZl mulmx_sumr mxdot_suml.
  by under [in RHS]eq_bigr do rewrite mxdot_form_outer.
have gj j : (0 <= mxdot (pj j *m Q) (pj j))%R by rewrite -gQ subr_ge0 hj.
suff : (0 <= mxdot (p *m Q) p)%R by rewrite -gQ subr_ge0.
apply/ler_addgt0Pr => e e0.
pose M := (frobenius Q * (2 * frobenius p + 1) + 1)%R.
have M0 : (0 < M)%R.
  rewrite /M ltr_pwDr// mulr_ge0 ?frobenius_ge0//.
  by rewrite addr_ge0// mulr_ge0// frobenius_ge0.
have eM : (0 < Num.min 1 (e / M))%R by rewrite lt_min ltr01 divr_gt0.
have [j hj'] := dense p Dp _ eM.
have hd1 : (frobenius (pj j - p) < 1)%R.
  by apply: lt_le_trans hj' _; rewrite ge_min lexx.
have hd2 : (frobenius (pj j - p) < e / M)%R.
  by apply: lt_le_trans hj' _; rewrite ge_min lexx orbT.
have hpj : (frobenius (pj j) <= frobenius p + 1)%R.
  have -> : pj j = (pj j - p + p)%R by rewrite subrK.
  by apply: le_trans (frobeniusD _ _) _; lra.
have L := mxdot_form_lipschitz Q (pj j) p.
have h1 : (frobenius Q * (frobenius (pj j) + frobenius p) <= M)%R.
  rewrite /M; apply: (@le_trans _ _ (frobenius Q * (2 * frobenius p + 1))%R).
    by apply: ler_wpM2l; [exact: frobenius_ge0|lra].
  by rewrite lerDl.
have h2' : (frobenius Q * (frobenius (pj j) + frobenius p) *
    frobenius (pj j - p) <= M * frobenius (pj j - p))%R.
  by apply: ler_wpM2r; [exact: frobenius_ge0|exact: h1].
have h3 : (M * frobenius (pj j - p) < e)%R.
  by rewrite mulrC -ltr_pdivlMr.
have := le_lt_trans (le_trans L h2') h3.
by rewrite ltr_norml => /andP[_]; have := gj j; lra.
Qed.

End small_ball_linear.

Section affine_moments.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

(* A finite fourth moment gives integrable first and second powers. *)
Lemma integrable_pow4 (X : T -> R) : measurable_fun [set: T] X ->
  \int[P]_t (X t ^+ 4)%:E < +oo ->
  P.-integrable [set: T] (EFin \o X) /\
  P.-integrable [set: T] (EFin \o (fun t => X t ^+ 2)%R).
Proof.
move=> mX X4.
have mX4 : measurable_fun [set: T] (fun t => X t ^+ 4)%R.
  exact: measurable_funX.
have i4 : P.-integrable [set: T] (EFin \o (fun t => X t ^+ 4)%R).
  apply/integrableP; split; first exact/measurable_EFinP.
  under eq_integral do rewrite /= ger0_norm ?exprn_even_ge0//.
  exact: X4.
have i14 : P.-integrable [set: T] (EFin \o (fun t => 1 + X t ^+ 4)%R).
  have -> : EFin \o (fun t => 1 + X t ^+ 4)%R =
      (fun t => 1%:E) \+ (EFin \o (fun t => X t ^+ 4)%R).
    by apply/funext => t; rewrite /= EFinD.
  by apply: integrableD => //; exact: finite_measure_integrable_cst.
split.
  apply: (le_integrable _ _ _ i14) => //; first exact/measurable_EFinP.
  move=> t _ /=; rewrite !lee_fin.
  rewrite [X in (_ <= X)%R]ger0_norm ?addr_ge0 ?exprn_even_ge0//.
  have a0 := normr_ge0 (X t).
  rewrite -[(X t ^+ 4)%R](@ger0_norm _ (X t ^+ 4)%R) ?exprn_even_ge0//.
  rewrite normrX; have := sqr_ge0 (`|X t| ^+ 2 - 2^-1)%R.
  by have := sqr_ge0 (`|X t| - 2^-1)%R; nra.
apply: (le_integrable _ _ _ i14) => //.
  by apply/measurable_EFinP; exact: measurable_funX.
move=> t _ /=; rewrite !lee_fin !ger0_norm ?addr_ge0 ?exprn_even_ge0//.
by have := sqr_ge0 (X t ^+ 2 - 2^-1)%R; nra.
Qed.

Lemma integral_affine_sqr (X : T -> R) (b : R) :
  P.-integrable [set: T] (EFin \o X) ->
  P.-integrable [set: T] (EFin \o (fun t => X t ^+ 2)%R) ->
  \int[P]_t ((X t - b) ^+ 2)%:E =
  \int[P]_t (X t ^+ 2)%:E - (2 * b)%:E * \int[P]_t (X t)%:E + (b ^+ 2)%:E.
Proof.
move=> i1 i2.
have i3 : P.-integrable [set: T] (EFin \o (fun t => - (2 * b) * X t)%R).
  have -> : EFin \o (fun t => - (2 * b) * X t)%R =
      (fun t => (- (2 * b))%:E * (EFin \o X) t).
    by apply/funext => t; rewrite /= EFinM.
  exact: integrableZl.
have i4 : P.-integrable [set: T] (fun=> (b ^+ 2)%:E).
  exact: finite_measure_integrable_cst.
have -> : (fun t => ((X t - b) ^+ 2)%:E) =
    (EFin \o (fun t => X t ^+ 2)%R) \+ (EFin \o (fun t => - (2 * b) * X t)%R)
    \+ (fun=> (b ^+ 2)%:E).
  by apply/funext => t; rewrite /= -!EFinD; congr EFin; ring.
rewrite integralD//; first exact: (integrableD _ i2 i3).
rewrite integralD// integral_cst//.
rewrite [X in _ * X]probability_setT mule1.
have -> : \int[P]_t (EFin \o (fun t => - (2 * b) * X t)%R) t =
    (- (2 * b))%:E * \int[P]_t (X t)%:E.
  by rewrite -integralZl//; apply: eq_integral => t _; rewrite /= EFinM.
by rewrite EFinN mulNe.
Qed.

Lemma integral_affine_pow4_le (X : T -> R) (b : R) :
  measurable_fun [set: T] X ->
  \int[P]_t ((X t - b) ^+ 4)%:E <=
  8%:E * (\int[P]_t (X t ^+ 4)%:E + (b ^+ 4)%:E).
Proof.
move=> mX.
have e4 (x : R) : (x ^+ 4 = (x ^+ 2) ^+ 2)%R by rewrite -exprM.
have p4 (x : R) : (0 <= x ^+ 4)%R by rewrite e4 sqr_ge0.
have pw t : ((X t - b) ^+ 4 <= 8 * X t ^+ 4 + 8 * b ^+ 4)%R.
  have h1 : ((X t - b) ^+ 2 <= 2 * (X t ^+ 2 + b ^+ 2))%R.
    by have := sqr_ge0 (X t + b); nra.
  have h0 := sqr_ge0 (X t - b).
  have h2 : ((X t - b) ^+ 4 <= (2 * (X t ^+ 2 + b ^+ 2)) ^+ 2)%R.
    by rewrite e4 ler_sqr ?nnegrE// mulr_ge0// addr_ge0// sqr_ge0.
  by apply: le_trans h2 _; have := sqr_ge0 (X t ^+ 2 - b ^+ 2); nra.
have mX4 : measurable_fun [set: T] (fun t => X t ^+ 4)%R.
  exact: measurable_funX.
apply: (@le_trans _ _ (\int[P]_t ((8 * X t ^+ 4 + 8 * b ^+ 4)%R)%:E)).
  apply: ge0_le_integral => //.
  - by move=> t _; rewrite lee_fin p4.
  - apply/measurable_EFinP; apply: measurable_funX.
    by apply: measurable_funB => //; exact: measurable_cst.
  - apply/measurable_EFinP; apply: measurable_funD; last exact: measurable_cst.
    by apply: measurable_funM => //; exact: measurable_cst.
  - by move=> t _; rewrite lee_fin.
under eq_integral do rewrite EFinD.
rewrite ge0_integralD//.
- by move=> t _; rewrite lee_fin mulr_ge0.
- by apply/measurable_EFinP; apply: measurable_funM.
- by move=> t _; rewrite lee_fin mulr_ge0.
- under eq_integral do rewrite EFinM.
  rewrite ge0_integralZl_EFin//; first last.
  + rewrite integral_cst//.
    rewrite [X in _ + _ * X <= _]probability_setT mule1.
    have h40 : 0 <= \int[P]_t (X t ^+ 4)%:E.
      by apply: integral_ge0 => t _; rewrite lee_fin.
    by rewrite [X in _ <= X]ge0_muleDr ?lee_fin.
  + exact/measurable_EFinP.
  + by move=> t _; rewrite lee_fin.
Qed.

(* Markov's inequality. *)
Lemma markov_ge0 (Y : T -> R) (B : R) : measurable_fun [set: T] Y ->
  (forall t, 0 <= Y t)%R -> (0 < B)%R ->
  P [set t | (B < Y t)%R] <= (B^-1)%:E * \int[P]_t (Y t)%:E.
Proof.
move=> mY Y0 B0.
set A := [set t | (B < Y t)%R].
have mA : measurable A.
  rewrite -[X in measurable X]setTI.
  exact: (measurable_fun_ltr (measurable_cst B) mY measurableT).
have h : B%:E * P A <= \int[P]_t (Y t)%:E.
  rewrite -[X in _ * P X]setIT -integral_indic//.
  rewrite -ge0_integralZl_EFin//; first last.
  - apply: ge0_le_integral => //.
    + by move=> t _; rewrite -EFinM lee_fin mulr_ge0 ?indicE// ltW.
    + apply: emeasurable_funM; first exact: measurable_cst.
      exact/measurable_EFinP/measurable_indic.
    + exact/measurable_EFinP.
    + move=> t _; rewrite -EFinM lee_fin indicE.
      case: (t \in A) / boolP => tA; last by rewrite mulr0 Y0.
      by rewrite mulr1 ltW//; move: tA; rewrite inE.
  - exact: ltW.
  - exact/measurable_EFinP/measurable_indic.
have Bi : (0 <= B^-1)%R by rewrite invr_ge0 ltW.
have Bi' : 0 <= (B^-1)%:E by rewrite lee_fin.
have := lee_wpmul2l Bi' h.
by rewrite muleA -EFinM mulVf ?gt_eqF// mul1e.
Qed.

End affine_moments.
