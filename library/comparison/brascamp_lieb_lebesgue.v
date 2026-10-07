From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import archimedean ring_tactic field_tactic.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology.
From mathcomp Require Import normedtype sequences derive realfun exp.
From mathcomp Require Import measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun measurable_realfun.
From mathcomp Require Import lebesgue_integral.
From mathcomp Require Import trigo probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral.
From GaussianAnalysis.gaussian Require Import gauss lebesgue_rV.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.comparison Require Import gauss_linear brascamp_lieb.

(**md**************************************************************************)
(* # The Brascamp-Lieb inequality: from bounded functions to [0, +oo]         *)
(*                                                                            *)
(* Let u_1, ..., u_n be unit vectors of 'rV[R]_m and c_1, ..., c_n positive   *)
(* weights such that sum_i c_i u_i^T u_i is the identity matrix. The Gaussian *)
(* form of the Brascamp-Lieb inequality for measurable f_i with values in     *)
(* [delta, K], 0 < delta,                                                     *)
(*                                                                            *)
(*   int prod_i f_i(<x, u_i>)^{c_i} dgauss_m(x)                               *)
(*     <= prod_i (int f_i d(normal_prob 0 1))^{c_i},                          *)
(*                                                                            *)
(* is gauss_brascamp_lieb_bounded of brascamp_lieb.v. This file derives:      *)
(* - the same for measurable f_i with values in [0, K]                        *)
(*   (gauss_brascamp_lieb_ge0): apply it to f_i + 1/(k+1), and let k -> oo;   *)
(*   the right side converges since a^c is continuous on [0, +oo) for c > 0;  *)
(* - the same for measurable F_i : R -> [0, +oo] (gauss_brascamp_lieb), with  *)
(*   extended integrals and poweR: apply the previous case to the             *)
(*   truncations min (F_i, k), monotone convergence on the left, and          *)
(*   monotonicity on the right; the product of the truncated factors          *)
(*   converges to the product of the limits, with 0 * +oo = 0;                *)
(* - the Lebesgue form (brascamp_lieb)                                        *)
(*                                                                            *)
(*   int_{R^m} prod_i F_i(<x, u_i>)^{c_i} dx <= prod_i (int_R F_i)^{c_i},     *)
(*                                                                            *)
(*   from the Gaussian form for f_i(t) = F_i(t) sqrt (2 pi) exp (t^2 / 2):    *)
(*   the integral of f_i against the standard normal law is the Lebesgue      *)
(*   integral of F_i, and since sum_i c_i <x, u_i>^2 = |x|^2 and              *)
(*   sum_i c_i = m (tight_frame_mxdot_sqr, tight_frame_sum),                  *)
(*   prod_i (sqrt (2 pi) exp (<x, u_i>^2 / 2))^{c_i} = (2 pi)^{m/2}           *)
(*   exp (|x|^2 / 2) is the inverse of the density gauss_pdf of gauss m       *)
(*   with respect to lebesgue_rV m.                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section extension.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Let powR_sum (x : R) I (r : seq I) (P : pred I) (a : I -> R) : 0 < x ->
  x `^ (\sum_(i <- r | P i) a i) = \prod_(i <- r | P i) x `^ a i.
Proof.
move=> x0; have xD p q : x `^ (p + q) = x `^ p * x `^ q.
  by rewrite powRD// (gt_eqF x0) /= implybT.
elim: r => [|i r IH]; first by rewrite !big_nil powRr0.
by rewrite !big_cons; case: ifP => // _; rewrite xD IH.
Qed.

Let emeasurable_prod d (T : measurableType d) I (r : seq I)
    (h : I -> T -> \bar R) :
  (forall i, measurable_fun [set: T] (h i)) ->
  measurable_fun [set: T] (fun x => \prod_(i <- r) h i x)%E.
Proof.
move=> mh; elim: r => [|i r IH].
  by under eq_fun do rewrite big_nil; exact: measurable_cst.
by under eq_fun do rewrite big_cons; exact: emeasurable_funM.
Qed.

Let lee_prod I (r : seq I) (P : pred I) (f g : I -> \bar R) :
  (forall i, P i -> 0 <= f i)%E -> (forall i, P i -> f i <= g i)%E ->
  (\prod_(i <- r | P i) f i <= \prod_(i <- r | P i) g i)%E.
Proof.
move=> f0 fg; elim/(big_load (fun x : \bar R => 0 <= x)%E): _.
elim/big_rec2: _ => // i y x Pi [x0 xy]; split; first by rewrite mule_ge0 ?f0.
by rewrite lee_pmul ?f0 ?fg.
Qed.

(* (a + 1 / (k + 1))^c tends to a^c. *)
Let cvg_powR_harmonic (a c : R) : 0 <= a -> 0 < c ->
  (a + harmonic k) `^ c @[k --> \oo] --> a `^ c.
Proof.
move=> a0 c0.
have h0 k : 0 < harmonic k :> R by rewrite /harmonic/= invr_gt0 ltr0n.
have [->|an0] := eqVneq a 0.
  rewrite powR0 ?gt_eqF//.
  under eq_fun do rewrite add0r.
  have := (cvg_at_rightP (@powR R ^~ c) 0 0).1 (@powR_cvg0 R c c0) harmonic.
  by apply; split; [exact: h0|exact: cvg_harmonic].
have apos : 0 < a by rewrite lt0r an0.
have hf : (fun k => a + harmonic k) @ \oo --> a.
  rewrite -[X in _ --> X]addr0.
  by apply: cvgD; [exact: cvg_cst|exact: cvg_harmonic].
have hg : {for a, continuous (@powR R ^~ c)}.
  apply: differentiable_continuous; apply/derivable1_diffP.
  by apply: derivable_powR; rewrite in_itv/= andbT.
exact: (@cvg_comp _ _ _ _ _ _ _ _ hf hg).
Qed.

(* A nondecreasing sequence lies below its limit. *)
Let nd_le_lim (v : nat -> \bar R) (l : \bar R) : nondecreasing_seq v ->
  v @ \oo --> l -> forall k, (v k <= l)%E.
Proof.
move=> nd vl k; rewrite -(cvg_lim (@ereal_hausdorff R) vl).
apply: lime_ge; first exact: cvgP vl.
near=> j; apply: nd; near: j.
by exists k.
Unshelve. all: by end_near. Qed.

(* The product of finitely many nondecreasing nonnegative sequences tends to
   the product of the limits, with the convention 0 * +oo = 0. *)
Let cvg_prod_nd (I : Type) (r : seq I) (v : I -> nat -> \bar R)
    (l : I -> \bar R) :
  (forall i k, (0 <= v i k)%E) -> (forall i, nondecreasing_seq (v i)) ->
  (forall i, v i @ \oo --> l i) ->
  (fun k => \prod_(i <- r) v i k)%E @ \oo --> (\prod_(i <- r) l i)%E.
Proof.
move=> v0 nd vl; elim: r => [|i r IH].
  have -> : (fun k => \prod_(j <- [::]) v j k)%E = fun=> 1%E.
    by apply/funext => k; rewrite big_nil.
  by rewrite big_nil; exact: cvg_cst.
have -> : (fun k => \prod_(j <- i :: r) v j k)%E =
    (fun k => v i k * \prod_(j <- r) v j k)%E.
  by apply/funext => k; rewrite big_cons.
rewrite big_cons.
have ndP : nondecreasing_seq (fun k => \prod_(j <- r) v j k)%E.
  by move=> k1 k2 k12; apply: lee_prod => j _; [exact: v0|exact: nd].
have [li0|li0] := eqVneq (l i) 0.
  have vi0 k : v i k = 0.
    apply/eqP; rewrite eq_le v0 andbT.
    by have := nd_le_lim (nd i) (vl i) k; rewrite li0.
  have -> : (fun k => v i k * \prod_(j <- r) v j k)%E = fun=> 0%E.
    by apply/funext => k; rewrite vi0 mul0e.
  by rewrite li0 mul0e; exact: cvg_cst.
have [L0|L0] := eqVneq (\prod_(j <- r) l j)%E 0.
  have P0 k : (\prod_(j <- r) v j k)%E = 0.
    have Pge0 : (0 <= \prod_(j <- r) v j k)%E.
      by apply: prode_ge0 => j _; exact: v0.
    apply/eqP; rewrite eq_le Pge0 andbT.
    by have := nd_le_lim ndP IH k; rewrite L0.
  have -> : (fun k => v i k * \prod_(j <- r) v j k)%E = fun=> 0%E.
    by apply/funext => k; rewrite P0 mule0.
  by rewrite L0 mule0; exact: cvg_cst.
apply: cvgeM; [|exact: vl|exact: IH].
by rewrite mule_defE (negbTE li0) (negbTE L0).
Qed.

(* min (a, k)^c tends to a^c for a in [0, +oo]. *)
Let cvg_poweR_mine (a : \bar R) (c : R) : (0 <= a)%E -> 0 < c ->
  ((mine a k%:R%:E) `^ c)%E @[k --> \oo] --> (a `^ c)%E.
Proof.
move=> a0 c0; case: a a0 => [r| |] //= r0.
  apply: cvg_near_cst; near=> k.
  suff -> : mine r%:E k%:R%:E = r%:E by [].
  apply/min_idPl; rewrite lee_fin; near: k.
  exists (Num.truncn r).+1 => // k /= rk.
  by apply: (le_trans (ltW (truncnS_gt r))); rewrite ler_nat.
rewrite gt_eqF//.
apply/cvgeryP/cvgryPge => A.
pose B := maxr A 1.
have AB : A <= B by rewrite /B le_max lexx.
have B0 : 0 <= B by rewrite /B le_max ler01 orbT.
have BE : B = (B `^ c^-1) `^ c by rewrite -powRrM mulVf ?gt_eqF// powRr1.
near=> k.
have hk : B `^ c^-1 <= k%:R.
  near: k; exists (Num.truncn (B `^ c^-1)).+1 => // k /= hk.
  by apply: (le_trans (ltW (truncnS_gt _))); rewrite ler_nat.
apply: (le_trans AB); rewrite [X in X <= _]BE.
apply: ge0_ler_powR => //; first exact: ltW.
- by rewrite nnegrE powR_ge0.
- by rewrite nnegrE ler0n.
Unshelve. all: by end_near. Qed.

(* The Gaussian form for bounded nonnegative functions, from the bounded
   case applied to f + 1 / (k + 1). *)
Lemma gauss_brascamp_lieb_ge0 m n (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R)
    (f : 'I_n -> R -> R) (K : R) :
  (forall i, mxdot (u i) (u i) = 1) -> (forall i, 0 < c i) ->
  \sum_i c i *: ((u i)^T *m u i) = 1%:M ->
  (forall i, measurable_fun [set: R] (f i)) ->
  (forall i y, 0 <= f i y <= K) ->
  \int[gauss m]_x (\prod_i (f i (mxdot x (u i))) `^ (c i)) <=
  \prod_i (\int[N]_y f i y) `^ (c i).
Proof.
move=> hu hc hframe mf fK.
have f0 i y : 0 <= f i y by case/andP: (fK i y).
have fK' i y : f i y <= K by case/andP: (fK i y).
pose K1 := maxr K 0 + 1.
have K11 : 1 <= K1 by rewrite /K1 lerDr le_max lexx orbT.
have KK1 : K + 1 <= K1 by rewrite /K1 lerD2r le_max lexx.
have mP (g : 'I_n -> R -> R) : (forall i, measurable_fun [set: R] (g i)) ->
    measurable_fun [set: 'rV[R]_m]
      (fun x => \prod_i (g i (mxdot x (u i))) `^ (c i)).
  move=> mg; apply: measurable_prod => i _.
  apply: measurableT_comp (@measurable_powR R _) _.
  exact: measurableT_comp (mg i) (measurable_mxdot (u i)).
have bP (g : 'I_n -> R -> R) (B : R) : (forall i y, 0 <= g i y <= B) ->
    forall x, `|\prod_i (g i (mxdot x (u i))) `^ (c i)| <= \prod_i B `^ (c i).
  move=> gB x; rewrite ger0_norm.
    by apply: prodr_ge0 => i _; exact: powR_ge0.
  apply: ler_prod => i _; rewrite powR_ge0 /=.
  have /andP[g0 gB'] := gB i (mxdot x (u i)).
  apply: ge0_ler_powR => //; first exact: ltW.
  by rewrite nnegrE (le_trans g0).
have iP (g : 'I_n -> R -> R) (B : R) :
    (forall i, measurable_fun [set: R] (g i)) ->
    (forall i y, 0 <= g i y <= B) ->
    (gauss m).-integrable [set: 'rV[R]_m]
      (EFin \o (fun x => \prod_i (g i (mxdot x (u i))) `^ (c i))).
  by move=> mg gB; exact: (bounded_integrable _ (mP g mg) (bP g B gB)).
pose a i := \int[N]_y f i y.
have step k : \int[gauss m]_x (\prod_i (f i (mxdot x (u i))) `^ (c i)) <=
    \prod_i (a i + harmonic k) `^ (c i).
  have d0 : 0 < harmonic k :> R by rewrite /harmonic/= invr_gt0 ltr0n.
  have d1 : harmonic k <= 1 :> R.
    by rewrite /harmonic/= invf_le1 ?ler1n// ltr0n.
  pose g i y := f i y + harmonic k.
  have mg i : measurable_fun [set: R] (g i).
    by apply: measurable_funD => //; exact: mf.
  have fK1 i y : 0 <= f i y <= K1.
    by rewrite f0 /=; have := fK' i y; lra.
  have gK1 i y : 0 <= g i y <= K1.
    have := f0 i y; have := fK' i y; rewrite /g => h1 h2.
    by apply/andP; split; lra.
  have gb i y : harmonic k <= g i y <= K1.
    have := f0 i y; have := fK' i y; rewrite /g => h1 h2.
    by apply/andP; split; lra.
  have dK : harmonic k <= K1 by lra.
  have H := gauss_brascamp_lieb_bounded hu hc hframe d0 dK mg gb.
  have eqa i : \int[N]_y g i y = a i + harmonic k.
    have if1 : N.-integrable [set: R] (EFin \o f i).
      apply: (bounded_integrable N (mf i) (C := K1)) => y.
      by rewrite ger0_norm ?f0//; have /andP[] := fK1 i y.
    have if2 : N.-integrable [set: R] (EFin \o cst (harmonic k : R)).
      exact: finite_measure_integrable_cst.
    rewrite /g (@RintegralD _ _ _ N setT (f i) (cst (harmonic k))
      measurableT if1 if2).
    by rewrite Rintegral_cst//= probability_setT mulr1.
  apply: (@le_trans _ _ (\int[gauss m]_x
      (\prod_i (g i (mxdot x (u i))) `^ (c i)))).
    apply: le_Rintegral => //.
    - exact: (iP f K1).
    - exact: (iP g K1).
    move=> x _; apply: ler_prod => i _; rewrite powR_ge0 /=.
    apply: ge0_ler_powR => //; first exact: ltW.
    - by rewrite nnegrE.
    - by rewrite nnegrE; have /andP[] := gK1 i (mxdot x (u i)).
    - by rewrite /g lerDl ltW.
  apply: le_trans H _; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_bigr => i _; rewrite eqa.
have cv : (fun k => \prod_i (a i + harmonic k) `^ (c i)) @ \oo -->
    \prod_i (a i) `^ (c i).
  apply: (@cvg_big _ _ _ _ _ mul_continuous _ _ _
    (fun i k => (a i + harmonic k) `^ (c i)) (fun i => a i `^ c i)) => // i _.
  apply: cvg_powR_harmonic => //.
  by apply: Rintegral_ge0 => y _; exact: f0.
have : \int[gauss m]_x (\prod_i (f i (mxdot x (u i))) `^ (c i)) <=
    lim ((fun k => \prod_i (a i + harmonic k) `^ (c i)) @ \oo).
  apply: limr_ge; first exact: cvgP cv.
  by apply: nearW => k; exact: step.
by rewrite (cvg_lim (@Rhausdorff R) cv).
Qed.

(* The Gaussian form of the Brascamp-Lieb inequality for measurable
   F_i : R -> [0, +oo], from the bounded case by monotone convergence along
   the truncations min (F_i, k). *)
Theorem gauss_brascamp_lieb m n (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R)
    (F : 'I_n -> R -> \bar R) :
  (forall i, mxdot (u i) (u i) = 1) -> (forall i, 0 < c i) ->
  \sum_i c i *: ((u i)^T *m u i) = 1%:M ->
  (forall i, measurable_fun [set: R] (F i)) ->
  (forall i t, 0 <= F i t)%E ->
  (\int[gauss m]_x \prod_i F i (mxdot x (u i)) `^ c i <=
   \prod_i (\int[normal_prob 0 1]_t F i t) `^ c i)%E.
Proof.
move=> hu hc hframe mF F0.
pose T (k : nat) i y := mine (F i y) k%:R%:E.
have T0 k i y : (0 <= T k i y)%E by rewrite /T le_min F0 lee_fin ler0n.
have Tk k i y : (T k i y <= k%:R%:E)%E by rewrite /T ge_min lexx orbT.
have TF k i y : (T k i y <= F i y)%E by rewrite /T ge_min lexx.
have Tnd k1 k2 i y : (k1 <= k2)%N -> (T k1 i y <= T k2 i y)%E.
  move=> k12; rewrite /T le_min !ge_min lexx /=.
  by rewrite lee_fin ler_nat k12 orbT.
have Tfin k i y : T k i y \is a fin_num.
  by rewrite ge0_fin_numE// (le_lt_trans (Tk k i y))// ltry.
pose t k i y := fine (T k i y).
have tE k i y : (t k i y)%:E = T k i y by rewrite /t fineK.
have mT k i : measurable_fun [set: R] (T k i).
  exact: measurable_mine (mF i) (measurable_cst _).
have mt k i : measurable_fun [set: R] (t k i).
  exact: measurableT_comp (mT k i).
have tb k i y : 0 <= t k i y <= k%:R.
  by apply/andP; split; rewrite -lee_fin tE; [exact: T0|exact: Tk].
pose G k x := (\prod_i (T k i (mxdot x (u i))) `^ c i)%E.
have GE k x : G k x = ((\prod_i (t k i (mxdot x (u i))) `^ c i)%R)%:E.
  rewrite -prodEFin; apply: eq_bigr => i _.
  by rewrite -poweR_EFin tE.
have mG k : measurable_fun [set: 'rV[R]_m] (G k).
  apply: emeasurable_prod => i.
  apply: measurableT_comp (@measurable_poweR R (c i)) _.
  exact: measurableT_comp (mT k i) (measurable_mxdot (u i)).
have G0 k x : (0 <= G k x)%E by apply: prode_ge0 => i _; exact: poweR_ge0.
have powT k1 k2 i y : (k1 <= k2)%N ->
    ((T k1 i y) `^ c i <= (T k2 i y) `^ c i)%E.
  move=> k12; apply: gt0_ler_poweR; first exact: ltW.
  - by rewrite in_itv/= T0 leey.
  - by rewrite in_itv/= T0 leey.
  - exact: Tnd.
have ndG x : nondecreasing_seq (G ^~ x).
  move=> k1 k2 k12; apply: lee_prod => i _; first exact: poweR_ge0.
  exact: powT.
have limG x : G ^~ x @ \oo --> (\prod_i F i (mxdot x (u i)) `^ c i)%E.
  have h1 i k : (0 <= (T k i (mxdot x (u i))) `^ c i)%E by exact: poweR_ge0.
  have h2 i : nondecreasing_seq (fun k => (T k i (mxdot x (u i))) `^ c i)%E.
    by move=> k1 k2 k12; exact: powT.
  have h3 i : (fun k => (T k i (mxdot x (u i))) `^ c i)%E @ \oo -->
      ((F i (mxdot x (u i))) `^ c i)%E.
    exact: (cvg_poweR_mine (F0 i (mxdot x (u i))) (hc i)).
  exact: (@cvg_prod_nd _ (index_enum 'I_n) _ _ h1 h2 h3).
have -> : (\int[gauss m]_x \prod_i F i (mxdot x (u i)) `^ c i)%E =
    (\int[gauss m]_x limn (G ^~ x))%E.
  apply: eq_integral => x _.
  by rewrite (cvg_lim (@ereal_hausdorff R) (limG x)).
rewrite (@monotone_convergence _ _ _ (gauss m) setT measurableT G mG
  (fun k x _ => G0 k x) (fun x _ => ndG x)).
apply: lime_le.
  apply: ereal_nondecreasing_is_cvgn => k1 k2 k12.
  by apply: ge0_le_integral => // x _; exact: ndG.
apply: nearW => k.
have iGk : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun x => \prod_i (t k i (mxdot x (u i))) `^ c i)).
  apply: (bounded_integrable _ _ (C := \prod_i (k%:R : R) `^ c i)).
    apply: measurable_prod => i _.
    apply: measurableT_comp (@measurable_powR R _) _.
    exact: measurableT_comp (mt k i) (measurable_mxdot (u i)).
  move=> x; rewrite ger0_norm.
    by apply: prodr_ge0 => i _; exact: powR_ge0.
  apply: ler_prod => i _; rewrite powR_ge0 /=.
  have /andP[t0 tk] := tb k i (mxdot x (u i)).
  apply: ge0_ler_powR => //; first exact: ltW.
  by rewrite nnegrE ler0n.
have -> : (\int[gauss m]_x G k x)%E =
    (\int[gauss m]_x (\prod_i (t k i (mxdot x (u i))) `^ c i))%:E.
  have fin := integrable_fin_num measurableT iGk.
  under eq_integral => x _ do rewrite GE.
  by rewrite /Rintegral fineK.
apply: le_trans (_ : ((\prod_i (\int[N]_y t k i y) `^ c i)%R)%:E <= _)%E.
  by rewrite lee_fin; exact: (gauss_brascamp_lieb_ge0 hu hc hframe (mt k)).
rewrite -prodEFin; apply: lee_prod => i _; first by rewrite lee_fin powR_ge0.
have itk : N.-integrable [set: R] (EFin \o t k i).
  apply: (bounded_integrable N (mt k i) (C := k%:R)) => y.
  by have /andP[t0 tk] := tb k i y; rewrite ger0_norm.
rewrite -poweR_EFin; apply: gt0_ler_poweR; first exact: ltW.
- rewrite in_itv/= leey andbT lee_fin.
  by apply: Rintegral_ge0 => y _; have /andP[] := tb k i y.
- by rewrite in_itv/= leey andbT integral_ge0.
rewrite /Rintegral fineK; first by have := integrable_fin_num measurableT itk.
apply: ge0_le_integral => //.
- by move=> y _; rewrite /= tE.
- by apply/measurable_EFinP; exact: mt.
- exact: mF.
- by move=> y _; rewrite /= tE.
Qed.

Theorem brascamp_lieb m n (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R)
    (F : 'I_n -> R -> \bar R) :
  (forall i, mxdot (u i) (u i) = 1) -> (forall i, 0 < c i) ->
  \sum_i c i *: ((u i)^T *m u i) = 1%:M ->
  (forall i, measurable_fun [set: R] (F i)) -> (forall i t, 0 <= F i t)%E ->
  (\int[lebesgue_rV m]_x \prod_i F i (mxdot x (u i)) `^ c i <=
   \prod_i (\int[lebesgue_measure]_t F i t) `^ c i)%E.
Proof.
move=> hu hc hframe mF F0.
have pi0 : 0 < pi :> R := pi_gt0 R.
have sp0 : 0 < Num.sqrt (2 * pi) :> R by rewrite sqrtr_gt0 mulr_gt0.
pose g (t : R) := Num.sqrt (2 * pi) * expR (t ^+ 2 / 2).
have g0 t : 0 < g t by rewrite mulr_gt0 ?expR_gt0.
have mg : measurable_fun [set: R] g.
  apply: measurable_funM => //; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurable_funX.
pose f i t := (F i t * (g t)%:E)%E.
have mf i : measurable_fun [set: R] (f i).
  by apply: emeasurable_funM => //; exact/measurable_EFinP.
have f0 i t : (0 <= f i t)%E by rewrite mule_ge0// lee_fin ltW.
(* f i against the standard normal law is F i against Lebesgue measure *)
have gpdf t : g t * normal_pdf 0 1 t = 1.
  rewrite normal_pdfE ?oner_neq0// /normal_peak /normal_fun subr0 expr1n mul1r.
  have -> : (pi *+ 2 : R) = 2 * pi by rewrite mulr_natl.
  rewrite /g mulrACA -expRD mulNr addrN expR0 mulr1.
  by rewrite divff// gt_eqF.
have int_f i :
    (\int[normal_prob 0 1]_t f i t = \int[lebesgue_measure]_t F i t)%E.
  rewrite ge0_integral_normal_prob//; apply: eq_integral => t _.
  by rewrite /f -muleA -EFinM gpdf mule1.
(* the integrand on 'rV[R]_m *)
have mG : measurable_fun [set: 'rV[R]_m]
    (fun x => \prod_i F i (mxdot x (u i)) `^ c i)%E.
  apply: emeasurable_prod => i.
  apply: measurableT_comp (@measurable_poweR R (c i)) _.
  exact: measurableT_comp (mF i) (measurable_mxdot (u i)).
have G0 x : (0 <= \prod_i F i (mxdot x (u i)) `^ c i)%E.
  by apply: prode_ge0 => i _; exact: poweR_ge0.
have gc t (a : R) : g t `^ a =
    Num.sqrt (2 * pi) `^ a * expR (a * (t ^+ 2 / 2)).
  rewrite /g powRM ?sqrtr_ge0 ?expR_ge0//.
  by rewrite -expRM [_ * a]mulrC.
have rid x : \prod_i g (mxdot x (u i)) `^ c i = (gauss_pdf x)^-1.
  rewrite (eq_bigr _ (fun i _ => gc (mxdot x (u i)) (c i))) big_split /=.
  rewrite -powR_sum// -expR_sum (tight_frame_sum hu hframe).
  rewrite powR_mulrn ?sqrtr_ge0//.
  rewrite /gauss_pdf invfM invrK -expRN mulNr opprK.
  congr (_ * expR _).
  rewrite -(tight_frame_mxdot_sqr hframe x) mulr_suml.
  by apply: eq_bigr => i _; rewrite mulrA.
have pw x : (\prod_i F i (mxdot x (u i)) `^ c i * ((gauss_pdf x)^-1)%R%:E =
    \prod_i f i (mxdot x (u i)) `^ c i)%E.
  have e i : (f i (mxdot x (u i)) `^ c i =
      F i (mxdot x (u i)) `^ c i * (g (mxdot x (u i)) `^ c i)%:E)%E.
    by rewrite /f poweRM ?F0 ?lee_fin ?(ltW (g0 _))// poweR_EFin.
  by rewrite (eq_bigr _ (fun i _ => e i)) big_split /= prodEFin rid.
rewrite ge0_integral_lebesgue_rV_gauss//.
under eq_integral => x _ do rewrite pw.
have -> : (\prod_i (\int[lebesgue_measure]_t F i t) `^ c i =
    \prod_i (\int[normal_prob 0 1]_t f i t) `^ c i)%E.
  by apply: eq_bigr => i _; rewrite int_f.
exact: gauss_brascamp_lieb.
Qed.

End extension.
