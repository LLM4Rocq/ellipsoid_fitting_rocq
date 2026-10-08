From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp trigo measure.
From mathcomp Require Import lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral.
From GaussianAnalysis.gaussian Require Import gauss.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import gauss_smoothing.
From GaussianAnalysis.comparison Require Import gauss_concentration slepian.
From GaussianAnalysis.comparison Require Import gauss_shift escape.

(**md**************************************************************************)
(* # Sudakov's minoration and the dual Sudakov inequality                     *)
(*                                                                            *)
(* Two classical entropy bounds for Gaussian processes, with explicit         *)
(* constants, and the facts they rest on. g has law gauss n.                  *)
(* - gauss_max_lower: the largest of n independent standard normal variables  *)
(*   has mean at least sqrt (ln n) / 2 - 2.                                   *)
(* - sudakov_minoration (Sudakov): if the points xs i of 'rV[R]_n,            *)
(*   i < k + 1, are pairwise at distance at least eps, then                   *)
(*   eps (sqrt (ln (k + 1)) / 2 - 2) <= sqrt 2 E max_i <g, xs i>. Proof: the  *)
(*   Sudakov-Fernique inequality (slepian.v) against independent normal       *)
(*   variables of variance eps^2 / 2, then gauss_max_lower.                   *)
(* - gauss_shift_sym: for a measurable symmetric set A,                       *)
(*   gauss n (h + A) >= exp (- |h|^2 / 2) gauss n A, by the Cameron-Martin    *)
(*   formula (gauss_shift.v) and cosh >= 1.                                   *)
(* - dual_sudakov (Pajor and Tomczak-Jaegermann, by Talagrand's argument): if *)
(*   nrm is a measurable seminorm with E nrm(g) <= L, the points of the       *)
(*   Euclidean ball of radius r that are pairwise more than eps apart for nrm *)
(*   are at most 2 exp (8 r^2 L^2 / eps^2).                                   *)
(* - separated_net: if the eps-separated lists of points of a set K have at   *)
(*   most M points, K has an eps-net of at most M of its own points, a        *)
(*   separated list of largest size.                                          *)
(* These two bounds replace volume arguments: covering.v covers the           *)
(* nuclear-norm ball by products of column balls with them.                   *)
(*                                                                            *)
(* ```                                                                        *)
(*   separated dist K eps s == s is a list of distinct points of K, pairwise  *)
(*                             more than eps apart for dist                   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section separated_net.
Context {R : realType} {T : eqType}.
Variables (dist : T -> T -> R) (K : set T) (eps : R).
Hypothesis dist_sym : forall x y, dist x y = dist y x.
Hypothesis dist_refl : forall x, dist x x <= eps.

(* s is a list of distinct points of K, pairwise more than eps apart. *)
Definition separated (s : seq T) := [/\ uniq s, {subset s <= K} &
  forall x y, x \in s -> y \in s -> x != y -> eps < dist x y].

(* If the eps-separated lists of points of K have at most M points, K has an
   eps-net of at most M of its points: a separated list of largest size. *)
Lemma separated_net (M : nat) : (forall s, separated s -> (size s <= M)%N) ->
  exists s : seq T, [/\ {subset s <= K}, (size s <= M)%N &
    forall x, K x -> exists2 y, y \in s & dist x y <= eps].
Proof.
move=> hM.
pose P n := `[< exists s, separated s /\ size s = n >].
have P0 : P 0%N by apply/asboolP; exists [::]; split => //; split.
have PM n : P n -> (n <= M)%N by move=> /asboolP[s [hs <-]]; exact: hM.
case: (ex_maxnP (ex_intro P 0%N P0) PM) => n0 Pn0 n0max.
have Mn0 := PM _ Pn0.
move: Pn0 => /asboolP[s [[us sK ssep] sn]].
exists s; split => //; first by rewrite sn.
move=> x Kx; apply: contrapT => hneg.
have hall y : y \in s -> eps < dist x y.
  move=> ys; rewrite ltNge; apply/negP => h; apply: hneg; by exists y.
have xs : x \notin s.
  by apply/negP => xs; have := hall x xs; rewrite ltNge dist_refl.
have : P n0.+1.
  apply/asboolP; exists (x :: s); split; last by rewrite /= sn.
  split; first by rewrite /= xs us.
    move=> y; rewrite inE => /orP[/eqP ->|/sK //]; exact: mem_set.
  move=> y z; rewrite !inE => /orP[/eqP ->|ys] /orP[/eqP ->|zs].
  - by rewrite eqxx.
  - by move=> _; exact: hall.
  - by move=> _; rewrite dist_sym; exact: hall.
  - exact: ssep.
by move=> /n0max; rewrite ltnn.
Qed.

End separated_net.

Section gauss_max.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

(* A lower bound on the standard normal probability of ]t, t + 1]. *)
Lemma normal_prob_itv_ge (t : R) : 0 <= t ->
  ((expR (- ((t + 1) ^+ 2 / 2)) / 3)%:E <= N `]t, (t + 1)%R]%classic)%E.
Proof.
move=> t0.
set c := expR (- ((t + 1) ^+ 2 / 2)) / 3.
have mI : measurable (`]t, (t + 1)%R] : set R) by exact: measurable_itv.
have -> : (c%:E = \int[lebesgue_measure]_(x in `]t, (t + 1)%R]) (cst c%:E) x)%E.
  rewrite integral_cst // [X in (_ * X)%E]lebesgue_measure_itv /= lte_fin.
  by rewrite ltrDl ltr01 -EFinD addrAC subrr add0r mule1.
apply: ge0_le_integral => //.
- by move=> x _; rewrite lee_fin divr_ge0 ?expR_ge0.
- by apply/measurable_EFinP; apply: measurable_funTS;
    exact: measurable_normal_pdf.
move=> x; rewrite /= in_itv /= => /andP[tx xt].
rewrite lee_fin /c normal_pdfE ?oner_neq0 //.
have pi4 : pi < 4 :> R.
  by have := @pihalf_lt2 R; rewrite ltr_pdivrMr // => h; lra.
have s0 : 0 < Num.sqrt (pi *+ 2) :> R.
  by rewrite sqrtr_gt0 mulrn_wgt0 //; exact: pi_gt0.
have s3 : Num.sqrt (pi *+ 2) <= 3 :> R.
  have -> : (3 : R) = Num.sqrt (3 ^+ 2) by rewrite sqrtr_sqr ger0_norm.
  by rewrite ler_wsqrtr // mulr2n; lra.
have hp : 3^-1 <= normal_peak 1 :> R.
  by rewrite /normal_peak expr1n mul1r lef_pV2 ?posrE.
have hf : expR (- ((t + 1) ^+ 2 / 2)) <= normal_fun 0 1 x.
  rewrite /normal_fun subr0 expr1n ler_expR.
  have hx : x ^+ 2 <= (t + 1) ^+ 2 by rewrite ler_sqr ?nnegrE; lra.
  by rewrite -mulNr ler_pM2r //; lra.
rewrite mulrC; apply: ler_pM => //; rewrite ?invr_ge0 ?expR_ge0 //.
Qed.

Let mx_norm_frob m n' (B : 'M[R]_(m, n')) : `|B| <= frobenius B.
Proof.
have -> : `|B| = \big[maxr/0]_ij `|B ij.1 ij.2| by rewrite -mx_normrE.
apply: bigmax_le => [|ij _]; first exact: frobenius_ge0.
exact: frobenius_entry.
Qed.

(* The largest of n independent standard normal variables has mean at least
   sqrt (ln n) / 2 - 2. *)
Theorem gauss_max_lower k :
  Num.sqrt (ln k.+1%:R) / 2 - 2 <= \int[gauss k.+1]_g rmax (g : 'rV[R]_k.+1).
Proof.
set n := k.+1.
have iF : (gauss n).-integrable setT (EFin \o (fun g : 'rV[R]_n => rmax g)).
  apply: (@integrable_gauss_lipschitz _ _ _ 1) => x y.
  by rewrite mul1r (le_trans (rmax_lipschitz _ _)) // mx_norm_frob.
have iA : (gauss n).-integrable setT
    (EFin \o (fun g : 'rV[R]_n => `|g 0 ord0|)).
  apply: (@integrable_gauss_lipschitz _ _ _ 1) => x y.
  rewrite mul1r (le_trans (ler_dist_dist _ _)) //.
  by have := frobenius_entry (x - y) 0 ord0; rewrite !mxE.
(* E |g_0| <= 1, through gauss 1 and gauss_frobenius_mean_le *)
have mabs : measurable_fun [set: R] (fun t : R => (`|t|)%:E).
  by apply/measurable_EFinP; exact: normr_measurable.
have abs0 (t : R) : (0 <= (`|t|)%:E)%E by rewrite lee_fin.
have hA : \int[gauss n]_g `|g 0 ord0| <= 1 :> R.
  have e1 := ge0_integral_gauss_coord (n := n) ord0 mabs abs0.
  have e2 := ge0_integral_gauss_coord (n := 1) ord0 mabs abs0.
  have e3 : \int[gauss 1]_g frobenius (g : 'rV[R]_1) =
      \int[gauss 1]_g `|g 0 ord0|.
    apply: eq_Rintegral => g _.
    by rewrite /frobenius /mxdot !big_ord1 -expr2 sqrtr_sqr.
  have := @gauss_frobenius_mean_le R 1; rewrite sqrtr1 e3.
  by rewrite /Rintegral e1 -e2.
have mF : measurable_fun [set: 'rV[R]_n] (fun g : 'rV[R]_n => rmax g).
  exact: continuous_measurable_mx continuous_rmax.
(* E max >= t P(max > t) - E |g_0| *)
have key (t : R) : 0 <= t ->
    t * fine (gauss n [set g | t < rmax g]) - 1 <= \int[gauss n]_g rmax g.
  move=> t0; set S := [set g : 'rV[R]_n | t < rmax g].
  have mS : measurable S.
    have := mF measurableT _ (measurable_itv `]t, +oo[).
    rewrite setTI; congr measurable; apply/seteqP.
    by split => g /=; rewrite in_itv /= andbT.
  have iI : (gauss n).-integrable setT (EFin \o \1_S).
    apply: (@integrable_prob_bounded _ _ _ (gauss n) _ 1).
      exact: measurable_indic.
    by move=> g; rewrite indicE; case: (g \in S); rewrite ?normr1 ?normr0.
  have iS : (gauss n).-integrable setT (EFin \o (fun g => t * \1_S g)).
    apply: (@integrable_prob_bounded _ _ _ (gauss n) _ t).
      by apply: measurable_funM => //; exact: measurable_indic.
    move=> g; rewrite normrM (ger0_norm t0) indicE.
    by case: (g \in S); rewrite ?normr1 ?normr0 ?mulr1 ?mulr0.
  have iD : (gauss n).-integrable setT
      (EFin \o (fun g : 'rV[R]_n => t * \1_S g - `|g 0 ord0|)).
    have := integrableB measurableT iS iA.
    by apply: eq_integrable => // g _; rewrite /= EFinB.
  have hp g : t * \1_S g - `|g 0 ord0| <= rmax g.
    rewrite indicE; have [gS|gS] := boolP (g \in S).
      move: gS; rewrite inE /S /= => gS.
      by rewrite mulr1; have := normr_ge0 (g 0 ord0); lra.
    rewrite mulr0 sub0r; apply: le_trans (le_rmax g ord0).
    by rewrite lerNl -normrN ler_norm.
  have := le_Rintegral measurableT iD iF (fun g _ => hp g).
  rewrite RintegralB // RintegralZl //.
  have -> : \int[gauss n]_g \1_S g = fine (gauss n S).
    by rewrite /Rintegral integral_indic // setIT.
  by lra.
have [s2|s2] := leP (Num.sqrt (ln n%:R) : R) 2.
  by have := key 0 (lexx 0); rewrite mul0r; lra.
(* for sqrt (ln n) > 2, take t = sqrt (ln n) - 1: P(max <= t) <= 1/2 *)
set t := Num.sqrt (ln n%:R) - 1 : R.
have t1 : 1 <= t by rewrite /t; lra.
have ln0 : 0 <= ln n%:R :> R by rewrite ln_ge0 // ler1n.
have tE : (t + 1) ^+ 2 = ln n%:R :> R by rewrite /t subrK sqr_sqrtr.
have n0 : 0 < n%:R :> R by rewrite ltr0n.
set q := fine (N `]-oo, t]%classic).
have mlo : measurable (`]-oo, t] : set R) by exact: measurable_itv.
have mhi : measurable (`]t, +oo[ : set R) by exact: measurable_itv.
have Nlo : N `]-oo, t]%classic = (1 - N `]t, +oo[%classic)%E.
  rewrite -probability_setC //; congr N; apply/seteqP; split => x /=;
    rewrite !in_itv /= ?andbT; [move=> xt; apply/negP; rewrite -leNgt|];
    by rewrite // leNgt => /negP.
have qE : N `]-oo, t]%classic = q%:E.
  by rewrite /q fineK // ge0_fin_numE ?measure_ge0 //
    (le_lt_trans (probability_le1 _ _)) ?ltry.
set a := expR (- ((t + 1) ^+ 2 / 2)).
have a0 : 0 < a by exact: expR_gt0.
have hhi : ((a / 3)%:E <= N `]t, +oo[%classic)%E.
  apply: le_trans (normal_prob_itv_ge (le_trans ler01 t1)) _.
  apply: le_measure; rewrite ?inE //.
  by move=> x /=; rewrite !in_itv /= => /andP[-> _].
have hq : q <= 1 - a / 3.
  suff : (q%:E <= (1 - a / 3)%:E)%E by rewrite lee_fin.
  have hiE : N `]t, +oo[%classic = (fine (N `]t, +oo[%classic))%:E.
    by rewrite fineK // ge0_fin_numE ?measure_ge0 //
      (le_lt_trans (probability_le1 _ _)) ?ltry.
  by move: hhi; rewrite -qE Nlo hiE -EFinB !lee_fin; lra.
have q0 : 0 <= q by rewrite /q fine_ge0 // measure_ge0.
have eC : gauss n [set g : 'rV[R]_n | rmax g <= t] = (q ^+ n)%:E.
  have -> : [set g : 'rV[R]_n | rmax g <= t] =
      [set g | forall i, `]-oo, t]%classic (g 0 i)].
    apply/seteqP; split => g /=.
      by move=> h i; rewrite in_itv /=; exact: le_trans (le_rmax g i) h.
    by move=> h; apply: rmax_le => i; have := h i; rewrite in_itv /=.
  apply: eq_trans (@gauss_box R n (fun=> `]-oo, t]%classic) (fun=> mlo)) _.
  under eq_bigr do rewrite qE.
  by rewrite prodEFin prodr_const card_ord.
have a2 : a ^+ 2 * n%:R = 1.
  have -> : a ^+ 2 = (n%:R)^-1.
    rewrite /a -expRM_natl.
    have -> : 2%:R * - ((t + 1) ^+ 2 / 2) = - ln n%:R :> R.
      by rewrite tE; field.
    by rewrite expRN lnK // posrE.
  by rewrite mulVf // gt_eqF.
have n9 : 9 <= n%:R :> R.
  have l4 : 4 < ln n%:R :> R.
    have := s2; rewrite -(@ltr_pXn2r _ 2) ?nnegrE ?sqrtr_ge0 // sqr_sqrtr //.
    by move=> h; lra.
  have := l4; rewrite -ltr_expR lnK ?posrE // => /ltW; apply: le_trans.
  have e2 : 3 <= expR 2 :> R by have := expR_ge1Dx (2 : R); lra.
  have -> : (4 : R) = 2%:R * 2 by rewrite -natrM.
  rewrite expRM_natl; have -> : (9 : R) = 3 ^+ 2 by rewrite expr2; lra.
  by rewrite ler_pXn2r ?nnegrE //; lra.
have na3 : 3 <= n%:R * a.
  have sq : (n%:R * a) ^+ 2 = n%:R :> R.
    rewrite exprMn; have := a2; set A := a ^+ 2; set B := n%:R; move=> h.
    have -> : B ^+ 2 * A = B * (A * B) by rewrite expr2; ring.
    by rewrite h mulr1.
  rewrite -(@ler_pXn2r _ 2) ?nnegrE ?mulr_ge0 ?ler0n ?(ltW a0) // sq.
  by have -> : (3 : R) ^+ 2 = 9 by rewrite expr2; lra.
have qn : q ^+ n <= 2^-1.
  apply: le_trans (_ : expR (- (a / 3)) ^+ n <= _).
    apply: lerXn2r; rewrite ?nnegrE ?expR_ge0 //.
    by apply: le_trans hq _; have := expR_ge1Dx (- (a / 3)); lra.
  rewrite -expRM_natl.
  apply: le_trans (_ : expR (-1) <= _).
    by rewrite ler_expR; lra.
  have e1 : 2 <= expR 1 :> R by have := expR_ge1Dx (1 : R); lra.
  by rewrite expRN lef_pV2 ?posrE ?expR_gt0.
have PS : 2^-1 <= fine (gauss n [set g : 'rV[R]_n | t < rmax g]).
  have mC : measurable [set g : 'rV[R]_n | rmax g <= t].
    by have := mF measurableT _ mlo; rewrite setTI; congr measurable.
  have -> : [set g : 'rV[R]_n | t < rmax g] = ~` [set g | rmax g <= t].
    by apply/seteqP; split => g /=; rewrite ltNge => /negP.
  by rewrite probability_setC // eC -EFinB /=; lra.
have := key t (le_trans ler01 t1).
have := ler_wpM2l (le_trans ler01 t1) PS.
by rewrite /t; lra.
Qed.

End gauss_max.

Section sudakov_minoration.
Context {R : realType}.

Lemma rmaxZ k (c : R) (z : 'rV[R]_k.+1) : 0 <= c -> rmax (c *: z) = c * rmax z.
Proof.
move=> c0; apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: rmax_le => j; rewrite mxE ler_wpM2l // le_rmax.
by have [j ->] := rmax_eq z; have := le_rmax (c *: z) j; rewrite mxE.
Qed.

(* Sudakov's minoration: if the points xs i of 'rV[R]_n are pairwise at
   distance at least eps, then E max_i <g, xs i> is at least
   eps (sqrt (ln (k + 1)) / 2 - 2) / sqrt 2. *)
Theorem sudakov_minoration n k (xs : 'I_k.+1 -> 'rV[R]_n) (eps : R) :
  0 <= eps -> (forall i j, i != j -> eps <= frobenius (xs i - xs j)) ->
  eps * (Num.sqrt (ln k.+1%:R) / 2 - 2) <=
  Num.sqrt 2 * \int[gauss n]_g rmax (\row_i mxdot g (xs i)).
Proof.
move=> e0 sep.
pose A : 'M[R]_(n, k.+1) := \matrix_(j, i) xs i 0 j.
have rowA (g : 'rV[R]_n) : \row_i mxdot g (xs i) = g *m A.
  apply/rowP => i; rewrite !mxE /mxdot big_ord1; apply: eq_bigr => j _.
  by rewrite !mxE.
have AtA j l : (A^T *m A) j l = mxdot (xs j) (xs l).
  by rewrite mxE /mxdot big_ord1; apply: eq_bigr => i _; rewrite !mxE.
have s2 : 0 < Num.sqrt 2 :> R by rewrite sqrtr_gt0.
(* the process of independent normals with increments of variance eps^2 *)
pose c := eps / Num.sqrt 2.
have c0 : 0 <= c by rewrite divr_ge0 // ltW.
pose B : 'M[R]_k.+1 := c *: 1%:M.
have BtB j l : (B^T *m B) j l = c ^+ 2 * (j == l)%:R.
  by rewrite /B linearZ /= mulmx1 !mxE eq_sym mulrA expr2.
have hBA j l : incr_var B j l <= incr_var A j l.
  rewrite /incr_var !BtB !AtA !eqxx.
  have -> : mxdot (xs j) (xs j) + mxdot (xs l) (xs l) -
      2 * mxdot (xs j) (xs l) = frobenius (xs j - xs l) ^+ 2.
    by rewrite frobenius_sqr mxdotBl !mxdotBr (mxdotC (xs l) (xs j)); ring.
  have [->|jl] := eqVneq j l.
    by rewrite subrr frobenius0 expr0n /=; lra.
  have -> : (true%:R : R) = 1 by [].
  have -> : (false%:R : R) = 0 by [].
  rewrite !mulr1 mulr0 mulr0 subr0.
  have hc : c ^+ 2 + c ^+ 2 = eps ^+ 2.
    by rewrite /c expr_div_n sqr_sqrtr //; field; rewrite gt_eqF.
  rewrite hc; apply: lerXn2r; rewrite ?nnegrE ?frobenius_ge0 //.
  exact: sep.
have sf := sudakov_fernique hBA.
have iA := integrable_gauss_rmax A.
have iB := integrable_gauss_rmax B.
have h1 := fine_le (integrable_fin_num measurableT iB)
  (integrable_fin_num measurableT iA) sf.
have eB : \int[gauss k.+1]_y rmax (y *m B) = c * \int[gauss k.+1]_y rmax y.
  rewrite -RintegralZl //; last first.
    by apply: eq_Rintegral => y _; rewrite /B -scalemxAr mulmx1 rmaxZ.
  apply: (@integrable_gauss_lipschitz _ _ _ 1) => x y.
  rewrite mul1r (le_trans (rmax_lipschitz _ _)) //.
  have -> : `|x - y| = \big[maxr/0]_ij `|(x - y) ij.1 ij.2|.
    by rewrite -mx_normrE.
  apply: bigmax_le => [|ij _]; first exact: frobenius_ge0.
  exact: frobenius_entry.
have hmax := @gauss_max_lower R k.
have eA : \int[gauss n]_g rmax (\row_i mxdot g (xs i)) =
    \int[gauss n]_g rmax (g *m A).
  by apply: eq_Rintegral => g _; rewrite rowA.
rewrite eA.
have h2 : \int[gauss k.+1]_y rmax (y *m B) <=
  \int[gauss n]_g rmax (g *m A) := h1.
rewrite eB in h2.
have h3 := ler_wpM2l c0 hmax.
have -> : eps = Num.sqrt 2 * c by rewrite /c mulrC divfK // gt_eqF.
rewrite -mulrA; apply: ler_wpM2l; first exact: ltW.
exact: le_trans h3 h2.
Qed.

End sudakov_minoration.

Section dual_sudakov.
Context {R : realType} {n : nat}.

(* The Gaussian measure of a symmetric set decreases at most by the factor
   exp (- |h|^2 / 2) under the translation by h (Cameron-Martin). *)
Lemma gauss_shift_sym (A : set 'rV[R]_n) (h : 'rV[R]_n) : measurable A ->
  (forall x, A x -> A (- x)) ->
  ((expR (- (mxdot h h / 2)))%:E * gauss n A <=
   gauss n [set x | A (x - h)%R])%E.
Proof.
move=> mA symA.
have symE x : \1_A (- x) = \1_A x :> R.
  rewrite !indicE; congr (_%:R); congr nat_of_bool; apply/idP/idP;
    rewrite !inE => /symA //; by rewrite opprK.
have mI : measurable_fun setT (fun x : 'rV[R]_n => (\1_A x : R)%:E).
  by apply/measurable_EFinP; exact: measurable_indic.
have mexp (c : R) :
    measurable_fun setT (fun x : 'rV[R]_n => expR (c * mxdot h x)).
  apply: measurableT_comp => //; apply: measurable_funM => //.
  exact: measurable_mxdotl.
pose f (c : R) (x : 'rV[R]_n) := ((\1_A x : R) * expR (c * mxdot h x))%:E.
have mf c : measurable_fun setT (f c).
  apply/measurable_EFinP; apply: measurable_funM => //; exact: measurable_indic.
have f0 c x : (0 <= f c x)%E by rewrite lee_fin mulr_ge0 // expR_ge0.
(* the symmetry of A and of gauss n *)
have eJ : (\int[gauss n]_x f 1%R x = \int[gauss n]_x f (-1)%R x)%E.
  rewrite -(ge0_integral_gauss_opp (mf (-1)%R) (f0 (-1)%R)).
  apply: eq_integral => x _; rewrite /f symE mxdotNr; congr (_ * expR _)%:E.
  by rewrite mulN1r mul1r opprK.
set e := expR (- (mxdot h h / 2)).
have mS : measurable [set x : 'rV[R]_n | A (x - h)%R].
  have : measurable_fun setT (fun x : 'rV[R]_n => x - h).
    by apply: measurable_addmx => //; exact: measurable_cst.
  by move=> /(_ measurableT A mA); rewrite setTI; congr measurable.
(* Cameron-Martin *)
have eS : gauss n [set x | A (x - h)%R] =
    (e%:E * \int[gauss n]_x f (-1)%R x)%E.
  rewrite -[X in gauss n X]setIT -integral_indic //.
  transitivity (\int[gauss n]_x (\1_A (x + - h) : R)%:E)%E.
    by apply: eq_integral => x _; rewrite !indicE.
  have i0 (x : 'rV[R]_n) : (0 <= (\1_A x : R)%:E)%E by rewrite lee_fin.
  rewrite (ge0_integral_gauss_shift (- h) mI i0).
  rewrite -ge0_integralZl //; first by rewrite lee_fin expR_ge0.
  apply: eq_integral => x _; rewrite /f /e -!EFinM; congr EFin.
  rewrite mxdotNl mxdotNl mxdotNr opprK mulN1r expRD; ring.
(* gauss n A <= int_A exp (- <h, x>), as cosh >= 1 *)
have eA : (gauss n A <= \int[gauss n]_x f (-1)%R x)%E.
  rewrite -[X in gauss n X]setIT -integral_indic //.
  apply: (@le_trans _ _
    (\int[gauss n]_x ((2^-1)%:E * (f 1%R x + f (-1)%R x)))%E).
    apply: ge0_le_integral => //.
      by apply: measurable_funeM; exact: emeasurable_funD.
    move=> x _; rewrite /f -EFinD -EFinM lee_fin -mulrDr.
    have := expR_cosh_ge (mxdot h x); rewrite mulN1r mul1r => hc.
    rewrite indicE; case: (x \in A); rewrite ?mul0r ?mulr0 // !mul1r.
    have -> : (true%:R : R) = 1 by [].
    by have := sqr_ge0 (mxdot h x); lra.
  rewrite ge0_integralZl //.
  - exact: emeasurable_funD.
  - by move=> x _; rewrite adde_ge0.
  rewrite ge0_integralD // eJ.
  set J := (\int[gauss n]_x f (-1)%R x)%E.
  have J0 : (0 <= J)%E by apply: integral_ge0 => x _; exact: f0.
  have -> : (J + J = 2%:E * J)%E.
    by rewrite (_ : (2 : \bar R) = 1 + 1)%E // ge0_muleDl // mul1e.
  by rewrite muleA -EFinM mulVf // mul1e.
by rewrite eS; apply: lee_wpmul2l => //; rewrite lee_fin expR_ge0.
Qed.

(* The dual Sudakov inequality of Pajor and Tomczak-Jaegermann, by
   Talagrand's argument: if nrm is a seminorm with E nrm(g) <= L, points of
   the Euclidean ball of radius r that are pairwise more than eps apart for
   nrm are at most 2 exp (8 r^2 L^2 / eps^2). *)
Theorem dual_sudakov (nrm : 'rV[R]_n -> R) (r eps L : R) k
    (xs : 'I_k.+1 -> 'rV[R]_n) :
  measurable_fun setT nrm ->
  (forall x, nrm (- x) = nrm x) ->
  (forall x y, nrm (x + y) <= nrm x + nrm y) ->
  (forall (c : R) x, 0 <= c -> nrm (c *: x) = c * nrm x) ->
  (gauss n).-integrable setT (EFin \o nrm) ->
  0 < eps -> 0 < L -> \int[gauss n]_g nrm g <= L ->
  (forall i, frobenius (xs i) <= r) ->
  (forall i j, i != j -> eps < nrm (xs i - xs j)) ->
  k.+1%:R <= 2 * expR (8 * r ^+ 2 * L ^+ 2 / eps ^+ 2).
Proof.
move=> mN nN nD nZ iN e0 L0 hL hr sep.
have nr0 x : 0 <= nrm x.
  have z : nrm 0 = 0 by have := nZ 0 x (lexx 0); rewrite scale0r mul0r.
  by have := nD x (- x); rewrite subrr z nN; lra.
have L2 : 0 < 2 * L by rewrite mulr_gt0.
pose B0 := [set y : 'rV[R]_n | nrm y <= 2 * L].
have mB0 : measurable B0.
  have := mN measurableT _ (measurable_itv `]-oo, (2 * L)%R]).
  by rewrite setTI; congr measurable; apply/seteqP; split => y /=;
    rewrite in_itv.
have symB0 x : B0 x -> B0 (- x) by rewrite /B0 /= nN.
(* Markov: nrm g <= 2 L with probability at least 1/2 *)
have hB0 : ((2^-1)%:E <= gauss n B0)%E.
  pose S := [set y : 'rV[R]_n | 2 * L < nrm y].
  have mS : measurable S.
    have := mN measurableT _ (measurable_itv `](2 * L)%R, +oo[).
    by rewrite setTI; congr measurable; apply/seteqP; split => y /=;
      rewrite in_itv /= andbT.
  have iS : (gauss n).-integrable setT (EFin \o \1_S).
    apply: (@integrable_prob_bounded _ _ _ (gauss n) _ 1).
      exact: measurable_indic.
    by move=> y; rewrite indicE; case: (y \in S); rewrite ?normr1 ?normr0.
  have iI : (gauss n).-integrable setT (EFin \o (fun y => 2 * L * \1_S y)).
    apply: (@integrable_prob_bounded _ _ _ (gauss n) _ (2 * L)).
      by apply: measurable_funM => //; exact: measurable_indic.
    move=> y; rewrite normrM (ger0_norm (ltW L2)) indicE.
    case: (y \in S); rewrite ?normr1 ?normr0 ?mulr1 ?mulr0 //.
    exact: ltW.
  have hp y : 2 * L * \1_S y <= nrm y.
    rewrite indicE; case: (boolP (y \in S)) => yS; last by rewrite mulr0.
    by move: yS; rewrite inE /S /= mulr1 => /ltW.
  have := le_Rintegral measurableT iI iN (fun y _ => hp y).
  rewrite RintegralZl //.
  have -> : \int[gauss n]_y \1_S y = fine (gauss n S).
    by rewrite /Rintegral integral_indic // setIT.
  move=> h.
  have PS : fine (gauss n S) <= 2^-1.
    rewrite -(ler_pM2l L2).
    by apply: le_trans h _; rewrite mulrAC mulfV ?mul1r; lra.
  have SE : gauss n S = (fine (gauss n S))%:E.
    by rewrite fineK // ge0_fin_numE ?measure_ge0 //
      (le_lt_trans (probability_le1 _ _)) ?ltry.
  have -> : B0 = ~` S.
    by apply/seteqP; split => y /=; rewrite /B0 /S /= leNgt => /negP.
  by rewrite probability_setC // SE -EFinB lee_fin; lra.
(* the translates of B0 by s xs i are disjoint *)
pose s := 4 * L / eps.
have s0 : 0 < s by rewrite divr_gt0 // mulr_gt0.
pose Sh (i : 'I_k.+1) := [set y : 'rV[R]_n | B0 (y - s *: xs i)%R].
have mSh i : measurable (Sh i).
  have : measurable_fun setT (fun y : 'rV[R]_n => y - s *: xs i).
    by apply: measurable_addmx => //; exact: measurable_cst.
  by move=> /(_ measurableT B0 mB0); rewrite setTI; congr measurable.
have triv : trivIset setT Sh.
  move=> i j _ _ [z [/= zi zj]]; apply/eqP; apply/negPn/negP => ij.
  have hsep := sep i j ij.
  have h1 : nrm (s *: (xs i - xs j)) <= 4 * L.
    have -> : s *: (xs i - xs j) = (z - s *: xs j) + - (z - s *: xs i).
      by apply/esym; rewrite opprB addrC addrA subrK scalerBr.
    apply: le_trans (nD _ _) _; rewrite nN.
    move: zi zj; rewrite /B0 /= => h2 h3.
    by apply: le_trans (lerD h3 h2) _; rewrite le_eqVlt; apply/orP; left;
      apply/eqP; ring.
  rewrite (nZ _ _ (ltW s0)) in h1.
  have : nrm (xs i - xs j) <= eps.
    rewrite -(ler_pM2l s0); apply: le_trans h1 _.
    by rewrite /s divfK ?gt_eqF.
  by lra.
(* each translate has measure at least exp (- s^2 r^2 / 2) / 2 *)
set c := expR (- (s ^+ 2 * r ^+ 2 / 2)).
have c0 : 0 < c by exact: expR_gt0.
have hSi i : ((c / 2)%:E <= gauss n (Sh i))%E.
  have := gauss_shift_sym (s *: xs i) mB0 symB0.
  apply: le_trans; rewrite EFinM.
  apply: lee_pmul; rewrite ?lee_fin ?(ltW c0) ?invr_ge0 //.
  rewrite /c ler_expR lerN2 ler_pM2r // mxdotZl mxdotZr mulrA -expr2.
  rewrite ler_wpM2l ?sqr_ge0 // -frobenius_sqr.
  have r0 : 0 <= r := le_trans (frobenius_ge0 _) (hr i).
  by rewrite ler_pXn2r ?nnegrE ?frobenius_ge0 //; exact: hr.
have hU : (\sum_(i < k.+1) gauss n (Sh i) <= 1)%E.
  rewrite -measure_bigsetU_ord //; apply: probability_le1.
  by apply: bigsetU_measurable => i _; exact: mSh.
have hsum : ((k.+1%:R * (c / 2))%:E <= 1)%E.
  apply: le_trans hU.
  have -> : (k.+1%:R * (c / 2))%:E = (\sum_(i < k.+1) (c / 2)%:E)%E.
    by rewrite sumEFin sumr_const card_ord mulr_natl.
  by apply: lee_sum => i _; exact: hSi.
move: hsum; rewrite lee_fin => hsum.
have -> : 8 * r ^+ 2 * L ^+ 2 / eps ^+ 2 = s ^+ 2 * r ^+ 2 / 2.
  have epsne : eps != 0 by rewrite gt_eqF.
  by rewrite /s; field.
have ec : expR (s ^+ 2 * r ^+ 2 / 2) = c^-1 by rewrite /c expRN invrK.
rewrite ec.
have cne : c != 0 by rewrite gt_eqF.
have hk : k.+1%:R * (c / 2) * (2 / c) = k.+1%:R by field.
rewrite -[X in X <= _]hk; apply: ler_piMl => //.
by rewrite divr_ge0 // ltW.
Qed.

End dual_sudakov.
