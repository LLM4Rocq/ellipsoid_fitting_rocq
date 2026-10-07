From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals ereal topology.
From mathcomp Require Import normedtype sequences exp.
From mathcomp Require Import measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun measurable_realfun.
From mathcomp Require Import lebesgue_integral.
From mathcomp Require Import trigo probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral.
From GaussianAnalysis.gaussian Require Import gauss lebesgue_rV.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import gauss_linear.

(**md**************************************************************************)
(* # The Brascamp-Lieb inequality: from the Gaussian to the Lebesgue form     *)
(*                                                                            *)
(* Let u_1, ..., u_n be unit vectors of 'rV[R]_m and c_1, ..., c_n positive   *)
(* weights such that sum_i c_i u_i^T u_i is the identity matrix. Then         *)
(* sum_i c_i <x, u_i>^2 = |x|^2 for every x (weighted_frame_mxdot) and        *)
(* sum_i c_i = m (weighted_frame_trace). The Gaussian form of the             *)
(* Brascamp-Lieb inequality, for measurable F_i : R -> [0, +oo],              *)
(*                                                                            *)
(*   int prod_i F_i(<x, u_i>)^{c_i} dgauss_m(x)                               *)
(*     <= prod_i (int F_i d(normal_prob 0 1))^{c_i},                          *)
(*                                                                            *)
(* implies the Lebesgue form (brascamp_lieb)                                  *)
(*                                                                            *)
(*   int_{R^m} prod_i F_i(<x, u_i>)^{c_i} dx <= prod_i (int_R F_i)^{c_i}.     *)
(*                                                                            *)
(* Proof: apply the Gaussian form to f_i(t) = F_i(t) sqrt (2 pi) exp (t^2/2). *)
(* The integral of f_i against the standard normal law is the Lebesgue        *)
(* integral of F_i, and by the two frame identities                           *)
(* prod_i (sqrt (2 pi) exp (<x, u_i>^2 / 2))^{c_i} = (2 pi)^{m/2}             *)
(* exp (|x|^2 / 2) is the inverse of the density gauss_pdf of gauss m with    *)
(* respect to lebesgue_rV m.                                                  *)
(*                                                                            *)
(* Values are extended reals, the powers are poweR, and the products follow   *)
(* the conventions of MathComp-Analysis (0 * +oo = 0). The Gaussian form is   *)
(* a hypothesis of the section lebesgue_form until it is proved in            *)
(* brascamp_lieb.v.                                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section weighted_frame.
Context {R : realType} (m n : nat) (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R).
Hypothesis frame : \sum_i c i *: ((u i)^T *m u i) = 1%:M.

Lemma weighted_frame_mxdot (x : 'rV[R]_m) :
  mxdot x x = \sum_i c i * mxdot x (u i) ^+ 2.
Proof.
transitivity (mxdot x (x *m 1%:M)); first by rewrite mulmx1.
rewrite -frame mulmx_sumr mxdot_sumr; apply: eq_bigr => i _.
rewrite -scalemxAr mulmxA [x *m (u i)^T]mx11_scalar mul_scalar_mx -mxdot_rowE.
by rewrite !mxdotZr expr2.
Qed.

Lemma weighted_frame_trace :
  (forall i, mxdot (u i) (u i) = 1) -> \sum_i c i = m%:R.
Proof.
move=> hu; transitivity (\tr (1%:M : 'M[R]_m)); last exact: mxtrace1.
rewrite -frame raddf_sum; apply: eq_bigr => i _ /=.
by rewrite mxtraceZ mxtrace_mulC -mxdot_trace hu mulr1.
Qed.

End weighted_frame.

Section lebesgue_form.
Context {R : realType}.

(* The Gaussian form of the Brascamp-Lieb inequality, as stated in the
   header of brascamp_lieb.v. *)
Hypothesis gauss_brascamp_lieb : forall m n (u : 'I_n -> 'rV[R]_m)
    (c : 'I_n -> R) (F : 'I_n -> R -> \bar R),
  (forall i, mxdot (u i) (u i) = 1) -> (forall i, 0 < c i) ->
  \sum_i c i *: ((u i)^T *m u i) = 1%:M ->
  (forall i, measurable_fun [set: R] (F i)) ->
  (forall i t, 0 <= F i t)%E ->
  (\int[gauss m]_x \prod_i F i (mxdot x (u i)) `^ c i <=
   \prod_i (\int[normal_prob 0 1]_t F i t) `^ c i)%E.

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
  rewrite -powR_sum// -expR_sum (weighted_frame_trace hframe hu).
  rewrite powR_mulrn ?sqrtr_ge0//.
  rewrite /gauss_pdf invfM invrK -expRN mulNr opprK.
  congr (_ * expR _).
  rewrite (weighted_frame_mxdot hframe x) mulr_suml.
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

End lebesgue_form.
