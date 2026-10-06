From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import partial_derivative gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import gauss_smoothing slepian.

(**md**************************************************************************)
(* # The law of a linear image of a Gaussian vector                           *)
(*                                                                            *)
(* For x of law gauss n and A an n x k matrix, x *m A is a centered Gaussian  *)
(* vector with covariance A^T *m A. Its law depends only on that covariance:  *)
(* if A^T *m A = B^T *m B, with B an m x k matrix, then                       *)
(* gauss n [set x | X (x *m A)] = gauss m [set y | X (y *m B)] for every      *)
(* measurable set X of 'rV[R]_k (gauss_mulmx_law). When the columns of A are  *)
(* orthonormal, x *m A has law gauss k (gauss_orthogonal_law); in particular  *)
(* gauss n is invariant under every orthogonal matrix. The integral forms are *)
(* ge0_integral_gauss_mulmx and integral_gauss_orthogonal.                    *)
(*                                                                            *)
(* The proof goes through test functions. Kahane's comparison inequality,     *)
(* applied in both directions, gives equal expectations to every test of      *)
(* class C^2 with polynomially bounded derivatives (gauss_law_smooth). A      *)
(* bounded Lipschitz function G is the uniform limit of its double Gaussian   *)
(* smoothings gauss_smooth t (gauss_smooth t G), which are of class C^2       *)
(* because Gaussian integration by parts moves the derivative inside the      *)
(* second smoothing (gauss_smooth_partial_stein); hence the expectations of G *)
(* agree too (gauss_law_lipschitz). Finally a finite measure on 'rV[R]_k is   *)
(* determined by the integrals of the Lipschitz functions with values in      *)
(* [0, 1] (measure_lipschitz_unique): the sets {Phi > 0}, for Phi nonnegative *)
(* and Lipschitz, are closed under intersection, generate the Borel sets      *)
(* (measurable_lipschitz_pos), and their indicators are nondecreasing limits  *)
(* of min 1 (i Phi).                                                          *)
(*                                                                            *)
(* ```                                                                        *)
(* lipschitz_pos == the sets [set x | 0 < Phi x], for Phi : 'rV[R]_k -> R     *)
(*                  nonnegative and Lipschitz for the Euclidean norm          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section affine_derive.
Context {R : realType} {n : nat}.

(* The derivative of y |-> F (x + c y) along a coordinate. *)
Lemma is_derive_affine_comp (F : 'rV[R]_n -> R) (x y : 'rV[R]_n) (c d : R) j :
  is_derive (x + c *: y) (delta_mx 0 j) F d ->
  is_derive y (delta_mx 0 j) (fun y => F (x + c *: y)) (c * d).
Proof.
move=> Fd.
have G0 : is_derive (0 + c * 0 : R) 1
    (fun t : R => F (t *: delta_mx 0 j + (x + c *: y))) d.
  rewrite mulr0 addr0.
  apply: (is_derive_transfer (G := F) (b := x + c *: y) (w := delta_mx 0 j)) => // h.
  by rewrite addr0 -[h%:A]/(h * 1) mulr1.
have G1 := @is_derive1_comp R (fun t : R => F (t *: delta_mx 0 j + (x + c *: y)))
  (fun h : R => 0 + c * h) 0 _ _ G0 (is_derive_affine 0 c 0).
apply: (is_derive_transfer (G := (fun t : R => F (t *: delta_mx 0 j + (x + c *: y))) \o
  (fun h : R => 0 + c * h)) (b := 0) (w := 1)).
  move=> h /=; rewrite addr0 add0r -[h%:A]/(h * 1) mulr1.
  by congr F; rewrite scalerDr scalerA addrCA.
by rewrite mulrC in G1.
Qed.

End affine_derive.

(* The partial derivatives of the Gaussian smoothing of a bounded Lipschitz
   function are bounded and Lipschitz. *)
Section smooth_partial.
Context {R : realType} {n : nat}.
Variables (G : 'rV[R]_n -> R) (K L eps : R).
Hypothesis GK : forall x, `|G x| <= K.
Hypothesis GL : forall x y, `|G x - G y| <= L * frobenius (x - y).
Hypothesis eps0 : 0 < eps.

Let K0 : 0 <= K := le_trans (normr_ge0 _) (GK 0).
Let mG : measurable_fun [set: 'rV[R]_n] G :=
  continuous_measurable_mx (lipschitz_frobenius_continuous GL).
Let iF := @integrable_gauss_frobenius R n.

Let mGc x j : measurable_fun [set: 'rV[R]_n] (fun y => G (x + eps *: y) * y 0 j).
Proof.
apply: measurable_funM; last exact: measurable_mxentry.
apply: measurableT_comp mG _; apply: measurable_addmx; first exact: measurable_cst.
by apply: measurable_scalemx => //; exact: measurable_cst.
Qed.

Let iGc x j :
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun y => G (x + eps *: y) * y 0 j)).
Proof.
apply: (integrable_gauss_poly (mGc x j) (C := K) (k := 1)) => y.
rewrite normrM expr1 mulrDr mulr1 (le_trans (ler_wpM2r (normr_ge0 _) (GK _)))//.
apply: (@le_trans _ _ (K * `|y|)); first by rewrite ler_wpM2l// mx_norm_entry_le.
by rewrite lerDr.
Qed.

Lemma gauss_smooth_partial_bounded j x :
  `|gauss_smooth_partial eps G j x| <=
  eps^-1 * K * \int[gauss n]_y frobenius (y : 'rV[R]_n).
Proof.
rewrite /gauss_smooth_partial normrM ger0_norm ?invr_ge0 ?(ltW eps0)// -mulrA.
apply: ler_wpM2l; first by rewrite invr_ge0 ltW.
rewrite (le_trans (le_normr_Rintegral _ _))// -RintegralZl//.
apply: le_Rintegral => //.
- apply: (le_integrable measurableT _ _ (iGc x j)).
    exact/measurable_EFinP/measurableT_comp.
  by move=> y _; rewrite /comp lee_fin normr_id.
- have := integrableZl measurableT K iF.
  by apply: eq_integrable => // y _; rewrite /= EFinM.
- move=> y _; rewrite normrM ler_pM// (le_trans (frobenius_entry y 0 j))//.
Qed.

Lemma gauss_smooth_partial_lipschitz j x x' :
  `|gauss_smooth_partial eps G j x - gauss_smooth_partial eps G j x'| <=
  eps^-1 * L * \int[gauss n]_y frobenius (y : 'rV[R]_n) * frobenius (x - x').
Proof.
have c0 : 0 <= L * frobenius (x - x').
  by rewrite (le_trans _ (GL x x'))// normr_ge0.
rewrite /gauss_smooth_partial -mulrBr normrM ger0_norm ?invr_ge0 ?(ltW eps0)//.
rewrite -!mulrA; apply: ler_wpM2l; first by rewrite invr_ge0 ltW.
rewrite -RintegralB//.
have mD : measurable_fun [set: 'rV[R]_n]
    (fun y => G (x + eps *: y) * y 0 j - G (x' + eps *: y) * y 0 j).
  exact: measurable_funB.
have iD : (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun y => G (x + eps *: y) * y 0 j - G (x' + eps *: y) * y 0 j)).
  have := integrableB measurableT (iGc x j) (iGc x' j).
  by apply: eq_integrable => // y _; rewrite /= EFinB.
rewrite (le_trans (le_normr_Rintegral _ _))//.
rewrite mulrCA mulrC -RintegralZl//.
apply: le_Rintegral => //.
- apply: (le_integrable measurableT _ _ iD).
    exact/measurable_EFinP/measurableT_comp.
  by move=> y _; rewrite /comp lee_fin normr_id.
- have := integrableZl measurableT (L * frobenius (x - x')) iF.
  by apply: eq_integrable => // y _; rewrite /= EFinM.
- move=> y _; rewrite -mulrBl normrM.
  rewrite ler_pM ?normr_ge0//; last exact: (le_trans (frobenius_entry y 0 j)).
  rewrite (le_trans (GL _ _))//.
  by rewrite opprD addrACA subrr addr0.
Qed.

End smooth_partial.

(* Gaussian vectors with the same covariance give the same expectation to a
   test of class C^2 whose derivatives grow at most polynomially: Kahane's
   comparison inequality holds in both directions. *)
Section gauss_law_smooth.
Context {R : realType} {k : nat}.
Variables (F : 'rV[R]_k -> R) (DF : 'I_k -> 'rV[R]_k -> R)
  (D2F : 'I_k -> 'I_k -> 'rV[R]_k -> R).
Hypothesis F_partial : forall j z, is_derive z (delta_mx 0 j) F (DF j z).
Hypothesis DF_partial : forall j l z, is_derive z (delta_mx 0 l) (DF j) (D2F j l z).
Hypothesis D2F_cont : forall j l, continuous (D2F j l).
Variables (C : R) (p : nat).
Hypothesis F_poly : forall z, `|F z| <= C * (1 + `|z| ^+ p).
Hypothesis DF_poly : forall j z, `|DF j z| <= C * (1 + `|z| ^+ p).
Hypothesis D2F_poly : forall j l z, `|D2F j l z| <= C * (1 + `|z| ^+ p).

Theorem gauss_law_smooth n m (A : 'M[R]_(n, k)) (B : 'M[R]_(m, k)) :
  A^T *m A = B^T *m B ->
  (\int[gauss n]_x (F (x *m A))%:E = \int[gauss m]_y (F (y *m B))%:E)%E.
Proof.
have S0 n' m' (A' : 'M[R]_(n', k)) (B' : 'M[R]_(m', k)) :
    A'^T *m A' = B'^T *m B' -> forall z,
    \sum_(j < k) \sum_(l < k) (A'^T *m A' - B'^T *m B') j l * D2F j l z <= 0.
  move=> -> z; rewrite subrr big1// => j _.
  by rewrite big1// => l _; rewrite mxE mul0r.
move=> AB; apply/eqP; rewrite eq_le; apply/andP; split.
  exact: (gauss_comparison_partial F_partial DF_partial D2F_cont F_poly DF_poly
    D2F_poly (S0 _ _ _ _ AB)).
exact: (gauss_comparison_partial F_partial DF_partial D2F_cont F_poly DF_poly
  D2F_poly (S0 _ _ _ _ (esym AB))).
Qed.

End gauss_law_smooth.

(* The double smoothing gauss_smooth delta (gauss_smooth eps G) of a bounded
   Lipschitz function G is of class C^2, with bounded derivatives. *)
Section double_smooth.
Context {R : realType} {k : nat}.
Variables (G : 'rV[R]_k -> R) (K L eps delta : R).
Hypothesis GK : forall x, `|G x| <= K.
Hypothesis GL : forall x y, `|G x - G y| <= L * frobenius (x - y).
Hypothesis eps0 : 0 < eps.
Hypothesis delta0 : 0 < delta.

Local Notation Ey := (\int[gauss k]_y frobenius (y : 'rV[R]_k)).
Local Notation F := (gauss_smooth eps G).
Local Notation Fj j := (gauss_smooth_partial eps G j).

Let FK x : `|F x| <= K := gauss_smooth_bounded eps GK GL x.
Let FL x y : `|F x - F y| <= L * frobenius (x - y) :=
  gauss_smooth_lipschitz eps GK GL x y.
Let FjK j x : `|Fj j x| <= eps^-1 * K * Ey :=
  gauss_smooth_partial_bounded GK GL eps0 j x.
Let FjL j x y : `|Fj j x - Fj j y| <= eps^-1 * L * Ey * frobenius (x - y) :=
  gauss_smooth_partial_lipschitz GK GL eps0 j x y.
Let Fd x j : is_derive x (delta_mx 0 j) F (Fj j x) := gauss_smooth_derive GK GL eps0 x j.

Let K0 : 0 <= K := le_trans (normr_ge0 _) (GK 0).
Let Ey0 : 0 <= Ey.
Proof. by apply: Rintegral_ge0 => // y _; exact: frobenius_ge0. Qed.
Let Kj0 : 0 <= eps^-1 * K * Ey.
Proof. by rewrite !mulr_ge0// invr_ge0 ltW. Qed.

(* Gaussian integration by parts swaps the smoothing and the derivative. *)
Lemma gauss_smooth_partial_stein j x :
  gauss_smooth_partial delta F j x = gauss_smooth delta (Fj j) x.
Proof.
have shift (H : 'rV[R]_k -> R) (M : R) :
    (forall y y', `|H y - H y'| <= M * frobenius (y - y')) ->
    forall y y', `|H (x + delta *: y) - H (x + delta *: y')| <=
      M * delta * frobenius (y - y').
  move=> HL y y'; rewrite (le_trans (HL _ _))// opprD addrACA subrr add0r.
  by rewrite -scalerBr frobeniusZ gtr0_norm// mulrA.
have cFa : continuous (fun y : 'rV[R]_k => F (x + delta *: y)).
  exact: lipschitz_frobenius_continuous (shift _ _ FL).
have cFja : continuous (fun y : 'rV[R]_k => delta * Fj j (x + delta *: y)).
  apply: (@lipschitz_frobenius_continuous _ _ _ (delta * (eps^-1 * L * Ey * delta))).
  move=> y y'; rewrite -mulrBr normrM gtr0_norm// -mulrA ler_wpM2l ?(ltW delta0)//.
  exact: (shift _ _ (FjL j)).
have Pd y : is_derive y (delta_mx 0 j) (fun y => F (x + delta *: y))
    (delta * Fj j (x + delta *: y)).
  exact: is_derive_affine_comp (Fd _ j).
have h := @gauss_ibp R k j (fun y => F (x + delta *: y))
  (fun y => delta * Fj j (x + delta *: y)) (K + delta * (eps^-1 * K * Ey)) 0 Pd cFa cFja.
set C := K + _ in h.
have C0 : 0 <= C by rewrite /C addr_ge0// mulr_ge0// ltW.
have Cb c (y : 'rV[R]_k) : c <= C -> c <= C * (1 + `|y| ^+ 0).
  by move=> cC; rewrite expr0 mulrDr mulr1 (le_trans cC)// lerDl.
have e : (\int[gauss k]_y (y 0 j * F (x + delta *: y))%:E =
    \int[gauss k]_y (delta * Fj j (x + delta *: y))%:E)%E.
  apply: h => y; apply: Cb.
    by rewrite (le_trans (FK _))// /C lerDl mulr_ge0// ltW.
  rewrite normrM gtr0_norm// (le_trans _ (_ : delta * (eps^-1 * K * Ey) <= C))//.
    by rewrite ler_wpM2l ?(ltW delta0)// FjK.
  by rewrite /C lerDr.
have cFj : continuous (fun y : 'rV[R]_k => Fj j (x + delta *: y)).
  exact: lipschitz_frobenius_continuous (shift _ _ (FjL j)).
have iFj : (gauss k).-integrable [set: 'rV[R]_k]
    (EFin \o (fun y => Fj j (x + delta *: y))).
  apply: (integrable_gauss_bounded (C := eps^-1 * K * Ey)); last by move=> y; exact: FjK.
  exact: continuous_measurable_mx cFj.
rewrite /gauss_smooth_partial /gauss_smooth.
have -> : \int[gauss k]_y (F (x + delta *: y) * y 0 j) =
    \int[gauss k]_y (delta * Fj j (x + delta *: y)).
  rewrite /Rintegral -e; congr fine; apply: eq_integral => y _.
  by rewrite mulrC.
by rewrite RintegralZl// mulKf// gt_eqF.
Qed.

Local Notation H := (gauss_smooth delta F).

Let H_partial j z : is_derive z (delta_mx 0 j) H (gauss_smooth delta (Fj j) z).
Proof.
by rewrite -gauss_smooth_partial_stein; exact: (gauss_smooth_derive FK FL delta0).
Qed.

Let DH_partial j l z : is_derive z (delta_mx 0 l) (gauss_smooth delta (Fj j))
  (gauss_smooth_partial delta (Fj j) l z).
Proof. exact: (gauss_smooth_derive (FjK j) (FjL j) delta0). Qed.

Let D2H_cont j l : continuous (gauss_smooth_partial delta (Fj j) l).
Proof. exact: (continuous_gauss_smooth_partial (FjK j) (FjL j) delta0). Qed.

Let Kjj0 : 0 <= delta^-1 * (eps^-1 * K * Ey) * Ey.
Proof. by rewrite !mulr_ge0// invr_ge0 ltW. Qed.

Let C := K + eps^-1 * K * Ey + delta^-1 * (eps^-1 * K * Ey) * Ey.

Let Cb c (z : 'rV[R]_k) : c <= C -> c <= C * (1 + `|z| ^+ 0).
Proof.
have C0 : 0 <= C by rewrite /C !addr_ge0.
by move=> cC; rewrite expr0 mulrDr mulr1 (le_trans cC)// lerDl.
Qed.

Let H_poly z : `|H z| <= C * (1 + `|z| ^+ 0).
Proof.
apply: Cb; rewrite (le_trans (gauss_smooth_bounded delta FK FL z))// /C -addrA.
by rewrite lerDl addr_ge0.
Qed.

Let DH_poly j z : `|gauss_smooth delta (Fj j) z| <= C * (1 + `|z| ^+ 0).
Proof.
apply: Cb; rewrite (le_trans (gauss_smooth_bounded delta (FjK j) (FjL j) z))// /C.
by rewrite -addrA [K + _]addrC -addrA lerDl addr_ge0.
Qed.

Let D2H_poly j l z :
  `|gauss_smooth_partial delta (Fj j) l z| <= C * (1 + `|z| ^+ 0).
Proof.
apply: Cb; rewrite (le_trans (gauss_smooth_partial_bounded (FjK j) (FjL j) delta0 l z))//.
by rewrite /C lerDr addr_ge0.
Qed.

(* The double smoothing of G has the same expectation under two Gaussian
   vectors with the same covariance. *)
Lemma gauss_law_double_smooth n m (A : 'M[R]_(n, k)) (B : 'M[R]_(m, k)) :
  A^T *m A = B^T *m B ->
  \int[gauss n]_x H (x *m A) = \int[gauss m]_y H (y *m B).
Proof.
move=> AB; rewrite /Rintegral; congr fine.
exact: (gauss_law_smooth H_partial DH_partial D2H_cont H_poly DH_poly D2H_poly AB).
Qed.

End double_smooth.

Section gauss_law_lipschitz.
Context {R : realType}.

Lemma normr_Rintegral_gauss_le n (f : 'rV[R]_n -> R) (c : R) :
  measurable_fun [set: 'rV[R]_n] f -> (forall x, `|f x| <= c) ->
  `|\int[gauss n]_x f x| <= c.
Proof.
move=> mf fc; have c0 : 0 <= c := le_trans (normr_ge0 _) (fc 0).
have mA : measurable_fun [set: 'rV[R]_n] (fun x => `|f x|) by exact: measurableT_comp.
rewrite (le_trans (le_normr_Rintegral _ _))//; first exact: integrable_gauss_bounded mf fc.
apply: (@le_trans _ _ (\int[gauss n]_x c)); last first.
  by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
apply: le_Rintegral => //.
- by apply: (integrable_gauss_bounded (C := c) mA) => x; rewrite normr_id.
- by apply: (integrable_gauss_bounded (C := c)) => // x; rewrite ger0_norm.
Qed.

Lemma lipschitz_frobenius_mulmx n k (f : 'rV[R]_k -> R) (L : R) (A : 'M[R]_(n, k)) :
  (forall x y, `|f x - f y| <= L * frobenius (x - y)) ->
  forall x y : 'rV[R]_n,
    `|f (x *m A) - f (y *m A)| <= `|L| * frobenius A * frobenius (x - y).
Proof.
move=> fL x y; rewrite (le_trans (fL _ _))// -mulmxBl.
apply: (le_trans (ler_wpM2r (frobenius_ge0 _) (ler_norm L))).
by rewrite -mulrA ler_wpM2l// [frobenius A * _]mulrC frobenius_mulmx.
Qed.

(* Gaussian vectors with the same covariance give the same expectation to
   every bounded Lipschitz function. *)
Theorem gauss_law_lipschitz n m k (A : 'M[R]_(n, k)) (B : 'M[R]_(m, k))
    (G : 'rV[R]_k -> R) (K L : R) :
  (forall x, `|G x| <= K) -> (forall x y, `|G x - G y| <= L * frobenius (x - y)) ->
  A^T *m A = B^T *m B ->
  \int[gauss n]_x G (x *m A) = \int[gauss m]_y G (y *m B).
Proof.
move=> GK GL0 AB.
have GL x y : `|G x - G y| <= `|L| * frobenius (x - y).
  exact: le_trans (GL0 x y) (ler_wpM2r (frobenius_ge0 _) (ler_norm L)).
set Ey := \int[gauss k]_y frobenius (y : 'rV[R]_k).
have Ey0 : 0 <= Ey by apply: Rintegral_ge0 => // y _; exact: frobenius_ge0.
pose H t := gauss_smooth t (gauss_smooth t G).
have HK t z : `|H t z| <= K.
  exact: gauss_smooth_bounded (gauss_smooth_bounded t GK GL)
    (gauss_smooth_lipschitz t GK GL) z.
have HG t : 0 < t -> forall z, `|H t z - G z| <= `|L| * t * Ey + `|L| * t * Ey.
  move=> t0 z.
  have -> : H t z - G z = (H t z - gauss_smooth t G z) + (gauss_smooth t G z - G z).
    by rewrite addrA subrK.
  rewrite (le_trans (ler_normD _ _))// lerD//.
    exact: (gauss_smooth_close (gauss_smooth_bounded t GK GL)
      (gauss_smooth_lipschitz t GK GL) t0).
  exact: (gauss_smooth_close GK GL t0).
have cH t : continuous (H t).
  exact: lipschitz_frobenius_continuous (gauss_smooth_lipschitz t
    (gauss_smooth_bounded t GK GL) (gauss_smooth_lipschitz t GK GL)).
have cG : continuous G := lipschitz_frobenius_continuous GL.
have mC n' (C : 'M[R]_(n', k)) (f : 'rV[R]_k -> R) : continuous f ->
    measurable_fun [set: 'rV[R]_n'] (fun x => f (x *m C)).
  move=> cf; apply: measurableT_comp (continuous_measurable_mx cf) _.
  by apply: measurable_mulmx => //; exact: measurable_cst.
have close n' (C : 'M[R]_(n', k)) t : 0 < t ->
    `|\int[gauss n']_x G (x *m C) - \int[gauss n']_x H t (x *m C)| <=
    `|L| * t * Ey + `|L| * t * Ey.
  move=> t0; rewrite -RintegralB//.
  - exact: (integrable_gauss_bounded (mC _ _ _ cG) (fun x => GK _)).
  - exact: (integrable_gauss_bounded (mC _ _ _ (cH t)) (fun x => HK t _)).
  apply: normr_Rintegral_gauss_le.
    exact: measurable_funB (mC _ _ _ cG) (mC _ _ _ (cH t)).
  by move=> x; rewrite distrC; exact: HG.
apply/eqP; rewrite -subr_eq0 -normr_le0; apply/ler_addgt0Pr => e e0; rewrite add0r.
have d0 : 0 < 4 * (`|L| * Ey) + 1 by rewrite (lt_le_trans ltr01)// lerDr !mulr_ge0.
pose t := e / (4 * (`|L| * Ey) + 1).
have t0 : 0 < t by rewrite /t divr_gt0.
have -> : \int[gauss n]_x G (x *m A) - \int[gauss m]_y G (y *m B) =
    (\int[gauss n]_x G (x *m A) - \int[gauss n]_x H t (x *m A)) -
    (\int[gauss m]_y G (y *m B) - \int[gauss m]_y H t (y *m B)).
  rewrite (gauss_law_double_smooth GK GL t0 t0 AB).
  by rewrite opprB addrA subrK.
rewrite (le_trans (ler_normB _ _))//.
apply: (le_trans (lerD (close _ A t t0) (close _ B t t0))).
have -> : `|L| * t * Ey + `|L| * t * Ey + (`|L| * t * Ey + `|L| * t * Ey) =
    4 * (`|L| * Ey) * t by ring.
rewrite /t [_ * (e / _)]mulrA ler_pdivrMr//.
by rewrite mulrDr mulr1 mulrC lerDl ltW.
Qed.

End gauss_law_lipschitz.

(* A finite measure on row vectors is determined by the integrals of the
   Lipschitz functions with values in [0, 1]. The sets {Phi > 0}, for Phi
   nonnegative and Lipschitz, are closed under intersection and generate the
   Borel sets; the indicator of {Phi > 0} is the nondecreasing limit of
   min 1 (i Phi). *)
Section lipschitz_unique.
Context {R : realType} {k : nat}.

Definition lipschitz_pos : set (set 'rV[R]_k) :=
  [set [set x | 0 < Phi x] | Phi in [set Phi : 'rV[R]_k -> R |
    (forall x, 0 <= Phi x) /\
    exists L, forall x y, `|Phi x - Phi y| <= L * frobenius (x - y)]].

Lemma minr_dist (a b c d : R) :
  `|Num.min a b - Num.min c d| <= `|a - c| + `|b - d|.
Proof.
have [h1 h2] : a - c <= `|a - c| /\ c - a <= `|a - c|.
  by split; [exact: ler_norm|rewrite distrC; exact: ler_norm].
have [h3 h4] : b - d <= `|b - d| /\ d - b <= `|b - d|.
  by split; [exact: ler_norm|rewrite distrC; exact: ler_norm].
have h5 := normr_ge0 (a - c); have h6 := normr_ge0 (b - d).
rewrite ler_norml !minEle.
by case: (leP a b); case: (leP c d) => * /=; apply/andP; split; lra.
Qed.

Lemma maxr_dist (a b c d : R) :
  `|Num.max a b - Num.max c d| <= `|a - c| + `|b - d|.
Proof.
have [h1 h2] : a - c <= `|a - c| /\ c - a <= `|a - c|.
  by split; [exact: ler_norm|rewrite distrC; exact: ler_norm].
have [h3 h4] : b - d <= `|b - d| /\ d - b <= `|b - d|.
  by split; [exact: ler_norm|rewrite distrC; exact: ler_norm].
have h5 := normr_ge0 (a - c); have h6 := normr_ge0 (b - d).
rewrite ler_norml !maxEle.
by case: (leP a b); case: (leP c d) => * /=; apply/andP; split; lra.
Qed.

Lemma measurable_pos (Phi : 'rV[R]_k -> R) (L : R) :
  (forall x y, `|Phi x - Phi y| <= L * frobenius (x - y)) ->
  measurable [set x | 0 < Phi x].
Proof.
move=> PL; have mP := continuous_measurable_mx (lipschitz_frobenius_continuous PL).
have := mP measurableT _ (measurable_itv `]0, +oo[); rewrite setTI.
by congr measurable; apply/seteqP; split => x /=; rewrite in_itv/= andbT.
Qed.

Lemma setI_closed_lipschitz_pos : setI_closed lipschitz_pos.
Proof.
move=> _ _ [P [P0 [L PL]] <-] [Q [Q0 [M QL]] <-].
exists (fun x => Num.min (P x) (Q x)).
  split=> [x|]; first by rewrite le_min P0 Q0.
  exists (`|L| + `|M|) => x y; rewrite (le_trans (minr_dist _ _ _ _))// mulrDl.
  apply: lerD.
    exact: le_trans (PL x y) (ler_wpM2r (frobenius_ge0 _) (ler_norm L)).
  exact: le_trans (QL x y) (ler_wpM2r (frobenius_ge0 _) (ler_norm M)).
by apply/seteqP; split => x /=; rewrite lt_min => /andP.
Qed.

Lemma lipschitz_pos_setT : lipschitz_pos [set: 'rV[R]_k].
Proof.
exists (fun _ => 1); last by apply/seteqP; split => x //= _; exact: ltr01.
split=> [_|]; first exact: ler01.
by exists 0 => x y; rewrite subrr normr0 mul0r.
Qed.

Lemma measurable_lipschitz_pos : measurable = <<s lipschitz_pos >>.
Proof.
apply/seteqP; split; last first.
  apply: smallest_sub; first exact: sigma_algebra_measurable.
  by move=> _ [P [_ [L PL]] <-]; exact: measurable_pos PL.
pose T := g_sigma_algebraType lipschitz_pos.
have mid : measurable_fun [set: T] (fun x : T => x : 'rV[R]_k).
  apply/measurable_fun_mxP => i j.
  apply: (measurability _ (RGenInftyO.measurableE R)) => _ [_ [c ->] <-].
  rewrite setTI; apply: sub_sigma_algebra.
  exists (fun x : 'rV[R]_k => Num.max 0 (c - x i j)).
    split=> [x|]; first by rewrite le_max lexx.
    exists 1 => x y; rewrite mul1r (le_trans (maxr_dist _ _ _ _))// subrr normr0 add0r.
    have -> : c - x i j - (c - y i j) = - (x - y) i j by rewrite !mxE; ring.
    by rewrite normrN frobenius_entry.
  by apply/seteqP; split => x /=; rewrite in_itv/= lt_max ltxx/= subr_gt0.
by move=> X mX; have := mid measurableT X mX; rewrite setTI.
Qed.

Lemma lipschitz_pos_agree (mu1 mu2 : {measure set 'rV[R]_k -> \bar R}) :
  (forall (Phi : 'rV[R]_k -> R) (L : R), (forall x, 0 <= Phi x <= 1) ->
     (forall x y, `|Phi x - Phi y| <= L * frobenius (x - y)) ->
     (\int[mu1]_x (Phi x)%:E = \int[mu2]_x (Phi x)%:E)%E) ->
  forall A, lipschitz_pos A -> mu1 A = mu2 A.
Proof.
move=> h _ [P [P0 [L PL]] <-].
have mA := measurable_pos PL.
pose phi (i : nat) x := Num.min 1 (i%:R * P x).
have phi01 i x : 0 <= phi i x <= 1.
  by rewrite /phi le_min ge_min lexx ler01 mulr_ge0.
have phiL i x y : `|phi i x - phi i y| <= (i%:R * `|L|) * frobenius (x - y).
  rewrite /phi (le_trans (minr_dist _ _ _ _))// subrr normr0 add0r -mulrBr normrM.
  rewrite normr_nat -mulrA ler_wpM2l//.
  exact: le_trans (PL x y) (ler_wpM2r (frobenius_ge0 _) (ler_norm L)).
have mphi i : measurable_fun [set: 'rV[R]_k] (fun x => (phi i x)%:E).
  apply/measurable_EFinP; apply: continuous_measurable_mx.
  exact: lipschitz_frobenius_continuous (phiL i).
have nd x : {homo (fun i => (phi i x)%:E) : i j / (i <= j)%N >-> (i <= j)%E}.
  move=> i j ij; rewrite lee_fin /phi le_min ge_min lexx/=.
  by rewrite ge_min (ler_wpM2r (P0 x))// ?ler_nat// orbT.
have lim x : limn (fun i => (phi i x)%:E) = (\1_[set x | 0 < P x] x)%:E.
  apply/cvg_lim => //; rewrite indicE.
  have [Px0|Px0] := ltP 0 (P x).
    rewrite mem_set//.
    have [N HN] : exists N : nat, (P x)^-1 < N%:R.
      by eexists; apply: archimedean.Num.Theory.archi_boundP; rewrite invr_ge0 ltW.
    apply: cvg_near_cst; near=> i.
    rewrite /phi; congr EFin; apply/min_idPl.
    rewrite -ler_pdivrMr// div1r (le_trans (ltW HN))// ler_nat.
    by near: i; exact: nbhs_infty_ge.
  have nPx : ~ [set x0 | 0 < P x0] x.
    by move=> /= Px; have := lt_le_trans Px Px0; rewrite ltxx.
  rewrite (memNset nPx).
  have Px : P x = 0 by apply/le_anti; rewrite Px0 P0.
  apply: cvg_near_cst; apply: nearW => i.
  by rewrite /phi Px mulr0; congr EFin; apply/min_idPr; exact: ler01.
have int (mu : {measure set 'rV[R]_k -> \bar R}) :
    mu [set x | 0 < P x] = limn (fun i => (\int[mu]_x (phi i x)%:E)%E).
  rewrite -(setIT [set x | 0 < P x]) -integral_indic//.
  rewrite -(monotone_convergence mu measurableT mphi).
  - by move=> i x _; rewrite lee_fin; case/andP: (phi01 i x).
  - by move=> x _; exact: nd x.
  - by apply: eq_integral => x _; rewrite lim.
rewrite !int (_ : (fun i => (\int[mu1]_x (phi i x)%:E)%E) =
  (fun i => (\int[mu2]_x (phi i x)%:E)%E))//.
by apply/funext => i; exact: h (phi01 i) (phiL i).
Unshelve. all: by end_near.
Qed.

Theorem measure_lipschitz_unique (mu1 mu2 : {measure set 'rV[R]_k -> \bar R}) :
  (mu1 [set: 'rV[R]_k] < +oo)%E ->
  (forall (Phi : 'rV[R]_k -> R) (L : R), (forall x, 0 <= Phi x <= 1) ->
     (forall x y, `|Phi x - Phi y| <= L * frobenius (x - y)) ->
     (\int[mu1]_x (Phi x)%:E = \int[mu2]_x (Phi x)%:E)%E) ->
  forall X, measurable X -> mu1 X = mu2 X.
Proof.
move=> mu1T h; apply: (measure_unique lipschitz_pos (fun=> [set: 'rV[R]_k])).
- exact: measurable_lipschitz_pos.
- exact: setI_closed_lipschitz_pos.
- by move=> _; exact: lipschitz_pos_setT.
- by rewrite bigcup_const.
- exact: lipschitz_pos_agree.
- by move=> _.
Qed.

End lipschitz_unique.

(* The law of x *m A, for x of law gauss n, depends only on A^T *m A: two
   centered Gaussian vectors with the same covariance have the same law. *)
Section gauss_mulmx_law.
Context {R : realType}.

Theorem gauss_mulmx_law n m k (A : 'M[R]_(n, k)) (B : 'M[R]_(m, k)) X :
  A^T *m A = B^T *m B -> measurable X ->
  gauss n [set x | X (x *m A)] = gauss m [set y | X (y *m B)].
Proof.
move=> AB mX.
have mA : measurable_fun [set: 'rV[R]_n] (fun x => x *m A).
  by apply: measurable_mulmx => //; exact: measurable_cst.
have mB : measurable_fun [set: 'rV[R]_m] (fun y => y *m B).
  by apply: measurable_mulmx => //; exact: measurable_cst.
pose mu1 : {measure set 'rV[R]_k -> \bar R} := pushforward (gauss n) (fun x => x *m A).
pose mu2 : {measure set 'rV[R]_k -> \bar R} := pushforward (gauss m) (fun y => y *m B).
have mu1T : (mu1 mA [set: 'rV[R]_k] < +oo)%E.
  have -> : mu1 mA [set: 'rV[R]_k] = gauss n [set: 'rV[R]_n] by [].
  by rewrite probability_setT ltry.
apply: (@measure_lipschitz_unique R k (mu1 mA) (mu2 mB) mu1T _ X mX) => Phi L P01 PL.
have cPhi : continuous Phi := lipschitz_frobenius_continuous PL.
have mPhi : measurable_fun [set: 'rV[R]_k] (fun y => (Phi y)%:E).
  by apply/measurable_EFinP; exact: continuous_measurable_mx cPhi.
have Phi0 : {in [set: 'rV[R]_k], forall y, (0 <= (Phi y)%:E)%E}.
  by move=> y _; rewrite lee_fin; case/andP: (P01 y).
rewrite /mu1 /mu2 !ge0_integral_pushforward// !preimage_setT.
have PK x : `|Phi x| <= 1 by rewrite ger0_norm; case/andP: (P01 x).
have iC n' (C : 'M[R]_(n', k)) :
    (gauss n').-integrable [set: 'rV[R]_n'] (EFin \o (fun x => Phi (x *m C))).
  apply: (integrable_gauss_bounded (C := 1)) => //.
  apply: measurableT_comp (continuous_measurable_mx cPhi) _.
  by apply: measurable_mulmx => //; exact: measurable_cst.
have eA : (\int[gauss n]_x (Phi (x *m A))%:E)%E = (\int[gauss n]_x Phi (x *m A))%:E.
  by rewrite fineK// (integrable_fin_num _ (iC _ A)).
have eB : (\int[gauss m]_x (Phi (x *m B))%:E)%E = (\int[gauss m]_x Phi (x *m B))%:E.
  by rewrite fineK// (integrable_fin_num _ (iC _ B)).
transitivity ((\int[gauss n]_x Phi (x *m A))%:E); first exact: eA.
transitivity ((\int[gauss m]_x Phi (x *m B))%:E); last exact: esym eB.
by congr EFin; exact: (gauss_law_lipschitz PK PL AB).
Qed.

(* If the columns of A are orthonormal, x *m A has law gauss k: in
   particular gauss n is invariant under every orthogonal matrix. *)
Corollary gauss_orthogonal_law n k (A : 'M[R]_(n, k)) X :
  A^T *m A = 1%:M -> measurable X -> gauss n [set x | X (x *m A)] = gauss k X.
Proof.
move=> A1 mX.
have A1' : A^T *m A = (1%:M : 'M[R]_k)^T *m 1%:M by rewrite A1 trmx1 mulmx1.
rewrite (gauss_mulmx_law A1' mX).
by congr (gauss k _); apply/seteqP; split => y /=; rewrite mulmx1.
Qed.

Corollary ge0_integral_gauss_mulmx n m k (A : 'M[R]_(n, k)) (B : 'M[R]_(m, k))
    (f : 'rV[R]_k -> \bar R) :
  A^T *m A = B^T *m B -> measurable_fun [set: 'rV[R]_k] f -> (forall y, 0 <= f y)%E ->
  (\int[gauss n]_x f (x *m A) = \int[gauss m]_y f (y *m B))%E.
Proof.
move=> AB mf f0.
have mA : measurable_fun [set: 'rV[R]_n] (fun x => x *m A).
  by apply: measurable_mulmx => //; exact: measurable_cst.
have mB : measurable_fun [set: 'rV[R]_m] (fun y => y *m B).
  by apply: measurable_mulmx => //; exact: measurable_cst.
have := ge0_integral_pushforward mA (gauss n) measurableT mf (fun y _ => f0 y).
rewrite preimage_setT => <-.
have := ge0_integral_pushforward mB (gauss m) measurableT mf (fun y _ => f0 y).
rewrite preimage_setT => <-.
by apply: eq_measure_integral => X mX _; exact: gauss_mulmx_law.
Qed.

Corollary integral_gauss_orthogonal n k (A : 'M[R]_(n, k)) (f : 'rV[R]_k -> \bar R) :
  A^T *m A = 1%:M -> (gauss k).-integrable [set: 'rV[R]_k] f ->
  (\int[gauss n]_x f (x *m A) = \int[gauss k]_y f y)%E.
Proof.
move=> A1; apply: integral_image.
- by apply: measurable_mulmx => //; exact: measurable_cst.
- by move=> X mX; exact: gauss_orthogonal_law.
Qed.

End gauss_mulmx_law.
