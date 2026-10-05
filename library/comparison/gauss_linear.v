From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix interval.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp Require Import ereal topology normedtype sequences exp numfun.
From mathcomp Require Import measure lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral gauss.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import normal_mgf normal_linear.

(**md**************************************************************************)
(* # Linear forms of a standard Gaussian vector                               *)
(*                                                                            *)
(* For x of law gauss n and a nonzero row vector a, the inner product mxdot x *)
(* a has law normal_prob 0 (frobenius a), the normal law with variance |a|^2  *)
(* (gauss_mxdot). Integrals of functions of mxdot x a are integrals against   *)
(* that law (ge0_integral_gauss_mxdot, integral_gauss_mxdot). The moment      *)
(* generating function of mxdot x a is expR (t^2 |a|^2 / 2) for every a       *)
(* (integral_gauss_expR_mxdot), and its tails are those of the normal law     *)
(* (gauss_mxdot_upper_tail, gauss_mxdot_abs_tail).                            *)
(*                                                                            *)
(* ```                                                                        *)
(*   row_tail a == the row of the coordinates 1, ..., n of a : 'rV[R]_n.+1    *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section normal_prob_normr.
Context {R : realType}.

Lemma normal_pdf_normr (m s x : R) : normal_pdf m `|s| x = normal_pdf m s x.
Proof.
rewrite /normal_pdf normr_eq0; case: ifP => // _.
by rewrite /normal_peak /normal_fun real_normK ?num_real.
Qed.

Lemma normal_prob_normr (m s : R) A : normal_prob m `|s| A = normal_prob m s A.
Proof. by rewrite /normal_prob; under eq_integral do rewrite normal_pdf_normr. Qed.

End normal_prob_normr.

Section row_tail.
Context {R : realType} (n : nat).

(* The coordinates 1, ..., n of a row vector of size n.+1. *)
Definition row_tail (a : 'rV[R]_n.+1) : 'rV[R]_n := \row_j a 0 (lift ord0 j).

Lemma mxdot_rV_cons (a : 'rV[R]_n.+1) t (v : 'rV[R]_n) :
  mxdot (rV_cons (t, v)) a = t * a 0 ord0 + mxdot v (row_tail a).
Proof.
rewrite /mxdot !big_ord1 big_ord_recl rV_cons0; congr (_ + _).
by apply: eq_bigr => j _; rewrite rV_consS mxE.
Qed.

Lemma mxdot_row_tail (a : 'rV[R]_n.+1) :
  mxdot a a = a 0 ord0 ^+ 2 + mxdot (row_tail a) (row_tail a).
Proof.
rewrite /mxdot !big_ord1 big_ord_recl expr2; congr (_ + _).
by apply: eq_bigr => j _; rewrite !mxE.
Qed.

End row_tail.

Section gauss_mxdot.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma measurable_mxdot n (a : 'rV[R]_n) :
  measurable_fun [set: 'rV[R]_n] (fun x => mxdot x a).
Proof.
rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
by apply: measurable_funM => //; exact: measurable_mxentry.
Qed.

Theorem gauss_mxdot n (a : 'rV[R]_n) (A : set R) : a != 0 -> measurable A ->
  gauss n [set x | A (mxdot x a)] = normal_prob 0 (frobenius a) A.
Proof.
elim: n a A => [|n IH] a A a0 mA.
  by move: a0; rewrite (_ : a = 0) ?eqxx//; apply/matrixP => i [].
rewrite gaussS; set a0' := a 0 ord0; set b := row_tail a.
have -> : @rV_cons R n @^-1` [set x | A (mxdot x a)] =
    [set p | A (a0' * p.1 + mxdot p.2 b)].
  by apply/seteqP; split => -[t v] /=; rewrite mxdot_rV_cons mulrC.
have fa : frobenius a = Num.sqrt (a0' ^+ 2 + frobenius b ^+ 2).
  by rewrite /frobenius sqr_sqrtr ?mxdot_ge0// -mxdot_row_tail.
have [b0|b0] := eqVneq b 0.
  have a00 : a0' != 0.
    apply: contra a0 => /eqP h; apply/eqP/matrixP => i j; rewrite (ord1 i) mxE.
    case: (unliftP ord0 j) => [k ->|->]//.
    by have := congr1 (fun M : 'rV_n => M 0 k) b0; rewrite /b mxE !mxE.
  have -> : [set p : R * 'rV_n | A (a0' * p.1 + mxdot p.2 b)] =
      ((fun t => a0' * t + 0) @^-1` A) `*` [set: 'rV[R]_n].
    apply/seteqP; split => -[t v] /=; rewrite b0 mxdot0r addr0 //.
    by case.
  rewrite product_measure1E//.
    by rewrite -[X in measurable X]setTI; apply: measurable_affine.
  rewrite [X in (_ * X)%E]probability_setT mule1.
  transitivity (normal_prob 0 1 ((fun t : R => a0' * t + 0) @^-1` A)); first by [].
  rewrite (normal_prob_affine 0 0 a00 (oner_neq0 R) mA) mulr0 add0r mulr1.
  by rewrite fa b0 frobenius0 expr0n /= addr0 sqrtr_sqr normal_prob_normr.
have fb0 : frobenius b != 0 by rewrite frobenius_eq0.
transitivity ((N \x normal_prob 0 (frobenius b))%E
    [set p | A (a0' * p.1 + 1 * p.2)]).
  rewrite /product_measure1 /=; apply: eq_integral => t _.
  have mA' : measurable [set y : R | A (a0' * t + y)].
    have -> : [set y : R | A (a0' * t + y)] = (fun y => 1 * y + a0' * t) @^-1` A.
      by apply/seteqP; split => y /=; rewrite mul1r addrC.
    by rewrite -[X in measurable X]setTI; apply: measurable_affine.
  have -> : xsection [set p | A (a0' * p.1 + 1 * p.2)] t =
      [set y : R | A (a0' * t + y)].
    by apply/seteqP; split => y; rewrite /xsection /= inE /= mul1r.
  rewrite -(IH b _ b0 mA'); congr (gauss n _).
  by apply/seteqP; split => v; rewrite /xsection /= inE.
rewrite (normal_prob_lincomb 0 0 a0' (oner_neq0 R) fb0 (oner_neq0 R) mA).
by rewrite !mulr0 addr0 expr1n !mulr1 mul1r fa.
Qed.

Lemma ge0_integral_gauss_mxdot n (a : 'rV[R]_n) (f : R -> \bar R) : a != 0 ->
    measurable_fun [set: R] f -> (forall y, (0 <= f y)%E) ->
  (\int[gauss n]_x f (mxdot x a) = \int[normal_prob 0 (frobenius a)]_y f y)%E.
Proof.
move=> a0 mf f0; pose phi : 'rV[R]_n -> measurableTypeR R := fun x => mxdot x a.
have mphi : measurable_fun [set: 'rV[R]_n] phi := measurable_mxdot a.
have := @ge0_integral_pushforward _ _ _ _ R _ mphi (gauss n) setT f measurableT mf.
move=> /(_ (fun y _ => f0 y)); rewrite preimage_setT => <-.
apply: (eq_measure_integral (normal_prob 0 (frobenius a))) => A mA _.
exact: (gauss_mxdot a0 mA).
Qed.

Lemma integrable_gauss_mxdot n (a : 'rV[R]_n) (f : R -> \bar R) : a != 0 ->
    measurable_fun [set: R] f ->
  (gauss n).-integrable [set: 'rV[R]_n] (fun x => f (mxdot x a)) <->
  (normal_prob 0 (frobenius a)).-integrable [set: R] f.
Proof.
move=> a0 mf.
have mfa : measurable_fun [set: 'rV[R]_n] (fun x => f (mxdot x a)).
  exact: measurableT_comp mf (measurable_mxdot a).
have E : (\int[gauss n]_x `|f (mxdot x a)| =
    \int[normal_prob 0 (frobenius a)]_y `|f y|)%E.
  by rewrite (@ge0_integral_gauss_mxdot n a (fun y => `|f y|%E) a0)//;
    exact: measurableT_comp.
by split => /integrableP[_ fi]; apply/integrableP; split => //; rewrite ?E// -E.
Qed.

Lemma integral_gauss_mxdot n (a : 'rV[R]_n) (f : R -> \bar R) : a != 0 ->
    (normal_prob 0 (frobenius a)).-integrable [set: R] f ->
  (\int[gauss n]_x f (mxdot x a) = \int[normal_prob 0 (frobenius a)]_y f y)%E.
Proof.
move=> a0 fi; have mf := measurable_int _ fi.
pose phi : 'rV[R]_n -> measurableTypeR R := fun x => mxdot x a.
have mphi : measurable_fun [set: 'rV[R]_n] phi := measurable_mxdot a.
have fai := (integrable_gauss_mxdot a0 mf).2 fi.
have := @integral_pushforward _ _ _ _ R _ mphi (gauss n) setT f mf.
rewrite preimage_setT => /(_ fai measurableT) <-.
apply: (eq_measure_integral (normal_prob 0 (frobenius a))) => A mA _.
exact: (gauss_mxdot a0 mA).
Qed.

Theorem integral_gauss_expR_mxdot n (a : 'rV[R]_n) t :
  (\int[gauss n]_x (expR (t * mxdot x a))%:E =
   (expR (t ^+ 2 * frobenius a ^+ 2 / 2))%:E)%E.
Proof.
have [->|a0] := eqVneq a 0.
  under eq_integral do rewrite mxdot0r mulr0 expR0.
  rewrite integral_cst// [X in (_ * X)%E]probability_setT mule1.
  by rewrite frobenius0 expr0n /= mulr0 mul0r expR0.
rewrite (@ge0_integral_gauss_mxdot n a (fun y => (expR (t * y))%:E) a0)//.
  by apply/measurable_EFinP; apply: measurableT_comp => //; exact: measurable_funM.
by rewrite integral_normal_expR ?frobenius_eq0// mulr0 add0r.
Qed.

Theorem gauss_mxdot_upper_tail n (a : 'rV[R]_n) (u : R) : a != 0 -> 0 <= u ->
  (gauss n [set x | u <= mxdot x a]%R <=
   (expR (- u ^+ 2 / (2 * frobenius a ^+ 2)))%:E)%E.
Proof.
move=> a0 u0; rewrite (gauss_mxdot a0 (A := [set y : R | u <= y])).
  by rewrite -set_itvcy; exact: measurable_itv.
have := @normal_prob_upper_tail R 0 (frobenius a) u.
by rewrite add0r; apply; rewrite ?frobenius_eq0.
Qed.

Theorem gauss_mxdot_abs_tail n (a : 'rV[R]_n) (u : R) : a != 0 -> 0 <= u ->
  (gauss n [set x | u <= `|mxdot x a|]%R <=
   (2 * expR (- u ^+ 2 / (2 * frobenius a ^+ 2)))%:E)%E.
Proof.
move=> a0 u0; rewrite (gauss_mxdot a0 (A := [set y : R | u <= `|y|])).
  have -> : [set y : R | u <= `|y|] = [set y | u <= y] `|` [set y | y <= - u].
    apply/seteqP; split => y /=; first by rewrite ler_normr => /orP[|]; [left|right; lra].
    by move=> [h|h]; rewrite ler_normr; apply/orP; [left|right; lra].
  by apply: measurableU; [rewrite -set_itvcy|rewrite -set_itvNyc]; exact: measurable_itv.
have := @normal_prob_abs_tail R 0 (frobenius a) u.
have -> : [set x : R | u <= `|x - 0|] = [set y | u <= `|y|].
  by apply/seteqP; split => y /=; rewrite subr0.
by apply; rewrite ?frobenius_eq0.
Qed.

End gauss_mxdot.
