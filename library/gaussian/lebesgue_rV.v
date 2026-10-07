From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix interval archimedean.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import reals ereal interval_inference topology.
From mathcomp Require Import normedtype sequences exp numfun measure trigo.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral.
From GaussianAnalysis.gaussian Require Import gauss.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import normal_linear.

(**md**************************************************************************)
(* # Lebesgue measure on row vectors                                          *)
(*                                                                            *)
(* lebesgue_rV n is Lebesgue measure on 'rV[R]_n, built as gauss n is: the    *)
(* image of the product of Lebesgue measure on the line (first coordinate)    *)
(* and lebesgue_rV n' (the others) under rV_cons. It is sigma-finite, gives   *)
(* a box the product of the lengths of its sides (lebesgue_rV_box), and it is *)
(* the only measure that does (lebesgue_rV_unique). Integrals against it are  *)
(* iterated integrals over the first coordinate and the others                *)
(* (ge0_integral_lebesgue_rV_cons), or over two blocks of coordinates         *)
(* (ge0_integral_lebesgue_rV_row_mx); the integral of a product of functions  *)
(* of the coordinates is the product of their integrals                       *)
(* (ge0_integral_lebesgue_rV_prod).                                           *)
(*                                                                            *)
(* It is invariant under translations (lebesgue_rV_shift) and permutations   *)
(* of the coordinates (lebesgue_rV_col_perm), and x |-> a x multiplies it by  *)
(* |a|^-n (lebesgue_rV_scale). The standard Gaussian measure gauss n has the  *)
(* density gauss_pdf with respect to it (ge0_integral_gauss_pdf,              *)
(* gauss_lebesgue_rV). Finally, the integral of                               *)
(* exp (- frobenius (x - z) ^ 2 / (2 s^2)) is (sqrt (2 pi) s)^n               *)
(* (lebesgue_rV_gauss_integral), and the closed Euclidean ball of radius r    *)
(* has measure at most (sqrt (2 pi e / n) r)^n (lebesgue_rV_ball_le). Here    *)
(* frobenius x is the Euclidean norm of x (matrix/euclidean.v), and           *)
(* frobenius x ^ 2 = mxdot x x.                                               *)
(*                                                                            *)
(* ```                                                                        *)
(* lebesgue_rV_cons m == the image of lebesgue_measure \x m under rV_cons,    *)
(*                       for a sigma-finite measure m on 'rV[R]_n             *)
(*  lebesgue_rV_rec n == Lebesgue measure on 'rV[R]_n as a sigma-finite       *)
(*                       measure, by recursion on n                           *)
(*      lebesgue_rV n == the function of lebesgue_rV_rec n, with the same     *)
(*                       structure; the lemmas are stated for it              *)
(*        gauss_pdf x == (2 pi)^(-n/2) exp (- mxdot x x / 2), the density of  *)
(*                       gauss n with respect to lebesgue_rV n                *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* HB declares canonical projections that the structures of the measure
   already provide; the warning says so. The setting lasts until the end of
   this file and is not exported. *)
Set Warnings "-redundant-canonical-projection".

Section lebesgue_rV_cons.
Context {R : realType} (n : nat).
Variable m : {sigma_finite_measure set 'rV[R]_n -> \bar R}.
Local Notation leb := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Definition lebesgue_rV_cons (A : set 'rV[R]_n.+1) : \bar R :=
  (leb \x m) (@rV_cons R n @^-1` A).

Let mcons := @measurable_rV_cons R n.

Let lebesgue_rV_cons0 : lebesgue_rV_cons set0 = 0.
Proof. by rewrite /lebesgue_rV_cons preimage_set0 measure0. Qed.

Let lebesgue_rV_cons_ge0 A : 0 <= lebesgue_rV_cons A.
Proof. exact: measure_ge0. Qed.

Let lebesgue_rV_cons_sigma_additive : semi_sigma_additive lebesgue_rV_cons.
Proof.
move=> F mF tF mUF; rewrite /lebesgue_rV_cons preimage_bigcup.
apply: measure_semi_sigma_additive.
- by move=> k; rewrite -[X in measurable X]setTI; exact: mcons.
- apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- by rewrite -preimage_bigcup -[X in measurable X]setTI; exact: mcons.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ lebesgue_rV_cons
  lebesgue_rV_cons0 lebesgue_rV_cons_ge0 lebesgue_rV_cons_sigma_additive.

Let uncons (x : 'rV[R]_n.+1) : measurableTypeR R * 'rV[R]_n :=
  (x 0%R 0%R, rsubmx (x : 'rV[R]_(1 + n))).

Let unconsK p : uncons (rV_cons p) = p.
Proof.
case: p => t v; rewrite /uncons /=; congr pair; last exact: row_mxKr.
exact: (@rV_cons0 R n (t, v)).
Qed.

Let measurable_uncons : measurable_fun [set: 'rV[R]_n.+1] uncons.
Proof.
apply: measurable_fun_pair; last exact: (@measurable_rsubmx _ R 1 1 n).
by move=> _ Y mY; exact: (measurable_mxentry 0%R 0%R measurableT mY).
Qed.

Let lebesgue_rV_cons_sigma_finite : sigma_finite setT lebesgue_rV_cons.
Proof.
have /sigma_finiteP[F [TF ndF Foo]] := sigma_finiteT leb.
have /sigma_finiteP[G [TG ndG Goo]] := sigma_finiteT m.
have UFG : \bigcup_k (F k `*` G k) = setT.
  rewrite -setXTT TF TG predeqE => -[x y]; split.
    by move=> [k _ []/= ? ?]; split; exists k.
  move=> [/= [i _ Fix] [j _ Gjy]]; exists (maxn i j) => //; split.
  - by move: x Fix; exact/subsetPset/ndF/leq_maxl.
  - by move: y Gjy; exact/subsetPset/ndG/leq_maxr.
exists (fun k => uncons @^-1` (F k `*` G k)).
  by rewrite -preimage_bigcup UFG preimage_setT.
move=> k; have [mF Fk] := Foo k; have [mG Gk] := Goo k; split.
  rewrite -[X in measurable X]setTI; apply: measurable_uncons => //.
  exact: measurableX.
rewrite /lebesgue_rV_cons.
have -> : @rV_cons R n @^-1` (uncons @^-1` (F k `*` G k)) = F k `*` G k.
  apply/seteqP; split => p.
    by change ((F k `*` G k) (uncons (rV_cons p)) -> (F k `*` G k) p);
      rewrite unconsK.
  by change ((F k `*` G k) p -> (F k `*` G k) (uncons (rV_cons p)));
    rewrite unconsK.
by rewrite product_measure1E// lte_mul_pinfty// ge0_fin_numE.
Qed.

HB.instance Definition _ := Measure_isSigmaFinite.Build _ _ _ lebesgue_rV_cons
  lebesgue_rV_cons_sigma_finite.

End lebesgue_rV_cons.

Section lebesgue_rV.
Context {R : realType}.

Fixpoint lebesgue_rV_rec n : {sigma_finite_measure set 'rV[R]_n -> \bar R} :=
  if n is n'.+1 then lebesgue_rV_cons (lebesgue_rV_rec n')
  else \d_(0%R : 'rV[R]_0).

Definition lebesgue_rV n : set 'rV[R]_n -> \bar R := lebesgue_rV_rec n.

HB.instance Definition _ (n : nat) :=
  SigmaFiniteMeasure.copy (@lebesgue_rV n) (lebesgue_rV_rec n).

End lebesgue_rV.
Arguments lebesgue_rV {R} n.

Section lebesgue_rV_box.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma lebesgue_rVS n X :
  lebesgue_rV n.+1 X = (leb \x lebesgue_rV n) (@rV_cons R n @^-1` X).
Proof. by []. Qed.

Lemma lebesgue_rV_box n (A : 'I_n -> set R) : (forall i, measurable (A i)) ->
  lebesgue_rV n [set x : 'rV[R]_n | forall i, A i (x 0%R i)] =
    \prod_(i < n) leb (A i).
Proof.
elim: n A => [|n IH] A mA.
  rewrite big_ord0 (_ : [set _ | _] = setT).
    by apply/seteqP; split => // x _ [].
  exact: diracT.
rewrite lebesgue_rVS.
have -> : @rV_cons R n @^-1` [set x | forall i, A i (x 0%R i)] =
    A ord0 `*` [set v : 'rV_n | forall i, A (lift ord0 i) (v 0%R i)].
  apply/seteqP; split => [[t v] /= H|[t v] [/= H0 H1] i].
    split; first by have := H ord0; rewrite rV_cons0.
    by move=> i; have := H (lift ord0 i); rewrite rV_consS.
  case: (unliftP ord0 i) => [j ->|->]; last by rewrite rV_cons0.
  by rewrite rV_consS; exact: H1.
rewrite product_measure1E.
- exact: mA.
- by apply: (@measurable_rowbox _ R n (fun i => A (lift ord0 i))) => i;
    exact: mA.
rewrite big_ord_recl; congr (_ * _).
exact: (IH (fun i => A (lift ord0 i)) (fun i => mA _)).
Qed.

Lemma lebesgue_rV_unique n (mu : {measure set 'rV[R]_n -> \bar R}) :
  (forall A : 'I_n -> set R, (forall i, measurable (A i)) ->
     mu [set x : 'rV[R]_n | forall i, A i (x 0%R i)] =
       \prod_(i < n) leb (A i)) ->
  forall X, measurable X -> lebesgue_rV n X = mu X.
Proof.
move=> muA X mX.
pose I (k : nat) : set R := `[(- k%:R)%R, k%:R]%classic.
pose g (k : nat) : set 'rV[R]_n := [set x | forall i, I k (x 0%R i)].
have mI k : measurable (I k) by exact: measurable_itv.
apply: (measure_unique mxboxes g) => //.
- exact: measurable_mxboxes.
- exact: setI_closed_mxboxes.
- move=> k; exists (fun _ _ => I k) => //.
  by apply/seteqP; split=> x xA => [i|i j]; [|rewrite (ord1 i)]; exact: xA.
- apply/seteqP; split => // x _; exists (Num.truncn `|x|).+1 => // i.
  rewrite /I /= in_itv /= -ler_norml.
  by apply: (le_trans (mx_norm_entry_le x 0%R i)); exact/ltW/truncnS_gt.
- move=> _ [A mA <-].
  have -> : mxbox A = [set x : 'rV[R]_n | forall j, A 0%R j (x 0%R j)].
    by rewrite rowboxE; apply/seteqP; split=> x xA i j; rewrite (ord1 i);
      exact: xA.
  by rewrite /= lebesgue_rV_box ?muA// => j; exact: mA.
- move=> k; rewrite /=.
  have -> : lebesgue_rV n (g k) = \prod_(i < n) leb (I k).
    exact: (@lebesgue_rV_box n (fun _ => I k) (fun _ => mI k)).
  have /fin_numPlt/andP[_ ->] // : \prod_(i < n) leb (I k) \is a fin_num.
  by apply: prode_fin_num => i _; rewrite /I lebesgue_measure_itv; case: ifP.
Qed.

End lebesgue_rV_box.

Section lebesgue_rV_integral.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Let integral_lebesgue_rVS n (f : 'rV[R]_n.+1 -> \bar R) D :
  \int[lebesgue_rV n.+1]_(x in D) f x =
  \int[pushforward (leb \x lebesgue_rV n) (@rV_cons R n)]_(x in D) f x.
Proof. by apply: eq_measure_integral. Qed.

Lemma ge0_integral_lebesgue_rV_cons n (f : 'rV[R]_n.+1 -> \bar R) :
  measurable_fun [set: 'rV[R]_n.+1] f -> (forall x, 0 <= f x) ->
  \int[lebesgue_rV n.+1]_x f x =
    \int[leb]_t \int[lebesgue_rV n]_v f (rV_cons (t, v)).
Proof.
move=> mf f0.
rewrite integral_lebesgue_rVS ge0_integral_pushforward// preimage_setT.
rewrite fubini_tonelli1//; first exact: measurableT_comp.
by move=> p; exact: f0.
Qed.

Lemma integrable_lebesgue_rV_cons n (f : 'rV[R]_n.+1 -> \bar R) :
  measurable_fun [set: 'rV[R]_n.+1] f ->
  (lebesgue_rV n.+1).-integrable [set: 'rV[R]_n.+1] f <->
  (leb \x lebesgue_rV n).-integrable [set: measurableTypeR R * 'rV[R]_n]
    (f \o @rV_cons R n).
Proof.
move=> mf.
have mfc : measurable_fun [set: measurableTypeR R * 'rV[R]_n]
    (f \o @rV_cons R n).
  exact: measurableT_comp.
have E : \int[lebesgue_rV n.+1]_x `|f x| =
    \int[leb \x lebesgue_rV n]_p `|(f \o @rV_cons R n) p|.
  rewrite integral_lebesgue_rVS ge0_integral_pushforward ?preimage_setT//.
  exact: measurableT_comp.
by split=> /integrableP[_ fi]; apply/integrableP; split => //;
  [rewrite -E|rewrite E].
Qed.

Lemma integral_lebesgue_rV_cons n (f : 'rV[R]_n.+1 -> \bar R) :
  (lebesgue_rV n.+1).-integrable [set: 'rV[R]_n.+1] f ->
  \int[lebesgue_rV n.+1]_x f x =
    \int[leb]_t \int[lebesgue_rV n]_v f (rV_cons (t, v)).
Proof.
move=> fi; have mf := measurable_int _ fi.
have fci := (integrable_lebesgue_rV_cons mf).1 fi.
rewrite integral_lebesgue_rVS integral_pushforward ?preimage_setT//.
  by rewrite -(integral12_prod_meas1 fci).
Qed.

End lebesgue_rV_integral.

Section lebesgue_rV_prod.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma ge0_integral_lebesgue_rV_prod n (f : 'I_n -> R -> R) :
  (forall i, measurable_fun [set: R] (f i)) -> (forall i t, (0 <= f i t)%R) ->
  \int[lebesgue_rV n]_x (\prod_(i < n) f i (x 0%R i))%:E =
  \prod_(i < n) \int[leb]_t (f i t)%:E.
Proof.
have mprod m (g : 'I_m -> R -> R) : (forall i, measurable_fun [set: R] (g i)) ->
    measurable_fun [set: 'rV[R]_m] (fun x => (\prod_(i < m) g i (x 0%R i))%:E).
  move=> mg; apply/measurable_EFinP; apply: measurable_prod => i _.
  exact: measurableT_comp (mg i) (measurable_mxentry 0%R i).
have p0 m (g : 'I_m -> R -> R) : (forall i t, (0 <= g i t)%R) ->
    forall x : 'rV[R]_m, 0 <= (\prod_(i < m) g i (x 0%R i))%:E.
  by move=> g0 x; rewrite lee_fin prodr_ge0.
elim: n f => [|n IH] f mf f0.
  rewrite big_ord0; under eq_integral do rewrite big_ord0.
  by rewrite integral_cst// mul1e; exact: diracT.
pose f' i := f (lift ord0 i).
have mF := mprod _ f mf; have F0 := p0 _ f f0.
have mF' := mprod n f' (fun i => mf _); have F0' := p0 n f' (fun i => f0 _).
rewrite ge0_integral_lebesgue_rV_cons//.
transitivity (\int[leb]_t ((f ord0 t)%:E *
    \prod_(i < n) \int[leb]_u (f' i u)%:E)).
  apply: eq_integral => t _.
  transitivity (\int[lebesgue_rV n]_v
      ((f ord0 t)%:E * (\prod_(i < n) f' i (v 0%R i))%:E)).
    apply: eq_integral => v _; rewrite big_ord_recl rV_cons0 EFinM.
    by under eq_bigr do rewrite rV_consS.
  rewrite ge0_integralZl_EFin// (IH f')//.
  - by move=> i; exact: mf.
  - by move=> i; exact: f0.
have I0 : 0 <= \prod_(i < n) \int[leb]_u (f' i u)%:E.
  apply: prode_ge0 => i _; apply: integral_ge0 => t _.
  by rewrite lee_fin; exact: f0.
have mf0 : measurable_fun [set: R] (fun t => (f ord0 t)%:E).
  by apply/measurable_EFinP; exact: mf.
rewrite ge0_integralZr//; first by move=> t _; rewrite lee_fin.
by rewrite [in RHS]big_ord_recl.
Qed.

End lebesgue_rV_prod.

Section lebesgue_rV_image.
Context {R : realType} (n : nat).
Local Open Scope ereal_scope.
Variable phi : 'rV[R]_n -> 'rV[R]_n.
Hypothesis mphi : measurable_fun [set: 'rV[R]_n] phi.
Variable c : {nonneg R}.
Hypothesis phiE : forall X, measurable X ->
  lebesgue_rV n (phi @^-1` X) = c%:num%:E * lebesgue_rV n X.

Let image_lebesgue_rV (f : 'rV[R]_n -> \bar R) D :
  \int[pushforward (lebesgue_rV n) phi]_(x in D) f x =
  \int[mscale c (lebesgue_rV n)]_(x in D) f x.
Proof. by apply: eq_measure_integral => A mA _; exact: phiE. Qed.

Lemma ge0_integral_lebesgue_rV_image (f : 'rV[R]_n -> \bar R) :
  measurable_fun [set: 'rV[R]_n] f -> (forall x, 0 <= f x) ->
  \int[lebesgue_rV n]_x f (phi x) = c%:num%:E * \int[lebesgue_rV n]_x f x.
Proof.
move=> mf f0.
rewrite -ge0_integral_mscale//.
by rewrite -image_lebesgue_rV ge0_integral_pushforward// preimage_setT.
Qed.

Lemma integrable_lebesgue_rV_image (f : 'rV[R]_n -> \bar R) :
  (lebesgue_rV n).-integrable [set: 'rV[R]_n] f ->
  (lebesgue_rV n).-integrable [set: 'rV[R]_n] (f \o phi).
Proof.
move=> fi; have mf := measurable_int _ fi.
apply/integrableP; split; first exact: measurableT_comp.
rewrite (ge0_integral_lebesgue_rV_image (f := abse \o f))//.
- exact: measurableT_comp.
- by move=> x; exact: abse_ge0.
- by apply: lte_mul_pinfty => //; case/integrableP: fi.
Qed.

Lemma integral_lebesgue_rV_image (f : 'rV[R]_n -> \bar R) :
  (lebesgue_rV n).-integrable [set: 'rV[R]_n] f ->
  \int[lebesgue_rV n]_x f (phi x) = c%:num%:E * \int[lebesgue_rV n]_x f x.
Proof.
move=> fi; have mf := measurable_int _ fi.
rewrite [LHS]integralE [in RHS]integralE.
have -> : \int[lebesgue_rV n]_x (fun y => f (phi y))^\+ x =
    c%:num%:E * \int[lebesgue_rV n]_x f^\+ x.
  rewrite (_ : (fun y => f (phi y))^\+ = f^\+ \o phi).
    exact: funepos_comp.
  apply: (ge0_integral_lebesgue_rV_image (f := f^\+)) => [|x].
    exact: measurable_funepos.
  exact: funepos_ge0.
have -> : \int[lebesgue_rV n]_x (fun y => f (phi y))^\- x =
    c%:num%:E * \int[lebesgue_rV n]_x f^\- x.
  rewrite (_ : (fun y => f (phi y))^\- = f^\- \o phi).
    exact: funeneg_comp.
  apply: (ge0_integral_lebesgue_rV_image (f := f^\-)) => [|x].
    exact: measurable_funeneg.
  exact: funeneg_ge0.
rewrite [RHS]muleBr//.
by apply: fin_num_adde_defl; rewrite fin_numN; exact: integrable_neg_fin_num.
Qed.

End lebesgue_rV_image.

Section lebesgue_rV_invariance.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).

(* If the preimage of every box under phi has c times the measure of the
   box, then so has the preimage of every measurable set. *)
Lemma lebesgue_rV_preimage n (phi : 'rV[R]_n -> 'rV[R]_n) (c : R) :
  measurable_fun [set: 'rV[R]_n] phi -> 0 < c ->
  (forall A : 'I_n -> set R, (forall i, measurable (A i)) ->
    lebesgue_rV n (phi @^-1` [set x : 'rV[R]_n | forall i, A i (x 0 i)]) =
      (c%:E * \prod_(i < n) leb (A i))%E) ->
  forall X, measurable X ->
    lebesgue_rV n (phi @^-1` X) = (c%:E * lebesgue_rV n X)%E.
Proof.
move=> mphi c0 phiA X mX.
pose mu0 : {measure set 'rV[R]_n -> \bar R} := pushforward (lebesgue_rV n) phi.
have ci0 : 0 <= c^-1 by rewrite invr_ge0 ltW.
pose mu := mscale (NngNum ci0) (mu0 mphi).
have c_neq0 : c != 0 by rewrite gt_eqF.
have -> : lebesgue_rV n X = mu X.
  apply: lebesgue_rV_unique => // A mA; rewrite /mu; unfold mscale.
  rewrite -[X in (_ * X)%E = _]/(lebesgue_rV n
    (phi @^-1` [set x : 'rV[R]_n | forall i, A i (x 0%R i)])).
  by rewrite phiA// muleA -EFinM mulVf ?mul1e.
by rewrite /mu; unfold mscale; rewrite /= muleA -EFinM divff ?mul1e.
Qed.

Lemma measurable_rV_shift n (b : 'rV[R]_n) :
  measurable_fun [set: 'rV[R]_n] (fun x => x + b).
Proof. by apply: measurable_addmx => //; exact: measurable_cst. Qed.

Lemma lebesgue_rV_shift n (b : 'rV[R]_n) (X : set 'rV[R]_n) : measurable X ->
  lebesgue_rV n ((fun x => x + b) @^-1` X) = lebesgue_rV n X.
Proof.
move=> mX.
rewrite (lebesgue_rV_preimage (measurable_rV_shift b) ltr01) ?mul1e//.
move=> A mA; rewrite mul1e.
pose B i := (fun t : R => 1 * t + b 0 i) @^-1` A i.
have mB i : measurable (B i).
  by rewrite /B -[X in measurable X]setTI; exact: measurable_affine.
have -> : (fun x => x + b) @^-1` [set x : 'rV[R]_n | forall i, A i (x 0 i)] =
    [set x : 'rV[R]_n | forall i, B i (x 0 i)].
  by apply/seteqP; split => x /= H i; have := H i;
    rewrite /B /preimage /= mxE mul1r.
rewrite lebesgue_rV_box//; apply: eq_bigr => i _.
by rewrite /B lebesgue_measure_affine ?oner_neq0// normr1 invr1 mul1e.
Qed.

Lemma measurable_rV_scale n (a : R) :
  measurable_fun [set: 'rV[R]_n] (fun x => a *: x).
Proof. by apply: measurable_scalemx => //; exact: measurable_cst. Qed.

Lemma lebesgue_rV_scale n (a : R) (X : set 'rV[R]_n) : a != 0 -> measurable X ->
  lebesgue_rV n ((fun x => a *: x) @^-1` X) =
    ((`|a| ^- n)%:E * lebesgue_rV n X)%E.
Proof.
move=> a0 mX.
have an0 : 0 < `|a| ^- n by rewrite invr_gt0 exprn_gt0// normr_gt0.
rewrite (lebesgue_rV_preimage (measurable_rV_scale (n:=n) a) an0)//.
move=> A mA.
pose B i := (fun t : R => a * t + 0) @^-1` A i.
have mB i : measurable (B i).
  by rewrite /B -[X in measurable X]setTI; exact: measurable_affine.
have -> : (fun x => a *: x) @^-1` [set x : 'rV[R]_n | forall i, A i (x 0 i)] =
    [set x : 'rV[R]_n | forall i, B i (x 0 i)].
  by apply/seteqP; split => x /= H i; have := H i;
    rewrite /B /preimage /= mxE addr0.
rewrite lebesgue_rV_box//.
under eq_bigr do rewrite /B lebesgue_measure_affine//.
by rewrite big_split /= prodEFin prodr_const card_ord exprVn.
Qed.

Lemma lebesgue_rV_col_perm n (s : 'S_n) (X : set 'rV[R]_n) : measurable X ->
  lebesgue_rV n (col_perm s @^-1` X) = lebesgue_rV n X.
Proof.
move=> mX.
rewrite (lebesgue_rV_preimage (measurable_col_perm s) ltr01) ?mul1e//.
move=> A mA; rewrite mul1e.
have -> : col_perm s @^-1` [set x : 'rV[R]_n | forall i, A i (x 0 i)] =
    [set x : 'rV[R]_n | forall j, A ((s^-1)%g j) (x 0 j)].
  apply/seteqP; split => x /= H j.
    by have := H ((s^-1)%g j); rewrite mxE permKV.
  by rewrite mxE; have := H (s j); rewrite permK.
rewrite (@lebesgue_rV_box _ n (fun j => A ((s^-1)%g j))).
  by move=> j; exact: mA.
by rewrite [RHS](reindex_inj (@perm_inj _ (s^-1)%g)).
Qed.

Lemma lebesgue_rV_row_mx n m (X : set 'rV[R]_(n + m)) : measurable X ->
  lebesgue_rV (n + m) X =
  (lebesgue_rV n \x lebesgue_rV m)%E
    ((fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2) @^-1` X).
Proof.
move=> mX.
have mg : measurable_fun [set: 'rV[R]_n * 'rV[R]_m]
    (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2).
  exact: measurable_row_mx measurable_fst measurable_snd.
pose mu0 : {measure set 'rV[R]_(n + m) -> \bar R} :=
  pushforward (lebesgue_rV n \x lebesgue_rV m)%E
    (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2).
transitivity (mu0 mg X); last by [].
apply: lebesgue_rV_unique => // A mA; rewrite /mu0 /pushforward.
rewrite -[LHS]/((lebesgue_rV n \x lebesgue_rV m)%E
  ((fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2) @^-1`
    [set x : 'rV[R]_(n + m) | forall i, A i (x 0 i)])).
have -> : (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2) @^-1`
    [set x : 'rV[R]_(n + m) | forall i, A i (x 0 i)] =
    [set x : 'rV[R]_n | forall i, A (lshift m i) (x 0 i)] `*`
    [set y : 'rV[R]_m | forall j, A (rshift n j) (y 0 j)].
  apply/seteqP; split => [[x y] /= H|[x y] [/= H1 H2] k].
    split => i; [have := H (lshift m i)|have := H (rshift n i)].
      by rewrite row_mxEl.
    by rewrite row_mxEr.
  by rewrite -[k]splitK; case: (fintype.split k) => i /=;
    rewrite ?row_mxEl ?row_mxEr.
rewrite product_measure1E.
- by apply: (@measurable_rowbox _ R n (fun i => A (lshift m i))) => i;
    exact: mA.
- by apply: (@measurable_rowbox _ R m (fun j => A (rshift n j))) => j;
    exact: mA.
rewrite big_split_ord; congr (_ * _)%E.
- by apply: lebesgue_rV_box => i; exact: mA.
- by apply: lebesgue_rV_box => j; exact: mA.
Qed.

End lebesgue_rV_invariance.

Section lebesgue_rV_invariance_integral.
Context {R : realType}.
Local Open Scope ereal_scope.

Lemma ge0_integral_lebesgue_rV_shift n (b : 'rV[R]_n) (f : 'rV[R]_n -> \bar R) :
  measurable_fun [set: 'rV[R]_n] f -> (forall x, 0 <= f x) ->
  \int[lebesgue_rV n]_x f (x + b)%R = \int[lebesgue_rV n]_x f x.
Proof.
move=> mf f0; have c1 : (0 <= 1 :> R)%R by [].
rewrite (ge0_integral_lebesgue_rV_image (measurable_rV_shift b)
  (c := NngNum c1)).
- by move=> X mX; rewrite /= mul1e lebesgue_rV_shift.
- exact: mf.
- exact: f0.
- by rewrite /= mul1e.
Qed.

Lemma integral_lebesgue_rV_shift n (b : 'rV[R]_n) (f : 'rV[R]_n -> \bar R) :
  (lebesgue_rV n).-integrable [set: 'rV[R]_n] f ->
  \int[lebesgue_rV n]_x f (x + b)%R = \int[lebesgue_rV n]_x f x.
Proof.
move=> fi; have c1 : (0 <= 1 :> R)%R by [].
rewrite (integral_lebesgue_rV_image (measurable_rV_shift b) (c := NngNum c1)).
- by move=> X mX; rewrite /= mul1e lebesgue_rV_shift.
- exact: fi.
- by rewrite /= mul1e.
Qed.

Lemma integrable_lebesgue_rV_shift n (b : 'rV[R]_n) (f : 'rV[R]_n -> \bar R) :
  (lebesgue_rV n).-integrable [set: 'rV[R]_n] f ->
  (lebesgue_rV n).-integrable [set: 'rV[R]_n] (fun x => f (x + b)%R).
Proof.
move=> fi; have c1 : (0 <= 1 :> R)%R by [].
apply: (integrable_lebesgue_rV_image (measurable_rV_shift b) (c := NngNum c1)).
- by move=> X mX; rewrite /= mul1e lebesgue_rV_shift.
- exact: fi.
Qed.

Lemma ge0_integral_lebesgue_rV_scale n (a : R) (f : 'rV[R]_n -> \bar R) :
  (a != 0)%R -> measurable_fun [set: 'rV[R]_n] f -> (forall x, 0 <= f x) ->
  \int[lebesgue_rV n]_x f (a *: x) =
    (`|a| ^- n)%:E * \int[lebesgue_rV n]_x f x.
Proof.
move=> a0 mf f0; have c0 : (0 <= `|a| ^- n :> R)%R.
  by rewrite invr_ge0 exprn_ge0.
rewrite (ge0_integral_lebesgue_rV_image (measurable_rV_scale (n:=n) a)
  (c := NngNum c0)) //.
by move=> X mX; rewrite lebesgue_rV_scale.
Qed.

Lemma integral_lebesgue_rV_scale n (a : R) (f : 'rV[R]_n -> \bar R) :
  (a != 0)%R -> (lebesgue_rV n).-integrable [set: 'rV[R]_n] f ->
  \int[lebesgue_rV n]_x f (a *: x) =
    (`|a| ^- n)%:E * \int[lebesgue_rV n]_x f x.
Proof.
move=> a0 fi; have c0 : (0 <= `|a| ^- n :> R)%R.
  by rewrite invr_ge0 exprn_ge0.
rewrite (integral_lebesgue_rV_image (measurable_rV_scale (n:=n) a)
  (c := NngNum c0)) //.
by move=> X mX; rewrite lebesgue_rV_scale.
Qed.

Lemma integrable_lebesgue_rV_scale n (a : R) (f : 'rV[R]_n -> \bar R) :
  (a != 0)%R -> (lebesgue_rV n).-integrable [set: 'rV[R]_n] f ->
  (lebesgue_rV n).-integrable [set: 'rV[R]_n] (fun x => f (a *: x)).
Proof.
move=> a0 fi; have c0 : (0 <= `|a| ^- n :> R)%R.
  by rewrite invr_ge0 exprn_ge0.
apply: (integrable_lebesgue_rV_image (measurable_rV_scale (n:=n) a)
  (c := NngNum c0)) => //.
by move=> X mX; rewrite lebesgue_rV_scale.
Qed.

Lemma ge0_integral_lebesgue_rV_col_perm n (s : 'S_n) (f : 'rV[R]_n -> \bar R) :
  measurable_fun [set: 'rV[R]_n] f -> (forall x, 0 <= f x) ->
  \int[lebesgue_rV n]_x f (col_perm s x) = \int[lebesgue_rV n]_x f x.
Proof.
move=> mf f0; have c1 : (0 <= 1 :> R)%R by [].
rewrite (ge0_integral_lebesgue_rV_image (measurable_col_perm s)
  (c := NngNum c1)).
- by move=> X mX; rewrite /= mul1e lebesgue_rV_col_perm.
- exact: mf.
- exact: f0.
- by rewrite /= mul1e.
Qed.

Lemma integral_lebesgue_rV_col_perm n (s : 'S_n) (f : 'rV[R]_n -> \bar R) :
  (lebesgue_rV n).-integrable [set: 'rV[R]_n] f ->
  \int[lebesgue_rV n]_x f (col_perm s x) = \int[lebesgue_rV n]_x f x.
Proof.
move=> fi; have c1 : (0 <= 1 :> R)%R by [].
rewrite (integral_lebesgue_rV_image (measurable_col_perm s) (c := NngNum c1)).
- by move=> X mX; rewrite /= mul1e lebesgue_rV_col_perm.
- exact: fi.
- by rewrite /= mul1e.
Qed.

Lemma ge0_integral_lebesgue_rV_row_mx n m (f : 'rV[R]_(n + m) -> \bar R) :
  measurable_fun [set: 'rV[R]_(n + m)] f -> (forall x, 0 <= f x) ->
  \int[lebesgue_rV (n + m)]_x f x =
    \int[lebesgue_rV n]_x \int[lebesgue_rV m]_y f (row_mx x y).
Proof.
move=> mf f0.
have mg : measurable_fun [set: 'rV[R]_n * 'rV[R]_m]
    (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2).
  exact: measurable_row_mx measurable_fst measurable_snd.
pose mu0 : {measure set 'rV[R]_(n + m) -> \bar R} :=
  pushforward (lebesgue_rV n \x lebesgue_rV m)%E
    (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2).
transitivity (\int[mu0 mg]_x f x).
  by apply: eq_measure_integral => A mA _; exact: lebesgue_rV_row_mx.
rewrite ge0_integral_pushforward// preimage_setT.
rewrite (fubini_tonelli1 (fun p : 'rV[R]_n * 'rV[R]_m => f (row_mx p.1 p.2)))//.
exact: measurableT_comp.
Qed.

Lemma integral_lebesgue_rV_row_mx n m (f : 'rV[R]_(n + m) -> \bar R) :
  (lebesgue_rV (n + m)).-integrable [set: 'rV[R]_(n + m)] f ->
  \int[lebesgue_rV (n + m)]_x f x =
    \int[lebesgue_rV n]_x \int[lebesgue_rV m]_y f (row_mx x y).
Proof.
move=> fi; have mf := measurable_int _ fi.
have mg : measurable_fun [set: 'rV[R]_n * 'rV[R]_m]
    (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2).
  exact: measurable_row_mx measurable_fst measurable_snd.
pose mu0 : {measure set 'rV[R]_(n + m) -> \bar R} :=
  pushforward (lebesgue_rV n \x lebesgue_rV m)%E
    (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2).
have E A : measurable A -> lebesgue_rV (n + m) A = mu0 mg A.
  by move=> mA; exact: lebesgue_rV_row_mx.
have fi' : (mu0 mg).-integrable [set: 'rV[R]_(n + m)] f.
  apply/integrableP; split => //.
  rewrite -(eq_measure_integral _ (fun A mA _ => E A mA)).
  by case/integrableP: fi.
have fgi : (lebesgue_rV n \x lebesgue_rV m).-integrable
    [set: 'rV[R]_n * 'rV[R]_m] (f \o (fun p => row_mx p.1 p.2)).
  apply/integrableP; split; first exact: measurableT_comp.
  have := @ge0_integral_pushforward _ _ _ _ R _ mg
    (lebesgue_rV n \x lebesgue_rV m)%E setT (abse \o f) measurableT
    (measurableT_comp _ mf) (fun y _ => abse_ge0 _).
  by rewrite preimage_setT => <-; case/integrableP: fi'.
transitivity (\int[mu0 mg]_x f x).
  by apply: eq_measure_integral => A mA _; exact: E.
rewrite integral_pushforward ?preimage_setT//.
by rewrite -(integral12_prod_meas1 fgi).
Qed.

End lebesgue_rV_invariance_integral.

Section gauss_density.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).
Local Notation N := (@normal_prob R 0 1).

Definition gauss_pdf n (x : 'rV[R]_n) : R :=
  Num.sqrt (2 * pi) ^- n * expR (- mxdot x x / 2).

Lemma gauss_pdf_gt0 n (x : 'rV[R]_n) : 0 < gauss_pdf x.
Proof.
rewrite /gauss_pdf mulr_gt0 ?expR_gt0// invr_gt0 exprn_gt0// sqrtr_gt0.
by rewrite mulr_gt0 ?pi_gt0.
Qed.

Lemma gauss_pdf_ge0 n (x : 'rV[R]_n) : 0 <= gauss_pdf x.
Proof. exact/ltW/gauss_pdf_gt0. Qed.

Let measurable_mxdotB n (z : 'rV[R]_n) :
  measurable_fun [set: 'rV[R]_n] (fun x => mxdot (x - z) (x - z)).
Proof.
apply: measurable_sum => i; apply: measurable_sum => j.
have mE : measurable_fun [set: 'rV[R]_n] (fun x => (x - z) i j).
  rewrite (_ : (fun x => (x - z) i j) = (fun x => x i j - z i j)).
    by apply/funext => x; rewrite !mxE.
  by apply: measurable_funB => //; exact: measurable_mxentry.
exact: measurable_funM.
Qed.

Lemma measurable_gauss_pdf n : measurable_fun [set: 'rV[R]_n] (@gauss_pdf n).
Proof.
apply: measurable_funM => //; apply: measurableT_comp => //.
apply: measurable_funM => //; apply: measurableT_comp => //.
have := measurable_mxdotB (0 : 'rV[R]_n).
by rewrite (_ : (fun x => mxdot (x - 0) (x - 0)) = (fun x => mxdot x x))//;
  apply/funext => x; rewrite subr0.
Qed.

Let mxdot_rV_cons_self n t (v : 'rV[R]_n) :
  mxdot (rV_cons (t, v)) (rV_cons (t, v)) = t ^+ 2 + mxdot v v.
Proof.
rewrite /mxdot !big_ord1 big_ord_recl rV_cons0 /= expr2; congr (_ + _).
by apply: eq_bigr => j _; rewrite rV_consS.
Qed.

Lemma gauss_pdf_cons n t (v : 'rV[R]_n) :
  gauss_pdf (rV_cons (t, v)) = normal_pdf 0 1 t * gauss_pdf v.
Proof.
rewrite /gauss_pdf mxdot_rV_cons_self normal_pdfE ?oner_neq0//.
rewrite /normal_peak /normal_fun subr0 expr1n mul1r.
have -> : (pi *+ 2 : R) = 2 * pi by rewrite mulr_natl.
have -> : - (t ^+ 2 + mxdot v v) / 2 = - t ^+ 2 / 2 + - mxdot v v / 2 :> R.
  by rewrite opprD mulrDl.
rewrite expRD exprS invfM.
by rewrite -!mulrA; congr (_ * _); rewrite mulrCA; congr (_ * _).
Qed.

Let integral_normal_fun (c s : R) : 0 < s ->
  (\int[leb]_t (normal_fun c s t)%:E = (Num.sqrt (2 * pi) * s)%:E)%E.
Proof.
move=> s0.
have := integral_normal_pdf c s; rewrite normal_pdfE ?gt_eqF//.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin.
- exact: measurableT.
- by move=> t _; rewrite lee_fin normal_fun_ge0.
- by apply/measurable_EFinP; exact: measurable_normal_fun.
- exact: normal_peak_ge0.
have pk0 : 0 < normal_peak s by rewrite normal_peak_gt0// gt_eqF.
case: (\int[leb]_t (normal_fun c s t)%:E)%E => [r||].
- rewrite -EFinM => -[E]; congr EFin.
  have -> : r = (normal_peak s)^-1.
    by apply/(@mulfI _ (normal_peak s)); rewrite ?gt_eqF// E mulfV// gt_eqF.
  rewrite /normal_peak invrK -mulr_natl mulrCA mulrC.
  by rewrite sqrtrM ?mulr_ge0 ?pi_ge0// sqrtr_sqr gtr0_norm.
- by rewrite mulry gtr0_sg// mul1e.
- by rewrite mulrNy gtr0_sg// mul1e.
Qed.

Lemma lebesgue_rV_gauss_integral n (z : 'rV[R]_n) (s : R) : 0 < s ->
  (\int[lebesgue_rV n]_x (expR (- mxdot (x - z) (x - z) / (2 * s ^+ 2)))%:E =
    ((Num.sqrt (2 * pi) * s) ^+ n)%:E)%E.
Proof.
move=> s0.
have -> : (fun x => (expR (- mxdot (x - z) (x - z) / (2 * s ^+ 2)))%:E) =
    (fun x : 'rV[R]_n => (\prod_(i < n) normal_fun (z 0 i) s (x 0 i))%:E).
  apply/funext => x; congr EFin; rewrite /normal_fun -expR_sum; congr expR.
  rewrite /mxdot big_ord1 -sumrN mulr_suml; apply: eq_bigr => i _.
  by rewrite !mxE -expr2; congr (_ / _); rewrite mulr_natl.
rewrite (@ge0_integral_lebesgue_rV_prod _ n (fun i => normal_fun (z 0 i) s)).
- by move=> i; exact: measurable_normal_fun.
- by move=> i t; exact: normal_fun_ge0.
under eq_bigr do rewrite integral_normal_fun//.
by rewrite prodEFin prodr_const card_ord.
Qed.

Lemma lebesgue_rV_ball_le n (z : 'rV[R]_n) (r : R) : 0 < r ->
  (lebesgue_rV n [set x | (frobenius (x - z) <= r)%R] <=
    ((Num.sqrt (2 * pi * expR 1 / n%:R) * r) ^+ n)%:E)%E.
Proof.
move=> r0; set B := [set x | _].
have mD := measurable_mxdotB z.
have BE : B = (fun x => mxdot (x - z) (x - z)) @^-1` `]-oo, r ^+ 2]%classic.
  apply/seteqP; split => x /=; rewrite in_itv /= -frobenius_sqr;
    by rewrite ler_sqr ?nnegrE ?frobenius_ge0// ltW.
have mB : measurable B.
  rewrite BE -[X in measurable X]setTI.
  by apply: mD => //; exact: measurable_itv.
case: n z B mD BE mB => [|n] z B mD BE mB.
  rewrite expr0; apply: (@le_trans _ _ (lebesgue_rV 0 setT)).
    by apply: le_measure => //; rewrite inE.
  by have -> : lebesgue_rV 0 [set: 'rV[R]_0] = 1%E by exact: diracT.
pose s := r / Num.sqrt n.+1%:R.
have sn0 : 0 < Num.sqrt n.+1%:R :> R by rewrite sqrtr_gt0 ltr0n.
have s0 : 0 < s by rewrite divr_gt0.
pose c := expR (n.+1%:R / 2) : R.
have mG : measurable_fun [set: 'rV[R]_n.+1]
    (fun x => expR (- mxdot (x - z) (x - z) / (2 * s ^+ 2))).
  apply: measurableT_comp => //; apply: measurable_funM => //.
  exact: measurableT_comp.
have -> : lebesgue_rV n.+1 B = (\int[lebesgue_rV n.+1]_x (\1_B x)%:E)%E.
  by rewrite integral_indic// setIT.
apply: (@le_trans _ _ (\int[lebesgue_rV n.+1]_x
    (c%:E * (expR (- mxdot (x - z) (x - z) / (2 * s ^+ 2)))%:E))%E).
  apply: ge0_le_integral => //.
  - exact/measurable_EFinP/measurable_indic.
  - by apply/measurable_EFinP; exact: measurable_funM.
  move=> x _; rewrite -EFinM lee_fin indicE.
  have [xB|_] := boolP (x \in B); last by rewrite mulr_ge0 ?expR_ge0.
  rewrite /c -expRD (le_trans _ (expR_ge1Dx _))// lerDl.
  move: xB; rewrite BE inE /= in_itv /= => xr.
  have rn0 : r != 0 by rewrite gt_eqF.
  have nn0 : n.+1%:R != 0 :> R by rewrite pnatr_eq0.
  have -> : - mxdot (x - z) (x - z) / (2 * s ^+ 2) =
      - (n.+1%:R / 2 * (mxdot (x - z) (x - z) / r ^+ 2)).
    by rewrite /s expr_div_n sqr_sqrtr ?ler0n//; field.
  have q1 : mxdot (x - z) (x - z) / r ^+ 2 <= 1.
    by rewrite ler_pdivrMr ?exprn_gt0// mul1r.
  by rewrite -[X in X + _]mulr1 -mulrN -mulrDr mulr_ge0 ?subr_ge0.
rewrite ge0_integralZl_EFin.
- exact: measurableT.
- by move=> x _; rewrite lee_fin expR_ge0.
- exact/measurable_EFinP.
- exact: expR_ge0.
rewrite lebesgue_rV_gauss_integral// -EFinM lee_fin le_eqVlt; apply/orP; left.
apply/eqP; rewrite /c /s expRM_natl -exprMn; congr (_ ^+ _).
have e2 : Num.sqrt (expR 1) = expR (2^-1) :> R.
  rewrite -[X in expR X](@mulfV _ 2) ?pnatr_eq0// expRM_natl.
  by rewrite sqrtr_sqr ger0_norm ?expR_ge0.
have p0 : 0 <= 2 * pi :> R by rewrite mulr_ge0 ?pi_ge0.
have h1 : 0 <= 2 * pi * expR 1 :> R by rewrite mulr_ge0 ?expR_ge0.
rewrite (sqrtrM _ h1) (sqrtrM _ p0) e2 sqrtrV//.
by rewrite mulrCA mulrA -[RHS]mulrA [r * _]mulrC mulrA mulrAC.
Qed.

Local Open Scope ereal_scope.

Lemma ge0_integral_gauss_pdf n (f : 'rV[R]_n -> \bar R) :
  measurable_fun [set: 'rV[R]_n] f -> (forall x, 0 <= f x) ->
  \int[gauss n]_x f x = \int[lebesgue_rV n]_x (f x * (gauss_pdf x)%:E).
Proof.
elim: n f => [|n IH] f mf f0.
  transitivity (\int[gauss 0]_x (f x * (gauss_pdf x)%:E)).
    apply: eq_integral => x _.
    rewrite /gauss_pdf /mxdot big_ord1 big_ord0 expr0 invr1 mul1r oppr0 mul0r.
    by rewrite expR0 mule1.
  by apply: eq_measure_integral.
have mF m : measurable_fun [set: 'rV[R]_m] (fun x => (gauss_pdf x)%:E).
  by apply/measurable_EFinP; exact: measurable_gauss_pdf.
have mft t : measurable_fun [set: 'rV[R]_n] (fun v => f (rV_cons (t, v))).
  by apply: measurableT_comp => //; apply: measurableT_comp.
pose h (p : measurableTypeR R * 'rV[R]_n) :=
  f (rV_cons p) * (gauss_pdf p.2)%:E.
have mh : measurable_fun [set: measurableTypeR R * 'rV[R]_n] h.
  apply: emeasurable_funM; first exact: measurableT_comp.
  exact: measurableT_comp (mF n) measurable_snd.
have h0 p : 0 <= h p by rewrite mule_ge0// lee_fin gauss_pdf_ge0.
rewrite ge0_integral_gauss_cons// ge0_integral_lebesgue_rV_cons.
- by apply: emeasurable_funM => //; exact: mF.
- by move=> x; rewrite mule_ge0// lee_fin gauss_pdf_ge0.
transitivity (\int[N]_t \int[lebesgue_rV n]_v h (t, v)).
  by apply: eq_integral => t _; rewrite IH.
rewrite ge0_integral_normal_prob.
- by move=> t; apply: integral_ge0 => v _; exact: h0.
- exact: (measurable_fun_fubini_tonelli_F h mh h0).
apply: eq_integral => t _; rewrite -ge0_integralZr.
- exact: measurableT.
- by apply: emeasurable_funM => //; exact: mF.
- by move=> v _; exact: h0.
- by rewrite lee_fin normal_pdf_ge0.
apply: eq_integral => v _.
by rewrite /h gauss_pdf_cons -muleA -EFinM [(_ * normal_pdf _ _ _)%R]mulrC.
Qed.

Lemma integrable_gauss_pdf n (f : 'rV[R]_n -> \bar R) :
  measurable_fun [set: 'rV[R]_n] f ->
  (gauss n).-integrable [set: 'rV[R]_n] f <->
  (lebesgue_rV n).-integrable [set: 'rV[R]_n]
    (fun x => f x * (gauss_pdf x)%:E).
Proof.
move=> mf.
have E : \int[gauss n]_x `|f x| =
    \int[lebesgue_rV n]_x `|f x * (gauss_pdf x)%:E|.
  rewrite ge0_integral_gauss_pdf.
  - exact: measurableT_comp.
  - by move=> x; exact: abse_ge0.
  apply: eq_integral => x _.
  by rewrite abseM (@gee0_abs _ (gauss_pdf x)%:E)// lee_fin gauss_pdf_ge0.
split=> /integrableP[_ fi]; apply/integrableP; split.
- apply: emeasurable_funM => //.
  by apply/measurable_EFinP; exact: measurable_gauss_pdf.
- by rewrite -E.
- exact: mf.
- by rewrite E.
Qed.

Lemma integral_gauss_pdf n (f : 'rV[R]_n -> \bar R) :
  (gauss n).-integrable [set: 'rV[R]_n] f ->
  \int[gauss n]_x f x = \int[lebesgue_rV n]_x (f x * (gauss_pdf x)%:E).
Proof.
move=> fi; have mf := measurable_int _ fi.
have p0 x : 0 <= (gauss_pdf x)%:E by rewrite lee_fin gauss_pdf_ge0.
rewrite [LHS]integralE [RHS]integralE; congr (_ - _).
- rewrite ge0_integral_gauss_pdf.
  + exact: measurable_funepos.
  + by move=> x; exact: funepos_ge0.
  apply: eq_integral => x _; rewrite !funeposE.
  by rewrite muleC maxe_pMr// mule0 muleC.
- rewrite ge0_integral_gauss_pdf.
  + exact: measurable_funeneg.
  + by move=> x; exact: funeneg_ge0.
  apply: eq_integral => x _; rewrite !funenegE.
  by rewrite muleC maxe_pMr// mule0 muleN muleC.
Qed.

Lemma ge0_integral_lebesgue_rV_gauss n (f : 'rV[R]_n -> \bar R) :
  measurable_fun [set: 'rV[R]_n] f -> (forall x, 0 <= f x) ->
  \int[lebesgue_rV n]_x f x = \int[gauss n]_x (f x * ((gauss_pdf x)^-1)%R%:E).
Proof.
move=> mf f0.
have pdfV (x : 'rV[R]_n) :
    ((gauss_pdf x)^-1 = Num.sqrt (2 * pi) ^+ n * expR (mxdot x x / 2))%R.
  by rewrite /gauss_pdf invfM invrK -expRN mulNr opprK.
rewrite ge0_integral_gauss_pdf.
- apply: emeasurable_funM => //; apply/measurable_EFinP.
  under eq_fun do rewrite pdfV.
  apply: measurable_funM => //; apply: measurableT_comp => //.
  apply: measurable_funM => //.
  have := measurable_mxdotB (0 : 'rV[R]_n).
  by rewrite (_ : (fun x => mxdot (x - 0) (x - 0)) = (fun x => mxdot x x))//;
    apply/funext => x; rewrite subr0.
- by move=> x; rewrite mule_ge0// lee_fin invr_ge0 gauss_pdf_ge0.
apply: eq_integral => x _.
by rewrite -muleA -EFinM mulVf ?mule1// gt_eqF// gauss_pdf_gt0.
Qed.

Lemma gauss_lebesgue_rV n (X : set 'rV[R]_n) : measurable X ->
  gauss n X = \int[lebesgue_rV n]_(x in X) (gauss_pdf x)%:E.
Proof.
move=> mX.
transitivity (\int[gauss n]_x (\1_X x)%:E).
  by rewrite integral_indic// setIT.
rewrite ge0_integral_gauss_pdf//; first exact/measurable_EFinP/measurable_indic.
rewrite [RHS]integral_mkcond; apply: eq_integral => x _.
by rewrite /patch indicE; case: ifP => _; rewrite ?mul1e ?mul0e.
Qed.

End gauss_density.
