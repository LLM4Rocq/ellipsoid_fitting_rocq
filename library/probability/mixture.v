From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum finfun.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral hoelder probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import lindeberg moments.
From GaussianAnalysis.probability Require Import conditioning subgaussian.

(**md**************************************************************************)
(* # Finite mixtures of probabilities                                         *)
(*                                                                            *)
(* The mixture of probabilities P i, i in a finite type I, with weights w i:  *)
(* the law of a variable drawn from P i with probability w i. The weights     *)
(* are nonnegative of sum one, a proof argument of the mixture, as            *)
(* uniform_prob takes a < b.                                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*  mixture_weights w == w i >= 0 for every i and \sum_i w i = 1              *)
(*     mixture P hw == for hw : mixture_weights w, the probability            *)
(*                     A |-> \sum_i w i P i (A)                               *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - mixtureE: mixture P hw A = \sum_i w i P i (A);                           *)
(* - ge0_integral_mixture, integrable_mixture, integral_mixture,              *)
(*   expectation_mixture: \int f d(mixture P hw) = \sum_i w i \int f dP_i for *)
(*   f nonnegative and measurable, or integrable under every P i, and then    *)
(*   f is integrable under the mixture; Lfun1_mixture and Lfun2_mixture for   *)
(*   L^1 and L^2;                                                             *)
(* - variance_mixture: the law of total variance,                             *)
(*     Var X = \sum_i w i (Var_i X + (E_i X - E X)^2);                        *)
(* - subgaussian_mixture, subexponential_mixture: a variable subgaussian      *)
(*   (subexponential) with constant K under every P i is so under the         *)
(*   mixture;                                                                 *)
(* - distribution_mixture: the image of a mixture by a measurable map is the  *)
(*   mixture of the images;                                                   *)
(* - big_tuple_distr, mixture_weights_prod: \sum over s : n.-tuple I of       *)
(*   \prod_k F k (s_k) is \prod_k \sum_i F k i, so the product weights are    *)
(*   mixture weights;                                                         *)
(* - tuple_prod_mixture: the product of n copies of a mixture is the mixture, *)
(*   over the label tuples s with the product weights, of the products        *)
(*   tuple_prod (fun k => P (s_k)) n: on boxes by bigA_distr_bigA, then       *)
(*   measure_tuple_box_unique;                                                *)
(* - mixture_cover: measurable sets E i with P i (E i) <= eps that all        *)
(*   contain a set F have a measurable intersection, containing F, of         *)
(*   mixture probability at most eps.                                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition mixture_weights (I : finType) (R : realType) (w : I -> R) : Prop :=
  (forall i, 0 <= w i) /\ \sum_i w i = 1.

Section mixture_weights_props.
Context (I : finType) (R : realType) (w : I -> R) (hw : mixture_weights w).

Lemma mixture_weights_ge0 i : 0 <= w i.
Proof. by case: hw. Qed.

Lemma mixture_weights_sum : \sum_i w i = 1.
Proof. by case: hw. Qed.

(* Weights of sum one live on a nonempty type. *)
Lemma mixture_weights_inhabited : exists i : I, true.
Proof.
case: (pickP (fun _ : I => true)) => [i _|h]; first by exists i.
have := mixture_weights_sum; rewrite big_pred0 // => /eqP.
by rewrite eq_sym oner_eq0.
Qed.

End mixture_weights_props.

(* HB declares canonical projections that the structures of the measure
   already provide; the warning says so. The setting lasts until the end of
   this file and is not exported. *)
Set Warnings "-redundant-canonical-projection".

Section mixture.
Context d (T : measurableType d) (R : realType) (I : finType).
Variables (w : I -> R) (P : I -> probability T R).
Local Open Scope ereal_scope.

Definition mixture (hw : mixture_weights w) (A : set T) : \bar R :=
  \sum_i (w i)%:E * P i A.

Variable hw : mixture_weights w.

Let w0 i : (0 <= w i)%R. Proof. exact: mixture_weights_ge0. Qed.

Let mixture0 : mixture hw set0 = 0.
Proof. by rewrite /mixture big1 // => i _; rewrite measure0 mule0. Qed.

Let mixture_ge0 A : 0 <= mixture hw A.
Proof. by apply: sume_ge0 => i _; rewrite mule_ge0 // lee_fin. Qed.

Let mixture_sigma_additive : semi_sigma_additive (mixture hw).
Proof.
move=> F mF tF mUF; rewrite [X in _ --> X](_ : _ =
    lim ((fun n => \sum_(0 <= k < n) mixture hw (F k)) @ \oo)); last first.
  by apply: is_cvg_ereal_nneg_natsum => k _; exact: mixture_ge0.
rewrite /mixture nneseries_sum; try by move=> i j _; rewrite mule_ge0 // lee_fin.
apply: eq_bigr => /= i _; rewrite nneseriesZl; try by move=> j _.
by rewrite (measure_semi_bigcup (P i)).
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (mixture hw)
  mixture0 mixture_ge0 mixture_sigma_additive.

Let mixture_setT : mixture hw [set: T] = 1.
Proof.
rewrite /mixture (eq_bigr (fun i => (w i)%:E)); try
  by move=> i _; rewrite probability_setT mule1.
by rewrite sumEFin (mixture_weights_sum hw).
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R (mixture hw) mixture_setT.

Lemma mixtureE A : mixture hw A = \sum_i (w i)%:E * P i A.
Proof. by []. Qed.

(* The mixture as a finite sum of scaled measures, indexed by nat. *)
Let mterm (k : nat) : {measure set T -> \bar R} :=
  if insub k : option 'I_#|I| is Some o then
    mscale (NngNum (w0 (enum_val o))) (P (enum_val o))
  else mzero.

Let mtermE (k : 'I_#|I|) :
  mterm k = mscale (NngNum (w0 (enum_val k))) (P (enum_val k)).
Proof. by rewrite /mterm valK. Qed.

Let sum_enum (F : I -> \bar R) : \sum_i F i = \sum_(k < #|I|) F (enum_val k).
Proof. by rewrite -big_enum_val; apply: eq_bigl => i; rewrite inE. Qed.

Let mixture_msum A : mixture hw A = msum mterm #|I| A.
Proof.
rewrite /mixture /msum sum_enum; apply: eq_bigr => k _.
by rewrite mtermE.
Qed.

Lemma ge0_integral_mixture (D : set T) (f : T -> \bar R) :
  measurable D -> measurable_fun D f -> (forall x, D x -> 0 <= f x) ->
  \int[mixture hw]_(x in D) f x = \sum_i (w i)%:E * \int[P i]_(x in D) f x.
Proof.
move=> mD mf f0.
rewrite (eq_measure_integral (msum mterm #|I|)); try
  by move=> A mA _; exact: mixture_msum.
rewrite ge0_integral_measure_sum // sum_enum; apply: eq_bigr => k _.
by rewrite mtermE ge0_integral_mscale.
Qed.

Lemma integrable_mixture (D : set T) (f : T -> \bar R) : measurable D ->
  (forall i, (P i).-integrable D f) -> (mixture hw).-integrable D f.
Proof.
move=> mD iP; have [i0 _] := mixture_weights_inhabited hw.
have mf : measurable_fun D f := measurable_int _ (iP i0).
apply/integrableP; split => //.
have ma : measurable_fun D (fun x => `|f x|) by exact: measurableT_comp.
have a0 x : D x -> 0 <= `|f x| by move=> _; exact: abse_ge0.
rewrite ge0_integral_mixture //.
apply: lte_sum_pinfty => i _.
have /integrableP[_ fi] := iP i.
by rewrite lte_mul_pinfty // lee_fin.
Qed.

Lemma integral_mixture (D : set T) (f : T -> \bar R) : measurable D ->
  (forall i, (P i).-integrable D f) ->
  \int[mixture hw]_(x in D) f x = \sum_i (w i)%:E * \int[P i]_(x in D) f x.
Proof.
move=> mD iP; have [i0 _] := mixture_weights_inhabited hw.
have mf : measurable_fun D f := measurable_int _ (iP i0).
have mp : measurable_fun D f^\+ by exact: measurable_funepos.
have mn : measurable_fun D f^\- by exact: measurable_funeneg.
have p0 x : D x -> 0 <= f^\+ x by move=> _; exact: funepos_ge0.
have n0 x : D x -> 0 <= f^\- x by move=> _; exact: funeneg_ge0.
rewrite integralE ge0_integral_mixture // ge0_integral_mixture //.
pose a i := fine (\int[P i]_(x in D) f^\+ x).
pose b i := fine (\int[P i]_(x in D) f^\- x).
have ha i : \int[P i]_(x in D) f^\+ x = (a i)%:E.
  rewrite /a fineK //; apply: integrable_fin_num => //.
  by apply: integrable_funepos => //; exact: iP.
have hb i : \int[P i]_(x in D) f^\- x = (b i)%:E.
  rewrite /b fineK //; apply: integrable_fin_num => //.
  by apply: integrable_funeneg => //; exact: iP.
rewrite [X in X - _ = _](eq_bigr (fun i => (w i * a i)%:E)); try
  by move=> i _; rewrite ha EFinM.
rewrite [X in _ - X = _](eq_bigr (fun i => (w i * b i)%:E)); try
  by move=> i _; rewrite hb EFinM.
rewrite [RHS](eq_bigr (fun i => (w i * (a i - b i))%:E)); try
  by move=> i _; rewrite integralE ha hb -EFinB EFinM.
rewrite !sumEFin -EFinB; congr EFin.
by rewrite -sumrB; apply: eq_bigr => i _; ring.
Qed.

Lemma expectation_mixture (X : T -> R) : (forall i, X \in Lfun (P i) 1) ->
  'E_(mixture hw)[X] = \sum_i (w i)%:E * 'E_(P i)[X].
Proof.
move=> X1; rewrite unlock integral_mixture //.
by move=> i; exact/Lfun1_integrable.
Qed.

Lemma Lfun1_mixture (X : T -> R) : (forall i, X \in Lfun (P i) 1) ->
  X \in Lfun (mixture hw) 1.
Proof.
move=> X1; apply/Lfun1_integrable; apply: integrable_mixture => // i.
exact/Lfun1_integrable.
Qed.

Lemma Lfun2_mixture (X : T -> R) : (forall i, X \in Lfun (P i) 2%:E) ->
  X \in Lfun (mixture hw) 2%:E.
Proof.
move=> X2; have [i0 _] := mixture_weights_inhabited hw.
have := X2 i0; rewrite inE => /andP[]; rewrite inE /= => mX _.
apply: integrable_sqr_Lfun2 => //.
by apply: integrable_mixture => // i; exact: Lfun2_integrable_sqr.
Qed.

(* The law of total variance. *)
Lemma variance_mixture (X : T -> R) : (forall i, X \in Lfun (P i) 2%:E) ->
  'V_(mixture hw)[X] =
    \sum_i (w i)%:E * ('V_(P i)[X] + ('E_(P i)[X] - 'E_(mixture hw)[X]) ^+ 2).
Proof.
move=> X2.
have X1 i : X \in Lfun (P i) 1 :=
  Lfun_subset12 (fin_num_measure (P i) _ measurableT) (X2 i).
have Xs i : (X ^+ 2)%R \in Lfun (P i) 1 := Lfun2_sqr (X2 i).
rewrite (varianceE (Lfun2_mixture X2)).
rewrite (expectation_mixture Xs) (expectation_mixture X1).
pose e i := fine 'E_(P i)[X]; pose q i := fine 'E_(P i)[X ^+ 2].
have hE i : 'E_(P i)[X] = (e i)%:E by rewrite fineK // expectation_fin_num.
have hQ i : 'E_(P i)[X ^+ 2] = (q i)%:E by rewrite fineK // expectation_fin_num.
have hV i : 'V_(P i)[X] = (q i - e i ^+ 2)%:E.
  by rewrite (varianceE (X2 i)) hE hQ -EFin_expe -EFinB.
pose m := (\sum_i w i * e i)%R.
have hm : \sum_i (w i)%:E * 'E_(P i)[X] = m%:E.
  by rewrite /m -sumEFin; apply: eq_bigr => i _; rewrite hE -EFinM.
rewrite hm (eq_bigr (fun i => (w i * q i)%:E)); try
  by move=> i _; rewrite hQ -EFinM.
rewrite sumEFin -EFin_expe -EFinB.
rewrite (eq_bigr (fun i => (w i * (q i - e i ^+ 2 + (e i - m) ^+ 2))%:E)); try
  by move=> i _; rewrite hV hE -EFinB -EFin_expe -EFinD -EFinM.
rewrite sumEFin; congr EFin.
have -> : (\sum_i w i * (q i - e i ^+ 2 + (e i - m) ^+ 2) =
    \sum_i (w i * q i - 2 * m * (w i * e i) + m ^+ 2 * w i))%R.
  by apply: eq_bigr => i _; ring.
rewrite big_split /= sumrB -!mulr_sumr (mixture_weights_sum hw) -/m.
by ring.
Qed.

Lemma subgaussian_mixture (X : T -> R) (K : R) :
  (forall i, subgaussian (P i) X K) -> subgaussian (mixture hw) X K.
Proof.
move=> sX; have [i0 _] := mixture_weights_inhabited hw.
have [K0 mX _] := sX i0; split => //.
have me : measurable_fun [set: T] (fun t => (expR (X t ^+ 2 / K ^+ 2))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurable_funX.
have e0 t : [set: T] t -> 0 <= (expR (X t ^+ 2 / K ^+ 2))%:E.
  by move=> _; rewrite lee_fin expR_ge0.
rewrite ge0_integral_mixture //.
apply: (@le_trans _ _ (\sum_i (w i)%:E * 2%:E)).
  apply: lee_sum => i _; apply: lee_wpmul2l; first by rewrite lee_fin.
  by have [_ _ h] := sX i.
rewrite (eq_bigr (fun i => (w i * 2)%:E)); try by move=> i _; rewrite EFinM.
by rewrite sumEFin -mulr_suml (mixture_weights_sum hw) mul1r.
Qed.

Lemma subexponential_mixture (Y : T -> R) (L : R) :
  (forall i, subexponential (P i) Y L) -> subexponential (mixture hw) Y L.
Proof.
move=> sY; have [i0 _] := mixture_weights_inhabited hw.
have [L0 mY _] := sY i0; split => //.
have me : measurable_fun [set: T] (fun t => (expR (`|Y t| / L))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurableT_comp.
have e0 t : [set: T] t -> 0 <= (expR (`|Y t| / L))%:E.
  by move=> _; rewrite lee_fin expR_ge0.
rewrite ge0_integral_mixture //.
apply: (@le_trans _ _ (\sum_i (w i)%:E * 2%:E)).
  apply: lee_sum => i _; apply: lee_wpmul2l; first by rewrite lee_fin.
  by have [_ _ h] := sY i.
rewrite (eq_bigr (fun i => (w i * 2)%:E)); try by move=> i _; rewrite EFinM.
by rewrite sumEFin -mulr_suml (mixture_weights_sum hw) mul1r.
Qed.

(* Sets E i of small P i-probability that contain a set F: their
   intersection is a measurable event of small mixture probability that
   contains F. *)
Lemma mixture_cover (E : I -> set T) (F : set T) (eps : R) :
  (forall i, measurable (E i)) -> (forall i, F `<=` E i) ->
  (forall i, P i (E i) <= eps%:E) ->
  [/\ measurable (\bigcap_(i in [set: I]) E i),
      F `<=` \bigcap_(i in [set: I]) E i &
      mixture hw (\bigcap_(i in [set: I]) E i) <= eps%:E].
Proof.
move=> mE FE PE.
have mI : measurable (\bigcap_(i in [set: I]) E i).
  by apply: fin_bigcap_measurable => // i _; exact: mE.
split => //; first by move=> x Fx i _; exact: FE.
rewrite mixtureE; apply: (@le_trans _ _ (\sum_i (w i)%:E * eps%:E)).
  apply: lee_sum => i _; apply: lee_wpmul2l; first by rewrite lee_fin.
  have mEi := mE i.
  apply: le_trans (PE i); apply: le_measure; rewrite ?inE //.
  exact: bigcap_inf.
rewrite (eq_bigr (fun i => (w i * eps)%:E)); try by move=> i _; rewrite EFinM.
by rewrite sumEFin -mulr_suml (mixture_weights_sum hw) mul1r.
Qed.

End mixture.

Section mixture_maps.
Context d (T : measurableType d) (R : realType) (I : finType).
Variables (w : I -> R) (P : I -> probability T R) (hw : mixture_weights w).
Local Open Scope ereal_scope.

(* The image of a mixture is the mixture of the images. *)
Lemma distribution_mixture d' (T' : measurableType d') (f : {mfun T >-> T'})
    (A : set T') :
  distribution (mixture P hw) f A =
  mixture (fun i => distribution (P i) f) hw A.
Proof. by rewrite /mixture /distribution /pushforward. Qed.

End mixture_maps.

(* A sum over n-tuples of products is a product of sums. *)
Lemma big_tuple_distr (R : comPzSemiRingType) (I : finType) n
    (F : 'I_n -> I -> R) :
  \sum_(s : n.-tuple I) \prod_(k < n) F k (tnth s k) =
  \prod_(k < n) \sum_i F k i.
Proof.
have hb : bijective (fun s : n.-tuple I => [ffun k => tnth s k]).
  exists (fun f : {ffun 'I_n -> I} => [tuple f k | k < n]).
    by move=> s; apply: eq_from_tnth => k; rewrite tnth_mktuple ffunE.
  by move=> f; apply/ffunP => k; rewrite ffunE tnth_mktuple.
rewrite bigA_distr_bigA (reindex _ (onW_bij _ hb)).
by apply: eq_bigr => s _; apply: eq_bigr => k _; rewrite ffunE.
Qed.

Lemma mixture_weights_prod (I : finType) (R : realType) (w : I -> R) n :
  mixture_weights w ->
  mixture_weights (fun s : n.-tuple I => \prod_(k < n) w (tnth s k)).
Proof.
move=> hw; split.
  by move=> s; apply: prodr_ge0 => k _; exact: mixture_weights_ge0.
rewrite (big_tuple_distr (fun (k : 'I_n) i => w i)).
by rewrite big1 // => k _; exact: mixture_weights_sum.
Qed.

Section tuple_prod_mixture.
Context d (T : measurableType d) (R : realType) (I : finType).
Variables (w : I -> R) (P : I -> probability T R) (hw : mixture_weights w).
Local Open Scope ereal_scope.

(* The product of n copies of a mixture is the mixture, over the label
   tuples s with weights \prod_k w (s_k), of the products of the P (s_k);
   i0 is any label, for the indices past n. *)
Lemma tuple_prod_mixture (i0 : I) n (A : set (n.-tuple T)) : measurable A ->
  tuple_prod (fun=> mixture P hw) n A =
  \sum_(s : n.-tuple I) (\prod_(k < n) w (tnth s k))%:E *
    tuple_prod (fun k => P (nth i0 s k)) n A.
Proof.
move=> mA.
pose Q (s : n.-tuple I) := tuple_prod (fun k => P (nth i0 s k)) n.
have hW := mixture_weights_prod n hw.
rewrite -(mixtureE Q hW).
apply: (measure_tuple_box_unique (mu1 := tuple_prod (fun=> mixture P hw) n)
  (mu2 := mixture Q hW)) => //.
  by rewrite (le_lt_trans (probability_le1 _ _)) ?ltry.
move=> B mB.
change (tuple_prod (fun=> mixture P hw) n (tuple_box B) =
  mixture Q hW (tuple_box B)).
rewrite tuple_prod_box // mixtureE.
pose p i (k : 'I_n) := fine (P i (B k)).
have hp i k : P i (B k) = (p i k)%:E.
  by rewrite /p fineK //; apply: fin_num_measure; exact: mB.
have -> : \prod_(k < n) mixture P hw (B k) =
    (\prod_(k < n) \sum_i w i * p i k)%:E.
  rewrite -prodEFin; apply: eq_bigr => k _.
  by rewrite mixtureE -sumEFin; apply: eq_bigr => i _; rewrite hp EFinM.
have -> : \sum_(s : n.-tuple I) (\prod_(k < n) w (tnth s k))%:E * Q s (tuple_box B) =
    (\sum_(s : n.-tuple I) \prod_(k < n) (w (tnth s k) * p (tnth s k) k))%:E.
  rewrite -sumEFin; apply: eq_bigr => s _.
  rewrite /Q tuple_prod_box // big_split /= EFinM.
  congr (_ * _); rewrite -prodEFin; apply: eq_bigr => k _.
  by rewrite -(tnth_nth i0) hp.
congr EFin.
by rewrite (big_tuple_distr (fun k i => (w i * p i k)%R)).
Qed.

End tuple_prod_mixture.

