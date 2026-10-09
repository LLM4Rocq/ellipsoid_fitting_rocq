From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral charge probability.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From GaussianAnalysis.probability Require Import conditioning.

(**md**************************************************************************)
(* # Laws given by a density                                                  *)
(*                                                                            *)
(* For a probability mu on a measurable type T and a measurable f : T -> R,   *)
(* nonnegative everywhere, of integral one against mu, density_prob mu f is   *)
(* the probability A |-> int_A f dmu. Its measure is the integral of a        *)
(* nonnegative function, sigma-additive by semi_sigma_additive_nng_induced of *)
(* MathComp-Analysis. When f is not such a density, density_prob mu f is mu   *)
(* itself (density_prob_default), so that density_prob mu f is a probability  *)
(* for every f; the results below assume prob_density mu f.                   *)
(* density_law mu f hf is the same probability, built from a proof hf of      *)
(* prob_density mu f: its value on A is int_A f dmu by definition, with no    *)
(* fallback.                                                                  *)
(* - density_probE: density_prob mu f A = int_A f dmu.                        *)
(* - density_prob_dominates: density_prob mu f is absolutely continuous with  *)
(*   respect to mu.                                                           *)
(* - ge0_integral_density_prob, integrable_density_prob,                      *)
(*   integral_density_prob: integrating g against density_prob mu f is        *)
(*   integrating g f against mu, for g nonnegative or integrable.             *)
(* - density_prob_ae, eq_density_prob: a density may be changed on a mu-null  *)
(*   set: int_A f' dmu = density_prob mu f A for measurable A when f' = f     *)
(*   mu-almost everywhere, even if f' is negative somewhere, and two          *)
(*   densities equal mu-almost everywhere give the same probability.          *)
(* - prob_density_tuple_prod, tuple_prod_density: if f_k is a density         *)
(*   against nu_k for every k < n, the product of the laws                    *)
(*   density_prob nu_k f_k, k < n, has the density x |-> prod_k f_k (x_k)     *)
(*   against tuple_prod nu n. indic_tuple_box: the indicator of a box is the  *)
(*   product of the indicators of its sides.                                  *)
(* - density_lawE: density_law mu f hf A = int_A f dmu. density_law_prob:     *)
(*   density_law mu f hf is density_prob mu f. integral_density_law_prob:     *)
(*   integrals against the two agree, so every result on density_prob holds   *)
(*   for density_law. density_law_dominates, ge0_integral_density_law,        *)
(*   integrable_density_law, integral_density_law, eq_density_law and         *)
(*   tuple_prod_density_law restate the results above for density_law.        *)
(*                                                                            *)
(* ```                                                                        *)
(*   prob_density mu f == f is measurable, nonnegative everywhere, and of     *)
(*                        integral one against mu                             *)
(*   density_prob mu f == the probability with density f against mu, if       *)
(*                        prob_density mu f, and mu otherwise                 *)
(*   density_law mu f hf == the probability with density f against mu, for    *)
(*                          a proof hf of prob_density mu f                   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition prob_density d (T : measurableType d) (R : realType)
    (mu : probability T R) (f : T -> R) : Prop :=
  [/\ measurable_fun [set: T] f, forall x, 0 <= f x &
      (\int[mu]_x (f x)%:E = 1)%E].

Definition density_prob d (T : measurableType d) (R : realType)
    (mu : probability T R) (f : T -> R) : set T -> \bar R :=
  if pselect (prob_density mu f) then fun A => (\int[mu]_(x in A) (f x)%:E)%E
  else mu.

(* HB declares canonical projections that the structures of the measure
   already provide; the warning says so. The setting lasts until the end of
   this file and is not exported. *)
Set Warnings "-redundant-canonical-projection".

Section density_prob_measure.
Context d (T : measurableType d) (R : realType).
Variables (mu : probability T R) (f : T -> R).
Local Notation P := (density_prob mu f).

Let P0 : P set0 = 0%E.
Proof.
rewrite /density_prob; case: pselect => [p|np]; first exact: integral_set0.
exact: measure0.
Qed.

Let P_ge0 A : (0 <= P A)%E.
Proof.
rewrite /density_prob; case: pselect => [[mf f0 f1]|np]; last first.
  exact: measure_ge0.
by apply: integral_ge0 => x _; rewrite lee_fin.
Qed.

Let P_sigma_additive : semi_sigma_additive P.
Proof.
rewrite /density_prob; case: pselect => [[mf f0 f1]|np]; last first.
  exact: measure_semi_sigma_additive.
apply: semi_sigma_additive_nng_induced; first exact/measurable_EFinP.
by move=> x; rewrite lee_fin.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ P P0 P_ge0 P_sigma_additive.

Let P_setT : P [set: T] = 1%E.
Proof.
rewrite /density_prob; case: pselect => [[mf f0 f1]|np]; first exact: f1.
exact: probability_setT.
Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R P P_setT.

Lemma density_prob_default : ~ prob_density mu f -> P = mu.
Proof. by rewrite /density_prob; case: pselect. Qed.

End density_prob_measure.

Section density_prob_integral.
Context d (T : measurableType d) (R : realType).
Variables (mu : probability T R) (f : T -> R).
Hypothesis hf : prob_density mu f.
Local Notation P := (density_prob mu f).
Local Open Scope ereal_scope.

Let mF : measurable_fun [set: T] (fun x => (f x)%:E).
Proof. by case: hf => mf _ _; exact/measurable_EFinP. Qed.

Let F0 x : 0 <= (f x)%:E.
Proof. by case: hf => _ f0 _; rewrite lee_fin. Qed.

Lemma density_probE A : P A = \int[mu]_(x in A) (f x)%:E.
Proof. by rewrite /density_prob; case: pselect => // nf; case: (nf hf). Qed.

Lemma density_prob_dominates : P `<< mu.
Proof.
apply/null_content_dominatesP => A mA muA0; rewrite density_probE.
have mFA : measurable_fun A (fun x => (f x)%:E) := measurable_funTS mF.
have := @integral_abs_eq0 _ _ _ mu A _ mA mFA muA0.
by under eq_integral do rewrite gee0_abs ?F0//.
Qed.

Let RN_density : ae_eq mu [set: T] (Radon_Nikodym_SigmaFinite.f P mu)
  (fun x => (f x)%:E).
Proof.
apply: integral_ae_eq.
- exact: measurableT.
- exact: Radon_Nikodym_SigmaFinite.f_integrable density_prob_dominates.
- exact: mF.
- move=> E _ mE.
  rewrite -(Radon_Nikodym_SigmaFinite.f_integral density_prob_dominates mE).
  exact: density_probE.
Qed.

Lemma ge0_integral_density_prob (g : T -> \bar R) E : measurable E ->
  (forall x, 0 <= g x) -> measurable_fun E g ->
  \int[P]_(x in E) g x = \int[mu]_(x in E) (g x * (f x)%:E).
Proof.
move=> mE g0 mg.
rewrite -(Radon_Nikodym_SigmaFinite.change_of_variables
  density_prob_dominates g0 mE mg).
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //; apply: measurable_funTS.
  exact: measurable_int
    (Radon_Nikodym_SigmaFinite.f_integrable density_prob_dominates).
- by apply: emeasurable_funM => //; exact: measurable_funTS.
- exact: ae_eqe_mul2l (ae_eq_subset (subsetT E) RN_density).
Qed.

Lemma integrable_density_prob (g : T -> \bar R) E : measurable E ->
  measurable_fun E g ->
  P.-integrable E g <-> mu.-integrable E (fun x => g x * (f x)%:E).
Proof.
move=> mE mg.
have mFE : measurable_fun E (fun x => (f x)%:E) := measurable_funTS mF.
have EE : \int[P]_(x in E) `|g x| = \int[mu]_(x in E) `|g x * (f x)%:E|.
  rewrite ge0_integral_density_prob//; first exact: measurableT_comp.
  by apply: eq_integral => x _; rewrite abseM (gee0_abs (F0 x)).
split=> /integrableP[_ gi]; apply/integrableP; split.
- exact: emeasurable_funM.
- by rewrite -EE.
- exact: mg.
- by rewrite EE.
Qed.

Lemma integral_density_prob (g : T -> \bar R) E : measurable E ->
  P.-integrable E g ->
  \int[P]_(x in E) g x = \int[mu]_(x in E) (g x * (f x)%:E).
Proof.
move=> mE gi; have mg := measurable_int _ gi.
rewrite [LHS]integralE [RHS]integralE.
congr (_ - _); rewrite ge0_integral_density_prob//.
- exact: measurable_funepos.
- apply: eq_integral => x _; rewrite !funeposE.
  by rewrite muleC maxe_pMr ?F0// mule0 muleC.
- exact: measurable_funeneg.
- apply: eq_integral => x _; rewrite !funenegE.
  by rewrite muleC maxe_pMr ?F0// mule0 muleN muleC.
Qed.

(* The density may be changed on a mu-null set, even to negative values. *)
Lemma density_prob_ae (f' : T -> R) A : measurable A ->
  measurable_fun [set: T] f' ->
  ae_eq mu [set: T] (fun x => (f x)%:E) (fun x => (f' x)%:E) ->
  P A = \int[mu]_(x in A) (f' x)%:E.
Proof.
move=> mA mf' ff'; rewrite density_probE.
apply: ae_eq_integral => //.
- exact: measurable_funTS.
- by apply: measurable_funTS; exact/measurable_EFinP.
- exact: ae_eq_subset (subsetT A) ff'.
Qed.

End density_prob_integral.

Lemma eq_density_prob d (T : measurableType d) (R : realType)
    (mu : probability T R) (f f' : T -> R) :
  prob_density mu f -> prob_density mu f' ->
  ae_eq mu [set: T] (fun x => (f x)%:E) (fun x => (f' x)%:E) ->
  forall A, measurable A -> density_prob mu f A = density_prob mu f' A.
Proof.
move=> hf hf' ff' A mA; rewrite (density_probE hf').
by apply: density_prob_ae => //; case: hf'.
Qed.

(* The constructor with the proof that f is a density: the set function
   A |-> int_A f dmu itself, with no fallback. *)
Definition density_law d (T : measurableType d) (R : realType)
    (mu : probability T R) (f : T -> R) (hf : prob_density mu f) :
    set T -> \bar R :=
  fun A => (\int[mu]_(x in A) (f x)%:E)%E.
Arguments density_law {d T R} mu f hf.

Section density_law_measure.
Context d (T : measurableType d) (R : realType).
Variables (mu : probability T R) (f : T -> R) (hf : prob_density mu f).
Local Notation L := (density_law mu f hf).
Local Open Scope ereal_scope.

Let mF : measurable_fun [set: T] (fun x => (f x)%:E).
Proof. by case: hf => mf _ _; exact/measurable_EFinP. Qed.

Let F0 x : 0 <= (f x)%:E.
Proof. by case: hf => _ f0 _; rewrite lee_fin. Qed.

Let L0 : L set0 = 0.
Proof. exact: integral_set0. Qed.

Let L_ge0 A : 0 <= L A.
Proof. by apply: integral_ge0 => x _; exact: F0. Qed.

Let L_sigma_additive : semi_sigma_additive L.
Proof. exact: semi_sigma_additive_nng_induced mF F0. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ L L0 L_ge0 L_sigma_additive.

Let L_setT : L [set: T] = 1.
Proof. by have [_ _ f1] := hf; exact: f1. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R L L_setT.

Lemma density_lawE A : L A = \int[mu]_(x in A) (f x)%:E.
Proof. by []. Qed.

End density_law_measure.

Section density_law_integral.
Context d (T : measurableType d) (R : realType).
Variables (mu : probability T R) (f : T -> R) (hf : prob_density mu f).
Local Notation L := (density_law mu f hf).
Local Open Scope ereal_scope.

(* density_law and density_prob agree when f is a density. *)
Lemma density_law_prob : L = density_prob mu f.
Proof. by apply/funext => A; rewrite (density_probE hf). Qed.

Lemma integral_density_law_prob (g : T -> \bar R) D :
  \int[L]_(x in D) g x = \int[density_prob mu f]_(x in D) g x.
Proof.
by apply: eq_measure_integral => A _ _; exact: (esym (density_probE hf A)).
Qed.

Lemma density_law_dominates : L `<< mu.
Proof. by rewrite density_law_prob; exact: density_prob_dominates. Qed.

Lemma ge0_integral_density_law (g : T -> \bar R) E : measurable E ->
  (forall x, 0 <= g x) -> measurable_fun E g ->
  \int[L]_(x in E) g x = \int[mu]_(x in E) (g x * (f x)%:E).
Proof.
move=> mE g0 mg; rewrite integral_density_law_prob.
exact: (ge0_integral_density_prob hf mE g0 mg).
Qed.

Lemma integrable_density_law (g : T -> \bar R) E : measurable E ->
  measurable_fun E g ->
  L.-integrable E g <-> mu.-integrable E (fun x => g x * (f x)%:E).
Proof.
move=> mE mg; have h := integrable_density_prob hf mE mg.
have e : \int[L]_(x in E) `|g x| =
    \int[density_prob mu f]_(x in E) `|g x|.
  exact: integral_density_law_prob.
split=> [/integrableP[_ gi]|/h/integrableP[_ gi]].
  by apply/h/integrableP; split => //; rewrite -e.
by apply/integrableP; split => //; rewrite e.
Qed.

Lemma integral_density_law (g : T -> \bar R) E : measurable E ->
  L.-integrable E g ->
  \int[L]_(x in E) g x = \int[mu]_(x in E) (g x * (f x)%:E).
Proof.
move=> mE gi; have mg := measurable_int _ gi.
rewrite integral_density_law_prob; apply: (integral_density_prob hf mE).
exact/(integrable_density_prob hf mE mg)/(integrable_density_law mE mg).
Qed.

End density_law_integral.

Lemma eq_density_law d (T : measurableType d) (R : realType)
    (mu : probability T R) (f f' : T -> R) (hf : prob_density mu f)
    (hf' : prob_density mu f') :
  ae_eq mu [set: T] (fun x => (f x)%:E) (fun x => (f' x)%:E) ->
  forall A, measurable A -> density_law mu f hf A = density_law mu f' hf' A.
Proof.
by move=> ff' A mA; rewrite !density_law_prob; exact: eq_density_prob.
Qed.

Section tuple_prod_density.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* The indicator of a box is the product of the indicators of its sides. *)
Lemma indic_tuple_box n (A : 'I_n -> set T) (x : n.-tuple T) :
  (\1_(tuple_box A) x = \prod_(k < n) \1_(A k) (tnth x k) :> R)%R.
Proof.
have [xA|xA] := pselect (tuple_box A x).
  rewrite indicE (mem_set xA) big1 // => k _.
  by rewrite indicE (mem_set (xA k)).
have [k nk] : exists k, ~ A k (tnth x k).
  apply: contrapT => h; apply: xA => k.
  by apply: contrapT => hk; apply: h; exists k.
by rewrite indicE (memNset xA) (bigD1 k) //= indicE (memNset nk) mul0r.
Qed.

Lemma prob_density_tuple_prod (nu : nat -> probability T R)
    (f : nat -> T -> R) n :
  (forall k, (k < n)%N -> prob_density (nu k) (f k)) ->
  prob_density (tuple_prod nu n) (fun x => \prod_(k < n) f k (tnth x k))%R.
Proof.
move=> hf; split.
- apply: measurable_prod => k _.
  apply: measurableT_comp (measurable_tnth k).
  by case: (hf k (ltn_ord k)).
- move=> x; apply: prodr_ge0 => k _.
  by case: (hf k (ltn_ord k)) => _ f0 _; exact: f0.
pose g k := if (k < n)%N then f k else fun=> 0%R.
have gE (k : 'I_n) : g k = f k by rewrite /g ltn_ord.
have mg k : measurable_fun [set: T] (g k).
  rewrite /g; case: ifPn => [kn|_]; last exact: measurable_cst.
  by case: (hf k kn).
have g0 k t : (0 <= g k t)%R.
  rewrite /g; case: ifPn => [kn|_] //.
  by case: (hf k kn) => _ f0 _; exact: f0.
transitivity (\int[tuple_prod nu n]_x (\prod_(k < n) g k (tnth x k))%:E).
  by apply: eq_integral => x _; congr (_%:E); apply: eq_bigr => k _; rewrite gE.
rewrite ge0_integral_tuple_prod_prod //.
by rewrite big1 // => k _; rewrite gE; case: (hf k (ltn_ord k)).
Qed.

Lemma tuple_prod_density (nu : nat -> probability T R) (f : nat -> T -> R)
    n E :
  (forall k, (k < n)%N -> prob_density (nu k) (f k)) -> measurable E ->
  tuple_prod (fun k => density_prob (nu k) (f k)) n E =
  \int[tuple_prod nu n]_(x in E) (\prod_(k < n) f k (tnth x k))%:E.
Proof.
move=> hf mE; have hF := prob_density_tuple_prod hf.
transitivity (density_prob (tuple_prod nu n)
  (fun x => \prod_(k < n) f k (tnth x k))%R E); last exact: density_probE.
have fin : tuple_prod (fun k => density_prob (nu k) (f k)) n [set: n.-tuple T]
    < +oo.
  by rewrite probability_setT ltry.
apply: (measure_tuple_box_unique fin) => // A mA.
transitivity (\prod_(k < n) density_prob (nu k) (f k) (A k)).
  exact: tuple_prod_box.
transitivity (density_prob (tuple_prod nu n)
  (fun x => \prod_(k < n) f k (tnth x k))%R (tuple_box A)); last by [].
rewrite (density_probE hF).
pose h (k : nat) (t : T) : R :=
  if insub k is Some i then (f k t * \1_(A i) t)%R else 0%R.
have hE (k : 'I_n) t : h k t = (f k t * \1_(A k) t)%R by rewrite /h valK.
have mh k : measurable_fun [set: T] (h k).
  rewrite /h; case: insubP => [i ki ik|_]; last exact: measurable_cst.
  apply: measurable_funM; first by case: (hf k ki).
  exact: measurable_indic.
have h0 k t : (0 <= h k t)%R.
  rewrite /h; case: insubP => [i ki ik|_] //.
  apply: mulr_ge0; last by rewrite indicE.
  by case: (hf k ki) => _ f0 _; exact: f0.
transitivity (\prod_(k < n) \int[nu k]_t (h k t)%:E); last first.
  rewrite -ge0_integral_tuple_prod_prod //.
  rewrite [RHS]integral_mkcond; apply: eq_integral => x _.
  rewrite epatch_indic /= indic_tuple_box -EFinM -big_split /=.
  by congr (_%:E); apply: eq_bigr => k _; rewrite hE.
apply: eq_bigr => k _; rewrite (density_probE (hf k (ltn_ord k))).
rewrite [LHS]integral_mkcond; apply: eq_integral => t _.
by rewrite epatch_indic /= hE EFinM.
Qed.

Lemma tuple_prod_density_law (nu : nat -> probability T R) (f : nat -> T -> R)
    (hf : forall k, prob_density (nu k) (f k)) n E : measurable E ->
  tuple_prod (fun k => density_law (nu k) (f k) (hf k)) n E =
  \int[tuple_prod nu n]_(x in E) (\prod_(k < n) f k (tnth x k))%:E.
Proof.
move=> mE; rewrite -(tuple_prod_density (fun k _ => hf k) mE).
have fin : tuple_prod (fun k => density_law (nu k) (f k) (hf k)) n
    [set: n.-tuple T] < +oo.
  by rewrite probability_setT ltry.
apply: (measure_tuple_box_unique fin) => // A mA.
transitivity (\prod_(k < n) density_law (nu k) (f k) (hf k) (A k)).
  exact: tuple_prod_box.
transitivity (\prod_(k < n) density_prob (nu k) (f k) (A k)).
  by apply: eq_bigr => k _; rewrite density_law_prob.
by symmetry; exact: tuple_prod_box.
Qed.

End tuple_prod_density.
