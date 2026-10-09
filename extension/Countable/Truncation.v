(* The truncation of a countable mixture of product laws to a finite one,
   and the coupling of their samples, at Stdlib's R: item K2 of phase 8
   (notes/three-extensions-plan.md, sections 1.3 and 5.2; lane A). The
   definitions are those of CountableMixtureDefinitions and
   MixtureDefinitions; the general facts on countable mixtures of laws and
   on label sums are those of item L1, library/probability/countable_mixture.v.

   Proved here, for a family with countable_mixture_family K w mu.
   - trunc_cut, trunc_r_le: for every d, a cutoff cut d whose tail mass
     r_d = sum_(s > cut d) w d s (trunc_r d) is at most (d + 1)^-3
     (cmixture_tail_small of library/probability/countable_mixture.v).
   - The truncated finite family: trunc_N d = cut d + 2 components
     (trunc_w, trunc_mu). The components s <= cut d keep their weights and
     laws. The component cut d + 1 has weight r_d, and its coordinate j has
     the law trunc_tail d j of the normalized tail
     sum_(s > cut d) w d s mu d s j / r_d (the law mu d 0 j when r_d = 0).
     trunc_tail_component: this law is a component law with constant K
     (mean 0 by integral_cmixture, variance 1 and the subgaussian bound by
     ge0_integral_cmixture). trunc_family: mixture_family K for the
     truncated family. trunc_fourth: countable_fourth_moment kappa gives
     mixture_fourth_moment kappa, since r_d times the fourth moment of the
     tail law is the tail of the series of the fourth moments.
   - trunc_coupling: for every measurable set E of samples of n points,
       |countable_mixture_probability (w d) (mu d) n d E
        - mixture_probability (trunc_N d) (trunc_w d) (trunc_mu d) n d E|
       <= n r_d,
     by label_coupling and bernoulli_tail of countable_mixture.v: the
     labelled laws of the two families agree on the label tuples whose
     labels are all at most cut d. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import esum exp ereal measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis Require Import lindeberg.
From GaussianAnalysis.probability Require Import subgaussian mixture.
From GaussianAnalysis.probability Require Import countable_mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality.Mixture Require Import Component.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

Section truncation.
Variables (K : R) (w : nat -> nat -> R).
Variable (mu : nat -> nat -> nat -> probability (measurableTypeR R) R).
Hypothesis hfam : countable_mixture_family K w mu.

Lemma trunc_weights d : cmixture_weights (w d).
Proof. by have [h1 [h2 _]] := hfam d; split. Qed.

(* 1. The cutoff: the weights above cut d have mass at most (d + 1)^-3. *)
Lemma trunc_bound_gt0 d : 0 < (d.+1%:R ^+ 3)^-1 :> R.
Proof. by rewrite invr_gt0 exprn_gt0 // ltr0n. Qed.

Definition trunc_cut d : nat :=
  projT1 (cid (cmixture_tail_small (trunc_weights d) (trunc_bound_gt0 d))).

Definition trunc_r d : R := cmixture_tail (w d) (trunc_cut d).

Lemma trunc_r_le d : trunc_r d <= (d.+1%:R ^+ 3)^-1.
Proof.
exact: (projT2 (cid (cmixture_tail_small (trunc_weights d)
  (trunc_bound_gt0 d)))).
Qed.

Lemma trunc_r_ge0 d : 0 <= trunc_r d.
Proof.
rewrite /trunc_r /cmixture_tail; apply: fine_ge0.
by apply: nneseries_ge0 => k _ _; rewrite lee_fin; have [h _] := hfam d.
Qed.

(* 2. The truncated finite family: the components s <= cut d, and the
   component (cut d).+1 of weight r_d whose coordinate laws are those of
   the normalized tail (the component 0 when r_d = 0). *)
Definition trunc_N d : nat := (trunc_cut d).+2.

Definition trunc_w d (k : nat) : R :=
  if (k <= trunc_cut d)%N then w d k
  else if k == (trunc_cut d).+1 then trunc_r d else 0.

Definition trunc_tw d : nat -> R :=
  if 0 < trunc_r d then cmixture_tail_w (w d) (trunc_cut d)
  else fun s => if s == 0%N then 1 else 0.

Lemma trunc_twP d : cmixture_weights (trunc_tw d).
Proof.
rewrite /trunc_tw; case: ifP => r0.
  exact: cmixture_tail_weights (trunc_weights d) _ r0.
split => [s|]; first by case: ifP.
have f0 k : (0 <= k)%N -> (0 <= ((if k == 0%N then 1 else 0 : R))%:E)%E.
  by move=> _; rewrite lee_fin; case: ifP.
rewrite (nneseries_split 0 1 f0) add0n big_nat1 /= eseries0 ?adde0 //.
by move=> k k1 _; case: k k1.
Qed.

Definition trunc_tail d (j : nat) : probability (measurableTypeR R) R :=
  cmixture (fun s => mu d s j) (trunc_twP d).

Definition trunc_mu d (k j : nat) : probability (measurableTypeR R) R :=
  if (k <= trunc_cut d)%N then mu d k j else trunc_tail d j.

(* The normalized tail of component laws with constant K is a component
   law with constant K: mean 0 (integral_cmixture), variance 1 and the
   subgaussian bound (ge0_integral_cmixture). *)
Lemma trunc_tail_component d j : (j < d)%N ->
  mixture_component_law K (trunc_tail d j).
Proof.
move=> jd.
have hc s : mixture_component_law K (mu d s j).
  by have [_ [_ h]] := hfam d; exact: h.
have hw := trunc_twP d.
set tw := trunc_tw d in hw *.
have tw0 s : 0 <= tw s by have [h _] := hw.
have K0 : 0 < K := component_law_K K (mu d 0%N j) (hc 0%N).
have sum2 (c : R) : (\sum_(s <oo) (tw s)%:E * c%:E = c%:E)%E.
  under eq_eseriesr do rewrite muleC.
  have twe : forall s : nat, true -> (0 <= (tw s)%:E)%E.
    by move=> s _; rewrite lee_fin.
  by rewrite nneseriesZl // hw.2 mule1.
have mpow k : measurable_fun setT
    (fun x : measurableTypeR R => (((x : RR) ^+ k)%:E : \bar RR)).
  by apply/measurable_EFinP; exact: measurable_funX.
have hsec s : (\int[mu d s j]_x (((x : RR) ^+ 2)%:E : \bar RR) = 1)%E.
  exact: component_law_second K (mu d s j) (hc s).
have p2 : forall x : measurableTypeR R, setT x ->
    (0 <= (((x : RR) ^+ 2)%:E : \bar RR))%E.
  by move=> x _; rewrite lee_fin sqr_ge0.
split => //; rewrite !unlock /trunc_tail; split; [|split].
- (* mean zero *)
  have absle (x : RR) : `|x| <= 1 + x ^+ 2.
    have h1 := normr_ge0 x.
    have h2 : `|x| ^+ 2 = x ^+ 2 by rewrite real_normK // num_real.
    by nra.
  have abs2 s : (\int[mu d s j]_x `|(((x : RR) ^+ 1)%:E : \bar RR)| <=
      2%:E)%E.
    apply: (@le_trans _ _
      (\int[mu d s j]_x ((1 + (x : RR) ^+ 2)%:E : \bar RR))%E).
      apply: ge0_le_integral => //.
      - by apply: measurableT_comp => //; exact: mpow.
      - by apply/measurable_EFinP; apply: measurable_funD => //;
          exact: measurable_funX.
      - by move=> x _; rewrite expr1 lee_fin.
    under eq_integral do rewrite EFinD.
    have c0 : forall x : measurableTypeR R, setT x -> (0 <= (1 : \bar RR))%E.
      by move=> x _; exact: lee01.
    have mc : measurable_fun setT
        (fun _ : measurableTypeR R => (1%E : \bar RR)).
      exact: measurable_cst.
    rewrite (ge0_integralD (mu d s j) measurableT c0 mc p2 (mpow 2%N)) hsec.
    by rewrite integral_cst //= probability_setT mule1 -EFinD.
  have fs : (\sum_(s <oo) (tw s)%:E *
      \int[mu d s j]_x `|(((x : RR) ^+ 1)%:E : \bar RR)| < +oo)%E.
    apply: (@le_lt_trans _ _ (\sum_(s <oo) (tw s)%:E * 2%:E)%E).
      apply: lee_nneseries => [s _ _|s _].
        rewrite mule_ge0 ?lee_fin ?tw0 //.
        by apply: integral_ge0 => x _; exact: abse_ge0.
      by apply: lee_wpmul2l; [rewrite lee_fin tw0 | exact: abs2].
    by rewrite sum2 ltry.
  have ii s : (mu d s j).-integrable setT
      (fun x : measurableTypeR R => (((x : RR) ^+ 1)%:E : \bar RR)).
    exact: component_law_integrable K (mu d s j) (hc s) 1%N.
  rewrite /universality_power.
  have [_ ->] := integral_cmixture (trunc_twP d) measurableT (mpow 1%N) ii fs.
  have hm s : (\int[mu d s j]_x (((x : RR) ^+ 1)%:E : \bar RR) = 0)%E.
    under eq_integral do rewrite expr1.
    exact: component_law_mean K (mu d s j) (hc s).
  under eq_eseriesr do rewrite hm mule0.
  by rewrite eseries0.
- (* variance one *)
  rewrite (ge0_integral_cmixture _ (trunc_twP d) measurableT (mpow 2%N) p2).
  under eq_eseriesr do rewrite hsec.
  exact: sum2.
- (* the subgaussian bound *)
  have mt : measurable_fun setT (fun x : measurableTypeR R =>
      ((universality_subgaussian_test K x)%:E : \bar RR)).
    apply/measurable_EFinP; rewrite /universality_subgaussian_test.
    apply: (@measurableT_comp _ _ _ _ _ _ expR) => //.
    by apply: measurable_funM => //; exact: measurable_funX.
  have t0 : forall x : measurableTypeR R, setT x ->
      (0 <= ((universality_subgaussian_test K x)%:E : \bar RR))%E.
    by move=> x _; rewrite lee_fin expR_ge0.
  rewrite (ge0_integral_cmixture _ (trunc_twP d) measurableT mt t0).
  apply: le_trans (_ : (\sum_(s <oo) (tw s)%:E * 2%:E <= _)%E).
    apply: lee_nneseries => [s _ _|s _].
      by rewrite mule_ge0 ?lee_fin ?tw0 //; exact: integral_ge0.
    apply: lee_wpmul2l; first by rewrite lee_fin tw0.
    by have [_ [_ [_ h]]] := hc s; move: h; rewrite unlock.
  by rewrite sum2.
Qed.

Lemma trunc_family : mixture_family K trunc_N trunc_w trunc_mu.
Proof.
move=> d; have [w0 [w1 hc]] := hfam d.
split; [|split].
- move=> k _; rewrite /trunc_w; case: ifP => _; first exact: w0.
  by case: ifP => _; [exact: trunc_r_ge0 | exact: lexx].
- rewrite /trunc_N big_ord_recr /= /trunc_w ltnn eqxx.
  have [_ hh] := cmixture_tailE (trunc_weights d) (trunc_cut d).
  rewrite -[RHS]hh /trunc_r; congr (_ + _).
  by apply: eq_bigr => k _; rewrite -ltnS ltn_ord.
- move=> k j kN jd; rewrite /trunc_mu; case: ifP => _; first exact: hc.
  exact: trunc_tail_component.
Qed.

Lemma trunc_fourth (kappa : R) : countable_fourth_moment kappa w mu ->
  mixture_fourth_moment kappa trunc_N trunc_w trunc_mu.
Proof.
move=> h4 d j jd.
have [w0 [w1 hc]] := hfam d.
have hd := h4 d j jd.
rewrite /trunc_N big_ord_recr /=.
have lastw : trunc_w d (trunc_cut d).+1 = trunc_r d.
  by rewrite /trunc_w ltnn eqxx.
have lastm : trunc_mu d (trunc_cut d).+1 j = trunc_tail d j.
  by rewrite /trunc_mu ltnn.
have headm (k : 'I_(trunc_cut d).+1) :
    ((trunc_w d k)%:E * 'E_(trunc_mu d k j)[universality_power 4] =
     (w d k)%:E * 'E_(mu d k j)[universality_power 4])%E.
  by rewrite /trunc_w /trunc_mu -ltnS ltn_ord.
rewrite lastw lastm (eq_bigr _ (fun k _ => headm k)).
pose E := fun s => ('E_(mu d s j)[universality_power 4])%E.
have E0 s : (0 <= E s)%E.
  rewrite /E unlock; apply: integral_ge0 => x _.
  by rewrite lee_fin /universality_power exprn_even_ge0.
have Ele s : (E s <= (4%:R * K ^+ 4)%:E)%E.
  by rewrite /E unlock; exact: component_law_fourth_le K (mu d s j) (hc s j jd).
have mx4 : measurable_fun setT
    (fun x : measurableTypeR R => (((x : RR) ^+ 4)%:E : \bar RR)).
  by apply/measurable_EFinP; exact: measurable_funX.
have x40 : forall x : measurableTypeR R, setT x ->
    (0 <= (((x : RR) ^+ 4)%:E : \bar RR))%E.
  by move=> x _; rewrite lee_fin exprn_even_ge0.
(* the tail component carries the fourth moment of the tail *)
have tailE : ('E_(trunc_tail d j)[universality_power 4] =
    \sum_(s <oo) (trunc_tw d s)%:E * E s)%E.
  rewrite unlock /trunc_tail /universality_power.
  rewrite (ge0_integral_cmixture _ (trunc_twP d) measurableT mx4 x40).
  by apply: eq_eseriesr => s _; rewrite /E unlock.
have wE0 s : (0 <= (w d s)%:E * E s)%E by rewrite mule_ge0 ?lee_fin.
have tailr : ((trunc_r d)%:E * 'E_(trunc_tail d j)[universality_power 4] =
    \sum_(s <oo | (trunc_cut d < s)%N) (w d s)%:E * E s)%E.
  rewrite tailE /trunc_tw; case: ifP => r0.
    rewrite (cmixture_tail_series (trunc_weights d) r0 E0) muleA -EFinM.
    by rewrite mulfV ?mul1e //; exact: lt0r_neq0.
  have rz : trunc_r d = 0.
    by apply/eqP; rewrite eq_le trunc_r_ge0 andbT leNgt r0.
  rewrite rz mul0e; apply/esym/eqP; rewrite eq_le; apply/andP; split.
    apply: (@le_trans _ _ (\sum_(s <oo | (trunc_cut d < s)%N)
        (4%:R * K ^+ 4)%:E * (w d s)%:E)%E).
      apply: lee_nneseries => [s _ _|s _]; first exact: wE0.
      rewrite [X in (_ <= X)%E]muleC; apply: lee_wpmul2l; last exact: Ele.
      by rewrite lee_fin.
    have wP s : (trunc_cut d < s)%N -> (0 <= (w d s)%:E)%E.
      by move=> _; rewrite lee_fin.
    rewrite nneseriesZl //.
    have [h _] := cmixture_tailE (trunc_weights d) (trunc_cut d).
    by rewrite h -/(trunc_r d) rz mule0.
  by apply: nneseries_ge0 => s _ _; exact: wE0.
rewrite /E in tailr wE0; rewrite tailr -hd.
have wE0' k : (0 <= k)%N ->
    (0 <= (w d k)%:E * ('E_(mu d k j)[universality_power 4]))%E.
  by move=> _; exact: wE0.
by rewrite (nneseries_split 0 (trunc_cut d).+1 wE0') add0n ereal_series
  big_mkord.
Qed.

(* 3. The coupling of the samples. *)
Lemma trunc_coupling (n d : nat) (E : set (paper_main_sample n d)) :
  measurable E ->
  (`|countable_mixture_probability (w d) (mu d) n d E -
     mixture_probability (trunc_N d) (trunc_w d) (trunc_mu d) n d E| <=
   (n%:R * trunc_r d)%:E)%E.
Proof.
move=> mE.
have [q0 [q1 _]] := trunc_family d.
have mN : (trunc_cut d < trunc_N d)%N by rewrite /trunc_N.
have qp k : (k <= trunc_cut d)%N -> trunc_w d k = w d k.
  by rewrite /trunc_w => ->.
(* the labelled laws agree on the label tuples with all labels <= cut d *)
have QQ (t : n.-tuple 'I_(trunc_N d)) :
    all (fun k : 'I_(trunc_N d) => (k <= trunc_cut d)%N) t ->
    mixture_labelled_law (trunc_N d) (trunc_mu d) n d t E =
    countable_labelled_law (mu d) n d
      (map_tuple (@nat_of_ord (trunc_N d)) t) E.
  move=> ht; rewrite /mixture_labelled_law /countable_labelled_law.
  congr (tuple_prod _ _ E); apply/funext => k.
  rewrite /mixture_label /trunc_mu /=.
  have -> : (nth 0%N (map val t) (k %/ d) <= trunc_cut d)%N.
    have [kn|kn] := ltnP (k %/ d) n.
      have hm : nth 0%N (map val t) (k %/ d) \in map val t.
        by rewrite mem_nth // size_map size_tuple.
      by move: hm => /mapP [x xt ->]; exact: (allP ht x xt).
    by rewrite nth_default // size_map size_tuple.
  by [].
apply: le_trans (label_coupling (trunc_weights d) mE mN q0 q1 qp QQ) _.
rewrite lee_fin -/(trunc_r d).
apply: bernoulli_tail; apply/andP; split; first exact: trunc_r_ge0.
have [_ hh] := cmixture_tailE (trunc_weights d) (trunc_cut d).
have : 0 <= \sum_(k < (trunc_cut d).+1) w d k.
  by apply: sumr_ge0 => k _; have [h0 _] := hfam d; exact: h0.
by rewrite /trunc_r; lra.
Qed.

End truncation.
