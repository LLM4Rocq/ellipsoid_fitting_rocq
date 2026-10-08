(* Exact fitting for the paired law, from the finite-mixture theorem, at
   Stdlib's R: item P3 of phase 6 (notes/paired-law-plan-v2.md, section
   4.3; notes/mixture-product-universality.md, section 5).

   Proved here.
   - paired_family, paired_fourth: for -1 <= eps d <= 7/3 and the uniform
     law mu, the paired law of a point is a finite mixture of product laws
     whose components are component laws with constant 3
     (mixture_family 3 of MixtureDefinitions) and whose coordinates have
     the common fourth moment 9/5 (mixture_fourth_moment), with the
     components, weights and laws of Paired/Law.
   - paired_of_mixture: mixture_theorem_statement implies paired_statement,
     since paired_probability is mixture_probability on measurable events
     (paired_probability_mixture of Paired/Law). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions MixtureStatement.
From EllipsoidUniversality Require Import PairedDefinitions PairedStatement.
From EllipsoidUniversality.Paired Require Import Uniform Law.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section paired_family.
Variables (eps : nat -> R) (mu : probability (measurableTypeR R) R).
Hypothesis he : forall d, - 1 <= eps d <= 7%:R / 3%:R.
Hypothesis hmu : paired_uniform_spec mu.

Lemma paired_family :
  mixture_family 3%:R paired_N (fun d => paired_w (eps d) d)
    (fun d => paired_mu (eps d) mu d).
Proof.
move=> d; split; first by move=> s _; exact: paired_w_ge0.
split; first exact: paired_w_sum.
by move=> s j _ _; exact: (paired_mu_component (eps d) mu (he d) hmu).
Qed.

Lemma paired_fourth :
  mixture_fourth_moment (9%:R / 5%:R) paired_N (fun d => paired_w (eps d) d)
    (fun d => paired_mu (eps d) mu d).
Proof. by move=> d j _; exact: (paired_mu_fourth (eps d) mu (he d) hmu). Qed.

(* The paired law and the mixture agree on measurable events. *)
Lemma paired_mixtureE (n : nat -> nat)
    (E : forall d, set (paper_main_sample (n d) d)) :
  (forall d, measurable (E d)) ->
  (fun d => paired_probability (eps d) mu (n d) d (E d)) =
  (fun d => mixture_probability (paired_N d) (paired_w (eps d) d)
              (paired_mu (eps d) mu d) (n d) d (E d)).
Proof.
move=> mE; apply/funext => d.
exact: (paired_probability_mixture (eps d) mu (he d) hmu (n d) d (E d) (mE d)).
Qed.

End paired_family.

Theorem paired_of_mixture : mixture_theorem_statement -> paired_statement.
Proof.
move=> [hM hI] alpha a0.
have k1 : 1 < 9%:R / 5%:R :> R by rewrite ltr_pdivlMr // mul1r ltr_nat.
have K0 : 0 < 3%:R :> R by rewrite ltr0n.
have [h1 h2 [m3 h3]] := hM (9%:R / 5%:R) 3%:R alpha k1 K0 a0.
split.
- move=> ha; have [c [c1 [m1 [m2 h]]]] := h1 ha.
  exists c; split => //; split => //; split => // eps he mu hmu n hn.
  rewrite (paired_mixtureE _ _ he hmu n _ (fun d => m1 (n d) d)).
  rewrite (paired_mixtureE _ _ he hmu n _ (fun d => m2 (n d) d)).
  exact: h _ _ _ (paired_family _ _ he hmu) (paired_fourth _ _ he hmu) n hn.
- move=> ha; have [e0 [m0 h]] := h2 ha.
  split => //; split => // eps he mu hmu n hn.
  rewrite (paired_mixtureE _ _ he hmu n _ (fun d => m0 (n d) d)).
  exact: h _ _ _ (paired_family _ _ he hmu) (paired_fourth _ _ he hmu) n hn.
- split => // eps he mu hmu n hn e e0.
  rewrite (paired_mixtureE _ _ he hmu n _ (fun d => m3 (n d) d e)).
  exact: h3 _ _ _ (paired_family _ _ he hmu) (paired_fourth _ _ he hmu) n hn e e0.
- move=> ah; have [C [C0 hC]] := hI 3%:R alpha K0 a0 ah.
  exists C; split => // eps he mu hmu n hn e e0.
  have [D hD] := hC _ _ _ (paired_family _ _ he hmu) n hn e e0.
  exists D => d dD; have [E [mE PE hE]] := hD d dD.
  exists E; split => //.
  by rewrite (paired_probability_mixture (eps d) mu (he d) hmu (n d) d E mE).
Qed.
