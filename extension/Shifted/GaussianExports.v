(* Gaussian specializations of the existing mixture inputs. Every
   probability below uses gaussian_product_law (n * d), the frozen flat
   sample law. These statements concern centered Gaussian samples only.
   Interpolation and adjoint bounds use measurable exceptional sets;
   their full success events are not asserted measurable. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.matrix Require Import euclidean.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions ConditionDefinitions.
From EllipsoidUniversality Require Import MixtureStatement ConditionStatement.
From EllipsoidUniversality Require Import MixtureTheorem ConditionTheorem.
Require Import EllipsoidUniversality.Condition.Theorem.
From EllipsoidUniversality.Sat Require Import Apriori.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Shifted Require Import GaussianInputs.

Import GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition gaussian_condition_threshold_statement : Prop :=
  forall C alpha : R, 1 < C -> 0 < alpha ->
  (forall n d, measurable (universality_conditioned_fit_event n d C)) /\
  (forall n : nat -> nat, universality_density_tends_to n alpha ->
    (alpha < condition_alpha C ->
      paper_main_tends_to (fun d => gaussian_product_law (n d * d)
        (universality_conditioned_fit_event (n d) d C)) 1%R) /\
    (condition_alpha C < alpha ->
      paper_main_tends_to (fun d => gaussian_product_law (n d * d)
        (universality_conditioned_fit_event (n d) d C)) 0%R)).

Definition gaussian_condition_number_statement : Prop :=
  (forall n d, measurable_fun [set: paper_main_sample n d]
    (data_condition_number n d)) /\
  (forall alpha : R, 0 < alpha -> alpha < 4%:R^-1 ->
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   forall eps delta : R, 0 < eps -> 0 < delta ->
   exists D : nat, forall d, (D <= d)%N ->
   exists E : set (paper_main_sample (n d) d), [/\ measurable E,
     (gaussian_product_law (n d * d) E <= delta%:E)%E &
     forall x, ~ E x ->
       (`|data_condition_number (n d) d x - (condition_star alpha)%:E| <=
         eps%:E)%E]).

Definition gaussian_interpolation_statement : Prop :=
  forall alpha : R, 0 < alpha -> alpha < 2%:R^-1 ->
  exists C : R, 0 < C /\
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (gaussian_product_law (n d * d) E <= eps%:E)%E &
    forall x, ~ E x -> mixture_interpolation (n d) d C x].

Definition gaussian_adjoint_statement : Prop :=
  forall alpha : R, 0 < alpha ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (gaussian_product_law (n d * d) E <= eps%:E)%E &
    forall x, ~ E x -> norm_good (n d) d 1%:R x /\
      forall z : 'rV[R]_(n d),
        frobenius (sample_adj x z) <=
          adj_const 2%:R 252%:R (alpha + 1) *
            Num.sqrt d%:R * frobenius z].

Definition gaussian_fitting_error_statement : Prop :=
  forall alpha : R, 0 < alpha ->
  (forall n d eps,
    measurable (universality_error_event n d
      (universality_e_star alpha 3%:R) eps)) /\
  (forall n : nat -> nat, universality_density_tends_to n alpha ->
   forall eps : R, 0 < eps ->
    paper_main_tends_to (fun d => gaussian_product_law (n d * d)
      (universality_error_event (n d) d
        (universality_e_star alpha 3%:R) eps)) 0%R).

Theorem gaussian_adjoint_holds : gaussian_adjoint_statement.
Proof.
move=> alpha a0 n hn eps e0.
have [D hD] := adjoint_bound_limit 3%:R 2%:R alpha
  (fun _ _ => gaussian_law_probability) n
  (fun _ _ _ => gaussian_coordinate_law) a0 hn eps e0.
exists D => d dD; have [E [mE PE hE]] := hD d dD.
exists E; split => //.
by rewrite gaussian_sample_lawE.
Qed.

Lemma gaussian_mixture_tends_to (n : nat -> nat)
    (E : forall d, set (paper_main_sample (n d) d)) (l : R) :
  paper_main_tends_to (fun d =>
    mixture_probability 1 (fun=> 1) (fun _ _ => gaussian_law_probability)
      (n d) d (E d)) l ->
  paper_main_tends_to (fun d => gaussian_product_law (n d * d) (E d)) l.
Proof.
have -> : (fun d => gaussian_product_law (n d * d) (E d)) =
    (fun d => mixture_probability 1 (fun=> 1)
      (fun _ _ => gaussian_law_probability) (n d) d (E d)).
  by apply/funext => d; rewrite gaussian_mixture_probability.
by [].
Qed.

Lemma gaussian_condition_threshold_of_mixture :
  condition_statement -> gaussian_condition_threshold_statement.
Proof.
move=> h C alpha C1 a0.
have K0 : (0 : R) < 2%:R by rewrite ltr0n.
have [mE hC] := h 2%:R C alpha K0 C1 a0.
split => // n hn.
have [hlo hhi] := hC _ _ _ gaussian_mixture_family
  gaussian_mixture_fourth_moment n hn.
split=> hlt; apply: gaussian_mixture_tends_to.
- exact: hlo hlt.
- exact: hhi hlt.
Qed.

Lemma gaussian_condition_number_of_mixture :
  (forall n d, measurable_fun [set: paper_main_sample n d]
    (data_condition_number n d)) ->
  condition_number_statement -> gaussian_condition_number_statement.
Proof.
move=> mC h; split => // alpha a0 a4 n hn eps delta e0 de0.
have K0 : (0 : R) < 2%:R by rewrite ltr0n.
have [D hD] := h 2%:R alpha K0 a0 a4 _ _ _ gaussian_mixture_family
  gaussian_mixture_fourth_moment n hn eps delta e0 de0.
exists D => d dD; have [E [mE PE hE]] := hD d dD.
exists E; split => //.
by rewrite -gaussian_mixture_probability.
Qed.

Lemma gaussian_interpolation_of_mixture :
  mixture_interpolation_statement -> gaussian_interpolation_statement.
Proof.
move=> h alpha a0 a2.
have K0 : (0 : R) < 2%:R by rewrite ltr0n.
have [C [C0 hC]] := h 2%:R alpha K0 a0 a2.
exists C; split => // n hn eps e0.
have [D hD] := hC _ _ _ gaussian_mixture_family n hn eps e0.
exists D => d dD; have [E [mE PE hE]] := hD d dD.
exists E; split => //.
by rewrite -gaussian_mixture_probability.
Qed.

Lemma gaussian_fitting_error_of_mixture :
  mixture_statement -> gaussian_fitting_error_statement.
Proof.
move=> h alpha a0.
have k1 : (1 : R) < 3%:R by rewrite ltr1n.
have K0 : (0 : R) < 2%:R by rewrite ltr0n.
have [_ _ [mE hE]] := h 3%:R 2%:R alpha k1 K0 a0.
split => // n hn eps e0; apply: gaussian_mixture_tends_to.
exact: hE _ _ _ gaussian_mixture_family gaussian_mixture_fourth_moment n hn eps e0.
Qed.

Theorem gaussian_interpolation_holds : gaussian_interpolation_statement.
Proof.
apply: gaussian_interpolation_of_mixture.
by have [_ h] := mixture_theorem.
Qed.

Theorem gaussian_fitting_error_holds : gaussian_fitting_error_statement.
Proof.
apply: gaussian_fitting_error_of_mixture.
by have [h _] := mixture_theorem.
Qed.

Theorem gaussian_condition_threshold_holds : gaussian_condition_threshold_statement.
Proof.
apply: gaussian_condition_threshold_of_mixture.
by have [h _ _ _] := condition_theorem.
Qed.

Theorem gaussian_condition_number_holds : gaussian_condition_number_statement.
Proof.
apply: gaussian_condition_number_of_mixture.
- exact: measurable_data_condition_number.
- by have [_ h _ _] := condition_theorem.
Qed.
