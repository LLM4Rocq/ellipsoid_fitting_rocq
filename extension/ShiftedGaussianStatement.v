(* S2: condition numbers for arbitrary deterministic Gaussian translations.
   The constants in the subcritical bound precede the sample-size and shift
   sequences. Its upper-fit event may depend on the specified shift.
   A separate lower-bound statement holds on one event for all translations,
   at every positive density; its constant is quantified independently.
   Source: doc/shifted-gaussian.tex and the formalization plan, S2.
   These are review drafts, not frozen statements. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun probability.
From GaussianAnalysis.matrix Require Import euclidean.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions ConditionDefinitions.
From EllipsoidUniversality.Shifted Require Import Translations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition shifted_gaussian_measurability_statement : Prop :=
  forall n d : nat, forall (m : 'cV[R]_d) (C : R),
  [/\ measurable (sample_translate m @^-1` universality_pd_fit_event n d),
    measurable
      (sample_translate m @^-1` universality_conditioned_fit_event n d C) &
    measurable_fun [set: paper_main_sample n d]
      (fun x => data_condition_number n d (sample_translate m x))].

(* The Borel exceptional set is chosen before m and the condition bound B.
   The lower bound concerns the extended infimum, including samples with
   no fit. It also bounds every realized conditioned fit directly. *)
Definition shifted_gaussian_uniform_lower_statement : Prop :=
  forall alpha : R, 0 < alpha ->
  exists c : R, 0 < c /\
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d),
    [/\ measurable E, (gaussian_product_law (n d*d) E <= eps%:E)%E &
      forall x, ~ E x -> forall m : 'cV[R]_d,
        ((c*(1+frobenius m/Num.sqrt d%:R))%:E <=
          data_condition_number (n d) d (sample_translate m x))%E /\
        (forall B : R,
          universality_conditioned_fit_event (n d) d B (sample_translate m x) ->
          c*(1+frobenius m/Num.sqrt d%:R) <= B)].

(* Both bounds and an actual positive definite fit hold on the same event.
   No restriction is imposed on the magnitude of the deterministic shift.
   The finite upper bound controls the extended optimum without selecting
   a minimizing matrix or asserting that the infimum is attained. *)
Definition shifted_gaussian_bounds_statement : Prop :=
  forall alpha : R, 0 < alpha -> alpha < 4%:R^-1 ->
  exists c C : R, [/\ 0 < c, c <= C &
    forall (n : nat -> nat) (m : forall d, 'cV[R]_d),
    universality_density_tends_to n alpha ->
    forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    exists E : set (paper_main_sample (n d) d),
      [/\ measurable E, (gaussian_product_law (n d*d) E <= eps%:E)%E &
        forall x, ~ E x ->
        [/\ universality_pd_fit_event (n d) d (sample_translate (m d) x),
          universality_conditioned_fit_event (n d) d
            (C*(1+frobenius (m d)/Num.sqrt d%:R)) (sample_translate (m d) x) &
          ((c*(1+frobenius (m d)/Num.sqrt d%:R))%:E <=
            data_condition_number (n d) d (sample_translate (m d) x) <=
            (C*(1+frobenius (m d)/Num.sqrt d%:R))%:E)%E]]].

Definition shifted_gaussian_statement : Prop :=
  [/\ shifted_gaussian_measurability_statement,
    shifted_gaussian_uniform_lower_statement & shifted_gaussian_bounds_statement].
