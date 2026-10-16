(* S7: exact opposite-shift mixture laws and their fitting consequences.
   This is an explicit proposition for review, not a frozen statement.

   The outer-product identity holds over any realType, for independent
   samples from a centrally symmetric row law. The fitting clauses use
   the project's Stdlib-R definitions. Every weight lies in the closed
   interval [0,1]; asymptotic weights may vary with dimension.

   The Gaussian clauses retain their separate shift assumptions: the
   sharp conditioned threshold and optimal-condition limit require a
   small shift, while the existence bound, two-sided condition bounds,
   fitting-error limit and PSD nonexistence allow arbitrary shifts.
   Finite/countable mixtures require symmetry of the actual row law;
   their PD existence clause requires only sparse support, with no
   restriction on shift magnitude. No clause transfers arbitrary-center
   quadric exclusion or an infimum over further translations. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun probability.
From GaussianAnalysis.analysis Require Import family_reindexing.
From GaussianAnalysis.gaussian Require Import gauss measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean coordinate_blocks.
From GaussianAnalysis.probability Require Import lindeberg mixture tuple_rows symmetric_shift.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions
  ConditionDefinitions MixtureDefinitions CountableMixtureDefinitions.
From EllipsoidUniversality.Shifted Require Import GaussianCondition
  MixtureRows SignMixture.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

(* Equality of the joint laws of all individual outer products. *)
Definition shifted_sign_outer_statement : Prop :=
  forall (F : realType) (d n : nat) (P : probability 'rV[F]_d F)
    (m : 'rV[F]_d) (w : F) (hw : 0 <= w <= 1)
    (A : set (n.-tuple 'M[F]_d)),
  row_symmetric_law P -> measurable A ->
  tuple_prod (fun=>sign_shift_law P m hw) n
    (tuple_map (fun _=>row_outer) @^-1` A) =
  tuple_prod (fun=>row_shift_law P m) n
    (tuple_map (fun _=>row_outer) @^-1` A).

(* Exact finite-sample centered-fitting probabilities and observable laws. *)
Definition shifted_sign_observables_statement : Prop :=
  forall (d n : nat) (P : probability 'rV[RR]_d RR)
    (m : 'cV[R]_d) (w : R) (hw : 0 <= w <= 1),
  row_symmetric_law P ->
  [/\
    sign_mixture_sample_law P m hw n (paper_main_fit_event n d) =
      shifted_iid_sample_law P m n (paper_main_fit_event n d),
    sign_mixture_sample_law P m hw n (universality_pd_fit_event n d) =
      shifted_iid_sample_law P m n (universality_pd_fit_event n d),
    (forall C : R,
      sign_mixture_sample_law P m hw n (universality_conditioned_fit_event n d C) =
        shifted_iid_sample_law P m n (universality_conditioned_fit_event n d C)),
    (forall A : set (\bar R), measurable A ->
      sign_mixture_sample_law P m hw n (data_condition_number n d @^-1` A) =
        shifted_iid_sample_law P m n (data_condition_number n d @^-1` A)) &
    (forall A : set RR, measurable A ->
      sign_mixture_sample_law P m hw n (universality_fitting_error n d @^-1` A) =
        shifted_iid_sample_law P m n (universality_fitting_error n d @^-1` A))].

(* Gaussian applications, with constants chosen before shifts and weights. *)
Definition shifted_sign_gaussian_statement : Prop :=
(* gaussian_sign_condition_threshold *)
(forall (alpha C : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (w : nat -> R) (hw : forall d, 0 <= w d <= 1),
  1 < C -> 0 < alpha -> universality_density_tends_to N alpha ->
  gaussian_small_shift m ->
  (alpha < condition_alpha C ->
    paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
      (N d) (universality_conditioned_fit_event (N d) d C)) 1) /\
  (condition_alpha C < alpha ->
    paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
      (N d) (universality_conditioned_fit_event (N d) d C)) 0)) /\

(* gaussian_sign_optimal_tail *)
(forall (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (w : nat -> R) (hw : forall d, 0 <= w d <= 1),
  0 < alpha -> alpha < 4%:R^-1 ->
  universality_density_tends_to N alpha -> gaussian_small_shift m ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
    (N d) [set x | (eps%:E < `|data_condition_number (N d) d x-
      (condition_star alpha)%:E|)%E]) 0) /\

(* gaussian_sign_arbitrary_shift_exists *)
(forall (alpha : R),
  0 < alpha -> alpha < 4%:R^-1 ->
  exists K : R, 0 < K /\
  forall (N : nat -> nat) (m : forall d, 'cV[R]_d)
    (w : nat -> R) (hw : forall d, 0 <= w d <= 1),
  universality_density_tends_to N alpha ->
  paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
    (N d) (universality_conditioned_fit_event (N d) d
      (K*(1+frobenius (m d)/Num.sqrt d%:R)))) 1) /\

(* gaussian_sign_error_limit *)
(forall (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (w : nat -> R) (hw : forall d, 0 <= w d <= 1),
  0 < alpha -> universality_density_tends_to N alpha ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
    (N d) (universality_error_event (N d) d (universality_e_star alpha 3%:R) eps)) 0) /\

(* gaussian_sign_arbitrary_shift_condition_bounds *)
(forall (alpha : R),
  0 < alpha -> alpha < 4%:R^-1 ->
  exists c C : R, [/\ 0 < c, c <= C &
  forall (N : nat -> nat) (m : forall d, 'cV[R]_d)
    (w : nat -> R) (hw : forall d, 0 <= w d <= 1),
    universality_density_tends_to N alpha ->
    forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    exists E : set (paper_main_sample (N d) d),
      [/\ measurable E,
        (sign_mixture_sample_law (gauss d) (m d) (hw d) (N d) E <= eps%:E)%E &
        forall x, ~ E x ->
        universality_conditioned_fit_event (N d) d
          (C*(1+frobenius (m d)/Num.sqrt d%:R)) x /\
        ((c*(1+frobenius (m d)/Num.sqrt d%:R))%:E <=
          data_condition_number (N d) d x <=
          (C*(1+frobenius (m d)/Num.sqrt d%:R))%:E)%E]]) /\

(* gaussian_sign_psd_nonexistence *)
(forall (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (w : nat -> R) (hw : forall d, 0 <= w d <= 1),
  4%:R^-1 < alpha -> universality_density_tends_to N alpha ->
  paper_main_tends_to (fun d => sign_mixture_sample_law (gauss d) (m d) (hw d)
    (N d) (paper_main_fit_event (N d) d)) 0).

(* Symmetric finite and countable product-mixture applications. *)
Definition shifted_sign_mixture_statement : Prop :=
(forall (K : R) (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : mixture_family K N w mu)
    (kappa alpha : R) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) (a : nat -> R) (ha : forall d, 0<=a d<=1),
  1<kappa -> universality_alpha_star kappa<alpha -> 0<K ->
  (forall d, row_symmetric_law (finite_row_law hfam d)) ->
  mixture_fourth_moment kappa N w mu -> universality_density_tends_to n alpha ->
  paper_main_tends_to (fun d=>sign_mixture_sample_law
    (finite_row_law hfam d) (m d) (ha d) (n d) (paper_main_fit_event (n d) d)) 0) /\
(forall (K : R) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : countable_mixture_family K w mu)
    (kappa alpha : R) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) (a : nat -> R) (ha : forall d, 0<=a d<=1),
  1<kappa -> universality_alpha_star kappa<alpha -> 0<K ->
  (forall d, row_symmetric_law (countable_row_law hfam d)) ->
  countable_fourth_moment kappa w mu -> universality_density_tends_to n alpha ->
  paper_main_tends_to (fun d=>sign_mixture_sample_law
    (countable_row_law hfam d) (m d) (ha d) (n d) (paper_main_fit_event (n d) d)) 0) /\
(forall (kappa K alpha : R)
    (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : mixture_family K N w mu) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) (a : nat -> R) (ha : forall d, 0<=a d<=1),
  1<kappa -> 0<K -> 0<alpha -> alpha<universality_alpha_star kappa ->
  (forall d, row_symmetric_law (finite_row_law hfam d)) ->
  mixture_fourth_moment kappa N w mu -> universality_density_tends_to n alpha ->
  family_sequence_limit (fun d => (#|coordinate_support (m d)|)%:R/d%:R : RR) 0 ->
  paper_main_tends_to (fun d=>sign_mixture_sample_law
    (finite_row_law hfam d) (m d) (ha d) (n d) (universality_pd_fit_event (n d) d)) 1) /\
(forall (kappa K alpha : R)
    (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : countable_mixture_family K w mu) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) (a : nat -> R) (ha : forall d, 0<=a d<=1),
  1<kappa -> 0<K -> 0<alpha -> alpha<universality_alpha_star kappa ->
  (forall d, row_symmetric_law (countable_row_law hfam d)) ->
  countable_fourth_moment kappa w mu -> universality_density_tends_to n alpha ->
  family_sequence_limit (fun d => (#|coordinate_support (m d)|)%:R/d%:R : RR) 0 ->
  paper_main_tends_to (fun d=>sign_mixture_sample_law
    (countable_row_law hfam d) (m d) (ha d) (n d) (universality_pd_fit_event (n d) d)) 1).

Definition shifted_sign_statement : Prop :=
  [/\ shifted_sign_outer_statement, shifted_sign_observables_statement,
       shifted_sign_gaussian_statement & shifted_sign_mixture_statement].
