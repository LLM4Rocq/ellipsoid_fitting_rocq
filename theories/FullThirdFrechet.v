From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights ThirdDefinitions Cumulants
  MatrixSecond MatrixThird LowerDefinitions LowerFrechet FullThirdDefinitions
  MatrixCoordinates.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/FullThirdFrechet.v from Coquelicot to MathComp-Analysis.

   Every theorem of the original keeps its name and its arguments, in the
   same order. No lemma is added. The statements change form in the same
   ways as in the port of LowerFrechet, which this module imports.

   1. Normed spaces. Coquelicot's NormedModule R_AbsRing becomes
      normedModType R, a real normed space of MathComp-Analysis.

   2. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis: f is differentiable at A and its
      differential 'd f A is l. Both say that l is linear and continuous and
      that f (A + H) = f A + l H + o(H) as H tends to 0.

   3. Linear maps. Coquelicot's is_linear l, in the hypotheses of
      lower_inner_covariance_frechet and lower_third_frechet, is stated as in
      LowerFrechet and MatrixCoordinates as the conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and Coquelicot's norm bound, with the
      absolute value on R and the norm of E.

   4. Real-valued maps. A map into R given to is_diff or linear is written
      with codomain R^o, the normed module view of R, as in
      (F z s : E -> R^o). R^o is R by definition, so F keeps the type
      nat -> nat -> E -> R of the original, and the maps are the same.

   So the hypotheses and conclusions say the same thing as in the original.
   lower_second_symmetric, lower_third_swap_left and lower_third_swap_right
   keep their statements word for word, with E : normedModType R.

   The arithmetic is Stdlib's, as in the original. In the proofs,
   filterdiff_linear becomes matrix_linear_is_diff of MatrixCoordinates,
   which is why this module imports MatrixCoordinates in addition to the
   imports of the original. filterdiff_const becomes is_diff_cst,
   filterdiff_ext_lin becomes is_diff_eq with an equation of functions,
   filterdiff_minus_fct becomes is_diffB, and filterdiff_scal_r_fct becomes
   the product rule matrix_second_mult_frechet of MatrixSecond with a
   constant left factor. *)

Theorem lower_inner_covariance_frechet {E : normedModType R} gamma
    (F : nat -> nat -> E -> R) S (A U V : E) z :
  S <> [] ->
  (forall s, In s S ->
    linear (F z s : E -> R^o) /\
    exists M : R, 0 < M /\ forall x : E, (`|F z s x|)%R <= M * (`|x|)%R) ->
  is_diff A ((fun M => lower_inner_covariance gamma F S M U V z) : E -> R^o)
    (fun W => gamma * lower_inner_cumulant gamma F S A U V W z).
Proof.
  intros HS HF.
  pose proof (gibbs_covariance_frechet gamma (F z) (F z)
    (fun s (_ : E) => F z s U) (fun (_ : nat) (_ : E) => 0)
    (fun s (_ : E) => F z s V) (fun (_ : nat) (_ : E) => 0) S A HS) as HD.
  assert (HDf : forall s, In s S -> is_diff A (F z s : E -> R^o) (F z s)).
  { intros s Hs; apply matrix_linear_is_diff, HF; exact Hs. }
  assert (HU : forall s, In s S ->
    is_diff A ((fun _ : E => F z s U) : E -> R^o) (fun _ : E => 0)).
  { intros s Hs; exact (is_diff_cst (F z s U : R^o) A). }
  assert (HV : forall s, In s S ->
    is_diff A ((fun _ : E => F z s V) : E -> R^o) (fun _ : E => 0)).
  { intros s Hs; exact (is_diff_cst (F z s V : R^o) A). }
  specialize (HD HDf HU HV).
  unfold lower_inner_covariance, lower_inner_cumulant.
  apply: (is_diff_eq HD).
  apply: funext => W.
  change (gibbs_covariance gamma (fun s => F z s A) S
      (fun _ => 0) (fun s => F z s V) +
    gibbs_covariance gamma (fun s => F z s A) S
      (fun s => F z s U) (fun _ => 0) +
    gamma * gibbs_cumulant3 gamma (fun s => F z s A) S
      (fun s => F z s U) (fun s => F z s V) (fun s => F z s W) =
    gamma * gibbs_cumulant3 gamma (fun s => F z s A) S
      (fun s => F z s U) (fun s => F z s V) (fun s => F z s W)).
  rewrite gibbs_covariance_zero_left gibbs_covariance_zero_right; ring.
Qed.

Theorem lower_third_frechet {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U V : E) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall z s, In z Y -> In s S ->
    linear (F z s : E -> R^o) /\
    exists M : R, 0 < M /\ forall x : E, (`|F z s x|)%R <= M * (`|x|)%R) ->
  is_diff A ((fun M => lower_second beta gamma F Y S M U V) : E -> R^o)
    (lower_third beta gamma F Y S A U V).
Proof.
  intros Hb Hg HY HS HL.
  assert (HF : forall y, In y Y ->
    is_diff A ((fun M => lower_inner_value gamma F S M y) : E -> R^o)
      (fun W => lower_inner_first gamma F S A W y)).
  { intros z Hz; apply lower_inner_frechet; try assumption; intros; apply HL; assumption. }
  assert (HD : forall P y, In y Y ->
    is_diff A ((fun M => lower_inner_first gamma F S M P y) : E -> R^o)
      (fun W => gamma * lower_inner_covariance gamma F S A P W y)).
  { intros P z Hz; apply lower_inner_first_frechet; try assumption; intros; apply HL; assumption. }
  assert (HC : forall P Q y, In y Y ->
    is_diff A ((fun M => lower_inner_covariance gamma F S M P Q y) : E -> R^o)
      (fun W => gamma * lower_inner_cumulant gamma F S A P Q W y)).
  { intros P Q z Hz; apply lower_inner_covariance_frechet; try assumption; intros; apply HL; assumption. }
  have H1 := gibbs_average_frechet (- beta)
    (fun y M => lower_inner_value gamma F S M y)
    (fun y W => lower_inner_first gamma F S A W y)
    (fun y M => lower_inner_covariance gamma F S M U V y)
    (fun y W => gamma * lower_inner_cumulant gamma F S A U V W y)
    Y A HY HF (HC U V).
  have H2 := gibbs_covariance_frechet (- beta)
    (fun y M => lower_inner_value gamma F S M y)
    (fun y W => lower_inner_first gamma F S A W y)
    (fun y M => lower_inner_first gamma F S M U y)
    (fun y W => gamma * lower_inner_covariance gamma F S A U W y)
    (fun y M => lower_inner_first gamma F S M V y)
    (fun y W => gamma * lower_inner_covariance gamma F S A V W y)
    Y A HY HF (HD U) (HD V).
  (* Coquelicot's filterdiff_scal_r_fct becomes the product rule with a
     constant left factor. *)
  have P1 := matrix_second_mult_frechet (fun _ : E => gamma) _ A (fun _ : E => 0) _
    (is_diff_cst (gamma : R^o) A) H1.
  have P2 := matrix_second_mult_frechet (fun _ : E => beta) _ A (fun _ : E => 0) _
    (is_diff_cst (beta : R^o) A) H2.
  have HM := is_diffB P1 P2.
  unfold lower_second at 1.
  apply: (is_diff_eq HM).
  apply: funext => W.
  change (0 * gibbs_average (- beta) (lower_inner_value gamma F S A) Y
        (lower_inner_covariance gamma F S A U V) +
      gamma * (gibbs_average (- beta) (lower_inner_value gamma F S A) Y
        (fun y => gamma * lower_inner_cumulant gamma F S A U V W y) +
      (- beta) * gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
        (lower_inner_covariance gamma F S A U V) (lower_inner_first gamma F S A W)) -
    (0 * gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
        (lower_inner_first gamma F S A U) (lower_inner_first gamma F S A V) +
      beta * (gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
        (fun y => gamma * lower_inner_covariance gamma F S A U W y)
        (lower_inner_first gamma F S A V) +
      gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
        (lower_inner_first gamma F S A U)
        (fun y => gamma * lower_inner_covariance gamma F S A V W y) +
      (- beta) * gibbs_cumulant3 (- beta) (lower_inner_value gamma F S A) Y
        (lower_inner_first gamma F S A U) (lower_inner_first gamma F S A V)
        (lower_inner_first gamma F S A W))) =
    lower_third beta gamma F Y S A U V W).
  unfold lower_third.
  rewrite gibbs_average_scale gibbs_covariance_scale_left gibbs_covariance_scale_right.
  rewrite (gibbs_covariance_sym (- beta)
    (lower_inner_value gamma F S A) Y
    (lower_inner_first gamma F S A U)
    (lower_inner_covariance gamma F S A V W)).
  ring.
Qed.

Theorem lower_second_symmetric {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U V : E) :
  lower_second beta gamma F Y S A U V = lower_second beta gamma F Y S A V U.
Proof.
  assert (HC : lower_inner_covariance gamma F S A U V = lower_inner_covariance gamma F S A V U).
  { apply FunctionalExtensionality.functional_extensionality; intros z.
    unfold lower_inner_covariance; apply gibbs_covariance_sym. }
  unfold lower_second; rewrite HC (gibbs_covariance_sym (- beta)
    (lower_inner_value gamma F S A) Y (lower_inner_first gamma F S A U)
    (lower_inner_first gamma F S A V)); reflexivity.
Qed.

Theorem lower_third_swap_left {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U V W : E) :
  lower_third beta gamma F Y S A U V W =
  lower_third beta gamma F Y S A V U W.
Proof.
  assert (HC : (lower_inner_covariance gamma F S A U V) =
    (lower_inner_covariance gamma F S A V U)).
  { apply FunctionalExtensionality.functional_extensionality; intros y.
    unfold lower_inner_covariance; apply gibbs_covariance_sym. }
  assert (HT : (lower_inner_cumulant gamma F S A U V W) =
    (lower_inner_cumulant gamma F S A V U W)).
  { apply FunctionalExtensionality.functional_extensionality; intros y.
    unfold lower_inner_cumulant; apply gibbs_cumulant3_swap_left. }
  unfold lower_third; rewrite HC HT.
  rewrite (gibbs_cumulant3_swap_left (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_first gamma F S A U)
    (lower_inner_first gamma F S A V)
    (lower_inner_first gamma F S A W)); ring.
Qed.

Theorem lower_third_swap_right {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U V W : E) :
  lower_third beta gamma F Y S A U V W =
  lower_third beta gamma F Y S A U W V.
Proof.
  assert (HC : (lower_inner_covariance gamma F S A V W) =
    (lower_inner_covariance gamma F S A W V)).
  { apply FunctionalExtensionality.functional_extensionality; intros y.
    unfold lower_inner_covariance; apply gibbs_covariance_sym. }
  assert (HT : (lower_inner_cumulant gamma F S A U V W) =
    (lower_inner_cumulant gamma F S A U W V)).
  { apply FunctionalExtensionality.functional_extensionality; intros y.
    unfold lower_inner_cumulant; apply gibbs_cumulant3_swap_right. }
  unfold lower_third; rewrite HC HT.
  rewrite (gibbs_cumulant3_swap_right (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_first gamma F S A U)
    (lower_inner_first gamma F S A V)
    (lower_inner_first gamma F S A W)); ring.
Qed.
