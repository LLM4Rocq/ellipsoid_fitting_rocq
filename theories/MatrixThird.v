From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive realfun.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights GibbsDerivatives
  ThirdDefinitions Cumulants MatrixDefinitions MatrixCoordinates MatrixTrace
  MatrixGibbsDefinitions MatrixGibbs MatrixSecondDefinitions MatrixSecond MatrixThirdDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/MatrixThird.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements change form in four ways, the same ways as in the
   ports of MatrixCoordinates, MatrixTrace, MatrixGibbs and MatrixSecond.

   1. Normed spaces. Coquelicot's NormedModule R_AbsRing becomes
      normedModType R, a real normed space of MathComp-Analysis. On
      matrix n the norm is the Frobenius norm of MatrixDefinitions, as in
      Coquelicot.

   2. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis: f is differentiable at A and its
      differential 'd f A is l. Both say that l is linear and continuous and
      that f (A + H) = f A + l H + o(H) as H tends to 0. Coquelicot's
      is_linear contains the continuity of l as a norm bound; in
      MathComp-Analysis it comes with differentiable. So the hypotheses and
      conclusions say the same thing as in the original.

   3. Real-valued maps. A map into R is written with codomain R^o, the
      normed module view of R, because is_diff and linear need a normed
      module on the codomain, as in (F i : E -> R^o). R^o is R by
      definition, so F, DF, U, DU, V and DV keep the type nat -> E -> R of
      the original, and the maps are the same.

   4. Linear maps. Coquelicot's is_linear l, in the conclusion of
      matrix_nested_third_linear_last, is a record with three fields:
      l (plus x y) = plus (l x) (l y), l (scal k x) = scal k (l x), and
      exists M, 0 < M /\ forall x, norm (l x) <= M * norm x.
      As in MatrixCoordinates and MatrixTrace, the port states it as
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R,
      MathComp's algebraic linearity together with Coquelicot's norm bound.
      The norms are the Frobenius norm on matrices and the absolute value on
      R, as in Coquelicot, so the bound means the same, constants included.

   The arithmetic in the statements is Stdlib's, as in the original, and so
   is exp inside partition, gibbs_weight and gibbs_average. This file does
   not import MathComp's exp module, so an unqualified ln would be Stdlib's;
   none occurs. matrix_covariance_differential_identity and the four swap
   theorems keep their statements word for word.

   The port adds one lemma, matrix_third_is_diff_linear, marked below. It
   takes the place of the step proj1 of Coquelicot's filterdiff, which
   extracts is_linear l from filterdiff f F l, in the proof of
   matrix_nested_third_linear_last. *)

Lemma matrix_covariance_differential_identity c f I u v w du dv :
  I <> [] ->
  gibbs_average c f I (fun i => du i * v i + u i * dv i) +
    c * gibbs_covariance c f I (fun i => u i * v i) w -
    ((gibbs_average c f I du + c * gibbs_covariance c f I u w) * gibbs_average c f I v +
      gibbs_average c f I u * (gibbs_average c f I dv + c * gibbs_covariance c f I v w)) =
  gibbs_covariance c f I du v + gibbs_covariance c f I u dv + c * gibbs_cumulant3 c f I u v w.
Proof.
  intros HI; rewrite <- gibbs_cumulant3_covariance by exact HI.
  rewrite gibbs_average_add; unfold gibbs_covariance; ring.
Qed.

(* A covariance is differentiated with changing scores and both changing
   observables.  The third argument of the cumulant is the score derivative. *)
Theorem gibbs_covariance_frechet {E : normedModType R}
    c (F DF U DU V DV : nat -> E -> R) I (A : E) :
  I <> [] ->
  (forall i, In i I -> is_diff A (F i : E -> R^o) (DF i)) ->
  (forall i, In i I -> is_diff A (U i : E -> R^o) (DU i)) ->
  (forall i, In i I -> is_diff A (V i : E -> R^o) (DV i)) ->
  is_diff A
    ((fun M => gibbs_covariance c (fun i => F i M) I (fun i => U i M) (fun i => V i M))
      : E -> R^o)
    (fun H =>
      gibbs_covariance c (fun i => F i A) I (fun i => DU i H) (fun i => V i A) +
      gibbs_covariance c (fun i => F i A) I (fun i => U i A) (fun i => DV i H) +
      c * gibbs_cumulant3 c (fun i => F i A) I (fun i => U i A) (fun i => V i A)
        (fun i => DF i H)).
Proof.
  intros HI HF HU HV.
  (* The average of the products U i * V i. *)
  have H1 := gibbs_average_frechet c F DF (fun i M => U i M * V i M)
    (fun i H => DU i H * V i A + U i A * DV i H) I A HI HF
    (fun i Hi => matrix_second_mult_frechet (U i) (V i) A (DU i) (DV i)
      (HU i Hi) (HV i Hi)).
  (* The product of the averages of U and of V. *)
  have H2 := matrix_second_mult_frechet
    (fun M => gibbs_average c (fun i => F i M) I (fun i => U i M))
    (fun M => gibbs_average c (fun i => F i M) I (fun i => V i M)) A _ _
    (gibbs_average_frechet c F DF U DU I A HI HF HU)
    (gibbs_average_frechet c F DF V DV I A HI HF HV).
  have HD := is_diffB H1 H2.
  unfold gibbs_covariance at 1.
  apply: (is_diff_eq HD).
  apply: funext => H.
  change (gibbs_average c (fun i => F i A) I (fun i => DU i H * V i A + U i A * DV i H) +
      c * gibbs_covariance c (fun i => F i A) I (fun i => U i A * V i A) (fun i => DF i H) -
    ((gibbs_average c (fun i => F i A) I (fun i => DU i H) +
        c * gibbs_covariance c (fun i => F i A) I (fun i => U i A) (fun i => DF i H)) *
      gibbs_average c (fun i => F i A) I (fun i => V i A) +
     gibbs_average c (fun i => F i A) I (fun i => U i A) *
      (gibbs_average c (fun i => F i A) I (fun i => DV i H) +
        c * gibbs_covariance c (fun i => F i A) I (fun i => V i A) (fun i => DF i H))) =
    gibbs_covariance c (fun i => F i A) I (fun i => DU i H) (fun i => V i A) +
    gibbs_covariance c (fun i => F i A) I (fun i => U i A) (fun i => DV i H) +
    c * gibbs_cumulant3 c (fun i => F i A) I (fun i => U i A) (fun i => V i A)
      (fun i => DF i H)).
  apply matrix_covariance_differential_identity; exact HI.
Qed.

Theorem matrix_inner_covariance_frechet n gamma offset coeff S (A U V : matrix n) y :
  S <> [] ->
  is_diff A
    ((fun M => matrix_inner_covariance n gamma offset coeff S M U V y)
      : matrix n -> R^o)
    (fun W => gamma * matrix_inner_cumulant n gamma offset coeff S A U V W y).
Proof.
  intros HS.
  pose proof (gibbs_covariance_frechet gamma
    (fun s M => matrix_affine_scores n offset coeff M y s)
    (fun s W => trace_pair n (coeff y s) W)
    (fun s (_ : matrix n) => trace_pair n (coeff y s) U)
    (fun (_ : nat) (_ : matrix n) => 0)
    (fun s (_ : matrix n) => trace_pair n (coeff y s) V)
    (fun (_ : nat) (_ : matrix n) => 0) S A HS) as HD.
  assert (HF : forall s, In s S ->
    is_diff A
      ((fun M => matrix_affine_scores n offset coeff M y s) : matrix n -> R^o)
      (fun W => trace_pair n (coeff y s) W)).
  { intros; apply matrix_affine_score_frechet. }
  assert (HU : forall s, In s S ->
    is_diff A ((fun _ : matrix n => trace_pair n (coeff y s) U) : matrix n -> R^o)
      (fun _ : matrix n => 0)).
  { intros s Hs; exact (is_diff_cst (trace_pair n (coeff y s) U : R^o) A). }
  assert (HV : forall s, In s S ->
    is_diff A ((fun _ : matrix n => trace_pair n (coeff y s) V) : matrix n -> R^o)
      (fun _ : matrix n => 0)).
  { intros s Hs; exact (is_diff_cst (trace_pair n (coeff y s) V : R^o) A). }
  specialize (HD HF HU HV).
  unfold matrix_inner_covariance, matrix_inner_cumulant.
  apply: (is_diff_eq HD).
  apply: funext => W.
  change (gibbs_covariance gamma (matrix_affine_scores n offset coeff A y) S
      (fun _ => 0) (fun s => trace_pair n (coeff y s) V) +
    gibbs_covariance gamma (matrix_affine_scores n offset coeff A y) S
      (fun s => trace_pair n (coeff y s) U) (fun _ => 0) +
    gamma * gibbs_cumulant3 gamma (matrix_affine_scores n offset coeff A y) S
      (fun s => trace_pair n (coeff y s) U) (fun s => trace_pair n (coeff y s) V)
      (fun s => trace_pair n (coeff y s) W) =
    gamma * gibbs_cumulant3 gamma (matrix_affine_scores n offset coeff A y) S
      (fun s => trace_pair n (coeff y s) U) (fun s => trace_pair n (coeff y s) V)
      (fun s => trace_pair n (coeff y s) W)).
  rewrite gibbs_covariance_zero_left gibbs_covariance_zero_right; ring.
Qed.

Theorem matrix_inner_cumulant_swap_left n gamma offset coeff S (A U V W : matrix n) y :
  matrix_inner_cumulant n gamma offset coeff S A U V W y =
  matrix_inner_cumulant n gamma offset coeff S A V U W y.
Proof. unfold matrix_inner_cumulant; apply gibbs_cumulant3_swap_left. Qed.

Theorem matrix_inner_cumulant_swap_right n gamma offset coeff S (A U V W : matrix n) y :
  matrix_inner_cumulant n gamma offset coeff S A U V W y =
  matrix_inner_cumulant n gamma offset coeff S A U W V y.
Proof. unfold matrix_inner_cumulant; apply gibbs_cumulant3_swap_right. Qed.

(* The three covariance placements retain the three independent directions. *)
Theorem matrix_nested_second_evaluation_frechet n beta gamma offset coeff Y S
    (A U V : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  is_diff A
    ((fun M => matrix_nested_second_derivative n beta gamma offset coeff Y S M U V)
      : matrix n -> R^o)
    (matrix_nested_third_derivative n beta gamma offset coeff Y S A U V).
Proof.
  intros Hb Hg HY HS.
  assert (HF : forall y, In y Y ->
    is_diff A
      ((fun M => matrix_inner_values n gamma offset coeff S M y) : matrix n -> R^o)
      (fun W => matrix_inner_derivative n gamma offset coeff S A W y)).
  { intros; apply matrix_inner_frechet; assumption. }
  assert (HD : forall P y, In y Y ->
    is_diff A
      ((fun M => matrix_inner_derivative n gamma offset coeff S M P y)
        : matrix n -> R^o)
      (fun W => gamma * matrix_inner_covariance n gamma offset coeff S A P W y)).
  { intros; apply matrix_inner_derivative_frechet; exact HS. }
  assert (HC : forall P Q y, In y Y ->
    is_diff A
      ((fun M => matrix_inner_covariance n gamma offset coeff S M P Q y)
        : matrix n -> R^o)
      (fun W => gamma * matrix_inner_cumulant n gamma offset coeff S A P Q W y)).
  { intros; apply matrix_inner_covariance_frechet; exact HS. }
  (* The first term, gamma times a Gibbs average of inner covariances. *)
  have H1 := is_diffZ gamma (gibbs_average_frechet (- beta)
    (fun y M => matrix_inner_values n gamma offset coeff S M y)
    (fun y W => matrix_inner_derivative n gamma offset coeff S A W y)
    (fun y M => matrix_inner_covariance n gamma offset coeff S M U V y)
    (fun y W => gamma * matrix_inner_cumulant n gamma offset coeff S A U V W y)
    Y A HY HF (HC U V)).
  (* The second term, beta times a Gibbs covariance of inner derivatives. *)
  have H2 := is_diffZ beta (gibbs_covariance_frechet (- beta)
    (fun y M => matrix_inner_values n gamma offset coeff S M y)
    (fun y W => matrix_inner_derivative n gamma offset coeff S A W y)
    (fun y M => matrix_inner_derivative n gamma offset coeff S M U y)
    (fun y W => gamma * matrix_inner_covariance n gamma offset coeff S A U W y)
    (fun y M => matrix_inner_derivative n gamma offset coeff S M V y)
    (fun y W => gamma * matrix_inner_covariance n gamma offset coeff S A V W y)
    Y A HY HF (HD U) (HD V)).
  have H12 := is_diffB H1 H2.
  unfold matrix_nested_second_derivative at 1.
  apply: (is_diff_eq H12).
  apply: funext => W.
  change (gamma * (gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y
        (fun y => gamma * matrix_inner_cumulant n gamma offset coeff S A U V W y) +
      - beta * gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
        (matrix_inner_covariance n gamma offset coeff S A U V)
        (matrix_inner_derivative n gamma offset coeff S A W)) -
    beta * (gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
        (fun y => gamma * matrix_inner_covariance n gamma offset coeff S A U W y)
        (matrix_inner_derivative n gamma offset coeff S A V) +
      gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
        (matrix_inner_derivative n gamma offset coeff S A U)
        (fun y => gamma * matrix_inner_covariance n gamma offset coeff S A V W y) +
      - beta * gibbs_cumulant3 (- beta) (matrix_inner_values n gamma offset coeff S A) Y
        (matrix_inner_derivative n gamma offset coeff S A U)
        (matrix_inner_derivative n gamma offset coeff S A V)
        (matrix_inner_derivative n gamma offset coeff S A W)) =
    matrix_nested_third_derivative n beta gamma offset coeff Y S A U V W).
  unfold matrix_nested_third_derivative.
  rewrite gibbs_average_scale gibbs_covariance_scale_left gibbs_covariance_scale_right.
  rewrite (gibbs_covariance_sym (- beta)
    (fun y => matrix_inner_values n gamma offset coeff S A y) Y
    (fun y => matrix_inner_derivative n gamma offset coeff S A U y)
    (matrix_inner_covariance n gamma offset coeff S A V W)).
  assert (HE : forall t c1 c2 c3 k : R,
    gamma * (gamma * t + (- beta) * c1) -
    beta * (gamma * c2 + gamma * c3 + (- beta) * k) =
    gamma ^ 2 * t - beta * gamma * (c1 + c2 + c3) + beta ^ 2 * k).
  { intros; ring. }
  apply HE.
Qed.

Theorem matrix_nested_third_swap_left n beta gamma offset coeff Y S (A U V W : matrix n) :
  matrix_nested_third_derivative n beta gamma offset coeff Y S A U V W =
  matrix_nested_third_derivative n beta gamma offset coeff Y S A V U W.
Proof.
  assert (HC : (fun y => matrix_inner_covariance n gamma offset coeff S A U V y) =
    (fun y => matrix_inner_covariance n gamma offset coeff S A V U y)).
  { apply FunctionalExtensionality.functional_extensionality; intros y.
    apply matrix_inner_covariance_symmetric. }
  assert (HT : (fun y => matrix_inner_cumulant n gamma offset coeff S A U V W y) =
    (fun y => matrix_inner_cumulant n gamma offset coeff S A V U W y)).
  { apply FunctionalExtensionality.functional_extensionality; intros y.
    apply matrix_inner_cumulant_swap_left. }
  unfold matrix_nested_third_derivative; rewrite HC HT.
  rewrite (gibbs_cumulant3_swap_left (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_derivative n gamma offset coeff S A U)
    (matrix_inner_derivative n gamma offset coeff S A V)
    (matrix_inner_derivative n gamma offset coeff S A W)); ring.
Qed.

Theorem matrix_nested_third_swap_right n beta gamma offset coeff Y S (A U V W : matrix n) :
  matrix_nested_third_derivative n beta gamma offset coeff Y S A U V W =
  matrix_nested_third_derivative n beta gamma offset coeff Y S A U W V.
Proof.
  assert (HC : (fun y => matrix_inner_covariance n gamma offset coeff S A V W y) =
    (fun y => matrix_inner_covariance n gamma offset coeff S A W V y)).
  { apply FunctionalExtensionality.functional_extensionality; intros y.
    apply matrix_inner_covariance_symmetric. }
  assert (HT : (fun y => matrix_inner_cumulant n gamma offset coeff S A U V W y) =
    (fun y => matrix_inner_cumulant n gamma offset coeff S A U W V y)).
  { apply FunctionalExtensionality.functional_extensionality; intros y.
    apply matrix_inner_cumulant_swap_right. }
  unfold matrix_nested_third_derivative; rewrite HC HT.
  rewrite (gibbs_cumulant3_swap_right (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_derivative n gamma offset coeff S A U)
    (matrix_inner_derivative n gamma offset coeff S A V)
    (matrix_inner_derivative n gamma offset coeff S A W)); ring.
Qed.

(* Added by the port, in place of proj1 of Coquelicot's filterdiff: the
   derivative l in is_diff A f l is linear, and it is bounded, in the form
   of Coquelicot's is_linear. The differential 'd f A is a linear map of
   MathComp, and it is continuous because f is differentiable at A; a
   continuous linear map between normed spaces is bounded. *)
Lemma matrix_third_is_diff_linear {U W : normedModType R} (f l : U -> W) (A : U) :
  is_diff A f l ->
  linear l /\
  exists M : R, 0 < M /\ forall x : U, (`|l x|)%R <= M * (`|x|)%R.
Proof.
  move=> Hd.
  have [Hdiff Hval] := Hd.
  have Hc : continuous ('d f A) := diff_continuous Hdiff.
  have Hb : bounded_near ('d f A) (nbhs (0%R : U)).
  { by apply/linear_bounded_continuous. }
  move/linear_boundedP: Hb => Hb.
  have [M M0 HM] := pinfty_ex_gt0 Hb.
  split.
  - rewrite -Hval; exact: linearP.
  - exists M; split; first by apply/RltP.
    move=> x; rewrite -Hval; apply/RleP; exact: HM.
Qed.
