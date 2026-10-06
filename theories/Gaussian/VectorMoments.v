From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.OperatorDefinitions
  Matrix.OperatorNormProperties Matrix.FrobeniusNorm Tensor.Definitions
  Chaos.SecondOrderDefinitions Gaussian.VectorDefinitions
  Matrix.VectorCoordinates Gaussian.VectorDomain Gaussian.VectorStein
  Gaussian.VectorLinearity Gaussian.VectorFiniteSums.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Moments of linear functions of a standard Gaussian vector x of
   vector n. A linear map f is MathComp's linear (f : vector n -> R^o) with
   a bound `|f x| <= M * `|x|, as in Matrix.EntriesAndLinearMaps. Linear maps and
   products of two of them satisfy gaussian_vector_domain
   (gaussian_vector_linear_domain, gaussian_vector_linear_product_domain).
   The coordinates are centered (gaussian_vector_coordinate_moment), the
   expectation of vector_entry n x i * f x is f (chaos_basis n i)
   (gaussian_vector_linear_coordinate_moment), and the expectation of the
   product of the linear forms of u and v is the sum of the u i * v i
   (gaussian_vector_linear_forms_covariance). *)

Lemma gaussian_vector_linear_continuous n (f : vector n -> R) :
  (linear (f : vector n -> R^o) /\
    exists M : R, 0 < M /\ forall x : vector n, (`|f x|)%R <= M * (`|x|)%R) ->
  forall x, {for x, continuous f}.
Proof.
  intros HL x.
  exact (matrix_linear_continuous (f : vector n -> R^o) HL x).
Qed.

Lemma gaussian_vector_linear_growth n (f : vector n -> R) :
  (linear (f : vector n -> R^o) /\
    exists M : R, 0 < M /\ forall x : vector n, (`|f x|)%R <= M * (`|x|)%R) ->
  exists C : R, 0 <= C /\
    forall x, Rabs (f x) <= C * (1 + (`|x|)%R)^1.
Proof.
  intros [_ [C [HC HB]]].
  exists C; split; [lra|intro x].
  specialize (HB x); rewrite -RabsE in HB.
  assert (Hx : 0 <= (`|x|)%R) by (apply/RleP; apply normr_ge0).
  simpl; nra.
Qed.

Theorem gaussian_vector_linear_domain n (f : vector n -> R) :
  (linear (f : vector n -> R^o) /\
    exists M : R, 0 < M /\ forall x : vector n, (`|f x|)%R <= M * (`|x|)%R) ->
  gaussian_vector_domain n f.
Proof.
  intro HL; destruct (gaussian_vector_linear_growth n f HL) as [C [HC HB]].
  apply (gaussian_vector_polynomial_domain n f C 1).
  - apply gaussian_vector_linear_continuous; exact HL.
  - exact HC.
  - exact HB.
Qed.

Theorem gaussian_vector_linear_product_domain n (f g : vector n -> R) :
  (linear (f : vector n -> R^o) /\
    exists M : R, 0 < M /\ forall x : vector n, (`|f x|)%R <= M * (`|x|)%R) ->
  (linear (g : vector n -> R^o) /\
    exists M : R, 0 < M /\ forall x : vector n, (`|g x|)%R <= M * (`|x|)%R) ->
  gaussian_vector_domain n (fun x => f x * g x).
Proof.
  intros Hf Hg.
  destruct (gaussian_vector_linear_growth n f Hf) as [C [HC HBf]].
  destruct (gaussian_vector_linear_growth n g Hg) as [D [HD HBg]].
  apply (gaussian_vector_polynomial_domain n _ (C*D) 2).
  - intro x.
    exact: (@continuousM R (vector_NormedModule n) f g x
      (gaussian_vector_linear_continuous n f Hf x)
      (gaussian_vector_linear_continuous n g Hg x)).
  - apply Rmult_le_pos; assumption.
  - intro x; rewrite Rabs_mult.
    replace (C*D*(1+(`|x|)%R)^2) with ((C*(1+(`|x|)%R)^1)*(D*(1+(`|x|)%R)^1)) by ring.
    apply Rmult_le_compat; try apply Rabs_pos; [apply HBf|apply HBg].
Qed.

Theorem gaussian_vector_coordinate_moment n i :
  (i <= n)%coq_nat ->
  gaussian_vector_domain n (fun x => vector_entry n x i) /\
  gaussian_vector_expectation n (fun x => vector_entry n x i) = 0.
Proof.
  intro Hi; split.
  - apply gaussian_vector_linear_domain; unfold vector_entry; apply tuple_entry_linear.
  - assert (HD : forall x : vector n,
      is_diff x ((fun _ : vector n => (1:R)) : vector n -> R^o) (fun _ : vector n => (0:R))).
    { intro x; exact (is_diff_cst (1 : R^o) x). }
    pose proof (gaussian_vector_first_stein n i (fun _ => 1) (fun _ _ => 0)
      1 0 0 0 Hi HD ltac:(intro x; apply: cst_continuous)
      ltac:(lra) ltac:(lra) ltac:(intro x; cbn; rewrite ?Rabs_R1; lra)
      ltac:(intro x; cbn; rewrite ?Rabs_R0; lra)) as [_ HE].
    rewrite (proj2 (gaussian_vector_constant n 0)) in HE.
    transitivity (gaussian_vector_expectation n (fun x => vector_entry n x i * 1)).
    + apply gaussian_vector_expectation_ext; intro x; ring.
    + symmetry; exact HE.
Qed.

Theorem gaussian_vector_linear_coordinate_moment n i (f : vector n -> R) :
  (i <= n)%coq_nat ->
  (linear (f : vector n -> R^o) /\
    exists M : R, 0 < M /\ forall x : vector n, (`|f x|)%R <= M * (`|x|)%R) ->
  gaussian_vector_domain n (fun x => vector_entry n x i * f x) /\
  gaussian_vector_expectation n (fun x => vector_entry n x i * f x) = f (chaos_basis n i).
Proof.
  intros Hi HL; split.
  - apply gaussian_vector_linear_product_domain;
      [unfold vector_entry; apply tuple_entry_linear|exact HL].
  - destruct (gaussian_vector_linear_growth n f HL) as [C [HC HB]].
    pose proof (gaussian_vector_first_stein n i f (fun _ => f)
      C 1 (Rabs (f (chaos_basis n i))) 0 Hi
      ltac:(intro x; exact (matrix_linear_is_diff (f : vector n -> R^o) x HL))
      ltac:(intro x; apply: cst_continuous) HC (Rabs_pos _) HB
      ltac:(intro x; simpl; lra)) as [_ HE].
    rewrite (proj2 (gaussian_vector_constant n (f (chaos_basis n i)))) in HE.
    symmetry; exact HE.
Qed.

Lemma gaussian_vector_linear_form_is_linear n (u : nat -> R) :
  linear ((fun x : vector n => coordinate_sum n (fun i => u i * vector_entry n x i))
      : vector n -> R^o) /\
    exists M : R, 0 < M /\ forall x : vector n,
      (`|coordinate_sum n (fun i => u i * vector_entry n x i)|)%R <= M * (`|x|)%R.
Proof.
  apply coordinate_sum_linear; intros i Hi.
  apply matrix_linear_scale; unfold vector_entry; apply tuple_entry_linear.
Qed.

Lemma gaussian_vector_linear_form_basis n (u : nat -> R) i :
  (i <= n)%coq_nat ->
  coordinate_sum n (fun j => u j * vector_entry n (chaos_basis n i) j) = u i.
Proof.
  intro Hi; transitivity (coordinate_sum n (fun j => u j * (if Nat.eqb j i then 1 else 0))).
  - apply coordinate_sum_ext; intros j Hj.
    rewrite (vector_coordinate_basis_entry n i j Hj); reflexivity.
  - apply operator_coordinate_sum_select; exact Hi.
Qed.

Theorem gaussian_vector_linear_form_moment n (u : nat -> R) :
  gaussian_vector_domain n (fun x => coordinate_sum n (fun i => u i * vector_entry n x i)) /\
  gaussian_vector_expectation n (fun x => coordinate_sum n (fun i => u i * vector_entry n x i)) = 0.
Proof.
  split.
  - apply gaussian_vector_linear_domain; apply gaussian_vector_linear_form_is_linear.
  - rewrite (proj2 (gaussian_vector_coordinate_sum n n
      (fun i x => u i * vector_entry n x i) ltac:(intros i Hi;
        exact (proj1 (gaussian_vector_scale n (fun x => vector_entry n x i) (u i)
          (proj1 (proj1 (gaussian_vector_coordinate_moment n i Hi)))))))).
    transitivity (coordinate_sum n (fun _ => 0)); [|apply operator_coordinate_sum_zero].
    apply coordinate_sum_ext; intros i Hi.
    rewrite (proj2 (gaussian_vector_scale n (fun x => vector_entry n x i) (u i)
      (proj1 (proj1 (gaussian_vector_coordinate_moment n i Hi))))).
    rewrite (proj2 (gaussian_vector_coordinate_moment n i Hi)); ring.
Qed.

Theorem gaussian_vector_linear_forms_covariance n (u v : nat -> R) :
  List.Forall (gaussian_vector_domain n)
    [(fun x => coordinate_sum n (fun i => u i * vector_entry n x i));
     (fun x => coordinate_sum n (fun i => v i * vector_entry n x i));
     (fun x => coordinate_sum n (fun i => u i * vector_entry n x i) *
       coordinate_sum n (fun i => v i * vector_entry n x i))] /\
  gaussian_vector_expectation n (fun x =>
    coordinate_sum n (fun i => u i * vector_entry n x i) *
    coordinate_sum n (fun i => v i * vector_entry n x i)) =
  coordinate_sum n (fun i => u i * v i).
Proof.
  pose (f := fun x : vector n => coordinate_sum n (fun j => v j * vector_entry n x j)).
  assert (HL : linear (f : vector n -> R^o) /\
    exists M : R, 0 < M /\ forall x : vector n, (`|f x|)%R <= M * (`|x|)%R)
    by (unfold f; apply gaussian_vector_linear_form_is_linear).
  assert (HM : forall i, (i <= n)%coq_nat ->
    gaussian_vector_domain n (fun x => vector_entry n x i * f x) /\
    gaussian_vector_expectation n (fun x => vector_entry n x i * f x) = v i).
  { intros i Hi; destruct (gaussian_vector_linear_coordinate_moment n i f Hi HL) as [HD HE].
    split; [exact HD|rewrite HE; unfold f; apply gaussian_vector_linear_form_basis; exact Hi]. }
  split.
  - constructor; [apply gaussian_vector_linear_domain; apply gaussian_vector_linear_form_is_linear|].
    constructor; [apply gaussian_vector_linear_domain; apply gaussian_vector_linear_form_is_linear|].
    constructor; [apply gaussian_vector_linear_product_domain;
      apply gaussian_vector_linear_form_is_linear|constructor].
  - transitivity (gaussian_vector_expectation n (fun x => coordinate_sum n
      (fun i => u i * (vector_entry n x i * f x)))).
    + apply gaussian_vector_expectation_ext; intro x; unfold f.
      transitivity (coordinate_sum n (fun i =>
        coordinate_sum n (fun j => v j * vector_entry n x j) * (u i * vector_entry n x i))).
      * rewrite normeq_coordinate_sum_scale; ring.
      * apply coordinate_sum_ext; intros; ring.
    + rewrite (proj2 (gaussian_vector_coordinate_sum n n
        (fun i x => u i * (vector_entry n x i * f x)) ltac:(intros i Hi;
          exact (proj1 (gaussian_vector_scale n (fun x => vector_entry n x i * f x) (u i)
            (proj1 (proj1 (HM i Hi)))))))).
      apply coordinate_sum_ext; intros i Hi.
      rewrite (proj2 (gaussian_vector_scale n (fun x => vector_entry n x i * f x) (u i)
        (proj1 (proj1 (HM i Hi))))).
      rewrite (proj2 (HM i Hi)); reflexivity.
Qed.
