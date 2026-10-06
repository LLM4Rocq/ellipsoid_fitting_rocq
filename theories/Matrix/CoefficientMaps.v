From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.Trace Matrix.OperatorNorm
  Gibbs.NestedGradientDefinitions Gibbs.MatrixNestedGradient
  Gibbs.HessianDefinitions Gibbs.MatrixThirdDerivative Gibbs.NestedHessian
  Gibbs.MatrixThirdDerivativeDefinitions Matrix.ThirdOrderArrays
  Gibbs.MatrixThirdContinuity Tensor.ThirdArrayContraction.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Linear maps on tuples, matrices and arrays, given by their coefficients.
   A bounded linear map l is written as the conjunction
     linear l /\ exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
   where the norms are the Euclidean norms of all entries.
   - module_coordinate_sum_linear and matrix_build_linear: finite sums of
     bounded linear maps, and matrices of them, are bounded linear maps.
     So are the entries of Hessian and third-order arrays, and the action
     hessian_action n H V, both in H and in V.
   - matrix_basis_expansion writes a matrix in the basis matrix_basis, and
     matrix_linear_basis_reconstruction recovers a linear map on matrices
     from its values on that basis (only the algebraic part of the
     hypothesis is used).
   - actual_third_action: the action of the array
     matrix_nested_third_coefficients is the derivative of the nested
     Hessian, matrix_nested_hessian_derivative; actual_third_evaluation:
     its evaluation at U, V, W is matrix_nested_third_derivative. *)

Lemma module_coordinate_sum_ext (V : normedModType R) n (f g : nat -> V) :
  (forall i, (i <= n)%coq_nat -> f i = g i) ->
  module_coordinate_sum V n f = module_coordinate_sum V n g.
Proof.
  revert f g; induction n as [|n IH]; intros f g H; simpl.
  - apply H; lia.
  - f_equal.
    + apply H; lia.
    + apply IH; intros i Hi; apply H; lia.
Qed.

Lemma module_linear_sum {E V : normedModType R} (f g : E -> V) :
  (linear f /\
    exists M : R, 0 < M /\ forall x : E, (`|f x|)%R <= M * (`|x|)%R) ->
  (linear g /\
    exists M : R, 0 < M /\ forall x : E, (`|g x|)%R <= M * (`|x|)%R) ->
  linear (fun x => (f x + g x)%R) /\
    exists M : R, 0 < M /\ forall x : E, (`|f x + g x|)%R <= M * (`|x|)%R.
Proof.
  intros [Lf [Mf [Mf0 HMf]]] [Lg [Mg [Mg0 HMg]]]; split.
  - intros a u v; rewrite /= Lf Lg scalerDr.
    by rewrite addrACA.
  - exists (Mf + Mg); split; [lra|]; intros x.
    apply (Rle_trans _ ((`|f x|)%R + (`|g x|)%R)).
    + apply/RleP; apply ler_normD.
    + specialize (HMf x); specialize (HMg x); lra.
Qed.

Lemma module_coordinate_sum_linear {E V : normedModType R} n (F : nat -> E -> V) :
  (forall i, (i <= n)%coq_nat ->
    linear (F i) /\
    exists M : R, 0 < M /\ forall x : E, (`|F i x|)%R <= M * (`|x|)%R) ->
  linear (fun x => module_coordinate_sum V n (fun i => F i x)) /\
    exists M : R, 0 < M /\
      forall x : E,
        (`|module_coordinate_sum V n (fun i => F i x)|)%R <= M * (`|x|)%R.
Proof.
  revert F; induction n as [|n IH]; intros F HF; simpl.
  - apply HF; lia.
  - apply (module_linear_sum (F O)
      (fun x => module_coordinate_sum V n (fun i => F (S i) x))).
    + apply HF; lia.
    + apply (IH (fun i => F (S i))); intros i Hi; apply HF; lia.
Qed.

Theorem matrix_build_linear {E : normedModType R} n (F : nat -> nat -> E -> R) :
  (forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat ->
    linear (F i j : E -> R^o) /\
    exists M : R, 0 < M /\ forall x : E, (`|F i j x|)%R <= M * (`|x|)%R) ->
  linear (fun x => matrix_build n (fun i j => F i j x)) /\
    exists M : R, 0 < M /\
      forall x : E, (`|matrix_build n (fun i j => F i j x)|)%R <= M * (`|x|)%R.
Proof.
  intros HF; unfold matrix_build.
  apply (tuple_build_linear n
    (fun i x => tuple_build R^o n (fun j => F i j x))); intros i Hi.
  apply (@tuple_build_linear E R^o n (fun j x => F i j x)); intros j Hj.
  apply HF; assumption.
Qed.

Theorem hessian_entry_linear n i j :
  linear (fun H : hessian_array n => hessian_entry n H i j) /\
  exists M : R, 0 < M /\
    forall H : hessian_array n, (`|hessian_entry n H i j|)%R <= M * (`|H|)%R.
Proof.
  unfold hessian_entry.
  apply (matrix_linear_comp
    (tuple_entry (tuple_NormedModule (matrix_NormedModule n) n) n i)
    (tuple_entry (matrix_NormedModule n) n j)); apply tuple_entry_linear.
Qed.

Theorem third_entry_linear n i j :
  linear (fun T : third_array n => third_entry n T i j) /\
  exists M : R, 0 < M /\
    forall T : third_array n, (`|third_entry n T i j|)%R <= M * (`|T|)%R.
Proof.
  unfold third_entry.
  apply (matrix_linear_comp
    (tuple_entry (tuple_NormedModule (hessian_NormedModule n) n) n i)
    (tuple_entry (hessian_NormedModule n) n j)); apply tuple_entry_linear.
Qed.

Theorem hessian_action_linear_array n (V : matrix n) :
  linear (fun H : hessian_array n => hessian_action n H V) /\
  exists M : R, 0 < M /\
    forall H : hessian_array n, (`|hessian_action n H V|)%R <= M * (`|H|)%R.
Proof.
  unfold hessian_action.
  apply (matrix_build_linear n
    (fun i j (H : hessian_array n) => trace_pair n (hessian_entry n H i j) V)).
  intros i j Hi Hj.
  apply (matrix_linear_comp (fun H : hessian_array n => hessian_entry n H i j)
    (fun B : matrix n => trace_pair n B V : R^o)).
  - apply hessian_entry_linear.
  - apply trace_pair_left_linear.
Qed.

Theorem hessian_action_linear_direction n (H : hessian_array n) :
  linear (hessian_action n H) /\
  exists M : R, 0 < M /\
    forall V : matrix n, (`|hessian_action n H V|)%R <= M * (`|V|)%R.
Proof.
  unfold hessian_action.
  apply (matrix_build_linear n
    (fun i j (V : matrix n) => trace_pair n (hessian_entry n H i j) V)).
  intros i j Hi Hj.
  apply trace_pair_linear.
Qed.

Lemma linear_module_coordinate_sum {E V : normedModType R} n (f : nat -> E) (L : E -> V) :
  (linear L /\
    exists M : R, 0 < M /\ forall x : E, (`|L x|)%R <= M * (`|x|)%R) ->
  L (module_coordinate_sum E n f) = module_coordinate_sum V n (fun i => L (f i)).
Proof.
  intros [HL _].
  have HD : forall u v : E, L (u + v)%R = (L u + L v)%R.
  { intros u v; have := HL 1%R u v; rewrite !scale1r; exact. }
  revert f; induction n as [|n IH]; intros f; simpl; [reflexivity|].
  rewrite HD IH; reflexivity.
Qed.

Lemma module_coordinate_sum_real n f :
  module_coordinate_sum R^o n f = coordinate_sum n f.
Proof. revert f; induction n; intros f; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.

Theorem matrix_basis_expansion n (M : matrix n) :
  module_coordinate_sum (matrix_NormedModule n) n (fun i =>
    module_coordinate_sum (matrix_NormedModule n) n (fun j =>
      matrix_scale n (matrix_entry n M j i) (matrix_basis n j i))) = M.
Proof.
  apply matrix_ext; intros r c Hr Hc.
  change ((fun B : matrix n => matrix_entry n B r c : R^o)
    (module_coordinate_sum (matrix_NormedModule n) n (fun i =>
      module_coordinate_sum (matrix_NormedModule n) n (fun j =>
        matrix_scale n (matrix_entry n M j i) (matrix_basis n j i)))) = matrix_entry n M r c).
  etransitivity; [exact (@linear_module_coordinate_sum (matrix_NormedModule n) R^o n
    (fun i => module_coordinate_sum (matrix_NormedModule n) n (fun j =>
      matrix_scale n (matrix_entry n M j i) (matrix_basis n j i)))
    (fun B : matrix n => matrix_entry n B r c : R^o) (matrix_entry_linear n r c)) |].
  rewrite module_coordinate_sum_real.
  transitivity (coordinate_sum n (fun i => coordinate_sum n (fun j =>
    matrix_entry n M j i * (if (Nat.eqb r j && Nat.eqb c i)%bool then 1 else 0)))).
  - apply coordinate_sum_ext; intros i Hi.
    etransitivity; [exact (@linear_module_coordinate_sum (matrix_NormedModule n) R^o n
      (fun j => matrix_scale n (matrix_entry n M j i) (matrix_basis n j i))
      (fun B : matrix n => matrix_entry n B r c : R^o) (matrix_entry_linear n r c)) |].
    rewrite module_coordinate_sum_real.
    apply coordinate_sum_ext; intros j Hj.
    rewrite matrix_entry_scale (matrix_basis_entry n j i r c Hr Hc); reflexivity.
  - transitivity (coordinate_sum n (fun i =>
      matrix_entry n M r i * (if Nat.eqb i c then 1 else 0))).
    + apply coordinate_sum_ext; intros i Hi.
      transitivity (coordinate_sum n (fun j =>
        (matrix_entry n M j i * (if Nat.eqb i c then 1 else 0)) *
        (if Nat.eqb j r then 1 else 0))).
      * apply coordinate_sum_ext; intros j Hj.
        rewrite (Nat.eqb_sym r j) (Nat.eqb_sym c i).
        destruct (Nat.eqb j r), (Nat.eqb i c); simpl; ring.
      * exact (gradient_coordinate_sum_select n r
          (fun j => matrix_entry n M j i * (if Nat.eqb i c then 1 else 0)) Hr).
    + exact (gradient_coordinate_sum_select n c (matrix_entry n M r) Hc).
Qed.

Theorem matrix_linear_basis_reconstruction {V : normedModType R}
    n (L : matrix n -> V) (W : matrix n) :
  (linear L /\
    exists M : R, 0 < M /\ forall x : matrix n, (`|L x|)%R <= M * (`|x|)%R) ->
  coefficient_contract V n (fun i j => L (matrix_basis n j i)) W = L W.
Proof.
  intros HL.
  pose L' : {linear matrix_NormedModule n -> V} :=
    HB.pack L (GRing.isLinear.Build R (matrix_NormedModule n) V *:%R L (proj1 HL)).
  have HZ : forall (c : R) (x : matrix n), L (c *: x)%R = (c *: L x)%R.
  { intros c x; exact (linearZ_LR L' c x). }
  have E := matrix_basis_expansion n W.
  rewrite -{2}E.
  rewrite (linear_module_coordinate_sum n _ L HL).
  unfold coefficient_contract; apply module_coordinate_sum_ext; intros i Hi.
  rewrite (linear_module_coordinate_sum n _ L HL).
  apply module_coordinate_sum_ext; intros j Hj.
  unfold matrix_scale; rewrite HZ; reflexivity.
Qed.

Theorem actual_third_action n beta gamma offset coeff Y S (A W : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  third_action n (matrix_nested_third_coefficients n beta gamma offset coeff Y S A) W =
  matrix_nested_hessian_derivative n beta gamma offset coeff Y S A W.
Proof.
  intros Hb Hg HY HS.
  unfold third_action.
  transitivity (coefficient_contract (hessian_NormedModule n) n
    (fun i j => matrix_nested_hessian_derivative n beta gamma offset coeff Y S A (matrix_basis n j i)) W).
  - unfold coefficient_contract; apply module_coordinate_sum_ext; intros i Hi.
    apply module_coordinate_sum_ext; intros j Hj.
    unfold matrix_nested_third_coefficients, third_entry, third_build.
    rewrite (tuple_entry_build _ n i _ Hi) (tuple_entry_build _ n j _ Hj).
    reflexivity.
  - apply matrix_linear_basis_reconstruction.
    exact (matrix_third_is_diff_linear _ _ A
      (matrix_nested_hessian_frechet n beta gamma offset coeff Y S Hb Hg HY HS A)).
Qed.

Theorem actual_third_evaluation n beta gamma offset coeff Y S (A U V W : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  third_evaluation n (matrix_nested_third_coefficients n beta gamma offset coeff Y S A) U V W =
  matrix_nested_third_derivative n beta gamma offset coeff Y S A U V W.
Proof.
  intros Hb Hg HY HS; unfold third_evaluation.
  rewrite (actual_third_action n beta gamma offset coeff Y S A W Hb Hg HY HS).
  apply matrix_nested_hessian_derivative_evaluation; assumption.
Qed.
