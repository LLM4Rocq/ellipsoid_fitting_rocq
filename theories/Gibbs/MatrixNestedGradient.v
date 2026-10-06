From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.Weights Matrix.Definitions Matrix.EntriesAndLinearMaps Matrix.Trace
  Gibbs.MatrixDefinitions Gibbs.MatrixFrechet
  Gibbs.MatrixSecondDerivativeDefinitions Gibbs.MatrixSecondDerivative
  Tensor.GibbsDefinitions Matrix.EntrywiseDifferentials
  Gibbs.NestedGradientDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* The gradient matrix of the nested soft minimax of matrices
   (Gibbs.NestedGradientDefinitions) and its derivative.
   - trace_pair_basis: trace_pair n B (matrix_basis n j i) is the entry
     (i, j) of B, where matrix_basis n i j is the matrix unit
     (matrix_basis_entry).
   - matrix_inner_gradient_trace and matrix_nested_gradient_trace: the
     trace pairing of the inner or nested gradient with U is the directional
     derivative in the direction U (matrix_inner_derivative,
     matrix_nested_derivative). Hence the entry (i, j) of the nested
     gradient is the derivative in the direction matrix_basis n j i
     (matrix_nested_gradient_entry).
   - matrix_nested_gradient_frechet: for beta, gamma > 0 and nonempty Y
     and S, the nested gradient is differentiable at every A, with
     differential matrix_nested_gradient_derivative.
   Differentiability is MathComp's is_diff, for the Frobenius norm that
   matrix n carries in Matrix.Definitions. With ssreflect loaded, the
   statements write (i <= n)%coq_nat for Stdlib's order on nat; the
   literals, the arithmetic and Nat.eqb are Stdlib's. *)

Lemma gradient_coordinate_sum_zero n : coordinate_sum n (fun _ => 0) = 0.
Proof. induction n; simpl; lra. Qed.

Lemma gradient_coordinate_sum_select n j f :
  (j <= n)%coq_nat ->
  coordinate_sum n (fun i => f i * (if Nat.eqb i j then 1 else 0)) = f j.
Proof.
  revert j f; induction n as [|n IH]; intros [|j] f Hj; simpl.
  - ring.
  - lia.
  - assert (HZ : coordinate_sum n (fun i => f (S i) * 0) = 0).
    { transitivity (coordinate_sum n (fun _ => 0));
        [|apply gradient_coordinate_sum_zero].
      apply coordinate_sum_ext; intros; ring. }
    rewrite HZ; ring.
  - rewrite (IH j (fun i => f (S i)) ltac:(lia)); ring.
Qed.

Theorem matrix_basis_entry n i j r c :
  (r <= n)%coq_nat -> (c <= n)%coq_nat ->
  matrix_entry n (matrix_basis n i j) r c =
  (if (Nat.eqb r i && Nat.eqb c j)%bool then 1 else 0).
Proof. intros; unfold matrix_basis; apply matrix_entry_build; assumption. Qed.

Theorem trace_pair_basis n (B : matrix n) i j :
  (i <= n)%coq_nat -> (j <= n)%coq_nat ->
  trace_pair n B (matrix_basis n j i) = matrix_entry n B i j.
Proof.
  intros Hi Hj; unfold trace_pair.
  transitivity (coordinate_sum n (fun r => coordinate_sum n (fun c =>
    (matrix_entry n B r c * (if Nat.eqb r i then 1 else 0)) *
    (if Nat.eqb c j then 1 else 0)))).
  - apply coordinate_sum_ext; intros r Hr.
    apply coordinate_sum_ext; intros c Hc.
    rewrite (matrix_basis_entry n j i c r Hc Hr).
    destruct (Nat.eqb r i), (Nat.eqb c j); simpl; ring.
  - transitivity (coordinate_sum n (fun r =>
      matrix_entry n B r j * (if Nat.eqb r i then 1 else 0))).
    + apply coordinate_sum_ext; intros r Hr.
      exact (gradient_coordinate_sum_select n j
        (fun c => matrix_entry n B r c * (if Nat.eqb r i then 1 else 0)) Hj).
    + exact (gradient_coordinate_sum_select n i (fun r => matrix_entry n B r j) Hi).
Qed.

(* The map B |-> trace_pair n B U is linear: the proof packs the algebraic
   part of trace_pair_left_linear of Matrix.Trace as a {linear _ -> _} of
   MathComp, and uses linear0, linearD and linearZ. *)
Lemma gradient_weighted_sum_trace n q B I (U : matrix n) :
  trace_pair n (matrix_weighted_sum n q B I) U =
  finite_sum (fun i => q i * trace_pair n (B i) U) I.
Proof.
  pose L : {linear matrix_NormedModule n -> R^o} :=
    HB.pack (fun M : matrix n => trace_pair n M U : R^o)
      (GRing.isLinear.Build R (matrix_NormedModule n) R^o *:%R
        (fun M : matrix n => trace_pair n M U : R^o)
        (proj1 (trace_pair_left_linear n U))).
  have HL : forall M : matrix n, trace_pair n M U = L M by [].
  induction I as [|i I IH]; simpl.
  - rewrite HL; unfold matrix_zero; rewrite linear0; reflexivity.
  - rewrite HL; unfold matrix_add, matrix_scale; rewrite linearD linearZ.
    rewrite -!HL IH; reflexivity.
Qed.

Lemma gradient_gibbs_mean_trace n c f I B (U : matrix n) :
  trace_pair n (matrix_gibbs_mean n c f I B) U =
  gibbs_average c f I (fun i => trace_pair n (B i) U).
Proof. unfold matrix_gibbs_mean; rewrite gradient_weighted_sum_trace; reflexivity. Qed.

Theorem matrix_inner_gradient_trace n gamma offset coeff S (A U : matrix n) y :
  trace_pair n (matrix_inner_gradient n gamma offset coeff S A y) U =
  matrix_inner_derivative n gamma offset coeff S A U y.
Proof.
  unfold matrix_inner_gradient, matrix_inner_derivative.
  apply gradient_gibbs_mean_trace.
Qed.

Theorem matrix_nested_gradient_trace n beta gamma offset coeff Y S (A U : matrix n) :
  trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S A) U =
  matrix_nested_derivative n beta gamma offset coeff Y S A U.
Proof.
  unfold matrix_nested_gradient, matrix_nested_derivative.
  rewrite gradient_gibbs_mean_trace.
  apply gibbs_average_ext; intros y Hy; apply matrix_inner_gradient_trace.
Qed.

Theorem matrix_nested_gradient_entry n beta gamma offset coeff Y S (A : matrix n) i j :
  (i <= n)%coq_nat -> (j <= n)%coq_nat ->
  matrix_entry n (matrix_nested_gradient n beta gamma offset coeff Y S A) i j =
  matrix_nested_derivative n beta gamma offset coeff Y S A (matrix_basis n j i).
Proof.
  intros Hi Hj; rewrite -(trace_pair_basis n
    (matrix_nested_gradient n beta gamma offset coeff Y S A) i j Hi Hj).
  apply matrix_nested_gradient_trace.
Qed.

Theorem matrix_nested_gradient_frechet n beta gamma offset coeff Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  forall A : matrix n,
  is_diff A (matrix_nested_gradient n beta gamma offset coeff Y S)
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A).
Proof.
  intros Hb Hg HY HS A; unfold matrix_nested_gradient_derivative.
  (* The gradient is rebuilt from its entries
     (matrix_nested_gradient_entry). *)
  have E : matrix_nested_gradient n beta gamma offset coeff Y S =
    (fun M => matrix_build n (fun i j =>
      matrix_nested_derivative n beta gamma offset coeff Y S M
        (matrix_basis n j i))).
  { apply: funext => M; apply matrix_ext; intros i j Hi Hj.
    rewrite (matrix_entry_build n _ i j Hi Hj).
    exact (matrix_nested_gradient_entry n beta gamma offset coeff Y S M i j Hi Hj). }
  rewrite E.
  apply (matrix_build_frechet n
    (fun i j M => matrix_nested_derivative n beta gamma offset coeff Y S M
      (matrix_basis n j i))
    (fun i j V => matrix_nested_second_derivative n beta gamma offset coeff Y S A
      (matrix_basis n j i) V) A).
  intros i j Hi Hj; apply matrix_nested_derivative_frechet; assumption.
Qed.
