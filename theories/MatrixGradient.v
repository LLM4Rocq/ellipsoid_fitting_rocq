From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights
  MatrixDefinitions MatrixCoordinates MatrixTrace MatrixGibbsDefinitions MatrixGibbs
  MatrixSecondDefinitions MatrixSecond TensorGibbsDefinitions
  MatrixAssembly GradientDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/MatrixGradient.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements change form in three ways, the same ways as in the
   ports of MatrixCoordinates, MatrixGibbs and MatrixSecond, which this
   module imports.

   1. Order on indices. With ssreflect loaded, (i <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      statements write (i <= n)%coq_nat, which is ssrnat's notation for
      Stdlib's le. The meaning is unchanged.

   2. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis: f is differentiable at A and its
      differential 'd f A is l. Both say that l is linear and continuous and
      that f (A + H) = f A + l H + o(H) as H tends to 0, for the Frobenius
      norm that matrix n carries in MatrixDefinitions, as in Coquelicot.

   3. Real-valued maps. A map into R given to is_diff is written with
      codomain R^o, the normed module view of R, as in
      (fun M => soft_minimax ... : matrix n -> R^o). R^o is R by definition,
      so the map is the same.

   The literals 0 and 1, the products and sums, Nat.eqb and the test && are
   Stdlib's, as in the original. The definitions used here, matrix_basis,
   matrix_inner_gradient, matrix_nested_gradient and
   matrix_nested_gradient_derivative of GradientDefinitions, are unchanged.
   No lemma is added. *)

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

(* The original uses the fields linear_zero, linear_plus and linear_scal of
   Coquelicot's is_linear for the map B |-> trace_pair n B U. Here the
   algebraic part of trace_pair_left_linear of MatrixTrace is packed as a
   {linear _ -> _} of MathComp inside the proof, and linear0, linearD and
   linearZ play the same roles. *)
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
  (* The gradient is rebuilt from its entries, as filterdiff_ext with
     matrix_rebuild and matrix_nested_gradient_entry did in the original. *)
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

Theorem matrix_soft_minimax_gradient_frechet n beta gamma offset coeff Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  forall A : matrix n,
  is_diff A
    ((fun M => soft_minimax beta gamma (matrix_affine_scores n offset coeff M) Y S)
      : matrix n -> R^o)
    (trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S A)) /\
  is_diff A (matrix_nested_gradient n beta gamma offset coeff Y S)
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A).
Proof.
  intros Hb Hg HY HS A; split.
  - apply: (is_diff_eq
      (matrix_nested_soft_minimax_frechet n beta gamma offset coeff Y S A
        Hb Hg HY HS)).
    apply: funext => U; symmetry; apply matrix_nested_gradient_trace.
  - apply matrix_nested_gradient_frechet; assumption.
Qed.
