From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixAssembly
  LowerDefinitions LowerFrechet LowerNormBounds CoefficientMaps BlockBasis BlockOperatorDefinitions
  OperatorDefinitions GoeDefinitions JointDefinitions TimeDefinitions MatrixThird JointTimeCalculus
  RowArrayDefinitions RowObservableDefinitions RowTimeDefinitions.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/RowTimeCalculus.v from Coquelicot to MathComp-Analysis.

   The original imported the bundle InterpolationProofs for its inner module
   JointTimeCalculus. The port imports the standalone ported module
   JointTimeCalculus instead, and MatrixThird for matrix_third_is_diff_linear
   (see below). The other imports are those of the original.

   Every theorem keeps its name and its arguments, in the same order. The
   statements change form in two ways, without a change of meaning.

   1. Derivatives of a function of a real variable. Coquelicot's
      is_derive g t l becomes MathComp's @is_derive R R^o V t 1 g l, as in the
      port of JointTimeCalculus: g is derivable at t in the direction 1 and
      its derivative there is l. For gaussian_array_time_derivative the
      codomain V is tuple_NormedModule (matrix_NormedModule n) m, the space of
      block arrays of the original (block_NormedModule n m of LowerDefinitions
      by definition); for the two value derivatives it is R^o, the normed
      module view of R.

   2. Index lists. With ssreflect loaded, the bare name seq means MathComp's
      type of sequences, so gaussian_array_velocity_row_sum and
      gaussian_array_value_row_derivative write List.seq 0 (Datatypes.S m),
      Stdlib's list [0; ...; m] of the original, as LowerDefinitions does.

   The port adds one lemma, marked below: row_time_array_is_diff, the
   Frechet derivative of the array path t |-> gaussian_row_array n m t xs,
   h |-> h *: gaussian_array_velocity n m t xs, which Coquelicot's
   is_derive was by definition. Both derivative theorems are proved from it.

   What changes in the proofs. Coquelicot's tuple_build_frechet and
   filterdiff_comp' become tuple_build_frechet of the ported MatrixAssembly and
   MathComp's is_diff_comp. InterpolationProofs.JointTimeCalculus's
   joint_matrix_time_derivative is used in its Frechet form
   joint_matrix_time_is_diff of the ported JointTimeCalculus. Coquelicot's
   filterdiff_ext_lin becomes is_diff_eq, or the computation of the derivative
   through deriveE and diff_val. The linearity of lower_block_first at a point,
   which the original took from proj1 of Coquelicot's filterdiff, comes from
   matrix_third_is_diff_linear of the ported MatrixThird, in the form
   linear L /\ bound of the ported CoefficientMaps. Coquelicot's linear_plus
   and linear_scal become MathComp's linearD and linearZ for block_inject,
   which BlockBasis declares linear, and two local facts for
   lower_block_first. Stdlib's rewrite ... by, "rewrite <- ... at 1" and
   "rewrite A, B" are replaced by ssreflect rewrites with explicit arguments.

   Assumptions. The value theorems mention lower_block_phi or
   lower_block_first, whose definitions use Stdlib's logarithm Rpower.ln
   (through soft_max), so they rest on Classical_Prop.classic besides the
   seven axioms of analysis/README.md, as the port of JointTimeCalculus
   explains. No proof of this module calls classic itself. *)

(* Added by the port. The Frechet derivative of the array path at t. *)
Lemma row_time_array_is_diff n m t xs : 0 < t < 1 ->
  is_diff (t : R^o)
    ((fun u : R^o => gaussian_row_array n m u xs) :
      R^o -> tuple_NormedModule (matrix_NormedModule n) m)
    (fun h : R^o => (h *: gaussian_array_velocity n m t xs)%R).
Proof.
  intro Ht; unfold gaussian_row_array.
  have HT := @tuple_build_frechet R^o (matrix_NormedModule n) m
    (fun i (u : R^o) => gaussian_row_matrix n u i xs)
    (fun i (h : R^o) => (h *: joint_time_velocity n t (fst (gaussian_row_pair n i xs))
      (snd (gaussian_row_pair n i xs)))%R) t
    (fun i _ => joint_matrix_time_is_diff n (matrix_zero n) t _ _ Ht).
  apply: (is_diff_eq HT).
  apply: funext => h.
  apply tuple_ext; intros i Hi.
  rewrite (tuple_entry_build _ _ _ _ Hi).
  unfold gaussian_array_velocity.
  rewrite linearZ /= (tuple_entry_build _ _ _ _ Hi); reflexivity.
Qed.

Theorem gaussian_array_time_derivative n m t xs :
  0<t<1 ->
  @is_derive R R^o (tuple_NormedModule (matrix_NormedModule n) m) t 1
    (fun u : R => gaussian_row_array n m u xs) (gaussian_array_velocity n m t xs).
Proof.
  intro Ht.
  exact (@joint_time_derive_of_is_diff (tuple_NormedModule (matrix_NormedModule n) m) _ t _
    (row_time_array_is_diff n m t xs Ht)).
Qed.

Theorem gaussian_array_value_time_derivative n m beta gamma y B Y S t xs :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] -> 0<t<1 ->
  @is_derive R R^o R^o t 1 (fun u => gaussian_array_value n m beta gamma y B Y S u xs)
    (lower_block_first n m beta gamma y B Y S (gaussian_row_array n m t xs)
      (gaussian_array_velocity n m t xs)).
Proof.
  intros Hb Hg HY HS Ht; unfold gaussian_array_value.
  have HF := proj1 (lower_block_derivatives n m beta gamma y B Y S Hb Hg HY HS
    (gaussian_row_array n m t xs)).
  have HC := is_diff_comp (row_time_array_is_diff n m t xs Ht) HF.
  apply: DeriveDef.
    exact/diff_derivable/ex_diff.
  rewrite deriveE ?diff_val //= scale1r; reflexivity.
Qed.

Theorem gaussian_array_velocity_row_sum n m beta gamma y B Y S t xs :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] ->
  lower_block_first n m beta gamma y B Y S (gaussian_row_array n m t xs)
    (gaussian_array_velocity n m t xs) =
  SoftDefinitions.finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S t i xs)
    (List.seq 0 (Datatypes.S m)).
Proof.
  intros Hb Hg HY HS.
  set (A := gaussian_row_array n m t xs).
  set (L := lower_block_first n m beta gamma y B Y S A).
  have HL : linear (L : block_NormedModule n m -> R^o) /\
    exists M : R, 0 < M /\ forall x : block_NormedModule n m, (`|L x|)%R <= M * (`|x|)%R.
  { exact (matrix_third_is_diff_linear _ _ A
      (proj1 (lower_block_derivatives n m beta gamma y B Y S Hb Hg HY HS A))). }
  have HD : forall u v : block_NormedModule n m, L (u + v)%R = L u + L v.
  { intros u v; have := proj1 HL 1%R u v; rewrite !scale1r; exact. }
  have H0 : L 0%R = 0.
  { have := HD 0%R 0%R; rewrite addr0 => H; lra. }
  have HZ : forall (a : R) (u : block_NormedModule n m), L (a *: u)%R = a * L u.
  { intros a u; have H := proj1 HL a u 0%R.
    rewrite addr0 in H; rewrite H H0.
    change (Rplus (Rmult a (L u)) 0 = Rmult a (L u)); ring. }
  rewrite -(block_sum_injections n m (gaussian_array_velocity n m t xs)).
  rewrite (linear_module_coordinate_sum m _ (L : block_NormedModule n m -> R^o) HL).
  rewrite module_coordinate_sum_real lower_coordinate_sum_finite.
  apply GibbsWeights.gibbs_sum_ext; intros i Hi.
  apply in_seq in Hi.
  unfold gaussian_array_velocity, block_entry.
  rewrite (tuple_entry_build _ _ _ _ (ltac:(lia) : (i <= m)%coq_nat)).
  unfold joint_time_velocity, matrix_add, matrix_scale.
  (* Two rewrites with linearZ, not !linearZ, which would also rewrite inside
     goe_matrix, itself a scaled sum. *)
  rewrite linearD linearZ linearZ.
  rewrite HD HZ HZ.
  unfold gaussian_row_velocity; cbn zeta.
  fold (block_inject n m i (joint_quadratic_input n (fst (gaussian_row_pair n i xs)))).
  fold (block_inject n m i (goe_matrix n (snd (gaussian_row_pair n i xs)))).
  fold A L.
  change (/(2*sqrt t)*L (block_inject n m i (joint_quadratic_input n (fst (gaussian_row_pair n i xs)))) +
    (-/(2*sqrt(1-t)))*L (block_inject n m i (goe_matrix n (snd (gaussian_row_pair n i xs)))) =
    L (block_inject n m i (joint_quadratic_input n (fst (gaussian_row_pair n i xs))))/(2*sqrt t) -
    L (block_inject n m i (goe_matrix n (snd (gaussian_row_pair n i xs))))/(2*sqrt(1-t))).
  unfold Rdiv; ring.
Qed.

Theorem gaussian_array_value_row_derivative n m beta gamma y B Y S t xs :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] -> 0<t<1 ->
  @is_derive R R^o R^o t 1 (fun u => gaussian_array_value n m beta gamma y B Y S u xs)
    (SoftDefinitions.finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S t i xs)
      (List.seq 0 (Datatypes.S m))).
Proof.
  intros Hb Hg HY HS Ht.
  rewrite -(gaussian_array_velocity_row_sum n m beta gamma y B Y S t xs Hb Hg HY HS).
  apply gaussian_array_value_time_derivative; assumption.
Qed.
