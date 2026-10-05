From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace OperatorDefinitions
  SoftDefinitions MatrixGibbsDefinitions MatrixGibbs GradientDefinitions MatrixGradient
  SymmetricBasis QuadraticDefinitions GoeDefinitions JointDefinitions TimeDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module JointTimeCalculus of theories/InterpolationProofs.v,
   extracted to build/agent2/unbundled/JointTimeCalculus.v, from Coquelicot
   to MathComp-Analysis, as a standalone module.

   Every lemma and theorem of the original keeps its name and its arguments,
   in the same order. joint_matrix_normalized_path and
   joint_time_velocity_trace keep their text. The other four statements
   change form in one way, without a change of meaning.

   1. Derivatives of a function of a real variable. Coquelicot's
      is_derive g t l, for g : R -> V, becomes MathComp's
      @is_derive R R^o V t 1 g l: g is derivable at t in the direction 1 and
      its derivative there is l. Both say that (g (t + h) - g t) / h tends to
      l as h tends to 0 with h <> 0. For V = R the codomain is R^o, the
      normed module view of R, as in AnalysisBridge
      (AnalysisBridge.is_derive_Reals relates it to Stdlib's
      derivable_pt_lim). This concerns joint_time_sqrt_derivative,
      joint_time_complement_sqrt_derivative and joint_soft_time_derivative
      (V = R^o) and joint_matrix_time_derivative (V = matrix_NormedModule n,
      the nested tuples of MatrixDefinitions with the Frobenius norm). The
      direction 1 is Stdlib's literal, as in AnalysisBridge and in the
      restated challenge ellipsoid_interpolation_time, whose first clause is
      joint_soft_time_derivative word for word.

   The port adds four lemmas, marked below. joint_time_is_diff_of_derive and
   joint_time_derive_of_is_diff relate the derivative of a function of a
   real variable to its Frechet derivative h |-> h *: l on R^o, which
   Coquelicot identified by definition (its is_derive was filterdiff with
   the differential fun h => scal h l). joint_time_derive_scale is the
   derivative of u |-> k u *: v, in place of Coquelicot's is_derive_scal_l
   at a normed module. joint_matrix_time_is_diff states the conclusion of
   joint_matrix_time_derivative as a Frechet derivative, the form that
   is_diff_comp and tuple_build_frechet take; the ports of JointTimeSecond
   and RowTimeCalculus, which composed joint_matrix_time_derivative with
   filterdiff_comp' and tuple_build_frechet, can use it.

   What changes in the proofs. Coquelicot's is_derive_ext_loc on matrices
   becomes MathComp's near_eq_is_derive, with the neighbourhood given by
   AnalysisBridge.nbhs_Reals. Coquelicot's is_derive_plus,
   is_derive_const and is_derive_scal_l on matrix_NormedModule n become
   MathComp's is_deriveD, is_derive_cst and joint_time_derive_scale.
   is_derive_sqrt, is_derive_minus, is_derive_const and is_derive_id become
   the lemmas of AnalysisBridge with the same names (is_derive_id_R for the
   last). In joint_soft_time_derivative, Coquelicot's filterdiff_comp'
   becomes is_diff_comp, and filterdiff_ext_lin becomes the computation of
   the derivative through deriveE and diff_val. The Frechet derivative of the
   soft value is matrix_nested_soft_minimax_frechet of the ported MatrixGibbs,
   as before. Stdlib's "rewrite A, B" is written "rewrite A B", since
   ssreflect's rewrite is loaded, and trace_pair_scale is rewritten with
   explicit arguments, because a bare rewrite would also unfold goe_matrix,
   which is itself a matrix_scale.

   Assumptions. joint_soft_time_derivative mentions soft_minimax, whose
   definition uses Stdlib's logarithm Rpower.ln, so it rests on
   Classical_Prop.classic besides the seven axioms of analysis/README.md.
   The other statements rest on the seven axioms only. *)

(* Added by the port. A derivative in the direction 1 of a function of a
   real variable is its Frechet derivative h |-> h *: l on R^o. *)
Lemma joint_time_is_diff_of_derive {W : normedModType R} (f : R -> W) (t : R) (l : W) :
  @is_derive R R^o W t 1 f l ->
  is_diff (t : R^o) (f : R^o -> W) (fun h : R^o => (h *: l)%R).
Proof.
move=> Hder.
have [Ed Hv] := Hder.
have Dd : differentiable (f : R^o -> W) t by apply/derivable1_diffP.
apply: DiffDef; first exact Dd.
rewrite diff1E // derive1E Hv; apply: funext => h /=.
reflexivity.
Qed.

(* Added by the port. The converse of joint_time_is_diff_of_derive. *)
Lemma joint_time_derive_of_is_diff {W : normedModType R} (f : R -> W) (t : R) (l : W) :
  is_diff (t : R^o) (f : R^o -> W) (fun h : R^o => (h *: l)%R) ->
  @is_derive R R^o W t 1 f l.
Proof.
move=> HL.
apply: DeriveDef.
  exact/diff_derivable/ex_diff.
by rewrite deriveE ?diff_val //= scale1r.
Qed.

(* Added by the port. The derivative of u |-> k u *: v, for a real function
   k with derivative dk at t, is dk *: v. This replaces Coquelicot's
   is_derive_scal_l at a normed module. *)
Lemma joint_time_derive_scale {W : normedModType R} (k : R -> R) (t dk : R) (v : W) :
  @is_derive R R^o R^o t 1 k dk ->
  @is_derive R R^o W t 1 (fun u : R => (k u *: v)%R) (dk *: v)%R.
Proof.
move=> Hk.
have Hd := @joint_time_is_diff_of_derive R^o k t dk Hk.
have HC := is_diff_comp Hd (is_diff_scalel (k t) v).
apply: joint_time_derive_of_is_diff.
apply: (is_diff_eq HC).
apply: funext => h /=.
by rewrite scalerA.
Qed.

Lemma joint_matrix_normalized_path n C t x z : 0 <= t ->
  joint_matrix n C t x z = matrix_add n C
    (matrix_add n (matrix_scale n (sqrt t) (joint_quadratic_input n x))
      (matrix_scale n (sqrt(1-t)) (goe_matrix n z))).
Proof.
  intro Ht; apply matrix_ext; intros i j Hi Hj.
  unfold joint_matrix, joint_quadratic_input, quadratic_matrix.
  rewrite !matrix_entry_add !matrix_entry_scale !(matrix_entry_build _ _ _ _ Hi Hj).
  have HN : 0 < INR (S n) by apply lt_0_INR; lia.
  rewrite matrix_entry_zero (sqrt_div t (INR (S n)) Ht HN).
  unfold Rdiv; ring.
Qed.

Lemma joint_time_sqrt_derivative t : 0 < t -> @is_derive R R^o R^o t 1 sqrt (/(2*sqrt t)).
Proof. intro Ht; apply is_derive_Reals, derivable_pt_lim_sqrt; exact Ht. Qed.

Lemma joint_time_complement_sqrt_derivative t : t < 1 ->
  @is_derive R R^o R^o t 1 (fun u => sqrt(1-u)) (-/(2*sqrt(1-t))).
Proof.
  intro Ht; replace (-/(2*sqrt(1-t))) with ((0-1)/(2*sqrt(1-t))) by (unfold Rdiv; ring).
  apply (is_derive_sqrt (fun u => 1 - u) t (0 - 1)); [|lra].
  apply (is_derive_minus (fun _ => 1) (fun u => u) t 0 1);
    [exact (is_derive_const 1 t)|exact (is_derive_id_R t)].
Qed.

Theorem joint_matrix_time_derivative n C t x z : 0 < t < 1 ->
  @is_derive R R^o (matrix_NormedModule n) t 1
    (fun u : R => joint_matrix n C u x z) (joint_time_velocity n t x z).
Proof.
  intros Ht.
  have Hsum : @is_derive R R^o (matrix_NormedModule n) t 1
      (fun u : R => matrix_add n C
        (matrix_add n (matrix_scale n (sqrt u) (joint_quadratic_input n x))
          (matrix_scale n (sqrt(1-u)) (goe_matrix n z))))
      (joint_time_velocity n t x z).
  { have H1 := joint_time_derive_scale sqrt t (/(2*sqrt t)) (joint_quadratic_input n x)
      (joint_time_sqrt_derivative t ltac:(lra)).
    have H2 := joint_time_derive_scale (fun u => sqrt(1-u)) t (-/(2*sqrt(1-t)))
      (goe_matrix n z) (joint_time_complement_sqrt_derivative t ltac:(lra)).
    have H12 := is_deriveD H1 H2.
    have H0 := is_deriveD (is_derive_cst (C : matrix_NormedModule n) (t : R^o) 1) H12.
    unfold joint_time_velocity, matrix_add, matrix_scale.
    rewrite -[X in is_derive _ _ _ X](add0r).
    exact H0. }
  apply: (near_eq_is_derive _ Hsum).
  apply (proj2 (nbhs_Reals t _)).
  exists (t/2); split; [lra|]; intros u Hu.
  symmetry; apply joint_matrix_normalized_path.
  apply Rabs_def2 in Hu; lra.
Qed.

(* Added by the port. The conclusion of joint_matrix_time_derivative as a
   Frechet derivative on R^o, the form of Coquelicot's is_derive. *)
Lemma joint_matrix_time_is_diff n C t x z : 0 < t < 1 ->
  is_diff (t : R^o) ((fun u : R^o => joint_matrix n C u x z) : R^o -> matrix_NormedModule n)
    (fun h : R^o => (h *: joint_time_velocity n t x z)%R).
Proof.
  intro Ht.
  exact (@joint_time_is_diff_of_derive (matrix_NormedModule n) _ t _
    (joint_matrix_time_derivative n C t x z Ht)).
Qed.

Lemma joint_time_velocity_trace n beta gamma offset coeff Y S C t x z :
  trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S (joint_matrix n C t x z))
    (joint_time_velocity n t x z) =
  joint_quadratic_trace n beta gamma offset coeff Y S C t x z/(2*sqrt t) -
  joint_goe_trace n beta gamma offset coeff Y S C t x z/(2*sqrt(1-t)).
Proof.
  unfold joint_time_velocity; rewrite trace_pair_add.
  rewrite (trace_pair_scale n _ (joint_quadratic_input n x))
    (trace_pair_scale n _ (goe_matrix n z)).
  unfold joint_quadratic_trace, joint_goe_trace.
  assert (HC : forall A B : matrix n, trace_pair n A B = trace_pair n B A).
  { apply symmetric_trace_pair_comm. }
  rewrite (HC _ (joint_quadratic_input n x)) (HC _ (goe_matrix n z)); unfold Rdiv; ring.
Qed.

Theorem joint_soft_time_derivative n beta gamma offset coeff Y S C t x z :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 < t < 1 ->
  @is_derive R R^o R^o t 1 (fun u => joint_soft_value n beta gamma offset coeff Y S C u x z)
    (joint_quadratic_trace n beta gamma offset coeff Y S C t x z/(2*sqrt t) -
     joint_goe_trace n beta gamma offset coeff Y S C t x z/(2*sqrt(1-t))).
Proof.
  intros Hb Hg HY HS Ht; unfold joint_soft_value.
  have HP := joint_matrix_time_is_diff n C t x z Ht.
  have HF := matrix_nested_soft_minimax_frechet n beta gamma offset coeff Y S
    (joint_matrix n C t x z) Hb Hg HY HS.
  have HC := is_diff_comp HP HF.
  apply: DeriveDef.
    exact/diff_derivable/ex_diff.
  rewrite deriveE ?diff_val //= scale1r.
  rewrite -matrix_nested_gradient_trace joint_time_velocity_trace; reflexivity.
Qed.
