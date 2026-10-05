From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace OperatorDefinitions
  SoftDefinitions MatrixGibbsDefinitions MatrixSecondDefinitions MatrixGibbs
  GradientDefinitions MatrixGradient MatrixHessian QuadraticCalculus GoeDefinitions
  JointDefinitions TimeDefinitions JointTimeCalculus.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module JointTimeSecond of theories/InterpolationProofs.v,
   extracted to build/agent2/unbundled/JointTimeSecond.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   Every lemma and theorem of the original keeps its name and its arguments,
   in the same order. No lemma is added. The four statements change form in
   one way, without a change of meaning.

   1. Derivatives of a function of a real variable. Coquelicot's
      is_derive g t l, for g : R -> V, becomes MathComp's
      @is_derive R R^o V t 1 g l: g is derivable at t in the direction 1 and
      its derivative there is l. Both say that (g (t + h) - g t) / h tends to
      l as h tends to 0 with h <> 0. For V = R the codomain is R^o, the
      normed module view of R, as in AnalysisBridge
      (AnalysisBridge.is_derive_Reals relates it to Stdlib's
      derivable_pt_lim). This concerns joint_time_inverse_sqrt_derivative,
      joint_time_inverse_complement_derivative and
      joint_soft_time_second_derivative (V = R^o), and
      joint_matrix_time_second_derivative (V = matrix_NormedModule n, the
      nested tuples of MatrixDefinitions with the Frobenius norm). The
      direction 1 is Stdlib's literal, as in the ported JointTimeCalculus and
      in the restated challenge ellipsoid_interpolation_time, whose second
      clause of group 1 is joint_soft_time_second_derivative word for word.

   What changes in the proofs. Coquelicot's is_derive_inv, is_derive_scal,
   is_derive_comp, is_derive_minus, is_derive_const, is_derive_id and
   is_derive_opp on R become the lemmas of AnalysisBridge with the same names
   (is_derive_id_R for is_derive_id). Coquelicot's is_derive_plus and
   is_derive_scal_l on matrix_NormedModule n become MathComp's is_deriveD and
   joint_time_derive_scale of the ported JointTimeCalculus. In
   joint_soft_time_second_derivative, Coquelicot's is_derive_ext becomes a
   rewrite of the function by funext, filterdiff_comp' becomes is_diff_comp
   with joint_matrix_time_is_diff of the ported JointTimeCalculus, and
   filterdiff_ext_lin becomes the computation of the derivative through
   deriveE and diff_val, as in the port of joint_soft_time_derivative. The
   second-order identity is matrix_nested_gradient_derivative_trace of the
   ported MatrixHessian, as before. The derivative is evaluated at the
   direction 1, so the factor h of the original is 1 and scale1r removes it;
   Coquelicot's linear_scal and trace_pair_scale are not needed.

   Assumptions. joint_time_inverse_sqrt_derivative,
   joint_time_inverse_complement_derivative and
   joint_matrix_time_second_derivative rest on the seven axioms of
   analysis/README.md only. joint_soft_time_second_derivative also rests on
   Classical_Prop.classic, which it inherits from the ported
   matrix_nested_gradient_frechet and matrix_nested_gradient_derivative_trace:
   Print Assumptions shows classic for both. *)

Lemma joint_time_inverse_sqrt_derivative t : 0 < t ->
  @is_derive R R^o R^o t 1 (fun u => /(2*sqrt u)) (-/(4*t*sqrt t)).
Proof.
  intro Ht; assert (Hs : 0 < sqrt t) by (apply sqrt_lt_R0; exact Ht).
  assert (HE : -/(4*t*sqrt t) = -(2*/(2*sqrt t))/(2*sqrt t)^2).
  { field_simplify; try lra.
    replace (sqrt t^3) with ((sqrt t*sqrt t)*sqrt t) by ring.
    rewrite (sqrt_def t (Rlt_le _ _ Ht)).
    replace (4*t*sqrt t) with (4*(t*sqrt t)) by ring; reflexivity. }
  rewrite HE; apply (is_derive_inv (fun u=>2*sqrt u) t (2*/(2*sqrt t))); [|lra].
  apply is_derive_scal; apply joint_time_sqrt_derivative; exact Ht.
Qed.

Lemma joint_time_inverse_complement_derivative t : t < 1 ->
  @is_derive R R^o R^o t 1 (fun u => -/(2*sqrt(1-u))) (-/(4*(1-t)*sqrt(1-t))).
Proof.
  intro Ht.
  assert (HD : @is_derive R R^o R^o t 1 (fun u => /(2*sqrt(1-u))) (/(4*(1-t)*sqrt(1-t)))).
  { replace (/(4*(1-t)*sqrt(1-t))) with
      ((-1)*(-/(4*(1-t)*sqrt(1-t)))) by ring.
    apply (is_derive_comp (fun v=>/(2*sqrt v)) (fun u=>1-u)
      t (-/(4*(1-t)*sqrt(1-t))) (-1)).
    - apply joint_time_inverse_sqrt_derivative; lra.
    - replace (-1) with (0-1) by ring.
      apply (is_derive_minus (fun _=>1) (fun u=>u) t 0 1);
      [exact (is_derive_const 1 t)|exact (is_derive_id_R t)]. }
  exact (is_derive_opp _ t _ HD).
Qed.
