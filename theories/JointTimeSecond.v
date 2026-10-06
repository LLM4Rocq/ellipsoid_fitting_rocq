From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace OperatorDefinitions
  SoftDefinitions MatrixGibbsDefinitions MatrixSecondDefinitions MatrixGibbs
  GradientDefinitions MatrixGradient MatrixHessian QuadraticCalculus GoeDefinitions
  JointDefinitions TimeDefinitions JointTimeCalculus.
Import ListNotations.
Open Scope R_scope.

(* Second time derivatives of the coefficients sqrt t and sqrt (1 - t) of
   the joint interpolation path, whose first derivatives are / (2 * sqrt t)
   and - / (2 * sqrt (1 - t)).
   - joint_time_inverse_sqrt_derivative: for t > 0, the derivative at t of
     u |-> / (2 * sqrt u) is - / (4 * t * sqrt t).
   - joint_time_inverse_complement_derivative: for t < 1, the derivative at
     t of u |-> - / (2 * sqrt (1 - u)) is - / (4 * (1 - t) * sqrt (1 - t)).
   The derivatives are MathComp's is_derive at t in the direction 1, the
   ordinary derivative of a function R -> R. *)

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
