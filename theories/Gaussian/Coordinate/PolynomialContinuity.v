From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.Tuples Analysis.CoordinateTopology.
Import ListNotations.
Open Scope R_scope.

(* Closure properties of finite_joint_continuous, the joint continuity of a
   function of the d coordinates of a list xs. Write x_i for
   List.nth i xs 0. Each coordinate x_i with i < d is continuous
   (finite_joint_continuous_nth), and sums, products, scalar multiples and
   differences of continuous functions are continuous. Hence, for F
   continuous, so are x_i * F, (x_i * x_i - 1) * F and (x_i * x_j) * F.

   The statements write List.nth and (i < d)%coq_nat because MathComp is
   loaded: its seq.nth takes its arguments in another order, and
   (i < d)%nat would be ssrnat's boolean ltn. The sum, product and
   difference go through finite_joint_continuous_filter
   (Analysis.CoordinateTopology), which states the joint continuity as
   MathComp's continuity on coordinates_uniform_space d. *)

Lemma finite_joint_continuous_nth d i :
  (i < d)%coq_nat -> finite_joint_continuous d (fun xs => List.nth i xs 0).
Proof.
  intros Hi z eps; exists eps; intros w Hw.
  exact (proj1 (coordinates_close_iff d eps w z) Hw i Hi).
Qed.

Lemma finite_joint_continuous_add d F G :
  finite_joint_continuous d F -> finite_joint_continuous d G ->
  finite_joint_continuous d (fun xs => F xs + G xs).
Proof.
  intros HF HG; apply finite_joint_continuous_filter; intro z.
  apply (continuous_plus (coordinates_uniform_space d)
    (fun w => F (coordinates_to_list d w)) (fun w => G (coordinates_to_list d w))).
  - apply finite_joint_continuous_filter; exact HF.
  - apply finite_joint_continuous_filter; exact HG.
Qed.

Lemma finite_joint_continuous_mult d F G :
  finite_joint_continuous d F -> finite_joint_continuous d G ->
  finite_joint_continuous d (fun xs => F xs * G xs).
Proof.
  intros HF HG; apply finite_joint_continuous_filter; intro z.
  apply (continuous_mult (coordinates_uniform_space d)
    (fun w => F (coordinates_to_list d w)) (fun w => G (coordinates_to_list d w))).
  - apply finite_joint_continuous_filter; exact HF.
  - apply finite_joint_continuous_filter; exact HG.
Qed.

Lemma finite_joint_continuous_scale d F a :
  finite_joint_continuous d F ->
  finite_joint_continuous d (fun xs => a * F xs).
Proof.
  intro HF; apply finite_joint_continuous_mult.
  - apply finite_joint_continuous_constant.
  - exact HF.
Qed.

Lemma finite_joint_continuous_minus d F G :
  finite_joint_continuous d F -> finite_joint_continuous d G ->
  finite_joint_continuous d (fun xs => F xs - G xs).
Proof.
  intros HF HG; apply finite_joint_continuous_filter; intro z.
  apply (continuous_minus (coordinates_uniform_space d)
    (fun w => F (coordinates_to_list d w)) (fun w => G (coordinates_to_list d w))).
  - apply finite_joint_continuous_filter; exact HF.
  - apply finite_joint_continuous_filter; exact HG.
Qed.

Lemma finite_joint_continuous_times_coordinate d F i :
  finite_joint_continuous d F -> (i < d)%coq_nat ->
  finite_joint_continuous d (fun xs => List.nth i xs 0 * F xs).
Proof.
  intros HF Hi; apply finite_joint_continuous_mult.
  - apply finite_joint_continuous_nth; exact Hi.
  - exact HF.
Qed.

Lemma finite_joint_continuous_times_centered_square d F i :
  finite_joint_continuous d F -> (i < d)%coq_nat ->
  finite_joint_continuous d (fun xs => (List.nth i xs 0 * List.nth i xs 0 - 1) * F xs).
Proof.
  intros HF Hi; apply finite_joint_continuous_mult; [|exact HF].
  apply finite_joint_continuous_minus.
  - apply finite_joint_continuous_mult; apply finite_joint_continuous_nth; exact Hi.
  - apply finite_joint_continuous_constant.
Qed.

Lemma finite_joint_continuous_times_two_coordinates d F i j :
  finite_joint_continuous d F -> (i < d)%coq_nat -> (j < d)%coq_nat ->
  finite_joint_continuous d (fun xs => (List.nth i xs 0 * List.nth j xs 0) * F xs).
Proof.
  intros HF Hi Hj; apply finite_joint_continuous_mult; [|exact HF].
  apply finite_joint_continuous_mult; apply finite_joint_continuous_nth; assumption.
Qed.
