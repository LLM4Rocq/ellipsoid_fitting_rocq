From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import GaussianCoordinateDefinitions GaussianCoordinateBasics
  GaussianCoordinateTopology.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/GaussianCoordinatePolynomialContinuity.v from Coquelicot
   to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the
   same order, and says the same thing. finite_joint_continuous comes from
   the port of GaussianCoordinateDefinitions, which copies the original
   definition word for word. The changes of text are the following.

   1. nth. With MathComp loaded, an unqualified nth is MathComp's seq.nth,
      whose arguments come in another order. The statements write List.nth,
      which is the nth of the original (Stdlib's). This affects
      finite_joint_continuous_nth, finite_joint_continuous_times_coordinate,
      finite_joint_continuous_times_centered_square and
      finite_joint_continuous_times_two_coordinates.

   2. The bound on the index. With ssreflect loaded, (i < d)%nat is
      ssrnat's boolean ltn. The statements write (i < d)%coq_nat, which is
      Peano's lt, the relation of the original. The same four lemmas are
      affected.

   The statements of finite_joint_continuous_add, finite_joint_continuous_mult,
   finite_joint_continuous_scale and finite_joint_continuous_minus are the
   original text.

   Proofs. finite_joint_continuous_nth is the original proof. The original
   proofs of add, mult and minus went through finite_joint_continuous_filter
   and Coquelicot's continuous_plus, continuous_mult and continuous_minus on
   coordinates_uniform_space d. The port does the same with the port of
   finite_joint_continuous_filter (GaussianCoordinateTopology), where
   continuity at a point is MathComp's {for z, continuous f}, and with the
   combinators continuous_plus, continuous_mult and continuous_minus of
   AnalysisBridge, stated for any topological domain and codomain R with
   Stdlib's operations. The other proofs are the original ones. *)

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
