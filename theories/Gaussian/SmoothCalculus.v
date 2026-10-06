(* Coordinate calculus for bounded smooth Gaussian tests. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateDerivativeDefinitions
  Analysis.CoordinatePermutationDefinitions Analysis.CoordinatePermutations
  Gaussian.CovarianceLinearImages.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_coordinate_derivative_value_ext d a F DF DG :
  finite_coordinate_derivative d a F DF ->
  (forall xs, List.length xs = d -> DF xs = DG xs) ->
  finite_coordinate_derivative d a F DG.
Proof.
intros HD He xs Hxs; rewrite <- (He xs Hxs); exact (HD xs Hxs).
Qed.

Lemma paper_main_coordinate_derivative_const d a c :
  finite_coordinate_derivative d a (fun _ => c) (fun _ => 0).
Proof.
intros xs Hxs; apply is_derive_const.
Qed.

Lemma paper_main_coordinate_derivative_add d a F G DF DG :
  finite_coordinate_derivative d a F DF ->
  finite_coordinate_derivative d a G DG ->
  finite_coordinate_derivative d a (fun xs => F xs + G xs) (fun xs => DF xs + DG xs).
Proof.
intros HF HG xs Hxs; apply is_derive_plus; [exact (HF xs Hxs)|exact (HG xs Hxs)].
Qed.

Lemma paper_main_coordinate_derivative_scale d a F DF c :
  finite_coordinate_derivative d a F DF ->
  finite_coordinate_derivative d a (fun xs => c * F xs) (fun xs => c * DF xs).
Proof.
intros HF xs Hxs; apply is_derive_scal; exact (HF xs Hxs).
Qed.

Lemma paper_main_coordinate_derivative_mult d a F G DF DG :
  finite_coordinate_derivative d a F DF ->
  finite_coordinate_derivative d a G DG ->
  finite_coordinate_derivative d a (fun xs => F xs * G xs)
    (fun xs => DF xs * G xs + F xs * DG xs).
Proof.
intros HF HG xs Hxs.
pose proof (is_derive_mult (fun t => F (replace_coordinate a t xs))
  (fun t => G (replace_coordinate a t xs)) (List.nth a xs 0)
  (DF xs) (DG xs) (HF xs Hxs) (HG xs Hxs)) as H.
rewrite replace_coordinate_self in H; exact H.
Qed.

Lemma paper_main_polynomial_zero_bound d C F :
  finite_polynomial_bound d C 0 F <->
  0 <= C /\ forall xs, List.length xs = d -> Rabs (F xs) <= C.
Proof.
unfold finite_polynomial_bound; split; intros [HC HF]; split; [exact HC| |exact HC|].
- intros xs Hxs; specialize (HF xs Hxs); rewrite product_weight_zero Rmult_1_r in HF; exact HF.
- intros xs Hxs; rewrite product_weight_zero Rmult_1_r; apply HF; exact Hxs.
Qed.
