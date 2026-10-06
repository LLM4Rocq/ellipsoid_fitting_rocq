(* Polynomial domination of the value and its actual coordinate derivatives. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Gaussian.CoordinateWeightDefinitions Gaussian.CoordinateWeights
  Gaussian.CovarianceLinearImages Gordon.Coordinates.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_finite_value_bound H Y S M :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> Rabs (H y s) <= M) ->
  Rabs (finite_minimax H Y S) <= M.
Proof.
intros HY HS HM.
unfold finite_minimax.
destruct (finite_min_attained (fun y => finite_max (H y) S) Y HY) as [y [Hy Ey]].
rewrite Ey.
destruct (finite_max_attained (H y) S HS) as [s [Hs Es]].
rewrite Es; apply HM; assumption.
Qed.

Lemma paper_main_gordon_soft_value_bound beta gamma H Y S M :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> Rabs (H y s) <= M) ->
  Rabs (soft_minimax beta gamma H Y S) <= M +
    Rabs (Rpower.ln (INR (List.length Y)) / beta) +
    Rabs (Rpower.ln (INR (List.length S)) / gamma).
Proof.
intros Hb Hg HY HS HM.
pose proof (paper_main_gordon_finite_value_bound H Y S M HY HS HM) as HB.
pose proof (soft_minimax_bounds beta gamma H Y S Hb Hg HY HS) as [HL HU].
pose proof (Rle_abs (finite_minimax H Y S)).
pose proof (Rle_abs (- finite_minimax H Y S)).
rewrite Rabs_Ropp in H1.
pose proof (Rle_abs (Rpower.ln (INR (List.length Y)) / beta)).
pose proof (Rle_abs (Rpower.ln (INR (List.length S)) / gamma)).
pose proof (Rabs_pos (Rpower.ln (INR (List.length Y)) / beta)).
pose proof (Rabs_pos (Rpower.ln (INR (List.length S)) / gamma)).
apply Rabs_le; split; lra.
Qed.

Definition paper_main_gordon_growth_constant beta gamma (Y S : list nat) : R :=
  1 + Rabs (Rpower.ln (INR (List.length Y)) / beta) +
    Rabs (Rpower.ln (INR (List.length S)) / gamma) + 2 * (beta + gamma).

Theorem paper_main_gordon_polynomial_growth K beta gamma J Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  let C := paper_main_gordon_growth_constant beta gamma Y S in
  finite_polynomial_bound K C 1 (paper_main_gordon_value beta gamma J Y S) /\
  (forall a, finite_polynomial_bound K C 1 (paper_main_gordon_first beta gamma J Y S a)) /\
  (forall a b, finite_polynomial_bound K C 1 (paper_main_gordon_second beta gamma J Y S a b)).
Proof.
intros Hb Hg HY HS HJ C.
pose proof (Rabs_pos (Rpower.ln (INR (List.length Y)) / beta)) as HYlog.
pose proof (Rabs_pos (Rpower.ln (INR (List.length S)) / gamma)) as HSlog.
assert (HC0 : 0 <= C) by (unfold C, paper_main_gordon_growth_constant; lra).
assert (HC1 : 1 <= C) by (unfold C, paper_main_gordon_growth_constant; lra).
assert (HC2 : 2 * (beta + gamma) <= C) by (unfold C, paper_main_gordon_growth_constant; lra).
split.
- split; [exact HC0|]; intros xs Hxs.
  pose proof (gaussian_coordinate_product_weight_at_least_one 1 xs) as HW.
  assert (HJb : forall y s, In y Y -> In s S ->
    Rabs (paper_main_gordon_scores J xs y s) <= gaussian_coordinate_product_weight 1 xs).
  { intros y s Hy Hs; unfold paper_main_gordon_scores.
    apply coordinate_le_weight_one; rewrite Hxs; apply HJ; assumption. }
  pose proof (paper_main_gordon_soft_value_bound beta gamma
    (paper_main_gordon_scores J xs) Y S (gaussian_coordinate_product_weight 1 xs)
    Hb Hg HY HS HJb) as HB.
  unfold paper_main_gordon_value, C, paper_main_gordon_growth_constant; nra.
- split.
  + intros a; split; [exact HC0|]; intros xs Hxs.
    pose proof (paper_main_gordon_first_bound beta gamma J Y S a xs HY HS).
    pose proof (gaussian_coordinate_product_weight_at_least_one 1 xs); nra.
  + intros a b; split; [exact HC0|]; intros xs Hxs.
    pose proof (paper_main_gordon_second_bound beta gamma J Y S a b xs
      ltac:(lra) ltac:(lra) HY HS).
    pose proof (gaussian_coordinate_product_weight_at_least_one 1 xs); nra.
Qed.
