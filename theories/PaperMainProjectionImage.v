(* Finite nonlinear coordinate images: continuity, bounds and chain rules. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GaussianCovarianceSums
  GaussianCoordinateDefinitions GaussianCoordinateBasics GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianCovarianceChainRule PaperMainGaussianSmoothCalculus.
Open Scope R_scope.

Definition paper_main_projection_image K (U : nat -> list R -> R) xs :=
  List.map (fun a => U a xs) (List.seq 0 K).

Lemma paper_main_projection_image_length K U xs :
  List.length(paper_main_projection_image K U xs)=K.
Proof. unfold paper_main_projection_image; rewrite List.length_map List.length_seq; reflexivity. Qed.
Lemma paper_main_projection_image_nth K U xs a : (a<K)%coq_nat ->
  List.nth a (paper_main_projection_image K U xs) 0=U a xs.
Proof. intro Ha; unfold paper_main_projection_image; exact(nth_map_seq _ K a Ha). Qed.

Lemma paper_main_projection_uniform_close d K (U : nat -> list R -> R) :
  (forall a, (a<K)%coq_nat -> finite_joint_continuous d (U a)) ->
  forall z (eps : posreal), exists delta : posreal,
    forall w, close_n d delta w z -> forall a, (a<K)%coq_nat ->
      Rabs(U a (coordinates_to_list d w)-U a (coordinates_to_list d z))<eps.
Proof.
induction K as [|K IH]; intros HU z eps.
- exists eps; intros w Hw a Ha; lia.
- destruct (IH (fun a Ha => HU a ltac:(lia)) z eps) as [delta1 H1].
  destruct (HU K ltac:(lia) z eps) as [delta2 H2].
  assert (HD : 0 < Rmin delta1 delta2) by (apply Rmin_pos; apply cond_pos).
  exists (mkposreal _ HD); intros w Hw a Ha.
  assert (HW1 : close_n d delta1 w z).
  { apply (coordinates_close_mono d (Rmin delta1 delta2) delta1); [apply Rmin_l|exact Hw]. }
  assert (HW2 : close_n d delta2 w z).
  { apply (coordinates_close_mono d (Rmin delta1 delta2) delta2); [apply Rmin_r|exact Hw]. }
  destruct (Nat.eq_dec a K) as [->|Hne]; [exact(H2 w HW2)|apply H1; [exact HW1|lia]].
Qed.

Theorem paper_main_projection_image_continuous d K U F :
  (forall a, (a<K)%coq_nat -> finite_joint_continuous d (U a)) ->
  finite_joint_continuous K F ->
  finite_joint_continuous d (fun xs => F(paper_main_projection_image K U xs)).
Proof.
intros HU HF z eps.
set (iz := paper_main_projection_image K U (coordinates_to_list d z)).
destruct (HF (coordinates_of_list K iz) eps) as [delta Hdelta].
destruct (paper_main_projection_uniform_close d K U HU z delta) as [eta Heta].
exists eta; intros w Hw.
pose proof (Hdelta (coordinates_of_list K
  (paper_main_projection_image K U (coordinates_to_list d w)))) as HH.
rewrite (coordinates_list_roundtrip _ _ (paper_main_projection_image_length _ _ _)) in HH.
rewrite (coordinates_list_roundtrip _ _ (paper_main_projection_image_length _ _ _)) in HH.
apply HH; apply (coordinates_close_lists K delta _ _
  (paper_main_projection_image_length _ _ _) (paper_main_projection_image_length _ _ _)).
intros a Ha; unfold iz; rewrite !paper_main_projection_image_nth; try exact Ha.
apply Heta; assumption.
Qed.

Lemma paper_main_projection_image_bounded d K U F C :
  finite_polynomial_bound K C 0 F ->
  finite_polynomial_bound d C 0 (fun xs => F(paper_main_projection_image K U xs)).
Proof.
intro HF; apply paper_main_polynomial_zero_bound in HF; destruct HF as [HC HF].
apply paper_main_polynomial_zero_bound; split; [exact HC|].
intros xs Hxs; apply HF; apply paper_main_projection_image_length.
Qed.

Theorem paper_main_projection_image_coordinate d K i U DU F DF :
  (forall a, (a<K)%coq_nat -> finite_coordinate_derivative K a F (DF a)) ->
  (forall a, (a<K)%coq_nat -> finite_joint_continuous K (DF a)) ->
  (forall a, (a<K)%coq_nat -> finite_coordinate_derivative d i (U a) (DU a)) ->
  finite_coordinate_derivative d i (fun xs => F(paper_main_projection_image K U xs))
    (fun xs => finite_sum (fun a => DF a (paper_main_projection_image K U xs)*DU a xs) (List.seq 0 K)).
Proof.
intros HF HC HU; apply (finite_coordinate_derivative_comp d K i F DF
  (paper_main_projection_image K U) DU HF HC).
- intros xs Hxs; apply paper_main_projection_image_length.
- intros a Ha xs Hxs.
  apply (is_derive_ext (fun t => U a (replace_coordinate i t xs))).
  + intro t; rewrite (paper_main_projection_image_nth K U _ a Ha); reflexivity.
  + exact (HU a Ha xs Hxs).
Qed.

Theorem paper_main_projection_image_parameter K (U : nat -> R -> R) DU F DF t :
  (forall a, (a<K)%coq_nat -> finite_coordinate_derivative K a F (DF a)) ->
  (forall a, (a<K)%coq_nat -> finite_joint_continuous K (DF a)) ->
  (forall a, (a<K)%coq_nat -> @is_derive R R^o R^o t 1 (U a) (DU a)) ->
  @is_derive R R^o R^o t 1 (fun s => F(List.map (fun a => U a s) (List.seq 0 K)))
    (finite_sum (fun a => DF a (List.map (fun b => U b t) (List.seq 0 K))*DU a) (List.seq 0 K)).
Proof.
intros HF HC HU; apply (finite_chain_rule K F DF
  (fun s => List.map (fun a => U a s) (List.seq 0 K)) DU t HF HC).
- intro s; rewrite List.length_map List.length_seq; reflexivity.
- intros a Ha; apply (is_derive_ext (U a)).
  + intro s; rewrite (nth_map_seq _ K a Ha); reflexivity.
  + exact(HU a Ha).
Qed.
