(* Signed lattice centers and their exponential counting bound. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import PaperMainGordonBudget.
Import ListNotations.
Open Scope R_scope.

Fixpoint paper_main_gordon_signs h (xs : list nat) : list (list R) :=
  match xs with
  | [] => [[]]
  | x :: rest =>
      List.map (cons (h * INR x)) (paper_main_gordon_signs h rest) ++
      List.map (cons (- (h * INR x))) (paper_main_gordon_signs h rest)
  end.

Definition paper_main_gordon_signed_grid d K h :=
  List.flat_map (paper_main_gordon_signs h) (paper_main_gordon_budget_grid d K).

Lemma paper_main_gordon_signs_cardinality h xs :
  List.length (paper_main_gordon_signs h xs) = (2^List.length xs)%nat.
Proof.
induction xs as [|x xs IH]; [reflexivity|].
cbn [paper_main_gordon_signs length].
rewrite length_app, !length_map, IH; simpl; lia.
Qed.

Lemma paper_main_gordon_signs_cover h xs :
  forall u : nat -> R,
  (forall i, (i < List.length xs)%nat ->
    Rabs (Rabs (u i) - h * INR (List.nth i xs 0%nat)) <= h) ->
  exists ys, List.In ys (paper_main_gordon_signs h xs) /\
    forall i, (i < List.length xs)%nat -> Rabs (u i - List.nth i ys 0) <= h.
Proof.
induction xs as [|x xs IH]; intros u H.
- exists []; split; [simpl; auto|intros i Hi; simpl in Hi; lia].
- destruct (IH (fun i => u (S i)) ltac:(intros i Hi; apply (H (S i)); simpl; lia)) as [ys [Hys HE]].
  pose proof (H 0%nat ltac:(simpl; lia)) as H0; simpl in H0.
  destruct (Rle_dec 0 (u 0%nat)) as [Hu|Hu].
  + exists (h*INR x :: ys); split.
    * simpl; apply in_app_iff; left; apply in_map; exact Hys.
    * intros [|i] Hi; simpl; [rewrite (Rabs_right (u 0%nat) ltac:(lra)) in H0; exact H0|apply HE; simpl in Hi; lia].
  + exists (-(h*INR x) :: ys); split.
    * simpl; apply in_app_iff; right; apply in_map; exact Hys.
    * intros [|i] Hi; simpl; [|apply HE; simpl in Hi; lia].
      rewrite (Rabs_left (u 0%nat) ltac:(lra)) in H0.
      replace (u 0%nat - - (h*INR x)) with (-(-u 0%nat - h*INR x)) by ring.
      rewrite Rabs_Ropp; exact H0.
Qed.

Lemma paper_main_gordon_flat_map_cardinality {A B : Type} (f : A -> list B) C m :
  (forall x, List.In x C -> List.length (f x) = m) ->
  List.length (List.flat_map f C) = (List.length C * m)%nat.
Proof.
induction C as [|x C IH]; intros H; [reflexivity|].
simpl; rewrite length_app, (H x ltac:(simpl; auto)), IH by (intros; apply H; simpl; auto).
lia.
Qed.

Lemma paper_main_gordon_signed_grid_cardinality d K h :
  (List.length (paper_main_gordon_signed_grid d K h) <= 2^(2*d+K))%nat.
Proof.
unfold paper_main_gordon_signed_grid.
rewrite (paper_main_gordon_flat_map_cardinality _ _ (2^d)%nat).
- replace (2*d+K)%nat with ((d+K)+d)%nat by lia.
  rewrite Nat.pow_add_r; apply Nat.mul_le_mono_r.
  apply paper_main_gordon_budget_grid_cardinality.
- intros xs H; rewrite paper_main_gordon_signs_cardinality.
  rewrite (paper_main_gordon_budget_grid_length d K xs H); reflexivity.
Qed.
