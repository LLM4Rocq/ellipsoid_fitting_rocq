From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions
  SymmetricDefinitions SymmetricBasis GoeDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module GoePairs of theories/InterpolationProofs.v (also
   copied in GoeProofs.v and JointProofs.v) from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original used nothing from Coquelicot directly. Its only Coquelicot
   content came through matrix n, coordinate_sum, symmetric_basis and its
   two parts, and goe_pairs, goe_vector_index and goe_basis of
   GoeDefinitions. Their ports keep the same names, arguments and values, so
   the import of Coquelicot is dropped and the text below is the original,
   unchanged.

   This file loads no MathComp module. As a consequence map, seq, flat_map,
   ++, length, nth and In are Stdlib's list functions, with Stdlib's argument
   order nth k l default, and (a <= b)%nat is Stdlib's Peano order le, as in
   the original and as in the port of GoeDefinitions. The ports of
   SymmetricBasis and SecondChaosAlgebra write the same order as
   (a <= b)%coq_nat, which is the same term. The arithmetic, the literals and
   the sums are Stdlib's, as before.

   An importer that loads all_ssreflect_compat sees MathComp's nth, map,
   seq, ++ and <= under these names and notations. To state or match these
   lemmas it writes List.nth, List.map, List.seq, (_ ++ _)%list and
   (_ <= _)%coq_nat. Stdlib's length, In, NoDup and the division
   (_ / _)%nat keep their meaning there. *)

Lemma goe_pairs_nonempty n : goe_pairs n <> [].
Proof. unfold goe_pairs; discriminate. Qed.

Lemma goe_vector_dimension n : S (goe_vector_index n) = length (goe_pairs n).
Proof.
  unfold goe_vector_index; apply Nat.succ_pred_pos.
  destruct (goe_pairs n) eqn:H; [exfalso; apply (goe_pairs_nonempty n); exact H|simpl; lia].
Qed.

Lemma goe_upper_length k a :
  (2 * length (flat_map (fun i => map (fun j => (i,j))
    (seq (S i) (a+k-i))) (seq a (S k))) = k * S k)%nat.
Proof.
  revert a; induction k as [|k IH]; intro a.
  - change (2 * length (map (fun j => (a,j)) (seq (S a) (a+0-a)) ++ []) = 0)%nat.
    rewrite Nat.add_0_r, Nat.sub_diag; reflexivity.
  - change (2 * length (map (fun j => (a,j)) (seq (S a) (a+S k-a)) ++
      flat_map (fun i => map (fun j => (i,j)) (seq (S i) (a+S k-i)))
        (seq (S a) (S k))) = S k * S (S k))%nat.
    rewrite length_app, length_map, length_seq.
    replace (a+S k-a)%nat with (S k) by lia.
    replace (a+S k)%nat with (S a+k)%nat by lia.
    pose proof (IH (S a)); nia.
Qed.

Lemma goe_pairs_length_twice n :
  (2 * length (goe_pairs n) = S n * S (S n))%nat.
Proof.
  unfold goe_pairs; rewrite length_app, length_map, length_seq.
  pose proof (goe_upper_length n O) as H; simpl Nat.add in H; nia.
Qed.

Theorem goe_pairs_length n :
  length (goe_pairs n) = (S n * S (S n) / 2)%nat.
Proof.
  pose proof (goe_pairs_length_twice n) as H.
  replace (S n * S (S n))%nat with (length (goe_pairs n) * 2)%nat by nia.
  rewrite Nat.div_mul by lia; reflexivity.
Qed.

Theorem goe_pairs_valid n a b :
  In (a,b) (goe_pairs n) <-> (a <= b /\ b <= n)%nat.
Proof.
  unfold goe_pairs; rewrite in_app_iff; split.
  - intros [H|H].
    + apply in_map_iff in H as [i [He Hi]]; inversion He; subst.
      apply in_seq in Hi; lia.
    + apply in_flat_map in H as [i [Hi H]].
      apply in_map_iff in H as [j [He Hj]]; inversion He; subst.
      apply in_seq in Hi; apply in_seq in Hj; lia.
  - intros [Hab Hb]; destruct (Nat.eq_dec a b) as [He|He].
    + left; apply in_map_iff; exists a; split; [congruence|apply in_seq; lia].
    + right; apply in_flat_map; exists a; split; [apply in_seq; lia|].
      apply in_map_iff; exists b; split; [reflexivity|apply in_seq; lia].
Qed.

Lemma goe_nodup_map_injective {A B : Type} (f : A -> B) xs :
  (forall x y, f x = f y -> x = y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros Hf H; induction H; simpl; constructor; [|exact IHNoDup].
  intro Hin; apply in_map_iff in Hin as [y [He Hy]]; apply H.
  assert (y=x) by (apply Hf; exact He); subst; exact Hy.
Qed.

Lemma goe_rows_nodup n xs : NoDup xs ->
  NoDup (flat_map (fun a => map (fun b => (a,b)) (seq (S a) (n-a))) xs).
Proof.
  intro H; induction H as [|a xs Hnot Hnd IH]; simpl; [constructor|].
  apply NoDup_app.
  - apply goe_nodup_map_injective; [intros; congruence|apply seq_NoDup].
  - exact IH.
  - intros [i j] Hi Hj; apply in_map_iff in Hi as [b [He Hb]]; inversion He; subst.
    apply in_flat_map in Hj as [c [Hc Hj]].
    apply in_map_iff in Hj as [d [He2 Hd]]; inversion He2; subst; contradiction.
Qed.

Theorem goe_pairs_nodup n : NoDup (goe_pairs n).
Proof.
  unfold goe_pairs; apply NoDup_app.
  - apply goe_nodup_map_injective; [intros; congruence|apply seq_NoDup].
  - apply goe_rows_nodup, seq_NoDup.
  - intros [a b] H1 H2; apply in_map_iff in H1 as [i [He Hi]]; inversion He; subst.
    apply in_flat_map in H2 as [j [Hj H2]].
    apply in_map_iff in H2 as [k [He2 Hk]]; inversion He2; subst.
    apply in_seq in Hk; lia.
Qed.

Lemma goe_pairs_nth_valid n k : (k <= goe_vector_index n)%nat ->
  (fst (nth k (goe_pairs n) (O,O)) <= snd (nth k (goe_pairs n) (O,O)) /\
   snd (nth k (goe_pairs n) (O,O)) <= n)%nat.
Proof.
  intro Hk; pose proof (goe_vector_dimension n) as Hd.
  assert (Hkl : (k < length (goe_pairs n))%nat) by lia.
  pose proof (@nth_In (nat*nat) k (goe_pairs n) (O,O) Hkl) as H.
  destruct (nth k (goe_pairs n) (O,O)) as [a b] eqn:He.
  apply goe_pairs_valid; exact H.
Qed.

Lemma goe_pairs_nth_injective n i j :
  (i <= goe_vector_index n)%nat -> (j <= goe_vector_index n)%nat ->
  nth i (goe_pairs n) (O,O) = nth j (goe_pairs n) (O,O) -> i=j.
Proof.
  intros Hi Hj He; apply (proj1 (NoDup_nth (goe_pairs n) (O,O)) (goe_pairs_nodup n) i j);
    try exact He; pose proof (goe_vector_dimension n); lia.
Qed.

Lemma goe_sum_app {A : Type} (h : A -> R) xs ys :
  fold_right Rplus 0 (map h (xs++ys)) =
    fold_right Rplus 0 (map h xs) + fold_right Rplus 0 (map h ys).
Proof. induction xs; simpl; [ring|rewrite IHxs; ring]. Qed.

Lemma goe_sum_flat_map {A B : Type} (F : A -> list B) (h : B -> R) xs :
  fold_right Rplus 0 (map h (flat_map F xs)) =
    fold_right Rplus 0 (map (fun a => fold_right Rplus 0 (map h (F a))) xs).
Proof. induction xs; simpl; [reflexivity|rewrite goe_sum_app, IHxs; reflexivity]. Qed.

Lemma goe_coordinate_sum_seq n f :
  coordinate_sum n f = fold_right Rplus 0 (map f (seq 0 (S n))).
Proof.
  revert f; induction n as [|n IH]; intro f; [simpl; ring|].
  change (f O + coordinate_sum n (fun i => f (S i)) =
    f O + fold_right Rplus 0 (map f (seq 1 (S n)))).
  rewrite <- seq_shift, map_map, <- IH; reflexivity.
Qed.

Lemma goe_coordinate_sum_nth {A : Type} n (xs : list A) (h : A -> R) d :
  length xs = S n -> coordinate_sum n (fun k => h (nth k xs d)) =
    fold_right Rplus 0 (map h xs).
Proof.
  revert xs; induction n as [|n IH]; intros [|a xs] H; simpl in H; try lia.
  - destruct xs; simpl in H; [simpl; ring|discriminate].
  - change (h a + coordinate_sum n (fun k => h (nth k xs d)) =
      h a + fold_right Rplus 0 (map h xs)); rewrite IH by lia; reflexivity.
Qed.

Lemma goe_sum_zero {A : Type} (xs : list A) :
  fold_right Rplus 0 (map (fun _ => 0) xs) = 0.
Proof. induction xs; simpl; [reflexivity|rewrite IHxs; ring]. Qed.

Lemma goe_masked_row n a h : (a <= n)%nat ->
  fold_right Rplus 0 (map h (seq (S a) (n-a))) =
    coordinate_sum n (fun b => if Nat.ltb a b then h b else 0).
Proof.
  intro Ha; rewrite goe_coordinate_sum_seq.
  replace (S n) with (S a+(n-a))%nat by lia.
  rewrite seq_app, goe_sum_app.
  assert (H0 : fold_right Rplus 0 (map (fun b => if Nat.ltb a b then h b else 0)
    (seq 0 (S a))) = 0).
  { transitivity (fold_right Rplus 0 (map (fun _ => 0) (seq 0 (S a)))); [|apply goe_sum_zero].
    f_equal; apply map_ext_in; intros b Hb; apply in_seq in Hb.
    rewrite (proj2 (Nat.ltb_ge a b) ltac:(lia)); reflexivity. }
  rewrite H0, Rplus_0_l; f_equal; apply map_ext_in.
  intros b Hb; apply in_seq in Hb; rewrite (proj2 (Nat.ltb_lt a b) ltac:(lia)); reflexivity.
Qed.

Theorem goe_basis_sum n (h : matrix n -> R) :
  coordinate_sum (goe_vector_index n) (fun k => h (goe_basis n k)) =
  coordinate_sum n (fun a => h (symmetric_diagonal_basis n a)) +
  coordinate_sum n (fun a => coordinate_sum n (fun b =>
    if Nat.ltb a b then h (symmetric_offdiagonal_basis n a b) else 0)).
Proof.
  unfold goe_basis.
  rewrite (goe_coordinate_sum_nth (goe_vector_index n) (goe_pairs n)
    (fun ab => h (symmetric_basis n (fst ab) (snd ab))) (O,O))
    by (symmetry; apply goe_vector_dimension).
  unfold goe_pairs; rewrite goe_sum_app, map_map, goe_sum_flat_map.
  rewrite !goe_coordinate_sum_seq; apply f_equal2; [|].
  - f_equal; apply map_ext; intro a; simpl; unfold symmetric_basis; rewrite Nat.eqb_refl; reflexivity.
  - f_equal; apply map_ext_in; intros a Ha; apply in_seq in Ha.
    rewrite map_map; change (fold_right Rplus 0
      (map (fun b => h (symmetric_basis n a b)) (seq (S a) (n-a))) =
      coordinate_sum n (fun b => if Nat.ltb a b then h (symmetric_offdiagonal_basis n a b) else 0)).
    transitivity (fold_right Rplus 0
      (map (fun b => h (symmetric_offdiagonal_basis n a b)) (seq (S a) (n-a)))).
    + f_equal; apply map_ext_in; intros b Hb; apply in_seq in Hb.
      unfold symmetric_basis; rewrite (proj2 (Nat.eqb_neq a b) ltac:(lia)); reflexivity.
    + apply goe_masked_row; lia.
Qed.

