(* Coordinates of the two pure endpoints of the multirow interpolation, for
   the challenge multirow_expectation_derivative.

   The N rows are read from one list of N (d + D) coordinates: row i is the
   chunk of length d + D at position i, its first d entries are the
   quadratic coordinates x_i and the other D the GOE coordinates z_i.

   mexp_row_suffixes N d D xs keeps the last D entries of every row, in row
   order; row_prefixes N d D xs of RowMarginalDefinitions keeps the first d.
   mexp_row_suffixes_gaussian_expectation says that the iterated Gaussian
   expectation of F (mexp_row_suffixes xs) over N (d + D) coordinates is the
   expectation of F over N D coordinates, as
   row_prefixes_gaussian_expectation of GaussianRowMarginal does for the
   prefixes. Neither needs a hypothesis on F.

   mexp_goe_lift N d D zs goes the other way: it puts d zeros in front of
   every chunk of length D of zs, and mexp_quadratic_lift N d D xs puts D
   zeros after every chunk of length d of xs. Both keep closeness of the
   coordinates and the product weights, so continuity and polynomial bounds
   pass from a function of N (d + D) coordinates to its composite with a
   lift.

   Only Stdlib and port modules without MathComp are imported, so ++,
   length, firstn, skipn, + and * on nat and the operations on R are
   Stdlib's. No Axiom, Parameter or Admitted. *)

From Stdlib Require Import Reals List Arith Lia Lra.
From EllipsoidFitting Require Import RowCoordinateDefinitions RowMarginalDefinitions
  GaussianProductDefinitions GaussianProduct GaussianLastDefinitions GaussianLastIntegration
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianPermutationContinuity.
Import ListNotations.
Open Scope R_scope.

Fixpoint mexp_row_suffixes {A : Type} (N d D : nat) (xs : list A) : list A :=
  match N with
  | O => nil
  | S k => firstn D (skipn d xs) ++ mexp_row_suffixes k d D (skipn (d+D) xs)
  end.

Fixpoint mexp_goe_lift (N d D : nat) (zs : list R) : list R :=
  match N with
  | O => nil
  | S k => repeat 0 d ++ firstn D zs ++ mexp_goe_lift k d D (skipn D zs)
  end.

Fixpoint mexp_quadratic_lift (N d D : nat) (xs : list R) : list R :=
  match N with
  | O => nil
  | S k => firstn d xs ++ repeat 0 D ++ mexp_quadratic_lift k d D (skipn d xs)
  end.

(* List facts. *)

Lemma mexp_skipn_app_exact {A : Type} (l1 l2 : list A) k :
  skipn (length l1 + k) (l1 ++ l2) = skipn k l2.
Proof. induction l1 as [|a l1 IH]; simpl; [reflexivity|exact IH]. Qed.

Lemma mexp_skipn_app_length {A : Type} (l1 l2 : list A) :
  skipn (length l1) (l1 ++ l2) = l2.
Proof. rewrite <- (Nat.add_0_r (length l1)), mexp_skipn_app_exact; reflexivity. Qed.

Lemma mexp_firstn_app_length {A : Type} (l1 l2 : list A) :
  firstn (length l1) (l1 ++ l2) = l1.
Proof. induction l1 as [|a l1 IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma mexp_row_chunk_S {A : Type} K i (xs : list A) :
  row_chunk K (S i) xs = row_chunk K i (skipn K xs).
Proof.
  unfold row_chunk; rewrite skipn_skipn; simpl.
  replace (K + i*K)%nat with (i*K + K)%nat by lia; reflexivity.
Qed.

Lemma mexp_row_chunk_app_0 {A : Type} K (l1 l2 : list A) :
  length l1 = K -> row_chunk K 0 (l1 ++ l2) = l1.
Proof. intro H; subst K; unfold row_chunk; simpl; apply mexp_firstn_app_length. Qed.

Lemma mexp_row_chunk_app_S {A : Type} K i (l1 l2 : list A) :
  length l1 = K -> row_chunk K (S i) (l1 ++ l2) = row_chunk K i l2.
Proof.
  intro H; rewrite mexp_row_chunk_S; subst K; rewrite mexp_skipn_app_length; reflexivity.
Qed.

Lemma mexp_split_row {A : Type} N d D (xs : list A) :
  length xs = (S N*(d+D))%nat ->
  exists front b tail, xs = front ++ b ++ tail /\ length front = d /\
    length b = D /\ length tail = (N*(d+D))%nat.
Proof.
  intro HL.
  exists (firstn d xs), (firstn D (skipn d xs)), (skipn D (skipn d xs)).
  split; [rewrite !firstn_skipn; reflexivity|].
  rewrite !length_firstn, !length_skipn, HL; simpl; repeat split; lia.
Qed.

Lemma mexp_length_repeat {A : Type} (a : A) k : length (repeat a k) = k.
Proof. induction k as [|k IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

(* Suffixes. *)

Theorem mexp_row_suffixes_first_block {A : Type} N d D (front b tail : list A) :
  length front = d -> length b = D ->
  mexp_row_suffixes (S N) d D (front ++ b ++ tail) = b ++ mexp_row_suffixes N d D tail.
Proof.
  intros HF HB; simpl mexp_row_suffixes.
  assert (H1 : skipn d (front ++ b ++ tail) = b ++ tail).
  { subst d; apply mexp_skipn_app_length. }
  assert (H2 : skipn (d+D) (front ++ b ++ tail) = tail).
  { subst d D; rewrite mexp_skipn_app_exact, mexp_skipn_app_length; reflexivity. }
  rewrite H1, H2; f_equal; subst D; apply mexp_firstn_app_length.
Qed.

Theorem mexp_row_suffixes_row_chunk {A : Type} N d D i (xs : list A) :
  length xs = (N*(d+D))%nat -> (i < N)%nat ->
  row_chunk D i (mexp_row_suffixes N d D xs) = skipn d (row_chunk (d+D) i xs).
Proof.
  revert i xs; induction N as [|N IH]; intros i xs HL Hi; [lia|].
  destruct (mexp_split_row N d D xs HL) as [front [b [tail [-> [HF [HB HT]]]]]].
  rewrite mexp_row_suffixes_first_block by assumption.
  rewrite app_assoc.
  destruct i as [|i].
  - rewrite mexp_row_chunk_app_0 by exact HB.
    rewrite mexp_row_chunk_app_0 by (rewrite length_app; lia).
    subst d; rewrite mexp_skipn_app_length; reflexivity.
  - rewrite mexp_row_chunk_app_S by exact HB.
    rewrite mexp_row_chunk_app_S by (rewrite length_app; lia).
    apply IH; [exact HT|lia].
Qed.

Theorem mexp_row_suffixes_gaussian_expectation N d D (F : list R -> R) :
  gaussian_iterated_expectation (N*(d+D)) (fun xs => F (mexp_row_suffixes N d D xs)) =
  gaussian_iterated_expectation (N*D) F.
Proof.
  revert F; induction N as [|N IH]; intro F; [reflexivity|].
  change (gaussian_iterated_expectation ((d+D)+N*(d+D))
    (fun xs => F (mexp_row_suffixes (S N) d D xs)) =
    gaussian_iterated_expectation (D+N*D) F).
  rewrite (gaussian_iterated_suffix_expectation (d+D) (N*(d+D))).
  rewrite (gaussian_iterated_suffix_expectation d D).
  rewrite (gaussian_iterated_suffix_expectation D (N*D) F).
  transitivity (gaussian_iterated_expectation d
    (fun _ => gaussian_iterated_expectation D (gaussian_suffix_marginal (N*D) F))).
  - apply gaussian_iterated_expectation_ext; intros front HF.
    unfold gaussian_suffix_marginal.
    apply gaussian_iterated_expectation_ext; intros b HB.
    transitivity (gaussian_iterated_expectation (N*(d+D))
      (fun tail => F (b ++ mexp_row_suffixes N d D tail))).
    + apply gaussian_iterated_expectation_ext; intros tail HT.
      rewrite <- app_assoc, mexp_row_suffixes_first_block by assumption; reflexivity.
    + exact (IH (fun ys => F (b ++ ys))).
  - exact (proj2 (gaussian_iterated_constant d _)).
Qed.

(* Lifts. *)

Lemma mexp_forall2_repeat {A B : Type} (P : A -> B -> Prop) a b k :
  P a b -> Forall2 P (repeat a k) (repeat b k).
Proof. intro H; induction k as [|k IH]; simpl; constructor; assumption. Qed.

Lemma mexp_forall2_firstn {A B : Type} (P : A -> B -> Prop) k xs ys :
  Forall2 P xs ys -> Forall2 P (firstn k xs) (firstn k ys).
Proof.
  revert xs ys; induction k as [|k IH]; intros xs ys H; simpl; [constructor|].
  destruct H; simpl; constructor; auto.
Qed.

Lemma mexp_forall2_skipn {A B : Type} (P : A -> B -> Prop) k xs ys :
  Forall2 P xs ys -> Forall2 P (skipn k xs) (skipn k ys).
Proof.
  revert xs ys; induction k as [|k IH]; intros xs ys H; simpl; [exact H|].
  destruct H; simpl; [constructor|apply IH; exact H0].
Qed.

Lemma mexp_product_weight_zeros p k :
  gaussian_coordinate_product_weight p (repeat 0 k) = 1.
Proof.
  induction k as [|k IH]; simpl; [reflexivity|].
  rewrite IH; unfold gaussian_coordinate_weight; rewrite Rabs_R0, Rplus_0_r, pow1; ring.
Qed.

Theorem mexp_goe_lift_length N d D zs :
  length zs = (N*D)%nat -> length (mexp_goe_lift N d D zs) = (N*(d+D))%nat.
Proof.
  revert zs; induction N as [|N IH]; intros zs HL; [reflexivity|].
  simpl mexp_goe_lift; rewrite !length_app, mexp_length_repeat, length_firstn, IH.
  - simpl in HL; lia.
  - rewrite length_skipn; simpl in HL; lia.
Qed.

Theorem mexp_goe_lift_row_chunk N d D i zs :
  length zs = (N*D)%nat -> (i < N)%nat ->
  row_chunk (d+D) i (mexp_goe_lift N d D zs) = repeat 0 d ++ row_chunk D i zs.
Proof.
  revert i zs; induction N as [|N IH]; intros i zs HL Hi; [lia|].
  simpl mexp_goe_lift; rewrite app_assoc.
  assert (Hb : length (repeat 0 d ++ firstn D zs) = (d+D)%nat).
  { rewrite length_app, mexp_length_repeat, length_firstn; simpl in HL; lia. }
  destruct i as [|i].
  - rewrite mexp_row_chunk_app_0 by exact Hb; unfold row_chunk; reflexivity.
  - rewrite mexp_row_chunk_app_S by exact Hb.
    rewrite IH by (try rewrite length_skipn; simpl in HL; lia).
    rewrite mexp_row_chunk_S; reflexivity.
Qed.

Theorem mexp_goe_lift_forall2 (P : R -> R -> Prop) N d D zs ws :
  P 0 0 -> Forall2 P zs ws -> Forall2 P (mexp_goe_lift N d D zs) (mexp_goe_lift N d D ws).
Proof.
  intro H0; revert zs ws; induction N as [|N IH]; intros zs ws H; simpl; [constructor|].
  apply Forall2_app; [apply mexp_forall2_repeat; exact H0|].
  apply Forall2_app; [apply mexp_forall2_firstn; exact H|].
  apply IH; apply mexp_forall2_skipn; exact H.
Qed.

Theorem mexp_goe_lift_weight p N d D zs :
  length zs = (N*D)%nat ->
  gaussian_coordinate_product_weight p (mexp_goe_lift N d D zs) =
  gaussian_coordinate_product_weight p zs.
Proof.
  revert zs; induction N as [|N IH]; intros zs HL.
  - destruct zs; [reflexivity|simpl in HL; discriminate].
  - simpl mexp_goe_lift.
    rewrite !gaussian_coordinate_product_weight_append, mexp_product_weight_zeros, IH.
    + rewrite <- gaussian_coordinate_product_weight_append, firstn_skipn; ring.
    + rewrite length_skipn; simpl in HL; lia.
Qed.

Theorem mexp_quadratic_lift_length N d D xs :
  length xs = (N*d)%nat -> length (mexp_quadratic_lift N d D xs) = (N*(d+D))%nat.
Proof.
  revert xs; induction N as [|N IH]; intros xs HL; [reflexivity|].
  simpl mexp_quadratic_lift; rewrite !length_app, mexp_length_repeat, length_firstn, IH.
  - simpl in HL; lia.
  - rewrite length_skipn; simpl in HL; lia.
Qed.

Theorem mexp_quadratic_lift_row_chunk N d D i xs :
  length xs = (N*d)%nat -> (i < N)%nat ->
  row_chunk (d+D) i (mexp_quadratic_lift N d D xs) = row_chunk d i xs ++ repeat 0 D.
Proof.
  revert i xs; induction N as [|N IH]; intros i xs HL Hi; [lia|].
  simpl mexp_quadratic_lift; rewrite app_assoc.
  assert (Hb : length (firstn d xs ++ repeat 0 D) = (d+D)%nat).
  { rewrite length_app, mexp_length_repeat, length_firstn; simpl in HL; lia. }
  destruct i as [|i].
  - rewrite mexp_row_chunk_app_0 by exact Hb; unfold row_chunk; reflexivity.
  - rewrite mexp_row_chunk_app_S by exact Hb.
    rewrite IH by (try rewrite length_skipn; simpl in HL; lia).
    rewrite mexp_row_chunk_S; reflexivity.
Qed.

Theorem mexp_quadratic_lift_forall2 (P : R -> R -> Prop) N d D xs ys :
  P 0 0 -> Forall2 P xs ys ->
  Forall2 P (mexp_quadratic_lift N d D xs) (mexp_quadratic_lift N d D ys).
Proof.
  intro H0; revert xs ys; induction N as [|N IH]; intros xs ys H; simpl; [constructor|].
  apply Forall2_app; [apply mexp_forall2_firstn; exact H|].
  apply Forall2_app; [apply mexp_forall2_repeat; exact H0|].
  apply IH; apply mexp_forall2_skipn; exact H.
Qed.

Theorem mexp_quadratic_lift_weight p N d D xs :
  length xs = (N*d)%nat ->
  gaussian_coordinate_product_weight p (mexp_quadratic_lift N d D xs) =
  gaussian_coordinate_product_weight p xs.
Proof.
  revert xs; induction N as [|N IH]; intros xs HL.
  - destruct xs; [reflexivity|simpl in HL; discriminate].
  - simpl mexp_quadratic_lift.
    rewrite !gaussian_coordinate_product_weight_append, mexp_product_weight_zeros, IH.
    + rewrite <- (firstn_skipn d xs) at 3.
      rewrite gaussian_coordinate_product_weight_append; ring.
    + rewrite length_skipn; simpl in HL; lia.
Qed.

(* Regularity passes to the composites with the lifts. *)

Lemma mexp_close_zero (e : posreal) : Rabs (0-0) < e.
Proof. replace (0-0) with 0 by ring; rewrite Rabs_R0; apply cond_pos. Qed.

Theorem mexp_goe_lift_continuous N d D F :
  finite_joint_continuous (N*(d+D)) F ->
  finite_joint_continuous (N*D) (fun zs => F (mexp_goe_lift N d D zs)).
Proof.
  apply finite_joint_continuous_list_map.
  - apply mexp_goe_lift_length.
  - intros e xs ys _ _ H; apply mexp_goe_lift_forall2; [apply mexp_close_zero|exact H].
Qed.

Theorem mexp_quadratic_lift_continuous N d D F :
  finite_joint_continuous (N*(d+D)) F ->
  finite_joint_continuous (N*d) (fun xs => F (mexp_quadratic_lift N d D xs)).
Proof.
  apply finite_joint_continuous_list_map.
  - apply mexp_quadratic_lift_length.
  - intros e xs ys _ _ H; apply mexp_quadratic_lift_forall2; [apply mexp_close_zero|exact H].
Qed.

Theorem mexp_goe_lift_polynomial N d D C p F :
  finite_polynomial_bound (N*(d+D)) C p F ->
  finite_polynomial_bound (N*D) C p (fun zs => F (mexp_goe_lift N d D zs)).
Proof.
  intros [HC HF]; split; [exact HC|]; intros zs HL.
  rewrite <- (mexp_goe_lift_weight p N d D zs HL).
  apply HF; apply mexp_goe_lift_length; exact HL.
Qed.

Theorem mexp_quadratic_lift_polynomial N d D C p F :
  finite_polynomial_bound (N*(d+D)) C p F ->
  finite_polynomial_bound (N*d) C p (fun xs => F (mexp_quadratic_lift N d D xs)).
Proof.
  intros [HC HF]; split; [exact HC|]; intros xs HL.
  rewrite <- (mexp_quadratic_lift_weight p N d D xs HL).
  apply HF; apply mexp_quadratic_lift_length; exact HL.
Qed.
