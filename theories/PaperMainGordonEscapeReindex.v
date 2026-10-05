(* Invariance of the iterated standard Gaussian expectation under an
   injective reindexing of the coordinates. For sigma mapping {0..d-1}
   injectively into itself, paper_main_gordon_reindex sigma d xs is the list
   x_(sigma 0), ..., x_(sigma (d-1)). For jointly continuous, polynomially
   bounded F, E_d[F (reindex sigma d xs)] = E_d[F]. The coordinate
   x_(sigma (d-1)) is moved last with gaussian_iterated_move_last and
   integrated out with gaussian_iterated_last_expectation; induction on d
   does the rest. The matrix transpose is the instance used for Gordon's
   escape bound: paper_main_gordon_transpose N M sends the row-major
   coordinates of an N-by-M matrix to the row-major coordinates of its
   M-by-N transpose, and both lists have the same iterated Gaussian
   expectations. *)
From Stdlib Require Import Reals List Lia Lra Psatz Permutation FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianLastDefinitions GaussianLastIntegration GaussianCoordinateMarginals
  GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianPermutationContinuity GaussianPermutationWeights GaussianCoordinateMove.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_reindex (sigma : nat -> nat) d (xs : list R) : list R :=
  List.map (fun k => List.nth (sigma k) xs 0) (List.seq 0 d).

Definition paper_main_gordon_injective_on d (sigma : nat -> nat) : Prop :=
  (forall k, (k < d)%nat -> (sigma k < d)%nat) /\
  (forall k l, (k < d)%nat -> (l < d)%nat -> sigma k = sigma l -> k = l).

Lemma paper_main_gordon_reindex_length sigma d xs :
  length (paper_main_gordon_reindex sigma d xs) = d.
Proof. unfold paper_main_gordon_reindex; rewrite length_map, length_seq; reflexivity. Qed.

Lemma paper_main_gordon_reindex_nth sigma d xs k :
  (k < d)%nat ->
  List.nth k (paper_main_gordon_reindex sigma d xs) 0 = List.nth (sigma k) xs 0.
Proof.
intros Hk; unfold paper_main_gordon_reindex.
rewrite (nth_indep (List.map (fun k => List.nth (sigma k) xs 0) (List.seq 0 d)) 0
  (List.nth (sigma 0%nat) xs 0)) by (rewrite length_map, length_seq; exact Hk).
rewrite (map_nth (fun k => List.nth (sigma k) xs 0) (List.seq 0 d) 0%nat k).
rewrite seq_nth by exact Hk; reflexivity.
Qed.

Lemma paper_main_gordon_reindex_forall2 sigma d (e : posreal) xs ys :
  (forall k, (k < d)%nat -> (sigma k < d)%nat) ->
  length xs = d -> length ys = d ->
  List.Forall2 (fun x y => Rabs (x - y) < e) xs ys ->
  List.Forall2 (fun x y => Rabs (x - y) < e)
    (paper_main_gordon_reindex sigma d xs) (paper_main_gordon_reindex sigma d ys).
Proof.
intros Hr Hxs Hys H.
apply coordinate_nth_forall2.
- rewrite !paper_main_gordon_reindex_length; reflexivity.
- intros i Hi; rewrite paper_main_gordon_reindex_length in Hi.
  rewrite !paper_main_gordon_reindex_nth by exact Hi.
  apply (coordinate_forall2_nth _ xs ys H); rewrite Hxs; apply Hr; exact Hi.
Qed.

Lemma paper_main_gordon_reindex_continuous d sigma F :
  (forall k, (k < d)%nat -> (sigma k < d)%nat) ->
  finite_joint_continuous d F ->
  finite_joint_continuous d (fun xs => F (paper_main_gordon_reindex sigma d xs)).
Proof.
intros Hr HF.
apply (finite_joint_continuous_list_map d d (paper_main_gordon_reindex sigma d) F).
- intros xs _; apply paper_main_gordon_reindex_length.
- intros e xs ys Hxs Hys H; apply paper_main_gordon_reindex_forall2; assumption.
- exact HF.
Qed.

Lemma paper_main_gordon_map_nth_seq (xs : list R) :
  List.map (fun k => List.nth k xs 0) (List.seq 0 (length xs)) = xs.
Proof.
induction xs as [|x xs IH]; [reflexivity|].
simpl; f_equal.
rewrite <- seq_shift, map_map; exact IH.
Qed.

Lemma paper_main_gordon_reindex_permutation d sigma xs :
  paper_main_gordon_injective_on d sigma -> length xs = d ->
  Permutation (paper_main_gordon_reindex sigma d xs) xs.
Proof.
intros [Hr Hi] Hxs.
assert (HN : NoDup (List.map sigma (List.seq 0 d))).
{ apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
  intros k l Hk Hl Heq; apply in_seq in Hk; apply in_seq in Hl.
  apply Hi; [lia|lia|exact Heq]. }
assert (Hincl : incl (List.map sigma (List.seq 0 d)) (List.seq 0 d)).
{ intros m Hm; apply in_map_iff in Hm; destruct Hm as [k [Hkm Hk]].
  apply in_seq in Hk; apply in_seq; pose proof (Hr k ltac:(lia)); lia. }
assert (Hincl' : incl (List.seq 0 d) (List.map sigma (List.seq 0 d))).
{ apply NoDup_length_incl; [exact HN|rewrite length_map; lia|exact Hincl]. }
assert (HP : Permutation (List.map sigma (List.seq 0 d)) (List.seq 0 d)).
{ apply NoDup_Permutation; [exact HN|apply seq_NoDup|].
  intros m; split; [apply Hincl|apply Hincl']. }
transitivity (List.map (fun k => List.nth k xs 0) (List.map sigma (List.seq 0 d))).
{ unfold paper_main_gordon_reindex; rewrite map_map; apply Permutation_refl. }
transitivity (List.map (fun k => List.nth k xs 0) (List.seq 0 d)).
{ apply Permutation_map; exact HP. }
rewrite <- Hxs, paper_main_gordon_map_nth_seq; apply Permutation_refl.
Qed.

Lemma paper_main_gordon_reindex_polynomial_bound d sigma C p F :
  paper_main_gordon_injective_on d sigma ->
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C p (fun xs => F (paper_main_gordon_reindex sigma d xs)).
Proof.
intros Hs HB.
apply (finite_polynomial_bound_permutation d C p F (paper_main_gordon_reindex sigma d));
  [|exact HB].
intros xs Hxs; apply paper_main_gordon_reindex_permutation; assumption.
Qed.

(* Entries of the list with one coordinate moved last. *)

Lemma paper_main_gordon_move_last_nth_before j xs m :
  (m < j)%nat -> List.nth m (move_coordinate_last j xs) 0 = List.nth m xs 0.
Proof.
revert xs m; induction j as [|j IH]; intros [|x xs] [|m] Hm; simpl; try lia;
  try reflexivity.
apply IH; lia.
Qed.

Lemma paper_main_gordon_move_last_nth_after j xs m :
  (j <= m)%nat -> (S m < length xs)%nat ->
  List.nth m (move_coordinate_last j xs) 0 = List.nth (S m) xs 0.
Proof.
revert xs m; induction j as [|j IH]; intros [|x xs] m Hjm Hm; simpl in *; try lia.
- rewrite app_nth1 by lia; reflexivity.
- destruct m as [|m]; [lia|]; simpl; apply IH; lia.
Qed.

(* The reindexing invariance. *)

Theorem paper_main_gordon_reindex_expectation d sigma F C p :
  paper_main_gordon_injective_on d sigma ->
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_expectation d (fun xs => F (paper_main_gordon_reindex sigma d xs)) =
  gaussian_iterated_expectation d F.
Proof.
revert sigma F C; induction d as [|d IH]; intros sigma F C [Hr Hi] HC HB.
- reflexivity.
- set (j := sigma d).
  set (sigma1 := fun k => if (sigma k <? j)%nat then sigma k else (sigma k - 1)%nat).
  set (sigma2 := fun k => if (k <? d)%nat then sigma1 k else d).
  assert (Hj : (j < S d)%nat) by (apply Hr; lia).
  assert (Hne : forall k, (k < d)%nat -> sigma k <> j).
  { intros k Hk Heq; assert (k = d) by (apply Hi; [lia|lia|exact Heq]); lia. }
  assert (H1 : paper_main_gordon_injective_on d sigma1).
  { split.
    - intros k Hk; unfold sigma1.
      pose proof (Hr k ltac:(lia)); pose proof (Hne k Hk).
      destruct (Nat.ltb_spec (sigma k) j); lia.
    - intros k l Hk Hl; unfold sigma1.
      pose proof (Hne k Hk); pose proof (Hne l Hl).
      destruct (Nat.ltb_spec (sigma k) j); destruct (Nat.ltb_spec (sigma l) j);
        intros Heq; apply Hi; lia. }
  assert (H2 : paper_main_gordon_injective_on (S d) sigma2).
  { split.
    - intros k Hk; unfold sigma2.
      destruct (Nat.ltb_spec k d); [pose proof (proj1 H1 k ltac:(lia)); lia|lia].
    - intros k l Hk Hl; unfold sigma2.
      destruct (Nat.ltb_spec k d); destruct (Nat.ltb_spec l d); intros Heq.
      + apply (proj2 H1); [lia|lia|exact Heq].
      + pose proof (proj1 H1 k ltac:(lia)); lia.
      + pose proof (proj1 H1 l ltac:(lia)); lia.
      + lia. }
  assert (Hpt : forall xs, length xs = S d ->
    paper_main_gordon_reindex sigma (S d) xs =
    paper_main_gordon_reindex sigma2 (S d) (move_coordinate_last j xs)).
  { intros xs Hxs; apply nth_ext with (d := 0) (d' := 0).
    - rewrite !paper_main_gordon_reindex_length; reflexivity.
    - intros n Hn; rewrite paper_main_gordon_reindex_length in Hn.
      rewrite !paper_main_gordon_reindex_nth by exact Hn.
      unfold sigma2; destruct (Nat.ltb_spec n d) as [Hnd|Hnd].
      + unfold sigma1; pose proof (Hne n Hnd); pose proof (Hr n ltac:(lia)).
        destruct (Nat.ltb_spec (sigma n) j).
        * rewrite paper_main_gordon_move_last_nth_before by lia; reflexivity.
        * rewrite paper_main_gordon_move_last_nth_after by lia.
          f_equal; lia.
      + assert (n = d) by lia; subst n.
        change (sigma d) with j.
        rewrite <- (move_coordinate_last_nth_selected j xs) by lia.
        f_equal; lia. }
  pose proof (paper_main_gordon_reindex_continuous (S d) sigma2 F (proj1 H2) HC) as HC2.
  pose proof (paper_main_gordon_reindex_polynomial_bound (S d) sigma2 C p F H2 HB) as HB2.
  transitivity (gaussian_iterated_expectation (S d)
    (fun ys => F (paper_main_gordon_reindex sigma2 (S d) ys))).
  { rewrite (gaussian_iterated_move_last (S d) j _ C p Hj HC2 HB2).
    apply gaussian_iterated_expectation_ext; intros xs Hxs.
    rewrite (Hpt xs Hxs); reflexivity. }
  rewrite (gaussian_iterated_last_expectation d
    (fun ys => F (paper_main_gordon_reindex sigma2 (S d) ys))).
  rewrite (gaussian_iterated_last_expectation d F).
  transitivity (gaussian_iterated_expectation d
    (fun zs => gaussian_last_marginal F (paper_main_gordon_reindex sigma1 d zs))).
  { apply gaussian_iterated_expectation_ext; intros zs Hzs.
    unfold gaussian_last_marginal; f_equal; apply functional_extensionality; intros t.
    f_equal; apply nth_ext with (d := 0) (d' := 0).
    - rewrite length_app, !paper_main_gordon_reindex_length; simpl; lia.
    - intros n Hn; rewrite paper_main_gordon_reindex_length in Hn.
      rewrite paper_main_gordon_reindex_nth by exact Hn.
      unfold sigma2; destruct (Nat.ltb_spec n d) as [Hnd|Hnd].
      + pose proof (proj1 H1 n Hnd).
        rewrite app_nth1 by lia.
        rewrite app_nth1 by (rewrite paper_main_gordon_reindex_length; exact Hnd).
        rewrite paper_main_gordon_reindex_nth by exact Hnd; reflexivity.
      + assert (n = d) by lia; subst n.
        rewrite app_nth2 by lia.
        rewrite app_nth2 by (rewrite paper_main_gordon_reindex_length; lia).
        rewrite paper_main_gordon_reindex_length, Hzs, Nat.sub_diag; reflexivity. }
  exact (IH sigma1 (gaussian_last_marginal F) (C * gaussian_coordinate_weight_moment p) H1
    (gaussian_last_marginal_continuous d F C p HC HB)
    (gaussian_last_marginal_polynomial_bound d F C p HC HB)).
Qed.

(* The transpose of a row-major matrix. *)

Definition paper_main_gordon_transpose_index N M k : nat :=
  ((k mod N) * M + k / N)%nat.

Definition paper_main_gordon_transpose N M (xs : list R) : list R :=
  paper_main_gordon_reindex (paper_main_gordon_transpose_index N M) (M * N) xs.

Lemma paper_main_gordon_transpose_index_entry N M i j :
  (i < N)%nat -> (j < M)%nat ->
  paper_main_gordon_transpose_index N M (j * N + i) = (i * M + j)%nat.
Proof.
intros Hi Hj; unfold paper_main_gordon_transpose_index.
rewrite <- (Nat.div_unique (j * N + i) N j i Hi) by ring.
rewrite <- (Nat.mod_unique (j * N + i) N j i Hi) by ring.
reflexivity.
Qed.

Lemma paper_main_gordon_transpose_injective N M :
  (0 < N)%nat -> paper_main_gordon_injective_on (M * N) (paper_main_gordon_transpose_index N M).
Proof.
intros HN; split.
- intros k Hk; unfold paper_main_gordon_transpose_index.
  assert (Hm : (k mod N < N)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hd : (k / N < M)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
  nia.
- intros k l Hk Hl Heq; unfold paper_main_gordon_transpose_index in Heq.
  assert (Hdk : (k / N < M)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
  assert (Hdl : (l / N < M)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
  assert (E1 : (k / N = (k mod N * M + k / N) mod M)%nat)
    by (apply (Nat.mod_unique _ M (k mod N) (k / N)); [exact Hdk|ring]).
  assert (E2 : (k mod N = (k mod N * M + k / N) / M)%nat)
    by (apply (Nat.div_unique _ M (k mod N) (k / N)); [exact Hdk|ring]).
  assert (E3 : (l / N = (l mod N * M + l / N) mod M)%nat)
    by (apply (Nat.mod_unique _ M (l mod N) (l / N)); [exact Hdl|ring]).
  assert (E4 : (l mod N = (l mod N * M + l / N) / M)%nat)
    by (apply (Nat.div_unique _ M (l mod N) (l / N)); [exact Hdl|ring]).
  rewrite Heq in E1, E2.
  assert (Hq1 : (k / N = l / N)%nat) by congruence.
  assert (Hq2 : (k mod N = l mod N)%nat) by congruence.
  rewrite (Nat.div_mod k N), (Nat.div_mod l N) by lia.
  rewrite Hq1, Hq2; reflexivity.
Qed.

Lemma paper_main_gordon_transpose_length N M xs :
  length (paper_main_gordon_transpose N M xs) = (M * N)%nat.
Proof. apply paper_main_gordon_reindex_length. Qed.

Lemma paper_main_gordon_transpose_nth N M xs i j :
  (i < N)%nat -> (j < M)%nat ->
  List.nth (j * N + i) (paper_main_gordon_transpose N M xs) 0 = List.nth (i * M + j) xs 0.
Proof.
intros Hi Hj; unfold paper_main_gordon_transpose.
rewrite paper_main_gordon_reindex_nth by nia.
rewrite paper_main_gordon_transpose_index_entry by assumption; reflexivity.
Qed.

Theorem paper_main_gordon_transpose_regular N M F C p :
  (0 < N)%nat ->
  finite_joint_continuous (M * N) F -> finite_polynomial_bound (M * N) C p F ->
  finite_joint_continuous (N * M) (fun xs => F (paper_main_gordon_transpose N M xs)) /\
  finite_polynomial_bound (N * M) C p (fun xs => F (paper_main_gordon_transpose N M xs)).
Proof.
intros HN HC HB; rewrite (Nat.mul_comm N M); unfold paper_main_gordon_transpose; split.
- apply paper_main_gordon_reindex_continuous;
    [apply (proj1 (paper_main_gordon_transpose_injective N M HN))|exact HC].
- apply paper_main_gordon_reindex_polynomial_bound;
    [apply (paper_main_gordon_transpose_injective N M HN)|exact HB].
Qed.

Theorem paper_main_gordon_transpose_expectation N M F C p :
  (0 < N)%nat ->
  finite_joint_continuous (M * N) F -> finite_polynomial_bound (M * N) C p F ->
  gaussian_iterated_expectation (N * M) (fun xs => F (paper_main_gordon_transpose N M xs)) =
  gaussian_iterated_expectation (M * N) F.
Proof.
intros HN HC HB; rewrite (Nat.mul_comm N M).
exact (paper_main_gordon_reindex_expectation (M * N) _ F C p
  (paper_main_gordon_transpose_injective N M HN) HC HB).
Qed.
