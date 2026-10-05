(* Sums of row losses over the blocks of a list, and their soft minimum.
   For a list xs of N blocks of length p,
     paper_main_loss_array p N ell xs j = sum_(i < N) ell i j (block i),
   and paper_main_loss_array_soft p N beta f I ell xs is the soft minimum
   over j in I of f j + paper_main_loss_array p N ell xs j.
   - paper_main_loss_array_bounds: if every ell i j takes values in [0, 1],
     the sum takes values in [0, N].
   - paper_main_loss_array_continuous: if every ell i j is continuous, so is
     the sum, as a function of the N p coordinates.
   - paper_main_loss_array_soft_regular: for nonempty I and beta > 0, under
     both hypotheses the soft minimum is continuous and bounded by
     |soft_min beta f I| + N, so it satisfies pmdf_regular (continuity and
     a polynomial bound). *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions SoftExtrema
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianPermutationContinuity GaussianBlockPermutation PaperMainDataFeatureMomentsCoordinates
  PaperMainGaussianSmoothCalculus PaperMainGordonContinuity PaperMainSoftLipschitz.
Open Scope R_scope.

Fixpoint paper_main_loss_array p N (ell : nat -> nat -> list R -> R) (xs : list R) (j : nat) :=
  match N with O => 0 | S k => ell 0%nat j (List.firstn p xs)+
    paper_main_loss_array p k (fun i => ell (S i)) (List.skipn p xs) j end.

Definition paper_main_loss_array_soft p N beta f I ell xs :=
  soft_min beta (fun j => f j+paper_main_loss_array p N ell xs j) I.

Lemma paper_main_loss_firstn_length p m (xs : list R) : List.length xs=Nat.add p m ->
  List.length(List.firstn p xs)=p.
Proof. intro H; rewrite List.length_firstn H; apply Nat.min_l; lia. Qed.
Lemma paper_main_loss_skipn_length p m (xs : list R) : List.length xs=Nat.add p m ->
  List.length(List.skipn p xs)=m.
Proof. intro H; rewrite List.length_skipn H; lia. Qed.

Lemma paper_main_loss_firstn_continuous p m F : finite_joint_continuous p F ->
  finite_joint_continuous (Nat.add p m) (fun xs => F(List.firstn p xs)).
Proof.
intro HF; apply (finite_joint_continuous_list_map (Nat.add p m) p (List.firstn p) F).
- intros xs Hxs; apply (paper_main_loss_firstn_length p m); exact Hxs.
- intros eps xs ys Hx Hy H; apply block_firstn_forall2; exact H.
- exact HF.
Qed.
Lemma paper_main_loss_skipn_continuous p m F : finite_joint_continuous m F ->
  finite_joint_continuous (Nat.add p m) (fun xs => F(List.skipn p xs)).
Proof.
intro HF; apply (finite_joint_continuous_list_map (Nat.add p m) m (List.skipn p) F).
- intros xs Hxs; apply (paper_main_loss_skipn_length p m); exact Hxs.
- intros eps xs ys Hx Hy H; apply block_skipn_forall2; exact H.
- exact HF.
Qed.

Lemma paper_main_loss_array_append p N ell xs ys j : List.length xs=p ->
  paper_main_loss_array p (S N) ell (List.app xs ys) j=
  ell 0%nat j xs+paper_main_loss_array p N (fun i => ell(S i)) ys j.
Proof.
intro Hxs; simpl paper_main_loss_array.
rewrite <-Hxs; rewrite firstn_app skipn_app firstn_all skipn_all Nat.sub_diag.
simpl; rewrite app_nil_r; reflexivity.
Qed.

Theorem paper_main_loss_array_bounds p N ell I :
  (forall i j xs, (i<N)%coq_nat -> In j I -> List.length xs=p -> 0<=ell i j xs<=1) ->
  forall xs j, List.length xs=Nat.mul N p -> In j I ->
    0<=paper_main_loss_array p N ell xs j<=INR N.
Proof.
revert ell; induction N as [|N IH]; intros ell HE xs j Hxs Hj; [simpl; lra|].
assert (Hfirst : List.length(List.firstn p xs)=p) by
  (apply (paper_main_loss_firstn_length p (Nat.mul N p)); exact Hxs).
assert (Hrest : List.length(List.skipn p xs)=Nat.mul N p) by
  (apply paper_main_loss_skipn_length; exact Hxs).
pose proof(HE 0%nat j (List.firstn p xs) ltac:(lia) Hj Hfirst) as HH.
pose proof(IH (fun i => ell(S i)) ltac:(intros; apply HE; try assumption; lia)
  (List.skipn p xs) j Hrest Hj) as HT.
change (0<=ell 0%nat j (List.firstn p xs)+paper_main_loss_array p N (fun i => ell(S i)) (List.skipn p xs) j<=INR(S N)).
rewrite S_INR; lra.
Qed.

Theorem paper_main_loss_array_continuous p N ell I :
  (forall i j, (i<N)%coq_nat -> In j I -> finite_joint_continuous p (ell i j)) ->
  forall j, In j I -> finite_joint_continuous (Nat.mul N p) (fun xs => paper_main_loss_array p N ell xs j).
Proof.
revert ell; induction N as [|N IH]; intros ell HE j Hj.
- change (finite_joint_continuous 0 (fun _ => 0)); apply finite_joint_continuous_constant.
-
change (finite_joint_continuous (Nat.add p (Nat.mul N p)) (fun xs =>
  ell 0%nat j (List.firstn p xs)+paper_main_loss_array p N (fun i => ell(S i)) (List.skipn p xs) j)).
apply finite_joint_continuous_add.
- apply paper_main_loss_firstn_continuous; apply HE; [lia|exact Hj].
- apply (paper_main_loss_skipn_continuous p (Nat.mul N p)
    (fun ys => paper_main_loss_array p N (fun i => ell(S i)) ys j)).
  apply (IH (fun i => ell(S i))); [|exact Hj].
  intros i k Hi Hk; apply HE; [lia|exact Hk].
Qed.

Theorem paper_main_loss_array_soft_regular p N beta f I ell : I<>nil -> 0<beta ->
  (forall i j, (i<N)%coq_nat -> In j I -> finite_joint_continuous p (ell i j)) ->
  (forall i j xs, (i<N)%coq_nat -> In j I -> List.length xs=p -> 0<=ell i j xs<=1) ->
  pmdf_regular (Nat.mul N p) (paper_main_loss_array_soft p N beta f I ell).
Proof.
intros HI Hb HC HB; split.
- unfold paper_main_loss_array_soft,soft_min.
  replace (fun xs => -soft_max beta (fun j => -(f j+paper_main_loss_array p N ell xs j)) I)
    with (fun xs => (-1)*soft_max beta (fun j => -(f j+paper_main_loss_array p N ell xs j)) I)
    by (apply functional_extensionality; intros; ring).
  apply finite_joint_continuous_scale; apply paper_main_gordon_soft_max_continuous; [exact HI|].
  intros j Hj; replace (fun xs => -(f j+paper_main_loss_array p N ell xs j))
    with (fun xs => (-1)*(f j+paper_main_loss_array p N ell xs j))
    by (apply functional_extensionality; intros; ring).
  apply finite_joint_continuous_scale; apply finite_joint_continuous_add;
    [apply finite_joint_continuous_constant|apply (paper_main_loss_array_continuous p N ell I HC); exact Hj].
- exists (Rabs(soft_min beta f I)+INR N),0%nat.
  apply paper_main_polynomial_zero_bound; split; [pose proof(Rabs_pos(soft_min beta f I)); pose proof(pos_INR N); lra|].
  intros xs Hxs.
  assert (Hdiff : Rabs(paper_main_loss_array_soft p N beta f I ell xs-soft_min beta f I)<=INR N).
  { unfold paper_main_loss_array_soft; apply paper_main_soft_min_lipschitz; [exact Hb|exact HI|].
    intros j Hj; pose proof(paper_main_loss_array_bounds p N ell I HB xs j Hxs Hj) as HH.
    replace (f j+paper_main_loss_array p N ell xs j-f j) with (paper_main_loss_array p N ell xs j) by ring.
    rewrite Rabs_pos_eq; lra. }
  pose proof(Rabs_triang (paper_main_loss_array_soft p N beta f I ell xs-soft_min beta f I) (soft_min beta f I)) as HH.
  replace (paper_main_loss_array_soft p N beta f I ell xs-soft_min beta f I+soft_min beta f I)
    with (paper_main_loss_array_soft p N beta f I ell xs) in HH by ring; lra.
Qed.
