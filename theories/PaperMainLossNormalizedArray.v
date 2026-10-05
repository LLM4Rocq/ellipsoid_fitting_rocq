(* The normalized soft minimum of a loss array over a finite prior.

   paper_main_loss_entropy_shift N beta I F xs = (F xs + ln |I| / beta) / N
   is regular (pmdf_regular) when F is, and its iterated Gaussian
   expectation is (E F + ln |I| / beta) / N. The normalized array
   paper_main_loss_normalized_array p N beta I ell is this shift of the soft
   minimum over j in I of paper_main_loss_array p N ell xs j
   (paper_main_loss_normalized_arrayE). Let N > 0, I be nonempty and
   beta > 0.
   - paper_main_loss_normalized_array_regular: if every ell i j is
     continuous with values in [0, 1], the normalized array is regular.
   - paper_main_loss_normalized_array_bounds: if every ell i j takes values
     in [0, 1], the normalized array lies in [0, 1].
   - paper_main_loss_normalized_array_gap: if every array value is at least
     N e, the normalized array is at least e.
   - paper_main_loss_normalized_array_witness: the normalized array is at
     most (array value at j) / N + ln |I| / (beta N) for every j in I. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions PaperMainDataFeatureMomentsCoordinates
  PaperMainLossArray PaperMainLossSoftNormalized.
Open Scope R_scope.

Definition paper_main_loss_entropy_shift N beta (I : list nat) (F : list R -> R) xs :=
  /INR N*(F xs+Rpower.ln(INR(List.length I))/beta).

Lemma paper_main_loss_entropy_shift_regular d N beta I F :
  pmdf_regular d F -> pmdf_regular d (paper_main_loss_entropy_shift N beta I F).
Proof.
intro HF; unfold paper_main_loss_entropy_shift; apply pmdf_regular_scale.
apply pmdf_regular_add; [exact HF|apply pmdf_regular_const].
Qed.

Lemma paper_main_loss_entropy_shift_expectation d N beta I F :
  gaussian_iterated_integrable d F ->
  gaussian_iterated_expectation d (paper_main_loss_entropy_shift N beta I F)=
  /INR N*(gaussian_iterated_expectation d F+Rpower.ln(INR(List.length I))/beta).
Proof.
intro HF; unfold paper_main_loss_entropy_shift.
pose proof(gaussian_iterated_constant d (Rpower.ln(INR(List.length I))/beta)) as [HC EC].
pose proof(gaussian_iterated_add d F (fun _ => Rpower.ln(INR(List.length I))/beta) HF HC) as [HA EA].
rewrite (proj2(gaussian_iterated_scale d _ (/INR N) HA)),EA,EC; reflexivity.
Qed.

Definition paper_main_loss_normalized_array p N beta I ell :=
  paper_main_loss_entropy_shift N beta I
    (paper_main_loss_array_soft p N beta (fun _ => 0) I ell).

Lemma paper_main_loss_normalized_array_regular p N beta I ell : I<>nil -> 0<beta ->
  (forall i j, (i<N)%nat -> In j I -> finite_joint_continuous p (ell i j)) ->
  (forall i j xs, (i<N)%nat -> In j I -> List.length xs=p -> 0<=ell i j xs<=1) ->
  pmdf_regular (Nat.mul N p) (paper_main_loss_normalized_array p N beta I ell).
Proof.
intros HI Hb HC HB; apply paper_main_loss_entropy_shift_regular.
apply paper_main_loss_array_soft_regular; assumption.
Qed.

Lemma paper_main_loss_normalized_arrayE p N beta I ell xs :
  paper_main_loss_normalized_array p N beta I ell xs=
  paper_main_loss_soft_normalized N beta (paper_main_loss_array p N ell xs) I.
Proof.
unfold paper_main_loss_normalized_array,paper_main_loss_entropy_shift,
  paper_main_loss_array_soft,paper_main_loss_soft_normalized.
assert (H : (fun j => 0+paper_main_loss_array p N ell xs j)=paper_main_loss_array p N ell xs)
  by (apply functional_extensionality; intros; ring).
rewrite H; reflexivity.
Qed.

Theorem paper_main_loss_normalized_array_bounds p N beta I ell : (0<N)%nat -> I<>nil -> 0<beta ->
  (forall i j xs, (i<N)%nat -> In j I -> List.length xs=p -> 0<=ell i j xs<=1) ->
  forall xs, List.length xs=Nat.mul N p ->
    0<=paper_main_loss_normalized_array p N beta I ell xs<=1.
Proof.
intros HN HI Hb HB xs Hxs; rewrite paper_main_loss_normalized_arrayE.
apply paper_main_loss_soft_normalized_bounds; try assumption.
intros j Hj; apply (paper_main_loss_array_bounds p N ell I HB xs j Hxs Hj).
Qed.

Theorem paper_main_loss_normalized_array_gap p N beta I ell xs e : (0<N)%nat -> I<>nil -> 0<beta ->
  (forall j, In j I -> INR N*e<=paper_main_loss_array p N ell xs j) ->
  e<=paper_main_loss_normalized_array p N beta I ell xs.
Proof.
intros HN HI Hb Hgap; rewrite paper_main_loss_normalized_arrayE.
apply paper_main_loss_soft_normalized_gap; assumption.
Qed.

Theorem paper_main_loss_normalized_array_witness p N beta I ell xs j :
  (0<N)%nat -> I<>nil -> 0<beta -> In j I ->
  paper_main_loss_normalized_array p N beta I ell xs<=
  /INR N*paper_main_loss_array p N ell xs j+Rpower.ln(INR(List.length I))/(beta*INR N).
Proof.
intros HN HI Hb Hj; rewrite paper_main_loss_normalized_arrayE.
pose proof(proj2(paper_main_loss_soft_normalized_minimum N beta (paper_main_loss_array p N ell xs) I HN Hb HI)) as H.
pose proof(finite_min_member (paper_main_loss_array p N ell xs) I j Hj) as HM.
assert (Hinv : 0<=/INR N) by (apply Rlt_le,Rinv_0_lt_compat,lt_0_INR; exact HN).
pose proof(Rmult_le_compat_l (/INR N) _ _ Hinv HM); lra.
Qed.
