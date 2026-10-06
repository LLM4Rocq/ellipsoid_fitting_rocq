(* Repeated row replacement with a bound uniform over finite priors. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.Coordinate.PolynomialContinuity Data.FeatureMomentsCoordinates
  Radius.ExponentialMoments Loss.Array Loss.SoftCost Loss.BlockComparison.
Open Scope R_scope.

Definition paper_main_loss_mixed p q N beta f I (h : nat -> list R -> R)
  (ell : nat -> nat -> list R -> R) xs :=
  soft_min beta (fun j => f j+(h j (List.firstn p xs)+
    paper_main_loss_array q N ell (List.skipn p xs) j)) I.

Lemma paper_main_loss_mixed_regular p q N beta f I h ell : I<>nil -> 0<beta ->
  (forall j, In j I -> finite_joint_continuous p (h j)) ->
  (forall j xs, In j I -> List.length xs=p -> 0<=h j xs<=1) ->
  (forall i j, (i<N)%coq_nat -> In j I -> finite_joint_continuous q (ell i j)) ->
  (forall i j xs, (i<N)%coq_nat -> In j I -> List.length xs=q -> 0<=ell i j xs<=1) ->
  pmdf_regular (Nat.add p (Nat.mul N q)) (paper_main_loss_mixed p q N beta f I h ell).
Proof.
intros HI Hb HC HB HEC HEB; unfold paper_main_loss_mixed.
apply (paper_main_loss_soft_regular _ _ _ _ _ (1+INR N)); [exact HI|exact Hb|pose proof(pos_INR N); lra| |].
- intros j Hj; apply finite_joint_continuous_add.
  + apply paper_main_loss_firstn_continuous; apply HC; exact Hj.
  + apply (paper_main_loss_skipn_continuous p (Nat.mul N q)
      (fun ys => paper_main_loss_array q N ell ys j)).
    apply (paper_main_loss_array_continuous q N ell I HEC); exact Hj.
- intros j xs Hj Hxs.
  pose proof(HB j (List.firstn p xs) Hj (paper_main_loss_firstn_length p (Nat.mul N q) xs Hxs)) as H1.
  pose proof(paper_main_loss_array_bounds q N ell I HEB (List.skipn p xs) j
    (paper_main_loss_skipn_length p (Nat.mul N q) xs Hxs) Hj) as H2.
  rewrite Rabs_pos_eq; lra.
Qed.

Lemma paper_main_loss_mixed_append p q N beta f I h ell xs ys : List.length xs=p ->
  paper_main_loss_mixed p q N beta f I h ell (List.app xs ys)=
  paper_main_loss_array_soft q N beta (fun j => f j+h j xs) I ell ys.
Proof.
intro Hxs; unfold paper_main_loss_mixed,paper_main_loss_array_soft.
rewrite (maximum_radius_firstn_append p xs ys Hxs) (maximum_radius_skipn_append p xs ys Hxs).
f_equal; apply functional_extensionality; intro j; ring.
Qed.

Lemma paper_main_loss_mixed_first p q N beta f I h ell xs ys : List.length xs=p ->
  paper_main_loss_mixed p q N beta f I h ell (List.app xs ys)=
  soft_min beta (fun j => (f j+paper_main_loss_array q N ell ys j)+h j xs) I.
Proof.
intro Hxs; rewrite (paper_main_loss_mixed_append _ _ _ _ _ _ _ _ _ _ Hxs).
unfold paper_main_loss_array_soft; f_equal; apply functional_extensionality; intro j; ring.
Qed.

Lemma paper_main_loss_array_first p N beta f I ell xs ys : List.length xs=p ->
  paper_main_loss_array_soft p (S N) beta f I ell (List.app xs ys)=
  soft_min beta (fun j => (f j+paper_main_loss_array p N (fun i => ell(S i)) ys j)+ell 0%nat j xs) I.
Proof.
intro Hxs; unfold paper_main_loss_array_soft.
f_equal; apply functional_extensionality; intro j.
rewrite (paper_main_loss_array_append p N ell xs ys j Hxs); ring.
Qed.

Theorem paper_main_loss_array_comparison p q N beta I ellQ ellG B : I<>nil -> 0<beta ->
  (forall i j, (i<N)%coq_nat -> In j I -> finite_joint_continuous p (ellQ i j)) ->
  (forall i j xs, (i<N)%coq_nat -> In j I -> List.length xs=p -> 0<=ellQ i j xs<=1) ->
  (forall i j, (i<N)%coq_nat -> In j I -> finite_joint_continuous q (ellG i j)) ->
  (forall i j xs, (i<N)%coq_nat -> In j I -> List.length xs=q -> 0<=ellG i j xs<=1) ->
  (forall i f, (i<N)%coq_nat ->
    Rabs(gaussian_iterated_expectation p (fun xs => soft_min beta (fun j => f j+ellQ i j xs) I)-
      gaussian_iterated_expectation q (fun xs => soft_min beta (fun j => f j+ellG i j xs) I))<=B) ->
  forall f, Rabs(gaussian_iterated_expectation (Nat.mul N p) (paper_main_loss_array_soft p N beta f I ellQ)-
    gaussian_iterated_expectation (Nat.mul N q) (paper_main_loss_array_soft q N beta f I ellG))<=INR N*B.
Proof.
intros HI Hb; revert ellQ ellG; induction N as [|N IH]; intros ellQ ellG HQC HQB HGC HGB HR f.
- change (Rabs(soft_min beta (fun j => f j+0) I-soft_min beta (fun j => f j+0) I)<=0*B).
  replace (soft_min beta (fun j => f j+0) I-soft_min beta (fun j => f j+0) I) with 0 by ring.
  rewrite Rabs_R0; lra.
- assert (HQtC : forall i j, (i<N)%coq_nat -> In j I -> finite_joint_continuous p (ellQ(S i) j))
    by (intros; apply HQC; try assumption; lia).
  assert (HQtB : forall i j xs, (i<N)%coq_nat -> In j I -> List.length xs=p -> 0<=ellQ(S i) j xs<=1)
    by (intros; apply HQB; try assumption; lia).
  assert (HGtC : forall i j, (i<N)%coq_nat -> In j I -> finite_joint_continuous q (ellG(S i) j))
    by (intros; apply HGC; try assumption; lia).
  assert (HGtB : forall i j xs, (i<N)%coq_nat -> In j I -> List.length xs=q -> 0<=ellG(S i) j xs<=1)
    by (intros; apply HGB; try assumption; lia).
  assert (HQ0C : forall j, In j I -> finite_joint_continuous p (ellQ 0%nat j))
    by (intros; apply HQC; try assumption; lia).
  assert (HQ0B : forall j xs, In j I -> List.length xs=p -> 0<=ellQ 0%nat j xs<=1)
    by (intros; apply HQB; try assumption; lia).
  assert (HG0C : forall j, In j I -> finite_joint_continuous q (ellG 0%nat j))
    by (intros; apply HGC; try assumption; lia).
  assert (HG0B : forall j xs, In j I -> List.length xs=q -> 0<=ellG 0%nat j xs<=1)
    by (intros; apply HGB; try assumption; lia).
  pose proof(paper_main_loss_array_soft_regular p (S N) beta f I ellQ HI Hb HQC HQB) as HQR.
  pose proof(paper_main_loss_array_soft_regular q (S N) beta f I ellG HI Hb HGC HGB) as HGR.
  pose proof(paper_main_loss_mixed_regular q p N beta f I (ellG 0%nat) (fun i => ellQ(S i))
    HI Hb HG0C HG0B HQtC HQtB) as HMR.
  set (M := paper_main_loss_mixed q p N beta f I (ellG 0%nat) (fun i => ellQ(S i))) in *.
  assert (Hfirst : Rabs(gaussian_iterated_expectation (Nat.mul (S N) p)
    (paper_main_loss_array_soft p (S N) beta f I ellQ)-
    gaussian_iterated_expectation (Nat.add q (Nat.mul N p)) M)<=B).
  { apply (paper_main_loss_conditional_prefix_comparison p q (Nat.mul N p)); [exact HQR|exact HMR|].
    intros ys Hys.
    assert (EQ : gaussian_iterated_expectation p (fun xs => paper_main_loss_array_soft p (S N) beta f I ellQ (List.app xs ys))=
      gaussian_iterated_expectation p (fun xs => soft_min beta
        (fun j => (f j+paper_main_loss_array p N (fun i => ellQ(S i)) ys j)+ellQ 0%nat j xs) I)).
    { apply gaussian_iterated_expectation_ext; intros xs Hxs; apply paper_main_loss_array_first; exact Hxs. }
    assert (EG : gaussian_iterated_expectation q (fun xs => M(List.app xs ys))=
      gaussian_iterated_expectation q (fun xs => soft_min beta
        (fun j => (f j+paper_main_loss_array p N (fun i => ellQ(S i)) ys j)+ellG 0%nat j xs) I)).
    { apply gaussian_iterated_expectation_ext; intros xs Hxs; unfold M; apply paper_main_loss_mixed_first; exact Hxs. }
    rewrite EQ EG; apply HR; lia. }
  assert (Htail : Rabs(gaussian_iterated_expectation (Nat.add q (Nat.mul N p)) M-
    gaussian_iterated_expectation (Nat.mul (S N) q)
      (paper_main_loss_array_soft q (S N) beta f I ellG))<=INR N*B).
  { apply (paper_main_loss_conditional_suffix_comparison q (Nat.mul N p) (Nat.mul N q)); [exact HMR|exact HGR|].
    intros xs Hxs.
    assert (EQ : gaussian_iterated_expectation (Nat.mul N p) (fun ys => M(List.app xs ys))=
      gaussian_iterated_expectation (Nat.mul N p)
        (paper_main_loss_array_soft p N beta (fun j => f j+ellG 0%nat j xs) I (fun i => ellQ(S i)))).
    { apply gaussian_iterated_expectation_ext; intros ys Hys; unfold M; apply paper_main_loss_mixed_append; exact Hxs. }
    assert (EG : gaussian_iterated_expectation (Nat.mul N q)
      (fun ys => paper_main_loss_array_soft q (S N) beta f I ellG (List.app xs ys))=
      gaussian_iterated_expectation (Nat.mul N q)
        (paper_main_loss_array_soft q N beta (fun j => f j+ellG 0%nat j xs) I (fun i => ellG(S i)))).
    { apply gaussian_iterated_expectation_ext; intros ys Hys; unfold paper_main_loss_array_soft.
      f_equal; apply functional_extensionality; intro j.
      rewrite (paper_main_loss_array_append q N ellG xs ys j Hxs); ring. }
    rewrite EQ EG; apply IH; try assumption.
    intros i g Hi; apply HR; lia. }
  rewrite S_INR.
  set (X := gaussian_iterated_expectation (Nat.mul (S N) p)
    (paper_main_loss_array_soft p (S N) beta f I ellQ)) in *.
  set (Y := gaussian_iterated_expectation (Nat.mul (S N) q)
    (paper_main_loss_array_soft q (S N) beta f I ellG)) in *.
  set (Z := gaussian_iterated_expectation (Nat.add q (Nat.mul N p)) M) in *.
  replace (X-Y) with ((X-Z)+(Z-Y)) by ring.
  pose proof(Rabs_triang (X-Z) (Z-Y)); nra.
Qed.
