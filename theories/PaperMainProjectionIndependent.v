(* Transport the comparison to two independent Gaussian coordinate blocks. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums
  GaussianProductDefinitions GaussianProduct GaussianLastDefinitions GaussianLastIntegration
  GaussianCovarianceLinear GaussianCovarianceEndpoints PaperMainGaussianSmoothCovariance
  PaperMainProjectionStein PaperMainProjectionImage PaperMainProjectionAlgebra
  PaperMainProjectionVariance PaperMainProjectionProduct PaperMainProjectionBlocks
  PaperMainProjectionComparison.
Open Scope R_scope.

Lemma paper_main_projection_left_pairing p q A B :
  paper_main_projection_pairing ((Nat.add p q))%coq_nat (paper_main_projection_left p A)
    (paper_main_projection_left p B)=paper_main_projection_pairing p A B.
Proof.
unfold paper_main_projection_pairing; apply paper_main_projection_sum_prefix.
- intros i Hi; apply paper_main_projection_sum_prefix.
  + intros j Hj; rewrite (paper_main_projection_left_inside p A i j Hi Hj)
      (paper_main_projection_left_inside p B i j Hi Hj); reflexivity.
  + intros j Hj HjD; rewrite (paper_main_projection_left_outside p A i j (or_intror Hj)); ring.
- intros i Hi HiD; rewrite <- (finite_sum_zero (List.seq 0 ((Nat.add p q)))).
  apply finite_sum_ext; intros j Hj; rewrite (paper_main_projection_left_outside p A i j (or_introl Hi)); ring.
Qed.

Lemma paper_main_projection_right_covariance p q c e :
  paper_main_projection_covariance ((Nat.add p q))%coq_nat (paper_main_projection_right p c)
    (paper_main_projection_right p e)=paper_main_projection_covariance q c e.
Proof.
unfold paper_main_projection_covariance; rewrite finite_sum_seq_split.
assert (H0 : finite_sum (fun i => paper_main_projection_right p c i*paper_main_projection_right p e i) (List.seq 0 p)=0).
{ rewrite <- (finite_sum_zero (List.seq 0 p)); apply finite_sum_ext; intros i Hi; apply in_seq in Hi.
  rewrite (paper_main_projection_right_inside p c i ltac:(lia)); ring. }
rewrite H0 Rplus_0_l; apply finite_sum_ext; intros j Hj; rewrite !paper_main_projection_right_shift; reflexivity.
Qed.

Lemma paper_main_projection_square_pairing d A :
  paper_main_projection_square_coefficients d A=paper_main_projection_pairing d A A.
Proof.
unfold paper_main_projection_square_coefficients,paper_main_projection_pairing.
apply finite_sum_ext; intros i Hi; apply finite_sum_ext; intros j Hj; ring.
Qed.
Lemma paper_main_projection_left_square p q A :
  paper_main_projection_square_coefficients ((Nat.add p q))%coq_nat (paper_main_projection_left p A)=
    paper_main_projection_square_coefficients p A.
Proof. rewrite !paper_main_projection_square_pairing paper_main_projection_left_pairing; reflexivity. Qed.

Lemma paper_main_projection_left_symmetric p q A :
  (forall i j, (i<p)%coq_nat -> (j<p)%coq_nat -> A i j=A j i) ->
  forall i j, (i<(Nat.add p q))%coq_nat -> (j<(Nat.add p q))%coq_nat ->
    paper_main_projection_left p A i j=paper_main_projection_left p A j i.
Proof.
intros HA i j Hi Hj; destruct(Nat.lt_ge_cases i p) as [Hip|Hip]; destruct(Nat.lt_ge_cases j p) as [Hjp|Hjp].
- rewrite (paper_main_projection_left_inside p A i j Hip Hjp)
    (paper_main_projection_left_inside p A j i Hjp Hip); apply HA; assumption.
- rewrite (paper_main_projection_left_outside p A i j (or_intror Hjp))
    (paper_main_projection_left_outside p A j i (or_introl Hjp)); reflexivity.
- rewrite (paper_main_projection_left_outside p A i j (or_introl Hip))
    (paper_main_projection_left_outside p A j i (or_intror Hip)); reflexivity.
- rewrite (paper_main_projection_left_outside p A i j (or_introl Hip))
    (paper_main_projection_left_outside p A j i (or_introl Hjp)); reflexivity.
Qed.

Lemma paper_main_projection_left_operator p q A eps :
  paper_main_projection_operator_bound p A eps ->
  paper_main_projection_operator_bound ((Nat.add p q))%coq_nat (paper_main_projection_left p A) eps.
Proof.
intros HO z.
assert (HE : finite_sum (fun i => (finite_sum (fun j => paper_main_projection_left p A i j*z j) (List.seq 0 ((Nat.add p q))))^2) (List.seq 0 ((Nat.add p q)))=
  finite_sum (fun i => (finite_sum (fun j => A i j*z j) (List.seq 0 p))^2) (List.seq 0 p)).
{ apply paper_main_projection_sum_prefix.
  - intros i Hi; f_equal; apply paper_main_projection_sum_prefix.
    + intros j Hj; rewrite (paper_main_projection_left_inside p A i j Hi Hj); reflexivity.
    + intros j Hj HjD; rewrite (paper_main_projection_left_outside p A i j (or_intror Hj)); ring.
  - intros i Hi HiD.
    assert (Hz : finite_sum (fun j => paper_main_projection_left p A i j*z j) (List.seq 0 ((Nat.add p q)))=0).
    { rewrite <- (finite_sum_zero (List.seq 0 ((Nat.add p q)))); apply finite_sum_ext; intros j Hj.
      rewrite (paper_main_projection_left_outside p A i j (or_introl Hi)); ring. }
    rewrite Hz; ring. }
rewrite HE; eapply Rle_trans; [apply HO|].
apply Rmult_le_compat_l; [apply pow2_ge_0|].
rewrite finite_sum_seq_split; assert (H0 : 0<=finite_sum (fun k => z ((Nat.add p k))%coq_nat^2) (List.seq 0 q)).
{ apply finite_sum_nonneg; intros; apply pow2_ge_0. }
lra.
Qed.

Lemma paper_main_projection_left_expectation p q K A F :
  gaussian_iterated_expectation ((Nat.add p q))%coq_nat (fun xs => F(paper_main_projection_image K
    (fun a => paper_main_projection_quadratic ((Nat.add p q))%coq_nat (paper_main_projection_left p (A a))) xs))=
  gaussian_iterated_expectation p (fun xs => F(paper_main_projection_image K
    (fun a => paper_main_projection_quadratic p (A a)) xs)).
Proof.
transitivity (gaussian_iterated_expectation ((Nat.add p q))%coq_nat (fun xs => F(paper_main_projection_image K
  (fun a => paper_main_projection_quadratic p (A a)) (List.firstn p xs)))).
- apply gaussian_iterated_expectation_ext; intros xs Hxs; f_equal.
  unfold paper_main_projection_image; apply map_ext; intro a; apply paper_main_projection_left_quadratic.
- rewrite gaussian_iterated_suffix_expectation; apply gaussian_iterated_expectation_ext; intros xs Hxs.
  unfold gaussian_suffix_marginal.
  transitivity (gaussian_iterated_expectation q (fun _ => F(paper_main_projection_image K
    (fun a => paper_main_projection_quadratic p (A a)) xs))).
  + apply gaussian_iterated_expectation_ext; intros ys Hys; rewrite <- Hxs; rewrite firstn_app_exact; reflexivity.
  + apply (proj2(gaussian_iterated_constant q _)).
Qed.

Lemma paper_main_projection_right_expectation p q K c F :
  gaussian_iterated_expectation ((Nat.add p q))%coq_nat (fun xs => F(paper_main_projection_image K
    (fun a => linear_form ((Nat.add p q))%coq_nat (paper_main_projection_right p (c a))) xs))=
  gaussian_iterated_expectation q (fun xs => F(paper_main_projection_image K (fun a => linear_form q (c a)) xs)).
Proof.
transitivity (gaussian_iterated_expectation ((Nat.add p q))%coq_nat (fun xs => F(paper_main_projection_image K
  (fun a => linear_form q (c a)) (List.skipn p xs)))).
- apply gaussian_iterated_expectation_ext; intros xs Hxs; f_equal.
  unfold paper_main_projection_image; apply map_ext; intro a; apply paper_main_projection_right_linear.
- rewrite gaussian_iterated_suffix_expectation.
  transitivity (gaussian_iterated_expectation p (fun _ => gaussian_iterated_expectation q
    (fun ys => F(paper_main_projection_image K (fun a => linear_form q (c a)) ys)))).
  + apply gaussian_iterated_expectation_ext; intros xs Hxs; unfold gaussian_suffix_marginal.
    apply gaussian_iterated_expectation_ext; intros ys Hys; rewrite <- Hxs; rewrite skipn_app_exact; reflexivity.
  + apply (proj2(gaussian_iterated_constant p _)).
Qed.

Theorem paper_main_projection_independent_comparison n q K A c F DF D2F C eps S :
  paper_main_gaussian_smooth_test K F DF D2F C 0 ->
  (forall a i j, (a<K)%coq_nat -> (i<=n)%coq_nat -> (j<=n)%coq_nat -> A a i j=A a j i) ->
  (forall a, (a<K)%coq_nat -> paper_main_projection_operator_bound (Datatypes.S n) (A a) eps) ->
  (forall a, (a<K)%coq_nat -> paper_main_projection_square_coefficients (Datatypes.S n) (A a)<=S^2) ->
  (forall a b, (a<K)%coq_nat -> (b<K)%coq_nat ->
    paper_main_projection_covariance q (c a) (c b)= 2*paper_main_projection_pairing (Datatypes.S n) (A a) (A b)) ->
  0<=eps -> 0<=S ->
  Rabs(gaussian_iterated_expectation (Datatypes.S n)
    (fun xs => F(paper_main_projection_image K (fun a => paper_main_projection_quadratic (Datatypes.S n) (A a)) xs))-
    gaussian_iterated_expectation q (fun xs => F(paper_main_projection_image K (fun a => linear_form q (c a)) xs)))<=
    INR K*(INR K*(2*C*eps*S)).
Proof.
intros HF HA HO HN HC Heps HS.
assert (Hsym : forall a i j, (a<K)%coq_nat -> (i<=(Nat.add n q))%coq_nat -> (j<=(Nat.add n q))%coq_nat ->
  paper_main_projection_left (Datatypes.S n) (A a) i j=paper_main_projection_left (Datatypes.S n) (A a) j i).
{ intros a i j Ha Hi Hj; apply (paper_main_projection_left_symmetric (Datatypes.S n) q (A a)); try lia.
  intros k l Hk Hl; apply HA; lia. }
pose proof(paper_main_projection_smooth_comparison ((Nat.add n q))%coq_nat K
  (fun a => paper_main_projection_left (Datatypes.S n) (A a))
  (fun a => paper_main_projection_right (Datatypes.S n) (c a)) F DF D2F C eps S
  HF Hsym ltac:(intros; apply (paper_main_projection_blocks_orthogonal (Datatypes.S n) q))
  ltac:(intros a Ha; apply (paper_main_projection_left_operator (Datatypes.S n) q); apply HO; exact Ha)
  ltac:(intros a Ha; rewrite (paper_main_projection_left_square (Datatypes.S n) q); apply HN; exact Ha)
  ltac:(intros a b Ha Hb; rewrite (paper_main_projection_right_covariance (Datatypes.S n) q)
    (paper_main_projection_left_pairing (Datatypes.S n) q); apply HC; assumption)
  Heps HS) as H.
rewrite (paper_main_projection_left_expectation (Datatypes.S n) q K A F)
  (paper_main_projection_right_expectation (Datatypes.S n) q K c F) in H.
exact H.
Qed.
