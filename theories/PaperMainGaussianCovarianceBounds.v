(* Gaussian vectors with the same covariance on the first K coordinates give
   the same expectation to a continuous, polynomially bounded test. For a
   loading P with p columns, let P xs be the list of the K values
   gaussian_covariance_row p P a xs. If the covariance entries
   gaussian_covariance_entry of P and Q agree for a, b < K, then
     E_p f (P xs) = E_q f (Q ys)
   (paper_main_covariance_equal_expectation). The proof reads both sides as
   integrals against gauss p and gauss q of the library (GaussianLawBridge):
   P (list_of_row x) is list_of_row (x *m A) for the matrix A of the loading
   (paper_main_covariance_image_row), A^T *m A is the matrix of the
   covariance entries (paper_main_covariance_gram), and the law of x *m A
   depends only on A^T *m A (integral_gauss_mulmx). The proof does not use
   the derivatives of f; the section keeps them as hypotheses so that the
   statement is unchanged. *)
From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianCovarianceDefinitions
  GaussianCovarianceSums GaussianCovarianceDomains GaussianProbabilityProductDefinitions.
Open Scope R_scope.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis Require Import measurable_matrix gauss gauss_law.
From EllipsoidFitting Require Import GaussianLawBridge.
From EllipsoidFitting Require Import RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope classical_set_scope.
Local Notation RR := (R : realType).

Lemma paper_main_covariance_finite_sum n (g : nat -> R) :
  finite_sum g (List.seq 0 n) = (\sum_(i < n) g i)%R.
Proof.
elim: n g => [|n IH] g; first by rewrite big_ord0.
rewrite big_ord_recl /= finite_sum_seq_shift.
change (g 0%nat + finite_sum (fun i => g (S i)) (List.seq 0 n) =
  g 0%nat + (\sum_(i < n) g (S i))%R).
by rewrite IH.
Qed.

(* The matrix of a loading: column a holds the coefficients of row a. *)
Definition paper_main_covariance_mx p K (P : nat -> nat -> R) : 'M[RR]_(p, K) :=
  (\matrix_(i, a) P a i)%R.

Lemma paper_main_covariance_image_row K p P (x : 'rV[RR]_p) :
  gaussian_covariance_image K p P (list_of_row x) =
  list_of_row (x *m paper_main_covariance_mx p K P)%R.
Proof.
apply: (nth_ext _ _ 0 0).
  by rewrite /gaussian_covariance_image length_map length_seq list_of_row_length.
move=> a; rewrite /gaussian_covariance_image length_map length_seq => /ssrnat.ltP aK.
rewrite (nth_map_seq _ _ _ (elimT ssrnat.ltP aK)).
have -> : a = Ordinal aK by [].
rewrite list_of_row_nth /gaussian_covariance_row finite_sum_seqE !mxE.
by apply: eq_bigr => i _; rewrite list_of_row_nth mxE mulrC.
Qed.

Lemma paper_main_covariance_gram K p P (a b : 'I_K) :
  ((paper_main_covariance_mx p K P)^T *m paper_main_covariance_mx p K P)%R a b =
  gaussian_covariance_entry p P a b.
Proof.
rewrite /gaussian_covariance_entry finite_sum_seqE !mxE.
by apply: eq_bigr => i _; rewrite !mxE.
Qed.

Section SmoothFunction.
Variables (K : nat) (f : list R -> R) (Df : nat -> list R -> R)
  (D2f : nat -> nat -> list R -> R) (C : R) (r : nat).
Hypothesis Hf : finite_joint_continuous K f.
Hypothesis HD : forall a, (a < K)%coq_nat ->
  finite_coordinate_derivative K a f (Df a).
Hypothesis HDc : forall a, (a < K)%coq_nat ->
  finite_joint_continuous K (Df a).
Hypothesis HD2 : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  finite_coordinate_derivative K b (Df a) (D2f a b).
Hypothesis HD2c : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  finite_joint_continuous K (D2f a b).
Hypothesis Hfb : finite_polynomial_bound K C r f.
Hypothesis HDb : forall a, (a < K)%coq_nat ->
  finite_polynomial_bound K C r (Df a).
Hypothesis HD2b : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  finite_polynomial_bound K C r (D2f a b).

Theorem paper_main_covariance_equal_expectation p q P Q :
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    gaussian_covariance_entry p P a b = gaussian_covariance_entry q Q a b) ->
  gaussian_iterated_expectation p (fun xs => f (gaussian_covariance_image K p P xs)) =
  gaussian_iterated_expectation q (fun ys => f (gaussian_covariance_image K q Q ys)).
Proof using Hf HD HDc HD2 HD2c Hfb HDb HD2b.
move=> Hcov.
have [MP [HMP HP]] := finite_matrix_bound P K p.
have [MQ [HMQ HQ]] := finite_matrix_bound Q K q.
have [cP bP] := gaussian_covariance_image_regular K p P MP f C r HMP HP Hf Hfb.
have [cQ bQ] := gaussian_covariance_image_regular K q Q MQ f C r HMQ HQ Hf Hfb.
rewrite (proj2 (gaussian_iterated_expectation_gauss_poly _ _ _ _ cP bP)).
rewrite (proj2 (gaussian_iterated_expectation_gauss_poly _ _ _ _ cQ bQ)).
under eq_Rintegral do rewrite paper_main_covariance_image_row.
under [RHS]eq_Rintegral do rewrite paper_main_covariance_image_row.
rewrite /Rintegral; congr fine.
apply: (integral_gauss_mulmx (f := fun z : 'rV[RR]_K => (f (list_of_row z))%:E)).
  apply/matrixP => a b; rewrite !paper_main_covariance_gram.
  by apply: Hcov; apply/ssrnat.ltP.
apply/measurable_EFinP; apply: continuous_measurable_mx.
exact: list_of_row_continuous.
Qed.

End SmoothFunction.

(* The same for the probabilities of the events S (g (P xs)), for g
   continuous and S measurable. *)
Lemma paper_main_covariance_event p K P (g : list R -> R)
    (S : set (measurableTypeR R)) :
  finite_joint_continuous K g -> measurable S ->
  gaussian_product_law p [set t | S (g (gaussian_covariance_image K p P (tval t)))] =
  gauss p [set x : 'rV[RR]_p |
    [set z : 'rV[RR]_K | S (g (list_of_row z))] (x *m paper_main_covariance_mx p K P)%R].
Proof.
move=> cg mS.
have mY : measurable [set z : 'rV[RR]_K | S (g (list_of_row z))].
  have := continuous_measurable_mx (list_of_row_continuous K g cg) measurableT mS.
  by rewrite setTI.
have mX : measurable [set x : 'rV[RR]_p |
    [set z : 'rV[RR]_K | S (g (list_of_row z))] (x *m paper_main_covariance_mx p K P)%R].
  have mA : measurable_fun [set: 'rV[RR]_p] (fun x => x *m paper_main_covariance_mx p K P)%R.
    by apply: measurable_mulmx => //; exact: measurable_cst.
  by have := mA measurableT _ mY; rewrite setTI.
rewrite (gauss_gaussian_product_law _ _ mX).
congr (gaussian_product_law p _); apply/seteqP; split => t /=;
  by rewrite -paper_main_covariance_image_row list_of_row_of_tuple.
Qed.

Theorem paper_main_covariance_equal_law p q K P Q (g : list R -> R)
    (S : set (measurableTypeR R)) :
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    gaussian_covariance_entry p P a b = gaussian_covariance_entry q Q a b) ->
  finite_joint_continuous K g -> measurable S ->
  gaussian_product_law p [set t | S (g (gaussian_covariance_image K p P (tval t)))] =
  gaussian_product_law q [set t | S (g (gaussian_covariance_image K q Q (tval t)))].
Proof.
move=> Hcov cg mS.
rewrite (paper_main_covariance_event p K P g S cg mS).
rewrite (paper_main_covariance_event q K Q g S cg mS).
apply: gauss_mulmx_law.
  apply/matrixP => a b; rewrite !paper_main_covariance_gram.
  by apply: Hcov; apply/ssrnat.ltP.
have := continuous_measurable_mx (list_of_row_continuous K g cg) measurableT mS.
by rewrite setTI.
Qed.
