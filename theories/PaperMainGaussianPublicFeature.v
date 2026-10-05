(* The Gaussian feature estimate on the public true-dimensional matrices. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix normedtype.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure lebesgue_measure.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums MatrixDefinitions
  TensorDefinitions GaussianProbabilityProductDefinitions PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainMatrixTransport
  PaperMainGordonOperatorNet PaperMainGaussianFeatureCoordinates
  PaperMainGaussianFeatureBounds PaperMainGaussianFeatureTail.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_public_gaussian_row n i xs : 'M[R]_(S n) :=
  paper_main_matrix_to_public n (paper_main_gaussian_feature_row n i xs).

Definition paper_main_public_gaussian_pairing n N u (T : 'M[R]_(S n)) xs :=
  finite_sum (fun i => u i*paper_main_pairing (paper_main_public_gaussian_row n i xs) T)
    (List.seq 0 N).

Lemma paper_main_public_gaussian_row_symmetric n i xs :
  paper_main_symmetric (paper_main_public_gaussian_row n i xs).
Proof.
apply paper_main_matrix_public_symmetric.
apply paper_main_gaussian_feature_row_symmetric.
Qed.

Lemma paper_main_public_gaussian_pairing_transport n N u (T : 'M[R]_(S n)) xs :
  paper_main_symmetric T ->
  paper_main_public_gaussian_pairing n N u T xs =
  paper_main_gaussian_feature_pairing n N u (paper_main_matrix_from_public n T) xs.
Proof.
intro HT.
unfold paper_main_public_gaussian_pairing, paper_main_gaussian_feature_pairing.
apply finite_sum_ext; intros i Hi.
rewrite paper_main_matrix_public_pairing; [apply paper_main_matrix_internal_symmetric; exact HT|].
by rewrite paper_main_matrix_public_roundtrip.
Qed.

Theorem paper_main_public_gaussian_feature_bound n N u (T : 'M[R]_(S n)) xs :
  List.length xs = Nat.mul N (paper_main_symmetric_dimension n) ->
  paper_main_symmetric T ->
  Rabs (sqrt(INR(S n))*paper_main_public_gaussian_pairing n N u T xs) <=
  sqrt 2*paper_main_gordon_operator_norm N (paper_main_symmetric_dimension n) xs *
    euclidean_norm u (List.seq 0 N)*paper_main_frobenius T.
Proof.
intros Hxs HT.
rewrite (paper_main_public_gaussian_pairing_transport n N u T xs HT).
rewrite <- (paper_main_matrix_internal_frobenius n T).
apply paper_main_gaussian_feature_normalized_bound; [exact Hxs|].
apply paper_main_matrix_internal_symmetric; exact HT.
Qed.

Theorem paper_main_public_gaussian_feature_exceptional_event n N t :
  Nat.lt 0 N -> 0 < t ->
  exists E : set ((N*paper_main_symmetric_dimension n).-tuple (measurableTypeR R)),
    measurable E /\
    (gaussian_product_law (N*paper_main_symmetric_dimension n) E <= (2*exp(-t))%:E)%E /\
    forall x, ~ E x -> forall u (T : 'M[R]_(S n)), paper_main_symmetric T ->
    Rabs (sqrt(INR(S n))*paper_main_public_gaussian_pairing n N u T (tval x)) <=
    (2*sqrt 2*paper_main_gaussian_operator_threshold N (paper_main_symmetric_dimension n) t)*
      euclidean_norm u (List.seq 0 N)*paper_main_frobenius T.
Proof.
intros HN Ht.
destruct (paper_main_gaussian_feature_exceptional_event n N t HN Ht) as [E [HE [HP Hbound]]].
exists E; split; [exact HE|]; split; [exact HP|].
intros x Hx u T HT.
rewrite (paper_main_public_gaussian_pairing_transport n N u T (tval x) HT).
rewrite <- (paper_main_matrix_internal_frobenius n T).
apply Hbound; [exact Hx|apply paper_main_matrix_internal_symmetric; exact HT].
Qed.
