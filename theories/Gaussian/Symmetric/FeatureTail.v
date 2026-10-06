(* Measurable exceptional events for the normalized symmetric Gaussian map.
   This is a non-sharp bound with explicit numerical constants. *)
From Stdlib Require Import Reals List Lia Lra Psatz Classical_Prop.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval normedtype.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure lebesgue_measure.
From EllipsoidFitting Require Import Soft.Definitions Matrix.Definitions
  Tensor.Definitions GaussianProbabilityProductDefinitions Gordon.Entropy
  Gordon.OperatorNet Gaussian.Tail.Operator Gaussian.Symmetric.Coordinates
  Gaussian.Symmetric.FeatureBounds.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_operator_threshold N M t :=
  sqrt (2*(paper_main_gordon_entropy_constant (1/4)*(INR N+INR M)+t)).

Lemma paper_main_gaussian_entropy_positive :
  0 < paper_main_gordon_entropy_constant (1/4).
Proof.
unfold paper_main_gordon_entropy_constant.
assert (H : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
nra.
Qed.

Lemma paper_main_gaussian_operator_threshold_positive N M t :
  0 < t -> 0 < paper_main_gaussian_operator_threshold N M t.
Proof.
intro Ht.
unfold paper_main_gaussian_operator_threshold; apply sqrt_lt_R0.
pose proof paper_main_gaussian_entropy_positive.
pose proof (pos_INR N); pose proof (pos_INR M); nra.
Qed.

Lemma paper_main_gaussian_operator_threshold_square N M t :
  0 < t ->
  (paper_main_gaussian_operator_threshold N M t)^2 =
  2*(paper_main_gordon_entropy_constant (1/4)*(INR N+INR M)+t).
Proof.
intro Ht.
unfold paper_main_gaussian_operator_threshold; apply pow2_sqrt.
pose proof paper_main_gaussian_entropy_positive.
pose proof (pos_INR N); pose proof (pos_INR M); nra.
Qed.

Theorem paper_main_gaussian_operator_exponential_tail N M t :
  Nat.lt 0 N -> Nat.lt 0 M -> 0 < t ->
  (gaussian_product_law (N*M)
    [set x | Rlt (2*paper_main_gaussian_operator_threshold N M t)
      (paper_main_gaussian_operator_random N M x)] <= (2*exp(-t))%:E)%E.
Proof.
intros HN HM Ht.
pose proof (paper_main_gaussian_operator_tail N M (paper_main_gaussian_operator_threshold N M t) HN HM (paper_main_gaussian_operator_threshold_positive N M t Ht)) as H.
rewrite (paper_main_gaussian_operator_threshold_square N M t Ht) in H.
replace (paper_main_gordon_entropy_constant (1/4)*(INR N+INR M) -
 2*(paper_main_gordon_entropy_constant (1/4)*(INR N+INR M)+t)/2) with (-t) in H by field.
exact H.
Qed.

Theorem paper_main_gaussian_feature_exceptional_event n N t :
  Nat.lt 0 N -> 0 < t ->
  exists E : set ((N*paper_main_symmetric_dimension n).-tuple (measurableTypeR R)),
    measurable E /\
    (gaussian_product_law (N*paper_main_symmetric_dimension n) E <= (2*exp(-t))%:E)%E /\
    forall x, ~ E x -> forall u (T : matrix n), symmetric_matrix n T ->
    Rabs (sqrt(INR(S n))*paper_main_gaussian_feature_pairing n N u T (tval x)) <=
    (2*sqrt 2*paper_main_gaussian_operator_threshold N (paper_main_symmetric_dimension n) t) *
      euclidean_norm u (List.seq 0 N) * (`|T|)%R.
Proof.
intros HN Ht.
exists [set x | Rlt (2*paper_main_gaussian_operator_threshold N (paper_main_symmetric_dimension n) t)
 (paper_main_gaussian_operator_random N (paper_main_symmetric_dimension n) x)].
split; [apply paper_main_gaussian_operator_tail_measurable|].
split.
- apply paper_main_gaussian_operator_exponential_tail; [exact HN|unfold paper_main_symmetric_dimension; lia|exact Ht].
- intros x Hx u T HT.
  apply paper_main_gaussian_feature_normalized_good.
  + exact: size_tuple.
  + apply Rnot_lt_le; exact Hx.
  + exact HT.
Qed.
