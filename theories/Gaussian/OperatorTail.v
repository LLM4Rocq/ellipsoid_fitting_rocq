(* A dimension-sensitive upper tail for the genuine Gaussian operator norm. *)
From Stdlib Require Import Reals List Lia Lra Psatz Classical_Prop.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure lebesgue_measure.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability Gordon.ProcessCovariance Gordon.Scalar
  Gordon.Entropy Gordon.OperatorNet Gordon.OperatorContinuity Gaussian.Union
  Gaussian.MatrixTail.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_operator_random N M
    (x : (N*M).-tuple (measurableTypeR R)) : measurableTypeR R :=
  paper_main_gordon_operator_norm N M (tval x).

Lemma paper_main_gaussian_operator_measurable N M :
  measurable_fun [set: (N*M).-tuple (measurableTypeR R)] (paper_main_gaussian_operator_random N M).
Proof.
exact: (gpp_joint_measurable (N*M) _ (paper_main_gordon_operator_continuous N M)).
Qed.

Lemma paper_main_gaussian_operator_tail_measurable N M L :
  measurable [set x | Rlt L (paper_main_gaussian_operator_random N M x)].
Proof.
have HE : [set x | Rlt L (paper_main_gaussian_operator_random N M x)] =
 paper_main_gaussian_operator_random N M @^-1` `]L, +oo[.
{ rewrite preimage_itvoy; apply/seteqP; split=> x /=.
  - by move=> H; apply/RltP.
  - by move/RltP. }
rewrite HE.
have H := paper_main_gaussian_operator_measurable N M measurableT `]L, +oo[ (measurable_itv _).
by rewrite setTI in H.
Qed.

Lemma paper_main_gaussian_operator_test_subset r s N M z v B :
  (forall xs, List.length xs = Nat.mul N M ->
    (forall y t, Nat.lt y r -> Nat.lt t s ->
      Rabs (paper_main_gordon_matrix_value N M (z y) (v t) xs) <= B) ->
    paper_main_gordon_operator_norm N M xs <= 2*B) ->
  [set x | Rlt (2*B) (paper_main_gaussian_operator_random N M x)] `<=`
  paper_main_gaussian_matrix_test_event r s N M z v B.
Proof.
intros HD x Hx; apply NNPP; intro Hnot.
have Hlen : List.length (tval x) = Nat.mul N M by exact: size_tuple.
have HS : forall y t, Nat.lt y r -> Nat.lt t s ->
 Rabs (paper_main_gordon_matrix_value N M (z y) (v t) (tval x)) <= B.
{ intros y t Hy Ht.
  apply Rnot_lt_le; intro Hlarge; apply Hnot.
  unfold paper_main_gaussian_matrix_test_event.
  apply paper_main_finite_event_union_member; exists y; split.
  - apply List.in_seq; lia.
  - apply paper_main_finite_event_union_member; exists t; split.
    + apply List.in_seq; lia.
    + change (B <= Rabs (paper_main_gordon_matrix_value N M (z y) (v t) (tval x))); lra. }
have H := HD (tval x) Hlen HS.
change (2*B < paper_main_gordon_operator_norm N M (tval x)) in Hx; lra.
Qed.

Lemma paper_main_gaussian_count_exponential r s C B :
  Nat.lt 0 r -> Nat.lt 0 s -> ln(INR r)+ln(INR s) <= C ->
  2*INR r*INR s*exp(-B^2/2) <= 2*exp(C-B^2/2).
Proof.
intros Hr Hs HC.
have HrR : 0 < INR r by apply lt_0_INR; exact Hr.
have HsR : 0 < INR s by apply lt_0_INR; exact Hs.
have HE : 2*INR r*INR s*exp(-B^2/2) = 2*exp(ln(INR r)+ln(INR s)-B^2/2).
{ replace (-B^2/2) with (-(B^2/2)) by field.
  unfold Rminus; rewrite !exp_plus !exp_ln; try assumption; ring. }
rewrite HE; apply Rmult_le_compat_l; [lra|].
apply Soft.Extrema.exp_monotone; lra.
Qed.

Theorem paper_main_gaussian_operator_tail N M B :
  Nat.lt 0 N -> Nat.lt 0 M -> 0 < B ->
  (gaussian_product_law (N*M)
    [set x | Rlt (2*B) (paper_main_gaussian_operator_random N M x)] <=
    (2*exp(paper_main_gordon_entropy_constant (1/4)*(INR N+INR M)-B^2/2))%:E)%E.
Proof.
intros HN HM HB.
destruct (paper_main_gordon_operator_discretization N M HN HM)
 as [r [s [z [v [Hr [Hs [Hz [Hv [HE HD]]]]]]]]].
have HZ : forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1.
{ intros y Hy; apply Hz; exact: (elimT ssrnat.ltP Hy). }
have HV : forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1.
{ intros t Ht; apply Hv; exact: (elimT ssrnat.ltP Ht). }
have Htest := paper_main_gaussian_matrix_test_bound r s N M z v B HZ HV HB.
have Hsub : [set x | Rlt (2*B) (paper_main_gaussian_operator_random N M x)] `<=`
 paper_main_gaussian_matrix_test_event r s N M z v B.
{ apply: paper_main_gaussian_operator_test_subset.
  intros xs Hxs Hscore; apply HD; [exact Hxs|lra|exact Hscore]. }
have Hmono : (gaussian_product_law (N*M)
 [set x | Rlt (2*B) (paper_main_gaussian_operator_random N M x)] <=
 gaussian_product_law (N*M) (paper_main_gaussian_matrix_test_event r s N M z v B))%E.
{ apply: le_measure; rewrite ?inE.
  - exact: paper_main_gaussian_operator_tail_measurable.
  - exact: paper_main_gaussian_matrix_test_measurable.
  - exact Hsub. }
eapply le_trans; first exact Hmono.
eapply le_trans; first exact Htest.
rewrite lee_fin; apply/RleP.
change (2*INR r*INR s*exp(-B^2/2) <=
  2*exp(paper_main_gordon_entropy_constant (1/4)*(INR N+INR M)-B^2/2)).
exact: (paper_main_gaussian_count_exponential r s _ B Hr Hs HE).
Qed.
