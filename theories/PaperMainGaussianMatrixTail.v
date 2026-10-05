(* Absolute Gaussian tails and finite testing events for rectangular matrices. *)
From Stdlib Require Import Reals List Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure lebesgue_measure.
From EllipsoidFitting Require Import GaussianCovarianceDefinitions GaussianProbabilityProductDefinitions
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonLipschitz
  PaperMainGaussianLinearLaw PaperMainGaussianTails PaperMainGaussianUnion.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_matrix_random N M u v
    (x : (N*M).-tuple (measurableTypeR R)) :=
  paper_main_gordon_matrix_value N M u v (tval x).

Lemma paper_main_gaussian_matrix_as_linear N M u v x :
  paper_main_gaussian_matrix_random N M u v x =
  paper_main_gaussian_linear_random (N*M)
    (paper_main_gordon_matrix_loading N M (fun _ => u) (fun _ => v) 0%nat) x.
Proof.
unfold paper_main_gaussian_matrix_random, paper_main_gaussian_linear_random.
symmetry; apply paper_main_gordon_raw_matrix_row.
Qed.

Lemma paper_main_gaussian_matrix_loading_unit N M u v :
  paper_main_gordon_dot N u u = 1 -> paper_main_gordon_dot M v v = 1 ->
  let a := paper_main_gordon_matrix_loading N M (fun _ => u) (fun _ => v) 0%nat in
  paper_main_gordon_dot (N*M) a a = 1.
Proof.
intros Hu Hv.
change (gaussian_covariance_entry (N*M) (paper_main_gordon_matrix_loading N M (fun _ => u) (fun _ => v)) 0 0 = 1).
rewrite paper_main_gordon_raw_matrix_covariance Hu Hv; lra.
Qed.

Lemma paper_main_gaussian_matrix_absolute_measurable N M u v B :
  measurable [set x | Rle B (Rabs (paper_main_gaussian_matrix_random N M u v x))].
Proof.
have HE : [set x | Rle B (Rabs (paper_main_gaussian_matrix_random N M u v x))] =
 [set x | Rle B (Rabs (paper_main_gaussian_linear_random (N*M)
 (paper_main_gordon_matrix_loading N M (fun _ => u) (fun _ => v) 0%nat) x))].
{ apply: eq_set; move=> x; by rewrite paper_main_gaussian_matrix_as_linear. }
rewrite HE; apply: paper_main_gaussian_linear_absolute_measurable.
Qed.

Theorem paper_main_gaussian_unit_matrix_absolute_tail N M u v B :
  paper_main_gordon_dot N u u = 1 -> paper_main_gordon_dot M v v = 1 -> 0 < B ->
  (gaussian_product_law (N*M)
    [set x | Rle B (Rabs (paper_main_gaussian_matrix_random N M u v x))] <=
    (2*exp(-B^2/2))%:E)%E.
Proof.
intros Hu Hv HB.
have HE : [set x | Rle B (Rabs (paper_main_gaussian_matrix_random N M u v x))] =
 [set x | Rle B (Rabs (paper_main_gaussian_linear_random (N*M)
 (paper_main_gordon_matrix_loading N M (fun _ => u) (fun _ => v) 0%nat) x))].
{ apply: eq_set; move=> x; by rewrite paper_main_gaussian_matrix_as_linear. }
rewrite HE; apply: paper_main_gaussian_unit_linear_absolute_tail.
- exact: (paper_main_gaussian_matrix_loading_unit N M u v Hu Hv).
- exact HB.
Qed.

Definition paper_main_gaussian_matrix_test_event r s N M z v B :=
  paper_main_finite_event_union (List.seq 0 r) (fun y =>
    paper_main_finite_event_union (List.seq 0 s) (fun t =>
      [set x | Rle B (Rabs (paper_main_gaussian_matrix_random N M (z y) (v t) x))])).

Lemma paper_main_gaussian_matrix_test_measurable r s N M z v B :
  measurable (paper_main_gaussian_matrix_test_event r s N M z v B).
Proof.
apply: paper_main_gaussian_union_measurable; intros y Hy.
apply: paper_main_gaussian_union_measurable; intros t Ht.
apply: paper_main_gaussian_matrix_absolute_measurable.
Qed.

Theorem paper_main_gaussian_matrix_test_bound r s N M z v B :
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  0 < B ->
  (gaussian_product_law (N*M) (paper_main_gaussian_matrix_test_event r s N M z v B) <=
    (2*INR r*INR s*exp(-B^2/2))%:E)%E.
Proof.
intros Hz Hv HB.
set E := fun y t => [set x | Rle B (Rabs (paper_main_gaussian_matrix_random N M (z y) (v t) x))].
have HMeas y t : measurable (E y t) by apply: paper_main_gaussian_matrix_absolute_measurable.
have Hinner y : (y < r)%nat ->
 (gaussian_product_law (N*M) (paper_main_finite_event_union (List.seq 0 s) (E y)) <=
  (INR s*(2*exp(-B^2/2)))%:E)%E.
{ intro Hy.
  have HT : forall t, List.In t (List.seq 0 s) ->
   (gaussian_product_law (N*M) (E y t) <= (2*exp(-B^2/2))%:E)%E.
  { intros t Ht; apply: paper_main_gaussian_unit_matrix_absolute_tail.
    - exact: Hz Hy.
    - apply Hv; apply/ssrnat.ltP; apply List.in_seq in Ht; lia.
    - exact HB. }
  have H := paper_main_gaussian_union_bound (N*M) (List.seq 0 s) (E y) (2*exp(-B^2/2))
   (fun t _ => HMeas y t) HT.
  rewrite List.length_seq in H; exact H. }
have HO : forall y, List.In y (List.seq 0 r) ->
 (gaussian_product_law (N*M) (paper_main_finite_event_union (List.seq 0 s) (E y)) <=
  (INR s*(2*exp(-B^2/2)))%:E)%E.
{ intros y Hy; apply Hinner; apply/ssrnat.ltP; apply List.in_seq in Hy; lia. }
have HMOuter y : measurable (paper_main_finite_event_union (List.seq 0 s) (E y)).
{ apply: paper_main_gaussian_union_measurable; intros; apply HMeas. }
have H := paper_main_gaussian_union_bound (N*M) (List.seq 0 r)
 (fun y => paper_main_finite_event_union (List.seq 0 s) (E y)) (INR s*(2*exp(-B^2/2)))
 (fun y _ => HMOuter y) HO.
rewrite List.length_seq in H.
eapply le_trans; first exact H.
rewrite lee_fin; apply/RleP.
change (INR r*(INR s*(2*exp(-B^2/2))) <= 2*INR r*INR s*exp(-B^2/2)).
nra.
Qed.
