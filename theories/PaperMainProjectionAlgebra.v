(* Finite contraction algebra behind the quadratic/Gaussian interpolation. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums
  GaussianCovarianceLinear PaperMainProjectionStein.
Open Scope R_scope.

Definition paper_main_projection_gram d (A B : nat -> nat -> R) xs :=
  finite_sum (fun i => linear_form d (A i) xs*linear_form d (B i) xs) (List.seq 0 d).
Definition paper_main_projection_cross d (A : nat -> nat -> R) (c : nat -> R) xs :=
  finite_sum (fun i => linear_form d (A i) xs*c i) (List.seq 0 d).
Definition paper_main_projection_covariance d (c e : nat -> R) :=
  finite_sum (fun i => c i*e i) (List.seq 0 d).

Lemma paper_main_projection_contraction_rows d A DF xs :
  paper_main_projection_contraction d A DF xs=
    finite_sum (fun i => linear_form d (A i) xs*DF i xs) (List.seq 0 d).
Proof.
unfold paper_main_projection_contraction,linear_form.
apply finite_sum_ext; intros i Hi; rewrite <- finite_sum_scale_r.
apply finite_sum_ext; intros j Hj; ring.
Qed.

Lemma paper_main_projection_weighted_swap I J f g h :
  finite_sum (fun i => f i*finite_sum (fun j => h j*g i j) J) I=
    finite_sum (fun j => h j*finite_sum (fun i => f i*g i j) I) J.
Proof.
transitivity (finite_sum (fun i => finite_sum (fun j => f i*(h j*g i j)) J) I).
- apply finite_sum_ext; intros i Hi; symmetry; apply finite_sum_scale.
- rewrite finite_sum_swap; apply finite_sum_ext; intros j Hj.
  rewrite <- finite_sum_scale; apply finite_sum_ext; intros i Hi; ring.
Qed.

Lemma paper_main_projection_quadratic_contraction d K A B c u v H xs :
  paper_main_projection_contraction d A
    (fun i ys => finite_sum (fun b => H b*((2*u)*linear_form d (B b i) ys+v*c b i)) (List.seq 0 K)) xs=
  finite_sum (fun b => H b*((2*u)*paper_main_projection_gram d A (B b) xs+
    v*paper_main_projection_cross d A (c b) xs)) (List.seq 0 K).
Proof.
rewrite paper_main_projection_contraction_rows paper_main_projection_weighted_swap.
apply finite_sum_ext; intros b Hb; f_equal.
unfold paper_main_projection_gram,paper_main_projection_cross.
rewrite -finite_sum_scale -finite_sum_scale -finite_sum_plus.
apply finite_sum_ext; intros i Hi; ring.
Qed.

Lemma paper_main_projection_linear_contraction d K c A e u v H xs :
  finite_sum (fun i => c i*finite_sum
    (fun b => H b*((2*u)*linear_form d (A b i) xs+v*e b i)) (List.seq 0 K)) (List.seq 0 d)=
  finite_sum (fun b => H b*((2*u)*paper_main_projection_cross d (A b) c xs+
    v*paper_main_projection_covariance d c (e b))) (List.seq 0 K).
Proof.
rewrite paper_main_projection_weighted_swap.
apply finite_sum_ext; intros b Hb; f_equal.
unfold paper_main_projection_cross,paper_main_projection_covariance.
rewrite -finite_sum_scale -finite_sum_scale -finite_sum_plus.
apply finite_sum_ext; intros i Hi; ring.
Qed.

Lemma paper_main_projection_scalar_cancellation u v G X Y C :
  u<>0 -> v<>0 -> X=0 -> Y=0 ->
  ((2*u)*G+v*X)/(2*u)-((2*u)*Y+v*C)/(2*v)=G-C/2.
Proof. intros Hu Hv -> ->; field; split; assumption. Qed.

Theorem paper_main_projection_contraction_cancellation d K A c u v H xs :
  u<>0 -> v<>0 ->
  (forall a b, (a<K)%coq_nat -> (b<K)%coq_nat -> paper_main_projection_cross d (A a) (c b) xs=0) ->
  finite_sum (fun a =>
    paper_main_projection_contraction d (A a)
      (fun i ys => finite_sum (fun b => H a b*((2*u)*linear_form d (A b i) ys+v*c b i)) (List.seq 0 K)) xs/(2*u)-
    finite_sum (fun i => c a i*finite_sum
      (fun b => H a b*((2*u)*linear_form d (A b i) xs+v*c b i)) (List.seq 0 K)) (List.seq 0 d)/(2*v)) (List.seq 0 K)=
  finite_sum (fun a => finite_sum (fun b => H a b*
    (paper_main_projection_gram d (A a) (A b) xs-paper_main_projection_covariance d (c a) (c b)/2))
      (List.seq 0 K)) (List.seq 0 K).
Proof.
intros Hu Hv HX; apply finite_sum_ext; intros a Ha; apply in_seq in Ha.
rewrite paper_main_projection_quadratic_contraction paper_main_projection_linear_contraction.
unfold Rdiv; rewrite -finite_sum_scale_r -finite_sum_scale_r -finite_sum_minus.
apply finite_sum_ext; intros b Hb; apply in_seq in Hb.
pose proof(paper_main_projection_scalar_cancellation u v
  (paper_main_projection_gram d (A a) (A b) xs)
  (paper_main_projection_cross d (A a) (c b) xs)
  (paper_main_projection_cross d (A b) (c a) xs)
  (paper_main_projection_covariance d (c a) (c b)) Hu Hv
  (HX a b ltac:(lia) ltac:(lia)) (HX b a ltac:(lia) ltac:(lia))) as HE.
unfold Rdiv in HE; rewrite <- HE; ring.
Qed.
