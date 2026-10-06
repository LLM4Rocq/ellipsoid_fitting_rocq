(* An actual Gaussian expectation identity for the interpolation error. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.Iterated.Definitions
  Gaussian.Iterated.Expectation Gaussian.Covariance.LinearImages
  Gaussian.Iterated.FiniteSums Gaussian.Smooth.Test Projection.Stein
  Projection.Image Projection.Spatial Projection.Algebra.
Open Scope R_scope.

Lemma paper_main_projection_expectation_combination d F F' G G' alpha beta :
  gaussian_iterated_integrable d F -> gaussian_iterated_integrable d F' ->
  gaussian_iterated_integrable d G -> gaussian_iterated_integrable d G' ->
  gaussian_iterated_expectation d F=gaussian_iterated_expectation d F' ->
  gaussian_iterated_expectation d G=gaussian_iterated_expectation d G' ->
  gaussian_iterated_integrable d (fun xs => alpha*F xs+beta*G xs) /\
  gaussian_iterated_integrable d (fun xs => alpha*F' xs+beta*G' xs) /\
  gaussian_iterated_expectation d (fun xs => alpha*F xs+beta*G xs)=
    gaussian_iterated_expectation d (fun xs => alpha*F' xs+beta*G' xs).
Proof.
intros HF HF' HG HG' EF EG.
destruct(gaussian_iterated_scale d F alpha HF) as [H1 E1].
destruct(gaussian_iterated_scale d F' alpha HF') as [H2 E2].
destruct(gaussian_iterated_scale d G beta HG) as [H3 E3].
destruct(gaussian_iterated_scale d G' beta HG') as [H4 E4].
destruct(gaussian_iterated_add d _ _ H1 H3) as [H5 E5].
destruct(gaussian_iterated_add d _ _ H2 H4) as [H6 E6].
split; [exact H5|]; split; [exact H6|]; rewrite E5 E6 E1 E2 E3 E4 EF EG; reflexivity.
Qed.

Definition paper_main_projection_error d K (A : nat -> nat -> nat -> R)
  (c : nat -> nat -> R) (U : nat -> list R -> R) (D2F : nat -> nat -> list R -> R) xs :=
  finite_sum (fun a => finite_sum (fun b => D2F a b (paper_main_projection_image K U xs)*
    (paper_main_projection_gram d (A a) (A b) xs-paper_main_projection_covariance d (c a) (c b)/2))
      (List.seq 0 K)) (List.seq 0 K).
Definition paper_main_projection_mixed_velocity d K (A : nat -> nat -> nat -> R)
  (c : nat -> nat -> R) u v (DF : nat -> list R -> R) xs :=
  finite_sum (fun a => (paper_main_projection_quadratic d (A a) xs/(2*u)-linear_form d (c a) xs/(2*v))*
    DF a (paper_main_projection_image K (paper_main_projection_feature d A c u v) xs)) (List.seq 0 K).

Theorem paper_main_projection_mixed_error n K A c u v F DF D2F C :
  paper_main_gaussian_smooth_test K F DF D2F C 0 ->
  (forall a i j, (a<K)%coq_nat -> (i<=n)%coq_nat -> (j<=n)%coq_nat -> A a i j=A a j i) ->
  u<>0 -> v<>0 ->
  (forall a b xs, (a<K)%coq_nat -> (b<K)%coq_nat ->
    paper_main_projection_cross (S n) (A a) (c b) xs=0) ->
  gaussian_iterated_integrable (S n)
    (paper_main_projection_error (S n) K A c (paper_main_projection_feature (S n) A c u v) D2F) /\
  gaussian_iterated_expectation (S n) (paper_main_projection_mixed_velocity (S n) K A c u v DF)=
    gaussian_iterated_expectation (S n)
      (paper_main_projection_error (S n) K A c (paper_main_projection_feature (S n) A c u v) D2F).
Proof.
intros HF HA Hu Hv HX.
set (U := paper_main_projection_feature (S n) A c u v).
set (DU := paper_main_projection_feature_gradient (S n) A c u v).
set (H := fun a xs => DF a (paper_main_projection_image K U xs)).
set (DH := paper_main_projection_test_gradient K U DU D2F).
set (L := fun xs => finite_sum (fun a => /(2*u)*(paper_main_projection_quadratic (S n) (A a) xs*H a xs)+
  (-/(2*v))*(linear_form (S n) (c a) xs*H a xs)) (List.seq 0 K)).
set (R := fun xs => finite_sum (fun a => /(2*u)*paper_main_projection_contraction (S n) (A a) (DH a) xs+
  (-/(2*v))*finite_sum (fun i => c a i*DH a i xs) (List.seq 0 (S n))) (List.seq 0 K)).
assert (HS : gaussian_iterated_integrable (S n) L /\ gaussian_iterated_integrable (S n) R /\
  gaussian_iterated_expectation (S n) L=gaussian_iterated_expectation (S n) R).
{ apply paper_main_projection_sum_expectation; intros a Ha; apply in_seq in Ha.
  destruct(paper_main_projection_feature_quadratic_stein n K A c u v F DF D2F C HF HA a ltac:(lia)) as [HQ [HDQ EQ]].
  destruct(paper_main_projection_feature_linear_stein n K A c u v F DF D2F C HF HA a ltac:(lia)) as [HG [HDG EG]].
  apply paper_main_projection_expectation_combination; assumption. }
assert (EL : forall xs, L xs=paper_main_projection_mixed_velocity (S n) K A c u v DF xs).
{ intro xs; unfold L,paper_main_projection_mixed_velocity,H,U.
  apply finite_sum_ext; intros a Ha; unfold Rdiv; ring. }
assert (ER : forall xs, R xs=paper_main_projection_error (S n) K A c U D2F xs).
{ intro xs; unfold R,paper_main_projection_error.
  transitivity (finite_sum (fun a =>
    paper_main_projection_contraction (S n) (A a)
      (fun i ys => finite_sum (fun b => D2F a b (paper_main_projection_image K U xs)*
        ((2*u)*linear_form (S n) (A b i) ys+v*c b i)) (List.seq 0 K)) xs/(2*u)-
    finite_sum (fun i => c a i*finite_sum (fun b => D2F a b (paper_main_projection_image K U xs)*
      ((2*u)*linear_form (S n) (A b i) xs+v*c b i)) (List.seq 0 K)) (List.seq 0 (S n))/(2*v)) (List.seq 0 K)).
  - apply finite_sum_ext; intros a Ha.
    unfold paper_main_projection_contraction,DH,paper_main_projection_test_gradient,
      DU,paper_main_projection_feature_gradient,Rdiv; ring.
  - apply paper_main_projection_contraction_cancellation; [exact Hu|exact Hv|].
    intros a b Ha Hb; apply HX; assumption. }
destruct HS as [HI [HJ HE]].
split.
- apply (gaussian_iterated_integrable_ext (S n) R _ (fun xs _ => ER xs) HJ).
- transitivity (gaussian_iterated_expectation (S n) L).
  + apply gaussian_iterated_expectation_ext; intros xs Hxs; symmetry; apply EL.
  + rewrite HE; apply gaussian_iterated_expectation_ext; intros xs Hxs; apply ER.
Qed.
