(* Linear Gaussian moments and tails under the exact product law. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import GaussianProductDefinitions GaussianCovarianceDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductIntegrals
  GaussianProbabilityProductContinuity PaperMainGordonProcessCovariance
  PaperMainGordonWidth PaperMainGaussianMatrixMGF.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_linear_random d a
    (x : d.-tuple (measurableTypeR R)) : measurableTypeR R :=
  paper_main_gordon_dot d a (fun i => List.nth i (tval x) 0).

Lemma paper_main_gaussian_linear_random_measurable d a :
  measurable_fun [set: d.-tuple (measurableTypeR R)] (paper_main_gaussian_linear_random d a).
Proof.
exact: (gpp_joint_measurable d _ (paper_main_gordon_dot_continuous d a)).
Qed.

HB.instance Definition _ d a :=
  isMeasurableFun.Build _ _ _ _ (paper_main_gaussian_linear_random d a)
    (paper_main_gaussian_linear_random_measurable d a).

Lemma paper_main_gaussian_linear_law_mgf d a t :
  (\int[gaussian_product_law d]_x (exp (t*paper_main_gaussian_linear_random d a x))%:E =
    (exp (t^2*paper_main_gordon_dot d a a/2))%:E)%E.
Proof.
destruct (paper_main_gaussian_scaled_vector_mgf d a t) as [[HI [HA HD]] HV].
have HM := gpp_joint_measurable d _ (paper_main_gaussian_scaled_vector_continuous d a t).
have HE := (gpp_all_sections d _ (proj2 (measurable_EFinP _ _) HM) HI HA).2.
rewrite HV in HE; exact HE.
Qed.

Lemma paper_main_gaussian_linear_law_chernoff d a q u :
  0 < q ->
  (gaussian_product_law d [set x | Rle u (paper_main_gaussian_linear_random d a x)] <=
    (exp (q^2*paper_main_gordon_dot d a a/2-q*u))%:E)%E.
Proof.
move=> Hq.
have Hq' : (0 < q)%R by apply/RltP.
pose X : {RV gaussian_product_law d >-> (R : realType)} :=
 @MeasurableFun.Pack _ _ _ (R : realType) (fun x => paper_main_gaussian_linear_random d a x)
 (MeasurableFun.Class (isMeasurableFun.Build _ _ _ (R : realType) _
 (paper_main_gaussian_linear_random_measurable d a))).
have H := chernoff X (r:=q) u Hq'.
rewrite /mmt_gen_fun unlock /X /= in H.
move: H.
under eq_integral do rewrite -RexpE mulrC.
rewrite paper_main_gaussian_linear_law_mgf -RexpE -EFinM.
change ((gaussian_product_law d [set x | (u <= paper_main_gaussian_linear_random d a x)%R] <=
 ((exp(q^2*paper_main_gordon_dot d a a/2)*exp(-(q*u)))%Rcoq)%:E)%E ->
 (gaussian_product_law d [set x | Rle u (paper_main_gaussian_linear_random d a x)] <=
 (exp(q^2*paper_main_gordon_dot d a a/2-q*u))%:E)%E).
rewrite -exp_plus.
have HS : [set x : d.-tuple (measurableTypeR R) | (u <= paper_main_gaussian_linear_random d a x)%R] =
 [set x | Rle u (paper_main_gaussian_linear_random d a x)].
{ apply/seteqP; split=> x /=.
  - by move/RleP.
  - by move=> H; apply/RleP. }
rewrite HS; trivial.
Qed.

Theorem paper_main_gaussian_unit_linear_upper_tail d a u :
  paper_main_gordon_dot d a a = 1 -> 0 < u ->
  (gaussian_product_law d [set x | Rle u (paper_main_gaussian_linear_random d a x)] <=
    (exp (-u^2/2))%:E)%E.
Proof.
intros Ha Hu.
pose proof (paper_main_gaussian_linear_law_chernoff d a u u Hu) as H.
rewrite Ha in H.
replace (u^2*1/2-u*u) with (-u^2/2) in H by field.
exact H.
Qed.
