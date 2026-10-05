(* Two-sided tails for linear forms under the exact Gaussian product law. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability exp measurable_realfun.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainGordonProcessCovariance PaperMainGordonBilinear
  PaperMainGaussianMatrixMGF PaperMainGaussianLinearLaw.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_gaussian_linear_upper_measurable d a u :
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle u (paper_main_gaussian_linear_random d a x)].
Proof.
have HE : [set x : d.-tuple (measurableTypeR R) | Rle u (paper_main_gaussian_linear_random d a x)] =
 paper_main_gaussian_linear_random d a @^-1` `[u, +oo[.
{ rewrite preimage_itvcy; apply/seteqP; split=> x /=.
  - by move=> H; apply/RleP.
  - by move/RleP. }
rewrite HE.
have H := paper_main_gaussian_linear_random_measurable d a measurableT `[u, +oo[ (measurable_itv _).
by rewrite setTI in H.
Qed.

Lemma paper_main_gaussian_linear_negative d a x :
  paper_main_gaussian_linear_random d (fun i => -a i) x =
  -paper_main_gaussian_linear_random d a x.
Proof.
unfold paper_main_gaussian_linear_random.
pose proof (paper_main_gaussian_dot_scale_left d a (fun i => List.nth i (tval x) 0) (-1)) as H.
replace (fun i => -1*a i) with (fun i => -a i) in H.
- rewrite H; lra.
- apply FunctionalExtensionality.functional_extensionality; intros i; lra.
Qed.

Lemma paper_main_gaussian_unit_negative d a :
  paper_main_gordon_dot d a a = 1 ->
  paper_main_gordon_dot d (fun i => -a i) (fun i => -a i) = 1.
Proof.
intro Ha.
pose proof (paper_main_gordon_dot_scale d a (-1)) as H.
replace (fun i => -1*a i) with (fun i => -a i) in H.
- rewrite H Ha; lra.
- apply FunctionalExtensionality.functional_extensionality; intros i; lra.
Qed.

Lemma paper_main_gaussian_linear_absolute_event d a u :
  [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (paper_main_gaussian_linear_random d a x))] =
  [set x | Rle u (paper_main_gaussian_linear_random d a x)] `|`
  [set x | Rle u (paper_main_gaussian_linear_random d (fun i => -a i) x)].
Proof.
apply/seteqP; split=> x /=; rewrite paper_main_gaussian_linear_negative.
- unfold Rabs; destruct Rcase_abs; lra.
- pose proof (Rle_abs (paper_main_gaussian_linear_random d a x)).
  pose proof (Rle_abs (-paper_main_gaussian_linear_random d a x)).
  rewrite Rabs_Ropp in H0; intros [H1|H1]; lra.
Qed.

Lemma paper_main_gaussian_linear_absolute_measurable d a u :
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (paper_main_gaussian_linear_random d a x))].
Proof.
rewrite paper_main_gaussian_linear_absolute_event.
apply: measurableU; apply: paper_main_gaussian_linear_upper_measurable.
Qed.

Theorem paper_main_gaussian_unit_linear_absolute_tail d a u :
  paper_main_gordon_dot d a a = 1 -> 0 < u ->
  (gaussian_product_law d [set x | Rle u (Rabs (paper_main_gaussian_linear_random d a x))] <=
    (2*exp(-u^2/2))%:E)%E.
Proof.
move=> Ha Hu.
rewrite paper_main_gaussian_linear_absolute_event.
have H1 := paper_main_gaussian_unit_linear_upper_tail d a u Ha Hu.
have H2 := paper_main_gaussian_unit_linear_upper_tail d (fun i => -a i) u
 (paper_main_gaussian_unit_negative d a Ha) Hu.
Import Order.TTheory.
eapply le_trans; first exact: (measureU2 _ (paper_main_gaussian_linear_upper_measurable d a u)
 (paper_main_gaussian_linear_upper_measurable d (fun i => -a i) u)).
have H := leeD H1 H2.
move: H; rewrite -EFinD.
have HE (z : R) : (z+z)%R = Rmult 2 z.
{ change (z + z = 2*z); lra. }
rewrite HE; trivial.
Qed.
