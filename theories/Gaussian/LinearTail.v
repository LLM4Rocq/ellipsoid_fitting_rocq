(* Exact-law tails and finite unions for Gaussian linear forms with squared
   coefficient norm at most one. No independence between the forms is needed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.CoordinateWeightDefinitions Gaussian.CoordinatePolynomialContinuity
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  Gordon.ProcessCovariance Gordon.Lipschitz Gaussian.SmoothTail
  Gaussian.LipschitzClip Gaussian.LipschitzApproximation
  Gaussian.LipschitzConcentration Gaussian.SymmetricLawReflection
  Gaussian.SymmetricLaw.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_linear_form d (c : nat -> R) (xs : list R) : R :=
  paper_main_gordon_dot d c (fun k => List.nth k xs 0).

Lemma paper_main_gaussian_linear_form_lipschitz d c :
  paper_main_gordon_dot d c c <= 1 ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
  Rabs (paper_main_gaussian_linear_form d c xs -
    paper_main_gaussian_linear_form d c ys) <= 1 * paper_main_gordon_distance d xs ys.
Proof.
intros HC xs ys _ _.
pose proof (paper_main_gordon_sum_cauchy c
  (fun k => List.nth k xs 0 - List.nth k ys 0) (List.seq 0 d)) as H.
assert (HE : finite_sum (fun k => c k * (List.nth k xs 0-List.nth k ys 0)) (List.seq 0 d) =
  paper_main_gaussian_linear_form d c xs - paper_main_gaussian_linear_form d c ys).
{ unfold paper_main_gaussian_linear_form, paper_main_gordon_dot.
  rewrite <- finite_sum_minus; apply finite_sum_ext; intros k _; ring. }
assert (HS : finite_sum (fun k => (c k)^2) (List.seq 0 d) = paper_main_gordon_dot d c c).
{ unfold paper_main_gordon_dot; apply finite_sum_ext; intros k _; ring. }
rewrite HE HS -paper_main_gordon_distance_squared in H.
pose proof (paper_main_gordon_distance_nonnegative d xs ys).
pose proof (Rabs_pos (paper_main_gaussian_linear_form d c xs-paper_main_gaussian_linear_form d c ys)).
pose proof (Rsqr_abs (paper_main_gaussian_linear_form d c xs-paper_main_gaussian_linear_form d c ys)).
unfold Rsqr in H2.
pose proof (pow2_ge_0 (paper_main_gordon_distance d xs ys)); nra.
Qed.

Lemma paper_main_gaussian_linear_form_odd d c xs :
  paper_main_gaussian_linear_form d c (List.map Ropp xs) =
  - paper_main_gaussian_linear_form d c xs.
Proof.
unfold paper_main_gaussian_linear_form, paper_main_gordon_dot.
transitivity (finite_sum (fun k => -1 * (c k * List.nth k xs 0)) (List.seq 0 d)).
- apply finite_sum_ext; intros k _; rewrite paper_main_symmetric_nth_neg; ring.
- rewrite finite_sum_scale; ring.
Qed.

Theorem paper_main_gaussian_odd_lipschitz_mean d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs-F ys) <= L * paper_main_gordon_distance d xs ys) ->
  (forall xs, List.length xs = d -> F (List.map Ropp xs) = -F xs) ->
  gaussian_iterated_expectation d F = 0.
Proof.
move=> HL Hlip Hodd.
have HC := paper_main_gaussian_lipschitz_continuous d F L HL Hlip.
have HB := paper_main_gaussian_lipschitz_polynomial_bound d F L HL Hlip.
have HR := paper_main_gaussian_iterated_reflect d F _ 2 HC HB.
have [HI _] := paper_main_gaussian_lipschitz_domain d F L HL Hlip.
have HE : gaussian_iterated_expectation d (fun xs => F (List.map Ropp xs)) =
  gaussian_iterated_expectation d (fun xs => -1*F xs).
  apply: gaussian_iterated_expectation_ext => xs Hxs; rewrite Hodd //; ring.
rewrite HE (proj2 (gaussian_iterated_scale d F (-1) HI)) in HR; lra.
Qed.

Theorem paper_main_gaussian_linear_form_mean d c :
  paper_main_gordon_dot d c c <= 1 ->
  gaussian_iterated_expectation d (paper_main_gaussian_linear_form d c) = 0.
Proof.
move=> HC; apply: (paper_main_gaussian_odd_lipschitz_mean d _ 1 Rle_0_1
  (paper_main_gaussian_linear_form_lipschitz d c HC)).
move=> xs _; exact: paper_main_gaussian_linear_form_odd.
Qed.

Theorem paper_main_gaussian_linear_form_tail d c u :
  paper_main_gordon_dot d c c <= 1 -> 0 < u ->
  (gaussian_product_law d [set x | Rle u
    (Rabs (paper_main_gaussian_linear_form d c (tval x)))] <=
    (2*exp(-u^2/2))%:E)%E.
Proof.
move=> HC Hu.
have H := paper_main_gaussian_lipschitz_two_sided_tail d
  (paper_main_gaussian_linear_form d c) 1 u Rlt_0_1
  (paper_main_gaussian_linear_form_lipschitz d c HC) Hu.
rewrite (paper_main_gaussian_linear_form_mean d c HC) in H.
have HE : [set x : d.-tuple (measurableTypeR R) | Rle u
    (Rabs (paper_main_gaussian_linear_form d c (tval x)-0))] =
  [set x | Rle u (Rabs (paper_main_gaussian_linear_form d c (tval x)))].
  apply/seteqP; split=> x /=; by rewrite Rminus_0_r.
rewrite HE in H; replace (2*1^2) with 2 in H by ring; exact H.
Qed.

Lemma paper_main_gaussian_linear_form_tail_measurable d c u :
  paper_main_gordon_dot d c c <= 1 ->
  measurable [set x : d.-tuple (measurableTypeR R) | Rle u
    (Rabs (paper_main_gaussian_linear_form d c (tval x)))].
Proof.
move=> HC.
apply: (paper_main_gaussian_smooth_ge_measurable d (fun xs => Rabs (paper_main_gaussian_linear_form d c xs)) u).
apply: finite_joint_continuous_abs.
exact: (paper_main_gaussian_lipschitz_continuous d _ 1 Rle_0_1
  (paper_main_gaussian_linear_form_lipschitz d c HC)).
Qed.

Fixpoint paper_main_gaussian_linear_union {I : Type} d (c : I -> nat -> R)
    (ids : list I) u : set (d.-tuple (measurableTypeR R)) :=
  match ids with
  | nil => set0
  | cons i rest => [set x | Rle u (Rabs (paper_main_gaussian_linear_form d (c i) (tval x)))]
      `|` paper_main_gaussian_linear_union d c rest u
  end.

Lemma paper_main_gaussian_linear_union_measurable I d (c : I -> nat -> R) ids u :
  (forall i, List.In i ids -> paper_main_gordon_dot d (c i) (c i) <= 1) ->
  measurable (paper_main_gaussian_linear_union d c ids u).
Proof.
elim: ids => [|i ids IH] HC; first exact: measurable0.
apply: measurableU.
- apply: paper_main_gaussian_linear_form_tail_measurable; apply: HC; by left.
- apply: IH => j Hj; apply: HC; by right.
Qed.

Theorem paper_main_gaussian_linear_union_bound I d (c : I -> nat -> R) ids u :
  (forall i, List.In i ids -> paper_main_gordon_dot d (c i) (c i) <= 1) ->
  0 < u ->
  (gaussian_product_law d (paper_main_gaussian_linear_union d c ids u) <=
    ((INR (List.length ids) * (2*exp(-u^2/2)))%Rcoq)%:E)%E.
Proof.
elim: ids => [|i ids IH] HC Hu; first by rewrite /paper_main_gaussian_linear_union measure0 /= Rmult_0_l.
have HCi : paper_main_gordon_dot d (c i) (c i) <= 1.
  apply: HC; left; reflexivity.
have HCr : forall j, List.In j ids -> paper_main_gordon_dot d (c j) (c j) <= 1.
  move=> j Hj; apply: HC; by right.
have H1 := paper_main_gaussian_linear_form_tail d (c i) u HCi Hu.
have H2 := IH HCr Hu.
have HU := measureU2 (gaussian_product_law d)
  (paper_main_gaussian_linear_form_tail_measurable d (c i) u HCi)
  (paper_main_gaussian_linear_union_measurable I d c ids u HCr).
eapply le_trans; first exact HU.
eapply le_trans; first exact (leeD H1 H2).
rewrite -EFinD lee_fin; apply/RleP.
change (2*exp(-u^2/2)+INR (List.length ids)*(2*exp(-u^2/2)) <=
  INR (S (List.length ids))*(2*exp(-u^2/2))).
rewrite S_INR; lra.
Qed.

Lemma paper_main_gaussian_linear_unionE I d (c : I -> nat -> R) ids u x :
  paper_main_gaussian_linear_union d c ids u x <->
  exists i, List.In i ids /\ u <= Rabs (paper_main_gaussian_linear_form d (c i) (tval x)).
Proof.
elim: ids => [|i ids IH]; first by split; [case|move=> [j [[] _]]].
change ((u <= Rabs (paper_main_gaussian_linear_form d (c i) (tval x)) \/
  paper_main_gaussian_linear_union d c ids u x) <->
  exists j, List.In j (i::ids) /\ u <= Rabs (paper_main_gaussian_linear_form d (c j) (tval x))).
rewrite IH; split.
- move=> [H|[j [Hj H]]]; [exists i; split; [by left|exact H]|exists j; split; [by right|exact H]].
- move=> [j [[<-|Hj] H]]; [by left|right; by exists j].
Qed.
