(* Dimension-sensitive radius control for all independent Gaussian sample
   blocks, under the exact product law. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.IteratedExpectationDefinitions GaussianProbabilityProductDefinitions
  Gaussian.ProductLawBasics Soft.Definitions Analysis.FiniteSumAlgebra
  PaperMainDefinitions Sampling Head.Law Gordon.Lipschitz Gaussian.Norm
  Gaussian.NormConcentration Gaussian.SmoothTail Gaussian.LipschitzClip
  Gaussian.LipschitzConcentration.
From EllipsoidFitting Require Import Analysis.RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

Theorem paper_main_gaussian_lipschitz_upper_margin d F L b u :
  0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_expectation d F <= b -> 0 < u ->
  (gaussian_product_law d [set x | Rle (b+u) (F (tval x))] <=
    (exp (-u^2/(2*L^2)))%:E)%E.
Proof.
move=> HL Hlip Hb Hu.
have HC := paper_main_gaussian_lipschitz_continuous d F L (Rlt_le _ _ HL) Hlip.
have HS : [set x : d.-tuple T | Rle (b+u) (F (tval x))] `<=`
  [set x | Rle (gaussian_iterated_expectation d F+u) (F (tval x))].
{ move=> x /= H; lra. }
have HM : (gaussian_product_law d [set x | Rle (b+u) (F (tval x))] <=
  gaussian_product_law d [set x | Rle (gaussian_iterated_expectation d F+u) (F (tval x))])%E.
{ apply: le_measure; rewrite ?inE.
  - exact: paper_main_gaussian_smooth_ge_measurable.
  - exact: paper_main_gaussian_smooth_ge_measurable.
  - exact HS. }
exact: le_trans HM (paper_main_gaussian_lipschitz_upper_tail d F L u HL Hlip Hu).
Qed.

Theorem paper_main_gaussian_norm_upper_tail d u :
  0 < u ->
  (gaussian_product_law d [set x | Rle (sqrt (INR d)+u) (paper_main_gaussian_norm (tval x))] <=
    (exp (-u^2/2))%:E)%E.
Proof.
move=> Hu.
have H := paper_main_gaussian_lipschitz_upper_margin d paper_main_gaussian_norm 1
  (sqrt (INR d)) u Rlt_0_1 (paper_main_gaussian_norm_lipschitz d)
  (proj2 (paper_main_gaussian_norm_expectation d)) Hu.
replace (2*1^2) with 2 in H by ring; exact H.
Qed.

Theorem paper_main_gaussian_norm_twice_radius d :
  Nat.lt 0 d ->
  (gaussian_product_law d [set x | Rle (2*sqrt (INR d)) (paper_main_gaussian_norm (tval x))] <=
    (exp (-INR d/2))%:E)%E.
Proof.
move=> Hd.
have Hdp : 0 < INR d by apply lt_0_INR.
have H := paper_main_gaussian_norm_upper_tail d (sqrt (INR d)) (sqrt_lt_R0 _ Hdp).
rewrite (pow2_sqrt _ (pos_INR d)) in H.
replace (sqrt (INR d)+sqrt (INR d)) with (2*sqrt (INR d)) in H by ring.
exact H.
Qed.

Fixpoint paper_main_data_radius_event (N d : nat) (r : R) :
    set ((Nat.mul N d).-tuple T) :=
  match N return set ((Nat.mul N d).-tuple T) with
  | O => set0
  | S k => [set x | Rle r (paper_main_gaussian_norm
      (tval (paper_main_take_coordinates d (Nat.mul k d) x)))] `|`
      (paper_main_drop_coordinates d (Nat.mul k d) @^-1` paper_main_data_radius_event k d r)
  end.

Lemma paper_main_data_radius_event_measurable N d r :
  measurable (paper_main_data_radius_event N d r).
Proof.
elim: N => [|N IH]; first exact: measurable0.
apply: measurableU.
- have H := paper_main_take_coordinates_measurable d (Nat.mul N d) measurableT
    [set x | Rle r (paper_main_gaussian_norm (tval x))]
    (paper_main_gaussian_smooth_ge_measurable d paper_main_gaussian_norm r
      (paper_main_gaussian_norm_continuous d)).
  by rewrite setTI in H.
- have H := paper_main_drop_coordinates_measurable d (Nat.mul N d) measurableT
    (paper_main_data_radius_event N d r) IH.
  by rewrite setTI in H.
Qed.

Theorem paper_main_data_radius_union N d r b :
  (gaussian_product_law d [set x | Rle r (paper_main_gaussian_norm (tval x))] <= b%:E)%E ->
  (gaussian_product_law (Nat.mul N d) (paper_main_data_radius_event N d r) <=
    (INR N*b)%:E)%E.
Proof.
move=> HB; elim: N => [|N IH].
- by rewrite /paper_main_data_radius_event measure0 mul0r.
- have HE := paper_main_gaussian_smooth_ge_measurable d paper_main_gaussian_norm r
    (paper_main_gaussian_norm_continuous d).
  have HM1 := paper_main_take_coordinates_measurable d (Nat.mul N d) measurableT _ HE.
  rewrite setTI in HM1.
  have HM2 := paper_main_drop_coordinates_measurable d (Nat.mul N d) measurableT _
    (paper_main_data_radius_event_measurable N d r).
  rewrite setTI in HM2.
  change (gaussian_product_law (Nat.add d (Nat.mul N d))
    ((paper_main_take_coordinates d (Nat.mul N d) @^-1`
      [set x | Rle r (paper_main_gaussian_norm (tval x))]) `|`
     (paper_main_drop_coordinates d (Nat.mul N d) @^-1` paper_main_data_radius_event N d r)) <=
    (INR (S N)*b)%:E)%E.
  have HU := measureU2 (gaussian_product_law (Nat.add d (Nat.mul N d))) HM1 HM2.
  have H1 : (gaussian_product_law (Nat.add d (Nat.mul N d))
    (paper_main_take_coordinates d (Nat.mul N d) @^-1`
      [set x | Rle r (paper_main_gaussian_norm (tval x))]) <= b%:E)%E.
  { rewrite (paper_main_take_coordinates_law d (Nat.mul N d) _ HE); exact HB. }
  have H2 : (gaussian_product_law (Nat.add d (Nat.mul N d))
    (paper_main_drop_coordinates d (Nat.mul N d) @^-1` paper_main_data_radius_event N d r) <=
    (INR N*b)%:E)%E.
  { rewrite (paper_main_drop_coordinates_law d (Nat.mul N d) _
      (paper_main_data_radius_event_measurable N d r)); exact IH. }
  eapply le_trans; first exact HU.
  eapply le_trans; first exact (leeD H1 H2).
  rewrite -EFinD lee_fin; apply/RleP.
  change (b+INR N*b <= INR (S N)*b); rewrite S_INR; lra.
Qed.

Corollary paper_main_data_radius_probability N d :
  Nat.lt 0 d ->
  (gaussian_product_law (Nat.mul N d)
    (paper_main_data_radius_event N d (2*sqrt (INR d))) <=
    (INR N*exp (-INR d/2))%:E)%E.
Proof.
move=> Hd; apply: paper_main_data_radius_union.
exact: paper_main_gaussian_norm_twice_radius.
Qed.

Lemma paper_main_data_take_nth d m (x : (Nat.add d m).-tuple T) j :
  Nat.lt j d ->
  List.nth j (tval (paper_main_take_coordinates d m x)) 0 = List.nth j (tval x) 0.
Proof.
revert x j; induction d as [|d IH]; intros x j Hj; first lia.
destruct j as [|j].
- change (tnth x ord0 = List.nth 0 (tval x) 0).
  rewrite gpp_nthE (tnth_nth 0); reflexivity.
- change (List.nth j (tval (paper_main_take_coordinates d m
    (paper_main_tail_coordinate (Nat.add d m) x))) 0 = List.nth (S j) (tval x) 0).
  rewrite (IH _ j ltac:(lia)).
  change (List.nth j (behead (tval x)) 0 = List.nth (S j) (tval x) 0).
  clear Hj; by case: (tval x) => [|a xs] //=; case: j.
Qed.

Definition paper_main_data_point_norm d i (xs : list R) : R :=
  sqrt (Soft.Definitions.finite_sum (fun j => (List.nth (Nat.add (Nat.mul i d) j) xs 0)^2)
    (List.seq 0 d)).

Lemma paper_main_data_first_norm d m (x : (Nat.add d m).-tuple T) :
  paper_main_gaussian_norm (tval (paper_main_take_coordinates d m x)) =
    paper_main_data_point_norm d 0 (tval x).
Proof.
unfold paper_main_gaussian_norm, paper_main_data_point_norm.
rewrite <- (paper_main_gaussian_squares_coordinates d
  (tval (paper_main_take_coordinates d m x)) (size_tuple _)).
f_equal; apply finite_sum_ext; intros j Hj; apply List.in_seq in Hj.
rewrite (paper_main_data_take_nth d m x j ltac:(lia)).
reflexivity.
Qed.

Lemma paper_main_data_drop_norm d m (x : (Nat.add d m).-tuple T) i :
  paper_main_data_point_norm d i (tval (paper_main_drop_coordinates d m x)) =
    paper_main_data_point_norm d (S i) (tval x).
Proof.
unfold paper_main_data_point_norm.
f_equal; apply finite_sum_ext; intros j _.
rewrite paper_main_drop_coordinates_nth.
replace (Nat.add d (Nat.add (Nat.mul i d) j)) with (Nat.add (Nat.mul (S i) d) j) by lia.
reflexivity.
Qed.

Theorem paper_main_data_radius_eventE N d r (x : (Nat.mul N d).-tuple T) :
  paper_main_data_radius_event N d r x <->
  exists i, Nat.lt i N /\ r <= paper_main_data_point_norm d i (tval x).
Proof.
revert x; induction N as [|N IH]; intros x.
- split; [by case|intros [i [Hi _]]; lia].
- change ((r <= paper_main_gaussian_norm
    (tval (paper_main_take_coordinates d (Nat.mul N d) x)) \/
    paper_main_data_radius_event N d r (paper_main_drop_coordinates d (Nat.mul N d) x)) <->
    exists i, Nat.lt i (S N) /\ r <= paper_main_data_point_norm d i (tval x)).
  rewrite paper_main_data_first_norm IH; split.
  + intros [H|[i [Hi H]]].
    * exists 0%nat; split; [lia|exact H].
    * exists (S i); split; [lia|].
      rewrite (paper_main_data_drop_norm d (Nat.mul N d) x i) in H; exact H.
  + intros [[|i] [Hi H]].
    * left; exact H.
    * right; exists i; split; [lia|].
      rewrite (paper_main_data_drop_norm d (Nat.mul N d) x i); exact H.
Qed.

Theorem paper_main_data_point_norm_square N d i (x : paper_main_sample N d) :
  (paper_main_data_point_norm d i (tval x))^2 =
    (((paper_main_point x i)^T *m paper_main_point x i) 0 0)%R.
Proof.
unfold paper_main_data_point_norm.
assert (HS : 0 <= finite_sum (fun j => (List.nth (Nat.add (Nat.mul i d) j) (tval x) 0)^2)
  (List.seq 0 d)).
{ apply finite_sum_nonneg; intros j _; nra. }
rewrite (pow2_sqrt _ HS) finite_sum_seqE mxE.
apply: eq_bigr => j _; rewrite /paper_main_point !mxE.
change ((List.nth (Nat.add (Nat.mul i d) j) (tval x) 0)^2 =
  List.nth (i*d+j)%N (tval x) 0 * List.nth (i*d+j)%N (tval x) 0).
have Hi : (i*d+j)%N = Nat.add (Nat.mul i d) j by rewrite mulnE addnE.
rewrite Hi; ring.
Qed.

Corollary paper_main_data_radius_good N d (x : paper_main_sample N d) :
  ~ paper_main_data_radius_event N d (2*sqrt (INR d)) x ->
  forall i, Nat.lt i N ->
    Rle (((paper_main_point x i)^T *m paper_main_point x i) 0 0)%R (4*INR d).
Proof.
intros Hgood i Hi.
assert (Hnorm : paper_main_data_point_norm d i (tval x) < 2*sqrt (INR d)).
{ apply Rnot_le_lt; intro Hbad; apply Hgood.
  apply paper_main_data_radius_eventE; exists i; auto. }
pose proof (sqrt_pos (INR d)).
pose proof (pow2_sqrt _ (pos_INR d)).
assert (Hpos : 0 <= paper_main_data_point_norm d i (tval x)).
{ unfold paper_main_data_point_norm; apply sqrt_pos. }
rewrite <- paper_main_data_point_norm_square; nra.
Qed.
