(* Finite-prior hybrid and data losses on full data rows.

   Fix a head dimension r, a bulk dimension m = mi + 1 and
   D = paper_main_symmetric_dimension mi. A finite nonempty prior I of state
   indices carries triples (Hs j, Bs j, bs j). A data row of length r + m is
   (g, y) and a hybrid row of length r + D is (g, z). The offset of state j
   on a row is the head value g^T H_j g - Tr H_j - b_j. The data row loss is
   phi (offset + y^T B_j y - Tr B_j) (pmdf_quad) and the hybrid row loss is
   phi (offset + linear_form D (goe_loading mi B_j) z), with
   phi (t) = 1 - exp (- t^2). The entropy-shifted normalized soft minima of
   the two loss arrays (PaperMainLossNormalizedArray) are Z_data and Z_goe.
   1. The loss array is the finite sum of the losses of its rows.
   2. Both row losses are continuous with values in [0, 1], so Z_data and
      Z_goe are regular with values in [0, 1].
   3. For symmetric B the GOE loading reads the A24 bulk value:
      linear_form D (goe_loading mi B) z = sqrt (mi + 1) <G_i, B> when z is
      row i of the bulk array.
   4. The row layout and the head-prefix/bulk-suffix layout of A24 differ by
      a coordinate permutation. Its tuple map is measurable and keeps the
      product law (PaperMainGaussianPermutationLaw), so every event of the
      split layout has the same probability in the row layout.
   5. On a hybrid row-layout tuple, the loss array of state j is N times the
      A24 hybrid risk of the residual at (H_j, b_j, B_j). r = 0 is included. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums GaussianCovarianceLinear
  GaussianProductDefinitions GaussianProduct GaussianCoordinateDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductMeasure
  GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainMatrixTransport
  PaperMainGaussianFeatureCoordinates PaperMainGaussianPublicFeature PaperMainConeGaussianCoordinates
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments
  PaperMainProjectionRegular PaperMainProjectionPublic PaperMainTranslatedLoss
  PaperMainLossArray PaperMainLossRowIncrement PaperMainLossSoftNormalized PaperMainLossNormalizedArray
  PaperMainSampling PaperMainHeadLaw PaperMainGaussianPermutationLaw
  PaperMainHeadSmallBallNet PaperMainProjectedBulkComplement PaperMainHybridResidual PaperMainHybridLoss.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. The loss array is the sum of its row losses. *)

Lemma paper_main_hybrid_finite_array_sum p N (ell : nat -> nat -> list R -> R)
    (xs : list R) (j : nat) :
  paper_main_loss_array p N ell xs j =
  \sum_(i < N) ell i j (List.firstn p (List.skipn (i * p)%N xs)).
Proof.
elim: N ell xs => [|N IH] ell xs; first by rewrite big_ord0.
rewrite big_ord_recl /= IH RplusE.
congr (_ + _); apply: eq_bigr => i _.
by rewrite List.skipn_skipn /bump leq0n add1n plusE mulSn addnC.
Qed.

(* 2. Rows, offsets and row losses. *)

Definition paper_main_hybrid_finite_head r (row : list R) : 'cV[R]_r :=
  \col_(k < r) List.nth k row 0.

Lemma paper_main_hybrid_finite_head_app r (xs ys : list R) :
  length xs = r ->
  paper_main_hybrid_finite_head r (xs ++ ys)%list = paper_main_hybrid_finite_head r xs.
Proof.
move=> Hxs; apply/matrixP => k l; rewrite !mxE List.app_nth1 // Hxs.
exact/ssrnat.ltP.
Qed.

Definition paper_main_hybrid_finite_offset r (Hs : nat -> 'M[R]_r) (bs : nat -> R)
    (j : nat) (row : list R) : R :=
  paper_main_head_small_ball_value (Hs j) (bs j) (paper_main_hybrid_finite_head r row).

Lemma paper_main_hybrid_finite_offset_regular r q Hs bs j :
  pmdf_regular (r + q)%coq_nat (paper_main_hybrid_finite_offset r Hs bs j).
Proof.
apply: (pmdf_regular_ext _ (fun row => (\sum_(a < r) \sum_(c < r)
    (Hs j a c * (List.nth a row 0 * List.nth c row 0))%Rcoq) +
    (- (paper_main_trace (Hs j) + bs j)))%Rcoq).
  move=> row; rewrite /paper_main_hybrid_finite_offset /paper_main_head_small_ball_value
    /paper_main_quadratic_form.
  have -> : \sum_(i < r) \sum_(c < r) paper_main_hybrid_finite_head r row i 0 * Hs j i c *
      paper_main_hybrid_finite_head r row c 0 =
      \sum_(a < r) \sum_(c < r) (Hs j a c * (List.nth a row 0 * List.nth c row 0))%Rcoq.
    apply: eq_bigr => a _; apply: eq_bigr => c _; rewrite !mxE.
    have E : forall x h y : R, (x * h * y = h * (x * y))%Rcoq by move=> x h y; ring.
    exact: E.
  have E : forall s t b : R, (s + - (t + b) = s - t - b)%Rcoq by move=> s t b; ring.
  exact: E.
apply: pmdf_regular_add; last exact: pmdf_regular_const.
apply: (pmdf_bigsum _ r _ _).1 => a.
apply: (pmdf_bigsum _ r _ _).1 => c.
apply: pmdf_regular_scale; apply: pmdf_regular_mult; apply: pmdf_regular_nth.
  by have := ltn_ord a; move/ssrnat.ltP; lia.
by have := ltn_ord c; move/ssrnat.ltP; lia.
Qed.

(* The data row loss phi (offset + y^T B_j y - Tr B_j) on rows (g, y) of
   length r + (mi + 1), and the hybrid row loss
   phi (offset + linear_form D (goe_loading mi B_j) z) on rows (g, z) of
   length r + D. They do not depend on the row index. *)

Definition paper_main_hybrid_finite_data_loss r mi (Hs : nat -> 'M[R]_r) (bs : nat -> R)
    (Bs : nat -> 'M[R]_(S mi)) (i j : nat) (row : list R) : R :=
  paper_main_loss (paper_main_hybrid_finite_offset r Hs bs j row +
    pmdf_quad mi (Bs j) (List.skipn r row)).

Definition paper_main_hybrid_finite_goe_loss r mi (Hs : nat -> 'M[R]_r) (bs : nat -> R)
    (Bs : nat -> 'M[R]_(S mi)) (i j : nat) (row : list R) : R :=
  paper_main_loss (paper_main_hybrid_finite_offset r Hs bs j row +
    linear_form (paper_main_symmetric_dimension mi)
      (paper_main_projection_goe_loading mi (Bs j)) (List.skipn r row)).

Lemma paper_main_hybrid_finite_data_loss_continuous r mi Hs bs Bs i j :
  finite_joint_continuous (r + S mi)%coq_nat
    (paper_main_hybrid_finite_data_loss r mi Hs bs Bs i j).
Proof.
have -> : paper_main_hybrid_finite_data_loss r mi Hs bs Bs i j =
    (fun row => paper_main_loss (0 + (paper_main_hybrid_finite_offset r Hs bs j row +
      pmdf_quad mi (Bs j) (List.skipn r row))))%Rcoq.
  by apply: functional_extensionality => row; rewrite Rplus_0_l.
apply: paper_main_loss_joint_continuous.
apply: GaussianCoordinatePolynomialContinuity.finite_joint_continuous_add.
  exact: (paper_main_hybrid_finite_offset_regular r (S mi) Hs bs j).1.
exact: (paper_main_loss_skipn_continuous r (S mi) _ (pmdf_quad_regular mi (Bs j)).1).
Qed.

Lemma paper_main_hybrid_finite_goe_loss_continuous r mi Hs bs Bs i j :
  finite_joint_continuous (r + paper_main_symmetric_dimension mi)%coq_nat
    (paper_main_hybrid_finite_goe_loss r mi Hs bs Bs i j).
Proof.
have -> : paper_main_hybrid_finite_goe_loss r mi Hs bs Bs i j =
    (fun row => paper_main_loss (0 + (paper_main_hybrid_finite_offset r Hs bs j row +
      linear_form (paper_main_symmetric_dimension mi)
        (paper_main_projection_goe_loading mi (Bs j)) (List.skipn r row))))%Rcoq.
  by apply: functional_extensionality => row; rewrite Rplus_0_l.
apply: paper_main_loss_joint_continuous.
apply: GaussianCoordinatePolynomialContinuity.finite_joint_continuous_add.
  exact: (paper_main_hybrid_finite_offset_regular r _ Hs bs j).1.
exact: (paper_main_loss_skipn_continuous r _ _
  (paper_main_projection_regular_linear _ _).1).
Qed.

Lemma paper_main_hybrid_finite_data_loss_bounds r mi Hs bs Bs i j row :
  (0 <= paper_main_hybrid_finite_data_loss r mi Hs bs Bs i j row <= 1)%Rcoq.
Proof. exact: paper_main_loss_bounds. Qed.

Lemma paper_main_hybrid_finite_goe_loss_bounds r mi Hs bs Bs i j row :
  (0 <= paper_main_hybrid_finite_goe_loss r mi Hs bs Bs i j row <= 1)%Rcoq.
Proof. exact: paper_main_loss_bounds. Qed.

(* The two normalized finite soft losses on N full rows. *)

Definition paper_main_hybrid_finite_data N r mi beta (I : list nat) Hs bs Bs :=
  paper_main_loss_normalized_array (r + S mi)%coq_nat N beta I
    (paper_main_hybrid_finite_data_loss r mi Hs bs Bs).

Definition paper_main_hybrid_finite_goe N r mi beta (I : list nat) Hs bs Bs :=
  paper_main_loss_normalized_array (r + paper_main_symmetric_dimension mi)%coq_nat N beta I
    (paper_main_hybrid_finite_goe_loss r mi Hs bs Bs).

Lemma paper_main_hybrid_finite_data_regular N r mi beta I Hs bs Bs :
  I <> nil -> (0 < beta)%Rcoq ->
  pmdf_regular (N * (r + S mi))%coq_nat (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs).
Proof.
move=> HI Hb; apply: paper_main_loss_normalized_array_regular => //.
  by move=> i j _ _; exact: paper_main_hybrid_finite_data_loss_continuous.
by move=> i j xs _ _ _; exact: paper_main_hybrid_finite_data_loss_bounds.
Qed.

Lemma paper_main_hybrid_finite_goe_regular N r mi beta I Hs bs Bs :
  I <> nil -> (0 < beta)%Rcoq ->
  pmdf_regular (N * (r + paper_main_symmetric_dimension mi))%coq_nat
    (paper_main_hybrid_finite_goe N r mi beta I Hs bs Bs).
Proof.
move=> HI Hb; apply: paper_main_loss_normalized_array_regular => //.
  by move=> i j _ _; exact: paper_main_hybrid_finite_goe_loss_continuous.
by move=> i j xs _ _ _; exact: paper_main_hybrid_finite_goe_loss_bounds.
Qed.

Lemma paper_main_hybrid_finite_goe_bounds N r mi beta I Hs bs Bs xs :
  (0 < N)%coq_nat -> I <> nil -> (0 < beta)%Rcoq ->
  length xs = (N * (r + paper_main_symmetric_dimension mi))%coq_nat ->
  (0 <= paper_main_hybrid_finite_goe N r mi beta I Hs bs Bs xs <= 1)%Rcoq.
Proof.
move=> HN HI Hb Hxs; apply: paper_main_loss_normalized_array_bounds => //.
by move=> i j ys _ _ _; exact: paper_main_hybrid_finite_goe_loss_bounds.
Qed.

(* 3. The GOE loading reads the A24 bulk value. *)

Lemma paper_main_hybrid_finite_goe_bulk N mi
    (x : (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R))
    (B : 'M[R]_(S mi)) (i : 'I_N) (zs : list R) :
  paper_main_symmetric B ->
  (forall k, (k < paper_main_symmetric_dimension mi)%coq_nat ->
     List.nth k zs 0 = List.nth (i * paper_main_symmetric_dimension mi + k)%coq_nat (tval x) 0) ->
  linear_form (paper_main_symmetric_dimension mi) (paper_main_projection_goe_loading mi B) zs =
  (sqrt (INR (S mi)) *
   paper_main_pairing (paper_main_public_gaussian_row mi i (tval x)) B)%Rcoq.
Proof.
move=> HB Hz.
have := congr1 (fun M : 'cV[R]_N => M i 0) (paper_main_hybrid_bulk_value_code N mi x B HB).
rewrite /paper_main_hybrid_bulk_value /paper_main_projected_bulk_vector !mxE => ->.
rewrite /linear_form /paper_main_projection_goe_loading -RmultE -finite_sum_scale.
apply: finite_sum_ext => k Hk.
have HkD : (k < paper_main_symmetric_dimension mi)%coq_nat.
  by have := proj2 (proj1 (List.in_seq _ _ _) Hk); lia.
rewrite (Hz k HkD) /paper_main_cone_code -RmultE.
have E : forall a b c : R, (a * b * c = a * (b * c))%Rcoq by move=> a b c; ring.
exact: E.
Qed.

(* 4. The row layout and the split layout. Position j of the split layout
   (heads of the N rows, then their bulks) comes from position
   paper_main_hybrid_finite_source N p q j of the row layout (N rows of
   p + q coordinates). *)

Definition paper_main_hybrid_finite_source N p q (j : nat) : nat :=
  if (j < N * p)%N then (j %/ p * (p + q) + j %% p)%N
  else ((j - N * p) %/ q * (p + q) + p + (j - N * p) %% q)%N.

Lemma paper_main_hybrid_finite_source_lt N p q j :
  (j < N * (p + q))%N -> (paper_main_hybrid_finite_source N p q j < N * (p + q))%N.
Proof.
move=> Hj; rewrite /paper_main_hybrid_finite_source.
case: ifP => Hjp.
  have Hp : (0 < p)%N by case: p Hjp {Hj} => [|p]; rewrite ?muln0.
  have Ha : (j %/ p < N)%N by rewrite ltn_divLR // mulnC.
  have Hb : (j %% p < p)%N by rewrite ltn_pmod.
  move: Ha Hb => /ssrnat.ltP Ha /ssrnat.ltP Hb; apply/ssrnat.ltP.
  rewrite -?multE -?plusE in Ha Hb *; nia.
have Hjp' : (N * p <= j)%N by rewrite leqNgt Hjp.
have Hq : (0 < q)%N.
  case: q Hj => [|q] Hj //.
  by rewrite addn0 in Hj; move: Hjp; rewrite Hj.
have Hj' : (j - N * p < N * q)%N.
  move: Hj Hjp' => /ssrnat.ltP Hj /ssrnat.leP Hjp'; apply/ssrnat.ltP.
  rewrite -?multE -?minusE -?plusE in Hj Hjp' *; nia.
have Ha : ((j - N * p) %/ q < N)%N by rewrite ltn_divLR // mulnC.
have Hb : ((j - N * p) %% q < q)%N by rewrite ltn_pmod.
move: Ha Hb => /ssrnat.ltP Ha /ssrnat.ltP Hb; apply/ssrnat.ltP.
rewrite -?multE -?plusE in Ha Hb *; nia.
Qed.

Lemma paper_main_hybrid_finite_divmod a b d :
  (b < d)%N -> (a * d + b) %/ d = a /\ (a * d + b) %% d = b.
Proof.
move=> Hb; have Hd : (0 < d)%N by apply: leq_ltn_trans Hb.
split; first by rewrite divnMDl // divn_small // addn0.
by rewrite modnMDl modn_small.
Qed.

Lemma paper_main_hybrid_finite_source_inj N p q j1 j2 :
  (j1 < N * (p + q))%N -> (j2 < N * (p + q))%N ->
  paper_main_hybrid_finite_source N p q j1 = paper_main_hybrid_finite_source N p q j2 ->
  j1 = j2.
Proof.
move=> Hj1 Hj2; rewrite /paper_main_hybrid_finite_source.
have Hhead : forall j, (j < N * p)%N -> (j %% p < p + q)%N /\ (j %% p < p)%N.
  move=> j Hj; have Hp : (0 < p)%N by case: p Hj {Hj1 Hj2} => [|p]; rewrite ?muln0.
  have H := ltn_pmod j Hp; split => //; exact: leq_trans H (leq_addr q p).
have Hbulk : forall j, (j < N * (p + q))%N -> ~~ (j < N * p)%N ->
    (p + (j - N * p) %% q < p + q)%N.
  move=> j Hj Hjp.
  have Hq : (0 < q)%N.
    case: q Hj {Hj1 Hj2 Hhead} => [|q] Hj //.
    by rewrite addn0 in Hj; move: Hjp; rewrite Hj.
  by rewrite ltn_add2l ltn_pmod.
case: ifP => H1; case: ifP => H2 E.
- have [Hb1 _] := Hhead j1 H1; have [Hb2 _] := Hhead j2 H2.
  have [Ea1 Eb1] := paper_main_hybrid_finite_divmod (j1 %/ p) (j1 %% p) (p + q) Hb1.
  have [Ea2 Eb2] := paper_main_hybrid_finite_divmod (j2 %/ p) (j2 %% p) (p + q) Hb2.
  rewrite E in Ea1 Eb1.
  have Ea : j1 %/ p = j2 %/ p by rewrite -Ea1 Ea2.
  have Eb : j1 %% p = j2 %% p by rewrite -Eb1 Eb2.
  by rewrite (divn_eq j1 p) (divn_eq j2 p) Ea Eb.
- have [Hb1' Hb1] := Hhead j1 H1.
  have [_ Eb1] := paper_main_hybrid_finite_divmod (j1 %/ p) (j1 %% p) (p + q) Hb1'.
  have [_ Eb2] := paper_main_hybrid_finite_divmod ((j2 - N * p) %/ q)
    (p + (j2 - N * p) %% q) (p + q) (Hbulk j2 Hj2 (negbT H2)).
  rewrite addnA -E Eb1 in Eb2.
  by move: Hb1; rewrite Eb2 ltnNge leq_addr.
- have [Hb2' Hb2] := Hhead j2 H2.
  have [_ Eb2] := paper_main_hybrid_finite_divmod (j2 %/ p) (j2 %% p) (p + q) Hb2'.
  have [_ Eb1] := paper_main_hybrid_finite_divmod ((j1 - N * p) %/ q)
    (p + (j1 - N * p) %% q) (p + q) (Hbulk j1 Hj1 (negbT H1)).
  rewrite addnA E Eb2 in Eb1.
  by move: Hb2; rewrite Eb1 ltnNge leq_addr.
- have [Ea1 Eb1] := paper_main_hybrid_finite_divmod ((j1 - N * p) %/ q)
    (p + (j1 - N * p) %% q) (p + q) (Hbulk j1 Hj1 (negbT H1)).
  have [Ea2 Eb2] := paper_main_hybrid_finite_divmod ((j2 - N * p) %/ q)
    (p + (j2 - N * p) %% q) (p + q) (Hbulk j2 Hj2 (negbT H2)).
  rewrite addnA E in Ea1 Eb1; rewrite addnA in Ea2 Eb2.
  rewrite Ea2 in Ea1; rewrite Eb2 in Eb1.
  move/addnI: Eb1 => Eb1.
  have Ediff : (j1 - N * p = j2 - N * p)%N.
    by rewrite (divn_eq (j1 - N * p) q) (divn_eq (j2 - N * p) q) Ea1 Eb1.
  have Hj1p : (N * p <= j1)%N by rewrite leqNgt H1.
  have Hj2p : (N * p <= j2)%N by rewrite leqNgt H2.
  by rewrite -(subnK Hj1p) -(subnK Hj2p) Ediff.
Qed.

Lemma paper_main_hybrid_finite_source_head N p q i k :
  (i < N)%N -> (k < p)%N ->
  paper_main_hybrid_finite_source N p q (i * p + k) = (i * (p + q) + k)%N.
Proof.
move=> Hi Hk; rewrite /paper_main_hybrid_finite_source.
have Hlt : (i * p + k < N * p)%N.
  move: Hi Hk => /ssrnat.ltP Hi /ssrnat.ltP Hk; apply/ssrnat.ltP.
  rewrite -?multE -?plusE in Hi Hk *; nia.
have [Ea Eb] := paper_main_hybrid_finite_divmod i k p Hk.
by rewrite Hlt Ea Eb.
Qed.

Lemma paper_main_hybrid_finite_source_bulk N p q i k :
  (i < N)%N -> (k < q)%N ->
  paper_main_hybrid_finite_source N p q (N * p + (i * q + k)) = (i * (p + q) + p + k)%N.
Proof.
move=> Hi Hk; rewrite /paper_main_hybrid_finite_source.
have Hge : (N * p + (i * q + k) < N * p)%N = false by rewrite ltnNge leq_addr.
have [Ea Eb] := paper_main_hybrid_finite_divmod i k q Hk.
by rewrite Hge addKn Ea Eb.
Qed.

Definition paper_main_hybrid_finite_source_ord N p q (j : 'I_(N * (p + q))) :
    'I_(N * (p + q)) :=
  Ordinal (paper_main_hybrid_finite_source_lt N p q j (ltn_ord j)).

Lemma paper_main_hybrid_finite_source_ord_inj N p q :
  injective (paper_main_hybrid_finite_source_ord N p q).
Proof.
move=> j1 j2 /(congr1 val) /= E; apply: val_inj.
exact: (paper_main_hybrid_finite_source_inj N p q j1 j2 (ltn_ord j1) (ltn_ord j2) E).
Qed.

Definition paper_main_hybrid_finite_perm N p q : 'S_(N * (p + q)) :=
  perm (paper_main_hybrid_finite_source_ord_inj N p q).

(* The split-layout pair (heads, bulks) of a row-layout tuple. *)

Definition paper_main_hybrid_finite_split N p q
    (x : (N * (p + q)).-tuple (measurableTypeR R)) :
    (N * p).-tuple (measurableTypeR R) * (N * q).-tuple (measurableTypeR R) :=
  paper_main_split_coordinates (N * p) (N * q)
    (tcast (mulnDr N p q) (paper_main_permute_tuple (paper_main_hybrid_finite_perm N p q) x)).

Lemma paper_main_hybrid_finite_split_measurable N p q :
  measurable_fun [set: (N * (p + q)).-tuple (measurableTypeR R)]
    (paper_main_hybrid_finite_split N p q).
Proof.
apply: (measurableT_comp (paper_main_split_coordinates_measurable _ _)).
apply: (measurableT_comp (paper_main_tcast_measurable _ _ _)).
exact: paper_main_permute_tuple_measurable.
Qed.

(* Every split-layout event has the same probability in the row layout. *)

Theorem paper_main_hybrid_finite_split_law N p q
    (E : set ((N * p).-tuple (measurableTypeR R) * (N * q).-tuple (measurableTypeR R))) :
  measurable E ->
  gaussian_product_law (N * (p + q)) (paper_main_hybrid_finite_split N p q @^-1` E) =
  gaussian_product_law (Nat.add (N * p) (N * q))
    (paper_main_split_coordinates (N * p) (N * q) @^-1` E).
Proof.
move=> mE.
set E' := paper_main_split_coordinates (N * p) (N * q) @^-1` E.
have mE' : measurable E'.
  have := paper_main_split_coordinates_measurable (N * p) (N * q) measurableT E mE.
  by rewrite setTI.
have mE'' : measurable (tcast (mulnDr N p q) @^-1` E').
  have := paper_main_tcast_measurable _ _ (mulnDr N p q) measurableT E' mE'.
  by rewrite setTI.
change (gaussian_product_law (N * (p + q))
  (paper_main_permute_tuple (paper_main_hybrid_finite_perm N p q) @^-1`
    (tcast (mulnDr N p q) @^-1` E')) = gaussian_product_law (Nat.add (N * p) (N * q)) E').
rewrite paper_main_permute_tuple_law //.
exact: paper_main_tcast_law.
Qed.

(* Coordinates of the split pair. *)

Lemma paper_main_hybrid_finite_take_nth k m
    (x : (Nat.add k m).-tuple (measurableTypeR R)) l :
  (l < k)%coq_nat ->
  List.nth l (tval (paper_main_take_coordinates k m x)) 0 = List.nth l (tval x) 0.
Proof.
elim: k x l => [|k IH] x l Hl; first lia.
case: l Hl => [|l] Hl.
- change (tnth x ord0 = List.nth 0 (tval x) 0).
  by rewrite gpp_nthE (tnth_nth 0%R).
- change (List.nth l (tval (paper_main_take_coordinates k m
    (paper_main_tail_coordinate (Nat.add k m) x))) 0 = List.nth (S l) (tval x) 0).
  rewrite (IH _ l ltac:(lia)).
  change (List.nth l (behead (tval x)) 0 = List.nth (S l) (tval x) 0).
  by case: (tval x) => [|a xs] //=; case: l {IH Hl}.
Qed.

Lemma paper_main_hybrid_finite_permute_nth N p q
    (x : (N * (p + q)).-tuple (measurableTypeR R)) j :
  (j < N * (p + q))%N ->
  List.nth j (tval (paper_main_permute_tuple (paper_main_hybrid_finite_perm N p q) x)) 0 =
  List.nth (paper_main_hybrid_finite_source N p q j) (tval x) 0.
Proof.
move=> Hj.
have E1 : List.nth j (tval (paper_main_permute_tuple (paper_main_hybrid_finite_perm N p q) x)) 0 =
    tnth (paper_main_permute_tuple (paper_main_hybrid_finite_perm N p q) x) (Ordinal Hj).
  by rewrite gpp_nthE (tnth_nth 0).
rewrite E1 paper_main_permute_tuple_tnth permE (tnth_nth 0) -gpp_nthE.
by [].
Qed.

Lemma paper_main_hybrid_finite_split_head N p q
    (x : (N * (p + q)).-tuple (measurableTypeR R)) i k :
  (i < N)%N -> (k < p)%N ->
  List.nth (i * p + k)%N (tval (paper_main_hybrid_finite_split N p q x).1) 0 =
  List.nth (i * (p + q) + k)%N (tval x) 0.
Proof.
move=> Hi Hk.
have Hlt : (i * p + k < N * p)%N.
  move: Hi Hk => /ssrnat.ltP Hi /ssrnat.ltP Hk; apply/ssrnat.ltP.
  rewrite -?multE -?plusE in Hi Hk *; nia.
have Hlt' : (i * p + k < N * (p + q))%N.
  by apply: leq_trans Hlt _; rewrite leq_mul2l leq_addr orbT.
rewrite /paper_main_hybrid_finite_split /paper_main_split_coordinates /=.
rewrite (paper_main_hybrid_finite_take_nth _ _ _ _ (elimT ssrnat.ltP Hlt)).
by rewrite val_tcast paper_main_hybrid_finite_permute_nth // paper_main_hybrid_finite_source_head.
Qed.

Lemma paper_main_hybrid_finite_split_bulk N p q
    (x : (N * (p + q)).-tuple (measurableTypeR R)) i k :
  (i < N)%N -> (k < q)%N ->
  List.nth (i * q + k)%N (tval (paper_main_hybrid_finite_split N p q x).2) 0 =
  List.nth (i * (p + q) + p + k)%N (tval x) 0.
Proof.
move=> Hi Hk.
have Hlt : (N * p + (i * q + k) < N * (p + q))%N.
  move: Hi Hk => /ssrnat.ltP Hi /ssrnat.ltP Hk; apply/ssrnat.ltP.
  rewrite -?multE -?plusE in Hi Hk *; nia.
rewrite /paper_main_hybrid_finite_split /paper_main_split_coordinates /=.
rewrite paper_main_drop_coordinates_nth val_tcast plusE.
by rewrite paper_main_hybrid_finite_permute_nth // paper_main_hybrid_finite_source_bulk.
Qed.

Lemma paper_main_hybrid_finite_row_nth p (xs : list R) i k :
  (k < p)%N ->
  List.nth k (List.firstn p (List.skipn (i * p)%N xs)) 0 = List.nth (i * p + k)%N xs 0.
Proof.
move=> Hk; rewrite List.nth_firstn.
have -> : Nat.ltb k p = true by apply/Nat.ltb_lt/ssrnat.ltP.
by rewrite List.nth_skipn plusE.
Qed.

(* 5. On a hybrid row-layout tuple, the loss array of state j is N times
   the A24 hybrid risk of the residual at (H_j, b_j, B_j). *)

Theorem paper_main_hybrid_finite_goe_array N r mi Hs bs Bs
    (x : (N * (r + paper_main_symmetric_dimension mi)).-tuple (measurableTypeR R)) (j : nat) :
  paper_main_symmetric (Bs j) ->
  paper_main_loss_array (r + paper_main_symmetric_dimension mi)%coq_nat N
    (paper_main_hybrid_finite_goe_loss r mi Hs bs Bs) (tval x) j =
  (INR N * paper_main_hybrid_risk N (paper_main_hybrid_residual N r mi
     (paper_main_hybrid_finite_split N r (paper_main_symmetric_dimension mi) x).1
     (paper_main_hybrid_finite_split N r (paper_main_symmetric_dimension mi) x).2
     (Hs j) (bs j) (Bs j)))%Rcoq.
Proof.
move=> HB.
set D := paper_main_symmetric_dimension mi.
set h := (paper_main_hybrid_finite_split N r D x).1.
set xb := (paper_main_hybrid_finite_split N r D x).2.
rewrite paper_main_hybrid_finite_array_sum /paper_main_hybrid_risk.
have Hsum : \sum_(i < N) paper_main_hybrid_finite_goe_loss r mi Hs bs Bs i j
      (List.firstn (r + D)%coq_nat (List.skipn (i * (r + D)%coq_nat)%N (tval x))) =
    \sum_(i < N) paper_main_loss (paper_main_hybrid_residual N r mi h xb (Hs j) (bs j) (Bs j) i 0).
  apply: eq_bigr => i _.
  rewrite /paper_main_hybrid_finite_goe_loss /paper_main_hybrid_residual
    /paper_main_hybrid_head_value !mxE.
  congr (paper_main_loss (_ + _)).
  - rewrite /paper_main_hybrid_finite_offset; congr paper_main_head_small_ball_value.
    apply/matrixP => k l; rewrite [l]ord1 !mxE.
    have Hk : (k < (r + D)%coq_nat)%N by rewrite plusE ltn_addr.
    rewrite (paper_main_hybrid_finite_row_nth _ _ _ _ Hk).
    by rewrite (paper_main_hybrid_finite_split_head _ _ _ _ _ _ (ltn_ord i) (ltn_ord k)).
  - apply: paper_main_hybrid_finite_goe_bulk => // k Hk.
    rewrite List.nth_skipn plusE.
    have Hrk : (r + k < (r + D)%coq_nat)%N by rewrite plusE ltn_add2l; apply/ssrnat.ltP.
    rewrite (paper_main_hybrid_finite_row_nth _ _ _ _ Hrk).
    have HkD : (k < D)%N by apply/ssrnat.ltP.
    rewrite [in RHS](paper_main_hybrid_finite_split_bulk _ _ _ _ _ _ (ltn_ord i) HkD).
    by rewrite -addnA.
rewrite Hsum.
have key : forall (n : nat) (f : 'I_n -> R),
    \sum_(i < n) f i = (INR n * ((\sum_(i < n) f i) / INR n))%Rcoq.
  move=> [|n] f; first by rewrite big_ord0 /= Rmult_0_l.
  have Hn : INR n.+1 <> 0%Rcoq by apply: not_0_INR.
  have E : forall s a : R, (a <> 0 -> s = a * (s / a))%Rcoq by move=> s a Ha; field.
  exact: E.
exact: key.
Qed.

(* If every state of the prior has hybrid risk at least e at the split pair
   of x, then Z_goe (x) >= e, for every beta > 0. *)

Corollary paper_main_hybrid_finite_goe_gap N r mi beta (I : list nat) Hs bs Bs
    (x : (N * (r + paper_main_symmetric_dimension mi)).-tuple (measurableTypeR R)) (e : R) :
  (0 < N)%coq_nat -> I <> nil -> (0 < beta)%Rcoq ->
  (forall j, In j I -> paper_main_symmetric (Bs j)) ->
  (forall j, In j I ->
     (e <= paper_main_hybrid_risk N (paper_main_hybrid_residual N r mi
        (paper_main_hybrid_finite_split N r (paper_main_symmetric_dimension mi) x).1
        (paper_main_hybrid_finite_split N r (paper_main_symmetric_dimension mi) x).2
        (Hs j) (bs j) (Bs j)))%Rcoq) ->
  (e <= paper_main_hybrid_finite_goe N r mi beta I Hs bs Bs (tval x))%Rcoq.
Proof.
move=> HN HI Hb HB Hgap.
apply: paper_main_loss_normalized_array_gap => // j Hj.
rewrite (paper_main_hybrid_finite_goe_array N r mi Hs bs Bs x j (HB j Hj)).
apply: Rmult_le_compat_l; [exact: pos_INR | exact: Hgap].
Qed.
