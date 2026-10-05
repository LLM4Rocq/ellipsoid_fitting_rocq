(* The actual head/tail compact value on the capped unit dual set, and the
   joint measurability of its threshold events. Data dimension S n; a head
   sample h of k rows and a tail sample x of q rows have the features
   W i = paper_main_head_feature h i (i < k) and V i = paper_main_head_feature x i
   (i < q). With
     Y_cap = paper_main_head_capped_dual q (S n) theta
           = {y | paper_main_gordon_dot q y y = 1 /\ forall i < q, |y_i| <= theta / sqrt (S n)},
   the compact value is the original value of PaperMainHeadSectionMinimax,
     value(h, x) = inf_(y in Y_cap) sup_(S in section(W)) <sum_(i<q) y_i V_i, S>.
   No net is chosen anywhere.
   - Y_cap contains the constant vector 1 / sqrt q when q, d > 0, theta > 0
     and d <= q theta^2 (paper_main_head_capped_dual_nonempty). If Y_cap is
     empty, the value is 0.
   - For kappa >= 1 every threshold event {c <= value} is measurable in the
     product space of (h, x), and the value is a measurable function.
   - For a fixed row permutation pi of the k + q rows, the value at the head
     and tail blocks of the permuted full sample has measurable threshold
     events with the product law of PaperMainHeadSelectionLaw. For a fixed
     list J of k distinct rows, pi can be chosen with head rows J in order and
     tail rows the other rows in increasing order (index identities and
     feature identities are returned). J is fixed, not chosen from the
     data. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  GaussianProbabilityDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductMeasure
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature PaperMainGeometryHeadWidth
  PaperMainGordonProcessCovariance PaperMainSampling PaperMainHeadLaw PaperMainDataSampleTail
  PaperMainGaussianResidualJoint PaperMainHeadSelectionLaw
  PaperMainHeadSectionMeasurable PaperMainHeadSectionMinimax PaperMainHeadSectionApprox.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* The capped unit dual set. *)

Definition paper_main_head_capped_dual (q d : nat) (theta : R) : (nat -> R) -> Prop :=
  fun y => paper_main_gordon_dot q y y = 1 /\
    forall i, (i < q)%N -> Rabs (y i) <= theta / sqrt (INR d).

Lemma paper_main_head_capped_dual_unit q d theta (y : nat -> R) :
  paper_main_head_capped_dual q d theta y -> paper_main_gordon_dot q y y = 1.
Proof. by case. Qed.

Lemma paper_main_head_constant_unit (q : nat) :
  (0 < q)%N ->
  paper_main_gordon_dot q (fun _ => / sqrt (INR q)) (fun _ => / sqrt (INR q)) = 1.
Proof.
move=> Hq.
have HqR : 0 < INR q by apply: lt_0_INR; apply/ssrnat.ltP.
rewrite /paper_main_gordon_dot finite_sum_const List.length_seq.
rewrite -Rinv_mult (sqrt_sqrt _ (Rlt_le _ _ HqR)).
by field; apply: Rgt_not_eq.
Qed.

Lemma paper_main_head_capped_dual_const (q d : nat) (theta : R) :
  (0 < q)%N -> (0 < d)%N -> 0 < theta -> INR d <= INR q * theta ^ 2 ->
  paper_main_head_capped_dual q d theta (fun _ => / sqrt (INR q)).
Proof.
move=> Hq Hd Ht Hdq.
have HqR : 0 < INR q by apply: lt_0_INR; apply/ssrnat.ltP.
have HdR : 0 < INR d by apply: lt_0_INR; apply/ssrnat.ltP.
have Hsq : 0 < sqrt (INR q) by apply: sqrt_lt_R0.
have Hsd : 0 < sqrt (INR d) by apply: sqrt_lt_R0.
split; first exact: paper_main_head_constant_unit.
move=> i _.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ (Rinv_0_lt_compat _ Hsq))).
have Hle : sqrt (INR d) <= theta * sqrt (INR q).
  have Hth : sqrt (theta ^ 2) = theta by apply: sqrt_pow2; exact: Rlt_le.
  rewrite -[X in _ <= X * _]Hth -(sqrt_mult _ _ (pow2_ge_0 theta) (Rlt_le _ _ HqR)).
  apply: sqrt_le_1_alt; nra.
have Hdiv : theta / sqrt (INR d) - / sqrt (INR q) =
    (theta * sqrt (INR q) - sqrt (INR d)) / (sqrt (INR d) * sqrt (INR q)).
  by field; split; apply: Rgt_not_eq.
have Hnn : 0 <= (theta * sqrt (INR q) - sqrt (INR d)) / (sqrt (INR d) * sqrt (INR q)).
  apply: Rmult_le_pos; first lra.
  by apply: Rlt_le; apply: Rinv_0_lt_compat; apply: Rmult_lt_0_compat.
lra.
Qed.

Theorem paper_main_head_capped_dual_nonempty (q d : nat) (theta : R) :
  (0 < q)%N -> (0 < d)%N -> 0 < theta -> INR d <= INR q * theta ^ 2 ->
  exists y, paper_main_head_capped_dual q d theta y.
Proof.
move=> Hq Hd Ht Hdq; exists (fun _ => / sqrt (INR q)).
exact: paper_main_head_capped_dual_const.
Qed.

Local Open Scope ring_scope.

(* The compact value of a head sample and a tail sample. *)

Definition paper_main_head_compact_value n k q (kappa theta : R)
    (h : paper_main_sample k (S n)) (x : paper_main_sample q (S n)) : R :=
  paper_main_head_section_minimax kappa q (paper_main_head_capped_dual q (S n) theta)
    (fun i : 'I_k => paper_main_head_feature h i) (fun i => paper_main_head_feature x i).

Lemma paper_main_head_compact_value_empty n k q (kappa theta : R) h x :
  ~ (exists y, paper_main_head_capped_dual q (S n) theta y) ->
  paper_main_head_compact_value n k q kappa theta h x = 0.
Proof. exact: paper_main_head_section_minimax_empty_dual. Qed.

Lemma paper_main_head_compact_feature_fst n k q (i : nat) (a b : 'I_(S n)) :
  measurable_fun [set: paper_main_sample k (S n) * paper_main_sample q (S n)]
    ((fun hx => paper_main_head_feature hx.1 i a b) : _ -> T).
Proof.
exact: (measurableT_comp (paper_main_gaussian_residual_feature_entry_measurable k (S n) i a b)
  measurable_fst).
Qed.

Lemma paper_main_head_compact_feature_snd n k q (i : nat) (a b : 'I_(S n)) :
  measurable_fun [set: paper_main_sample k (S n) * paper_main_sample q (S n)]
    ((fun hx => paper_main_head_feature hx.2 i a b) : _ -> T).
Proof.
exact: (measurableT_comp (paper_main_gaussian_residual_feature_entry_measurable q (S n) i a b)
  measurable_snd).
Qed.

Theorem paper_main_head_compact_value_ge_measurable n k q (kappa theta c : R) :
  1 <= kappa ->
  measurable [set hx : paper_main_sample k (S n) * paper_main_sample q (S n) |
    c <= paper_main_head_compact_value n k q kappa theta hx.1 hx.2].
Proof.
move=> Hk.
have [HY|HY] := pselect (exists y, paper_main_head_capped_dual q (S n) theta y).
  exact: (paper_main_head_section_minimax_ge_measurable n k kappa q _
    (fun i hx => paper_main_head_feature hx.1 i) (fun i hx => paper_main_head_feature hx.2 i)
    c Hk HY (@paper_main_head_capped_dual_unit q (S n) theta)
    (fun i a b => paper_main_head_compact_feature_fst n k q i a b)
    (fun i a b => paper_main_head_compact_feature_snd n k q i a b)).
have -> : [set hx : paper_main_sample k (S n) * paper_main_sample q (S n) |
    c <= paper_main_head_compact_value n k q kappa theta hx.1 hx.2] = [set _ | c <= 0].
  by apply/seteqP; split => hx /=; rewrite paper_main_head_compact_value_empty.
have [Hc|Hc] := pselect (c <= 0).
  have -> : [set _ : paper_main_sample k (S n) * paper_main_sample q (S n) | c <= 0] = setT.
    by apply/seteqP; split => hx.
  exact: measurableT.
have -> : [set _ : paper_main_sample k (S n) * paper_main_sample q (S n) | c <= 0] = set0.
  by apply/seteqP; split => hx // H; apply: Hc.
exact: measurable0.
Qed.

Theorem paper_main_head_compact_value_measurable n k q (kappa theta : R) :
  1 <= kappa ->
  measurable_fun [set: paper_main_sample k (S n) * paper_main_sample q (S n)]
    ((fun hx => paper_main_head_compact_value n k q kappa theta hx.1 hx.2) : _ -> T).
Proof.
move=> Hk.
have [HY|HY] := pselect (exists y, paper_main_head_capped_dual q (S n) theta y).
  exact: (paper_main_head_section_minimax_measurable n k kappa q _
    (fun i hx => paper_main_head_feature hx.1 i) (fun i hx => paper_main_head_feature hx.2 i)
    Hk HY (@paper_main_head_capped_dual_unit q (S n) theta)
    (fun i a b => paper_main_head_compact_feature_fst n k q i a b)
    (fun i a b => paper_main_head_compact_feature_snd n k q i a b)).
have -> : (fun hx : paper_main_sample k (S n) * paper_main_sample q (S n) =>
    paper_main_head_compact_value n k q kappa theta hx.1 hx.2) = (fun _ => 0).
  by apply: funext => hx; rewrite paper_main_head_compact_value_empty.
exact: measurable_cst.
Qed.

(* The full sample: head and tail blocks of a row permutation. *)

Theorem paper_main_head_compact_value_selection n k q (kappa theta c : R)
    (pi : 'S_(k + q)) :
  1 <= kappa ->
  measurable [set x : paper_main_sample (k + q) (S n) |
    c <= paper_main_head_compact_value n k q kappa theta
      (paper_main_head_selection k q (S n) pi x).1
      (paper_main_head_selection k q (S n) pi x).2] /\
  paper_main_probability (k + q) (S n) [set x : paper_main_sample (k + q) (S n) |
    c <= paper_main_head_compact_value n k q kappa theta
      (paper_main_head_selection k q (S n) pi x).1
      (paper_main_head_selection k q (S n) pi x).2] =
  (gaussian_product_law (k * S n)%N \x gaussian_product_law (q * S n)%N)%E
    [set hx | c <= paper_main_head_compact_value n k q kappa theta hx.1 hx.2].
Proof.
move=> Hk.
have mE := paper_main_head_compact_value_ge_measurable n k q kappa theta c Hk.
have -> : [set x : paper_main_sample (k + q) (S n) |
    c <= paper_main_head_compact_value n k q kappa theta
      (paper_main_head_selection k q (S n) pi x).1
      (paper_main_head_selection k q (S n) pi x).2] =
  paper_main_head_selection k q (S n) pi @^-1`
    [set hx | c <= paper_main_head_compact_value n k q kappa theta hx.1 hx.2] by [].
split.
  have H := paper_main_head_selection_measurable k q (S n) pi measurableT _ mE.
  by rewrite setTI in H.
exact: paper_main_head_selection_law.
Qed.

Corollary paper_main_head_compact_value_fixed n k q (kappa theta c : R) (J : seq nat) :
  1 <= kappa -> uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  exists pi : 'S_(k + q),
    (forall t : 'I_k, nat_of_ord (pi (lshift q t)) = nth 0%N J t) /\
    (forall u : 'I_q,
      nat_of_ord (pi (rshift k u)) = nth 0%N (paper_main_head_complement (k + q) J) u) /\
    (forall (x : paper_main_sample (k + q) (S n)) (t : 'I_k),
      paper_main_head_feature (paper_main_head_selection k q (S n) pi x).1 t =
      paper_main_head_feature x (nth 0%N J t)) /\
    (forall (x : paper_main_sample (k + q) (S n)) (u : 'I_q),
      paper_main_head_feature (paper_main_head_selection k q (S n) pi x).2 u =
      paper_main_head_feature x (nth 0%N (paper_main_head_complement (k + q) J) u)) /\
    measurable [set x : paper_main_sample (k + q) (S n) |
      c <= paper_main_head_compact_value n k q kappa theta
        (paper_main_head_selection k q (S n) pi x).1
        (paper_main_head_selection k q (S n) pi x).2] /\
    paper_main_probability (k + q) (S n) [set x : paper_main_sample (k + q) (S n) |
      c <= paper_main_head_compact_value n k q kappa theta
        (paper_main_head_selection k q (S n) pi x).1
        (paper_main_head_selection k q (S n) pi x).2] =
    (gaussian_product_law (k * S n)%N \x gaussian_product_law (q * S n)%N)%E
      [set hx | c <= paper_main_head_compact_value n k q kappa theta hx.1 hx.2].
Proof.
move=> Hk HJu HJs HJa.
have [pi [Hh Ht]] := paper_main_head_selection_perm_exists k q J HJu HJs HJa.
exists pi; split => //; split => //.
split.
  by move=> x t; rewrite paper_main_head_selection_head_feature Hh.
split.
  by move=> x u; rewrite paper_main_head_selection_tail_feature Ht.
exact: paper_main_head_compact_value_selection.
Qed.
