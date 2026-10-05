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

Local Open Scope ring_scope.

(* The compact value of a head sample and a tail sample. *)

Definition paper_main_head_compact_value n k q (kappa theta : R)
    (h : paper_main_sample k (S n)) (x : paper_main_sample q (S n)) : R :=
  paper_main_head_section_minimax kappa q (paper_main_head_capped_dual q (S n) theta)
    (fun i : 'I_k => paper_main_head_feature h i) (fun i => paper_main_head_feature x i).

Lemma paper_main_head_compact_feature_fst n k q (i : nat) (a b : 'I_(S n)) :
  measurable_fun [set: paper_main_sample k (S n) * paper_main_sample q (S n)]
    ((fun hx => paper_main_head_feature hx.1 i a b) : _ -> T).
Proof.
exact: (measurableT_comp (paper_main_gaussian_residual_feature_entry_measurable k (S n) i a b)
  measurable_fst).
Qed.

(* The full sample: head and tail blocks of a row permutation. *)
