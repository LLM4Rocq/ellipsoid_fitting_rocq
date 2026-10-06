(* The compact head/tail value with coordinate-clipped tail features, and
   its agreement with the raw value outside the coordinate event. The
   clipped feature of tail row i is
     paper_main_data_clipped_feature U n i (tval x)
   (Data.Clipped: every coordinate clipped to [-U, U]); the head
   features stay raw. The clipped compact value
   paper_main_head_compact_clipped_value is the section minimax of
   Head.SectionMinimax on the capped unit dual set
   paper_main_head_capped_dual q (S n) theta with these tail features, as
   paper_main_head_compact_value (Head.CompactEvent) is with the
   raw ones.
   - The minimax only sees the tail features of index i < q
     (paper_main_head_compact_minimax_ext).
   - Outside the coordinate event paper_main_data_coordinate_event q (S n) U
     of the tail sample (some coordinate with |.| >= U), every clipped tail
     feature equals the raw one, so the clipped and raw compact values are
     equal (paper_main_head_compact_clipped_eq). For a row permutation of
     a full sample outside its coordinate event, the tail of the selection
     is outside the coordinate event of the tail sample
     (paper_main_head_compact_coordinate_tail).
   - For kappa >= 1 the clipped compact value is measurable in (h, x)
     (paper_main_head_compact_clipped_measurable).
   - The clipped operator-good event
     {|sum_i y_i Vclip_i|_F <= L |y|_2 for all y} is measurable, and
     outside the coordinate event it is the raw operator-good event
     (paper_main_head_compact_clipped_operator_measurable and
     paper_main_head_compact_clipped_operator_eq).
   The entry measurability of the clipped features is proved first
   (paper_main_head_clipped_feature_entry_measurable). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  GaussianProbabilityDefinitions GaussianProbabilityProductDefinitions
  Gaussian.Law.ProductBasics PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadFrobenius Geometry.HeadFeature
  Geometry.HeadWidth Gordon.ProcessCovariance Gaussian.Sample.Deletion Head.Law
  Data.SampleTail Measurability.Coordinates Gaussian.Lipschitz.Clip
  Data.FeatureMoments Data.Clipped Gaussian.Sample.ResidualJoint
  Head.SelectionLaw Head.SectionMeasurable Head.SectionMinimax
  Head.SectionApprox Head.CompactEvent Head.CompactEventOperator.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* Entry measurability of the clipped features. *)

Lemma paper_main_head_clip_measurable {dX : measure_display} {X : measurableType dX}
    (U : R) (f : X -> T) :
  measurable_fun [set: X] f ->
  measurable_fun [set: X] (fun x => (paper_main_gaussian_clip U (f x) : T)).
Proof.
move=> Hf.
have -> : (fun x => paper_main_gaussian_clip U (f x)) =
    (fun x => Num.max (-U)%R (Num.min U (f x))).
  by apply/funext => x; rewrite /paper_main_gaussian_clip RmaxE RminE.
apply: measurable_maxr; first exact: measurable_cst.
apply: measurable_minr; first exact: measurable_cst.
exact: Hf.
Qed.

Lemma paper_main_head_clipped_feature_entry_measurable (U : R) n N i (a b : 'I_(S n)) :
  measurable_fun [set: paper_main_sample N (S n)]
    (fun x => (paper_main_data_clipped_feature U n i (tval x) a b : T)).
Proof.
have -> : (fun x : paper_main_sample N (S n) =>
    paper_main_data_clipped_feature U n i (tval x) a b) =
  (fun x => ((Num.sqrt (S n)%:R)^-1 *
    (paper_main_gaussian_clip U (List.nth (i * S n + a)%N (tval x) 0) *
     paper_main_gaussian_clip U (List.nth (i * S n + b)%N (tval x) 0) - (a == b)%:R))%R).
  by apply/funext => x; rewrite /paper_main_data_clipped_feature paper_main_data_feature_entry.
apply: measurable_funM; first exact: measurable_cst.
apply: measurable_funB; last exact: measurable_cst.
by apply: measurable_funM; apply: paper_main_head_clip_measurable; exact: pm_coord_measurable.
Qed.

Local Open Scope ring_scope.

(* The minimax only sees the tail features of index below q. *)

Lemma paper_main_head_compact_minimax_ext {d m : nat} (kappa : R) q
    (Y : (nat -> R) -> Prop) (W : 'I_m -> 'M[R]_d) (V1 V2 : nat -> 'M[R]_d) :
  (forall i, (i < q)%N -> V1 i = V2 i) ->
  paper_main_head_section_minimax kappa q Y W V1 =
  paper_main_head_section_minimax kappa q Y W V2.
Proof.
move=> HV.
have Hc : forall y, paper_main_head_section_combination q y V1 =
    paper_main_head_section_combination q y V2.
  by move=> y; apply: eq_bigr => i _; rewrite HV.
rewrite /paper_main_head_section_minimax; congr inf.
apply/seteqP; split => _ [y Hy <-]; exists y => //; by rewrite Hc.
Qed.

(* The clipped compact value. *)

Definition paper_main_head_compact_clipped_value n k q (kappa theta U : R)
    (h : paper_main_sample k (S n)) (x : paper_main_sample q (S n)) : R :=
  paper_main_head_section_minimax kappa q (paper_main_head_capped_dual q (S n) theta)
    (fun i : 'I_k => paper_main_head_feature h i)
    (fun i => paper_main_data_clipped_feature U n i (tval x)).

(* Agreement outside the coordinate event. *)

Lemma paper_main_head_compact_clipped_features n q (U : R) (x : paper_main_sample q (S n)) :
  ~ paper_main_data_coordinate_event q (S n) U x ->
  forall i, (i < q)%N ->
    paper_main_data_clipped_feature U n i (tval x) = paper_main_head_feature x i.
Proof.
move=> Hx i Hi.
apply: paper_main_data_clipped_feature_head => // l Hl.
have Hq : (l %/ S n < q)%N by rewrite ltn_divLR.
have Ha : (l %% S n < S n)%N by rewrite ltn_mod.
case: (Rle_lt_dec U (Rabs (List.nth l (tval x) 0))) => [HU|HU]; last exact: Rlt_le.
exfalso; apply: Hx; exists (Ordinal Hq), (Ordinal Ha).
by rewrite pmds_point_entry /= -divn_eq.
Qed.

Theorem paper_main_head_compact_clipped_eq n k q (kappa theta U : R)
    (h : paper_main_sample k (S n)) (x : paper_main_sample q (S n)) :
  ~ paper_main_data_coordinate_event q (S n) U x ->
  paper_main_head_compact_clipped_value n k q kappa theta U h x =
  paper_main_head_compact_value n k q kappa theta h x.
Proof.
move=> Hx; apply: paper_main_head_compact_minimax_ext => i Hi.
exact: paper_main_head_compact_clipped_features.
Qed.

Lemma paper_main_head_compact_coordinate_tail n k q (U : R) (pi : 'S_(k + q))
    (x : paper_main_sample (k + q) (S n)) :
  ~ paper_main_data_coordinate_event (k + q) (S n) U x ->
  ~ paper_main_data_coordinate_event q (S n) U (paper_main_head_selection k q (S n) pi x).2.
Proof.
move=> Hx [u [a H]]; apply: Hx; exists (pi (rshift k u)), a.
by rewrite -(paper_main_head_selection_tail_point k q (S n) pi x u).
Qed.

(* Measurability of the clipped compact value. *)

Lemma paper_main_head_compact_clipped_feature_snd n k q (U : R) (i : nat) (a b : 'I_(S n)) :
  measurable_fun [set: paper_main_sample k (S n) * paper_main_sample q (S n)]
    ((fun hx => paper_main_data_clipped_feature U n i (tval hx.2) a b) : _ -> T).
Proof.
exact: (measurableT_comp (paper_main_head_clipped_feature_entry_measurable U n q i a b)
  measurable_snd).
Qed.

Theorem paper_main_head_compact_clipped_measurable n k q (kappa theta U : R) :
  1 <= kappa ->
  measurable_fun [set: paper_main_sample k (S n) * paper_main_sample q (S n)]
    ((fun hx => paper_main_head_compact_clipped_value n k q kappa theta U hx.1 hx.2) : _ -> T).
Proof.
move=> Hk.
have [HY|HY] := pselect (exists y, paper_main_head_capped_dual q (S n) theta y).
  have H := (paper_main_head_section_minimax_measurable n k kappa q _
    (fun i hx => paper_main_head_feature hx.1 i)
    (fun i (hx : paper_main_sample k (S n) * paper_main_sample q (S n)) =>
      paper_main_data_clipped_feature U n i (tval hx.2))
    Hk HY (@paper_main_head_capped_dual_unit q (S n) theta)
    (fun i a b => paper_main_head_compact_feature_fst n k q i a b)
    (fun i a b => paper_main_head_compact_clipped_feature_snd n k q U i a b)).
  exact: H.
have -> : (fun hx : paper_main_sample k (S n) * paper_main_sample q (S n) =>
    paper_main_head_compact_clipped_value n k q kappa theta U hx.1 hx.2) = (fun _ => 0).
  apply: funext => hx.
  by rewrite /paper_main_head_compact_clipped_value paper_main_head_section_minimax_empty_dual.
exact: measurable_cst.
Qed.

(* The clipped operator-good event. *)

Lemma paper_main_head_operator_ext {d : nat} q (V1 V2 : nat -> 'M[R]_d) (L : R) :
  (forall i, (i < q)%N -> V1 i = V2 i) ->
  paper_main_head_section_operator_bound q V1 L <-> paper_main_head_section_operator_bound q V2 L.
Proof.
move=> HV.
have Hc : forall y, paper_main_head_section_combination q y V1 =
    paper_main_head_section_combination q y V2.
  by move=> y; apply: eq_bigr => i _; rewrite HV.
by split => [[HL H]|[HL H]]; split => // y; [rewrite -Hc | rewrite Hc].
Qed.

Corollary paper_main_head_compact_clipped_operator_measurable n k q (U L : R) :
  measurable [set hx : paper_main_sample k (S n) * paper_main_sample q (S n) |
    paper_main_head_section_operator_bound q
      (fun i => paper_main_data_clipped_feature U n i (tval hx.2)) L].
Proof.
have H := (paper_main_head_operator_event_measurable q
  (fun i (hx : paper_main_sample k (S n) * paper_main_sample q (S n)) =>
    paper_main_data_clipped_feature U n i (tval hx.2)) L
  (fun i a b => paper_main_head_compact_clipped_feature_snd n k q U i a b)).
exact: H.
Qed.

Corollary paper_main_head_compact_clipped_operator_eq n q (U L : R)
    (x : paper_main_sample q (S n)) :
  ~ paper_main_data_coordinate_event q (S n) U x ->
  paper_main_head_section_operator_bound q
    (fun i => paper_main_data_clipped_feature U n i (tval x)) L <->
  paper_main_head_section_operator_bound q (fun i => paper_main_head_feature x i) L.
Proof.
move=> Hx; apply: paper_main_head_operator_ext => i Hi.
exact: paper_main_head_compact_clipped_features.
Qed.
