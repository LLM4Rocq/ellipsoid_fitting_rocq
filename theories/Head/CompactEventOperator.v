(* Measurability of the operator-norm event of the tail-feature map. Let
   V i (i < q) be matrices depending entrywise measurably on a point x of a
   measurable space. The event
     {x | paper_main_head_section_operator_bound q (V x) L}
       = {x | 0 <= L /\ forall y, |sum_(i<q) y_i V_i(x)|_F <= L |y|_2}
   is measurable (paper_main_head_operator_event_measurable).
   - For q = 0 the combination is 0 and the event is {0 <= L}.
   - For q > 0 fix finite 1/(j+1)-nets of the unit sphere of
     paper_main_gordon_dot q contained in it
     (paper_main_gordon_finite_net_exists).
     A unit y is within 1/(j+1) of a net point v, so
       |sum_i y_i V_i|_F <= |sum_i v_i V_i|_F + (j+1)^-1 sum_i |V_i|_F
     for every j, and the bound for every y follows by homogeneity
     (paper_main_head_operator_from_unit). So the event is {0 <= L}
     intersected with the countably many events
     <sum_i v_i V_i, sum_i v_i V_i> <= L^2 at the net points.
   The nets are fixed once and for all and do not depend on x. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  GaussianProbabilityDefinitions GaussianProbabilityProductDefinitions
  Gaussian.ProductLawBasics PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadFrobenius Geometry.HeadFeature
  Geometry.HeadWidth Gordon.ProcessCovariance Gordon.Bilinear Gordon.Nets
  Gordon.NetExistence Sampling Head.Law Data.SampleTail Gaussian.ResidualJoint
  Head.SelectionLaw Head.FiniteSupportSelector Head.SectionMeasurable
  Head.SectionMinimax Head.SectionApprox Head.CompactEvent.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* Normalization of a nonzero dual vector. *)

Lemma paper_main_head_operator_normalize q (y : nat -> R) (r : R) :
  0 < r -> r ^ 2 = paper_main_gordon_dot q y y ->
  paper_main_gordon_dot q (fun i => Rdiv (y i) r) (fun i => Rdiv (y i) r) = 1.
Proof.
move=> Hr H2.
have HE : paper_main_gordon_dot q (fun i => Rdiv (y i) r) (fun i => Rdiv (y i) r) =
    / r ^ 2 * paper_main_gordon_dot q y y.
  rewrite /paper_main_gordon_dot -finite_sum_scale; apply: finite_sum_ext => i _.
  by rewrite /Rdiv; field; apply: Rgt_not_eq.
by rewrite HE -H2; field; apply: Rgt_not_eq.
Qed.

Local Open Scope ring_scope.

(* Homogeneity and the zero vector. *)

Lemma paper_main_head_operator_combinationZ {d : nat} q (r : R) (u : nat -> R)
    (V : nat -> 'M[R]_d) :
  paper_main_head_section_combination q (fun i => r * u i) V =
  r *: paper_main_head_section_combination q u V.
Proof.
rewrite /paper_main_head_section_combination scaler_sumr.
by apply: eq_bigr => i _; rewrite scalerA.
Qed.

Lemma paper_main_head_operator_combination0 {d : nat} q (y : nat -> R) (V : nat -> 'M[R]_d) :
  paper_main_gordon_dot q y y = 0 -> paper_main_head_section_combination q y V = 0.
Proof.
move=> H0; rewrite /paper_main_head_section_combination big1 // => i _.
have Hi : `|y i| <= 0.
  apply: (paper_main_head_section_coord_le q y 0 i (ltn_ord i) (lexx 0)).
  by rewrite H0 expr0n.
by move: Hi; rewrite normr_le0 => /eqP ->; rewrite scale0r.
Qed.

Lemma paper_main_head_operator_frobenius_le {d : nat} (M : 'M[R]_d) (L : R) :
  0 <= L -> paper_main_frobenius M <= L <-> paper_main_pairing M M <= L ^+ 2.
Proof.
move=> HL; split => H.
  rewrite -pmh_frobenius_sqr !expr2.
  exact: (ler_pM (pmh_frobenius_ge0 _ _) (pmh_frobenius_ge0 _ _) H H).
rewrite /paper_main_frobenius -(ger0_norm HL) -sqrtr_sqr.
exact: ler_wsqrtr.
Qed.

(* The bound on unit vectors gives the operator bound. *)

Lemma paper_main_head_operator_from_unit {d : nat} q (V : nat -> 'M[R]_d) (L : R) :
  0 <= L ->
  (forall u, paper_main_gordon_dot q u u = 1 ->
    paper_main_frobenius (paper_main_head_section_combination q u V) <= L) ->
  paper_main_head_section_operator_bound q V L.
Proof.
move=> HL Hunit; split => // y.
have H2 := paper_main_gordon_euclidean_squared q y.
have Hr0 : 0 <= euclidean_norm y (List.seq 0 q) by apply/RleP; exact: sqrt_pos.
have [Hr|Hr] := eqVneq (euclidean_norm y (List.seq 0 q)) 0.
  have Hy0 : paper_main_gordon_dot q y y = 0 by rewrite -H2 Hr RpowE expr0n.
  rewrite (paper_main_head_operator_combination0 q y V Hy0) pmh_frobenius0 Hr mulr0.
  exact: lexx.
have Hrp : Rlt 0 (euclidean_norm y (List.seq 0 q)) by apply/RltP; rewrite lt_def Hr Hr0.
have Hu := paper_main_head_operator_normalize q y _ Hrp H2.
have -> : paper_main_head_section_combination q y V =
    paper_main_head_section_combination q
      (fun i => euclidean_norm y (List.seq 0 q) * Rdiv (y i) (euclidean_norm y (List.seq 0 q))) V.
  apply: eq_bigr => i _; congr (_ *: _).
  by rewrite RdivE mulrC divfK.
rewrite paper_main_head_operator_combinationZ pmh_frobeniusZ (ger0_norm Hr0) mulrC.
apply: ler_wpM2r; first exact: Hr0.
exact: Hunit.
Qed.

(* The event is measurable. *)

Theorem paper_main_head_operator_event_measurable {dX : measure_display}
    {X : measurableType dX} {d : nat} q (V : nat -> X -> 'M[R]_d) (L : R) :
  (forall i a b, measurable_fun [set: X] ((fun x => V i x a b) : X -> T)) ->
  measurable [set x | paper_main_head_section_operator_bound q (fun i => V i x) L].
Proof.
move=> mV.
have [HL|HL] := pselect (0 <= L); last first.
  have -> : [set x | paper_main_head_section_operator_bound q (fun i => V i x) L] = set0.
    by apply/seteqP; split => x // [H _]; apply: HL.
  exact: measurable0.
have [Hq|Hq] := eqVneq q 0%N.
  have -> : [set x | paper_main_head_section_operator_bound q (fun i => V i x) L] = setT.
    apply/seteqP; split => x // _; split => // y.
    rewrite /paper_main_head_section_combination Hq big_ord0 pmh_frobenius0.
    by apply: mulr_ge0 => //; apply/RleP; exact: sqrt_pos.
  exact: measurableT.
have Hq0 : (0 < q)%N by rewrite lt0n.
pose U := fun y : nat -> R => paper_main_gordon_dot q y y = 1.
have HU : exists y, U y by exists (fun _ => / sqrt (INR q)); exact: paper_main_head_constant_unit.
have Hnets : forall j : nat, exists sv : nat * (nat -> nat -> R),
    paper_main_gordon_finite_net q U sv.2 (List.seq 0 sv.1) (j.+1%:R^-1).
  move=> j.
  have He : Rlt 0 (j.+1%:R^-1) by apply/RltP; rewrite invr_gt0 ltr0n.
  have [s [v [_ Hnet]]] := paper_main_gordon_finite_net_exists q U _ He HU (fun y Hy => Hy).
  by exists (s, v).
have [sv Hsv] := choice Hnets.
pose s := fun j => (sv j).1.
pose v := fun j => (sv j).2.
have HvU : forall j t, (t < s j)%N -> U (v j t).
  move=> j t Ht; apply: (proj1 (Hsv j)).
  exact/(paper_main_head_section_seq_lt t (s j)).
have Hchar : forall x, paper_main_head_section_operator_bound q (fun i => V i x) L <->
    (forall j t, (t < s j)%N ->
      paper_main_frobenius (paper_main_head_section_combination q (v j t) (fun i => V i x)) <= L).
  move=> x; split.
    move=> [_ HB] j t Ht.
    apply: le_trans (HB (v j t)) _.
    by rewrite (paper_main_head_section_euclidean_unit q _ (HvU j t Ht)) mulr1.
  move=> H; apply: paper_main_head_operator_from_unit => // y Hy.
  set B := paper_main_head_section_tail_norm q (fun i => V i x).
  have HB0 : 0 <= B by exact: paper_main_head_section_tail_norm_ge0.
  apply: (paper_main_head_section_eps_le _ _ B HB0) => j.
  have [t [Ht Hdist]] := (proj2 (Hsv j)) y Hy.
  have Ht' : (t < s j)%N by exact/(paper_main_head_section_seq_lt t (s j)).
  have Hj0 : 0 <= j.+1%:R^-1 :> R by rewrite invr_ge0 ler0n.
  have Hcoord : forall i, (i < q)%N -> `|y i - v j t i| <= j.+1%:R^-1.
    move=> i Hi.
    apply: (paper_main_head_section_coord_le q (fun i => y i - v j t i) _ i Hi Hj0).
    by apply/RleP; rewrite -RpowE.
  have Hdiff := paper_main_head_section_combination_diff q y (v j t) (fun i => V i x).
  have Hsum : \sum_(i < q) `|y i - v j t i| * paper_main_frobenius (V i x) <=
      j.+1%:R^-1 * B.
    rewrite /B /paper_main_head_section_tail_norm mulr_sumr; apply: ler_sum => i _.
    apply: ler_wpM2r; first exact: pmh_frobenius_ge0.
    exact: Hcoord i (ltn_ord i).
  have Htri := pmh_frobenius_triangle _
    (paper_main_head_section_combination q (v j t) (fun i => V i x))
    (paper_main_head_section_combination q y (fun i => V i x) -
      paper_main_head_section_combination q (v j t) (fun i => V i x)).
  rewrite addrC subrK in Htri.
  have Hv := H j t Ht'.
  rewrite lerBlDr; apply: le_trans Htri _.
  apply: lerD; first exact: Hv.
  exact: le_trans Hdiff Hsum.
have -> : [set x | paper_main_head_section_operator_bound q (fun i => V i x) L] =
    \bigcap_(j : nat) \bigcap_(t : nat) [set x | (t < s j)%N ->
      paper_main_pairing (paper_main_head_section_combination q (v j t) (fun i => V i x))
        (paper_main_head_section_combination q (v j t) (fun i => V i x)) <= L ^+ 2].
  apply/seteqP; split=> x Hx.
    move=> j _ t _ Ht; apply/(paper_main_head_operator_frobenius_le _ _ HL).
    exact: ((Hchar x).1 Hx j t Ht).
  apply/(Hchar x) => j t Ht; apply/(paper_main_head_operator_frobenius_le _ _ HL).
  exact: (Hx j I t I Ht).
apply: bigcapT_measurable => j; apply: bigcapT_measurable => t.
apply: paper_main_head_section_imp_guard.
apply: paper_main_head_section_le_measurable; last exact: measurable_cst.
by apply: paper_main_finite_pairing_measurable;
  exact: (paper_main_head_section_combination_measurable q (v j t) V mV).
Qed.
