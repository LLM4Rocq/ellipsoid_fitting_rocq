(* Pieces of the lower spectral bound of the raw features.
   1. Row event (paper_main_squarefree_row_event). The frame event of
      paper_main_column_frame (PaperMainColumnConcentrationFrame) at
      tolerance 1/64 is measurable and its probability tends to 0 under
      eventual density >= c > 0 and eventually 0 < N(d) <= d^2. For all
      large d, outside it, every row sum of squares
      D_i = sum_q pmnb_X d (tval x) i q ^ 2 satisfies
      |D_i / 'C(d, 2) - 1| <= 1/64, the last condition of
      paper_main_column_frame_good.
   2. Deterministic step (paper_main_squarefree_coercivity_from_box). For
      0 < N, d >= 9 and 4 N <= d^2, the row bound and the non-backtracking
      box -(49/24) I <= pmlo_T 1 - s I, with kap = (sqrt (N 'C(d, 2)))^-1
      and s = kap N, give raw-feature coercivity with constant d^2 / 128
      (paper_main_squarefree_coercivity of PaperMainSquarefreeCoercivity).
   3. Unions (paper_main_event_union3). Three measurable families of
      events whose probabilities tend to 0 have a measurable union whose
      probability tends to 0. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainAsymptotics PaperMainFixedDensity PaperMainSquarefreeEdgeUpperLimit
  PaperMainGeometryHeadCoefficients PaperMainFeatureGramBlocks PaperMainSquarefreeEdgeLower
  PaperMainSquarefreeWalkNB PaperMainColumnRemainder PaperMainColumnConcentrationFrameEvents
  PaperMainColumnConcentrationFrame PaperMainSquarefreeCoercivity.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. The row event. *)
Theorem paper_main_squarefree_row_event (N : nat -> nat) (c : R) :
  0 < c -> paper_main_eventually_ge (paper_main_density N) c ->
  (exists D, forall d, (D <= d)%N -> (0 < N d)%N /\ (N d <= d ^ 2)%N) ->
  exists E : forall d, set (paper_main_sample (N d) d),
    (forall d, measurable (E d)) /\
    paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 /\
    exists D : nat, forall d, (D <= d)%N -> forall x : paper_main_sample (N d) d, ~ E d x ->
      forall i : 'I_(N d),
        `|(\sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) (N d) i q) ^+ 2) / ('C(d, 2))%:R - 1| <=
        1 / 64.
Proof.
move=> Hc Hlow Hup.
have [_ Hframe] := paper_main_column_frame N c Hc Hlow Hup.
have H164 : (0 : R) < 1 / 64 by rewrite divr_gt0 // ltr0n.
have [E [mE [limE [D HD]]]] := Hframe (1 / 64) H164.
exists E; split => //; split => //.
exists D => d Hd x Hx i.
by have [_ _ _ _ Hrow] := HD d Hd x Hx; exact: Hrow.
Qed.

(* 2. The deterministic step from the non-backtracking box to coercivity. *)
Theorem paper_main_squarefree_coercivity_from_box N d (x : paper_main_sample N d) :
  (0 < N)%N -> (9 <= d)%N -> (4 * N <= d ^ 2)%N ->
  (forall i : 'I_N,
     `|(\sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) N i q) ^+ 2) / ('C(d, 2))%:R - 1| <= 1 / 64) ->
  paper_main_loewner_le ((- (49 / 24)) *: 1%:M)
    (pmlo_T N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1) 1 -
     ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1 * N%:R) *: 1%:M) ->
  paper_main_head_coercive (paper_main_feature_gram N d x) ((1 / 128) * d%:R ^+ 2)%R.
Proof.
move=> HN Hd9 HN4 Hrow Hbox.
have Hd2 : (2 <= d)%N by apply: leq_trans Hd9.
have [Hs0 Hs1] := paper_main_squarefree_coercivity_scale N d HN Hd9 HN4.
exact (paper_main_squarefree_coercivity N d x HN Hd2 Hs0 Hs1 Hrow Hbox).
Qed.

(* 3. Finite unions of vanishing events. *)
Lemma paper_main_event_union3 (N : nat -> nat) (E1 E2 E3 : forall d, set (paper_main_sample (N d) d)) :
  (forall d, measurable (E1 d)) -> (forall d, measurable (E2 d)) -> (forall d, measurable (E3 d)) ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d (E1 d)) 0 ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d (E2 d)) 0 ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d (E3 d)) 0 ->
  (forall d, measurable (E1 d `|` E2 d `|` E3 d)) /\
  paper_main_tends_to (fun d => paper_main_probability (N d) d (E1 d `|` E2 d `|` E3 d)) 0.
Proof.
move=> m1 m2 m3 l1 l2 l3.
have mU : forall d, measurable (E1 d `|` E2 d `|` E3 d).
  by move=> d; exact: (measurableU _ _ (measurableU _ _ (m1 d) (m2 d)) (m3 d)).
split => //.
apply: (paper_main_tends_to_zero_squeeze_eventually _ (fun d =>
  (paper_main_probability (N d) d (E1 d) + paper_main_probability (N d) d (E2 d) +
   paper_main_probability (N d) d (E3 d))%E) 0).
- by move=> d; exact: measure_ge0.
- move=> d _; rewrite /paper_main_probability.
  apply: le_trans (measureU2 _ (measurableU _ _ (m1 d) (m2 d)) (m3 d)) _.
  by apply: leeD => //; exact: (measureU2 _ (m1 d) (m2 d)).
- apply: pmel_tends_to_add => //.
    by move=> d; apply: adde_ge0; exact: measure_ge0.
  by apply: pmel_tends_to_add.
Qed.
