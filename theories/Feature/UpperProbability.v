(* Actual full raw-feature upper control from the diagonal and square-free blocks. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainDefinitions Asymptotics Geometry.Psd Geometry.HeadCorrection
  Feature.GramBlocks Feature.DiagonalLimit SquareFree.EdgeUpperLimit.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition paper_main_feature_upper_event N d : set (paper_main_sample N d) :=
  paper_main_diag_trace_event N d `|` paper_main_squarefree_upper_event N d.

Lemma paper_main_feature_upper_event_measurable N d : measurable (paper_main_feature_upper_event N d).
Proof.
apply: measurableU; [exact: paper_main_diag_trace_event_measurable|exact: paper_main_squarefree_upper_event_measurable].
Qed.

Theorem paper_main_feature_upper_event_bound N d (x : paper_main_sample N d) :
  (0<d)%N -> ~paper_main_feature_upper_event N d x ->
  paper_main_loewner_le (paper_main_feature_gram N d x)
    ((3*N%:R+106%:R*d%:R^+2) *: 1%:M).
Proof.
move=> Hd Hx.
have Hdiag : ~paper_main_diag_trace_event N d x by move=> H; apply: Hx; left.
have Hsq : ~paper_main_squarefree_upper_event N d x by move=> H; apply: Hx; right.
have [_ HD] := paper_main_diag_trace_event_bound N d x Hdiag.
have HS := paper_main_squarefree_upper_bound N d x Hd Hsq.
rewrite paper_main_feature_gram_blocks scalerDl.
exact: pmh_loewner_add HD HS.
Qed.

Theorem paper_main_feature_upper_event_limit (N : nat -> nat) c :
  0<c -> paper_main_eventually_ge (paper_main_density N) c ->
  (exists D, forall d, (D<=d)%N -> (0<N d)%N /\ (N d<=d^2)%N) ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d (paper_main_feature_upper_event (N d) d)) 0.
Proof.
move=> Hc Hlow Hup.
have HD := paper_main_diag_block_tends_to_zero N c Hc Hlow.
have HS := paper_main_squarefree_upper_event_tends_to_zero N Hup.
apply: (paper_main_tends_to_zero_squeeze _ (fun d =>
  (paper_main_probability (N d) d (paper_main_diag_trace_event (N d) d)+
   paper_main_probability (N d) d (paper_main_squarefree_upper_event (N d) d))%E)).
- by move=> d; exact: measure_ge0.
- move=> d; rewrite /paper_main_probability /paper_main_feature_upper_event.
  apply: measureU2; [exact: paper_main_diag_trace_event_measurable|exact: paper_main_squarefree_upper_event_measurable].
- by apply: pmel_tends_to_add => // d; exact: measure_ge0.
Qed.

Corollary paper_main_feature_upper_edge (N : nat -> nat) c :
  0<c -> paper_main_eventually_ge (paper_main_density N) c ->
  (exists D, forall d, (D<=d)%N -> (0<N d)%N /\ (N d<=d^2)%N) ->
  exists E : forall d, set (paper_main_sample (N d) d),
    (forall d, measurable (E d)) /\
    paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 /\
    forall d (x : paper_main_sample (N d) d), (0<d)%N -> (N d<=d^2)%N -> ~E d x ->
      paper_main_loewner_le (paper_main_feature_gram (N d) d x) ((109%:R*d%:R^+2) *: 1%:M).
Proof.
move=> Hc Hlow Hup.
exists (fun d => paper_main_feature_upper_event (N d) d); split.
- by move=> d; exact: paper_main_feature_upper_event_measurable.
- split; first exact: (paper_main_feature_upper_event_limit N c Hc Hlow Hup).
  move=> d x Hd HN Hx.
  apply: pmh_loewner_trans (paper_main_feature_upper_event_bound (N d) d x Hd Hx) _.
  apply: pmh_loewner_scalar.
  have HNR : (N d)%:R<=d%:R^+2 :> R by rewrite -natrX ler_nat.
  nra.
Qed.
