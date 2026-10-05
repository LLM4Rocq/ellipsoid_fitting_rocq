(* The lower spectral law at fixed scalar parameters
   (paper_main_squarefree_lower_probability_at).

   Let N : nat -> nat, c > 0 and c1 with eventual density >= c and,
   eventually, 0 < N(d), 4 N(d) <= d^2 and d^2 <= c1 N(d). Fix k and
   eta > 0 with K = 2^(k+1), t = pmnbr_t k = 12 (K + 1) and the scalar gap
     2^K t + pmlo_rho (t + 1) (3 K eta t) K <= (49/24)^K.
   The union of three measurable events,
   - the remainder event of paper_main_column_remainder_probability at K
     and eta (all E_m, m < K, have operator bound eta outside it),
   - the row event of paper_main_squarefree_row_event, outside which every
     row i of X = pmnb_X d (tval x) has |sum_q X_iq^2 / C(d, 2) - 1| <= 1/64,
   - the non-backtracking trace event paper_main_squarefree_trace_event at
     the exact normalization,
   has probability tending to 0, and for all large d every sample outside
   it has raw-feature coercivity with constant d^2 / 128
   (paper_main_squarefree_coercivity_outside_trace). The scalar gap is the
   only hypothesis on (k, eta); it is deterministic. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainDefinitions
  PaperMainGeometryHeadCoefficients PaperMainFeatureGramBlocks PaperMainSquarefreeEdgeLower
  PaperMainSquarefreeWalkNB PaperMainSquarefreeWalkNBEvent PaperMainSquarefreeWalkNBRate
  PaperMainColumnRemainderProbability PaperMainSquarefreeLowerProbabilityBase
  PaperMainSquarefreeLowerProbabilityTrace.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Theorem paper_main_squarefree_lower_probability_at (N : nat -> nat) (c : R) (c1 k : nat) (eta : R) :
  0 < c -> paper_main_eventually_ge (paper_main_density N) c ->
  (exists D, forall d, (D <= d)%N ->
     (0 < N d)%N /\ (4 * N d <= d ^ 2)%N /\ (d ^ 2 <= c1 * N d)%N) ->
  0 < eta ->
  2 ^+ (2 ^ k.+1) * pmnbr_t k + pmlo_rho (pmnbr_t k + 1) (3 * (2 ^ k.+1)%:R * eta * pmnbr_t k) (2 ^ k.+1) <=
    (49 / 24) ^+ (2 ^ k.+1) ->
  exists E : forall d, set (paper_main_sample (N d) d),
    (forall d, measurable (E d)) /\
    paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 /\
    exists D : nat, forall d, (D <= d)%N -> forall x : paper_main_sample (N d) d, ~ E d x ->
      paper_main_head_coercive (paper_main_feature_gram (N d) d x) ((1 / 128) * d%:R ^+ 2)%R.
Proof.
move=> Hc Hlow Hcount Heta Hgap.
have [D0 HD0] := Hcount.
have Hup : exists D, forall d, (D <= d)%N -> (0 < N d)%N /\ (N d <= d ^ 2)%N.
  exists D0 => d Hd; have [HN [H4N _]] := HD0 d Hd; split => //.
  by apply: leq_trans H4N; exact: leq_pmull.
have [E1 [mE1 [lE1 [D1 HD1]]]] :=
  paper_main_column_remainder_probability N c Hc Hlow Hup (2 ^ k.+1) eta Heta.
have [E2 [mE2 [lE2 [D2 HD2]]]] := paper_main_squarefree_row_event N c Hc Hlow Hup.
have lE3 := paper_main_squarefree_trace_tends_to_zero N c1 k Hcount.
have [mU lU] := paper_main_event_union3 N E1 E2
  (fun d => paper_main_squarefree_trace_event (N d) d k) mE1 mE2
  (fun d => paper_main_squarefree_trace_event_measurable (N d) d k) lE1 lE2 lE3.
exists (fun d => E1 d `|` E2 d `|` paper_main_squarefree_trace_event (N d) d k).
split => //; split => //.
exists (maxn (maxn D0 9) (maxn D1 D2)) => d Hd x Hx.
have Hd0 : (maxn D0 9 <= d)%N by exact: leq_trans (leq_maxl _ _) Hd.
have Hd12 : (maxn D1 D2 <= d)%N by exact: leq_trans (leq_maxr _ _) Hd.
have HdD0 : (D0 <= d)%N by exact: leq_trans (leq_maxl _ _) Hd0.
have Hd9 : (9 <= d)%N by exact: leq_trans (leq_maxr _ _) Hd0.
have HdD1 : (D1 <= d)%N by exact: leq_trans (leq_maxl _ _) Hd12.
have HdD2 : (D2 <= d)%N by exact: leq_trans (leq_maxr _ _) Hd12.
have [HN [H4N _]] := HD0 d HdD0.
have HE := HD1 d HdD1 x (fun h => Hx (or_introl (or_introl h))).
have Hrow := HD2 d HdD2 x (fun h => Hx (or_introl (or_intror h))).
have Htr : ~ paper_main_squarefree_trace_event (N d) d k x := fun h => Hx (or_intror h).
exact (paper_main_squarefree_coercivity_outside_trace (N d) d x k eta HN Hd9 H4N (ltW Heta) Htr HE Hgap Hrow).
Qed.
