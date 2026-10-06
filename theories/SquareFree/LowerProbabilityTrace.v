(* The NB trace event of the actual lower spectral law at the exact
   normalization.

   With kap = (sqrt (N 'C(d, 2)))^-1, K = 2^(k+1), p = pmnbr_p d =
   2^(pmel_k d + 4) and t = pmnbr_t k = 12 (K + 1):
   1. Normalization: lam^-2 = kap for lam = pmnbr_lam N d, 0 < N, d >= 2.
   2. The trace event pmnbv_union N d kap K p t is measurable.
   3. Rate: under the premises of pmnbr_rate its probability is at most 1/d.
   4. Limit: for fixed c1 and k, if eventually 0 < N(d), 4 N(d) <= d^2 and
      d^2 <= c1 N(d), its probability tends to 0; the growth premise of
      pmnbr_rate holds eventually by pmlg_eventual.
   5. Outside it, with all remainders E_m (m < K) at operator bound eta,
      the scalar gap at t and theta = 49/24, and the row bound 1/64, the raw
      feature Gram is coercive with constant d^2 / 128 (j = pmel_k d + 2,
      so 2^(j+2) = p). *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainDefinitions DiagonalBlock.Limit Geometry.HeadCoefficients
  Feature.GramBlocks SquareFree.EdgeUpperLimit SquareFree.EdgeLower
  SquareFree.WalkNB SquareFree.WalkNBEvent SquareFree.WalkNBRate
  SquareFree.LogarithmicGrowth SquareFree.LowerProbabilityBox.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. Normalization. *)
Lemma paper_main_squarefree_trace_kap N d : (0 < N)%N -> (2 <= d)%N ->
  ((pmnbr_lam N d)^-1 ^+ 2)%R = (Num.sqrt (N%:R * ('C(d, 2))%:R))^-1.
Proof.
move=> HN Hd.
have [_ _ H2] := pmnbr_lam_facts N d HN Hd.
by rewrite exprVn H2 natrM.
Qed.

(* 2. The trace event at the exact normalization. *)
Definition paper_main_squarefree_trace_event (N d k : nat) : set (paper_main_sample N d) :=
  pmnbv_union N d ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1) (2 ^ k.+1) (pmnbr_p d) (pmnbr_t k).

Theorem paper_main_squarefree_trace_event_measurable N d k :
  measurable (paper_main_squarefree_trace_event N d k).
Proof.
exact: pmnbv_union_measurable.
Qed.

(* 3. The rate. *)
Theorem paper_main_squarefree_trace_rate (N d c1 k : nat) : (0 < N)%N -> (4 * N <= d ^ 2)%N ->
  (d ^ 2 <= c1 * N)%N -> (2 ^ (48 * 200) <= d)%N -> (pmnbr_A c1 k * pmel_L d ^ 1178 <= d)%N ->
  (paper_main_probability N d (paper_main_squarefree_trace_event N d k) <= (1 / d%:R)%:E)%E.
Proof.
move=> HN H4N Hc1 Hd HA.
have Hd2 : (2 <= d)%N by apply: leq_trans Hd; exact: (@leq_pexp2l 2 1 (48 * 200)).
rewrite /paper_main_squarefree_trace_event -(paper_main_squarefree_trace_kap N d HN Hd2).
exact (pmnbr_rate N d c1 k HN H4N Hc1 Hd HA).
Qed.

(* 4. The limit. *)
Theorem paper_main_squarefree_trace_tends_to_zero (N : nat -> nat) (c1 k : nat) :
  (exists D, forall d, (D <= d)%N ->
     (0 < N d)%N /\ (4 * N d <= d ^ 2)%N /\ (d ^ 2 <= c1 * N d)%N) ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d
    (paper_main_squarefree_trace_event (N d) d k)) 0.
Proof.
move=> [D HD].
have [DA HDA] := pmlg_eventual (pmnbr_A c1 k) 1178.
apply: (pmdbl_inv_rate _ 1) => //.
exists (maxn D (maxn DA (2 ^ (48 * 200)))) => d Hd.
have HdD : (D <= d)%N by exact: leq_trans (leq_maxl _ _) Hd.
have Hd' : (maxn DA (2 ^ (48 * 200)) <= d)%N by exact: leq_trans (leq_maxr _ _) Hd.
have HdA : (DA <= d)%N by exact: leq_trans (leq_maxl _ _) Hd'.
have Hd96 : (2 ^ (48 * 200) <= d)%N by exact: leq_trans (leq_maxr _ _) Hd'.
have [HN [H4N Hc1]] := HD d HdD.
exact (paper_main_squarefree_trace_rate (N d) d c1 k HN H4N Hc1 Hd96 (HDA d HdA)).
Qed.

(* 5. Coercivity outside the trace event. *)
Theorem paper_main_squarefree_coercivity_outside_trace N d (x : paper_main_sample N d)
    (k : nat) (eta : R) :
  (0 < N)%N -> (9 <= d)%N -> (4 * N <= d ^ 2)%N -> 0 <= eta ->
  ~ paper_main_squarefree_trace_event N d k x ->
  (forall m, (m < 2 ^ k.+1)%N ->
     pmlo_opb N (pmlo_E N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N)
       ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1) ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1 * N%:R) m) eta) ->
  2 ^+ (2 ^ k.+1) * pmnbr_t k + pmlo_rho (pmnbr_t k + 1) (3 * (2 ^ k.+1)%:R * eta * pmnbr_t k) (2 ^ k.+1) <=
    (49 / 24) ^+ (2 ^ k.+1) ->
  (forall i : 'I_N,
     `|(\sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) N i q) ^+ 2) / ('C(d, 2))%:R - 1| <= 1 / 64) ->
  paper_main_head_coercive (paper_main_feature_gram N d x) ((1 / 128) * d%:R ^+ 2)%R.
Proof.
move=> HN Hd9 HN4 Heta Hx HE Hgap Hrow.
have Ht : 1 <= pmnbr_t k by rewrite /pmnbr_t ler1n muln_gt0.
exact (paper_main_squarefree_coercivity_from_remainders N d x k (pmel_k d).+2 (pmnbr_t k) eta
  HN Hd9 HN4 Ht Heta Hx HE Hgap Hrow).
Qed.
