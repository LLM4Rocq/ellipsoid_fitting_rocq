(* The diagonal block operator bound with probability tending to one
   (lem:diagonal-feature-block of the paper, proved with a fourth trace
   moment instead of the matrix Bernstein inequality).

   For a sample x of N points of R^d, D = paper_main_diag_block N d x has
   the entries x_ia^2 - 1, and Z = D^T D - 2 N I (paper_main_diag_centered).
   - paper_main_diag_trace_event_measurable: the event tr Z^4 > N^4
     (paper_main_diag_trace_event) is measurable.
     paper_main_diag_trace_event_bound: outside it, D^T D <= 3 N I and
     D D^T <= 3 N I (paper_main_diag_block_from_trace).
   - paper_main_diag_trace_event_markov: Markov's inequality (MathComp's
     markov), the law transport pmdf_actual and the moment bound of
     Feature.DiagonalMoment give
       P (tr Z^4 > N^4)
         <= (N (2^21 d^4 + 16 d) + 3 N (N - 1) d (4 d + 52)^2) / N^4.
   - paper_main_diag_block_tends_to_zero: if N(d) / d^2 >= c > 0
     eventually, the bound is at most ((2^21 + 16) / c^3 + 9408 / c^2) / d
     (pmdbl_rate), so the probability tends to 0. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import Gaussian.Iterated.Definitions
  Analysis.CoordinateContinuityDefinitions
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  PaperMainDefinitions Data.FeatureMomentsCoordinates Data.FeatureMoments
  SquareFree.Diagonal Feature.GramBlocks Feature.DiagonalTrace
  Feature.DiagonalMoment.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. The event. *)
Definition paper_main_diag_centered N d (x : paper_main_sample N d) : 'M[R]_d :=
  (paper_main_diag_block N d x)^T *m paper_main_diag_block N d x - (2 * N%:R) *: 1%:M.

Definition paper_main_diag_trace_event N d : set (paper_main_sample N d) :=
  [set x | N%:R ^+ 4 < \tr (paper_main_diag_centered N d x *m paper_main_diag_centered N d x *m
    paper_main_diag_centered N d x *m paper_main_diag_centered N d x)].

Definition pmdbl_F N d (xs : list R) : R :=
  \tr (pmdm_S d N xs *m pmdm_S d N xs *m pmdm_S d N xs *m pmdm_S d N xs).

Lemma pmdbl_event_list N d :
  paper_main_diag_trace_event N d = [set x | Rlt (N%:R ^+ 4) (pmdbl_F N d (tval x))].
Proof.
apply/seteqP; split => x /=;
  rewrite /paper_main_diag_trace_event /paper_main_diag_centered /=
    paper_main_diag_block_centered /pmdbl_F; by move/RltP.
Qed.

Theorem paper_main_diag_trace_event_measurable N d :
  measurable (paper_main_diag_trace_event N d).
Proof.
rewrite pmdbl_event_list.
have [HC _] := paper_main_diag_trace4_regular d N.
exact: (pmsd_gt_measurable (N * d) (pmdbl_F N d) (N%:R ^+ 4) HC).
Qed.

(* Outside the event, the diagonal block is bounded. *)
Theorem paper_main_diag_trace_event_bound N d (x : paper_main_sample N d) :
  ~ paper_main_diag_trace_event N d x ->
  paper_main_loewner_le ((paper_main_diag_block N d x)^T *m paper_main_diag_block N d x)
    ((3 * N%:R) *: 1%:M) /\
  paper_main_loewner_le (paper_main_diag_block N d x *m (paper_main_diag_block N d x)^T)
    ((3 * N%:R) *: 1%:M).
Proof.
move=> Hx; apply: paper_main_diag_block_from_trace.
by rewrite leNgt; apply/negP.
Qed.

(* 2. Markov. *)
Definition pmdbl_X N d (x : (N * d).-tuple (measurableTypeR R)) : measurableTypeR R :=
  pmdbl_F N d (tval x).

Lemma pmdbl_X_measurable N d :
  measurable_fun [set: (N * d).-tuple (measurableTypeR R)] (pmdbl_X N d).
Proof.
have [HC _] := paper_main_diag_trace4_regular d N.
exact: (gpp_joint_measurable (N * d) (pmdbl_F N d) HC).
Qed.

Theorem paper_main_diag_trace_event_markov N d : (0 < N)%N ->
  (paper_main_probability N d (paper_main_diag_trace_event N d) <=
   ((N%:R * (2 ^+ 21 * d%:R ^+ 4 + 16 * d%:R) +
     3 * N%:R * (N%:R - 1) * d%:R * (4 * d%:R + 52) ^+ 2) / N%:R ^+ 4)%:E)%E.
Proof.
move=> HN.
have HR := paper_main_diag_trace4_regular d N.
have [HC _] := HR.
have [_ HE] := pmdf_actual (N * d) (pmdbl_F N d) HR.
have Hge xs : 0 <= pmdbl_F N d xs by exact: paper_main_diag_trace4_ge0.
pose X : {RV gaussian_product_law (N * d) >-> (R : realType)} :=
  @MeasurableFun.Pack _ _ _ (R : realType) (pmdbl_X N d)
  (MeasurableFun.Class (isMeasurableFun.Build _ _ _ (R : realType) _
  (pmdbl_X_measurable N d))).
have Ht : 0 < N%:R ^+ 4 :> R by rewrite exprn_gt0 // ltr0n.
have HM := @markov _ _ _ _ X id (N%:R ^+ 4) Ht (@measurable_id _ _ setT) (fun r Hr => Hr)
  (fun r s _ _ Hrs => Hrs).
have HEX : ('E_(gaussian_product_law (N * d))[(id \o (fun x => `|x|%R)) \o X] =
    (gaussian_iterated_expectation (N * d) (pmdbl_F N d))%:E)%E.
  rewrite unlock -HE; apply: eq_integral => x _ /=.
  by rewrite /pmdbl_X ger0_norm.
have Hset : [set x | ((N%:R ^+ 4)%:E <= `|(X x)%:E|)%E] =
    [set x : (N * d).-tuple (measurableTypeR R) | Rle (N%:R ^+ 4) (pmdbl_F N d (tval x))].
  apply/seteqP; split => x /=.
    by rewrite lee_fin /pmdbl_X ger0_norm //; move/RleP.
  by rewrite lee_fin /pmdbl_X ger0_norm //; move/RleP.
rewrite Hset HEX in HM.
have Hmeas := pmsd_ge_measurable (N * d) (pmdbl_F N d) (N%:R ^+ 4) HC.
have Hsub : paper_main_diag_trace_event N d `<=`
    [set x : (N * d).-tuple (measurableTypeR R) | Rle (N%:R ^+ 4) (pmdbl_F N d (tval x))].
  rewrite pmdbl_event_list => x /= Hx; exact: Rlt_le.
have HP : (paper_main_probability N d (paper_main_diag_trace_event N d) <=
    gaussian_product_law (N * d)
      [set x : (N * d).-tuple (measurableTypeR R) | Rle (N%:R ^+ 4)%R (pmdbl_F N d (tval x))])%E.
  rewrite /paper_main_probability; apply: le_measure; rewrite ?inE //.
  exact: paper_main_diag_trace_event_measurable.
apply: (le_trans HP).
have HM' : (gaussian_product_law (N * d)
      [set x : (N * d).-tuple (measurableTypeR R) | Rle (N%:R ^+ 4)%R (pmdbl_F N d (tval x))] <=
    ((N%:R ^+ 4)^-1)%:E * (gaussian_iterated_expectation (N * d) (pmdbl_F N d))%:E)%E.
  by rewrite lee_pdivlMl.
apply: (le_trans HM'); rewrite -EFinM lee_fin mulrC.
apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
exact: paper_main_diag_trace_moment.
Qed.

(* 3. The rate. *)
Lemma pmdbl_rate (c : R) (N d : nat) : 0 < c -> (0 < d)%N -> c * d%:R ^+ 2 <= N%:R ->
  (N%:R * (2 ^+ 21 * d%:R ^+ 4 + 16 * d%:R) +
    3 * N%:R * (N%:R - 1) * d%:R * (4 * d%:R + 52) ^+ 2) / N%:R ^+ 4 <=
  ((2 ^+ 21 + 16) / c ^+ 3 + 9408 / c ^+ 2) / d%:R.
Proof.
move=> Hc Hd HcN.
set n := N%:R in HcN *; set x := d%:R.
have Hx1 : 1 <= x by rewrite /x ler1n.
have Hx0 : 0 < x by lra.
have Hcx : 0 < c * x ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have Hn0 : 0 < n by lra.
pose a := c^-1.
have Ha : 0 < a by rewrite invr_gt0.
have Hac : a * c = 1 by rewrite mulVf // gt_eqF.
have Hax : x ^+ 2 <= a * n.
  have := ler_wpM2l (ltW Ha) HcN; rewrite mulrA Hac mul1r; exact.
have Hx2 : 0 <= x ^+ 2 by exact: exprn_ge0.
have H3 : x ^+ 6 <= (a * n) ^+ 3.
  have -> : x ^+ 6 = (x ^+ 2) ^+ 3 by rewrite -exprM.
  by apply: lerXn2r; rewrite ?nnegrE // (le_trans Hx2 Hax).
have H2 : x ^+ 4 <= (a * n) ^+ 2.
  have -> : x ^+ 4 = (x ^+ 2) ^+ 2 by rewrite -exprM.
  by apply: lerXn2r; rewrite ?nnegrE // (le_trans Hx2 Hax).
have -> : (2 ^+ 21 + 16) / c ^+ 3 + 9408 / c ^+ 2 = (2 ^+ 21 + 16) * a ^+ 3 + 9408 * a ^+ 2.
  by rewrite /a !exprVn.
rewrite ler_pdivrMr ?exprn_gt0 //.
rewrite [X in _ <= X]mulrAC ler_pdivlMr //.
have Hx5 : x ^+ 5 <= x ^+ 6 by exact: (ler_weXn2l Hx1 (isT : (5 <= 6)%N)).
have Hx26 : x ^+ 2 <= x ^+ 6 by exact: (ler_weXn2l Hx1 (isT : (2 <= 6)%N)).
have HK0 : 0 <= 4 * x + 52 by lra.
have HK2 : (4 * x + 52) ^+ 2 <= (56 * x) ^+ 2.
  by apply: lerXn2r; rewrite ?nnegrE //; lra.
have T1 : n * (2 ^+ 21 * x ^+ 4 + 16 * x) * x <= (2 ^+ 21 + 16) * n * x ^+ 6.
  have E : n * (2 ^+ 21 * x ^+ 4 + 16 * x) * x = n * (2 ^+ 21 * x ^+ 5 + 16 * x ^+ 2) by ring.
  have E' : (2 ^+ 21 + 16) * n * x ^+ 6 = n * ((2 ^+ 21 + 16) * x ^+ 6) by ring.
  rewrite E E'; apply: ler_wpM2l; first exact: ltW.
  lra.
have T2 : 3 * n * (n - 1) * x * (4 * x + 52) ^+ 2 * x <= 9408 * n ^+ 2 * x ^+ 4.
  have Hq : 0 <= 3 * n * x ^+ 2 by rewrite !mulr_ge0 // ltW.
  have E : 3 * n * (n - 1) * x * (4 * x + 52) ^+ 2 * x =
      (3 * n * x ^+ 2) * ((n - 1) * (4 * x + 52) ^+ 2) by ring.
  have E' : 9408 * n ^+ 2 * x ^+ 4 = (3 * n * x ^+ 2) * (n * (56 * x) ^+ 2) by ring.
  rewrite E E'; apply: ler_wpM2l => //.
  have H0 : 0 <= (4 * x + 52) ^+ 2 by exact: sqr_ge0.
  nra.
have T3 : (2 ^+ 21 + 16) * n * x ^+ 6 <= (2 ^+ 21 + 16) * n * (a * n) ^+ 3.
  by apply: ler_wpM2l => //; rewrite mulr_ge0 // ltW.
have T4 : 9408 * n ^+ 2 * x ^+ 4 <= 9408 * n ^+ 2 * (a * n) ^+ 2.
  apply: ler_wpM2l H2; apply: mulr_ge0; [exact: ler0n | exact: (exprn_ge0 2 (ltW Hn0))].
have E : ((2 ^+ 21 + 16) * a ^+ 3 + 9408 * a ^+ 2) * n ^+ 4 =
    (2 ^+ 21 + 16) * n * (a * n) ^+ 3 + 9408 * n ^+ 2 * (a * n) ^+ 2 by ring.
rewrite E; lra.
Qed.

Lemma pmdbl_inv_rate (p : nat -> \bar R) (A : R) :
  0 <= A -> (forall d, (0 <= p d)%E) ->
  (exists D, forall d, (D <= d)%N -> (p d <= (A / d%:R)%:E)%E) ->
  paper_main_tends_to p 0.
Proof.
move=> HA Hp [D HD] eps Heps.
have [K HK] := INR_unbounded (A / eps).
exists (maxn D K.+1) => d Hd.
have HdD : (D <= d)%N by exact: leq_trans (leq_maxl _ _) Hd.
have HdK : (K.+1 <= d)%N by exact: leq_trans (leq_maxr _ _) Hd.
have HKd : K%:R < d%:R :> R by rewrite ltr_nat.
have HAK : A / eps < K%:R by rewrite -INRE; apply/RltP.
have Hd0 : 0 < d%:R :> R by rewrite ltr0n (leq_trans _ HdK).
have Hrate : A / d%:R < eps.
  rewrite ltr_pdivrMr //.
  have := HAK; rewrite ltr_pdivrMr // => HAK'.
  have : eps * K%:R <= eps * d%:R by apply: ler_wpM2l; [exact: ltW | exact: ltW].
  lra.
rewrite sube0 (gee0_abs (Hp d)).
apply: le_lt_trans (HD d HdD) _; rewrite lte_fin; exact: Hrate.
Qed.

(* 4. The limit. *)
Theorem paper_main_diag_block_tends_to_zero (N : nat -> nat) (c : R) :
  0 < c -> paper_main_eventually_ge (paper_main_density N) c ->
  paper_main_tends_to
    (fun d => paper_main_probability (N d) d (paper_main_diag_trace_event (N d) d)) 0.
Proof.
move=> Hc [D HD].
have Hc2 : 0 < c ^+ 2 by rewrite exprn_gt0.
have Hc3 : 0 < c ^+ 3 by rewrite exprn_gt0.
have HA : 0 <= (2 ^+ 21 + 16) / c ^+ 3 + 9408 / c ^+ 2.
  apply: addr_ge0; apply: divr_ge0.
  - by apply: addr_ge0; [apply: exprn_ge0; exact: ler0n | exact: ler0n].
  - exact: ltW.
  - exact: ler0n.
  - exact: ltW.
apply: (pmdbl_inv_rate _ _ HA); first by move=> d; exact: measure_ge0.
exists (maxn D 1) => d Hd.
have HdD : (D <= d)%N by exact: leq_trans (leq_maxl _ _) Hd.
have Hd1 : (0 < d)%N by exact: leq_trans (leq_maxr _ _) Hd.
have Hd0 : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0 // ltr0n.
have HcN : c * d%:R ^+ 2 <= (N d)%:R.
  by have := HD d HdD; rewrite /paper_main_density ler_pdivlMr.
have HN0 : (0 < N d)%N.
  by rewrite -(ltr0n R); apply: lt_le_trans HcN; rewrite mulr_gt0.
apply: (le_trans (paper_main_diag_trace_event_markov (N d) d HN0)).
by rewrite lee_fin; exact: pmdbl_rate.
Qed.
