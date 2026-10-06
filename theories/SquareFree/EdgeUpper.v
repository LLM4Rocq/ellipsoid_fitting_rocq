(* The upper spectral edge of the square-free block, first part: the trace
   moment and the trace box.
   - pmeu_walk_weight: the walk weight of SquareFree.WalkBridge is
     the sum of the moment weights over the valid walks of
     SquareFree.WalkShapeOnce, with B = 4 L.
   - pmeu_absorb: 2 (4L)^4 <= 2^L for L >= 32. This absorbs the residual
     polynomial factor at logarithmic walk length.
   - paper_main_squarefree_offdiag_trace_le: for the off-diagonal part W of
     V V^T and L >= 32, E tr W^L <= N (52 d^2)^L when 0 < N <= d^2 and
     16 L^2 (2L)^45 <= d.
   - pmeu_trace_box: for symmetric Z and L = 2^(j+1), tr Z^L <= t^L gives
     -t I <= Z <= t I, by opnorm_le_trace_exp of
     GaussianAnalysis.matrix.opnorm. *)
From Stdlib Require Import Reals Lia ArithRing.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic sesquilinear.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.IteratedExpectationDefinitions GaussianProbabilityProductDefinitions
  SquareFree.WalkMoments SquareFree.WalkExpansion SquareFree.WalkWeight
  SquareFree.WalkCount SquareFree.WalkExcess SquareFree.WalkBridge
  SquareFree.WalkShapeRecursion SquareFree.WalkShapeOnce
  SquareFree.WalkShapeBound PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.Separation Geometry.HeadFrobenius
  Geometry.HeadFeature Geometry.HeadCorrection Geometry.HeadCoefficients
  Spectral.SymmetricBilinear Cone.ConditionOperator DiagonalBlock.Trace
  Spectral.SymmetricDiagonalization.
Import GRing.Theory Num.Theory Order.TTheory.

(* 1. Sums over lists of a fixed length and over tuples. *)
Lemma pmeu_sum_tuple0 (T : finType) (G : seq T -> nat) :
  (\sum_(t : 0.-tuple T) G t = G [::])%N.
Proof.
rewrite (big_pred1 [tuple]) // => t /=; apply/esym/eqP; apply: val_inj.
by apply: size0nil; rewrite size_tuple.
Qed.

Lemma pmeu_sum_tuple_cons (T : finType) (K : nat) (G : seq T -> nat) :
  (\sum_(w : K.+1.-tuple T) G w = \sum_(x : T) \sum_(t : K.-tuple T) G (x :: t))%N.
Proof.
rewrite pair_bigA /= (reindex (fun p : T * K.-tuple T => [tuple of p.1 :: p.2])) //=.
apply: onW_bij; exists (fun w : K.+1.-tuple T => (thead w, [tuple of behead w])).
  by case=> x t /=; rewrite theadE; congr (_, _); apply: val_inj.
by move=> w; rewrite /= [in RHS](tuple_eta w).
Qed.

Lemma pmeu_seqs_tuple (T : finType) (P : pred T) (K : nat) (F : seq T -> nat) :
  (\sum_(t <- pmsw_seqs [seq x <- index_enum T | P x] K) F t =
   \sum_(t : K.-tuple T) all P t * F t)%N.
Proof.
elim: K F => [|K IH] F.
  by rewrite /= big_seq1 (pmeu_sum_tuple0 _ (fun t => (all P t * F t)%N)) /= mul1n.
rewrite /= big_allpairs_dep /= big_filter.
rewrite (pmeu_sum_tuple_cons _ _ (fun t => (all P t * F t)%N)) /=.
rewrite big_mkcond /=; apply: eq_bigr => x _; rewrite (IH (fun t => F (x :: t))).
by case: (P x) => /=; last by rewrite big1.
Qed.

(* 2. The walk weight is the sum over valid walks. *)
Theorem pmeu_walk_weight (N d K : nat) :
  pmsw_walk_weight N d K = pmso_S N d (4 * K.+1) K.+1 K.+1 0.
Proof.
rewrite /pmso_S leqnn /pmsw_walk_weight.
rewrite -(pair_bigA _ (fun (rs : K.+1.-tuple 'I_N) (ps : K.+1.-tuple ('I_d * 'I_d)) =>
  ((0 <= pmso_fv N rs) * pmso_w N d (4 * K.+1) rs ps)%N)) /=.
rewrite (pmeu_sum_tuple_cons _ _ (fun s : seq 'I_N => \sum_(ps : K.+1.-tuple ('I_d * 'I_d))
  ((0 <= pmso_fv N s) * pmso_w N d (4 * K.+1) s ps)%N)) /=.
apply: eq_bigr => i _.
rewrite -/(pmsw_seqs (pmsw_pairs d) K.+1) /pmsw_pairs.
rewrite -{1}(filter_predT (index_enum 'I_N)) (pmeu_seqs_tuple _ predT K (fun t =>
  (pmsw_steps N i t i * \sum_(ps <- pmsw_seqs [seq p <- index_enum ('I_d * 'I_d)%type |
    p.1 != p.2] K.+1) pmsw_even_b N d (i :: t) ps *
    (4 * K.+1) ^ (2 * pmsc_e N d (i :: t) ps))%N)).
apply: eq_bigr => t _; rewrite all_predT mul1n.
rewrite (pmeu_seqs_tuple _ (fun p : 'I_d * 'I_d => p.1 != p.2) K.+1 (fun ps =>
  (pmsw_even_b N d (i :: t) ps * (4 * K.+1) ^ (2 * pmsc_e N d (i :: t) ps))%N)).
rewrite big_distrr /=; apply: eq_bigr => ps _.
rewrite mul1n /pmso_w /pmso_valid size_tuple /= size_tuple eqxx /=.
rewrite (pmsw_bridge_loopfree N i t) /pmsc_distinct.
by rewrite -!mulnb -!mulnA.
Qed.

(* 3. The residual polynomial factor at logarithmic length. *)
Lemma pmeu_step4 (L : nat) : (32 <= L -> L.+1 ^ 4 <= 2 * L ^ 4)%N.
Proof.
move=> HL.
have H1 : (32 * (L * L * L) <= L * L * L * L)%N.
  by rewrite [X in (_ <= X)%N]mulnC leq_mul2r HL orbT.
have H2 : (32 * (L * L) <= L * L * L)%N by rewrite [X in (_ <= X)%N]mulnC leq_mul2r HL orbT.
have H3 : (32 * L <= L * L)%N by rewrite leq_mul2r HL orbT.
move: HL H1 H2 H3; rewrite !expnE /= -!multE.
by move=> /ssrnat.leP HL /ssrnat.leP H1 /ssrnat.leP H2 /ssrnat.leP H3; apply/ssrnat.leP; lia.
Qed.

Lemma pmeu_absorb (L : nat) : (32 <= L -> 2 * (4 * L) ^ 4 <= 2 ^ L)%N.
Proof.
elim: L => [//|L IH] HL.
case: (ltngtP L 31) => [H | H | ->].
- by move: HL; rewrite ltnS leqNgt H.
- have IH' := IH H; have H4 := pmeu_step4 L H.
  rewrite (expnS 2 L); apply: (@leq_trans (2 * (2 * (4 * L) ^ 4))).
    by rewrite leq_mul2l /= !expnMn mulnCA leq_mul2l /=; exact: H4.
  by rewrite leq_mul2l IH' orbT.
- have E : (4 * 32 = 2 ^ 7)%N by [].
  by rewrite E -expnM -expnS leq_exp2l.
Qed.

(* 4. The trace moment of the off-diagonal part. *)
Theorem pmeu_walk_weight_le (N d L : nat) : (0 < N)%N -> (0 < d)%N -> (N <= d ^ 2)%N ->
  (32 <= L)%N -> (16 * L ^ 2 * (2 * L) ^ 45 <= d)%N ->
  (pmsw_walk_weight N d L.-1 <= N * (52 * d ^ 2) ^ L)%N.
Proof.
move=> HN Hd HNd HL HLd.
have HL0 : (0 < L)%N by exact: leq_trans _ HL.
have HL1 : L.-1.+1 = L by rewrite prednK.
rewrite pmeu_walk_weight HL1.
have HB : (0 < 4 * L)%N by rewrite muln_gt0.
have HB2 : ((4 * L) ^ 2 = 16 * L ^ 2)%N by rewrite expnMn.
have H2 : ((4 * L) ^ 2 * (2 * L) ^ 45 <= d)%N by rewrite HB2.
have H1 : (L * (4 * L) ^ 2 <= d)%N.
  apply: leq_trans H2; rewrite mulnC leq_mul2l; apply/orP; right.
  apply: leq_trans (leq_pmulr L (isT : (0 < 2)%N)) _; rewrite mulnC.
  by rewrite -{1}(expn1 (2 * L)) leq_pexp2l // muln_gt0.
apply: leq_trans (pmsb_S_le N d (4 * L) L L HN Hd HB HNd H1 H2) _.
rewrite (_ : (52 * d ^ 2 = 2 * (26 * d ^ 2))%N); first by rewrite mulnA.
rewrite (expnMn 2 (26 * d ^ 2) L); have Ha := pmeu_absorb L HL.
move: Ha; move: ((4 * L) ^ 4)%N ((26 * d ^ 2) ^ L)%N (2 ^ L)%N => X Y Z Ha.
rewrite [(2 * N)%N]mulnC -!mulnA leq_mul2l; apply/orP; right.
by rewrite mulnA leq_mul2r Ha orbT.
Qed.

(* 5. A trace power bound is a Loewner box, with no spectral theorem. *)
Section TracePower.
Local Open Scope ring_scope.
Variable n : nat.
Implicit Types (Z : 'M[R]_n) (v : 'cV[R]_n).

Lemma pmeu_trmx_exp Z m : Z^T = Z -> (Z ^+ m)^T = Z ^+ m.
Proof.
move=> HZ; elim: m => [|m IH]; first by rewrite !expr0 trmx1.
rewrite exprS -mulmxE trmx_mul IH HZ.
by rewrite mulmxE -exprSr exprS.
Qed.

Theorem pmeu_trace_box Z (t : R) j : Z^T = Z -> 0 <= t ->
  \tr (Z ^+ (2 ^ j.+1)) <= t ^+ (2 ^ j.+1) ->
  paper_main_loewner_le ((- t) *: 1%:M) Z /\ paper_main_loewner_le Z (t *: 1%:M).
Proof.
move=> /symmetricmxP HZ Ht HT; apply/paper_main_loewner_boxP; split => //.
apply/(opnorm_symP HZ Ht)/(opnorm_le_trace_exp HZ (p := 2 ^ j.+1)) => //.
  by rewrite oddX.
by rewrite expn_gt0.
Qed.

End TracePower.

(* 6. The trace moment of the off-diagonal part of V V^T. *)
Section TraceMoment.
Local Open Scope ring_scope.

Theorem paper_main_squarefree_offdiag_trace_le (N d L : nat) : (0 < N)%N -> (0 < d)%N ->
  (N <= d ^ 2)%N -> (32 <= L)%N -> (16 * L ^ 2 * (2 * L) ^ 45 <= d)%N ->
  gaussian_iterated_expectation (N * d) (fun xs => \tr (pmsw_W N d xs ^+ L)) <=
  (N * (52 * d ^ 2) ^ L)%N%:R.
Proof.
move=> HN Hd HNd HL HLd.
have HL1 : L.-1.+1 = L by rewrite prednK // (leq_trans _ HL).
have H := paper_main_squarefree_offdiag_weight N d L.-1; rewrite HL1 in H.
apply: le_trans H _; rewrite ler_nat.
exact: pmeu_walk_weight_le.
Qed.

End TraceMoment.
