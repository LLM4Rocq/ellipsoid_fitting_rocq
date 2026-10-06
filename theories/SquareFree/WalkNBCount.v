(* The non-backtracking (NB) trace moment as a sum over marked walks.
   The trace moment of SquareFree.WalkNB is a sum over closed walks
   whose columns are NB inside each of the q + 1 segments of m + 1 steps.
   Marking the segment starts (pmnct_ms0) turns this into the marked NB
   condition of SquareFree.WalkNBMarks (pmnct_segs_nb), and the
   walk sum into the sum of pmnm_w over tuple walks with B = 4 L
   (pmnct_weight), since each walk moment is at most [even] (4 L)^(2e)
   (pmsw_bridge_weight).
   - pmnct_moment_walk: E tr T(m+1)^(q+1) <= kap^L sum_W pmnm_w ms0 W, with
     L = (q+1)(m+1) and q + 1 marks (pmnct_ms0_count).
   The only probability input is the expansion pmnb_trace_moment. *)
From Stdlib Require Import Reals Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.IteratedExpectationDefinitions GaussianProbabilityProductDefinitions
  SquareFree.WalkMoments SquareFree.WalkExpansion SquareFree.WalkWeight
  SquareFree.WalkCount SquareFree.WalkExcess SquareFree.WalkBridge
  SquareFree.WalkShapeOnce SquareFree.WalkShapeBound SquareFree.EdgeLower
  SquareFree.WalkNB SquareFree.EdgeUpper SquareFree.WalkNBMarks
  SquareFree.WalkNBCore SquareFree.WalkNBCoreSum.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope nat_scope.

(* 1. Marks at the segment starts. *)
Definition pmnct_ms0 (s L : nat) : seq bool := mkseq (fun t => t %% s == 0) L.

Lemma pmnct_ms0_size s L : size (pmnct_ms0 s L) = L.
Proof.
by rewrite size_mkseq.
Qed.

Lemma pmnct_ms0_count s q : 0 < s -> count id (pmnct_ms0 s (q * s)) = q.
Proof.
move=> Hs; rewrite /pmnct_ms0 /mkseq count_map.
elim: q => [|q IH]; first by rewrite mul0n.
rewrite mulSn addnC iotaD count_cat IH add0n -[in RHS]addn1; congr (_ + _).
(* In the block [q s, q s + s), only q s is a multiple of s. *)
have -> : iota (q * s) s = q * s :: iota (q * s).+1 s.-1.
  by rewrite -[X in iota _ X](prednK Hs).
rewrite /= modnMl eqxx add1n; congr (_.+1).
apply/eqP; rewrite -leqn0 leqNgt -has_count; apply/negP => /hasP [t].
rewrite mem_iota => /andP [H1 H2] /= Ht.
have Et : t = q * s + (t - q * s) by rewrite subnKC // ltnW.
move: Ht; rewrite Et modnMDl modn_small; last first.
  by rewrite subn_eq0 leqNgt H1.
by rewrite ltn_subLR ?(ltnW H1) // (leq_trans H2) // addSnnS prednK.
Qed.

(* Inside a segment, consecutive columns differ. *)
Lemma pmnct_segs_nth (C : finType) (c0 : C) seg q (cs : seq C) t : 0 < seg ->
  size cs = q * seg -> pmnb_segs C seg q cs -> t.+1 < size cs -> t.+1 %% seg != 0 ->
  nth c0 cs t != nth c0 cs t.+1.
Proof.
move=> Hseg; elim: q cs t => [|q IH] cs t Hsz; first by rewrite Hsz mul0n.
move=> /= /andP [Hc Hrest] Ht Hmod.
have Hsz1 : size (take seg cs) = seg by rewrite size_takel // Hsz mulSn leq_addr.
have Hsz2 : size (drop seg cs) = q * seg by rewrite size_drop Hsz mulSn addKn.
case: (ltnP t.+1 seg) => Hts.
  (* Inside the first segment: the path condition. *)
  move: Hc Hsz1; case Etk: (take seg cs) => [|c rest] Hc Hsz1.
    by move: Hseg; rewrite -Hsz1.
  have Htr : t < size rest by move: Hsz1 => /= Hs1; rewrite -ltnS Hs1.
  have := (pathP c0 Hc) t Htr.
  have -> : nth c0 rest t = nth c0 (c :: rest) t.+1 by [].
  by rewrite -Etk !nth_take // (ltn_trans (ltnSn t) Hts).
(* Past the first segment: drop it. *)
have Hne : t.+1 != seg by apply: contraNneq Hmod => ->; rewrite modnn.
have Hst : seg <= t by rewrite -ltnS ltn_neqAle eq_sym Hne Hts.
have Et : t = seg + (t - seg) by rewrite subnKC.
have Et1 : t.+1 = seg + (t - seg).+1 by rewrite addnS -Et.
rewrite Et1 [X in nth c0 cs X != _]Et -!nth_drop.
apply: IH => //.
  by rewrite Hsz2 -(ltn_add2l seg) -Et1 -mulSn -Hsz.
by move: Hmod; rewrite Et1 modnDl.
Qed.

Lemma pmnct_segs_nb d (q0 : 'I_d * 'I_d) seg q (cs : seq ('I_d * 'I_d)) : 0 < seg ->
  size cs = q * seg -> pmnb_segs _ seg q cs -> pmnm_nb d q0 (pmnct_ms0 seg (q * seg)) cs.
Proof.
move=> Hseg Hsz Hsegs; apply/(pmnm_nbP d q0) => t Ht.
rewrite /pmnm_succ /pmnct_ms0; case: ifP => Ht1.
  rewrite nth_mkseq -?Hsz //; case: eqP => [// | Hm] /=.
  by apply: (pmnct_segs_nth _ q0 seg q cs t Hseg Hsz Hsegs Ht1); apply/eqP.
(* The step back to position 0 crosses a junction. *)
by rewrite nth_mkseq ?mod0n // -Hsz (leq_ltn_trans (leq0n t) Ht).
Qed.

(* 2. The walk weight of the trace moment. *)
Lemma pmnct_weight N d (q0 : 'I_d * 'I_d) m q :
  (\sum_(i < N) \sum_(rs <- pmsw_seqs (index_enum 'I_N) (m + q * m.+1))
     \sum_(cs <- pmsw_seqs (index_enum ('I_d * 'I_d)%type) (q.+1 * m.+1))
       [&& pmsw_steps N i rs i, pmnb_segs _ m.+1 q.+1 cs &
           all (fun c : 'I_d * 'I_d => (c.1 < c.2)%N) cs] *
       (pmsw_even_b N d (i :: rs) cs *
        (4 * (q.+1 * m.+1)) ^ (2 * pmsc_e N d (i :: rs) cs)) <=
   \sum_(W : (q.+1 * m.+1).-tuple 'I_N * (q.+1 * m.+1).-tuple ('I_d * 'I_d))
     pmnm_w N d q0 (4 * (q.+1 * m.+1)) (pmnct_ms0 m.+1 (q.+1 * m.+1)) W.1 W.2)%N.
Proof.
set K := m + q * m.+1.
have EL : q.+1 * m.+1 = K.+1 by rewrite mulSn addSn.
rewrite EL.
set B := 4 * K.+1.
(* The tuple walks: a root, K more rows, and K + 1 pairs. *)
rewrite -(pair_bigA _ (fun (rs : K.+1.-tuple 'I_N) (ps : K.+1.-tuple ('I_d * 'I_d)) =>
  pmnm_w N d q0 B (pmnct_ms0 m.+1 K.+1) rs ps)).
rewrite (pmeu_sum_tuple_cons _ _ (fun s : seq 'I_N => \sum_(ps : K.+1.-tuple ('I_d * 'I_d))
  pmnm_w N d q0 B (pmnct_ms0 m.+1 K.+1) s ps)).
apply: leq_sum => i _.
rewrite -{1}(filter_predT (index_enum 'I_N)) (pmeu_seqs_tuple _ predT K (fun t =>
  \sum_(cs <- pmsw_seqs (index_enum ('I_d * 'I_d)%type) K.+1)
    [&& pmsw_steps N i t i, pmnb_segs _ m.+1 q.+1 cs &
        all (fun c : 'I_d * 'I_d => (c.1 < c.2)%N) cs] *
    (pmsw_even_b N d (i :: t) cs * B ^ (2 * pmsc_e N d (i :: t) cs)))).
apply: leq_sum => t _; rewrite all_predT mul1n.
rewrite -{1}(filter_predT (index_enum ('I_d * 'I_d)%type)) (pmeu_seqs_tuple _ predT K.+1
  (fun cs => [&& pmsw_steps N i t i, pmnb_segs _ m.+1 q.+1 cs &
        all (fun c : 'I_d * 'I_d => (c.1 < c.2)%N) cs] *
    (pmsw_even_b N d (i :: t) cs * B ^ (2 * pmsc_e N d (i :: t) cs)))).
apply: leq_sum => ps _; rewrite all_predT mul1n /pmnm_w.
(* Pointwise: such a walk is valid, marked NB and increasing. *)
case Hg: [&& pmsw_steps N i t i, pmnb_segs _ m.+1 q.+1 ps &
    all (fun c : 'I_d * 'I_d => (c.1 < c.2)%N) ps]; last by rewrite mul0n.
case He: (pmsw_even_b N d (i :: t) ps); last by rewrite mul0n muln0.
move: Hg => /and3P [Hst Hsg Hinc].
have Hps : size ps = K.+1 by rewrite size_tuple.
have -> : [&& pmso_valid N d (i :: t) ps, pmnm_nb d q0 (pmnct_ms0 m.+1 K.+1) ps
    & pmnm_incr d ps] = true.
  apply/and3P; split => //.
    apply/and4P; split.
    - by rewrite Hps /= size_tuple.
    - by rewrite -pmsw_bridge_loopfree.
    - by apply: sub_all Hinc => c /= Hc; rewrite neq_ltn Hc.
    - by apply/pmso_evenP; apply/pmsw_even_bP.
  have Hsz' : size ps = q.+1 * m.+1 by rewrite Hps EL.
  by have := pmnct_segs_nb d q0 m.+1 q.+1 ps (ltn0Sn m) Hsz' Hsg; rewrite EL.
by rewrite !mul1n.
Qed.

(* 3. The trace moment is at most kap^L times the marked walk sum. *)
Section Moment.
Local Open Scope ring_scope.
Variables (N d : nat) (q0 : 'I_d * 'I_d).

Theorem pmnct_moment_walk (kap : R) m q : 0 <= kap ->
  gaussian_iterated_expectation (N * d)
    (fun xs => \tr (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d xs) kap m.+1 ^+ q.+1)) <=
  kap ^+ (q.+1 * m.+1) *
  (\sum_(W : (q.+1 * m.+1).-tuple 'I_N * (q.+1 * m.+1).-tuple ('I_d * 'I_d))
     pmnm_w N d q0 (4 * (q.+1 * m.+1)) (pmnct_ms0 m.+1 (q.+1 * m.+1)) W.1 W.2)%:R.
Proof.
move=> Hk.
rewrite pmnb_trace_moment; apply: ler_wpM2l; first exact: exprn_ge0.
set L := (q.+1 * m.+1)%N.
have EL : L = (m + q * m.+1).+1 by rewrite /L mulSn addSn.
apply: (le_trans _ (_ : (\sum_(i < N) \sum_(rs <- pmsw_seqs (index_enum 'I_N) (m + q * m.+1))
  \sum_(cs <- pmsw_seqs (index_enum ('I_d * 'I_d)%type) L)
    [&& pmsw_steps N i rs i, pmnb_segs _ m.+1 q.+1 cs &
        all (fun c : 'I_d * 'I_d => (c.1 < c.2)%N) cs] *
    (pmsw_even_b N d (i :: rs) cs * (4 * L) ^ (2 * pmsc_e N d (i :: rs) cs)))%N%:R <= _)).
  (* Each moment is at most [even] (4 L)^(2e). *)
  rewrite natr_sum; apply: ler_sum => i _.
  rewrite natr_sum big_seq [X in _ <= X]big_seq; apply: ler_sum => rs Hrs.
  rewrite natr_sum big_seq [X in _ <= X]big_seq; apply: ler_sum => cs Hcs.
  case HB: [&& pmsw_steps N i rs i, pmnb_segs _ m.+1 q.+1 cs &
      all (fun c : 'I_d * 'I_d => (c.1 < c.2)%N) cs]; last by rewrite mul0r mul0n.
  rewrite mul1r mul1n natrM natrX.
  move: HB => /and3P [Hst _ Hinc].
  have Hsz := pmsw_seqs_size Hrs.
  have Hcs' : cs \in pmsw_seqs (pmsw_pairs d) (size rs).+1.
    rewrite pmnb_seqs_mem; move: Hcs; rewrite pmnb_seqs_mem => /andP [Hcsz _].
    rewrite Hsz -EL Hcsz /=; apply/allP => c Hc.
    change (c \in pmsw_pairs d).
    rewrite /pmsw_pairs mem_filter mem_index_enum andbT neq_ltn.
    by have := allP Hinc c Hc => ->.
  have := pmsw_bridge_weight N d i rs cs Hcs' Hst.
  by rewrite Hsz -EL.
by rewrite ler_nat; exact: pmnct_weight.
Qed.

End Moment.
