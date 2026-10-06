(* From the moments of walk words to a walk weight.
   SquareFree.WalkExpansion writes E tr W^(K+1) as a sum over
   closed walks i, t, i and label lists ps of the moments of walk words.
   This file reads these words in the walk model of
   SquareFree.WalkCount, with rows rs = i :: t and L = K + 1 steps:
   - the coordinates r * d + c (r < N, c < d) enumerate 'I_(N * d)
     (pmsw_big_coord);
   - the multiplicity of r * d + c in the word is the degree
     pmsc_deg rs ps r c (pmsw_bridge_count). So the moment is the product of
     moment_factor over all degrees, and the exponent of pmsw_moment_le is
     the excess pmsc_X (pmsw_bridge_excess);
   - the walks of E tr W^(K+1) are loop-free with distinct label pairs, and
     a nonzero moment makes them even (pmsw_bridge_loopfree,
     pmsw_bridge_distinct, pmsw_bridge_even);
   - so the moment is at most [even] (4 L)^(2 e), with the deficiency
     e = 2 L + 2 - 2 R - C (pmsw_bridge_weight). Summed over walks, this
     bounds E tr W^(K+1) by a natural number, the walk weight
     pmsw_walk_weight (paper_main_squarefree_offdiag_weight). *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.IteratedExpectationDefinitions GaussianProbabilityProductDefinitions
  SquareFree.WalkMoments SquareFree.WalkExpansion SquareFree.WalkWeight
  SquareFree.WalkCount SquareFree.WalkExcess.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. The coordinates r * d + c enumerate 'I_(N * d). *)
Lemma pmsw_big_coord (T : Type) (idx : T) (op : Monoid.law idx) (N d : nat) (F : nat -> T) :
  \big[op/idx]_(k < N * d) F k = \big[op/idx]_(r < N) \big[op/idx]_(c < d) F (pmsw_coord d r c).
Proof.
rewrite -(big_mkord xpredT F).
elim: N => [|N IH]; first by rewrite mul0n big_ord0 big_geq.
rewrite mulSnr big_ord_recr /= (big_cat_nat (leq0n (N * d)) (leq_addr d (N * d))) /= IH.
congr (op _ _).
rewrite -{1}[(N * d)%N]add0n big_addn addKn big_mkord; apply: eq_bigr => c _.
by rewrite /pmsw_coord addnC.
Qed.

Lemma pmsw_seqs_all (T : eqType) (s : seq T) K w :
  w \in pmsw_seqs s K -> all (fun x => x \in s) w.
Proof.
elim: K w => [|K IH] w /=; first by rewrite inE => /eqP ->.
by case/allpairsP => [[x u] [Hx Hu ->]] /=; rewrite Hx (IH u Hu).
Qed.

Section Bridge.
Variables N d : nat.
Implicit Types (i : 'I_N) (t : seq 'I_N) (ps : seq ('I_d * 'I_d)).

(* 2. Multiplicities, moments and the excess. *)
Lemma pmsw_rows_closed i t : pmsw_rows N i t i = zip (i :: t) (rot 1 (i :: t)).
Proof. by rewrite /pmsw_rows rot1_cons. Qed.

Lemma pmsw_bridge_count i t ps (r : 'I_N) (c : 'I_d) : size ps = (size t).+1 ->
  count_mem (pmsw_coord d r c) (pmsw_word N d i t i ps) = pmsc_deg N d (i :: t) ps r c.
Proof.
move=> Hs; rewrite (pmsw_count_word N d r c i t i ps Hs) pmsw_rows_closed.
by [].
Qed.

Lemma pmsw_bridge_excess i t ps : size ps = (size t).+1 ->
  (\sum_(k < N * d) ((count_mem (k : nat) (pmsw_word N d i t i ps))./2 -
      (0 < count_mem (k : nat) (pmsw_word N d i t i ps))))%N =
  pmsc_X N d (i :: t) ps.
Proof.
move=> Hs.
rewrite (pmsw_big_coord _ _ _ N d (fun k => ((count_mem k (pmsw_word N d i t i ps))./2 -
  (0 < count_mem k (pmsw_word N d i t i ps)))%N)).
by apply: eq_bigr => r _; apply: eq_bigr => c _; rewrite /pmsc_term pmsw_bridge_count.
Qed.

(* 3. The walks of E tr W^(K+1). *)
Lemma pmsw_steps_all i t (j : 'I_N) :
  pmsw_steps N i t j = all (fun e => e.1 != e.2) (zip (i :: t) (rcons t j)).
Proof. by elim: t i => [|k t IH] i /=; rewrite ?andbT // IH. Qed.

Lemma pmsw_bridge_loopfree i t : pmsw_steps N i t i = pmsc_loopfree N (i :: t).
Proof. by rewrite pmsw_steps_all /pmsc_loopfree rot1_cons. Qed.

Lemma pmsw_bridge_distinct K ps : ps \in pmsw_seqs (pmsw_pairs d) K -> pmsc_distinct d ps.
Proof.
move=> /pmsw_seqs_all /allP H; apply/allP => p /H.
by rewrite /pmsw_pairs mem_filter => /andP [].
Qed.

Lemma pmsw_bridge_even i t ps : size ps = (size t).+1 ->
  pmsw_moment (N * d) (pmsw_word N d i t i ps) != 0 -> pmsc_even N d (i :: t) ps.
Proof.
move=> Hs Hm r c; have := pmsw_word_moment_even N d i t i ps Hs Hm r c.
by rewrite -(pmsw_count_word N d r c i t i ps Hs) pmsw_bridge_count.
Qed.

(* 4. The weight of a walk. *)
Definition pmsw_even_b (rs : seq 'I_N) ps : bool :=
  [forall r : 'I_N, [forall c : 'I_d, ~~ odd (pmsc_deg N d rs ps r c)]].

Lemma pmsw_even_bP (rs : seq 'I_N) ps : reflect (pmsc_even N d rs ps) (pmsw_even_b rs ps).
Proof.
apply: (iffP forallP) => [H r c | H r]; first by have /forallP := H r; apply.
by apply/forallP => c; exact: H.
Qed.

Theorem pmsw_bridge_weight i t ps :
  ps \in pmsw_seqs (pmsw_pairs d) (size t).+1 -> pmsw_steps N i t i ->
  pmsw_moment (N * d) (pmsw_word N d i t i ps) <=
  (pmsw_even_b (i :: t) ps)%:R * (4 * (size t).+1)%:R ^+ (2 * pmsc_e N d (i :: t) ps).
Proof.
move=> Hps Hst.
have Hs : size ps = (size t).+1 := pmsw_seqs_size Hps.
case: (eqVneq (pmsw_moment (N * d) (pmsw_word N d i t i ps)) 0) => [-> | Hm].
  by rewrite mulr_ge0 ?ler0n ?exprn_ge0.
have He := pmsw_bridge_even i t ps Hs Hm.
rewrite (introT (pmsw_even_bP _ _) He) mul1r.
have Hl : pmsc_loopfree N (i :: t) by rewrite -pmsw_bridge_loopfree.
have HX := pmsc_X_le_e N d (i :: t) ps Hs Hl (pmsw_bridge_distinct _ _ Hps) He.
apply: (le_trans (pmsw_moment_le _ _)).
rewrite (pmsw_word_size N d i t i ps Hs) (pmsw_bridge_excess i t ps Hs) Hs.
by apply: ler_weXn2l HX; rewrite ler1n muln_gt0.
Qed.

(* 5. The walk weight bounds E tr W^(K+1). *)
Definition pmsw_walk_weight K : nat :=
  (\sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    pmsw_steps N i t i * \sum_(ps <- pmsw_seqs (pmsw_pairs d) K.+1)
      pmsw_even_b (i :: t) ps * (4 * K.+1) ^ (2 * pmsc_e N d (i :: t) ps))%N.

Theorem paper_main_squarefree_offdiag_weight K :
  gaussian_iterated_expectation (N * d) (fun xs => \tr (pmsw_W N d xs ^+ K.+1)) <=
  (pmsw_walk_weight K)%:R.
Proof.
rewrite paper_main_squarefree_offdiag_walks /pmsw_walk_weight natr_sum.
apply: ler_sum => i _; rewrite natr_sum big_seq [X in _ <= X]big_seq.
apply: ler_sum => t Ht; rewrite natrM natr_sum.
case Hst: (pmsw_steps N i t i); last by rewrite !mul0r.
rewrite !mul1r big_seq [X in _ <= X]big_seq; apply: ler_sum => ps Hps.
rewrite natrM natrX -(pmsw_seqs_size Ht).
by apply: pmsw_bridge_weight; rewrite ?(pmsw_seqs_size Ht).
Qed.

End Bridge.
