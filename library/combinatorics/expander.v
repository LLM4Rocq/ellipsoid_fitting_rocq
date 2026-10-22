From mathcomp Require Import all_ssreflect_compat fingroup perm.
From mathcomp Require Import ssralg ssrnum rat.
From mathcomp Require Import arithmetic_tactic ring_tactic.
From GaussianAnalysis.combinatorics Require Import binomial_bounds.

(**md**************************************************************************)
(* # Expanding bipartite multigraphs from permutations                        *)
(*                                                                            *)
(* For d permutations s 0, ..., s (d - 1) of 'I_l, consider the bipartite     *)
(* multigraph on the 2 l vertices 'I_(l + l) whose edge with label (j, u),    *)
(* for j < d and u < l, joins the left vertex lshift l u to the right vertex  *)
(* rshift l (s j u). Every vertex has degree d, the right ones because each s *)
(* j is a bijection; there are no loops, and parallel edges are distinct      *)
(* labels.                                                                    *)
(*                                                                            *)
(* - perm_cut s W: the cut of a vertex set W, the set of labels (j, u) whose  *)
(*   edge has exactly one end in W. Its cardinal counts the edges of the cut  *)
(*   with their multiplicities.                                               *)
(* - expander: for every l >= 1 there are 100 permutations s 0, ..., s 99 of  *)
(*   'I_l such that every vertex set W satisfies min(|W|, 2 l - |W|) <=       *)
(*   |perm_cut s W|; this statement was accepted with batch 1 of phase 14.    *)
(* - perm_cut_eq0: under that inequality, a set with an empty cut is empty or *)
(*   the whole vertex set; the example expander_connected gives a connected   *)
(*   multigraph for every l >= 1.                                             *)
(*                                                                            *)
(* General lemmas on the way:                                                 *)
(* - perm_imset_eq: the permutations of 'I_n act transitively on the sets of  *)
(*   a given size (from tuple_permP on the indicators of the two sets);       *)
(* - perm_into_card: #{tau : tau(S) in B} C(n, |S|) = C(|B|, |S|) n!, since   *)
(*   the sets tau(S) of size |S| have fibers of the same size                 *)
(*   (perm_fiber_card); with bin_mul_pow of binomial_bounds.v,                *)
(*   perm_into_bound: #{tau : tau(S) in B} n^|S| <= |B|^|S| n!;               *)
(* - perm_cutC, card_sides and perm_cut_ge: the cut does not change under     *)
(*   complement, and d |a - b| <= |perm_cut s W| for a and b the sizes of the *)
(*   two sides of W (card_perm_preim: the right vertices also have degree d); *)
(* - card_exists_le: the union bound for cardinals.                           *)
(*                                                                            *)
(* A Rocq formalization of the lemma 'Expanding multigraphs' (lem:expander)   *)
(* of 'Exponential PSD rank of positively shifted matching matrices' (family  *)
(* 126 of the OpenAI math collection, revision 1581d4cbd),                    *)
(* source/sections/parity.tex, lines 28-91, with d = 100 and beta = 1/100.    *)
(* The statement departs from the TeX in three ways. It holds for every l >=  *)
(* 1, that is for every even t = 2 l >= 2, where the TeX says every           *)
(* sufficiently large even t: no step of the proof uses largeness. It names   *)
(* the construction of the proof, the union of 100 permutations between the   *)
(* two sides, where the TeX states the existence of a bipartite 100-regular   *)
(* multigraph. And since beta d = 1, the expansion inequality is an           *)
(* inequality of natural numbers. Connectivity, the last sentence of the      *)
(* lemma, is perm_cut_eq0: a set with an empty cut is empty or the whole      *)
(* vertex set.                                                                *)
(*                                                                            *)
(* The proof counts the tuples of permutations, among the (l!)^100, that fail *)
(* at some W, with crude constants in place of the entropy bound of the TeX,  *)
(* in nat, with no real type and no large numeral computed. A failure at W    *)
(* gives a failure at a set of size w <= l (by complement). For such a set,   *)
(* with a and b the sizes of its sides, a failure forces 100 |a - b| < w,     *)
(* hence 20 b <= 11 w and 45 w <= 100 a + 1, and at most w - 1 exceptional    *)
(* labels from the left side of W to the outside of the right side            *)
(* (perm_cut_fail_card). Counting the tuples permutation by permutation, the  *)
(* failures at W number at most w C(100 w, w) (11 w / (20 l))^(44 w) (l!)^100 *)
(* (expander_fail_set); the factor (w / l)^(44 w) is kept through the union   *)
(* over the C(2 l, w) sets of size w, and with C(n, w) w^w <= 4^w n^w (e      *)
(* replaced by 4) the failures at size w number at most 2^-w (l!)^100         *)
(* (expander_fail_size), because 12800 (11/20)^44 <= 1 (expander_const,       *)
(* through 3 * 11^2 <= 20^2 and 12800 <= 3^22). The sum over w is below       *)
(* (l!)^100 (expander_fail_card). This is the crude chain of the audit of the *)
(* manuscript, with at most w - 1 exceptional labels and e replaced by 4. It  *)
(* follows no Lean module of the collection, which proves a weaker theorem by *)
(* another route and has no expander.                                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(* The cut of W in the bipartite multigraph on 'I_(l + l) of d permutations:
   the label (j, u) joins lshift l u to rshift l (s j u). *)
Definition perm_cut (d l : nat) (s : 'I_d -> {perm 'I_l})
    (W : {set 'I_(l + l)}) : {set 'I_d * 'I_l} :=
  [set e | (lshift l e.2 \in W) != (rshift l (s e.1 e.2) \in W)].

Section transitive.
Variable n : nat.

(* The permutations of 'I_n act transitively on the sets of a given size. *)
Lemma perm_imset_eq (S T : {set 'I_n}) : #|S| = #|T| ->
  exists rho : {perm 'I_n}, rho @: S = T.
Proof.
move=> eST.
(* The number of entries of the indicator of X on which a holds depends
   only on #|X|. *)
have cnt (X : {set 'I_n}) (a : pred bool) :
    count a [seq i \in X | i <- enum 'I_n] =
    if a true then (if a false then n else #|X|)
    else (if a false then n - #|X| else 0).
  rewrite count_map.
  have -> : count (preim (mem X) a) (enum 'I_n) =
      count (fun i => if i \in X then a true else a false) (enum 'I_n).
    by apply: eq_count => i /=; case: (i \in X).
  case: (a true); case: (a false).
  - by rewrite (eq_count (a2 := predT)) ?count_predT ?size_enum_ord // => i;
      case: ifP.
  - have -> : count (fun i : 'I_n => if i \in X then true else false)
        (enum 'I_n) = count (mem X) (enum 'I_n).
      by apply: eq_count => i /=; case: (i \in X).
    by rewrite cardE enumT -size_filter.
  - have -> : count (fun i : 'I_n => if i \in X then false else true)
        (enum 'I_n) = count (mem (~: X)) (enum 'I_n).
      by apply: eq_count => i /=; rewrite inE; case: (i \in X).
    have <- : #|~: X| = n - #|X| by rewrite cardsCs setCK card_ord.
    by rewrite cardE enumT -size_filter.
  - by rewrite (@eq_count _ _ pred0) ?count_pred0 // => i /=; case: (i \in X).
(* The indicators of S and T are permutations of each other. *)
pose tS : n.-tuple bool := [tuple (i \in S) | i < n].
have vS : val tS = [seq i \in S | i <- enum 'I_n] by [].
have pe : perm_eq [seq i \in T | i <- enum 'I_n] tS.
  by apply/seq.permP => a; rewrite vS !cnt eST.
case/tuple_permP: pe => p hp.
have hpi i : (i \in T) = (p i \in S).
  have := congr1 (fun s => nth false s i) hp.
  rewrite /= (nth_map i) ?size_enum_ord ?ltn_ord // nth_ord_enum.
  by rewrite (nth_map i) ?size_enum_ord ?ltn_ord // nth_ord_enum tnth_mktuple.
exists p^-1%g; apply/setP => i.
by rewrite hpi -[i in LHS](permK p) mem_imset //; exact: perm_inj.
Qed.

(* All the sets tau @: S of a given size have fibers of the same size. *)
Lemma perm_fiber_card (S T1 T2 : {set 'I_n}) : #|T1| = #|T2| ->
  #|[set tau : {perm 'I_n} | tau @: S == T1]| =
  #|[set tau : {perm 'I_n} | tau @: S == T2]|.
Proof.
have le (X Y : {set 'I_n}) : #|X| = #|Y| ->
    #|[set tau : {perm 'I_n} | tau @: S == X]| <=
    #|[set tau : {perm 'I_n} | tau @: S == Y]|.
  move=> eXY; have [rho hr] := perm_imset_eq eXY.
  rewrite -(card_imset _ (mulIg rho)); apply: subset_leq_card.
  apply/subsetP => sig /imsetP[tau]; rewrite !inE => /eqP htau ->.
  apply/eqP; rewrite -hr -htau -imset_comp; apply: eq_imset => x.
  by rewrite /= permM.
by move=> e; apply/eqP; rewrite eqn_leq !le.
Qed.

(* The permutations that map S into B, counted through the fibers of
   tau |-> tau @: S. *)
Lemma perm_into_card (S B : {set 'I_n}) :
  #|[set tau : {perm 'I_n} | tau @: S \subset B]| * 'C(n, #|S|) =
  'C(#|B|, #|S|) * n`!.
Proof.
set k := #|S|.
pose f := #|[set tau : {perm 'I_n} | tau @: S == S]|.
have fib (T : {set 'I_n}) :
    #|T| = k -> #|[set tau : {perm 'I_n} | tau @: S == T]| = f.
  by move=> h; apply: perm_fiber_card; rewrite h.
have szS (tau : {perm 'I_n}) : #|tau @: S| = k.
  by rewrite card_imset //; exact: perm_inj.
(* Count the permutations by the image of S. *)
have part (P : pred {set 'I_n}) :
    #|[set tau : {perm 'I_n} | P (tau @: S)]| =
    #|[set T : {set 'I_n} | P T & #|T| == k]| * f.
  rewrite -sum1_card (partition_big (fun tau : {perm 'I_n} => tau @: S)
    (fun T => P T && (#|T| == k))) /=; last first.
  - rewrite -sum_nat_const; apply: eq_big => [T|T /andP[PT /eqP hT]].
      by rewrite inE.
    rewrite -(fib T hT) -sum1_card; apply: eq_bigl => tau; rewrite !inE.
    by apply/andP/idP => [[]//|/[dup] /eqP-> ->].
  - by move=> tau; rewrite inE szS eqxx andbT.
have e1 : #|[set tau : {perm 'I_n} | predT (tau @: S)]| = n`!.
  by rewrite -card_Sn; apply: eq_card => tau; rewrite inE.
have e2 : #|[set T : {set 'I_n} | predT T & #|T| == k]| = 'C(n, k).
  rewrite -[n in RHS](card_ord n) -card_draws.
  by apply: eq_card => T; rewrite !inE.
have hT := part predT; rewrite e1 e2 in hT.
rewrite (part (fun T => T \subset B)) cards_draws hT.
by rewrite -mulnA [f * _]mulnC.
Qed.

End transitive.

(* (b / l)^x decreases in x, in the form used for counting. *)
Lemma leq_pow_ratio c X b l K M : 0 < l -> b <= l -> K <= M ->
  c * l ^ M <= b ^ M * X -> c * l ^ K <= b ^ K * X.
Proof.
move=> l0 bl /subnKC <-; set r := M - K; rewrite !expnD => h.
rewrite -(@leq_pmul2r (l ^ r)) ?expn_gt0 ?l0 //.
apply: leq_trans (_ : b ^ K * b ^ r * X <= _).
  by rewrite -mulnA; apply: leq_trans h; rewrite mulnA.
rewrite mulnAC leq_mul2l; apply/orP; right.
by elim: r {h} => // r IH; rewrite !expnS leq_mul.
Qed.


Section cut.
Variables (d l : nat) (s : 'I_d -> {perm 'I_l}).
Implicit Types W : {set 'I_(l + l)}.

(* The two sides of a vertex set. *)
Definition lside W := [set u : 'I_l | lshift l u \in W].
Definition rside W := [set v : 'I_l | rshift l v \in W].

(* The cut does not change under complement. *)
Lemma perm_cutC W : perm_cut s (~: W) = perm_cut s W.
Proof.
by apply/setP => e; rewrite !inE; case: (_ \in W); case: (_ \in W).
Qed.

(* |W| = a + b, with a and b the sizes of its two sides. *)
Lemma card_sides W : #|W| = #|lside W| + #|rside W|.
Proof.
rewrite -!sum1_card big_mkcond /= big_split_ord /=.
by congr (_ + _); rewrite [RHS]big_mkcond /=; apply: eq_bigr => i _;
  rewrite inE.
Qed.

(* #{(j, u) : s j u in B} = d |B|: every right vertex has degree d. *)
Lemma card_perm_preim (B : {set 'I_l}) :
  #|[set e : 'I_d * 'I_l | s e.1 e.2 \in B]| = d * #|B|.
Proof.
pose F j u := if s j u \in B then 1 else 0.
transitivity (\sum_(e : 'I_d * 'I_l) F e.1 e.2).
  by rewrite -sum1_card big_mkcond /=; apply: eq_bigr => e _; rewrite inE.
rewrite -(pair_bigA _ F) /= -[d in RHS](card_ord d) -sum_nat_const.
apply: eq_bigr => j _; rewrite -sum1_card [RHS]big_mkcond /=.
by rewrite [RHS](reindex_inj (@perm_inj _ (s j))).
Qed.

(* Degree counting: d |a - b| <= |perm_cut s W|, in nat. *)
Lemma perm_cut_ge W :
  d * (#|lside W| - #|rside W|) <= #|perm_cut s W| /\
  d * (#|rside W| - #|lside W|) <= #|perm_cut s W|.
Proof.
set A := lside W; set B := rside W.
pose D := setX [set: 'I_d] A.
pose P := [set e : 'I_d * 'I_l | s e.1 e.2 \in B].
have cD : #|D| = d * #|A| by rewrite cardsX cardsT card_ord.
have cP : #|P| = d * #|B| by exact: card_perm_preim.
(* The labels from A to the complement of B, and the labels from the
   complement of A to B, are in the cut. *)
have s1 : D :\: P \subset perm_cut s W.
  apply/subsetP => -[j u]; rewrite !inE /= => /andP[hP hA].
  by rewrite hA (negbTE hP).
have s2 : P :\: D \subset perm_cut s W.
  apply/subsetP => -[j u]; rewrite !inE /= => /andP[hD hB].
  by rewrite hB (negbTE hD).
split.
- apply: leq_trans (subset_leq_card s1); rewrite cardsD mulnBr -cD -cP.
  by apply: leq_sub2l; apply: subset_leq_card; apply: subsetIr.
- apply: leq_trans (subset_leq_card s2); rewrite cardsD mulnBr -cD -cP.
  by apply: leq_sub2l; apply: subset_leq_card; apply: subsetIr.
Qed.


(* Connectivity: under the expansion inequality at W, an empty cut has a
   trivial side. *)
Lemma perm_cut_eq0 W : minn #|W| (l + l - #|W|) <= #|perm_cut s W| ->
  perm_cut s W = set0 -> W = set0 \/ W = setT.
Proof.
move=> h c0; move: h; rewrite c0 cards0 leqn0.
case: (leqP #|W| (l + l - #|W|)) => hm.
  by rewrite cards_eq0 => /eqP ->; left.
move=> h; right.
have : #|~: W| == 0 by rewrite cardsCs setCK card_ord h.
by rewrite cards_eq0 => /eqP hc; rewrite -[W]setCK hc setC0.
Qed.

End cut.

Section count.
Variables (d l : nat).
Local Notation tuples := {ffun 'I_d -> {perm 'I_l}}.

(* With bin_mul_pow: the fraction of the permutations of 'I_l that map S
   into B is at most (|B| / l)^|S|. *)
Lemma perm_into_bound (S B : {set 'I_l}) :
  #|[set tau : {perm 'I_l} | tau @: S \subset B]| * l ^ #|S| <=
  #|B| ^ #|S| * l`!.
Proof.
have kl : #|S| <= l by apply: leq_trans (max_card _) _; rewrite card_ord.
have bl : #|B| <= l by apply: leq_trans (max_card _) _; rewrite card_ord.
rewrite -(@leq_pmul2r 'C(l, #|S|)) ?bin_gt0 //.
rewrite mulnAC perm_into_card mulnAC [X in _ <= X]mulnAC.
by rewrite [_ ^ _ * 'C(_, _)]mulnC leq_mul2r bin_mul_pow ?orbT.
Qed.

(* The tuples of d permutations that fail at W, with a and b the sizes of
   the sides of W: they have fewer than |W| exceptional labels, from the
   left side of W to the outside of its right side, and each set E of
   exceptional labels leaves at least K labels that must map into the right
   side. *)
Lemma perm_cut_fail_card (W : {set 'I_(l + l)}) K : 0 < l ->
  K + #|W| <= d * #|lside W| + 1 ->
  #|[set f : tuples | #|perm_cut f W| < #|W|]| * l ^ K <=
  #|[set E : {set 'I_d * 'I_l} |
      E \subset setX [set: 'I_d] (lside W) & #|E| < #|W|]| *
  (#|rside W| ^ K * l`! ^ d).
Proof.
move=> l0 hK.
set A := lside W; set B := rside W; set w := #|W|.
set D := setX [set: 'I_d] A.
set Es := [set E : {set 'I_d * 'I_l} | E \subset D & #|E| < w].
(* The exceptional labels of f: from A to the complement of B. *)
pose Ef (f : tuples) := [set e in D | f e.1 e.2 \notin B].
pose G (E : {set 'I_d * 'I_l}) :=
  [set f : tuples | [forall e in D :\: E, f e.1 e.2 \in B]].
have bl : #|B| <= l by apply: leq_trans (max_card _) _; rewrite card_ord.
(* A failure at W lies in G E for its set E of exceptional labels. *)
have h1 : #|[set f : tuples | #|perm_cut f W| < w]| <= \sum_(E in Es) #|G E|.
  rewrite -sum1_card (partition_big Ef (mem Es)) /=.
    move=> f; rewrite !inE => hf; apply/andP; split.
      by apply/subsetP => e; rewrite inE => /andP[].
    apply: leq_ltn_trans hf; apply: subset_leq_card; apply/subsetP => -[j u].
    by rewrite !inE /=; case/andP => hu hb; rewrite hu (negbTE hb).
  apply: leq_sum => E _; rewrite sum1dep_card; apply: subset_leq_card.
  apply/subsetP => f; rewrite !inE => /andP[_ /eqP <-].
  apply/forall_inP => e; rewrite !inE => /andP[he hD].
  by move: he; rewrite hD /= negbK.
(* The count of G E, coordinate by coordinate. *)
have hG E : E \in Es -> #|G E| * l ^ K <= #|B| ^ K * l`! ^ d.
  rewrite inE => /andP[ED Ew].
  pose Sj (j : 'I_d) := [set u in A | (j, u) \notin E].
  pose Pj (j : 'I_d) := [set tau : {perm 'I_l} | tau @: Sj j \subset B].
  have famG : #|G E| = \prod_(j < d) #|Pj j|.
    have -> : #|G E| = #|(family (fun j => mem (Pj j)) : simpl_pred tuples)|.
      apply: eq_card => f; rewrite inE.
      apply/forall_inP/familyP => [h j | h [j u] he].
      - rewrite inE; apply/subsetP => _ /imsetP[u hu ->]; apply: (h (j, u)).
        by move: hu; rewrite !inE /= => /andP[hA hE]; rewrite hE hA.
      - have := h j; rewrite inE => /subsetP; apply; apply: imset_f.
        by move: he; rewrite !inE /= => /andP[hE hA]; rewrite hA hE.
    by rewrite card_family foldrE big_map big_enum.
  have sumS : \sum_(j < d) #|Sj j| = #|D :\: E|.
    pose F j u := if (j, u) \in D :\: E then 1 else 0.
    transitivity (\sum_(e : 'I_d * 'I_l) F e.1 e.2); last first.
      by rewrite -sum1_card [RHS]big_mkcond /=; apply: eq_bigr => -[j u] _.
    rewrite -(pair_bigA _ F) /=; apply: eq_bigr => j _.
    rewrite -sum1_card [LHS]big_mkcond /=; apply: eq_bigr => u _.
    by rewrite /F !inE /= andbC.
  have KS : K <= #|D :\: E|.
    rewrite cardsD (setIidPr ED) cardsX cardsT card_ord.
    have h2 : #|E| + K < d * #|A| + 1.
      by apply: leq_trans hK; rewrite addnC ltn_add2l.
    rewrite addn1 ltnS in h2.
    by rewrite leq_subRL // (leq_trans (leq_addr K _) h2).
  apply: (@leq_pow_ratio _ _ _ _ K (#|D :\: E|) l0 bl KS).
  rewrite famG -sumS !expn_sum -[d in l`! ^ d](card_ord d) -prod_nat_const.
  by rewrite -!big_split /=; apply: leq_prod => j _; exact: perm_into_bound.
apply: leq_trans (leq_mul h1 (leqnn _)) _.
by rewrite big_distrl /= -sum_nat_const; exact: leq_sum.
Qed.

End count.

(* The power with a fixed exponent is monotone, with no condition on e. *)
Lemma leq_pow2r m n e : m <= n -> m ^ e <= n ^ e.
Proof. by move=> mn; elim: e => // e IH; rewrite !expnS leq_mul. Qed.

(* The constant of the union bound: (4 2) 2 (4 100) 2 (11^2)^22 <= (20^2)^22,
   with small numerals only. *)
Lemma expander_const :
  4 * 2 * 2 * (4 * 100) * 2 * (11 ^ 2) ^ 22 <= (20 ^ 2) ^ 22.
Proof.
apply: (@leq_trans (3 ^ 22 * (11 ^ 2) ^ 22)).
  rewrite leq_mul2r; apply/orP; right.
  apply: (@leq_trans (3 ^ 2 * 3 * 3 ^ 6 * 3)).
    by apply: leq_mul => //; apply: leq_mul => //; apply: leq_mul.
  by rewrite -expnSr -expnD -expnSr leq_pexp2l.
by rewrite -expnMn; apply: leq_pow2r.
Qed.

(* All the sets of size w together, for 0 < w <= l, with K = 44 w. *)
Lemma expander_size_bound l w : 0 < w -> w <= l ->
  'C(l + l, w) * (w * 'C(100 * w, w)) * (11 * w) ^ (2 * (22 * w)) * 2 ^ w <=
  l ^ (2 * (22 * w)) * 20 ^ (2 * (22 * w)).
Proof.
move=> w0 wl; set K := 2 * (22 * w).
have wK : w <= K by rewrite /K mulnA leq_pmull.
have h1 : 'C(l + l, w) * w ^ w <= (4 * 2) ^ w * l ^ w.
  by rewrite expnMn -mulnA -expnMn mul2n -addnn; exact: bin_expnn_le.
have h2 : 'C(100 * w, w) <= (4 * 100) ^ w.
  have := bin_expnn_le (100 * w) w.
  rewrite expnMn [X in _ <= X]mulnA -expnMn leq_mul2r => /orP[|//].
  by rewrite expn_eq0 eqn0Ngt w0.
have h3 : w <= 2 ^ w by apply: ltnW; apply: ltn_expl.
have h4 : w ^ K <= w ^ w * l ^ (K - w).
  by rewrite -{1}(subnKC wK) expnD leq_mul2l leq_pow2r ?orbT.
rewrite expnMn.
apply: (@leq_trans ('C(l + l, w) * (2 ^ w * (4 * 100) ^ w) *
  (11 ^ K * (w ^ w * l ^ (K - w))) * 2 ^ w)).
  apply: leq_mul (leqnn _); apply: leq_mul.
    exact: leq_mul (leqnn _) (leq_mul h3 h2).
  exact: leq_mul (leqnn _) h4.
have -> : 'C(l + l, w) * (2 ^ w * (4 * 100) ^ w) *
    (11 ^ K * (w ^ w * l ^ (K - w))) * 2 ^ w =
    ('C(l + l, w) * w ^ w) * (2 ^ w * (4 * 100) ^ w * 2 ^ w) *
    (11 ^ K * l ^ (K - w)) by ring.
apply: (@leq_trans ((4 * 2) ^ w * l ^ w * (2 ^ w * (4 * 100) ^ w * 2 ^ w) *
  (11 ^ K * l ^ (K - w)))).
  by rewrite !leq_mul2r h1 !orbT.
have -> : (4 * 2) ^ w * l ^ w * (2 ^ w * (4 * 100) ^ w * 2 ^ w) *
    (11 ^ K * l ^ (K - w)) =
    ((4 * 2) ^ w * 2 ^ w * (4 * 100) ^ w * 2 ^ w * 11 ^ K) *
    (l ^ w * l ^ (K - w)) by ring.
rewrite -expnD subnKC // mulnC leq_mul2l; apply/orP; right.
rewrite -!expnMn /K !expnM -expnMn.
by apply: leq_pow2r; exact: expander_const.
Qed.

(* The union bound for cardinals. *)

Lemma card_exists_le (I T : finType) (J : {pred I}) (P : I -> {pred T}) :
  #|[set x | [exists i in J, x \in P i]]| <= \sum_(i in J) #|P i|.
Proof.
have -> : \sum_(i in J) #|P i| =
    \sum_x \sum_(i in J) (if x \in P i then 1 else 0).
  rewrite exchange_big /=; apply: eq_bigr => i _.
  by rewrite -sum1_card big_mkcond.
rewrite -sum1_card big_mkcond /=; apply: leq_sum => x _; rewrite inE.
case: existsP => [[i /andP[iJ xi]]|_] //.
by rewrite (bigD1 i) //= xi.
Qed.


(* sum_(1 <= w <= m) 2^(m - w) = 2^m - 1. *)
Lemma sum_pow2_pos m : 0 < m -> \sum_(w < m.+1 | 0 < w) 2 ^ (m - w) < 2 ^ m.
Proof.
case: m => // m _; rewrite big_mkcond big_ord_recl /= add0n.
have -> : \sum_(i < m.+1) (if 0 < bump 0 i then 2 ^ (m.+1 - bump 0 i) else 0) =
    \sum_(i < m.+1) 2 ^ (m - i).
  by apply: eq_bigr => i _; rewrite /bump /= add1n subSS.
exact: sum_pow2_rev.
Qed.


Section expander.
Variable l : nat.
Local Notation tuples := {ffun 'I_100 -> {perm 'I_l}}.

(* The sets of fewer than w labels in a set of at most 100 w labels. *)
Lemma small_sets_card (D : {set 'I_100 * 'I_l}) w : #|D| <= 100 * w ->
  #|[set E : {set 'I_100 * 'I_l} | E \subset D & #|E| < w]| <=
  w * 'C(100 * w, w).
Proof.
move=> Dw.
apply: (@leq_trans #|[set E : {set 'I_100 * 'I_l} |
    [exists m in [pred m : 'I_w | true],
      E \in [set E : {set 'I_100 * 'I_l} | E \subset D & #|E| == m]]]|).
  apply: subset_leq_card; apply/subsetP => E; rewrite !inE => /andP[ED Ew].
  by apply/existsP; exists (Ordinal Ew); rewrite !inE ED eqxx.
apply: leq_trans (card_exists_le _ _) _.
rewrite -[w in X in _ <= X * _](card_ord w) -sum_nat_const.
apply: leq_sum => m _; rewrite cards_draws.
apply: leq_trans (leq_bin2l _ Dw) _.
have mw : m <= w by apply: ltnW.
have := @bin_half_mono (100 * w) m (w - m); rewrite subnKC //; apply.
by rewrite geq_half_double -mul2n leq_mul2r orbT.
Qed.


(* One set W of size w: either no tuple fails at W, or W is balanced and
   the failures number at most w C(100 w, w) (11 w / (20 l))^K (l!)^100. *)
Lemma expander_fail_set (W : {set 'I_(l + l)}) w : 0 < l -> #|W| = w ->
  #|[set f : tuples | #|perm_cut f W| < #|W|]| *
    (l ^ (2 * (22 * w)) * 20 ^ (2 * (22 * w))) <=
  w * 'C(100 * w, w) * (11 * w) ^ (2 * (22 * w)) * l`! ^ 100.
Proof.
move=> l0 Ww; set K := 2 * (22 * w).
case: (boolP [exists f : tuples, #|perm_cut f W| < #|W|]) =>
    [/existsP[f hf]|hn]; last first.
  rewrite (_ : #|_| = 0) //; apply/eqP; rewrite cards_eq0; apply/eqP.
  apply/setP => f; rewrite !inE; apply/negbTE.
  by move: hn; rewrite negb_exists => /forallP; apply.
set a := #|lside W|; set b := #|rside W|.
have [ca cb] := perm_cut_ge f W.
have sw : w = a + b by rewrite -Ww card_sides.
rewrite mulnBr leq_subLR in ca; rewrite mulnBr leq_subLR in cb.
rewrite Ww -addn1 in hf; move: ca cb hf; set c := #|perm_cut f W| => ca cb hf.
have hK : K + #|W| <= 100 * a + 1.
  rewrite Ww /K; move: ca cb hf; rewrite sw -!(ler_nat rat) ?natrD ?natrM.
  by lra.
have h20 : 20 * b <= 11 * w.
  move: ca cb hf; rewrite sw -!(ler_nat rat) ?natrD ?natrM.
  by lra.
have hb := @perm_cut_fail_card 100 l W K l0 hK.
have hE : #|[set E : {set 'I_100 * 'I_l} |
    E \subset setX [set: 'I_100] (lside W) & #|E| < #|W|]| <=
    w * 'C(100 * w, w).
  rewrite Ww; apply: small_sets_card.
  by rewrite cardsX cardsT card_ord leq_mul2l sw leq_addr orbT.
rewrite mulnA; apply: leq_trans (leq_mul hb (leqnn _)) _.
set Es := #|[set E : {set 'I_100 * 'I_l} | _ & _]| in hb hE *.
have -> : Es * (b ^ K * l`! ^ 100) * 20 ^ K = Es * (20 * b) ^ K * l`! ^ 100.
  by rewrite expnMn; ring.
apply: leq_mul (leq_mul hE _) (leqnn _).
exact: leq_pow2r.
Qed.


(* All the sets of size w together. *)
Lemma expander_fail_size w : 0 < l -> 0 < w -> w <= l ->
  #|[set f : tuples | [exists W in [set W : {set 'I_(l + l)} | #|W| == w],
      f \in [set f : tuples | #|perm_cut f W| < #|W|]]]| * 2 ^ w <=
  l`! ^ 100.
Proof.
move=> l0 w0 wl; set K := 2 * (22 * w).
set S := [set W : {set 'I_(l + l)} | #|W| == w].
pose bw W := #|[set f : tuples | #|perm_cut f W| < #|W|]|.
pose c := w * 'C(100 * w, w) * (11 * w) ^ K * l`! ^ 100.
have pos : 0 < l ^ K * 20 ^ K by rewrite muln_gt0 !expn_gt0 l0.
rewrite -(leq_pmul2r pos).
apply: (@leq_trans ((\sum_(W in S) bw W) * 2 ^ w * (l ^ K * 20 ^ K))).
  by rewrite !leq_mul2r card_exists_le !orbT.
apply: (@leq_trans ((\sum_(W in S) c) * 2 ^ w)).
  rewrite mulnAC big_distrl /= leq_mul2r; apply/orP; right.
  by apply: leq_sum => W; rewrite inE => /eqP Ww; exact: expander_fail_set.
rewrite sum_nat_const card_draws card_ord /c.
have -> : 'C(l + l, w) * (w * 'C(100 * w, w) * (11 * w) ^ K * l`! ^ 100) *
    2 ^ w =
    ('C(l + l, w) * (w * 'C(100 * w, w)) * (11 * w) ^ K * 2 ^ w) * l`! ^ 100.
  by ring.
by rewrite mulnC leq_mul2l expander_size_bound ?orbT.
Qed.


(* Fewer than (l!)^100 tuples fail at some set W. *)
Lemma expander_fail_card : 0 < l ->
  #|[set f : tuples | [exists W : {set 'I_(l + l)},
      #|perm_cut f W| < minn #|W| (l + l - #|W|)]]| < l`! ^ 100.
Proof.
move=> l0; set F := l`! ^ 100.
pose B (w : 'I_l.+1) := [set f : tuples |
  [exists W in [set W : {set 'I_(l + l)} | #|W| == w],
    f \in [set f : tuples | #|perm_cut f W| < #|W|]]].
(* A failure gives a failure at a set of size at most l. *)
have sub : [set f : tuples | [exists W : {set 'I_(l + l)},
    #|perm_cut f W| < minn #|W| (l + l - #|W|)]] \subset
    [set f | [exists w in [pred w : 'I_l.+1 | 0 < w], f \in B w]].
  apply/subsetP => f; rewrite !inE => /existsP[W0 hW0].
  have cW0 : #|W0| <= l + l.
    by apply: leq_trans (max_card _) _; rewrite card_ord.
  have [W [Wl hW]] : exists W : {set 'I_(l + l)},
      #|W| <= l /\ #|perm_cut f W| < #|W|.
    case: (leqP #|W0| l) => h.
    - exists W0; split => //; apply: leq_trans hW0 _.
      by rewrite geq_minl.
    - exists (~: W0); have cC : #|~: W0| = l + l - #|W0|.
        by rewrite cardsCs setCK card_ord.
      split; first by rewrite cC leq_subLR leq_add2r ltnW.
      by rewrite perm_cutC cC; apply: leq_trans hW0 (geq_minr _ _).
  have Wl' : #|W| < l.+1 by rewrite ltnS.
  apply/existsP; exists (Ordinal Wl'); rewrite !inE /=.
  apply/andP; split; first exact: leq_ltn_trans (leq0n _) hW.
  by apply/existsP; exists W; rewrite !inE eqxx.
apply: leq_ltn_trans (subset_leq_card sub) _.
apply: leq_ltn_trans (card_exists_le _ _) _.
(* The sizes together: a geometric sum. *)
have hB (w : 'I_l.+1) : 0 < w -> #|B w| * 2 ^ w <= F.
  by move=> w0; apply: expander_fail_size; rewrite // -ltnS.
rewrite -(ltn_pmul2r (expn_gt0 2 l)) big_distrl /=.
apply: (@leq_ltn_trans (\sum_(w in [pred w : 'I_l.+1 | 0 < w])
  F * 2 ^ (l - w))).
  apply: leq_sum => w w0.
  have e : 2 ^ l = 2 ^ w * 2 ^ (l - w) by rewrite -expnD subnKC // -ltnS.
  by rewrite e mulnA leq_mul2r hB ?orbT.
rewrite -big_distrr /= ltn_pmul2l ?expn_gt0 ?fact_gt0 //.
exact: sum_pow2_pos.
Qed.

(* The expander lemma: some tuple fails at no set W. *)
Lemma expander : 0 < l -> exists s : 'I_100 -> {perm 'I_l},
  forall W : {set 'I_(l + l)}, minn #|W| (l + l - #|W|) <= #|perm_cut s W|.
Proof.
move=> l0; have hc := expander_fail_card l0.
set bad := [set f : tuples | _] in hc.
case: (pickP [pred f : tuples | f \notin bad]) => [f /= hf | hall].
  exists f => W; move: hf; rewrite inE negb_exists => /forallP /(_ W).
  by rewrite -leqNgt.
have : [set: tuples] \subset bad.
  by apply/subsetP => f _; have := hall f; rewrite /= => /negbFE.
move/subset_leq_card; rewrite cardsT card_ffun card_ord card_Sn => h.
by have := leq_ltn_trans h hc; rewrite ltnn.
Qed.

End expander.

(* An example: for every l >= 1, some 100 permutations of 'I_l give a
   connected bipartite multigraph on 2 l vertices. *)
Example expander_connected l : 0 < l -> exists s : 'I_100 -> {perm 'I_l},
  forall W : {set 'I_(l + l)}, perm_cut s W = set0 -> W = set0 \/ W = setT.
Proof.
by move=> l0; have [s hs] := expander l0; exists s => W; apply: perm_cut_eq0.
Qed.
