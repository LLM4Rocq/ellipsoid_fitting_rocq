From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import zmodp.
From mathcomp Require Import matrix sesquilinear reals exp.
From GaussianAnalysis.fourier Require Import boolean_fourier product_smoothing.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.matrix Require Import real_spectral psd_part multiplicity.
From GaussianApplications Require Import PsdRank.Model PsdRank.CellBounds.

(**md**************************************************************************)
(* # PSD rank of shifted matching matrices: averaging within a cell           *)
(*                                                                            *)
(* The lemma 'Local averaging' of 'Exponential PSD rank of positively shifted *)
(* matching matrices' (family 126 of the OpenAI math collection, revision     *)
(* 1581d4cbd, source/sections/local-averaging.tex, lines 12-247), on the      *)
(* frame of the cells of Model.v (local data m : {perm 'I_k}, terminal j at m *)
(* j, internal pair q at m (a + 1 + 2q) and m (a + 2 + 2q), full bits         *)
(* cell_bit b y). A Rocq formalization of the credited argument, with the     *)
(* audit reviews/phase13-psd-audit/trace.md. It follows no Lean module of the *)
(* collection; the multiplicity step that it uses, in                         *)
(* library/matrix/multiplicity.v, follows two:                                *)
(* Lean: Involutions.lean, SpectralMultiplicity.lean                          *)
(*                                                                            *)
(* The laws of a cell of size k with a free bits, d = a + 1:                  *)
(* - cell_mu R b: the uniform law on the w(b)-subsets of 'I_k (w =            *)
(*   cell_weight k b);                                                        *)
(* - cell_nu R: the uniform law on the local data m : {perm 'I_k};            *)
(* - cell_pi R b m y: the uniform law on the support of the restrictions, the *)
(*   sets x with cell_support b m y x; cell_count k b y is the size of the    *)
(*   support of the identity layout, which every support has.                 *)
(*                                                                            *)
(* Main results:                                                              *)
(* - local_averaging: for a odd there are k0 = 13 (a + 1) and                 *)
(*   theta : nat -> R, theta >= 0 with theta k -> 0 along the even k (in      *)
(*   epsilon form), such that for every even k with 6 <= k, 2 (a + 1) <= k    *)
(*   and k0 <= k and both charges b, cell_hyps a k b (theta k) holds: the     *)
(*   three laws are probability vectors, the channels average to cell_mu      *)
(*   under cell_nu, and E_m (E_(pi^m) g - E_mu g)^2 <= theta k E_mu g^2 for   *)
(*   every real g; and 0 < cell_pi R b m y x implies cell_support b m y x.    *)
(*   One may take theta k = sqrt (8 sqrt (cell_cmass d) (1 + ln (h + 1)) /    *)
(*   sqrt (h + 1)), h = (k - d) / 2, that is O_d (k^(-1/4) sqrt (log k)) as   *)
(*   in the manuscript.                                                       *)
(* - cell_pi_gt0: for 2 (a + 1) <= k, 0 < cell_pi R b m y x exactly when      *)
(*   cell_support b m y x.                                                    *)
(* - cell_marginal, cell_mu_prob, cell_nu_prob, cell_pi_prob, cell_count_eq   *)
(*   (cell_count = C(h, g) > 0 with g = (w - s) / 2, s the number of          *)
(*   1-terminals), cell_support_perm (the support of m is the image under m   *)
(*   of the support of the identity layout).                                  *)
(*                                                                            *)
(* The arithmetic estimates of the trace are central_ratio, pair_sum_bound    *)
(* and root_ln_lim of CellBounds.v (item A2b): C(2n, w)^2 <= 16^(n - h) 4     *)
(* 16^(T + 1) (h + 1) C(h, g)^4 near the center; the sum of the trace formula *)
(* below is at most 8 (1 + ln (h + 1)); C (1 + ln n) / sqrt n tends to 0.     *)
(*                                                                            *)
(* The proof. The support of the identity layout is the image of the          *)
(* g-subsets of the h internal pairs (xG), so it has C(h, g) points, and g <= *)
(* h exactly when 2 d <= k (the audit's threshold). The marginal follows from *)
(* the invariance of the law of the hits and the transitivity of the          *)
(* permutations on pairs of sets with the same sizes and intersection size    *)
(* (perm_two_sets, by perm_map_uniq). The kernel K = N E_m [pi^m pi^m^T] on   *)
(* the w-subsets (indexed as ksubset k w of multiplicity.v, N = C(k, w)) is   *)
(* positive semidefinite, K 1 = 1, and K commutes with ksubset_mx w s, the    *)
(* perm_mx of the permutation that s induces; trace_multiplicity and          *)
(* ksubset_multiplicity give (x^T K x)^2 <= (tr K^2 - 1) / (k / 2) |x|^4 for  *)
(* x orthogonal to 1, hence the contraction. The trace of K^2 is computed     *)
(* exactly by the classes of intersection size of each row: K is constant on  *)
(* each class (perm_two_sets), the class sums are hypc c / C(h, g) (the count *)
(* of the points of a support that meet one of them in c points), the classes *)
(* have C(w, c) C(k - w, w - c) points (card_meet_sets), and only the classes *)
(* c = s + 2 i, i <= g, are charged: tr K^2 = C(k, w) / C(h, g)^2 sum_(i <=   *)
(* g) (C(g, i) C(h - g, g - i))^2 / (C(w, s + 2 i) C(k - w, w - s - 2 i)),    *)
(* the formula (local:trace-formula), which the estimates bound by sqrt       *)
(* (cell_cmass d (h + 1)) 8 (1 + ln (h + 1)).                                 *)
(*                                                                            *)
(* Departures. Departure 2 of the plan: k is even, 6 <= k, 2 d <= k and theta *)
(* k -> 0 beside the symbolic threshold k0 = 13 d, where the manuscript has k *)
(* sufficiently large; k >= 13 d gives h >= 6 d, which the near-central       *)
(* binomial bound needs with T = d (the audit's T = ceil ((d + 2) / 4) is not *)
(* needed). The local data are permutations of 'I_k with the uniform law, not *)
(* ordered terminals with a perfect matching: every local datum is the image  *)
(* of the same number of permutations, so the laws are the same. The variance *)
(* bound is the scalar one with E_mu g^2 on the right, the form that          *)
(* smoothing_hyps of product_smoothing.v takes; the matrix form of the        *)
(* manuscript is not needed. The class constancy, implicit in the TeX         *)
(* (trace.md, point 4), is proved. The sum of the trace formula is bounded,   *)
(* in CellBounds.v, through a_j b_j <= (a_j^2 + b_j^2) / 2, not through the   *)
(* product of the two square-root bounds. The constants stay symbolic: no     *)
(* numeral is evaluated.                                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*         cell_mu R b == the uniform law of the w(b)-subsets of 'I_k         *)
(*           cell_nu R == the uniform law of the local data {perm 'I_k}       *)
(*    cell_count k b y == the size of the support of the identity layout      *)
(*  cell_pi R b m y x == the uniform law on the support of cell_support       *)
(* cell_hyps a k b th == the five conditions of smoothing_hyps for one cell   *)
(*      cell_theta a k == the contraction constant at k                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section cell_laws.
Variables (R : realType) (a k : nat).

(* The uniform law of the w(b)-subsets of 'I_k. *)
Definition cell_mu (b : 'F_2) (x : {set 'I_k}) : R :=
  (#|x| == cell_weight k b)%:R / ('C(k, cell_weight k b))%:R.

(* The uniform law of the local data. *)
Definition cell_nu (m : {perm 'I_k}) : R := (k`!)%:R^-1.

(* The number of points of the support for the identity layout. *)
Definition cell_count (b : 'F_2) (y : 'rV['F_2]_a) : nat :=
  #|[set x | cell_support b (1%g : {perm 'I_k}) y x]|.

(* The channel: the uniform law on the support of the restrictions. *)
Definition cell_pi (b : 'F_2) (m : {perm 'I_k}) (y : 'rV['F_2]_a)
    (x : {set 'I_k}) : R :=
  (cell_support b m y x)%:R / (cell_count b y)%:R.

End cell_laws.

(* The support for the local data m is the image under m of the support for
   the identity layout. *)
Local Lemma mem_imset_permV (T : Finite.type) (s : {perm T}) (x : {set T}) v :
  (v \in s^-1%g @: x) = (s v \in x).
Proof. by rewrite -{1}(permK s v) mem_imset //; exact: perm_inj. Qed.

Lemma cell_support_perm a k b (m : {perm 'I_k}) (y : 'rV['F_2]_a) x :
  cell_support b m y x = cell_support b 1%g y (m^-1%g @: x).
Proof.
rewrite /cell_support (card_imset _ (@perm_inj _ m^-1%g)).
congr [&& _, _ & _].
  apply: eq_forallb => j; apply: eq_forallb => v.
  by rewrite perm1 mem_imset_permV.
apply: eq_forallb => v; apply: eq_forallb => u.
by rewrite !perm1 !mem_imset_permV.
Qed.

(* The identity layout: the vertices v < d = a + 1 are the terminals, and
   the vertices d + 2q and d + 2q + 1 form the internal pair q < h. A subset
   satisfying the restrictions is the set of the 1-terminals and the union
   of a set G of internal pairs. *)
Section layout.
Variables (a k : nat) (b : 'F_2) (y : 'rV['F_2]_a).
Local Notation d := a.+1.
Local Notation h := (k - a.+1)./2.
Hypotheses (dk : (a.+1 <= k)%N) (ek : ~~ odd (k - a.+1)).

Local Lemma layout_k : (d + h.*2 = k)%N.
Proof. by rewrite halfK (negbTE ek) subn0 subnKC. Qed.

Local Lemma pu_lt (q : 'I_h) : ((d + q.*2).+1 < k)%N.
Proof.
rewrite -[X in (_ < X)%N]layout_k -addnS ltn_add2l.
by rewrite -doubleS leq_double.
Qed.

Local Lemma pv_lt (q : 'I_h) : (d + q.*2 < k)%N.
Proof. exact: ltnW (pu_lt q). Qed.

Local Definition pv (q : 'I_h) : 'I_k := Ordinal (pv_lt q).
Local Definition pu (q : 'I_h) : 'I_k := Ordinal (pu_lt q).

(* The vertex v >= d lies in the pair (v - d)/2. *)
Local Definition in_pairs (G : {set 'I_h}) (v : 'I_k) : bool :=
  [exists q in G, (v - d)./2 == q].

Local Lemma pidx_lt (v : 'I_k) : (d <= v)%N -> ((v - d)./2 < h)%N.
Proof.
move=> dv; rewrite ltn_half_double halfK (negbTE ek) subn0.
by rewrite ltn_sub2r // (leq_ltn_trans dv).
Qed.

(* The terminal bit of the vertex v: v < d and the full bit at v is 1. *)
Local Definition tbit (v : 'I_k) : bool :=
  [exists j : 'I_d, (val j == val v) && (cell_bit b y j != 0)].

Local Definition xG (G : {set 'I_h}) : {set 'I_k} :=
  [set v : 'I_k | if (v < d)%N then tbit v else in_pairs G v].

Local Definition tset : {set 'I_k} := [set v : 'I_k | (v < d)%N && tbit v].

Local Lemma pv_inj : injective pv.
Proof. by move=> q q' /(congr1 val) /= /addnI /double_inj /val_inj. Qed.

Local Lemma pu_inj : injective pu.
Proof. by move=> q q' /(congr1 val) [] /addnI /double_inj /val_inj. Qed.

Local Lemma xG_split G : xG G = tset :|: (pv @: G :|: pu @: G).
Proof.
apply/setP => v; rewrite !inE.
case: ltnP => vd /=.
  have -> : (v \in [set pv x | x in G]) = false.
    apply/negbTE/imsetP => -[q _ vq]; move: vd.
    by rewrite vq /= ltnNge leq_addr.
  have -> : (v \in [set pu x | x in G]) = false.
    apply/negbTE/imsetP => -[q _ vq]; move: vd.
    by rewrite vq /= ltnNge -addnS leq_addr.
  by rewrite !orbF.
apply/idP/idP.
  case/existsP => q /andP [qG /eqP e].
  have hv : val v = (d + (v - d))%N by rewrite subnKC.
  have := odd_double_half (v - d); rewrite e.
  case: (odd (v - d)) => /= hq; apply/orP; [right|left]; apply/imsetP;
    exists q => //; apply: val_inj; rewrite /= hv -hq ?addnS //.
case/orP => /imsetP [q qG ->]; apply/existsP; exists q; rewrite qG /=.
  by rewrite addKn doubleK.
by rewrite -addnS addKn /= uphalf_double.
Qed.

Local Lemma card_xG G : #|xG G| = (#|tset| + #|G|.*2)%N.
Proof.
have disj1 : [disjoint tset & [set pv x | x in G] :|: [set pu x | x in G]].
  rewrite -setI_eq0; apply/eqP/setP => v; rewrite !inE.
  apply/negbTE; rewrite negb_and -implybE; apply/implyP => /andP [vd _].
  apply/negP => /orP [] /imsetP [q _ vq];
    by move: vd; rewrite vq /= ltnNge ?leq_addr // -addnS leq_addr.
have disj2 : [disjoint [set pv x | x in G] & [set pu x | x in G]].
  rewrite -setI_eq0; apply/eqP/setP => v; rewrite !inE.
  apply/negbTE/negP => /andP [/imsetP [q _ ->] /imsetP [q' _ /(congr1 val) e]].
  by have := congr1 odd e; rewrite /= !oddD !odd_double; case: (odd a).
have cU (A B : {set 'I_k}) : [disjoint A & B] -> #|A :|: B| = (#|A| + #|B|)%N.
  by move=> dAB; apply/eqP; rewrite (leq_card_setU A B).2.
rewrite xG_split !cU // (card_imset _ pv_inj) (card_imset _ pu_inj).
by rewrite addnn.
Qed.

Local Lemma xGI G G' : xG (G :&: G') = xG G :&: xG G'.
Proof.
apply/setP => v; rewrite !inE; case: ifP => _; first by rewrite andbb.
apply/idP/andP => [/existsP [q /andP [/setIP [qG qG'] e]]|].
  by split; apply/existsP; exists q; rewrite ?qG ?qG'.
case=> /existsP [q /andP [qG /eqP e]] /existsP [q' /andP [qG' /eqP e']].
have qq : q = q' by apply: val_inj; rewrite /= -e e'.
by apply/existsP; exists q; rewrite inE qG qq qG' -qq e /=.
Qed.

Local Lemma mem_pv_xG q G : (pv q \in xG G) = (q \in G).
Proof.
rewrite inE /= ltnNge leq_addr /=.
apply/existsP/idP => [[q' /andP [q'G /eqP e]]|qG]; last first.
  by exists q; rewrite qG /= addKn doubleK.
by rewrite addKn doubleK in e; rewrite (val_inj e).
Qed.

Local Lemma xG_inj : injective xG.
Proof.
by move=> G G' e; apply/setP => q; rewrite -!mem_pv_xG e.
Qed.

Local Lemma cell_support_xG x :
  cell_support b 1%g y x =
  (#|x| == cell_weight k b) && (x == xG [set q | pv q \in x]).
Proof.
have tbitE (v : 'I_k) (j : 'I_d) :
    val j = val v -> tbit v = (cell_bit b y j != 0).
  move=> jv; apply/existsP/idP => [[j' /andP [/eqP j'v bj']]|bj]; last first.
    by exists j; rewrite jv eqxx.
  by have <- : j' = j by apply: val_inj; rewrite j'v jv.
have pairsS G (v u : 'I_k) : (d <= v)%N -> ~~ odd (v - d) ->
    val u = (val v).+1 -> in_pairs G u = in_pairs G v.
  move=> dv ev uv; rewrite /in_pairs uv subSn //.
  by rewrite -[(v - d).+1]add1n halfD /= (negbTE ev) /= add0n.
rewrite /cell_support; case: (#|x| == _) => //=.
set Gx := [set q | pv q \in x].
apply/andP/eqP => [[/forallP ht /forallP hp]|xE].
  apply/setP => v; rewrite inE; case: ltnP => vd.
    have := ht (Ordinal vd); move/forallP/(_ v).
    rewrite eqxx /= perm1 => /eqP ->.
    by rewrite (tbitE v (Ordinal vd)).
  have q0 := pidx_lt vd.
  set q := Ordinal q0.
  have -> : in_pairs Gx v = (pv q \in x).
    apply/existsP/idP => [[q' /andP [q'G /eqP e]]|qx].
      have qq : q' = q by apply: val_inj; rewrite /= e.
      by move: q'G; rewrite inE qq.
    by exists q; rewrite inE qx /=.
  have := odd_double_half (v - d).
  case ov: (odd (v - d)) => /= hq.
    have := hp (pv q); move/forallP/(_ v).
    have vS : val v = (val (pv q)).+1.
      by rewrite /= -addnS -[(_./2.*2).+1]add1n hq subnKC.
    have pre : [&& (a < pv q)%N, ~~ odd (pv q - d) & val v == (pv q).+1].
      by rewrite vS eqxx andbT /= ltnS leq_addr addKn odd_double.
    by rewrite pre !perm1 /= => /eqP ->.
  have vq : val v = val (pv q) by rewrite /= -[_./2.*2]add0n hq subnKC.
  by rewrite (val_inj vq).
split.
  apply/forallP => j; apply/forallP => v; apply/implyP => /eqP vj.
  have vd : (v < d)%N by rewrite vj ltn_ord.
  by rewrite perm1 xE inE vd (tbitE v j).
apply/forallP => v; apply/forallP => u.
apply/implyP => /and3P [vd ev /eqP uv].
have ud : (d <= u)%N by rewrite uv ltnS ltnW.
by rewrite !perm1 xE !inE ltnNge vd ltnNge ud /= (pairsS Gx v u).
Qed.

End layout.

(* The elements of 'F_2 are 0 and 1. *)
Local Lemma F2_bit (z : 'F_2) : z = (z != 0)%:R.
Proof. by case: z => [[|[|]]] // ?; apply: val_inj. Qed.

Local Lemma F2_natr (n : nat) : (n%:R : 'F_2) = (odd n)%:R.
Proof. by rewrite -(@Fp_nat_mod 2) // modn2. Qed.

Local Lemma F2_sum_bits n (z : 'I_n -> 'F_2) :
  \sum_(j < n) z j = (\sum_(j < n) nat_of_bool (z j != 0%R))%:R.
Proof.
rewrite natr_sum; apply: eq_bigr => j _.
by rewrite {1}(F2_bit (z j)); case: (z j != 0).
Qed.

(* The number of 1-terminals and the number of chosen pairs. *)
Section support_count.
Variables (a k : nat) (b : 'F_2) (y : 'rV['F_2]_a).
Local Notation d := a.+1.
Local Notation h := (k - a.+1)./2.
Hypotheses (ao : odd a) (ke : ~~ odd k) (h2d : ((a.+1).*2 <= k)%N).

Local Lemma cs_dk : (d <= k)%N.
Proof. by apply: leq_trans h2d; rewrite -addnn leq_addr. Qed.

Local Lemma cs_ek : ~~ odd (k - d).
Proof. by rewrite oddB ?cs_dk //= ao (negbTE ke). Qed.

Local Lemma card_tset_bits :
  #|tset k b y| = #|[set j : 'I_d | cell_bit b y j != 0]|.
Proof.
have winj : injective (widen_ord cs_dk).
  by move=> j j' e; apply: val_inj; exact: (congr1 val e).
rewrite -(card_imset _ winj); apply: eq_card => v; rewrite !inE.
apply/andP/imsetP => [[vd /existsP [j /andP [/eqP jv bj]]]|[j]].
  by exists j; rewrite ?inE //; apply: val_inj.
rewrite inE => bj ->; split; first by rewrite /= ltn_ord.
by apply/existsP; exists j; rewrite bj eqxx.
Qed.

Local Lemma odd_tset : odd #|tset k b y| = (b != 0).
Proof.
rewrite card_tset_bits -sum1_card big_mkcond /= big_ord_recr /=.
have bitw (j : 'I_a) : cell_bit b y (widen_ord (leqnSn a) j) = y 0 j.
  rewrite /cell_bit; case: insubP => [j' _ e|]; last by rewrite /= ltn_ord.
  by congr (y 0 _); apply: val_inj; rewrite e.
have bitm : cell_bit b y ord_max = b + \sum_(j < a) y 0 j.
  by rewrite /cell_bit insubF //= ltnn.
under eq_bigr => j _ do rewrite inE bitw.
rewrite inE bitm F2_sum_bits F2_natr.
set c1 := (\sum_(j < a) (if _ then _ else _))%N.
move: c1 => c.
by rewrite (F2_bit b); case: (b != 0); case oc: (odd c); rewrite oddD oc.
Qed.

Local Lemma tset_le : (#|tset k b y| <= d)%N.
Proof.
by rewrite card_tset_bits -[X in (_ <= X)%N]card_ord max_card.
Qed.

Local Notation w := (cell_weight k b).
Local Notation s := #|tset k b y|.
Local Notation g := ((cell_weight k b - #|tset k b y|)./2).

Local Lemma tset_le_w : (s <= w)%N.
Proof.
have /andP [lo _] := cell_weight_bounds k b.
apply: leq_trans tset_le _; apply: leq_trans lo.
by rewrite divn2 -[d]doubleK half_leq.
Qed.

Local Lemma g_double : (s + g.*2 = w)%N.
Proof.
by rewrite halfK oddB ?tset_le_w // odd_tset cell_weight_odd addbb subn0 subnKC
  ?tset_le_w.
Qed.

Local Lemma g_le_h : (g <= h)%N.
Proof.
apply: half_leq.
have kK : k = (k./2).*2 by rewrite -[LHS](odd_double_half k) (negbTE ke).
have dK : (d <= k./2)%N by rewrite -[d]doubleK half_leq.
have Kd : (k./2 <= k - d)%N.
  by rewrite leq_subRL ?cs_dk // [X in (_ <= X)%N]kK -addnn leq_add2r.
have so := odd_tset; move: so.
rewrite /cell_weight divn2.
case: (b != 0); case oK: (odd k./2) => /= so.
- exact: leq_trans (leq_subr _ _) Kd.
- apply: leq_trans Kd; rewrite leq_subLR -addn1 addnC leq_add2r.
  by case: #|tset k b y| so.
- apply: leq_trans (leq_subr _ _) _.
  have dK' : (d < k./2)%N.
    rewrite ltn_neqAle dK andbT; apply/eqP => e.
    by move: oK; rewrite -e /= ao.
  rewrite leq_subRL ?cs_dk // [X in (_ <= X)%N]kK -addnn addnS -addSn.
  by rewrite leq_add2r.
- exact: leq_trans (leq_subr _ _) Kd.
Qed.

Local Lemma support_set :
  [set x | cell_support b (1%g : {perm 'I_k}) y x] =
  xG b y @: [set G : {set 'I_h} | #|G| == g].
Proof.
apply/setP => x; rewrite inE (cell_support_xG _ _ cs_dk cs_ek).
apply/andP/imsetP => [[/eqP xw /eqP xE]|[G]].
  exists [set q | pv cs_dk cs_ek q \in x] => //; rewrite inE.
  have := xw; rewrite {1}xE (card_xG _ _ cs_dk cs_ek) => e.
  by apply/eqP/double_inj/(@addnI #|tset k b y|); rewrite e g_double.
rewrite inE => /eqP Gg ->; rewrite (card_xG _ _ cs_dk cs_ek) Gg g_double eqxx.
split=> //; apply/eqP; congr xG; apply/setP => q.
by rewrite inE mem_pv_xG.
Qed.

Lemma cell_count_eq : cell_count k b y = 'C(h, g).
Proof.
rewrite /cell_count support_set (card_imset _ (xG_inj cs_dk cs_ek)).
by rewrite card_draws card_ord.
Qed.

Lemma cell_count_gt0 : (0 < cell_count k b y)%N.
Proof. by rewrite cell_count_eq bin_gt0 g_le_h. Qed.

End support_count.

(* Two pairs of sets with the same sizes and the same intersection size are
   conjugate under the permutations. *)
Local Lemma perm_two_sets (T : Finite.type) (x1 x2 z1 z2 : {set T}) :
  #|x1| = #|z1| -> #|x2| = #|z2| -> #|x1 :&: x2| = #|z1 :&: z2| ->
  exists s : {perm T}, s @: x1 = z1 /\ s @: x2 = z2.
Proof.
move=> e1 e2 e12.
pose L (u1 u2 : {set T}) := enum (u1 :&: u2) ++ enum (u1 :\: u2) ++
  enum (u2 :\: u1) ++ enum (~: (u1 :|: u2)).
have Lu u1 u2 : uniq (L u1 u2).
  apply: count_mem_uniq => v.
  rewrite /L !count_cat !(count_uniq_mem _ (enum_uniq _)) !mem_cat !mem_enum.
  by rewrite !inE; case: (v \in u1); case: (v \in u2).
have sz : size (L x1 x2) = size (L z1 z2).
  rewrite !size_cat -!cardE.
  rewrite (cardsD x1 x2) (cardsD z1 z2) (cardsD x2 x1) (cardsD z2 z1).
  rewrite (cardsCs (~: (x1 :|: x2))) (cardsCs (~: (z1 :|: z2))) !setCK.
  rewrite (cardsU x1 x2) (cardsU z1 z2).
  by rewrite (setIC x2 x1) (setIC z2 z1) e1 e2 e12.
have [s] := perm_map_uniq (Lu x1 x2) (Lu z1 z2) sz.
have s1 : size [seq s i | i <- enum (x1 :&: x2)] = size (enum (z1 :&: z2)).
  by rewrite size_map -!cardE.
have s2 : size [seq s i | i <- enum (x1 :\: x2)] = size (enum (z1 :\: z2)).
  by rewrite size_map -!cardE (cardsD x1 x2) (cardsD z1 z2) e1 e12.
have s3 : size [seq s i | i <- enum (x2 :\: x1)] = size (enum (z2 :\: z1)).
  rewrite size_map -!cardE (cardsD x2 x1) (cardsD z2 z1).
  by rewrite (setIC x2 x1) (setIC z2 z1) e2 e12.
rewrite /L !map_cat => /eqP.
rewrite (eqseq_cat _ _ s1) => /andP [/eqP h1].
rewrite (eqseq_cat _ _ s2) => /andP [/eqP h2].
rewrite (eqseq_cat _ _ s3) => /andP [/eqP h3 _].
have im (A B : {set T}) : map s (enum A) = enum B -> s @: A = B.
  move=> h; apply/setP => v; rewrite -[v \in B]mem_enum -h.
  by apply/imsetP/mapP => -[u uA ->]; exists u; rewrite ?mem_enum in uA *.
exists s; split.
  by rewrite -(setID x1 x2) imsetU (im _ _ h1) (im _ _ h2) setID.
by rewrite -(setID x2 x1) imsetU setIC (im _ _ h1) (im _ _ h3) setIC setID.
Qed.

(* Moving x by s and the local data by s^-1 on the right. *)
Lemma cell_support_conj a k b (m s : {perm 'I_k}) (y : 'rV['F_2]_a)
    (x : {set 'I_k}) :
  cell_support b m y (s @: x) = cell_support b (m * s^-1)%g y x.
Proof.
rewrite [LHS]cell_support_perm [RHS]cell_support_perm -imset_comp.
by congr cell_support; apply: eq_imset => v; rewrite /= invMg invgK permM.
Qed.

(* The supports for the local data m are the images under m of the support
   for the identity layout. *)
Lemma support_perm_set a k b (m : {perm 'I_k}) (y : 'rV['F_2]_a) :
  [set x | cell_support b m y x] =
  (fun x : {set 'I_k} => m @: x) @: [set x | cell_support b 1%g y x].
Proof.
have mK (u : {set 'I_k}) : m @: (m^-1%g @: u) = u.
  by rewrite -imset_comp (eq_imset _ (permKV m)) imset_id.
have Km (u : {set 'I_k}) : m^-1%g @: (m @: u) = u.
  by rewrite -imset_comp (eq_imset _ (permK m)) imset_id.
apply/setP => x; rewrite inE cell_support_perm.
apply/idP/imsetP => [h|[z zS ->]].
  by exists (m^-1%g @: x); rewrite ?inE ?mK.
by rewrite Km; rewrite inE in zS.
Qed.

Lemma card_support a k b (m : {perm 'I_k}) (y : 'rV['F_2]_a) :
  #|[set x | cell_support b m y x]| = cell_count k b y.
Proof.
have Km (u : {set 'I_k}) : m^-1%g @: (m @: u) = u.
  by rewrite -imset_comp (eq_imset _ (permK m)) imset_id.
have inj : injective (fun u : {set 'I_k} => m @: u).
  by move=> u v e; rewrite -(Km u) -(Km v) /= e.
by rewrite support_perm_set (card_imset _ inj).
Qed.

Lemma card_support_mem a k b (m : {perm 'I_k}) (y : 'rV['F_2]_a)
    (x : {set 'I_k}) :
  cell_support b m y x -> #|x| = cell_weight k b.
Proof. by rewrite /cell_support => /andP [/eqP]. Qed.

Local Lemma cell_pi_off (R : realType) a k b (m : {perm 'I_k}) (y : 'rV['F_2]_a)
    (x : {set 'I_k}) :
  #|x| != cell_weight k b -> cell_pi R b m y x = 0.
Proof.
move=> xw; rewrite /cell_pi; case hs: (cell_support b m y x); first last.
  by rewrite mul0r.
by move: xw; rewrite (card_support_mem hs) eqxx.
Qed.

Section cell_probs.
Variables (R : realType) (a k : nat) (b : 'F_2) (y : 'rV['F_2]_a).
Hypotheses (ao : odd a) (ke : ~~ odd k) (h2d : ((a.+1).*2 <= k)%N).
Local Notation w := (cell_weight k b).

Local Lemma cell_weight_le : (w <= k)%N.
Proof.
have /andP [_ hi] := cell_weight_bounds k b; apply: leq_trans hi _.
have kK : k = (k./2).*2 by rewrite -[LHS](odd_double_half k) (negbTE ke).
have k1 : (0 < k./2)%N.
  by rewrite -(ltn_double 0) -kK (leq_trans _ h2d) // -(ltn_double 0) doubleS.
by rewrite divn2 [X in (_ <= X)%N]kK -addnn -addn1 leq_add2l.
Qed.

Lemma cell_mu_prob : prob_vec (@cell_mu R k b).
Proof.
split=> [x|]; first by rewrite /cell_mu divr_ge0 ?ler0n.
rewrite /cell_mu -mulr_suml -natr_sum.
have -> : (\sum_(x : {set 'I_k}) nat_of_bool (#|x| == w) = 'C(k, w))%N.
  by rewrite -big_mkcond /= sum1_card -cardsE card_draws card_ord.
by rewrite divff // pnatr_eq0 -lt0n bin_gt0 cell_weight_le.
Qed.

Lemma cell_nu_prob : prob_vec (@cell_nu R k).
Proof.
split=> [m|]; first by rewrite /cell_nu invr_ge0 ler0n.
rewrite /cell_nu sumr_const card_Sn -(mulr_natl (k`!%:R^-1 : R) k`!) mulfV //.
by rewrite pnatr_eq0 -lt0n fact_gt0.
Qed.

Lemma cell_pi_prob (m : {perm 'I_k}) : prob_vec (cell_pi R b m y).
Proof.
split=> [x|]; first by rewrite /cell_pi divr_ge0 ?ler0n.
rewrite /cell_pi -mulr_suml -natr_sum.
have -> : (\sum_(x : {set 'I_k}) nat_of_bool (cell_support b m y x) =
    cell_count k b y)%N.
  by rewrite -big_mkcond /= sum1_card -cardsE card_support.
by rewrite divff // pnatr_eq0 -lt0n cell_count_gt0.
Qed.

(* The number of local data whose support contains x. *)
Local Definition cell_hits (x : {set 'I_k}) : R :=
  \sum_(m : {perm 'I_k}) (cell_support b m y x)%:R.

Local Lemma cell_hits_conj (s : {perm 'I_k}) (x : {set 'I_k}) :
  cell_hits (s @: x) = cell_hits x.
Proof.
rewrite /cell_hits; under eq_bigr do rewrite cell_support_conj.
by rewrite [RHS](reindex_inj (mulIg s^-1%g)).
Qed.

Local Lemma cell_hits_card (x : {set 'I_k}) : #|x| != w -> cell_hits x = 0.
Proof.
move=> xw; apply: big1 => m _.
case hs: (cell_support b m y x) => //.
by move: xw; rewrite (card_support_mem hs) eqxx.
Qed.

Local Lemma cell_hits_const (x x' : {set 'I_k}) : #|x| = w -> #|x'| = w ->
  cell_hits x = cell_hits x'.
Proof.
move=> xw x'w.
have e1 : #|x| = #|x'| by rewrite xw x'w.
have e12 : #|x :&: x| = #|x' :&: x'| by rewrite !setIid.
have [s [sx _]] := perm_two_sets e1 e1 e12.
by rewrite -sx cell_hits_conj.
Qed.

Local Lemma cell_hits_sum : \sum_x cell_hits x = (k`! * cell_count k b y)%:R.
Proof.
rewrite /cell_hits exchange_big /=.
under eq_bigr => m _.
  rewrite -natr_sum.
  have -> : (\sum_(x : {set 'I_k}) nat_of_bool (cell_support b m y x) =
      cell_count k b y)%N.
    by rewrite -big_mkcond /= sum1_card -cardsE card_support.
  over.
by rewrite sumr_const card_Sn natrM mulr_natl.
Qed.

Local Lemma cell_hitsE (x : {set 'I_k}) : #|x| = w ->
  cell_hits x = (k`! * cell_count k b y)%:R / 'C(k, w)%:R.
Proof.
move=> xw.
have Cw : 'C(k, w)%:R != 0 :> R.
  by rewrite pnatr_eq0 -lt0n bin_gt0 cell_weight_le.
apply: (mulIf Cw); rewrite mulfVK // -cell_hits_sum.
rewrite (bigID (fun x0 : {set 'I_k} => #|x0| == w)) /=.
have z : \sum_(i : {set 'I_k} | #|i| != w) cell_hits i = 0.
  by apply: big1 => x0 /cell_hits_card.
rewrite z addr0 (eq_bigr (fun _ => cell_hits x)); last first.
  rewrite sumr_const -cardsE card_draws card_ord.
  by rewrite mulr_natr.
by move=> x0 /eqP x0w; apply: cell_hits_const.
Qed.

Lemma cell_marginal (x : {set 'I_k}) :
  \sum_(m : {perm 'I_k}) cell_nu R m * cell_pi R b m y x = cell_mu R b x.
Proof.
rewrite /cell_nu /cell_pi.
under eq_bigr do rewrite mulrA.
rewrite -mulr_suml -mulr_sumr -/(cell_hits x) /cell_mu.
have kf : k`!%:R != 0 :> R by rewrite pnatr_eq0 -lt0n fact_gt0.
have Zf : (cell_count k b y)%:R != 0 :> R.
  by rewrite pnatr_eq0 -lt0n cell_count_gt0.
case: eqP => xw.
  rewrite cell_hitsE // natrM mul1r.
  by rewrite -!mulrA mulKf // mulrC -mulrA mulVf ?mulr1.
by rewrite cell_hits_card ?mulr0 ?mul0r //; apply/eqP.
Qed.

End cell_probs.

(* The number of q-subsets of T that meet A in c points. *)
Local Lemma card_meet_sets (T : Finite.type) (A : {set T}) (q c : nat) :
  (c <= q)%N ->
  #|[set B : {set T} | (#|B| == q) && (#|A :&: B| == c)]| =
  ('C(#|A|, c) * 'C(#|T| - #|A|, q - c))%N.
Proof.
move=> cq.
pose f (B : {set T}) := (A :&: B, B :\: A).
have finj : injective f.
  move=> B B' [e1 e2]; rewrite -(setID B A) -(setID B' A).
  by rewrite ![B :&: A]setIC ![B' :&: A]setIC e1 e2.
rewrite -(card_imset _ finj).
have -> : f @: [set B : {set T} | (#|B| == q) && (#|A :&: B| == c)] =
    setX [set C : {set T} | C \subset A & #|C| == c]
         [set D : {set T} | D \subset ~: A & #|D| == (q - c)%N].
  apply/setP => -[C D]; rewrite !inE /=.
  apply/imsetP/andP => [[B] |].
    rewrite inE => /andP [/eqP Bq /eqP ABc] [-> ->].
    rewrite subsetIl ABc eqxx; split=> //.
    by rewrite (cardsD B A) setIC Bq ABc eqxx andbT setDE subsetIr.
  case=> /andP [CA /eqP Cc] /andP [DA /eqP Dc].
  have dDA : [disjoint D & A] by rewrite -[A]setCK -subsets_disjoint.
  have AC : A :&: C = C by apply/setIidPr.
  have AD : A :&: D = set0 by rewrite setIC; apply: disjoint_setI0.
  have DmA : D :\: A = D by apply/setDidPl.
  have CmA : C :\: A = set0 by apply/eqP; rewrite setD_eq0.
  have CD : C :&: D = set0.
    rewrite -AC -setIA [A :&: (C :&: D)]setIC -setIA [D :&: A]setIC AD.
    by rewrite setI0.
  exists (C :|: D); last by rewrite /f setIUr AC AD setU0 setDUl DmA CmA set0U.
  rewrite inE setIUr AC AD setU0 Cc eqxx andbT cardsU CD cards0 subn0 Cc Dc.
  by rewrite subnKC.
by rewrite cardsX !cards_draws (cardsCs (~: A)) setCK.
Qed.

(* The kernel K = N E_m[pi^m pi^m^T] on the w-subsets, N = C(k, w). *)
Section kernel.
Variables (R : realType) (a k : nat) (b : 'F_2) (y : 'rV['F_2]_a).
Hypotheses (ao : odd a) (ke : ~~ odd k) (h2d : ((a.+1).*2 <= k)%N).
Local Notation w := (cell_weight k b).
Local Notation X := (ksubset k w).
Local Notation N := #|{: X}|.
Local Notation xs i := (val (enum_val i : X)).

Local Lemma card_ksubset : N = 'C(k, w).
Proof.
by rewrite card_sig -cardsE card_draws card_ord.
Qed.

(* Sums of functions supported by the w-subsets. *)
Local Lemma sum_wsets (F : {set 'I_k} -> R) :
  (forall x : {set 'I_k}, #|x| != w -> F x = 0) ->
  \sum_x F x = \sum_(i < N) F (xs i).
Proof.
move=> F0.
rewrite (bigID (fun x : {set 'I_k} => #|x| == w)) /=.
have z : \sum_(x : {set 'I_k} | #|x| != w) F x = 0 by apply: big1 => x /F0.
rewrite z addr0 (big_sub [pred x : {set 'I_k} | #|x| == w]).
rewrite (reindex (@enum_val X predT)) //.
exact: onW_bij (@enum_val_bij X).
Qed.

Local Lemma pi_sum (m : {perm 'I_k}) : \sum_(j < N) cell_pi R b m y (xs j) = 1.
Proof.
rewrite -(sum_wsets (@cell_pi_off R a k b m y)).
by case: (@cell_pi_prob R a k b y ao ke h2d m).
Qed.

Local Definition kfun (x x' : {set 'I_k}) : R :=
  N%:R * \sum_(m : {perm 'I_k})
    cell_nu R m * cell_pi R b m y x * cell_pi R b m y x'.

Local Definition kmx : 'M[R]_N := \matrix_(i, j) kfun (xs i) (xs j).

Local Lemma kfunC x x' : kfun x x' = kfun x' x.
Proof.
by rewrite /kfun; congr (_ * _); apply: eq_bigr => m _; rewrite mulrAC.
Qed.

Local Lemma kfun_conj (s : {perm 'I_k}) (x x' : {set 'I_k}) :
  kfun (s @: x) (s @: x') = kfun x x'.
Proof.
rewrite /kfun /cell_pi; congr (_ * _).
rewrite [RHS](reindex_inj (mulIg s^-1%g)) /=; apply: eq_bigr => m _.
by rewrite !cell_support_conj.
Qed.

Local Lemma kmx_sym : kmx \is symmetricmx.
Proof.
by apply/symmetricmxP/matrixP => i j; rewrite !mxE kfunC.
Qed.

Local Lemma kmx_form (v : 'cV[R]_N) :
  mxdot v (kmx *m v) = N%:R *
    \sum_(m : {perm 'I_k}) cell_nu R m *
      (\sum_(i < N) cell_pi R b m y (xs i) * v i 0) ^+ 2.
Proof.
set p := fun m (i : 'I_N) => cell_pi R b m y (xs i).
transitivity (\sum_i \sum_j \sum_m
    N%:R * cell_nu R m * (p m i * v i 0) * (p m j * v j 0)).
  rewrite /mxdot; apply: eq_bigr => i _; rewrite big_ord1 mxE mulr_sumr.
  apply: eq_bigr => j _; rewrite mxE /kfun mulr_sumr mulr_suml !mulr_sumr.
  apply: eq_bigr => m _.
  rewrite /p -[v i 0]/(v i ord0) -[v j 0]/(v j ord0).
  move: (v i ord0) (v j ord0) (cell_nu R m) => vi vj nu.
  move: (cell_pi R b m y _) (cell_pi R b m y _) => pi pj.
  by rewrite !mulrA [vi * _]mulrC (mulrAC _ vi nu) (mulrAC _ vi pj).
rewrite mulr_sumr.
have e (m : {perm 'I_k}) : N%:R * (cell_nu R m *
      (\sum_(i < N) cell_pi R b m y (xs i) * v i 0) ^+ 2) =
    \sum_i \sum_j N%:R * cell_nu R m * (p m i * v i 0) * (p m j * v j 0).
  rewrite expr2 mulr_suml mulrA mulr_sumr; apply: eq_bigr => i _.
  by rewrite mulr_sumr mulr_sumr; apply: eq_bigr => j _; rewrite mulrA.
rewrite [RHS](eq_bigr _ (fun m _ => e m)) [RHS]exchange_big.
by apply: eq_bigr => i _; rewrite [RHS]exchange_big.
Qed.

Local Lemma kmx_psd : psdmx kmx.
Proof.
split; first exact: kmx_sym.
move=> v; rewrite kmx_form mulr_ge0 ?ler0n // sumr_ge0 // => m _.
by rewrite mulr_ge0 ?sqr_ge0 // /cell_nu invr_ge0 ler0n.
Qed.

Local Lemma kmx_one : kmx *m (const_mx 1 : 'cV[R]_N) = const_mx 1.
Proof.
apply/matrixP => i z; rewrite !mxE.
under eq_bigr do rewrite !mxE mulr1 /kfun.
rewrite -mulr_sumr exchange_big /=.
under eq_bigr do rewrite -mulr_sumr pi_sum mulr1.
rewrite (@cell_marginal R a k b y ao ke h2d) /cell_mu (valP (enum_val i)).
rewrite mul1r card_ksubset mulfV // pnatr_eq0 -lt0n bin_gt0.
exact: cell_weight_le ke h2d.
Qed.

Local Lemma kmx_commute (s : {perm 'I_k}) :
  ksubset_mx R w s *m kmx = kmx *m ksubset_mx R w s.
Proof.
have -> : kmx *m ksubset_mx R w s = (ksubset_mx R w s^-1 *m kmx)^T.
  by rewrite trmx_mul tr_ksubset_mx invgK (symmetricmxP _ kmx_sym).
apply/matrixP => i j; rewrite [RHS]mxE !ksubset_mx_mul !mxE !enum_rankK.
rewrite invgK !val_kact -(kfun_conj s (s^-1%g @: _) (val (enum_val j))).
by rewrite -imset_comp (eq_imset _ (permKV s)) imset_id kfunC.
Qed.

End kernel.

(* The permutation matrix that s induces on the w-subsets, as a perm_mx. *)
Section kperm.
Variables (R : realType) (k w : nat).
Local Notation X := (ksubset k w).
Local Notation N := #|{: X}|.

Local Definition kperm_fun (s : {perm 'I_k}) (i : 'I_N) : 'I_N :=
  enum_rank (kact s^-1%g (enum_val i)).

Local Lemma kperm_inj s : injective (kperm_fun s).
Proof.
by move=> i j /enum_rank_inj /(can_inj (kactVK s)) /enum_val_inj.
Qed.

Local Definition kperm s : {perm 'I_N} := perm (@kperm_inj s).

Local Lemma ksubset_mx_permE s : ksubset_mx R w s = perm_mx (kperm s).
Proof.
apply/matrixP => i j; rewrite ksubset_mxE !mxE permE /kperm_fun.
congr (_%:R); congr (nat_of_bool _).
apply/eqP/eqP => e; first by rewrite e kactK enum_valK.
by rewrite -e enum_rankK kactVK.
Qed.

End kperm.

Section contraction.
Variables (R : realType) (a k : nat) (b : 'F_2) (y : 'rV['F_2]_a).
Hypotheses (ao : odd a) (ke : ~~ odd k) (h2d : ((a.+1).*2 <= k)%N).
Hypothesis k6 : (6 <= k)%N.
Local Notation w := (cell_weight k b).
Local Notation X := (ksubset k w).
Local Notation N := #|{: X}|.
Local Notation xs i := (val (enum_val i : X)).
Local Notation K := (@kmx R a k b y).

Local Lemma kmx_quad (v : 'cV[R]_N) : mxdot v (const_mx 1) = 0 ->
  mxdot v (K *m v) ^+ 2 <= (\tr (K *m K) - 1) / (k %/ 2)%:R * mxdot v v ^+ 2.
Proof.
move=> v1.
pose S := [seq @kperm k w s | s <- enum {perm 'I_k}].
apply: (@trace_multiplicity R N (k %/ 2) K S) => //.
- exact: kmx_psd.
- exact: kmx_one.
- by rewrite divn_gt0 // (leq_trans _ k6).
- move=> p /mapP [s _ ->]; rewrite -(ksubset_mx_permE R).
  exact: kmx_commute.
move=> Q Qs QQ Q0 Q1 hQ.
apply: (ksubset_multiplicity ke k6 Qs QQ Q0 Q1) => s.
by rewrite (ksubset_mx_permE R); apply: hQ; apply: map_f; rewrite mem_enum.
Qed.

Local Lemma cell_variance (B : R) (g : {set 'I_k} -> R) :
  0 <= B -> (\tr (K *m K) - 1) / (k %/ 2)%:R <= B ->
  \sum_(m : {perm 'I_k}) cell_nu R m *
    (\sum_x cell_pi R b m y x * g x - \sum_x cell_mu R b x * g x) ^+ 2
  <= Num.sqrt B * \sum_x cell_mu R b x * g x ^+ 2.
Proof.
move=> B0 hB.
have Nf : N%:R != 0 :> R.
  by rewrite card_ksubset pnatr_eq0 -lt0n bin_gt0 (cell_weight_le b ke h2d).
have N0 : 0 < N%:R :> R by rewrite lt0r Nf ler0n.
have mu_w (x : {set 'I_k}) : #|x| != w -> cell_mu R b x * g x = 0.
  by move=> xw; rewrite /cell_mu (negbTE xw) mul0r mul0r.
have mu_w2 (x : {set 'I_k}) : #|x| != w -> cell_mu R b x * g x ^+ 2 = 0.
  by move=> xw; rewrite /cell_mu (negbTE xw) !mul0r.
have mu_i (i : 'I_N) : cell_mu R b (xs i) = N%:R^-1.
  by rewrite /cell_mu (valP (enum_val i)) mul1r card_ksubset.
set E := \sum_x cell_mu R b x * g x.
have EE : E = N%:R^-1 * \sum_(i < N) g (xs i).
  rewrite /E (sum_wsets mu_w) mulr_sumr; apply: eq_bigr => i _.
  by rewrite mu_i.
have sg : \sum_(i < N) g (xs i) = N%:R * E by rewrite EE mulVKf.
(* The centered values of g on the w-subsets. *)
pose v : 'cV[R]_N := \col_i (g (xs i) - E).
have pi_w (m : {perm 'I_k}) (x : {set 'I_k}) :
    #|x| != w -> cell_pi R b m y x * g x = 0.
  by move=> xw; rewrite cell_pi_off // mul0r.
have pv (m : {perm 'I_k}) : \sum_x cell_pi R b m y x * g x - E =
    \sum_(i < N) cell_pi R b m y (xs i) * v i 0.
  rewrite (sum_wsets (pi_w m)).
  under [RHS]eq_bigr do rewrite mxE mulrBr.
  by rewrite sumrB -mulr_suml (@pi_sum R a k b y ao ke h2d m) mul1r.
under eq_bigr do rewrite pv.
rewrite -(mulKf Nf (\sum_m _)) -(@kmx_form R a k b y v).
have v1 : mxdot v (const_mx 1) = 0.
  rewrite /mxdot; under eq_bigr do rewrite big_ord1 !mxE mulr1.
  by rewrite sumrB sumr_const card_ord -(mulr_natl E) EE mulVKf // subrr.
have vKv0 : 0 <= mxdot v (K *m v) by case: (@kmx_psd R a k b y) => _; apply.
have vv0 : 0 <= mxdot v v := mxdot_ge0 v.
have key : mxdot v (K *m v) <= Num.sqrt B * mxdot v v.
  rewrite -(ler_pXn2r (isT : (0 < 2)%N)) ?nnegrE ?mulr_ge0 ?sqrtr_ge0 //.
  rewrite exprMn sqr_sqrtr //; apply: le_trans (kmx_quad v1) _.
  by apply: ler_wpM2r; [exact: sqr_ge0 | exact: hB].
(* |v|^2 = sum g^2 - N E^2. *)
have vv : mxdot v v <= N%:R * \sum_x cell_mu R b x * g x ^+ 2.
  rewrite (sum_wsets mu_w2) mulr_sumr.
  under eq_bigr do rewrite mu_i mulVKf //.
  rewrite /mxdot -subr_ge0 -sumrB.
  have e i : g (xs i) ^+ 2 - \sum_(j < 1) v i j * v i j =
      g (xs i) * E *+ 2 - E ^+ 2.
    rewrite big_ord1 mxE -expr2 sqrrB opprD opprB addrA addrC addrA.
    by rewrite -addrA [g _ ^+ 2 + _]addrC subrK addrC.
  under eq_bigr do rewrite e.
  rewrite sumrB sumrMnl -mulr_suml sg sumr_const card_ord.
  rewrite -mulrA -expr2 -(mulr_natl (E ^+ 2)) mulr2n addrK.
  by rewrite mulr_ge0 ?ler0n ?sqr_ge0.
have h1 : N%:R^-1 * mxdot v (K *m v) <= N%:R^-1 * (Num.sqrt B * mxdot v v).
  by rewrite ler_wpM2l // invr_ge0 ltW.
apply: (le_trans h1).
by rewrite mulrCA ler_wpM2l ?sqrtr_ge0 // ler_pdivrMl.
Qed.

End contraction.

(* A sum of squares of a constant family. *)
Local Lemma sum_sqr_const (R : realType) (I : Finite.type) (P : pred I)
    (F : I -> R) :
  (forall j j', P j -> P j' -> F j = F j') ->
  \sum_(j | P j) F j ^+ 2 = (\sum_(j | P j) F j) ^+ 2 / #|P|%:R.
Proof.
move=> hF.
have [j0 Pj0|P0] := pickP P; last first.
  by rewrite !big_pred0 // expr0n /= mul0r.
have e1 : \sum_(j | P j) F j ^+ 2 = \sum_(j | P j) F j0 ^+ 2.
  by apply: eq_bigr => j Pj; rewrite (hF j j0).
have e2 : \sum_(j | P j) F j = \sum_(j | P j) F j0.
  by apply: eq_bigr => j Pj; rewrite (hF j j0).
rewrite e1 e2 !sumr_const.
have P1 : #|P|%:R != 0 :> R.
  by rewrite pnatr_eq0 -lt0n; apply/card_gt0P; exists j0.
move: #|P| P1 => n n0.
rewrite -(mulr_natr (F j0 ^+ 2)) -(mulr_natr (F j0)) exprMn (expr2 (n%:R)).
by rewrite mulrA mulfK.
Qed.

(* The trace of K^2, by the classes of intersection size in each row. *)
Section trace.
Variables (R : realType) (a k : nat) (b : 'F_2) (y : 'rV['F_2]_a).
Hypotheses (ao : odd a) (ke : ~~ odd k) (h2d : ((a.+1).*2 <= k)%N).
Local Notation w := (cell_weight k b).
Local Notation X := (ksubset k w).
Local Notation N := #|{: X}|.
Local Notation xs i := (val (enum_val i : X)).
Local Notation K := (@kmx R a k b y).

(* The sum of the row i of K over the class c. *)
Local Definition rclass (i : 'I_N) (c : nat) : R :=
  \sum_(j < N | #|xs i :&: xs j| == c) K i j.

Local Lemma kmx_class i j j' :
  #|xs i :&: xs j| = #|xs i :&: xs j'| -> K i j = K i j'.
Proof.
move=> e.
have ej : #|xs j| = #|xs j'|.
  by rewrite (eqP (valP (enum_val j))) (eqP (valP (enum_val j'))).
have [s [si sj]] := perm_two_sets (erefl #|xs i|) ej e.
by rewrite !mxE -si -sj kfun_conj si.
Qed.

Local Lemma trace_classes : \tr (K *m K) =
  \sum_(i < N) \sum_(c < w.+1)
    rclass i c ^+ 2 / #|[pred j : 'I_N | #|xs i :&: xs j| == c]|%:R.
Proof.
rewrite /mxtrace; apply: eq_bigr => i _; rewrite mxE.
have KT j : K j i = K i j.
  by rewrite -[in LHS](symmetricmxP _ (@kmx_sym R a k b y)) mxE.
under eq_bigr do rewrite KT -expr2.
have le (j : 'I_N) : (#|xs i :&: xs j| < w.+1)%N.
  rewrite ltnS; apply: leq_trans (subset_leq_card (subsetIl _ _)) _.
  exact: eq_leq (eqP (valP (enum_val i))).
rewrite (partition_big (fun j : 'I_N => (inord #|xs i :&: xs j| : 'I_w.+1))
  xpredT) //=.
apply: eq_bigr => c _.
have cl (j : 'I_N) :
    (inord #|xs i :&: xs j| == c :> 'I_w.+1) = (#|xs i :&: xs j| == c).
  by rewrite -val_eqE /= inordK // le.
rewrite (eq_bigl _ _ cl).
rewrite (sum_sqr_const (P := fun j : 'I_N => #|xs i :&: xs j| == c)) //.
by move=> j j' /eqP ej /eqP ej'; apply: kmx_class; rewrite ej ej'.
Qed.

Local Notation s := #|tset k b y|.
Local Notation g := ((cell_weight k b - #|tset k b y|)./2).
Local Notation h := ((k - a.+1)./2).
Local Notation Z := (cell_count k b y).

(* The number of points x' of a support that meet a point x of it in c
   points: s + 2 i = c, with i the number of common pairs. *)
Local Definition hypc (c : nat) : nat :=
  \sum_(i < g.+1) (c == s + i.*2) * ('C(g, i) * 'C(h - g, g - i)).

Local Lemma card_imsetI (T : Finite.type) (t : {perm T}) (A B : {set T}) :
  #|(t @: A) :&: (t @: B)| = #|A :&: B|.
Proof.
have inj : {in A & B, injective t} by move=> u v _ _; exact: perm_inj.
by rewrite -(imsetI inj) card_imset //; exact: perm_inj.
Qed.

Local Lemma count_meet_support (m : {perm 'I_k}) (x : {set 'I_k}) c :
  cell_support b m y x ->
  #|[set x' | cell_support b m y x' && (#|x :&: x'| == c)]| = hypc c.
Proof.
move=> hx.
set z := m^-1%g @: x.
have hz : cell_support b 1%g y z by rewrite -cell_support_perm.
have mK (u : {set 'I_k}) : m @: (m^-1%g @: u) = u.
  by rewrite -imset_comp (eq_imset _ (permKV m)) imset_id.
have Km (u : {set 'I_k}) : m^-1%g @: (m @: u) = u.
  by rewrite -imset_comp (eq_imset _ (permK m)) imset_id.
(* Move to the identity layout. *)
have -> : [set x' | cell_support b m y x' & #|x :&: x'| == c] =
    (fun u : {set 'I_k} => m @: u) @:
      [set z' | cell_support b 1%g y z' & #|z :&: z'| == c].
  apply/setP => x'; rewrite inE.
  apply/andP/imsetP => [[sx' cx]|[z' hz' ->]].
    exists (m^-1%g @: x'); last by rewrite mK.
    by rewrite inE -cell_support_perm sx' /= card_imsetI.
  rewrite inE in hz'; case/andP: hz' => sz' cz'.
  by rewrite cell_support_perm Km sz' -[x]mK card_imsetI.
have minj : injective (fun u : {set 'I_k} => m @: u).
  by move=> u v e; rewrite -(Km u) -(Km v) /= e.
rewrite (card_imset _ minj).
(* The points of the identity support are the sets xG G', |G'| = g. *)
have dk := cs_dk h2d; have ek := cs_ek ao ke h2d.
have SS := support_set b y ao ke h2d.
have : z \in [set x | cell_support b 1%g y x] by rewrite inE.
rewrite SS => /imsetP [G0]; rewrite inE => /eqP G0g zE.
have -> : [set z' | cell_support b 1%g y z' & #|z :&: z'| == c] =
    xG b y @: [set G' : {set 'I_h} |
      (#|G'| == g) && (s + (#|G0 :&: G'|).*2 == c)].
  apply/setP => z'; rewrite inE.
  have := SS; move/setP/(_ z'); rewrite inE => ->.
  apply/andP/imsetP => [[/imsetP [G' G'g ->] cz]|[G' G'P ->]].
    exists G' => //; rewrite !inE in G'g *; rewrite G'g /=.
    by rewrite zE -xGI (card_xG b y dk ek) in cz.
  rewrite inE in G'P; case/andP: G'P => G'g sc; split.
    by apply/imsetP; exists G'; rewrite ?inE.
  by rewrite zE -xGI (card_xG b y dk ek).
rewrite (card_imset _ (xG_inj dk ek)).
(* Count by the number i of common pairs. *)
have le (G' : {set 'I_h}) : (#|G0 :&: G'| < g.+1)%N.
  by rewrite ltnS -G0g subset_leq_card ?subsetIl.
rewrite -sum1_card.
rewrite (partition_big (fun G' => inord #|G0 :&: G'| : 'I_g.+1) xpredT) //=.
rewrite /hypc; apply: eq_bigr => i _; rewrite sum1_card.
have cl (G' : {set 'I_h}) :
    (inord #|G0 :&: G'| == i :> 'I_g.+1) = (#|G0 :&: G'| == i).
  by rewrite -val_eqE /= inordK // le.
have [ci|nci] := eqVneq c (s + i.*2).
  have ig : (i <= g)%N by rewrite -ltnS ltn_ord.
  have cm := @card_meet_sets _ G0 g i ig; rewrite G0g card_ord in cm.
  rewrite /= mul1n -cm; apply: eq_card => G'.
  rewrite !inE /= unfold_in /= inE cl ci.
  by rewrite eqn_add2l -!muln2 eqn_mul2r /= -andbA andbb.
rewrite /= mul0n; apply: eq_card0 => G'; rewrite unfold_in /= inE cl.
apply/negP => /andP [/andP [_ /eqP e] /eqP ei].
by move: nci; rewrite -e ei eqxx.
Qed.

Local Lemma rclassE i c : rclass i c = (hypc c)%:R / Z%:R.
Proof.
set x := xs i.
have Zf : Z%:R != 0 :> R.
  by rewrite pnatr_eq0 -lt0n (cell_count_gt0 b y ao ke h2d).
have Nf : N%:R != 0 :> R.
  by rewrite card_ksubset pnatr_eq0 -lt0n bin_gt0 (cell_weight_le b ke h2d).
(* For each local data, the class sum of pi^m is hypc c / Z on the support. *)
have inner (m : {perm 'I_k}) :
    \sum_(j < N | #|x :&: xs j| == c)
      cell_pi R b m y (xs j) * cell_pi R b m y x =
    (hypc c)%:R / Z%:R * cell_pi R b m y x.
  case hs: (cell_support b m y x); last first.
    have p0 : cell_pi R b m y x = 0 by rewrite /cell_pi hs mul0r.
    by rewrite p0 mulr0; apply: big1 => j _; rewrite mulr0.
  rewrite -mulr_suml; congr (_ * _).
  have F0 (x' : {set 'I_k}) : #|x'| != w ->
      (#|x :&: x'| == c)%:R * cell_pi R b m y x' = 0.
    by move=> x'w; rewrite cell_pi_off // mulr0.
  have -> : \sum_(j < N | #|x :&: xs j| == c) cell_pi R b m y (xs j) =
      \sum_(j < N) (#|x :&: xs j| == c)%:R * cell_pi R b m y (xs j).
    rewrite big_mkcond /=; apply: eq_bigr => j _.
    by case: eqP; rewrite ?mul1r ?mul0r.
  rewrite -(sum_wsets F0) /cell_pi.
  under eq_bigr do rewrite mulrA -natrM.
  rewrite -mulr_suml -natr_sum -(count_meet_support c hs).
  congr (_%:R / _).
  rewrite -[RHS]sum1_card [RHS]big_mkcond /=; apply: eq_bigr => x' _.
  by rewrite inE andbC; case: (_ == _); case: (cell_support _ _ _ _).
rewrite /rclass; under eq_bigr do rewrite mxE /kfun.
rewrite -mulr_sumr exchange_big /=.
have e (m : {perm 'I_k}) : \sum_(j < N | #|x :&: xs j| == c)
    cell_nu R m * cell_pi R b m y x * cell_pi R b m y (xs j) =
    (hypc c)%:R / Z%:R * (cell_nu R m * cell_pi R b m y x).
  rewrite [RHS]mulrCA -inner mulr_sumr.
  by apply: eq_bigr => j _; rewrite [RHS]mulrA [RHS]mulrAC.
rewrite (eq_bigr _ (fun m _ => e m)) -mulr_sumr.
rewrite (@cell_marginal R a k b y ao ke h2d) /cell_mu (valP (enum_val i)).
by rewrite mul1r -card_ksubset mulrCA mulfV // mulr1.
Qed.

Local Lemma class_card (i : 'I_N) c : (c <= w)%N ->
  #|[pred j : 'I_N | #|xs i :&: xs j| == c]| = ('C(w, c) * 'C(k - w, w - c))%N.
Proof.
move=> cw.
have xinj : injective (fun j : 'I_N => xs j).
  by move=> j j' /val_inj /enum_val_inj.
rewrite -(card_imset _ xinj).
have -> : [set xs j | j in [pred j : 'I_N | #|xs i :&: xs j| == c]] =
    [set B : {set 'I_k} | (#|B| == w) && (#|xs i :&: B| == c)].
  apply/setP => B; rewrite inE; apply/imsetP/andP => [[j jP ->]|[Bw BP]].
    by split; [exact: (valP (enum_val j)) | exact: jP].
  by exists (enum_rank (Sub B Bw : X)); rewrite ?inE enum_rankK.
by rewrite card_meet_sets // (eqP (valP (enum_val i))) card_ord.
Qed.

Local Lemma hypc_pair (i : 'I_g.+1) :
  hypc (s + i.*2) = ('C(g, i) * 'C(h - g, g - i))%N.
Proof.
rewrite /hypc (bigD1 i) //= eqxx mul1n big1 ?addn0 // => i' ii'.
rewrite eqn_add2l -!muln2 eqn_mul2r /=.
by rewrite (_ : (i == i' :> nat) = false) // eq_sym; apply/negbTE.
Qed.

Local Lemma hypc_off c : (forall i : 'I_g.+1, c != s + i.*2) -> hypc c = 0%N.
Proof.
move=> nc; rewrite /hypc big1 // => i _.
by rewrite (negbTE (nc i)) mul0n.
Qed.

(* The trace formula, by the number i of common pairs. *)
Local Lemma trace_pairs : \tr (K *m K) =
  N%:R / Z%:R ^+ 2 * \sum_(i < g.+1)
    ('C(g, i) * 'C(h - g, g - i))%:R ^+ 2 /
    ('C(w, s + i.*2) * 'C(k - w, w - (s + i.*2)))%:R.
Proof.
rewrite trace_classes.
pose F (c : nat) : R := (hypc c)%:R ^+ 2 / ('C(w, c) * 'C(k - w, w - c))%:R.
have row (i : 'I_N) : \sum_(c < w.+1) rclass i c ^+ 2 /
    #|[pred j : 'I_N | #|xs i :&: xs j| == c]|%:R =
    \sum_(c < w.+1) F c / Z%:R ^+ 2.
  apply: eq_bigr => c _; rewrite rclassE.
  have cw : (c <= w)%N by rewrite -ltnS ltn_ord.
  by rewrite (class_card i cw) /F expr_div_n mulrAC.
rewrite (eq_bigr _ (fun i _ => row i)) sumr_const card_ord.
rewrite -(mulr_natl (\sum_(c < w.+1) F c / Z%:R ^+ 2) N) -mulr_suml.
rewrite mulrA [N%:R * _ / _]mulrAC; congr (_ * _).
(* Only the classes s + 2 i, i <= g, are charged. *)
transitivity (\sum_(c < w.+1) \sum_(i < g.+1)
    (c == s + i.*2 :> nat)%:R * F c).
  apply: eq_bigr => c _.
  case: (pickP (fun i : 'I_g.+1 => (c : nat) == s + i.*2)) => [i /eqP ci|nc].
    rewrite (bigD1 i) //= ci eqxx mul1r big1 ?addr0 // => i' ii'.
    rewrite eqn_add2l -!muln2 eqn_mul2r /=.
    rewrite (_ : (i == i' :> nat) = false) ?mul0r //.
    by apply/negbTE; rewrite eq_sym.
  have Fc0 : F c = 0.
    by rewrite /F hypc_off ?expr0n /= ?mul0r // => i; rewrite nc.
  by rewrite Fc0; symmetry; apply: big1 => i _; rewrite mulr0.
rewrite exchange_big; apply: eq_bigr => i _.
have lt : (s + i.*2 < w.+1)%N.
  rewrite ltnS; apply: (leq_trans _ (eq_leq (g_double b y h2d))).
  by rewrite leq_add2l leq_double -ltnS ltn_ord.
rewrite (bigD1 (Ordinal lt)) //= eqxx mul1r big1 ?addr0.
  move=> c nc; rewrite (_ : (c == s + i.*2 :> nat) = false) ?mul0r //.
  by apply/negbTE; apply: contra nc => /eqP e; apply/eqP/val_inj.
by rewrite /F hypc_pair.
Qed.

End trace.

(* The bound on the trace of K^2, for h >= 6 d. *)
Section trace_bound.
Variables (R : realType) (a k : nat) (b : 'F_2) (y : 'rV['F_2]_a).
Hypotheses (ao : odd a) (ke : ~~ odd k) (h2d : ((a.+1).*2 <= k)%N).
Local Notation d := a.+1.
Local Notation h := ((k - a.+1)./2).
Hypothesis h6 : (6 * d <= h)%N.
Local Notation w := (cell_weight k b).
Local Notation K := (@kmx R a k b y).

(* The constant of the central ratio, with T = d. *)
Definition cell_cmass (d : nat) : nat := (16 ^ d./2 * 4 * 16 ^ d.+1)%N.

Local Lemma trace_bound : \tr (K *m K) <=
  Num.sqrt ((cell_cmass d)%:R * h.+1%:R) * (8%:R * (1 + ln (h.+1%:R : R))).
Proof.
have dk := cs_dk h2d; have ek := cs_ek ao ke h2d.
have lk := layout_k dk ek.
have gd := g_double b y h2d; have gh := g_le_h b y ao ke h2d.
have sd := tset_le b y h2d.
set s := #|tset k b y| in gd gh sd *; set g := ((w - s)./2) in gd gh *.
(* k = 2 n with n = h + d/2, and |2 g - h| <= 2 d. *)
have kn : k./2 = (h + d./2)%N.
  by rewrite -[in LHS]lk halfD odd_double andbF doubleK add0n addnC.
have kK : (k = 2 * k./2)%N.
  by rewrite mul2n -[LHS](odd_double_half k) (negbTE ke).
have hn : (h <= k./2)%N by rewrite kn leq_addr.
have Ckw : (k./2 <= w)%N.
  by have /andP [lo _] := cell_weight_bounds k b; rewrite -divn2.
have wk : (w <= k./2.+1)%N.
  by have /andP [_ hi] := cell_weight_bounds k b; rewrite -divn2.
have hB : (h <= 2 * (g + d))%N.
  apply: leq_trans hn _; apply: leq_trans Ckw _.
  rewrite -gd mul2n doubleD addnC leq_add // (leq_trans sd) //.
  by rewrite -addnn leq_addl.
have hC : (2 * g <= h + 2 * d)%N.
  rewrite mul2n -[g.*2](addKn s) gd; apply: leq_trans (leq_subr _ _) _.
  apply: leq_trans wk _; rewrite kn -addnS leq_add2l.
  by rewrite ltn_half_double mul2n -!muln2 -mulnA ltn_Pmulr.
have hA : ((h - g).*2 <= k - w)%N.
  rewrite doubleB -gd -[in X in (_ <= X)%N]lk.
  by rewrite -(subnDl s) leq_sub2r // leq_add2r.
rewrite (trace_pairs R b y ao ke h2d) (cell_count_eq b y ao ke h2d).
rewrite card_ksubset.
have hs := pair_sum_bound R gh gd hA.
apply: ler_pM.
- by rewrite divr_ge0 ?ler0n ?exprn_ge0.
- by apply: sumr_ge0 => i _; rewrite divr_ge0 ?ler0n ?exprn_ge0.
- have Zp : (0 < 'C(h, g))%N by rewrite bin_gt0.
  rewrite -(ler_pXn2r (isT : (0 < 2)%N)) ?nnegrE ?divr_ge0 ?sqrtr_ge0 ?ler0n
    ?exprn_ge0 //.
  rewrite sqr_sqrtr ?mulr_ge0 ?ler0n // expr_div_n -exprM.
  rewrite ler_pdivrMr ?exprn_gt0 ?ltr0n // -!natrX -!natrM ler_nat.
  have cr' := central_ratio w hn h6 hB hC.
  by rewrite -kK kn addKn in cr'; rewrite /cell_cmass.
- exact: hs.
Qed.

Local Lemma ratio_bound : (\tr (K *m K) - 1) / (k %/ 2)%:R <=
  8%:R * Num.sqrt (cell_cmass d)%:R * (1 + ln (h.+1%:R : R)) / Num.sqrt h.+1%:R.
Proof.
have dk := cs_dk h2d; have ek := cs_ek ao ke h2d.
have lk := layout_k dk ek.
have kn : k./2 = (h + d./2)%N.
  by rewrite -[in LHS]lk halfD odd_double andbF doubleK add0n addnC.
have d2 : (0 < d./2)%N.
  rewrite -(ltn_double 0) -[X in (_ < X)%N]addn0 -{1}(odd_double_half d) /= ao.
  by case: a ao.
have kh : (h.+1%:R : R) <= (k %/ 2)%:R.
  by rewrite ler_nat divn2 kn -addn1 leq_add2l.
have hp : (0 : R) < h.+1%:R by rewrite ltr0n.
have Ln : (0 : R) <= 1 + ln h.+1%:R by rewrite addr_ge0 // ln_ge0 // ler1n.
have N0 : (0 : R) <=
    Num.sqrt ((cell_cmass d)%:R * h.+1%:R) * (8%:R * (1 + ln h.+1%:R)).
  by rewrite mulr_ge0 ?sqrtr_ge0 ?mulr_ge0 ?ler0n.
apply: (@le_trans _ _ (\tr (K *m K) / (k %/ 2)%:R)).
  by rewrite ler_wpM2r ?invr_ge0 ?ler0n // lerBlDr lerDl.
have kpos : (0 : R) <= (k %/ 2)%:R^-1 by rewrite invr_ge0 ler0n.
apply: (le_trans (ler_wpM2r kpos trace_bound)).
apply: (@le_trans _ _ (Num.sqrt ((cell_cmass d)%:R * h.+1%:R) *
    (8%:R * (1 + ln h.+1%:R)) / h.+1%:R)).
  by rewrite ler_wpM2l // lef_pV2 ?posrE // (lt_le_trans hp kh).
(* sqrt (M (h + 1)) / (h + 1) = sqrt M / sqrt (h + 1). *)
rewrite le_eqVlt; apply/orP; left; apply/eqP.
rewrite sqrtrM ?ler0n //.
have sH0 : Num.sqrt (h.+1%:R : R) != 0 by rewrite gt_eqF ?sqrtr_gt0.
rewrite -[X in _ / X = _](@sqr_sqrtr _ (h.+1%:R)) ?ler0n //.
set sM := Num.sqrt (cell_cmass d)%:R; set sH := Num.sqrt h.+1%:R.
rewrite expr2 invfM mulrA [sM * sH * _]mulrAC mulfK //.
by rewrite mulrCA mulrA.
Qed.

End trace_bound.

(* The local averaging lemma. *)
Section local_averaging.
Variable R : realType.

Definition cell_hyps (a k : nat) (b : 'F_2) (theta : R) : Prop :=
  [/\ prob_vec (@cell_mu R k b), prob_vec (@cell_nu R k),
      forall (m : {perm 'I_k}) (y : 'rV['F_2]_a), prob_vec (cell_pi R b m y),
      forall (y : 'rV['F_2]_a) (x : {set 'I_k}),
        \sum_m cell_nu R m * cell_pi R b m y x = cell_mu R b x &
      forall (y : 'rV['F_2]_a) (g : {set 'I_k} -> R),
        \sum_m cell_nu R m *
          (\sum_x cell_pi R b m y x * g x - \sum_x cell_mu R b x * g x) ^+ 2
        <= theta * \sum_x cell_mu R b x * g x ^+ 2].

Lemma cell_pi_gt0 a k b (m : {perm 'I_k}) (y : 'rV['F_2]_a) (x : {set 'I_k}) :
  odd a -> ~~ odd k ->
  ((a.+1).*2 <= k)%N -> (0 < cell_pi R b m y x) = cell_support b m y x.
Proof.
move=> ao ke h2d; rewrite /cell_pi; case: (cell_support b m y x).
  by rewrite mul1r invr_gt0 ltr0n (cell_count_gt0 b y ao ke h2d).
by rewrite mul0r ltxx.
Qed.

Definition cell_theta (a k : nat) : R :=
  Num.sqrt (8%:R * Num.sqrt (cell_cmass a.+1)%:R *
    (1 + ln (((k - a.+1)./2).+1%:R : R)) /
    Num.sqrt ((k - a.+1)./2).+1%:R).

Theorem local_averaging (a : nat) : odd a ->
  exists (k0 : nat) (theta : nat -> R),
  [/\ forall k, 0 <= theta k,
      forall e : R, 0 < e -> exists k1, forall k, ~~ odd k -> (k1 <= k)%N ->
        theta k <= e &
      forall k, ~~ odd k -> (6 <= k)%N -> (2 * a.+1 <= k)%N -> (k0 <= k)%N ->
      forall b : 'F_2, cell_hyps a k b (theta k) /\
        (forall (m : {perm 'I_k}) (y : 'rV['F_2]_a) (x : {set 'I_k}),
           0 < cell_pi R b m y x -> cell_support b m y x)].
Proof.
move=> ao.
pose C : R := 8%:R * Num.sqrt (cell_cmass a.+1)%:R.
have C0 : 0 <= C by rewrite mulr_ge0 ?ler0n ?sqrtr_ge0.
have B0 (k : nat) : 0 <= C * (1 + ln (((k - a.+1)./2).+1%:R : R)) /
    Num.sqrt ((k - a.+1)./2).+1%:R.
  by rewrite divr_ge0 ?sqrtr_ge0 // mulr_ge0 // addr_ge0 // ln_ge0 // ler1n.
exists (13 * a.+1)%N, (cell_theta a); split.
- by move=> k; exact: sqrtr_ge0.
- move=> e e0.
  have [n1 hn1] := root_ln_lim C (exprn_gt0 2 e0).
  exists (2 * n1 + a.+1)%N => k _ kk.
  have e2 : 0 <= e ^+ 2 by rewrite exprn_ge0 // ltW.
  rewrite /cell_theta -/C -(gtr0_norm e0) -sqrtr_sqr (ler_sqrt _ e2).
  apply: hn1; apply: leqW; rewrite -[n1]doubleK half_leq //.
  have dk : (a.+1 <= k)%N by apply: leq_trans kk; rewrite leq_addl.
  by rewrite (leq_subRL _ dk) addnC -mul2n.
move=> k ke k6 k2d k13 b.
have h2d : ((a.+1).*2 <= k)%N by rewrite -mul2n.
(* k >= 13 d gives h >= 6 d. *)
have h6 : (6 * a.+1 <= (k - a.+1)./2)%N.
  have dk : (a.+1 <= k)%N by apply: leq_trans h2d; rewrite -addnn leq_addr.
  rewrite -(doubleK (6 * a.+1)%N) half_leq // (leq_subRL _ dk) -mul2n mulnA.
  by rewrite -{1}[a.+1]mul1n -mulnDl.
split; last by move=> m y x; rewrite cell_pi_gt0.
split.
- exact: cell_mu_prob ke h2d.
- exact: cell_nu_prob.
- by move=> m y; exact: cell_pi_prob ao ke h2d m.
- by move=> y x; exact: cell_marginal ao ke h2d x.
move=> y g.
have rb := @ratio_bound R a k b y ao ke h2d h6.
exact: (@cell_variance R a k b y ao ke h2d k6 _ g (B0 k) rb).
Qed.

End local_averaging.
