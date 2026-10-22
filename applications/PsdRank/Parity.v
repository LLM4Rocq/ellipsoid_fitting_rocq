From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import zmodp matrix reals.
From mathcomp Require Import arithmetic_tactic.
From GaussianAnalysis.fourier Require Import boolean_fourier.
From GaussianAnalysis.combinatorics Require Import expander.
From GaussianApplications.PsdRank Require Import Model Main.

(**md**************************************************************************)
(* # The parity functional                                                    *)
(*                                                                            *)
(* Item A4 of phase 14 (AGENTS.md, section Phase 14): a Rocq formalization of *)
(* the credited argument of the proposition 'Parity functional' of            *)
(* 'Exponential PSD rank of positively shifted matching matrices' (family 126 *)
(* of the OpenAI math collection, revision 1581d4cbd),                        *)
(* source/sections/parity.tex, lines 93-284, with the statement at lines      *)
(* 131-150. It follows no Lean module of the collection, whose development    *)
(* proves a weaker theorem by another route.                                  *)
(*                                                                            *)
(* It is stated on the frame of PsdRank/Model.v: the cells 'I_(l + l), the    *)
(* graph of the 100 permutations sigma j of 'I_l whose edge (j, u) joins the  *)
(* cells lshift l u and rshift l (sigma j u) at position j at both ends, the  *)
(* free bits y : 'M['F_2]_(l + l, 99), the charges b and f_eps sigma b eps y  *)
(* = (the number of edges whose two incidence bits differ) - eps.             *)
(*                                                                            *)
(* - parity_functional_holds: if min(|W|, t - |W|) <= |perm_cut sigma W| for  *)
(*   every set W of cells, with t = l + l, and t >= 1000, then                *)
(*   parity_functional (t %/ 1000) eps (f_eps sigma b eps) of PsdRank/Main.v  *)
(*   holds, for any charges b and any eps: there is a linear functional Phi,  *)
(*   nonnegative on the squares of the functions of block degree at most D =  *)
(*   t %/ 1000, with Phi f_eps = - eps and |Phi h| <= (2^99)^t c when |h| <=  *)
(*   c. It is the hypothesis on the parity functional that item A6            *)
(*   discharges.                                                              *)
(*                                                                            *)
(* The construction. Vertex sets are F_2 rows W, and edge sets F_2 matrices   *)
(* indexed by the labels (j, u): cutvec W is the cut of W, and edgevec p the  *)
(* set of edges with an odd number of free incidences selected by a frequency *)
(* p (the positions j < 99 are the free bits). sideval p is the sign (-1)^(b  *)
(* . W) of the small side W of the cut edgevec p, with 5 |W| <= t, when p has *)
(* block degree at most 2 D and edgevec p is a cut, and 0 otherwise; Phi h =  *)
(* sum_p fcoef h p sideval p (parity_phi).                                    *)
(*                                                                            *)
(* The proof. An edge set edgevec p has at most 99 blk_deg p <= 198 D < t / 5 *)
(* edges (ewt_edgevec), so a cut edgevec p has a side of size at most t / 5   *)
(* (small_exists), unique by connectivity (cut_unique). The small sides add   *)
(* up (sideval_cocycle), which regroups Phi(g^2) into squares over the        *)
(* classes of the relation edgevec (p + q) is a cut, through a representative *)
(* of each class (class_rep, sideval_class, parity_phi_sqr). The sign of an   *)
(* edge has value 1, at a free position and at the parity position            *)
(* (parity_phi_sign), so every disagreement indicator has value 0 and Phi     *)
(* f_eps = - eps (parity_phi_feps). The bound follows from the bound on the   *)
(* Fourier coefficients (parity_phi_norm).                                    *)
(*                                                                            *)
(* Departure 1 of phase 14: the block degree is D = t %/ 1000 for every t >=  *)
(* 1000, where the TeX takes tau = 1/1000, D = floor(tau t) and t large. The  *)
(* hypothesis t >= 1000 is necessary: at D = 0 the functional is the uniform  *)
(* mean. The frame takes t = l + l, so t is even. The odd total charge is not *)
(* used, and Phi 1 = 1 (parity_phi_cst) is proved although PsdRank/Main.v     *)
(* does not need it.                                                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma F2_neq (x y : 'F_2) : ((x != 0) != (y != 0)) = (x + y != 0).
Proof.
by case: (F2_cases x) => ->; case: (F2_cases y) => ->;
  rewrite ?addF2_11 ?add0r ?addr0.
Qed.

Lemma F2_double (x : 'F_2) : x + x = 0.
Proof. by case: (F2_cases x) => ->; rewrite ?addr0 ?addF2_11. Qed.

Section graph.
Variables (l : nat) (sigma : 'I_100 -> {perm 'I_l}).
Local Notation t := (l + l)%N.
Local Notation vset := 'rV['F_2]_t.
Local Notation eset := 'M['F_2]_(100, l).
Local Notation cube := 'M['F_2]_(t, 99).

(* Vertex sets as F_2 rows, edge sets as F_2 matrices indexed by labels. *)
Definition vsupp (W : vset) : {set 'I_t} := [set i | W 0 i != 0].
Definition vwt (W : vset) : nat := #|vsupp W|.
Definition ewt (E : eset) : nat :=
  #|[set e : 'I_100 * 'I_l | E e.1 e.2 != 0]|.

(* The cut of W: the edges with exactly one end in W. *)
Definition cutvec (W : vset) : eset :=
  \matrix_(j, u) (W 0 (lshift l u) + W 0 (rshift l (sigma j u))).

(* The edges with an odd number of free incidences selected by p: the edge
   (j, u) sits at position j at both ends, and the positions j < 99 are the
   free bits. *)
Definition edgevec (p : cube) : eset :=
  \matrix_(j, u) (if insub (val j) is Some j'
    then p (lshift l u) j' + p (rshift l (sigma j u)) j' else 0).

Lemma cutvecD W W' : cutvec (W + W') = cutvec W + cutvec W'.
Proof. by apply/matrixP => j u; rewrite !mxE addrACA. Qed.

Lemma cutvec0 : cutvec 0 = 0.
Proof. by apply/matrixP => j u; rewrite !mxE addr0. Qed.

Lemma cutvec1 : cutvec (const_mx 1) = 0.
Proof. by apply/matrixP => j u; rewrite !mxE addF2_11. Qed.

Lemma edgevecD p q : edgevec (p + q) = edgevec p + edgevec q.
Proof.
apply/matrixP => j u; rewrite !mxE.
by case: insub => [j'|]; rewrite ?mxE ?addr0 // addrACA.
Qed.

Lemma edgevec0 : edgevec 0 = 0.
Proof.
apply/matrixP => j u; rewrite !mxE.
by case: insub => [j'|]; rewrite ?mxE ?addr0.
Qed.

Lemma ewt0 : ewt 0 = 0%N.
Proof. by apply: eq_card0 => e; rewrite !inE mxE eqxx. Qed.

Lemma ewt_cutvec W : ewt (cutvec W) = #|perm_cut sigma (vsupp W)|.
Proof. by apply: eq_card => e; rewrite !inE mxE F2_neq. Qed.

Lemma vwtD W W' : (vwt (W + W') <= vwt W + vwt W')%N.
Proof.
apply: leq_trans (leq_card_setU _ _); apply/subset_leq_card/subsetP => i.
rewrite !inE mxE; apply: contraR; rewrite negb_or !negbK.
by case/andP => /eqP -> /eqP ->; rewrite addr0.
Qed.

Lemma vwt1 : vwt (const_mx 1) = t.
Proof.
rewrite /vwt -[RHS](card_ord t); apply: eq_card => i.
by rewrite !inE mxE oner_eq0.
Qed.

Lemma vwt0 : vwt 0 = 0%N.
Proof. by apply: eq_card0 => i; rewrite !inE mxE eqxx. Qed.

Lemma vwt_le W : (vwt W <= t)%N.
Proof. by apply: leq_trans (max_card _) _; rewrite card_ord. Qed.

(* The vertices of the nonzero rows of p carry the selected incidences;
   each edge of edgevec p has one of them at one end, and an incidence
   determines its edge. *)
Lemma ewt_edgevec p : (ewt (edgevec p) <= 99 * blk_deg p)%N.
Proof.
pose A := [set ij : 'I_t * 'I_99 | p ij.1 ij.2 != 0].
have hA : (#|A| <= 99 * blk_deg p)%N.
  rewrite mulnC; apply: (@leq_trans #|setX [set i : 'I_t | row i p != 0]
    [set: 'I_99]|).
    apply/subset_leq_card/subsetP => -[i j]; rewrite !inE /= andbT => h.
    by apply: contra h => /eqP /rowP /(_ j); rewrite !mxE => ->.
  by rewrite cardsX cardsT card_ord.
apply: leq_trans hA.
pose g (e : 'I_100 * 'I_l) : 'I_t * 'I_99 :=
  if insub (val e.1) is Some j' then
    (if p (lshift l e.2) j' != 0 then (lshift l e.2, j')
     else (rshift l (sigma e.1 e.2), j'))
  else (lshift l e.2, ord0).
set S := [set e : 'I_100 * 'I_l | edgevec p e.1 e.2 != 0].
have Sj e : e \in S -> exists j' : 'I_99, val e.1 = val j'.
  rewrite inE mxE; case: insubP => [j' _ ej _|_]; last by rewrite eqxx.
  by exists j'.
have inj : {in S &, injective g}.
  move=> [j1 u1] [j2 u2] h1 h2; have [j1' /= e1] := Sj _ h1.
  have [j2' /= e2] := Sj _ h2; rewrite /g /=.
  case: insubP => [k1 _ ek1|]; last by rewrite e1 ltn_ord.
  case: insubP => [k2 _ ek2|]; last by rewrite e2 ltn_ord.
  have jj (h : k1 = k2) : j1 = j2 by apply: ord_inj; rewrite -ek1 -ek2 h.
  case: ifP => _; case: ifP => _ h;
    have /= hu := congr1 fst h; have /= hk := congr1 snd h.
  - by rewrite (jj hk) (lshift_inj hu).
  - by move/eqP: hu; rewrite eq_lrshift.
  - by move/eqP: hu; rewrite eq_rlshift.
  - by move: hu; rewrite (jj hk) => /rshift_inj /perm_inj ->.
rewrite /ewt -/S -(card_in_imset inj).
apply/subset_leq_card/subsetP => _ /imsetP[e eS ->].
move: eS; rewrite /g inE mxE; case: insubP => [j' _ ej|_]; last first.
  by rewrite eqxx.
case: ifP => hl /=; rewrite inE //=.
by move: hl => /negbFE /eqP ->; rewrite add0r.
Qed.

Section expansion.
Hypothesis hexp : forall W : {set 'I_t},
  (minn #|W| (t - #|W|) <= #|perm_cut sigma W|)%N.

(* Connectivity: a set with an empty cut is empty or everything. *)
Lemma cutvec_eq0 W : cutvec W = 0 -> W = 0 \/ W = const_mx 1.
Proof.
move=> c0; have : perm_cut sigma (vsupp W) = set0.
  by apply/eqP; rewrite -cards_eq0 -ewt_cutvec c0 ewt0.
case/(perm_cut_eq0 (hexp _)) => h; [left|right]; apply/rowP => i;
  move/setP: h => /(_ i); rewrite !inE !mxE.
- by move/negbFE/eqP.
- by case: (F2_cases (W 0 i)) => -> //; rewrite eqxx.
Qed.

(* Two sets with the same cut and small total size are equal. *)
Lemma cut_unique W W' : cutvec W = cutvec W' -> (vwt W + vwt W' < t)%N ->
  W = W'.
Proof.
move=> e h; have : cutvec (W + W') = 0.
  by rewrite cutvecD e -[X in X + _]oppmxF2 addNr.
case/cutvec_eq0 => [/eqP|h1]; first by rewrite addmxF2_eq0 => /eqP.
by have := leq_ltn_trans (vwtD W W') h; rewrite h1 vwt1 ltnn.
Qed.


Lemma vsuppC W : vsupp (W + const_mx 1) = ~: vsupp W.
Proof.
apply/setP => i; rewrite !inE !mxE.
by case: (F2_cases (W 0 i)) => ->; rewrite ?add0r ?addF2_11 ?eqxx ?oner_eq0.
Qed.

Section sides.
Variables (R : realType) (b : vset) (D : nat).
Hypothesis hD : (1000 * D <= t)%N.
Hypothesis hD1 : (0 < D)%N.

Let t0 : (0 < t)%N.
Proof. by apply: leq_trans hD; rewrite muln_gt0 hD1. Qed.

(* A side of the cut edgevec p of size at most t / 5, if there is one. *)
Definition small_side (p : cube) : option vset :=
  [pick W : vset | (cutvec W == edgevec p) && (5 * vwt W <= t)%N].

(* The value of the functional on the character of p: the sign of b on the
   small side of edgevec p, when p has block degree at most 2 D and
   edgevec p is a cut, and 0 otherwise. *)
Definition sideval (p : cube) : R :=
  if (blk_deg p <= 2 * D)%N then
    (if small_side p is Some W then bchar R b W else 0)
  else 0.

(* A cut with at most 2 D (d - 1) edges has a side of size at most t / 5. *)
Lemma small_exists p W : (blk_deg p <= 2 * D)%N -> cutvec W = edgevec p ->
  exists W0, cutvec W0 = edgevec p /\ (5 * vwt W0 <= t)%N.
Proof.
move=> bp cW.
have hw : (minn (vwt W) (t - vwt W) <= 99 * (2 * D))%N.
  apply: leq_trans (hexp (vsupp W)) _; rewrite -ewt_cutvec cW.
  by apply: leq_trans (ewt_edgevec p) _; rewrite leq_mul2l bp orbT.
have h5 : (5 * (99 * (2 * D)) <= t)%N.
  by apply: leq_trans hD; rewrite !mulnA leq_mul2r orbC.
case: (leqP (vwt W) (t - vwt W)) => hm.
  exists W; split => //; apply: leq_trans h5; rewrite leq_mul2l.
  by move: hw; rewrite (minn_idPl hm) => ->; rewrite orbT.
exists (W + const_mx 1); rewrite cutvecD cutvec1 addr0; split => //.
apply: leq_trans h5; rewrite leq_mul2l; apply/orP; right.
move: hw; rewrite (minn_idPr (ltnW hm)) => hw.
by rewrite /vwt vsuppC cardsCs setCK card_ord.
Qed.

Lemma small_sum W W' : (5 * vwt W <= t)%N -> (5 * vwt W' <= t)%N ->
  (vwt W + vwt W' < t)%N.
Proof.
move=> h1 h2; rewrite -(ltn_pmul2l (isT : (0 < 5)%N)) mulnDr.
apply: leq_ltn_trans (leq_add h1 h2) _.
by rewrite addnn -mul2n ltn_pmul2r.
Qed.

Lemma sideval_cut p W : (blk_deg p <= 2 * D)%N -> cutvec W = edgevec p ->
  (5 * vwt W <= t)%N -> sideval p = bchar R b W.
Proof.
move=> bp cW sW; rewrite /sideval bp /small_side.
case: pickP => [W0 /andP[/eqP c0 s0] | none]; last first.
  by have := none W; rewrite cW eqxx sW.
by rewrite (cut_unique (_ : cutvec W0 = cutvec W)) ?cW // small_sum.
Qed.

Lemma sideval_nocut p : (forall W, cutvec W != edgevec p) -> sideval p = 0.
Proof.
move=> nc; rewrite /sideval /small_side; case: ifP => // _.
by case: pickP => [W0 /andP[c0 _]|//]; rewrite (negbTE (nc W0)) in c0.
Qed.

Lemma sideval_big p : (2 * D < blk_deg p)%N -> sideval p = 0.
Proof. by move=> h; rewrite /sideval leqNgt h. Qed.

Lemma sideval0 : sideval 0 = 1.
Proof.
have b0 : (blk_deg (0 : cube) <= 2 * D)%N.
  by rewrite /blk_deg (_ : [set _ | _] = set0) ?cards0 //; apply/setP => i;
    rewrite !inE row0 eqxx.
have c00 : cutvec 0 = edgevec 0 by rewrite cutvec0 edgevec0.
have s00 : (5 * vwt 0 <= t)%N by rewrite vwt0.
by rewrite (sideval_cut b0 c00 s00) bcharC bchar0.
Qed.

Lemma sideval_norm p : `|sideval p| <= 1.
Proof.
rewrite /sideval; case: ifP => _; last by rewrite normr0.
case: small_side => [W|]; last by rewrite normr0.
by case: (bchar_sign R b W) => ->; rewrite ?normr1 ?normrN1.
Qed.

(* The cocycle identity: if edgevec (p + q) and edgevec (q + r) are cuts,
   then the small side of edgevec (p + r) is the sum of their small sides. *)
Lemma sideval_cocycle p q r :
  (blk_deg (p + q) <= 2 * D)%N -> (blk_deg (q + r) <= 2 * D)%N ->
  (blk_deg (p + r) <= 2 * D)%N ->
  (exists W, cutvec W = edgevec (p + q)) ->
  (exists W, cutvec W = edgevec (q + r)) ->
  sideval (p + r) = sideval (p + q) * sideval (q + r).
Proof.
move=> b1 b2 b3 [V1 c1] [V2 c2].
have [W1 [e1 s1]] := small_exists b1 c1.
have [W2 [e2 s2]] := small_exists b2 c2.
have epr : edgevec (p + r) = cutvec (W1 + W2).
  rewrite cutvecD e1 e2 -edgevecD; congr edgevec.
  by rewrite [RHS]addrA addmxF2K.
have [W3 [e3 s3]] := small_exists b3 (esym epr).
have W3E : W3 = W1 + W2.
  apply: cut_unique; first by rewrite e3 epr.
  apply: leq_ltn_trans (leq_add (leqnn _) (vwtD W1 W2)) _.
  rewrite -(ltn_pmul2l (isT : (0 < 5)%N)) !mulnDr.
  apply: leq_ltn_trans (leq_add s3 (leq_add s1 s2)) _.
  have -> : (t + (t + t) = 3 * t)%N by rewrite !mulSn mul0n addn0.
  by rewrite -mulnDr ltn_mul2r t0.
by rewrite (sideval_cut b3 e3 s3) (sideval_cut b1 e1 s1)
  (sideval_cut b2 e2 s2) W3E bcharDr.
Qed.


(* ## The functional *)

Local Notation N := (#|{: cube}|%:R : R).

Definition parity_phi (h : cube -> R^o) : R :=
  \sum_(p : cube) fcoef h p * sideval p.

(* The kernel of the functional: Phi h = N^-1 sum_y h y K y. *)
Definition phi_kernel (y : cube) : R := \sum_(p : cube) bchar R p y * sideval p.

Lemma parity_phiE h :
  parity_phi h = N^-1 * \sum_(y : cube) h y * phi_kernel y.
Proof.
rewrite /parity_phi /fcoef /phi_kernel.
have sE (x : R) (v : R^o) : x *: v = x * v :> R by [].
under eq_bigr => p _ do rewrite sE -mulrA mulr_suml.
rewrite -mulr_sumr exchange_big /=; congr (_ * _).
apply: eq_bigr => y _; rewrite mulr_sumr; apply: eq_bigr => p _.
by rewrite sE mulrA [bchar R p y * _]mulrC.
Qed.

Lemma eq_parity_phi g h : g =1 h -> parity_phi g = parity_phi h.
Proof. by move=> gh; rewrite !parity_phiE; under eq_bigr do rewrite gh. Qed.

Lemma parity_phiD g h :
  parity_phi (fun y => g y + h y) = parity_phi g + parity_phi h.
Proof.
rewrite !parity_phiE -mulrDr -big_split /=; congr (_ * _).
by apply: eq_bigr => y _; rewrite mulrDl.
Qed.

Lemma parity_phiZ c h : parity_phi (fun y => c * h y) = c * parity_phi h.
Proof.
rewrite !parity_phiE mulrCA; congr (_ * _); rewrite mulr_sumr.
by apply: eq_bigr => y _; rewrite mulrA.
Qed.

Lemma parity_phi_sum (I : finType) (F : I -> cube -> R^o) :
  parity_phi (fun y => \sum_(i : I) F i y) = \sum_(i : I) parity_phi (F i).
Proof.
rewrite parity_phiE; under eq_bigr do rewrite mulr_suml.
rewrite exchange_big /= mulr_sumr; apply: eq_bigr => i _.
by rewrite parity_phiE.
Qed.

Lemma fcoef_char (q p : cube) :
  fcoef (fun y => bchar R q y : R^o) p = (p == q)%:R.
Proof.
have sE (x : R) (v : R^o) : x *: v = x * v :> R by [].
rewrite /fcoef sE; under eq_bigr do rewrite sE.
rewrite bchar_orthogonal; case: eqP => _; last by rewrite mulr0.
by rewrite mulVf // card_cube_neq0.
Qed.

Lemma parity_phi_char q : parity_phi (fun y => bchar R q y) = sideval q.
Proof.
rewrite /parity_phi; under eq_bigr do rewrite fcoef_char.
rewrite (bigD1 q) //= eqxx mul1r big1 ?addr0 // => p pq.
by rewrite (negbTE pq) mul0r.
Qed.

Lemma parity_phi_cst c : parity_phi (fun _ => c) = c.
Proof.
transitivity (parity_phi (fun y => c * bchar R 0 y)).
  by apply: eq_parity_phi => y; rewrite bchar0 mulr1.
by rewrite parity_phiZ parity_phi_char sideval0 mulr1.
Qed.

Lemma parity_phi_norm h c : (forall y, `|h y : R| <= c) ->
  `|parity_phi h| <= N * c.
Proof.
move=> hc; rewrite /parity_phi.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: (@le_trans _ _ (\sum_(p : cube) c)).
  2: by rewrite sumr_const mulr_natl.
apply: ler_sum => p _; rewrite normrM.
have fc := fcoef_norm_le p hc.
apply: le_trans _ fc; rewrite -[X in _ <= X]mulr1.
by apply: ler_wpM2l; [exact: normr_ge0 | exact: sideval_norm].
Qed.


(* ## The value on f_eps *)

Lemma last_pos (j : 'I_100) : ~~ (val j < 99)%N -> j = ord_max.
Proof.
move=> h; apply: ord_inj => /=; apply/eqP.
by rewrite eqn_leq -ltnS ltn_ord leqNgt h.
Qed.

Lemma inc_bit_free y (i : 'I_t) (j : 'I_100) (j' : 'I_99) : val j = val j' ->
  inc_bit b y i j = y i j'.
Proof.
move=> e; rewrite /inc_bit /cell_bit.
case: insubP => [k _ ek|]; last by rewrite e ltn_ord.
by rewrite mxE; congr (y i _); apply: val_inj; rewrite ek e.
Qed.

Lemma inc_bit_last y (i : 'I_t) :
  inc_bit b y i ord_max = b 0 i + \sum_(j' < 99) y i j'.
Proof.
rewrite /inc_bit /cell_bit insubF ?ltnn //; congr (_ + _).
by apply: eq_bigr => j' _; rewrite mxE.
Qed.

(* The frequency with row i full of ones. *)
Definition rowones (i : 'I_t) : cube := \matrix_(i', j') (i' == i)%:R.

Lemma bdot_rowones (i : 'I_t) y : bdot (rowones i) y = \sum_(j' < 99) y i j'.
Proof.
rewrite /bdot (bigD1 i) //=.
have -> : \sum_(i' < t | i' != i) \sum_(j < 99) rowones i i' j * y i' j = 0.
  by apply: big1 => i' ni; apply: big1 => j _; rewrite mxE (negbTE ni) mul0r.
by rewrite addr0; apply: eq_bigr => j _; rewrite mxE eqxx mul1r.
Qed.

Lemma sign_dis (x x' : 'F_2) :
  2 * (x != x')%:R = 1 - (-1) ^+ nat_of_ord (x + x') :> R.
Proof.
case: (F2_cases x) => ->; case: (F2_cases x') => ->;
  rewrite ?addr0 ?add0r ?addF2_11 ?eqxx ?oner_eq0 ?(eq_sym (0 : 'F_2) 1)
    ?oner_eq0 ?natF2_0 ?natF2_1 ?expr0 ?expr1 /=; lra.
Qed.

Lemma char_free (u : 'I_l) (j : 'I_100) (j' : 'I_99) y : val j = val j' ->
  (-1) ^+ nat_of_ord (inc_bit b y (lshift l u) j +
    inc_bit b y (rshift l (sigma j u)) j) =
  bchar R (delta_mx (lshift l u) j' + delta_mx (rshift l (sigma j u)) j') y.
Proof.
move=> e; rewrite !(inc_bit_free _ _ e) /bchar bdotDl.
by rewrite !(bdotC (delta_mx _ _)) !bdot_delta.
Qed.

Lemma char_last (u : 'I_l) y :
  (-1) ^+ nat_of_ord (inc_bit b y (lshift l u) ord_max +
    inc_bit b y (rshift l (sigma ord_max u)) ord_max) =
  (-1) ^+ nat_of_ord (b 0 (lshift l u) + b 0 (rshift l (sigma ord_max u))) *
  bchar R (rowones (lshift l u) + rowones (rshift l (sigma ord_max u))) y
  :> R.
Proof.
by rewrite !inc_bit_last addrACA [LHS]signF2D /bchar bdotDl !bdot_rowones.
Qed.

Lemma blk_deg_two (q : cube) (i1 i2 : 'I_t) :
  (forall i, i != i1 -> i != i2 -> row i q = 0) -> (blk_deg q <= 2 * D)%N.
Proof.
move=> h; apply: (@leq_trans #|[set i1; i2]|).
  apply: subset_leq_card; apply/subsetP => i; rewrite !inE; apply: contraR.
  by rewrite negb_or => /andP[n1 n2]; rewrite h // eqxx.
rewrite cards2; apply: (@leq_trans 2); first by case: (i1 != i2).
by rewrite -[X in (X <= _)%N]muln1 leq_mul2l hD1 orbT.
Qed.

Lemma sideval_free (u : 'I_l) (j : 'I_100) (j' : 'I_99) : val j = val j' ->
  sideval (delta_mx (lshift l u) j' + delta_mx (rshift l (sigma j u)) j') = 1.
Proof.
move=> e; set q := _ + _.
have bq : (blk_deg q <= 2 * D)%N.
  apply: (@blk_deg_two _ (lshift l u) (rshift l (sigma j u))) => i n1 n2.
  by apply/rowP => k; rewrite !mxE (negbTE n1) (negbTE n2) /= addr0.
have eq0 : cutvec 0 = edgevec q.
  rewrite cutvec0; apply/matrixP => j2 u2; rewrite [RHS]mxE [LHS]mxE.
  case: insubP => [k _ ek|_] //; rewrite !mxE.
  case: (eqVneq k j') => [kj|kj]; last first.
    by rewrite /= ?andbF /= ?mulr0n ?addr0.
  have jj : j2 = j by apply: ord_inj; rewrite -ek kj e.
  rewrite jj eq_lshift eq_lrshift eq_rlshift eq_rshift.
  rewrite (inj_eq (@perm_inj _ (sigma j))) /= ?andbT ?mulr0n ?addr0 ?add0r.
  by rewrite F2_double.
have s0 : (5 * vwt 0 <= t)%N by rewrite vwt0.
by rewrite (sideval_cut bq eq0 s0) bcharC bchar0.
Qed.

Lemma sideval_last (u : 'I_l) :
  sideval (rowones (lshift l u) + rowones (rshift l (sigma ord_max u))) =
  (-1) ^+ nat_of_ord (b 0 (lshift l u) + b 0 (rshift l (sigma ord_max u))).
Proof.
set i1 := lshift l u; set i2 := rshift l (sigma ord_max u).
set q := _ + _; pose V : vset := delta_mx 0 i1 + delta_mx 0 i2.
have bq : (blk_deg q <= 2 * D)%N.
  apply: (@blk_deg_two _ i1 i2) => i n1 n2.
  by apply/rowP => k; rewrite !mxE (negbTE n1) (negbTE n2) addr0.
have cV : cutvec V = edgevec q.
  apply/matrixP => j2 u2; rewrite [RHS]mxE [LHS]mxE.
  case: insubP => [k _ ek|nk]; first by rewrite !mxE.
  rewrite (last_pos nk) !mxE /i1 /i2 !eqxx /= eq_lshift eq_lrshift eq_rlshift.
  rewrite eq_rshift (inj_eq (@perm_inj _ (sigma ord_max))) /= ?mulr0n.
  by rewrite ?addr0 ?add0r F2_double.
have sV : (5 * vwt V <= t)%N.
  apply: (@leq_trans (5 * 2)).
    rewrite leq_mul2l; apply/orP; right; apply: (@leq_trans #|[set i1; i2]|).
      apply: subset_leq_card; apply/subsetP => i; rewrite !inE !mxE /=.
      by apply: contraR; rewrite negb_or => /andP[/negbTE -> /negbTE ->].
    by rewrite cards2; case: (i1 != i2).
  by apply: (leq_trans _ hD); rewrite (@leq_trans 1000) // leq_pmulr.
by rewrite (sideval_cut bq cV sV) /bchar bdotDr !bdot_delta.
Qed.


(* The sign (-1)^(x + x') of an edge has value 1: its frequency has block
   degree at most 2 and edgevec the cut of the empty set (a free position)
   or of the two ends (the parity position). *)
Lemma parity_phi_sign (j : 'I_100) (u : 'I_l) :
  parity_phi (fun y => (-1) ^+ nat_of_ord (inc_bit b y (lshift l u) j +
    inc_bit b y (rshift l (sigma j u)) j) : R^o) = 1.
Proof.
case: (ltnP (val j) 99) => hj.
  pose j' : 'I_99 := Ordinal hj; have e : val j = val j' by [].
  transitivity (parity_phi (fun y => bchar R
      (delta_mx (lshift l u) j' + delta_mx (rshift l (sigma j u)) j') y)).
    by apply: eq_parity_phi => y; exact: char_free.
  by rewrite parity_phi_char sideval_free.
have jm : j = ord_max by apply: last_pos; rewrite -leqNgt.
rewrite jm; pose c : R :=
  (-1) ^+ nat_of_ord (b 0 (lshift l u) + b 0 (rshift l (sigma ord_max u))).
transitivity (parity_phi (fun y => c * bchar R (rowones (lshift l u) +
    rowones (rshift l (sigma ord_max u))) y)).
  by apply: eq_parity_phi => y; rewrite char_last.
rewrite parity_phiZ parity_phi_char sideval_last /c -signF2D F2_double.
by rewrite natF2_0 expr0.
Qed.

(* Every disagreement indicator has value 0, so Phi f_eps = - eps. *)
Lemma parity_phi_feps eps : parity_phi (f_eps sigma b eps) = - eps.
Proof.
pose dis (e : 'I_100 * 'I_l) (y : cube) : R^o :=
  (inc_bit b y (lshift l e.2) e.1 !=
   inc_bit b y (rshift l (sigma e.1 e.2)) e.1)%:R.
have hdis e : parity_phi (dis e) = 0.
  have h2 : 2 * parity_phi (dis e) = 0.
    rewrite -parity_phiZ.
    transitivity (parity_phi (fun y => 1 + (-1) * ((-1) ^+ nat_of_ord
      (inc_bit b y (lshift l e.2) e.1 +
       inc_bit b y (rshift l (sigma e.1 e.2)) e.1) : R^o))).
      by apply: eq_parity_phi => y; rewrite /dis sign_dis mulN1r.
    by rewrite parity_phiD parity_phi_cst parity_phiZ parity_phi_sign
      mulN1r subrr.
  by move/eqP: h2; rewrite mulf_eq0 pnatr_eq0 /= => /eqP.
transitivity (parity_phi (fun y => \sum_(e : 'I_100 * 'I_l) dis e y + - eps)).
  apply: eq_parity_phi => y; rewrite /f_eps /disagreements; congr (_ - _).
  rewrite -sum1_card natr_sum big_mkcond /=; apply: eq_bigr => e _.
  by rewrite inE /dis; case: (_ != _).
by rewrite parity_phiD parity_phi_sum parity_phi_cst big1 ?add0r.
Qed.


(* ## Positivity on squares of low block degree *)

(* p and q are related when edgevec (p + q) is a cut: an equivalence. *)
Definition cut_rel (p q : cube) : bool :=
  [exists W : vset, cutvec W == edgevec (p + q)].

Lemma cut_rel_refl (p : cube) : cut_rel p p.
Proof.
have pp : p + p = 0 by apply/eqP; rewrite addmxF2_eq0.
by apply/existsP; exists 0; rewrite cutvec0 pp edgevec0.
Qed.

Lemma cut_rel_sym (p q : cube) : cut_rel p q = cut_rel q p.
Proof. by rewrite /cut_rel addrC. Qed.

Lemma cut_rel_trans (p q r : cube) : cut_rel p q -> cut_rel q r -> cut_rel p r.
Proof.
move=> /existsP[W1 /eqP e1] /existsP[W2 /eqP e2]; apply/existsP.
exists (W1 + W2); rewrite cutvecD e1 e2 -edgevecD.
by rewrite [p + q + _]addrA addmxF2K.
Qed.

Lemma blk_degD (p q : cube) : (blk_deg (p + q) <= blk_deg p + blk_deg q)%N.
Proof.
rewrite -blk_distE; apply: leq_trans (blk_dist_triangle p 0 q) _.
by rewrite !blk_distE addr0 add0r.
Qed.

(* The representative of the class of p among the frequencies of block
   degree at most D, and the sign of p relative to it. *)
Definition class_rep (p : cube) : cube :=
  odflt 0 [pick q : cube | (blk_deg q <= D)%N && cut_rel p q].

Definition class_sign (p : cube) : R := sideval (p + class_rep p).

Lemma class_rep_spec (p : cube) : (blk_deg p <= D)%N ->
  (blk_deg (class_rep p) <= D)%N /\ cut_rel p (class_rep p).
Proof.
move=> bp; rewrite /class_rep; case: pickP => [q /andP[bq cq] | none] //=.
by have := none p; rewrite bp cut_rel_refl.
Qed.

Lemma class_rep_eq (p q : cube) : cut_rel p q -> class_rep p = class_rep q.
Proof.
move=> cpq; rewrite /class_rep; congr (odflt _ _); apply: eq_pick => r /=.
congr (_ && _); apply/idP/idP => h.
- by apply: cut_rel_trans h; rewrite cut_rel_sym.
- exact: cut_rel_trans cpq h.
Qed.

Lemma sideval_class (p q : cube) : (blk_deg p <= D)%N -> (blk_deg q <= D)%N ->
  sideval (p + q) =
  (class_rep p == class_rep q)%:R * class_sign p * class_sign q.
Proof.
move=> bp bq.
have b2 (p' q' : cube) : (blk_deg p' <= D)%N -> (blk_deg q' <= D)%N ->
    (blk_deg (p' + q') <= 2 * D)%N.
  move=> h1 h2; apply: (leq_trans (blk_degD p' q')).
  by rewrite mul2n -addnn leq_add.
have [rp cp] := class_rep_spec bp; have [rq cq] := class_rep_spec bq.
case: (eqVneq (class_rep p) (class_rep q)) => [e|ne].
  rewrite mul1r /class_sign -e.
  have cutp : exists W, cutvec W = edgevec (p + class_rep p).
    by move/existsP: cp => [W /eqP]; exists W.
  have cutq : exists W, cutvec W = edgevec (class_rep p + q).
    move: cq; rewrite cut_rel_sym -e => /existsP[W /eqP cW]; exists W.
    by rewrite cW.
  rewrite (sideval_cocycle (b2 _ _ bp rp) (b2 _ _ rp bq) (b2 _ _ bp bq)
    cutp cutq).
  by rewrite [class_rep p + q]addrC.
rewrite mul0r mul0r; apply: sideval_nocut => W; apply/negP => /eqP cW.
have : cut_rel p q by apply/existsP; exists W; rewrite cW.
by move/class_rep_eq => e; rewrite e eqxx in ne.
Qed.

Lemma parity_phi_sqr (g : cube -> R^o) : low_blk_deg D g ->
  0 <= parity_phi (fun y => g y ^+ 2).
Proof.
move=> lowg.
pose c (p : cube) : R := if (blk_deg p <= D)%N then fcoef g p else 0.
have gE y : g y = \sum_(p : cube) bchar R p y * c p.
  rewrite (proj1 (low_blk_deg_expansion _ _) lowg y) big_mkcond /=.
  by apply: eq_bigr => p _; rewrite /c; case: ifP => _; rewrite ?mulr0.
have sqE y : g y ^+ 2 =
    \sum_(p : cube) \sum_(q : cube) c p * c q * bchar R (p + q) y.
  rewrite expr2 {1}gE mulr_suml; apply: eq_bigr => p _.
  rewrite gE mulr_sumr; apply: eq_bigr => q _.
  by rewrite bcharD mulrACA mulrC.
rewrite (eq_parity_phi sqE) parity_phi_sum.
under eq_bigr do rewrite parity_phi_sum.
under eq_bigr do under eq_bigr do rewrite parity_phiZ parity_phi_char.
(* Regroup into squares over the classes. *)
pose x (p : cube) : R := c p * class_sign p.
pose Sc (r : cube) : R := \sum_(q : cube | class_rep q == r) x q.
have eqS : \sum_(p : cube) \sum_(q : cube) c p * c q * sideval (p + q) =
    \sum_(r : cube) (\sum_(p : cube | class_rep p == r) x p) ^+ 2.
  transitivity (\sum_(p : cube) x p * Sc (class_rep p)).
    apply: eq_bigr => p _; rewrite mulr_sumr [RHS]big_mkcond /=.
    apply: eq_bigr => q _.
    case: (boolP (blk_deg p <= D)%N) => bp; last first.
      by rewrite /x /c (negbTE bp) !mul0r; case: ifP.
    case: (boolP (blk_deg q <= D)%N) => bq; last first.
      by rewrite /x /c (negbTE bq) mulr0 !mul0r mulr0; case: ifP.
    rewrite (sideval_class bp bq) eq_sym /x.
    by case: ifP => _ /=; rewrite ?mulr1n ?mulr0n ?mul1r ?mul0r ?mulr0 //;
      rewrite mulrACA.
  rewrite (partition_big class_rep (fun _ => true)) //=.
  apply: eq_bigr => r _; rewrite expr2 mulr_suml.
  by apply: eq_big => [p|p /eqP ->] //=.
by rewrite eqS; apply: sumr_ge0 => r _; exact: sqr_ge0.
Qed.

End sides.

End expansion.
End graph.

(* The parity functional of the proposition 'Parity functional', at block
   degree D = t %/ 1000 for t = l + l >= 1000 cells (departure 1). *)
Lemma parity_functional_holds (R : realType) (l : nat)
    (sigma : 'I_100 -> {perm 'I_l}) (b : 'rV['F_2]_(l + l)) (eps : R) :
  (forall W : {set 'I_(l + l)},
     (minn #|W| (l + l - #|W|) <= #|perm_cut sigma W|)%N) ->
  (1000 <= l + l)%N ->
  parity_functional ((l + l) %/ 1000) eps (f_eps sigma b eps).
Proof.
move=> hexp ht; set D := ((l + l) %/ 1000)%N.
have hD : (1000 * D <= l + l)%N by rewrite mulnC leq_divM.
have hD1 : (0 < D)%N by rewrite divn_gt0.
exists (parity_phi sigma b D); split.
- by move=> g h; exact: parity_phiD.
- by move=> c g; exact: parity_phiZ.
- by move=> g lg; apply: parity_phi_sqr.
- by apply: parity_phi_feps.
- move=> h c hc; rewrite -natrX -card_cube.
  exact: parity_phi_norm.
Qed.
