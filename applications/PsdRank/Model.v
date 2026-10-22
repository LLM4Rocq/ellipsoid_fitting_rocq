From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix reals.
From mathcomp Require Import fingroup perm zmodp.
From GaussianAnalysis.matrix Require Import psd_part psd_factorization.
From GaussianApplications Require Import PsdRankDefinitions PsdRankStatement.
From GaussianApplications Require Import PsdLiftDefinitions.

(**md**************************************************************************)
(* # PSD rank of shifted matching matrices: the model                         *)
(*                                                                            *)
(* Sanity lemmas for the definitions of PsdRankDefinitions.v, reviewed with   *)
(* the PSD main statement (batch 3 of phase 13; AGENTS.md, section Phase 13)  *)
(* and not frozen. Phase 14 adds here the rest of the model of the proof.     *)
(* From 'Exponential PSD rank of positively shifted matching matrices'        *)
(* (family 126 of the OpenAI math collection, revision 1581d4cbd,             *)
(* source/sections/introduction.tex, lines 12-23 and 46-50); a Rocq           *)
(* formalization of the credited arguments. The Lean development of the       *)
(* collection has the parity count and the diagonal factorization:            *)
(* Lean: cut_degree_identity, crossingCount_pos (FiniteFactorization.lean)    *)
(* Lean: exists_diagonal_factorization (FiniteFactorization.lean, line 69)    *)
(*                                                                            *)
(* - matching_count: |U| = sum_(e in M) |e cap U| for every set U of        *)
(*   vertices and every perfect matching M; card_perfect_matching: M has n/2  *)
(*   edges.                                                                   *)
(* - crossing_odd: a perfect matching crosses an odd set an odd number of     *)
(*   times; crossing_le: at most n times.                                     *)
(* - shifted_matching_mx_ge, shifted_matching_mx_le: every entry of A_n(rho)  *)
(*   is at least rho, and at most n if rho <= 1.                              *)
(* - card_kn_edges: K_n has 'C(n, 2) edges.                                   *)
(* - shifted_matching_one_factorization: A_n(1) has a PSD factorization of    *)
(*   size 'C(n, 2), by the diagonal matrices indexed by the edges with the    *)
(*   entries 1_(e in delta(U)) for a row and 1_(e in M) for a column.         *)
(* - psd_rank_closed_fails: hence psd_rank_statement with rho = 1 allowed     *)
(*   fails at every real type, since 'C(n, 2)^K < 2^n for large even n; the   *)
(*   exclusion of rho = 1 is necessary.                                       *)
(* - psd_rank_statementE: psd_rank_statement with the factors written out,    *)
(*   for the reviewer's comparison.                                           *)
(*                                                                            *)
(* The frame of the cells (phase 14), shared by the local averaging, the      *)
(* parity functional and the realization (AGENTS.md, section Phase 14; the    *)
(* plan notes/phase14-plan.md, section 4.3), with the encoding of the PSD     *)
(* audit (reviews/phase13-psd-audit/realization.md, lines 104-128 and         *)
(* 279-298). Not frozen and not reviewed by the user:                         *)
(* - cell_weight k b: w(b), the size in {k/2, k/2 + 1} congruent to the       *)
(*   charge b modulo 2 (local-averaging.tex, lines 12-21); cell_weight_odd:   *)
(*   it is odd exactly when b = 1; cell_weight_bounds.                        *)
(* - cell_bit b y j: the full bit j of a cell of charge b with free bits y:   *)
(*   the free bits, then the parity bit b + (the sum of the free bits).       *)
(* - cell_support b m y x: the support of the restrictions of a cell with     *)
(*   local data m (terminal j at m j, internal pairs after the terminals):    *)
(*   #|x| = w(b), terminal j in x exactly when its full bit is 1, and each    *)
(*   internal pair inside or outside x (local-averaging.tex, lines 28-36).    *)
(* - inc_bit b y i j, disagreements sigma b y and f_eps sigma b eps y: on     *)
(*   the cells 'I_(l + l) of the graph H of 100 permutations sigma j of 'I_l, *)
(*   whose edge (j, u) joins the cells lshift l u and rshift l (sigma j u) at *)
(*   position j, the incidence bit, the number of edges whose two incidence   *)
(*   bits differ, and f_eps(y) = disagreements - eps.                         *)
(*                                                                            *)
(* Matchings from pairings (phase 14, item A1):                               *)
(* - pairing p: p is a fixed-point-free involution of 'I_n; pairing_edges p:  *)
(*   the edges {v, p v}; pairing_perfect: they form a perfect matching,       *)
(*   pairing_matching; pairing_crossing: it crosses an odd set U once for     *)
(*   each v of U with p v outside U.                                          *)
(* - std_partner, std_pairing, std_matching: for even n, the pairs            *)
(*   {2q, 2q + 1} give a perfect matching.                                    *)
(* - cards2I: #|{x, y} cap A| = [x in A] + [y in A] for x != y.               *)
(*                                                                            *)
(* The finite type kn_edges n of the edges of K_n is in                       *)
(* PsdLiftDefinitions.v (phase 14), whose statement uses it.                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section model.
Variable n : nat.

Lemma card_kn_edges : #|{: kn_edges n}| = 'C(n, 2).
Proof. by rewrite card_sig -cardsE card_draws card_ord. Qed.

(* Double counting: every vertex lies in exactly one edge of M, so
   |U| = sum_(e in M) |e cap U| for every set U of vertices. *)
Lemma matching_count (M : perfect_matching n) (U : {set 'I_n}) :
  #|U| = (\sum_(e in val M) #|e :&: U|)%N.
Proof.
case: M => M /= /andP[_ /forallP Mcov]; rewrite -sum1_card.
transitivity (\sum_(v in U) \sum_(e in M) (v \in e : nat))%N.
  apply: eq_bigr => v _; rewrite -(eqP (Mcov v)) -sum1_card.
  rewrite big_mkcond [RHS]big_mkcond /=.
  by apply: eq_bigr => e _; rewrite inE; case: (e \in M); case: (v \in e).
rewrite exchange_big /=; apply: eq_bigr => e _.
rewrite -sum1_card big_mkcond [RHS]big_mkcond /=.
by apply: eq_bigr => v _; rewrite inE; case: (v \in e); case: (v \in U).
Qed.

(* A perfect matching of K_n has n / 2 edges. *)
Lemma card_perfect_matching (M : perfect_matching n) : (#|val M|).*2 = n.
Proof.
have h := matching_count M [set: 'I_n]; rewrite cardsT card_ord in h.
rewrite [RHS]h; case: M {h} => M /= /andP[/forall_inP Medge _].
rewrite -muln2 -sum_nat_const; apply: eq_bigr => e eM.
by rewrite setIT (eqP (Medge e eM)).
Qed.

Lemma crossing_le (U : odd_set n) (M : perfect_matching n) :
  (crossing U M <= n)%N.
Proof.
apply: leq_trans (subset_leq_card (subsetIl _ _)) _.
by rewrite -[X in (_ <= X)%N](card_perfect_matching M) -addnn leq_addr.
Qed.

Lemma crossing_odd (U : odd_set n) (M : perfect_matching n) :
  odd (crossing U M).
Proof.
have sumU := matching_count M (val U).
case: U sumU => U oddU /= sumU; case: M sumU => M pM /= sumU.
rewrite /crossing /=; move: pM => /andP[/forall_inP Medge _].
have cut : M :&: edge_cut U = [set e in M | #|e :&: U| == 1]%N.
  apply/setP => e; rewrite !inE; case eM: (e \in M) => //=.
  by rewrite (Medge e eM).
have oddsum (A : {set {set 'I_n}}) (f : {set 'I_n} -> nat) :
    odd (\sum_(e in A) f e) = odd (\sum_(e in A) (odd (f e) : nat)).
  apply: (big_ind2 (fun a b => odd a = odd b)) => //.
    by move=> a1 a2 b1 b2 h1 h2; rewrite !oddD h1 h2.
  by move=> e _; rewrite oddb.
move: oddU; rewrite sumU oddsum cut.
(* an edge meets U in 0, 1 or 2 vertices *)
have -> : (\sum_(e in M) (odd #|e :&: U| : nat) =
    \sum_(e in M) (#|e :&: U| == 1 : nat))%N.
  apply: eq_bigr => e eM.
  have : (#|e :&: U| <= 2)%N.
    by rewrite -(eqP (Medge e eM)); exact/subset_leq_card/subsetIl.
  by case: #|e :&: U| => [|[|[|]]].
move=> h; rewrite -sum1_card big_mkcond /=; move: h; rewrite big_mkcond /=.
apply: eq_ind; apply: (congr1 odd); apply: eq_bigr => e _.
by rewrite inE; case: (e \in M).
Qed.

Lemma shifted_matching_mx_ge (R : realType) (rho : R) (U : odd_set n)
    (M : perfect_matching n) :
  rho <= shifted_matching_mx rho U M.
Proof.
rewrite /shifted_matching_mx lerDr subr_ge0 ler1n.
by have := crossing_odd U M; case: (crossing U M).
Qed.

Lemma shifted_matching_mx_le (R : realType) (rho : R) (U : odd_set n)
    (M : perfect_matching n) :
  rho <= 1 -> shifted_matching_mx rho U M <= n%:R.
Proof.
move=> r1; rewrite /shifted_matching_mx -addrA.
apply: le_trans (_ : (crossing U M)%:R + 0 <= _).
  by rewrite lerD2l addrC subr_le0.
by rewrite addr0 ler_nat crossing_le.
Qed.

Lemma shifted_matching_one_factorization (R : realType) :
  psd_factorization (@shifted_matching_mx n R 1) 'C(n, 2).
Proof.
rewrite -card_kn_edges.
pose a (U : odd_set n) (k : 'I_#|{: kn_edges n}|) : R :=
  (val (enum_val k) \in edge_cut (val U))%:R.
pose b (M : perfect_matching n) (k : 'I_#|{: kn_edges n}|) : R :=
  (val (enum_val k) \in val M)%:R.
exists (fun U => diag_mx (\row_k a U k)), (fun M => diag_mx (\row_k b M k)).
split => [U|M|U M].
- by apply: psdmx_diag => k; rewrite mxE ler0n.
- by apply: psdmx_diag => k; rewrite mxE ler0n.
rewrite mulmx_diag mxtrace_diag /shifted_matching_mx subrK.
under eq_bigr do rewrite !mxE.
rewrite /a /b (reindex (@enum_rank (kn_edges n))) /=.
  by apply: onW_bij; exact: enum_rank_bij.
under eq_bigr do rewrite enum_rankK -natrM.
rewrite -natr_sum /crossing; congr (_%:R).
(* the edges of M crossing U, as edges of K_n *)
set S := val M :&: edge_cut (val U).
have Sedge e : e \in S -> kn_edge e by rewrite !inE => /andP[_ /andP[]].
have -> : S = val @: [set x : kn_edges n | val x \in S].
  apply/setP => e; apply/idP/imsetP => [eS|[x]]; last by rewrite inE => xS ->.
  by exists (exist _ e (Sedge e eS)); rewrite // inE.
rewrite card_imset; first exact: val_inj.
rewrite -sum1_card big_mkcond /=; apply: eq_bigr => x _; rewrite !inE andbC.
by case: (kn_edge (sval x)); case: (_ == 1)%N; case: (sval x \in val M).
Qed.

End model.

(* The statement with the factors written out. *)
Lemma psd_rank_statementE : psd_rank_statement <->
  forall R : realType, exists K : nat, (0 < K)%N /\
  forall rho : R, 0 < rho < 1 ->
  exists n0 : nat, forall n : nat, ~~ odd n -> (n0 <= n)%N ->
  forall (r : nat) (F : odd_set n -> 'M[R]_r)
         (G : perfect_matching n -> 'M[R]_r),
    (forall U, psdmx (F U)) -> (forall M, psdmx (G M)) ->
    (forall U M, shifted_matching_mx rho U M = \tr (F U *m G M)) ->
    (2 ^ n <= r ^ K)%N.
Proof.
split=> h R; have [K [K0 hK]] := h R; exists K; split=> // rho rho01;
  have [n0 hn0] := hK rho rho01; exists n0 => n en n0n.
  by move=> r F G Fp Gp AE; apply: (hn0 n en n0n r); exists F, G.
by move=> r [F [G [Fp Gp AE]]]; exact: (hn0 n en n0n r F G Fp Gp AE).
Qed.

(* There are 2^|T| sets of elements of a finite type T. *)
Lemma card_set_type (T : finType) : #|{: {set T}}| = (2 ^ #|T|)%N.
Proof. by have := card_powerset [set: T]; rewrite powersetT !cardsT. Qed.

(* 'C(j, 2) <= 2^j: the sets of two elements of 'I_j are among its sets. *)
Lemma bin2_le_exp j : ('C(j, 2) <= 2 ^ j)%N.
Proof.
have := card_draws 'I_j 2; rewrite card_ord => <-.
by apply: leq_trans (max_card _) _; rewrite card_set_type card_ord.
Qed.

Lemma bin2_mul2 j : ('C(j, 2) * 2 = j * j.-1)%N.
Proof. by have := bin_ffact j 2; rewrite ffactnS ffactn1. Qed.

(* 2 K j < 2^j once j >= 4 K + 2. *)
Lemma lin_lt_exp K j : (4 * K + 2 <= j)%N -> (j * 2 * K < 2 ^ j)%N.
Proof.
move=> hj; apply: leq_trans (bin2_le_exp j).
rewrite -(ltn_pmul2r (isT : (0 < 2)%N)) bin2_mul2.
have -> : (j * 2 * K * 2 = j * (4 * K))%N.
  by rewrite -!mulnA; congr (_ * _)%N; rewrite mulnCA mulnC.
have j0 : (0 < j)%N by apply: leq_trans hj; rewrite addn2.
rewrite ltn_pmul2l //.
by case: j hj j0 => // j'; rewrite addn2 ltnS.
Qed.

(* For every K > 0 and every m there is an even n >= m with
   'C(n, 2)^K < 2^n. *)
Lemma bin2_pow_lt_exp K m : (0 < K)%N ->
  exists n, [/\ ~~ odd n, (m <= n)%N & ('C(n, 2) ^ K < 2 ^ n)%N].
Proof.
move=> K0; pose j := (m + (4 * K + 2))%N.
exists (2 ^ j)%N; split.
- by rewrite oddX /j addn2 !addnS.
- apply: leq_trans (ltnW (ltn_expl j (ltnSn 1))); exact: leq_addr.
- have bn : ('C(2 ^ j, 2) <= 2 ^ (j * 2))%N.
    apply: leq_trans (_ : 2 ^ j * (2 ^ j).-1 <= _)%N.
      by rewrite -bin2_mul2 leq_pmulr.
    by rewrite expnM -mulnn leq_mul2l leq_pred orbT.
  apply: leq_ltn_trans (_ : 2 ^ (j * 2 * K) < _)%N.
    by rewrite expnM leq_exp2r.
  by rewrite ltn_exp2l // lin_lt_exp // leq_addl.
Qed.

(* The statement with rho = 1 allowed fails at every real type: A_n(1) has
   a factorization of size 'C(n, 2) for every n. *)
Lemma psd_rank_closed_fails (R : realType) :
  ~ (exists K : nat, (0 < K)%N /\
     forall rho : R, 0 < rho <= 1 ->
     exists n0 : nat, forall n : nat, ~~ odd n -> (n0 <= n)%N ->
     forall r : nat, psd_factorization (@shifted_matching_mx n R rho) r ->
     (2 ^ n <= r ^ K)%N).
Proof.
move=> [K [K0 h]].
have [n0 hn0] := h 1 (andb_true_intro (conj ltr01 (lexx 1))).
have [n [en nn0 lt]] := bin2_pow_lt_exp n0 K0.
have := hn0 n en nn0 _ (shifted_matching_one_factorization n R).
by rewrite leqNgt lt.
Qed.

(* The frame of the cells (phase 14). The shared definitions of the local
   averaging (Cells.v), the parity functional (Parity.v) and the realization
   (Realization.v): one graph, one incidence order and one bit layout, with
   the encoding of the PSD audit (reviews/phase13-psd-audit/realization.md,
   lines 104-128 and 279-298; final.md, lines 496-517). A cell has the
   vertices 'I_k; its local data are a permutation m of 'I_k, with the
   terminal j at m j for j <= a and the q-th internal pair at m (a + 1 + 2q)
   and m (a + 2 + 2q); its free bits are a row of a bits. *)
Section cell_frame.
Variables (a k : nat).

(* w(b): the size in {k/2, k/2 + 1} congruent to the charge b modulo 2. *)
Definition cell_weight (b : 'F_2) : nat :=
  if odd (k %/ 2) == (b != 0) then k %/ 2 else (k %/ 2).+1.

(* The full bits of a cell of charge b with free bits y: the a free bits,
   then at position a the parity bit b + (the sum of the free bits). *)
Definition cell_bit (b : 'F_2) (y : 'rV['F_2]_a) (j : 'I_a.+1) : 'F_2 :=
  if insub (val j) is Some j' then y 0 j' else b + \sum_(j' < a) y 0 j'.

(* The support of the restrictions: x is in the support when #|x| = w(b),
   each terminal lies in x exactly when its full bit is 1, and each internal
   pair lies inside or outside x. *)
Definition cell_support (b : 'F_2) (m : {perm 'I_k}) (y : 'rV['F_2]_a)
    (x : {set 'I_k}) : bool :=
  [&& #|x| == cell_weight b,
      [forall j : 'I_a.+1, forall v : 'I_k,
         (val v == val j) ==> ((m v \in x) == (cell_bit b y j != 0))] &
      [forall v : 'I_k, forall u : 'I_k,
         [&& (a < v)%N, ~~ odd (v - a.+1)%N & val u == (val v).+1] ==>
           ((m v \in x) == (m u \in x))]].

End cell_frame.

(* The size of the local points is odd exactly when the charge is 1. *)
Lemma cell_weight_odd k (b : 'F_2) : odd (cell_weight k b) = (b != 0).
Proof.
rewrite /cell_weight; case: eqP => [-> //|].
by rewrite /=; case: (odd _); case: (b != 0).
Qed.

(* The size of the local points is k/2 or k/2 + 1. *)
Lemma cell_weight_bounds k (b : 'F_2) :
  (k %/ 2 <= cell_weight k b <= (k %/ 2).+1)%N.
Proof. by rewrite /cell_weight; case: ifP => _; rewrite leqnn ?leqnSn. Qed.

(* The graph H on the cells 'I_(l + l): 100 permutations sigma j of 'I_l;
   the edge (j, u) joins the cells lshift l u and rshift l (sigma j u), at
   position j at both ends. The charges are a row b of 'F_2 on the cells;
   the free bits of all the cells are a matrix y with a row of 99 bits per
   cell. t is written (l + l)%N: under the ring scope a bare l + l is the
   addition of the ring nat, which the lemmas on nat do not rewrite. *)
Section frame.
Variables (R : realType) (l : nat) (sigma : 'I_100 -> {perm 'I_l}).
Variable (b : 'rV['F_2]_(l + l)).
Local Notation t := (l + l)%N.
Local Notation cube := 'M['F_2]_(t, 99).

(* The incidence bit of cell i at position j: the full bit j of cell i. *)
Definition inc_bit (y : cube) (i : 'I_t) (j : 'I_100) : 'F_2 :=
  cell_bit (b 0 i) (row i y) j.

(* The number of edges of H whose two incidence bits differ. *)
Definition disagreements (y : cube) : nat :=
  #|[set e : 'I_100 * 'I_l |
      inc_bit y (lshift l e.2) e.1 != inc_bit y (rshift l (sigma e.1 e.2)) e.1]|.

(* f_eps(y) = (the number of disagreeing edges) - eps. *)
Definition f_eps (eps : R) (y : cube) : R^o := (disagreements y)%:R - eps.

End frame.

(* Matchings from pairings (item A1 of phase 14). A pairing of 'I_n is a
   fixed-point-free involution p; its edges {v, p v} form a perfect matching,
   and the matching crosses an odd set U once for each v of U whose partner
   lies outside U. For even n, the pairs {2q, 2q + 1} give one. The Lean
   development of the collection has the same conversion:
   Lean: fromPairing (MatchingConversion.lean, line 39)
   Lean: crossingCount_fromPairing (MatchingConversion.lean, line 89) *)

(* The points of A among two distinct points. *)
Lemma cards2I (T : finType) (x y : T) (A : {set T}) :
  x != y -> #|[set x; y] :&: A| = ((x \in A) + (y \in A))%N.
Proof.
move=> xy; rewrite (cardsD1 x) (cardsD1 y (_ :\ x)).
have -> : [set x; y] :&: A :\ x :\ y = set0.
  by apply/setP => z; rewrite !inE; case: (z =P y); case: (z =P x).
by rewrite cards0 addn0 !inE eqxx /= (eq_sym y x) (negbTE xy) /= eqxx.
Qed.

Section pairings.
Variable n : nat.

(* p is a fixed-point-free involution of 'I_n. *)
Definition pairing (p : 'I_n -> 'I_n) : bool :=
  [forall v, (p (p v) == v) && (p v != v)].

(* The edges {v, p v}. *)
Definition pairing_edges (p : 'I_n -> 'I_n) : {set {set 'I_n}} :=
  [set [set v; p v] | v : 'I_n].

Variable p : 'I_n -> 'I_n.
Hypothesis hp : pairing p.

Let pK v : p (p v) = v.
Proof. by have /forallP/(_ v)/andP[/eqP] := hp. Qed.

Let pN v : p v != v.
Proof. by have /forallP/(_ v)/andP[] := hp. Qed.

(* The edge of v is the edge of its partner. *)
Let edge_sym v : [set p v; p (p v)] = [set v; p v].
Proof. by rewrite pK setUC. Qed.

(* An edge of the pairing that contains u is the edge of u. *)
Let edge_of u v : u \in [set v; p v] -> [set v; p v] = [set u; p u].
Proof.
by rewrite !inE => /orP[] /eqP ->; rewrite // -[in RHS](pK v) edge_sym.
Qed.

Lemma pairing_perfect : is_perfect_matching (pairing_edges p).
Proof.
apply/andP; split.
  apply/forallP => e; apply/implyP => /imsetP[v _ ->]; rewrite /kn_edge cards2.
  by have := pN v; rewrite eq_sym => ->.
apply/forallP => u; apply/cards1P; exists [set u; p u].
apply/setP => e; rewrite !inE; apply/andP/eqP => [[/imsetP[v _ ->] /edge_of //]|->].
by split; [apply/imsetP; exists u | rewrite !inE eqxx].
Qed.

Definition pairing_matching : perfect_matching n :=
  Sub (pairing_edges p) pairing_perfect.

(* The crossing number: the vertices of U whose partner lies outside U. *)
Lemma pairing_crossing (U : odd_set n) :
  crossing U pairing_matching = #|[set v in val U | p v \notin val U]|.
Proof.
rewrite /crossing /=; set D := [set v in val U | p v \notin val U].
have vNp v : v != p v by have := pN v; rewrite eq_sym.
have -> : pairing_edges p :&: edge_cut (val U) = (fun v => [set v; p v]) @: D.
  apply/setP => e; rewrite !inE; apply/andP/imsetP => [[/imsetP[v _ ->]]|[v]].
    rewrite cards2I ?vNp // => /andP[_].
    case vU: (v \in val U); case pU: (p v \in val U) => //= _.
      by exists v; rewrite // inE vU pU.
    by exists (p v); rewrite ?edge_sym // inE pU pK vU.
  rewrite inE => /andP[vU pU] ->; split; first by apply/imsetP; exists v.
  by rewrite /kn_edge cards2 vNp cards2I ?vNp // vU (negbTE pU).
rewrite card_in_imset // => v w; rewrite !inE => /andP[vU pvU] /andP[wU pwU] e.
have : v \in [set w; p w] by rewrite -e !inE eqxx.
by rewrite !inE => /orP[/eqP //|/eqP vp]; move: pwU; rewrite -vp vU.
Qed.

End pairings.

(* For even n, the partners of the pairs {2q, 2q + 1}. *)
Definition std_partner (n : nat) (v : 'I_n) : 'I_n :=
  insubd v (if odd v then (val v).-1 else (val v).+1).

Lemma std_pairing n : ~~ odd n -> pairing (@std_partner n).
Proof.
move=> en; pose f m := if odd m then m.-1 else m.+1.
have ff m : f (f m) = m.
  by rewrite /f; case: m => [|m] //=; case om: (odd m) => /=; rewrite ?om.
have fN m : f m != m.
  by rewrite /f; case: m => [|m] //=; case: (odd m) => /=; rewrite ?neq_ltn ?ltnSn ?orbT.
have flt (v : 'I_n) : (f v < n)%N.
  rewrite /f; case: ifP => ov; first exact: leq_ltn_trans (leq_pred _) (ltn_ord v).
  rewrite ltn_neqAle ltn_ord andbT; apply/eqP => vn.
  by move: en; rewrite -vn /= ov.
have vs (v : 'I_n) : val (std_partner v) = f v.
  by rewrite /std_partner val_insubd flt.
apply/forallP => v; apply/andP; split; first by apply/eqP/val_inj; rewrite !vs ff.
by rewrite -val_eqE vs fN.
Qed.

(* For even n there is a perfect matching. *)
Definition std_matching (n : nat) (en : ~~ odd n) : perfect_matching n :=
  pairing_matching (std_pairing en).
