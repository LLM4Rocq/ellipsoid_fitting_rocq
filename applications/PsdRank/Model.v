From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix reals.
From GaussianAnalysis.matrix Require Import psd_part psd_factorization.
From GaussianApplications Require Import PsdRankDefinitions PsdRankStatement.

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
(*   entries 1_(e in delta(U)) for a row and 1_(e in M) for a column; so the  *)
(*   exclusion of rho = 1 in psd_rank_statement is necessary.                 *)
(* - psd_rank_statementE: psd_rank_statement with the factors written out,    *)
(*   for the reviewer's comparison.                                           *)
(*                                                                            *)
(* ```                                                                        *)
(*           kn_edges n == the edges of K_n, as a finite type                 *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section model.
Variable n : nat.

(* The edges of K_n, as a finite type. *)
Definition kn_edges := {e : {set 'I_n} | kn_edge e}.

Lemma card_kn_edges : #|{: kn_edges}| = 'C(n, 2).
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
pose a (U : odd_set n) (k : 'I_#|{: kn_edges}|) : R :=
  (val (enum_val k) \in edge_cut (val U))%:R.
pose b (M : perfect_matching n) (k : 'I_#|{: kn_edges}|) : R :=
  (val (enum_val k) \in val M)%:R.
exists (fun U => diag_mx (\row_k a U k)), (fun M => diag_mx (\row_k b M k)).
split => [U|M|U M].
- by apply: psdmx_diag => k; rewrite mxE ler0n.
- by apply: psdmx_diag => k; rewrite mxE ler0n.
rewrite mulmx_diag mxtrace_diag /shifted_matching_mx subrK.
under eq_bigr do rewrite !mxE.
rewrite /a /b (reindex (@enum_rank kn_edges)) /=.
  by apply: onW_bij; exact: enum_rank_bij.
under eq_bigr do rewrite enum_rankK -natrM.
rewrite -natr_sum /crossing; congr (_%:R).
(* the edges of M crossing U, as edges of K_n *)
set S := val M :&: edge_cut (val U).
have Sedge e : e \in S -> kn_edge e by rewrite !inE => /andP[_ /andP[]].
have -> : S = val @: [set x : kn_edges | val x \in S].
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
