From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix reals.
From mathcomp Require Import boolp.
From GaussianAnalysis.matrix Require Import psd_part psd_factorization psd_duality.
From GaussianAnalysis.combinatorics Require Import expander.
From GaussianApplications Require Import PsdRankDefinitions PsdRankStatement.
From GaussianApplications Require Import PsdLiftDefinitions PsdLiftStatement.
From GaussianApplications.PsdRank Require Import Model.

(**md**************************************************************************)
(* # PSD rank of shifted matching matrices: the corollary on exact lifts      *)
(*                                                                            *)
(* Item A7 of phase 14 (AGENTS.md, section Phase 14; the plan                 *)
(* notes/phase14-plan.md, T14): the corollary 'Unshifted rank and exact       *)
(* lifts' of 'Exponential PSD rank of positively shifted matching matrices'   *)
(* (family 126 of the OpenAI math collection, revision 1581d4cbd,             *)
(* source/sections/introduction.tex, lines 74-114), a Rocq formalization of   *)
(* the credited argument, from the main theorem.                              *)
(*                                                                            *)
(* psd_lift_from_rank: psd_rank_statement -> psd_lift_statement, with         *)
(* K' = 2 K and n0' = max(n0, K + 1, 4), where K and n0 are those of the main *)
(* theorem at rho = 1/2:                                                      *)
(* - rank_shift_factorization: a factorization of A_n(0) of size r gives one  *)
(*   of A_n(rho) of size r + 1 (psd_factorization_shift); exp_succ_le turns   *)
(*   2^n <= (r + 1)^K into 2^n <= r^(2 K) for K < n;                          *)
(* - slack_rank_factorization: the rows of T_n(0) at the odd sets are         *)
(*   A_n(0) (psd_factorization_restrict);                                     *)
(* - lift_slack_factorization: for even n >= 4, an exact semidefinite lift    *)
(*   of size r gives a PSD factorization of T_n(0) of size r. The column of   *)
(*   a perfect matching M is a point of the slice that maps to the indicator  *)
(*   of M (match_vec); the row of an edge or of an odd set is the certificate *)
(*   of psd_slack_certificate_affine (matrix/psd_duality.v) for the affine    *)
(*   function of the row, nonnegative on the slice because every point of     *)
(*   the slice maps into the polytope, and zero at a tight matching:          *)
(*   tight_edge (a perfect matching that avoids an edge) and tight_odd (one   *)
(*   that crosses an odd set once), from pairings of the vertices (item A1)   *)
(*   conjugated by a permutation (perm_imset_eq of combinatorics/expander.v). *)
(*                                                                            *)
(* Departure: the TeX passes through Edmonds's description of the polytope,   *)
(* the facets and the cone-factorization theorem; this file needs none of     *)
(* them. Like the Lean development of the collection, it builds the row       *)
(* factors from a duality certificate at a tight matching:                    *)
(* Lean: affineLift_hasFactorization (AffineFactorization.lean, line 13)      *)
(* The tight matchings are proved here by another route; their statements     *)
(* are those of                                                               *)
(* Lean: oddCut_has_tight_matching (TightMatchings.lean, line 12)             *)
(* Lean: edge_has_tight_matching (TightMatchings.lean, line 46)               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* The partner of v is 2q + 1 if v = 2q and 2q if v = 2q + 1. *)
Lemma std_partnerE q (v : 'I_q) : ~~ odd q ->
  val (std_partner v) = if odd v then (val v).-1 else (val v).+1.
Proof.
move=> eq; rewrite /std_partner val_insubd.
case ov: (odd v); first by rewrite (leq_ltn_trans (leq_pred _) (ltn_ord v)).
case: ltnP => // qv.
have /eqP vq : (val v).+1 == q by rewrite eqn_leq qv ltn_ord.
by move: eq; rewrite -[q in odd q]vq /= ov.
Qed.

Section tight.
Variable n : nat.

(* A pairing conjugated by a permutation s: v |-> s (p (s^-1 v)). *)
Definition conj_partner (s : {perm 'I_n}) (p : 'I_n -> 'I_n) (v : 'I_n) :
  'I_n := s (p ((s^-1)%g v)).

Lemma conj_pairing s p : pairing p -> pairing (conj_partner s p).
Proof.
move=> /forallP hp; apply/forallP => v; rewrite /conj_partner permK.
have /andP[/eqP -> pv] := hp ((s^-1)%g v); rewrite permKV eqxx /=.
by rewrite -[X in _ != X](permKV s v) (inj_eq perm_inj).
Qed.

(* The vertices below m. *)
Lemma card_initial m : (m <= n)%N -> #|[set i : 'I_n | (i < m)%N]| = m.
Proof.
move=> mn; have wi : injective (widen_ord mn) by move=> i j /(congr1 val) /= /val_inj.
rewrite -[RHS](card_ord m) -(card_imset _ wi).
congr #|pred_of_set _|; apply/setP => i; rewrite inE.
apply/idP/imsetP => [im|[j _ ->]]; last exact: (ltn_ord j).
by exists (Ordinal im) => //; apply/val_inj.
Qed.

Hypothesis en : ~~ odd n.

(* For an odd set U, a perfect matching that crosses U once: number U first,
   then pair 2q with 2q + 1; only the pair of the last vertex of U crosses. *)
Lemma tight_odd (U : odd_set n) : exists M : perfect_matching n, crossing U M = 1%N.
Proof.
have Un : (#|val U| <= n)%N by rewrite -[n in (_ <= n)%N]card_ord max_card.
have [s sA] := perm_imset_eq (card_initial Un).
have hp := conj_pairing s (std_pairing en).
exists (pairing_matching hp); rewrite pairing_crossing.
have inU v : (v \in val U) = ((s^-1)%g v < #|val U|)%N.
  by rewrite -[in LHS]sA -[v in LHS](permKV s v) mem_imset ?inE //; exact: perm_inj.
have oU : odd #|val U| := valP U.
have U0 : (0 < #|val U|)%N by case: #|val U| oU.
have i0n : (#|val U|.-1 < n)%N by rewrite -ltnS prednK // ltnS.
rewrite -(cards1 (s (Ordinal i0n))); congr #|pred_of_set _|; apply/setP => v.
rewrite !inE !inU /conj_partner permK -[v in RHS](permKV s v) (inj_eq perm_inj).
rewrite -val_eqE /=; move: ((s^-1)%g v) => j; rewrite std_partnerE //.
case oj: (odd j); last by rewrite -leqNgt -eqn_leq -[in RHS]eqSS prednK.
case: (ltnP j) => jU //=; first rewrite (leq_ltn_trans (leq_pred _) jU) /=.
all: by apply/esym/eqP => je; move: oU; rewrite -(prednK U0) /= -je oj.
Qed.

Hypothesis n4 : (4 <= n)%N.

(* For an edge e, a perfect matching that avoids it: number the ends of e
   0 and 2, then pair 2q with 2q + 1. *)
Lemma tight_edge (e : {set 'I_n}) :
  kn_edge e -> exists M : perfect_matching n, e \notin val M.
Proof.
move=> /cards2P[u [v [uv ->]]].
have h0 : (0 < n)%N by apply: leq_trans n4.
have h2 : (2 < n)%N by apply: leq_trans n4.
pose i0 := Ordinal h0; pose i2 := Ordinal h2.
have [s sA] : exists s : {perm 'I_n}, s @: [set i0; i2] = [set u; v].
  by apply: perm_imset_eq; rewrite !cards2 uv.
have hp := conj_pairing s (std_pairing en).
exists (pairing_matching hp); apply/negP => /imsetP[w _ ew].
have inA x : (x \in [set u; v]) = ((s^-1)%g x \in [set i0; i2]).
  by rewrite -[in LHS]sA -[x in LHS](permKV s x) mem_imset //; exact: perm_inj.
have wA := inA w; have pA := inA (conj_partner s (@std_partner n) w).
rewrite ew !inE eqxx /= in wA; rewrite ew !inE eqxx orbT /conj_partner permK in pA.
move: wA pA; move: ((s^-1)%g w) => j.
by move/esym/orP => [] /eqP ->; rewrite -!val_eqE /= std_partnerE.
Qed.

End tight.

Section lift.
Variables (R : realType) (n : nat).

(* The indicator vector of a perfect matching, a point of the polytope. *)
Definition match_vec (M : perfect_matching n) : {ffun kn_edges n -> R} :=
  [ffun e => (val e \in val M)%:R].

Lemma match_vec_polytope M : in_matching_polytope (match_vec M).
Proof.
exists (fun M' => (M' == M)%:R); split.
- by move=> M'; rewrite ler0n.
- by rewrite (bigD1 M) //= eqxx big1 ?addr0 // => M' /negbTE ->.
- move=> e; rewrite ffunE (bigD1 M) //= eqxx mul1r big1 ?addr0 // => M' /negbTE ->.
  by rewrite mul0r.
Qed.

(* The edges of the cut of U that lie in M: the crossing number. *)
Lemma cut_sum (U : odd_set n) (M : perfect_matching n) :
  \sum_(e : kn_edges n | val e \in edge_cut (val U)) ((val e \in val M)%:R : R) =
  (crossing U M)%:R.
Proof.
rewrite -natr_sum /crossing; congr (_%:R).
rewrite -big_mkcondr sum1dep_card -(card_imset _ val_inj).
congr #|pred_of_set _|; apply/setP => x; rewrite in_setI.
apply/imsetP/andP => [[e]|[xM xc]]; first by rewrite inE => /andP[ec eM] ->.
have kx : kn_edge x by move: xc; rewrite inE => /andP[].
by exists (exist _ x kx); rewrite // inE xc xM.
Qed.

Hypotheses (en : ~~ odd n) (n4 : (4 <= n)%N).

(* An exact semidefinite lift of size r gives a PSD factorization of T_n(0)
   of size r. The column of M is a point X M of the slice that maps to the
   indicator of M; the row of an edge or of an odd set is a certificate of
   psd_slack_certificate_affine for the affine function of the row, which
   is nonnegative on the slice and vanishes at a tight matching. *)
Lemma lift_slack_factorization (r : nat) :
  semidefinite_lift R n r -> psd_factorization (@matching_slack_mx n R) r.
Proof.
move=> [m [C [c [D [d0 hl]]]]].
have hX (M : perfect_matching n) : exists X : 'M[R]_r,
    [/\ psdmx X, forall l, \tr (C l *m X) = c l &
        forall e, \tr (D e *m X) + d0 e = (val e \in val M)%:R].
  have [X [Xp XC Xe]] := (hl (match_vec M)).1 (match_vec_polytope M).
  by exists X; split=> // e; move/ffunP: Xe => /(_ e); rewrite !ffunE => <-.
have [X hXM] := choice hX.
have Xp M : psdmx (X M) by case: (hXM M).
have XC M l : \tr (C l *m X M) = c l by case: (hXM M) => _ h _; exact: h.
have Xe M e : \tr (D e *m X M) + d0 e = (val e \in val M)%:R by case: (hXM M).
(* a point of the slice maps to a point of the polytope *)
have slice (Y : 'M[R]_r) : psdmx Y -> (forall l, \tr (C l *m Y) = c l) ->
    exists2 w : perfect_matching n -> R, forall M, 0 <= w M &
      \sum_M w M = 1 /\
      forall e, \tr (D e *m Y) + d0 e = \sum_M w M * (val e \in val M)%:R.
  move=> Yp YC; have [|w [w0 w1 we]] := (hl [ffun e => \tr (D e *m Y) + d0 e]).2.
    by exists Y.
  by exists w => //; split=> // e; rewrite -we ffunE.
have hF (i : (kn_edges n + odd_set n)%type) : exists A : 'M[R]_r,
    psdmx A /\ forall M, matching_slack_mx R i M = \tr (A *m X M).
  case: i => [e|U].
  - have [M0 eM0] := tight_edge en n4 (valP e).
    have nonneg Y : psdmx Y -> (forall l, \tr (C l *m Y) = c l) ->
        0 <= \tr (D e *m Y) + d0 e.
      move=> Yp YC; have [w w0 [_ ->]] := slice Y Yp YC.
      by apply: sumr_ge0 => M _; rewrite mulr_ge0 ?ler0n.
    have tight : \tr (D e *m X M0) + d0 e = 0 by rewrite Xe (negbTE eM0).
    have [A Ap AE] := psd_slack_certificate_affine Xp XC nonneg tight.
    by exists A; split=> // M; rewrite AE Xe.
  pose DU := \sum_(e : kn_edges n | val e \in edge_cut (val U)) D e.
  pose dU := \sum_(e : kn_edges n | val e \in edge_cut (val U)) d0 e - 1.
  have DUE Y : \tr (DU *m Y) + dU =
      \sum_(e : kn_edges n | val e \in edge_cut (val U)) (\tr (D e *m Y) + d0 e) - 1.
    by rewrite /DU /dU mulmx_suml raddf_sum /= big_split /= addrA.
  have DUX M : \tr (DU *m X M) + dU = (crossing U M)%:R - 1.
    by rewrite DUE (eq_bigr _ (fun e _ => Xe M e)) cut_sum.
  have [M0 cM0] := tight_odd en U.
  have nonneg Y : psdmx Y -> (forall l, \tr (C l *m Y) = c l) ->
      0 <= \tr (DU *m Y) + dU.
    move=> Yp YC; have [w w0 [w1 we]] := slice Y Yp YC.
    rewrite DUE subr_ge0 (eq_bigr _ (fun e _ => we e)) exchange_big.
    rewrite -[X in X <= _]w1; apply: ler_sum => M _.
    by rewrite -mulr_sumr cut_sum ler_peMr // ler1n odd_gt0 // crossing_odd.
  have tight : \tr (DU *m X M0) + dU = 0 by rewrite DUX cM0 subrr.
  have [A Ap AE] := psd_slack_certificate_affine Xp XC nonneg tight.
  by exists A; split=> // M; rewrite AE DUX.
have [F hFi] := choice hF.
exists F, X; split=> [i|M|i M]; [by case: (hFi i) | exact: Xp |].
by case: (hFi i) => _ ->.
Qed.

End lift.

Section rank.
Variable R : realType.

Lemma psd_factorization_ext (I J : finType) (A B : I -> J -> R) (r : nat) :
  (forall i j, A i j = B i j) -> psd_factorization A r -> psd_factorization B r.
Proof.
by move=> AB [F [G [Fp Gp AE]]]; exists F, G; split=> // i j; rewrite -AB.
Qed.

(* The rows of T_n(0) at the odd sets are the rows of A_n(0). *)
Lemma slack_rank_factorization n r :
  psd_factorization (@matching_slack_mx n R) r ->
  psd_factorization (@shifted_matching_mx n R 0) r.
Proof.
move/(psd_factorization_restrict (@inr (kn_edges n) (odd_set n)) id).
by apply: psd_factorization_ext => U M; rewrite /shifted_matching_mx addr0.
Qed.

(* A_n(0) + rho = A_n(rho), so a factorization of A_n(0) of size r gives one
   of A_n(rho) of size r + 1. *)
Lemma rank_shift_factorization n r (rho : R) : 0 <= rho ->
  psd_factorization (@shifted_matching_mx n R 0) r ->
  psd_factorization (@shifted_matching_mx n R rho) r.+1.
Proof.
move=> rho0 /(psd_factorization_shift rho0).
by apply: psd_factorization_ext => U M; rewrite /shifted_matching_mx addr0.
Qed.

End rank.

(* 2^n <= (r + 1)^K with 0 < K < n gives 2^n <= r^(2 K): r = 0 and r = 1 are
   excluded, and r + 1 <= r^2 for r >= 2. *)
Lemma exp_succ_le (n r K : nat) : (0 < K)%N -> (K < n)%N ->
  (2 ^ n <= r.+1 ^ K)%N -> (2 ^ n <= r ^ (2 * K))%N.
Proof.
move=> K0 Kn; case: r => [|[|r]] h.
- by move: h; rewrite exp1n -(expn0 2) leq_exp2l // leqn0 => /eqP n0; move: Kn; rewrite n0.
- by move: h; rewrite leq_exp2l // leqNgt Kn.
by apply: leq_trans h _; rewrite expnM leq_exp2r // (ltn_exp2l 1 2).
Qed.

(* The corollary from the main theorem: K' = 2 K and n0' = max(n0, K + 1, 4),
   with n0 the threshold of psd_rank_statement at rho = 1/2. *)
Theorem psd_lift_from_rank : psd_rank_statement -> psd_lift_statement.
Proof.
move=> hT R; have [K [K0 hK]] := hT R.
have h12 : 0 < (2^-1 : R) < 1 by rewrite invr_gt0 ltr0n /= invf_lt1 ?ltr0n ?ltr1n.
have [n0 hn0] := hK _ h12.
have /andP[h0 _] := h12.
exists (2 * K)%N; split; first by rewrite muln_gt0.
exists (maxn n0 (maxn K.+1 4)) => n en; rewrite !geq_max => /and3P[nn0 nK n4] r.
have hA : psd_factorization (@shifted_matching_mx n R 0) r -> (2 ^ n <= r ^ (2 * K))%N.
  move=> /(rank_shift_factorization (ltW h0)) h.
  by apply: exp_succ_le => //; exact: hn0 en nn0 _ h.
split=> [|/slack_rank_factorization|/(lift_slack_factorization en n4)/slack_rank_factorization];
  exact: hA.
Qed.

