From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From GaussianAnalysis.matrix Require Import von_neumann.

(**md**************************************************************************)
(* # Effective rank of a weighted sum of rank-one matrices                    *)
(*                                                                            *)
(* Let u_1, ..., u_n be row vectors of R^p whose rank-one matrices u_i^T u_i  *)
(* are close to the identity in the sense that                                *)
(*   sum_i <u_i^T u_i - I, A>^2 <= L^2 |A|_F^2   for every p x p matrix A,    *)
(* and let t be weights with |t| = 1 and 8 L^2 t_i^2 <= k for every i, with   *)
(* 0 < k <= p. Then Sigma_t = sum_i t_i^2 u_i^T u_i has fewer than k          *)
(* eigenvalues below 1/8: its sorted eigenvalues spec Sigma_t                 *)
(* (von_neumann.v) are at least 1/8 at every index j with j + k <= p          *)
(* (effective_rank_spec).                                                     *)
(*                                                                            *)
(* This is the deterministic part of Lemma 3.12 of Koehler and Sohn (arXiv    *)
(* 2608.27372, lines 3314-3405 of arxiv_v1.tex), where the hypothesis comes   *)
(* from the a priori estimate of the features (u_i u_i^T - I) / sqrt p. The   *)
(* proof is the paper's: if k eigenvalues were below 1/8, the projection H on *)
(* their eigenvectors would give <H, Sigma_t> < k / 8, while the hypothesis   *)
(* at A = H, which has |H|_F^2 = tr H = k, bounds the weight of the points    *)
(* with u_i H u_i^T < k / 2, and gives <H, Sigma_t> >= k / 4.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section effective_rank.
Variable R : realType.

Lemma effective_rank_spec n p (u : 'I_n -> 'rV[R]_p) (t : 'rV[R]_n) (L : R)
    (k : nat) :
  (forall A : 'M[R]_p,
     \sum_i mxdot ((u i)^T *m u i - 1%:M) A ^+ 2 <= L ^+ 2 * mxdot A A) ->
  (0 < k)%N -> (k <= p)%N -> mxdot t t = 1 ->
  (forall i, 8 * L ^+ 2 * t 0 i ^+ 2 <= k%:R) ->
  forall j : 'I_p, (j + k <= p)%N ->
  8^-1 <= spec (\sum_i t 0 i ^+ 2 *: ((u i)^T *m u i)) 0 j.
Proof.
move=> hL k0 kp t1 hl j jk.
set S := \sum_i _.
have Ss : S \is symmetricmx.
  apply/symmetricmxP; rewrite /S linear_sum /=; apply: eq_bigr => i _.
  by rewrite linearZ /= trmx_mul trmxK.
have [P Po SE] := spec_decomposition Ss.
rewrite leNgt; apply/negP => hj.
(* H, the projection on the eigenvectors of the last k eigenvalues *)
pose e : 'rV[R]_p := \row_a ((p - k <= a)%N)%:R.
pose H := P^T *m diag_mx e *m P.
have PTo : P^T \is orthogonalmx by rewrite trmx_orthogonal.
have conj (X Y : 'M[R]_p) :
    mxdot (P^T *m X *m P) (P^T *m Y *m P) = mxdot X Y.
  by rewrite mxdot_orthogonalmxr // mxdot_orthogonalmxl.
have e01 a : e 0 a * e 0 a = e 0 a.
  by rewrite mxE; case: leqP; rewrite ?mul0r ?mul1r.
have esum : \sum_(a < p) e 0 a = k%:R.
  rewrite (eq_bigr (fun a : 'I_p => ((p - k <= a)%N)%:R)).
    by move=> a _; rewrite mxE.
  rewrite -natr_sum; congr (_%:R).
  rewrite -(big_mkord xpredT (fun i => nat_of_bool (p - k <= i)%N)).
  rewrite (big_cat_nat (leq0n (p - k)) (leq_subr k p)) /=.
  rewrite [X in (X + _)%N]big_nat_cond [X in (X + _)%N]big1.
    by move=> i /andP[/andP[_ hi] _]; rewrite leqNgt hi.
  rewrite add0n big_nat_cond (eq_bigr (fun=> 1%N)).
    by move=> i /andP[/andP[hi _] _]; rewrite hi.
  by rewrite -big_nat_cond sum_nat_const_nat muln1 subKn.
have HH : mxdot H H = k%:R.
  rewrite /H conj mxdot_diag -esum; apply: eq_bigr => a _; exact: e01.
have trH : \tr H = k%:R.
  rewrite /H mxtrace_mulC mulmxA.
  have /orthogonalmxP -> : P \is orthogonalmx := Po.
  by rewrite mul1mx mxtrace_diag esum.
(* <H, S> < k / 8: the last k eigenvalues are below 1/8 *)
have upper : mxdot H S < k%:R / 8.
  rewrite {1}SE /H conj mxdot_diag.
  apply: (@le_lt_trans _ _ (\sum_a e 0 a * spec S 0 j)).
    apply: ler_sum => a _; rewrite [e 0 a]mxE.
    case: leqP => ha; rewrite ?mul0r ?mul1r //.
    apply: spec_decr; apply: leq_trans ha.
    by rewrite leq_subRL ?(leq_trans (leq_addl j k)) // addnC.
  by rewrite -mulr_suml esum ltr_pM2l ?ltr0n.
(* <H, S> >= k / 4, from the hypothesis at A = H *)
pose q i := mxdot H ((u i)^T *m u i).
have qE i : mxdot ((u i)^T *m u i - 1%:M) H = q i - k%:R.
  rewrite mxdotBl [X in X - _]mxdotC; congr (_ - _).
  by rewrite mxdot_trace mul1mx mxtrace_tr trH.
have hq : \sum_i (q i - k%:R) ^+ 2 <= L ^+ 2 * k%:R.
  have h := hL H; rewrite HH in h; apply: le_trans h.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_bigr => i _; rewrite qE.
have kn : k%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
(* x >= k/2 - (2/k) (x - k)^2 for every real x *)
have key (x : R) : k%:R / 2 - 2 / k%:R * (x - k%:R) ^+ 2 <= x.
  rewrite -subr_ge0.
  have -> : x - (k%:R / 2 - 2 / k%:R * (x - k%:R) ^+ 2) =
      2 / k%:R * (x - 3 * k%:R / 4) ^+ 2 + 3 * k%:R / 8 by field.
  apply: addr_ge0.
    by apply: mulr_ge0; [apply: divr_ge0; exact: ler0n | exact: sqr_ge0].
  by apply: divr_ge0; [apply: mulr_ge0; exact: ler0n | exact: ler0n].
have ts : \sum_i t 0 i ^+ 2 = 1.
  by rewrite -t1 /mxdot big_ord1; apply: eq_bigr => i _; rewrite expr2.
(* the weighted deviations: sum_i t_i^2 (q_i - k)^2 <= k^2 / 8 *)
have hw : \sum_i t 0 i ^+ 2 * (q i - k%:R) ^+ 2 <= k%:R ^+ 2 / 8.
  have [L0|L0] := eqVneq L 0.
    rewrite L0 expr0n /= mul0r in hq.
    have z i : (q i - k%:R) ^+ 2 = 0.
      apply: (psumr_eq0P (P := xpredT) (fun i _ => sqr_ge0 (q i - k%:R))) => //.
      by apply/le_anti; rewrite hq sumr_ge0 // => l _; exact: sqr_ge0.
    rewrite big1 ?divr_ge0 ?exprn_ge0 ?ler0n // => i _.
    by rewrite z mulr0.
  have L2 : 0 < L ^+ 2 by rewrite lt_def sqrf_eq0 L0 sqr_ge0.
  apply: (@le_trans _ _ (\sum_i k%:R / (8 * L ^+ 2) * (q i - k%:R) ^+ 2)).
    apply: ler_sum => i _; apply: ler_wpM2r; first exact: sqr_ge0.
    have p8 : 0 < 8 * L ^+ 2 by rewrite mulr_gt0.
    by rewrite ler_pdivlMr // mulrC; exact: hl.
  rewrite -mulr_sumr.
  apply: le_trans (ler_wpM2l _ hq) _.
    by rewrite divr_ge0 ?ler0n // mulr_ge0 // ltW.
  have L2n : L ^+ 2 != 0 by rewrite gt_eqF.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have low : k%:R / 4 <= mxdot H S.
  have -> : mxdot H S = \sum_i t 0 i ^+ 2 * q i.
    by rewrite /S mxdot_sumr; apply: eq_bigr => i _; rewrite mxdotZr.
  apply: (@le_trans _ _ (\sum_i t 0 i ^+ 2 *
      (k%:R / 2 - 2 / k%:R * (q i - k%:R) ^+ 2))); last first.
    by apply: ler_sum => i _; apply: ler_wpM2l; [exact: sqr_ge0 | exact: key].
  rewrite (eq_bigr (fun i => k%:R / 2 * t 0 i ^+ 2 -
      2 / k%:R * (t 0 i ^+ 2 * (q i - k%:R) ^+ 2))).
    by move=> i _; ring.
  rewrite sumrB -!mulr_sumr ts mulr1.
  have h : 2 / k%:R * \sum_i t 0 i ^+ 2 * (q i - k%:R) ^+ 2 <=
      2 / k%:R * (k%:R ^+ 2 / 8).
    by apply: ler_wpM2l => //; rewrite divr_ge0 ?ler0n.
  have e8 : 2 / k%:R * (k%:R ^+ 2 / 8) = k%:R / 4 :> R by field.
  rewrite e8 in h.
  have e2 : k%:R / 2 - k%:R / 4 = k%:R / 4 :> R by field.
  by rewrite -e2 lerD2l lerN2.
have kpos : 0 < k%:R :> R by rewrite ltr0n.
have := le_lt_trans low upper.
lra.
Qed.

End effective_rank.
