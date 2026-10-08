(* The effective-rank bound: Lemma 3.12 and Corollary 3.13 of Koehler and
   Sohn (arXiv 2608.27372, lines 3314-3470 of arxiv_v1.tex), at Stdlib's R.
   Item S7 of stage 3 of phase 5 (lane C), with
   library/matrix/effective_rank.v.

   For a sample x of n points of R^d and an injective list of columns
   c : 'I_p -> 'I_d, block_row c x i = (x_(i, c a))_a is the block of point
   i (lane B's stage_row c x i of Sat/OneStage), and
   Sigma_t = sum_i t_i^2 u_i^T u_i with u_i = block_row c x i.

   Proved here.
   - block_row_dev: if the a priori estimate |L_X^* z|_F <= C sqrt d |z|
     holds for every z (adjoint_bound, adjoint_bound_data of Sat/Apriori),
     then sum_i <u_i^T u_i - I, A>^2 <= (C d)^2 |A|_F^2 for every p x p
     matrix A: <u_i^T u_i - I_p, A> = <x_i x_i^T - I_d, E A E^T> with E the
     isometric embedding of the columns c, and the sum is d |L_X (E A E^T)|^2
     (frobenius_sample_map_le).
   - block_effective_rank (Lemma 3.12, Corollary 3.13): on the same event,
     for every injective c, every k with 0 < k <= p and every t with
     |t| = 1 and 8 C^2 d^2 t_i^2 <= k, spec Sigma_t j >= 1/8 whenever
     j + k <= p (effective_rank_spec of library/matrix/effective_rank.v);
     block_effective_rank_light is the form with light tails,
     K d t_i^2 <= 1 and 8 C^2 d <= K k. The paper's probability-one event
     is thus the single event of adjoint_bound, for all blocks, sets I and
     tails t at once.
   - block_row_sqnorm: |u_i|^2 <= |x_i|^2, which is less than 2 d on
     norm_good n d 1 x. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From GaussianAnalysis.matrix Require Import euclidean nuclear von_neumann.
From GaussianAnalysis.matrix Require Import effective_rank.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality.Sat Require Import Apriori.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section block_rows.
Variables (n d p : nat) (x : paper_main_sample n d) (c : 'I_p -> 'I_d).

(* The coordinates of point i in the columns c. *)
Definition block_row (i : 'I_n) : 'rV[R]_p :=
  \row_a paper_main_point x i (c a) 0.

(* The isometric embedding of the columns c. *)
Definition block_embed : 'M[R]_(d, p) := \matrix_(j, a) (j == c a)%:R.

Lemma block_rowE i : block_row i = (paper_main_point x i)^T *m block_embed.
Proof.
apply/rowP => a; rewrite /block_embed !mxE (bigD1 (c a)) //= big1 ?addr0.
  by move=> j ja; rewrite !mxE (negPf ja) mulr0.
by rewrite !mxE eqxx mulr1.
Qed.

Lemma block_embed_orth : injective c -> block_embed^T *m block_embed = 1%:M.
Proof.
move=> ci; apply/matrixP => a b.
rewrite /block_embed !mxE (bigD1 (c a)) //= big1 ?addr0.
  by move=> j ja; rewrite !mxE (negPf ja) mul0r.
by rewrite !mxE eqxx mul1r (inj_eq ci).
Qed.

Lemma block_row_sqnorm i : injective c ->
  frobenius (block_row i) ^+ 2 <=
  mxdot (paper_main_point x i) (paper_main_point x i).
Proof.
move=> ci.
have -> : frobenius (block_row i) ^+ 2 =
    \sum_a paper_main_point x i (c a) 0 ^+ 2.
  rewrite frobenius_sqr /mxdot big_ord1.
  by apply: eq_bigr => a _; rewrite mxE expr2.
have -> : mxdot (paper_main_point x i) (paper_main_point x i) =
    \sum_j paper_main_point x i j 0 ^+ 2.
  by apply: eq_bigr => j _; rewrite big_ord1 expr2.
rewrite -(big_imset (fun j => paper_main_point x i j 0 ^+ 2) (in2W ci)) /=.
rewrite [X in _ <= X](bigID (mem (c @: predT))) /= lerDl.
by apply: sumr_ge0 => j _; exact: sqr_ge0.
Qed.

Lemma block_row_dev (C : R) : (0 < d)%N -> 0 <= C -> injective c ->
  (forall z : 'rV[R]_n,
     frobenius (sample_adj x z) <= C * Num.sqrt d%:R * frobenius z) ->
  forall A : 'M[R]_p,
  \sum_i mxdot ((block_row i)^T *m block_row i - 1%:M) A ^+ 2 <=
  (C * d%:R) ^+ 2 * mxdot A A.
Proof.
move=> d0 C0 ci hC A.
have EE := block_embed_orth ci.
set E := block_embed in EE *.
set B := E *m A *m E^T.
have sd0 : 0 < Num.sqrt d%:R :> R by rewrite sqrtr_gt0 ltr0n.
have trB : \tr B = \tr A.
  by rewrite /B mxtrace_mulC mulmxA EE mul1mx.
have BB : mxdot B B = mxdot A A.
  rewrite /B mxdot_mulmxr mxdot_mulmxl trmxK -!mulmxA EE mulmx1.
  by rewrite !mulmxA EE mul1mx.
(* <u_i^T u_i - I, A> = <x_i x_i^T - I, B> = sqrt d (L_X B)_i *)
have key i : mxdot ((block_row i)^T *m block_row i - 1%:M) A =
    Num.sqrt d%:R * sample_map x B 0 i.
  rewrite /sample_map /coef_map mxE /sample_W mxdotZl mulrA.
  rewrite mulfV ?gt_eqF // mul1r.
  rewrite block_rowE trmx_mul trmxK !mxdotBl.
  congr (_ - _); last by rewrite !mxdot_trace !mul1mx !mxtrace_tr trB.
  by rewrite mxdot_mulmxr mxdot_mulmxl [RHS]mxdot_mulmxr trmx_mul !trmxK -/E
    /B !mulmxA.
under eq_bigr do rewrite key.
have hm := frobenius_sample_map_le n d x C hC B C0.
have e : \sum_i (Num.sqrt d%:R * sample_map x B 0 i) ^+ 2 =
    d%:R * frobenius (sample_map x B) ^+ 2.
  rewrite frobenius_sqr /mxdot big_ord1 mulr_sumr; apply: eq_bigr => i _.
  by rewrite exprMn sqr_sqrtr ?ler0n // expr2.
rewrite e.
apply: le_trans (_ : d%:R * (C * Num.sqrt d%:R * frobenius B) ^+ 2 <= _).
  rewrite ler_wpM2l ?ler0n // ler_sqr ?nnegrE ?frobenius_ge0 //.
  by rewrite mulr_ge0 ?frobenius_ge0 // mulr_ge0 // sqrtr_ge0.
rewrite !exprMn sqr_sqrtr ?ler0n // frobenius_sqr BB.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(* Lemma 3.12 and Corollary 3.13. *)
Theorem block_effective_rank (C : R) (t : 'rV[R]_n) (k : nat) :
  (0 < d)%N -> 0 <= C -> injective c ->
  (forall z : 'rV[R]_n,
     frobenius (sample_adj x z) <= C * Num.sqrt d%:R * frobenius z) ->
  (0 < k)%N -> (k <= p)%N -> mxdot t t = 1 ->
  (forall i, 8 * C ^+ 2 * d%:R ^+ 2 * t 0 i ^+ 2 <= k%:R) ->
  forall j : 'I_p, (j + k <= p)%N ->
  8^-1 <= spec (\sum_i t 0 i ^+ 2 *: ((block_row i)^T *m block_row i)) 0 j.
Proof.
move=> d0 C0 ci hC k0 kp t1 hl j jk.
apply: (effective_rank_spec (L := C * d%:R) _ k0 kp t1) => //.
  exact: block_row_dev.
move=> i; have h := hl i.
by rewrite exprMn !mulrA; rewrite !expr2 !mulrA in h.
Qed.

(* The same for light tails: K d t_i^2 <= 1 and 8 C^2 d <= K k. *)
Corollary block_effective_rank_light (C K : R) (t : 'rV[R]_n) (k : nat) :
  (0 < d)%N -> 0 <= C -> injective c ->
  (forall z : 'rV[R]_n,
     frobenius (sample_adj x z) <= C * Num.sqrt d%:R * frobenius z) ->
  (0 < k)%N -> (k <= p)%N -> mxdot t t = 1 ->
  (forall i, K * d%:R * t 0 i ^+ 2 <= 1) -> 8 * C ^+ 2 * d%:R <= K * k%:R ->
  forall j : 'I_p, (j + k <= p)%N ->
  8^-1 <= spec (\sum_i t 0 i ^+ 2 *: ((block_row i)^T *m block_row i)) 0 j.
Proof.
move=> d0 C0 ci hC k0 kp t1 hlight hK j jk.
apply: (block_effective_rank C t k d0 C0 ci hC k0 kp t1) => // i.
have dt : 0 <= d%:R * t 0 i ^+ 2 by rewrite mulr_ge0 ?ler0n ?sqr_ge0.
apply: le_trans (_ : K * k%:R * (d%:R * t 0 i ^+ 2) <= _).
  have -> : 8 * C ^+ 2 * d%:R ^+ 2 * t 0 i ^+ 2 =
      8 * C ^+ 2 * d%:R * (d%:R * t 0 i ^+ 2) by ring.
  exact: ler_wpM2r.
have -> : K * k%:R * (d%:R * t 0 i ^+ 2) = k%:R * (K * d%:R * t 0 i ^+ 2).
  by ring.
by rewrite -[X in _ <= X]mulr1 ler_wpM2l ?ler0n.
Qed.

End block_rows.
