(* The effective-rank bound: Lemma 3.12 and Corollary 3.13 of Koehler and
   Sohn (arXiv 2608.27372, lines 3314-3436 of arxiv_v1.tex), at Stdlib's R.
   Item S7 of stage 3 of phase 5 (lane C).

   Plan (names come with the proofs). On the event of Proposition 3.1 in
   dimension p (Sat/Apriori), where
   Lambda = sup_{|A|_F <= 1} (sum_i <z_i z_i^T - I, A>^2)^(1/2) <= C p,
   deterministically: for every t with |t|_2 = 1 and
   |t|_oo <= (K d)^(-1/2), K >= K_0, the matrix Sigma_t = sum_i t_i^2 z_i z_i^T
   has at most eps p eigenvalues below 1/8. Proof: for a subspace H of
   dimension floor (eps p), Markov's inequality bounds the number of i with
   |P_H z_i|^2 <= dim H / 2 by 4 Lambda^2 / dim H; lightness bounds their
   weight; H spanned by eigenvectors gives the contradiction. Corollary
   3.13: the same for the blocks of Proposition 3.4, uniformly in the
   heads I (item S9 of lane B uses it). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
