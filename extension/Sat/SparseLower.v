(* The sparse lower bound: Proposition 3.3 of Koehler and Sohn (arXiv
   2608.27372, lines 2303-2418 of arxiv_v1.tex), at Stdlib's R. Item S4 of
   stage 3 of phase 5 (lane C).

   Plan (names come with the proofs). On the event of Proposition 3.1
   (Sat/Apriori), deterministically: for every lambda with at most
   C0 d ln d nonzero coordinates,
     nuclear (L_X^* lambda) >= c sqrt d / (ln d)^4 |lambda|_1.
   The certificate A = (1/d) sum_{i in I} y_i W_i, with I the support of
   lambda and y = Q_I^(-1) sign (lambda), satisfies <A, W_j> = sign
   lambda_j on I and opnorm A <= C (ln d)^4 / sqrt d, from |y|_2 <= 2
   sqrt |I|, |y|_oo <= C (ln d)^2 and A = d^(-3/2) (X_I D_y X_I^T -
   (sum_i y_i) I); then the duality of matrix/nuclear.v. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
