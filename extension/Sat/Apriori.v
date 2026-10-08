(* The a priori estimates: Proposition 3.1 of Koehler and Sohn (arXiv
   2608.27372, lines 2133-2300 of arxiv_v1.tex), at Stdlib's R. Item S3 of
   stage 3 of phase 5 (lane C), with
   library/random_matrix/restricted_isometry.v.

   Plan (names come with the proofs). For x_1, ..., x_n i.i.d. with
   independent coordinates of laws universality_coordinate_law kappa K,
   n <= C0 d^2, W_i = (x_i x_i^T - I) / sqrt d, Q_I = (1/d) (<W_i, W_j>)
   for i, j in I, and X_I the d x |I| matrix of the x_i, i in I: for every
   C0' there is C such that, with probability tending to one,
   - sup_{|I| <= C0' d ln d} |Q_I - I|_op <= C (ln d)^(3/2) / sqrt d, from
     restricted_isometry applied to the columns sqrt (d/2) mxvec W_i, whose
     linear forms are subexponential by the Hanson-Wright inequality
     (requests/c-to-a.md), and the concentration of |x_i|^2 / d;
   - sup_{|I| <= C0' d ln d} |X_I|_op <= C sqrt d ln d, from the operator
     norm of a matrix with independent subgaussian entries
     (subgaussian_matrix.v, lane A) and a union bound over the subsets;
   - |L_X R| <= C sqrt d |R|_F for every R, with L_X R = (<W_i, R>)_i, and
     nuclear (L_X^* z) <= C d |z| for every z, from |W|_op <= C sqrt D and
     nuclear A <= sqrt d frobenius A (matrix/nuclear.v). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
