(* The small-residual interpolation: Theorem 2.3 (lines 878-893, proof
   lines 2464-2528, the shelling argument) and Theorem 1.9 (proof lines
   957-974) of Koehler and Sohn (arXiv 2608.27372), at Stdlib's R. Item S10
   of stage 3 of phase 5 (lane C).

   Plan (names come with the proofs).
   - Theorem 2.3: if n / d^2 -> alpha < 1/2, with probability tending to
     one every lambda in R^n splits into its C d ln d largest coordinates,
     the head h, and the rest, the tail t, with
       nuclear (L_X^* lambda) >= c (sqrt d / (ln d)^4 |h|_1 + d |t|_2).
     Shelling: move the largest coordinates into the head until the tail is
     K-light (|t|_oo <= (K d)^(-1/2) |t|_2) or negligible; then
     Proposition 3.3 (Sat/SparseLower) for the head, Proposition 3.4 (item
     S9 of lane B) for the light tail, and the a priori estimates
     (Sat/Apriori).
   - Theorem 1.9: with probability tending to one, every y in the range of
     A_X = P_{1^perp} L_X is A_X Delta_y for a symmetric Delta_y with
     opnorm Delta_y <= C ((ln d)^4 / sqrt d |y|_oo + |y|_2 / d), by
     the range duality of matrix/nuclear.v and Theorem 2.3. Lane A's
     Sat/Universality (S11) uses it with the residual of Proposition 2.1. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
