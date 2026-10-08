(* Proposition 3.4 of Koehler and Sohn, "Universality and sharp thresholds
   for ellipsoid fitting" (arXiv 2608.27372, lines 2436-2450, proof lines
   3610-3805 of arxiv_v1.tex): the light-tail quotient-norm lower bound.
   Item S9 of stage 3 of phase 5 (lane B). This file holds the plan; the
   proofs come next.

   Statement. Let x_1, ..., x_n be the points of a sample whose coordinates
   are independent with laws universality_coordinate_law kappa K0, and let
   n / d^2 tend to alpha in (0, 1/2). There are K > 0 and gamma > 0,
   depending only on alpha and K0, such that for every C0 > 0, with
   probability tending to one: for every set I of at most C0 d ln d rows,
   every t with t_i = 0 on I and |t|_oo <= (K d)^(-1/2) |t|_2, and every h
   with h_i = 0 outside I and |h|_1 <= d^(2/3) |t|_2, the nuclear norm of
   L_X^* (h + t) = d^(-1/2) sum_i (h + t)_i (x_i x_i^T - I) is at least
   gamma d |t|_2.

   Plan of the proof, as in the paper.
   - Blocks. The columns are cut into L blocks I_1, ..., I_L of sizes
     d / L + O(1). Stage l = 2, ..., L reveals the rows of I and the
     columns U_l = I_1 + ... + I_(l-1); its fresh block is I_l, and the
     U_l x I_l block of L_X^* lambda is stage_map of Sat/OneStage.v. The
     nuclear norm of a block is at most that of the whole matrix.
   - Good events. G_l asks that the first (1 - eps) p_l sorted eigenvalues
     (spec, library/matrix/von_neumann.v) of
     Sigma_(t, l) = sum_i t_i^2 u_(i, l)^T u_(i, l) be at least mu, and
     that |t_i| |u_(i, l)| <= rho. Each eigenvalue is a Lipschitz function
     of the matrix (spec_lipschitz), so G_l is closed in the revealed
     coordinates; spec_decomposition gives the matrix Q that
     stage_small_ball (Lemma 3.14) takes.
   - A fixed pair. For fixed I, t and h, the events that the block l of
     L_X^* (h + t) has nuclear norm at most 2 gamma d and that G_l holds
     occur together for every l with probability at most
     (C gamma)^((1 - eps) D_L), D_L = sum_l p_l q_l, by stage_small_ball
     at each stage and the sequential revealing of the stages
     (tuple_prod_chain_le, library/probability/conditioning.v).
   - Nets. Nets of the light unit tails of size (C / gamma)^n and of the
     heads of size exp (o(d^2)), the bounds of Proposition 3.1 (iii) (lane
     C, Sat/Apriori) and max_i |x_i|^2 <= 2 d to pass from the nets to all
     pairs, a union bound over the sets I, and the choice of L, eps, gamma
     and K with alpha < (1 - eps) (1 - 1/L) / 2.
   Inputs of lane C (requests/b-to-c.md): Corollary 3.13 in the form of the
   sorted eigenvalues, and Proposition 3.1 (iii). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From GaussianAnalysis Require Import euclidean opnorm von_neumann.
From GaussianAnalysis Require Import lindeberg tuple_rows conditioning.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Sat Require Import OneStage.
