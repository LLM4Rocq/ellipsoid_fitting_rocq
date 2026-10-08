From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals ereal.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.

(**md**************************************************************************)
(* # Uniform directions and the rotation invariance of the GOE                *)
(*                                                                            *)
(* Let g have law gauss n and v = g / |g|, a uniform point of the unit        *)
(* sphere. Item G6 of phase 5 replaces the Haar measure on the orthogonal     *)
(* group, which MathComp-Analysis does not have, in Lemma 5.13 of Koehler and *)
(* Sohn (arXiv 2608.27372, lines 5820-5860) by the moments of v and the       *)
(* invariance of the law of the GOE under conjugation by orthogonal matrices. *)
(*                                                                            *)
(* Planned results (phase 5, stage 2; names come with the proofs):            *)
(*                                                                            *)
(* - E v_i^2 = 1 / n, E v_i^4 = 3 / (n (n + 2)) and E v_i^2 v_j^2 = 1 / (n (n *)
(*   + 2)) for i != j, from the rotation invariance of gauss n                *)
(*   (gauss_orthogonal_law of comparison/gauss_law.v) and the independence of *)
(*   |g| and g / |g|.                                                         *)
(* - For A symmetric: E (v A v^T) = \tr A / n and E (v A v^T)^2 = ((\tr A)^2  *)
(*   + 2 \tr (A^2)) / (n (n + 2)).                                            *)
(* - The law of goe_mx a is invariant under W |-> Q W Q^T for every           *)
(*   orthogonal Q.                                                            *)
(* - For F from the symmetric matrices to the matrices with F (Q W Q^T) = Q F *)
(*   (W) Q^T for every orthogonal Q (for instance a continuous function of W  *)
(*   in the sense of the spectral calculus): E[(1 / d) \sum_j (F (W)_jj - \tr *)
(*   F (W) / d)^2] = (2 / (d + 2)) E[\tr (F (W)^2) / d - (\tr F (W) / d)^2],  *)
(*   so the diagonal of F (W) is nearly constant (Lemma 5.13 with a uniform   *)
(*   direction instead of a Haar matrix).                                     *)
(******************************************************************************)
