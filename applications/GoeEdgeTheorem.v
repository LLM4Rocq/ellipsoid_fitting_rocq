From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals ereal.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.random_matrix Require Import goe_edge.
From GaussianApplications Require Import GoeEdgeStatement.

(**md**************************************************************************)
(* # Sharp upper edge of the GOE: the theorem                                 *)
(*                                                                            *)
(* Target T3 of phase 12. goe_edge_theorem proves goe_edge_statement of       *)
(* GoeEdgeStatement.v: for d >= 1, a of law gauss (d * d) and W = goe_mx a,   *)
(* the map a |-> lambda_max W is measurable and integrable, E lambda_max W <= *)
(* 2, P(lambda_max W >= 2 + t) and P(lambda_max (- W) >= 2 + t) are at most   *)
(* exp (- d t^2 / 4), and P(opnorm W >= 2 + t) <= 2 exp (- d t^2 / 4), for    *)
(* every t >= 0. Each conjunct is a result of                                 *)
(* library/random_matrix/goe_edge.v (goe_lambda_max_mean,                     *)
(* goe_lambda_max_tail, goe_lambda_maxN_tail, goe_opnorm_edge_tail), whose    *)
(* header describes the proof.                                                *)
(*                                                                            *)
(* A Rocq formalization of the credited argument of 'Cutoff throughout the    *)
(* high-temperature Sherrington-Kirkpatrick phase' (family 227 of the OpenAI  *)
(* math collection, revision 1581d4cbd): the lemma 'Gaussian concentration    *)
(* and comparison' and the first paragraph of the proof of the proposition    *)
(* 'Good disorder' (appendices/entropy.tex). The Lean modules that follow the *)
(* same argument, in lean/OAI/Probability/SKRatio of the collection:          *)
(* Lean: goe_expected_top (Matrices/DiagonalTMemLp.lean, line 93)             *)
(* Lean: goe_norm_tail (Matrices/GoeMatrixQuadCoeff.lean, line 115)           *)
(* The statement is at beta = 1 and has the sharp tail constant d / 4, where  *)
(* the TeX and the Lean modules have a constant with pi^2.                    *)
(******************************************************************************)

Theorem goe_edge_theorem : goe_edge_statement.
Proof.
move=> R d d0; split.
- by split; [exact: measurable_goe_lambda_max|exact: integrable_goe_lambda_max].
- exact: goe_lambda_max_mean.
- move=> t t0.
  by split; [exact: goe_lambda_max_tail|exact: goe_lambda_maxN_tail].
- by move=> t t0; exact: goe_opnorm_edge_tail.
Qed.
