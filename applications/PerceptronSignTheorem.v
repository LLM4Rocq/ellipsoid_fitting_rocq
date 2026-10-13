From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianApplications Require Import PerceptronSignDefinitions.
From GaussianApplications Require Import PerceptronSignStatement.
From GaussianApplications.Perceptron Require Import Pressure.

(**md**************************************************************************)
(* # Sign and Gaussian patterns of the Ising perceptron: the theorem          *)
(*                                                                            *)
(* Target T6 of phase 12. perceptron_sign_theorem proves                      *)
(* perceptron_sign_statement of PerceptronSignStatement.v from                *)
(* perceptron_sign_compare of Perceptron/Pressure.v, a Rocq formalization of  *)
(* the credited argument of the first paragraph of the proof of Theorem       *)
(* ext:sign of 'The free energy of the Ising random perceptron' (family 222   *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* sections/extensions.tex). The collection has no Lean version of it.        *)
(*                                                                            *)
(* The constant is C = 1 + (|B3| + 6 |B1| |B2| + 6 |B1|^3) / 2: it is         *)
(* positive for all bounds, and when bounded_C3 f B0 B1 B2 B3 holds the       *)
(* bounds are nonnegative, so C is at least the constant                      *)
(* (B3 + 6 B1 B2 + 6 B1^3) / 2 of perceptron_sign_compare. The continuity of  *)
(* f''' in bounded_C3 is not used.                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Theorem perceptron_sign_theorem : perceptron_sign_statement.
Proof.
move=> R B0 B1 B2 B3.
pose K := `|B3| + 6 * `|B1| * `|B2| + 6 * `|B1| ^+ 3.
have K0 : 0 <= K by rewrite /K !addr_ge0 // ?mulr_ge0 // exprn_ge0.
exists (1 + K / 2); split.
  by apply: (lt_le_trans ltr01); rewrite lerDl divr_ge0.
move=> f M N [f1 [f2 [f3 [df df1 df2 _ fB]]]] N0.
have fB0 x : `|f x| <= B0 by case: (fB x).
have fB1 x : `|f1 x| <= B1 by case: (fB x).
have fB2 x : `|f2 x| <= B2 by case: (fB x).
have fB3 x : `|f3 x| <= B3 by case: (fB x).
have [iP cP] := perceptron_sign_compare M N0 df df1 df2 fB0 fB1 fB2 fB3.
split=> //; apply: le_trans cP _.
apply: ler_wpM2r; first exact: powR_ge0.
apply: ler_wpM2r; first exact: ler0n.
have b1 : 0 <= B1 := le_trans (normr_ge0 _) (fB1 0).
have b2 : 0 <= B2 := le_trans (normr_ge0 _) (fB2 0).
have b3 : 0 <= B3 := le_trans (normr_ge0 _) (fB3 0).
rewrite /K !ger0_norm //.
by move: (B3 + _ + _) => k; lra.
Qed.
