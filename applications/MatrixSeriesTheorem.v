From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals ereal exp.
From mathcomp Require Import measure lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import gauss.
From GaussianAnalysis.matrix Require Import opnorm.
From GaussianAnalysis.random_matrix Require Import matrix_series.
From GaussianApplications Require Import MatrixSeriesStatement.

(**md**************************************************************************)
(* # Gaussian matrix series: the theorem                                      *)
(*                                                                            *)
(* Target T1 of phase 12. matrix_series_theorem proves                        *)
(* matrix_series_statement of MatrixSeriesStatement.v from the library file   *)
(* random_matrix/matrix_series.v, which is a Rocq formalization of the        *)
(* credited argument of Lemma 4.2, 'A Gaussian matrix estimate', of           *)
(* 'Pointwise convergence of fourfold ergodic averages for mixing             *)
(* transformations' (family 154 of the OpenAI math collection, revision       *)
(* 1581d4cbd, sections/04-packing.tex). The collection has no Lean version of *)
(* it.                                                                        *)
(*                                                                            *)
(* - (a) is gauss_mx_series_moment, with H_j H_j = H_j^2.                     *)
(* - (b) is gauss_mx_series_opnorm.                                           *)
(* - (c) is gauss_mx_series_opnorm_log with C = 5: the hypothesis on the      *)
(*   maximum of the two operator norms gives each of them,                    *)
(*   2 tr (\sum_j B_j B_j^T) <= 2 d gives tr (\sum_j B_j B_j^T) <= d, and     *)
(*   sqrt (sqrt d) = d^(1/4).                                                 *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Theorem matrix_series_theorem : matrix_series_statement.
Proof.
move=> R; split.
- move=> n r H q Hs q0.
  have -> : \sum_(j < r) H j *m H j = \sum_(j < r) H j ^+ 2.
    by apply: eq_bigr => j _; rewrite expr2 mulmxE.
  exact: gauss_mx_series_moment.
- by move=> m p r B q q0; exact: gauss_mx_series_opnorm.
exists 5; split => // m p r B d d1 hs ht.
have d0 : 0 <= d by apply: le_trans d1.
have -> : Num.sqrt (Num.sqrt d) = d `^ 4^-1.
  rewrite -powR12_sqrt // -powR12_sqrt ?powR_ge0 // -powRrM.
  by congr (_ `^ _); field.
rewrite ge_max in hs; case/andP: hs => hs1 hs2.
have two : (0 : R) < 2 by [].
rewrite ler_pM2l // in ht.
exact: gauss_mx_series_opnorm_log.
Qed.
