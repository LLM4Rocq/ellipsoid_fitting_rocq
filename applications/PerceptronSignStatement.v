From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianApplications Require Import PerceptronSignDefinitions.

(**md**************************************************************************)
(* # Sign and Gaussian patterns of the Ising perceptron: the statement        *)
(*                                                                            *)
(* Target T6 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The statement of a Rocq formalization   *)
(* of the credited argument of the first paragraph of the proof of Theorem    *)
(* ext:sign of 'The free energy of the Ising random perceptron' (family 222   *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* sections/extensions.tex): the coordinate-replacement form of the Lindeberg *)
(* principle, with a third-derivative bound C N^(-5/2) in one pattern entry.  *)
(* The collection has no Lean version of it. This file holds the statement    *)
(* only; its definitions are those of PerceptronSignDefinitions.v.            *)
(*                                                                            *)
(* perceptron_sign_statement, for every R and all bounds B0, B1, B2, B3:      *)
(* there is C > 0 such that for every potential f of class C^3 with |f| <=    *)
(* B0, |f'| <= B1, |f''| <= B2 and |f'''| <= B3 (bounded_C3), every number of *)
(* patterns M and every N >= 1,                                               *)
(*                                                                            *)
(* (a) g |-> p_N(vec_mx g, f) is integrable against gauss (M * N), so that    *)
(* gauss_pressure M N f is the expectation of the pressure under Gaussian     *)
(* patterns;                                                                  *)
(*                                                                            *)
(* (b) |E_sign p_N - E_Gauss p_N| <= C M N^(-3/2), the power being powR.      *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - The constant C depends only on the four bounds, uniformly in M and N, as *)
(*   the user asked (formally also on R).                                     *)
(* - The class of potentials: f of class C^3 with f, f', f'' and f'''         *)
(*   bounded, which contains the manuscript's C_c^infinity, as the user       *)
(*   accepted. The extension to bounded Borel potentials whose                *)
(*   discontinuities form a Gaussian-null set, the rest of Theorem ext:sign,  *)
(*   is not part of the statement; for arbitrary bounded Borel potentials the *)
(*   comparison fails, as the manuscript remarks.                             *)
(* - M is arbitrary, not M_N = floor (alpha N): with M_N N entries, (b) is    *)
(*   the manuscript's error O_f(N^(-1/2)).                                    *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition perceptron_sign_statement : Prop :=
  forall (R : realType) (B0 B1 B2 B3 : R),
  exists C : R, 0 < C /\
  forall (f : R -> R) (M N : nat), bounded_C3 f B0 B1 B2 B3 -> (0 < N)%N ->
    (gauss (M * N)).-integrable [set: 'rV[R]_(M * N)]
      (EFin \o (fun g : 'rV[R]_(M * N) => perceptron_pressure f (vec_mx g))) /\
    `|sign_pressure M N f - gauss_pressure M N f| <=
      C * M%:R * N%:R `^ (- (3 / 2)).
