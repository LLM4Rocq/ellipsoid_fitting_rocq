From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.

(**md**************************************************************************)
(* # Sign and Gaussian patterns of the Ising perceptron: the definitions      *)
(*                                                                            *)
(* Target T6 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The definitions of the statement of     *)
(* PerceptronSignStatement.v, from 'The free energy of the Ising random       *)
(* perceptron' (family 222 of the OpenAI math collection, revision 1581d4cbd, *)
(* sections/model.tex, equation def:pressure, and sections/extensions.tex,    *)
(* Theorem ext:sign). The collection has no Lean version of it. R is any      *)
(* realType.                                                                  *)
(*                                                                            *)
(* - spin_col x is the column of the spins of x in {-1, 1}^N, x of {ffun 'I_N *)
(*   -> bool}.                                                                *)
(* - perceptron_pressure f G = (1/N) ln (2^(-N) sum_x exp (sum_mu f ((G x)_mu *)
(*   / sqrt N))), for patterns G of 'M[R]_(M, N), with rows g^1, ..., g^M,    *)
(*   and a potential f : R -> R: the normalized pressure p_N(f) of the        *)
(*   manuscript, with the uniform probability on the cube and b_mu(x) =       *)
(*   <g^mu, x> / sqrt N, at M patterns.                                       *)
(* - gauss_pressure M N f is its expectation under Gaussian patterns: G =     *)
(*   vec_mx g, with g of law gauss (M * N), so that the M N entries of G are  *)
(*   independent standard normal. sign_pressure M N f is its expectation      *)
(*   under sign patterns: the average over the 2^(M N) matrices of entries in *)
(*   {-1, 1}, so that the entries are independent uniform signs.              *)
(* - bounded_C3 f B0 B1 B2 B3: f has derivatives f', f'' and f''' everywhere, *)
(*   f''' is continuous (f is of class C^3), and |f| <= B0, |f'| <= B1, |f''| *)
(*   <= B2, |f'''| <= B3 on R.                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

Section perceptron_sign_definitions.
Variable R : realType.
Implicit Types M N : nat.

Definition spin_col N (x : {ffun 'I_N -> bool}) : 'cV[R]_N :=
  \col_i (if x i then 1 else -1).

Definition perceptron_pressure M N (f : R -> R) (G : 'M[R]_(M, N)) : R :=
  N%:R^-1 * ln ((2 ^+ N)^-1 * \sum_(x : {ffun 'I_N -> bool})
    expR (\sum_(mu < M) f ((G *m spin_col x) mu 0 / Num.sqrt N%:R))).

Definition gauss_pressure M N (f : R -> R) : R :=
  \int[gauss (M * N)]_g perceptron_pressure f (vec_mx g).

Definition sign_pressure M N (f : R -> R) : R :=
  (2 ^+ (M * N))^-1 * \sum_(s : {ffun 'I_M * 'I_N -> bool})
    perceptron_pressure f (\matrix_(mu, i) (if s (mu, i) then 1 else -1)).

Definition bounded_C3 (f : R -> R) (B0 B1 B2 B3 : R) : Prop :=
  exists f1 f2 f3 : R -> R,
  [/\ forall x : R, is_derive x 1 f (f1 x),
      forall x : R, is_derive x 1 f1 (f2 x),
      forall x : R, is_derive x 1 f2 (f3 x),
      continuous f3 &
      forall x : R,
        [/\ `|f x| <= B0, `|f1 x| <= B1, `|f2 x| <= B2 & `|f3 x| <= B3]].

End perceptron_sign_definitions.
