From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import reals sequences.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.random_matrix Require Import goe.

(**md**************************************************************************)
(* # The spectral gap of the SK heat-bath dynamics: the definitions           *)
(*                                                                            *)
(* Target T4 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The definitions of the statement of     *)
(* SKGapStatement.v, from 'Cutoff throughout the high-temperature             *)
(* Sherrington-Kirkpatrick phase' (family 227 of the OpenAI math collection,  *)
(* revision 1581d4cbd): sections/02-model-inputs.tex, subsection 'Two clocks  *)
(* and the Dirichlet form', and appendices/entropy.tex, subsection 'A two-    *)
(* spin estimate and a uniform gap'. The Lean counterparts, in                *)
(* lean/OAI/Probability/SKRatio of the collection:                            *)
(* Lean: weight, mass, expectation, variance, dirichlet (Matrices/Spin.lean)  *)
(* Lean: spinGradient (Calculus/Expectation.lean)                             *)
(*                                                                            *)
(* All are finite sums over the cube; R is any realType.                      *)
(*                                                                            *)
(* - The cube {-1, 1}^n is {ffun 'I_n -> bool}. spin b is 1 for true and -1   *)
(*   for false, and spin_vec x is the column of the spins of x. spin_set x i  *)
(*   b sets the spin i of x to b: the manuscript's x^(i,+) and x^(i,-) are    *)
(*   spin_set x i true and spin_set x i false.                                *)
(* - The Ising law nu of a matrix A of 'M[R]_n and a field theta of 'cV[R]_n: *)
(*   ising_weight A theta x = exp (x^T A x / 2 + <theta, x>), ising_mass A    *)
(*   theta x is ising_weight A theta x divided by the sum of the weights,     *)
(*   ising_mean A theta f = sum_x nu(x) f(x), and ising_var A theta f = nu[(f *)
(*   - nu[f])^2]. The statement takes A = s J with J symmetric of zero        *)
(*   diagonal, as the manuscript does; the definitions make sense for every   *)
(*   A.                                                                       *)
(* - half_diff i f x = (f (x^(i,+)) - f (x^(i,-))) / 2 is the half-difference *)
(*   d_i f of the manuscript.                                                 *)
(* - ising_cond_mean A theta i x = (w (x^(i,+)) - w (x^(i,-))) / (w (x^(i,+)) *)
(*   + w (x^(i,-))), with w = ising_weight A theta, is the conditional mean   *)
(*   m_i of the spin i given the other spins under nu; it is tanh ((A x)_i +  *)
(*   theta_i) when A is symmetric and A_ii = 0. ising_cond_var A theta i x =  *)
(*   1 - m_i^2 is v_i, the conditional variance of the spin i.                *)
(* - ising_dirichlet A theta f = sum_i nu[v_i (d_i f)^2] is the Dirichlet     *)
(*   form of the heat-bath dynamics with rate one at every site (the          *)
(*   manuscript's equation model-dirichlet); for a law of full support, such  *)
(*   as nu, it is sum_i nu[Var(f | x_(-i))], the form of the Lean module.     *)
(* - ising_cov A theta is the covariance matrix of the spins under nu: its    *)
(*   entry (i, j) is nu[x_i x_j] - nu[x_i] nu[x_j].                           *)
(* - sk_coupling beta a = beta (W - Diag W), with W = goe_mx a                *)
(*   (random_matrix/goe.v). For a of law gauss (n * n), its entries J_ij, i < *)
(*   j, are independent centered normal of variance beta^2 / n, with J_ji =   *)
(*   J_ij and J_ii = 0: the disorder of the manuscript.                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section sk_gap_definitions.
Variable R : realType.
Implicit Types n : nat.

Definition spin (b : bool) : R := if b then 1 else -1.

Definition spin_vec n (x : {ffun 'I_n -> bool}) : 'cV[R]_n :=
  \col_i spin (x i).

Definition spin_set n (x : {ffun 'I_n -> bool}) (i : 'I_n) (b : bool) :
    {ffun 'I_n -> bool} :=
  [ffun j => if j == i then b else x j].

Definition ising_weight n (A : 'M[R]_n) (theta : 'cV[R]_n)
    (x : {ffun 'I_n -> bool}) : R :=
  expR (mxdot (spin_vec x) (A *m spin_vec x) / 2 + mxdot theta (spin_vec x)).

Definition ising_mass n (A : 'M[R]_n) (theta : 'cV[R]_n)
    (x : {ffun 'I_n -> bool}) : R :=
  ising_weight A theta x / \sum_(y : {ffun 'I_n -> bool}) ising_weight A theta y.

Definition ising_mean n (A : 'M[R]_n) (theta : 'cV[R]_n)
    (f : {ffun 'I_n -> bool} -> R) : R :=
  \sum_(x : {ffun 'I_n -> bool}) ising_mass A theta x * f x.

Definition ising_var n (A : 'M[R]_n) (theta : 'cV[R]_n)
    (f : {ffun 'I_n -> bool} -> R) : R :=
  ising_mean A theta (fun x => (f x - ising_mean A theta f) ^+ 2).

Definition half_diff n (i : 'I_n) (f : {ffun 'I_n -> bool} -> R)
    (x : {ffun 'I_n -> bool}) : R :=
  (f (spin_set x i true) - f (spin_set x i false)) / 2.

Definition ising_cond_mean n (A : 'M[R]_n) (theta : 'cV[R]_n) (i : 'I_n)
    (x : {ffun 'I_n -> bool}) : R :=
  (ising_weight A theta (spin_set x i true) -
     ising_weight A theta (spin_set x i false)) /
  (ising_weight A theta (spin_set x i true) +
     ising_weight A theta (spin_set x i false)).

Definition ising_cond_var n (A : 'M[R]_n) (theta : 'cV[R]_n) (i : 'I_n)
    (x : {ffun 'I_n -> bool}) : R :=
  1 - ising_cond_mean A theta i x ^+ 2.

Definition ising_dirichlet n (A : 'M[R]_n) (theta : 'cV[R]_n)
    (f : {ffun 'I_n -> bool} -> R) : R :=
  \sum_(i < n) ising_mean A theta
    (fun x => ising_cond_var A theta i x * half_diff i f x ^+ 2).

Definition ising_cov n (A : 'M[R]_n) (theta : 'cV[R]_n) : 'M[R]_n :=
  \matrix_(i, j)
    (ising_mean A theta (fun x => spin (x i) * spin (x j)) -
     ising_mean A theta (fun x => spin (x i)) *
     ising_mean A theta (fun x => spin (x j))).

Definition sk_coupling n (beta : R) (a : 'rV[R]_(n * n)) : 'M[R]_n :=
  beta *: (goe_mx a - diag_mx (\row_i goe_mx a i i)).

End sk_gap_definitions.
