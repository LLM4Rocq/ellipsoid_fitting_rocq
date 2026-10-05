(* Definitions of the draft challenge paper_main_results: the glossary of
   the three main statements of the paper (arXiv 2608.10184v1, thm:main,
   thm:conditioned and cor:alternative), and nothing else. Every definition
   is concrete and is meant to be read by the reviewer; the README of the
   challenge reads each one in the paper's language.

   Vocabulary. Stdlib's R is the real field, read through MathComp's
   ring_scope: + - * / are the field operations, <= and < the (boolean)
   order, n%:R the real number n, \sum a finite sum. Vectors and matrices
   are MathComp's: 'cV[R]_d is the space of column vectors of length d,
   'M[R]_d the space of d x d real matrices, v i 0 and S i j their entries
   (indices i j : 'I_d, the integers below d), *m the matrix product, ^T the
   transpose, *: the scalar multiple, 1%:M the identity matrix. d is the
   true dimension: 'M[R]_0 is the zero-dimensional space.

   1. Linear algebra (paper section 1.1 and sec:notation): the quadratic
      form x^T S x, symmetry, S >= 0 (positive semidefinite), S > 0
      (positive definite), the Loewner order A <= B, and the trace.
   2. Samples and points: n independent standard Gaussian points of R^d are
      one tuple of n*d independent standard normal coordinates under
      gaussian_product_law (n*d) of GaussianProbabilityProductDefinitions,
      which is the law of n*d independent N(0,1) coordinates (a probability
      measure on tuples, checked in challenge gaussian_probability_product
      of the port). Point i is the block of d coordinates starting at index
      i*d.
   3. The three events of the paper, as sets of samples: the fit event of
      (P), the well-conditioned fit event of thm:conditioned, and the
      balanced positive definite combination event eq:alt-cor-event.
   4. Probability: p(n, d) is the gaussian_product_law (n*d) measure of the
      event, an extended real in [0, 1] when the event is measurable. The
      main statement asserts the measurability of every event it measures.
   5. Asymptotics, written out: a real sequence is eventually at most c,
      limsup < c, limsup <= c, liminf > c, and an extended-real sequence
      tends to a real l. They are the elementary equivalents of the
      limsup, liminf and limit conditions of the theorems.

   The module contains definitions only: no lemma, no Axiom, no Parameter,
   no Admitted. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* 1. Linear algebra. *)

(* The quadratic form v^T S v = sum_{i,j} v_i S_{ij} v_j. *)
Definition paper_main_quadratic_form {d : nat} (S : 'M[R]_d) (v : 'cV[R]_d) : R :=
  \sum_(i < d) \sum_(j < d) v i 0 * S i j * v j 0.

(* S is symmetric: S_{ij} = S_{ji}. The paper's S^d. *)
Definition paper_main_symmetric {d : nat} (S : 'M[R]_d) : Prop :=
  forall i j : 'I_d, S i j = S j i.

(* S >= 0: S is symmetric and v^T S v >= 0 for every v. The paper's S^d_+. *)
Definition paper_main_psd {d : nat} (S : 'M[R]_d) : Prop :=
  paper_main_symmetric S /\ forall v : 'cV[R]_d, 0 <= paper_main_quadratic_form S v.

(* S > 0: S is symmetric and v^T S v > 0 for every v <> 0. *)
Definition paper_main_pd {d : nat} (S : 'M[R]_d) : Prop :=
  paper_main_symmetric S /\
  forall v : 'cV[R]_d, v != 0 -> 0 < paper_main_quadratic_form S v.

(* The Loewner order A <= B: B - A >= 0. *)
Definition paper_main_loewner_le {d : nat} (A B : 'M[R]_d) : Prop :=
  paper_main_psd (B - A).

(* The trace sum_i S_{ii}. *)
Definition paper_main_trace {d : nat} (S : 'M[R]_d) : R :=
  \sum_(i < d) S i i.

(* 2. Samples and points. *)

(* A sample of n points of R^d: one tuple of n*d real coordinates, the
   coordinates of x_1, ..., x_n one point after the other. As a measurable
   type it carries the product sigma-algebra of the Borel sets of R; as a
   probability space it carries gaussian_product_law (n*d). It is a
   notation, so that MathComp finds that structure on the tuple type. *)
Notation paper_main_sample n d := ((n * d)%nat.-tuple (measurableTypeR R)).

(* Point i of the sample (i = 0, ..., n-1): the column vector of the d
   coordinates at positions i*d, ..., i*d + d - 1 of the tuple. *)
Definition paper_main_point {n d : nat} (x : paper_main_sample n d) (i : nat) : 'cV[R]_d :=
  \col_(j < d) List.nth (i * d + j)%nat (tval x) 0.

(* 3. The events. *)

(* (P) is feasible: there is S >= 0 with x_i^T S x_i = d for every i < n.
   No norm, trace or spectral restriction. *)
Definition paper_main_fit_event (n d : nat) : set (paper_main_sample n d) :=
  [set x | exists S : 'M[R]_d,
    paper_main_psd S /\
    forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = d%:R].

(* The same S fits, has trace d and satisfies lm I <= S <= lp I. *)
Definition paper_main_conditioned_event (n d : nat) (lm lp : R) : set (paper_main_sample n d) :=
  [set x | exists S : 'M[R]_d,
    paper_main_psd S /\
    (forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = d%:R) /\
    paper_main_trace S = d%:R /\
    paper_main_loewner_le (lm *: 1%:M) S /\
    paper_main_loewner_le S (lp *: 1%:M)].

(* eq:alt-cor-event: there are real weights y_1, ..., y_n with sum 0 such
   that sum_i y_i x_i x_i^T > 0. *)
Definition paper_main_balanced_pd_event (n d : nat) : set (paper_main_sample n d) :=
  [set x | exists y : 'I_n -> R,
    \sum_(i < n) y i = 0 /\
    paper_main_pd (\sum_(i < n) y i *: (paper_main_point x i *m (paper_main_point x i)^T))].

(* 4. Probability. *)

(* The probability of an event of samples under the law of n independent
   standard Gaussian points of R^d. An extended real; it is in [0, 1] for a
   measurable event. *)
Definition paper_main_probability (n d : nat) (E : set (paper_main_sample n d)) : \bar R :=
  gaussian_product_law (n * d) E.

(* 5. Asymptotics. *)

(* n(d) / d^2 for a sequence n : nat -> nat of sample sizes. *)
Definition paper_main_density (n : nat -> nat) (d : nat) : R :=
  (n d)%:R / d%:R ^+ 2.

(* u_d <= c for every large d. *)
Definition paper_main_eventually_le (u : nat -> R) (c : R) : Prop :=
  exists D : nat, forall d : nat, (D <= d)%nat -> u d <= c.

(* u_d >= c for every large d. *)
Definition paper_main_eventually_ge (u : nat -> R) (c : R) : Prop :=
  exists D : nat, forall d : nat, (D <= d)%nat -> c <= u d.

(* limsup_d u_d < c: some c' < c bounds u_d for every large d. *)
Definition paper_main_limsup_lt (u : nat -> R) (c : R) : Prop :=
  exists c' : R, c' < c /\ paper_main_eventually_le u c'.

(* limsup_d u_d <= c: for every eps > 0, u_d <= c + eps for every large d. *)
Definition paper_main_limsup_le (u : nat -> R) (c : R) : Prop :=
  forall eps : R, 0 < eps -> paper_main_eventually_le u (c + eps).

(* liminf_d u_d > c: some c' > c is below u_d for every large d. *)
Definition paper_main_liminf_gt (u : nat -> R) (c : R) : Prop :=
  exists c' : R, c < c' /\ paper_main_eventually_ge u c'.

(* p_d -> l as d -> oo, for an extended-real sequence and a real limit:
   for every eps > 0, |p_d - l| < eps for every large d. An infinite p_d
   never satisfies the bound. *)
Definition paper_main_tends_to (p : nat -> \bar R) (l : R) : Prop :=
  forall eps : R, 0 < eps ->
  exists D : nat, forall d : nat, (D <= d)%nat -> (`|p d - l%:E| < eps%:E)%E.
