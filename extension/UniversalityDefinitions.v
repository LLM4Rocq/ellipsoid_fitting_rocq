(* The glossary of the universality statement of Koehler and Sohn,
   "Universality and sharp thresholds for ellipsoid fitting" (arXiv
   2608.27372, Theorem 1.2, lines 164-190 of arxiv_v1.tex), and nothing
   else. Every definition is concrete and is meant to be read by the
   reviewer; the comment of UniversalityStatement reads the statement in the
   paper's language. This module reuses the definitions of
   PaperMainDefinitions that do not depend on the law of the data: the
   quadratic form, symmetry, positive semidefiniteness and definiteness, the
   Loewner order, the trace, the samples and their points, the fit event, the
   probability-free asymptotic conditions.

   Vocabulary. Stdlib's R is the real field, read through MathComp's
   ring_scope, as in PaperMainDefinitions: + - * / are the field operations,
   <= and < the boolean order, n%:R the real number n, x ^+ k the power,
   Num.sqrt the square root (0 on negative numbers), `|x| the absolute
   value, \sum a finite sum, sup and inf MathComp's least upper and greatest
   lower bounds of a set of reals (0 for a set that is empty or unbounded on
   that side), expR the exponential and pi the number pi of
   MathComp-Analysis. A probability measure on the Borel sets of R is a
   probability (measurableTypeR R) R, and 'E_mu[X] is the expectation of
   MathComp-Analysis, an extended real (the integral of X against mu).

   1. Coordinate laws (paper lines 160-171). A law mu of one coordinate is
      admissible with fourth moment kappa and subgaussian constant K when
      E X = 0, E X^2 = 1, E X^4 = kappa and E exp (X^2 / K^2) <= 2. The last
      condition is the paper's bound ||X||_{psi_2} <= K on the subgaussian
      norm inf {t > 0 : E exp (X^2 / t^2) <= 2} (line 162); the two are
      equivalent for K > 0 by monotone convergence, which is not proved
      here. It makes every power of X integrable, so the three moment
      equations are equations between finite numbers.
   2. The product laws. The law of n independent coordinates with laws
      mu 0, ..., mu (n-1) is tuple_prod of the library (GaussianAnalysis,
      probability/lindeberg.v): the same construction as the frozen
      gaussian_product_law, a binary product of MathComp-Analysis and the
      image under (x, xs) |-> x :: xs, on the same tuple type. A sample of
      n points of R^d whose coordinate j has law nu j, the same for every
      point, is the product of the laws nu (k mod d) over the n*d
      coordinates, on paper_main_sample n d, read as PaperMainDefinitions
      reads it: point i is the block of d coordinates starting at index i*d.
      The paper's data x_1, ..., x_n are i.i.d. and x_1 has independent
      coordinates whose laws may depend on the coordinate (line 169 takes a
      supremum over j) and on d (line 171 only asks that kappa and K do not
      depend on n and d): the statement quantifies over such families.
   3. The semicircle law and the threshold (paper lines 343-404). nu is the
      law on [-sqrt 2, sqrt 2] with density sqrt (2 - x^2) / pi; MathComp's
      square root is 0 on negative numbers, so the indicator of the support
      is not written. m(w) and s(w) are the integrals of (x - w)_+ and
      (x - w)_+^2 against nu, and E_kappa(w) = s(w) + (kappa - 3)/2 m(w)^2.
      The paper defines omega_kappa as the unique solution in
      [-sqrt 2, sqrt 2] of w = (kappa - 3)/2 m(w) (lines 373-376) and
      omega_{alpha,kappa} as the unique solution below sqrt 2 of
      E_kappa(w) = alpha (lines 401-404); both uniqueness claims are
      Proposition 5.10 of the paper (lines 5312-5349), proved there from
      the strict monotonicity of w - (kappa - 3)/2 m(w) and of E_kappa.
      Here the two numbers are the least upper bounds of the half-lines
      {w | w <= (kappa - 3)/2 m(w)} and {w < sqrt 2 | alpha <= E_kappa(w)},
      which are the paper's solutions when the monotonicity holds (for
      kappa > 1 and alpha > 0) and are real numbers in every case. The
      threshold is alpha*(kappa) = E_kappa(omega_kappa)
      (eq:alpha-star-scalar-main, lines 364-372): this is the primary
      definition, because the limiting error e*(alpha, kappa) =
      (2/alpha) ((kappa - 3)/2 m(omega_{alpha,kappa}) -
      omega_{alpha,kappa})_+^2 (lines 394-404) is built from the same
      functions. The variational representation of
      lines 380-389, the supremum of (int x f dnu)^2 / (int f^2 dnu +
      (kappa - 3)/2) over f >= 0 in L^2(nu) with int f dnu = 1, which the
      paper's Theorem 1.2 cites as the definition (line 173) and proves
      equal to the former in Proposition 5.10 (ii), is also defined, as
      universality_alpha_star_variational; the equality of the two is a
      theorem of the paper, not a definition. The square integrability of
      f and the integrability of f against nu are MathComp's integrable
      predicates, which include measurability; the integral of x f(x) is
      then finite by Cauchy-Schwarz and is not assumed.
   4. The optimal squared fitting error of a sample (eq:thm:least:squares,
      lines 183-187): the infimum over S >= 0 with trace d and r >= 0 of
      (1/n) sum_i (x_i^T S x_i / sqrt d - r)^2.
   5. The events, as sets of samples. The paper's fit is x_i^T R x_i = 1
      (line 178); the frozen fit event of PaperMainDefinitions asks for
      value d. For d >= 1 the two events are equal up to the scaling
      R |-> d R, which preserves positive semidefiniteness, so the frozen
      event is reused for the unsatisfiable claim. For the satisfiable
      claim, which asks for a positive definite fit (line 178) with
      condition number O(1) (line 180), two new events are defined with the
      paper's value 1: a positive definite fit, and a fit S with
      lm I <= S <= c lm I for some lm > 0, that is a positive definite fit
      of condition number at most c. The error event is
      |Gamma_X - e| > eps.
   6. Asymptotics. The paper assumes n/d^2 -> alpha (line 172); this
      convergence of the real sequence n(d)/d^2 is written out, with the
      density paper_main_density of PaperMainDefinitions. The limits of
      probabilities are paper_main_tends_to.

   The module contains definitions only: no lemma, no Axiom, no Parameter,
   no Admitted. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution sequences trigo.
From GaussianAnalysis Require Import lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* 1. Coordinate laws. *)

(* The functions x |-> x^k and x |-> exp (x^2 / K^2) on the Borel line,
   whose expectations the class uses. *)
Definition universality_power (k : nat) (x : measurableTypeR R) : R := (x : R) ^+ k.

Definition universality_subgaussian_test (K : R) (x : measurableTypeR R) : R :=
  expR ((x : R) ^+ 2 / K ^+ 2).

(* mu has mean 0, variance 1, fourth moment kappa and subgaussian norm at
   most K: E X = 0, E X^2 = 1, E X^4 = kappa and E exp (X^2 / K^2) <= 2. *)
Definition universality_coordinate_law (kappa K : R)
    (mu : probability (measurableTypeR R) R) : Prop :=
  0 < K /\
  ('E_mu[universality_power 1])%E = 0%:E /\
  ('E_mu[universality_power 2])%E = 1%:E /\
  ('E_mu[universality_power 4])%E = kappa%:E /\
  (('E_mu[universality_subgaussian_test K])%E <= (2%:R)%:E)%E.

(* 2. The product laws. *)

(* The law of n independent coordinates with laws mu 0, ..., mu (n-1), a
   probability measure on n-tuples: tuple_prod of the library. *)
Definition universality_product_law (mu : nat -> probability (measurableTypeR R) R)
    (n : nat) : probability (n.-tuple (measurableTypeR R)) R :=
  tuple_prod mu n.

(* The law of a sample of n points of R^d whose coordinate j has law nu j
   for every point: coordinate k of the tuple, which is coordinate k mod d
   of point k / d, has law nu (k mod d). *)
Definition universality_sample_law (nu : nat -> probability (measurableTypeR R) R)
    (n d : nat) : probability (paper_main_sample n d) R :=
  universality_product_law (fun k => nu (k %% d)%N) (n * d).

(* The probability of an event of samples under that law. An extended
   real; it is in [0, 1] for a measurable event. *)
Definition universality_probability (nu : nat -> probability (measurableTypeR R) R)
    (n d : nat) (E : set (paper_main_sample n d)) : \bar R :=
  universality_sample_law nu n d E.

(* 3. The semicircle law and the threshold. *)

(* The positive part (x)_+ = max (x, 0). *)
Definition universality_positive_part (x : R) : R := Num.max x 0.

(* The density of the semicircle law nu on [-sqrt 2, sqrt 2]: it is 0
   outside, since Num.sqrt is 0 on negative numbers. *)
Definition universality_semicircle_density (x : R) : R :=
  Num.sqrt (2%:R - x ^+ 2) / pi.

(* The integral of f against nu, as a real number. *)
Definition universality_semicircle_integral (f : R -> R) : R :=
  \int[lebesgue_measure]_x (f x * universality_semicircle_density x).

(* f is integrable against nu (this includes measurability). *)
Definition universality_semicircle_integrable (f : R -> R) : Prop :=
  lebesgue_measure.-integrable setT
    (fun x : measurableTypeR R => (f x * universality_semicircle_density x)%:E).

(* m(w) = int (x - w)_+ dnu(x) and s(w) = int (x - w)_+^2 dnu(x). *)
Definition universality_m (w : R) : R :=
  universality_semicircle_integral (fun x => universality_positive_part (x - w)).

Definition universality_s (w : R) : R :=
  universality_semicircle_integral (fun x => universality_positive_part (x - w) ^+ 2).

(* E_kappa(w) = s(w) + (kappa - 3)/2 m(w)^2. *)
Definition universality_energy (kappa w : R) : R :=
  universality_s w + (kappa - 3%:R) / 2%:R * universality_m w ^+ 2.

(* omega_kappa, the solution of w = (kappa - 3)/2 m(w): the least upper
   bound of {w | w <= (kappa - 3)/2 m(w)}. *)
Definition universality_cutoff (kappa : R) : R :=
  sup [set w : R | w <= (kappa - 3%:R) / 2%:R * universality_m w].

(* alpha*(kappa) = E_kappa(omega_kappa). *)
Definition universality_alpha_star (kappa : R) : R :=
  universality_energy kappa (universality_cutoff kappa).

(* The variational representation of alpha*(kappa): the supremum over
   f >= 0, square integrable against nu with int f dnu = 1, of
   (int x f(x) dnu(x))^2 / (int f(x)^2 dnu(x) + (kappa - 3)/2). *)
Definition universality_alpha_star_variational (kappa : R) : R :=
  sup [set r : R | exists f : R -> R,
    (forall x : R, 0 <= f x) /\
    universality_semicircle_integrable f /\
    universality_semicircle_integrable (fun x => f x ^+ 2) /\
    universality_semicircle_integral f = 1 /\
    r = universality_semicircle_integral (fun x => x * f x) ^+ 2 /
        (universality_semicircle_integral (fun x => f x ^+ 2) + (kappa - 3%:R) / 2%:R)].

(* omega_{alpha,kappa}, the solution below sqrt 2 of E_kappa(w) = alpha:
   the least upper bound of {w < sqrt 2 | alpha <= E_kappa(w)}. *)
Definition universality_level_cutoff (alpha kappa : R) : R :=
  sup [set w : R | w < Num.sqrt 2%:R /\ alpha <= universality_energy kappa w].

(* e*(alpha, kappa) = (2/alpha) ((kappa - 3)/2 m(omega_{alpha,kappa})
   - omega_{alpha,kappa})_+^2. *)
Definition universality_e_star (alpha kappa : R) : R :=
  2%:R / alpha *
  universality_positive_part
    ((kappa - 3%:R) / 2%:R * universality_m (universality_level_cutoff alpha kappa)
     - universality_level_cutoff alpha kappa) ^+ 2.

(* 4. The optimal squared fitting error. *)

(* Gamma_X: the infimum over S >= 0 with trace d and r >= 0 of
   (1/n) sum_i (x_i^T S x_i / sqrt d - r)^2. *)
Definition universality_fitting_error (n d : nat) (x : paper_main_sample n d) : R :=
  inf [set v : R | exists (S : 'M[R]_d) (r : R),
    paper_main_psd S /\ paper_main_trace S = d%:R /\ 0 <= r /\
    v = (\sum_(i < n)
          (paper_main_quadratic_form S (paper_main_point x i) / Num.sqrt d%:R - r) ^+ 2)
        / n%:R].

(* 5. The events. *)

(* A positive definite fit with value 1: S > 0 with x_i^T S x_i = 1 for
   every i < n. *)
Definition universality_pd_fit_event (n d : nat) : set (paper_main_sample n d) :=
  [set x | exists S : 'M[R]_d,
    paper_main_pd S /\
    forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = 1].

(* A positive definite fit of condition number at most c: some S and some
   lm > 0 with lm I <= S <= c lm I and x_i^T S x_i = 1 for every i < n. *)
Definition universality_conditioned_fit_event (n d : nat) (c : R) :
    set (paper_main_sample n d) :=
  [set x | exists (S : 'M[R]_d) (lm : R),
    0 < lm /\
    paper_main_loewner_le (lm *: 1%:M) S /\
    paper_main_loewner_le S ((c * lm) *: 1%:M) /\
    forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = 1].

(* The optimal squared fitting error is farther than eps from e. *)
Definition universality_error_event (n d : nat) (e eps : R) : set (paper_main_sample n d) :=
  [set x | eps < `|universality_fitting_error n d x - e|].

(* 6. Asymptotics. *)

(* n(d) / d^2 -> alpha: for every eps > 0, |n(d)/d^2 - alpha| < eps for
   every large d. *)
Definition universality_density_tends_to (n : nat -> nat) (alpha : R) : Prop :=
  forall eps : R, 0 < eps ->
  exists D : nat, forall d : nat, (D <= d)%nat -> `|paper_main_density n d - alpha| < eps.
