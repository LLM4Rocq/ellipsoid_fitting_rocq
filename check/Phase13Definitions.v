(* The project definitions that the frozen statements of phase 13 and the
   accepted general statements of its packets unfold to, characterized by
   properties that determine them (AGENTS.md, section Phase 13, step 0,
   item 5; the plan notes/phase13-plan.md, section 4.4).

   Each lemma states its property in this file, written out down to the
   definitions of MathComp and MathComp-Analysis, and is proved by
   computation (by []). make check compiles the file into
   build/phase13_definitions.txt, a required output, so it fails unless
   each definition still computes to the text written here: after a change
   of its meaning, and also after a change of its implementation that keeps
   the meaning but not the computation. scripts/check_sources.py fixes the
   code of this file. Each freeze extends it, and the code of every earlier
   freeze stays an unchanged prefix.

   Freeze 1, the definitions of packet S (batch 1):
   - unif_mean (probability/finite_mean.v): #|T|^-1 times the sum of the
     values.
   - unif_var (probability/finite_mean.v): the uniform mean of the squared
     deviations from the uniform mean.
   - binomial_mean (probability/binomial_mean.v): the sum over j <= m of
     the binomial weights C(m, j) p^j (1 - p)^(m - j) times f j.
   - linear_op, monotone_op (probability/commuting_operators.v): pointwise
     additivity and homogeneity, and pointwise monotonicity, of an
     operator on the functions X -> R.
   - meet_avg (probability/commuting_operators.v): the uniform mean over the
     members E c of a finite family of f (S :&: E c). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From GaussianAnalysis.probability Require Import finite_mean binomial_mean.
From GaussianAnalysis.probability Require Import commuting_operators.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma unif_mean_characterization (R : realFieldType) (T : finType)
    (f : T -> R) :
  unif_mean f = (#|T|%:R)^-1 * \sum_(x : T) f x.
Proof. by []. Qed.

Lemma unif_var_characterization (R : realFieldType) (T : finType)
    (f : T -> R) :
  unif_var f =
  (#|T|%:R)^-1 * \sum_(x : T) (f x - (#|T|%:R)^-1 * \sum_(y : T) f y) ^+ 2.
Proof. by []. Qed.

Lemma binomial_mean_characterization (R : numDomainType) (m : nat) (p : R)
    (f : nat -> R) :
  binomial_mean m p f =
  \sum_(j < m.+1) (p ^+ j * (1 - p) ^+ (m - j) *+ 'C(m, j)) * f j.
Proof. by []. Qed.

Lemma linear_op_characterization (R : numDomainType) (X : Type)
    (A : (X -> R) -> X -> R) :
  linear_op A <->
  (forall (f g : X -> R) (x : X),
     A (fun y => f y + g y) x = A f x + A g x) /\
  (forall (a : R) (f : X -> R) (x : X), A (fun y => a * f y) x = a * A f x).
Proof. by []. Qed.

Lemma monotone_op_characterization (R : numDomainType) (X : Type)
    (A : (X -> R) -> X -> R) :
  monotone_op A <->
  forall f g : X -> R, (forall y, f y <= g y) -> forall x, A f x <= A g x.
Proof. by []. Qed.

Lemma meet_avg_characterization (R : realFieldType) (T C : finType)
    (E : C -> {set T}) (f : {set T} -> R) (S : {set T}) :
  meet_avg E f S = (#|C|%:R)^-1 * \sum_(c : C) f (S :&: E c).
Proof. by []. Qed.

Print Assumptions meet_avg_characterization.

(* Freeze 2, the definitions that T11 and packet P (batch 2) unfold to:
   - bdot, bchar, blk_deg, blk_dist, fcoef and low_blk_deg
     (fourier/boolean_fourier.v): the F_2 pairing, the character
     (-1)^(p . y), the number of nonzero rows, the number of differing rows,
     the Fourier coefficient normalized by the number of points, and the
     vanishing of the coefficients of block degree larger than D;
   - prob_vec, prod_avg, smoothing_hyps and weighted_gram
     (fourier/product_smoothing.v);
   - psd_factorization (matrix/psd_factorization.v), through psdmx.
   T10 and T11 also name psdmx, and T11 names frobenius;
   check/ApplicationsDefinitions.v protects both, and mxdot, which their
   definitions use. *)

From mathcomp Require Import zmodp matrix reals.
From GaussianAnalysis.fourier Require Import boolean_fourier product_smoothing.
From GaussianAnalysis.matrix Require Import psd_part psd_factorization.

Lemma bdot_characterization (t a : nat) (p y : 'M['F_2]_(t, a)) :
  bdot p y = \sum_(i < t) \sum_(j < a) p i j * y i j.
Proof. by []. Qed.

Lemma bchar_characterization (R : pzRingType) (t a : nat)
    (p y : 'M['F_2]_(t, a)) :
  bchar R p y = (-1) ^+ nat_of_ord (\sum_(i < t) \sum_(j < a) p i j * y i j).
Proof. by []. Qed.

Lemma blk_deg_characterization (t a : nat) (p : 'M['F_2]_(t, a)) :
  blk_deg p = #|[set i : 'I_t | row i p != 0]|.
Proof. by []. Qed.

Lemma blk_dist_characterization (t a : nat) (p q : 'M['F_2]_(t, a)) :
  blk_dist p q = #|[set i : 'I_t | row i p != row i q]|.
Proof. by []. Qed.

Lemma fcoef_characterization (R : numFieldType) (t a : nat) (V : lmodType R)
    (f : 'M['F_2]_(t, a) -> V) (p : 'M['F_2]_(t, a)) :
  fcoef f p = (#|{: 'M['F_2]_(t, a)}|%:R)^-1 *:
    \sum_(y : 'M['F_2]_(t, a))
      (-1) ^+ nat_of_ord (\sum_(i < t) \sum_(j < a) p i j * y i j) *: f y.
Proof. by []. Qed.

Lemma low_blk_deg_characterization (R : numFieldType) (t a : nat)
    (V : lmodType R) (D : nat) (f : 'M['F_2]_(t, a) -> V) :
  low_blk_deg D f <->
  forall p : 'M['F_2]_(t, a),
    (D < #|[set i : 'I_t | row i p != 0%R]|)%N ->
    (#|{: 'M['F_2]_(t, a)}|%:R)^-1 *:
      \sum_(y : 'M['F_2]_(t, a))
        (-1) ^+ nat_of_ord (\sum_(i < t) \sum_(j < a) p i j * y i j) *: f y
    = 0.
Proof. by []. Qed.

Lemma prob_vec_characterization (R : numDomainType) (T : finType)
    (w : T -> R) :
  prob_vec w <-> (forall x, 0 <= w x) /\ \sum_x w x = 1.
Proof. by []. Qed.

Lemma prod_avg_characterization (R : numDomainType) (X M : finType)
    (t a : nat) (V : lmodType R) (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R)
    (F : t.-tuple X -> V) (m : t.-tuple M) (y : 'M['F_2]_(t, a)) :
  prod_avg pi F m y =
  \sum_(x : t.-tuple X)
    (\prod_(i < t) pi i (tnth m i) (row i y) (tnth x i)) *: F x.
Proof. by []. Qed.

Lemma smoothing_hyps_characterization (R : numDomainType) (X M : finType)
    (t a : nat) (mu : 'I_t -> X -> R) (nu : 'I_t -> M -> R)
    (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R) (theta : R) :
  smoothing_hyps mu nu pi theta <->
  [/\ forall i, (forall x, 0 <= mu i x) /\ \sum_x mu i x = 1,
      forall i, (forall m, 0 <= nu i m) /\ \sum_m nu i m = 1,
      forall i m y, (forall x, 0 <= pi i m y x) /\ \sum_x pi i m y x = 1,
      forall i y x, \sum_m nu i m * pi i m y x = mu i x &
      forall i y (g : X -> R),
        \sum_m nu i m * (\sum_x pi i m y x * g x - \sum_x mu i x * g x) ^+ 2
          <= theta * \sum_x mu i x * g x ^+ 2].
Proof. by []. Qed.

Lemma weighted_gram_characterization (R : numFieldType) (t a r : nat)
    (lambda : R) (Rw : nat) (H : 'M['F_2]_(t, a) -> 'M[R]_(Rw, r))
    (q : 'M['F_2]_(t, a)) :
  weighted_gram lambda H q =
  \sum_(p : 'M['F_2]_(t, a))
    lambda ^+ #|[set i : 'I_t | row i q != row i p]| *:
      (((#|{: 'M['F_2]_(t, a)}|%:R)^-1 *: \sum_(y : 'M['F_2]_(t, a))
          (-1) ^+ nat_of_ord (\sum_(i < t) \sum_(j < a) p i j * y i j) *: H y)
       *m ((#|{: 'M['F_2]_(t, a)}|%:R)^-1 *: \sum_(y : 'M['F_2]_(t, a))
          (-1) ^+ nat_of_ord (\sum_(i < t) \sum_(j < a) p i j * y i j) *: H y)^T).
Proof. by []. Qed.

Lemma psd_factorization_characterization (R : realType) (I J : finType)
    (A : I -> J -> R) (r : nat) :
  psd_factorization A r <->
  exists (F : I -> 'M[R]_r) (G : J -> 'M[R]_r),
    [/\ forall i, psdmx (F i), forall j, psdmx (G j) &
        forall i j, A i j = \tr (F i *m G j)].
Proof. by []. Qed.

Print Assumptions psd_factorization_characterization.
