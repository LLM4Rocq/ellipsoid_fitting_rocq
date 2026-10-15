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
