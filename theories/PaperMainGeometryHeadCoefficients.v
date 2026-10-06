(* Coefficient and Frobenius bounds of the exact head correction, the
   deterministic core of eq:aJ-l2 and eq:EJ-frob in the proof of
   lem:head-correction-bounds (manuscript lines 1001-1023).

   Notation of PaperMainGeometryHeadCorrection: Q is the Gram matrix of the
   head W, r the residuals of P, a coefficients with Q a = r and
   E = - sum_j a_j W_j. Assume the lower Gram edge in the explicit form
   u^T Q u >= mu |u|^2 for every u, with mu > 0 (paper: Q_J >= c d I from
   the feature edge). Then Q is invertible, mu^2 |a|^2 <= |r|^2 (eq:aJ-l2
   with mu = c d), and |E|_F^2 = a^T r <= |r|^2 / mu. The last bound
   replaces the paper's |E|_F^2 = a^T Q a <= C d |a|^2 and needs no upper
   Gram bound. With |r|^2 <= mu eta^2 and 0 <= eta < 1, the normalization
   and support transfer of PaperMainGeometryHeadCorrection apply to
   a = Q^-1 r. The lower Gram edge and the residual bound are hypotheses
   here. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* The lower edge u^T Q u >= mu |u|^2 of a square matrix. *)
Definition paper_main_head_coercive {m : nat} (Q : 'M[R]_m) (mu : R) : Prop :=
  forall u : 'cV[R]_m, mu * (u^T *m u) 0 0 <= (u^T *m Q *m u) 0 0.

Section HeadCoefficients.
Variables (d m : nat).
Implicit Types (P Z : 'M[R]_d) (W : 'I_m -> 'M[R]_d) (a r u v : 'cV[R]_m).

Lemma pmh_vec_dot u v : (u^T *m v) 0 0 = \sum_(i < m) u i 0 * v i 0.
Proof. by rewrite mxE; apply: eq_bigr => i _; rewrite mxE. Qed.

Lemma pmh_vec_sqr_ge0 u : 0 <= (u^T *m u) 0 0.
Proof.
by rewrite pmh_vec_dot; apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
Qed.

Lemma paper_main_head_quadratic_solve W P a :
  paper_main_head_gram W *m a = paper_main_head_residual W P ->
  (a^T *m paper_main_head_gram W *m a) 0 0 =
  (a^T *m paper_main_head_residual W P) 0 0.
Proof. by move=> Ha; rewrite -mulmxA Ha. Qed.

(* The scalar core: mu s <= c and 0 <= mu^2 s - 2 mu c + t give
   mu^2 s <= t and mu c <= t, for s = |a|^2, c = a^T r, t = |r|^2. *)
Lemma pmh_coercive_core a r (mu : R) :
  0 < mu -> mu * (a^T *m a) 0 0 <= (a^T *m r) 0 0 ->
  mu ^+ 2 * (a^T *m a) 0 0 <= (r^T *m r) 0 0 /\
  mu * (a^T *m r) 0 0 <= (r^T *m r) 0 0.
Proof.
move=> Hmu Hc.
have Hexp : 0 <= mu ^+ 2 * (a^T *m a) 0 0 - 2 * mu * (a^T *m r) 0 0 +
    (r^T *m r) 0 0.
  have -> : mu ^+ 2 * (a^T *m a) 0 0 - 2 * mu * (a^T *m r) 0 0 + (r^T *m r) 0 0 =
      \sum_(i < m) (mu * a i 0 - r i 0) ^+ 2.
    rewrite !pmh_vec_dot !mulr_sumr -sumrB -big_split /=.
    by apply: eq_bigr => i _; ring.
  by apply: sumr_ge0 => i _; rewrite sqr_ge0.
split; nra.
Qed.

Theorem paper_main_head_coefficients_bound W P a (mu : R) :
  0 < mu -> paper_main_head_coercive (paper_main_head_gram W) mu ->
  paper_main_head_gram W *m a = paper_main_head_residual W P ->
  mu ^+ 2 * (a^T *m a) 0 0 <=
  ((paper_main_head_residual W P)^T *m paper_main_head_residual W P) 0 0.
Proof.
move=> Hmu HQ Ha.
have Hc := HQ a; rewrite (paper_main_head_quadratic_solve _ _ _ Ha) in Hc.
by case: (pmh_coercive_core _ _ _ Hmu Hc).
Qed.

Theorem paper_main_head_correction_energy W P a (mu : R) :
  0 < mu -> paper_main_head_coercive (paper_main_head_gram W) mu ->
  paper_main_head_gram W *m a = paper_main_head_residual W P ->
  mu * paper_main_frobenius (paper_main_head_correction W a) ^+ 2 <=
  ((paper_main_head_residual W P)^T *m paper_main_head_residual W P) 0 0.
Proof.
move=> Hmu HQ Ha.
have Hc := HQ a; rewrite (paper_main_head_quadratic_solve _ _ _ Ha) in Hc.
rewrite paper_main_head_correction_frobenius (paper_main_head_quadratic_solve _ _ _ Ha).
by case: (pmh_coercive_core _ _ _ Hmu Hc).
Qed.

Theorem paper_main_head_gram_coercive_unit W (mu : R) :
  0 < mu -> paper_main_head_coercive (paper_main_head_gram W) mu ->
  paper_main_head_gram W \in unitmx.
Proof.
move=> Hmu HQ.
rewrite -row_free_unit -kermx_eq0; apply/eqP/row_matrixP => i.
rewrite row0.
set v := row i (kermx (paper_main_head_gram W)).
have Hv : v *m paper_main_head_gram W = 0 by rewrite /v -row_mul mulmx_ker row0.
apply/eqP; apply: contraT => Hv0.
have Hu0 : v^T != 0 by apply: contra Hv0 => /eqP H; rewrite -[v]trmxK H trmx0.
have Hpos := pms_sqnorm_gt0 _ _ Hu0.
have Hq := HQ v^T.
rewrite trmxK Hv mul0mx [X in _ <= X]mxE in Hq.
rewrite trmxK in Hpos.
have Hp := mulr_gt0 Hmu Hpos.
lra.
Qed.

End HeadCoefficients.
