From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.

(**md**************************************************************************)
(* # The largest eigenvalue of a real square matrix                           *)
(*                                                                            *)
(* lambda_max A is the supremum of the quadratic form mxdot x (A *m x) over   *)
(* the unit vectors x of 'cV[R]_n, in the conventions of opnorm (opnorm.v)    *)
(* and rayleigh_max (real_spectral.v): column vectors, the Frobenius inner    *)
(* product mxdot. For a symmetric matrix it is the largest eigenvalue. For n  *)
(* = 0 there is no unit vector and lambda_max A = 0, the supremum of the      *)
(* empty set (lambda_max_dim0).                                               *)
(*                                                                            *)
(* The definition is alone in the section lambda_max, which is frozen with    *)
(* the statement of target T3 of phase 12 (AGENTS.md, section Phase 12; the   *)
(* sharp upper edge of the GOE, from 'Cutoff throughout the high-temperature  *)
(* Sherrington-Kirkpatrick phase', family 227 of the OpenAI math collection,  *)
(* revision 1581d4cbd): the source checker of scripts/ compares its code and  *)
(* the Require commands of this file with the acceptance commit fc76edf. The  *)
(* lemmas below it may grow.                                                  *)
(*                                                                            *)
(* Proved:                                                                    *)
(*                                                                            *)
(* - lambda_max_ub, lambda_max_form: x^T A x <= lambda_max A for every unit   *)
(*   x, and x^T A x <= lambda_max A x^T x for every x.                        *)
(* - lambda_max_le: for n > 0, lambda_max A <= b as soon as x^T A x <= b for  *)
(*   every unit x; lambda_max_attained: for n > 0, the supremum is attained   *)
(*   at a unit vector (rayleigh_max).                                         *)
(* - lambda_max_eigenvector, eigenvalue_le_lambda_max: for n > 0 and A        *)
(*   symmetric, lambda_max A is an eigenvalue of A, and it bounds every       *)
(*   eigenvalue of A.                                                         *)
(* - lambda_max_opnorm, lambda_maxD: lambda_max A <= opnorm A, and lambda_max *)
(*   (A + B) <= lambda_max A + lambda_max B.                                  *)
(* - lambda_max_lipschitz, lambda_max_lipschitz_frobenius: `|lambda_max A -   *)
(*   lambda_max B| <= opnorm (A - B) <= frobenius (A - B).                    *)
(* - opnorm_lambda_max: for a symmetric A, opnorm A = Num.max (lambda_max A)  *)
(*   (lambda_max (- A)).                                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*   lambda_max A == the supremum of mxdot x (A *m x) over the columns x      *)
(*                   with mxdot x x = 1; the largest eigenvalue of a          *)
(*                   symmetric A                                              *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section lambda_max.
Variable R : realType.

Definition lambda_max n (A : 'M[R]_n) : R :=
  sup [set mxdot x (A *m x) | x in [set x : 'cV[R]_n | mxdot x x = 1]].

End lambda_max.

Section lambda_max_lemmas.
Variable R : realType.
Implicit Types n : nat.

Lemma mxdot_unit_dim n (x : 'cV[R]_n) : mxdot x x = 1 -> (0 < n)%N.
Proof.
by case: n x => // x; rewrite /mxdot big_ord0 => /esym/eqP; rewrite oner_eq0.
Qed.

Lemma lambda_max_dim0 (A : 'M[R]_0) : lambda_max A = 0.
Proof.
rewrite /lambda_max (_ : [set _ | _ in _] = set0) ?sup0 //.
apply/seteqP; split => y // [x x1 _].
by have := mxdot_unit_dim x1; rewrite ltnn.
Qed.

Lemma lambda_max_set_neq0 n (A : 'M[R]_n) : (0 < n)%N ->
  [set mxdot x (A *m x) | x in [set x : 'cV[R]_n | mxdot x x = 1]] !=set0.
Proof.
case: n A => // n A _; pose e : 'cV[R]_n.+1 := delta_mx 0 0.
exists (mxdot e (A *m e)); exists e => //=.
by rewrite /e mxdot_delta mxE !eqxx.
Qed.

Lemma lambda_max_ubound n (A : 'M[R]_n) :
  ubound [set mxdot x (A *m x) | x in [set x : 'cV[R]_n | mxdot x x = 1]]
    (opnorm A).
Proof.
move=> _ [x /= x1 <-]; have f1 : frobenius x = 1 by rewrite /frobenius x1 sqrtr1.
apply: le_trans (real_ler_norm (num_real _)) _.
by apply: le_trans (mxdot_opnorm _ _ _) _; rewrite f1 !mulr1.
Qed.

Lemma lambda_max_has_sup n (A : 'M[R]_n) : (0 < n)%N ->
  has_sup [set mxdot x (A *m x) | x in [set x : 'cV[R]_n | mxdot x x = 1]].
Proof.
move=> n0; split; first exact: lambda_max_set_neq0.
by exists (opnorm A); exact: lambda_max_ubound.
Qed.

Lemma lambda_max_ub n (A : 'M[R]_n) (x : 'cV[R]_n) :
  mxdot x x = 1 -> mxdot x (A *m x) <= lambda_max A.
Proof.
move=> x1; have n0 := mxdot_unit_dim x1.
by apply: (ub_le_sup (proj2 (lambda_max_has_sup A n0))); exists x.
Qed.

Lemma lambda_max_le n (A : 'M[R]_n) (b : R) : (0 < n)%N ->
  (forall x : 'cV[R]_n, mxdot x x = 1 -> mxdot x (A *m x) <= b) ->
  lambda_max A <= b.
Proof.
move=> n0 Ab; apply: ge_sup; first exact: lambda_max_set_neq0.
by move=> _ [x /= x1 <-]; exact: Ab.
Qed.

Lemma lambda_max_form n (A : 'M[R]_n) (x : 'cV[R]_n) :
  mxdot x (A *m x) <= lambda_max A * mxdot x x.
Proof.
have [->|x0] := eqVneq x 0; first by rewrite mulmx0 mxdot0l mulr0.
have c0 : 0 < frobenius x by rewrite frobenius_gt0.
set c := frobenius x in c0 *; set y := c^-1 *: x.
have y1 : mxdot y y = 1.
  rewrite /y mxdotZl mxdotZr mulrA -expr2 -frobenius_sqr -exprMn.
  by rewrite mulVf ?gt_eqF // expr1n.
have := lambda_max_ub A y1; rewrite /y -scalemxAr mxdotZl mxdotZr mulrA.
by rewrite -expr2 exprVn mulrC ler_pdivrMr ?exprn_gt0 // frobenius_sqr.
Qed.

Lemma lambda_max_attained n (A : 'M[R]_n) : (0 < n)%N ->
  exists2 v : 'cV[R]_n, mxdot v v = 1 & mxdot v (A *m v) = lambda_max A.
Proof.
case: n A => // n A _; have [v v1 vmax] := rayleigh_max A.
exists v => //; apply/eqP; rewrite eq_le lambda_max_ub //=.
by apply: lambda_max_le => // x x1; have := vmax x; rewrite x1 mulr1.
Qed.

Lemma lambda_max_eigenvector n (A : 'M[R]_n) : (0 < n)%N ->
  A \is symmetricmx ->
  exists2 v : 'cV[R]_n, mxdot v v = 1 & A *m v = lambda_max A *: v.
Proof.
move=> n0 Asym; have [v v1 vE] := lambda_max_attained A n0.
exists v => //; set l := lambda_max A.
have Msym : l%:M - A \is symmetricmx.
  by apply/symmetricmxP; rewrite linearB /= tr_scalar_mx (symmetricmxP _ Asym).
have Mform (x : 'cV[R]_n) :
    mxdot x ((l%:M - A) *m x) = l * mxdot x x - mxdot x (A *m x).
  by rewrite mulmxBl mul_scalar_mx mxdotBr mxdotZr.
have Mpsd (x : 'cV[R]_n) : 0 <= mxdot x ((l%:M - A) *m x).
  by rewrite Mform subr_ge0 lambda_max_form.
have v0 : mxdot v ((l%:M - A) *m v) = 0 by rewrite Mform v1 mulr1 vE subrr.
have := psd_form_eq0 Msym Mpsd v0.
by rewrite mulmxBl mul_scalar_mx => /eqP; rewrite subr_eq0 => /eqP <-.
Qed.

Lemma eigenvalue_le_lambda_max n (A : 'M[R]_n) (v : 'cV[R]_n) (mu : R) :
  mxdot v v = 1 -> A *m v = mu *: v -> mu <= lambda_max A.
Proof.
by move=> v1 Av; have := lambda_max_ub A v1; rewrite Av mxdotZr v1 mulr1.
Qed.

Lemma lambda_max_opnorm n (A : 'M[R]_n) : lambda_max A <= opnorm A.
Proof.
case: n A => [|n] A; first by rewrite lambda_max_dim0 opnorm_ge0.
by apply: lambda_max_le => // x x1; apply: lambda_max_ubound; exists x.
Qed.

Lemma lambda_maxD n (A B : 'M[R]_n) :
  lambda_max (A + B) <= lambda_max A + lambda_max B.
Proof.
case: n A B => [|n] A B; first by rewrite !lambda_max_dim0 addr0.
apply: lambda_max_le => // x x1.
by rewrite mulmxDl mxdotDr lerD // lambda_max_ub.
Qed.

Lemma lambda_max_lipschitz n (A B : 'M[R]_n) :
  `|lambda_max A - lambda_max B| <= opnorm (A - B).
Proof.
have le (C D : 'M[R]_n) : lambda_max C - lambda_max D <= opnorm (C - D).
  rewrite lerBlDl; have -> : C = D + (C - D) by rewrite addrC subrK.
  rewrite [X in opnorm X]addrC addKr.
  by apply: le_trans (lambda_maxD _ _) _; rewrite lerD2l lambda_max_opnorm.
rewrite ler_norml (le A B) andbT lerNl opprB.
by rewrite -opnormN opprB le.
Qed.

Lemma lambda_max_lipschitz_frobenius n (A B : 'M[R]_n) :
  `|lambda_max A - lambda_max B| <= frobenius (A - B).
Proof. exact: le_trans (lambda_max_lipschitz A B) (opnorm_le_frobenius _). Qed.

Lemma opnorm_lambda_max n (A : 'M[R]_n) : A \is symmetricmx ->
  opnorm A = Num.max (lambda_max A) (lambda_max (- A)).
Proof.
case: n A => [|n] A Asym.
  rewrite !lambda_max_dim0 maxxx; apply/eqP; rewrite eq_le opnorm_ge0 andbT.
  by apply: opnorm_le => x _; rewrite /frobenius /mxdot big_ord0 sqrtr0.
have m0 : 0 <= Num.max (lambda_max A) (lambda_max (- A)).
  pose e : 'cV[R]_n.+1 := delta_mx 0 0.
  have e1 : mxdot e e = 1 by rewrite mxdot_delta mxE !eqxx.
  have h1 := lambda_max_ub A e1; have h2 := lambda_max_ub (- A) e1.
  rewrite mulNmx mxdotNr in h2; rewrite le_max.
  case: (lerP 0 (mxdot e (A *m e))) => h; first by rewrite (le_trans h h1).
  by rewrite (le_trans _ h2) ?orbT // oppr_ge0 ltW.
apply/eqP; rewrite eq_le ge_max lambda_max_opnorm /=.
rewrite -[X in lambda_max (- A) <= X]opnormN lambda_max_opnorm andbT.
apply/(opnorm_symP Asym m0) => x; rewrite ler_norml; apply/andP; split.
  rewrite lerNl -mxdotNr -mulNmx; apply: le_trans (lambda_max_form _ _) _.
  by rewrite ler_wpM2r ?mxdot_ge0 // le_max lexx orbT.
apply: le_trans (lambda_max_form _ _) _.
by rewrite ler_wpM2r ?mxdot_ge0 // le_max lexx.
Qed.

End lambda_max_lemmas.
