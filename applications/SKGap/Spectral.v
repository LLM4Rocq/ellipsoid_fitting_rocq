From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals.
From mathcomp Require Import ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_gap.
From GaussianApplications Require Import SKGapDefinitions.
From GaussianApplications.SKGap Require Import Ising.

(**md**************************************************************************)
(* # The spectral gap of the heat-bath dynamics from a bound on its square    *)
(*                                                                            *)
(* Part of target T4 of phase 12 (AGENTS.md, section Phase 12), the spectral  *)
(* gap of the heat-bath dynamics of the Sherrington-Kirkpatrick model for     *)
(* beta < 1/2: the spectral step of item T4a. A Rocq formalization of the     *)
(* credited argument of the end of the proof of the proposition 'Gap and      *)
(* covariance under scaled interactions and fields' (rcut:prop:uniform-gap)   *)
(* of 'Cutoff throughout the high-temperature Sherrington-Kirkpatrick phase'  *)
(* (family 227 of the OpenAI math collection, revision 1581d4cbd, file        *)
(* appendices/entropy.tex). It follows the TeX, not a Lean module of the      *)
(* collection.                                                                *)
(*                                                                            *)
(* Take any matrix A and field theta, the Ising law nu of SKGapDefinitions.v, *)
(* the projections D_i = I - E_i of SKGap/Ising.v and L = ising_gen A theta = *)
(* sum_i D_i, the heat-bath generator with rate one at every site, up to      *)
(* sign. In L^2(nu), L is linear (ising_gen_lin) and self-adjoint             *)
(* (ising_gen_sym, from ising_dproj_adj), <f, L f>_nu is the Dirichlet form   *)
(* (ising_gen_form), hence nonnegative, and the kernel of L is the constants  *)
(* (ising_gen_ker, from ising_dirichlet_eq0). So wpoincare_from_square of     *)
(* probability/finite_gap.v applies: if k E(g) <= nu[(L g)^2] for every g,    *)
(* then k Var_nu(f) <= E(f) for every f (ising_gap_from_square). The          *)
(* manuscript applies the bound to a nonconstant eigenfunction of L; the      *)
(* library uses the spectral theorem for the matrix of L.                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section ising_gap.
Variables (R : realType) (n : nat) (A : 'M[R]_n) (theta : 'cV[R]_n).
Local Notation cube := {ffun 'I_n -> bool}.
Local Notation nu := (ising_mass A theta).
Local Notation E := (ising_mean A theta).
Local Notation D := (ising_dproj A theta).
Local Notation L := (ising_gen A theta).
Implicit Types (f g : cube -> R).

(* The inner product of L^2(nu). *)
Lemma wdot_ising f g : wdot nu f g = E (fun x => f x * g x).
Proof.
by apply: eq_bigr => x _; rewrite mulrA.
Qed.

(* The generator is linear and self-adjoint, its form is the Dirichlet form
   and its kernel is the constants. *)
Lemma ising_gen_lin (a : R) f g x :
  L (fun y => a * f y + g y) x = a * L f x + L g x.
Proof.
rewrite /ising_gen mulr_sumr -big_split; apply: eq_bigr => i _ /=.
rewrite /ising_dproj /ising_cexp.
have d := lt0r_neq0 (ising_pair_den A theta i x).
by field.
Qed.

Lemma ising_gen_dot f g :
  wdot nu f (L g) = \sum_i E (fun x => D i f x * D i g x).
Proof.
rewrite wdot_ising.
transitivity (E (fun x => \sum_i f x * D i g x)).
  by apply: ising_mean_ext => x; rewrite /ising_gen mulr_sumr.
rewrite ising_mean_sum; apply: eq_bigr => i _.
exact: ising_dproj_adj.
Qed.

Lemma ising_gen_form f : wdot nu f (L f) = ising_dirichlet A theta f.
Proof.
rewrite ising_gen_dot ising_dirichletE; apply: eq_bigr => i _.
by apply: ising_mean_ext => x; rewrite expr2.
Qed.

Lemma ising_gen_sym f g : wdot nu f (L g) = wdot nu (L f) g.
Proof.
rewrite [RHS]wdotC !ising_gen_dot; apply: eq_bigr => i _.
by apply: ising_mean_ext => x; rewrite mulrC.
Qed.

Lemma ising_gen_ge0 f : 0 <= wdot nu f (L f).
Proof. by rewrite ising_gen_form; exact: ising_dirichlet_ge0. Qed.

Lemma ising_gen_ker g : (forall x, L g x = 0) <-> (forall x y, g x = g y).
Proof.
split => hg.
  apply: (@ising_dirichlet_eq0 _ _ A theta); rewrite -ising_gen_form.
  by rewrite /wdot big1 // => x _; rewrite hg mulr0.
move=> x; rewrite /ising_gen big1 // => i _.
rewrite /ising_dproj /ising_cexp (hg (spin_set x i true) x).
rewrite (hg (spin_set x i false) x).
have d := lt0r_neq0 (ising_pair_den A theta i x).
by field.
Qed.

(* The interface of the assembly of T4: a bound of the Dirichlet form by
   the squared norm of the generator gives the spectral gap. *)
Theorem ising_gap_from_square (k : R) :
  (forall g, k * ising_dirichlet A theta g <=
     E (fun x => ising_gen A theta g x ^+ 2)) ->
  forall f, k * ising_var A theta f <= ising_dirichlet A theta f.
Proof.
move=> hsq f.
have hsq' g : k * wdot nu g (L g) <= wdot nu (L g) (L g).
  rewrite ising_gen_form wdot_ising.
  have -> : E (fun x => L g x * L g x) = E (fun x => L g x ^+ 2).
    by apply: ising_mean_ext => x; rewrite expr2.
  exact: hsq.
have := wpoincare_from_square (ising_mass_gt0 A theta) ising_gen_lin
  ising_gen_sym (fun f => ising_gen_ge0 f) (ising_mass_sum A theta)
  ising_gen_ker hsq' f.
by rewrite ising_gen_form.
Qed.

End ising_gap.
