From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum boolp.
From GaussianAnalysis.probability Require Import finite_mean binomial_mean.

(**md**************************************************************************)
(* # Commuting operators and averages over random intersections               *)
(*                                                                            *)
(* - Iterates of monotone maps of a preorder T (a preorderType). The iterates *)
(*   of a monotone map are monotone (homo_iter). If A and B are monotone, B   *)
(*   sub-commutes with A (B (A y) <= A (B y) for every y), and at one point   *)
(*   x, B x <= A x, then iter m B x <= iter m A x for every m                 *)
(*   (iter_le_subcomm). The comparison at a single point is what the          *)
(*   applications have: there, the one-step comparison holds at one function  *)
(*   only.                                                                    *)
(* - Operators on the functions X -> R, for a type X and a numDomainType R:   *)
(*   linear_op A says that A is additive and homogeneous, and monotone_op A   *)
(*   that f <= g pointwise implies A f <= A g pointwise (for a linear         *)
(*   operator, positivity). linear_op is the pointwise form of MathComp's     *)
(*   linearity (linear) for the module of functions X -> R of                 *)
(*   classical/functions.v; it lets the hypotheses be stated on plain         *)
(*   functions. A linear operator commutes with finite sums and binomial      *)
(*   means (linear_op_sum, linear_op_binomial_mean). The pointwise comparison *)
(*   of the iterates of two monotone operators (monotone_iter_le); the        *)
(*   iterate of a multiple of a linear operator (iter_scale); the binomial    *)
(*   expansion of the iterate of the p-mixture of two commuting linear        *)
(*   operators (iter_mix_binomial): in the language of Markov operators, m    *)
(*   steps that each move by A with probability p and by B otherwise make a   *)
(*   binomial number of A-steps (the example lazy_walk_binomial: m steps of   *)
(*   the lazy walk on nat that moves to the right with probability p give the *)
(*   binomial law); and the fixed-count interpolation (binomial_mix_le_iter): *)
(*   if A, B and C are monotone linear operators, A and B commute, A and B    *)
(*   sub-commute with C (A (C g) <= C (A g) and B (C g) <= C (B g) pointwise, *)
(*   for every g), and the p-mixture of A and B is below C at f, then for 0   *)
(*   <= p <= 1 the binomial mixture of the iterates of A and B at f is below  *)
(*   the iterate of C at f.                                                   *)
(* - Averages over random intersections, for a finite family E : C -> {set T} *)
(*   of subsets of a finite type T and f : {set T} -> R, over a realFieldType *)
(*   R: meet_avg E f S is the mean of f (S :&: E c) for c uniform on C. It is *)
(*   a monotone linear operator (meet_avg_linear, meet_avg_monotone) that     *)
(*   fixes the constants when C is nonempty (meet_avg_cst); any two such      *)
(*   averages commute (meet_avgC); and its m-th iterate intersects S with m   *)
(*   independent uniform members of the family (iter_meet_avg).               *)
(*                                                                            *)
(* This file is part of target T9 of phase 13: a Rocq formalization, in       *)
(* general form, of the operator comparisons of the credited argument of 'A   *)
(* limiting satisfiability threshold for every fixed clause size' (family 235 *)
(* of the OpenAI math collection, revision 1581d4cbd). The manuscript proves  *)
(* its interpolation and transfer lemmas (source/sections/convergence.tex,    *)
(* the lemmas 'Auxiliary product inequality' and 'Proper-clause transfer')    *)
(* with marked Poisson families, a derivative in time and Poisson thinning.   *)
(* The Lean development of the collection (lean/OAI/Probability/RandomSAT)    *)
(* fixes the number of random constraints and compares the iterates of        *)
(* commuting averaging operators instead; this file follows it. The Lean      *)
(* development compares the iterates for exactly commuting monotone operators *)
(* on real functions; here the comparison is stated for sub-commuting         *)
(* monotone maps of a preorder, at one point, and its operator forms are      *)
(* corollaries; the fixed-count interpolation asks only that A and B          *)
(* sub-commute with C. In the manuscript the averages are over one uniform    *)
(* random constraint, which keeps the solutions that satisfy it: an average   *)
(* over random intersections.                                                 *)
(* Lean: finiteClauseAverage (Interpolation.lean, line 24)                    *)
(* Lean: finiteClauseAverage_commute (Interpolation.lean, line 53)            *)
(* Lean: iterate_compare_of_commute (Interpolation.lean, line 77)             *)
(* Lean: mixedAverage (Interpolation.lean, line 92)                           *)
(* Lean: mixed_finiteAverage_iterate (Interpolation.lean, line 278)           *)
(* Lean: auxiliary_interpolation (Interpolation.lean, line 397)               *)
(* Lean: proper_scaled_le_auxiliaryProbability (Transfer.lean, line 150)      *)
(*                                                                            *)
(* ```                                                                        *)
(*        linear_op A == the operator A : (X -> R) -> X -> R is additive and  *)
(*                       homogeneous, at every point of X                     *)
(*      monotone_op A == f <= g pointwise implies A f <= A g pointwise        *)
(*     meet_avg E f S == unif_mean (fun c => f (S :&: E c)), the mean of f at *)
(*                       the intersection of S with a uniform member of E     *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section operators.
Context {R : numDomainType} {X : Type}.

(* Linearity and monotonicity of an operator on the functions X -> R. *)
Definition linear_op (A : (X -> R) -> X -> R) : Prop :=
  (forall (f g : X -> R) (x : X),
     A (fun y => f y + g y) x = A f x + A g x) /\
  (forall (a : R) (f : X -> R) (x : X), A (fun y => a * f y) x = a * A f x).

Definition monotone_op (A : (X -> R) -> X -> R) : Prop :=
  forall f g : X -> R, (forall y, f y <= g y) -> forall x, A f x <= A g x.

End operators.

Section meet_avg.
Context {R : realFieldType} {T C : finType}.

(* The mean of f at the intersection of S with a uniform member of the
   family E. *)
Definition meet_avg (E : C -> {set T}) (f : {set T} -> R) (S : {set T}) : R :=
  unif_mean (fun c => f (S :&: E c)).

End meet_avg.

Section iter_order.
Context {disp : Order.disp_t} {T : preorderType disp}.

(* The iterates of a monotone map of a preorder are monotone. *)
Lemma homo_iter (A : T -> T) (m : nat) :
  {homo A : x y / (x <= y)%O} -> {homo iter m A : x y / (x <= y)%O}.
Proof. by move=> hA; elim: m => // m IH x y xy /=; apply: hA; exact: IH. Qed.

(* The comparison of the iterates of two monotone maps at one point x: if B
   sub-commutes with A and B x <= A x, then iter m B x <= iter m A x. *)
Lemma iter_le_subcomm (A B : T -> T) (x : T) :
  {homo A : y z / (y <= z)%O} -> {homo B : y z / (y <= z)%O} ->
  (forall y, (B (A y) <= A (B y))%O) -> (B x <= A x)%O ->
  forall m, (iter m B x <= iter m A x)%O.
Proof.
move=> hA hB BA Bx.
have BAm j y : (B (iter j A y) <= iter j A (B y))%O.
  by elim: j y => // j IH y /=; exact: le_trans (BA _) (hA _ _ (IH y)).
elim=> // m IH /=.
apply: le_trans (hB _ _ IH) _; apply: le_trans (BAm m x) _.
by rewrite -iterS iterSr; exact: homo_iter.
Qed.

End iter_order.

Section operators.
Context {R : numDomainType} {X : Type}.
Implicit Types (A B C : (X -> R) -> X -> R) (f g : X -> R).

(* The same comparison for monotone operators on functions, at one
   function f, pointwise. *)
Lemma monotone_iter_le A B f :
  monotone_op A -> monotone_op B ->
  (forall g x, B (A g) x <= A (B g) x) -> (forall x, B f x <= A f x) ->
  forall (m : nat) (x : X), iter m B f x <= iter m A f x.
Proof.
move=> hA hB BA Bf m x.
have hA' : {homo A : g h / (g <= h)%O}.
  by move=> g h /lefP gh; apply/lefP; exact: hA.
have hB' : {homo B : g h / (g <= h)%O}.
  by move=> g h /lefP gh; apply/lefP; exact: hB.
have BA' g : (B (A g) <= A (B g))%O by apply/lefP; exact: BA.
have Bf' : (B f <= A f)%O by apply/lefP.
by move/lefP: (iter_le_subcomm hA' hB' BA' Bf' m); apply.
Qed.

(* A linear operator commutes with finite sums, and with binomial means. *)
Lemma linear_op0 A : linear_op A -> forall x, A (fun=> 0) x = 0.
Proof.
case=> _ hZ x; have h := hZ 0 (fun=> (0 : R)) x.
transitivity (A (fun y : X => 0 * (fun=> (0 : R)) y) x).
  by congr A; apply: funext => y; rewrite mul0r.
by rewrite h mul0r.
Qed.

Lemma linear_op_sum A (I : Type) (r : seq I) (P : pred I) (c : I -> R)
    (F : I -> X -> R) :
  linear_op A -> forall x,
  A (fun y => \sum_(i <- r | P i) c i * F i y) x =
  \sum_(i <- r | P i) c i * A (F i) x.
Proof.
move=> hA x; have [hD hZ] := hA.
elim: r => [|i r IH].
  rewrite big_nil; transitivity (A (fun=> 0) x); last exact: linear_op0.
  by congr A; apply: funext => y; rewrite big_nil.
have -> : (fun y => \sum_(j <- i :: r | P j) c j * F j y) =
    (fun y => (if P i then c i * F i y else 0) +
              \sum_(j <- r | P j) c j * F j y).
  by apply: funext => y; rewrite big_cons; case: (P i); rewrite ?add0r.
rewrite hD IH big_cons; case: (P i) => /=; last by rewrite linear_op0 // add0r.
by rewrite hZ.
Qed.

Lemma linear_op_binomial_mean A m p (F : nat -> X -> R) :
  linear_op A -> forall x,
  A (fun y => binomial_mean m p (fun j => F j y)) x =
  binomial_mean m p (fun j => A (F j) x).
Proof. by move=> hA x; rewrite /binomial_mean linear_op_sum. Qed.

(* The iterate of c A is c ^+ m times the iterate of A. *)
Lemma iter_scale A (c : R) :
  linear_op A ->
  forall (m : nat) (f : X -> R) (x : X),
  iter m (fun g y => c * A g y) f x = c ^+ m * iter m A f x.
Proof.
case=> _ hZ; elim=> [|m IH] f x /=; first by rewrite expr0 mul1r.
have -> : iter m (fun g y => c * A g y) f = (fun y => c ^+ m * iter m A f y).
  by apply: funext => y; exact: IH.
by rewrite hZ exprS mulrA.
Qed.

(* The binomial expansion of the iterate of the p-mixture of two commuting
   linear operators. *)
Lemma iter_mix_binomial A B (p : R) :
  linear_op A -> linear_op B -> (forall f, A (B f) = B (A f)) ->
  forall (m : nat) (f : X -> R) (x : X),
  iter m (fun g y => p * A g y + (1 - p) * B g y) f x =
  binomial_mean m p (fun j => iter j A (iter (m - j) B f) x).
Proof.
move=> hA hB AB.
have BA j g : B (iter j A g) = iter j A (B g).
  by elim: j g => // j IH g /=; rewrite -AB IH.
elim=> [|m IH] f x; first by rewrite binomial_mean0.
have -> : iter m.+1 (fun g y => p * A g y + (1 - p) * B g y) f x =
    p * A (iter m (fun g y => p * A g y + (1 - p) * B g y) f) x +
    (1 - p) * B (iter m (fun g y => p * A g y + (1 - p) * B g y) f) x by [].
have -> : iter m (fun g y => p * A g y + (1 - p) * B g y) f =
    (fun y => binomial_mean m p (fun j => iter j A (iter (m - j) B f) y)).
  by apply: funext => y; exact: IH.
rewrite (linear_op_binomial_mean _ _ _ hA) (linear_op_binomial_mean _ _ _ hB).
rewrite binomial_meanS addrC; congr (_ + _).
by congr (_ * _); apply: eq_binomial_mean => j jm; rewrite BA subSn.
Qed.

(* The fixed-count interpolation: if the p-mixture of A and B is below C at
   f, so is the binomial mixture of their iterates below the iterate of C,
   for monotone linear operators A, B and C such that A and B commute and
   sub-commute with C. *)
Lemma binomial_mix_le_iter A B C (p : R) (f : X -> R) :
  0 <= p <= 1 ->
  linear_op A -> linear_op B -> linear_op C ->
  monotone_op A -> monotone_op B -> monotone_op C ->
  (forall g, A (B g) = B (A g)) -> (forall g x, A (C g) x <= C (A g) x) ->
  (forall g x, B (C g) x <= C (B g) x) ->
  (forall x, p * A f x + (1 - p) * B f x <= C f x) ->
  forall (m : nat) (x : X),
  binomial_mean m p (fun j => iter j A (iter (m - j) B f) x) <=
  iter m C f x.
Proof.
move=> /andP[p0 p1] hA hB hC mA mB mC AB AC BC Mf m x.
rewrite -(iter_mix_binomial p hA hB AB).
apply: (monotone_iter_le mC) => //.
  move=> g h gh y; apply: lerD; apply: ler_wpM2l; rewrite ?subr_ge0 //.
    exact: mA.
  exact: mB.
move=> g y; have [hCD hCZ] := hC.
rewrite (hCD (fun z => p * A g z) (fun z => (1 - p) * B g z)).
rewrite (hCZ p (A g)) (hCZ (1 - p) (B g)).
by apply: lerD; apply: ler_wpM2l; rewrite ?subr_ge0.
Qed.

End operators.

Section meet_avg_theory.
Context {R : realFieldType} {T C : finType}.
Implicit Types (E : C -> {set T}) (f g : {set T} -> R) (S : {set T}).

(* Averages over random intersections are monotone linear operators, they
   fix the constants, and any two of them commute. *)
Lemma meet_avg_linear E : linear_op (@meet_avg R T C E).
Proof.
split=> [f g S|a f S]; rewrite /meet_avg; [exact: unif_meanD|exact: unif_meanZ].
Qed.

Lemma meet_avg_monotone E : monotone_op (@meet_avg R T C E).
Proof. by move=> f g fg S; apply: ler_unif_mean => c; exact: fg. Qed.

Lemma meet_avg_cst E (a : R) S :
  (0 < #|C|)%N -> meet_avg E (fun=> a) S = a.
Proof. by move=> C0; exact: unif_mean_cst. Qed.

Lemma meet_avgC (D : finType) E (F : D -> {set T}) f :
  meet_avg E (meet_avg F f) = meet_avg F (meet_avg E f).
Proof.
apply: funext => S; rewrite /meet_avg unif_mean_comm.
by apply: eq_unif_mean => d; apply: eq_unif_mean => c; rewrite setIAC.
Qed.

(* The m-th iterate intersects S with m independent uniform members. *)
Lemma iter_meet_avg E (m : nat) f S :
  iter m (meet_avg E) f S =
  unif_mean (fun t : m.-tuple C => f (S :&: \bigcap_(c <- t) E c)).
Proof.
elim: m S => [|m IH] S; first by rewrite unif_mean_tuple0 /= big_nil setIT.
transitivity (unif_mean (fun c => iter m (meet_avg E) f (S :&: E c))) => //.
rewrite unif_mean_tuple_cons; apply: eq_unif_mean => c; rewrite IH.
by apply: eq_unif_mean => t; rewrite big_cons setIA.
Qed.

End meet_avg_theory.

(* An example: m steps of the lazy walk on nat that moves one step to the
   right with probability p, and stays otherwise, observed from 0, give the
   binomial law of m trials. *)
Example lazy_walk_binomial (R : numDomainType) (p : R) (m : nat)
    (f : nat -> R) :
  iter m (fun g y => p * g y.+1 + (1 - p) * g y) f 0%N = binomial_mean m p f.
Proof.
pose A (g : nat -> R) y := g y.+1; pose B (g : nat -> R) (y : nat) := g y.
have hA : linear_op A by [].
have hB : linear_op B by [].
have AB g : A (B g) = B (A g) by [].
have iterA j g y : iter j A g y = g (y + j)%N.
  by elim: j y => [|j IH] y; rewrite ?addn0 //= /A IH addnS.
have iterB j g : iter j B g = g by elim: j => //= j ->.
rewrite (iter_mix_binomial p hA hB AB); apply: eq_binomial_mean => j _.
by rewrite iterA iterB.
Qed.
