From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import arithmetic_tactic ring_tactic.

(**md**************************************************************************)
(* # Uniform means on finite types                                            *)
(*                                                                            *)
(* For a finite type T and f : T -> R, unif_mean f = #|T|^-1 \sum_x f x is    *)
(* the mean of f under the uniform law of T, and unif_var f = unif_mean (f -  *)
(* unif_mean f)^2 its variance; R is a realFieldType. A tuple of m            *)
(* independent uniform coordinates is a uniform element of m.-tuple T, so     *)
(* these means express the expectations of functions of independent uniform   *)
(* random elements of finite sets as finite averages, without measure theory. *)
(*                                                                            *)
(* - Linearity, monotonicity and constants (unif_meanD, unif_meanZ,           *)
(*   unif_mean_sum, ler_unif_mean, unif_mean_cst), extensionality             *)
(*   (eq_unif_mean, eq_unif_var), invariance under bijections (unif_mean_bij, *)
(*   unif_var_bij), and the mean of the indicator of a predicate as the       *)
(*   proportion of the elements that satisfy it (unif_mean_indicator).        *)
(* - Fubini: the mean over T1 * T2 is the iterated mean (unif_mean_pair,      *)
(*   unif_mean_comm); the mean over m.+1.-tuple T is the mean over the head   *)
(*   of the mean over the tail (unif_mean_tuple_cons), and the mean of a      *)
(*   product over the coordinates is the product of the means                 *)
(*   (unif_mean_tuple_prod). The uniform law of T1 + T2 is the mixture of the *)
(*   uniform laws of T1 and T2 with weights #|T1| and #|T2|                   *)
(*   (unif_mean_sum_type).                                                    *)
(* - The variance: Var f = E f^2 - (E f)^2 (unif_varE), Var f <= E (f - c)^2  *)
(*   for every c (unif_var_le), (E f)^2 <= E f^2 (unif_mean_sqr_le), and the  *)
(*   law of total variance for a pair and for the head of a tuple             *)
(*   (unif_var_pair, unif_var_tuple_cons).                                    *)
(* - Bounds, for target T9 of phase 13: the union bound (unif_mean_union),    *)
(*   the complement of an event (unif_mean_indicatorN), Markov's inequality   *)
(*   (unif_mean_markov), the bound of a mean by a cutoff t >= 0 and the       *)
(*   probability of the event f >= t (unif_mean_cutoff), Chebyshev's          *)
(*   inequality (unif_chebyshev), and the independence of the coordinates of  *)
(*   a uniform tuple (unif_mean_tuple_prod_ord), in particular of the         *)
(*   coordinates in a set J of positions (unif_mean_tuple_prod_set; the       *)
(*   example unif_mean_fair_bits). Each of these statements is also a         *)
(*   compiled Prop definition, named after its lemma with the suffix          *)
(*   _statement, for review with batch 1 of phase 13; these definitions go    *)
(*   once the statements are accepted.                                        *)
(*                                                                            *)
(* This file is part of target T7 of phase 12: a Rocq formalization of the    *)
(* finite means of the credited argument of the proposition 'Polynomial       *)
(* concentration' of 'A limiting satisfiability threshold for every fixed     *)
(* clause size' (family 235 of the OpenAI math collection, revision           *)
(* 1581d4cbd, source/sections/concentration.tex), where the expectations over *)
(* independent uniform data are finite averages; the means of the statement   *)
(* of T7, in its definitions file, unfold to these. It follows the finite     *)
(* means of the Lean development of the collection, in                        *)
(* lean/OAI/Probability/RandomSAT:                                            *)
(* Lean: uniformMean (FiniteMean.lean, line 17)                               *)
(* Lean: uniformVariance (FiniteMean.lean, line 107)                          *)
(* Lean: uniformVariance_fin_succ (Variance.lean, line 322)                   *)
(*                                                                            *)
(* The bounds of phase 13 belong to target T9 of phase 13, the limiting       *)
(* threshold of the same manuscript: they are the finite means of the lemma   *)
(* 'Bounds on the centers' (source/sections/anchors.tex) and the Chebyshev    *)
(* step of the proposition 'Polynomial concentration', and follow these       *)
(* declarations of the Lean development:                                      *)
(* Lean: uniformProbability_exists_le (CenterBounds.lean, line 18)            *)
(* Lean: uniformMean_lower_tail (CenterBounds.lean, line 82)                  *)
(* Lean: uniformMean_upper_cutoff (CenterBounds.lean, line 92)                *)
(* Lean: uniformProbability_forall_mem (CenterBounds.lean, line 216)          *)
(* Lean: uniform_chebyshev (Concentration.lean, line 94)                      *)
(*                                                                            *)
(* Three of these statements drop a hypothesis of their Lean versions, and    *)
(* are proved without it: unif_mean_markov holds for t of any sign, where     *)
(* Lean assumes 0 <= t; unif_mean_cutoff and unif_chebyshev hold for an empty *)
(* T, where they read 0 <= t and 0 <= 0, while Lean assumes T nonempty.       *)
(*                                                                            *)
(* ```                                                                        *)
(*   unif_mean f == #|T|^-1 * \sum_(x : T) f x, the mean of f : T -> R        *)
(*                  under the uniform law of the finite type T                *)
(*    unif_var f == unif_mean (fun x => (f x - unif_mean f) ^+ 2)             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section unif_mean.
Variable R : realFieldType.

Definition unif_mean (T : finType) (f : T -> R) : R :=
  (#|T|%:R)^-1 * \sum_(x : T) f x.

Definition unif_var (T : finType) (f : T -> R) : R :=
  unif_mean (fun x => (f x - unif_mean f) ^+ 2).

Lemma unif_mean_sumE (T : finType) (f : T -> R) :
  #|T|%:R * unif_mean f = \sum_(x : T) f x.
Proof.
rewrite /unif_mean; have [T0|T0] := posnP #|T|.
  by rewrite T0 mul0r big1 // => x _; case: (fintype0 x T0).
by rewrite mulrA mulfV ?mul1r // pnatr_eq0 -lt0n.
Qed.

Lemma eq_unif_mean (T : finType) (f g : T -> R) :
  f =1 g -> unif_mean f = unif_mean g.
Proof. by move=> fg; rewrite /unif_mean (eq_bigr _ (fun x _ => fg x)). Qed.

Lemma eq_unif_var (T : finType) (f g : T -> R) :
  f =1 g -> unif_var f = unif_var g.
Proof.
move=> fg; rewrite /unif_var (eq_unif_mean fg).
by apply: eq_unif_mean => x; rewrite fg.
Qed.

Lemma unif_mean_cst (T : finType) (c : R) : (0 < #|T|)%N ->
  unif_mean (fun _ : T => c) = c.
Proof.
move=> T0; rewrite /unif_mean sumr_const -[c *+ _]mulr_natl mulrA.
rewrite mulVf ?mul1r //.
by rewrite pnatr_eq0 -lt0n.
Qed.

Lemma unif_meanD (T : finType) (f g : T -> R) :
  unif_mean (fun x => f x + g x) = unif_mean f + unif_mean g.
Proof. by rewrite /unif_mean big_split mulrDr. Qed.

Lemma unif_meanN (T : finType) (f : T -> R) :
  unif_mean (fun x => - f x) = - unif_mean f.
Proof. by rewrite /unif_mean sumrN mulrN. Qed.

Lemma unif_meanB (T : finType) (f g : T -> R) :
  unif_mean (fun x => f x - g x) = unif_mean f - unif_mean g.
Proof. by rewrite unif_meanD unif_meanN. Qed.

Lemma unif_meanZ (T : finType) (c : R) (f : T -> R) :
  unif_mean (fun x => c * f x) = c * unif_mean f.
Proof. by rewrite /unif_mean -mulr_sumr mulrCA. Qed.

Lemma unif_meanZr (T : finType) (c : R) (f : T -> R) :
  unif_mean (fun x => f x * c) = unif_mean f * c.
Proof.
by rewrite mulrC -unif_meanZ; apply: eq_unif_mean => x; rewrite mulrC.
Qed.

Lemma unif_mean_sum (T I : finType) (P : pred I) (F : I -> T -> R) :
  unif_mean (fun x => \sum_(i | P i) F i x) = \sum_(i | P i) unif_mean (F i).
Proof.
by rewrite /unif_mean exchange_big mulr_sumr.
Qed.

Lemma ler_unif_mean (T : finType) (f g : T -> R) :
  (forall x, f x <= g x) -> unif_mean f <= unif_mean g.
Proof.
move=> fg; rewrite /unif_mean ler_wpM2l ?invr_ge0 ?ler0n //.
by apply: ler_sum => x _; exact: fg.
Qed.

Lemma unif_mean_ge0 (T : finType) (f : T -> R) :
  (forall x, 0 <= f x) -> 0 <= unif_mean f.
Proof.
move=> f0; rewrite /unif_mean mulr_ge0 ?invr_ge0 ?ler0n //.
by apply: sumr_ge0 => x _; exact: f0.
Qed.

(* The mean of an indicator is the proportion of the elements where it
   holds. *)
Lemma unif_mean_indicator (T : finType) (P : pred T) :
  unif_mean (fun x => (P x)%:R) = #|[set x | P x]|%:R / #|T|%:R.
Proof.
rewrite /unif_mean mulrC; congr (_ / _).
rewrite -sum1dep_card natr_sum [RHS]big_mkcond /=.
by apply: eq_bigr => x _; case: (P x).
Qed.

Lemma unif_mean_le (T : finType) (f : T -> R) (c : R) : (0 < #|T|)%N ->
  (forall x, f x <= c) -> unif_mean f <= c.
Proof.
by move=> T0 fc; rewrite -(unif_mean_cst c T0); exact: ler_unif_mean.
Qed.

Lemma unif_mean_ge (T : finType) (f : T -> R) (c : R) : (0 < #|T|)%N ->
  (forall x, c <= f x) -> c <= unif_mean f.
Proof.
by move=> T0 fc; rewrite -(unif_mean_cst c T0); exact: ler_unif_mean.
Qed.

(* The mean is invariant under a bijection. *)
Lemma unif_mean_bij (T1 T2 : finType) (h : T1 -> T2) (f : T2 -> R) :
  bijective h -> unif_mean (fun x => f (h x)) = unif_mean f.
Proof.
move=> hb; rewrite /unif_mean (bij_eq_card hb); congr (_ * _).
by symmetry; apply: reindex; exact: onW_bij.
Qed.

(* Fubini for the uniform law of a product. *)
Lemma unif_mean_pair (T1 T2 : finType) (f : T1 * T2 -> R) :
  unif_mean f = unif_mean (fun x => unif_mean (fun y => f (x, y))).
Proof.
rewrite /unif_mean card_prod natrM invfM -mulrA; congr (_ * _).
rewrite -mulr_sumr pair_bigA /=; congr (_ * _).
by apply: eq_bigr => -[x y].
Qed.

Lemma unif_mean_comm (T1 T2 : finType) (f : T1 -> T2 -> R) :
  unif_mean (fun x => unif_mean (fun y => f x y)) =
  unif_mean (fun y => unif_mean (fun x => f x y)).
Proof.
have hb : bijective (fun q : T2 * T1 => (q.2, q.1)).
  by exists (fun p : T1 * T2 => (p.2, p.1)) => -[].
rewrite -(unif_mean_pair (fun p : T1 * T2 => f p.1 p.2)).
rewrite -(unif_mean_pair (fun q : T2 * T1 => f q.2 q.1)).
by rewrite -(unif_mean_bij (fun p : T1 * T2 => f p.1 p.2) hb).
Qed.

Lemma bij_tuple_cons (T : Type) m :
  bijective (fun p : T * m.-tuple T => [tuple of p.1 :: p.2]).
Proof.
exists (fun t => (thead t, [tuple of behead t])) => [[x t]|t] /=.
  by congr pair; apply: val_inj.
by rewrite [RHS]tuple_eta.
Qed.

(* The coordinates of a uniform tuple: the head and the tail are
   independent and uniform. *)
Lemma unif_mean_tuple0 (T : finType) (f : 0.-tuple T -> R) :
  unif_mean f = f [tuple].
Proof.
rewrite /unif_mean card_tuple expn0 invr1 mul1r (big_pred1 [tuple]) //.
by move=> t; rewrite inE tuple0 eqxx.
Qed.

Lemma unif_mean_tuple_cons (T : finType) m (f : m.+1.-tuple T -> R) :
  unif_mean f =
  unif_mean (fun x => unif_mean (fun t : m.-tuple T => f [tuple of x :: t])).
Proof.
rewrite -(unif_mean_pair (fun p : T * m.-tuple T => f [tuple of p.1 :: p.2])).
by rewrite (unif_mean_bij f (@bij_tuple_cons T m)).
Qed.

(* Independent coordinates: the mean of a product over the coordinates of a
   uniform tuple is the product of the means. *)
Lemma unif_mean_tuple_prod (T : finType) m (g : T -> R) :
  unif_mean (fun t : m.-tuple T => \prod_(x <- t) g x) = unif_mean g ^+ m.
Proof.
elim: m => [|m IH]; first by rewrite unif_mean_tuple0 big_nil expr0.
rewrite unif_mean_tuple_cons exprS -unif_meanZr.
apply: eq_unif_mean => x /=; rewrite -IH -unif_meanZ.
by apply: eq_unif_mean => t; rewrite big_cons.
Qed.

(* The uniform law of a sum type is a mixture of the uniform laws of its
   summands. *)
Lemma unif_mean_sum_type (T1 T2 : finType) (f : T1 + T2 -> R) :
  unif_mean f =
  #|T1|%:R / (#|T1| + #|T2|)%:R * unif_mean (fun x => f (inl x)) +
  #|T2|%:R / (#|T1| + #|T2|)%:R * unif_mean (fun y => f (inr y)).
Proof.
rewrite {1}/unif_mean card_sum big_sumType /=.
rewrite -(unif_mean_sumE (fun x => f (inl x))).
rewrite -(unif_mean_sumE (fun y => f (inr y))).
by rewrite mulrDr !mulrA; ring.
Qed.

(* The variance: E f^2 - (E f)^2, at most E (f - c)^2, and Jensen. *)
Lemma unif_mean_sqr_dev (T : finType) (f : T -> R) (c : R) : (0 < #|T|)%N ->
  unif_mean (fun x => (f x - c) ^+ 2) =
  unif_mean (fun x => f x ^+ 2) - 2 * c * unif_mean f + c ^+ 2.
Proof.
move=> T0.
have e x : (f x - c) ^+ 2 = f x ^+ 2 + (- (2 * c)) * f x + c ^+ 2 by ring.
rewrite (eq_unif_mean e) !unif_meanD unif_meanZ unif_mean_cst //; ring.
Qed.

Lemma unif_varE (T : finType) (f : T -> R) : (0 < #|T|)%N ->
  unif_var f = unif_mean (fun x => f x ^+ 2) - unif_mean f ^+ 2.
Proof. by move=> T0; rewrite /unif_var unif_mean_sqr_dev //; ring. Qed.

Lemma unif_var_le (T : finType) (f : T -> R) (c : R) : (0 < #|T|)%N ->
  unif_var f <= unif_mean (fun x => (f x - c) ^+ 2).
Proof.
move=> T0; rewrite unif_varE // unif_mean_sqr_dev //.
by have := sqr_ge0 (unif_mean f - c); rewrite sqrrB; lra.
Qed.

Lemma unif_mean_sqr_le (T : finType) (f : T -> R) :
  unif_mean f ^+ 2 <= unif_mean (fun x => f x ^+ 2).
Proof.
have [T0|T0] := posnP #|T|.
  have -> : unif_mean f = 0.
    by rewrite /unif_mean T0 invr0 mul0r.
  by rewrite expr0n /= unif_mean_ge0 // => x; exact: sqr_ge0.
have := unif_var_le f (unif_mean f) T0; rewrite unif_varE //.
have : 0 <= unif_var f.
  by apply: unif_mean_ge0 => x; exact: sqr_ge0.
by rewrite unif_varE //; lra.
Qed.

Lemma unif_var_ge0 (T : finType) (f : T -> R) : 0 <= unif_var f.
Proof. by apply: unif_mean_ge0 => x; exact: sqr_ge0. Qed.

Lemma unif_var_addl (T : finType) (c : R) (f : T -> R) : (0 < #|T|)%N ->
  unif_var (fun x => c + f x) = unif_var f.
Proof.
move=> T0; rewrite /unif_var unif_meanD unif_mean_cst //.
by apply: eq_unif_mean => x; congr (_ ^+ 2); ring.
Qed.

(* The law of total variance, for a pair and for the head of a tuple. *)
Lemma unif_var_pair (T1 T2 : finType) (f : T1 -> T2 -> R) :
  (0 < #|T1|)%N -> (0 < #|T2|)%N ->
  unif_var (fun p : T1 * T2 => f p.1 p.2) =
  unif_mean (fun x => unif_var (f x)) + unif_var (fun x => unif_mean (f x)).
Proof.
move=> T10 T20.
have T0 : (0 < #|{: T1 * T2}|)%N by rewrite card_prod muln_gt0 T10.
rewrite !unif_varE //.
under [in RHS]eq_unif_mean do rewrite unif_varE //.
rewrite unif_meanB !(unif_mean_pair (fun p => _)) /=.
by ring.
Qed.

Lemma unif_var_bij (T1 T2 : finType) (h : T1 -> T2) (f : T2 -> R) :
  bijective h -> unif_var (fun x => f (h x)) = unif_var f.
Proof.
move=> hb; rewrite /unif_var (unif_mean_bij f hb).
exact: (unif_mean_bij (fun y => (f y - unif_mean f) ^+ 2) hb).
Qed.

Lemma unif_var_tuple_cons (T : finType) m (f : m.+1.-tuple T -> R) :
  (0 < #|T|)%N ->
  unif_var f =
  unif_mean (fun x => unif_var (fun t : m.-tuple T => f [tuple of x :: t])) +
  unif_var (fun x => unif_mean (fun t : m.-tuple T => f [tuple of x :: t])).
Proof.
move=> T0; have Tm0 : (0 < #|{: m.-tuple T}|)%N.
  by rewrite card_tuple expn_gt0 T0.
rewrite -(unif_var_pair (fun x (t : m.-tuple T) => f [tuple of x :: t])) //.
exact: (esym (unif_var_bij f (@bij_tuple_cons T m))).
Qed.

End unif_mean.

(* The general statements of phase 13, for review. *)

(* The union bound: the probability that one of the events P i holds is at
   most the sum of their probabilities. *)
Definition unif_mean_union_statement : Prop :=
  forall (R : realFieldType) (T I : finType) (P : I -> pred T),
  unif_mean (fun x => [exists i, P i x]%:R : R) <=
  \sum_i unif_mean (fun x => (P i x)%:R : R).

(* The complement of an event. *)
Definition unif_mean_indicatorN_statement : Prop :=
  forall (R : realFieldType) (T : finType) (P : pred T), (0 < #|T|)%N ->
  unif_mean (fun x => (~~ P x)%:R : R) = 1 - unif_mean (fun x => (P x)%:R : R).

(* Markov's inequality for a nonnegative f; t may have any sign. *)
Definition unif_mean_markov_statement : Prop :=
  forall (R : realFieldType) (T : finType) (f : T -> R) (t : R),
  (forall x, 0 <= f x) ->
  t * unif_mean (fun x => (t <= f x)%R%:R : R) <= unif_mean f.

(* A bound by a cutoff: if f <= M, then E f <= t + M P(f >= t) for t >= 0. *)
Definition unif_mean_cutoff_statement : Prop :=
  forall (R : realFieldType) (T : finType) (f : T -> R) (M t : R),
  0 <= t -> (forall x, f x <= M) ->
  unif_mean f <= t + M * unif_mean (fun x => (t <= f x)%R%:R : R).

(* Chebyshev's inequality. *)
Definition unif_chebyshev_statement : Prop :=
  forall (R : realFieldType) (T : finType) (f : T -> R) (t : R), 0 < t ->
  unif_mean (fun x => (t <= `|f x - unif_mean f|)%R%:R : R) <=
  unif_var f / t ^+ 2.

(* The coordinates of a uniform tuple are independent: the mean of a
   product of functions of the coordinates is the product of the means. *)
Definition unif_mean_tuple_prod_ord_statement : Prop :=
  forall (R : realFieldType) (T : finType) (m : nat) (g : 'I_m -> T -> R),
  unif_mean (fun t : m.-tuple T => \prod_(i < m) g i (tnth t i)) =
  \prod_(i < m) unif_mean (g i).

(* In particular, the coordinates in a set J of positions are independent:
   the mean of a product over J is the product of the means. *)
Definition unif_mean_tuple_prod_set_statement : Prop :=
  forall (R : realFieldType) (T : finType) (m : nat) (J : {set 'I_m})
         (g : T -> R),
  (0 < #|T|)%N ->
  unif_mean (fun t : m.-tuple T => \prod_(i in J) g (tnth t i)) =
  unif_mean g ^+ #|J|.

Section unif_mean_bounds.
Variable R : realFieldType.

(* The union bound. *)
Lemma unif_mean_union (T I : finType) (P : I -> pred T) :
  unif_mean (fun x => [exists i, P i x]%:R : R) <=
  \sum_i unif_mean (fun x => (P i x)%:R : R).
Proof.
rewrite -unif_mean_sum; apply: ler_unif_mean => x.
case: existsP => [[i Pi]|_]; last by apply: sumr_ge0 => i _; exact: ler0n.
rewrite (bigD1 i) //= Pi lerDl; apply: sumr_ge0 => j _; exact: ler0n.
Qed.

(* The complement of an event. *)
Lemma unif_mean_indicatorN (T : finType) (P : pred T) : (0 < #|T|)%N ->
  unif_mean (fun x => (~~ P x)%:R : R) = 1 - unif_mean (fun x => (P x)%:R : R).
Proof.
move=> T0; rewrite -[X in X - _](unif_mean_cst (1 : R) T0) -unif_meanB.
by apply: eq_unif_mean => x; case: (P x); rewrite ?subrr ?subr0.
Qed.

(* Markov's inequality for a nonnegative f; t may have any sign. *)
Lemma unif_mean_markov (T : finType) (f : T -> R) (t : R) :
  (forall x, 0 <= f x) ->
  t * unif_mean (fun x => (t <= f x)%R%:R : R) <= unif_mean f.
Proof.
move=> f0; rewrite -unif_meanZ; apply: ler_unif_mean => x.
by case: (lerP t (f x)) => h; rewrite ?mulr1 ?mulr0.
Qed.

(* A bound by a cutoff: if f <= M, then E f <= t + M P(f >= t) for t >= 0. *)
Lemma unif_mean_cutoff (T : finType) (f : T -> R) (M t : R) :
  0 <= t -> (forall x, f x <= M) ->
  unif_mean f <= t + M * unif_mean (fun x => (t <= f x)%R%:R : R).
Proof.
move=> t0 fM; have [T0|T0] := posnP #|T|.
  have e (g : T -> R) : unif_mean g = 0 by rewrite /unif_mean T0 invr0 mul0r.
  by rewrite !e mulr0 addr0.
rewrite -unif_meanZ -[X in _ <= X + _](unif_mean_cst t T0) -unif_meanD.
apply: ler_unif_mean => x; case: (lerP t (f x)) => h /=.
  by rewrite mulr1 -[f x]add0r lerD.
by rewrite mulr0 addr0 ltW.
Qed.

(* Chebyshev's inequality. *)
Lemma unif_chebyshev (T : finType) (f : T -> R) (t : R) : 0 < t ->
  unif_mean (fun x => (t <= `|f x - unif_mean f|)%R%:R : R) <=
  unif_var f / t ^+ 2.
Proof.
move=> t0; rewrite ler_pdivlMr ?exprn_gt0 // -unif_meanZr /unif_var.
apply: ler_unif_mean => x.
case: (lerP t `|f x - unif_mean f|) => h; rewrite ?mul1r ?mul0r ?sqr_ge0 //.
rewrite -[(f x - unif_mean f) ^+ 2]real_normK ?num_real //.
by rewrite lerXn2r // ?nnegrE ?normr_ge0 // ltW.
Qed.

(* The coordinates of a uniform tuple are independent: the mean of a product
   of functions of the coordinates is the product of the means. *)
Lemma unif_mean_tuple_prod_ord (T : finType) m (g : 'I_m -> T -> R) :
  unif_mean (fun t : m.-tuple T => \prod_(i < m) g i (tnth t i)) =
  \prod_(i < m) unif_mean (g i).
Proof.
elim: m g => [|m IH] g; first by rewrite unif_mean_tuple0 !big_ord0.
rewrite unif_mean_tuple_cons big_ord_recl -unif_meanZr.
apply: eq_unif_mean => x /=; rewrite -(IH (fun i => g (lift ord0 i))).
rewrite -unif_meanZ; apply: eq_unif_mean => t.
rewrite big_ord_recl; congr (_ * _).
by apply: eq_bigr => i _; rewrite tnthS.
Qed.

Lemma unif_mean_tuple_prod_set (T : finType) m (J : {set 'I_m}) (g : T -> R) :
  (0 < #|T|)%N ->
  unif_mean (fun t : m.-tuple T => \prod_(i in J) g (tnth t i)) =
  unif_mean g ^+ #|J|.
Proof.
move=> T0; pose h i y := if i \in J then g y else 1.
transitivity (unif_mean (fun t : m.-tuple T => \prod_(i < m) h i (tnth t i))).
  by apply: eq_unif_mean => t; rewrite big_mkcond.
rewrite unif_mean_tuple_prod_ord -prodr_const [RHS]big_mkcond /=.
by apply: eq_bigr => i _; rewrite /h; case: (i \in J); rewrite ?unif_mean_cst.
Qed.

End unif_mean_bounds.

(* An example: for m independent fair bits, the probability that the bits
   at the positions of J are all 1 is 2^-#|J|. *)
Example unif_mean_fair_bits (R : realFieldType) m (J : {set 'I_m}) :
  unif_mean (fun t : m.-tuple bool => \prod_(i in J) (tnth t i)%:R : R) =
  2^-1 ^+ #|J|.
Proof.
rewrite (@unif_mean_tuple_prod_set R bool m J (fun b => b%:R)) ?card_bool //.
congr (_ ^+ _).
rewrite unif_mean_indicator card_bool.
have -> : #|[set b : bool | b]| = 1%N.
  rewrite (_ : [set b : bool | b] = [set true]) ?cards1 //.
  by apply/setP => -[]; rewrite !inE.
by rewrite div1r.
Qed.
