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
(*                                                                            *)
(* This file is part of target T7 of phase 12: a Rocq formalization of the    *)
(* finite means of the credited argument of the proposition 'Polynomial       *)
(* concentration' of 'A limiting satisfiability threshold for every fixed     *)
(* clause size' (family 235 of the OpenAI math collection, revision           *)
(* 1581d4cbd, source/sections/concentration.tex), where the expectations over *)
(* independent uniform data are finite averages; the statement of T7 is       *)
(* written with these means. It follows the finite means of the Lean          *)
(* development of the collection, in lean/OAI/Probability/RandomSAT:          *)
(* Lean: uniformMean (FiniteMean.lean, line 17)                               *)
(* Lean: uniformVariance (FiniteMean.lean, line 107)                          *)
(* Lean: uniformVariance_fin_succ (Variance.lean, line 322)                   *)
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

Import GRing.Theory Num.Theory.
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
