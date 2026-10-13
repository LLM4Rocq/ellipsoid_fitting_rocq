From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype sequences derive realfun exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.

(**md**************************************************************************)
(* # Derivatives of a log-partition function                                  *)
(*                                                                            *)
(* For a finite type X, weights w x > 0 and functions h x of a real parameter *)
(* t, the log-partition function t |-> ln (\sum_x w x exp (h x t)) has        *)
(* derivative the Gibbs mean of h' (is_derive_log_partition), and the         *)
(* derivative of the Gibbs mean of q is the mean of h' q + q' minus the       *)
(* product of the means of q and h' (is_derive_gibbs_mean). So, if the h x    *)
(* have three derivatives with |h'| <= b1, |h''| <= b2 and |h'''| <= b3, the  *)
(* log-partition function has three derivatives, and the third one is at      *)
(* most b3 + 6 b1 b2 + 6 b1^3 in absolute value (log_partition_derive3).      *)
(*                                                                            *)
(* Part of target T6 of phase 12: a Rocq formalization of the credited        *)
(* argument of the first paragraph of the proof of Theorem ext:sign of 'The   *)
(* free energy of the Ising random perceptron' (family 222 of the OpenAI math *)
(* collection, revision 1581d4cbd, sections/extensions.tex). The collection   *)
(* has no Lean version of it.                                                 *)
(*                                                                            *)
(* The manuscript bounds the third derivative of the normalized pressure by   *)
(* bounded Gibbs moments and cumulants of f', f'' and f'''. Here the third    *)
(* derivative is m3 - 3 m1 m2 + 2 m1^3 for the Gibbs means m1, m2 and m3 of   *)
(* h', h'^2 + h'' and h'^3 + 3 h' h'' + h''', and each term is bounded        *)
(* separately: no cancellation is used.                                       *)
(*                                                                            *)
(* ```                                                                        *)
(* gibbs_mean w H q == the mean of q under the probability on X with weights  *)
(*                     proportional to w x exp (H x)                          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

Section is_derive_fsum.
Context {R : realType} {X : finType}.

(* The derivative of a finite sum of functions. *)
Lemma is_derive_fsum (F F' : X -> R -> R) (t : R) :
  (forall x, is_derive t 1 (F x) (F' x t)) ->
  is_derive t 1 (fun t => \sum_x F x t) (\sum_x F' x t).
Proof.
move=> dF.
suff h (s : seq X) :
    is_derive t 1 (fun t => \sum_(x <- s) F x t) (\sum_(x <- s) F' x t).
  exact: h.
elim: s => [|y s IH].
  under eq_fun do rewrite big_nil.
  by rewrite big_nil; exact: is_derive_cst.
under eq_fun do rewrite big_cons.
by rewrite big_cons; exact: is_deriveD.
Qed.

End is_derive_fsum.

Section gibbs_mean.
Context {R : realType} {X : finType}.

(* The mean of q under the probability on X with weights w x exp (H x). *)
Definition gibbs_mean (w H q : X -> R) : R :=
  (\sum_x w x * expR (H x) * q x) / \sum_x w x * expR (H x).

Lemma gibbs_mass_gt0 (w H : X -> R) : (forall x, 0 < w x) ->
  (0 < #|X|)%N -> 0 < \sum_x w x * expR (H x).
Proof.
move=> w0 X0; have [x0 _] := card_gt0P X0.
rewrite (bigD1 x0) //=.
have h1 : 0 < w x0 * expR (H x0) by rewrite mulr_gt0 ?expR_gt0.
have h2 : 0 <= \sum_(x | x != x0) w x * expR (H x).
  by apply: sumr_ge0 => x _; rewrite mulr_ge0 ?expR_ge0 // ltW.
by move: (w x0 * _) (\sum_(_ | _) _) h1 h2 => a b; lra.
Qed.

Lemma gibbs_mean_le (w H q : X -> R) (b : R) : (forall x, 0 < w x) ->
  (0 < #|X|)%N -> (forall x, `|q x| <= b) -> `|gibbs_mean w H q| <= b.
Proof.
move=> w0 X0 qb; have Z0 := gibbs_mass_gt0 H w0 X0.
rewrite /gibbs_mean normrM normfV (gtr0_norm Z0) ler_pdivrMr //.
apply: le_trans (ler_norm_sum _ _ _) _.
rewrite mulr_sumr; apply: ler_sum => x _.
have e0 : 0 < w x * expR (H x) by rewrite mulr_gt0 ?expR_gt0.
by rewrite normrM (gtr0_norm e0) mulrC ler_wpM2r // ltW.
Qed.

End gibbs_mean.

Section log_partition.
Context {R : realType} {X : finType}.
Variables (w : X -> R) (h h1 : X -> R -> R).
Hypothesis w0 : forall x, 0 < w x.
Hypothesis X0 : (0 < #|X|)%N.
Hypothesis dh : forall x (t : R), is_derive t 1 (h x) (h1 x t).

Local Notation mean q t := (gibbs_mean w (h^~ t) (q^~ t)).

Lemma is_derive_gibbs_sum (q q' : X -> R -> R) (t : R) :
  (forall x, is_derive t 1 (q x) (q' x t)) ->
  is_derive t 1 (fun t => \sum_x w x * expR (h x t) * q x t)
    (\sum_x w x * expR (h x t) * (h1 x t * q x t + q' x t)).
Proof.
move=> dq.
apply: (is_derive_fsum (F := fun x t => w x * expR (h x t) * q x t)
  (F' := fun x t => w x * expR (h x t) * (h1 x t * q x t + q' x t))) => x.
have de : is_derive t 1 (fun t => expR (h x t)) (expR (h x t) * h1 x t).
  exact: (is_derive1_comp (is_derive_expR _) (dh x t)).
have dqx := dq x.
by apply: is_derive_eq; rewrite /GRing.scale /=; ring.
Qed.

Lemma is_derive_gibbs_mass (t : R) :
  is_derive t 1 (fun t => \sum_x w x * expR (h x t))
    (\sum_x w x * expR (h x t) * h1 x t).
Proof.
apply: (is_derive_fsum (F := fun x t => w x * expR (h x t))
  (F' := fun x t => w x * expR (h x t) * h1 x t)) => x.
have de : is_derive t 1 (fun t => expR (h x t)) (expR (h x t) * h1 x t).
  exact: (is_derive1_comp (is_derive_expR _) (dh x t)).
by apply: is_derive_eq; rewrite /GRing.scale /=; ring.
Qed.

(* The derivative of a Gibbs mean: mean (h1 q + q') - mean q * mean h1. *)
Lemma is_derive_gibbs_mean (q q' : X -> R -> R) (t : R) :
  (forall x, is_derive t 1 (q x) (q' x t)) ->
  is_derive t 1 (fun t => mean q t)
    (mean (fun x t => h1 x t * q x t + q' x t) t - mean q t * mean h1 t).
Proof.
move=> dq.
have Z0 : 0 < \sum_x w x * expR (h x t) := gibbs_mass_gt0 _ w0 X0.
have dZV := is_deriveV (lt0r_neq0 Z0) (is_derive_gibbs_mass t).
apply: is_derive_eq (is_deriveM (is_derive_gibbs_sum dq) dZV) _.
rewrite /gibbs_mean /GRing.scale /=.
by have Zn := lt0r_neq0 Z0; field.
Qed.

(* The derivative of the log-partition function is the mean of h1. *)
Lemma is_derive_log_partition (t : R) :
  is_derive t 1 (fun t => ln (\sum_x w x * expR (h x t))) (mean h1 t).
Proof.
have Z0 : 0 < \sum_x w x * expR (h x t) := gibbs_mass_gt0 _ w0 X0.
apply: is_derive_eq (is_derive1_comp (is_derive1_ln Z0)
  (is_derive_gibbs_mass t)) _.
by rewrite /gibbs_mean mulrC.
Qed.

(* Three derivatives of the log-partition function, the third bounded by
   b3 + 6 b1 b2 + 6 b1^3 when |h1| <= b1, |h2| <= b2 and |h3| <= b3. *)
Theorem log_partition_derive3 (h2 h3 : X -> R -> R) :
  (forall x (t : R), is_derive t 1 (h1 x) (h2 x t)) ->
  (forall x (t : R), is_derive t 1 (h2 x) (h3 x t)) ->
  exists L1 L2 L3 : R -> R,
  [/\ forall t : R,
        is_derive t 1 (fun t => ln (\sum_x w x * expR (h x t))) (L1 t),
      forall t : R, is_derive t 1 L1 (L2 t),
      forall t : R, is_derive t 1 L2 (L3 t) &
      forall t b1 b2 b3 : R, (forall x, `|h1 x t| <= b1) ->
        (forall x, `|h2 x t| <= b2) -> (forall x, `|h3 x t| <= b3) ->
        `|L3 t| <= b3 + 6 * b1 * b2 + 6 * b1 ^+ 3].
Proof.
move=> dh1 dh2.
pose q2 x t := h1 x t * h1 x t + h2 x t.
pose q2' x t := h2 x t * h1 x t + h1 x t * h2 x t + h3 x t.
pose q3 x t := h1 x t * q2 x t + q2' x t.
have dq2 x (t : R) : is_derive t 1 (q2 x) (q2' x t).
  have d1 := dh1 x t; have d2 := dh2 x t.
  by rewrite /q2 /q2'; apply: is_derive_eq; rewrite /GRing.scale /=; ring.
exists (fun t => mean h1 t), (fun t => mean q2 t - mean h1 t * mean h1 t),
  (fun t => mean q3 t - mean q2 t * mean h1 t -
            2 * mean h1 t * (mean q2 t - mean h1 t * mean h1 t)); split.
- exact: is_derive_log_partition.
- by move=> t; exact: (is_derive_gibbs_mean (dh1^~ t)).
- move=> t.
  have dm2 := is_derive_gibbs_mean (dq2^~ t).
  have dm1 := is_derive_gibbs_mean (dh1^~ t).
  by apply: is_derive_eq; rewrite /GRing.scale /= -/q2 -/q3; ring.
move=> t b1 b2 b3 hb1 hb2 hb3.
have [x0 _] := card_gt0P X0.
have b10 : 0 <= b1 := le_trans (normr_ge0 _) (hb1 x0).
have b20 : 0 <= b2 := le_trans (normr_ge0 _) (hb2 x0).
have hq2 x : `|q2 x t| <= b1 * b1 + b2.
  rewrite /q2 (le_trans (ler_normD _ _)) // normrM lerD //.
  exact: ler_pM.
have hq3 x :
    `|q3 x t| <= b1 * (b1 * b1 + b2) + (b2 * b1 + b1 * b2 + b3).
  rewrite /q3 (le_trans (ler_normD _ _)) // normrM lerD //.
    exact: ler_pM.
  rewrite /q2' (le_trans (ler_normD _ _)) // lerD //.
  rewrite (le_trans (ler_normD _ _)) // !normrM lerD //; exact: ler_pM.
have m1b : `|mean h1 t| <= b1 := gibbs_mean_le _ w0 X0 hb1.
have m2b : `|mean q2 t| <= b1 * b1 + b2 := gibbs_mean_le _ w0 X0 hq2.
have m3b := gibbs_mean_le (h^~ t) w0 X0 hq3.
move: m1b m2b m3b; move: (mean q3 t) (mean q2 t) (mean h1 t).
move=> A B m hm hB hA.
have e1 : `|B * m| <= (b1 * b1 + b2) * b1 by rewrite normrM ler_pM.
have e2 : `|m * m| <= b1 * b1 by rewrite normrM ler_pM.
have e3 : `|B - m * m| <= (b1 * b1 + b2) + b1 * b1.
  exact: le_trans (ler_normB _ _) (lerD hB e2).
have e4 : `|2 * m * (B - m * m)| <= 2 * b1 * ((b1 * b1 + b2) + b1 * b1).
  by rewrite !normrM normr_nat ler_pM // ?mulr_ge0 // ler_pM.
apply: le_trans (ler_normB _ _) _.
apply: le_trans (lerD (ler_normB _ _) e4) _.
apply: le_trans (lerD (lerD hA e1) (lexx _)) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

End log_partition.
