From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg.

(**md**************************************************************************)
(* # Product laws by blocks                                                   *)
(*                                                                            *)
(* A tuple of n * d coordinates read as n rows of d coordinates, row i being  *)
(* made of the coordinates i * d + j for j < d, as the samples of the         *)
(* ellipsoid fitting papers are read.                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*   row_index i j == the index i * d + j of 'I_(n * d), for i : 'I_n and     *)
(*                    j : 'I_d                                                *)
(* tuple_rows n d x == the n rows of length d of the (n * d)-tuple x          *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - ge0_integral_tuple_prodS, integral_tuple_prodS: Fubini for the first     *)
(*   coordinate, \int[tuple_prod mu n.+1] F =                                 *)
(*   \int[mu 0]_t \int[tuple_prod (fun i => mu i.+1) n]_ts F (t :: ts), for F *)
(*   nonnegative and measurable, or integrable (integrable_tuple_prodS); the  *)
(*   lemmas of lindeberg.v state it for bounded F;                            *)
(* - ge0_integral_tuple_prod_prod: independent coordinates, the integral of   *)
(*   \prod_i f_i (x_i) against tuple_prod mu n is the product of the          *)
(*   integrals of the f_i against the mu i, for f_i nonnegative and           *)
(*   measurable.                                                              *)
(*                                                                            *)
(* Planned results (phase 5, stage 1); names come with the proofs:            *)
(* - coordinatewise maps preserve independence: for measurable f_i : T -> T', *)
(*   the image of tuple_prod mu n under x |-> [tuple f_i (x_i) | i < n] is    *)
(*   tuple_prod of the images of the mu i under the f_i, so the integral of a *)
(*   bounded measurable, a nonnegative measurable or an integrable G against  *)
(*   the image is the integral of x |-> G [tuple f_i (x_i) | i < n] against   *)
(*   tuple_prod mu n;                                                         *)
(* - rows: the image of tuple_prod mu (n * d) under tuple_rows n d is the     *)
(*   product over i < n of the laws tuple_prod (fun j => mu (i * d + j)) d of *)
(*   the rows, and tuple_rows is a measurable bijection;                      *)
(* - blocks: the image of tuple_prod mu (n + m) under the split into the      *)
(*   first n and the last m coordinates is the product of tuple_prod mu n and *)
(*   tuple_prod (fun i => mu (n + i)) m, so a block of coordinates has the    *)
(*   product law of its coordinates and disjoint blocks are independent.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section tuple_rows.
Context (T : Type) (n d : nat).

Lemma row_index_subproof (i : 'I_n) (j : 'I_d) : (i * d + j < n * d)%N.
Proof.
rewrite (@leq_trans (i * d + d)) ?ltn_add2l // -mulSnr.
by rewrite leq_mul2r ltn_ord orbT.
Qed.

Definition row_index (i : 'I_n) (j : 'I_d) : 'I_(n * d) :=
  Ordinal (row_index_subproof i j).

Definition tuple_rows (x : (n * d).-tuple T) : n.-tuple (d.-tuple T) :=
  [tuple [tuple tnth x (row_index i j) | j < d] | i < n].

End tuple_rows.

Section tuple_prod_integral.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* Fubini for the first coordinate, for nonnegative functions. *)
Lemma ge0_integral_tuple_prodS (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> \bar R) :
  measurable_fun [set: n.+1.-tuple T] F -> (forall x, 0 <= F x) ->
  \int[tuple_prod mu n.+1]_x F x =
  \int[mu 0%N]_t
    \int[tuple_prod (fun i => mu i.+1) n]_ts F (tuple_cons (t, ts)).
Proof.
move=> mF F0 /=.
rewrite [LHS](@ge0_integral_distribution _ _ _ _ _
  (mu 0%N \x tuple_prod (fun i => mu i.+1) n) (@tuple_cons _ T n))//.
rewrite fubini_tonelli1//; first exact: measurableT_comp.
by move=> ?; exact: F0.
Qed.

Lemma integrable_tuple_prodS (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> \bar R) :
  measurable_fun [set: n.+1.-tuple T] F ->
  (tuple_prod mu n.+1).-integrable [set: n.+1.-tuple T] F <->
  (mu 0%N \x tuple_prod (fun i => mu i.+1) n).-integrable
    [set: T * n.-tuple T] (F \o @tuple_cons _ T n).
Proof.
move=> mF.
have mFc : measurable_fun [set: T * n.-tuple T] (F \o @tuple_cons _ T n).
  exact: measurableT_comp.
have E : \int[tuple_prod mu n.+1]_x `|F x| =
    \int[mu 0%N \x tuple_prod (fun i => mu i.+1) n]_p
      `|(F \o @tuple_cons _ T n) p|.
  rewrite [LHS](@ge0_integral_distribution _ _ _ _ _
    (mu 0%N \x tuple_prod (fun i => mu i.+1) n) (@tuple_cons _ T n))//.
  exact: measurableT_comp.
by split=> /integrableP[_ fi]; apply/integrableP; split => //;
  [rewrite -E|rewrite E].
Qed.

(* Fubini for the first coordinate, for integrable functions. *)
Lemma integral_tuple_prodS (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> \bar R) :
  (tuple_prod mu n.+1).-integrable [set: n.+1.-tuple T] F ->
  \int[tuple_prod mu n.+1]_x F x =
  \int[mu 0%N]_t
    \int[tuple_prod (fun i => mu i.+1) n]_ts F (tuple_cons (t, ts)).
Proof.
move=> Fi; have mF := measurable_int _ Fi.
have Fci := (integrable_tuple_prodS mu mF).1 Fi.
rewrite [LHS](@integral_distribution _ _ _ _ _
  (mu 0%N \x tuple_prod (fun i => mu i.+1) n) (@tuple_cons _ T n))//.
by rewrite -(integral12_prod_meas1 Fci).
Qed.

(* Independent coordinates: the integral of a product of nonnegative
   functions of the coordinates is the product of the integrals. *)
Lemma ge0_integral_tuple_prod_prod (mu : nat -> probability T R) n
    (f : nat -> T -> R) :
  (forall i, measurable_fun [set: T] (f i)) -> (forall i t, (0 <= f i t)%R) ->
  \int[tuple_prod mu n]_x (\prod_(i < n) f i (tnth x i))%:E =
  \prod_(i < n) \int[mu i]_t (f i t)%:E.
Proof.
elim: n mu f => [|n IH] mu f mf f0.
  rewrite big_ord0; under eq_integral do rewrite big_ord0.
  by rewrite integral_cst//= probability_setT mul1e.
have mprod m (g : nat -> T -> R) : (forall i, measurable_fun [set: T] (g i)) ->
    measurable_fun [set: m.-tuple T]
      (fun x => (\prod_(i < m) g i (tnth x i))%:E).
  move=> mg; apply/measurable_EFinP; apply: measurable_prod => i _.
  exact: measurableT_comp (mg i) (measurable_tnth i).
have p0 m (g : nat -> T -> R) : (forall i t, (0 <= g i t)%R) ->
    forall x : m.-tuple T, 0 <= (\prod_(i < m) g i (tnth x i))%:E.
  by move=> g0 x; rewrite lee_fin prodr_ge0.
rewrite ge0_integral_tuple_prodS//; [exact: mprod|exact: p0|].
transitivity (\int[mu 0%N]_t ((f 0%N t)%:E *
    \prod_(i < n) \int[mu i.+1]_u (f i.+1 u)%:E)).
  apply: eq_integral => t _.
  transitivity (\int[tuple_prod (fun i => mu i.+1) n]_v
      ((f 0%N t)%:E * (\prod_(i < n) f i.+1 (tnth v i))%:E)).
    apply: eq_integral => v _; rewrite big_ord_recl EFinM.
    by under eq_bigr do rewrite tnthS.
  rewrite ge0_integralZl_EFin//.
  - by move=> x _; exact: (p0 n (fun i => f i.+1) (fun i => f0 i.+1)).
  - exact: (mprod n (fun i => f i.+1) (fun i => mf i.+1)).
  - congr (_ * _).
    exact: (IH (fun i => mu i.+1) (fun i => f i.+1) (fun i => mf i.+1)
      (fun i => f0 i.+1)).
have I0 : 0 <= \prod_(i < n) \int[mu i.+1]_u (f i.+1 u)%:E.
  by apply: prode_ge0 => i _; apply: integral_ge0 => t _; rewrite lee_fin.
have mf0 : measurable_fun [set: T] (fun t => (f 0%N t)%:E).
  by apply/measurable_EFinP; exact: mf.
rewrite ge0_integralZr//; first by move=> t _; rewrite lee_fin.
by rewrite [in RHS]big_ord_recl.
Qed.

End tuple_prod_integral.
