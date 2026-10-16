(* S6 assembled against ShiftedMixtureSatStatement. SparseShift handles
   arbitrary coordinate support and discharges every auxiliary baseline
   and target estimate. The absence of a symmetry hypothesis is the
   intentional strengthening described in the statement header.
   Source: doc/shifted-gaussian.tex, sparse non-Gaussian shifts. *)

From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import reals Rstruct.
From EllipsoidUniversality Require Import ShiftedMixtureSatStatement.
From EllipsoidUniversality.Shifted Require Import SparseShift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Theorem shifted_mixture_sat_theorem : shifted_mixture_sat_statement.
Proof.
split.
- move=> kappa K alpha k1 K0 a0 below N w mu n hfam fourth hn m hs.
  split; first by move=> d; exact: measurable_sparse_translated_pd_fit.
  exact: (@finite_sparse_shift_theorem kappa K alpha k1 K0 a0 below
    N w mu n hfam fourth hn m hs).
- move=> kappa K alpha k1 K0 a0 below w mu n hfam fourth hn m hs.
  split; first by move=> d; exact: measurable_sparse_translated_pd_fit.
  exact: (@countable_sparse_shift_theorem kappa K alpha k1 K0 a0 below
    w mu n hfam fourth hn m hs).
Qed.
