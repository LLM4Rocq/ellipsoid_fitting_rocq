(* S5 assembled against ShiftedMixtureUnsatStatement. The same explicit
   margin from SymmetricQuadric serves both finite and countable families.
   Source: doc/shifted-gaussian.tex, symmetric-mixture nonexistence. *)

From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import reals Rstruct.
From EllipsoidUniversality Require Import ShiftedMixtureUnsatStatement.
From EllipsoidUniversality.Shifted Require Import SymmetricQuadric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Theorem shifted_mixture_unsat_theorem : shifted_mixture_unsat_statement.
Proof.
move=> kappa alpha k1 above.
exists (symmetric_quadric_margin kappa alpha).
split; first exact: symmetric_quadric_margin_gt0 k1 above.
split.
- move=> K K0 N w mu hfam sym fourth n hn eps eps0.
  exact: (@finite_symmetric_quadric kappa alpha K N w mu hfam
    k1 above K0 sym fourth n hn eps eps0).
- move=> K K0 w mu hfam sym fourth n hn eps eps0.
  exact: (@countable_symmetric_quadric kappa alpha K w mu hfam
    k1 above K0 sym fourth n hn eps eps0).
Qed.
