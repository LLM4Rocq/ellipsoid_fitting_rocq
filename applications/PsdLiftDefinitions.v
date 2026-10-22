From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix reals.
From GaussianAnalysis.matrix Require Import psd_part.
From GaussianApplications Require Import PsdRankDefinitions.

(**md**************************************************************************)
(* # PSD rank of matching matrices: the definitions of the corollary          *)
(*                                                                            *)
(* The corollary of phase 14 (AGENTS.md, section Phase 14, target T14, batch  *)
(* 1; the plan notes/phase14-plan.md, section 2). The definitions of the      *)
(* statement of PsdLiftStatement.v, from 'Exponential PSD rank of positively  *)
(* shifted matching matrices' (family 126 of the OpenAI math collection,      *)
(* revision 1581d4cbd, source/sections/introduction.tex, lines 56-80, the     *)
(* corollary 'Unshifted rank and exact lifts'). The other objects of the      *)
(* statement are those of PsdRankDefinitions.v: K_n, its perfect matchings,   *)
(* the odd sets, crossing U M = |M cap delta(U)| and A_n(rho). The Lean model *)
(* of the collection has the same notions:                                    *)
(* Lean: Row, slack (Model.lean, lines 17-33)                                 *)
(* Lean: matchingPoint, matchingPolytope, HasAffineLift (AffineModel.lean)    *)
(*                                                                            *)
(* For a natural number n, the vertices are 'I_n.                             *)
(* - kn_edges n is the finite type of the edges of K_n, the manuscript's E_n. *)
(* - matching_slack_mx is the matrix T_n(0): its rows are the edges and the   *)
(*   odd sets, its columns the perfect matchings; the row of an edge e is     *)
(*   1_(e in M), and the row of an odd set U is |M cap delta(U)| - 1, the row *)
(*   of A_n(0).                                                               *)
(* - in_matching_polytope x: x in R^(E_n) is a convex combination of the      *)
(*   indicator vectors 1_M of the perfect matchings, that is x lies in the    *)
(*   perfect matching polytope P_n = conv {1_M}.                              *)
(* - semidefinite_lift R n r: an exact semidefinite lift of P_n of size r.    *)
(*   There are finitely many matrices C l of 'M[R]_r with reals c l, and      *)
(*   matrices D e with reals d0 e for the edges, such that the points of P_n  *)
(*   are exactly the images (tr (D e X) + d0 e)_e of the positive             *)
(*   semidefinite X in 'M[R]_r with tr (C l X) = c l for every l.             *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - kn_edges was defined in PsdRank/Model.v in phase 13 (not frozen); it     *)
(*   moves here because the statement uses it, and Model.v imports this file. *)
(* - The rows of T_n(0) are indexed by the sum type of the edges and the odd  *)
(*   sets, as the Lean model's Row; the edge rows are inl e and the odd-set   *)
(*   rows inr U. Each edge row is 1 at the matchings that contain the edge.   *)
(* - The polytope is described by its points: x is in P_n when it is a        *)
(*   convex combination of the 1_M, which for a finite set of points is       *)
(*   membership in the convex hull. No inequality description is used, so     *)
(*   Edmonds' theorem is not part of the statement.                           *)
(* - A lift is written with traces. The manuscript's L is an affine subspace  *)
(*   of the real symmetric r x r matrices and the map to R^(E_n) is affine.   *)
(*   psdmx X includes the symmetry of X (library/matrix/psd_part.v), every    *)
(*   affine subspace of the symmetric matrices is cut out by finitely many    *)
(*   equations tr (C l X) = c l, and every affine map from them to R^(E_n)    *)
(*   has the form X |-> (tr (D e X) + d0 e)_e, so the two notions agree. The  *)
(*   lift is exact: the image of the section is P_n itself.                   *)
(* - The definitions take every n, R and r; the statement restricts n to      *)
(*   large even values, as the manuscript's corollary does (the manuscript    *)
(*   defines these objects for even n >= 4).                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*             kn_edges n == the edges of K_n, as a finite type               *)
(*    matching_slack_mx i M == T_n(0)_(i,M): 1_(e in M) for an edge row       *)
(*                           inl e, |M cap delta(U)| - 1 for an odd-set row   *)
(*                           inr U                                            *)
(* in_matching_polytope x == x is a convex combination of the 1_M             *)
(* semidefinite_lift R n r == P_n has an exact semidefinite lift of size r    *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section lift_definitions.
Variable n : nat.

(* The edges of K_n, as a finite type. *)
Definition kn_edges := {e : {set 'I_n} | kn_edge e}.

(* T_n(0): the edge rows 1_(e in M), then the odd-set rows of A_n(0),
   |M cap delta(U)| - 1. *)
Definition matching_slack_mx (R : realType)
    (i : (kn_edges + odd_set n)%type) (M : perfect_matching n) : R :=
  match i with
  | inl e => (val e \in val M)%:R
  | inr U => (crossing U M)%:R - 1
  end.

End lift_definitions.

Section lift.
Variables (R : realType) (n : nat).

(* x is in the perfect matching polytope: a convex combination of the
   indicator vectors of the perfect matchings. *)
Definition in_matching_polytope (x : {ffun kn_edges n -> R}) : Prop :=
  exists w : perfect_matching n -> R,
    [/\ forall M, 0 <= w M, \sum_M w M = 1 &
        forall e, x e = \sum_M w M * (val e \in val M)%:R].

(* An exact semidefinite lift of size r: the affine section
   {X psd : tr (C l X) = c l for every l} maps onto the polytope by
   X |-> (tr (D e X) + d0 e)_e. *)
Definition semidefinite_lift (r : nat) : Prop :=
  exists (m : nat) (C : 'I_m -> 'M[R]_r) (c : 'I_m -> R)
         (D : kn_edges n -> 'M[R]_r) (d0 : kn_edges n -> R),
  forall x : {ffun kn_edges n -> R},
    in_matching_polytope x <->
    exists X : 'M[R]_r,
      [/\ psdmx X, forall l, \tr (C l *m X) = c l &
          x = [ffun e => \tr (D e *m X) + d0 e]].

End lift.
