From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Tensor.Definitions Chaos.SecondOrderDefinitions
  Analysis.CoordinatePermutationDefinitions
  Gaussian.CoordinateDerivativeDefinitions Matrix.VectorListDefinitions
  Matrix.VectorCoordinates.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Partial derivatives of a Frechet differentiable function F on vector n,
   the vectors with S n coordinates and the Euclidean norm. Let e_i be the
   basis vector chaos_basis n i.
   - vector_frechet_coordinate_line: if F has differential dF at x
     (is_diff), then t |-> F (x + (t - a) e_i) has derivative dF e_i at a.
   - vector_frechet_coordinate_section: the same when coordinate i of a
     list xs of length S n varies, the vector being vector_of_list n xs.
   - vector_frechet_coordinate_derivative: if F is differentiable at every
     point, then xs |-> F (vector_of_list n xs) has the partial derivative
     dF (vector_of_list n xs) e_i in coordinate i
     (finite_coordinate_derivative). *)

(* The differential of the affine line u |-> x + (u - a) *: e is
   h |-> h *: e, at every point. *)
Lemma vector_coordinate_line_is_diff n (x e : vector n) (a t : R) :
  is_diff (t : R^o)
    (fun u : R^o => (x + (u - a) *: e)%R : vector_NormedModule n)
    (fun h : R^o => (h *: e)%R).
Proof.
  have -> : (fun u : R^o => (x + (u - a) *: e)%R : vector_NormedModule n) =
      (cst (x - a *: e) + ( *:%R^~ e))%R.
    by apply/funext => u /=; rewrite scalerBl addrA addrAC.
  apply: (is_diff_eq (is_diffD (is_diff_cst (x - a *: e)%R (t : R^o))
    (is_diff_scalel t e))).
  by apply/funext => h /=; rewrite add0r.
Qed.

Lemma vector_frechet_coordinate_line n (F dF : vector n -> R) (x : vector n) i
    (a : R) :
  is_diff x (F : vector n -> R^o) dF ->
  @is_derive R R^o R^o a 1%R
    (fun t : R => F (x + (t - a) *: chaos_basis n i)%R)
    (dF (chaos_basis n i)).
Proof.
  move=> HF.
  have HL := vector_coordinate_line_is_diff n x (chaos_basis n i) a a.
  have Hcenter : (x + (a - a) *: chaos_basis n i)%R = x
    by rewrite subrr scale0r addr0.
  have HD : is_diff (x + (a - a) *: chaos_basis n i)%R
      (F : vector_NormedModule n -> R^o) dF
    by rewrite Hcenter.
  have HC := is_diff_comp HL HD.
  apply: DeriveDef.
    exact/diff_derivable/ex_diff.
  by rewrite deriveE ?diff_val //= scale1r.
Qed.

Lemma vector_frechet_coordinate_section n i (F dF : vector n -> R) xs :
  length xs = S n -> (i <= n)%coq_nat ->
  is_diff (vector_of_list n xs) (F : vector n -> R^o) dF ->
  @is_derive R R^o R^o (List.nth i xs 0) 1%R
    (fun t : R => F (vector_of_list n (replace_coordinate i t xs)))
    (dF (chaos_basis n i)).
Proof.
  move=> Hxs Hi HF.
  have -> : (fun t : R => F (vector_of_list n (replace_coordinate i t xs))) =
      (fun t : R =>
        F (vector_of_list n xs + (t - List.nth i xs 0) *: chaos_basis n i)%R).
    by apply/funext => t; rewrite (vector_of_list_replace_line n xs i t Hxs Hi).
  exact: (vector_frechet_coordinate_line n F dF (vector_of_list n xs) i
    (List.nth i xs 0) HF).
Qed.

Theorem vector_frechet_coordinate_derivative n i (F : vector n -> R)
    (dF : vector n -> vector n -> R) :
  (i <= n)%coq_nat -> (forall x, is_diff x (F : vector n -> R^o) (dF x)) ->
  finite_coordinate_derivative (S n) i
    (fun xs => F (vector_of_list n xs))
    (fun xs => dF (vector_of_list n xs) (chaos_basis n i)).
Proof.
  intros Hi HF xs Hxs.
  apply vector_frechet_coordinate_section; [exact Hxs|exact Hi|apply HF].
Qed.
