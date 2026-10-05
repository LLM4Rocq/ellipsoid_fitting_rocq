From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions
  TensorDefinitions SecondChaosDefinitions
  GaussianCoordinatePermutationDefinitions
  GaussianCoordinateDerivativeDefinitions VectorCoordinateDefinitions
  VectorCoordinates.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module VectorCoordinateCalculus of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/GaussianVectorProofs.v), extracted to
   build/agent2/unbundled/VectorCoordinateCalculus.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   Every lemma and theorem keeps its name, its arguments in the same order
   and its hypotheses. One lemma is added, vector_coordinate_line_is_diff,
   which the proofs share. The vectors are those of the ported
   OperatorDefinitions: nested euclidean_product of R^o, with the Euclidean
   norm, whose topology is the product topology. The statements change form
   in the following ways, without a change of meaning.

   1. Derivatives of a function of a real variable. Coquelicot's
      is_derive g t l, for g : R -> V, becomes MathComp's
      @is_derive R R^o V t 1 g l: g is derivable at t in the direction 1
      and its derivative there is l. Both say that (g (t + h) - g t) / h
      tends to l as h tends to 0. For V = R the codomain is R^o, the normed
      module view of R, as in GaussianCoordinateDerivativeDefinitions. This
      concerns vector_coordinate_line_derive (V = vector n),
      vector_frechet_coordinate_line and vector_frechet_coordinate_section
      (V = R^o).

   2. Frechet derivatives. Coquelicot's filterdiff F (locally x) dF becomes
      is_diff x (F : vector n -> R^o) dF of MathComp-Analysis, the form of
      the restated challenge ellipsoid_gaussian_matrix (README difference 2):
      F is differentiable at x and its differential 'd F x is dF. Both say
      that dF is linear and continuous and that F (x + h) = F x + dF h +
      o (h). The cast to R^o gives the real line its normed module
      structure; R^o is R by definition, so F and dF are unchanged. This
      concerns vector_frechet_coordinate_line,
      vector_frechet_coordinate_section and
      vector_frechet_coordinate_derivative.

   3. Vector operations. Coquelicot's plus x (scal c v) becomes MathComp's
      (x + c *: v)%R on vector n, componentwise as before. Inside %R the
      scalar u - a is parsed with MathComp's subtraction on R. It is
      Stdlib's Rminus u a up to conversion (Rstruct's RminusE is proved by
      reflexivity), so the line is the one of the original. It is also the
      form of the right-hand side of vector_of_list_replace_line in the
      ported VectorCoordinates, so the proof of
      vector_frechet_coordinate_section rewrites with that lemma as before.

   4. Indices and lists. (i <= n)%nat becomes (i <= n)%coq_nat, Stdlib's
      Peano order, and nth becomes List.nth, Stdlib's nth, as in the ported
      VectorCoordinates, because with ssreflect loaded the bare notations
      would mean ssrnat's leq and seq.nth.

   The proofs follow the scheme of scalar_frechet_line in the ported
   MatrixFrechetUnique. Coquelicot's is_derive_minus, is_derive_scal_l and
   is_derive_plus, which gave the derivative of the line, become the
   differential of the affine map u |-> x + (u - a) *: e, obtained from
   is_diff_cst, is_diff_scalel and is_diffD. Coquelicot's filterdiff_comp'
   becomes is_diff_comp, filterdiff_ext_lin becomes the computation of the
   derivative through deriveE and diff_val, and is_derive_ext becomes a
   rewrite of the function with funext. The original also imported
   FunctionalExtensionality; boolp.funext takes its place. *)

(* Added for the proofs below: the differential of the affine line
   u |-> x + (u - a) *: e is h |-> h *: e, at every point. *)
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
