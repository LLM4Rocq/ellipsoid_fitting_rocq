From Stdlib Require Import Reals List.
From mathcomp Require Import ssralg ssrnum Rstruct normedtype derive.
From EllipsoidFitting Require Import GaussianCoordinatePermutationDefinitions.
Open Scope R_scope.

(* The derivative of F in coordinate i, at every list of length d, is DF.
   The original used Coquelicot's is_derive on R. Here it is MathComp's
   is_derive at the point nth i xs 0 in the direction 1, on R^o (R with its
   own normed module structure). Both are the ordinary derivative: each is
   equivalent to Stdlib's derivable_pt_lim, so the meaning is unchanged.
   The names List.nth and List.length are written in full because
   MathComp's seq.nth takes its arguments in another order. *)
Definition finite_coordinate_derivative d i (F DF : list R -> R) : Prop :=
  forall xs, List.length xs = d ->
  @is_derive R R^o R^o (List.nth i xs 0) 1%R
    (fun t => F (replace_coordinate i t xs)) (DF xs).
