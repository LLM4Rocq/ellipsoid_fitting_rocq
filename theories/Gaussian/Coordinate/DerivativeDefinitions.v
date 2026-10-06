From Stdlib Require Import Reals List.
From mathcomp Require Import ssralg ssrnum Rstruct normedtype derive.
From EllipsoidFitting Require Import Analysis.CoordinatePermutationDefinitions.
Open Scope R_scope.

(* Partial derivatives of functions of a list of coordinates.
   finite_coordinate_derivative d i F DF says that DF is the derivative of
   F in coordinate i at every list xs of length d: the function
   t |-> F (replace_coordinate i t xs) has derivative DF xs at
   t = nth i xs 0. The derivative is MathComp's is_derive in the direction
   1, on R^o (R with its own normed module structure); it is the ordinary
   derivative, equivalent to Stdlib's derivable_pt_lim
   (Analysis.CalculusBridge.is_derive_Reals). The names List.nth and List.length are
   written in full because MathComp's seq.nth takes its arguments in
   another order. *)
Definition finite_coordinate_derivative d i (F DF : list R -> R) : Prop :=
  forall xs, List.length xs = d ->
  @is_derive R R^o R^o (List.nth i xs 0) 1%R
    (fun t => F (replace_coordinate i t xs)) (DF xs).
