(* Time calculus of the row velocities along the simultaneous path
   Z(t) = gaussian_row_array n m t xs, pointwise in the coordinate list xs,
   for 0 < t < 1, beta, gamma > 0 and nonempty Y and S.
   - mexp_first_along: t |-> lower_block_first (Z(t)) U has derivative
     lower_block_second (Z(t)) U (dZ/dt), where dZ/dt is
     gaussian_array_velocity.
   - mexp_row_acceleration and mexp_row_velocity_derivative: the time
     derivative of the row velocity gaussian_row_velocity, including the
     terms of the other rows through Z(t).
   - mexp_velocity_sum_derivative: the derivative of a finite sum of row
     velocities is the sum of the row accelerations. *)
From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions Soft.Definitions
  Soft.MinimaxDerivativeDefinitions Soft.MinimaxFrechet Goe.Definitions
  Joint.Definitions Joint.TimeVelocity Row.ArrayDefinitions
  Matrix.BlockInjection Row.ObservableDefinitions Multirow.ArrayTimeDefinitions
  Multirow.ArrayTimeCalculus.
From EllipsoidFitting Require Analysis.CalculusBridge
  Joint.CoefficientSecondDerivatives.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

Lemma mexp_first_along n m beta gamma y B Y S (U : block_array n m) t xs :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 < t < 1 ->
  @is_derive R R^o R^o t 1
    (fun u => lower_block_first n m beta gamma y B Y S (gaussian_row_array n m u xs) U)
    (lower_block_second n m beta gamma y B Y S (gaussian_row_array n m t xs) U
      (gaussian_array_velocity n m t xs)).
Proof.
  intros Hb Hg HY HS Ht.
  have HF := proj2 (lower_block_derivatives n m beta gamma y B Y S Hb Hg HY HS
    (gaussian_row_array n m t xs)) U.
  have HC := is_diff_comp (row_time_array_is_diff n m t xs Ht) HF.
  apply: DeriveDef.
    exact/diff_derivable/ex_diff.
  rewrite deriveE ?diff_val //= scale1r; reflexivity.
Qed.

Definition mexp_row_acceleration n m beta gamma y B Y S t i (xs : list R) : R :=
  let A := gaussian_row_array n m t xs in
  let V := gaussian_array_velocity n m t xs in
  let W := block_inject n m i (joint_quadratic_input n (fst (gaussian_row_pair n i xs))) in
  let G := block_inject n m i (goe_matrix n (snd (gaussian_row_pair n i xs))) in
  lower_block_second n m beta gamma y B Y S A W V * /(2*sqrt t) +
  lower_block_first n m beta gamma y B Y S A W * (-/(4*t*sqrt t)) +
  (lower_block_second n m beta gamma y B Y S A G V * (-/(2*sqrt(1-t))) +
   lower_block_first n m beta gamma y B Y S A G * (-/(4*(1-t)*sqrt(1-t)))).

Lemma mexp_row_velocity_derivative n m beta gamma y B Y S t i xs :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 < t < 1 ->
  @is_derive R R^o R^o t 1 (fun u => gaussian_row_velocity n m beta gamma y B Y S u i xs)
    (mexp_row_acceleration n m beta gamma y B Y S t i xs).
Proof.
  intros Hb Hg HY HS Ht.
  set W := block_inject n m i (joint_quadratic_input n (fst (gaussian_row_pair n i xs))).
  set G := block_inject n m i (goe_matrix n (snd (gaussian_row_pair n i xs))).
  set LW := fun u => lower_block_first n m beta gamma y B Y S (gaussian_row_array n m u xs) W.
  set LG := fun u => lower_block_first n m beta gamma y B Y S (gaussian_row_array n m u xs) G.
  apply (proj2 (Analysis.CalculusBridge.is_derive_Reals _ _ _)).
  have HW := proj1 (Analysis.CalculusBridge.is_derive_Reals _ _ _) (mexp_first_along n m beta gamma y B Y S W t xs Hb Hg HY HS Ht).
  have HG := proj1 (Analysis.CalculusBridge.is_derive_Reals _ _ _) (mexp_first_along n m beta gamma y B Y S G t xs Hb Hg HY HS Ht).
  have Ha := proj1 (Analysis.CalculusBridge.is_derive_Reals _ _ _) (Joint.CoefficientSecondDerivatives.joint_time_inverse_sqrt_derivative t (proj1 Ht)).
  have Hc := proj1 (Analysis.CalculusBridge.is_derive_Reals _ _ _) (Joint.CoefficientSecondDerivatives.joint_time_inverse_complement_derivative t (proj2 Ht)).
  have E : (fun u => gaussian_row_velocity n m beta gamma y B Y S u i xs) =
    (fun u => LW u * /(2*sqrt u) + LG u * (-/(2*sqrt(1-u)))).
  { apply: funext => u; rewrite /gaussian_row_velocity /LW /LG /W /G /block_inject /=.
    unfold Rdiv; ring. }
  rewrite E; clear E.
  have HD := derivable_pt_lim_plus _ _ _ _ _
    (derivable_pt_lim_mult _ _ _ _ _ HW Ha) (derivable_pt_lim_mult _ _ _ _ _ HG Hc).
  unfold mexp_row_acceleration; cbv zeta; fold W G.
  refine (eq_ind _ (fun l => derivable_pt_lim _ t l) HD _ _).
  rewrite /LW /LG /=; ring.
Qed.

Lemma mexp_velocity_sum_derivative n m beta gamma y B Y S t xs (I : list nat) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 < t < 1 ->
  @is_derive R R^o R^o t 1
    (fun u => finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S u i xs) I)
    (finite_sum (fun i => mexp_row_acceleration n m beta gamma y B Y S t i xs) I).
Proof.
  intros Hb Hg HY HS Ht.
  apply (proj2 (Analysis.CalculusBridge.is_derive_Reals _ _ _)).
  induction I as [|i I IH]; simpl.
  - exact (derivable_pt_lim_const 0 t).
  - apply (derivable_pt_lim_plus
      (fun u => gaussian_row_velocity n m beta gamma y B Y S u i xs)
      (fun u => finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S u i xs) I)).
    + exact (proj1 (Analysis.CalculusBridge.is_derive_Reals _ _ _)
        (mexp_row_velocity_derivative n m beta gamma y B Y S t i xs Hb Hg HY HS Ht)).
    + exact IH.
Qed.
