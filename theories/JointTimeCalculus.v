From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace OperatorDefinitions
  SoftDefinitions MatrixGibbsDefinitions MatrixGibbs GradientDefinitions MatrixGradient
  SymmetricBasis QuadraticDefinitions GoeDefinitions JointDefinitions TimeDefinitions.
Import ListNotations.
Open Scope R_scope.

(* The time derivative of the joint interpolation path joint_matrix.
   - joint_matrix_normalized_path: for t >= 0, joint_matrix n C t x z is
     C + sqrt t * joint_quadratic_input n x + sqrt (1-t) * goe_matrix n z.
   - joint_matrix_time_derivative: for 0 < t < 1, the path has derivative
     joint_time_velocity n t x z in t, that is
     joint_quadratic_input n x / (2 * sqrt t) -
     goe_matrix n z / (2 * sqrt (1-t)); joint_matrix_time_is_diff states it
     as a differential (is_diff).
   - joint_time_sqrt_derivative and joint_time_complement_sqrt_derivative:
     the derivatives of sqrt t and of sqrt (1-t).
   The first three lemmas are general facts on functions of a real variable
   with values in a normed module W: is_derive in the direction 1 and
   is_diff with differential h |-> h *: l say the same thing
   (joint_time_is_diff_of_derive, joint_time_derive_of_is_diff), and
   u |-> k u *: v has derivative dk *: v when k has derivative dk
   (joint_time_derive_scale). *)

(* A derivative in the direction 1 of a function of a real variable gives
   its differential h |-> h *: l on R^o. *)
Lemma joint_time_is_diff_of_derive {W : normedModType R} (f : R -> W) (t : R) (l : W) :
  @is_derive R R^o W t 1 f l ->
  is_diff (t : R^o) (f : R^o -> W) (fun h : R^o => (h *: l)%R).
Proof.
move=> Hder.
have [Ed Hv] := Hder.
have Dd : differentiable (f : R^o -> W) t by apply/derivable1_diffP.
apply: DiffDef; first exact Dd.
rewrite diff1E // derive1E Hv; apply: funext => h /=.
reflexivity.
Qed.

(* The converse of joint_time_is_diff_of_derive. *)
Lemma joint_time_derive_of_is_diff {W : normedModType R} (f : R -> W) (t : R) (l : W) :
  is_diff (t : R^o) (f : R^o -> W) (fun h : R^o => (h *: l)%R) ->
  @is_derive R R^o W t 1 f l.
Proof.
move=> HL.
apply: DeriveDef.
  exact/diff_derivable/ex_diff.
by rewrite deriveE ?diff_val //= scale1r.
Qed.

(* The derivative of u |-> k u *: v, for a real function k with derivative
   dk at t, is dk *: v. *)
Lemma joint_time_derive_scale {W : normedModType R} (k : R -> R) (t dk : R) (v : W) :
  @is_derive R R^o R^o t 1 k dk ->
  @is_derive R R^o W t 1 (fun u : R => (k u *: v)%R) (dk *: v)%R.
Proof.
move=> Hk.
have Hd := @joint_time_is_diff_of_derive R^o k t dk Hk.
have HC := is_diff_comp Hd (is_diff_scalel (k t) v).
apply: joint_time_derive_of_is_diff.
apply: (is_diff_eq HC).
apply: funext => h /=.
by rewrite scalerA.
Qed.

Lemma joint_matrix_normalized_path n C t x z : 0 <= t ->
  joint_matrix n C t x z = matrix_add n C
    (matrix_add n (matrix_scale n (sqrt t) (joint_quadratic_input n x))
      (matrix_scale n (sqrt(1-t)) (goe_matrix n z))).
Proof.
  intro Ht; apply matrix_ext; intros i j Hi Hj.
  unfold joint_matrix, joint_quadratic_input, quadratic_matrix.
  rewrite !matrix_entry_add !matrix_entry_scale !(matrix_entry_build _ _ _ _ Hi Hj).
  have HN : 0 < INR (S n) by apply lt_0_INR; lia.
  rewrite matrix_entry_zero (sqrt_div t (INR (S n)) Ht HN).
  unfold Rdiv; ring.
Qed.

Lemma joint_time_sqrt_derivative t : 0 < t -> @is_derive R R^o R^o t 1 sqrt (/(2*sqrt t)).
Proof. intro Ht; apply is_derive_Reals, derivable_pt_lim_sqrt; exact Ht. Qed.

Lemma joint_time_complement_sqrt_derivative t : t < 1 ->
  @is_derive R R^o R^o t 1 (fun u => sqrt(1-u)) (-/(2*sqrt(1-t))).
Proof.
  intro Ht; replace (-/(2*sqrt(1-t))) with ((0-1)/(2*sqrt(1-t))) by (unfold Rdiv; ring).
  apply (is_derive_sqrt (fun u => 1 - u) t (0 - 1)); [|lra].
  apply (is_derive_minus (fun _ => 1) (fun u => u) t 0 1);
    [exact (is_derive_const 1 t)|exact (is_derive_id_R t)].
Qed.

Theorem joint_matrix_time_derivative n C t x z : 0 < t < 1 ->
  @is_derive R R^o (matrix_NormedModule n) t 1
    (fun u : R => joint_matrix n C u x z) (joint_time_velocity n t x z).
Proof.
  intros Ht.
  have Hsum : @is_derive R R^o (matrix_NormedModule n) t 1
      (fun u : R => matrix_add n C
        (matrix_add n (matrix_scale n (sqrt u) (joint_quadratic_input n x))
          (matrix_scale n (sqrt(1-u)) (goe_matrix n z))))
      (joint_time_velocity n t x z).
  { have H1 := joint_time_derive_scale sqrt t (/(2*sqrt t)) (joint_quadratic_input n x)
      (joint_time_sqrt_derivative t ltac:(lra)).
    have H2 := joint_time_derive_scale (fun u => sqrt(1-u)) t (-/(2*sqrt(1-t)))
      (goe_matrix n z) (joint_time_complement_sqrt_derivative t ltac:(lra)).
    have H12 := is_deriveD H1 H2.
    have H0 := is_deriveD (is_derive_cst (C : matrix_NormedModule n) (t : R^o) 1) H12.
    unfold joint_time_velocity, matrix_add, matrix_scale.
    rewrite -[X in is_derive _ _ _ X](add0r).
    exact H0. }
  apply: (near_eq_is_derive _ Hsum).
  apply (proj2 (nbhs_Reals t _)).
  exists (t/2); split; [lra|]; intros u Hu.
  symmetry; apply joint_matrix_normalized_path.
  apply Rabs_def2 in Hu; lra.
Qed.

(* The conclusion of joint_matrix_time_derivative as a differential on R^o,
   the form that is_diff_comp takes. *)
Lemma joint_matrix_time_is_diff n C t x z : 0 < t < 1 ->
  is_diff (t : R^o) ((fun u : R^o => joint_matrix n C u x z) : R^o -> matrix_NormedModule n)
    (fun h : R^o => (h *: joint_time_velocity n t x z)%R).
Proof.
  intro Ht.
  exact (@joint_time_is_diff_of_derive (matrix_NormedModule n) _ t _
    (joint_matrix_time_derivative n C t x z Ht)).
Qed.
