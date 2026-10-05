From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  OperatorDefinitions OperatorBounds OperatorProperties NormEquivalence
  TensorDefinitions TensorBounds SecondChaosDefinitions SecondChaosAlgebra.
From EllipsoidFitting Require Import TensorDefinitionsAux.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/SecondChaosBounds.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements change form in two ways, and keep their meaning.

   1. Norms. Coquelicot's norm x becomes MathComp's norm (`|x|)%R. On
      vector n it is still the Euclidean norm sqrt (x_0 ^ 2 + ... + x_n ^ 2),
      because the port of MatrixDefinitions nests euclidean_product of
      MatrixEuclideanProduct, which keeps Coquelicot's product norm instead
      of MathComp's max norm (analysis/README.md, difference 1). The
      constant 4 of the bounds is therefore stated against the same norm as
      in the original. Comparisons, products and powers around these norms
      are Stdlib's, as before.

   2. Extended reals. As in the ports of TensorDefinitions and TensorBounds,
      Coquelicot's Finite r becomes MathComp's r%:E, that is EFin r, in
      chaos_projective_bound. projective_operator_norm has the same value as
      in the original, as TensorDefinitions explains, so the statement means
      the same.

   The proofs keep their steps. In chaos_projective_bound, Coquelicot's
   Glb_Rbar_correct is replaced by projective_operator_norm_greatest of
   TensorDefinitionsAux, and Rbar_le of two finite values by MathComp's
   order on \bar R, which lee_fin and RleP bring back to Stdlib's Rle.
   With ssreflect loaded, the bare name eq_refl means ssreflect's lemma
   x == x, so chaos_tensor_value_bound writes Logic.eq_refl, and Stdlib's
   "rewrite A, B" and "rewrite ... by tac" are written in the forms that
   ssreflect accepts. *)

Theorem vector_inner_cauchy_schwarz n (x y : vector n) :
  Rabs (vector_inner n x y) <= (`|x|)%R * (`|y|)%R.
Proof.
  pose proof (coordinate_cauchy_schwarz_squared n (vector_entry n x) (vector_entry n y)) as H.
  rewrite -!vector_norm_squared in H.
  fold (vector_inner n x y) in H.
  pose proof (Rabs_pos (vector_inner n x y)).
  assert (Hx : 0 <= (`|x|)%R) by (apply/RleP; apply normr_ge0).
  assert (Hy : 0 <= (`|y|)%R) by (apply/RleP; apply normr_ge0).
  pose proof (Rmult_le_pos _ _ Hx Hy).
  rewrite -(vector_abs_square (vector_inner n x y)) in H; nra.
Qed.

Theorem chaos_pure_contraction_bound n (A1 A2 A3 : matrix n) (x : vector n) :
  symmetric_matrix n A1 -> symmetric_matrix n A2 -> symmetric_matrix n A3 ->
  Rabs (chaos_contraction n (fun H1 H2 H3 =>
    trace_pair n A1 H1 * trace_pair n A2 H2 * trace_pair n A3 H3) x) <=
  4 * (`|x|)%R ^ 2 * matrix_operator_norm n A1 * matrix_operator_norm n A2 *
    matrix_operator_norm n A3.
Proof.
  intros H1 H2 H3; rewrite (chaos_pure_contraction_inner n A1 A2 A3 x H1 H2 H3).
  rewrite Rabs_mult (Rabs_pos_eq 4 ltac:(lra)).
  replace (4 * (`|x|)%R ^ 2 * matrix_operator_norm n A1 * matrix_operator_norm n A2 *
    matrix_operator_norm n A3) with
    (4 * ((matrix_operator_norm n A1 * (`|x|)%R) *
      (matrix_operator_norm n A3 * (matrix_operator_norm n A2 * (`|x|)%R)))) by ring.
  apply Rmult_le_compat_l; [lra|].
  eapply Rle_trans; [apply vector_inner_cauchy_schwarz|].
  apply Rmult_le_compat; try (apply/RleP; apply normr_ge0).
  - apply matrix_action_norm_bound.
  - eapply Rle_trans; [apply matrix_action_norm_bound|].
    apply Rmult_le_compat_l; [apply matrix_operator_norm_nonnegative|apply matrix_action_norm_bound].
Qed.

Lemma chaos_contraction_ext n (T S : matrix n -> matrix n -> matrix n -> R) (x : vector n) :
  (forall U V W, symmetric_matrix n U -> symmetric_matrix n V -> symmetric_matrix n W ->
    T U V W = S U V W) ->
  chaos_contraction n T x = chaos_contraction n S x.
Proof.
  intros H; unfold chaos_contraction; f_equal.
  apply coordinate_sum_ext; intros a Ha; apply coordinate_sum_ext; intros b Hb.
  apply H; try apply chaos_first_symmetric; apply chaos_second_symmetric.
Qed.

Lemma chaos_contraction_zero n (x : vector n) :
  chaos_contraction n (fun _ _ _ => 0) x = 0.
Proof.
  assert (HZ : coordinate_sum n (fun _ => 0) = 0).
  { rewrite normeq_coordinate_sum_const; ring. }
  unfold chaos_contraction; rewrite HZ HZ; ring.
Qed.

Lemma chaos_contraction_scale n c (T : matrix n -> matrix n -> matrix n -> R) (x : vector n) :
  chaos_contraction n (fun U V W => c * T U V W) x = c * chaos_contraction n T x.
Proof.
  unfold chaos_contraction.
  transitivity (/ 2 * coordinate_sum n (fun a => c * coordinate_sum n
    (fun b => T (chaos_first n x a) (chaos_first n x b) (chaos_second n a b)))).
  - f_equal; apply coordinate_sum_ext; intros; apply normeq_coordinate_sum_scale.
  - rewrite normeq_coordinate_sum_scale; ring.
Qed.

Lemma chaos_contraction_add n (T S : matrix n -> matrix n -> matrix n -> R) (x : vector n) :
  chaos_contraction n (fun U V W => T U V W + S U V W) x =
    chaos_contraction n T x + chaos_contraction n S x.
Proof.
  unfold chaos_contraction.
  transitivity (/ 2 * coordinate_sum n (fun a =>
    coordinate_sum n (fun b => T (chaos_first n x a) (chaos_first n x b) (chaos_second n a b)) +
    coordinate_sum n (fun b => S (chaos_first n x a) (chaos_first n x b) (chaos_second n a b)))).
  - f_equal; apply coordinate_sum_ext; intros; apply normeq_coordinate_sum_add.
  - rewrite normeq_coordinate_sum_add; ring.
Qed.

Theorem chaos_atom_contraction_bound n (a : trace_atom n) (x : vector n) :
  symmetric_atom a ->
  Rabs (chaos_contraction n (atom_value a) x) <= 4 * (`|x|)%R ^ 2 * atom_cost a.
Proof.
  intros [H1 [H2 H3]].
  assert (HE : chaos_contraction n (atom_value a) x =
    atom_coefficient a * chaos_contraction n (fun U V W =>
      trace_pair n (atom_first a) U * trace_pair n (atom_second a) V *
      trace_pair n (atom_third a) W) x).
  { rewrite -chaos_contraction_scale; apply chaos_contraction_ext.
    intros; unfold atom_value; ring. }
  rewrite HE Rabs_mult.
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [apply Rabs_pos|apply chaos_pure_contraction_bound; assumption].
  - unfold atom_cost; right; ring.
Qed.

Theorem chaos_tensor_value_bound n (atoms : list (trace_atom n)) (x : vector n) :
  (forall a, In a atoms -> symmetric_atom a) ->
  Rabs (chaos_contraction n (tensor_value atoms) x) <= 4 * (`|x|)%R ^ 2 * tensor_cost atoms.
Proof.
  induction atoms as [|a atoms IH]; intros HS.
  - change (Rabs (chaos_contraction n (fun _ _ _ => 0) x) <= 4 * (`|x|)%R ^ 2 * 0).
    rewrite chaos_contraction_zero Rabs_R0; nra.
  - change (Rabs (chaos_contraction n (fun U V W => atom_value a U V W +
      tensor_value atoms U V W) x) <= 4 * (`|x|)%R ^ 2 * (atom_cost a + tensor_cost atoms)).
    rewrite chaos_contraction_add.
    eapply Rle_trans; [apply Rabs_triang|].
    pose proof (chaos_atom_contraction_bound n a x (HS a (or_introl Logic.eq_refl))) as HA.
    assert (HR : forall b, In b atoms -> symmetric_atom b).
    { intros b Hb; apply HS; right; exact Hb. }
    specialize (IH HR); nra.
Qed.

Theorem chaos_representation_bound n (T : matrix n -> matrix n -> matrix n -> R)
    (atoms : list (trace_atom n)) (x : vector n) :
  tensor_represents T atoms ->
  Rabs (chaos_contraction n T x) <= 4 * (`|x|)%R ^ 2 * tensor_cost atoms.
Proof.
  intros [HS HE]; rewrite (chaos_contraction_ext n T (tensor_value atoms) x HE).
  apply chaos_tensor_value_bound; exact HS.
Qed.

Theorem chaos_projective_bound n (T : matrix n -> matrix n -> matrix n -> R)
    (atoms : list (trace_atom n)) (x : vector n) :
  tensor_represents T atoms ->
  exists r : R, projective_operator_norm T = r%:E /\ 0 <= r /\
    Rabs (chaos_contraction n T x) <= 4 * (`|x|)%R ^ 2 * r.
Proof.
  intros HR.
  destruct (projective_operator_norm_finite n T atoms HR) as [r [HE [Hr HC]]].
  exists r; split; [exact HE|]; split; [exact Hr|].
  set (C := 4 * (`|x|)%R ^ 2).
  assert (HC0 : 0 <= C) by (unfold C; pose proof (pow2_ge_0 (`|x|)%R); nra).
  destruct (Req_dec C 0) as [HCz|HCz].
  - pose proof (chaos_representation_bound n T atoms x HR) as HB.
    fold C in HB; change (Rabs (chaos_contraction n T x) <= C * r).
    rewrite HCz in HB |- *; nra.
  - assert (HCp : 0 < C) by lra.
    set (q := Rabs (chaos_contraction n T x) / C).
    assert (HL : (q%:E <= projective_operator_norm T)%E).
    { apply projective_operator_norm_greatest.
      intros c [representation [Hrep ->]]; rewrite lee_fin; apply/RleP.
      apply (Rmult_le_reg_r C); [exact HCp|].
      unfold q; replace (Rabs (chaos_contraction n T x) / C * C) with
        (Rabs (chaos_contraction n T x)) by (field; exact HCz).
      pose proof (chaos_representation_bound n T representation x Hrep) as HB.
      fold C in HB; nra. }
    rewrite HE lee_fin in HL; move/RleP: HL => HL.
    change (Rabs (chaos_contraction n T x) <= C * r).
    apply (Rmult_le_reg_r (/ C)); [apply Rinv_0_lt_compat; exact HCp|].
    replace (C * r * / C) with r by (field; exact HCz).
    exact HL.
Qed.
