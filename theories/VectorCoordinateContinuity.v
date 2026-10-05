From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions
  VectorCoordinateDefinitions VectorCoordinates GaussianCoordinateDefinitions
  GaussianCoordinateBasics.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module VectorCoordinateContinuity of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/GaussianVectorProofs.v), extracted to
   build/agent2/unbundled/VectorCoordinateContinuity.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   Every lemma and theorem keeps its name and its arguments in the same
   order. No item is added. The original imported the bundle
   GaussianCoordinateProofs and named its inner modules
   GaussianCoordinateBasics and GaussianCoordinateTopology. This port imports
   the standalone module GaussianCoordinateBasics, the only one whose lemmas
   it uses (coordinates_close_iff). It does not import Coquelicot's
   Compactness: Tn and close_n come from the ported
   GaussianCoordinateDefinitions, where they are copies of Coquelicot's.

   Two statements change meaning, because the ball on vectors changed.

   1. vector_ball_coordinates. In Coquelicot a vector n is a nested
      prod_NormedModule, whose ball is the conjunction of the balls of the
      components, so ball x e y held exactly when every coordinate of y is
      within e of the same coordinate of x. The port of MatrixDefinitions
      keeps Coquelicot's Euclidean norm on vectors but gives them the norm
      ball, ball x e y <-> `|x - y| < e (README difference 1, and the notes
      of the port of MatrixDefinitions). The equivalence of the original is
      then false: for n = 1, x = (0, 0), y = (e / 2 + e / 4, e / 2 + e / 4)
      has both coordinates within e of x but lies at distance
      (3 / 4) sqrt 2 e > e. The port states the two true halves, as a
      conjunction:
      - a ball of radius e gives coordinates within e, since each coordinate
        of y - x is at most the Euclidean norm of y - x;
      - coordinates within e give a ball of radius INR (S n) * e, since the
        norm of y - x is at most the sum of the S n coordinates.
      The radius is written Rmult (INR (S n)) e, Stdlib's product, because
      the radius argument of MathComp's ball is read in ring_scope, where *
      would be MathComp's product. The two are equal by conversion.

   2. vector_of_coordinates_ball. For the same reason, closeness of the
      coordinate lists within e gives a ball of radius INR (S n) * e
      instead of e.

   The two statements serve what the original served. The only user of
   vector_of_coordinates_ball is vector_continuous_joint, whose proof now
   divides the radius of continuity by INR (S n). The only other user of
   vector_ball_coordinates in theories/ is joint_of_coordinates_ball of
   JointCoordinates (in JointProofs and InterpolationProofs), which uses
   the direction from coordinates to balls. Its conclusion is a ball on the
   joint vectors, which becomes a norm ball of euclidean_product in the port
   of JointDefinitions, so that lemma has to be restated with a larger
   radius too; the second half here, with euclidean_product_ball_add of
   MatrixEuclideanProduct, gives it with radius INR (S m) * e + INR (S n) * e.

   The third statement keeps its meaning.

   3. vector_continuous_joint. Coquelicot's forall x, continuous f x becomes
      forall x, {for x, continuous f}, continuity at every point x
      (README difference 5), the form of the restated challenge
      ellipsoid_gaussian_matrix. The topology of vector n is the one of its
      Euclidean norm, which is the product topology, as in Coquelicot, and
      the topology of R is the usual one (Rstruct_topology).
      finite_joint_continuous has the text of the original in the ported
      GaussianCoordinateDefinitions.

   Indices are written (i <= n)%coq_nat, Stdlib's Peano order, as in the
   ported VectorCoordinates, because with ssreflect loaded (i <= n)%nat
   would mean ssrnat's leq. *)

Lemma vector_ball_coordinates n (x y : vector n) e :
  (ball x e y -> forall i, (i <= n)%coq_nat ->
    Rabs (vector_entry n y i - vector_entry n x i) < e) /\
  ((forall i, (i <= n)%coq_nat ->
    Rabs (vector_entry n y i - vector_entry n x i) < e) ->
   ball x (Rmult (INR (S n)) e) y).
Proof.
  revert x y e; induction n as [|n IH]; intros x y e.
  - (* vector 0 is R^o, whose ball is the ball of the absolute value. *)
    assert (Hb : forall r : R, ball x r y <-> Rabs (y - x) < r).
    { intro r; rewrite -ball_normE /ball_ /=; split.
      - move=> /RltP H.
        change (Rabs (x - y) < r) in H.
        rewrite Rabs_minus_sym; exact H.
      - intro H; apply/RltP.
        change (Rabs (x - y) < r).
        rewrite Rabs_minus_sym; exact H. }
    split.
    + intros H i Hi; assert (i = O) by lia; subst i.
      exact (proj1 (Hb e) H).
    + intro H; apply (proj2 (Hb (Rmult (INR 1) e))).
      change (INR 1) with 1; rewrite Rmult_1_l.
      exact (H O (Nat.le_refl O)).
  - destruct x as [x xs], y as [y ys].
    split.
    + intros H [|i] Hi.
      * have [H0 _] := euclidean_product_ball_components H.
        simpl in H0; revert H0.
        rewrite -ball_normE /ball_ /= => /RltP H0.
        change (Rabs (x - y) < e) in H0.
        change (Rabs (y - x) < e).
        rewrite Rabs_minus_sym; exact H0.
      * have [_ Hs] := euclidean_product_ball_components H.
        simpl in Hs.
        exact (proj1 (IH xs ys e) Hs i ltac:(lia)).
    + intro H.
      assert (H0 : ball (x : R^o) e (y : R^o)).
      { rewrite -ball_normE /ball_ /=; apply/RltP.
        change (Rabs (x - y) < e).
        rewrite Rabs_minus_sym; exact (H O ltac:(lia)). }
      assert (Hs : ball xs (Rmult (INR (S n)) e) ys).
      { apply (proj2 (IH xs ys e)); intros i Hi.
        exact (H (S i) ltac:(lia)). }
      have HB := @euclidean_product_ball_add R^o (tuple_NormedModule R^o n)
        (x, xs) e (Rmult (INR (S n)) e) (y, ys) H0 Hs.
      replace (Rmult (INR (S (S n))) e) with (e + Rmult (INR (S n)) e)%R.
      * exact HB.
      * change (e + INR (S n) * e = INR (S (S n)) * e).
        rewrite (S_INR (S n)); ring.
Qed.

Lemma vector_of_coordinates_ball n (z w : Tn (S n) R) e :
  close_n (S n) e w z ->
  ball (vector_of_list n (coordinates_to_list (S n) z)) (Rmult (INR (S n)) e)
    (vector_of_list n (coordinates_to_list (S n) w)).
Proof.
  intro H; apply (proj2 (vector_ball_coordinates n _ _ e)); intros i Hi.
  rewrite (vector_entry_of_list n _ i Hi) (vector_entry_of_list n _ i Hi).
  exact (proj1 (coordinates_close_iff (S n) e w z) H i ltac:(lia)).
Qed.

Theorem vector_continuous_joint n (f : vector n -> R) :
  (forall x, {for x, continuous f}) ->
  finite_joint_continuous (S n) (fun xs => f (vector_of_list n xs)).
Proof.
  intros HC z eps.
  set x0 := vector_of_list n (coordinates_to_list (S n) z).
  assert (Hout : nbhs (f x0) (fun r : R => Rabs (r - f x0) < eps)).
  { apply/nbhs_ballP; exists (pos eps); [apply/RltP; exact (cond_pos eps)|].
    intros r Hr0.
    have /RltP Hr : is_true (`|f x0 - r| < pos eps)%R by exact Hr0.
    change (Rabs (f x0 - r) < eps) in Hr.
    rewrite Rabs_minus_sym; exact Hr. }
  have /nbhs_ballP [delta delta0 Hd] := HC x0 _ Hout.
  have Hdelta : 0 < delta by apply/RltP.
  have HS : 0 < INR (S n) by apply lt_0_INR; lia.
  exists (mkposreal (delta / INR (S n)) (Rdiv_lt_0_compat _ _ Hdelta HS)).
  intros w Hw; simpl in Hw.
  apply (Hd (vector_of_list n (coordinates_to_list (S n) w))).
  have HB := vector_of_coordinates_ball n z w _ Hw.
  replace delta with (Rmult (INR (S n)) (delta / INR (S n))).
  - exact HB.
  - field; lra.
Qed.
