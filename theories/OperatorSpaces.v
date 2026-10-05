From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorBounds
  CoefficientDefinitions CoefficientMaps CoefficientBounds
  NormedTransport OperatorSpaceDefinitions OperatorRepresentation OperatorNormedDefinitions.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/OperatorSpaces.v from Coquelicot to MathComp-Analysis.

   Every definition and theorem of the original keeps its name and its
   arguments, in the same order. No item is added. The statements change
   form in the ways of the ports of MatrixCoordinates, CoefficientMaps,
   OperatorSpaceDefinitions and OperatorNormedDefinitions.

   1. Linear maps. Coquelicot's is_linear l is a record with three fields,
        l (plus x y) = plus (l x) (l y),
        l (scal k x) = scal k (l x),
        exists M, 0 < M /\ forall x, norm (l x) <= M * norm x.
      As in OperatorSpaceDefinitions, the port states it as the conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity, which is equivalent to the first
      two fields, and of Coquelicot's norm bound. The bound uses Stdlib's 0,
      <, <= and * around MathComp's norms. This is the predicate of
      bounded_matrix_map, so the proof argument Hf of operator_family has
      the type it had in the original, up to this translation, and
      exist _ (f x) (Hf x) is an element of bounded_matrix_map n V as before.

   2. Coquelicot's NormedModule R_AbsRing becomes normedModType R, and its
      norm, zero, plus and scal become MathComp's `|_|, 0, + and *:,
      written (`|_|)%R, 0%R, (_ + _)%R and (_ *: _)%R. On
      bounded_matrix_NormedModule n V they are the operations that
      OperatorNormedDefinitions transports from operator_coefficients n V,
      as in the original: the norm of L is the norm of operator_encode n V L,
      and L + M is operator_decode n V (operator_encode n V L +
      operator_encode n V M).

   3. Norms and constants. operator_coefficients n V carries the Euclidean
      norm of its n + 1 by n + 1 entries, each measured with the norm of V
      (MatrixDefinitions keeps Coquelicot's product norm), and matrix n the
      Frobenius norm. So operator_coefficient_norm_bound and
      operator_apply_product_bound mean the same as in the original,
      constants included.

   4. Proofs. Coquelicot's is_linear_comp becomes matrix_linear_comp of
      MatrixCoordinates, and is_linear_scal_r is proved in place.
      linear_plus becomes the linearity equation at the scalar 1, and
      linear_scal and linear_zero become MathComp's linearZ_LR and linear0,
      applied to the map packed as a {linear _ -> _} inside the proof. The
      original rewrote functions with Coquelicot's is_linear_ext
      in operator_evaluation_linear and with Stdlib's
      functional_extensionality in operator_family_linear. The port uses
      funext of MathComp's boolp in both, which rests on
      boolp.functional_extensionality_dep, one of the seven axioms of the
      README. No proof uses Classical_Prop.classic. *)

Theorem operator_encode_linear n V :
  linear (operator_encode n V : bounded_matrix_NormedModule n V -> operator_coefficients n V) /\
  exists M : R, 0 < M /\
    forall L : bounded_matrix_NormedModule n V,
      (`|operator_encode n V L|)%R <= M * (`|L|)%R.
Proof. apply transport_encode_linear. Qed.

Theorem operator_decode_linear n V :
  linear (operator_decode n V : operator_coefficients n V -> bounded_matrix_NormedModule n V) /\
  exists M : R, 0 < M /\
    forall C : operator_coefficients n V,
      (`|operator_decode n V C : bounded_matrix_NormedModule n V|)%R <= M * (`|C|)%R.
Proof. apply transport_decode_linear. Qed.

Theorem operator_norm_encode n V (L : bounded_matrix_NormedModule n V) :
  (`|L|)%R = (`|operator_encode n V L|)%R.
Proof. reflexivity. Qed.

Theorem operator_norm_decode n V (C : operator_coefficients n V) :
  (`|operator_decode n V C : bounded_matrix_NormedModule n V|)%R = (`|C|)%R.
Proof.
  change ((`|operator_encode n V (operator_decode n V C)|)%R = (`|C|)%R).
  rewrite operator_encode_decode; reflexivity.
Qed.

Theorem operator_coefficient_linear n V i j :
  linear (fun C : operator_coefficients n V => operator_coefficient n V C i j) /\
  exists M : R, 0 < M /\
    forall C : operator_coefficients n V,
      (`|operator_coefficient n V C i j|)%R <= M * (`|C|)%R.
Proof.
  unfold operator_coefficient; apply (matrix_linear_comp
    (tuple_entry (tuple_NormedModule V n) n i) (tuple_entry V n j)); apply tuple_entry_linear.
Qed.

Theorem operator_coefficient_apply_linear_coefficients n V W :
  linear (fun C : operator_coefficients n V => operator_coefficient_apply n V C W) /\
  exists M : R, 0 < M /\
    forall C : operator_coefficients n V,
      (`|operator_coefficient_apply n V C W|)%R <= M * (`|C|)%R.
Proof.
  unfold operator_coefficient_apply, coefficient_contract.
  apply (module_coordinate_sum_linear n (fun i (C : operator_coefficients n V) =>
    module_coordinate_sum V n (fun j =>
      (matrix_entry n W j i *: operator_coefficient n V C i j)%R))).
  intros i Hi.
  apply (module_coordinate_sum_linear n (fun j (C : operator_coefficients n V) =>
    (matrix_entry n W j i *: operator_coefficient n V C i j)%R)).
  intros j Hj.
  apply (matrix_linear_comp (fun C : operator_coefficients n V => operator_coefficient n V C i j)
    (fun x : V => (matrix_entry n W j i *: x)%R)).
  - apply operator_coefficient_linear.
  - split.
    + intros a u v; rewrite /= scalerDr !scalerA.
      by rewrite mulrC.
    + exists (Rabs (matrix_entry n W j i) + 1); split.
      * assert (0 <= Rabs (matrix_entry n W j i)) by apply Rabs_pos; lra.
      * intros x; rewrite normrZ -RmultE RabsE.
        assert (0 <= (`|matrix_entry n W j i|)%R)
          by (apply/RleP; apply normr_ge0).
        assert (0 <= (`|x|)%R) by (apply/RleP; apply normr_ge0).
        have Hle : forall a h : R, 0 <= a -> 0 <= h -> a * h <= (a + 1) * h.
        { intros a h Ha Hh; nra. }
        apply Hle; assumption.
Qed.

Theorem operator_apply_encode n V (L : bounded_matrix_map n V) W :
  operator_coefficient_apply n V (operator_encode n V L) W = operator_apply n V L W.
Proof.
  change (operator_apply n V (operator_decode n V (operator_encode n V L)) W = operator_apply n V L W).
  rewrite operator_decode_encode; reflexivity.
Qed.

Theorem operator_evaluation_linear n V W :
  linear (fun L : bounded_matrix_NormedModule n V => operator_apply n V L W) /\
  exists M : R, 0 < M /\
    forall L : bounded_matrix_NormedModule n V,
      (`|operator_apply n V L W|)%R <= M * (`|L|)%R.
Proof.
  destruct (matrix_linear_comp
    (operator_encode n V : bounded_matrix_NormedModule n V -> operator_coefficients n V)
    (fun C => operator_coefficient_apply n V C W)
    (operator_encode_linear n V)
    (operator_coefficient_apply_linear_coefficients n V W)) as [HL [M [HM HB]]].
  split.
  - have -> : (fun L : bounded_matrix_NormedModule n V => operator_apply n V L W) =
      (fun L : bounded_matrix_NormedModule n V =>
        operator_coefficient_apply n V (operator_encode n V L) W).
    { apply funext; intros L; symmetry; apply operator_apply_encode. }
    exact HL.
  - exists M; split; [exact HM|]; intros L.
    rewrite -operator_apply_encode; apply HB.
Qed.

Theorem operator_apply_linear n V (L : bounded_matrix_NormedModule n V) :
  linear (operator_apply n V L) /\
  exists M : R, 0 < M /\
    forall W : matrix n, (`|operator_apply n V L W|)%R <= M * (`|W|)%R.
Proof. exact (proj2_sig L). Qed.

Theorem operator_apply_plus n V (L M : bounded_matrix_NormedModule n V) W :
  operator_apply n V (L + M)%R W = (operator_apply n V L W + operator_apply n V M W)%R.
Proof.
  have H := proj1 (operator_evaluation_linear n V W) 1%R L M.
  rewrite /= !scale1r in H; exact H.
Qed.

Theorem operator_apply_scal n V c (L : bounded_matrix_NormedModule n V) W :
  operator_apply n V (c *: L)%R W = (c *: operator_apply n V L W)%R.
Proof.
  pose F : {linear bounded_matrix_NormedModule n V -> V} :=
    HB.pack (fun L : bounded_matrix_NormedModule n V => operator_apply n V L W)
      (GRing.isLinear.Build R (bounded_matrix_NormedModule n V) V *:%R
        (fun L : bounded_matrix_NormedModule n V => operator_apply n V L W)
        (proj1 (operator_evaluation_linear n V W))).
  exact (linearZ_LR F c L).
Qed.

Theorem operator_apply_zero n V W :
  operator_apply n V (0%R : bounded_matrix_NormedModule n V) W = 0%R.
Proof.
  pose F : {linear bounded_matrix_NormedModule n V -> V} :=
    HB.pack (fun L : bounded_matrix_NormedModule n V => operator_apply n V L W)
      (GRing.isLinear.Build R (bounded_matrix_NormedModule n V) V *:%R
        (fun L : bounded_matrix_NormedModule n V => operator_apply n V L W)
        (proj1 (operator_evaluation_linear n V W))).
  exact (linear0 F).
Qed.

Theorem operator_coefficient_norm_bound n V (C : operator_coefficients n V) i j :
  (`|operator_coefficient n V C i j|)%R <= (`|C|)%R.
Proof.
  unfold operator_coefficient; eapply Rle_trans;
    [apply tuple_entry_norm_bound|apply tuple_entry_norm_bound].
Qed.

Theorem operator_apply_product_bound n V (L : bounded_matrix_NormedModule n V) W :
  (`|operator_apply n V L W|)%R <= INR (S n)^2 * (`|L|)%R * (`|W|)%R.
Proof.
  rewrite -operator_apply_encode; change
    ((`|coefficient_contract V n (operator_coefficient n V (operator_encode n V L)) W|)%R <=
      INR (S n)^2 * (`|operator_encode n V L|)%R * (`|W|)%R).
  apply coefficient_contract_product_bound; [apply/RleP; apply normr_ge0|].
  intros; apply operator_coefficient_norm_bound.
Qed.

Definition operator_family {E : Type} n (V : normedModType R) (f : E -> matrix n -> V)
    (Hf : forall x, linear (f x) /\
      exists M : R, 0 < M /\ forall W : matrix n, (`|f x W|)%R <= M * (`|W|)%R)
    (x : E) : bounded_matrix_NormedModule n V :=
  exist _ (f x) (Hf x).

Theorem operator_family_linear {E : normedModType R} n (V : normedModType R)
    (f : E -> matrix n -> V)
    (Hf : forall x, linear (f x) /\
      exists M : R, 0 < M /\ forall W : matrix n, (`|f x W|)%R <= M * (`|W|)%R) :
  (forall W, linear (fun x => f x W) /\
    exists M : R, 0 < M /\ forall x : E, (`|f x W|)%R <= M * (`|x|)%R) ->
  linear (operator_family n V f Hf) /\
  exists M : R, 0 < M /\
    forall x : E, (`|operator_family n V f Hf x|)%R <= M * (`|x|)%R.
Proof.
  intros H.
  assert (HE : linear (fun x => operator_encode n V (operator_family n V f Hf x)) /\
    exists M : R, 0 < M /\
      forall x : E, (`|operator_encode n V (operator_family n V f Hf x)|)%R <= M * (`|x|)%R).
  { unfold operator_encode, operator_family, operator_apply; simpl.
    refine (tuple_build_linear n _ _); intros i Hi.
    refine (tuple_build_linear n _ _); intros j Hj.
    apply H. }
  have HQ : operator_family n V f Hf =
    (fun x => operator_decode n V (operator_encode n V (operator_family n V f Hf x))).
  { apply funext; intros x; symmetry; apply operator_decode_encode. }
  rewrite HQ; apply (matrix_linear_comp
    (fun x => operator_encode n V (operator_family n V f Hf x))
    (operator_decode n V : operator_coefficients n V -> bounded_matrix_NormedModule n V));
    [exact HE|apply operator_decode_linear].
Qed.
