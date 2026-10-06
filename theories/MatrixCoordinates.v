From Stdlib Require Import Reals Lra Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Entries of tuples and matrices, and bounded linear maps. A bounded
   linear map l is stated as MathComp's linear l together with the bound
   exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R. Entries,
   compositions, sums, scalings and finite sums of such maps are bounded
   linear (tuple_entry_linear, matrix_linear_comp, coordinate_sum_linear).
   Such a map is continuous (matrix_linear_continuous) and is its own
   Frechet derivative (matrix_linear_is_diff). A real-valued map is given
   the codomain R^o, the normed module view of R, where linear or is_diff
   needs one. Index bounds are written (i <= n)%coq_nat, Stdlib's le,
   since with ssreflect loaded (i <= n)%nat is ssrnat's leq. *)

(* Declaring tuple_entry V n i a linear map makes HB report canonical
   projections that duplicate existing ones. Rocq ignores the duplicates; the
   warning is silenced in this file only. *)
Local Set Warnings "-redundant-canonical-projection".

Lemma tuple_entry_build (V : normedModType R) n i (f : nat -> V) :
  (i <= n)%coq_nat -> tuple_entry V n i (tuple_build V n f) = f i.
Proof.
  revert i f; induction n as [|n IH]; intros [|i] f Hi; simpl.
  - reflexivity.
  - lia.
  - reflexivity.
  - apply (IH i (fun j => f (S j))); lia.
Qed.

Lemma tuple_ext (V : normedModType R) n
    (x y : tuple_NormedModule V n) :
  (forall i, (i <= n)%coq_nat -> tuple_entry V n i x = tuple_entry V n i y) ->
  x = y.
Proof.
  revert x y; induction n as [|n IH]; intros x y H.
  - exact (H O (Nat.le_refl O)).
  - destruct x as [x xs], y as [y ys].
    assert (H0 : x = y) by (apply (H O); lia).
    assert (Htail : xs = ys).
    { apply IH; intros i Hi; apply (H (S i)); lia. }
    now rewrite H0 Htail.
Qed.

(* The bound holds with M = 1: an entry has at most the norm of the tuple. *)
Lemma tuple_entry_linear (V : normedModType R) n i :
  linear (tuple_entry V n i) /\
  exists M : R, 0 < M /\
    forall x : tuple_NormedModule V n,
      (`|tuple_entry V n i x|)%R <= M * (`|x|)%R.
Proof.
  split.
  - revert i; induction n as [|n IH]; intros [|i] a u v; simpl.
    + reflexivity.
    + by rewrite scaler0 addr0.
    + reflexivity.
    + exact (IH i a u.2 v.2).
  - exists 1; split; [lra|].
    assert (Hle : forall n i (x : tuple_NormedModule V n),
      (`|tuple_entry V n i x|)%R <= (`|x|)%R).
    { clear n i; intros n; induction n as [|n IH]; intros [|i] x; simpl.
      - lra.
      - rewrite normr0; apply/RleP; apply normr_ge0.
      - apply/RleP; apply (euclidean_product_norm_fst x).
      - apply (Rle_trans _ _ _ (IH i x.2)).
        apply/RleP; apply (euclidean_product_norm_snd x). }
    intros x; rewrite Rmult_1_l; apply Hle.
Qed.

(* tuple_entry V n i is a {linear _ -> _} of MathComp, so that linearD,
   linearZ, linear0 and the other lemmas about linear maps apply to it
   directly. *)
HB.instance Definition _ (V : normedModType R) n i :=
  GRing.isLinear.Build R (tuple_NormedModule V n) V *:%R (tuple_entry V n i)
    (proj1 (tuple_entry_linear V n i)).

Lemma matrix_entry_build n f i j :
  (i <= n)%coq_nat -> (j <= n)%coq_nat ->
  matrix_entry n (matrix_build n f) i j = f i j.
Proof.
  intros Hi Hj; unfold matrix_entry, matrix_build.
  rewrite !tuple_entry_build //.
Qed.

Lemma matrix_ext n (A B : matrix n) :
  (forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat ->
    matrix_entry n A i j = matrix_entry n B i j) -> A = B.
Proof.
  intros H; apply tuple_ext; intros i Hi.
  apply tuple_ext; intros j Hj; apply H; assumption.
Qed.

(* The composition of two bounded linear maps is bounded linear. *)
Lemma matrix_linear_comp {U V W : normedModType R}
    (l1 : U -> V) (l2 : V -> W) :
  (linear l1 /\
    exists M : R, 0 < M /\ forall x : U, (`|l1 x|)%R <= M * (`|x|)%R) ->
  (linear l2 /\
    exists M : R, 0 < M /\ forall y : V, (`|l2 y|)%R <= M * (`|y|)%R) ->
  linear (fun x => l2 (l1 x)) /\
    exists M : R, 0 < M /\ forall x : U, (`|l2 (l1 x)|)%R <= M * (`|x|)%R.
Proof.
  intros [L1 [M1 [M10 HM1]]] [L2 [M2 [M20 HM2]]]; split.
  - intros a u v; simpl; rewrite L1; apply L2.
  - exists (M2 * M1); split; [nra|]; intros x.
    apply (Rle_trans _ _ _ (HM2 _)).
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [lra|apply HM1].
Qed.

Lemma matrix_entry_linear n i j :
  linear (fun A : matrix n => matrix_entry n A i j : R^o) /\
  exists M : R, 0 < M /\
    forall A : matrix n, (`|matrix_entry n A i j|)%R <= M * (`|A|)%R.
Proof.
  unfold matrix_entry.
  apply (matrix_linear_comp
    (tuple_entry (tuple_NormedModule R^o n) n i)
    (tuple_entry R^o n j)); apply tuple_entry_linear.
Qed.

Lemma matrix_entry_add n (A B : matrix n) i j :
  matrix_entry n (matrix_add n A B) i j =
  matrix_entry n A i j + matrix_entry n B i j.
Proof.
  unfold matrix_entry, matrix_add; rewrite !linearD; reflexivity.
Qed.

Lemma matrix_entry_scale n c (A : matrix n) i j :
  matrix_entry n (matrix_scale n c A) i j = c * matrix_entry n A i j.
Proof.
  unfold matrix_entry, matrix_scale; rewrite !linearZ; reflexivity.
Qed.

Lemma matrix_entry_zero n i j : matrix_entry n (matrix_zero n) i j = 0.
Proof.
  unfold matrix_entry, matrix_zero; rewrite !linear0; reflexivity.
Qed.

(* MathComp's linear is algebraic only; the norm bound makes the map
   continuous. *)
Lemma matrix_linear_continuous {U W : normedModType R} (f : U -> W) :
  (linear f /\
    exists M : R, 0 < M /\ forall x : U, (`|f x|)%R <= M * (`|x|)%R) ->
  continuous f.
Proof.
  intros [Lf [M [M0 HM]]].
  pose L : {linear U -> W} := HB.pack f (GRing.isLinear.Build R U W *:%R f Lf).
  change (continuous L).
  apply: bounded_linear_continuous; apply/linear_boundedP.
  exists M; split; [by rewrite num_real|].
  move=> r /RltP Mr x.
  apply/RleP; apply (Rle_trans _ _ _ (HM x)).
  apply Rmult_le_compat_r; [apply/RleP; apply normr_ge0|lra].
Qed.

(* A linear map with a norm bound is its own Frechet derivative at every
   point. *)
Lemma matrix_linear_is_diff {U W : normedModType R} (f : U -> W) (x : U) :
  (linear f /\
    exists M : R, 0 < M /\ forall y : U, (`|f y|)%R <= M * (`|y|)%R) ->
  is_diff x f f.
Proof.
  intros Hf; have Hc := matrix_linear_continuous f Hf.
  destruct Hf as [Lf _].
  pose L : {linear U -> W} := HB.pack f (GRing.isLinear.Build R U W *:%R f Lf).
  change (is_diff x L L).
  apply: DiffDef; [exact: linear_differentiable | exact: diff_lin].
Qed.

Lemma matrix_entry_frechet n (A : matrix n) i j :
  is_diff A (fun M : matrix n => matrix_entry n M i j : R^o)
    (fun H : matrix n => matrix_entry n H i j).
Proof. apply matrix_linear_is_diff, matrix_entry_linear. Qed.

Lemma coordinate_sum_ext n f g :
  (forall i, (i <= n)%coq_nat -> f i = g i) ->
  coordinate_sum n f = coordinate_sum n g.
Proof.
  revert f g; induction n as [|n IH]; intros f g H; simpl.
  - apply H; lia.
  - f_equal.
    + apply H; lia.
    + apply IH; intros; apply H; lia.
Qed.

Lemma matrix_linear_sum {U : normedModType R} (f g : U -> R) :
  (linear (f : U -> R^o) /\
    exists M : R, 0 < M /\ forall x : U, (`|f x|)%R <= M * (`|x|)%R) ->
  (linear (g : U -> R^o) /\
    exists M : R, 0 < M /\ forall x : U, (`|g x|)%R <= M * (`|x|)%R) ->
  linear ((fun x => f x + g x) : U -> R^o) /\
    exists M : R, 0 < M /\
      forall x : U, Num.norm (f x + g x) <= M * (`|x|)%R.
Proof.
  intros [Lf [Mf [Mf0 HMf]]] [Lg [Mg [Mg0 HMg]]]; split.
  - intros a u v; rewrite /= Lf Lg.
    change (a * f u + f v + (a * g u + g v) =
      a * (f u + g u) + (f v + g v)); ring.
  - exists (Mf + Mg); split; [lra|]; intros x.
    rewrite -RabsE.
    apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite !RabsE.
    specialize (HMf x); specialize (HMg x); lra.
Qed.

Lemma matrix_linear_scale {U : normedModType R} (c : R) (f : U -> R) :
  (linear (f : U -> R^o) /\
    exists M : R, 0 < M /\ forall x : U, (`|f x|)%R <= M * (`|x|)%R) ->
  linear ((fun x => c * f x) : U -> R^o) /\
    exists M : R, 0 < M /\ forall x : U, Num.norm (c * f x) <= M * (`|x|)%R.
Proof.
  intros [Lf [Mf [Mf0 HMf]]]; split.
  - intros a u v; rewrite /= Lf.
    change (c * (a * f u + f v) = a * (c * f u) + c * f v); ring.
  - exists ((Rabs c + 1) * Mf); split.
    + assert (0 <= Rabs c) by apply Rabs_pos; nra.
    + intros x; specialize (HMf x); rewrite -RabsE in HMf.
      rewrite -RabsE Rabs_mult.
      assert (0 <= Rabs c) by apply Rabs_pos.
      assert (0 <= Rabs (f x)) by apply Rabs_pos.
      assert (0 <= (`|x|)%R) by (apply/RleP; apply normr_ge0).
      nra.
Qed.

Lemma coordinate_sum_linear {U : normedModType R} n (F : nat -> U -> R) :
  (forall i, (i <= n)%coq_nat ->
    linear (F i : U -> R^o) /\
    exists M : R, 0 < M /\ forall x : U, (`|F i x|)%R <= M * (`|x|)%R) ->
  linear ((fun x => coordinate_sum n (fun i => F i x)) : U -> R^o) /\
    exists M : R, 0 < M /\
      forall x : U, (`|coordinate_sum n (fun i => F i x)|)%R <= M * (`|x|)%R.
Proof.
  revert F; induction n as [|n IH]; intros F H; simpl.
  - apply H; lia.
  - apply matrix_linear_sum.
    + apply H; lia.
    + apply IH; intros i Hi; apply H; lia.
Qed.
