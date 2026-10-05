From Stdlib Require Import Reals Lra Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct prodnormedzmodule.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/MatrixAssembly.v from Coquelicot to MathComp-Analysis.

   The three results keep their names, their implicit and explicit arguments,
   and their order. Their statements change form in three ways, as in the
   port of MatrixCoordinates.

   1. Coquelicot's NormedModule R_AbsRing becomes normedModType R, and
      Coquelicot's filterdiff f (locally A) df becomes is_diff A f df of
      MathComp-Analysis: f is differentiable at A and its differential is df.
      Both say that f (A + H) = f A + df H + o(H), with df linear and
      continuous.

   2. With ssreflect loaded, (i <= n)%nat means ssrnat's boolean leq. The
      original means Stdlib's Peano order le, so the statements write
      (i <= n)%coq_nat, which is ssrnat's notation for Stdlib's le.

   3. The pair in pair_frechet lives in euclidean_product U V of
      MatrixEuclideanProduct, which carries Coquelicot's product norm
      sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2), and not in MathComp's
      U * V, which carries the max norm. This is the product that
      tuple_NormedModule nests, so tuple_build_frechet follows from
      pair_frechet by induction as in the original. The two norms are
      equivalent, so the derivative of a pair is the same for both; the proof
      goes through MathComp's is_diff_pair on U * V and the identity map from
      U * V to euclidean_product U V.

   In matrix_build_frechet the entries F i j and D i j are real valued. They
   are seen as maps into R^o, the normed module view of R, where is_diff needs
   a normed codomain. R^o is R by definition, so maps of type E -> R are
   accepted there.

   The port adds one lemma, pair_euclidean_identity_linear, marked below. *)

(* Added by the port. The identity map from MathComp's product U * V, with the
   max norm, to euclidean_product U V, with the Euclidean product norm, is
   linear and bounded with constant 2, in the form that the port of
   MatrixCoordinates gives to Coquelicot's is_linear. *)
Lemma pair_euclidean_identity_linear (U V : normedModType R) :
  linear ((fun p => p) : (U * V)%type -> euclidean_product U V) /\
  exists M : R, 0 < M /\
    forall p : (U * V)%type,
      (`|(p : euclidean_product U V)|)%R <= M * (`|p|)%R.
Proof.
  split.
  - intros a u v; reflexivity.
  - exists 2; split; [lra|]; intros p.
    assert (H0 : (`|(p : euclidean_product U V)| <= `|p.1| + `|p.2|)%R)
      by exact: euclidean_product_norm_le.
    have H1 : (`|p.1| <= `|p|)%R
      by rewrite prod_normE Order.TotalTheory.le_max Order.POrderTheory.lexx.
    have H2 : (`|p.2| <= `|p|)%R
      by rewrite prod_normE Order.TotalTheory.le_max Order.POrderTheory.lexx orbT.
    move: H0 H1 H2 => /RleP H0 /RleP H1 /RleP H2.
    rewrite -RplusE in H0; lra.
Qed.

Lemma pair_frechet {E U V : normedModType R}
    (f df : E -> U) (g dg : E -> V) (A : E) :
  is_diff A f df -> is_diff A g dg ->
  is_diff A ((fun M => (f M, g M)) : E -> euclidean_product U V)
    ((fun H => (df H, dg H)) : E -> euclidean_product U V).
Proof.
  intros HF HG.
  have Hj := matrix_linear_is_diff _ ((f A, g A) : (U * V)%type)
    (pair_euclidean_identity_linear U V).
  exact (@is_diff_comp R E (U * V)%type (euclidean_product U V) _ _ _ _ A
    (is_diff_pair HF HG) Hj).
Qed.

Theorem tuple_build_frechet {E V : normedModType R}
    n (F D : nat -> E -> V) (A : E) :
  (forall i, (i <= n)%coq_nat -> is_diff A (F i) (D i)) ->
  is_diff A (fun M => tuple_build V n (fun i => F i M))
    (fun H => tuple_build V n (fun i => D i H)).
Proof.
  revert F D; induction n as [|n IH]; intros F D HF; simpl.
  - apply HF; lia.
  - apply pair_frechet.
    + apply HF; lia.
    + apply IH; intros i Hi; apply HF; lia.
Qed.

Theorem matrix_build_frechet {E : normedModType R}
    n (F D : nat -> nat -> E -> R) (A : E) :
  (forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat ->
    is_diff A (F i j : E -> R^o) (D i j : E -> R^o)) ->
  is_diff A (fun M => matrix_build n (fun i j => F i j M))
    (fun H => matrix_build n (fun i j => D i j H)).
Proof.
  intros HF; unfold matrix_build; apply tuple_build_frechet; intros i Hi.
  apply tuple_build_frechet; intros j Hj; apply HF; assumption.
Qed.
