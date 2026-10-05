From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/MatrixTrace.v from Coquelicot to MathComp-Analysis.

   Every theorem of the original keeps its name and its arguments, in the
   same order. Four statements change form, in the ways the port of
   MatrixCoordinates describes.

   1. Linear maps. Coquelicot's is_linear l is stated as
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R,
      that is, MathComp's algebraic linearity together with Coquelicot's
      norm bound. The norms are those of MatrixDefinitions: the Frobenius
      norm on matrices and the absolute value on R, as in Coquelicot. This
      is the form of trace_pair_linear, trace_pair_left_linear and
      matrix_trace_linear, and of the hypotheses of matrix_linear_is_diff,
      coordinate_sum_linear and matrix_linear_comp of MatrixCoordinates.

   2. Real-valued maps. A map into R is written with codomain R^o, the
      normed module view of R, where linear or is_diff needs a module
      structure on the codomain, as in (trace_pair n B : matrix n -> R^o).
      R^o is R by definition, so nothing else changes.

   3. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis: f is differentiable at A and its
      differential 'd f A is l. Both say that
      f (A + H) = f A + l H + o(H), with l linear and continuous, for the
      Frobenius norm. This is the form of matrix_trace_frechet,
      trace_pair_frechet and exp_trace_pair_frechet.

   4. exp is Stdlib's exponential, as in the original. The proof of
      exp_trace_pair_frechet moves to MathComp's expR through RexpE only
      inside the proof.

   trace_pair_is_trace_product, trace_pair_add, trace_pair_scale and
   trace_pair_line_derivative keep their statements word for word.
   derivable_pt_lim is Stdlib's, as in the original.

   The port adds two Hierarchy Builder instances, marked below. They
   declare matrix_trace n and trace_pair n B linear maps of MathComp, so
   that linearD, linearZ, linear0 and the other lemmas about linear maps
   apply to them directly. They change no statement. *)

(* Declaring matrix_trace n and trace_pair n B linear makes HB report
   canonical projections that duplicate existing ones. Rocq ignores the
   duplicates; the warning is silenced in this file only. *)
Local Set Warnings "-redundant-canonical-projection".

Theorem trace_pair_linear n (B : matrix n) :
  linear (trace_pair n B : matrix n -> R^o) /\
  exists M : R, 0 < M /\
    forall H : matrix n, (`|trace_pair n B H|)%R <= M * (`|H|)%R.
Proof.
  unfold trace_pair; apply coordinate_sum_linear; intros i Hi.
  apply coordinate_sum_linear; intros j Hj.
  apply matrix_linear_scale, matrix_entry_linear.
Qed.

Theorem trace_pair_left_linear n (H : matrix n) :
  linear ((fun B : matrix n => trace_pair n B H) : matrix n -> R^o) /\
  exists M : R, 0 < M /\
    forall B : matrix n, (`|trace_pair n B H|)%R <= M * (`|B|)%R.
Proof.
  unfold trace_pair; apply coordinate_sum_linear; intros i Hi.
  apply coordinate_sum_linear; intros j Hj.
  have [L [M [M0 HM]]] :=
    matrix_linear_scale (matrix_entry n H j i) _ (matrix_entry_linear n i j).
  split.
  - have E : (fun B : matrix n => matrix_entry n B i j * matrix_entry n H j i) =
      (fun B : matrix n => matrix_entry n H j i * matrix_entry n B i j).
    { apply: funext => B; apply Rmult_comm. }
    rewrite E; exact L.
  - exists M; split; [exact M0|]; intros B.
    rewrite Rmult_comm; apply HM.
Qed.

Theorem matrix_trace_linear n :
  linear (matrix_trace n : matrix n -> R^o) /\
  exists M : R, 0 < M /\
    forall A : matrix n, (`|matrix_trace n A|)%R <= M * (`|A|)%R.
Proof.
  unfold matrix_trace; apply coordinate_sum_linear; intros i Hi.
  apply matrix_entry_linear.
Qed.

(* Added by the port: matrix_trace n is a {linear _ -> _} of MathComp. *)
HB.instance Definition _ n :=
  GRing.isLinear.Build R (matrix_NormedModule n) R^o *:%R (matrix_trace n)
    (proj1 (matrix_trace_linear n)).

(* Added by the port: trace_pair n B is a {linear _ -> _} of MathComp. *)
HB.instance Definition _ n (B : matrix n) :=
  GRing.isLinear.Build R (matrix_NormedModule n) R^o *:%R (trace_pair n B)
    (proj1 (trace_pair_linear n B)).

Theorem trace_pair_add n (B H K : matrix n) :
  trace_pair n B (matrix_add n H K) = trace_pair n B H + trace_pair n B K.
Proof. unfold matrix_add; rewrite linearD; reflexivity. Qed.

Theorem trace_pair_scale n (B H : matrix n) c :
  trace_pair n B (matrix_scale n c H) = c * trace_pair n B H.
Proof. unfold matrix_scale; rewrite linearZ; reflexivity. Qed.

(* This is a Frechet derivative on the entire finite matrix space. *)
Theorem trace_pair_frechet n (B A : matrix n) :
  is_diff A (trace_pair n B : matrix n -> R^o) (trace_pair n B).
Proof. apply matrix_linear_is_diff, trace_pair_linear. Qed.
