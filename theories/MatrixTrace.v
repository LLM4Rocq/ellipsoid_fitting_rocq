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

Theorem trace_pair_is_trace_product n (B H : matrix n) :
  trace_pair n B H = matrix_trace n (matrix_mul n B H).
Proof.
  unfold trace_pair, matrix_trace; apply coordinate_sum_ext; intros i Hi.
  rewrite matrix_mul_entry //.
Qed.

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

Theorem matrix_trace_frechet n (A : matrix n) :
  is_diff A (matrix_trace n : matrix n -> R^o) (matrix_trace n).
Proof. apply matrix_linear_is_diff, matrix_trace_linear. Qed.

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

Theorem exp_trace_pair_frechet n (B A : matrix n) :
  is_diff A ((fun M => exp (trace_pair n B M)) : matrix n -> R^o)
    (fun H => exp (trace_pair n B A) * trace_pair n B H).
Proof.
  set x := trace_pair n B A.
  (* The derivative of Stdlib's exp at x, as a differential on R^o. *)
  have Hexp : is_diff (x : R^o) (exp : R^o -> R^o) (fun h : R^o => h * exp x).
  { have Ee : (exp : R^o -> R^o) = (expR : R^o -> R^o).
    { apply: funext => t; rewrite RexpE; reflexivity. }
    rewrite Ee.
    have [Ed0 Hv0] := is_derive_expR x.
    have Ed : derivable (expR : R^o -> R^o) x 1 by exact Ed0.
    have Hv : 'D_1 (expR : R^o -> R^o) x = expR x by exact Hv0.
    have Dd : differentiable (expR : R^o -> R^o) x by apply/derivable1_diffP.
    apply: DiffDef; first exact Dd.
    rewrite diff1E // derive1E Hv; apply: funext => h /=.
    reflexivity. }
  have HC := is_diff_comp (trace_pair_frechet n B A) Hexp.
  apply: (is_diff_eq HC).
  apply: funext => H /=; rewrite /x; apply Rmult_comm.
Qed.

(* The same concrete matrix lines use the derivative predicate already used
   in the ellipsoid Gibbs development. *)
Theorem trace_pair_line_derivative n (B A U : matrix n) x :
  derivable_pt_lim
    (fun t => trace_pair n B (matrix_add n A (matrix_scale n t U))) x
    (trace_pair n B U).
Proof.
  apply (derivable_pt_lim_ext (fun t => trace_pair n B A + t * trace_pair n B U)).
  - intros t; rewrite trace_pair_add trace_pair_scale; reflexivity.
  - assert (H0 : derivable_pt_lim (fun _ => trace_pair n B A) x 0)
      by apply derivable_pt_lim_const.
    assert (H1 : derivable_pt_lim (fun t => t * trace_pair n B U) x
      (1 * trace_pair n B U)).
    { apply derivable_pt_lim_scal_right, derivable_pt_lim_id. }
    pose proof (derivable_pt_lim_plus (fun _ => trace_pair n B A)
      (fun t => t * trace_pair n B U) x 0 (1 * trace_pair n B U) H0 H1) as HD.
    rewrite Rmult_1_l Rplus_0_l in HD; exact HD.
Qed.
