From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions MatrixDefinitions MatrixCoordinates MatrixTrace
  MatrixGibbsDefinitions MatrixGibbs MatrixSecondDefinitions MatrixSecond
  MatrixThirdDefinitions MatrixThird MatrixAssembly GradientDefinitions MatrixGradient
  MatrixFrechetUnique HessianDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/MatrixHessian.v from Coquelicot to MathComp-Analysis.

   Every theorem of the original keeps its name and its arguments, in the
   same order. No lemma is added. The statements change form in three ways,
   the same ways as in the ports of MatrixCoordinates, MatrixAssembly,
   MatrixGradient, MatrixSecond and MatrixThird, which this module imports.

   1. Order on indices. With ssreflect loaded, (i <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      statements write (i <= n)%coq_nat, which is ssrnat's notation for
      Stdlib's le. The meaning is unchanged.

   2. Frechet derivatives. Coquelicot's NormedModule R_AbsRing becomes
      normedModType R, and Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis: f is differentiable at A and its
      differential 'd f A is l. Both say that l is linear and continuous and
      that f (A + H) = f A + l H + o(H) as H tends to 0. The norms are those
      of MatrixDefinitions and HessianDefinitions: the Frobenius norm on
      matrix n and the Euclidean norm of all entries on hessian_array n, as
      in Coquelicot. Differentiability does not depend on the choice among
      equivalent norms in any case.

   3. Real-valued maps. A map into R given to is_diff is written with
      codomain R^o, the normed module view of R, as in
      (fun M => soft_minimax ... : matrix n -> R^o). R^o is R by definition,
      so the map is the same.

   The arithmetic in the statements is Stdlib's, as in the original. The
   definitions used here, those of HessianDefinitions, GradientDefinitions,
   MatrixSecondDefinitions and MatrixThirdDefinitions, keep their names,
   arguments and values in the port.

   In the proofs, Coquelicot's filterdiff_ext becomes rewriting the function
   with funext, filterdiff_comp' becomes is_diff_comp, filterdiff_linear
   with trace_pair_left_linear becomes matrix_linear_is_diff of
   MatrixCoordinates with trace_pair_left_linear of MatrixTrace, and
   filterdiff_ext_lin becomes is_diff_eq. *)

Theorem hessian_entry_build n F i j :
  (i <= n)%coq_nat -> (j <= n)%coq_nat ->
  hessian_entry n (hessian_build n F) i j = F i j.
Proof.
  intros Hi Hj; unfold hessian_entry, hessian_build.
  rewrite (tuple_entry_build _ n i _ Hi) (tuple_entry_build _ n j _ Hj).
  reflexivity.
Qed.

Theorem hessian_build_frechet {E : normedModType R}
    n (F D : nat -> nat -> E -> matrix n) (A : E) :
  (forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat ->
    is_diff A (F i j) (D i j)) ->
  is_diff A (fun M => hessian_build n (fun i j => F i j M))
    (fun V => hessian_build n (fun i j => D i j V)).
Proof.
  intros HF; unfold hessian_build; apply tuple_build_frechet; intros i Hi.
  apply tuple_build_frechet; intros j Hj; apply HF; assumption.
Qed.

Theorem matrix_nested_gradient_derivative_trace n beta gamma offset coeff Y S
    (A U V : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  trace_pair n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A V) U =
  matrix_nested_second_derivative n beta gamma offset coeff Y S A U V.
Proof.
  intros Hb Hg HY HS.
  assert (HT : is_diff A
    ((fun M => matrix_nested_derivative n beta gamma offset coeff Y S M U)
      : matrix n -> R^o)
    (fun W => trace_pair n
      (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A W) U)).
  { have E : ((fun M => matrix_nested_derivative n beta gamma offset coeff Y S M U)
        : matrix n -> R^o) =
      ((fun B : matrix n => trace_pair n B U) : matrix n -> R^o) \o
        matrix_nested_gradient n beta gamma offset coeff Y S.
    { apply: funext => M /=; symmetry; apply matrix_nested_gradient_trace. }
    rewrite E.
    exact (is_diff_comp
      (matrix_nested_gradient_frechet n beta gamma offset coeff Y S Hb Hg HY HS A)
      (matrix_linear_is_diff
        ((fun B : matrix n => trace_pair n B U) : matrix n -> R^o)
        (matrix_nested_gradient n beta gamma offset coeff Y S A)
        (trace_pair_left_linear n U))). }
  exact (scalar_frechet_unique _ _ _ A HT
    (matrix_nested_derivative_frechet n beta gamma offset coeff Y S A U Hb Hg HY HS) V).
Qed.

Theorem matrix_nested_gradient_second_frechet n beta gamma offset coeff Y S
    (A U : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  is_diff A (fun M => matrix_nested_gradient_derivative n beta gamma offset coeff Y S M U)
    (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A U).
Proof.
  intros Hb Hg HY HS.
  unfold matrix_nested_gradient_derivative, matrix_nested_gradient_second_derivative.
  apply (matrix_build_frechet n
    (fun i j M => matrix_nested_second_derivative n beta gamma offset coeff Y S M
      (matrix_basis n j i) U)
    (fun i j W => matrix_nested_third_derivative n beta gamma offset coeff Y S A
      (matrix_basis n j i) U W) A).
  intros i j Hi Hj.
  apply matrix_nested_second_evaluation_frechet; assumption.
Qed.

Theorem matrix_nested_gradient_second_trace n beta gamma offset coeff Y S
    (A U V W : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  trace_pair n (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A U V) W =
  matrix_nested_third_derivative n beta gamma offset coeff Y S A W U V.
Proof.
  intros Hb Hg HY HS.
  assert (HT : is_diff A
    ((fun M => matrix_nested_second_derivative n beta gamma offset coeff Y S M W U)
      : matrix n -> R^o)
    (fun Z => trace_pair n
      (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A U Z) W)).
  { have E : ((fun M => matrix_nested_second_derivative n beta gamma offset coeff Y S M W U)
        : matrix n -> R^o) =
      ((fun B : matrix n => trace_pair n B W) : matrix n -> R^o) \o
        (fun M => matrix_nested_gradient_derivative n beta gamma offset coeff Y S M U).
    { apply: funext => M /=; symmetry.
      apply matrix_nested_gradient_derivative_trace; assumption. }
    rewrite E.
    exact (is_diff_comp
      (matrix_nested_gradient_second_frechet n beta gamma offset coeff Y S A U
        Hb Hg HY HS)
      (matrix_linear_is_diff
        ((fun B : matrix n => trace_pair n B W) : matrix n -> R^o)
        (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A U)
        (trace_pair_left_linear n W))). }
  exact (scalar_frechet_unique _ _ _ A HT
    (matrix_nested_second_evaluation_frechet n beta gamma offset coeff Y S A W U
      Hb Hg HY HS) V).
Qed.

Theorem matrix_nested_hessian_action n beta gamma offset coeff Y S (A V : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  hessian_action n (matrix_nested_hessian n beta gamma offset coeff Y S A) V =
  matrix_nested_gradient_derivative n beta gamma offset coeff Y S A V.
Proof.
  intros Hb Hg HY HS; apply matrix_ext; intros i j Hi Hj.
  unfold hessian_action, matrix_nested_hessian.
  rewrite (matrix_entry_build n _ i j Hi Hj).
  rewrite (hessian_entry_build n _ i j Hi Hj).
  rewrite (matrix_nested_gradient_derivative_trace n beta gamma offset coeff Y S
    A V (matrix_basis n j i) Hb Hg HY HS).
  unfold matrix_nested_gradient_derivative.
  rewrite (matrix_entry_build n _ i j Hi Hj).
  apply matrix_nested_second_symmetric.
Qed.

Theorem matrix_nested_hessian_frechet n beta gamma offset coeff Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  forall A : matrix n,
  is_diff A (matrix_nested_hessian n beta gamma offset coeff Y S)
    (matrix_nested_hessian_derivative n beta gamma offset coeff Y S A).
Proof.
  intros Hb Hg HY HS A; unfold matrix_nested_hessian, matrix_nested_hessian_derivative.
  apply (hessian_build_frechet n
    (fun i j M => matrix_nested_gradient_derivative n beta gamma offset coeff Y S M
      (matrix_basis n j i))
    (fun i j V => matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A
      (matrix_basis n j i) V) A).
  intros i j Hi Hj.
  apply matrix_nested_gradient_second_frechet; assumption.
Qed.

Theorem matrix_nested_hessian_derivative_action n beta gamma offset coeff Y S
    (A V W : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  hessian_action n (matrix_nested_hessian_derivative n beta gamma offset coeff Y S A W) V =
  matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A V W.
Proof.
  intros Hb Hg HY HS; apply matrix_ext; intros i j Hi Hj.
  unfold hessian_action, matrix_nested_hessian_derivative.
  rewrite (matrix_entry_build n _ i j Hi Hj).
  rewrite (hessian_entry_build n _ i j Hi Hj).
  rewrite (matrix_nested_gradient_second_trace n beta gamma offset coeff Y S
    A (matrix_basis n j i) W V Hb Hg HY HS).
  unfold matrix_nested_gradient_second_derivative.
  rewrite (matrix_entry_build n _ i j Hi Hj).
  apply matrix_nested_third_swap_left.
Qed.

Theorem matrix_nested_hessian_derivative_evaluation n beta gamma offset coeff Y S
    (A U V W : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  hessian_evaluation n (matrix_nested_hessian_derivative n beta gamma offset coeff Y S A W) U V =
  matrix_nested_third_derivative n beta gamma offset coeff Y S A U V W.
Proof.
  intros Hb Hg HY HS; unfold hessian_evaluation.
  rewrite (matrix_nested_hessian_derivative_action n beta gamma offset coeff Y S
    A V W Hb Hg HY HS).
  apply matrix_nested_gradient_second_trace; assumption.
Qed.
