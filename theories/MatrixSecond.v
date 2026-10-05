From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive realfun.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights GibbsDerivatives
  MatrixDefinitions MatrixCoordinates MatrixTrace MatrixGibbsDefinitions MatrixGibbs
  MatrixSecondDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/MatrixSecond.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements change form in the same three ways as in the port
   of MatrixGibbs, which this module imports.

   1. Normed spaces. Coquelicot's NormedModule R_AbsRing becomes
      normedModType R, a real normed space of MathComp-Analysis. On
      matrix n the norm is the Frobenius norm of MatrixDefinitions, as in
      Coquelicot.

   2. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis: f is differentiable at A and its
      differential 'd f A is l. Both say that l is linear and continuous and
      that f (A + H) = f A + l H + o(H) as H tends to 0. Coquelicot's
      is_linear contains the continuity of l as a norm bound; in
      MathComp-Analysis it comes with differentiable. So the hypotheses and
      conclusions say the same thing as in the original.

   3. Real-valued maps. A map into R is written with codomain R^o, the
      normed module view of R, because is_diff needs a normed module on the
      codomain, as in (F i : E -> R^o). R^o is R by definition, so F, D, DF,
      U and DU keep the type nat -> E -> R of the original, and the maps are
      the same.

   The arithmetic in the statements is Stdlib's, as in the original, and so
   is exp inside partition, gibbs_weight and gibbs_average. The definitions
   of MatrixSecondDefinitions are unchanged.

   The port adds one lemma, matrix_second_mult_frechet, marked below. It is
   the product rule in the form of Coquelicot's filterdiff_mult_fct, which
   the original applies twice. MathComp-Analysis states the product rule
   (is_diffM) with its own operations on functions, so this lemma restates
   it with Stdlib's product and sum. *)

(* Added by the port. The product rule, with the arguments and the
   derivative H |-> df H * g A + f A * dg H of Coquelicot's
   filterdiff_mult_fct. Coquelicot's hypothesis that the product of the
   scalars commutes is dropped, since the scalars are the reals. It is
   proved from MathComp-Analysis's is_diffM. *)
Lemma matrix_second_mult_frechet {E : normedModType R}
    (f g : E -> R) (A : E) (df dg : E -> R) :
  is_diff A (f : E -> R^o) df -> is_diff A (g : E -> R^o) dg ->
  is_diff A ((fun M => f M * g M) : E -> R^o)
    (fun H => df H * g A + f A * dg H).
Proof.
  intros HF HG.
  have HM := is_diffM HF HG.
  apply: (is_diff_eq HM).
  apply: funext => H.
  change (f A * dg H + g A * df H = df H * g A + f A * dg H).
  ring.
Qed.

Lemma matrix_quotient_frechet {E : normedModType R}
    (f g df dg : E -> R) (A : E) :
  g A <> 0 -> is_diff A (f : E -> R^o) df -> is_diff A (g : E -> R^o) dg ->
  is_diff A ((fun M => f M / g M) : E -> R^o)
    (fun H => (df H * g A - f A * dg H) / (g A) ^ 2).
Proof.
  (* The map p |-> 1 / p is differentiated with Stdlib's quotient rule and
     composed with g. The quotient is then f times this composite. *)
  intros HZ HF HG.
  have HI := matrix_gibbs_is_diff_of_Reals _ _ _
    (derivable_pt_lim_div (fct_cte 1) Ranalysis1.id (g A) 0 1
      (derivable_pt_lim_const 1 (g A)) (derivable_pt_lim_id (g A)) HZ).
  have HC := is_diff_comp HG HI.
  have HM := matrix_second_mult_frechet _ _ A _ _ HF HC.
  have E1 : (fun M => f M / g M) =
    (fun M => f M * ((fct_cte 1 / Ranalysis1.id)%F \o g) M).
  { apply: funext => M.
    change (f M * / g M = f M * (1 / g M)); unfold Rdiv; ring. }
  rewrite E1; apply: (is_diff_eq HM).
  apply: funext => H.
  change (df H * (1 / g A) + f A * (dg H * ((0 * g A - 1 * 1) / (g A)²)) =
    (df H * g A - f A * dg H) / (g A) ^ 2).
  unfold Rsqr; field; exact HZ.
Qed.

Lemma matrix_partition_frechet {E : normedModType R}
    c (F D : nat -> E -> R) I (A : E) :
  I <> [] -> (forall i, In i I -> is_diff A (F i : E -> R^o) (D i)) ->
  is_diff A ((fun M => partition c (fun i => F i M) I) : E -> R^o)
    (fun H => c * partition c (fun i => F i A) I *
      gibbs_average c (fun i => F i A) I (fun i => D i H)).
Proof.
  intros HI HF.
  assert (HZ : partition c (fun i => F i A) I <> 0).
  { pose proof (partition_positive c (fun i => F i A) I HI); lra. }
  have HP : is_diff A ((fun M => partition c (fun i => F i M) I) : E -> R^o)
      (fun H => finite_sum (fun i => exp (c * F i A) * (c * D i H)) I).
  { unfold partition; apply matrix_gibbs_sum_frechet.
    intros i Hi; apply matrix_gibbs_exp_frechet, HF; exact Hi. }
  apply: (is_diff_eq HP).
  apply: funext => H.
  change (finite_sum (fun i => exp (c * F i A) * (c * D i H)) I =
    c * partition c (fun i => F i A) I *
      gibbs_average c (fun i => F i A) I (fun i => D i H)).
  transitivity (c * finite_sum (fun i => exp (c * F i A) * D i H) I).
  - rewrite <- gibbs_sum_scale; apply gibbs_sum_ext; intros; ring.
  - rewrite gibbs_average_ratio; field; exact HZ.
Qed.

Theorem matrix_gibbs_weight_frechet {E : normedModType R}
    c (F D : nat -> E -> R) I (A : E) i :
  I <> [] -> In i I ->
  (forall j, In j I -> is_diff A (F j : E -> R^o) (D j)) ->
  is_diff A ((fun M => gibbs_weight c (fun j => F j M) I i) : E -> R^o)
    (fun H => c * gibbs_weight c (fun j => F j A) I i *
      (D i H - gibbs_average c (fun j => F j A) I (fun j => D j H))).
Proof.
  intros HI Hi HF.
  assert (HZ : partition c (fun j => F j A) I <> 0).
  { pose proof (partition_positive c (fun j => F j A) I HI); lra. }
  have HQ := matrix_quotient_frechet
    (fun M => exp (c * F i M)) (fun M => partition c (fun j => F j M) I) _ _ A
    HZ (matrix_gibbs_exp_frechet c (F i) (D i) A (HF i Hi))
    (matrix_partition_frechet c F D I A HI HF).
  unfold gibbs_weight; apply: (is_diff_eq HQ).
  apply: funext => H.
  change ((exp (c * F i A) * (c * D i H) * partition c (fun j => F j A) I -
      exp (c * F i A) * (c * partition c (fun j => F j A) I *
        gibbs_average c (fun j => F j A) I (fun j => D j H))) /
      (partition c (fun j => F j A) I) ^ 2 =
    c * (exp (c * F i A) / partition c (fun j => F j A) I) *
      (D i H - gibbs_average c (fun j => F j A) I (fun j => D j H))).
  field; exact HZ.
Qed.

(* Both the scores and observables vary over the whole normed space. *)
Theorem gibbs_average_frechet {E : normedModType R}
    c (F DF U DU : nat -> E -> R) I (A : E) :
  I <> [] ->
  (forall i, In i I -> is_diff A (F i : E -> R^o) (DF i)) ->
  (forall i, In i I -> is_diff A (U i : E -> R^o) (DU i)) ->
  is_diff A
    ((fun M => gibbs_average c (fun i => F i M) I (fun i => U i M)) : E -> R^o)
    (fun H =>
      gibbs_average c (fun i => F i A) I (fun i => DU i H) +
      c * gibbs_covariance c (fun i => F i A) I (fun i => U i A) (fun i => DF i H)).
Proof.
  intros HI HF HU.
  have HS : is_diff A
      ((fun M => finite_sum (fun i =>
        gibbs_weight c (fun j => F j M) I i * U i M) I) : E -> R^o)
      (fun H => finite_sum (fun i =>
        (c * gibbs_weight c (fun j => F j A) I i *
          (DF i H - gibbs_average c (fun j => F j A) I (fun j => DF j H))) * U i A +
        gibbs_weight c (fun j => F j A) I i * DU i H) I).
  { apply (matrix_gibbs_sum_frechet
      (fun i M => gibbs_weight c (fun j => F j M) I i * U i M)); intros i Hi.
    apply (matrix_second_mult_frechet
      (fun M => gibbs_weight c (fun j => F j M) I i) (U i)).
    + apply (matrix_gibbs_weight_frechet c F DF I A i); assumption.
    + apply HU; exact Hi. }
  unfold gibbs_average at 1; apply: (is_diff_eq HS).
  apply: funext => H.
  change (finite_sum (fun i =>
      (c * gibbs_weight c (fun j => F j A) I i *
        (DF i H - gibbs_average c (fun j => F j A) I (fun j => DF j H))) * U i A +
       gibbs_weight c (fun j => F j A) I i * DU i H) I =
    gibbs_average c (fun i => F i A) I (fun i => DU i H) +
    c * gibbs_covariance c (fun i => F i A) I (fun i => U i A) (fun i => DF i H)).
  transitivity (finite_sum (fun i =>
    gibbs_weight c (fun j => F j A) I i * DU i H +
    c * (gibbs_weight c (fun j => F j A) I i * (U i A * DF i H)) +
    (- c * gibbs_average c (fun j => F j A) I (fun j => DF j H)) *
      (gibbs_weight c (fun j => F j A) I i * U i A)) I).
  - apply gibbs_sum_ext; intros; ring.
  - rewrite !gibbs_sum_add !gibbs_sum_scale.
    unfold gibbs_covariance, gibbs_average; ring.
Qed.

Theorem matrix_inner_derivative_frechet n gamma offset coeff S (A U : matrix n) y :
  S <> [] ->
  is_diff A
    ((fun M => matrix_inner_derivative n gamma offset coeff S M U y)
      : matrix n -> R^o)
    (fun V => gamma * matrix_inner_covariance n gamma offset coeff S A U V y).
Proof.
  intros HS.
  pose proof (gibbs_average_frechet gamma
    (fun s M => matrix_affine_scores n offset coeff M y s)
    (fun s V => trace_pair n (coeff y s) V)
    (fun s (_ : matrix n) => trace_pair n (coeff y s) U)
    (fun (_ : nat) (_ : matrix n) => 0) S A HS) as HD.
  assert (HF : forall s, In s S ->
    is_diff A
      ((fun M => matrix_affine_scores n offset coeff M y s) : matrix n -> R^o)
      (fun V => trace_pair n (coeff y s) V)).
  { intros; apply matrix_affine_score_frechet. }
  assert (HU : forall s, In s S ->
    is_diff A ((fun _ : matrix n => trace_pair n (coeff y s) U) : matrix n -> R^o)
      (fun _ : matrix n => 0)).
  { intros s Hs; exact (is_diff_cst (trace_pair n (coeff y s) U : R^o) A). }
  specialize (HD HF HU).
  unfold matrix_inner_derivative, matrix_inner_covariance.
  apply: (is_diff_eq HD).
  apply: funext => V.
  change (gibbs_average gamma (matrix_affine_scores n offset coeff A y) S (fun _ => 0) +
    gamma * gibbs_covariance gamma (matrix_affine_scores n offset coeff A y) S
    (fun s => trace_pair n (coeff y s) U) (fun s => trace_pair n (coeff y s) V) =
    gamma * gibbs_covariance gamma (matrix_affine_scores n offset coeff A y) S
    (fun s => trace_pair n (coeff y s) U) (fun s => trace_pair n (coeff y s) V)).
  rewrite (gibbs_average_const _ _ _ _ HS); ring.
Qed.

Theorem matrix_nested_derivative_frechet n beta gamma offset coeff Y S (A U : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  is_diff A
    ((fun M => matrix_nested_derivative n beta gamma offset coeff Y S M U)
      : matrix n -> R^o)
    (matrix_nested_second_derivative n beta gamma offset coeff Y S A U).
Proof.
  intros Hb Hg HY HS.
  pose proof (gibbs_average_frechet (- beta)
    (fun y M => matrix_inner_values n gamma offset coeff S M y)
    (fun y V => matrix_inner_derivative n gamma offset coeff S A V y)
    (fun y M => matrix_inner_derivative n gamma offset coeff S M U y)
    (fun y V => gamma * matrix_inner_covariance n gamma offset coeff S A U V y)
    Y A HY) as HD.
  assert (HF : forall y, In y Y ->
    is_diff A
      ((fun M => matrix_inner_values n gamma offset coeff S M y) : matrix n -> R^o)
      (fun V => matrix_inner_derivative n gamma offset coeff S A V y)).
  { intros; apply matrix_inner_frechet; assumption. }
  assert (HU : forall y, In y Y ->
    is_diff A
      ((fun M => matrix_inner_derivative n gamma offset coeff S M U y)
        : matrix n -> R^o)
      (fun V => gamma * matrix_inner_covariance n gamma offset coeff S A U V y)).
  { intros; apply matrix_inner_derivative_frechet; exact HS. }
  specialize (HD HF HU).
  unfold matrix_nested_derivative.
  apply: (is_diff_eq HD).
  apply: funext => V.
  change (gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (fun y => gamma * matrix_inner_covariance n gamma offset coeff S A U V y) +
    - beta * gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (matrix_inner_derivative n gamma offset coeff S A U)
      (fun y => matrix_inner_derivative n gamma offset coeff S A V y) =
    matrix_nested_second_derivative n beta gamma offset coeff Y S A U V).
  unfold matrix_nested_second_derivative.
  rewrite gibbs_average_scale -Ropp_mult_distr_l; reflexivity.
Qed.

Lemma matrix_gibbs_covariance_symmetric c f I u v :
  gibbs_covariance c f I u v = gibbs_covariance c f I v u.
Proof.
  unfold gibbs_covariance.
  assert (HE : gibbs_average c f I (fun i => u i * v i) =
    gibbs_average c f I (fun i => v i * u i)).
  { apply gibbs_average_ext; intros; ring. }
  rewrite HE; ring.
Qed.

Theorem matrix_inner_covariance_symmetric n gamma offset coeff S (A U V : matrix n) y :
  matrix_inner_covariance n gamma offset coeff S A U V y =
  matrix_inner_covariance n gamma offset coeff S A V U y.
Proof. unfold matrix_inner_covariance; apply matrix_gibbs_covariance_symmetric. Qed.

Theorem matrix_nested_second_symmetric n beta gamma offset coeff Y S (A U V : matrix n) :
  matrix_nested_second_derivative n beta gamma offset coeff Y S A U V =
  matrix_nested_second_derivative n beta gamma offset coeff Y S A V U.
Proof.
  unfold matrix_nested_second_derivative.
  rewrite (matrix_gibbs_covariance_symmetric (- beta)
    (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_derivative n gamma offset coeff S A U)
    (matrix_inner_derivative n gamma offset coeff S A V)).
  f_equal; f_equal; apply gibbs_average_ext; intros; apply matrix_inner_covariance_symmetric.
Qed.
