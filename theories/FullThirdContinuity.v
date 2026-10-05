From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import GibbsDefinitions ThirdDefinitions LowerDefinitions LowerFrechet
  FullThirdDefinitions FullThirdFrechet FiniteGibbsContinuity MatrixCoordinates.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/FullThirdContinuity.v from Coquelicot to
   MathComp-Analysis.

   The theorem keeps its name and its arguments, in the same order. Its
   statement changes form in three ways, the ways of the ports of
   LowerFrechet and FullThirdFrechet, which this module imports.

   1. Normed spaces. Coquelicot's NormedModule R_AbsRing becomes
      normedModType R.

   2. Linear maps. Coquelicot's is_linear (F z s) is stated, as in
      LowerFrechet and MatrixCoordinates, as the conjunction
        linear (F z s) /\
        exists M : R, 0 < M /\ forall x, (`|F z s x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and Coquelicot's norm bound, with the
      absolute value on R and the norm of E. The map F z s is written with
      codomain R^o, the normed module view of R, where linear needs a module
      structure on the codomain. R^o is R by definition, so the map is the
      same.

   3. Continuity at a point. Coquelicot's continuous f A, continuity of f at
      the point A, becomes MathComp's {for A, continuous f} (difference 5 of
      analysis/README.md). The topology on E is the one of its norm, and the
      topology on R the one of the absolute value, as in Coquelicot.

   So the hypotheses and the conclusion say the same thing as in the
   original. The arithmetic inside lower_third is Stdlib's, as before.

   In the proof, Coquelicot's filterdiff_continuous becomes MathComp's
   differentiable_continuous applied to the field ex_diff of is_diff, and the
   continuity of the linear map F z s, which the original took from
   filterdiff_linear, comes from matrix_linear_continuous of MatrixCoordinates.
   That is why this module imports MatrixCoordinates in addition to the
   imports of the original. continuous_const becomes cst_continuous. *)

Theorem lower_third_continuous {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U V W : E) :
  0 < gamma -> Y <> [] -> S <> [] ->
  (forall z s, In z Y -> In s S ->
    linear (F z s : E -> R^o) /\
    exists M : R, 0 < M /\ forall x : E, (`|F z s x|)%R <= M * (`|x|)%R) ->
  {for A, continuous (fun M => lower_third beta gamma F Y S M U V W)}.
Proof.
  intros Hg HY HS HL.
  assert (HF : forall z, In z Y ->
    {for A, continuous (fun M => lower_inner_value gamma F S M z)}).
  { intros z Hz.
    have H : is_diff A ((fun M => lower_inner_value gamma F S M z) : E -> R^o)
      (fun U => lower_inner_first gamma F S A U z).
    { apply lower_inner_frechet; try assumption; intros; apply HL; assumption. }
    exact (@differentiable_continuous R E R^o A _ (@ex_diff R E R^o _ _ _ _ H)). }
  assert (HM : forall P z, In z Y ->
    {for A, continuous (fun M => lower_inner_first gamma F S M P z)}).
  { intros P z Hz.
    have H : is_diff A ((fun M => lower_inner_first gamma F S M P z) : E -> R^o)
      (fun V => gamma * lower_inner_covariance gamma F S A P V z).
    { apply lower_inner_first_frechet; try assumption; intros; apply HL; assumption. }
    exact (@differentiable_continuous R E R^o A _ (@ex_diff R E R^o _ _ _ _ H)). }
  assert (HC : forall P Q z, In z Y ->
    {for A, continuous (fun M => lower_inner_covariance gamma F S M P Q z)}).
  { intros P Q z Hz.
    have H : is_diff A ((fun M => lower_inner_covariance gamma F S M P Q z) : E -> R^o)
      (fun W => gamma * lower_inner_cumulant gamma F S A P Q W z).
    { apply lower_inner_covariance_frechet; try assumption; intros; apply HL; assumption. }
    exact (@differentiable_continuous R E R^o A _ (@ex_diff R E R^o _ _ _ _ H)). }
  assert (HT : forall z, In z Y ->
    {for A, continuous (fun M => lower_inner_cumulant gamma F S M U V W z)}).
  { intros z Hz; unfold lower_inner_cumulant.
    apply (@gibbs_cumulant3_continuous E gamma (F z)
      (fun s (_ : E) => F z s U) (fun s (_ : E) => F z s V)
      (fun s (_ : E) => F z s W) S A HS).
    - intros s Hs.
      exact (matrix_linear_continuous (F z s : E -> R^o) (HL z s Hz Hs) A).
    - intros s Hs; exact (@cst_continuous E R (F z s U) A).
    - intros s Hs; exact (@cst_continuous E R (F z s V) A).
    - intros s Hs; exact (@cst_continuous E R (F z s W) A). }
  (* Each hypothesis is given by name. The original tries hypotheses on
     goals of other shapes, with try assumption and first [apply HC |
     apply HM]. Here that makes Rocq unfold the Gibbs averages on both
     sides, and the compilation did not finish within five minutes. *)
  have Hcov : forall P Q R' : E,
    {for A, continuous (fun M => gibbs_covariance (- beta)
      (lower_inner_value gamma F S M) Y
      (lower_inner_covariance gamma F S M P Q) (lower_inner_first gamma F S M R'))}.
  { intros P Q R'.
    apply (@gibbs_covariance_continuous E (- beta)
      (fun z M => lower_inner_value gamma F S M z)
      (fun z M => lower_inner_covariance gamma F S M P Q z)
      (fun z M => lower_inner_first gamma F S M R' z) Y A HY HF).
    - intros z Hz; exact (HC P Q z Hz).
    - intros z Hz; exact (HM R' z Hz). }
  unfold lower_third; apply (@continuous_Rplus_fct E).
  - apply (@continuous_Rminus_fct E); apply (@continuous_Rmult_fct E).
    + exact (@cst_continuous E R (gamma ^ 2) A).
    + exact (@gibbs_average_continuous E (- beta)
        (fun z M => lower_inner_value gamma F S M z)
        (fun z M => lower_inner_cumulant gamma F S M U V W z) Y A HY HF HT).
    + exact (@cst_continuous E R (beta * gamma) A).
    + apply (@continuous_Rplus_fct E); [apply (@continuous_Rplus_fct E)|].
      * exact (Hcov U V W).
      * exact (Hcov U W V).
      * exact (Hcov V W U).
  - apply (@continuous_Rmult_fct E).
    + exact (@cst_continuous E R (beta ^ 2) A).
    + apply (@gibbs_cumulant3_continuous E (- beta)
        (fun z M => lower_inner_value gamma F S M z)
        (fun z M => lower_inner_first gamma F S M U z)
        (fun z M => lower_inner_first gamma F S M V z)
        (fun z M => lower_inner_first gamma F S M W z) Y A HY HF).
      * intros z Hz; exact (HM U z Hz).
      * intros z Hz; exact (HM V z Hz).
      * intros z Hz; exact (HM W z Hz).
Qed.
