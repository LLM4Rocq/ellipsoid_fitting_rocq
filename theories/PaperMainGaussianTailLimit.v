(* Stability of nonnegative Gaussian moment bounds under pointwise limits.
   These closure lemmas do not assert existence of smooth approximations. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope classical_set_scope.
Open Scope ring_scope.
Local Open Scope ereal_scope.

Lemma paper_main_limn_einf_bound (u : nat -> \bar R) (C : \bar R) :
  (forall n, u n <= C) -> limn_einf u <= C.
Proof.
move=> Hu; rewrite limn_einf_lim.
apply: lime_le; first exact: is_cvg_einfs.
apply: nearW => n.
apply: le_trans _ (Hu n).
apply: ereal_inf_lbound.
by exists n => //=.
Qed.

Lemma paper_main_nonnegative_integral_limit_bound d (T : measurableType d)
    (mu : {measure set T -> \bar R}) (f : nat -> T -> \bar R)
    (g : T -> \bar R) (C : \bar R) :
  (forall n, measurable_fun setT (f n)) ->
  (forall n x, 0 <= f n x) ->
  (forall x, f^~ x @ \oo --> g x) ->
  (forall n, \int[mu]_x f n x <= C) ->
  \int[mu]_x g x <= C.
Proof.
move=> mf f0 Hc HB.
have Hfat := @fatou d T R mu setT measurableT f mf (fun n x _ => f0 n x).
have HE : (\int[mu]_x limn_einf (f^~ x)) = \int[mu]_x g x.
  apply: eq_integral => x _.
  exact: (cvg_limn_einf_sup (Hc x)).1.
rewrite HE in Hfat.
apply: le_trans Hfat _.
exact: paper_main_limn_einf_bound.
Qed.

Lemma paper_main_centered_exponential_cvg (f a : nat -> R) (x b t : R) :
  f @ \oo --> x -> a @ \oo --> b ->
  (fun n => (expR (t * (f n - a n))%R)%:E) @ \oo -->
    (expR (t * (x - b))%R)%:E.
Proof.
move=> Hf Ha; apply/fine_cvgP; split.
- by apply: nearW => n.
- change ((expR \o (fun n => (t * (f n - a n))%R)) @ \oo -->
    expR (t * (x - b))%R).
  apply: (cvg_comp _ expR); last exact: continuous_expR.
  apply: cvgM; first exact: cvg_cst.
  exact: cvgB.
Qed.

Lemma paper_main_centered_exponential_measurable d (T : measurableType d)
    (f : T -> measurableTypeR R) (a t : R) :
  measurable_fun setT f ->
  measurable_fun setT (fun x => (expR (t * (f x - a))%R)%:E).
Proof.
move=> mf; apply/measurable_EFinP.
apply: (@measurableT_comp _ _ _ T (R : realType) (R : realType)
  (@expR (R : realType)) setT (fun x : T => (t * (f x - a))%R)).
- exact: measurable_expR.
- apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_funB => //; exact: measurable_cst.
Qed.

Theorem paper_main_centered_exponential_limit_bound d (T : measurableType d)
    (mu : {measure set T -> \bar R}) (f : nat -> T -> measurableTypeR R)
    (g : T -> measurableTypeR R) (a : nat -> R) (b t : R) (C : \bar R) :
  (forall n, measurable_fun setT (f n)) ->
  (forall x, f^~ x @ \oo --> g x) -> a @ \oo --> b ->
  (forall n, \int[mu]_x (expR (t * (f n x - a n))%R)%:E <= C) ->
  \int[mu]_x (expR (t * (g x - b))%R)%:E <= C.
Proof.
move=> mf Hf Ha HB.
apply: (@paper_main_nonnegative_integral_limit_bound d T mu
  (fun n x => (expR (t * (f n x - a n))%R)%:E)
  (fun x => (expR (t * (g x - b))%R)%:E) C).
- move=> n; exact: paper_main_centered_exponential_measurable.
- by move=> n x; rewrite lee_fin expR_ge0.
- move=> x; exact: paper_main_centered_exponential_cvg.
- exact HB.
Qed.
