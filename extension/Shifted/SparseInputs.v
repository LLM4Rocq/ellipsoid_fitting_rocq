(* Fit and interpolation inputs along arbitrary cofinal dimensions.
   The constants are chosen before the family and sample-count sequences.
   An explicit admissible baseline supplies dimensions omitted by the
   cofinal map. Repeated dimensions may carry different local families.
   No symmetry, head coordinates, or targets enter the selector. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences esum.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability arithmetic_tactic field_tactic.
From GaussianAnalysis.analysis Require Import family_reindexing.
From GaussianAnalysis.probability Require Import independent_row_signs.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions MixtureStatement MixtureTheorem.
From EllipsoidUniversality Require Import CountableMixtureDefinitions CountableMixtureStatement.
Require Import EllipsoidUniversality.Countable.Theorem.
From EllipsoidUniversality.Gaussian Require Import Threshold.
From EllipsoidUniversality.Shifted Require Import MixtureRows MainMoment ResidualLaws.
From EllipsoidUniversality.Shifted Require Import GaussianExistence ReserveDensity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition sparse_joint_cover n d
    (pi : set (paper_main_sample n d) -> \bar R) (c C eps : R) : Prop :=
  exists E : set (paper_main_sample n d),
    [/\ measurable E, (pi E <= eps%:E)%E &
      forall x, ~ E x ->
        universality_conditioned_fit_event n d c x /\
        mixture_interpolation n d C x].

Record sparse_finite_parameters := SparseFiniteParameters {
  sparse_finite_n : nat;
  sparse_finite_components : nat;
  sparse_finite_weights : nat -> R;
  sparse_finite_laws : nat -> nat -> probability (measurableTypeR R) R
}.

Definition sparse_finite_admissible (K kappa : R) (q : nat)
    (t : sparse_finite_parameters) : Prop :=
  ((forall s, (s < sparse_finite_components t)%N ->
      0 <= sparse_finite_weights t s) /\
    (\sum_(s < sparse_finite_components t) sparse_finite_weights t s = 1) /\
    (forall s j, (s < sparse_finite_components t)%N -> (j < q)%N ->
      mixture_component_law K (sparse_finite_laws t s j))) /\
  (forall j, (j < q)%N ->
    (\sum_(s < sparse_finite_components t) (sparse_finite_weights t s)%:E *
      'E_(sparse_finite_laws t s j)[universality_power 4])%E = kappa%:E).

Definition sparse_finite_probability q (t : sparse_finite_parameters) :=
  mixture_probability (sparse_finite_components t) (sparse_finite_weights t)
    (sparse_finite_laws t) (sparse_finite_n t) q.

Arguments sparse_finite_probability q t : clear implicits.

Record sparse_countable_parameters := SparseCountableParameters {
  sparse_countable_n : nat;
  sparse_countable_weights : nat -> R;
  sparse_countable_laws : nat -> nat -> probability (measurableTypeR R) R
}.

Definition sparse_countable_admissible (K kappa : R) (q : nat)
    (t : sparse_countable_parameters) : Prop :=
  ((forall s, 0 <= sparse_countable_weights t s) /\
    (\sum_(s <oo) (sparse_countable_weights t s)%:E = 1%:E)%E /\
    (forall s j, (j < q)%N ->
      mixture_component_law K (sparse_countable_laws t s j))) /\
  (forall j, (j < q)%N ->
    (\sum_(s <oo) (sparse_countable_weights t s)%:E *
      'E_(sparse_countable_laws t s j)[universality_power 4])%E = kappa%:E).

Definition sparse_countable_probability q (t : sparse_countable_parameters) :=
  countable_mixture_probability (sparse_countable_weights t)
    (sparse_countable_laws t) (sparse_countable_n t) q.

Arguments sparse_countable_probability q t : clear implicits.

Lemma sparse_input_density (n : nat -> nat) (alpha : RR) :
  family_sequence_limit (fun q => (n q)%:R/q%:R^+2 : RR) alpha ->
  universality_density_tends_to n alpha.
Proof.
move=> h eps eps0; have [D hD] := h eps eps0.
exists D => d dD.
rewrite /paper_main_density RdivE.
exact: hD.
Qed.

Lemma sparse_joint_cover_of_probability dT (T : measurableType dT)
    (P : probability T RR) (n d : nat)
    (f : T -> paper_main_sample n d)
    (pi : set (paper_main_sample n d) -> \bar RR) (c C eps : R) :
  measurable_fun [set: T] f ->
  (forall B : set (paper_main_sample n d), measurable B ->
    P (f @^-1` B) = pi B) ->
  measurable (universality_conditioned_fit_event n d c) ->
  (`|pi (universality_conditioned_fit_event n d c) - 1%:E| < (eps/2)%:E)%E ->
  (exists Ei : set (paper_main_sample n d),
    [/\ measurable Ei, (pi Ei <= (eps/2)%:E)%E &
      forall x, ~ Ei x -> mixture_interpolation n d C x]) ->
  sparse_joint_cover pi c C eps.
Proof.
move=> mf law mF closeF [Ei [mEi PEi interp]].
pose F := universality_conditioned_fit_event n d c.
have mPF : measurable (f @^-1` F).
  by rewrite -[X in measurable X]setTI; exact: mf.
have mPEi : measurable (f @^-1` Ei).
  by rewrite -[X in measurable X]setTI; exact: mf.
have closePF : (`|P (f @^-1` F) - 1%:E| < (eps/2)%:E)%E.
  by rewrite (law _ mF).
have PCF : (P (~` (f @^-1` F)) <= (eps/2)%:E)%E.
  exact: gaussian_complement_probability mPF closePF.
have PEE : (P (f @^-1` Ei) <= (eps/2)%:E)%E.
  by rewrite (law _ mEi).
have mU : measurable ((~` F) `|` Ei).
  exact: measurableU (measurableC mF) mEi.
exists ((~` F) `|` Ei); split.
- exact: mU.
- rewrite -(law _ mU).
  change (P ((~` (f @^-1` F)) `|` (f @^-1` Ei)) <= eps%:E)%E.
  apply: le_trans (measureU2 P (measurableC mPF) mPEi) _.
  apply: le_trans (leeD PCF PEE) _.
  rewrite -EFinD lee_fin.
  have -> : eps/2+eps/2 = eps by field.
  exact: lexx.
- move=> x nx; split.
  + apply: contrapT => nF; apply: nx; by left.
  + apply: interp => h; apply: nx; by right.
Qed.


Theorem finite_sparse_input_constants (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
  exists c C : R, [/\ 1 <= c, 0 < C &
    forall base : nat -> sparse_finite_parameters,
      (forall q, sparse_finite_admissible K kappa q (base q)) ->
      family_sequence_limit
        (fun q => (sparse_finite_n (base q))%:R/q%:R^+2 : RR) alpha ->
    forall (p : nat -> nat) (x : nat -> sparse_finite_parameters),
      family_cofinal p ->
      (forall d, sparse_finite_admissible K kappa (p d) (x d)) ->
      family_sequence_limit
        (fun d => (sparse_finite_n (x d))%:R/(p d)%:R^+2 : RR) alpha ->
    forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
      sparse_joint_cover (sparse_finite_probability (p d) (x d)) c C eps].
Proof.
move=> k1 K0 a0 below.
have [hm hi] := mixture_theorem.
have [hsat _ _] := hm kappa K alpha k1 K0 a0.
have [c [c1 [_ [mfit hfit]]]] := hsat below.
have /andP[_ ahalf] := universality_alpha_star_lt kappa k1.
have [C [C0 hinterp]] := hi K alpha K0 a0 (lt_trans below ahalf).
exists c, C; split=> //.
move=> base Ab hb p x hp Ax hx eps eps0.
apply: (@family_eventually_reindex RR (fun _ => sparse_finite_parameters)
  (sparse_finite_admissible K kappa)
  (fun q t => (sparse_finite_n t)%:R/q%:R^+2)
  (fun q t => sparse_joint_cover (sparse_finite_probability q t) c C eps)
  base alpha p x Ab hb _ hp Ax hx).
move=> s As hs.
have hfam : mixture_family K
    (fun q => sparse_finite_components (s q))
    (fun q => sparse_finite_weights (s q))
    (fun q => sparse_finite_laws (s q)) := fun q => (As q).1.
have hfourth : mixture_fourth_moment kappa
    (fun q => sparse_finite_components (s q))
    (fun q => sparse_finite_weights (s q))
    (fun q => sparse_finite_laws (s q)) := fun q => (As q).2.
have hn := sparse_input_density hs.
have [_ hfcvg] := hfit (fun q => sparse_finite_components (s q)) (fun q => sparse_finite_weights (s q)) (fun q => sparse_finite_laws (s q)) hfam hfourth _ hn.
have eps20 : 0 < eps/2 by rewrite divr_gt0.
have [DF hDF] := hfcvg _ eps20.
have [DI hDI] := hinterp (fun q => sparse_finite_components (s q)) (fun q => sparse_finite_weights (s q)) (fun q => sparse_finite_laws (s q)) hfam _ hn _ eps20.
exists (maxn DF DI) => q; rewrite geq_max => /andP[qF qI].
apply: (@sparse_joint_cover_of_probability _ _
  (independent_row_matrix_law (fun=> finite_row_law hfam q)
    (sparse_finite_n (s q))) (sparse_finite_n (s q)) q
  (@matrix_sample (sparse_finite_n (s q)) q)
  (sparse_finite_probability q (s q)) c C eps).
- exact: measurable_matrix_sample.
- move=> B mB; exact: finite_matrix_sample_law mB.
- exact: mfit.
- exact: hDF q qF.
- exact: hDI q qI.
Qed.

Theorem countable_sparse_input_constants (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
  exists c C : R, [/\ 1 <= c, 0 < C &
    forall base : nat -> sparse_countable_parameters,
      (forall q, sparse_countable_admissible K kappa q (base q)) ->
      family_sequence_limit
        (fun q => (sparse_countable_n (base q))%:R/q%:R^+2 : RR) alpha ->
    forall (p : nat -> nat) (x : nat -> sparse_countable_parameters),
      family_cofinal p ->
      (forall d, sparse_countable_admissible K kappa (p d) (x d)) ->
      family_sequence_limit
        (fun d => (sparse_countable_n (x d))%:R/(p d)%:R^+2 : RR) alpha ->
    forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
      sparse_joint_cover (sparse_countable_probability (p d) (x d)) c C eps].
Proof.
move=> k1 K0 a0 below.
have [hm hi] := countable_theorem_holds.
have [hsat _ _] := hm kappa K alpha k1 K0 a0.
have [c [c1 [_ [mfit hfit]]]] := hsat below.
have /andP[_ ahalf] := universality_alpha_star_lt kappa k1.
have [C [C0 hinterp]] := hi K alpha K0 a0 (lt_trans below ahalf).
exists c, C; split=> //.
move=> base Ab hb p x hp Ax hx eps eps0.
apply: (@family_eventually_reindex RR (fun _ => sparse_countable_parameters)
  (sparse_countable_admissible K kappa)
  (fun q t => (sparse_countable_n t)%:R/q%:R^+2)
  (fun q t => sparse_joint_cover (sparse_countable_probability q t) c C eps)
  base alpha p x Ab hb _ hp Ax hx).
move=> s As hs.
have hfam : countable_mixture_family K
    (fun q => sparse_countable_weights (s q))
    (fun q => sparse_countable_laws (s q)) := fun q => (As q).1.
have hfourth : countable_fourth_moment kappa
    (fun q => sparse_countable_weights (s q))
    (fun q => sparse_countable_laws (s q)) := fun q => (As q).2.
have hn := sparse_input_density hs.
have [_ hfcvg] := hfit (fun q => sparse_countable_weights (s q)) (fun q => sparse_countable_laws (s q)) hfam hfourth _ hn.
have eps20 : 0 < eps/2 by rewrite divr_gt0.
have [DF hDF] := hfcvg _ eps20.
have [DI hDI] := hinterp (fun q => sparse_countable_weights (s q)) (fun q => sparse_countable_laws (s q)) hfam _ hn _ eps20.
exists (maxn DF DI) => q; rewrite geq_max => /andP[qF qI].
apply: (@sparse_joint_cover_of_probability _ _
  (independent_row_matrix_law (fun=> countable_row_law hfam q)
    (sparse_countable_n (s q))) (sparse_countable_n (s q)) q
  (@matrix_sample (sparse_countable_n (s q)) q)
  (sparse_countable_probability q (s q)) c C eps).
- exact: measurable_matrix_sample.
- move=> B mB; exact: countable_matrix_sample_law mB.
- exact: mfit.
- exact: hDF q qF.
- exact: hDI q qI.
Qed.

(* Unbundled forms: the baseline uses the original full family and its
   sample-count sequence; candidate laws are required only at p(d). *)
Theorem finite_sparse_inputs (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
  exists c C : R, [/\ 1 <= c, 0 < C &
    forall (N0 : nat -> nat) (w0 : nat -> nat -> R)
      (mu0 : nat -> nat -> nat -> probability (measurableTypeR R) R)
      (n0 : nat -> nat),
    mixture_family K N0 w0 mu0 -> mixture_fourth_moment kappa N0 w0 mu0 ->
    universality_density_tends_to n0 alpha ->
    forall (p n N : nat -> nat) (w : nat -> nat -> R)
      (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
    family_cofinal p ->
    (forall d,
      (forall s, (s < N d)%N -> 0 <= w d s) /\
      (\sum_(s < N d) w d s = 1) /\
      (forall s j, (s < N d)%N -> (j < p d)%N ->
        mixture_component_law K (mu d s j))) ->
    (forall d j, (j < p d)%N ->
      (\sum_(s < N d) (w d s)%:E * 'E_(mu d s j)[universality_power 4])%E =
        kappa%:E) ->
    family_sequence_limit (fun d => (n d)%:R/(p d)%:R^+2 : RR) alpha ->
    forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
      sparse_joint_cover (mixture_probability (N d) (w d) (mu d) (n d) (p d))
        c C eps].
Proof.
move=> k1 K0 a0 below.
have [c [C [c1 C0 h]]] := finite_sparse_input_constants k1 K0 a0 below.
exists c, C; split=> //.
move=> N0 w0 mu0 n0 hfam0 hfourth0 hn0 p n N w mu hp hfam hfourth hn eps eps0.
apply: (h (fun q => SparseFiniteParameters (n0 q) (N0 q) (w0 q) (mu0 q))
  _ (reserve_density_scalar_limit hn0) p
  (fun d => SparseFiniteParameters (n d) (N d) (w d) (mu d)) hp _ hn eps eps0).
- move=> q; split; [exact: hfam0 | exact: hfourth0].
- move=> d; split; [exact: hfam | exact: hfourth].
Qed.

Theorem countable_sparse_inputs (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
  exists c C : R, [/\ 1 <= c, 0 < C &
    forall (w0 : nat -> nat -> R)
      (mu0 : nat -> nat -> nat -> probability (measurableTypeR R) R)
      (n0 : nat -> nat),
    countable_mixture_family K w0 mu0 -> countable_fourth_moment kappa w0 mu0 ->
    universality_density_tends_to n0 alpha ->
    forall (p n : nat -> nat) (w : nat -> nat -> R)
      (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
    family_cofinal p ->
    (forall d,
      (forall s, 0 <= w d s) /\
      (\sum_(s <oo) (w d s)%:E = 1%:E)%E /\
      (forall s j, (j < p d)%N -> mixture_component_law K (mu d s j))) ->
    (forall d j, (j < p d)%N ->
      (\sum_(s <oo) (w d s)%:E * 'E_(mu d s j)[universality_power 4])%E =
        kappa%:E) ->
    family_sequence_limit (fun d => (n d)%:R/(p d)%:R^+2 : RR) alpha ->
    forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
      sparse_joint_cover (countable_mixture_probability (w d) (mu d) (n d) (p d))
        c C eps].
Proof.
move=> k1 K0 a0 below.
have [c [C [c1 C0 h]]] := countable_sparse_input_constants k1 K0 a0 below.
exists c, C; split=> //.
move=> w0 mu0 n0 hfam0 hfourth0 hn0 p n w mu hp hfam hfourth hn eps eps0.
apply: (h (fun q => SparseCountableParameters (n0 q) (w0 q) (mu0 q))
  _ (reserve_density_scalar_limit hn0) p
  (fun d => SparseCountableParameters (n d) (w d) (mu d)) hp _ hn eps eps0).
- move=> q; split; [exact: hfam0 | exact: hfourth0].
- move=> d; split; [exact: hfam | exact: hfourth].
Qed.
