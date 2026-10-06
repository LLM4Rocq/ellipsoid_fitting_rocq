(* The Gaussian width of the data-dependent head section. Let
   D = paper_main_symmetric_dimension n, z a D-tuple of Gaussian coordinates
   with symmetric Gaussian matrix Z(z) (paper_main_public_symmetric_gaussian),
   and h a head sample of m rows of R^(S n) with features
   W k = paper_main_head_feature h k. The value
     paper_main_head_section_support_value n m kappa h z
       = paper_main_head_support (Z(z)) (paper_main_head_section kappa W)
   satisfies |value| <= |Z(z)|_F = |z| (the Euclidean norm of the
   coordinates), also for empty sections, whose support is 0. For
   kappa >= 1 it is jointly measurable in (h, z)
   (Head.SectionMeasurable). Hence for each h it is integrable
   under gaussian_product_law D, and the width
     paper_main_head_section_width n m kappa h
       = \int value(h, z) d gaussian_product_law D (z)
   is finite with |width h| <= E|z| (paper_main_head_section_width_bound).
   As a function of h it is measurable
   (paper_main_head_section_width_measurable): it is the Tonelli integral
   of the nonnegative jointly measurable function value + |Z|_F, minus the
   constant E|z|. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import Soft.Definitions
  Analysis.CoordinateContinuityDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  Gaussian.ProductLawBasics PaperMainDefinitions Geometry.Psd
  Geometry.HeadFrobenius Geometry.HeadFeature Geometry.HeadWidth Gaussian.Norm
  Gaussian.SmoothLaw Gaussian.FeatureCoordinates Gaussian.SymmetricLawPublic
  Gaussian.ResidualJoint Cone.ApproxSelector Head.SectionMeasurable.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

Definition paper_main_head_section_support_value n m (kappa : R)
    (h : paper_main_sample m (S n)) (z : (paper_main_symmetric_dimension n).-tuple T) : R :=
  paper_main_head_support (paper_main_public_symmetric_gaussian n (tval z))
    (paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k)).

Definition paper_main_head_section_width n m (kappa : R) (h : paper_main_sample m (S n)) :
    \bar R :=
  (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_z
    (paper_main_head_section_support_value n m kappa h z)%:E)%E.

(* The pointwise bound. *)

Lemma paper_main_head_section_value_bound n m (kappa : R) h z :
  `|paper_main_head_section_support_value n m kappa h z| <= paper_main_gaussian_norm (tval z).
Proof.
rewrite -(paper_main_public_symmetric_gaussian_norm n (tval z) (size_tuple z)).
exact: paper_main_head_section_support_bound.
Qed.

(* Measurability in z and jointly in (h, z). *)

Lemma paper_main_head_section_value_measurable n m (kappa : R) (h : paper_main_sample m (S n)) :
  1 <= kappa ->
  measurable_fun [set: (paper_main_symmetric_dimension n).-tuple T]
    ((fun z => paper_main_head_section_support_value n m kappa h z) : _ -> T).
Proof.
move=> Hk.
exact: (paper_main_head_section_support_measurable n m kappa
  (fun k (_ : (paper_main_symmetric_dimension n).-tuple T) => paper_main_head_feature h k)
  (fun z => paper_main_public_symmetric_gaussian n (tval z)) Hk
  (fun k a b => measurable_cst _)
  (paper_main_cone_selector_gaussian_entry_measurable n)).
Qed.

Lemma paper_main_head_section_value_joint_measurable n m (kappa : R) :
  1 <= kappa ->
  measurable_fun [set: paper_main_sample m (S n) * (paper_main_symmetric_dimension n).-tuple T]
    ((fun hz => paper_main_head_section_support_value n m kappa hz.1 hz.2) : _ -> T).
Proof.
move=> Hk.
apply: (paper_main_head_section_support_measurable n m kappa
  (fun k (hz : paper_main_sample m (S n) * (paper_main_symmetric_dimension n).-tuple T) =>
    paper_main_head_feature hz.1 k)
  (fun hz => paper_main_public_symmetric_gaussian n (tval hz.2)) Hk).
- move=> k a b.
  exact: (measurableT_comp (paper_main_gaussian_residual_feature_entry_measurable m (S n) k a b)
    measurable_fst).
- move=> a b.
  exact: (measurableT_comp (paper_main_cone_selector_gaussian_entry_measurable n a b)
    measurable_snd).
Qed.

(* The norm of the Gaussian coordinates. *)

Lemma paper_main_head_section_norm_law n :
  (gaussian_product_law (paper_main_symmetric_dimension n)).-integrable setT
    (fun z => (paper_main_gaussian_norm (tval z))%:E) /\
  (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_z
    (paper_main_gaussian_norm (tval z))%:E =
    (gaussian_iterated_expectation (paper_main_symmetric_dimension n)
      paper_main_gaussian_norm)%:E)%E.
Proof.
exact: (paper_main_gaussian_law_transport _ _ _ _
  (paper_main_gaussian_norm_continuous _) (paper_main_gaussian_norm_polynomial _)).
Qed.

Lemma paper_main_head_section_norm_measurable n :
  measurable_fun [set: (paper_main_symmetric_dimension n).-tuple T]
    ((fun z => paper_main_gaussian_norm (tval z)) : _ -> T).
Proof. exact: (gpp_joint_measurable _ _ (paper_main_gaussian_norm_continuous _)). Qed.

(* Integrability and the bound of the width. *)

Theorem paper_main_head_section_value_integrable n m (kappa : R) h :
  1 <= kappa ->
  (gaussian_product_law (paper_main_symmetric_dimension n)).-integrable setT
    (fun z => (paper_main_head_section_support_value n m kappa h z)%:E).
Proof.
move=> Hk.
have [HI _] := paper_main_head_section_norm_law n.
apply: (le_integrable measurableT _ _ HI).
- apply/measurable_EFinP; exact: (paper_main_head_section_value_measurable n m kappa h Hk).
- move=> z _; rewrite /= lee_fin.
  apply: le_trans (paper_main_head_section_value_bound n m kappa h z) _.
  exact: ler_norm.
Qed.

Theorem paper_main_head_section_width_bound n m (kappa : R) h :
  1 <= kappa ->
  (`|paper_main_head_section_width n m kappa h| <=
    (gaussian_iterated_expectation (paper_main_symmetric_dimension n)
      paper_main_gaussian_norm)%:E)%E.
Proof.
move=> Hk.
have [HI HE] := paper_main_head_section_norm_law n.
rewrite -HE /paper_main_head_section_width.
have mv : measurable_fun [set: (paper_main_symmetric_dimension n).-tuple T]
    (fun z => (paper_main_head_section_support_value n m kappa h z)%:E).
  apply/measurable_EFinP; exact: (paper_main_head_section_value_measurable n m kappa h Hk).
apply: le_trans (le_abse_integral _ measurableT mv) _.
apply: ge0_le_integral => //.
- apply: measurableT_comp mv; exact: abse_measurable.
- apply/measurable_EFinP; exact: (paper_main_head_section_norm_measurable n).
- move=> z _; rewrite /= lee_fin.
  exact: paper_main_head_section_value_bound.
Qed.

Corollary paper_main_head_section_width_fin n m (kappa : R) h :
  1 <= kappa -> paper_main_head_section_width n m kappa h \is a fin_num.
Proof.
move=> Hk.
have Hb := paper_main_head_section_width_bound n m kappa h Hk.
rewrite -abse_fin_num ge0_fin_numE ?abse_ge0 //.
exact: le_lt_trans Hb (ltry _).
Qed.

(* Measurability of the width in the head sample. *)

Theorem paper_main_head_section_width_measurable n m (kappa : R) :
  1 <= kappa ->
  measurable_fun [set: paper_main_sample m (S n)] (paper_main_head_section_width n m kappa).
Proof.
move=> Hk.
set P := gaussian_product_law (paper_main_symmetric_dimension n).
have [HIn HEn] := paper_main_head_section_norm_law n.
pose f := fun hz : paper_main_sample m (S n) * (paper_main_symmetric_dimension n).-tuple T =>
  (paper_main_head_section_support_value n m kappa hz.1 hz.2 +
    paper_main_gaussian_norm (tval hz.2))%:E.
have mf : measurable_fun setT f.
  apply/measurable_EFinP; apply: measurable_funD.
  - exact: paper_main_head_section_value_joint_measurable.
  - exact: (measurableT_comp (paper_main_head_section_norm_measurable n) measurable_snd).
have f0 : forall hz, (0 <= f hz)%E.
  move=> hz; rewrite lee_fin -lerBlDr sub0r.
  have := paper_main_head_section_value_bound n m kappa hz.1 hz.2.
  by rewrite ler_norml => /andP [].
have HT := measurable_fun_fubini_tonelli_F (m2 := P) _ mf f0.
have Heq : paper_main_head_section_width n m kappa =
    (fun h => fubini_F P f h - (gaussian_iterated_expectation (paper_main_symmetric_dimension n)
      paper_main_gaussian_norm)%:E)%E.
  apply: funext => h.
  rewrite /fubini_F /f /paper_main_head_section_width -HEn.
  have Hv := paper_main_head_section_value_integrable n m kappa h Hk.
  have HD0 := integrableD measurableT Hv HIn.
  have HD : (gaussian_product_law (paper_main_symmetric_dimension n)).-integrable setT
      (fun z => (paper_main_head_section_support_value n m kappa h z +
        paper_main_gaussian_norm (tval z))%:E).
    have -> : (fun z => (paper_main_head_section_support_value n m kappa h z +
        paper_main_gaussian_norm (tval z))%:E) =
      (fun z => (paper_main_head_section_support_value n m kappa h z)%:E +
        (paper_main_gaussian_norm (tval z))%:E)%E.
      by apply: funext => z; rewrite EFinD.
    exact: HD0.
  rewrite -(integralB measurableT HD HIn).
  by apply: eq_integral => z _; rewrite /= -EFinB addrK.
by rewrite Heq; apply: emeasurable_funB.
Qed.
