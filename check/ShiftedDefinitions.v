(* The project definitions that the frozen statements of the shifted
   Gaussian proof unfold to, characterized by properties that determine
   them (the freeze of the seven statement files, 16 October 2026).

   The seven files extension/Shifted<X>Statement.v, X = Condition,
   Gaussian, Quadric, Error, MixtureUnsat, MixtureSat and Sign, are frozen:
   scripts/check_sources.py compares their code with the acceptance commit
   51c2e14 (SHIFTED_BASELINE), and this fixes their own statement
   definitions. The statements also unfold to definitions of other files,
   which a change could alter without touching the statement files. This
   file protects those that no other check protects.

   Each lemma states a property written out in this file, down to the
   definitions of MathComp, MathComp-Analysis and Stdlib, to the constants
   of frozen files, to the pinned section tuple_prod of
   library/probability/lindeberg.v, to the definitions that
   check/ApplicationsDefinitions.v characterizes (here mxdot, frobenius and
   the measurable structure of matrices), and to the definitions
   characterized earlier in this file. Each lemma is proved by computation
   (by []). So make check fails as soon as a definition no longer computes
   to the text written here: after a change of its meaning, and also after
   a change of its implementation that keeps the meaning but not the
   computation. make check compiles the file into
   build/shifted_definitions.txt. scripts/check_sources.py fixes the code
   of this file (SHIFTED_DEFINITIONS_CHECK) and requires that output.

   The protected definitions, in the order of the lemmas:
   - family_sequence_limit (library/analysis/family_reindexing.v): u d
     tends to a: for every eps > 0, |u d - a| < eps for all large d.
   - coordinate_support (library/matrix/coordinate_blocks.v): the set of
     the indices i with m_i <> 0.
   - quadric_eval (library/matrix/quadric_certificate.v): the value
     <x, Q x> + <v, x> + c of a quadric at x.
   - tuple_map (library/probability/tuple_rows.v): the tuple of the
     g i (x_i).
   - mixture_weights (library/probability/mixture.v): w i >= 0 for every i,
     and the w i sum to 1.
   - mixture (library/probability/mixture.v): the probability
     A |-> sum_i w i P i (A).
   - cmixture_weights (library/probability/countable_mixture.v): p s >= 0
     for every s, and the series of the p s is 1.
   - cmixture (library/probability/countable_mixture.v): the probability
     A |-> sum_(s < oo) p s P s (A).
   - row_symmetric_law (library/probability/symmetric_shift.v):
     P (-A) = P (A) for every measurable set A of row vectors.
   - row_shift (library/probability/symmetric_shift.v): the measurable map
     x |-> x + m.
   - row_shift_law (library/probability/symmetric_shift.v): the law of
     X + m for X of law P.
   - sign_shift_weights (library/probability/symmetric_shift.v): w for the
     sign true, 1 - w for the sign false.
   - sign_shift_law (library/probability/symmetric_shift.v): w times the
     law of X + m plus 1 - w times the law of X - m.
   - row_outer (library/probability/symmetric_shift.v): the measurable map
     x |-> x^T x.
   - row_of_tuple (theories/Gaussian/Law/LibraryBridge.v): the row vector
     of the coordinates of a tuple.
   - point_law (extension/Sat/AprioriSparse.v): the law of that row vector
     when the tuple has law tuple_prod nu d.
   - sample_row_tuple (extension/Shifted/GaussianRows.v): the tuple of the
     n rows (paper_main_point x i)^T of a flat sample x.
   - sample_flat_row, sample_flat_col (extension/Shifted/GaussianRows.v):
     the row k / d and the column k mod d of the flat index k. An ordinal
     is determined by its value.
   - sample_of_row_tuple (extension/Shifted/GaussianRows.v): the flat
     sample whose entry k is the entry (k / d, k mod d) of a row tuple.
   - sample_translate (extension/Shifted/Translations.v): the flat sample
     whose rows are the rows of x plus m^T.
   - translation_fitting_error (extension/Shifted/TranslationError.v): the
     infimum over all translations m of the frozen
     universality_fitting_error of the translated sample.
   - gaussian_small_shift (extension/Shifted/GaussianCondition.v):
     |m d| <= e sqrt d for all large d, for every e > 0.
   - finite_row_law (extension/Shifted/MixtureRows.v): the mixture of the
     point laws of the components mu d s with the weights w d s, s < N d.
   - countable_row_law (extension/Shifted/MixtureRows.v): the countable
     mixture of the point laws of the mu d s with the weights w d s.
   - row_sample_map (extension/Shifted/SignMixture.v): the measurable map
     sample_of_row_tuple.
   - iid_row_sample_law (extension/Shifted/SignMixture.v): the law of the
     flat sample of n independent rows of law P.
   - shifted_iid_sample_law (extension/Shifted/SignMixture.v): the same
     with rows of law row_shift_law P m^T.
   - sign_mixture_sample_law (extension/Shifted/SignMixture.v): the same
     with rows of law sign_shift_law P m^T hw.

   The packed laws and maps. For a law, the lemma gives the value of the
   measure on every set; for a map, the value of the function. This fixes
   the generated constants they are built from in the way
   matrix_measurable_characterization of check/ApplicationsDefinitions.v
   fixes the measurable structure of matrices: the function of each
   canonical instance is fixed, and its class holds only proofs of
   propositions about that function (that it is a content, a measure,
   s-finite, sigma-finite, finite, of total mass at most 1 and of total
   mass 1, or that it is measurable). The function determines what these
   propositions say, and the values that the statements read depend only
   on the function.
   - mixture_characterization states the value through the canonical
     instance mixture_mixture__canonical__probability_measure_Probability
     of library/probability/mixture.v. This fixes that instance, its
     mixins HB_unnamed_mixin_4, 5 and 12 to 16, its factories
     HB_unnamed_factory_1 and 6, and the Let subproofs that they use:
     w0_subproof, mixture0_subproof, mixture_ge0_subproof,
     mixture_sigma_additive_subproof and mixture_setT_subproof.
     finite_row_law and sign_shift_law are read through this instance.
   - cmixture_characterization fixes in the same way the instance
     countable_mixture_cmixture__canonical__probability_measure_Probability
     of library/probability/countable_mixture.v, its mixins
     HB_unnamed_mixin_4, 5 and 12 to 16, its factories
     HB_unnamed_factory_1 and 6, and its Let subproofs p0_subproof,
     cmixture_mseries_subproof, cmixture0_subproof, cmixture_ge0_subproof,
     cmixture_sigma_additive_subproof and cmixture_setT_subproof.
     countable_row_law is read through it.
   - point_law_characterization computes the law of a point through the
     canonical instance
     LibraryBridge_row_of_tuple__canonical__measurable_function_MeasurableFun
     of theories/Gaussian/Law/LibraryBridge.v, so it fixes that instance
     and its factory HB_unnamed_factory_1.
   - row_shift, row_outer and row_sample_map are packed in place by
     HB.pack: no constant is generated for them.
   - point_law, row_shift_law and the laws of SignMixture.v are
     pushforwards (distribution of MathComp-Analysis), read through the
     canonical instance of distribution.

   The opaque lemmas used as proof arguments are not characterized. They
   are propositions, so their proofs cannot change any value, and their
   statements are fixed through the characterized definitions that use
   them: sample_flat_row_bound and sample_flat_col_bound (k / d < n and
   k mod d < d, in sample_flat_row and sample_flat_col),
   measurable_sample_of_row_tuple (row_sample_map), finite_row_weights and
   countable_row_weights (finite_row_law and countable_row_law),
   measurable_row_shift (row_shift), sign_shift_weightsP (sign_shift_law),
   measurable_row_outer (row_outer) and measurable_row_of_tuple (the
   instance of row_of_tuple). Ten more constants are reached only inside
   opaque proofs, so they cannot change a statement:
   sample_flat_dimension_pos, mixture_weights_ge0, mixture_weights_sum, and
   measurable_mxentry, measurable_fun_mxP, measurable_row_mx,
   measurable_trmx, measurable_const_mx, measurable_addmx and
   measurable_mulmx of library/gaussian/measurable_matrix.v.

   Protected elsewhere: the constants of the frozen files, tuple_prod
   (the pinned section), and mxdot, frobenius, psdmx, gauss and the
   measurable structure of matrices (check/ApplicationsDefinitions.v).
   The four helpers of library/gaussian/gauss.v that the statements reach,
   rV_cons, measurable_rV_cons, and the factory and canonical instance of
   the measurable function rV_cons, matter only through gauss, whose values
   on measurable sets gauss_characterization and gauss_determined fix.
   measure_matrix_display, the display tag of the measurable structure of
   matrices, is an opaque label with no measure content.

   Imports. The modules of the characterized definitions are required
   without Import, and the lemmas name these definitions by their full
   names, so that a short name of another module cannot stand for one of
   them. The three Import commands bring in canonical structures only
   (Import (canonicals)), no name, because elaboration needs them:
   - GaussianAnalysis.gaussian.measurable_matrix: the measurable structure
     of matrices, to read 'rV[R]_d as a measurable type, as in
     probability 'rV[R]_d R and measurable A for A : set 'rV[R]_d;
     check/ApplicationsDefinitions.v characterizes it;
   - GaussianAnalysis.probability.mixture and
     GaussianAnalysis.probability.countable_mixture: the canonical
     probability instances of mixture and cmixture, to read mixture P hw,
     cmixture P hp and sign_shift_law P m hw as probabilities, as the
     statements do.
   boolp is not imported. The report then gives the axioms of boolp under
   their qualified names, such as boolp.propositional_extensionality,
   which are the names of check/sat_variance_assumptions.expected.

   The file ends with shifted_characterizations, the tuple of the 29
   lemmas, and prints its axioms: one complete report.
   scripts/check_sources.py requires them to be among the seven of
   check/sat_variance_assumptions.expected. The proofs, by computation,
   add no axiom. The axioms come from the definitions that the lemmas
   state: the three axioms of boolp, through MathComp-Analysis, and
   ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
   FunctionalExtensionality.functional_extensionality_dep and
   Epsilon.epsilon_statement, through Stdlib's reals. *)

From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import classical_sets reals Rstruct.
From mathcomp Require Import ereal topology sequences measure lebesgue_measure.
From mathcomp Require Import probability.
Require GaussianAnalysis.gaussian.measurable_matrix.
Require GaussianAnalysis.analysis.family_reindexing.
Require GaussianAnalysis.matrix.euclidean.
Require GaussianAnalysis.matrix.coordinate_blocks.
Require GaussianAnalysis.matrix.quadric_certificate.
Require GaussianAnalysis.probability.lindeberg.
Require GaussianAnalysis.probability.tuple_rows.
Require GaussianAnalysis.probability.mixture.
Require GaussianAnalysis.probability.countable_mixture.
Require GaussianAnalysis.probability.symmetric_shift.
Require EllipsoidFitting.PaperMainDefinitions.
Require EllipsoidFitting.Gaussian.Law.LibraryBridge.
Require EllipsoidUniversality.UniversalityDefinitions.
Require EllipsoidUniversality.MixtureDefinitions.
Require EllipsoidUniversality.CountableMixtureDefinitions.
Require EllipsoidUniversality.Sat.AprioriSparse.
Require EllipsoidUniversality.Shifted.GaussianRows.
Require EllipsoidUniversality.Shifted.Translations.
Require EllipsoidUniversality.Shifted.TranslationError.
Require EllipsoidUniversality.Shifted.GaussianCondition.
Require EllipsoidUniversality.Shifted.MixtureRows.
Require EllipsoidUniversality.Shifted.SignMixture.
Import (canonicals) GaussianAnalysis.gaussian.measurable_matrix.
Import (canonicals) GaussianAnalysis.probability.mixture.
Import (canonicals) GaussianAnalysis.probability.countable_mixture.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Notation RR := (R : realType).

(* The library definitions, over any realType R. *)

Lemma family_sequence_limit_characterization (R : realType) (u : nat -> R)
    (a : R) :
  GaussianAnalysis.analysis.family_reindexing.family_sequence_limit u a <->
  forall eps : R, 0 < eps ->
    exists D : nat, forall d : nat, (D <= d)%N -> `|u d - a| < eps.
Proof. by []. Qed.

Lemma coordinate_support_characterization (R : realType) (d : nat)
    (m : 'cV[R]_d) :
  GaussianAnalysis.matrix.coordinate_blocks.coordinate_support m =
  [set i : 'I_d | m i 0 != 0]%SET.
Proof. by []. Qed.

Lemma quadric_eval_characterization (R : realType) (n : nat) (Q : 'M[R]_n)
    (v : 'cV[R]_n) (c : R) (x : 'cV[R]_n) :
  GaussianAnalysis.matrix.quadric_certificate.quadric_eval Q v c x =
  GaussianAnalysis.matrix.euclidean.mxdot x (Q *m x) +
    GaussianAnalysis.matrix.euclidean.mxdot v x + c.
Proof. by []. Qed.

Lemma tuple_map_characterization d d' (T : measurableType d)
    (T' : measurableType d') (g : nat -> T -> T') (n : nat) (x : n.-tuple T) :
  GaussianAnalysis.probability.tuple_rows.tuple_map g x =
  [tuple g i (tnth x i) | i < n].
Proof. by []. Qed.

Lemma mixture_weights_characterization (I : finType) (R : realType)
    (w : I -> R) :
  GaussianAnalysis.probability.mixture.mixture_weights w <->
  (forall i, 0 <= w i) /\ \sum_i w i = 1.
Proof. by []. Qed.

Lemma mixture_characterization d (T : measurableType d) (R : realType)
    (I : finType) (w : I -> R) (P : I -> probability T R)
    (hw : GaussianAnalysis.probability.mixture.mixture_weights w) (A : set T) :
  (GaussianAnalysis.probability.mixture.mixture P hw : probability T R) A =
  (\sum_i (w i)%:E * P i A)%E.
Proof. by []. Qed.

Lemma cmixture_weights_characterization (R : realType) (p : nat -> R) :
  GaussianAnalysis.probability.countable_mixture.cmixture_weights p <->
  (forall s, 0 <= p s) /\ (\sum_(s <oo) (p s)%:E = 1)%E.
Proof. by []. Qed.

Lemma cmixture_characterization d (T : measurableType d) (R : realType)
    (P : nat -> probability T R) (p : nat -> R)
    (hp : GaussianAnalysis.probability.countable_mixture.cmixture_weights p)
    (A : set T) :
  (GaussianAnalysis.probability.countable_mixture.cmixture P hp
    : probability T R) A =
  (\sum_(s <oo) (p s)%:E * P s A)%E.
Proof. by []. Qed.

Lemma row_symmetric_law_characterization (R : realType) (d : nat)
    (P : probability 'rV[R]_d R) :
  GaussianAnalysis.probability.symmetric_shift.row_symmetric_law P <->
  forall A : set 'rV[R]_d, measurable A -> P ((fun x => - x) @^-1` A) = P A.
Proof. by []. Qed.

Lemma row_shift_characterization (R : realType) (d : nat) (m x : 'rV[R]_d) :
  GaussianAnalysis.probability.symmetric_shift.row_shift m x = x + m.
Proof. by []. Qed.

Lemma row_shift_law_characterization (R : realType) (d : nat)
    (P : probability 'rV[R]_d R) (m : 'rV[R]_d) (A : set 'rV[R]_d) :
  (GaussianAnalysis.probability.symmetric_shift.row_shift_law P m
    : probability 'rV[R]_d R) A =
  P [set x | A (x + m)].
Proof. by []. Qed.

Lemma sign_shift_weights_characterization (R : realType) (w : R) (b : bool) :
  GaussianAnalysis.probability.symmetric_shift.sign_shift_weights w b =
  if b then w else 1 - w.
Proof. by []. Qed.

Lemma sign_shift_law_characterization (R : realType) (d : nat)
    (P : probability 'rV[R]_d R) (m : 'rV[R]_d) (w : R) (hw : 0 <= w <= 1)
    (A : set 'rV[R]_d) :
  (GaussianAnalysis.probability.symmetric_shift.sign_shift_law P m hw
    : probability 'rV[R]_d R) A =
  (\sum_(b : bool) (if b then w else 1 - w)%:E *
    P [set x | A (x + if b then m else - m)%R])%E.
Proof. by []. Qed.

Lemma row_outer_characterization (R : realType) (d : nat) (x : 'rV[R]_d) :
  GaussianAnalysis.probability.symmetric_shift.row_outer x = x^T *m x.
Proof. by []. Qed.

(* The definitions of theories/ and extension/, at Stdlib's R. *)

Lemma row_of_tuple_characterization (d : nat)
    (t : d.-tuple (measurableTypeR R)) :
  EllipsoidFitting.Gaussian.Law.LibraryBridge.row_of_tuple d t =
  \row_i (tnth t i : R).
Proof. by []. Qed.

Lemma point_law_characterization (d : nat)
    (nu : nat -> probability (measurableTypeR R) R) (A : set 'rV[RR]_d) :
  EllipsoidUniversality.Sat.AprioriSparse.point_law d nu A =
  GaussianAnalysis.probability.lindeberg.tuple_prod nu d
    [set t | A (\row_i (tnth t i : R))].
Proof. by []. Qed.

Lemma sample_row_tuple_characterization (n d : nat)
    (x : (n * d).-tuple (measurableTypeR R)) :
  @EllipsoidUniversality.Shifted.GaussianRows.sample_row_tuple n d x =
  [tuple (EllipsoidFitting.PaperMainDefinitions.paper_main_point x i)^T
     | i < n].
Proof. by []. Qed.

Lemma sample_flat_row_characterization (n d : nat) (k : 'I_(n * d)) :
  nat_of_ord (@EllipsoidUniversality.Shifted.GaussianRows.sample_flat_row
    n d k) = (k %/ d)%N.
Proof. by []. Qed.

Lemma sample_flat_col_characterization (n d : nat) (k : 'I_(n * d)) :
  nat_of_ord (@EllipsoidUniversality.Shifted.GaussianRows.sample_flat_col
    n d k) = (k %% d)%N.
Proof. by []. Qed.

Lemma sample_of_row_tuple_characterization (n d : nat)
    (x : n.-tuple 'rV[RR]_d) :
  @EllipsoidUniversality.Shifted.GaussianRows.sample_of_row_tuple n d x =
  [tuple tnth x (EllipsoidUniversality.Shifted.GaussianRows.sample_flat_row k)
       0 (EllipsoidUniversality.Shifted.GaussianRows.sample_flat_col k)
     | k < n * d].
Proof. by []. Qed.

Lemma sample_translate_characterization (n d : nat) (m : 'cV[RR]_d)
    (x : (n * d).-tuple (measurableTypeR R)) :
  @EllipsoidUniversality.Shifted.Translations.sample_translate n d m x =
  @EllipsoidUniversality.Shifted.GaussianRows.sample_of_row_tuple n d
    [tuple tnth (EllipsoidUniversality.Shifted.GaussianRows.sample_row_tuple x)
       i + m^T | i < n].
Proof. by []. Qed.

Lemma translation_fitting_error_characterization (n d : nat)
    (x : (n * d).-tuple (measurableTypeR R)) :
  EllipsoidUniversality.Shifted.TranslationError.translation_fitting_error
    n d x =
  inf [set
    EllipsoidUniversality.UniversalityDefinitions.universality_fitting_error n d
      (EllipsoidUniversality.Shifted.Translations.sample_translate m x)
    | m in [set: 'cV[RR]_d]].
Proof. by []. Qed.

Lemma gaussian_small_shift_characterization (m : forall d : nat, 'cV[R]_d) :
  EllipsoidUniversality.Shifted.GaussianCondition.gaussian_small_shift m <->
  forall e : R, 0 < e -> exists D : nat, forall d : nat, (D <= d)%N ->
    GaussianAnalysis.matrix.euclidean.frobenius (m d) <= e * Num.sqrt d%:R.
Proof. by []. Qed.

Lemma finite_row_law_characterization (K : R) (N : nat -> nat)
    (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : EllipsoidUniversality.MixtureDefinitions.mixture_family K N w mu)
    (d : nat) (A : set 'rV[RR]_d) :
  EllipsoidUniversality.Shifted.MixtureRows.finite_row_law hfam d A =
  (\sum_(s < N d) (w d s)%:E *
    EllipsoidUniversality.Sat.AprioriSparse.point_law d (mu d s) A)%E.
Proof. by []. Qed.

Lemma countable_row_law_characterization (K : R) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam :
      EllipsoidUniversality.CountableMixtureDefinitions.countable_mixture_family
        K w mu)
    (d : nat) (A : set 'rV[RR]_d) :
  EllipsoidUniversality.Shifted.MixtureRows.countable_row_law hfam d A =
  (\sum_(s <oo) (w d s)%:E *
    EllipsoidUniversality.Sat.AprioriSparse.point_law d (mu d s) A)%E.
Proof. by []. Qed.

Lemma row_sample_map_characterization (n d : nat) (x : n.-tuple 'rV[RR]_d) :
  EllipsoidUniversality.Shifted.SignMixture.row_sample_map n d x =
  @EllipsoidUniversality.Shifted.GaussianRows.sample_of_row_tuple n d x.
Proof. by []. Qed.

Lemma iid_row_sample_law_characterization (d : nat)
    (P : probability 'rV[RR]_d RR) (n : nat)
    (A : set ((n * d).-tuple (measurableTypeR R))) :
  EllipsoidUniversality.Shifted.SignMixture.iid_row_sample_law P n A =
  GaussianAnalysis.probability.lindeberg.tuple_prod (fun _ => P) n
    (@EllipsoidUniversality.Shifted.GaussianRows.sample_of_row_tuple n d
      @^-1` A).
Proof. by []. Qed.

Lemma shifted_iid_sample_law_characterization (d : nat)
    (P : probability 'rV[RR]_d RR) (m : 'cV[R]_d) (n : nat)
    (A : set ((n * d).-tuple (measurableTypeR R))) :
  EllipsoidUniversality.Shifted.SignMixture.shifted_iid_sample_law P m n A =
  GaussianAnalysis.probability.lindeberg.tuple_prod
    (fun _ => GaussianAnalysis.probability.symmetric_shift.row_shift_law P m^T)
    n
    (@EllipsoidUniversality.Shifted.GaussianRows.sample_of_row_tuple n d
      @^-1` A).
Proof. by []. Qed.

Lemma sign_mixture_sample_law_characterization (d : nat)
    (P : probability 'rV[RR]_d RR) (m : 'cV[R]_d) (w : R) (hw : 0 <= w <= 1)
    (n : nat) (A : set ((n * d).-tuple (measurableTypeR R))) :
  EllipsoidUniversality.Shifted.SignMixture.sign_mixture_sample_law P m hw n A =
  GaussianAnalysis.probability.lindeberg.tuple_prod
    (fun _ =>
      GaussianAnalysis.probability.symmetric_shift.sign_shift_law P m^T hw)
    n
    (@EllipsoidUniversality.Shifted.GaussianRows.sample_of_row_tuple n d
      @^-1` A).
Proof. by []. Qed.

Definition shifted_characterizations :=
  (@family_sequence_limit_characterization,
   @coordinate_support_characterization,
   @quadric_eval_characterization,
   @tuple_map_characterization,
   @mixture_weights_characterization,
   @mixture_characterization,
   @cmixture_weights_characterization,
   @cmixture_characterization,
   @row_symmetric_law_characterization,
   @row_shift_characterization,
   @row_shift_law_characterization,
   @sign_shift_weights_characterization,
   @sign_shift_law_characterization,
   @row_outer_characterization,
   @row_of_tuple_characterization,
   @point_law_characterization,
   @sample_row_tuple_characterization,
   @sample_flat_row_characterization,
   @sample_flat_col_characterization,
   @sample_of_row_tuple_characterization,
   @sample_translate_characterization,
   @translation_fitting_error_characterization,
   @gaussian_small_shift_characterization,
   @finite_row_law_characterization,
   @countable_row_law_characterization,
   @row_sample_map_characterization,
   @iid_row_sample_law_characterization,
   @shifted_iid_sample_law_characterization,
   @sign_mixture_sample_law_characterization).

Print Assumptions shifted_characterizations.
