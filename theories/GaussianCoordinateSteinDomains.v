(* Port of theories/GaussianCoordinateSteinDomains.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order
   and its text. The only change to the file is that the import line
   "From Coquelicot Require Import Coquelicot." is dropped: no statement or
   proof here names a Coquelicot notion. The proofs are the original ones,
   word for word.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So (i <= d)%nat is Peano's le, nth is Stdlib's List.nth,
   and the list notations and the operations on R are Stdlib's, as in the
   original. The ported lemmas that the proofs apply write (i < d)%coq_nat
   and List.nth, which elaborate to the same terms.

   The meaning of the statements follows the ported definitions they use.
   finite_joint_continuous (GaussianCoordinateDefinitions) and
   finite_polynomial_bound (GaussianCoordinateWeightDefinitions) have their
   original texts and involve no integral. finite_coordinate_derivative
   (GaussianCoordinateDerivativeDefinitions) says that each coordinate
   section has MathComp's derivative @is_derive R R^o R^o t 1 in place of
   Coquelicot's is_derive; both are the ordinary derivative of a function
   R -> R, so the hypothesis means what it meant.
   gaussian_iterated_integrable, gaussian_iterated_absolutely_integrable,
   gaussian_iterated_has_expectation and gaussian_iterated_expectation
   (GaussianProductDefinitions) now ask at each level for the Lebesgue
   integral over the line against the Gaussian kernel, in place of the
   improper Riemann integral (difference 4 of analysis/README.md). Every
   function in the conclusions is continuous and bounded by a constant times
   a polynomial weight, so it is absolutely integrable against the kernel,
   where the two integrals agree. The conclusions are therefore the Lebesgue
   counterparts of the original ones, under the same hypotheses. That the
   two integrals agree is a mathematical argument and is not proved in
   Rocq. No statement is weakened.

   The proofs use gaussian_iterated_polynomial_admissible (ported
   GaussianCoordinateMarginals), finite_joint_continuous_times_coordinate,
   finite_joint_continuous_times_centered_square and
   finite_joint_continuous_times_two_coordinates (ported
   GaussianCoordinatePolynomialContinuity),
   finite_polynomial_bound_times_coordinate,
   finite_polynomial_bound_times_centered_square and
   finite_polynomial_bound_times_two_coordinates (ported
   GaussianCoordinateWeights), and gaussian_iterated_coordinate_first_stein,
   gaussian_iterated_coordinate_second_stein and
   gaussian_iterated_coordinate_mixed_stein (ported GaussianCoordinateStein).
   Their statements are the original texts, up to the %coq_nat, List.nth and
   derivative notations described above. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCoordinateMarginals GaussianCoordinatePolynomialContinuity
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateStein.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_coordinate_polynomial_domain d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_integrable d F /\ gaussian_iterated_absolutely_integrable d F /\
  gaussian_iterated_has_expectation d F (gaussian_iterated_expectation d F) /\
  gaussian_iterated_has_expectation d (fun xs => Rabs (F xs))
    (gaussian_iterated_expectation d (fun xs => Rabs (F xs))).
Proof.
  intros HC HB.
  destruct (gaussian_iterated_polynomial_admissible d F C p HC HB)
    as [HI [HA [HV [HAV Hbound]]]].
  repeat split; assumption.
Qed.

Theorem gaussian_iterated_coordinate_first_stein_integrable d i F DF C p D q :
  (i <= d)%nat ->
  finite_joint_continuous (S d) F -> finite_joint_continuous (S d) DF ->
  finite_polynomial_bound (S d) C p F -> finite_polynomial_bound (S d) D q DF ->
  finite_coordinate_derivative (S d) i F DF ->
  List.Forall (fun G =>
    gaussian_iterated_integrable (S d) G /\ gaussian_iterated_absolutely_integrable (S d) G /\
    gaussian_iterated_has_expectation (S d) G (gaussian_iterated_expectation (S d) G) /\
    gaussian_iterated_has_expectation (S d) (fun xs => Rabs (G xs))
      (gaussian_iterated_expectation (S d) (fun xs => Rabs (G xs))))
    [F; DF; (fun xs => nth i xs 0 * F xs)] /\
  gaussian_iterated_expectation (S d) DF =
    gaussian_iterated_expectation (S d) (fun xs => nth i xs 0 * F xs).
Proof.
  intros Hi HCF HCDF HF HDF HD; split.
  - constructor.
    + exact (gaussian_coordinate_polynomial_domain (S d) F C p HCF HF).
    + constructor.
      * exact (gaussian_coordinate_polynomial_domain (S d) DF D q HCDF HDF).
      * constructor; [|constructor].
        apply (gaussian_coordinate_polynomial_domain (S d) _ C (S p)).
        -- apply finite_joint_continuous_times_coordinate; [exact HCF|lia].
        -- apply finite_polynomial_bound_times_coordinate; [exact HF|lia].
  - exact (gaussian_iterated_coordinate_first_stein d i F DF C p D q Hi HCF HCDF HF HDF HD).
Qed.

Theorem gaussian_iterated_coordinate_second_stein_integrable d i F DF DDF C p D q E r :
  (i <= d)%nat ->
  finite_joint_continuous (S d) F -> finite_joint_continuous (S d) DF ->
  finite_joint_continuous (S d) DDF ->
  finite_polynomial_bound (S d) C p F -> finite_polynomial_bound (S d) D q DF ->
  finite_polynomial_bound (S d) E r DDF ->
  finite_coordinate_derivative (S d) i F DF -> finite_coordinate_derivative (S d) i DF DDF ->
  List.Forall (fun G =>
    gaussian_iterated_integrable (S d) G /\ gaussian_iterated_absolutely_integrable (S d) G /\
    gaussian_iterated_has_expectation (S d) G (gaussian_iterated_expectation (S d) G) /\
    gaussian_iterated_has_expectation (S d) (fun xs => Rabs (G xs))
      (gaussian_iterated_expectation (S d) (fun xs => Rabs (G xs))))
    [F; DF; DDF; (fun xs => (nth i xs 0*nth i xs 0-1)*F xs)] /\
  gaussian_iterated_expectation (S d) DDF =
    gaussian_iterated_expectation (S d) (fun xs => (nth i xs 0*nth i xs 0-1)*F xs).
Proof.
  intros Hi HCF HCDF HCDDF HF HDF HDDF HD HDD; split.
  - constructor.
    + exact (gaussian_coordinate_polynomial_domain (S d) F C p HCF HF).
    + constructor.
      * exact (gaussian_coordinate_polynomial_domain (S d) DF D q HCDF HDF).
      * constructor.
        -- exact (gaussian_coordinate_polynomial_domain (S d) DDF E r HCDDF HDDF).
        -- constructor; [|constructor].
           apply (gaussian_coordinate_polynomial_domain (S d) _ C (S (S p))).
           ++ apply finite_joint_continuous_times_centered_square; [exact HCF|lia].
           ++ apply finite_polynomial_bound_times_centered_square; [exact HF|lia].
  - exact (gaussian_iterated_coordinate_second_stein d i F DF DDF C p D q E r
      Hi HCF HCDDF HF HDF HDDF HD HDD).
Qed.

Theorem gaussian_iterated_coordinate_mixed_stein_integrable d i j F DFj DFiDFj C p D q E r :
  (i <= d)%nat -> (j <= d)%nat -> i <> j ->
  finite_joint_continuous (S d) F -> finite_joint_continuous (S d) DFj ->
  finite_joint_continuous (S d) DFiDFj ->
  finite_polynomial_bound (S d) C p F -> finite_polynomial_bound (S d) D q DFj ->
  finite_polynomial_bound (S d) E r DFiDFj ->
  finite_coordinate_derivative (S d) j F DFj ->
  finite_coordinate_derivative (S d) i DFj DFiDFj ->
  List.Forall (fun G =>
    gaussian_iterated_integrable (S d) G /\ gaussian_iterated_absolutely_integrable (S d) G /\
    gaussian_iterated_has_expectation (S d) G (gaussian_iterated_expectation (S d) G) /\
    gaussian_iterated_has_expectation (S d) (fun xs => Rabs (G xs))
      (gaussian_iterated_expectation (S d) (fun xs => Rabs (G xs))))
    [F; DFj; DFiDFj; (fun xs => nth i xs 0*F xs); (fun xs => nth i xs 0*DFj xs);
      (fun xs => nth i xs 0*nth j xs 0*F xs)] /\
  gaussian_iterated_expectation (S d) DFiDFj =
    gaussian_iterated_expectation (S d) (fun xs => nth i xs 0*nth j xs 0*F xs).
Proof.
  intros Hi Hj Hij HCF HCj HCij HF HFj HFij HDj HDij; split.
  - constructor.
    + exact (gaussian_coordinate_polynomial_domain (S d) F C p HCF HF).
    + constructor.
      * exact (gaussian_coordinate_polynomial_domain (S d) DFj D q HCj HFj).
      * constructor.
        -- exact (gaussian_coordinate_polynomial_domain (S d) DFiDFj E r HCij HFij).
        -- constructor.
           ++ apply (gaussian_coordinate_polynomial_domain (S d) _ C (S p)).
              ** apply finite_joint_continuous_times_coordinate; [exact HCF|lia].
              ** apply finite_polynomial_bound_times_coordinate; [exact HF|lia].
           ++ constructor.
              ** apply (gaussian_coordinate_polynomial_domain (S d) _ D (S q)).
                 --- apply finite_joint_continuous_times_coordinate; [exact HCj|lia].
                 --- apply finite_polynomial_bound_times_coordinate; [exact HFj|lia].
              ** constructor; [|constructor].
                 apply (gaussian_coordinate_polynomial_domain (S d) _ C (S (S p))).
                 --- apply finite_joint_continuous_times_two_coordinates; [exact HCF|lia|lia].
                 --- apply finite_polynomial_bound_times_two_coordinates; [exact HF|lia|lia].
  - exact (gaussian_iterated_coordinate_mixed_stein d i j F DFj DFiDFj C p D q E r
      Hi Hj Hij HCF HCj HCij HF HFj HFij HDj HDij).
Qed.
