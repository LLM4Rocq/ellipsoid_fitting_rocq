From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import GaussianDefinitions GaussianIntegration
  GaussianProductDefinitions GaussianProduct GaussianLastDefinitions GaussianLastIntegration
  GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianCoordinateMarginals.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/GaussianCoordinateLastStein.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name and its arguments, in the same
   order, and no statement gains or loses a hypothesis. The changes of text
   are the following, and nothing else.

   1. Derivatives. In gaussian_iterated_last_first_stein and
      gaussian_iterated_last_second_stein, Coquelicot's hypothesis
        forall xs, length xs = d -> forall t,
          is_derive (fun u => F (xs++[u])) t (DF (xs++[t]))
      is written
        forall xs : list R, length xs = d -> forall t : R,
          @is_derive R R^o R^o t 1 (fun u => F (xs++[u])%list)
            (DF (xs++[t])%list),
      MathComp's derivative at the point t in the direction 1, on R with
      its own normed module structure R^o (and likewise for DF and DDF).
      Both are the ordinary derivative of a function R -> R: each is
      equivalent to Stdlib's derivable_pt_lim (Coquelicot's is_derive_Reals
      and is_derive_Reals of AnalysisBridge), so the meaning is unchanged.
      This is exactly the conclusion of finite_coordinate_derivative_last in
      the ported GaussianCoordinateDerivatives, which is how the importer
      GaussianCoordinateStein produces these hypotheses. The binders xs and
      t are annotated with list R and R, so that t has type R and not the
      carrier of R^o.

   2. Concatenation and nth. With ssreflect loaded, xs ++ [t] means
      MathComp's cat and nth is MathComp's seq.nth, whose arguments come in
      another order. The statements write (xs ++ [t])%list, which is
      Stdlib's app, and List.nth, as in the original and as in the ported
      GaussianLastDefinitions, GaussianCoordinateTopology and
      GaussianCoordinateDerivatives. length, S and the arithmetic on R are
      Stdlib's.

   Meaning. finite_joint_continuous and finite_polynomial_bound involve no
   integral and mean what they meant. gaussian_iterated_expectation is the
   iterated Gaussian expectation of the ported GaussianProductDefinitions,
   whose one-dimensional expectation is now the Lebesgue integral over the
   line (difference 4 of analysis/README.md). Under the hypotheses of the
   two theorems, every section t |-> F (xs ++ [t]) and every other function
   integrated is continuous and bounded by a constant times a polynomial,
   so it is absolutely integrable against the kernel, where the Lebesgue
   and the improper Riemann integrals agree. The two identities are
   therefore the same statements as before, about the same numbers. This
   agreement is a mathematical argument and is not proved in Rocq.
   gaussian_last_section_scalar_bound involves no integral and is the
   original statement.

   Proofs. The original scripts are kept. They apply gaussian_first_stein
   and gaussian_second_stein of the ported GaussianIntegration, which keep
   the hypotheses of the originals, with the derivative and pointwise
   continuity hypotheses in the forms above, and
   finite_joint_continuous_last_section of the ported
   GaussianCoordinateTopology, whose conclusion is
   forall t : R, {for t, continuous (fun u : R => F (xs ++ [u])%list)}.
   The comma form of rewrite is split in two, since ssreflect's rewrite
   does not accept it. *)

Lemma gaussian_last_section_scalar_bound d F C p xs :
  finite_polynomial_bound (S d) C p F -> length xs = d ->
  forall t, Rabs (F (xs++[t])%list) <=
    (C*gaussian_coordinate_product_weight p xs*2^p)*(1+Rabs t^p).
Proof.
  intros Hb Hxs t.
  eapply Rle_trans; [apply (gaussian_last_section_polynomial_bound d F C p xs Hb Hxs)|].
  replace (C*gaussian_coordinate_product_weight p xs*2^p*(1+Rabs t^p)) with
    ((C*gaussian_coordinate_product_weight p xs)*(2^p*(1+Rabs t^p))) by ring.
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos; [exact (proj1 Hb)|apply gaussian_coordinate_product_weight_nonnegative].
  - apply gaussian_coordinate_weight_polynomial_bound.
Qed.

Theorem gaussian_iterated_last_first_stein d F DF C p D q :
  finite_joint_continuous (S d) DF ->
  finite_polynomial_bound (S d) C p F ->
  finite_polynomial_bound (S d) D q DF ->
  (forall xs : list R, length xs = d -> forall t : R,
    @is_derive R R^o R^o t 1 (fun u => F (xs++[u])%list) (DF (xs++[t])%list)) ->
  gaussian_iterated_expectation (S d) DF =
  gaussian_iterated_expectation (S d) (fun xs => List.nth d xs 0 * F xs).
Proof.
  intros HC HF HDF HD.
  rewrite !gaussian_iterated_last_expectation.
  apply gaussian_iterated_expectation_ext; intros xs Hxs.
  pose proof (gaussian_first_stein (fun t => F (xs++[t])%list) (fun t => DF (xs++[t])%list)
    (C*gaussian_coordinate_product_weight p xs*2^p) p
    (D*gaussian_coordinate_product_weight q xs*2^q) q
    (HD xs Hxs)
    (finite_joint_continuous_last_section d DF xs HC Hxs)
    (gaussian_last_section_scalar_bound d F C p xs HF Hxs)
    (gaussian_last_section_scalar_bound d DF D q xs HDF Hxs)) as HS.
  repeat match type of HS with _ /\ _ => apply proj2 in HS end.
  rename HS into HE.
  unfold gaussian_last_marginal.
  etransitivity; [exact HE|].
  apply (f_equal gaussian_expectation); apply functional_extensionality; intro t.
  rewrite <- Hxs; rewrite nth_middle; reflexivity.
Qed.

Theorem gaussian_iterated_last_second_stein d F DF DDF C p D q E r :
  finite_joint_continuous (S d) DDF ->
  finite_polynomial_bound (S d) C p F ->
  finite_polynomial_bound (S d) D q DF ->
  finite_polynomial_bound (S d) E r DDF ->
  (forall xs : list R, length xs = d -> forall t : R,
    @is_derive R R^o R^o t 1 (fun u => F (xs++[u])%list) (DF (xs++[t])%list)) ->
  (forall xs : list R, length xs = d -> forall t : R,
    @is_derive R R^o R^o t 1 (fun u => DF (xs++[u])%list) (DDF (xs++[t])%list)) ->
  gaussian_iterated_expectation (S d) DDF =
  gaussian_iterated_expectation (S d)
    (fun xs => (List.nth d xs 0*List.nth d xs 0-1)*F xs).
Proof.
  intros HC HF HDF HDDF HD HDD.
  rewrite !gaussian_iterated_last_expectation.
  apply gaussian_iterated_expectation_ext; intros xs Hxs.
  pose proof (gaussian_second_stein (fun t => F (xs++[t])%list)
    (fun t => DF (xs++[t])%list) (fun t => DDF (xs++[t])%list)
    (C*gaussian_coordinate_product_weight p xs*2^p) p
    (D*gaussian_coordinate_product_weight q xs*2^q) q
    (E*gaussian_coordinate_product_weight r xs*2^r) r
    (HD xs Hxs) (HDD xs Hxs)
    (finite_joint_continuous_last_section d DDF xs HC Hxs)
    (gaussian_last_section_scalar_bound d F C p xs HF Hxs)
    (gaussian_last_section_scalar_bound d DF D q xs HDF Hxs)
    (gaussian_last_section_scalar_bound d DDF E r xs HDDF Hxs)) as HS.
  repeat match type of HS with _ /\ _ => apply proj2 in HS end.
  rename HS into HE.
  unfold gaussian_last_marginal.
  etransitivity; [exact HE|].
  apply (f_equal gaussian_expectation); apply functional_extensionality; intro t.
  rewrite <- Hxs; rewrite nth_middle; reflexivity.
Qed.
