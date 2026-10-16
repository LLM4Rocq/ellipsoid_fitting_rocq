(* Assembly of the explicit S7 proposition from the exact sign laws and
   the existing Gaussian and symmetric-mixture fitting consequences. *)
From mathcomp Require Import all_ssreflect_compat.
From GaussianAnalysis.probability Require Import symmetric_shift.
From EllipsoidUniversality Require Import ShiftedSignStatement.
From EllipsoidUniversality.Shifted Require Import SignMixture MixtureSign.

Theorem shifted_sign_theorem : shifted_sign_statement.
Proof.
split.
- move=> F d n P m w hw A symP mA.
  exact: symmetric_sign_shift_outer symP mA.
- move=> d n P m w hw symP; split.
  + exact: sign_mixture_psd_probability symP.
  + exact: sign_mixture_pd_probability symP.
  + move=> C; exact: sign_mixture_conditioned_probability symP.
  + move=> A mA; exact: sign_mixture_condition_number_law symP mA.
  + move=> A mA; exact: sign_mixture_fitting_error_law symP mA.
- split; first exact: gaussian_sign_condition_threshold.
  split; first exact: gaussian_sign_optimal_tail.
  split; first exact: gaussian_sign_arbitrary_shift_exists.
  split; first exact: gaussian_sign_error_limit.
  split; first exact: gaussian_sign_arbitrary_shift_condition_bounds.
  exact: gaussian_sign_psd_nonexistence.
- split; first exact: finite_sign_psd_nonexistence.
  split; first exact: countable_sign_psd_nonexistence.
  split; first exact: finite_sign_sparse_pd.
  exact: countable_sign_sparse_pd.
Qed.
