(* The axiom check of the exact normalization of PSD factors (target T10 of
   phase 13). The file only requires the frozen statement module and the
   theorem module, without Import, and names both by their absolute names,
   so that no name that the theorem module defines can stand for the frozen
   statement. The definition compiles only if psd_normalization_theorem
   proves the frozen statement psd_normalization_statement. The file then
   prints the full name of the definition and its axioms, which make check
   compares with check/psd_normalization_assumptions.expected. *)
Require GaussianApplications.PsdNormalizationStatement.
Require GaussianApplications.PsdNormalizationTheorem.

Definition psd_normalization_identity :
  GaussianApplications.PsdNormalizationStatement.psd_normalization_statement :=
  GaussianApplications.PsdNormalizationTheorem.psd_normalization_theorem.

Locate psd_normalization_identity.
Print Assumptions psd_normalization_identity.
