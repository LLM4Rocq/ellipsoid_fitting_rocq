(* Affine substitution in the whole-line integral interface, followed by the
   Gaussian inverse-density formula. Arithmetic is Stdlib R. *)
From Stdlib Require Import Reals Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge AnalysisIntegralDefinitions
  GaussianDefinitions GaussianKernel GaussianFubiniLebesgue
  PaperMainGaussianAffineIntegral.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_whole_line_affine_integral (m s : R) (F : R -> R) :
  0 < s -> continuous F ->
  whole_line_integral F =
  whole_line_integral (fun x => F (m + s * x) * s).
Proof.
move=> Hs HF; rewrite /whole_line_integral /Rintegral.
apply: congr1.
apply: (paper_main_affine_integral R m s F); last exact HF.
by apply/RltP.
Qed.

Lemma paper_main_whole_line_affine_integrable (m s : R) (F : R -> R) :
  0 < s -> continuous F ->
  whole_line_integrable F <->
  whole_line_integrable (fun x => F (m + s * x) * s).
Proof.
move=> Hs HF; rewrite /whole_line_integrable.
apply: (paper_main_affine_integrable R m s F); last exact HF.
by apply/RltP.
Qed.

Lemma paper_main_affine_inverse_continuous (m s : R) :
  continuous (fun y : R => (y - m) / s).
Proof.
move=> y; rewrite /Rdiv.
apply (@AnalysisBridge.continuous_mult R^o (fun y : R => y - m) (fun _ => / s) y).
- apply: continuous_minus; [exact: continuous_id | exact: continuous_const].
- exact: continuous_const.
Qed.

Theorem paper_main_gaussian_affine_density_integral (m s : R) (h w : R -> R) :
  0 < s -> continuous h -> continuous w ->
  gaussian_integral (fun z => h (m + s * z) * w z) =
  whole_line_integral (fun y =>
    h y * w ((y - m) / s) * gaussian_kernel ((y - m) / s) / s).
Proof.
move=> Hs Hh Hw.
set F := fun y => h y * w ((y - m) / s) * gaussian_kernel ((y - m) / s) / s.
have HF : continuous F.
  move=> y; rewrite /F /Rdiv.
  apply (@AnalysisBridge.continuous_mult R^o
    (fun y : R => h y * w ((y - m) * / s) * gaussian_kernel ((y - m) * / s))
    (fun _ => / s) y); last exact: continuous_const.
  apply: continuous_mult; last first.
  - apply: continuous_comp; [exact: paper_main_affine_inverse_continuous | exact: gaussian_kernel_continuous].
  - apply: continuous_mult; first exact: Hh.
    apply: continuous_comp; [exact: paper_main_affine_inverse_continuous | exact: Hw].
rewrite (paper_main_whole_line_affine_integral m s F Hs HF).
unfold gaussian_integral; apply: congr1; apply: functional_extensionality => z.
unfold F.
have Hz : (m + s * z - m) / s = z by field; lra.
rewrite Hz; field; lra.
Qed.

Theorem paper_main_gaussian_affine_density_integrable (m s : R) (h w : R -> R) :
  0 < s -> continuous h -> continuous w ->
  gaussian_integral_exists (fun z => h (m + s * z) * w z) <->
  whole_line_integrable (fun y =>
    h y * w ((y - m) / s) * gaussian_kernel ((y - m) / s) / s).
Proof.
move=> Hs Hh Hw.
set F := fun y => h y * w ((y - m) / s) * gaussian_kernel ((y - m) / s) / s.
have HF : continuous F.
  move=> y; rewrite /F /Rdiv.
  apply (@AnalysisBridge.continuous_mult R^o
    (fun y : R => h y * w ((y - m) * / s) * gaussian_kernel ((y - m) * / s))
    (fun _ => / s) y); last exact: continuous_const.
  apply: continuous_mult; last first.
  - apply: continuous_comp; [exact: paper_main_affine_inverse_continuous | exact: gaussian_kernel_continuous].
  - apply: continuous_mult; first exact: Hh.
    apply: continuous_comp; [exact: paper_main_affine_inverse_continuous | exact: Hw].
rewrite (paper_main_whole_line_affine_integrable m s F Hs HF).
unfold gaussian_integral_exists.
have HE : (fun z => h (m + s * z) * w z * gaussian_kernel z) =
    (fun z => F (m + s * z) * s).
  apply: functional_extensionality => z; unfold F.
  have Hz : (m + s * z - m) / s = z by field; lra.
  rewrite Hz; field; lra.
by rewrite HE.
Qed.
