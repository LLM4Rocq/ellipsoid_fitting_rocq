(* Width/statistical-dimension inequalities for a signed Lipschitz support
   function. The positive part is essential for a cone's unit SPHERE:
   spherical support can be negative. These analytic inequalities will be
   applied to the actual PSD support and its proved projection identity. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProductDefinitions GaussianProduct
  PaperMainGordonLipschitz PaperMainGaussianLipschitzClip
  PaperMainGaussianLipschitzApproximation PaperMainGaussianLipschitzVariance.
Open Scope R_scope.

Lemma paper_main_positive_part_lipschitz a b :
  Rabs (Rmax a 0 - Rmax b 0) <= Rabs (a - b).
Proof.
destruct (Rle_dec a 0) as [Ha|Ha]; destruct (Rle_dec b 0) as [Hb|Hb].
- rewrite (Rmax_right _ _ Ha) (Rmax_right _ _ Hb).
  rewrite Rminus_diag Rabs_R0; apply Rabs_pos.
- rewrite (Rmax_right a 0 Ha) (Rmax_left b 0 ltac:(lra)).
  rewrite Rminus_0_l Rabs_Ropp (Rabs_pos_eq b ltac:(lra)).
  pose proof (Rle_abs (b-a)); rewrite Rabs_minus_sym in H; lra.
- rewrite (Rmax_left a 0 ltac:(lra)) (Rmax_right b 0 Hb).
  rewrite Rminus_0_r (Rabs_pos_eq a ltac:(lra)).
  pose proof (Rle_abs (a-b)); lra.
- rewrite (Rmax_left a 0 ltac:(lra)) (Rmax_left b 0 ltac:(lra)); lra.
Qed.

Lemma paper_main_gaussian_positive_part_lipschitz d F L :
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (Rmax (F xs) 0 - Rmax (F ys) 0) <= L * paper_main_gordon_distance d xs ys.
Proof.
intros Hlip xs ys Hx Hy.
pose proof (paper_main_positive_part_lipschitz (F xs) (F ys)).
pose proof (Hlip xs ys Hx Hy); lra.
Qed.

Lemma paper_main_positive_part_square a : Rmax a 0 * Rmax a 0 <= a*a.
Proof.
destruct (Rle_dec a 0) as [Ha|Ha].
- rewrite (Rmax_right _ _ Ha); nra.
- rewrite (Rmax_left a 0 ltac:(lra)); lra.
Qed.

Theorem paper_main_gaussian_lipschitz_mean_square d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  (gaussian_iterated_expectation d F)^2 <=
    gaussian_iterated_expectation d (fun xs => F xs * F xs).
Proof.
intros HL Hlip.
pose proof (paper_main_gaussian_variance_identity d F L HL Hlip).
pose proof (paper_main_gaussian_variance_nonnegative d F L HL Hlip); lra.
Qed.

Definition paper_main_gaussian_positive_square d (F : list R -> R) :=
  gaussian_iterated_expectation d (fun xs => Rmax (F xs) 0 * Rmax (F xs) 0).

Theorem paper_main_gaussian_positive_square_nonnegative d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 <= paper_main_gaussian_positive_square d F.
Proof.
intros HL Hlip.
pose proof (paper_main_gaussian_positive_part_lipschitz d F L Hlip) as HP.
pose proof (paper_main_gaussian_lipschitz_mean_square d (fun xs => Rmax (F xs) 0)
  L HL HP) as H.
unfold paper_main_gaussian_positive_square; nra.
Qed.

Theorem paper_main_gaussian_positive_square_lower d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  paper_main_gaussian_positive_square d F - L^2 <=
    (gaussian_iterated_expectation d F)^2.
Proof.
intros HL Hlip.
pose proof (paper_main_gaussian_positive_part_lipschitz d F L Hlip) as HP.
pose proof (paper_main_gaussian_lipschitz_square_domain d F L HL Hlip) as HF2.
pose proof (paper_main_gaussian_lipschitz_square_domain d (fun xs => Rmax (F xs) 0)
  L HL HP) as HP2.
pose proof (gaussian_iterated_monotone d _ _ HP2 HF2
  ltac:(intros xs _; apply paper_main_positive_part_square)) as Hmono.
pose proof (paper_main_gaussian_variance_identity d F L HL Hlip).
pose proof (paper_main_gaussian_lipschitz_variance d F L HL Hlip).
unfold paper_main_gaussian_positive_square; lra.
Qed.

Theorem paper_main_gaussian_mean_positive_square_upper d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_expectation d F <= sqrt (paper_main_gaussian_positive_square d F).
Proof.
intros HL Hlip.
pose proof (paper_main_gaussian_positive_part_lipschitz d F L Hlip) as HP.
destruct (paper_main_gaussian_lipschitz_domain d F L HL Hlip) as [HF _].
destruct (paper_main_gaussian_lipschitz_domain d (fun xs => Rmax (F xs) 0) L HL HP)
  as [HI _].
pose proof (gaussian_iterated_monotone d _ _ HF HI
  ltac:(intros xs _; apply Rmax_l)) as Hmono.
pose proof (paper_main_gaussian_lipschitz_mean_square d (fun xs => Rmax (F xs) 0)
  L HL HP) as Hsq.
pose proof (paper_main_gaussian_positive_square_nonnegative d F L HL Hlip) as Hd.
pose proof (pow2_sqrt _ Hd).
pose proof (sqrt_pos (paper_main_gaussian_positive_square d F)).
unfold paper_main_gaussian_positive_square in *; nra.
Qed.

Theorem paper_main_gaussian_mean_positive_square_lower d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 <= gaussian_iterated_expectation d F ->
  sqrt (paper_main_gaussian_positive_square d F - L^2) <=
    gaussian_iterated_expectation d F.
Proof.
intros HL Hlip Hmean.
pose proof (paper_main_gaussian_positive_square_lower d F L HL Hlip) as H.
destruct (Rle_dec 0 (paper_main_gaussian_positive_square d F - L^2)) as [Hd|Hd].
- pose proof (pow2_sqrt _ Hd).
  pose proof (sqrt_pos (paper_main_gaussian_positive_square d F - L^2)); nra.
- rewrite sqrt_neg_0; lra.
Qed.
