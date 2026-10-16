From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear reals ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.matrix Require Import psd_splitting centered_correction.

(**md**************************************************************************)
(* # Centered quadratic measurements under a common translation              *)
(*                                                                            *)
(* The unnormalized measurement vector is P_n (x_i^T Q x_i)_i. Translation   *)
(* by m changes it by exactly 2 P_n H Q m, for symmetric Q. Its norm is      *)
(* bounded by 2 opnorm(H) opnorm(Q) frobenius(m), uniformly in Q and m.       *)
(* Divide by sqrt(n*d) for the normalized empirical residual.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section orthogonal_projection_norm.
Variable R : realType.

Lemma orthoprojmx_contract n p (P : 'M[R]_n) (X : 'M[R]_(n,p)) :
  orthoprojmx P -> frobenius (P *m X) <= frobenius X.
Proof.
move=> [/symmetricmxP PT PP].
have h := ler_mxdot X (P *m X).
have he : frobenius (P *m X)^+2 = mxdot X (P *m X).
  by rewrite frobenius_sqr mxdot_mulmxl PT mulmxA PP.
have [hz|hp] := leP (frobenius (P *m X)) 0.
  exact: le_trans hz (frobenius_ge0 X).
rewrite -he expr2 in h.
by rewrite ler_pM2r in h.
Qed.

Lemma centering_contract n p (X : 'M[R]_(n,p)) :
  (0 < n)%N -> frobenius (centering_mx n *m X) <= frobenius X.
Proof. by move=> n0; apply: orthoprojmx_contract; exact: centering_orthoproj. Qed.

Lemma centering_ones_zero n : (0 < n)%N ->
  (centering_mx n : 'M[R]_n) *m centering_ones n = 0.
Proof.
move=> n0.
have h := congr1 trmx (@centering_mass R n n0).
by move: h; rewrite trmx_mul trmxK (symmetricmxP _ (@centering_symmetric R n)) trmx0.
Qed.

End orthogonal_projection_norm.

Section translations.
Variable R : realType.

Definition matrix_translate n d (H : 'M[R]_(n,d)) (m : 'cV[R]_d) :=
  H + centering_ones n *m m^T.

Definition quadratic_values n d (H : 'M[R]_(n,d)) (Q : 'M[R]_d) : 'cV[R]_n :=
  \col_i mxdot (row i H)^T (Q *m (row i H)^T).

Definition centered_quadratic_values n d (H : 'M[R]_(n,d)) (Q : 'M[R]_d) :=
  centering_mx n *m quadratic_values H Q.

Lemma matrix_translate_row n d (H : 'M[R]_(n,d)) (m : 'cV[R]_d) i :
  (row i (matrix_translate H m))^T = (row i H)^T + m.
Proof.
apply/matrixP => j k; rewrite !ord1 /matrix_translate !mxE big_ord1.
by rewrite /centering_ones !mxE mul1r.
Qed.

Lemma quadratic_translate_form d (Q : 'M[R]_d) (u m : 'cV[R]_d) :
  Q \is symmetricmx ->
  mxdot (u+m) (Q *m (u+m)) =
    mxdot u (Q *m u) + 2 * mxdot u (Q *m m) + mxdot m (Q *m m).
Proof.
move=> /symmetricmxP QT.
rewrite mulmxDr !mxdotDl !mxdotDr.
have he : mxdot m (Q *m u) = mxdot u (Q *m m).
  by rewrite mxdotC mxdot_mulmxl QT.
rewrite he; ring.
Qed.

Lemma quadratic_values_translate n d (H : 'M[R]_(n,d))
    (Q : 'M[R]_d) (m : 'cV[R]_d) :
  Q \is symmetricmx ->
  quadratic_values (matrix_translate H m) Q = quadratic_values H Q +
    2 *: (H *m Q *m m) + mxdot m (Q *m m) *: centering_ones n.
Proof.
move=> Qs; apply/matrixP => i j; rewrite !ord1 /quadratic_values !mxE
  matrix_translate_row quadratic_translate_form //.
have he : mxdot (row i H)^T (Q *m m) = (H *m Q *m m) i 0.
  by rewrite mxdot_colE trmxK -mulmxA -row_mul mxE.
by rewrite he ?mulr1 mxE.
Qed.

Lemma centered_quadratic_translate n d (H : 'M[R]_(n,d))
    (Q : 'M[R]_d) (m : 'cV[R]_d) :
  (0 < n)%N -> Q \is symmetricmx ->
  centered_quadratic_values (matrix_translate H m) Q -
    centered_quadratic_values H Q =
      2 *: (centering_mx n *m (H *m Q *m m)).
Proof.
move=> n0 Qs.
rewrite /centered_quadratic_values quadratic_values_translate // !mulmxDr
  -!scalemxAr centering_ones_zero // scaler0 addr0.
by rewrite addrAC subrr add0r.
Qed.

Theorem centered_quadratic_translate_bound n d (H : 'M[R]_(n,d))
    (Q : 'M[R]_d) (m : 'cV[R]_d) :
  (0 < n)%N -> Q \is symmetricmx ->
  frobenius (centered_quadratic_values (matrix_translate H m) Q -
    centered_quadratic_values H Q) <=
      2 * opnorm H * opnorm Q * frobenius m.
Proof.
move=> n0 Qs.
rewrite centered_quadratic_translate // frobeniusZ normr_nat -!mulrA.
apply: ler_wpM2l; first by rewrite ler0n.
apply: (le_trans (@centering_contract R n 1 (H *m Q *m m) n0)).
rewrite -mulmxA.
apply: le_trans (frobenius_mulmx_opnorm H (Q *m m)) _.
apply: ler_wpM2l; first exact: opnorm_ge0.
exact: frobenius_mulmx_opnorm.
Qed.

(* Constant samples have zero centered quadratic measurements. *)
Example centered_constant_sample n d (m : 'cV[R]_d) (Q : 'M[R]_d) :
  (0 < n)%N -> Q \is symmetricmx ->
  centered_quadratic_values (centering_ones n *m m^T) Q = 0.
Proof.
move=> n0 Qs.
have q0 : quadratic_values (0 : 'M[R]_(n,d)) Q = 0.
  apply/matrixP => i j.
  by rewrite /quadratic_values !mxE row0 trmx0 mulmx0 mxdot0l.
have h := centered_quadratic_translate (0 : 'M[R]_(n,d)) m n0 Qs.
by move: h; rewrite /matrix_translate add0r /centered_quadratic_values q0
  !mul0mx !mulmx0 subr0 ?scaler0.
Qed.

End translations.
