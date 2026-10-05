(* Moments of the translated quadratic Gaussian form. For coefficients c on
   d coordinates and real b let Y = paper_main_head_small_ball_diag d c b,
     Y(xs) = sum_(i < d) c_i (x_i^2 - 1) - b,
     s = sum c_i^2,  t = sum c_i^3,  u = sum c_i^4.
   Under the iterated standard Gaussian expectation, by induction over the
   coordinates (the first coordinate is integrated last), with the moments
   E v = 0, E v^2 = 2, E v^3 = 8, E v^4 = 60 of v = x^2 - 1
   (paper_main_head_small_ball_diag_moments):
     E Y = -b,  E Y^2 = 2 s + b^2,  E Y^3 = 8 t - 6 b s - b^3,
     E Y^4 = 48 u + 12 s^2 - 32 b t + 12 b^2 s + b^4,
   all with iterated integrability. Since u <= s^2 and
   -32 b t <= 16 b^2 s + 16 u, this gives E Y^4 <= 19 (2 s + b^2)^2
   (paper_main_head_small_ball_diag_fourth), without hypercontractivity.
   Through the rotation of PaperMainHeadSmallBall, for real symmetric H of
   size d (paper_main_head_small_ball_moments),
     E (x^T H x - Tr H - b)^2 = 2 |H|_F^2 + b^2,
     E (x^T H x - Tr H - b)^4 <= 19 (2 |H|_F^2 + b^2)^2.
   d = 0 is included (Y = -b). *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianDefinitions GaussianExpectation
  GaussianProductDefinitions GaussianProduct GaussianCovarianceSums
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGaussianWeightedSquare
  PaperMainGaussianOrthogonal PaperMainGaussianQuadraticTail
  PaperMainDiagonalBlockMoment PaperMainHeadSmallBall.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_head_small_ball_diag d (c : nat -> R) (b : R) (xs : list R) : R :=
  paper_main_weighted_square d c xs - b.

Definition paper_main_head_small_ball_s2 d (c : nat -> R) : R :=
  finite_sum (fun i => c i ^ 2) (List.seq 0 d).
Definition paper_main_head_small_ball_s3 d (c : nat -> R) : R :=
  finite_sum (fun i => c i ^ 3) (List.seq 0 d).
Definition paper_main_head_small_ball_s4 d (c : nat -> R) : R :=
  finite_sum (fun i => c i ^ 4) (List.seq 0 d).

Lemma paper_main_head_small_ball_sum_cons (f : nat -> R) k :
  finite_sum f (List.seq 0 (S k)) = f 0%nat + finite_sum (fun i => f (S i)) (List.seq 0 k).
Proof.
change (List.seq 0 (S k)) with (0%nat :: List.seq 1 k).
rewrite /= (finite_sum_seq_shift _ 1 k).
reflexivity.
Qed.

(* Linear combinations under the iterated expectation. *)

Lemma paper_main_head_small_ball_inner d (a0 a1 a2 a3 a4 : R)
    (G0 G1 G2 G3 G4 : list R -> R) :
  gaussian_iterated_integrable d G0 -> gaussian_iterated_integrable d G1 ->
  gaussian_iterated_integrable d G2 -> gaussian_iterated_integrable d G3 ->
  gaussian_iterated_integrable d G4 ->
  gaussian_iterated_integrable d
    (fun xs => a0 * G0 xs + a1 * G1 xs + a2 * G2 xs + a3 * G3 xs + a4 * G4 xs) /\
  gaussian_iterated_expectation d
    (fun xs => a0 * G0 xs + a1 * G1 xs + a2 * G2 xs + a3 * G3 xs + a4 * G4 xs) =
  a0 * gaussian_iterated_expectation d G0 + a1 * gaussian_iterated_expectation d G1 +
  a2 * gaussian_iterated_expectation d G2 + a3 * gaussian_iterated_expectation d G3 +
  a4 * gaussian_iterated_expectation d G4.
Proof.
move=> H0 H1 H2 H3 H4.
have [I0 E0] := gaussian_iterated_scale d G0 a0 H0.
have [I1 E1] := gaussian_iterated_scale d G1 a1 H1.
have [I2 E2] := gaussian_iterated_scale d G2 a2 H2.
have [I3 E3] := gaussian_iterated_scale d G3 a3 H3.
have [I4 E4] := gaussian_iterated_scale d G4 a4 H4.
have [I01 E01] := gaussian_iterated_add d _ _ I0 I1.
have [I012 E012] := gaussian_iterated_add d _ _ I01 I2.
have [I0123 E0123] := gaussian_iterated_add d _ _ I012 I3.
have [I01234 E01234] := gaussian_iterated_add d _ _ I0123 I4.
split; first exact: I01234.
by rewrite E01234 E0123 E012 E01 E0 E1 E2 E3 E4.
Qed.

Lemma paper_main_head_small_ball_step d (F : list R -> R) (a0 a1 a2 a3 a4 : R -> R)
    (G0 G1 G2 G3 G4 : list R -> R) :
  (forall x xs, F (x :: xs) =
    a0 x * G0 xs + a1 x * G1 xs + a2 x * G2 xs + a3 x * G3 xs + a4 x * G4 xs) ->
  gaussian_iterated_integrable d G0 -> gaussian_iterated_integrable d G1 ->
  gaussian_iterated_integrable d G2 -> gaussian_iterated_integrable d G3 ->
  gaussian_iterated_integrable d G4 ->
  gaussian_integral_exists (fun x =>
    a0 x * gaussian_iterated_expectation d G0 + a1 x * gaussian_iterated_expectation d G1 +
    a2 x * gaussian_iterated_expectation d G2 + a3 x * gaussian_iterated_expectation d G3 +
    a4 x * gaussian_iterated_expectation d G4) ->
  gaussian_iterated_integrable (S d) F /\
  gaussian_iterated_expectation (S d) F =
  gaussian_expectation (fun x =>
    a0 x * gaussian_iterated_expectation d G0 + a1 x * gaussian_iterated_expectation d G1 +
    a2 x * gaussian_iterated_expectation d G2 + a3 x * gaussian_iterated_expectation d G3 +
    a4 x * gaussian_iterated_expectation d G4).
Proof.
move=> HF H0 H1 H2 H3 H4 Hout.
have Hsec : forall x, (fun xs => F (x :: xs)) =
    (fun xs => a0 x * G0 xs + a1 x * G1 xs + a2 x * G2 xs + a3 x * G3 xs + a4 x * G4 xs).
  by move=> x; apply: functional_extensionality => xs; exact: HF.
have Hin := fun x => paper_main_head_small_ball_inner d (a0 x) (a1 x) (a2 x) (a3 x) (a4 x)
  G0 G1 G2 G3 G4 H0 H1 H2 H3 H4.
have He : (fun x => gaussian_iterated_expectation d (fun xs => F (x :: xs))) =
    (fun x => a0 x * gaussian_iterated_expectation d G0 +
      a1 x * gaussian_iterated_expectation d G1 + a2 x * gaussian_iterated_expectation d G2 +
      a3 x * gaussian_iterated_expectation d G3 + a4 x * gaussian_iterated_expectation d G4).
  by apply: functional_extensionality => x; rewrite (Hsec x); exact: (proj2 (Hin x)).
split.
- split.
  + by move=> x; rewrite (Hsec x); exact: (proj1 (Hin x)).
  + by rewrite He.
- by rewrite /= He.
Qed.

(* Polynomials in v = x^2 - 1 of degree at most four. *)

Lemma paper_main_head_small_ball_outer (b0 b1 b2 b3 b4 : R) :
  gaussian_integral_exists (fun x => b0 + b1 * (x ^ 2 - 1) + b2 * (x ^ 2 - 1) ^ 2 +
    b3 * (x ^ 2 - 1) ^ 3 + b4 * (x ^ 2 - 1) ^ 4) /\
  gaussian_expectation (fun x => b0 + b1 * (x ^ 2 - 1) + b2 * (x ^ 2 - 1) ^ 2 +
    b3 * (x ^ 2 - 1) ^ 3 + b4 * (x ^ 2 - 1) ^ 4) = b0 + 2 * b2 + 8 * b3 + 60 * b4.
Proof.
set cs := [:: (b4, 8%N); (b3 - 4 * b4, 6%N); (b2 - 3 * b3 + 6 * b4, 4%N);
  (b1 - 2 * b2 + 3 * b3 - 4 * b4, 2%N); (b0 - b1 + b2 - b3 + b4, 0%N)].
have Z : (GRing.zero : R) = 0 by [].
have Hfun : (fun x => b0 + b1 * (x ^ 2 - 1) + b2 * (x ^ 2 - 1) ^ 2 +
    b3 * (x ^ 2 - 1) ^ 3 + b4 * (x ^ 2 - 1) ^ 4) = pmdm_poly cs.
  apply: functional_extensionality => x.
  rewrite /cs !pmdm_poly_cons pmdm_poly_nil.
  rewrite -!RpowE -!RplusE -!RmultE Z.
  ring.
rewrite Hfun.
have [HI HE] := pmdm_poly_exp cs.
split; first exact: HI.
rewrite HE /cs !pmdm_poly_moment_cons pmdm_poly_moment_nil.
rewrite -!RplusE -!RmultE Z.
simpl moment_factor; simpl INR.
ring.
Qed.

Lemma paper_main_head_small_ball_outer_ext (f : R -> R) (b0 b1 b2 b3 b4 : R) :
  (forall x, f x = b0 + b1 * (x ^ 2 - 1) + b2 * (x ^ 2 - 1) ^ 2 +
    b3 * (x ^ 2 - 1) ^ 3 + b4 * (x ^ 2 - 1) ^ 4) ->
  gaussian_integral_exists f /\ gaussian_expectation f = b0 + 2 * b2 + 8 * b3 + 60 * b4.
Proof.
move=> Hf.
have -> : f = (fun x => b0 + b1 * (x ^ 2 - 1) + b2 * (x ^ 2 - 1) ^ 2 +
    b3 * (x ^ 2 - 1) ^ 3 + b4 * (x ^ 2 - 1) ^ 4).
  by apply: functional_extensionality.
exact: paper_main_head_small_ball_outer.
Qed.

(* The moments of the diagonal form, by induction over the coordinates. *)

Theorem paper_main_head_small_ball_diag_moments d : forall (c : nat -> R) (b : R),
  (gaussian_iterated_integrable d (paper_main_head_small_ball_diag d c b) /\
   gaussian_iterated_expectation d (paper_main_head_small_ball_diag d c b) = - b) /\
  (gaussian_iterated_integrable d (fun xs => paper_main_head_small_ball_diag d c b xs ^ 2) /\
   gaussian_iterated_expectation d (fun xs => paper_main_head_small_ball_diag d c b xs ^ 2) =
     2 * paper_main_head_small_ball_s2 d c + b ^ 2) /\
  (gaussian_iterated_integrable d (fun xs => paper_main_head_small_ball_diag d c b xs ^ 3) /\
   gaussian_iterated_expectation d (fun xs => paper_main_head_small_ball_diag d c b xs ^ 3) =
     8 * paper_main_head_small_ball_s3 d c - 6 * b * paper_main_head_small_ball_s2 d c -
     b ^ 3) /\
  (gaussian_iterated_integrable d (fun xs => paper_main_head_small_ball_diag d c b xs ^ 4) /\
   gaussian_iterated_expectation d (fun xs => paper_main_head_small_ball_diag d c b xs ^ 4) =
     48 * paper_main_head_small_ball_s4 d c + 12 * paper_main_head_small_ball_s2 d c ^ 2 -
     32 * b * paper_main_head_small_ball_s3 d c +
     12 * b ^ 2 * paper_main_head_small_ball_s2 d c + b ^ 4).
Proof.
induction d as [|d IH] => c b.
  rewrite /paper_main_head_small_ball_diag /paper_main_weighted_square
    /paper_main_head_small_ball_s2 /paper_main_head_small_ball_s3
    /paper_main_head_small_ball_s4 /=.
  by do !split; ring.
set c' := fun i => c (S i).
have [[I1 E1] [[I2 E2] [[I3 E3] [I4 E4]]]] := IH c' b.
set Y' := paper_main_head_small_ball_diag d c' b in I1 E1 I2 E2 I3 E3 I4 E4.
set s' := paper_main_head_small_ball_s2 d c' in E2 E3 E4.
set t' := paper_main_head_small_ball_s3 d c' in E3 E4.
set u' := paper_main_head_small_ball_s4 d c' in E4.
have Hcons : forall x xs, paper_main_head_small_ball_diag (S d) c b (x :: xs) =
    c 0%nat * (x ^ 2 - 1) + Y' xs.
  move=> x xs; rewrite /Y' /paper_main_head_small_ball_diag paper_main_weighted_square_cons.
  rewrite /c'; ring.
have [I0 E0] := gaussian_iterated_constant d 1.
have Hs2 : paper_main_head_small_ball_s2 (S d) c = c 0%nat ^ 2 + s'.
  exact: paper_main_head_small_ball_sum_cons.
have Hs3 : paper_main_head_small_ball_s3 (S d) c = c 0%nat ^ 3 + t'.
  exact: paper_main_head_small_ball_sum_cons.
have Hs4 : paper_main_head_small_ball_s4 (S d) c = c 0%nat ^ 4 + u'.
  exact: paper_main_head_small_ball_sum_cons.
set a := c 0%nat in Hcons Hs2 Hs3 Hs4.
rewrite Hs2 Hs3 Hs4.
(* m = 1 *)
have Hsec1 : forall x xs, paper_main_head_small_ball_diag (S d) c b (x :: xs) =
    a * (x ^ 2 - 1) * 1 + 1 * Y' xs + 0 * 1 + 0 * 1 + 0 * 1.
  by move=> x xs; rewrite Hcons; ring.
have Hpt1 : forall x,
    a * (x ^ 2 - 1) * gaussian_iterated_expectation d (fun _ => 1) +
    1 * gaussian_iterated_expectation d Y' +
    0 * gaussian_iterated_expectation d (fun _ => 1) +
    0 * gaussian_iterated_expectation d (fun _ => 1) +
    0 * gaussian_iterated_expectation d (fun _ => 1) =
    - b + a * (x ^ 2 - 1) + 0 * (x ^ 2 - 1) ^ 2 + 0 * (x ^ 2 - 1) ^ 3 +
      0 * (x ^ 2 - 1) ^ 4.
  by move=> x; rewrite E0 E1; ring.
have [Ho1 Eo1] := paper_main_head_small_ball_outer_ext _ _ _ _ _ _ Hpt1.
have [J1 F1] := paper_main_head_small_ball_step d (paper_main_head_small_ball_diag (S d) c b)
  (fun x => a * (x ^ 2 - 1)) (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0)
  (fun _ => 1) Y' (fun _ => 1) (fun _ => 1) (fun _ => 1) Hsec1 I0 I1 I0 I0 I0 Ho1.
(* m = 2 *)
have Hsec2 : forall x xs, paper_main_head_small_ball_diag (S d) c b (x :: xs) ^ 2 =
    (a * (x ^ 2 - 1)) ^ 2 * 1 + 2 * (a * (x ^ 2 - 1)) * Y' xs + 1 * Y' xs ^ 2 +
    0 * 1 + 0 * 1.
  by move=> x xs; rewrite Hcons; ring.
have Hpt2 : forall x,
    (a * (x ^ 2 - 1)) ^ 2 * gaussian_iterated_expectation d (fun _ => 1) +
    2 * (a * (x ^ 2 - 1)) * gaussian_iterated_expectation d Y' +
    1 * gaussian_iterated_expectation d (fun xs => Y' xs ^ 2) +
    0 * gaussian_iterated_expectation d (fun _ => 1) +
    0 * gaussian_iterated_expectation d (fun _ => 1) =
    (2 * s' + b ^ 2) + (2 * a * (- b)) * (x ^ 2 - 1) + a ^ 2 * (x ^ 2 - 1) ^ 2 +
      0 * (x ^ 2 - 1) ^ 3 + 0 * (x ^ 2 - 1) ^ 4.
  by move=> x; rewrite E0 E1 E2; ring.
have [Ho2 Eo2] := paper_main_head_small_ball_outer_ext _ _ _ _ _ _ Hpt2.
have [J2 F2] := paper_main_head_small_ball_step d
  (fun xs => paper_main_head_small_ball_diag (S d) c b xs ^ 2)
  (fun x => (a * (x ^ 2 - 1)) ^ 2) (fun x => 2 * (a * (x ^ 2 - 1))) (fun _ => 1)
  (fun _ => 0) (fun _ => 0)
  (fun _ => 1) Y' (fun xs => Y' xs ^ 2) (fun _ => 1) (fun _ => 1) Hsec2 I0 I1 I2 I0 I0 Ho2.
(* m = 3 *)
have Hsec3 : forall x xs, paper_main_head_small_ball_diag (S d) c b (x :: xs) ^ 3 =
    (a * (x ^ 2 - 1)) ^ 3 * 1 + 3 * (a * (x ^ 2 - 1)) ^ 2 * Y' xs +
    3 * (a * (x ^ 2 - 1)) * Y' xs ^ 2 + 1 * Y' xs ^ 3 + 0 * 1.
  by move=> x xs; rewrite Hcons; ring.
have Hpt3 : forall x,
    (a * (x ^ 2 - 1)) ^ 3 * gaussian_iterated_expectation d (fun _ => 1) +
    3 * (a * (x ^ 2 - 1)) ^ 2 * gaussian_iterated_expectation d Y' +
    3 * (a * (x ^ 2 - 1)) * gaussian_iterated_expectation d (fun xs => Y' xs ^ 2) +
    1 * gaussian_iterated_expectation d (fun xs => Y' xs ^ 3) +
    0 * gaussian_iterated_expectation d (fun _ => 1) =
    (8 * t' - 6 * b * s' - b ^ 3) + (3 * a * (2 * s' + b ^ 2)) * (x ^ 2 - 1) +
      (3 * a ^ 2 * (- b)) * (x ^ 2 - 1) ^ 2 + a ^ 3 * (x ^ 2 - 1) ^ 3 +
      0 * (x ^ 2 - 1) ^ 4.
  by move=> x; rewrite E0 E1 E2 E3; ring.
have [Ho3 Eo3] := paper_main_head_small_ball_outer_ext _ _ _ _ _ _ Hpt3.
have [J3 F3] := paper_main_head_small_ball_step d
  (fun xs => paper_main_head_small_ball_diag (S d) c b xs ^ 3)
  (fun x => (a * (x ^ 2 - 1)) ^ 3) (fun x => 3 * (a * (x ^ 2 - 1)) ^ 2)
  (fun x => 3 * (a * (x ^ 2 - 1))) (fun _ => 1) (fun _ => 0)
  (fun _ => 1) Y' (fun xs => Y' xs ^ 2) (fun xs => Y' xs ^ 3) (fun _ => 1)
  Hsec3 I0 I1 I2 I3 I0 Ho3.
(* m = 4 *)
have Hsec4 : forall x xs, paper_main_head_small_ball_diag (S d) c b (x :: xs) ^ 4 =
    (a * (x ^ 2 - 1)) ^ 4 * 1 + 4 * (a * (x ^ 2 - 1)) ^ 3 * Y' xs +
    6 * (a * (x ^ 2 - 1)) ^ 2 * Y' xs ^ 2 + 4 * (a * (x ^ 2 - 1)) * Y' xs ^ 3 +
    1 * Y' xs ^ 4.
  by move=> x xs; rewrite Hcons; ring.
have Hpt4 : forall x,
    (a * (x ^ 2 - 1)) ^ 4 * gaussian_iterated_expectation d (fun _ => 1) +
    4 * (a * (x ^ 2 - 1)) ^ 3 * gaussian_iterated_expectation d Y' +
    6 * (a * (x ^ 2 - 1)) ^ 2 * gaussian_iterated_expectation d (fun xs => Y' xs ^ 2) +
    4 * (a * (x ^ 2 - 1)) * gaussian_iterated_expectation d (fun xs => Y' xs ^ 3) +
    1 * gaussian_iterated_expectation d (fun xs => Y' xs ^ 4) =
    (48 * u' + 12 * s' ^ 2 - 32 * b * t' + 12 * b ^ 2 * s' + b ^ 4) +
      (4 * a * (8 * t' - 6 * b * s' - b ^ 3)) * (x ^ 2 - 1) +
      (6 * a ^ 2 * (2 * s' + b ^ 2)) * (x ^ 2 - 1) ^ 2 +
      (4 * a ^ 3 * (- b)) * (x ^ 2 - 1) ^ 3 + a ^ 4 * (x ^ 2 - 1) ^ 4.
  by move=> x; rewrite E0 E1 E2 E3 E4; ring.
have [Ho4 Eo4] := paper_main_head_small_ball_outer_ext _ _ _ _ _ _ Hpt4.
have [J4 F4] := paper_main_head_small_ball_step d
  (fun xs => paper_main_head_small_ball_diag (S d) c b xs ^ 4)
  (fun x => (a * (x ^ 2 - 1)) ^ 4) (fun x => 4 * (a * (x ^ 2 - 1)) ^ 3)
  (fun x => 6 * (a * (x ^ 2 - 1)) ^ 2) (fun x => 4 * (a * (x ^ 2 - 1))) (fun _ => 1)
  (fun _ => 1) Y' (fun xs => Y' xs ^ 2) (fun xs => Y' xs ^ 3) (fun xs => Y' xs ^ 4)
  Hsec4 I0 I1 I2 I3 I4 Ho4.
split; [split; [exact: J1 | rewrite (eq_trans F1 Eo1); ring]|].
split; [split; [exact: J2 | rewrite (eq_trans F2 Eo2); ring]|].
split; [split; [exact: J3 | rewrite (eq_trans F3 Eo3); ring]|].
split; [exact: J4 | rewrite (eq_trans F4 Eo4); ring].
Qed.

(* The fourth moment bound. *)

Lemma paper_main_head_small_ball_s2_nonneg d (c : nat -> R) :
  0 <= paper_main_head_small_ball_s2 d c.
Proof.
by apply: finite_sum_nonnegative => i _; apply: pow2_ge_0.
Qed.

Lemma paper_main_head_small_ball_s4_le d : forall c : nat -> R,
  paper_main_head_small_ball_s4 d c <= paper_main_head_small_ball_s2 d c ^ 2.
Proof.
induction d as [|d IH] => c.
  rewrite /paper_main_head_small_ball_s4 /paper_main_head_small_ball_s2 /=; lra.
have H := IH (fun i => c (S i)).
have H0 := paper_main_head_small_ball_s2_nonneg d (fun i => c (S i)).
rewrite /paper_main_head_small_ball_s4 /paper_main_head_small_ball_s2
  !paper_main_head_small_ball_sum_cons.
rewrite /paper_main_head_small_ball_s4 /paper_main_head_small_ball_s2 in H H0.
set s' := finite_sum _ (List.seq 0 d) in H H0 *.
set u' := finite_sum (fun i => c (S i) ^ 4) (List.seq 0 d) in H *.
have Hc : 0 <= c 0%nat ^ 2 by apply: pow2_ge_0.
have E : c 0%nat ^ 4 = (c 0%nat ^ 2) ^ 2 by ring.
rewrite E.
nra.
Qed.

Lemma paper_main_head_small_ball_s3_bound d (c : nat -> R) (b : R) :
  - (32 * b * paper_main_head_small_ball_s3 d c) <=
  16 * b ^ 2 * paper_main_head_small_ball_s2 d c + 16 * paper_main_head_small_ball_s4 d c.
Proof.
rewrite /paper_main_head_small_ball_s3 /paper_main_head_small_ball_s2
  /paper_main_head_small_ball_s4.
have EL : - (32 * b * finite_sum (fun i => c i ^ 3) (List.seq 0 d)) =
    finite_sum (fun i => - (32 * b) * c i ^ 3) (List.seq 0 d).
  by rewrite finite_sum_scale; ring.
have ER : 16 * b ^ 2 * finite_sum (fun i => c i ^ 2) (List.seq 0 d) +
    16 * finite_sum (fun i => c i ^ 4) (List.seq 0 d) =
    finite_sum (fun i => 16 * b ^ 2 * c i ^ 2 + 16 * c i ^ 4) (List.seq 0 d).
  by rewrite finite_sum_plus !finite_sum_scale.
rewrite EL ER; apply: finite_sum_le => i _.
have := pow2_ge_0 (b * c i + c i ^ 2).
nra.
Qed.

Theorem paper_main_head_small_ball_diag_fourth d (c : nat -> R) (b : R) :
  gaussian_iterated_expectation d (fun xs => paper_main_head_small_ball_diag d c b xs ^ 4) <=
  19 * (2 * paper_main_head_small_ball_s2 d c + b ^ 2) ^ 2.
Proof.
have [_ [_ [_ [_ E4]]]] := paper_main_head_small_ball_diag_moments d c b.
rewrite E4.
have H1 := paper_main_head_small_ball_s4_le d c.
have H2 := paper_main_head_small_ball_s3_bound d c b.
have Hs := paper_main_head_small_ball_s2_nonneg d c.
set s := paper_main_head_small_ball_s2 d c in H1 H2 Hs *.
set t := paper_main_head_small_ball_s3 d c in H2 *.
set u := paper_main_head_small_ball_s4 d c in H1 H2 *.
have Hb : 0 <= b ^ 2 by apply: pow2_ge_0.
have Hsb : 0 <= s * b ^ 2 by apply: Rmult_le_pos.
have Hb4 : b ^ 4 = (b ^ 2) ^ 2 by ring.
rewrite Hb4.
nra.
Qed.

(* The moments of x^T H x - Tr H - b for real symmetric H. *)

Theorem paper_main_head_small_ball_moments d (H : 'M[R]_d) (b : R) :
  paper_main_symmetric H ->
  gaussian_iterated_expectation d
    (fun xs => (paper_main_gaussian_quadratic_statistic H xs - b) ^ 2) =
    2 * paper_main_pairing H H + b ^ 2 /\
  gaussian_iterated_expectation d
    (fun xs => (paper_main_gaussian_quadratic_statistic H xs - b) ^ 4) <=
    19 * (2 * paper_main_pairing H H + b ^ 2) ^ 2.
Proof.
move=> HH.
have [O [c [HO [Hid [Hfr [Hc Hrot]]]]]] := paper_main_head_small_ball_rotation d H HH.
have Hs : paper_main_head_small_ball_s2 d c = paper_main_pairing H H by exact: Hfr.
split.
  rewrite (Hrot b 0%nat) -Hs.
  have [_ [[_ E2] _]] := paper_main_head_small_ball_diag_moments d c b.
  exact: E2.
rewrite (Hrot b 2%nat) -Hs.
exact: (paper_main_head_small_ball_diag_fourth d c b).
Qed.
