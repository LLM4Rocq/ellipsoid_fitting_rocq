(* G13, last step: positive support for every unit dual vector, from G12's
   actual head J (manuscript lines 891-923, before convex separation).
   - Box to cone: an S with lo I <= S <= hi I (0 < lo) and <Z, S> > 0
     normalizes into the condition cone sphere K_(hi / lo) \cap S_F, so the
     support value sup_(K \cap S_F) <Z, .> of PaperMainGeometryHeadWidth is
     positive.
   - Combination. Fix d >= 2, theta > 0 and the G12 head budget
     K = head_tail_constant theta * d * ln d. Assume, for every head J with
     length J <= K:
     - a section S0 in [a I, b I] annihilating J;
     - the head Gram bound mu;
     - positive section support in [(a - delta) I, (b + delta) I] for every
       capped unit tail vanishing on J.
     Assume also the full operator bound A and
     A d^-2 (b + delta) sqrt d < delta sqrt mu / 2. Then every unit y has
     positive support in [(a - delta) I, (b + delta) I], hence positive
     support on K_((b + delta) / (a - delta)) \cap S_F.
   All cardinality, section, Gram and operator premises are explicit. No
   probability statement. *)
From Stdlib Require Import Reals List Lia Lra Psatz PeanoNat.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import Definitions FiniteSets HeadTail SoftDefinitions
  GaussianCovarianceSums PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadWidth
  PaperMainHeadTailDecompositionLog PaperMainHeadTailSupport PaperMainHeadTailSupportSplit.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Open Scope R_scope.

(* 1. From a Loewner box to the condition cone sphere. *)
Theorem paper_main_support_cone_sphere d (Z S : 'M[R]_d) (lo hi : R) :
  0 < lo -> paper_main_loewner_le (lo *: 1%:M)%R S -> paper_main_loewner_le S (hi *: 1%:M)%R ->
  0 < paper_main_pairing Z S ->
  paper_main_head_cone_sphere (hi / lo) (paper_main_head_normalize S) /\
  0 < paper_main_head_support Z (paper_main_head_cone_sphere (hi / lo)).
Proof.
move=> Hlo HSlo HShi HZS.
have HS0 : S != 0%R.
  apply/eqP => HS; rewrite HS pmh_pairing0r in HZS; exact: (Rlt_irrefl _ HZS).
have Hc := pmh_frobenius_gt0 _ S HS0.
have [Hl Hh] := paper_main_head_loewner_scale _ S (paper_main_frobenius S) lo hi Hc HSlo HShi.
have Hsph : paper_main_head_cone_sphere (hi / lo) (paper_main_head_normalize S).
  split; last exact: pmh_frobenius_normalize.
  exists (lo / paper_main_frobenius S)%R; split.
    by rewrite divr_gt0 //; apply/RltP.
  split; first exact: Hl.
  have -> : ((hi / lo) * (lo / paper_main_frobenius S) = hi / paper_main_frobenius S)%R.
    by rewrite mulrA divfK // lt0r_neq0 //; apply/RltP.
  exact: Hh.
split; first exact: Hsph.
have Hsupp := pmh_support_ge _ Z (paper_main_head_cone_sphere (hi / lo)) _
  (fun S' HS' => proj2 HS') Hsph.
apply: (Rlt_le_trans _ _ _ _ (elimT RleP Hsupp)).
rewrite /paper_main_head_normalize paper_main_pairing_scale.
apply/RltP; rewrite mulr_gt0 // ?invr_gt0 //.
exact: (introT RltP HZS).
Qed.

(* 2. Every unit dual vector has positive support. *)
Section All.
Variables (d n : nat) (W : nat -> 'M[R]_d).

(* The G12 head budget K = head_tail_constant theta * d * ln d. *)
Definition paper_main_head_budget (theta : R) : R :=
  head_tail_constant theta * INR d * ln (INR d).

Lemma pmhsa_tail_vector_head y J i :
  In i J -> paper_main_tail_list_vector y n J i = 0.
Proof.
move=> Hi; rewrite /paper_main_tail_list_vector.
case: (in_dec Nat.eq_dec i (tail_indices n J)) => [HT|HT] //=.
by have /outside_in [_ H] := HT.
Qed.

Lemma pmhsa_eps_half : (2 <= d)%coq_nat -> 1 / INR d ^ 2 <= 1 / 2.
Proof.
move=> Hd.
have H2 : 2 <= INR d by have := le_INR _ _ Hd; rewrite /=; lra.
have Hsq : 2 <= INR d ^ 2 by nra.
rewrite /Rdiv !Rmult_1_l; apply: Rinv_le_contravar => //; lra.
Qed.

Theorem paper_main_support_all (theta a b delta mu A : R) :
  (2 <= d)%coq_nat -> 0 < theta ->
  (forall i, (i < n)%nat -> paper_main_symmetric (W i)) ->
  0 < delta -> delta < a -> 0 < mu ->
  (forall J : list nat, NoDup J -> incl J (List.seq 0 n) ->
    INR (length J) <= paper_main_head_budget theta ->
    exists S0 : 'M[R]_d,
      paper_main_loewner_le (a *: 1%:M)%R S0 /\ paper_main_loewner_le S0 (b *: 1%:M)%R /\
      forall i, In i J -> paper_main_pairing (W i) S0 = 0) ->
  (forall J : list nat, NoDup J -> incl J (List.seq 0 n) ->
    INR (length J) <= paper_main_head_budget theta ->
    forall c : nat -> R, (forall i, ~ In i J -> c i = 0) ->
      mu * squared_norm c (List.seq 0 n) <=
        paper_main_frobenius (paper_main_support_combination d n W c) ^ 2) ->
  (forall c : nat -> R,
    paper_main_frobenius (paper_main_support_combination d n W c) <=
      A * euclidean_norm c (List.seq 0 n)) ->
  (forall J : list nat, NoDup J -> incl J (List.seq 0 n) ->
    INR (length J) <= paper_main_head_budget theta ->
    forall t : nat -> R, euclidean_norm t (List.seq 0 n) = 1 ->
      (forall i, In i J -> t i = 0) ->
      (forall i, Rabs (t i) <= theta / sqrt (INR d)) ->
      exists S : 'M[R]_d,
        paper_main_loewner_le ((a - delta) *: 1%:M)%R S /\
        paper_main_loewner_le S ((b + delta) *: 1%:M)%R /\
        (forall i, In i J -> paper_main_pairing (W i) S = 0) /\
        0 < paper_main_support_score d n W t S) ->
  A * (1 / INR d ^ 2) * (b + delta) * sqrt (INR d) < delta * (sqrt mu / 2) ->
  forall y : nat -> R, euclidean_norm y (List.seq 0 n) = 1 ->
    exists S : 'M[R]_d,
      paper_main_loewner_le ((a - delta) *: 1%:M)%R S /\
      paper_main_loewner_le S ((b + delta) *: 1%:M)%R /\
      0 < paper_main_support_score d n W y S.
Proof.
move=> Hd Hth HW Hd0 Hda Hmu Hsec HG HA Htail Hcond y Hy.
have Hd1 : (1 <= d)%coq_nat by lia.
have [J [HJ [Hincl [Hlen [Hmass Hcase]]]]] :=
  paper_main_head_tail_regularity theta d n y Hth Hd1 Hy.
case: Hcase => [Hsmall | [Hpos [Htu Htc]]].
  (* The tiny tail. *)
  have [S0 [Hlo [Hup HS0]]] := Hsec J HJ Hincl Hlen.
  exact: (paper_main_support_tiny d n W y J S0 a b delta mu A (1 / INR d ^ 2)
    HW Hy HJ Hincl Hsmall (pmhsa_eps_half Hd) Hmu (HG J HJ Hincl Hlen) HA
    Hd0 Hda Hlo Hup HS0 Hcond).
(* The capped tail. *)
have [S [Hlo [Hup [HS Hpos']]]] := Htail J HJ Hincl Hlen
  (paper_main_tail_list_vector y n J) Htu (fun i Hi => pmhsa_tail_vector_head y J i Hi) Htc.
exists S; split => //; split => //.
exact: (paper_main_support_spread d n W y J S HS Hpos Hpos').
Qed.

(* The cone form: positive support on K_((b + delta) / (a - delta)) \cap S_F. *)
Corollary paper_main_support_all_cone (theta a b delta mu A : R) :
  (2 <= d)%coq_nat -> 0 < theta ->
  (forall i, (i < n)%nat -> paper_main_symmetric (W i)) ->
  0 < delta -> delta < a -> 0 < mu ->
  (forall J : list nat, NoDup J -> incl J (List.seq 0 n) ->
    INR (length J) <= paper_main_head_budget theta ->
    exists S0 : 'M[R]_d,
      paper_main_loewner_le (a *: 1%:M)%R S0 /\ paper_main_loewner_le S0 (b *: 1%:M)%R /\
      forall i, In i J -> paper_main_pairing (W i) S0 = 0) ->
  (forall J : list nat, NoDup J -> incl J (List.seq 0 n) ->
    INR (length J) <= paper_main_head_budget theta ->
    forall c : nat -> R, (forall i, ~ In i J -> c i = 0) ->
      mu * squared_norm c (List.seq 0 n) <=
        paper_main_frobenius (paper_main_support_combination d n W c) ^ 2) ->
  (forall c : nat -> R,
    paper_main_frobenius (paper_main_support_combination d n W c) <=
      A * euclidean_norm c (List.seq 0 n)) ->
  (forall J : list nat, NoDup J -> incl J (List.seq 0 n) ->
    INR (length J) <= paper_main_head_budget theta ->
    forall t : nat -> R, euclidean_norm t (List.seq 0 n) = 1 ->
      (forall i, In i J -> t i = 0) ->
      (forall i, Rabs (t i) <= theta / sqrt (INR d)) ->
      exists S : 'M[R]_d,
        paper_main_loewner_le ((a - delta) *: 1%:M)%R S /\
        paper_main_loewner_le S ((b + delta) *: 1%:M)%R /\
        (forall i, In i J -> paper_main_pairing (W i) S = 0) /\
        0 < paper_main_support_score d n W t S) ->
  A * (1 / INR d ^ 2) * (b + delta) * sqrt (INR d) < delta * (sqrt mu / 2) ->
  forall y : nat -> R, euclidean_norm y (List.seq 0 n) = 1 ->
    0 < paper_main_head_support (paper_main_support_combination d n W y)
      (paper_main_head_cone_sphere ((b + delta) / (a - delta))).
Proof.
move=> Hd Hth HW Hd0 Hda Hmu Hsec HG HA Htail Hcond y Hy.
have [S [Hlo [Hup Hpos]]] := paper_main_support_all theta a b delta mu A
  Hd Hth HW Hd0 Hda Hmu Hsec HG HA Htail Hcond y Hy.
rewrite paper_main_support_score_pairing in Hpos.
have Had : 0 < a - delta by lra.
have [_ H] := paper_main_support_cone_sphere d _ S (a - delta) (b + delta) Had Hlo Hup Hpos.
exact: H.
Qed.

End All.
