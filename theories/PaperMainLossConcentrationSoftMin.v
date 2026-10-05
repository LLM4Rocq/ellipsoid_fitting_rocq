(* Concentration of the normalized finite-prior soft minimum.

   For row losses ell i j : list R -> R (row i < N, state j in a finite
   nonempty list I) that are continuous and take values in [0, 1], the
   normalized entropy-shifted soft minimum of the loss array
     Z = paper_main_loss_normalized_array p N beta I ell
       = (soft_min beta (sum_i ell i j (row i)) I + ln |I| / beta) / N
   (PaperMainLossNormalizedArray: continuous, values in [0, 1]) has row
   oscillation 1/N: replacing row k swaps one term ell k j z in every
   state, which changes the soft minimum by at most 1
   (paper_main_gibbs_row_change). The tails of
   PaperMainLossConcentrationTail with c = 1/N then give, for t > 0,
     P (Z <= E Z - t) <= exp (- N t^2 / 2),  P (E Z + t <= Z) <= exp (- N t^2 / 2),
   with no dependence on |I|, beta or the translations inside ell. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity
  PaperMainDataFeatureMomentsCoordinates PaperMainLossGibbs PaperMainLossArray
  PaperMainLossSoftNormalized PaperMainLossNormalizedArray
  PaperMainLossConcentrationRow PaperMainLossConcentrationTail.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Replacing row k swaps one term of the loss array. *)

Lemma paper_main_softmin_array_row p N (ell : nat -> nat -> list R -> R) k
    (a z z' b : list R) (j : nat) :
  (k < N)%coq_nat -> length a = (k * p)%coq_nat -> length z = p -> length z' = p ->
  (paper_main_loss_array p N ell (a ++ z ++ b)%list j - ell k j z =
   paper_main_loss_array p N ell (a ++ z' ++ b)%list j - ell k j z')%Rcoq.
Proof.
elim: k N ell a => [|k IH] N ell a HkN Ha Hz Hz'.
  case: a Ha => [|x a] Ha; last by rewrite /= in Ha.
  case: N HkN => [|N'] HkN; first lia.
  rewrite !List.app_nil_l !paper_main_loss_array_append //.
  by rewrite /Rminus; ring.
case: N HkN => [|N'] HkN; first lia.
have Hlen : length a = (p + k * p)%coq_nat by rewrite Ha /=.
have Ha1 : length (List.firstn p a) = p.
  by rewrite List.length_firstn Hlen; lia.
have Ha2 : length (List.skipn p a) = (k * p)%coq_nat.
  by rewrite List.length_skipn Hlen; lia.
rewrite -(List.firstn_skipn p a) -!List.app_assoc !paper_main_loss_array_append //.
have H := IH N' (fun i => ell (S i)) (List.skipn p a) ltac:(lia) Ha2 Hz Hz'.
lra.
Qed.

(* The normalized soft minimum has row oscillation 1/N. *)

Lemma paper_main_softmin_row_oscillation p N beta (I : list nat)
    (ell : nat -> nat -> list R -> R) :
  I <> nil -> (0 < beta)%Rcoq ->
  (forall i j xs, (i < N)%coq_nat -> In j I -> length xs = p ->
     (0 <= ell i j xs <= 1)%Rcoq) ->
  paper_main_row_oscillation N p (/ INR N)%Rcoq
    (paper_main_loss_normalized_array p N beta I ell).
Proof.
move=> HI Hb HB k a z z' b HkN Ha Hz Hz' Hlb.
have HkN' : (k < N)%coq_nat by apply/ssrnat.ltP.
have HNpos : (0 < INR N)%Rcoq by apply: lt_0_INR; lia.
have Hinv : (0 < / INR N)%Rcoq by apply: Rinv_0_lt_compat.
rewrite !paper_main_loss_normalized_arrayE /paper_main_loss_soft_normalized.
set g := fun s => (paper_main_loss_array p N ell (a ++ z ++ b)%list s - ell k s z)%Rcoq.
have E1 : paper_main_loss_array p N ell (a ++ z ++ b)%list =
    (fun s => g s + ell k s z)%Rcoq.
  by apply: functional_extensionality => s; rewrite /g; ring.
have E2 : paper_main_loss_array p N ell (a ++ z' ++ b)%list =
    (fun s => g s + ell k s z')%Rcoq.
  apply: functional_extensionality => s.
  rewrite /g (paper_main_softmin_array_row p N ell k a z z' b s) //; ring.
rewrite E1 E2.
have H := paper_main_gibbs_row_change beta g I (fun s => ell k s z) (fun s => ell k s z')
  Hb HI (fun s Hs => HB k s z HkN' Hs Hz) (fun s Hs => HB k s z' HkN' Hs Hz').
have Hr : Rabs (/ INR N) = / INR N by apply: Rabs_right; lra.
have key : forall A B L : R, (Rabs (A - B) <= 1)%Rcoq ->
    (Rabs (/ INR N * (A + L) - / INR N * (B + L)) <= / INR N)%Rcoq.
  move=> A B L HAB.
  have -> : (/ INR N * (A + L) - / INR N * (B + L) = / INR N * (A - B))%Rcoq by ring.
  rewrite Rabs_mult Hr.
  have := Rmult_le_compat_l _ _ _ (Rlt_le _ _ Hinv) HAB; lra.
exact: key.
Qed.

(* Bounds in [0, 1] give the uniform bound needed by the tails. *)

Lemma paper_main_softmin_abs_bound p N beta (I : list nat)
    (ell : nat -> nat -> list R -> R) :
  (0 < N)%N -> I <> nil -> (0 < beta)%Rcoq ->
  (forall i j xs, (i < N)%coq_nat -> In j I -> length xs = p ->
     (0 <= ell i j xs <= 1)%Rcoq) ->
  forall xs, length xs = (N * p)%nat ->
    (Rabs (paper_main_loss_normalized_array p N beta I ell xs) <= 1)%Rcoq.

Proof.
move=> HN HI Hb HB xs Hxs.
have HN' : (0 < N)%coq_nat by apply/ssrnat.ltP.
have [H0 H1] := paper_main_loss_normalized_array_bounds p N beta I ell HN' HI Hb HB xs Hxs.
by rewrite Rabs_right; lra.
Qed.

(* The lower tail: P (Z <= E Z - t) <= exp (- N t^2 / 2). *)

Theorem paper_main_softmin_lower_tail p N beta (I : list nat)
    (ell : nat -> nat -> list R -> R) (t : R) :
  (0 < N)%N -> I <> nil -> (0 < beta)%Rcoq -> (0 < t)%Rcoq ->
  (forall i j, (i < N)%coq_nat -> In j I -> finite_joint_continuous p (ell i j)) ->
  (forall i j xs, (i < N)%coq_nat -> In j I -> length xs = p ->
     (0 <= ell i j xs <= 1)%Rcoq) ->
  measurable [set x : (N * p).-tuple (measurableTypeR R) |
    (paper_main_loss_normalized_array p N beta I ell (tval x) <=
     gaussian_iterated_expectation (N * p)
       (paper_main_loss_normalized_array p N beta I ell) - t)%R] /\
  (gaussian_product_law (N * p)
     [set x | (paper_main_loss_normalized_array p N beta I ell (tval x) <=
       gaussian_iterated_expectation (N * p)
         (paper_main_loss_normalized_array p N beta I ell) - t)%R] <=
   ((exp (- (INR N * t ^ 2) / 2))%Rcoq)%:E)%E.
Proof.
move=> HN HI Hb Ht HC HB.
have HNpos : (0 < INR N)%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
have Hc : (0 < / INR N)%Rcoq by apply: Rinv_0_lt_compat.
have Hreg := paper_main_loss_normalized_array_regular p N beta I ell HI Hb HC HB.
have [Hm Hl] := paper_main_concentration_lower_tail N p
  (paper_main_loss_normalized_array p N beta I ell) 1 (/ INR N) t HN Hc Ht (proj1 Hreg)
  (paper_main_softmin_abs_bound p N beta I ell HN HI Hb HB)
  (paper_main_softmin_row_oscillation p N beta I ell HI Hb HB).
split => //.
have -> : (- (INR N * t ^ 2) / 2 = - (t ^ 2) / (2 * INR N * (/ INR N) ^ 2))%Rcoq.
  by field; lra.
exact: Hl.
Qed.

(* The upper tail: P (E Z + t <= Z) <= exp (- N t^2 / 2). *)

Theorem paper_main_softmin_upper_tail p N beta (I : list nat)
    (ell : nat -> nat -> list R -> R) (t : R) :
  (0 < N)%N -> I <> nil -> (0 < beta)%Rcoq -> (0 < t)%Rcoq ->
  (forall i j, (i < N)%coq_nat -> In j I -> finite_joint_continuous p (ell i j)) ->
  (forall i j xs, (i < N)%coq_nat -> In j I -> length xs = p ->
     (0 <= ell i j xs <= 1)%Rcoq) ->
  measurable [set x : (N * p).-tuple (measurableTypeR R) |
    (gaussian_iterated_expectation (N * p)
       (paper_main_loss_normalized_array p N beta I ell) + t <=
     paper_main_loss_normalized_array p N beta I ell (tval x))%R] /\
  (gaussian_product_law (N * p)
     [set x | (gaussian_iterated_expectation (N * p)
         (paper_main_loss_normalized_array p N beta I ell) + t <=
       paper_main_loss_normalized_array p N beta I ell (tval x))%R] <=
   ((exp (- (INR N * t ^ 2) / 2))%Rcoq)%:E)%E.
Proof.
move=> HN HI Hb Ht HC HB.
have HNpos : (0 < INR N)%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
have Hc : (0 < / INR N)%Rcoq by apply: Rinv_0_lt_compat.
have Hreg := paper_main_loss_normalized_array_regular p N beta I ell HI Hb HC HB.
have [Hm Hl] := paper_main_concentration_upper_tail N p
  (paper_main_loss_normalized_array p N beta I ell) 1 (/ INR N) t HN Hc Ht (proj1 Hreg)
  (paper_main_softmin_abs_bound p N beta I ell HN HI Hb HB)
  (paper_main_softmin_row_oscillation p N beta I ell HI Hb HB).
split => //.
have -> : (- (INR N * t ^ 2) / 2 = - (t ^ 2) / (2 * INR N * (/ INR N) ^ 2))%Rcoq.
  by field; lra.
exact: Hl.
Qed.

(* The moment generating function: E exp (lam (Z - E Z)) <= exp (lam^2 / (2 N)). *)

Theorem paper_main_softmin_mgf p N beta (I : list nat)
    (ell : nat -> nat -> list R -> R) (lam : R) :
  (0 < N)%N -> I <> nil -> (0 < beta)%Rcoq ->
  (forall i j, (i < N)%coq_nat -> In j I -> finite_joint_continuous p (ell i j)) ->
  (forall i j xs, (i < N)%coq_nat -> In j I -> length xs = p ->
     (0 <= ell i j xs <= 1)%Rcoq) ->
  (gaussian_iterated_expectation (N * p)
     (fun xs => exp (lam * (paper_main_loss_normalized_array p N beta I ell xs -
        gaussian_iterated_expectation (N * p)
          (paper_main_loss_normalized_array p N beta I ell)))) <=
   exp (lam ^ 2 / (2 * INR N)))%Rcoq.
Proof.
move=> HN HI Hb HC HB.
have HNpos : (0 < INR N)%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
have Hc : (0 < / INR N)%Rcoq by apply: Rinv_0_lt_compat.
have Hreg := paper_main_loss_normalized_array_regular p N beta I ell HI Hb HC HB.
have H := paper_main_concentration_rows N p
  (paper_main_loss_normalized_array p N beta I ell) 1 (/ INR N) lam (Rlt_le _ _ Hc)
  (proj1 Hreg) (paper_main_softmin_abs_bound p N beta I ell HN HI Hb HB)
  (paper_main_softmin_row_oscillation p N beta I ell HI Hb HB).
have -> : (lam ^ 2 / (2 * INR N) = lam ^ 2 * INR N * (/ INR N) ^ 2 / 2)%Rcoq.
  by field; lra.
exact: H.
Qed.
