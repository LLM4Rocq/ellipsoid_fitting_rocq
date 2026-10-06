(* Gaussian moments of coordinate monomials, for the walk expansions of the
   square-free feature Gram matrix.

   A word w is a finite list of coordinate indices. Its monomial is
   x^w = prod_(t in w) x_t (pmsw_mono), with x_t = List.nth t xs 0. For a
   word in D coordinates (every index < D):
   - pmsw_mono_reg: x^w is continuous with a polynomial bound
     (pmdf_regular), hence integrable;
   - paper_main_gaussian_monomial_moment: the iterated Gaussian expectation
     is E_D x^w = prod_(c < D) moment_factor (count of c in w)
     (pmsw_moment), by induction on D through the definition of
     gaussian_iterated_expectation, with the one-coordinate moments
     pmdm_pow_moment of Feature.DiagonalMoment;
   - moment_factor k is 0 for odd k, positive for even k and nonnegative
     for every k (pmsw_mf_odd, pmsw_mf_gt0, pmsw_mf_ge0), so the moment is 0
     when some multiplicity is odd (paper_main_monomial_moment_odd). *)
From Stdlib Require Import Reals List Lia FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Gaussian.Line.Expectation Gaussian.Line.PolynomialGrowthIntegrals
  GaussianProbabilityProductDefinitions Data.FeatureMomentsCoordinates
  Data.FeatureMoments Feature.DiagonalMoment.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Monomials of words. *)
Definition pmsw_mono (w : seq nat) (xs : list R) : R := \prod_(t <- w) List.nth t xs 0.

Definition pmsw_moment (D : nat) (w : seq nat) : R :=
  \prod_(c < D) moment_factor (count_mem (c : nat) w).

(* Drop the first coordinate: the indices t > 0, shifted down by one. *)
Definition pmsw_shift (w : seq nat) : seq nat := map predn (seq.filter (fun t => t != 0%N) w).

Lemma pmsw_mono_nil xs : pmsw_mono [::] xs = 1.
Proof. by rewrite /pmsw_mono big_nil. Qed.

Lemma pmsw_mono_cons1 t w xs : pmsw_mono (t :: w) xs = List.nth t xs 0 * pmsw_mono w xs.
Proof. by rewrite /pmsw_mono big_cons. Qed.

Lemma pmsw_mono_cat w1 w2 xs : pmsw_mono (w1 ++ w2) xs = pmsw_mono w1 xs * pmsw_mono w2 xs.
Proof. by rewrite /pmsw_mono big_cat. Qed.

Lemma pmsw_mono_head x xs w :
  pmsw_mono w (x :: xs) = x ^+ count_mem 0%N w * pmsw_mono (pmsw_shift w) xs.
Proof.
elim: w => [|t w IH]; first by rewrite !pmsw_mono_nil expr0 mulr1.
rewrite pmsw_mono_cons1 IH.
case: t => [|t] /=.
  by rewrite add1n exprS mulrA.
by rewrite add0n pmsw_mono_cons1 mulrCA.
Qed.

Lemma pmsw_count_shift w c : count_mem c (pmsw_shift w) = count_mem c.+1 w.
Proof.
elim: w => [|t w IH] //=.
by case: t => [|t] /=; rewrite IH // eqSS.
Qed.

Lemma pmsw_all_shift D w :
  all (fun t => (t < D.+1)%N) w -> all (fun t => (t < D)%N) (pmsw_shift w).
Proof.
elim: w => [|t w IH] //= /andP [Ht Hw].
case: t Ht => [|t] Ht /=; first exact: IH.
have Ht' : (t < D)%N by exact: Ht.
by rewrite Ht' IH.
Qed.

(* 2. Regularity. *)
Lemma pmsw_mono_reg D w : all (fun t => (t < D)%N) w -> pmdf_regular D (pmsw_mono w).
Proof.
elim: w => [|t w IH] /=.
  move=> _; apply: (pmdf_regular_ext _ (fun _ => 1)) => [xs|].
    by rewrite pmsw_mono_nil.
  exact: pmdm_reg_const.
case/andP => Ht Hw.
apply: (pmdf_regular_ext _ (fun xs => List.nth t xs 0 * pmsw_mono w xs)) => [xs|].
  by rewrite pmsw_mono_cons1.
by apply: pmdm_reg_mul; [exact: pmdm_reg_nth | exact: IH].
Qed.

(* 3. The moment of a monomial. *)
Theorem paper_main_gaussian_monomial_moment D w :
  all (fun t => (t < D)%N) w ->
  gaussian_iterated_expectation D (pmsw_mono w) = pmsw_moment D w.
Proof.
elim: D w => [|D IH] w Hw.
  case: w Hw => [|t w] //= _.
  by rewrite /pmsw_moment big_ord0 pmsw_mono_nil.
have Hs := pmsw_all_shift D w Hw.
have Hreg := pmsw_mono_reg D (pmsw_shift w) Hs.
have [Hk Ek] := pmdm_pow_moment (count_mem 0%N w).
have E1 : (fun x => gaussian_iterated_expectation D (fun xs => pmsw_mono w (x :: xs))) =
    (fun x => pmsw_moment D (pmsw_shift w) * x ^+ count_mem 0%N w).
  apply: functional_extensionality => x.
  transitivity (gaussian_iterated_expectation D
    (fun xs => x ^+ count_mem 0%N w * pmsw_mono (pmsw_shift w) xs)).
    by apply: gaussian_iterated_expectation_ext => xs _; rewrite pmsw_mono_head.
  by rewrite pmdm_E_scale // IH // mulrC.
transitivity (gaussian_expectation
  (fun x => pmsw_moment D (pmsw_shift w) * x ^+ count_mem 0%N w)).
  by rewrite -E1.
rewrite (gaussian_expectation_scale _ (pmsw_moment D (pmsw_shift w)) Hk) Ek.
rewrite /pmsw_moment big_ord_recl /= mulrC; congr (_ * _).
by apply: eq_bigr => c _; rewrite pmsw_count_shift.
Qed.

(* 4. Odd multiplicities vanish; the moment factors are nonnegative. *)
Lemma pmsw_mf_odd_double n : moment_factor n.*2.+1 = 0.
Proof.
elim: n => [|n IH]; first by [].
by rewrite doubleS pmdm_mfS IH mulr0.
Qed.

Lemma pmsw_mf_even_double n : 0 < moment_factor n.*2.
Proof.
elim: n => [|n IH]; first by rewrite pmdm_mf0 ltr01.
by rewrite doubleS pmdm_mfS mulr_gt0 // ltr0n.
Qed.

Lemma pmsw_mf_odd k : odd k -> moment_factor k = 0.
Proof.
move=> Hk; rewrite -(odd_double_half k) Hk add1n; exact: pmsw_mf_odd_double.
Qed.

Lemma pmsw_mf_gt0 k : ~~ odd k -> 0 < moment_factor k.
Proof.
move=> Hk; rewrite -(odd_double_half k) (negbTE Hk) add0n; exact: pmsw_mf_even_double.
Qed.

Lemma pmsw_mf_ge0 k : 0 <= moment_factor k.
Proof.
by case Hk: (odd k); [rewrite pmsw_mf_odd | apply: ltW; rewrite pmsw_mf_gt0 ?Hk].
Qed.

Theorem paper_main_monomial_moment_odd D w (c : 'I_D) :
  odd (count_mem (c : nat) w) -> pmsw_moment D w = 0.
Proof.
move=> Hodd; rewrite /pmsw_moment (bigD1 c) //=.
by rewrite (pmsw_mf_odd _ Hodd) mul0r.
Qed.
