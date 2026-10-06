(* Moments of one column of the square-free features under the Gaussian
   law. Coordinates are lists, as in Feature.DiagonalMoment. For a
   list ys of length d and a <> b below d, Y(ys) = (y_a y_b)^2 - 1. For a
   list xs of n * d coordinates, row i is xs_(i d), ..., xs_(i d + d - 1),
   and S_n(xs) = sum_(i < n) Y(row i of xs) (pmccm_S). E_D is the iterated
   Gaussian expectation gaussian_iterated_expectation in dimension D.
   1. pmccm_mono2: E_d [y_a^j y_b^k] = m_j m_k with m the Gaussian moments
      (from pmdm_factor and pmdm_marginal), so every polynomial in
      y_a^2 y_b^2 has an explicit expectation (pmccm_poly_exp).
   2. For a constant s (pmccm_shift1, pmccm_shift2, pmccm_shift4):
      E_d (s + Y) = s, E_d (s + Y)^2 = s^2 + 8 and
      E_d (s + Y)^4 = s^4 + 48 s^2 + 800 s + 10176. In particular E Y = 0,
      E Y^2 = 8 and E Y^4 = 10176.
   3. S_(n+1)(xs ++ ys) = S_n(xs) + Y(ys) (pmccm_S_app), so by induction
      over the rows (gaussian_iterated_suffix_expectation through
      pmdm_split_eq): E S_n = 0, E S_n^2 = 8 n and
      E S_n^4 = 10176 n + 192 n (n - 1) (pmccm_S_mean, pmccm_S_moment2 and
      pmccm_S_moment4). The last value is at most 10368 n^2 for n >= 1.
   Integrability comes from continuity with a polynomial bound
   (pmdf_regular). *)
From Stdlib Require Import Reals List Lia FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Gaussian.Line.Expectation Gaussian.Line.PolynomialGrowthIntegrals
  Gaussian.Iterated.SuffixMarginalDefinitions Gaussian.Iterated.LastIntegration
  Data.FeatureMomentsCoordinates Data.FeatureMoments PaperMainDefinitions
  Feature.DiagonalMoment.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Two coordinates of one row. *)

Lemma pmccm_mono2 d a b j k : (a < d)%N -> (b < d)%N -> a <> b ->
  gaussian_iterated_expectation d (fun ys => List.nth a ys 0 ^+ j * List.nth b ys 0 ^+ k) =
  moment_factor j * moment_factor k.
Proof.
move=> Ha Hb Hab.
have [Hj Ej] := pmdm_pow_moment j.
have [Hk Ek] := pmdm_pow_moment k.
have HG : pmdf_regular d (fun ys => List.nth b ys 0 ^+ k).
  by apply: pmdm_reg_exp; exact: pmdm_reg_nth.
have Hind : forall xs ys : list R, length xs = d -> length ys = d ->
    (forall c, c <> a -> List.nth c xs 0 = List.nth c ys 0) ->
    List.nth b xs 0 ^+ k = List.nth b ys 0 ^+ k.
  move=> xs ys _ _ Hxy; congr (_ ^+ _); apply: Hxy => Hba; exact: Hab (esym Hba).
have := pmdm_factor d a (fun x => x ^+ j) (fun ys => List.nth b ys 0 ^+ k) Ha Hj
  (pmdf_regular_integrable HG) Hind.
move=> ->.
by rewrite Ej (pmdm_marginal d b (fun x => x ^+ k) Hb Hk) Ek.
Qed.

(* Real combinations of the monomials u^k w^k, and their expectations. *)
Fixpoint pmccm_poly (cs : seq (R * nat)) (u w : R) : R :=
  if cs is p :: cs' then (p.1 * (u ^+ p.2 * w ^+ p.2) + pmccm_poly cs' u w)%R else 0%R.

Fixpoint pmccm_poly_moment (cs : seq (R * nat)) : R :=
  if cs is p :: cs' then
    (p.1 * (moment_factor p.2 * moment_factor p.2) + pmccm_poly_moment cs')%R
  else 0%R.

Lemma pmccm_poly_cons c k cs u w :
  pmccm_poly ((c, k) :: cs) u w = c * (u ^+ k * w ^+ k) + pmccm_poly cs u w.
Proof. by []. Qed.

Lemma pmccm_poly_nil u w : pmccm_poly [::] u w = 0.
Proof. by []. Qed.

Lemma pmccm_poly_moment_cons c k cs :
  pmccm_poly_moment ((c, k) :: cs) = c * (moment_factor k * moment_factor k) + pmccm_poly_moment cs.
Proof. by []. Qed.

Lemma pmccm_poly_moment_nil : pmccm_poly_moment [::] = 0.
Proof. by []. Qed.

Lemma pmccm_poly_exp d a b cs : (a < d)%N -> (b < d)%N -> a <> b ->
  pmdf_regular d (fun ys => pmccm_poly cs (List.nth a ys 0) (List.nth b ys 0)) /\
  gaussian_iterated_expectation d (fun ys => pmccm_poly cs (List.nth a ys 0) (List.nth b ys 0)) =
  pmccm_poly_moment cs.
Proof.
move=> Ha Hb Hab; elim: cs => [|[c k] cs [HR HE]] /=.
  split; first exact: pmdm_reg_const.
  exact: pmdm_E_const.
have Hm : pmdf_regular d (fun ys => List.nth a ys 0 ^+ k * List.nth b ys 0 ^+ k).
  by apply: pmdm_reg_mul; apply: pmdm_reg_exp; exact: pmdm_reg_nth.
have Hs : pmdf_regular d (fun ys => c * (List.nth a ys 0 ^+ k * List.nth b ys 0 ^+ k)).
  exact: pmdm_reg_scale.
split; first exact: pmdm_reg_add.
by rewrite pmdm_E_add // pmdm_E_scale // pmccm_mono2 // HE.
Qed.

(* 2. Y = (u w)^2 - 1, shifted by a constant. *)
Definition pmccm_y (u w : R) : R := ((u * w) ^+ 2 - 1)%R.

Lemma pmccm_poly_eval d a b (f : R -> R -> R) cs : (a < d)%N -> (b < d)%N -> a <> b ->
  (forall u w, f u w = pmccm_poly cs u w) ->
  gaussian_iterated_expectation d (fun ys => f (List.nth a ys 0) (List.nth b ys 0)) =
  pmccm_poly_moment cs.
Proof.
move=> Ha Hb Hab Hf.
have [_ HE] := pmccm_poly_exp d a b cs Ha Hb Hab.
rewrite -HE; apply: gaussian_iterated_expectation_ext => ys _; exact: Hf.
Qed.

Lemma pmccm_shift1 d a b (s : R) : (a < d)%N -> (b < d)%N -> a <> b ->
  gaussian_iterated_expectation d (fun ys => s + pmccm_y (List.nth a ys 0) (List.nth b ys 0)) = s.
Proof.
move=> Ha Hb Hab.
have E : forall u w t : R,
    t + ((u * w) ^+ 2 - 1) = 1 * (u ^+ 2 * w ^+ 2) + ((t - 1) * (u ^+ 0 * w ^+ 0) + 0).
  by move=> u w t; ring.
have Hid : forall u w : R, s + pmccm_y u w = pmccm_poly [:: (1, 2%N); (s - 1, 0%N)] u w.
  by move=> u w; rewrite !pmccm_poly_cons pmccm_poly_nil /pmccm_y; exact: E.
have := pmccm_poly_eval d a b (fun u w => s + pmccm_y u w) _ Ha Hb Hab Hid.
move=> ->.
rewrite !pmccm_poly_moment_cons pmccm_poly_moment_nil !pmdm_mfS !pmdm_mf0; ring.
Qed.

Lemma pmccm_shift2 d a b (s : R) : (a < d)%N -> (b < d)%N -> a <> b ->
  gaussian_iterated_expectation d (fun ys => (s + pmccm_y (List.nth a ys 0) (List.nth b ys 0)) ^+ 2) =
  s ^+ 2 + 8.
Proof.
move=> Ha Hb Hab.
have E : forall u w t : R,
    (t + ((u * w) ^+ 2 - 1)) ^+ 2 =
    1 * (u ^+ 4 * w ^+ 4) + (2 * (t - 1) * (u ^+ 2 * w ^+ 2) +
      ((t - 1) ^+ 2 * (u ^+ 0 * w ^+ 0) + 0)).
  by move=> u w t; ring.
have Hid : forall u w : R, (s + pmccm_y u w) ^+ 2 =
    pmccm_poly [:: (1, 4%N); (2 * (s - 1), 2%N); ((s - 1) ^+ 2, 0%N)] u w.
  by move=> u w; rewrite !pmccm_poly_cons pmccm_poly_nil /pmccm_y; exact: E.
have := pmccm_poly_eval d a b (fun u w => (s + pmccm_y u w) ^+ 2) _ Ha Hb Hab Hid.
move=> ->.
rewrite !pmccm_poly_moment_cons pmccm_poly_moment_nil !pmdm_mfS !pmdm_mf0; ring.
Qed.

Lemma pmccm_shift4 d a b (s : R) : (a < d)%N -> (b < d)%N -> a <> b ->
  gaussian_iterated_expectation d (fun ys => (s + pmccm_y (List.nth a ys 0) (List.nth b ys 0)) ^+ 4) =
  s ^+ 4 + 48 * s ^+ 2 + 800 * s + 10176.
Proof.
move=> Ha Hb Hab.
have E : forall u w t : R,
    (t + ((u * w) ^+ 2 - 1)) ^+ 4 =
    1 * (u ^+ 8 * w ^+ 8) + (4 * (t - 1) * (u ^+ 6 * w ^+ 6) +
      (6 * (t - 1) ^+ 2 * (u ^+ 4 * w ^+ 4) + (4 * (t - 1) ^+ 3 * (u ^+ 2 * w ^+ 2) +
      ((t - 1) ^+ 4 * (u ^+ 0 * w ^+ 0) + 0)))).
  by move=> u w t; ring.
have Hid : forall u w : R, (s + pmccm_y u w) ^+ 4 =
    pmccm_poly [:: (1, 8%N); (4 * (s - 1), 6%N); (6 * (s - 1) ^+ 2, 4%N);
      (4 * (s - 1) ^+ 3, 2%N); ((s - 1) ^+ 4, 0%N)] u w.
  by move=> u w; rewrite !pmccm_poly_cons pmccm_poly_nil /pmccm_y; exact: E.
have := pmccm_poly_eval d a b (fun u w => (s + pmccm_y u w) ^+ 4) _ Ha Hb Hab Hid.
move=> ->.
rewrite !pmccm_poly_moment_cons pmccm_poly_moment_nil !pmdm_mfS !pmdm_mf0; ring.
Qed.

(* 3. Rows of a list of n * d coordinates. *)
Definition pmccm_row d a b (i : nat) (xs : list R) : R :=
  pmccm_y (List.nth (i * d + a) xs 0) (List.nth (i * d + b) xs 0).

Definition pmccm_S d a b (n : nat) (xs : list R) : R := \sum_(i < n) pmccm_row d a b i xs.

Lemma pmccm_S_reg d a b n k : (a < d)%N -> (b < d)%N ->
  pmdf_regular (n * d) (fun xs => pmccm_S d a b n xs ^+ k).
Proof.
move=> Ha Hb; apply: pmdm_reg_exp; rewrite /pmccm_S; apply: pmdm_reg_sum => i.
rewrite /pmccm_row /pmccm_y; apply: pmdm_reg_sub; last exact: pmdm_reg_const.
apply: pmdm_reg_exp; apply: pmdm_reg_mul; apply: pmdm_reg_nth.
- exact: (pmdm_index_lt d n i a (ltn_ord i) Ha).
- exact: (pmdm_index_lt d n i b (ltn_ord i) Hb).
Qed.

Lemma pmccm_S_reg1 d a b n : (a < d)%N -> (b < d)%N -> pmdf_regular (n * d) (pmccm_S d a b n).
Proof.
move=> Ha Hb.
apply: (pmdf_regular_ext _ (fun xs => pmccm_S d a b n xs ^+ 1)) => [xs|]; first by rewrite expr1.
exact: pmccm_S_reg.
Qed.

Lemma pmccm_row_app_lt d a b n i xs ys : (a < d)%N -> (b < d)%N ->
  length xs = (n * d)%N -> (i < n)%N -> pmccm_row d a b i (xs ++ ys) = pmccm_row d a b i xs.
Proof.
move=> Ha Hb Hxs Hi.
have H1 : (i * d + a < length xs)%coq_nat.
  by rewrite Hxs; apply/ssrnat.ltP; exact: (pmdm_index_lt d n i a Hi Ha).
have H2 : (i * d + b < length xs)%coq_nat.
  by rewrite Hxs; apply/ssrnat.ltP; exact: (pmdm_index_lt d n i b Hi Hb).
by rewrite /pmccm_row (List.app_nth1 _ _ _ H1) (List.app_nth1 _ _ _ H2).
Qed.

Lemma pmccm_row_app_last d a b n xs ys : length xs = (n * d)%N ->
  pmccm_row d a b n (xs ++ ys) = pmccm_y (List.nth a ys 0) (List.nth b ys 0).
Proof.
move=> Hxs; rewrite /pmccm_row -Hxs -plusE.
by rewrite !List.app_nth2_plus.
Qed.

Lemma pmccm_S_app d a b n xs ys : (a < d)%N -> (b < d)%N -> length xs = (n * d)%N ->
  pmccm_S d a b n.+1 (xs ++ ys) = pmccm_S d a b n xs + pmccm_y (List.nth a ys 0) (List.nth b ys 0).
Proof.
move=> Ha Hb Hxs; rewrite /pmccm_S big_ord_recr /= (pmccm_row_app_last d a b n xs ys Hxs).
congr (_ + _); apply: eq_bigr => i _.
exact: (pmccm_row_app_lt d a b n i xs ys Ha Hb Hxs (ltn_ord i)).
Qed.

(* 4. Moments of the row sum, by induction over the rows. *)
Lemma pmccm_S_mean d a b n : (a < d)%N -> (b < d)%N -> a <> b ->
  gaussian_iterated_expectation (n * d) (pmccm_S d a b n) = 0.
Proof.
move=> Ha Hb Hab; elim: n => [|n IH].
  rewrite mul0n.
  transitivity (gaussian_iterated_expectation 0 (fun _ => 0%R)).
    by apply: gaussian_iterated_expectation_ext => xs _; rewrite /pmccm_S big_ord0.
  exact: pmdm_E_const.
rewrite pmdm_dim.
have Hstep : forall xs, length xs = (n * d)%N ->
    gaussian_iterated_expectation d (fun ys => pmccm_S d a b n.+1 (xs ++ ys)) = pmccm_S d a b n xs.
  move=> xs Hxs.
  transitivity (gaussian_iterated_expectation d
    (fun ys => pmccm_S d a b n xs + pmccm_y (List.nth a ys 0) (List.nth b ys 0))).
    by apply: gaussian_iterated_expectation_ext => ys _; rewrite pmccm_S_app.
  exact: pmccm_shift1.
by rewrite (pmdm_split_eq _ _ _ _ Hstep) IH.
Qed.

Lemma pmccm_S_moment2 d a b n : (a < d)%N -> (b < d)%N -> a <> b ->
  gaussian_iterated_expectation (n * d) (fun xs => pmccm_S d a b n xs ^+ 2) = 8 * n%:R.
Proof.
move=> Ha Hb Hab; elim: n => [|n IH].
  rewrite mul0n mulr0.
  transitivity (gaussian_iterated_expectation 0 (fun _ => 0%R)).
    by apply: gaussian_iterated_expectation_ext => xs _; rewrite /pmccm_S big_ord0 expr0n.
  exact: pmdm_E_const.
rewrite pmdm_dim.
have Hstep : forall xs, length xs = (n * d)%N ->
    gaussian_iterated_expectation d (fun ys => pmccm_S d a b n.+1 (xs ++ ys) ^+ 2) =
    pmccm_S d a b n xs ^+ 2 + 8.
  move=> xs Hxs.
  transitivity (gaussian_iterated_expectation d
    (fun ys => (pmccm_S d a b n xs + pmccm_y (List.nth a ys 0) (List.nth b ys 0)) ^+ 2)).
    by apply: gaussian_iterated_expectation_ext => ys _; rewrite pmccm_S_app.
  exact: pmccm_shift2.
rewrite (pmdm_split_eq _ _ _ _ Hstep) pmdm_E_add.
- exact: pmccm_S_reg.
- exact: pmdm_reg_const.
- by rewrite IH pmdm_E_const mulrSr; ring.
Qed.

Theorem pmccm_S_moment4 d a b n : (a < d)%N -> (b < d)%N -> a <> b ->
  gaussian_iterated_expectation (n * d) (fun xs => pmccm_S d a b n xs ^+ 4) =
  10176 * n%:R + 192 * n%:R * (n%:R - 1).
Proof.
move=> Ha Hb Hab; elim: n => [|n IH].
  rewrite mul0n.
  transitivity (gaussian_iterated_expectation 0 (fun _ => 0%R)).
    by apply: gaussian_iterated_expectation_ext => xs _; rewrite /pmccm_S big_ord0 expr0n.
  by rewrite pmdm_E_const; ring.
rewrite pmdm_dim.
have Hstep : forall xs, length xs = (n * d)%N ->
    gaussian_iterated_expectation d (fun ys => pmccm_S d a b n.+1 (xs ++ ys) ^+ 4) =
    pmccm_S d a b n xs ^+ 4 + 48 * pmccm_S d a b n xs ^+ 2 + 800 * pmccm_S d a b n xs + 10176.
  move=> xs Hxs.
  transitivity (gaussian_iterated_expectation d
    (fun ys => (pmccm_S d a b n xs + pmccm_y (List.nth a ys 0) (List.nth b ys 0)) ^+ 4)).
    by apply: gaussian_iterated_expectation_ext => ys _; rewrite pmccm_S_app.
  exact: pmccm_shift4.
have R4 := pmccm_S_reg d a b n 4 Ha Hb.
have R2 := pmccm_S_reg d a b n 2 Ha Hb.
have R1 := pmccm_S_reg1 d a b n Ha Hb.
have R2s : pmdf_regular (n * d) (fun xs => 48 * pmccm_S d a b n xs ^+ 2) by exact: pmdm_reg_scale.
have R1s : pmdf_regular (n * d) (fun xs => 800 * pmccm_S d a b n xs) by exact: pmdm_reg_scale.
have R42 : pmdf_regular (n * d)
    (fun xs => pmccm_S d a b n xs ^+ 4 + 48 * pmccm_S d a b n xs ^+ 2) by exact: pmdm_reg_add.
have R421 : pmdf_regular (n * d) (fun xs =>
    pmccm_S d a b n xs ^+ 4 + 48 * pmccm_S d a b n xs ^+ 2 + 800 * pmccm_S d a b n xs).
  exact: pmdm_reg_add.
rewrite (pmdm_split_eq _ _ _ _ Hstep).
rewrite pmdm_E_add; [exact: R421 | exact: pmdm_reg_const |].
rewrite pmdm_E_add; [exact: R42 | exact: R1s |].
rewrite pmdm_E_add; [exact: R4 | exact: R2s |].
rewrite pmdm_E_scale; [exact: R2 |].
rewrite pmdm_E_scale; [exact: R1 |].
rewrite pmdm_E_const IH (pmccm_S_moment2 d a b n Ha Hb Hab) (pmccm_S_mean d a b n Ha Hb Hab).
rewrite mulrSr; ring.
Qed.
