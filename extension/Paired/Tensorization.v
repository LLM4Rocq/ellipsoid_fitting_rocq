(* Moment and tail bounds for the latent-sign law, at Stdlib's R: item R2a of
   phase 9 (notes/phase6-three-extensions.md, section 2.3, (12) to (14)),
   the facts on h = paired_kernel that the tensorization bounds use. The
   law of one point is that of LatentSignScope (latent_point_expectation),
   and its two components are the product laws latent_side mu d s and
   latent_side mu d (- s) of Paired/Scope, of the coordinate laws
   paired_law mu s and paired_law mu (- s).

   1. Moments of h, over any realType and c > 0, for a law P with
      sym_uniform_spec c P and h = legendre4 c: int h^2 dP = 1/9, since
      int h dlam_1 = 1/9 and int h dlam_0 = 0 (Rintegral_legendre_h of
      Paired/Scope) and h (1 + h) - h = h^2 (Rintegral_legendre_sq); hence
      int h^2 dlam_a + int h^2 dlam_(-a) = 2/9 (Rintegral_legendre_sq_sum).
   2. The sum S = sum_(j < d) h(x_j), for 0 <= s <= 1 and the uniform law
      mu. Under latent_side mu d a, E h(x_j) = a / 9, E h(x_j)^2 is the
      second moment q_a of h under paired_law mu a, and
      E h(x_j) h(x_k) = (a / 9)^2 for j != k, so E S = d a / 9 and
      E S^2 = d q_a + d (d - 1) a^2 / 81. Averaging over a = s and a = - s
      with q_s + q_(-s) = 2 / 9: latent_kernel_sq_at, E h(x_j)^2 = 1/9 for
      every j < d; latent_kernel_sum_moments, E S = 0 and
      E S^2 = d / 9 + d (d - 1) s^2 / 81; latent_kernel_sum_variance, the
      same value for Var S.
   3. Hoeffding's inequality under each component, for -1 <= a <= 1.
      paired_kernel_subgaussian: h - a / 9 is subgaussian with constant 2
      under paired_law mu a, since it lies in [-3/7 - 1/9, 1 + 1/9] on
      [-sqrt 3, sqrt 3], which carries the law, and (10/9)^2 / 4 <= 1/3
      with exp (1/3) <= 2. latent_side_mgf: the moment generating function
      of sum_k b_k (h(x_k) - a / 9) under latent_side mu d a is at most
      exp (12 l^2 sum_k b_k^2) (subgaussian_sum_mgf of
      library/probability/subgaussian.v). latent_side_tail: with the
      exponential Markov inequality (measure_ge_expR of
      library/comparison/normal_mgf.v) at l = u / (24 sum_k b_k^2),
      P(sum_k b_k (h(x_k) - a / 9) >= u) <= exp (- u^2 / (48 sum_k b_k^2))
      for u >= 0. latent_side_hoeffding: for a set J of m > 0 coordinates,
      P(sum_(k in J) h(x_k) <= t) <= exp (- (m a / 9 - t)^2 / (48 m)) for
      t <= m a / 9, and P(sum_(k in J) h(x_k) >= t) <=
      exp (- (t - m a / 9)^2 / (48 m)) for t >= m a / 9.
      latent_side_sign_hoeffding: under the component latent_param s c of
      sign sigma = latent_param 1 c, P(sigma sum_(k in J) h(x_k) <= t) <=
      exp (- (m s / 9 - t)^2 / (48 m)) for t <= m s / 9. The constant 48
      is not the sharp constant of Hoeffding's inequality.
   4. The sign indicator and the other coordinates. latent_point_prob: the
      probability of a measurable set of points under the latent law is the
      average of its probabilities under the two components (from
      latent_point_expectationE of Paired/Scope). For the test function
      f = latent_sign_test d = 1{S > 0}: latent_sign_variance, for d >= 1,
      1/4 - exp (- d s^2 / 1944) / 4 <= Var f <= 1/4, since E f is within
      exp (- d s^2 / 3888) / 2 of 1/2 by item 3; latent_sign_variance_lim,
      Var f -> 1/4 as d -> oo for a fixed s > 0. latent_other_small: for
      j < d and 18 <= (d - 1) s,
      P(|sum_(k < d, k != j) h(x_k)| <= 1) <= exp (- (d - 1) s^2 / 15552),
      by item 3 with t = 1 under the component s and t = - 1 under the
      component - s. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import derive realfun exp.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg density_law.
From GaussianAnalysis.probability Require Import subgaussian.
From GaussianAnalysis.comparison Require Import normal_mgf.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import PairedDefinitions.
From EllipsoidUniversality Require Import LatentSignDefinitions LatentSignScope.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Paired Require Import Uniform Law LatentSign Scope.
From EllipsoidUniversality.Gaussian Require Import InProbability.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 0. Arithmetic. *)

Lemma seven_thirds_ge1 {RT : realType} : (1 : RT) <= 7%:R / 3%:R.
Proof. by rewrite ler_pdivlMr ?ltr0n // mul1r ler_nat. Qed.

Lemma kernel_dev_bound {RT : realType} (h a : RT) :
  - (3%:R / 7%:R) <= h <= 1 -> -1 <= a <= 1 ->
  (h - a / 9%:R) ^+ 2 / 2 ^+ 2 <= 3%:R^-1.
Proof.
move=> /andP[h1 h2] /andP[a1 a2].
have u1 : h - a / 9%:R <= 10%:R / 9%:R by lra.
have u2 : - (10%:R / 9%:R) <= h - a / 9%:R by lra.
nra.
Qed.

Lemma kernel_density_ge0 {RT : realType} (h a : RT) :
  - (3%:R / 7%:R) <= h <= 1 -> -1 <= a <= 1 -> 0 <= 1 + a * h.
Proof. by move=> /andP[h1 h2] /andP[a1 a2]; nra. Qed.

Lemma sign_variance_bound {RT : realType} (pS pN e : RT) :
  0 <= pN -> pN <= e -> 1 - e <= pS -> pS <= 1 ->
  4%:R^-1 - e ^+ 2 / 4%:R <=
    (pS + pN) / 2%:R - ((pS + pN) / 2%:R) ^+ 2 <= 4%:R^-1.
Proof.
move=> n0 ne se s1; apply/andP; split; last first.
  have := sqr_ge0 ((pS + pN) / 2%:R - 2%:R^-1); nra.
have h1 : pS + pN - 1 <= e by lra.
have h2 : - e <= pS + pN - 1 by lra.
nra.
Qed.

Lemma other_exponent {RT : realType} (m s : RT) : 0 < m -> 18%:R <= m * s ->
  m * s ^+ 2 / (48%:R * 324%:R) <= (m * s / 9%:R - 1) ^+ 2 / (48%:R * m).
Proof.
move=> m0 ms.
have mn : m != 0 by rewrite gt_eqF.
have e : m * s ^+ 2 / (48%:R * 324%:R) = (m * s / 18%:R) ^+ 2 / (48%:R * m).
  by field.
have h1 : 0 <= m * s / 18%:R by lra.
have h2 : m * s / 18%:R <= m * s / 9%:R - 1 by lra.
rewrite e ler_pM2r ?invr_gt0 ?mulr_gt0 ?ltr0n //.
by rewrite ler_sqr ?nnegrE //; apply: le_trans h2.
Qed.

Lemma tail_exponent {RT : realType} (u B : RT) : 0 < B ->
  3 * (u / (24%:R * B)) ^+ 2 * (B * 2 ^+ 2) + - (u / (24%:R * B) * u) =
  - (u ^+ 2 / (48%:R * B)).
Proof.
move=> B0; have Bn : B != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma avg_le {RT : realType} (x y z : RT) :
  x <= z -> y <= z -> (x + y) / 2%:R <= z.
Proof. by move=> h1 h2; lra. Qed.

Lemma sub_le_swap {RT : realType} (x y z : RT) : x - y <= z -> x - z <= y.
Proof. by move=> h; lra. Qed.

Lemma prod_ge_pos {RT : realType} (m s : RT) :
  0 <= s -> 18%:R <= m * s -> 0 < m.
Proof. by move=> s0 h; nra. Qed.

Lemma div9_ge1 {RT : realType} (w : RT) : 18%:R <= w -> 1 <= w / 9%:R.
Proof. by move=> h; lra. Qed.

Lemma abs_quarter {RT : realType} (V e eps : RT) :
  4%:R^-1 - e / 4%:R <= V -> V <= 4%:R^-1 -> 0 <= e -> 2 * e <= eps ->
  `|V - 4%:R^-1| <= eps.
Proof. by move=> h1 h2 e0 h3; rewrite ler_norml; apply/andP; split; lra. Qed.

(* 1. Moments of h. *)

Section legendre_moments.
Context {RT : realType}.
Variables (c : RT) (P : probability (measurableTypeR RT) RT).
Hypotheses (c0 : 0 < c) (hP : sym_uniform_spec c P).

Let ch : continuous (legendre4 c).
Proof. exact: continuous_legendre4. Qed.

Let cpow k : continuous (fun x => legendre4 c x ^+ k).
Proof.
move=> x; apply: (@cvg_comp _ _ _ (legendre4 c) (fun y => y ^+ k)).
  exact: ch.
exact: exprn_continuous.
Qed.

Let cmul (e : RT) (f : RT -> RT) : continuous f ->
  continuous (fun x => f x * (1 + e * legendre4 c x)).
Proof.
move=> cf x; apply: cvgM; first exact: cf.
apply: cvgD; first exact: cvg_cst.
by apply: cvgM; [exact: cvg_cst|exact: ch].
Qed.

(* int h^2 dP = int h dlam_1 - int h dlam_0 = 1/9. *)
Lemma Rintegral_legendre_sq : \int[P]_x (legendre4 c x ^+ 2) = 9%:R^-1.
Proof.
have h1 : -1 <= (1 : RT) <= 7%:R / 3%:R.
  by rewrite seven_thirds_ge1 andbT -subr_ge0 opprK addr_ge0 ?ler01.
have h0 : -1 <= (0 : RT) <= 7%:R / 3%:R.
  by rewrite lerN10 /= divr_ge0 ?ler0n.
have [_ e1] := legendre_law_cont c P c0 hP 1 _ h1 ch.
have [_ e0] := legendre_law_cont c P c0 hP 0 _ h0 ch.
have i1 := integrable_sym_uniform c P c0 hP _ (cmul 1 _ ch).
have i0 := integrable_sym_uniform c P c0 hP _ (cmul 0 _ ch).
transitivity (\int[legendre_law c P 1]_x legendre4 c x -
    \int[legendre_law c P 0]_x legendre4 c x).
  rewrite e1 e0 -RintegralB //.
  by apply: eq_Rintegral => x _; ring.
rewrite (Rintegral_legendre_h c P c0 hP 1 h1).
by rewrite (Rintegral_legendre_h c P c0 hP 0 h0) mul0r subr0 mul1r.
Qed.

(* int h^2 dlam_a + int h^2 dlam_(-a) = 2 int h^2 dP = 2/9. *)
Lemma Rintegral_legendre_sq_sum a : -1 <= a <= 7%:R / 3%:R ->
  -1 <= - a <= 7%:R / 3%:R ->
  \int[legendre_law c P a]_x (legendre4 c x ^+ 2) +
  \int[legendre_law c P (- a)]_x (legendre4 c x ^+ 2) = 2%:R / 9%:R.
Proof.
move=> ha hna.
have [_ ea] := legendre_law_cont c P c0 hP a _ ha (cpow 2).
have [_ ena] := legendre_law_cont c P c0 hP (- a) _ hna (cpow 2).
have ia := integrable_sym_uniform c P c0 hP _ (cmul a _ (cpow 2)).
have ina := integrable_sym_uniform c P c0 hP _ (cmul (- a) _ (cpow 2)).
have i2 := integrable_sym_uniform c P c0 hP _ (cpow 2).
rewrite ea ena -RintegralD //.
transitivity (\int[P]_x (2%:R * legendre4 c x ^+ 2)).
  by apply: eq_Rintegral => x _; ring.
by rewrite RintegralZl // Rintegral_legendre_sq.
Qed.

End legendre_moments.

(* 2 and 3. The sum of the kernels, and Hoeffding's inequality. *)

(* A sum over the coordinates j < d of List.nth, as a sum over the
   ordinals of 1 * d. *)
Lemma sum_nth_tnth (d : nat) (P : pred nat) (F : RR -> RR)
    (x : paper_main_sample 1 d) :
  \sum_(k < d | P k) F (List.nth k (tval x) 0) =
  \sum_(k < 1 * d | P k) F (tnth x k).
Proof.
rewrite -(big_mkord P (fun k => F (List.nth k (tval x) 0))).
have -> : index_iota 0 d = index_iota 0 (1 * d) by rewrite mul1n.
rewrite big_mkord; apply: eq_bigr => k _.
by rewrite (tnth_nth 0) List_nthE.
Qed.

Lemma sum_nth_tnthT (d : nat) (F : RR -> RR) (x : paper_main_sample 1 d) :
  \sum_(k < d) F (List.nth k (tval x) 0) = \sum_(k < 1 * d) F (tnth x k).
Proof. exact: (sum_nth_tnth d xpredT). Qed.

(* The test function 1{sum_(j < d) h(x_j) > 0}. *)
Definition latent_sign_test (d : nat) (x : paper_main_sample 1 d) : R :=
  \1_[set y : paper_main_sample 1 d |
       0 < \sum_(j < d) paired_kernel (List.nth j (tval y) 0)] x.

Section latent_tensor.
Variables (s : R) (mu : probability (measurableTypeR R) R) (d : nat).
Hypotheses (hs : 0 <= s <= 1) (hmu : paired_uniform_spec mu).

Let c0 : (0 : RR) < Num.sqrt 3%:R. Proof. by rewrite sqrtr_gt0 ltr0n. Qed.
Let hP : sym_uniform_spec (Num.sqrt 3%:R : RR) mu. Proof. exact: hmu. Qed.

Let mh : measurable_fun setT (paired_kernel : RR -> RR).
Proof. exact: measurable_paired_kernel. Qed.

Let ch : continuous (paired_kernel : RR -> RR).
Proof. exact: continuous_legendre4. Qed.

Let csq : continuous (fun t : RR => paired_kernel t ^+ 2 : RR).
Proof.
move=> x; apply: (@cvg_comp _ _ _ paired_kernel (fun y => y ^+ 2)).
  exact: ch.
exact: exprn_continuous.
Qed.

Let msq : measurable_fun setT (fun t : RR => paired_kernel t ^+ 2 : RR).
Proof. exact: continuous_measurable_fun. Qed.

Let range (a : R) : -1 <= a <= 1 -> -1 <= a <= 7%:R / 3%:R.
Proof.
by move=> /andP[a1 a2]; rewrite a1 /=; apply: le_trans a2 seven_thirds_ge1.
Qed.

Let rangeN (a : R) : -1 <= a <= 1 -> -1 <= - a <= 1.
Proof. by move=> /andP[a1 a2]; rewrite lerNl opprK a2 lerNl a1. Qed.

Let hs1 : -1 <= s <= 1.
Proof.
have /andP[s0 s1] := hs; rewrite s1 andbT.
by apply: (le_trans _ s0); exact: lerN10.
Qed.

Let hi a : -1 <= a <= 7%:R / 3%:R ->
  (paired_law mu a).-integrable setT (EFin \o (paired_kernel : RR -> RR)).
Proof. by move=> ha; have [] := legendre_law_cont _ _ c0 hP a _ ha ch. Qed.

Let isq a : -1 <= a <= 7%:R / 3%:R ->
  (paired_law mu a).-integrable setT
    (EFin \o (fun t : RR => paired_kernel t ^+ 2 : RR)).
Proof. by move=> ha; have [] := legendre_law_cont _ _ c0 hP a _ ha csq. Qed.

Let vh a : -1 <= a <= 7%:R / 3%:R ->
  \int[paired_law mu a]_t paired_kernel t = a / 9%:R.
Proof. exact: (Rintegral_legendre_h _ _ c0 hP). Qed.

(* The second moment of h under paired_law mu a. *)
Let q a : RR := \int[paired_law mu a]_t (paired_kernel t ^+ 2 : RR).

Let q_sum : q s + q (- s) = 2%:R / 9%:R.
Proof.
exact: (Rintegral_legendre_sq_sum _ _ c0 hP s (range s hs1)
  (range _ (rangeN s hs1))).
Qed.

(* The kernels of coordinates j and k under latent_side mu d a. *)
Let e_h a (ha : -1 <= a <= 7%:R / 3%:R) (j : 'I_(1 * d)) :
  (latent_side mu d a).-integrable setT
    (EFin \o (fun x => paired_kernel (tnth x j))) /\
  \int[latent_side mu d a]_x paired_kernel (tnth x j) = a / 9%:R.
Proof.
have [i e] := latent_side_coord mu d a _ j mh (hi a ha).
by split => //; rewrite e vh.
Qed.

Let e_hh a (ha : -1 <= a <= 7%:R / 3%:R) (j k : 'I_(1 * d)) :
  (latent_side mu d a).-integrable setT
    (EFin \o (fun x => paired_kernel (tnth x j) * paired_kernel (tnth x k))) /\
  \int[latent_side mu d a]_x (paired_kernel (tnth x j) * paired_kernel (tnth x k)) =
  if j == k then q a else (a / 9%:R) ^+ 2.
Proof.
(* eqVneq substitutes the value of j == k *)
have [<-|jk] := eqVneq j k.
  have ex (x : paper_main_sample 1 d) :
      paired_kernel (tnth x j) * paired_kernel (tnth x j) =
      paired_kernel (tnth x j) ^+ 2.
    by rewrite expr2.
  have [i e] := latent_side_coord mu d a _ j msq (isq a ha).
  split.
    by apply: (eq_integrable measurableT _ _ _ i) => x _ /=; rewrite ex.
  by rewrite (eq_Rintegral _ (fun x _ => ex x)) e.
have [i e] := latent_side_coordM mu d a _ _ j k jk mh mh (hi a ha) (hi a ha).
by split => //; rewrite e vh // expr2.
Qed.

Let H (x : paper_main_sample 1 d) : RR := \sum_(j < 1 * d) paired_kernel (tnth x j).

Let e_H a (ha : -1 <= a <= 7%:R / 3%:R) :
  (latent_side mu d a).-integrable setT (EFin \o H) /\
  \int[latent_side mu d a]_x H x = (a / 9%:R) *+ (1 * d).
Proof.
have i j := (e_h a ha j).1.
split.
  apply: (eq_integrable measurableT _ _ _ (integrable_sum measurableT
    (index_enum 'I_(1 * d)) (P := xpredT) (fun j _ => i j))) => x _ /=.
  by rewrite sumEFin.
rewrite /H (Rintegral_sum_ord _ _ _ _ _ _ i).
rewrite (eq_bigr (fun=> a / 9%:R) (fun j _ => (e_h a ha j).2)).
by rewrite sumr_const card_ord.
Qed.

Let e_H2 a (ha : -1 <= a <= 7%:R / 3%:R) :
  (latent_side mu d a).-integrable setT (EFin \o (fun x => H x ^+ 2)) /\
  \int[latent_side mu d a]_x (H x ^+ 2) =
  (q a - (a / 9%:R) ^+ 2 + (a / 9%:R) ^+ 2 *+ (1 * d)) *+ (1 * d).
Proof.
set v := (a / 9%:R) ^+ 2.
have ex x : H x ^+ 2 = \sum_(j < 1 * d) \sum_(k < 1 * d)
    (paired_kernel (tnth x j) * paired_kernel (tnth x k)).
  by rewrite /H expr2 mulr_suml; apply: eq_bigr => j _; rewrite mulr_sumr.
have i j k := (e_hh a ha j k).1.
have ij j : (latent_side mu d a).-integrable setT (EFin \o (fun x =>
    \sum_(k < 1 * d) (paired_kernel (tnth x j) * paired_kernel (tnth x k)))).
  apply: (eq_integrable measurableT _ _ _ (integrable_sum measurableT
    (index_enum 'I_(1 * d)) (P := xpredT) (fun k _ => i j k))) => x _ /=.
  by rewrite sumEFin.
have ek j k : \int[latent_side mu d a]_x
    (paired_kernel (tnth x j) * paired_kernel (tnth x k)) =
    (q a - v) * (j == k)%:R + v.
  by rewrite (e_hh a ha j k).2 /v; case: eqP => _;
    rewrite ?mulr1 ?subrK ?mulr0 ?add0r.
(* the row j: E h(x_j)^2 = q a and E h(x_j) h(x_k) = v for k != j *)
have row j : \int[latent_side mu d a]_x (\sum_(k < 1 * d)
    (paired_kernel (tnth x j) * paired_kernel (tnth x k))) =
    q a - v + v *+ (1 * d).
  rewrite (Rintegral_sum_ord _ _ _ _ _ _ (i j)) (eq_bigr _ (fun k _ => ek j k)).
  rewrite big_split /= sumr_const card_ord -mulr_sumr (bigD1 j) //= eqxx.
  have z : \sum_(k < 1 * d | k != j) ((j == k)%:R : RR) = 0.
    by apply: big1 => k kj; rewrite eq_sym (negbTE kj).
  by rewrite z addr0 mulr1.
split.
  apply: (eq_integrable measurableT _ _ _ (integrable_sum measurableT
    (index_enum 'I_(1 * d)) (P := xpredT) (fun j _ => ij j))) => x _ /=.
  by rewrite sumEFin ex.
rewrite (eq_Rintegral _ (fun x _ => ex x)) (Rintegral_sum_ord _ _ _ _ _ _ ij).
by rewrite (eq_bigr _ (fun j _ => row j)) sumr_const card_ord.
Qed.

Let mH : measurable_fun setT H.
Proof.
apply: measurable_sum => j.
exact: measurableT_comp mh (measurable_tnth j).
Qed.

Let hsp : -1 <= s <= 7%:R / 3%:R. Proof. exact: range. Qed.
Let hsn : -1 <= - s <= 7%:R / 3%:R. Proof. exact: range (rangeN _ hs1). Qed.

(* E h(x_j)^2 = 1/9 under the latent law. *)
Lemma latent_kernel_sq_at (j : nat) : (j < d)%N ->
  latent_point_expectation s mu d
    (fun x => paired_kernel (List.nth j (tval x) 0) ^+ 2) = 9%:R^-1.
Proof.
move=> jd; have jd' : (j < 1 * d)%N by rewrite mul1n.
set j' := Ordinal jd'.
have -> : (fun x : paper_main_sample 1 d =>
    paired_kernel (List.nth j (tval x) 0) ^+ 2 : RR) =
    (fun x => paired_kernel (tnth x j') ^+ 2).
  by apply/funext => x; rewrite (tnth_nth 0) List_nthE.
have mg : measurable_fun setT
    (fun x : paper_main_sample 1 d => (paired_kernel (tnth x j') ^+ 2 : RR)).
  exact: measurableT_comp msq (measurable_tnth j').
have [i1 e1] := latent_side_coord mu d s _ j' msq (isq s hsp).
have [i2 e2] := latent_side_coord mu d (- s) _ j' msq (isq (- s) hsn).
rewrite (latent_point_expectationE s mu d hs hmu _ mg i1 i2) e1 e2.
by rewrite -/(q s) -/(q (- s)) q_sum; field.
Qed.

(* E S = 0 and E S^2 = d / 9 + d (d - 1) s^2 / 81 for S = sum_j h(x_j). *)
Lemma latent_kernel_sum_moments :
  latent_point_expectation s mu d
    (fun x => \sum_(j < d) paired_kernel (List.nth j (tval x) 0)) = 0 /\
  latent_point_expectation s mu d
    (fun x => (\sum_(j < d) paired_kernel (List.nth j (tval x) 0)) ^+ 2) =
  d%:R / 9%:R + d%:R * (d%:R - 1) * s ^+ 2 / 81%:R.
Proof.
have eS : (fun x : paper_main_sample 1 d =>
    \sum_(j < d) paired_kernel (List.nth j (tval x) 0) : RR) = H.
  by apply/funext => x; rewrite sum_nth_tnthT.
have eS2 : (fun x : paper_main_sample 1 d =>
    (\sum_(j < d) paired_kernel (List.nth j (tval x) 0)) ^+ 2 : RR) =
    (fun x => H x ^+ 2).
  by apply/funext => x; rewrite sum_nth_tnthT.
have mH2 : measurable_fun setT (fun x : paper_main_sample 1 d => H x ^+ 2 : RR).
  exact: measurable_funX.
have [iHs eHs] := e_H s hsp.
have [iHn eHn] := e_H (- s) hsn.
have [iH2s eH2s] := e_H2 s hsp.
have [iH2n eH2n] := e_H2 (- s) hsn.
rewrite eS eS2.
rewrite (latent_point_expectationE s mu d hs hmu _ mH iHs iHn) eHs eHn.
rewrite (latent_point_expectationE s mu d hs hmu _ mH2 iH2s iH2n) eH2s eH2n.
split; first by field.
have -> : q (- s) = 2%:R / 9%:R - q s by rewrite -q_sum addrC addKr.
by field.
Qed.

(* Var S = d / 9 + d (d - 1) s^2 / 81. *)
Lemma latent_kernel_sum_variance :
  latent_point_expectation s mu d
    (fun x => (\sum_(j < d) paired_kernel (List.nth j (tval x) 0)) ^+ 2) -
  latent_point_expectation s mu d
    (fun x => \sum_(j < d) paired_kernel (List.nth j (tval x) 0)) ^+ 2 =
  d%:R / 9%:R + d%:R * (d%:R - 1) * s ^+ 2 / 81%:R.
Proof.
have [e1 e2] := latent_kernel_sum_moments.
by rewrite e1 e2 expr0n /= subr0.
Qed.

(* 3. Hoeffding's inequality under each component. *)

(* h - a / 9 is subgaussian with constant 2 under paired_law mu a. *)
Lemma paired_kernel_subgaussian (a : R) : -1 <= a <= 1 ->
  subgaussian (paired_law mu a)
    (fun t : RR => paired_kernel t - a / 9%:R : RR) 2.
Proof.
move=> ha.
have hd := paired_prob_density mu hmu a (range a ha).
have [_ pd0 pd1] := hd.
have mg : measurable_fun setT
    (fun t : RR => paired_kernel t - a / 9%:R : RR).
  by apply: measurable_funB => //; exact: measurable_cst.
pose G (t : RR) : \bar RR :=
  (expR ((paired_kernel t - a / 9%:R) ^+ 2 / 2 ^+ 2))%:E.
have mG : measurable_fun setT G.
  apply/measurable_EFinP; apply: (@measurableT_comp _ _ _ _ _ _ expR) => //.
  apply: measurable_funM; last exact: measurable_cst.
  exact: measurable_funX.
have G0 t : (0 <= G t)%E by rewrite lee_fin expR_ge0.
have mpd : measurable_fun setT (fun t : RR => (paired_density a t)%:E).
  by apply/measurable_EFinP; case: hd.
have hb : (\int[paired_law mu a]_t G t <= 2%:E)%E.
  rewrite (ge0_integral_density_prob hd measurableT G0 mG).
  have f10 : forall t, setT t -> (0 <= G t * (paired_density a t)%:E)%E.
    by move=> t _; rewrite mule_ge0 // lee_fin pd0.
  have mf1 : measurable_fun setT (fun t => G t * (paired_density a t)%:E)%E.
    exact: emeasurable_funM.
  have mf2 : measurable_fun setT
      (fun t : RR => (expR 3%:R^-1)%:E * (paired_density a t)%:E)%E.
    by apply: emeasurable_funM => //; exact: measurable_cst.
  apply: (@le_trans _ _
    (\int[mu]_t ((expR 3%:R^-1)%:E * (paired_density a t)%:E))%E).
    apply: (ge0_le_integral mu measurableT f10 mf1 mf2) => t _.
    rewrite /G /paired_density /legendre_density.
    case: ifPn => tc; last by rewrite !mule0.
    have hr := paired_kernel_range t tc.
    rewrite -!EFinM lee_fin.
    apply: ler_wpM2r; first exact: (kernel_density_ge0 _ _ hr ha).
    by rewrite ler_expR; exact: (kernel_dev_bound _ _ hr ha).
  have pd0' : forall t, setT t -> (0 <= (paired_density a t)%:E)%E.
    by move=> t _; rewrite lee_fin pd0.
  have k0 : (0 <= (expR (3%:R^-1 : RR))%:E)%E by rewrite lee_fin expR_ge0.
  rewrite (ge0_integralZl mu measurableT mpd pd0' k0) pd1 mule1 lee_fin.
  exact: expR_third_le2.
split; [by rewrite ltr0n | exact: mg | exact: hb].
Qed.

(* h - a / 9 is centered under paired_law mu a. *)
Lemma paired_kernel_centered (a : R) : -1 <= a <= 7%:R / 3%:R ->
  \int[paired_law mu a]_t (paired_kernel t - a / 9%:R : RR) = 0.
Proof.
move=> ha.
have i2 : (paired_law mu a).-integrable setT (EFin \o cst (a / 9%:R : RR)).
  exact: finite_measure_integrable_cst.
rewrite (RintegralB measurableT (hi a ha) i2) vh // Rintegral_cst //.
by rewrite -[Y in fine Y]/(paired_law mu a setT) probability_setT /= mulr1 subrr.
Qed.

(* The moment generating function of sum_k b_k (h(x_k) - a / 9). *)
Lemma latent_side_mgf (a l : R) (b : nat -> R) : -1 <= a <= 1 ->
  (\int[latent_side mu d a]_x
     (expR (l * \sum_(i < 1 * d) b i *
       (paired_kernel (tnth x i) - a / 9%:R))%R)%:E <=
   (expR (3 * l ^+ 2 * \sum_(i < 1 * d) b i ^+ 2 * 2 ^+ 2)%R)%:E)%E.
Proof.
move=> ha.
exact: (@subgaussian_sum_mgf _ _ RR (fun=> paired_law mu a) (1 * d)
  (fun=> fun t : RR => paired_kernel t - a / 9%:R : RR) (fun=> 2) b l
  (fun i _ => paired_kernel_subgaussian a ha)
  (fun i _ => paired_kernel_centered a (range a ha))).
Qed.

(* P(sum_k b_k (h(x_k) - a / 9) >= u) <= exp (- u^2 / (48 sum_k b_k^2)). *)
Lemma latent_side_tail (a u : R) (b : nat -> R) : -1 <= a <= 1 -> 0 <= u ->
  0 < \sum_(i < 1 * d) b i ^+ 2 ->
  (latent_side mu d a [set x | u <=
     \sum_(i < 1 * d) b i * (paired_kernel (tnth x i) - a / 9%:R)]%R <=
   (expR (- (u ^+ 2 / (48%:R * \sum_(i < 1 * d) b i ^+ 2)))%R)%:E)%E.
Proof.
move=> ha u0 B0.
set B := \sum_(i < 1 * d) b i ^+ 2 in B0 *.
pose Z (x : paper_main_sample 1 d) : RR :=
  \sum_(i < 1 * d) b i * (paired_kernel (tnth x i) - a / 9%:R).
have mZ : measurable_fun setT Z.
  apply: measurable_sum => i; apply: measurable_funM.
    exact: measurable_cst.
  apply: measurable_funB; last exact: measurable_cst.
  exact: measurableT_comp mh (measurable_tnth i).
pose l : RR := u / (24%:R * B).
have l0 : 0 <= l by rewrite /l divr_ge0 // mulr_ge0 ?ler0n // ltW.
apply: le_trans (measure_ge_expR (latent_side mu d a) u mZ l0) _.
have eZ x : (expR (l * (Z x - u)))%:E =
    ((expR (l * Z x))%:E * (expR (- (l * u)))%:E)%E.
  by rewrite mulrBr expRD EFinM.
under eq_integral do rewrite eZ.
have mE : measurable_fun setT (fun x => (expR (l * Z x))%:E : \bar RR).
  apply/measurable_EFinP; apply: (@measurableT_comp _ _ _ _ _ _ expR) => //.
  by apply: measurable_funM => //; exact: measurable_cst.
have E0 : forall x, setT x -> (0 <= (expR (l * Z x))%:E)%E.
  by move=> x _; rewrite lee_fin expR_ge0.
have k0 : (0 <= (expR (- (l * u)))%:E)%E by rewrite lee_fin expR_ge0.
rewrite (ge0_integralZr _ measurableT mE E0 k0).
apply: le_trans (lee_wpmul2r k0 (latent_side_mgf a l b ha)) _.
rewrite -EFinM -expRD lee_fin ler_expR -mulr_suml -/B.
by rewrite /l (tail_exponent _ _ B0).
Qed.

(* For a set J of m > 0 coordinates, the lower and the upper tail of
   sum_(k in J) h(x_k). *)
Lemma latent_side_hoeffding (a t : R) (J : pred nat) : -1 <= a <= 1 ->
  let m := (\sum_(i < 1 * d | J i) 1 : RR) in 0 < m ->
  (t <= m * a / 9%:R ->
   (latent_side mu d a
     [set x | \sum_(i < 1 * d | J i) paired_kernel (tnth x i) <= t]%R <=
   (expR (- ((m * a / 9%:R - t) ^+ 2 / (48%:R * m)))%R)%:E)%E) /\
  (m * a / 9%:R <= t ->
   (latent_side mu d a
     [set x | t <= \sum_(i < 1 * d | J i) paired_kernel (tnth x i)]%R <=
   (expR (- ((t - m * a / 9%:R) ^+ 2 / (48%:R * m)))%R)%:E)%E).
Proof.
move=> ha m m0.
pose S (x : paper_main_sample 1 d) : RR :=
  \sum_(i < 1 * d | J i) paired_kernel (tnth x i).
(* the weights sg 1_J *)
have eB (sg : RR) x : \sum_(i < 1 * d) (sg * (J i)%:R) *
    (paired_kernel (tnth x i) - a / 9%:R) = sg * (S x - m * a / 9%:R).
  have e1 : \sum_(i < 1 * d | J i) (paired_kernel (tnth x i) - a / 9%:R) =
      S x - m * a / 9%:R.
    rewrite sumrB /S /m -mulrA mulr_suml; congr (_ - _).
    by apply: eq_bigr => i _; rewrite mul1r.
  rewrite -e1 mulr_sumr [RHS]big_mkcond /=; apply: eq_bigr => i _.
  by case: (J i); rewrite /= ?mulr1 ?mulr0 ?mul0r.
have eW (sg : RR) : sg ^+ 2 = 1 ->
    \sum_(i < 1 * d) (sg * (J i)%:R) ^+ 2 = m.
  move=> s2; rewrite /m [RHS]big_mkcond /=; apply: eq_bigr => i _.
  by case: (J i); rewrite /= exprMn s2 mul1r ?expr1n ?expr0n.
split => ht.
  have u0 : 0 <= m * a / 9%:R - t by rewrite subr_ge0.
  have W0 : 0 < \sum_(i < 1 * d) ((- 1 : RR) * (J i)%:R) ^+ 2.
    by rewrite eW // sqrrN expr1n.
  have := latent_side_tail a _ (fun i => - 1 * (J i)%:R) ha u0 W0.
  rewrite eW ?sqrrN ?expr1n //.
  have -> : [set x | m * a / 9%:R - t <= \sum_(i < 1 * d)
      (- 1 * (J i)%:R) * (paired_kernel (tnth x i) - a / 9%:R)] =
      [set x | S x <= t].
    apply/seteqP; split => x /=; rewrite eB mulN1r opprB lerD2l lerN2 //.
  by [].
have u0 : 0 <= t - m * a / 9%:R by rewrite subr_ge0.
have W0 : 0 < \sum_(i < 1 * d) ((1 : RR) * (J i)%:R) ^+ 2 by rewrite eW // expr1n.
have := latent_side_tail a _ (fun i => 1 * (J i)%:R) ha u0 W0.
rewrite eW ?expr1n //.
have -> : [set x | t - m * a / 9%:R <= \sum_(i < 1 * d)
    (1 * (J i)%:R) * (paired_kernel (tnth x i) - a / 9%:R)] =
    [set x | t <= S x].
  apply/seteqP; split => x /=; rewrite eB mul1r lerD2r //.
by [].
Qed.

(* The sign form: under the component latent_param s c, of sign
   sigma = latent_param 1 c, P(sigma sum_(k in J) h(x_k) <= t) <=
   exp (- (m s / 9 - t)^2 / (48 m)) for t <= m s / 9. *)
Lemma latent_side_sign_hoeffding (t : R) (c : nat) (J : pred nat) :
  let m := (\sum_(i < 1 * d | J i) 1 : RR) in 0 < m -> t <= m * s / 9%:R ->
  (latent_side mu d (latent_param s c)
     [set x | latent_param 1 c *
        \sum_(i < 1 * d | J i) paired_kernel (tnth x i) <= t]%R <=
   (expR (- ((m * s / 9%:R - t) ^+ 2 / (48%:R * m)))%R)%:E)%E.
Proof.
move=> m m0 tm.
rewrite /latent_param; case: eqP => _.
  have [h _] := latent_side_hoeffding s t J hs1 m0.
  have -> : [set x : paper_main_sample 1 d | 1 *
      \sum_(i < 1 * d | J i) paired_kernel (tnth x i) <= t] =
      [set x | \sum_(i < 1 * d | J i) paired_kernel (tnth x i) <= t].
    by apply/seteqP; split => x /=; rewrite mul1r.
  exact: h.
have [_ h] := latent_side_hoeffding (- s) (- t) J (rangeN s hs1) m0.
have tm' : m * - s / 9%:R <= - t.
  by rewrite mulrN mulNr lerN2.
have -> : [set x : paper_main_sample 1 d | - 1 *
    \sum_(i < 1 * d | J i) paired_kernel (tnth x i) <= t] =
    [set x | - t <= \sum_(i < 1 * d | J i) paired_kernel (tnth x i)].
  by apply/seteqP; split => x /=; rewrite mulN1r lerNl.
have e : (- t - m * - s / 9%:R) ^+ 2 = (m * s / 9%:R - t) ^+ 2.
  by rewrite mulrN mulNr opprK addrC.
by rewrite -e; exact: h.
Qed.

(* 4. The sign indicator and the other coordinates. *)

(* The probability of a measurable set of points under the latent law. *)
Lemma latent_point_prob (E : set (paper_main_sample 1 d)) : measurable E ->
  latent_point_expectation s mu d (fun x => \1_E x : RR) =
  (fine (latent_side mu d s E) + fine (latent_side mu d (- s) E)) / 2%:R.
Proof.
move=> mE.
have mg : measurable_fun setT (fun x : paper_main_sample 1 d => \1_E x : RR).
  exact: measurable_indic.
have i a : (latent_side mu d a).-integrable setT
    (EFin \o (fun x : paper_main_sample 1 d => \1_E x : RR)).
  exact: integrable_indic.
rewrite (latent_point_expectationE s mu d hs hmu _ mg (i s) (i (- s))).
by rewrite /Rintegral !integral_indic // !setIT.
Qed.

Let fineP a (E : set (paper_main_sample 1 d)) (r : RR) : measurable E ->
  (latent_side mu d a E <= r%:E)%E -> fine (latent_side mu d a E) <= r.
Proof.
move=> mE h; have fE := fin_num_measure (latent_side mu d a) E mE.
by rewrite -lee_fin (fineK fE).
Qed.

Let fine_ge0' a (E : set (paper_main_sample 1 d)) :
  0 <= fine (latent_side mu d a E).
Proof. by apply: fine_ge0; exact: measure_ge0. Qed.

(* Var 1{S > 0} is within exp (- d s^2 / 1944) / 4 of 1/4. *)
Lemma latent_sign_variance : (0 < d)%N ->
  4%:R^-1 - expR (- (d%:R * s ^+ 2 / (24%:R * 81%:R))) / 4%:R <=
    latent_point_expectation s mu d (fun x => latent_sign_test d x ^+ 2) -
    latent_point_expectation s mu d (latent_sign_test d) ^+ 2 <= 4%:R^-1.
Proof.
move=> d0; set f := latent_sign_test d.
pose E := [set y : paper_main_sample 1 d | 0 < H y].
have eE : [set y : paper_main_sample 1 d |
    0 < \sum_(j < d) paired_kernel (List.nth j (tval y) 0)] = E.
  by apply/seteqP; split => y /=; rewrite sum_nth_tnthT.
have mE : measurable E.
  rewrite -[X in measurable X]setTI.
  by apply: measurable_fun_ltr => //; exact: measurable_cst.
have f1 : f = (fun x => \1_E x : RR).
  by apply/funext => x; rewrite /f /latent_sign_test eE.
have f2 : (fun x => f x ^+ 2) = (fun x => \1_E x : RR).
  apply/funext => x; rewrite f1 indicE.
  by case: (x \in E); rewrite ?expr1n ?expr0n.
rewrite f2 f1 (latent_point_prob E mE).
have dR : (0 : RR) < d%:R by rewrite ltr0n.
pose m := (\sum_(i < 1 * d | xpredT i) 1 : RR).
have em : m = d%:R.
  by rewrite /m big_mkcond /= sumr_const card_ord mul1n.
have m0 : 0 < m by rewrite em.
have dn : (d%:R : RR) != 0 by rewrite gt_eqF.
have /andP[s0 _] := hs.
pose e := expR (- ((m * s / 9%:R - 0) ^+ 2 / (48%:R * m))).
have e0 : 0 <= e by rewrite /e expR_ge0.
have ms0 : 0 <= m * s / 9%:R by rewrite divr_ge0 // mulr_ge0 // ltW.
pose S' (y : paper_main_sample 1 d) : RR :=
  \sum_(i < 1 * d | xpredT i) paired_kernel (tnth y i).
have mS' : measurable_fun setT S' by exact: mH.
(* under the component s, P(S <= 0) <= e, so P(E) >= 1 - e *)
have eC : ~` E = [set y | S' y <= 0].
  apply/seteqP; split => y /=; rewrite leNgt.
    by move=> /negP.
  by move=> /negP.
have PC : (latent_side mu d s [set y | S' y <= 0]%R <= e%:E)%E.
  have [h _] := latent_side_hoeffding s 0 xpredT hs1 m0.
  exact: h ms0.
have pS1 : 1 - e <= fine (latent_side mu d s E).
  have h := probability_setC (latent_side mu d s) mE.
  rewrite eC in h.
  have fE := fin_num_measure (latent_side mu d s) E mE.
  move: PC; rewrite h -(fineK fE) -EFinB lee_fin.
  exact: sub_le_swap.
have pS1' : fine (latent_side mu d s E) <= 1.
  by apply: fineP => //; exact: probability_le1.
(* under the component - s, P(E) <= P(S >= 0) <= e *)
have mU : measurable [set y : paper_main_sample 1 d | 0 <= S' y].
  rewrite -[X in measurable X]setTI.
  by apply: measurable_fun_ler => //; exact: measurable_cst.
have pN : fine (latent_side mu d (- s) E) <= e.
  apply: fineP => //.
  have [_ h] := latent_side_hoeffding (- s) 0 xpredT (rangeN s hs1) m0.
  have prem : m * - s / 9%:R <= 0 by rewrite mulrN mulNr oppr_le0.
  have eA : (0 - m * - s / 9%:R) ^+ 2 = (m * s / 9%:R - 0) ^+ 2.
    by rewrite mulrN mulNr subr0 sub0r opprK.
  have h' := h prem; rewrite eA in h'.
  apply: le_trans h'.
  apply: le_measure; rewrite ?inE.
  - exact: mE.
  - exact: mU.
  - by move=> y /= /ltW.
have hv := sign_variance_bound _ _ _ (fine_ge0' (- s) E) pN pS1 pS1'.
have ee : e ^+ 2 = expR (- (d%:R * s ^+ 2 / (24%:R * 81%:R))).
  by rewrite /e expr2 -expRD em; congr expR; field.
by rewrite -ee.
Qed.

(* P(|sum_(k < d, k != j) h(x_k)| <= 1) <= exp (- (d - 1) s^2 / 15552). *)
Lemma latent_other_small (j : nat) : (j < d)%N -> 18%:R <= (d%:R - 1) * s ->
  latent_point_expectation s mu d (fun x => \1_[set y : paper_main_sample 1 d |
    `|\sum_(k < d | (k : nat) != j) paired_kernel (List.nth k (tval y) 0)| <= 1] x
    : RR) <=
  expR (- ((d%:R - 1) * s ^+ 2 / (48%:R * 324%:R))).
Proof.
move=> jd ds.
pose J := fun k : nat => k != j.
pose Sj (y : paper_main_sample 1 d) : RR :=
  \sum_(k < 1 * d | J k) paired_kernel (tnth y k).
pose E := [set y : paper_main_sample 1 d | `|Sj y| <= 1].
have eE : [set y : paper_main_sample 1 d |
    `|\sum_(k < d | (k : nat) != j) paired_kernel (List.nth k (tval y) 0)| <= 1] = E.
  by apply/seteqP; split => y /=; rewrite (sum_nth_tnth d J).
have mSj : measurable_fun setT Sj.
  have -> : Sj = (fun y => \sum_(k < 1 * d)
      (if J k then paired_kernel (tnth y k) else 0)).
    by apply/funext => y; rewrite /Sj big_mkcond.
  apply: measurable_sum => k; case: (J k).
    exact: measurableT_comp mh (measurable_tnth k).
  exact: measurable_cst.
have mA : measurable_fun setT (fun y => `|Sj y| : RR).
  by apply: measurableT_comp; [exact: normr_measurable | exact: mSj].
have mE : measurable E.
  rewrite -[X in measurable X]setTI.
  by apply: measurable_fun_ler => //; exact: measurable_cst.
have mL : measurable [set y : paper_main_sample 1 d | Sj y <= 1].
  rewrite -[X in measurable X]setTI.
  by apply: measurable_fun_ler => //; exact: measurable_cst.
have mG : measurable [set y : paper_main_sample 1 d | - 1 <= Sj y].
  rewrite -[X in measurable X]setTI.
  by apply: measurable_fun_ler => //; exact: measurable_cst.
rewrite eE (latent_point_prob E mE).
pose m := (\sum_(i < 1 * d | J i) 1 : RR).
have jd' : (j < 1 * d)%N by rewrite mul1n.
have em : m = d%:R - 1.
  have e1 : \sum_(i < 1 * d) (1 : RR) = d%:R.
    by rewrite sumr_const card_ord mul1n.
  rewrite (bigD1 (Ordinal jd')) //= in e1.
  rewrite -e1 addrC addKr /m.
  by apply: eq_bigl.
have /andP[s0 _] := hs.
have ms : 18%:R <= m * s by rewrite em.
have m0 : 0 < m := prod_ge_pos _ _ s0 ms.
have m1 : 1 <= m * s / 9%:R := div9_ge1 _ ms.
pose A := (m * s / 9%:R - 1) ^+ 2 / (48%:R * m).
have bS : fine (latent_side mu d s E) <= expR (- A).
  apply: fineP => //.
  have [h _] := latent_side_hoeffding s 1 J hs1 m0.
  apply: le_trans (h m1).
  apply: le_measure; rewrite ?inE.
  - exact: mE.
  - exact: mL.
  - by move=> y; rewrite /E /= ler_norml => /andP[_ hy]; exact: hy.
have bN : fine (latent_side mu d (- s) E) <= expR (- A).
  apply: fineP => //.
  have [_ h] := latent_side_hoeffding (- s) (- 1) J (rangeN s hs1) m0.
  have prem : m * - s / 9%:R <= - 1 by rewrite mulrN mulNr lerN2.
  have eA : (- 1 - m * - s / 9%:R) ^+ 2 = (m * s / 9%:R - 1) ^+ 2.
    by rewrite mulrN mulNr opprK addrC.
  rewrite /A -eA.
  apply: le_trans (h prem).
  apply: le_measure; rewrite ?inE.
  - exact: mE.
  - exact: mG.
  - by move=> y; rewrite /E /= ler_norml => /andP[hy _]; exact: hy.
have hA : expR (- A) <= expR (- ((d%:R - 1) * s ^+ 2 / (48%:R * 324%:R))).
  by rewrite ler_expR lerN2 -em; exact: other_exponent.
by apply: le_trans hA; exact: avg_le.
Qed.

End latent_tensor.

(* Var 1{S > 0} -> 1/4 as d -> oo, for a fixed s > 0. *)
Lemma latent_sign_variance_lim (s : R) (mu : probability (measurableTypeR R) R) :
  0 < s <= 1 -> paired_uniform_spec mu ->
  forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%N ->
  `|latent_point_expectation s mu d (fun x => latent_sign_test d x ^+ 2) -
    latent_point_expectation s mu d (latent_sign_test d) ^+ 2 - 4%:R^-1|
  <= eps.
Proof.
move=> /andP[s0 s1] hmu eps e0.
have hs : 0 <= s <= 1 by rewrite (ltW s0) s1.
have sn : s != 0 by rewrite gt_eqF.
have c0 : 0 < 24%:R * 81%:R / s ^+ 2.
  by rewrite divr_gt0 ?exprn_gt0 // mulr_gt0 ?ltr0n.
have [D hD] := expR_lin_small _ _ c0 e0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1].
have /andP[lo hi] := latent_sign_variance s mu d hs hmu d1.
have ec : d%:R * s ^+ 2 / (24%:R * 81%:R) = d%:R / (24%:R * 81%:R / s ^+ 2).
  by field.
rewrite ec in lo.
apply: (abs_quarter _ _ _ lo hi (expR_ge0 _)).
exact: hD d dD.
Qed.

