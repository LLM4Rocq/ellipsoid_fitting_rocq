(* The coordinate tensorization of the variance for the latent-sign law:
   the proof of latent_tensorization_statement of the frozen
   LatentTensorization, at Stdlib's R. Item R2b of phase 9; the note
   notes/phase6-three-extensions.md, section 2.3, (12) to (14).

   Let T be a constant of (12) for the latent-sign law of parameter s in
   dimension d (latent_tensorization s mu d T), and write E for
   latent_point_expectation s mu d and V_j for the conditional variance
   given the coordinates other than j. The two parts test (12) with one
   bounded measurable function each; the tools are those of
   Paired/Conditional and Paired/Tensorization.

   1. f = sum_k ht(x_k), with ht = h 1_[-sqrt 3, sqrt 3], a bounded
      version of sum_k h(x_k) that equals it on the box. Its variance is
      d / 9 + d (d - 1) s^2 / 81 (latent_kernel_sum_variance). At a point
      of the box, V_j f = V_j g_j for g_j = ht(x_j), since the other terms
      do not depend on x_j (latent_cond_variance_shift), and
      0 <= V_j g_j <= E (g_j^2 | X_-j); by the tower property (latent_tower)
      E [E (g_j^2 | X_-j)] = E h(x_j)^2 = 1/9 (latent_kernel_sq_at). So
      0 <= sum_j E V_j f <= d / 9, and (12) gives
      T >= 1 + (d - 1) s^2 / 9 (latent_tensor_lower).
   2. f = latent_sign_test d = 1{sum_k h(x_k) > 0}. Its variance is at
      least 1/8 once exp (- d s^2 / 1944) <= 1/2 (latent_sign_variance). At
      a point x of the box, V_j f <= 1/4 (latent_cond_variance_indicator),
      and V_j f = 0 if |R_j(x)| > 1 for R_j = sum_(k != j) h(x_k), since then
      the sign of h(y) + R_j(x) does not depend on y in [-sqrt 3, sqrt 3]
      (latent_cond_variance_const). So
      E V_j f <= P(|R_j| <= 1) / 4 <= exp (- (d - 1) s^2 / 15552) / 4 for
      (d - 1) s >= 18 (latent_other_small), and (12) gives
      T >= (1 / (2 d)) exp ((d - 1) s^2 / 15552) (latent_tensor_exp), with
      c = 1/15552 and c' = 1/2.

   latent_tensor_theorem : latent_tensorization_statement. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import exp.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import PairedDefinitions.
From EllipsoidUniversality Require Import LatentSignDefinitions LatentSignScope.
From EllipsoidUniversality Require Import LatentTensorization.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Paired Require Import Uniform Law LatentSign Scope.
From EllipsoidUniversality.Paired Require Import Tensorization Conditional.
From EllipsoidUniversality.Gaussian Require Import InProbability.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 0. Arithmetic. *)

Lemma tensor_bound {RT : realType} (V Sg T B : RT) :
  0 < V -> 0 <= Sg -> Sg <= B -> V <= T * Sg -> V / B <= T.
Proof.
move=> V0 S0 SB h.
have TS : 0 < T * Sg := lt_le_trans V0 h.
have T0 : 0 < T by move: TS; nra.
have B0 : 0 < B by move: TS; nra.
rewrite ler_pdivrMr //; apply: le_trans h _.
by rewrite ler_pM2l.
Qed.

Lemma cond_var_le {RT : realType} (a b : RT) : a - b ^+ 2 <= a.
Proof. by rewrite lerBlDr lerDl sqr_ge0. Qed.

(* 1. The lower bound 1 + (d - 1) s^2 / 9. *)

Section tensor_lower.
Variables (s : R) (mu : probability (measurableTypeR R) R) (d : nat).
Hypotheses (hs : 0 <= s <= 1) (hmu : paired_uniform_spec mu).

Local Notation E := (latent_point_expectation s mu d).

(* ht = h 1_[-sqrt 3, sqrt 3] *)
Let ht (t : RR) : RR :=
  paired_kernel t * \1_[set y : RR | `|y| <= Num.sqrt 3%:R] t.

Let mht : measurable_fun setT ht.
Proof.
apply: measurable_funM; first exact: measurable_paired_kernel.
apply: measurable_indic.
by rewrite -[X in measurable X]setTI; apply: measurable_fun_ler.
Qed.

Let ht_eq t : `|t| <= Num.sqrt 3%:R -> ht t = paired_kernel t.
Proof. by move=> tc; rewrite /ht indicE mem_set // mulr1. Qed.

Let ht_bound t : `|ht t| <= 1.
Proof.
rewrite /ht indicE; case: (boolP (t \in _)) => [/set_mem tc|_].
  rewrite mulr1 ler_norml; have /andP[h1 h2] := paired_kernel_range t tc.
  by rewrite h2 andbT; apply: le_trans h1; rewrite lerN2 ler_pdivrMr ?ltr0n //
    mul1r ler_nat.
by rewrite mulr0 normr0.
Qed.

Let f (x : paper_main_sample 1 d) : RR := \sum_(k < 1 * d) ht (tnth x k).

Let mf : measurable_fun setT f.
Proof. by apply: measurable_sum => k; exact: measurableT_comp mht (measurable_tnth k). Qed.

Let f_bound x : `|f x| <= d%:R.
Proof.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (ler_sum _ (fun k _ => ht_bound (tnth x k))) _.
by rewrite sumr_const card_ord mul1n.
Qed.

Let S (x : paper_main_sample 1 d) : RR :=
  \sum_(j < d) paired_kernel (List.nth j (tval x) 0).

Let mS : measurable_fun setT S.
Proof.
have -> : S = (fun x => \sum_(k < 1 * d) paired_kernel (tnth x k)).
  by apply/funext => x; rewrite /S sum_nth_tnthT.
by apply: measurable_sum => k; exact: measurableT_comp measurable_paired_kernel
  (measurable_tnth k).
Qed.

Let fS x : latent_box d x -> f x = S x.
Proof.
move=> bx; rewrite /S sum_nth_tnthT; apply: eq_bigr => k _.
exact: ht_eq.
Qed.

Let var_f : latent_variance s mu d f =
  d%:R / 9%:R + d%:R * (d%:R - 1) * s ^+ 2 / 81%:R.
Proof.
rewrite /latent_variance.
rewrite (latent_expectation_eq s mu d hmu f S mf mS fS).
rewrite (latent_expectation_eq s mu d hmu (fun x => f x ^+ 2) (fun x => S x ^+ 2)
  (measurable_funX _ mf) (measurable_funX _ mS)
  (fun x bx => congr1 (fun t : RR => t ^+ 2) (fS x bx))).
exact: (latent_kernel_sum_variance s mu d hs hmu).
Qed.

(* 0 <= E V_j f <= 1/9 *)
Let cond_var_f (j : nat) : (j < d)%N ->
  0 <= E (latent_cond_variance s mu d j f) <= 9%:R^-1.
Proof.
move=> jd.
have jd1 : (j < 1 * d)%N by rewrite mul1n.
pose jo : 'I_(1 * d) := Ordinal jd1.
pose g (x : paper_main_sample 1 d) : RR := ht (tnth x jo).
pose r (x : paper_main_sample 1 d) : RR :=
  \sum_(k < 1 * d | (k : nat) != j) ht (tnth x k).
have mg : measurable_fun setT g := measurableT_comp mht (measurable_tnth jo).
have gb z : `|g z| <= 1 := ht_bound _.
have ef : f = (fun z => g z + r z).
  by apply/funext => z; rewrite /f (bigD1 jo) //=; congr (_ + _).
have hr x t : r (latent_replace d j x t) = r x.
  by apply: eq_bigr => k kj; rewrite tnth_mktuple (negbTE kj).
have mg2 : measurable_fun setT (fun z => g z ^+ 2 : RR) := measurable_funX _ mg.
have gb2 z : `|g z ^+ 2| <= 1.
  by rewrite normrX expr_le1 ?normr_ge0.
have [mCEg2 _] := measurable_latent_cond s mu d j hs hmu jd _ 1 mg2 gb2.
have [_ mCVf] := measurable_latent_cond s mu d j hs hmu jd f d%:R mf f_bound.
(* on the box, V_j f = V_j g lies in [0, E (g^2 | X_-j)] *)
have hV x : latent_box d x ->
    0 <= latent_cond_variance s mu d j f x <=
    latent_cond_expectation s mu d j (fun z => g z ^+ 2) x.
  move=> bx; rewrite ef (latent_cond_variance_shift s mu d j hs hmu jd g r 1 x
    mg gb (hr x) bx).
  rewrite (latent_cond_variance_ge0 s mu d j hs hmu jd g 1 x mg gb bx) /=.
  exact: cond_var_le.
have hCE x : latent_box d x ->
    `|latent_cond_expectation s mu d j (fun z => g z ^+ 2) x| <= 1.
  exact: (latent_cond_expectation_bound s mu d j hs hmu jd _ 1 x mg2 gb2).
have hVb x : latent_box d x -> `|latent_cond_variance s mu d j f x| <= 1.
  move=> bx; have /andP[v0 v1] := hV x bx; rewrite ger0_norm //.
  apply: le_trans v1 _; apply: le_trans (ler_norm _) _; exact: hCE.
apply/andP; split.
  rewrite -(latent_expectation0 s mu d).
  apply: (latent_expectation_le s mu d hs hmu _ _ 1 (measurable_cst _) mCVf).
    by move=> x bx; rewrite normr0 ler01 hVb.
  by move=> x bx; have /andP[] := hV x bx.
apply: (@le_trans _ _ (E (latent_cond_expectation s mu d j (fun z => g z ^+ 2)))).
  apply: (latent_expectation_le s mu d hs hmu _ _ 1 mCVf mCEg2).
    by move=> x bx; rewrite hVb // hCE.
  by move=> x bx; have /andP[] := hV x bx.
rewrite (latent_tower s mu d j hs hmu jd _ 1 mg2 gb2).
rewrite -(latent_kernel_sq_at s mu d hs hmu j jd) le_eqVlt; apply/orP; left.
have ev : (fun x : paper_main_sample 1 d =>
    paired_kernel (List.nth j (tval x) 0) ^+ 2 : RR) =
    (fun x => paired_kernel (tnth x jo) ^+ 2).
  by apply/funext => x; rewrite (tnth_nth 0) List_nthE.
rewrite ev; apply/eqP; apply: (latent_expectation_eq s mu d hmu _ _ mg2).
  apply: measurable_funX.
  exact: measurableT_comp measurable_paired_kernel (measurable_tnth jo).
by move=> x bx; rewrite /g ht_eq //; exact: bx.
Qed.

Lemma latent_tensor_lower (T : R) : (0 < d)%N ->
  latent_tensorization s mu d T -> 1 + (d%:R - 1) * s ^+ 2 / 9%:R <= T.
Proof.
move=> d0 hT.
have hf := hT f mf (ex_intro _ d%:R f_bound).
rewrite var_f in hf.
set Sg := \sum_(j < d) _ in hf.
have S0 : 0 <= Sg.
  by apply: sumr_ge0 => j _; have /andP[] := cond_var_f j (ltn_ord j).
have SB : Sg <= \sum_(j < d) (9%:R^-1 : RR).
  by apply: ler_sum => j _; have /andP[] := cond_var_f j (ltn_ord j).
rewrite sumr_const card_ord in SB.
have dn : (d%:R : RR) != 0 by rewrite pnatr_eq0 -lt0n.
have V0 : 0 < d%:R / 9%:R + d%:R * (d%:R - 1) * s ^+ 2 / 81%:R.
  have h1 : (0 : RR) < d%:R / 9%:R by rewrite divr_gt0 ?ltr0n.
  have dm1 : (0 : RR) <= d%:R - 1 by rewrite subr_ge0 ler1n.
  have h2 : (0 : RR) <= d%:R * (d%:R - 1) * s ^+ 2 / 81%:R.
    by rewrite divr_ge0 ?ler0n // mulr_ge0 ?sqr_ge0 // mulr_ge0 ?ler0n.
  by apply: lt_le_trans h1 _; rewrite lerDl.
have := tensor_bound _ _ _ _ V0 S0 SB hf.
have -> : (d%:R / 9%:R + d%:R * (d%:R - 1) * s ^+ 2 / 81%:R) / (9%:R^-1 *+ d) =
    1 + (d%:R - 1) * s ^+ 2 / 9%:R :> RR.
  by field.
by [].
Qed.

End tensor_lower.

(* 2. The exponential lower bound. *)

Lemma sign_stable {RT : realType} (hy r : RT) :
  - (3%:R / 7%:R) <= hy <= 1 -> 1 < `|r| -> (0 < hy + r) = (0 < r).
Proof.
move=> /andP[h1 h2]; rewrite ltr_normr => /orP[r1|r1].
  by apply/idP/idP => _; lra.
apply/idP/idP => h; last by lra.
by lra.
Qed.

Lemma half_le {RT : realType} (x : RT) : 2 * x <= 1 -> x <= 2^-1.
Proof. by move=> h; lra. Qed.

Lemma var_eighth {RT : realType} (e V : RT) :
  4%:R^-1 - e / 4%:R <= V -> e <= 2^-1 -> 8%:R^-1 <= V.
Proof. by move=> h1 h2; lra. Qed.

Lemma tensor_exp_arith {RT : realType} (V Sg T e dd : RT) :
  8%:R^-1 <= V -> V <= T * Sg -> 0 <= Sg -> Sg <= 4%:R^-1 * e * dd ->
  0 < e -> 0 < dd -> 2^-1 / dd * e^-1 <= T.
Proof.
move=> V8 h S0 SB e0 d0.
have V0 : 0 < V by apply: lt_le_trans V8; rewrite invr_gt0 ltr0n.
have := tensor_bound _ _ _ _ V0 S0 SB h.
apply: le_trans; rewrite ler_pdivlMr ?mulr_gt0 ?invr_gt0 ?ltr0n //.
have -> : 2^-1 / dd * e^-1 * (4%:R^-1 * e * dd) = 8%:R^-1 :> RT.
  have en : e != 0 by rewrite gt_eqF.
  have dn : dd != 0 by rewrite gt_eqF.
  by field.
exact: V8.
Qed.

Section tensor_exp.
Variables (s : R) (mu : probability (measurableTypeR R) R) (d : nat).
Hypotheses (hs : 0 <= s <= 1) (hmu : paired_uniform_spec mu).

Local Notation E := (latent_point_expectation s mu d).

Let sign_set : set (paper_main_sample 1 d) :=
  [set y | 0 < \sum_(j < d) paired_kernel (List.nth j (tval y) 0)].

Let msign : measurable sign_set.
Proof.
have -> : sign_set = [set y : paper_main_sample 1 d |
    0 < \sum_(k < 1 * d) paired_kernel (tnth y k)].
  by rewrite /sign_set; apply/seteqP; split => y /=; rewrite sum_nth_tnthT.
have mS : measurable_fun setT (fun y : paper_main_sample 1 d =>
    \sum_(k < 1 * d) paired_kernel (tnth y k) : RR).
  by apply: measurable_sum => k; exact: measurableT_comp measurable_paired_kernel
    (measurable_tnth k).
rewrite -[X in measurable X]setTI.
by apply: measurable_fun_ltr => //; exact: measurable_cst.
Qed.

Let mf : measurable_fun setT (latent_sign_test d : _ -> RR).
Proof. exact: measurable_indic msign. Qed.

Let f01 z : latent_sign_test d z = 0 \/ latent_sign_test d z = 1.
Proof. by rewrite /latent_sign_test indicE; case: (_ \in _); [right|left]. Qed.

Let fb z : `|latent_sign_test d z| <= 1.
Proof. by case: (f01 z) => ->; rewrite ?normr0 ?normr1 ?ler01. Qed.

(* 0 <= E V_j f <= P(|R_j| <= 1) / 4 *)
Let cond_var_sign (j : nat) : (j < d)%N ->
  0 <= E (latent_cond_variance s mu d j (latent_sign_test d)) <=
  4%:R^-1 * E (fun x => \1_[set y : paper_main_sample 1 d |
    `|\sum_(k < d | (k : nat) != j) paired_kernel (List.nth k (tval y) 0)| <= 1] x
    : RR).
Proof.
move=> jd.
have jd1 : (j < 1 * d)%N by rewrite mul1n.
pose jo : 'I_(1 * d) := Ordinal jd1.
pose Rj (y : paper_main_sample 1 d) : RR :=
  \sum_(k < 1 * d | (k : nat) != j) paired_kernel (tnth y k).
set A := [set y : paper_main_sample 1 d |
  `|\sum_(k < d | (k : nat) != j) paired_kernel (List.nth k (tval y) 0)| <= 1].
have eA : A = [set y | `|Rj y| <= 1].
  by rewrite /A; apply/seteqP; split => y /=; rewrite (sum_nth_tnth d (fun k => k != j)).
have mRj : measurable_fun setT Rj.
  have -> : Rj = (fun y => \sum_(k < 1 * d)
      (if (k : nat) != j then paired_kernel (tnth y k) else 0)).
    by apply/funext => y; rewrite /Rj big_mkcond.
  apply: measurable_sum => k; case: ((k : nat) != j).
    exact: measurableT_comp measurable_paired_kernel (measurable_tnth k).
  exact: measurable_cst.
have mA : measurable A.
  have mN : measurable_fun setT (fun y => `|Rj y| : RR).
    by apply: measurableT_comp; [exact: normr_measurable | exact: mRj].
  rewrite eA -[X in measurable X]setTI.
  by apply: measurable_fun_ler => //; exact: measurable_cst.
have mIA : measurable_fun setT (fun x : paper_main_sample 1 d => \1_A x : RR).
  exact: measurable_indic.
have IAb z : `|(\1_A z : RR)| <= 1.
  by rewrite indicE; case: (_ \in _); rewrite ?normr0 ?normr1 ?ler01.
have [_ mCV] := measurable_latent_cond s mu d j hs hmu jd _ 1 mf fb.
(* the sum of the kernels at the point x with x_j := y *)
have sum_rep x y : \sum_(k < d) paired_kernel
    (List.nth k (tval (latent_replace d j x y)) 0) = paired_kernel y + Rj x.
  transitivity (\sum_(k < 1 * d)
      (paired_kernel (tnth (latent_replace d j x y) k) : RR)).
    exact: (sum_nth_tnthT d paired_kernel (latent_replace d j x y)).
  have e1 : \sum_(k < 1 * d)
      (paired_kernel (tnth (latent_replace d j x y) k) : RR) =
      paired_kernel (tnth (latent_replace d j x y) jo) +
      \sum_(k < 1 * d | k != jo) paired_kernel (tnth (latent_replace d j x y) k).
    by rewrite (bigD1 jo).
  rewrite e1; congr (_ + _).
    by rewrite /latent_replace tnth_mktuple eqxx.
  apply: eq_big => [k|k kj] //.
  have kj' : (k == j :> nat) = false := negbTE kj.
  by rewrite /latent_replace tnth_mktuple kj'.
have hCV x : latent_box d x ->
    0 <= latent_cond_variance s mu d j (latent_sign_test d) x <=
    4%:R^-1 * \1_A x.
  move=> bx; rewrite (latent_cond_variance_ge0 s mu d j hs hmu jd _ 1 x mf fb bx) /=.
  rewrite indicE; case: (boolP (x \in A)) => [_|nA].
    by rewrite mulr1; exact: latent_cond_variance_indicator.
  have r1 : 1 < `|Rj x|.
    rewrite ltNge; apply/negP => h; move/negP: nA; apply; rewrite inE eA.
    exact: h.
  rewrite mulr0 (latent_cond_variance_const s mu d j hs hmu jd _
    (if 0 < Rj x then 1 else 0) x mf bx) // => y yc.
  have e : (0 < \sum_(k < d) paired_kernel
      (List.nth k (tval (latent_replace d j x y)) 0)) = (0 < Rj x).
    by rewrite sum_rep (sign_stable _ _ (paired_kernel_range y yc) r1).
  rewrite /latent_sign_test indicE.
  case: (boolP (0 < Rj x)) => h; rewrite -e in h.
    by rewrite mem_set.
  by rewrite memNset //= => h'; rewrite h' in h.

have q1 x : `|4%:R^-1 * (\1_A x : RR)| <= 1.
  rewrite indicE; case: (_ \in _); rewrite /= ?mulr0 ?normr0 ?ler01 //.
  by rewrite mulr1 ger0_norm ?invr_ge0 ?ler0n // invf_le1 ?ltr0n // ler1n.
have hCVb x : latent_box d x ->
    `|latent_cond_variance s mu d j (latent_sign_test d) x| <= 1.
  move=> bx; have /andP[c0 c1] := hCV x bx; rewrite ger0_norm //.
  exact: le_trans c1 (le_trans (ler_norm _) (q1 x)).
apply/andP; split.
  rewrite -(latent_expectation0 s mu d).
  apply: (latent_expectation_le s mu d hs hmu _ _ 1 (measurable_cst _) mCV).
    by move=> x bx; rewrite normr0 ler01 hCVb.
  by move=> x bx; have /andP[] := hCV x bx.
rewrite -(latent_expectationZ s mu d hs hmu _ _ 1 mIA IAb).
apply: (latent_expectation_le s mu d hs hmu _ _ 1 mCV).
- by apply: measurable_funM => //; exact: measurable_cst.
- by move=> x bx; rewrite hCVb // q1.
by move=> x bx; have /andP[] := hCV x bx.
Qed.

Lemma latent_tensor_exp (T : R) : (0 < d)%N -> 18%:R <= (d%:R - 1) * s ->
  expR (- (d%:R * s ^+ 2 / (24%:R * 81%:R))) <= 2^-1 ->
  latent_tensorization s mu d T ->
  2^-1 / d%:R * expR ((48%:R * 324%:R)^-1 * s ^+ 2 * (d%:R - 1)) <= T.
Proof.
move=> d0 ds e2 hT.
have hf := hT _ mf (ex_intro _ 1 fb).
have /andP[vlo _] := latent_sign_variance s mu d hs hmu d0.
have V8 : 8%:R^-1 <= latent_variance s mu d (latent_sign_test d).
  exact: (var_eighth _ _ vlo e2).
set e' := expR (- ((d%:R - 1) * s ^+ 2 / (48%:R * 324%:R))).
have Sb (j : 'I_d) :
    0 <= E (latent_cond_variance s mu d j (latent_sign_test d)) <= 4%:R^-1 * e'.
  have /andP[c0 c1] := cond_var_sign j (ltn_ord j).
  rewrite c0 /=; apply: le_trans c1 _; rewrite ler_pM2l ?invr_gt0 ?ltr0n //.
  exact: (latent_other_small s mu d hs hmu j (ltn_ord j) ds).
set Sg := \sum_(j < d) _ in hf.
have S0 : 0 <= Sg by apply: sumr_ge0 => j _; have /andP[] := Sb j.
have SB : Sg <= 4%:R^-1 * e' * d%:R.
  apply: (@le_trans _ _ (\sum_(j < d) (4%:R^-1 * e' : RR))).
    by apply: ler_sum => j _; have /andP[] := Sb j.
  by rewrite sumr_const card_ord mulr_natr.
have e0 : 0 < e' := expR_gt0 _.
have dR : (0 : RR) < d%:R by rewrite ltr0n.
have := tensor_exp_arith _ _ _ _ _ V8 hf S0 SB e0 dR.
have -> : e'^-1 = expR ((48%:R * 324%:R)^-1 * s ^+ 2 * (d%:R - 1)).
  rewrite /e' -expRN opprK; congr expR.
  have n : (48%:R * 324%:R : RR) != 0 by rewrite mulf_neq0 ?pnatr_eq0.
  by field.
by [].
Qed.

End tensor_exp.

Theorem latent_tensor_theorem : latent_tensorization_statement.
Proof.
split.
  move=> s mu d T hs hmu d0 hT.
  exact: (latent_tensor_lower s mu d hs hmu T d0 hT).
exists ((48%:R * 324%:R)^-1), 2^-1.
split; first by rewrite invr_gt0 mulr_gt0 ?ltr0n.
split; first by rewrite invr_gt0 ltr0n.
move=> s mu /andP[s0 s1] hmu.
have hs : 0 <= s <= 1 by rewrite (ltW s0) s1.
have sn : s != 0 by rewrite gt_eqF.
have c0 : 0 < 24%:R * 81%:R / s ^+ 2.
  by rewrite divr_gt0 ?exprn_gt0 // mulr_gt0 ?ltr0n.
have [D1 hD1] := expR_lin_small _ _ c0 ltr01.
pose D2 := (archimedean.Num.truncn (18%:R / s)).+2.
exists (maxn (maxn D1 D2) 1) => d T.
rewrite !geq_max => /andP[/andP[dD1 dD2] d1] hT.
have ds : 18%:R <= (d%:R - 1) * s.
  have h : 18%:R / s < (d.-1)%:R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    rewrite ler_nat -ltnS (ltn_predK d1); exact: dD2.
  have -> : (d%:R - 1 : RR) = (d.-1)%:R.
    by rewrite -subn1 natrB // ler1n.
  by apply: ltW; rewrite -ltr_pdivrMr.
have e2 : expR (- (d%:R * s ^+ 2 / (24%:R * 81%:R))) <= 2^-1.
  apply: half_le.
  have -> : d%:R * s ^+ 2 / (24%:R * 81%:R) = d%:R / (24%:R * 81%:R / s ^+ 2).
    by field.
  exact: hD1 d dD1.
exact: (latent_tensor_exp s mu d hs hmu T d1 ds e2 hT).
Qed.
