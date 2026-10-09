(* The conditional law of one coordinate of the latent-sign law given the
   others, at Stdlib's R: tools of item R2b of phase 9 for the definitions
   latent_replace, latent_cond_expectation and latent_cond_variance of the
   frozen LatentTensorization. Fix 0 <= s <= 1, the uniform law mu, d and
   j < d; rho is the density latent_sample_density s 1 d of a point
   against the product U of d copies of mu, h = paired_kernel, and the box
   is the set of the points whose coordinates lie in [-sqrt 3, sqrt 3],
   which carries U.

   1. Generic facts: measurable_inv, x |-> x^-1 is measurable on a
      realType; integrable_bounded_mul, a bounded measurable function times
      an integrable one is integrable.
   2. One coordinate. latent_replace d j x y is tuple_set x j y
      (latent_replace_set), so replacing twice is replacing once
      (latent_replace_idem). The density factors along the coordinate j:
      rho (x with x_j := y) = ((1 + s h y) P_s x + (1 - s h y) P_(-s) x) / 2
      (latent_density_replace), with P_a x the product of the 1 + a h(x_k)
      over k != j (latent_coord_prod). Hence the denominator of the
      conditional expectation is (P_s x + P_(-s) x) / 2, positive on the
      box (latent_cond_den, latent_cond_den_gt0).
   3. The conditional expectation and variance at a point of the box, for
      a bounded measurable g: |E (g | X_-j)| is at most the bound of g
      (latent_cond_expectation_bound); Var (g | X_-j) >= 0, since it is the
      integral of (g - E (g | X_-j))^2 against the conditional weights
      (latent_cond_variance_ge0); it does not change when one adds a
      function that does not depend on x_j (latent_cond_variance_shift);
      it is 0 when g does not depend on x_j on the box
      (latent_cond_variance_const), and at most 1/4 when g takes the
      values 0 and 1 (latent_cond_variance_indicator).
   4. Measurability and the tower property: x |-> E (g | X_-j)(x) and
      x |-> Var (g | X_-j)(x) are measurable (measurable_latent_cond); by
      Fubini at the coordinate j (integral_tuple_prod_set of
      library/probability/efron_stein.v),
      E [E (g | X_-j)] = E g (latent_tower).
   5. Expectations of functions that are bounded on the box: they do not
      depend on the values off the box (latent_expectation_box), and they
      are monotone (latent_expectation_le); two functions equal on the box
      have the same expectation (latent_expectation_eq); a constant factor
      comes out (latent_expectationZ).
   6. For the finite tensorization constant of Paired/TensorUpper:
      linearity (latent_expectationD, latent_expectation_cst); for g that
      does not depend on x_j, E g = int g Z dU (latent_expectation_indep);
      Z Var (g | X_-j) = int (g - E (g | X_-j))^2 rho on the box
      (latent_cond_variance_mul), hence w Var_mu (g (x with x_j := .)) <=
      Z Var (g | X_-j) when w <= rho on the support
      (latent_cond_variance_weight); Z <= w when rho <= w on the support
      (latent_cond_den_le). *)

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
From GaussianAnalysis.probability Require Import efron_stein.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import PairedDefinitions.
From EllipsoidUniversality Require Import LatentSignDefinitions LatentSignScope.
From EllipsoidUniversality Require Import LatentTensorization.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Paired Require Import Uniform Law LatentSign Scope.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. Generic facts. *)

Lemma measurable_inv {RT : realType} : measurable_fun setT (fun x : RT => x^-1).
Proof.
have e : [set: RT] = [set 0] `|` ~` [set 0].
  apply/seteqP; split => // x _.
  have [->|x0] := eqVneq x 0; first by left.
  by right => /= x00; rewrite x00 eqxx in x0.
rewrite e; apply/measurable_funU.
- exact: measurable_set1.
- exact: measurableC (measurable_set1 _).
split; first exact: measurable_fun_set1.
apply: open_continuous_measurable_fun.
  apply: closed_openC; apply: accessible_closed_set1.
  by apply: hausdorff_accessible; exact: Rhausdorff.
by move=> x; rewrite inE /= => /eqP x0; exact: inv_continuous.
Qed.

Lemma integrable_bounded_mul d' (T : measurableType d') (RT : realType)
    (P : {measure set T -> \bar RT}) (g w : T -> RT) (M : RT) :
  measurable_fun setT g -> (forall x, `|g x| <= M) ->
  P.-integrable setT (EFin \o w) ->
  P.-integrable setT (EFin \o (fun x => g x * w x)).
Proof.
move=> mg gM wi.
have mw : measurable_fun setT w by apply/measurable_EFinP; exact: measurable_int wi.
apply: (le_integrable measurableT _ _ (integrableZl measurableT `|M| wi)).
  by apply/measurable_EFinP; exact: measurable_funM.
move=> x _; rewrite /comp -EFinM /= lee_fin !normrM normr_id.
by apply: ler_wpM2r; [exact: normr_ge0 | exact: le_trans (gM x) (ler_norm M)].
Qed.

(* The arithmetic of the factors 1 + a h on the box. *)
Lemma factor_pos {RT : realType} (s h : RT) :
  0 <= s <= 1 -> - (3%:R / 7%:R) <= h <= 1 -> 0 < 1 + s * h.
Proof. by move=> /andP[s0 s1] /andP[h1 h2]; nra. Qed.

Lemma factor_neg_ge0 {RT : realType} (s h : RT) :
  0 <= s <= 1 -> - (3%:R / 7%:R) <= h <= 1 -> 0 <= 1 + - s * h.
Proof. by move=> /andP[s0 s1] /andP[h1 h2]; nra. Qed.

(* The density of the latent law, on the coordinate j, is an affine
   function of h(y). *)
Section affine_continuous.
Context {RT : realType}.

Lemma continuous_affine_legendre (c A B a b : RT) :
  continuous (fun y => ((1 + a * legendre4 c y) * A +
                        (1 + b * legendre4 c y) * B) / 2%:R).
Proof.
move=> y; apply: cvgM; last exact: cvg_cst.
apply: cvgD; apply: cvgM; try exact: cvg_cst.
  apply: cvgD; first exact: cvg_cst.
  by apply: cvgM; [exact: cvg_cst|exact: continuous_legendre4].
apply: cvgD; first exact: cvg_cst.
by apply: cvgM; [exact: cvg_cst|exact: continuous_legendre4].
Qed.

End affine_continuous.

(* The box of the points whose coordinates lie in [-sqrt 3, sqrt 3]. *)
Definition latent_box (d : nat) : set (paper_main_sample 1 d) :=
  [set x | forall k : 'I_(1 * d), `|tnth x k| <= Num.sqrt 3%:R].

(* Its indicator, as a product of indicators of the coordinates. *)
Definition latent_box_ind (d : nat) (x : paper_main_sample 1 d) : R :=
  \prod_(k < 1 * d) \1_[set y : RR | `|y| <= Num.sqrt 3%:R] (tnth x k).

Lemma measurable_latent_box_ind d :
  measurable_fun setT (fun x : paper_main_sample 1 d => latent_box_ind d x : RR).
Proof.
apply: measurable_prod => k _.
apply: measurableT_comp (measurable_tnth k).
apply: measurable_indic.
by rewrite -[X in measurable X]setTI; apply: measurable_fun_ler.
Qed.

Lemma latent_box_ind1 d x : latent_box d x -> latent_box_ind d x = 1.
Proof.
move=> bx; rewrite /latent_box_ind; apply: big1 => k _.
by rewrite indicE mem_set //; exact: bx.
Qed.

Lemma latent_box_ind0 d x : ~ latent_box d x -> latent_box_ind d x = 0.
Proof.
move=> nb; have [k hk] : exists k : 'I_(1 * d), ~ (`|tnth x k| <= Num.sqrt 3%:R).
  apply: contrapT => h; apply: nb => k.
  by apply: contrapT => hk; apply: h; exists k.
by rewrite /latent_box_ind (bigD1 k) //= indicE memNset ?mul0r.
Qed.

Lemma latent_box_ind_bound d x : `|latent_box_ind d x| <= 1.
Proof.
have [bx|nb] := pselect (latent_box d x).
  by rewrite latent_box_ind1 // normr1.
by rewrite latent_box_ind0 // normr0.
Qed.

Lemma var_identity {RT : realType} (A Ng Zx m : RT) : Zx != 0 -> Ng = m * Zx ->
  A / Zx - (Ng / Zx) ^+ 2 = (A + 2%:R * (- m) * Ng + (- m) ^+ 2 * Zx) / Zx.
Proof. by move=> Zn ->; field. Qed.

Lemma shift_identity {RT : realType} (A Ng Zx r : RT) : Zx != 0 ->
  (A + 2%:R * r * Ng + r ^+ 2 * Zx) / Zx - ((Ng + r * Zx) / Zx) ^+ 2 =
  A / Zx - (Ng / Zx) ^+ 2.
Proof. by move=> Zn; field. Qed.

Lemma const_identity {RT : realType} (c Zx : RT) : Zx != 0 ->
  c ^+ 2 * Zx / Zx - (c * Zx / Zx) ^+ 2 = 0.
Proof. by move=> Zn; field. Qed.

Lemma sqr_dev_bound {RT : realType} (A B m : RT) :
  A - B ^+ 2 <= A - 2%:R * m * B + m ^+ 2.
Proof. by have := sqr_ge0 (B - m); nra. Qed.

Lemma quarter_bound {RT : realType} (p : RT) : p - p ^+ 2 <= 4%:R^-1.
Proof. by have := sqr_ge0 (p - 2%:R^-1); nra. Qed.

Lemma bound_ge0 {T : Type} {RT : realType} (g : T -> RT) (M : RT) (z : T) :
  (forall z, `|g z| <= M) -> 0 <= M.
Proof. by move=> gM; exact: le_trans (normr_ge0 _) (gM z). Qed.

Lemma integrable_prob_bounded' d' (T : measurableType d') (RT : realType)
    (P : probability T RT) (g : T -> RT) (M : RT) :
  measurable_fun setT g -> (forall x, `|g x| <= M) ->
  P.-integrable setT (EFin \o g).
Proof.
move=> mg gM.
have i1 : P.-integrable setT (EFin \o (fun _ : T => (1 : RT))).
  exact: finite_measure_integrable_cst.
apply: (eq_integrable measurableT _ _ _
  (integrable_bounded_mul _ _ _ P g (fun=> 1) M mg gM i1)) => x _ /=.
by rewrite mulr1.
Qed.

Section latent_cond.
Variables (s : R) (mu : probability (measurableTypeR R) R) (d j : nat).
Hypotheses (hs : 0 <= s <= 1) (hmu : paired_uniform_spec mu) (jd : (j < d)%N).

Local Notation U := (universality_sample_law (fun=> mu) 1 d).
Local Notation rho := (latent_sample_density s 1 d).
Local Notation rep := (latent_replace d j).

Let c0 : (0 : RR) < Num.sqrt 3%:R. Proof. by rewrite sqrtr_gt0 ltr0n. Qed.
Let hP : sym_uniform_spec (Num.sqrt 3%:R : RR) mu. Proof. exact: hmu. Qed.

Let jd' : (j < 1 * d)%N. Proof. by rewrite mul1n. Qed.
Let j' : 'I_(1 * d) := Ordinal jd'.

(* 2. One coordinate. *)

Lemma latent_replace_set x y : rep x y = tuple_set x j' y.
Proof. by apply: eq_from_tnth => k; rewrite !tnth_mktuple. Qed.

Lemma latent_replace_idem x t y : rep (rep x t) y = rep x y.
Proof. by rewrite !latent_replace_set tuple_set_set. Qed.

Lemma tnth_latent_replace x y (k : 'I_(1 * d)) :
  tnth (rep x y) k = if k == j' then y else tnth x k.
Proof. by rewrite latent_replace_set tnth_mktuple. Qed.

(* The product of the factors of the other coordinates. *)
Definition latent_coord_prod (a : R) (x : paper_main_sample 1 d) : RR :=
  \prod_(k < 1 * d | k != j') (1 + a * paired_kernel (tnth x k)).

Local Notation Pj := latent_coord_prod.

Lemma latent_coord_prod_replace a x t : Pj a (rep x t) = Pj a x.
Proof. by apply: eq_bigr => k kj; rewrite tnth_latent_replace (negbTE kj). Qed.

Lemma latent_prod_replace a x y :
  latent_prod a d (rep x y) = (1 + a * paired_kernel y) * Pj a x.
Proof.
rewrite /latent_prod (bigD1 j') //= tnth_latent_replace eqxx; congr (_ * _).
by apply: eq_bigr => k kj; rewrite tnth_latent_replace (negbTE kj).
Qed.

Lemma latent_density_replace x y :
  rho (rep x y) = ((1 + s * paired_kernel y) * Pj s x +
                   (1 + (- s)%R * paired_kernel y) * Pj (- s)%R x) / 2%:R.
Proof. by rewrite latent_densityE !latent_prod_replace. Qed.

Lemma latent_box_replace x y : latent_box d x ->
  `|y| <= Num.sqrt 3%:R -> latent_box d (rep x y).
Proof.
by move=> bx yc k; rewrite tnth_latent_replace; case: ifP => _; [exact: yc|exact: bx].
Qed.

Lemma latent_coord_prod_pos x : latent_box d x -> 0 < Pj s x.
Proof.
move=> bx; apply: prodr_gt0 => k _.
exact: (factor_pos _ _ hs (paired_kernel_range _ (bx k))).
Qed.

Lemma latent_coord_prod_ge0 x : latent_box d x -> 0 <= Pj (- s)%R x.
Proof.
move=> bx; apply: prodr_ge0 => k _.
exact: (factor_neg_ge0 _ _ hs (paired_kernel_range _ (bx k))).
Qed.

Lemma latent_density_ge0 z : latent_box d z -> 0 <= rho z.
Proof.
move=> bz; rewrite latent_densityE; apply: divr_ge0; last by rewrite ler0n.
apply: addr_ge0; apply: prodr_ge0 => k _.
  exact: ltW (factor_pos _ _ hs (paired_kernel_range _ (bz k))).
exact: (factor_neg_ge0 _ _ hs (paired_kernel_range _ (bz k))).
Qed.

Let crho x : continuous (fun y : RR => rho (rep x y) : RR).
Proof.
have -> : (fun y : RR => rho (rep x y) : RR) = (fun y =>
    ((1 + s * legendre4 (Num.sqrt 3%:R) y) * Pj s x +
     (1 + (- s)%R * legendre4 (Num.sqrt 3%:R) y) * Pj (- s)%R x) / 2%:R).
  by apply/funext => y; rewrite latent_density_replace.
exact: continuous_affine_legendre.
Qed.

Let irho x : mu.-integrable setT (EFin \o (fun y : RR => rho (rep x y) : RR)).
Proof. exact: (integrable_sym_uniform _ _ c0 hP _ (crho x)). Qed.

Let mrep x : measurable_fun setT (rep x).
Proof.
apply/measurable_fun_tnthP => k.
apply: (eq_measurable_fun (fun y : RR => if k == j' then y else tnth x k)).
  by move=> y _; rewrite /= tnth_latent_replace.
by case: (k == j'); [exact: measurable_id | exact: measurable_cst].
Qed.

Let int_lin (a : R) : \int[mu]_y (1 + a * paired_kernel y : RR) = 1.
Proof.
transitivity (\int[mu]_y
    (y ^+ 0 * (1 + a * legendre4 (Num.sqrt 3%:R) y) : RR)).
  by apply: eq_Rintegral => y _; rewrite expr0 mul1r.
exact: (Rintegral_legendre0 (Num.sqrt 3%:R) mu c0 hP a).
Qed.

Let ilin (a : R) : mu.-integrable setT
  (EFin \o (fun y : RR => 1 + a * paired_kernel y : RR)).
Proof.
apply: (integrable_sym_uniform _ _ c0 hP).
move=> y; apply: cvgD; first exact: cvg_cst.
by apply: cvgM; [exact: cvg_cst|exact: continuous_legendre4].
Qed.

(* The denominator of the conditional expectation. *)
Lemma latent_cond_den x :
  \int[mu]_y (rho (rep x y) : RR) = (Pj s x + Pj (- s)%R x) / 2%:R.
Proof.
transitivity (\int[mu]_y (Pj s x / 2%:R * (1 + s * paired_kernel y) +
    Pj (- s)%R x / 2%:R * (1 + (- s)%R * paired_kernel y) : RR)).
  by apply: eq_Rintegral => y _; rewrite latent_density_replace; ring.
have i1 : mu.-integrable setT (EFin \o (fun y : RR =>
    Pj s x / 2%:R * (1 + s * paired_kernel y) : RR)).
  apply: (eq_integrable measurableT _ _ _
    (integrableZl measurableT (Pj s x / 2%:R) (ilin s))) => y _ /=.
  by rewrite EFinM.
have i2 : mu.-integrable setT (EFin \o (fun y : RR =>
    Pj (- s)%R x / 2%:R * (1 + (- s)%R * paired_kernel y) : RR)).
  apply: (eq_integrable measurableT _ _ _
    (integrableZl measurableT (Pj (- s)%R x / 2%:R) (ilin (- s)%R))) => y _ /=.
  by rewrite EFinM.
rewrite (RintegralD measurableT i1 i2).
rewrite (RintegralZl _ measurableT (ilin s)) (RintegralZl _ measurableT (ilin (- s)%R)).
by rewrite !int_lin !mulr1 -mulrDl.
Qed.

Lemma latent_cond_den_gt0 x : latent_box d x ->
  0 < \int[mu]_y (rho (rep x y) : RR).
Proof.
move=> bx; rewrite latent_cond_den divr_gt0 ?ltr0n //.
exact: ltr_wpDr (latent_coord_prod_ge0 x bx) (latent_coord_prod_pos x bx).
Qed.

(* 3. The conditional expectation and variance at a point of the box. *)

Let N (g : paper_main_sample 1 d -> R) (x : paper_main_sample 1 d) : RR :=
  \int[mu]_y (g (rep x y) * rho (rep x y) : RR).

Let Z (x : paper_main_sample 1 d) : RR := \int[mu]_y (rho (rep x y) : RR).

Let CEE g x : latent_cond_expectation s mu d j g x = N g x / Z x.
Proof. by []. Qed.

Let iN (g : paper_main_sample 1 d -> R) (M : R) x :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  mu.-integrable setT (EFin \o (fun y : RR => g (rep x y) * rho (rep x y) : RR)).
Proof.
move=> mg gM.
apply: (integrable_bounded_mul _ _ _ mu (fun y : RR => g (rep x y) : RR)
  (fun y : RR => rho (rep x y) : RR) M _ (fun y => gM (rep x y)) (irho x)).
exact: measurableT_comp mg (mrep x).
Qed.

(* Integrals against mu only see [-sqrt 3, sqrt 3]. *)
Let Rint_eq (q1 q2 : RR -> RR) :
  measurable_fun setT q1 -> measurable_fun setT q2 ->
  (forall y, `|y| <= Num.sqrt 3%:R -> q1 y = q2 y) ->
  \int[mu]_y q1 y = \int[mu]_y q2 y.
Proof.
move=> m1 m2 e; rewrite /Rintegral; congr fine.
apply: ae_eq_integral => //; [exact/measurable_EFinP|exact/measurable_EFinP|].
by apply: (sym_uniform_ae _ _ hP) => y yc /=; rewrite e.
Qed.

Let Rint_le (q1 q2 : RR -> RR) :
  mu.-integrable setT (EFin \o q1) -> mu.-integrable setT (EFin \o q2) ->
  (forall y, `|y| <= Num.sqrt 3%:R -> q1 y <= q2 y) ->
  \int[mu]_y q1 y <= \int[mu]_y q2 y.
Proof.
move=> i1 i2 h.
pose b := fun y : RR => \1_[set y : RR | `|y| <= Num.sqrt 3%:R] y : RR.
have mb : measurable_fun setT b.
  apply: measurable_indic.
  by rewrite -[X in measurable X]setTI; apply: measurable_fun_ler.
have bb y : `|b y| <= 1.
  by rewrite /b indicE; case: (_ \in _); rewrite ?normr1 ?normr0.
have m1 : measurable_fun setT q1 by apply/measurable_EFinP; exact: measurable_int i1.
have m2 : measurable_fun setT q2 by apply/measurable_EFinP; exact: measurable_int i2.
have e (q : RR -> RR) : measurable_fun setT q ->
    \int[mu]_y q y = \int[mu]_y (b y * q y).
  move=> mq; apply: Rint_eq => //; first exact: measurable_funM.
  by move=> y yc; rewrite /b indicE mem_set // mul1r.
rewrite (e _ m1) (e _ m2).
apply: le_Rintegral => //.
- exact: (integrable_bounded_mul _ _ _ mu b q1 1 mb bb i1).
- exact: (integrable_bounded_mul _ _ _ mu b q2 1 mb bb i2).
move=> y _; rewrite /b indicE; case: (boolP (y \in _)) => [/set_mem yc|_].
  by rewrite !mul1r; exact: h.
by rewrite !mul0r.
Qed.

Let Rint_ge0 (q : RR -> RR) : mu.-integrable setT (EFin \o q) ->
  (forall y, `|y| <= Num.sqrt 3%:R -> 0 <= q y) -> 0 <= \int[mu]_y q y.
Proof.
move=> qi h.
have i0 : mu.-integrable setT (EFin \o (fun _ : RR => (0 : RR))).
  exact: finite_measure_integrable_cst.
have := Rint_le _ _ i0 qi h.
by rewrite Rintegral_cst // mul0r.
Qed.

Let rho_rep_ge0 x y : latent_box d x -> `|y| <= Num.sqrt 3%:R ->
  0 <= rho (rep x y).
Proof.
by move=> bx yc; apply: latent_density_ge0; exact: latent_box_replace.
Qed.

(* |N g x| <= M Z x on the box. *)
Let N_bound (g : paper_main_sample 1 d -> R) (M : R) x :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  latent_box d x -> `|N g x| <= M * Z x.
Proof.
move=> mg gM bx.
have iZ := irho x.
have iZM (c : RR) : mu.-integrable setT
    (EFin \o (fun y : RR => c * rho (rep x y) : RR)).
  apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT c iZ)).
  by move=> y _ /=; rewrite EFinM.
have iNg := iN g M x mg gM.
have eZ (c : RR) : \int[mu]_y (c * rho (rep x y) : RR) = c * Z x.
  exact: RintegralZl.
rewrite ler_norml; apply/andP; split.
  rewrite -mulNr -eZ; apply: Rint_le => // y yc.
  apply: ler_wpM2r; first exact: rho_rep_ge0.
  by have := gM (rep x y); rewrite ler_norml => /andP[].
rewrite -eZ; apply: Rint_le => // y yc.
apply: ler_wpM2r; first exact: rho_rep_ge0.
by have := gM (rep x y); rewrite ler_norml => /andP[].
Qed.

Lemma latent_cond_expectation_bound (g : paper_main_sample 1 d -> R) (M : R) x :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  latent_box d x -> `|latent_cond_expectation s mu d j g x| <= M.
Proof.
move=> mg gM bx.
have Z0 : 0 < Z x := latent_cond_den_gt0 x bx.
rewrite CEE normrM normfV (gtr0_norm Z0) ler_pdivrMr //.
exact: N_bound.
Qed.

Let sq_bound (g : paper_main_sample 1 d -> R) (M : R) :
  (forall z, `|g z| <= M) -> forall z, `|g z ^+ 2| <= M ^+ 2.
Proof.
move=> gM z; rewrite normrX; apply: lerXn2r; rewrite ?nnegrE ?normr_ge0 //.
exact: (bound_ge0 g M z gM).
Qed.

(* N of g + r and of (g + r)^2, for r that does not depend on x_j. *)
Let N_shift (g r : paper_main_sample 1 d -> R) (M Mr : R) x :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  (forall t, r (rep x t) = r x) ->
  N (fun z => g z + r z) x = N g x + r x * Z x /\
  N (fun z => (g z + r z) ^+ 2) x =
  N (fun z => g z ^+ 2) x + 2%:R * r x * N g x + r x ^+ 2 * Z x.
Proof.
move=> mg gM hr.
have mg2 : measurable_fun setT (fun z => g z ^+ 2 : RR) by exact: measurable_funX.
have i1 := iN g M x mg gM.
have i2 := iN _ _ x mg2 (sq_bound g M gM).
have iZ := irho x.
have iZM (c : RR) : mu.-integrable setT
    (EFin \o (fun y : RR => c * rho (rep x y) : RR)).
  apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT c iZ)).
  by move=> y _ /=; rewrite EFinM.
have iNM (c : RR) : mu.-integrable setT
    (EFin \o (fun y : RR => c * (g (rep x y) * rho (rep x y)) : RR)).
  apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT c i1)).
  by move=> y _ /=; rewrite EFinM.
split.
  transitivity (\int[mu]_y (g (rep x y) * rho (rep x y) +
      r x * rho (rep x y) : RR)).
    by apply: eq_Rintegral => y _; rewrite hr mulrDl.
  by rewrite (RintegralD measurableT i1 (iZM (r x))) (RintegralZl _ measurableT iZ).
have i3 : mu.-integrable setT (EFin \o (fun y : RR =>
    g (rep x y) ^+ 2 * rho (rep x y) +
    2%:R * r x * (g (rep x y) * rho (rep x y)) : RR)).
  apply: (eq_integrable measurableT _ _ _ (integrableD measurableT i2
    (iNM (2%:R * r x)))) => y _ /=.
  by rewrite EFinD.
transitivity (\int[mu]_y (g (rep x y) ^+ 2 * rho (rep x y) +
    2%:R * r x * (g (rep x y) * rho (rep x y)) +
    r x ^+ 2 * rho (rep x y) : RR)).
  by apply: eq_Rintegral => y _; rewrite hr; ring.
rewrite (RintegralD measurableT i3 (iZM (r x ^+ 2))).
rewrite (RintegralD measurableT i2 (iNM (2%:R * r x))).
by rewrite (RintegralZl _ measurableT i1) (RintegralZl _ measurableT iZ).
Qed.

(* Var (g | X_-j) >= 0 on the box. *)
Lemma latent_cond_variance_ge0 (g : paper_main_sample 1 d -> R) (M : R) x :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  latent_box d x -> 0 <= latent_cond_variance s mu d j g x.
Proof.
move=> mg gM bx.
have Z0 : 0 < Z x := latent_cond_den_gt0 x bx.
have Zn : Z x != 0 := lt0r_neq0 Z0.
set m := N g x / Z x.
have [_ e2] := N_shift g (fun=> - m) M `|m| x mg gM (fun=> erefl).
have mg2 : measurable_fun setT (fun z => (g z - m) ^+ 2 : RR).
  by apply: measurable_funX; apply: measurable_funB => //; exact: measurable_cst.
have gmM z : `|g z - m| <= M + `|m|.
  by apply: le_trans (ler_normB _ _) _; rewrite lerD2r.
have i := iN _ _ x mg2 (sq_bound _ _ gmM).
have pos : 0 <= N (fun z => (g z - m) ^+ 2) x.
  apply: Rint_ge0 => // y yc.
  by apply: mulr_ge0; [exact: sqr_ge0 | exact: rho_rep_ge0].
have e : latent_cond_variance s mu d j g x = N (fun z => (g z - m) ^+ 2) x / Z x.
  rewrite /latent_cond_variance !CEE e2.
  have em : N g x = m * Z x by rewrite /m divfK.
  exact: (var_identity _ _ _ _ Zn em).
by rewrite e divr_ge0 // ltW.
Qed.

(* Var (g + r | X_-j) = Var (g | X_-j) on the box, for r that does not
   depend on x_j. *)
Lemma latent_cond_variance_shift (g r : paper_main_sample 1 d -> R) (M : R) x :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  (forall t, r (rep x t) = r x) -> latent_box d x ->
  latent_cond_variance s mu d j (fun z => g z + r z) x =
  latent_cond_variance s mu d j g x.
Proof.
move=> mg gM hr bx.
have Zn : Z x != 0 := lt0r_neq0 (latent_cond_den_gt0 x bx).
have [e1 e2] := N_shift g r M 0 x mg gM hr.
rewrite /latent_cond_variance !CEE e1 e2.
exact: (shift_identity _ _ _ _ Zn).
Qed.

(* Var (g | X_-j) = 0 at a point of the box where g does not depend on
   x_j. *)
Lemma latent_cond_variance_const (g : paper_main_sample 1 d -> R) (c : R) x :
  measurable_fun setT (g : _ -> RR) -> latent_box d x ->
  (forall y, `|y| <= Num.sqrt 3%:R -> g (rep x y) = c) ->
  latent_cond_variance s mu d j g x = 0.
Proof.
move=> mg bx hc.
have Zn : Z x != 0 := lt0r_neq0 (latent_cond_den_gt0 x bx).
have mrho : measurable_fun setT (fun y : RR => rho (rep x y) : RR).
  exact: continuous_measurable_fun (crho x).
have mgr : measurable_fun setT (fun y : RR => g (rep x y) : RR).
  exact: measurableT_comp mg (mrep x).
have e1 : N g x = c * Z x.
  rewrite -(RintegralZl _ measurableT (irho x)); apply: Rint_eq => //.
  - exact: measurable_funM.
  - by apply: measurable_funM => //; exact: measurable_cst.
  - by move=> y yc; rewrite hc.
have e2 : N (fun z => g z ^+ 2) x = c ^+ 2 * Z x.
  rewrite -(RintegralZl _ measurableT (irho x)); apply: Rint_eq => //.
  - by apply: measurable_funM => //; exact: measurable_funX.
  - by apply: measurable_funM => //; exact: measurable_cst.
  - by move=> y yc; rewrite hc.
rewrite /latent_cond_variance !CEE e1 e2.
exact: (const_identity _ _ Zn).
Qed.

(* Var (g | X_-j) <= 1/4 for g with values 0 and 1. *)
Lemma latent_cond_variance_indicator (g : paper_main_sample 1 d -> R) x :
  (forall z, g z = 0 \/ g z = 1) ->
  latent_cond_variance s mu d j g x <= 4%:R^-1.
Proof.
move=> g01; rewrite /latent_cond_variance.
have -> : (fun z => g z ^+ 2) = g.
  by apply/funext => z; case: (g01 z) => ->; rewrite ?expr0n ?expr1n.
exact: quarter_bound.
Qed.

(* 4. Measurability and the tower property. *)

Let mrho : measurable_fun setT (rho : paper_main_sample 1 d -> RR).
Proof.
have -> : (rho : paper_main_sample 1 d -> RR) =
    (fun x => (latent_prod s d x + latent_prod (- s)%R d x) / 2%:R).
  by apply/funext => x; rewrite latent_densityE.
apply: measurable_funM; last exact: measurable_cst.
by apply: measurable_funD; exact: measurable_latent_prod.
Qed.

Let iU (g : paper_main_sample 1 d -> R) (M : R) :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  U.-integrable setT (EFin \o (fun z => g z * rho z : RR)).
Proof.
move=> mg gM.
have hsp : -1 <= s <= 7%:R / 3%:R := latent_param_range s 0 hs.
have hsn : -1 <= (- s)%R <= 7%:R / 3%:R := latent_param_range s 1 hs.
have ig (a : R) : -1 <= a <= 7%:R / 3%:R ->
    U.-integrable setT (fun x => (g x * latent_prod a d x)%:E).
  move=> ha.
  have gi : (latent_side mu d a).-integrable setT (EFin \o (g : _ -> RR)).
    exact: (integrable_prob_bounded' _ _ _ _ g M mg gM).
  by have [] := latent_side_integral mu d hmu a g ha mg gi.
have i1 := ig s hsp; have i2 := ig (- s)%R hsn.
apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT 2^-1
  (integrableD measurableT i1 i2))) => x _ /=.
by rewrite latent_densityE -EFinD -EFinM; congr EFin; ring.
Qed.

Let ZN x : Z x = N (fun=> 1) x.
Proof. by apply: eq_Rintegral => y _; rewrite mul1r. Qed.

Let mN (f : paper_main_sample 1 d -> R) (Mf : R) :
  measurable_fun setT (f : _ -> RR) -> (forall z, `|f z| <= Mf) ->
  measurable_fun setT (fun x => N f x).
Proof.
move=> mf fM.
have Fi := iU f Mf mf fM.
have mI := measurable_integral_tuple_set j' Fi.
have -> : (fun x => N f x) = (fun x => fine ((\int[mu]_t
    ((EFin \o (fun z => (f z * rho z)%R : RR)) (tuple_set x j' t)))%E)).
  by apply/funext => x; rewrite /N /Rintegral; congr fine.
exact: measurableT_comp (fine_measurable measurableT) mI.
Qed.

Lemma measurable_latent_cond (g : paper_main_sample 1 d -> R) (M : R) :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  measurable_fun setT (fun x => latent_cond_expectation s mu d j g x : RR) /\
  measurable_fun setT (fun x => latent_cond_variance s mu d j g x : RR).
Proof.
move=> mg gM.
have m1 : measurable_fun setT (fun _ : paper_main_sample 1 d => (1 : RR)).
  exact: measurable_cst.
have b1 (z : paper_main_sample 1 d) : `|(fun=> 1 : RR) z| <= 1 by rewrite normr1.
have mZ : measurable_fun setT (fun x => Z x).
  by have -> : (fun x => Z x) = (fun x => N (fun=> 1) x);
    [apply/funext => x; exact: ZN | exact: mN m1 b1].
have mCE (f : paper_main_sample 1 d -> R) (Mf : R) :
    measurable_fun setT (f : _ -> RR) -> (forall z, `|f z| <= Mf) ->
    measurable_fun setT (fun x => latent_cond_expectation s mu d j f x : RR).
  move=> mf fM; apply: measurable_funM; first exact: mN mf fM.
  exact: measurableT_comp measurable_inv mZ.
have mg2 : measurable_fun setT (fun z => g z ^+ 2 : RR) by exact: measurable_funX.
split; first exact: mCE mg gM.
apply: measurable_funB; first exact: mCE mg2 (sq_bound g M gM).
by apply: measurable_funX; exact: mCE mg gM.
Qed.

(* The conditional expectation does not depend on x_j. *)
Lemma latent_cond_expectation_replace (g : paper_main_sample 1 d -> R) x t :
  latent_cond_expectation s mu d j g (rep x t) =
  latent_cond_expectation s mu d j g x.
Proof.
rewrite /latent_cond_expectation; congr (_ / _);
  by apply: eq_Rintegral => y _; rewrite latent_replace_idem.
Qed.

(* E [E (g | X_-j)] = E g. *)
Lemma latent_tower (g : paper_main_sample 1 d -> R) (M : R) :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  latent_point_expectation s mu d (latent_cond_expectation s mu d j g) =
  latent_point_expectation s mu d g.
Proof.
move=> mg gM.
have [mC _] := measurable_latent_cond g M mg gM.
set C := latent_cond_expectation s mu d j g in mC *.
have mb := measurable_latent_box_ind d.
pose Cb x : R := C x * latent_box_ind d x.
have Cb_bound x : `|Cb x| <= `|M|.
  have [bx|nb] := pselect (latent_box d x).
    rewrite /Cb latent_box_ind1 // mulr1.
    exact: le_trans (latent_cond_expectation_bound g M x mg gM bx) (ler_norm M).
  by rewrite /Cb latent_box_ind0 // mulr0 normr0.
have mCb : measurable_fun setT (Cb : _ -> RR) by exact: measurable_funM.
have mCr : measurable_fun setT (fun x => (C x * rho x)%:E : \bar RR).
  by apply/measurable_EFinP; exact: measurable_funM.
have mCbr : measurable_fun setT (fun x => (Cb x * rho x)%:E : \bar RR).
  by apply/measurable_EFinP; exact: measurable_funM.
have e1 : latent_point_expectation s mu d C = latent_point_expectation s mu d Cb.
  rewrite /latent_point_expectation /Rintegral; congr fine.
  apply: ae_eq_integral => //.
  by apply: (latent_box_ae mu d hmu) => x hx /=; rewrite /Cb latent_box_ind1 // mulr1.
have iCb := iU Cb `|M| mCb Cb_bound.
have ig := iU g M mg gM.
rewrite e1 /latent_point_expectation /Rintegral.
rewrite (integral_tuple_prod_set j' iCb) (integral_tuple_prod_set j' ig).
congr fine; apply: ae_eq_integral => //.
- have mI1 := measurable_integral_tuple_set j' iCb.
  by apply: mI1.
- have mI2 := measurable_integral_tuple_set j' ig.
  by apply: mI2.
apply: (latent_box_ae mu d hmu) => x bx /=.
have Z0 : 0 < Z x := latent_cond_den_gt0 x bx.
have iNg := iN g M x mg gM.
transitivity ((N g x)%:E).
  transitivity (\int[mu]_t ((C x * rho (rep x t))%:E))%E.
    apply: ae_eq_integral => //.
    - apply/measurable_EFinP; apply: measurable_funM.
        apply: measurableT_comp mCb _; apply: (eq_measurable_fun (rep x)).
          by move=> t _; rewrite latent_replace_set.
        exact: mrep x.
      apply: measurableT_comp mrho _; apply: (eq_measurable_fun (rep x)).
        by move=> t _; rewrite latent_replace_set.
      exact: mrep x.
    - apply/measurable_EFinP; apply: measurable_funM; first exact: measurable_cst.
      exact: continuous_measurable_fun (crho x).
    apply: (sym_uniform_ae _ _ hP) => t tc /=.
    have eC : C (rep x t) = C x := latent_cond_expectation_replace g x t.
    rewrite -latent_replace_set /Cb eC.
    by rewrite latent_box_ind1 ?mulr1 //; exact: latent_box_replace.
  transitivity ((C x)%:E *
      \int[mu]_t ((EFin \o (fun y : RR => rho (rep x y) : RR)) t))%E.
    rewrite -(integralZl measurableT (irho x)).
    by apply: eq_integral => t _; rewrite /= EFinM.
  have fZ : (\int[mu]_t ((EFin \o (fun y : RR => rho (rep x y) : RR)) t))%E =
      (Z x)%:E.
    rewrite /Z /Rintegral fineK //.
    exact: (integrable_fin_num measurableT (irho x)).
  rewrite fZ -EFinM /C CEE divfK //; exact: lt0r_neq0.
have fN : (\int[mu]_t ((g (rep x t) * rho (rep x t) : RR)%:E))%E = (N g x)%:E.
  rewrite /N /Rintegral fineK //.
  exact: (integrable_fin_num measurableT iNg).
rewrite -fN.
by apply: eq_integral => t _; rewrite /= latent_replace_set.
Qed.

(* 5. Expectations of functions bounded on the box. *)

Lemma latent_expectation_box (u : paper_main_sample 1 d -> R) :
  measurable_fun setT (u : _ -> RR) ->
  latent_point_expectation s mu d u =
  latent_point_expectation s mu d (fun x => u x * latent_box_ind d x).
Proof.
move=> mu'.
have mb := measurable_latent_box_ind d.
rewrite /latent_point_expectation /Rintegral; congr fine.
apply: ae_eq_integral => //.
- by apply/measurable_EFinP; exact: measurable_funM.
- apply/measurable_EFinP; apply: measurable_funM => //.
  exact: measurable_funM.
by apply: (latent_box_ae mu d hmu) => x hx /=; rewrite latent_box_ind1 // mulr1.
Qed.

Lemma latent_expectation_le (u v : paper_main_sample 1 d -> R) (M : R) :
  measurable_fun setT (u : _ -> RR) -> measurable_fun setT (v : _ -> RR) ->
  (forall x, latent_box d x -> `|u x| <= M /\ `|v x| <= M) ->
  (forall x, latent_box d x -> u x <= v x) ->
  latent_point_expectation s mu d u <= latent_point_expectation s mu d v.
Proof.
move=> mu' mv hM huv.
have mb := measurable_latent_box_ind d.
rewrite (latent_expectation_box u mu') (latent_expectation_box v mv).
have bnd (w : paper_main_sample 1 d -> R) :
    (forall x, latent_box d x -> `|w x| <= M) ->
    forall x, `|w x * latent_box_ind d x| <= `|M|.
  move=> hw x; have [bx|nb] := pselect (latent_box d x).
    by rewrite latent_box_ind1 // mulr1; exact: le_trans (hw x bx) (ler_norm M).
  by rewrite latent_box_ind0 // mulr0 normr0.
have bu := bnd u (fun x bx => (hM x bx).1).
have bv := bnd v (fun x bx => (hM x bx).2).
have mub : measurable_fun setT (fun x => u x * latent_box_ind d x : RR).
  exact: measurable_funM.
have mvb : measurable_fun setT (fun x => v x * latent_box_ind d x : RR).
  exact: measurable_funM.
have iu (a : R) := integrable_prob_bounded' _ _ _ (latent_side mu d a) _ _ mub bu.
have iv (a : R) := integrable_prob_bounded' _ _ _ (latent_side mu d a) _ _ mvb bv.
rewrite (latent_point_expectationE s mu d hs hmu _ mub (iu s) (iu (- s)%R)).
rewrite (latent_point_expectationE s mu d hs hmu _ mvb (iv s) (iv (- s)%R)).
have le_w x : u x * latent_box_ind d x <= v x * latent_box_ind d x.
  have [bx|nb] := pselect (latent_box d x).
    by rewrite latent_box_ind1 // !mulr1; exact: huv.
  by rewrite latent_box_ind0 // !mulr0.
rewrite ler_pM2r ?invr_gt0 ?ltr0n //.
apply: lerD; (apply: le_Rintegral => //; [exact: iu | exact: iv]).
Qed.

Lemma latent_expectation_eq (u v : paper_main_sample 1 d -> R) :
  measurable_fun setT (u : _ -> RR) -> measurable_fun setT (v : _ -> RR) ->
  (forall x, latent_box d x -> u x = v x) ->
  latent_point_expectation s mu d u = latent_point_expectation s mu d v.
Proof.
move=> mu' mv e.
rewrite (latent_expectation_box u mu') (latent_expectation_box v mv).
congr (latent_point_expectation s mu d _); apply/funext => x.
have [bx|nb] := pselect (latent_box d x); first by rewrite e.
by rewrite latent_box_ind0 // !mulr0.
Qed.

Lemma latent_expectationZ (c : R) (u : paper_main_sample 1 d -> R) (M : R) :
  measurable_fun setT (u : _ -> RR) -> (forall z, `|u z| <= M) ->
  latent_point_expectation s mu d (fun x => c * u x) =
  c * latent_point_expectation s mu d u.
Proof.
move=> mu' uM; rewrite /latent_point_expectation.
under eq_Rintegral do rewrite -mulrA.
exact: (RintegralZl c measurableT (iU u M mu' uM)).
Qed.

Lemma latent_expectation0 :
  latent_point_expectation s mu d (fun=> 0) = 0.
Proof.
rewrite /latent_point_expectation; under eq_Rintegral do rewrite mul0r.
by rewrite Rintegral_cst // mul0r.
Qed.

(* 6. Linearity, and the identities behind finite tensorization constants. *)

Lemma latent_integrable (g : paper_main_sample 1 d -> R) (M : R) :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  U.-integrable setT (EFin \o (fun z => g z * rho z : RR)).
Proof. exact: iU. Qed.

Lemma latent_expectationD (u v : paper_main_sample 1 d -> R) (Mu Mv : R) :
  measurable_fun setT (u : _ -> RR) -> (forall z, `|u z| <= Mu) ->
  measurable_fun setT (v : _ -> RR) -> (forall z, `|v z| <= Mv) ->
  latent_point_expectation s mu d (fun x => u x + v x) =
  latent_point_expectation s mu d u + latent_point_expectation s mu d v.
Proof.
move=> mu' uM mv vM; rewrite /latent_point_expectation.
under eq_Rintegral do rewrite mulrDl.
exact: (RintegralD measurableT (iU u Mu mu' uM) (iU v Mv mv vM)).
Qed.

Lemma latent_expectation_cst (c : R) :
  latent_point_expectation s mu d (fun=> c) = c.
Proof.
have m1 : measurable_fun setT (fun _ : paper_main_sample 1 d => (1 : RR)).
  exact: measurable_cst.
have b1 (z : paper_main_sample 1 d) : `|(fun=> 1 : RR) z| <= 1 by rewrite normr1.
have -> : (fun _ : paper_main_sample 1 d => c) = (fun x => c * (fun=> 1) x).
  by apply/funext => x; rewrite mulr1.
rewrite (latent_expectationZ c _ 1 m1 b1).
have hsp : -1 <= s <= 7%:R / 3%:R := latent_param_range s 0 hs.
have hsn : -1 <= (- s)%R <= 7%:R / 3%:R := latent_param_range s 1 hs.
have i1 (a : R) : (latent_side mu d a).-integrable setT
    (EFin \o (fun _ : paper_main_sample 1 d => (1 : RR))).
  exact: finite_measure_integrable_cst.
rewrite (latent_point_expectationE s mu d hs hmu _ m1 (i1 s) (i1 (- s)%R)).
rewrite !Rintegral_cst //.
rewrite -[X in fine X]/(latent_side mu d s setT) probability_setT /=.
rewrite -[X in fine X]/(latent_side mu d (- s)%R setT) probability_setT /=.
by rewrite !mulr1 -[X in _ / X]/(1 + 1) divff ?mulr1 // pnatr_eq0.
Qed.

(* For g that does not depend on x_j, E_P g = int g Z dU. *)
Lemma latent_expectation_indep (g : paper_main_sample 1 d -> R) (M : R) :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  (forall x t, g (rep x t) = g x) ->
  latent_point_expectation s mu d g = \int[U]_x (g x * Z x : RR).
Proof.
move=> mg gM hg.
have ig := iU g M mg gM.
rewrite /latent_point_expectation /Rintegral (integral_tuple_prod_set j' ig).
congr fine; apply: eq_integral => x _.
transitivity (\int[mu]_t ((g x)%:E * (rho (rep x t) : RR)%:E))%E.
  by apply: eq_integral => t _; rewrite /= -latent_replace_set hg EFinM.
rewrite (integralZl measurableT (irho x)).
have fZ : (\int[mu]_t ((EFin \o (fun y : RR => rho (rep x y) : RR)) t))%E =
    (Z x)%:E.
  rewrite /Z /Rintegral fineK //.
  exact: (integrable_fin_num measurableT (irho x)).
by rewrite fZ -EFinM.
Qed.

(* Z Var (g | X_-j) = int (g - E (g | X_-j))^2 rho, on the box. *)
Lemma latent_cond_variance_mul (g : paper_main_sample 1 d -> R) (M : R) x :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  latent_box d x ->
  latent_cond_variance s mu d j g x * Z x =
  \int[mu]_y ((g (rep x y) - latent_cond_expectation s mu d j g x) ^+ 2 *
               rho (rep x y) : RR).
Proof.
move=> mg gM bx.
have Z0 : 0 < Z x := latent_cond_den_gt0 x bx.
have Zn : Z x != 0 := lt0r_neq0 Z0.
have em : latent_cond_expectation s mu d j g x = N g x / Z x by [].
set m := N g x / Z x in em.
have [_ e2] := N_shift g (fun=> - m) M `|m| x mg gM (fun=> erefl).
have e : latent_cond_variance s mu d j g x = N (fun z => (g z - m) ^+ 2) x / Z x.
  rewrite /latent_cond_variance !CEE e2.
  have em' : N g x = m * Z x by rewrite /m divfK.
  exact: (var_identity _ _ _ _ Zn em').
by rewrite e divfK // em.
Qed.

Lemma measurable_latent_cond_den :
  measurable_fun setT (fun x => \int[mu]_y (rho (rep x y) : RR)).
Proof.
have m1 : measurable_fun setT (fun _ : paper_main_sample 1 d => (1 : RR)).
  exact: measurable_cst.
have b1 (z : paper_main_sample 1 d) : `|(fun=> 1 : RR) z| <= 1 by rewrite normr1.
have -> : (fun x => \int[mu]_y (rho (rep x y) : RR)) = (fun x => N (fun=> 1) x).
  by apply/funext => x; exact: ZN.
exact: mN m1 b1.
Qed.

Lemma measurable_latent_replace (y : RR) :
  measurable_fun setT (fun x : paper_main_sample 1 d => rep x y).
Proof.
apply/measurable_fun_tnthP => k.
apply: (eq_measurable_fun (fun x : paper_main_sample 1 d =>
  if k == j' then y else tnth x k)).
  by move=> x _; rewrite /= tnth_latent_replace.
by case: (k == j'); [exact: measurable_cst | exact: measurable_tnth].
Qed.

Lemma latent_cond_den_le (w : R) x :
  (forall y, `|y| <= Num.sqrt 3%:R -> rho (rep x y) <= w) ->
  \int[mu]_y (rho (rep x y) : RR) <= w.
Proof.
move=> hw.
have iw : mu.-integrable setT (EFin \o (fun _ : RR => w : RR)).
  exact: finite_measure_integrable_cst.
have := Rint_le _ _ (irho x) iw hw.
by rewrite Rintegral_cst // -[X in fine X]/(mu setT) probability_setT /= mulr1.
Qed.

(* w Var_mu (g (x with x_j := .)) <= Z Var (g | X_-j) when w <= rho on the
   support. *)
Lemma latent_cond_variance_weight (g : paper_main_sample 1 d -> R) (M w : R) x :
  measurable_fun setT (g : _ -> RR) -> (forall z, `|g z| <= M) ->
  latent_box d x -> 0 <= w ->
  (forall y, `|y| <= Num.sqrt 3%:R -> w <= rho (rep x y)) ->
  w * (\int[mu]_y (g (rep x y) ^+ 2 : RR) - (\int[mu]_y (g (rep x y) : RR)) ^+ 2) <=
  latent_cond_variance s mu d j g x * Z x.
Proof.
move=> mg gM bx w0 hw.
rewrite (latent_cond_variance_mul g M x mg gM bx).
set m := latent_cond_expectation s mu d j g x.
have mG : measurable_fun setT (fun y : RR => g (rep x y) : RR).
  exact: measurableT_comp mg (mrep x).
have M0 : 0 <= M := bound_ge0 g M x gM.
have iG : mu.-integrable setT (EFin \o (fun y : RR => g (rep x y) : RR)).
  exact: (integrable_prob_bounded' _ _ _ mu _ M mG (fun y => gM _)).
have mG2 : measurable_fun setT (fun y : RR => g (rep x y) ^+ 2 : RR).
  exact: measurable_funX.
have iG2 : mu.-integrable setT (EFin \o (fun y : RR => g (rep x y) ^+ 2 : RR)).
  exact: (integrable_prob_bounded' _ _ _ mu _ (M ^+ 2) mG2
    (fun y => sq_bound g M gM _)).
have gmM z : `|g z - m| <= M + `|m|.
  by apply: le_trans (ler_normB _ _) _; rewrite lerD2r.
have mGm : measurable_fun setT (fun y : RR => (g (rep x y) - m) ^+ 2 : RR).
  by apply: measurable_funX; apply: measurable_funB => //; exact: measurable_cst.
have iGm : mu.-integrable setT (EFin \o (fun y : RR => (g (rep x y) - m) ^+ 2 : RR)).
  exact: (integrable_prob_bounded' _ _ _ mu _ ((M + `|m|) ^+ 2) mGm
    (fun y => sq_bound (fun z => g z - m) _ gmM _)).
have mgm : measurable_fun setT (fun z => (g z - m) ^+ 2 : RR).
  by apply: measurable_funX; apply: measurable_funB => //; exact: measurable_cst.
have iGmr := iN (fun z => (g z - m) ^+ 2) _ x mgm (sq_bound _ _ gmM).
have iwGm : mu.-integrable setT
    (EFin \o (fun y : RR => w * (g (rep x y) - m) ^+ 2 : RR)).
  apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT w iGm)).
  by move=> y _ /=; rewrite EFinM.
(* w int (G - m)^2 <= int (G - m)^2 rho *)
have s1 : w * \int[mu]_y ((g (rep x y) - m) ^+ 2 : RR) <=
    \int[mu]_y ((g (rep x y) - m) ^+ 2 * rho (rep x y) : RR).
  rewrite -(RintegralZl w measurableT iGm); apply: Rint_le => // y yc.
  by rewrite mulrC; apply: ler_wpM2l; [exact: sqr_ge0 | exact: hw].
(* int G^2 - (int G)^2 <= int (G - m)^2 *)
have i3 : mu.-integrable setT (EFin \o (fun y : RR =>
    g (rep x y) ^+ 2 + (- (2%:R * m)) * g (rep x y) : RR)).
  have iZG : mu.-integrable setT
      (EFin \o (fun y : RR => (- (2%:R * m)) * g (rep x y) : RR)).
    apply: (eq_integrable measurableT _ _ _
      (integrableZl measurableT (- (2%:R * m)) iG)).
    by move=> y _ /=; rewrite EFinM.
  apply: (eq_integrable measurableT _ _ _ (integrableD measurableT iG2 iZG)).
  by move=> y _ /=; rewrite EFinD.
have ic : mu.-integrable setT (EFin \o (fun _ : RR => m ^+ 2 : RR)).
  exact: finite_measure_integrable_cst.
have e : \int[mu]_y ((g (rep x y) - m) ^+ 2 : RR) =
    \int[mu]_y (g (rep x y) ^+ 2 : RR) -
    2%:R * m * \int[mu]_y (g (rep x y) : RR) + m ^+ 2.
  transitivity (\int[mu]_y (g (rep x y) ^+ 2 + (- (2%:R * m)) * g (rep x y) +
      m ^+ 2 : RR)).
    by apply: eq_Rintegral => y _; ring.
  have iZG : mu.-integrable setT
      (EFin \o (fun y : RR => (- (2%:R * m)) * g (rep x y) : RR)).
    apply: (eq_integrable measurableT _ _ _
      (integrableZl measurableT (- (2%:R * m)) iG)).
    by move=> y _ /=; rewrite EFinM.
  rewrite (RintegralD measurableT i3 ic) (RintegralD measurableT iG2 iZG).
  rewrite (RintegralZl _ measurableT iG) Rintegral_cst //.
  rewrite -[X in fine X]/(mu setT) probability_setT /=.
  by rewrite mulr1 mulNr.
have s2 : \int[mu]_y (g (rep x y) ^+ 2 : RR) -
    (\int[mu]_y (g (rep x y) : RR)) ^+ 2 <=
    \int[mu]_y ((g (rep x y) - m) ^+ 2 : RR).
  by rewrite e; exact: sqr_dev_bound.
apply: (le_trans _ s1); exact: (ler_wpM2l w0 s2).
Qed.

End latent_cond.
