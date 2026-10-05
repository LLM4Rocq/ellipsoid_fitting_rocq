(* Weighted centered Gaussian squares. For arbitrary real coefficients a_i
   (of any sign) on d coordinates,
     Q d a xs = sum_(i < d) a_i * (x_i ^ 2 - 1),  x_i = nth i xs 0.
   - Scalar factor: for t a < 1/2,
     E exp(t a (x^2 - 1)) = exp(-t a) / sqrt(1 - 2 t a)
     (gaussian_quadratic_exponential_moment).
   - Exact finite product: if every 1 - 2 t a_i > 0, then exp(t Q) is
     iterated-integrable and absolutely integrable, and
     E_d exp(t Q) = prod_(i < d) exp(-t a_i) / sqrt(1 - 2 t a_i)
     (gaussian_separable_product_integral; no independence is assumed).
   - Scalar inequality: -ln(1-u) - u <= u^2/(2(1-|u|)) for |u| < 1. The
     positive side is gaussian_log_remainder_bound; the negative side
     follows from ln(1+w) >= w - w^2/2 for w >= 0, proved here from the
     sign of a derivative.
   - MGF bound: with v = sum_(i < d) a_i^2, |a_i| <= L and 2|t| L < 1,
     E_d exp(t Q) <= exp(t^2 v / (1 - 2|t| L)), and the log form. The
     case d = 0 and zero coefficients are included.
   Rpower.ln is written explicitly: MathComp's exp module is imported. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive realfun exp Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums GaussianDefinitions
  GaussianKernel GaussianMass GaussianExpectation GaussianQuadraticMGF
  GaussianProductDefinitions GaussianProduct RadiusAlgebra.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_weighted_square d (a : nat -> R) (xs : list R) : R :=
  finite_sum (fun i => a i * (List.nth i xs 0 ^ 2 - 1)) (List.seq 0 d).

Fixpoint paper_main_weighted_square_factors d t (a : nat -> R) : list (R -> R) :=
  match d with
  | O => nil
  | S k => (fun x => exp (t * (a 0%nat * (x ^ 2 - 1)))) ::
      paper_main_weighted_square_factors k t (fun i => a (S i))
  end.

Fixpoint paper_main_weighted_square_product d t (a : nat -> R) : R :=
  match d with
  | O => 1
  | S k => exp (- t * a 0%nat) / sqrt (1 - 2 * t * a 0%nat) *
      paper_main_weighted_square_product k t (fun i => a (S i))
  end.

Lemma paper_main_weighted_square_cons k (a : nat -> R) x xs :
  paper_main_weighted_square (S k) a (x :: xs) =
  a 0%nat * (x ^ 2 - 1) + paper_main_weighted_square k (fun i => a (S i)) xs.
Proof.
rewrite /paper_main_weighted_square.
change (List.seq 0 (S k)) with (0%nat :: List.seq 1 k).
rewrite /= (finite_sum_seq_shift _ 1 k).
reflexivity.
Qed.

Lemma paper_main_weighted_square_sum_cons k (a : nat -> R) :
  finite_sum (fun i => a i ^ 2) (List.seq 0 (S k)) =
  a 0%nat ^ 2 + finite_sum (fun i => a (S i) ^ 2) (List.seq 0 k).
Proof.
change (List.seq 0 (S k)) with (0%nat :: List.seq 1 k).
rewrite /= (finite_sum_seq_shift _ 1 k).
reflexivity.
Qed.

(* The scalar factor. *)
Lemma paper_main_weighted_square_scalar t a :
  t * a < 1/2 ->
  gaussian_integral_exists (fun x => exp (t * (a * (x ^ 2 - 1)))) /\
  gaussian_absolutely_integrable (fun x => exp (t * (a * (x ^ 2 - 1)))) /\
  gaussian_expectation (fun x => exp (t * (a * (x ^ 2 - 1)))) =
    exp (- t * a) / sqrt (1 - 2 * t * a).
Proof.
move=> Hta.
have Hh := gaussian_quadratic_exponential_has_integral (t * a) Hta.
have Hh2 : gaussian_has_integral (fun x => exp (t * (a * (x ^ 2 - 1))))
    (exp (- t * a) * (gaussian_mass / sqrt (1 - 2 * (t * a)))).
  have -> : (fun x => exp (t * (a * (x ^ 2 - 1)))) =
      (fun x => exp (- t * a) * exp (t * a * (x * x))).
    by apply: functional_extensionality => x; rewrite -exp_plus; congr exp; ring.
  exact: (gaussian_has_integral_scale _ _ (exp (- t * a)) Hh).
have Hex := gaussian_has_integral_exists _ _ Hh2.
split; first exact: Hex.
split.
  rewrite /gaussian_absolutely_integrable.
  have -> : (fun x => Rabs (exp (t * (a * (x ^ 2 - 1))))) =
      (fun x => exp (t * (a * (x ^ 2 - 1)))).
    by apply: functional_extensionality => x; apply: Rabs_pos_eq; apply: Rlt_le; apply: exp_pos.
  exact: Hex.
rewrite /gaussian_expectation (gaussian_integral_unique _ _ Hh2).
have Hm := gaussian_mass_positive.
have Hs : 0 < sqrt (1 - 2 * (t * a)) by apply sqrt_lt_R0; lra.
replace (1 - 2 * t * a) with (1 - 2 * (t * a)) by ring.
by field; lra.
Qed.

(* The exact finite product. *)

Lemma paper_main_weighted_square_factors_length d t a :
  length (paper_main_weighted_square_factors d t a) = d.
Proof.
revert a; induction d as [|d IH]; intros a; [reflexivity|].
by simpl; rewrite IH.
Qed.

Lemma paper_main_weighted_square_separable d t (a : nat -> R) xs :
  length xs = d ->
  exp (t * paper_main_weighted_square d a xs) =
    gaussian_separable_product (paper_main_weighted_square_factors d t a) xs.
Proof.
revert a xs; induction d as [|d IH]; intros a [|x xs] Hxs; simpl in Hxs; try discriminate.
- by rewrite /paper_main_weighted_square /= Rmult_0_r exp_0.
- rewrite paper_main_weighted_square_cons.
  change (gaussian_separable_product (paper_main_weighted_square_factors (S d) t a) (x :: xs))
    with (exp (t * (a 0%nat * (x ^ 2 - 1))) *
      gaussian_separable_product (paper_main_weighted_square_factors d t (fun i => a (S i))) xs).
  rewrite -(IH (fun i => a (S i)) xs ltac:(lia)).
  by rewrite -exp_plus; congr exp; ring.
Qed.

Lemma paper_main_weighted_square_factors_domain d t (a : nat -> R) :
  (forall i, (i < d)%coq_nat -> 0 < 1 - 2 * t * a i) ->
  List.Forall gaussian_integral_exists (paper_main_weighted_square_factors d t a) /\
  List.Forall gaussian_absolutely_integrable (paper_main_weighted_square_factors d t a) /\
  gaussian_product_expectations (paper_main_weighted_square_factors d t a) =
    paper_main_weighted_square_product d t a.
Proof.
revert a; induction d as [|d IH]; intros a Ha.
  by split; [constructor | split; [constructor | reflexivity]].
have Ha0 : t * a 0%nat < 1/2 by have := Ha 0%nat ltac:(lia); lra.
have [Hi [Habs He]] := paper_main_weighted_square_scalar t (a 0%nat) Ha0.
have [IH1 [IH2 IH3]] := IH (fun i => a (S i)) (fun i Hi => Ha (S i) ltac:(lia)).
split; first by constructor.
split; first by constructor.
by rewrite /= He IH3.
Qed.

Theorem paper_main_weighted_square_mgf d t (a : nat -> R) :
  (forall i, (i < d)%coq_nat -> 0 < 1 - 2 * t * a i) ->
  gaussian_iterated_integrable d (fun xs => exp (t * paper_main_weighted_square d a xs)) /\
  gaussian_iterated_absolutely_integrable d
    (fun xs => exp (t * paper_main_weighted_square d a xs)) /\
  gaussian_iterated_expectation d (fun xs => exp (t * paper_main_weighted_square d a xs)) =
    paper_main_weighted_square_product d t a.
Proof.
move=> Ha.
have [Hf [Habs HE]] := paper_main_weighted_square_factors_domain d t a Ha.
have [HI [HA [_ HEq]]] := gaussian_separable_product_integral _ Hf Habs.
rewrite paper_main_weighted_square_factors_length in HI HA HEq.
have Hext : forall xs, length xs = d ->
    gaussian_separable_product (paper_main_weighted_square_factors d t a) xs =
    exp (t * paper_main_weighted_square d a xs).
  by move=> xs Hxs; rewrite (paper_main_weighted_square_separable d t a xs Hxs).
split; first exact: (gaussian_iterated_integrable_ext d _ _ Hext HI).
split.
  rewrite /gaussian_iterated_absolutely_integrable in HA *.
  apply: (gaussian_iterated_integrable_ext d _ _ _ HA) => xs Hxs.
  by rewrite Hext.
by rewrite -(gaussian_iterated_expectation_ext d _ _ Hext) HEq HE.
Qed.

Lemma paper_main_weighted_square_product_pos d t (a : nat -> R) :
  (forall i, (i < d)%coq_nat -> 0 < 1 - 2 * t * a i) ->
  0 < paper_main_weighted_square_product d t a.
Proof.
revert a; induction d as [|d IH]; intros a Ha; first by simpl; lra.
simpl; apply: Rmult_lt_0_compat.
  apply: Rdiv_lt_0_compat; first exact: exp_pos.
  by apply: sqrt_lt_R0; exact: (Ha 0%nat ltac:(lia)).
exact: (IH (fun i => a (S i)) (fun i Hi => Ha (S i) ltac:(lia))).
Qed.

(* The scalar logarithmic inequality. *)

Lemma paper_main_weighted_square_log_lower_derivative v :
  -1 < v ->
  @is_derive R R^o R^o v 1 (fun w => Rpower.ln (1 + w) - w + w * w / 2) (v * v / (1 + v)).
Proof.
move=> Hv.
pose g1 := fun w : R => - w + w * w / 2.
pose g2 := fun w : R => 1 + w.
have H2 : derivable_pt_lim g2 v (0 + 1).
  apply: (derivable_pt_lim_plus (fun _ => 1) id);
    [exact: derivable_pt_lim_const | exact: derivable_pt_lim_id].
have H1 : derivable_pt_lim g1 v (- 1 + (1 * v + v * 1) / 2).
  apply: (derivable_pt_lim_plus (fun w => - w) (fun w => w * w / 2)).
    exact: (derivable_pt_lim_opp id v 1 (derivable_pt_lim_id v)).
  have Hm : derivable_pt_lim (fun w => w * w) v (1 * v + v * 1).
    by apply: (derivable_pt_lim_mult id id); exact: derivable_pt_lim_id.
  have Hs := derivable_pt_lim_scal (fun w => w * w) (/ 2) v _ Hm.
  have -> : (fun w => w * w / 2) = mult_real_fct (/ 2) (fun w => w * w).
    by apply: functional_extensionality => w; rewrite /mult_real_fct; field.
  by have -> : (1 * v + v * 1) / 2 = / 2 * (1 * v + v * 1) by field.
have D1 := RadiusAlgebra_is_derive_of_Reals H1.
have D2 := RadiusAlgebra_is_derive_of_Reals H2.
have Hpos : (0 < g2 v)%R.
  by apply/RltP; rewrite /g2 /=; change (0 < 1 + v); lra.
have D3 := is_derive1_comp (@is_derive1_ln R (g2 v) Hpos) D2.
have D := is_deriveD D3 D1.
have -> : (fun w => Rpower.ln (1 + w) - w + w * w / 2) = (((@exp.ln R) \o g2) + g1)%R.
  apply: funext => w; rewrite /g1 /g2 /=.
  change (Rpower.ln (1 + w) - w + w * w / 2 = @exp.ln R (Rplus 1 w) + (- w + w * w / 2)).
  by rewrite -RlnE; lra.
apply: is_derive_eq D _.
rewrite /g2 /=.
change (/ (1 + v) * (0 + 1) + (- 1 + (1 * v + v * 1) / 2) = v * v / (1 + v)).
by field; lra.
Qed.

Lemma paper_main_weighted_square_log_lower w :
  0 <= w -> w - w * w / 2 <= Rpower.ln (1 + w).
Proof.
move=> Hw.
pose f := fun v => Rpower.ln (1 + v) - v + v * v / 2.
have Df x : -1 < x -> @is_derive R R^o R^o x 1 f (x * x / (1 + x)).
  exact: paper_main_weighted_square_log_lower_derivative.
have key : f 0 <= f w.
  apply/RleP; apply: (@ger0_derive1_ndecr R f 0 w).
  - move=> x; rewrite in_itv /= => /andP [x0 _].
    have x0' : 0 < x by apply/RltP.
    by have [Hd _] := Df x ltac:(lra).
  - move=> x; rewrite in_itv /= => /andP [x0 _].
    have x0' : 0 < x by apply/RltP.
    have [_ Hv] := Df x ltac:(lra).
    rewrite derive1E Hv; apply/RleP.
    have Hx : 0 < 1 + x by lra.
    unfold Rdiv; apply: Rmult_le_pos; first nra.
    by apply/Rlt_le/Rinv_0_lt_compat.
  - apply: continuous_in_subspaceT => x /[1!inE].
    rewrite /= in_itv /= => /andP [x0 _].
    have x0' : 0 <= x by apply/RleP.
    have [Hd _] := Df x ltac:(lra).
    have Hc := differentiable_continuous (iffLR (derivable1_diffP _ _) Hd).
    exact Hc.
  - exact/RleP/Rle_refl.
  - by apply/RleP.
  - exact/RleP/Rle_refl.
move: key; rewrite /f Rplus_0_r ln_1.
by lra.
Qed.

Lemma paper_main_weighted_square_log_bound u :
  Rabs u < 1 -> - Rpower.ln (1 - u) - u <= u * u / (2 * (1 - Rabs u)).
Proof.
move=> Hu.
case: (Rle_lt_dec 0 u) => Hs.
  rewrite (Rabs_pos_eq u Hs) in Hu *.
  by apply: gaussian_log_remainder_bound; split.
rewrite (Rabs_left u Hs) in Hu *.
have Hw := paper_main_weighted_square_log_lower (- u) ltac:(lra).
have -> : 1 - u = 1 + - u by ring.
have Hp : 0 < 1 + u by lra.
apply: (Rle_trans _ (u * u / 2)); first lra.
apply: (Rmult_le_reg_r (2 * (1 - - u))); first lra.
have -> : u * u / (2 * (1 - - u)) * (2 * (1 - - u)) = u * u by field; lra.
have -> : u * u / 2 * (2 * (1 - - u)) = u * u * (1 + u) by field.
by nra.
Qed.

(* The factor bound and the MGF bound. *)

Lemma paper_main_weighted_square_sqrt_exp y :
  0 < y -> sqrt y = exp (Rpower.ln y / 2).
Proof.
move=> Hy.
have Hsq : exp (Rpower.ln y / 2) * exp (Rpower.ln y / 2) = y.
  by rewrite -exp_plus; replace (Rpower.ln y / 2 + Rpower.ln y / 2) with (Rpower.ln y)
    by field; exact: exp_ln.
rewrite -{1}Hsq; apply: sqrt_square; apply: Rlt_le; exact: exp_pos.
Qed.

Lemma paper_main_weighted_square_factor_bound t a L :
  Rabs a <= L -> 2 * Rabs t * L < 1 ->
  exp (- t * a) / sqrt (1 - 2 * t * a) <=
    exp (t * t * (a * a) / (1 - 2 * Rabs t * L)).
Proof.
move=> HaL HtL.
have Hta := Rabs_pos t.
have Hu : Rabs (2 * t * a) <= 2 * Rabs t * L.
  rewrite !Rabs_mult (Rabs_pos_eq 2 ltac:(lra)).
  by apply: Rmult_le_compat_l; [nra | exact HaL].
have Hu1 : Rabs (2 * t * a) < 1 by lra.
have Hpos : 0 < 1 - 2 * t * a by have := Rle_abs (2 * t * a); lra.
have Hden : 0 < 1 - 2 * Rabs t * L by lra.
have Hden' : 1 - 2 * Rabs t * L <= 1 - Rabs (2 * t * a) by lra.
have Hlog := paper_main_weighted_square_log_bound (2 * t * a) Hu1.
have Hf : exp (- t * a) / sqrt (1 - 2 * t * a) =
    exp ((- Rpower.ln (1 - 2 * t * a) - 2 * t * a) / 2).
  rewrite (paper_main_weighted_square_sqrt_exp _ Hpos).
  rewrite /Rdiv -exp_Ropp -exp_plus; congr exp; field.
rewrite Hf.
have Hinv : / (1 - Rabs (2 * t * a)) <= / (1 - 2 * Rabs t * L).
  by apply: Rinv_le_contravar.
have Hsq : 0 <= (2 * t * a) * (2 * t * a) by nra.
have Hb : (2 * t * a) * (2 * t * a) / (2 * (1 - Rabs (2 * t * a))) <=
    (2 * t * a) * (2 * t * a) / (2 * (1 - 2 * Rabs t * L)).
  rewrite /Rdiv !Rinv_mult; apply: Rmult_le_compat_l; first nra.
  by apply: Rmult_le_compat_l; [lra | exact Hinv].
have He : (2 * t * a) * (2 * t * a) / (2 * (1 - 2 * Rabs t * L)) / 2 =
    t * t * (a * a) / (1 - 2 * Rabs t * L) by field; lra.
have Hexp : (- Rpower.ln (1 - 2 * t * a) - 2 * t * a) / 2 <=
    t * t * (a * a) / (1 - 2 * Rabs t * L).
  rewrite -He; apply: Rmult_le_compat_r; first lra.
  exact: (Rle_trans _ _ _ Hlog Hb).
case: (Rle_lt_or_eq_dec _ _ Hexp) => [Hlt | Heq]; last by rewrite Heq; right.
by left; apply: exp_increasing.
Qed.

Theorem paper_main_weighted_square_product_bound d t (a : nat -> R) L :
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 2 * Rabs t * L < 1 ->
  paper_main_weighted_square_product d t a <=
    exp (t * t * finite_sum (fun i => a i ^ 2) (List.seq 0 d) / (1 - 2 * Rabs t * L)).
Proof.
revert a; induction d as [|d IH]; intros a Ha HtL.
  rewrite /= Rmult_0_r /Rdiv Rmult_0_l exp_0; lra.
have Hden : 0 < 1 - 2 * Rabs t * L by lra.
have Hpos : forall i, (i < S d)%coq_nat -> 0 < 1 - 2 * t * a i.
  move=> i Hi; have HaL := Ha i Hi.
  have Hta := Rabs_pos t.
  have Hu : Rabs (2 * t * a i) <= 2 * Rabs t * L.
    rewrite !Rabs_mult (Rabs_pos_eq 2 ltac:(lra)).
    by apply: Rmult_le_compat_l; [nra | exact HaL].
  by have := Rle_abs (2 * t * a i); lra.
have H0 := paper_main_weighted_square_factor_bound t (a 0%nat) L (Ha 0%nat ltac:(lia)) HtL.
have IH' := IH (fun i => a (S i)) (fun i Hi => Ha (S i) ltac:(lia)) HtL.
have Hf0 : 0 <= exp (- t * a 0%nat) / sqrt (1 - 2 * t * a 0%nat).
  apply: Rlt_le; apply: Rdiv_lt_0_compat; first exact: exp_pos.
  by apply: sqrt_lt_R0; exact: (Hpos 0%nat ltac:(lia)).
have Hp : 0 <= paper_main_weighted_square_product d t (fun i => a (S i)).
  apply: Rlt_le; apply: paper_main_weighted_square_product_pos => i Hi.
  exact: (Hpos (S i) ltac:(lia)).
rewrite paper_main_weighted_square_sum_cons.
change (paper_main_weighted_square_product (S d) t a) with
  (exp (- t * a 0%nat) / sqrt (1 - 2 * t * a 0%nat) *
    paper_main_weighted_square_product d t (fun i => a (S i))).
apply: (Rle_trans _ _ _ (Rmult_le_compat _ _ _ _ Hf0 Hp H0 IH')).
rewrite -exp_plus; right; congr exp.
by field; lra.
Qed.

Theorem paper_main_weighted_square_mgf_bound d (a : nat -> R) L t :
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 2 * Rabs t * L < 1 ->
  gaussian_iterated_expectation d (fun xs => exp (t * paper_main_weighted_square d a xs)) <=
    exp (t * t * finite_sum (fun i => a i ^ 2) (List.seq 0 d) / (1 - 2 * Rabs t * L)).
Proof.
move=> Ha HtL.
have Hpos : forall i, (i < d)%coq_nat -> 0 < 1 - 2 * t * a i.
  move=> i Hi; have HaL := Ha i Hi.
  have Hta := Rabs_pos t.
  have Hu : Rabs (2 * t * a i) <= 2 * Rabs t * L.
    rewrite !Rabs_mult (Rabs_pos_eq 2 ltac:(lra)).
    by apply: Rmult_le_compat_l; [nra | exact HaL].
  by have := Rle_abs (2 * t * a i); lra.
have [_ [_ HE]] := paper_main_weighted_square_mgf d t a Hpos.
rewrite HE; exact: paper_main_weighted_square_product_bound.
Qed.
