(* Parameter integrals over the real line, for the ports of the Gaussian
   modules that integrate a jointly continuous function of two variables
   against the Gaussian kernel: GaussianSections, GaussianRectangle,
   GaussianFubini, GaussianParameterBounds and the GaussianMixed modules.
   This is a helper module of the port of theories/ from Coquelicot to
   MathComp-Analysis. It has no counterpart in theories/: the original
   modules took these facts from Coquelicot (RInt_gen, is_RInt_gen and the
   improper integral lemmas of ImproperBounds, ImproperCutoff and
   ImproperDomination) or proved them in place. Every integral here is the
   Lebesgue integral of AnalysisIntegralDefinitions: whole_line_integral,
   whole_line_integrable, oriented_integral and segment_integrable, with
   Stdlib's operations on R in every statement.

   Contents.
   - Slices and products of jointly continuous functions: fubini_slice_left,
     fubini_slice_right (continuity of the sections), fubini_abs_2d (joint
     continuity of the absolute value), fubini_joint_continuous_left and
     fubini_joint_continuous_right (a function of one variable seen as a
     function of two), fubini_mult_1d_2d and fubini_mult_2d_1d (product with
     a continuous weight in one variable).
   - continuous_bounded_segment: a continuous function is bounded on a
     segment.
   - Integrability tools on a measurable set D of R, with the Lebesgue
     integral of MathComp: fubini_continuous_measurable,
     fubini_integrable_scale, fubini_integrable_scale_r, fubini_integrable_abs,
     fubini_integrable_norm, fubini_dominated_integrable (a measurable
     function dominated by c times an integrable function is integrable),
     fubini_Rintegral_bound and fubini_Rintegral_abs_le (bounds on the
     integral), fubini_segment_le_whole_line (the integral of a nonnegative
     integrable function over a measurable set is at most its integral over
     the line), fubini_integral_scale_l and fubini_integral_scale_r (the
     integral of a scaled function).
   - fubini_cutoff_cvg: for f integrable on the line, the integral of f over
     [-n, n] tends to the integral of f over the line as n tends to infinity
     through the natural numbers. Proved by dominated convergence.
   - whole_line_parameter_continuous: continuity in x of
     whole_line_integral (F x) when F is jointly continuous and dominated by
     g x * h y with g continuous and h integrable and nonnegative. Proved with
     MathComp's continuity_under_integral on the interval ]x - 1, x + 1[,
     with the dominating function (bound of g on [x - 1, x + 1]) * h.
     whole_line_parameter_continuous_weighted is the same for the integrand
     F x y * w y with a nonnegative continuous weight w, under
     whole_line_integrable (fun y => h y * w y).
   - whole_line_parameter_derivative: derivative in the parameter of
     whole_line_integral (F t) at a, when F is differentiable in t with
     derivative D t x on the band Rabs (t - a) <= rho, the slices F t are
     integrable there and D is dominated on the band by an integrable
     nonnegative G. It concludes whole_line_integrable (D a) and the
     derivative whole_line_integral (D a). Proved with MathComp's
     derivable_under_integral and differentiation_under_integral on the
     interval ]a - rho, a + rho[; the measurability of D a comes from the
     difference quotients along the sequence a + rho / 2 * harmonic n.
   - Fubini on the line: whole_line_fubini_inner_integrable,
     whole_line_fubini_inner_bound, whole_line_fubini_outer_integrable,
     fubini_iterated_cutoff_cvg and whole_line_fubini, for a jointly
     continuous F with Rabs (F x y) <= g x * h y, g and h continuous,
     nonnegative and integrable on the line: the two iterated integrals of F
     over the line are equal, and the outer integrands are integrable. The
     proof follows theories/GaussianFubini.v: Fubini on the squares [-n, n]^2
     (continuous_rectangle_fubini of RectangleFubini), then the limit n to
     infinity of both iterated integrals by dominated convergence, and the
     uniqueness of limits. whole_line_fubini_weighted is the form with a
     nonnegative continuous weight w on each variable, under
     whole_line_integrable (fun x => g x * w x) and
     whole_line_integrable (fun y => h y * w y); with w the Gaussian kernel it
     gives the exchange of two Gaussian integrals.

   Conventions. Measurability of f : R -> R is stated
   measurable_fun (setT : set (measurableTypeR R))
     (f : measurableTypeR R -> measurableTypeR R).
   The bounds of an interval `[a, b] are parsed in MathComp's ring scope, so
   the interval `[- INR n, INR n] carries MathComp's opposite; it is
   convertible with Stdlib's, and the lemmas on it are used through exact and
   apply, which work up to conversion. The header omits Import ListNotations:
   with it, the open interval `]l, r[ does not parse, because the token [
   after r starts a list. The module imports measurable_realfun for
   continuous_measurable_fun, measurable_EFinP, measurable_funM,
   measurable_funB and measurable_fun_cvg, which the bridge header does not
   reach. The scope classical_set_scope is opened locally for the notations
   \oo, @, --> and the set intervals. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import RectangleFubini.
From mathcomp Require Import measurable_realfun.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* Slices and products of jointly continuous functions. *)

Lemma fubini_slice_left (F : R -> R -> R) x :
  (forall u v, continuity_2d_pt F u v) -> continuous (F x).
Proof. move=> H y; exact: (rectangle_continuous_slice_right F x y (H x y)). Qed.

Lemma fubini_slice_right (F : R -> R -> R) y :
  (forall u v, continuity_2d_pt F u v) -> continuous (fun x => F x y).
Proof. move=> H x; exact: (rectangle_continuous_slice_left F x y (H x y)). Qed.

Lemma fubini_joint_continuous_right (h : R -> R) x y :
  {for y, continuous h} -> continuity_2d_pt (fun _ v => h v) x y.
Proof.
move=> /continuity_pt_filterlim hh.
exact: (continuity_1d_2d_pt_comp h (fun _ v => v) x y hh (continuity_2d_pt_id2 x y)).
Qed.

Lemma fubini_joint_continuous_left (g : R -> R) x y :
  {for x, continuous g} -> continuity_2d_pt (fun u _ => g u) x y.
Proof.
move=> /continuity_pt_filterlim hg.
exact: (continuity_1d_2d_pt_comp g (fun u _ => u) x y hg (continuity_2d_pt_id1 x y)).
Qed.

Lemma fubini_mult_1d_2d (F : R -> R -> R) (w : R -> R) x y :
  continuity_2d_pt F x y -> {for y, continuous w} ->
  continuity_2d_pt (fun u v => F u v * w v) x y.
Proof.
move=> hF hw; apply: continuity_2d_pt_mult => //.
exact: fubini_joint_continuous_right.
Qed.

Lemma fubini_mult_2d_1d (F : R -> R -> R) (w : R -> R) x y :
  continuity_2d_pt F x y -> {for x, continuous w} ->
  continuity_2d_pt (fun u v => w u * F u v) x y.
Proof.
move=> hF hw; apply: continuity_2d_pt_mult => //.
exact: fubini_joint_continuous_left.
Qed.

Lemma fubini_abs_2d (F : R -> R -> R) :
  (forall x y, continuity_2d_pt F x y) ->
  forall x y, continuity_2d_pt (fun u v => Rabs (F u v)) x y.
Proof.
move=> H x y; apply: (continuity_1d_2d_pt_comp Rabs F x y).
- exact: Rcontinuity_abs.
- exact: H.
Qed.

(* A continuous function is bounded on a segment. *)

Lemma continuous_bounded_segment (g : R -> R) a b :
  continuous g -> exists M, forall x, a <= x <= b -> Rabs (g x) <= M.
Proof.
move=> hg.
have [M HM] := rectangle_bound (fun u _ => g u) a b 0 0
  (fun x y => fubini_joint_continuous_left g x y (hg x)).
exists M => x hx; apply: (HM x 0 hx); lra.
Qed.

(* Integrability tools on a measurable subset D of the line. *)

Lemma fubini_continuous_measurable (f : R -> R) :
  continuous f ->
  measurable_fun (setT : set (measurableTypeR R))
    (f : measurableTypeR R -> measurableTypeR R).
Proof. move=> hf; exact: continuous_measurable_fun. Qed.

Lemma fubini_integrable_scale (D : set R) (f : R -> R) (c : R) :
  measurable (D : set (measurableTypeR R)) ->
  lebesgue_measure.-integrable D (EFin \o f) ->
  lebesgue_measure.-integrable D (EFin \o (fun y => c * f y)).
Proof.
move=> mD hf.
apply: (eq_integrable mD _ _ _ (integrableZl mD c hf)).
by move=> y _ /=; rewrite RmultE EFinM.
Qed.

Lemma fubini_integrable_scale_r (D : set R) (f : R -> R) (c : R) :
  measurable (D : set (measurableTypeR R)) ->
  lebesgue_measure.-integrable D (EFin \o f) ->
  lebesgue_measure.-integrable D (EFin \o (fun y => f y * c)).
Proof.
move=> mD hf.
apply: (eq_integrable mD _ _ _ (fubini_integrable_scale _ _ c mD hf)).
by move=> y _ /=; rewrite Rmult_comm.
Qed.

Lemma fubini_integrable_abs (D : set R) (f : R -> R) :
  measurable (D : set (measurableTypeR R)) ->
  lebesgue_measure.-integrable D (EFin \o f) ->
  lebesgue_measure.-integrable D (EFin \o (fun y => Rabs (f y))).
Proof.
move=> mD hf.
apply: (eq_integrable mD _ _ _ (integrable_abse hf)).
by move=> y _ /=; rewrite RabsE.
Qed.

Lemma fubini_integrable_norm (D : set R) (f : R -> R) :
  measurable (D : set (measurableTypeR R)) ->
  lebesgue_measure.-integrable D (EFin \o f) ->
  lebesgue_measure.-integrable D (EFin \o (fun y => `|f y|%R)).
Proof.
move=> mD hf.
apply: (eq_integrable mD _ _ _ (integrable_abse hf)).
by move=> y _ /=.
Qed.

Lemma fubini_dominated_integrable (D : set R) (f G : R -> R) (c : R) :
  measurable (D : set (measurableTypeR R)) ->
  measurable_fun (setT : set (measurableTypeR R))
    (f : measurableTypeR R -> measurableTypeR R) ->
  lebesgue_measure.-integrable D (EFin \o G) ->
  (forall y, D y -> Rabs (f y) <= c * G y) ->
  lebesgue_measure.-integrable D (EFin \o f).
Proof.
move=> mD mf iG hb.
have iG' := fubini_integrable_scale _ _ c mD iG.
apply: (le_integrable mD _ _ iG').
- exact/measurable_EFinP/measurable_funTS.
- move=> y Dy; rewrite /comp !abse_EFin lee_fin.
  apply/RleP; rewrite -!RabsE; apply: (Rle_trans _ _ _ (hb y Dy)); exact: Rle_abs.
Qed.

Lemma fubini_Rintegral_bound (D : set R) (f G : R -> R) (c : R) :
  measurable (D : set (measurableTypeR R)) ->
  lebesgue_measure.-integrable D (EFin \o f) ->
  lebesgue_measure.-integrable D (EFin \o G) ->
  (forall y, D y -> Rabs (f y) <= c * G y) ->
  Rabs (Rintegral lebesgue_measure D f) <= c * Rintegral lebesgue_measure D G.
Proof.
move=> mD hf hG hb.
have h1 := le_normr_Rintegral mD hf.
have hfa := fubini_integrable_norm _ _ mD hf.
have hGc := fubini_integrable_scale _ _ c mD hG.
have h2 : (Rintegral lebesgue_measure D (fun y => `|f y|%R) <=
          Rintegral lebesgue_measure D (fun y => c * G y))%R.
  apply: le_Rintegral => //.
  by move=> y Dy; apply/RleP; rewrite -RabsE; exact: hb.
rewrite (RintegralZl _ mD hG) in h2.
apply/RleP; rewrite RabsE.
exact: (Order.PreorderTheory.le_trans h1 h2).
Qed.

Lemma fubini_Rintegral_abs_le (D : set R) (f : R -> R) :
  measurable (D : set (measurableTypeR R)) ->
  lebesgue_measure.-integrable D (EFin \o f) ->
  Rabs (Rintegral lebesgue_measure D f) <=
  Rintegral lebesgue_measure D (fun y => Rabs (f y)).
Proof.
move=> mD hf.
have h1 := le_normr_Rintegral mD hf.
apply/RleP; rewrite RabsE.
suff -> : (fun y => Rabs (f y)) = (fun y => `|f y|%R) by [].
by apply/funext => y; rewrite RabsE.
Qed.

Lemma fubini_segment_le_whole_line (h : R -> R) (D : set R) :
  measurable (D : set (measurableTypeR R)) -> (forall y, 0 <= h y) ->
  whole_line_integrable h ->
  Rintegral lebesgue_measure D h <= whole_line_integral h.
Proof.
move=> mD h0 ih.
rewrite Rintegral_mkcond /whole_line_integral.
apply/RleP; apply: le_Rintegral => //.
- rewrite -restrict_EFin; apply/(integrable_mkcond _ mD).
  exact: (integrableS measurableT).
- move=> y _; rewrite patchE; case: ifP => _ //=.
  by apply/RleP; exact: h0.
Qed.

Lemma fubini_integral_scale_l (f : R -> R) (c : R) :
  whole_line_integrable f ->
  whole_line_integral (fun x => c * f x) = c * whole_line_integral f.
Proof.
by move=> hf; rewrite /whole_line_integral (RintegralZl _ measurableT hf).
Qed.

Lemma fubini_integral_scale_r (f : R -> R) (c : R) :
  whole_line_integrable f ->
  whole_line_integral (fun x => f x * c) = whole_line_integral f * c.
Proof.
by move=> hf; rewrite /whole_line_integral (RintegralZr _ measurableT hf).
Qed.

(* The integral over [-n, n] tends to the integral over the line. *)

Lemma fubini_cutoff_cvg (f : R -> R) : whole_line_integrable f ->
  (fun n : nat => Rintegral lebesgue_measure `[- INR n, INR n] f) @ \oo
    --> whole_line_integral f.
Proof.
move=> hf.
pose D n : set R := `[- INR n, INR n].
have mD n : measurable (D n : set (measurableTypeR R)) by exact: measurable_itv.
pose f_ n : R -> \bar R := (EFin \o f) \_ (D n).
have mf_ n : measurable_fun (setT : set (measurableTypeR R)) (f_ n).
  apply/(measurable_restrictT _ (mD n)); apply: measurable_funTS.
  exact: (measurable_int _ hf).
have f_f x : (setT : set R) x -> f_ n x @[n --> \oo] --> (EFin \o f) x.
  move=> _.
  have hx : \forall n \near \oo, Rabs x <= INR n.
    by apply: filterS (nbhs_infty_ger (Rabs x)) => n /RleP; rewrite -INRE.
  apply: cvg_near_cst; near=> n.
  have hxn : Rabs x <= INR n by near: n; exact: hx.
  have Dx : D n x.
    have [H1 _] := Rabs_le_between x (INR n); have := H1 hxn.
    rewrite /D /= in_itv /= => hh; apply/andP; split; apply/RleP; lra.
  by rewrite /f_ patchE (mem_set Dx).
have fin x : (setT : set R) x -> (`|(f x)%:E|%E \is a fin_num).
  by move=> _; rewrite abse_fin_num.
have ig : lebesgue_measure.-integrable setT (fun x => `|(f x)%:E|%E).
  exact: integrable_abse hf.
have bnd m x : (setT : set R) x -> (`|f_ m x| <= `|(f x)%:E|)%E.
  move=> _; rewrite /f_ patchE; case: ifP => _ //=.
  by rewrite normr0 lee_fin normr_ge0.
have key := @dominated_cvg _ _ _ lebesgue_measure setT measurableT f_ (EFin \o f)
  (fun x => `|(f x)%:E|%E) mf_ f_f fin ig bnd.
rewrite -(fineK (integrable_fin_num measurableT hf)) in key.
have E : (fun n : nat => Rintegral lebesgue_measure `[- INR n, INR n] f) =1
  fine \o (fun n => \int[lebesgue_measure]_(x in setT) f_ n x)%E.
  by move=> n; rewrite /Rintegral integral_mkcond.
rewrite (eq_cvg _ _ E).
exact: fine_cvg key.
Unshelve. all: by end_near.
Qed.

(* Real sequences. *)

Lemma fubini_seq_cvg0_add (e1 e2 : nat -> R) :
  e1 @ \oo --> 0 -> e2 @ \oo --> 0 -> (fun n => e1 n + e2 n) @ \oo --> 0.
Proof.
move=> h1 h2.
have H := @cvgD R R^o nat \oo _ e1 e2 0 0 h1 h2.
rewrite add0r in H.
exact: H.
Qed.

Lemma fubini_seq_unique (u : nat -> R) (l1 l2 : R) :
  u @ \oo --> l1 -> u @ \oo --> l2 -> l1 = l2.
Proof.
move=> h1 h2.
exact: (@cvg_unique _ (@Rhausdorff _) (u @ \oo) _ l1 l2 h1 h2).
Qed.

(* The oriented integral over a symmetric segment. *)

Lemma fubini_oriented_symmetric (f : R -> R) (A : R) : 0 <= A ->
  oriented_integral f (- A) A = Rintegral lebesgue_measure `[- A, A] f.
Proof.
move=> hA; rewrite /oriented_integral; case: Rle_dec => // h; exfalso; lra.
Qed.

Lemma fubini_segment_integrable (f : R -> R) (A : R) : 0 <= A -> continuous f ->
  lebesgue_measure.-integrable `[- A, A] (EFin \o f).
Proof.
move=> hA hf.
have := rectangle_continuous_segment_integrable f (- A) A hf.
rewrite /segment_integrable Rmin_left ?Rmax_right; try lra.
by [].
Qed.

(* Continuity of a parameter integral over the line. *)

Lemma whole_line_parameter_continuous (F : R -> R -> R) (g h : R -> R) :
  (forall x y, continuity_2d_pt F x y) -> continuous g ->
  whole_line_integrable h -> (forall y, 0 <= h y) ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  continuous (fun x => whole_line_integral (F x)).
Proof.
move=> HF Hg Hh Hh0 Hb x.
have [M HM] := continuous_bounded_segment g (x - 1) (x + 1) Hg.
pose l := x - 1; pose r := x + 1.
pose Phi := fun u => Rintegral lebesgue_measure setT (F u).
have hI : {in `]l, r[, continuous Phi}.
  apply: (@continuity_under_integral R _ _ lebesgue_measure F setT measurableT
    l r _ _ (fun y => M * h y)).
  - move=> u _; apply: (fubini_dominated_integrable _ _ _ (g u) measurableT _ Hh).
    + apply: fubini_continuous_measurable; exact: fubini_slice_left.
    + by move=> y _; exact: Hb.
  - apply: aeW => y _ u _; exact: (fubini_slice_right F y HF u).
  - exact: (fubini_integrable_scale _ _ M measurableT Hh).
  - move=> u /rectangle_open_mem hu; apply: aeW => y _.
    apply/RleP; rewrite -RabsE.
    have hg : Rabs (g u) <= M by apply: HM; rewrite /l /r in hu; lra.
    have := Hb u y; have := Hh0 y; have := Rle_abs (g u); nra.
have hx : {for x, continuous Phi}.
  apply: hI; apply/mem_set; rewrite /= in_itv /=; apply/andP; split; apply/RltP;
    rewrite /l /r; lra.
exact: hx.
Qed.

Lemma whole_line_parameter_continuous_weighted (F : R -> R -> R) (g h w : R -> R) :
  (forall x y, continuity_2d_pt F x y) -> continuous g -> continuous w ->
  whole_line_integrable (fun y => h y * w y) ->
  (forall y, 0 <= h y) -> (forall y, 0 <= w y) ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  continuous (fun x => whole_line_integral (fun y => F x y * w y)).
Proof.
move=> HF Hg Hw Hhw Hh0 Hw0 Hb.
apply: (whole_line_parameter_continuous (fun u v => F u v * w v) g
  (fun y => h y * w y)) => //.
- by move=> x y; apply: fubini_mult_1d_2d => //; exact: Hw.
- by move=> y; have := Hh0 y; have := Hw0 y; nra.
- move=> x y; rewrite Rabs_mult (Rabs_pos_eq (w y) (Hw0 y)).
  have := Hb x y; have := Hw0 y; nra.
Qed.

(* Derivative of a parameter integral over the line. *)

Lemma fubini_harmonic_seq (rho : R) : 0 < rho ->
  exists s : nat -> R, (forall n, 0 < s n <= rho / 2) /\ s @ \oo --> 0.
Proof.
move=> rho0.
exists (fun n => rho / 2 * harmonic n); split.
- move=> n; rewrite /harmonic /= -INRE -RinvE.
  have := pos_INR n; rewrite S_INR => h.
  split.
  + apply: Rmult_lt_0_compat; first lra.
    apply: Rinv_0_lt_compat; lra.
  + rewrite -{2}(Rmult_1_r (rho / 2)); apply: Rmult_le_compat_l; first lra.
    rewrite -Rinv_1; apply: Rinv_le_contravar; lra.
- have := cvgM (cvg_cst (rho / 2)) (@cvg_harmonic _).
  rewrite mulr0 => H; exact: H.
Qed.

Lemma fubini_derivative_seq (F : R -> R -> R) (D : R -> R -> R) (a : R) x :
  @is_derive R R^o R^o a 1 (fun u => F u x) (D a x) ->
  forall s : nat -> R, (forall n, s n <> 0) -> s @ \oo --> 0 ->
  (fun n => (F (a + s n) x - F a x) / s n) @ \oo --> D a x.
Proof.
move=> Hx s s0 sc.
have s0' n : s n != 0 by apply/negP => /eqP; exact: s0.
case: Hx => dv dE.
rewrite -dE /derive.
move: dv; rewrite /derivable => /cvgr_dnbhsP /(_ s (conj s0' sc)) H'.
apply: (cvg_trans _ H'); apply: near_eq_cvg; apply: nearW => n /=.
rewrite !scaleRE Rmult_1_r.
suff -> : (F (a + s n) x - F a x) / s n = / s n * (F (s n + a) x - F a x) by [].
by rewrite Rplus_comm /Rdiv Rmult_comm.
Qed.

Lemma whole_line_parameter_derivative (F D : R -> R -> R) (a rho : R) (G : R -> R) :
  0 < rho ->
  (forall t x, Rabs (t - a) <= rho ->
    @is_derive R R^o R^o t 1 (fun u => F u x) (D t x)) ->
  (forall t, Rabs (t - a) <= rho -> whole_line_integrable (F t)) ->
  (forall t x, Rabs (t - a) <= rho -> Rabs (D t x) <= G x) ->
  whole_line_integrable G -> (forall x, 0 <= G x) ->
  whole_line_integrable (D a) /\
  @is_derive R R^o R^o a 1 (fun t => whole_line_integral (F t))
    (whole_line_integral (D a)).
Proof.
move=> rho0 HD HF HG iG G0.
have haa : Rabs (a - a) <= rho by rewrite Rminus_diag Rabs_R0; lra.
pose l := a - rho; pose r := a + rho.
have Ia : (`]l, r[ : set R) a.
  by rewrite /= in_itv /=; apply/andP; split; apply/RltP; rewrite /l /r; lra.
have inI : forall t, (`]l, r[ : set R) t -> Rabs (t - a) <= rho.
  move=> t /rectangle_open_mem ht; rewrite /l /r in ht; apply/Rabs_le_between; lra.
have intf : forall t, (`]l, r[ : set R) t ->
    lebesgue_measure.-integrable setT (EFin \o F t).
  by move=> t /inI; exact: HF.
have derf1 : forall t x, (`]l, r[ : set R) t -> (setT : set R) x ->
    @derivable R R^o R^o (F^~ x) t 1.
  by move=> t x /inI ht _; case: (HD t x ht).
have Hd1 : forall t x, Rabs (t - a) <= rho -> partial1of2 F t x = D t x.
  by move=> t x ht; rewrite partial1of2E; case: (HD t x ht).
have G0' : forall x : R, (0 <= G x)%R by move=> x; apply/RleP; exact: G0.
have Gub : forall t x, (`]l, r[ : set R) t -> (setT : set R) x ->
    (`|partial1of2 F t x| <= G x)%R.
  by move=> t x /inI ht _; rewrite Hd1 //; apply/RleP; rewrite -RabsE; exact: HG.
have hd := derivable_under_integral measurableT Ia intf derf1 G0' iG Gub.
have hv := differentiation_under_integral measurableT Ia intf derf1 G0' iG Gub.
pose Phi := fun t => Rintegral lebesgue_measure setT (F t).
have hFd : @is_derive R R^o R^o a 1 Phi (Rintegral lebesgue_measure setT (D a)).
  apply: DeriveDef; first exact: hd.
  rewrite -derive1E /Phi hv.
  by apply: eq_Rintegral => x _; rewrite Hd1.
have [s [s_pos s_cvg]] := fubini_harmonic_seq rho rho0.
have s0 n : s n <> 0 by have := s_pos n; lra.
have sI n : (`]l, r[ : set R) (a + s n).
  have := s_pos n; rewrite /= in_itv /= => hs; apply/andP; split; apply/RltP;
    rewrite /l /r; lra.
pose q := fun (n : nat) (x : R) => (F (a + s n) x - F a x) / s n.
have mF : forall t, (`]l, r[ : set R) t ->
    measurable_fun (setT : set (measurableTypeR R))
      (F t : measurableTypeR R -> measurableTypeR R).
  by move=> t It; apply/measurable_EFinP; exact: (measurable_int _ (intf t It)).
have mq n : measurable_fun (setT : set (measurableTypeR R))
    (q n : measurableTypeR R -> measurableTypeR R).
  have H := measurable_funM (measurable_funB (mF _ (sI n)) (mF _ Ia))
    (@measurable_cst _ _ (measurableTypeR R) (measurableTypeR R) setT (/ s n)).
  exact: H.
have qcvg : forall x, (setT : set R) x -> q ^~ x @ \oo --> D a x.
  by move=> x _; exact: (fubini_derivative_seq F D a x (HD a x haa) s s0 s_cvg).
have mDa : measurable_fun (setT : set (measurableTypeR R))
    (D a : measurableTypeR R -> measurableTypeR R).
  have H := @measurable_fun_cvg _ (measurableTypeR R) _ setT q (D a) mq qcvg.
  exact: H.
have iDa : whole_line_integrable (D a).
  apply: (fubini_dominated_integrable _ _ _ 1 measurableT mDa iG).
  by move=> x _; rewrite Rmult_1_l; exact: HG.
split; first exact: iDa.
exact: hFd.
Qed.

(* Fubini on the line for a separably dominated jointly continuous
   integrand. *)

Lemma whole_line_fubini_inner_integrable (F : R -> R -> R) (g h : R -> R) :
  (forall x y, continuity_2d_pt F x y) -> whole_line_integrable h ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  forall x, whole_line_integrable (F x).
Proof.
move=> HF Hh Hb x.
apply: (fubini_dominated_integrable _ _ _ (g x) measurableT _ Hh).
- apply: fubini_continuous_measurable; exact: fubini_slice_left.
- by move=> y _; exact: Hb.
Qed.

Lemma whole_line_fubini_inner_bound (F : R -> R -> R) (g h : R -> R) :
  whole_line_integrable h -> (forall x y, Rabs (F x y) <= g x * h y) ->
  (forall x, whole_line_integrable (F x)) ->
  forall x, Rabs (whole_line_integral (F x)) <= g x * whole_line_integral h.
Proof.
move=> Hh Hb HFx x.
exact: (fubini_Rintegral_bound _ _ _ (g x) measurableT (HFx x) Hh (fun y _ => Hb x y)).
Qed.

Lemma whole_line_fubini_outer_integrable (F : R -> R -> R) (g h : R -> R) :
  (forall x y, continuity_2d_pt F x y) -> continuous g ->
  whole_line_integrable g -> whole_line_integrable h -> (forall y, 0 <= h y) ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  whole_line_integrable (fun x => whole_line_integral (F x)).
Proof.
move=> HF Hg Hig Hih Hh0 Hb.
apply: (fubini_dominated_integrable _ _ _ (whole_line_integral h) measurableT _ Hig).
- apply: fubini_continuous_measurable; exact: (whole_line_parameter_continuous F g h).
- move=> x _; rewrite Rmult_comm; apply: whole_line_fubini_inner_bound => //.
  exact: (whole_line_fubini_inner_integrable F g h).
Qed.

Lemma fubini_iterated_cutoff_cvg (F : R -> R -> R) (g h : R -> R) :
  (forall x y, continuity_2d_pt F x y) -> continuous g ->
  (forall x, 0 <= g x) -> (forall y, 0 <= h y) ->
  whole_line_integrable g -> whole_line_integrable h ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  (fun n : nat => oriented_integral
      (fun x => oriented_integral (F x) (- INR n) (INR n)) (- INR n) (INR n)) @ \oo
    --> whole_line_integral (fun x => whole_line_integral (F x)).
Proof.
move=> HF Hg Hg0 Hh0 Hig Hih Hb.
pose Phi := fun x => whole_line_integral (F x).
pose Phin := fun n : nat => fun x => oriented_integral (F x) (- INR n) (INR n).
pose D := fun n : nat => (`[- INR n, INR n] : set R).
have mD n : measurable (D n : set (measurableTypeR R)) by exact: measurable_itv.
have hn n : 0 <= INR n by exact: pos_INR.
have HFx : forall x, whole_line_integrable (F x) :=
  whole_line_fubini_inner_integrable F g h HF Hih Hb.
have cPhin n : continuous (Phin n).
  by move=> x; exact: rectangle_parameter_integral_continuous.
pose f_ := fun n : nat => ((EFin \o Phin n) \_ (D n) : R -> \bar R).
have mf_ n : measurable_fun (setT : set (measurableTypeR R)) (f_ n).
  apply/(measurable_restrictT _ (mD n)); apply: measurable_funTS.
  apply/measurable_EFinP; exact: fubini_continuous_measurable.
pose H := whole_line_integral h.
have H0 : 0 <= H by apply/RleP; apply: Rintegral_ge0 => y _; apply/RleP; exact: Hh0.
pose G := fun x => g x * H.
have G0 x : 0 <= G x by rewrite /G; have := Hg0 x; nra.
have Phin_bound n x : Rabs (Phin n x) <= G x.
  rewrite /Phin fubini_oriented_symmetric // -[`[- INR n, INR n]]/(D n).
  have h1 := fubini_Rintegral_bound (D n) (F x) h (g x) (mD n)
    (integrableS measurableT (mD n) (@subsetT _ _) (HFx x))
    (integrableS measurableT (mD n) (@subsetT _ _) Hih) (fun y _ => Hb x y).
  have h2 := fubini_segment_le_whole_line h (D n) (mD n) Hh0 Hih.
  have := Hg0 x; rewrite /G /H; nra.
have f_f x : (setT : set R) x -> f_ n x @[n --> \oo] --> (EFin \o Phi) x.
  move=> _.
  have hu : (fun n => Phin n x) @ \oo --> Phi x.
    have E : (fun n : nat => Rintegral lebesgue_measure `[- INR n, INR n] (F x)) =1
        (fun n => Phin n x).
      by move=> n; rewrite /Phin fubini_oriented_symmetric.
    rewrite -(eq_cvg _ _ E).
    exact: fubini_cutoff_cvg.
  have hv : (fun n => (Phin n x)%:E) @ \oo --> (Phi x)%:E.
    apply: cvg_EFin; first exact: nearW.
    exact: hu.
  apply: (cvg_trans _ hv); apply: near_eq_cvg.
  have hx : \forall n \near \oo, Rabs x <= INR n.
    by apply: filterS (nbhs_infty_ger (Rabs x)) => n /RleP; rewrite -INRE.
  near=> n.
  have hxn : Rabs x <= INR n by near: n; exact: hx.
  have Dx : D n x.
    have [H1 _] := Rabs_le_between x (INR n); have := H1 hxn.
    rewrite /D /= in_itv /= => hh; apply/andP; split; apply/RleP; lra.
  by rewrite /f_ patchE (mem_set Dx).
have fin x : (setT : set R) x -> ((EFin \o G) x \is a fin_num) by [].
have ig : lebesgue_measure.-integrable setT (EFin \o G).
  apply: (eq_integrable measurableT _ _ _
    (fubini_integrable_scale setT g H measurableT Hig)).
  by move=> x _ /=; rewrite /G Rmult_comm.
have bnd m x : (setT : set R) x -> (`|f_ m x| <= (EFin \o G) x)%E.
  move=> _; rewrite /f_ patchE; case: ifP => _ /=.
  - by rewrite lee_fin; apply/RleP; rewrite -RabsE; exact: Phin_bound.
  - by rewrite normr0 lee_fin; apply/RleP; exact: G0.
have key := @dominated_cvg _ _ _ lebesgue_measure setT measurableT f_ (EFin \o Phi)
  (EFin \o G) mf_ f_f fin ig bnd.
have iPhi : whole_line_integrable Phi :=
  whole_line_fubini_outer_integrable F g h HF Hg Hig Hih Hh0 Hb.
rewrite -(fineK (integrable_fin_num measurableT iPhi)) in key.
have E : (fun n : nat => oriented_integral (Phin n) (- INR n) (INR n)) =1
  fine \o (fun n => \int[lebesgue_measure]_(x in setT) f_ n x)%E.
  by move=> n; rewrite fubini_oriented_symmetric // /Rintegral integral_mkcond.
rewrite (eq_cvg _ _ E).
exact: fine_cvg key.
Unshelve. all: by end_near.
Qed.

Theorem whole_line_fubini (F : R -> R -> R) (g h : R -> R) :
  (forall x y, continuity_2d_pt F x y) -> continuous g -> continuous h ->
  (forall x, 0 <= g x) -> (forall y, 0 <= h y) ->
  whole_line_integrable g -> whole_line_integrable h ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  whole_line_integral (fun x => whole_line_integral (F x)) =
  whole_line_integral (fun y => whole_line_integral (fun x => F x y)).
Proof.
move=> HF Hg Hh Hg0 Hh0 Hig Hih Hb.
have HFt : forall y x, continuity_2d_pt (fun v u => F u v) y x.
  by move=> y x; exact: rectangle_continuous_transpose.
have Hbt : forall y x, Rabs (F x y) <= h y * g x.
  by move=> y x; rewrite Rmult_comm; exact: Hb.
have L := fubini_iterated_cutoff_cvg F g h HF Hg Hg0 Hh0 Hig Hih Hb.
have Rr := fubini_iterated_cutoff_cvg (fun y x => F x y) h g HFt Hh Hh0 Hg0 Hih Hig Hbt.
have E : (fun n : nat => oriented_integral
      (fun x => oriented_integral (F x) (- INR n) (INR n)) (- INR n) (INR n)) =1
    (fun n : nat => oriented_integral
      (fun y => oriented_integral (fun x => F x y) (- INR n) (INR n)) (- INR n) (INR n)).
  by move=> n; exact: continuous_rectangle_fubini.
rewrite (eq_cvg _ _ E) in L.
exact: (fubini_seq_unique _ _ _ L Rr).
Qed.

(* Fubini with a nonnegative continuous weight on each variable. With w the
   Gaussian kernel, the hypotheses on g and h are gaussian_integral_exists g
   and gaussian_integral_exists h. *)

Theorem whole_line_fubini_weighted (F : R -> R -> R) (g h w : R -> R) :
  (forall x y, continuity_2d_pt F x y) ->
  continuous g -> continuous h -> continuous w ->
  (forall x, 0 <= g x) -> (forall y, 0 <= h y) -> (forall x, 0 <= w x) ->
  whole_line_integrable (fun x => g x * w x) ->
  whole_line_integrable (fun y => h y * w y) ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  (forall x, whole_line_integrable (fun y => F x y * w y)) /\
  (forall y, whole_line_integrable (fun x => F x y * w x)) /\
  whole_line_integrable (fun x => whole_line_integral (fun y => F x y * w y) * w x) /\
  whole_line_integrable (fun y => whole_line_integral (fun x => F x y * w x) * w y) /\
  whole_line_integral (fun x => whole_line_integral (fun y => F x y * w y) * w x) =
  whole_line_integral (fun y => whole_line_integral (fun x => F x y * w x) * w y).
Proof.
move=> HF Hg Hh Hw Hg0 Hh0 Hw0 Higw Hihw Hb.
pose G := fun x y => F x y * w y * w x.
have HG : forall x y, continuity_2d_pt (fun u v => F u v * w v * w u) x y.
  move=> x y; apply: continuity_2d_pt_mult.
  - by apply: fubini_mult_1d_2d; [exact: HF | exact: Hw].
  - exact: (fubini_joint_continuous_left w x y (Hw x)).
have Hgw0 x : 0 <= g x * w x by have := Hg0 x; have := Hw0 x; nra.
have Hhw0 y : 0 <= h y * w y by have := Hh0 y; have := Hw0 y; nra.
have HGb : forall x y, Rabs (G x y) <= (g x * w x) * (h y * w y).
  move=> x y; rewrite /G !Rabs_mult (Rabs_pos_eq (w y) (Hw0 y)) (Rabs_pos_eq (w x) (Hw0 x)).
  have := Hb x y; have := Rmult_le_pos _ _ (Hw0 x) (Hw0 y).
  have := Hw0 x; have := Hw0 y; have := Rabs_pos (F x y); nra.
have cgw : continuous (fun x => g x * w x).
  by move=> x; exact: (continuous_mult _ _ _ x (Hg x) (Hw x)).
have chw : continuous (fun y => h y * w y).
  by move=> y; exact: (continuous_mult _ _ _ y (Hh y) (Hw y)).
have Hin : forall x, whole_line_integrable (fun y => F x y * w y).
  move=> x.
  apply: (fubini_dominated_integrable _ _ _ (g x) measurableT _ Hihw).
  - apply: fubini_continuous_measurable => y.
    exact: (continuous_mult _ _ _ y (fubini_slice_left F x HF y) (Hw y)).
  - move=> y _; rewrite Rabs_mult (Rabs_pos_eq (w y) (Hw0 y)).
    have := Hb x y; have := Hw0 y; nra.
have HinT : forall y, whole_line_integrable (fun x => F x y * w x).
  move=> y.
  apply: (fubini_dominated_integrable _ _ _ (h y) measurableT _ Higw).
  - apply: fubini_continuous_measurable => x.
    exact: (continuous_mult _ _ _ x (fubini_slice_right F y HF x) (Hw x)).
  - move=> x _; rewrite Rabs_mult (Rabs_pos_eq (w x) (Hw0 x)).
    have := Hb x y; have := Hw0 x; nra.
have inner : forall x,
    whole_line_integral (G x) = whole_line_integral (fun y => F x y * w y) * w x.
  by move=> x; exact: (fubini_integral_scale_r _ _ (Hin x)).
have innerT : forall y,
    whole_line_integral (fun x => G x y) =
    whole_line_integral (fun x => F x y * w x) * w y.
  move=> y.
  have -> : (fun x => G x y) = (fun x => (F x y * w x) * w y).
    by apply/funext => x; rewrite /G; ring.
  exact: (fubini_integral_scale_r _ _ (HinT y)).
have HGt : forall y x, continuity_2d_pt (fun v u => G u v) y x.
  by move=> y x; exact: (rectangle_continuous_transpose G x y (HG x y)).
have HGbt : forall y x, Rabs (G x y) <= (h y * w y) * (g x * w x).
  by move=> y x; rewrite Rmult_comm; exact: HGb.
have main := whole_line_fubini G _ _ HG cgw chw Hgw0 Hhw0 Higw Hihw HGb.
have outer := whole_line_fubini_outer_integrable G _ _ HG cgw Higw Hihw Hhw0 HGb.
have outerT := whole_line_fubini_outer_integrable (fun y x => G x y) _ _ HGt chw
  Hihw Higw Hgw0 HGbt.
split; [exact: Hin | split; [exact: HinT | split; [| split]]].
- by apply: (eq_integrable measurableT _ _ _ outer) => x _ /=; rewrite inner.
- by apply: (eq_integrable measurableT _ _ _ outerT) => y _ /=; rewrite innerT.
- transitivity (whole_line_integral (fun x => whole_line_integral (G x))).
    by apply: eq_Rintegral => x _; rewrite inner.
  rewrite main.
  by apply: eq_Rintegral => y _; rewrite innerT.
Qed.
