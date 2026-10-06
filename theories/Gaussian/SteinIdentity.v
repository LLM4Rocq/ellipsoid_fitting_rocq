(* Gaussian integration by parts on the line (Stein's identity), with the
   Lebesgue integral over the line. Here f' = df and df' = ddf, and the
   highest derivative is continuous. In the identities, the products of the
   kernel with f, or with df and x * f x, tend to 0 at both ends.
   - gaussian_stein_split_decay: if df x * gaussian_kernel x has integral
     l, so has x * f x * gaussian_kernel x; that is, E[x f(x)] = E[f'(x)].
   - gaussian_stein_second_split_decay: if ddf x * gaussian_kernel x has
     integral l, so has (x*x - 1) * f x * gaussian_kernel x.
   - gaussian_stein_moment_integrable: if df x * gaussian_kernel x is
     integrable on the line, so is x * f x * gaussian_kernel x.
     gaussian_stein_second_moment_integrable: if ddf x * gaussian_kernel x
     is integrable, so is (x*x - 1) * f x * gaussian_kernel x.
   - gaussian_stein_second_decay: the integral of
     (ddf x - (x*x - 1) * f x) * gaussian_kernel x is 0 when this integrand
     is integrable on the line. *)

From Stdlib Require Import Reals Lia Lra Psatz Classical_Prop.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import Gaussian.Kernel.
From EllipsoidFitting Require Import Analysis.RectangleFubini
  Analysis.ParameterIntegrals.
From mathcomp Require Import measurable_realfun.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* Tools for the integrability of the moments. *)
Lemma gaussian_stein_segment_integrable (g : R -> R) a b : a <= b ->
  continuous g -> lebesgue_measure.-integrable `[a, b] (EFin \o g).
Proof.
move=> hab hg.
have := rectangle_continuous_segment_integrable g a b hg.
by rewrite /segment_integrable Rmin_left ?Rmax_right.
Qed.

Lemma gaussian_stein_abs_continuous (g : R -> R) :
  continuous g -> continuous (fun t => Rabs (g t)).
Proof. move=> hg x; exact: (continuous_comp (hg x) (continuous_Rabs (g x))). Qed.

(* The oriented primitive of Rabs df from 0 bounds the increment of f. *)
Lemma gaussian_stein_abs_primitive_bound (f df : R -> R) x :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) -> continuous df ->
  Rabs (f x - f 0) <= Rabs (oriented_integral (fun t => Rabs (df t)) 0 x).
Proof.
move=> Hd Hc.
rewrite -(rectangle_oriented_FTC f df 0 x Hd Hc).
rewrite /oriented_integral; case: Rle_dec => h /=.
- have i := gaussian_stein_segment_integrable df 0 x h Hc.
  have h1 := fubini_Rintegral_abs_le _ df (measurable_itv _) i.
  have h2 : 0 <= Rintegral lebesgue_measure `[0, x] (fun t => Rabs (df t)).
  { apply/RleP; apply: Rintegral_ge0 => t _; apply/RleP; exact: Rabs_pos. }
  rewrite (Rabs_pos_eq _ h2); exact h1.
- have h' : x <= 0 by lra.
  have i := gaussian_stein_segment_integrable df x 0 h' Hc.
  have h1 := fubini_Rintegral_abs_le _ df (measurable_itv _) i.
  have h2 : 0 <= Rintegral lebesgue_measure `[x, 0] (fun t => Rabs (df t)).
  { apply/RleP; apply: Rintegral_ge0 => t _; apply/RleP; exact: Rabs_pos. }
  rewrite !Rabs_Ropp (Rabs_pos_eq _ h2); exact h1.
Qed.

Lemma gaussian_stein_abs_primitive_sign (g : R -> R) x :
  continuous g ->
  (0 <= x -> 0 <= oriented_integral (fun t => Rabs (g t)) 0 x) /\
  (x <= 0 -> oriented_integral (fun t => Rabs (g t)) 0 x <= 0).
Proof.
move=> Hc; split => hx.
- rewrite /oriented_integral; case: Rle_dec => h /=; last lra.
  apply/RleP; apply: Rintegral_ge0 => t _; apply/RleP; exact: Rabs_pos.
- case: (Rle_lt_or_eq_dec x 0 hx) => [hx0|->].
  + rewrite /oriented_integral; case: Rle_dec => h /=; first lra.
    set I := Rintegral _ _ _.
    have h2 : 0 <= I.
    { apply/RleP; apply: Rintegral_ge0 => t _; apply/RleP; exact: Rabs_pos. }
    lra.
  + rewrite rectangle_oriented_point; lra.
Qed.

(* A continuous nonnegative function whose integrals over the segments
   [-n, n] are bounded is integrable on the line. *)
Lemma gaussian_stein_nonneg_integrable (h : R -> R) C :
  continuous h -> (forall x, 0 <= h x) ->
  (forall n : nat, Rintegral lebesgue_measure `[- INR n, INR n] h <= C) ->
  whole_line_integrable h.
Proof.
move=> hc h0 hb.
have mh := fubini_continuous_measurable h hc.
apply/integrableP; split; first exact/measurable_EFinP.
have -> : (\int[lebesgue_measure]_(x in setT) `|(EFin \o h) x|)%E =
    (\int[lebesgue_measure]_(x in setT) (EFin \o h) x)%E.
{ apply: eq_integral => x _; rewrite /comp gee0_abs // lee_fin.
  apply/RleP; exact: h0. }
pose D n : set (measurableTypeR R) := `[- INR n, INR n].
have mD n : measurable (D n : set (measurableTypeR R)) by exact: measurable_itv.
have nd : nondecreasing_seq D.
{ move=> n m /leP nm; rewrite subsetEset => x.
  have := le_INR n m nm.
  rewrite /D /= !in_itv /= => hnm /andP [/RleP h1 /RleP h2].
  apply/andP; split; apply/RleP; lra. }
have mf : forall i, measurable_fun (D i) (EFin \o h).
{ move=> i; apply: measurable_funTS; exact/measurable_EFinP. }
have f0 : forall i x, D i x -> (0 <= (EFin \o h) x)%E.
{ move=> i x _; rewrite /comp lee_fin; apply/RleP; exact: h0. }
have cv := @ge0_nondecreasing_set_cvg_integral _ _ _ D (EFin \o h)
  lebesgue_measure nd mD mf f0.
have U : \bigcup_i D i = setT.
{ apply/seteqP; split => // x _.
  have hx : \forall n \near \oo, Rabs x <= INR n.
    by apply: filterS (nbhs_infty_ger (Rabs x)) => n /RleP; rewrite -INRE.
  have [N _ hN] := hx.
  exists N => //.
  have hxN : Rabs x <= INR N by apply: hN => /=.
  have [H1 _] := Rabs_le_between x (INR N); have := H1 hxN.
  rewrite /D /= in_itv /= => hh; apply/andP; split; apply/RleP; lra. }
rewrite U in cv.
have bnd : forall n,
    (\int[lebesgue_measure]_(x in D n) (EFin \o h) x <= C%:E)%E.
{ move=> n.
  have i := fubini_segment_integrable h (INR n) (pos_INR n) hc.
  rewrite -(fineK (integrable_fin_num (mD n) i)) lee_fin.
  apply/RleP; exact: hb. }
apply: (Order.POrderTheory.le_lt_trans (y := C%:E)); last exact: ltry.
rewrite -(cvg_lim _ cv) //.
apply: lime_le; first by apply/cvg_ex; eexists; exact: cv.
exact: nearW.
Qed.

(* The key estimate: if df * gaussian_kernel is integrable, then so is
   x * f x * gaussian_kernel x. With F the oriented primitive of Rabs df
   from 0, Rabs (x * f x) <= Rabs x * Rabs (f 0) + x * F x, and
   x * F x * gaussian_kernel x is the derivative of
   - F x * gaussian_kernel x plus Rabs (df x) * gaussian_kernel x. *)
Lemma gaussian_stein_moment_integrable (f df : R -> R) :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, {for t, continuous df}) ->
  whole_line_integrable (fun t => df t * gaussian_kernel t) ->
  whole_line_integrable (fun t => t * f t * gaussian_kernel t).
Proof.
move=> Hd Hc Hi.
have Hfc : continuous f := fun t => is_derive_continuous _ _ _ (Hd t).
have Ha := gaussian_stein_abs_continuous df Hc.
set a := fun t => Rabs (df t) in Ha.
have HF : forall x, @is_derive R R^o R^o x 1
    (fun z => oriented_integral a 0 z) (a x).
{ move=> x; exact: rectangle_oriented_primitive_derivative. }
set F := fun z => oriented_integral a 0 z in HF.
have HFc : continuous F := fun x => is_derive_continuous _ _ _ (HF x).
have Hk : continuous gaussian_kernel := gaussian_kernel_continuous.
have hF0 : forall x, 0 <= x * F x.
{ move=> x; have [s1 s2] := gaussian_stein_abs_primitive_sign df x Hc.
  rewrite /F /a; case: (Rle_dec 0 x) => hx.
  - have := s1 hx; nra.
  - have := s2 ltac:(lra); nra. }
pose h := fun x => x * F x * gaussian_kernel x.
have hc : continuous h.
{ move=> x; apply: continuous_mult; last exact: Hk.
  apply: continuous_mult; [exact: continuous_id | exact: HFc]. }
have h0 : forall x, 0 <= h x.
{ move=> x; rewrite /h; have := hF0 x; have := gaussian_kernel_positive x.
  nra. }
pose Q := fun x => - F x * gaussian_kernel x.
have HQ : forall x, @is_derive R R^o R^o x 1 Q
    (h x - a x * gaussian_kernel x).
{ move=> x.
  have H := is_derive_mult (fun y => - F y) gaussian_kernel x (- a x)
    (- x * gaussian_kernel x) (is_derive_opp F x (a x) (HF x))
    (gaussian_kernel_derivative x).
  have E : - a x * gaussian_kernel x + - F x * (- x * gaussian_kernel x) =
      h x - a x * gaussian_kernel x by rewrite /h; ring.
  rewrite E in H; exact H. }
have Hak : continuous (fun x => a x * gaussian_kernel x).
{ move=> x; apply: continuous_mult; [exact: Ha | exact: Hk]. }
have Hdiff : continuous (fun x => h x - a x * gaussian_kernel x).
{ move=> x; apply: continuous_minus; [exact: hc | exact: Hak]. }
have Iak : whole_line_integrable (fun x => a x * gaussian_kernel x).
{ have := fubini_integrable_abs setT _ measurableT Hi.
  apply: (eq_integrable measurableT) => x _ /=.
  rewrite /a Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _ (gaussian_kernel_positive x))).
  done. }
have ak0 : forall x, 0 <= a x * gaussian_kernel x.
{ move=> x; rewrite /a; have := Rabs_pos (df x);
  have := gaussian_kernel_positive x; nra. }
have bound : forall n : nat, Rintegral lebesgue_measure `[- INR n, INR n] h <=
    whole_line_integral (fun x => a x * gaussian_kernel x).
{ move=> n; have n0 := pos_INR n.
  rewrite -(fubini_oriented_symmetric h (INR n) n0).
  have E1 := rectangle_oriented_FTC Q _ (- INR n) (INR n) HQ Hdiff.
  have E2 := rectangle_oriented_minus h (fun x => a x * gaussian_kernel x)
    (- INR n) (INR n) (rectangle_continuous_segment_integrable _ _ _ hc)
    (rectangle_continuous_segment_integrable _ _ _ Hak).
  have E3 := fubini_oriented_symmetric (fun x => a x * gaussian_kernel x)
    (INR n) n0.
  have E4 := fubini_segment_le_whole_line (fun x => a x * gaussian_kernel x)
    `[- INR n, INR n] (measurable_itv _) ak0 Iak.
  have [s1 _] := gaussian_stein_abs_primitive_sign df (INR n) Hc.
  have [_ s2] := gaussian_stein_abs_primitive_sign df (- INR n) Hc.
  have q1 : Q (INR n) <= 0.
  { rewrite /Q /F /a; have := s1 n0;
    have := gaussian_kernel_positive (INR n); nra. }
  have q2 : 0 <= Q (- INR n).
  { rewrite /Q /F /a; have := s2 ltac:(lra);
    have := gaussian_kernel_positive (- INR n); nra. }
  rewrite E1 in E2; rewrite E3 in E2.
  lra. }
have Ih := gaussian_stein_nonneg_integrable h _ hc h0 bound.
pose G := fun x => Rabs (f 0) * (Rabs x * gaussian_kernel x) + h x.
have iG : whole_line_integrable G.
{ have a1 := fubini_integrable_scale setT _ (Rabs (f 0)) measurableT
    gaussian_kernel_abs_moment_integrable.
  apply: (eq_integrable measurableT _ _ _ (integrableD measurableT a1 Ih)).
  by move=> x _ /=; rewrite /G -EFinD -RplusE. }
apply: (fubini_dominated_integrable setT _ G 1 measurableT _ iG).
- apply: fubini_continuous_measurable => x.
  apply: continuous_mult; last exact: Hk.
  apply: continuous_mult; [exact: continuous_id | exact: Hfc].
- move=> x _; rewrite /G /h.
  have B := gaussian_stein_abs_primitive_bound f df x Hd Hc.
  change (Rabs (f x - f 0) <= Rabs (F x)) in B.
  have T : Rabs (f x) <= Rabs (f 0) + Rabs (f x - f 0).
  { have := Rabs_triang (f 0) (f x - f 0).
    by have -> : f 0 + (f x - f 0) = f x by ring. }
  have P : Rabs x * Rabs (F x) = x * F x.
  { rewrite -Rabs_mult; apply: Rabs_pos_eq; exact: hF0. }
  have kp := gaussian_kernel_positive x.
  have S : Rabs x * Rabs (f x) <= Rabs x * Rabs (f 0) + x * F x.
  { rewrite -P; have := Rabs_pos x; nra. }
  rewrite !Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _ kp)).
  have S' := Rmult_le_compat_r _ _ _ (Rlt_le _ _ kp) S.
  lra.
Qed.

(* Stein's identities. *)

Lemma gaussian_stein_split_decay (f df : R -> R) l :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, {for t, continuous df}) ->
  (f x * gaussian_kernel x @[x --> -oo%R] --> 0)%classic ->
  (f x * gaussian_kernel x @[x --> +oo%R] --> 0)%classic ->
  whole_line_has_integral (fun t => df t * gaussian_kernel t) l ->
  whole_line_has_integral (fun t => t * f t * gaussian_kernel t) l.
Proof.
  intros Hd Hc Hm Hp [Hi Hl].
  have Hx := gaussian_stein_moment_integrable f df Hd Hc Hi.
  have Is : whole_line_integrable (gaussian_stein_integrand f df).
  { apply: (eq_integrable measurableT _ _ _ (integrableB measurableT Hi Hx)).
    move=> y _ /=.
    by rewrite -EFinB /gaussian_stein_integrand -RminusE. }
  have [_ Hs0] := gaussian_stein_improper_decay f df Hd Hc Hm Hp Is.
  split; first exact Hx.
  have E : (fun t => t * f t * gaussian_kernel t) =
      (fun t => df t * gaussian_kernel t - gaussian_stein_integrand f df t).
  { apply/funext => t; unfold gaussian_stein_integrand; ring. }
  rewrite E /whole_line_integral (RintegralB measurableT Hi Is).
  unfold whole_line_integral in Hl, Hs0.
  rewrite Hl Hs0 -RminusE; ring.
Qed.
