(* Parameter integrals over the real line, with the Lebesgue integrals of
   AnalysisIntegralDefinitions and of MathComp, and Stdlib's operations on
   R in every statement.
   - whole_line_parameter_continuous: x |-> whole_line_integral (F x) is
     continuous when F is jointly continuous and dominated by g x * h y,
     with g continuous and h nonnegative and integrable. The proof applies
     MathComp's continuity_under_integral on ]x - 1, x + 1[.
     whole_line_parameter_continuous_weighted is the same for the
     integrand F x y * w y, with a nonnegative continuous weight w.
   - whole_line_parameter_derivative: on the band |t - a| <= rho, let
     every F t be integrable, let F t x have the derivative D t x in t,
     and let D be dominated by an integrable G >= 0. Then D a is
     integrable and t |-> whole_line_integral (F t) has the derivative
     whole_line_integral (D a) at a. The proof applies MathComp's
     derivable_under_integral and differentiation_under_integral; the
     measurability of D a comes from the difference quotients along
     a + rho / 2 * harmonic n.
   - fubini_cutoff_cvg: for f integrable on the line, the integral of f
     over [-n, n] tends to its integral over the line, by dominated
     convergence.
   The other lemmas are tools: continuity of the sections and products of
   jointly continuous functions, boundedness on segments, integrability
   and bounds on a measurable set (fubini_dominated_integrable,
   fubini_Rintegral_bound), and the oriented integral over [-A, A]
   (fubini_oriented_symmetric, fubini_segment_integrable).

   Conventions. Measurability of f : R -> R is stated for f seen as a map
   measurableTypeR R -> measurableTypeR R, on setT. The bounds of an
   interval `[a, b] are parsed in MathComp's ring scope, so
   `[- INR n, INR n] carries MathComp's opposite, which is convertible with
   Stdlib's. The module does not import ListNotations, under which the
   open interval `]l, r[ does not parse, and it imports measurable_realfun,
   which AnalysisBridge does not export. *)

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
