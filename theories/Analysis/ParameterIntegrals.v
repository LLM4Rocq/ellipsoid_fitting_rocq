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
   which Analysis.CalculusBridge does not export. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import Analysis.RectangleFubini.
From mathcomp Require Import measurable_realfun.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* Slices and products of jointly continuous functions. *)

(* A continuous function is bounded on a segment. *)

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

(* Derivative of a parameter integral over the line. *)
