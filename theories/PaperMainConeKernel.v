(* Deterministic existence of a cone-kernel point from positive dual
   support. For d > 0, kappa >= 1 and public matrices W_i (i < m): if for
   every nonzero coefficient vector y some P in the actual cone sphere
   paper_main_head_cone_sphere kappa has sum_i y_i <W_i, P> > 0, then some
   P in that cone sphere has <W_i, P> = 0 for every i.

   Proof. The objective g(S) = sum_i <W_i, S>^2 attains its minimum on the
   compact convex trace-one slice paper_main_cone_kernel_slice at some S_0
   (compact_EVT_min). Along a segment of the slice,
     g(S_0 + t (S - S_0)) = g(S_0) + t c + t^2 a,
   with y_i = <W_i, S_0>, c = 2 sum_i y_i (<W_i, S> - y_i) and a >= 0, so
   c >= 0 (pms_variational): sum_i y_i <W_i, S> >= g(S_0) on the slice. If
   g(S_0) > 0, the hypothesis for -y gives P with sum_i y_i <W_i, P> < 0,
   and P / Tr P lies in the slice: a contradiction. So g(S_0) = 0 and
   S_0 / |S_0|_F is the kernel point. The minimization is on the convex
   slice, never on the sphere. With m = 0 the hypothesis is vacuous and the
   conclusion is the nonemptiness of the cone sphere. A unit-y form and a
   positive head-support margin form follow. No separation theorem or
   existence conclusion is assumed. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryCompact PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadFeature PaperMainGeometryHeadSpectral PaperMainGeometryHeadWidth
  PaperMainGeometryHeadWidthCompact PaperMainConeKernelSlice.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* No return type annotation: Stdlib binds R_scope to R. *)
Definition paper_main_cone_kernel_objective d m (W : 'I_m -> 'M[R]_d) (S : 'M[R]_d) :=
  \sum_(i < m) paper_main_pairing (W i) S * paper_main_pairing (W i) S.

Lemma paper_main_cone_kernel_objective_ge0 d m (W : 'I_m -> 'M[R]_d) S :
  0 <= paper_main_cone_kernel_objective d m W S.
Proof. by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0. Qed.

Lemma paper_main_cone_kernel_objective_eq0 d m (W : 'I_m -> 'M[R]_d) S :
  paper_main_cone_kernel_objective d m W S = 0 -> forall i, paper_main_pairing (W i) S = 0.
Proof.
move=> H0 i.
have nn : forall k : 'I_m, true -> 0 <= paper_main_pairing (W k) S * paper_main_pairing (W k) S.
  by move=> k _; rewrite -expr2 sqr_ge0.
have Hall := psumr_eq0P nn H0.
by have := Hall i isT => /eqP; rewrite -expr2 sqrf_eq0 => /eqP.
Qed.

Lemma paper_main_cone_kernel_objective_continuous d m (W : 'I_m -> 'M[R]_d) :
  continuous (fun w : 'rV[R]_(d * d + 1) =>
    paper_main_cone_kernel_objective d m W (pmhw_S d w)).
Proof.
rewrite /paper_main_cone_kernel_objective.
apply: pmg_continuous_sum => i.
have Hc : continuous (fun w : 'rV[R]_(d * d + 1) => paper_main_pairing (W i) (pmhw_S d w)).
  rewrite /paper_main_pairing.
  apply: pmg_continuous_sum => k; apply: pmg_continuous_sum => l.
  by apply: pmg_continuousM; [exact: pmg_continuous_cst | exact: pmhw_S_continuous].
by apply: pmg_continuousM.
Qed.

Lemma paper_main_cone_kernel_objective_segment d m (W : 'I_m -> 'M[R]_d) (S0 S : 'M[R]_d)
    (t : R) :
  paper_main_cone_kernel_objective d m W (S0 + t *: (S - S0)) =
  paper_main_cone_kernel_objective d m W S0
  + t * (\sum_(i < m) (paper_main_pairing (W i) S0 *
                        (paper_main_pairing (W i) S - paper_main_pairing (W i) S0)
                      + paper_main_pairing (W i) S0 *
                        (paper_main_pairing (W i) S - paper_main_pairing (W i) S0)))
  + t * t * (\sum_(i < m) (paper_main_pairing (W i) S - paper_main_pairing (W i) S0) *
                          (paper_main_pairing (W i) S - paper_main_pairing (W i) S0)).
Proof.
rewrite /paper_main_cone_kernel_objective !mulr_sumr -!big_split /=; apply: eq_bigr => i _.
have -> : paper_main_pairing (W i) (S0 + t *: (S - S0)) =
    paper_main_pairing (W i) S0 + t * (paper_main_pairing (W i) S - paper_main_pairing (W i) S0).
  by rewrite pmh_pairingDr paper_main_pairing_scale pmh_pairingBr.
exact: pms_sqr_expand.
Qed.

(* The minimum on the compact slice and the variational inequality. *)

Lemma paper_main_cone_kernel_minimizer d m (kappa : R) (W : 'I_m -> 'M[R]_d) :
  (0 < d)%N -> 1 <= kappa ->
  exists2 w0, paper_main_cone_kernel_slice d kappa w0 &
    forall w, paper_main_cone_kernel_slice d kappa w ->
      paper_main_cone_kernel_objective d m W (pmhw_S d w0) <=
      paper_main_cone_kernel_objective d m W (pmhw_S d w).
Proof.
move=> Hd Hk.
have Hw : {within paper_main_cone_kernel_slice d kappa,
    continuous (fun w => paper_main_cone_kernel_objective d m W (pmhw_S d w))}.
  by apply: continuous_subspaceT; exact: paper_main_cone_kernel_objective_continuous.
have [w0 Hw0 Hmin] := compact_EVT_min (paper_main_cone_kernel_slice_nonempty _ _ Hd Hk)
  (paper_main_cone_kernel_slice_compact _ _ Hd Hk) Hw.
exists w0; first by rewrite -in_setE.
by move=> w Hwin; apply: Hmin; rewrite in_setE.
Qed.

Lemma paper_main_cone_kernel_variational d m (kappa : R) (W : 'I_m -> 'M[R]_d) w0 w :
  paper_main_cone_kernel_slice d kappa w0 -> paper_main_cone_kernel_slice d kappa w ->
  (forall v, paper_main_cone_kernel_slice d kappa v ->
     paper_main_cone_kernel_objective d m W (pmhw_S d w0) <=
     paper_main_cone_kernel_objective d m W (pmhw_S d v)) ->
  paper_main_cone_kernel_objective d m W (pmhw_S d w0) <=
    \sum_(i < m) paper_main_pairing (W i) (pmhw_S d w0) * paper_main_pairing (W i) (pmhw_S d w).
Proof.
move=> Hw0 Hw Hmin.
have a0 : 0 <= \sum_(i < m)
    (paper_main_pairing (W i) (pmhw_S d w) - paper_main_pairing (W i) (pmhw_S d w0)) *
    (paper_main_pairing (W i) (pmhw_S d w) - paper_main_pairing (W i) (pmhw_S d w0)).
  by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
have Hvar : forall t : R, 0 < t -> t <= 1 ->
    0 <= t * (\sum_(i < m) (paper_main_pairing (W i) (pmhw_S d w0) *
           (paper_main_pairing (W i) (pmhw_S d w) - paper_main_pairing (W i) (pmhw_S d w0))
         + paper_main_pairing (W i) (pmhw_S d w0) *
           (paper_main_pairing (W i) (pmhw_S d w) - paper_main_pairing (W i) (pmhw_S d w0))))
    + t * t * (\sum_(i < m)
        (paper_main_pairing (W i) (pmhw_S d w) - paper_main_pairing (W i) (pmhw_S d w0)) *
        (paper_main_pairing (W i) (pmhw_S d w) - paper_main_pairing (W i) (pmhw_S d w0))).
  move=> t t0 t1.
  have Hseg := paper_main_cone_kernel_slice_segment d kappa w0 w t (ltW t0) t1 Hw0 Hw.
  have := Hmin _ Hseg.
  by rewrite pmhw_S_lift paper_main_cone_kernel_objective_segment -addrA lerDl.
have Hc := pms_variational _ _ a0 Hvar.
rewrite big_split /= -mulr2n pmulrn_lge0 // in Hc.
have E : \sum_(i < m) paper_main_pairing (W i) (pmhw_S d w0) *
      (paper_main_pairing (W i) (pmhw_S d w) - paper_main_pairing (W i) (pmhw_S d w0)) =
    \sum_(i < m) paper_main_pairing (W i) (pmhw_S d w0) * paper_main_pairing (W i) (pmhw_S d w) -
    \sum_(i < m) paper_main_pairing (W i) (pmhw_S d w0) * paper_main_pairing (W i) (pmhw_S d w0).
  by rewrite -sumrB; apply: eq_bigr => i _; rewrite mulrBr.
by rewrite E subr_ge0 in Hc.
Qed.

(* The existence theorem. *)

Theorem paper_main_cone_kernel_exists d m (kappa : R) (W : 'I_m -> 'M[R]_d) :
  (0 < d)%N -> 1 <= kappa ->
  (forall y : 'I_m -> R, (exists i, y i != 0) ->
    exists P, paper_main_head_cone_sphere kappa P /\
      0 < \sum_(i < m) y i * paper_main_pairing (W i) P) ->
  exists P, paper_main_head_cone_sphere kappa P /\
    forall i, paper_main_pairing (W i) P = 0.
Proof.
move=> Hd Hk Hpos.
have [w0 Hw0 Hmin] := paper_main_cone_kernel_minimizer d m kappa W Hd Hk.
have [HS0 Hsph] := paper_main_cone_kernel_sphere_of_slice _ _ _ Hd Hk Hw0.
case: (eqVneq (paper_main_cone_kernel_objective d m W (pmhw_S d w0)) 0) => [H0 | H0].
  exists ((paper_main_frobenius (pmhw_S d w0))^-1 *: pmhw_S d w0); split => // i.
  have Hi := paper_main_cone_kernel_objective_eq0 _ _ _ _ H0 i.
  by rewrite paper_main_pairing_scale Hi mulr0.
exfalso.
have Hex : ~ (forall i, paper_main_pairing (W i) (pmhw_S d w0) = 0).
  move=> Hall; move/eqP: H0; apply.
  by rewrite /paper_main_cone_kernel_objective big1 // => i _; rewrite Hall mulr0.
have [i Hi] : exists i, paper_main_pairing (W i) (pmhw_S d w0) <> 0.
  apply: contrapT => Hno; apply: Hex => i; apply: contrapT => Hi.
  by apply: Hno; exists i.
have Hy : exists i, - paper_main_pairing (W i) (pmhw_S d w0) != 0.
  by exists i; rewrite oppr_eq0; apply/eqP.
have [P [HP HPpos]] := Hpos (fun i => - paper_main_pairing (W i) (pmhw_S d w0)) Hy.
have [Ht [lam Hsl]] := paper_main_cone_kernel_slice_of_sphere _ _ _ Hd Hk HP.
have Hv := paper_main_cone_kernel_variational d m kappa W _ _ Hw0 Hsl Hmin.
rewrite pmhw_S_lift in Hv.
have Hobj : 0 < paper_main_cone_kernel_objective d m W (pmhw_S d w0).
  by rewrite lt0r H0 paper_main_cone_kernel_objective_ge0.
have Hc : 0 < (paper_main_trace P)^-1 by rewrite invr_gt0.
have E : \sum_(i < m) paper_main_pairing (W i) (pmhw_S d w0) *
      paper_main_pairing (W i) ((paper_main_trace P)^-1 *: P) =
    - ((paper_main_trace P)^-1 * \sum_(i < m)
      - paper_main_pairing (W i) (pmhw_S d w0) * paper_main_pairing (W i) P).
  rewrite mulr_sumr -sumrN; apply: eq_bigr => k _.
  by rewrite paper_main_pairing_scale; ring.
rewrite E in Hv.
have HX : 0 < (paper_main_trace P)^-1 * \sum_(i < m)
    - paper_main_pairing (W i) (pmhw_S d w0) * paper_main_pairing (W i) P.
  by apply: mulr_gt0.
have := lt_le_trans Hobj Hv; rewrite oppr_gt0 => HnX.
by have := lt_trans HX HnX; rewrite ltxx.
Qed.

(* Zero rows: the conclusion is the nonemptiness of the cone sphere. *)
Corollary paper_main_cone_kernel_exists_zero d (kappa : R) (W : 'I_0 -> 'M[R]_d) :
  (0 < d)%N -> 1 <= kappa ->
  exists P, paper_main_head_cone_sphere kappa P /\
    forall i, paper_main_pairing (W i) P = 0.
Proof.
move=> Hd Hk; apply: paper_main_cone_kernel_exists => // y [i _].
by case: i.
Qed.

(* Unit coefficient vectors suffice. *)
Theorem paper_main_cone_kernel_exists_unit d m (kappa : R) (W : 'I_m -> 'M[R]_d) :
  (0 < d)%N -> 1 <= kappa ->
  (forall y : 'I_m -> R, \sum_(i < m) y i ^+ 2 = 1 ->
    exists P, paper_main_head_cone_sphere kappa P /\
      0 < \sum_(i < m) y i * paper_main_pairing (W i) P) ->
  exists P, paper_main_head_cone_sphere kappa P /\
    forall i, paper_main_pairing (W i) P = 0.
Proof.
move=> Hd Hk Hunit; apply: paper_main_cone_kernel_exists => // y [i Hi].
set s := \sum_(k < m) y k ^+ 2.
have Hs0 : 0 < s.
  rewrite /s (bigD1 i) //= ltr_pwDl //.
    by rewrite lt0r sqrf_eq0 Hi sqr_ge0.
  by apply: sumr_ge0 => k _; rewrite sqr_ge0.
set r := Num.sqrt s.
have Hr : 0 < r by rewrite /r sqrtr_gt0.
have Hr2 : r ^+ 2 = s by rewrite /r sqr_sqrtr // ltW.
have Hyu : \sum_(k < m) (r^-1 * y k) ^+ 2 = 1.
  under eq_bigr do rewrite exprMn.
  by rewrite -mulr_sumr -/s -Hr2 exprVn mulVf // expf_neq0 // gt_eqF.
have [P [HP HPpos]] := Hunit (fun k => r^-1 * y k) Hyu.
exists P; split => //.
have E : \sum_(k < m) y k * paper_main_pairing (W k) P =
    r * \sum_(k < m) (r^-1 * y k) * paper_main_pairing (W k) P.
  rewrite mulr_sumr; apply: eq_bigr => k _.
  by rewrite !mulrA mulfV ?mul1r // gt_eqF.
by rewrite E; apply: mulr_gt0.
Qed.

(* A positive head-support margin gives the hypothesis. *)
Theorem paper_main_cone_kernel_exists_support d m (kappa : R) (W : 'I_m -> 'M[R]_d) :
  (0 < d)%N -> 1 <= kappa ->
  (forall y : 'I_m -> R, \sum_(i < m) y i ^+ 2 = 1 ->
    0 < paper_main_head_support (\sum_(i < m) y i *: W i) (paper_main_head_cone_sphere kappa)) ->
  exists P, paper_main_head_cone_sphere kappa P /\
    forall i, paper_main_pairing (W i) P = 0.
Proof.
move=> Hd Hk Hsupp; apply: paper_main_cone_kernel_exists_unit => // y Hy.
apply: contrapT => Hno.
have HN := paper_main_head_cone_sphere_nonempty _ kappa Hd Hk.
have Hle : paper_main_head_support (\sum_(i < m) y i *: W i)
    (paper_main_head_cone_sphere kappa) <= 0.
  apply: ge_sup.
    by exists (paper_main_pairing (\sum_(i < m) y i *: W i) ((Num.sqrt d%:R)^-1 *: 1%:M)),
      ((Num.sqrt d%:R)^-1 *: 1%:M).
  move=> _ [P HP <-]; rewrite pmh_pairing_suml.
  by rewrite leNgt; apply/negP => Hgt; apply: Hno; exists P.
by have := lt_le_trans (Hsupp y Hy) Hle; rewrite ltxx.
Qed.
