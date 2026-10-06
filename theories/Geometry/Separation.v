(* Deterministic geometry for the main results of the paper, part 6: the
   existence half of lem:homogeneous (ii) (paper lines 700-737), by a
   variational argument on the compact set of trace-one positive
   semidefinite matrices of part 5, and the resulting alternatives.

   Setting. x is a sample of n points of R^d, a_i(S) = x_i^T S x_i,
   abar(S) = (sum_i a_i(S)) / n and F(S) = sum_i (a_i(S) - abar(S))^2, the
   squared norm of the paper's D_X S (the values a_i(S) projected to the
   complement of the all-ones vector). Suppose no nonzero S >= 0 has all
   a_i(S) equal. F attains its minimum on {S >= 0, Tr S = 1} at some S_0
   (part 5), F(S_0) > 0 (else S_0 would be a nonzero PSD kernel element),
   and y_i := a_i(S_0) - abar(S_0) sums to 0. For S in the set and t in
   (0, 1], S_0 + t (S - S_0) is in the set, so
     F(S_0) <= F(S_0 + t (S - S_0)) = F(S_0) + t c + t^2 a,
   with c = 2 sum_i y_i (z_i - y_i), z_i = a_i(S) - abar(S), and a >= 0;
   letting t go to 0 gives c >= 0, that is
     sum_i y_i a_i(S) = sum_i y_i z_i >= sum_i y_i^2 = F(S_0) > 0,
   the paper's obtuse-angle inequality <k_0, k> >= |k_0|^2 at the nearest
   point k_0 of D_X({S >= 0, Tr S = 1}) to the origin. Testing this with
   S = w w^T / (w^T w) gives w^T (sum_i y_i x_i x_i^T) w > 0 for w <> 0.

   - paper_main_homogeneous_existence: for every n and d, if every S >= 0
     with all a_i(S) equal is 0, the balanced positive definite event
     holds. At d = 0 this is paper_main_balanced_event_dim0; at n = 0 and
     d > 0 the hypothesis is contradictory (e e^T is in the empty kernel).
   - paper_main_homogeneous_alternative: for every n and d, some nonzero
     S >= 0 is in the kernel, or the balanced event holds.
   - paper_main_fit_alternative: for d > 0 and a spanning sample, the fit
     event holds if and only if the balanced event fails. *)

From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Gram Geometry.Exclusion Geometry.Homogeneous Geometry.Compact.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Scalar facts. The ring identities are proved in Stdlib's vocabulary,
   whose operations are convertible to MathComp's at R. *)

Lemma pms_sqr_expand (y u t : R) :
  (y + t * u) * (y + t * u) = y * y + t * (y * u + y * u) + t * t * (u * u).
Proof.
have H : Rmult (Rplus y (Rmult t u)) (Rplus y (Rmult t u)) =
  Rplus (Rplus (Rmult y y) (Rmult t (Rplus (Rmult y u) (Rmult y u))))
        (Rmult (Rmult t t) (Rmult u u)) by ring.
exact H.
Qed.

Lemma pms_mean_ring (a b t k : R) :
  (a + t * (b - a)) * k = a * k + t * (b * k - a * k).
Proof.
have H : Rmult (Rplus a (Rmult t (Rminus b a))) k =
  Rplus (Rmult a k) (Rmult t (Rminus (Rmult b k) (Rmult a k))) by ring.
exact H.
Qed.

Lemma pms_dev_ring (a b ma mb t : R) :
  (a + t * (b - a)) - (ma + t * (mb - ma)) = (a - ma) + t * ((b - mb) - (a - ma)).
Proof.
have H : Rminus (Rplus a (Rmult t (Rminus b a))) (Rplus ma (Rmult t (Rminus mb ma))) =
  Rplus (Rminus a ma) (Rmult t (Rminus (Rminus b mb) (Rminus a ma))) by ring.
exact H.
Qed.

(* If 0 <= t c + t^2 a for every t in (0, 1] and a >= 0, then c >= 0:
   given e > 0, t = e / (a + e) gives 0 <= c + t a <= c + e. *)
Lemma pms_variational (a c : R) : 0 <= a ->
  (forall t : R, 0 < t -> t <= 1 -> 0 <= t * c + t * t * a) -> 0 <= c.
Proof.
move=> a0 H; apply/ler_addgt0Pr => e e0.
have ae0 : 0 < a + e by exact: ltr_wpDl a0 e0.
set t := e / (a + e).
have t0 : 0 < t by exact: divr_gt0.
have t1 : t <= 1 by rewrite /t ler_pdivrMr // mul1r lerDr.
have ta : t * a <= e.
  rewrite -[leRHS](divfK (lt0r_neq0 ae0) e) -/t.
  by apply: (ler_wpM2l (ltW t0)); rewrite lerDl ltW.
have := H t t0 t1; rewrite -mulrA -mulrDr pmulr_rge0 // => Hc.
by apply: le_trans Hc _; rewrite lerD2l.
Qed.

(* 2. Linear algebra of the form, the trace and rank-one matrices. *)

Section Forms.
Variable d : nat.
Implicit Types (S M : 'M[R]_d) (v w : 'cV[R]_d).

Lemma pms_formD S M w :
  paper_main_quadratic_form (S + M) w =
  paper_main_quadratic_form S w + paper_main_quadratic_form M w.
Proof.
rewrite !paper_main_quadratic_formE mulmxDr mulmxDl.
by rewrite [fun_of_matrix (_ + _) _ _]mxE.
Qed.

Lemma pms_formB S M w :
  paper_main_quadratic_form (S - M) w =
  paper_main_quadratic_form S w - paper_main_quadratic_form M w.
Proof.
rewrite !paper_main_quadratic_formE mulmxBr mulmxBl.
by rewrite [fun_of_matrix (_ - _) _ _]mxE [fun_of_matrix (- _) _ _]mxE.
Qed.

Lemma pms_form_sum n (c : 'I_n -> R) (A : 'I_n -> 'M[R]_d) w :
  paper_main_quadratic_form (\sum_(i < n) c i *: A i) w =
  \sum_(i < n) c i * paper_main_quadratic_form (A i) w.
Proof.
rewrite -paper_main_pairing_outer paper_main_pairingC paper_main_pairing_sum.
by apply: eq_bigr => i _; rewrite paper_main_pairingC paper_main_pairing_outer.
Qed.

Lemma pms_psd_add S M : paper_main_psd S -> paper_main_psd M -> paper_main_psd (S + M).
Proof.
move=> [Hs Hp] [Ms Mp]; split=> [i j | w]; first by rewrite !mxE Hs Ms.
by rewrite pms_formD addr_ge0.
Qed.

Lemma pms_traceD S M : paper_main_trace (S + M) = paper_main_trace S + paper_main_trace M.
Proof. by rewrite /paper_main_trace -big_split /=; apply: eq_bigr => i _; rewrite mxE. Qed.

Lemma pms_traceB S M : paper_main_trace (S - M) = paper_main_trace S - paper_main_trace M.
Proof. by rewrite /paper_main_trace -sumrB; apply: eq_bigr => i _; rewrite !mxE. Qed.

Lemma pms_trace_scale (a : R) S : paper_main_trace (a *: S) = a * paper_main_trace S.
Proof. by rewrite /paper_main_trace mulr_sumr; apply: eq_bigr => i _; rewrite mxE. Qed.

Lemma pms_trace0 : paper_main_trace (0 : 'M[R]_d) = 0.
Proof. by rewrite /paper_main_trace big1 // => i _; rewrite mxE. Qed.

(* The segment from S to M stays in the trace-one PSD set. *)
Lemma pms_seg_psd S M (t : R) : 0 <= t -> t <= 1 ->
  paper_main_psd S -> paper_main_psd M -> paper_main_psd (S + t *: (M - S)).
Proof.
move=> t0 t1 HS HM.
have -> : S + t *: (M - S) = (1 - t) *: S + t *: M.
  by rewrite scalerBr addrA addrAC scalerBl scale1r.
apply: pms_psd_add; apply: paper_main_psd_scale => //.
by rewrite subr_ge0.
Qed.

Lemma pms_seg_trace S M (t : R) :
  paper_main_trace S = 1 -> paper_main_trace M = 1 ->
  paper_main_trace (S + t *: (M - S)) = 1.
Proof.
by move=> HS HM; rewrite pms_traceD pms_trace_scale pms_traceB HS HM subrr mulr0 addr0.
Qed.

Lemma pms_seg_in S M (t : R) : 0 <= t -> t <= 1 ->
  paper_main_psd S -> paper_main_trace S = 1 ->
  paper_main_psd M -> paper_main_trace M = 1 ->
  pmg_trace_one d (mxvec (S + t *: (M - S))).
Proof.
move=> t0 t1 HS trS HM trM; rewrite /pmg_trace_one /= mxvecK.
by split; [exact: pms_seg_psd | exact: pms_seg_trace].
Qed.

(* Rank-one matrices: the form is symmetric in the two vectors, the trace
   of w w^T is w^T w, positive for w <> 0. *)
Lemma pms_form_rank1 w v :
  paper_main_quadratic_form (w *m w^T) v = paper_main_quadratic_form (v *m v^T) w.
Proof.
by rewrite !paper_main_quadratic_formE !paper_main_form_rank1E paper_main_inner_sym.
Qed.

Lemma pms_sqnorm w : (w^T *m w) 0 0 = \sum_(i < d) w i 0 * w i 0.
Proof. by rewrite mxE; apply: eq_bigr => i _; rewrite mxE. Qed.

Lemma pms_trace_rank1 w : paper_main_trace (w *m w^T) = (w^T *m w) 0 0.
Proof.
rewrite pms_sqnorm /paper_main_trace; apply: eq_bigr => i _.
by rewrite mxE big_ord1 mxE.
Qed.

Lemma pms_sqnorm_gt0 w : w != 0 -> 0 < (w^T *m w) 0 0.
Proof.
move=> w0; rewrite pms_sqnorm lt0r; apply/andP; split.
  apply/eqP => H0; move/negP: w0; apply; apply/eqP; apply/matrixP => i j.
  have nn : forall k : 'I_d, true -> 0 <= w k 0 * w k 0.
    by move=> k _; rewrite -expr2 sqr_ge0.
  have Hall := psumr_eq0P nn H0.
  rewrite [j]ord1 [RHS]mxE.
  by have := Hall i isT => /eqP; rewrite -expr2 sqrf_eq0 => /eqP.
by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
Qed.

End Forms.

(* 3. The objective F and its behaviour along segments. *)

Section Objective.
Variables (n d : nat) (x : paper_main_sample n d).
Implicit Types (S M : 'M[R]_d).

(* No return type annotation ": R" on these definitions: Stdlib binds
   R_scope to the type R, so an annotated body is parsed with Rminus and
   Rdiv, which MathComp's rewriting lemmas do not match. *)
Definition pms_value S (i : 'I_n) :=
  paper_main_quadratic_form S (paper_main_point x i).
Definition pms_mean S := (\sum_(i < n) pms_value S i) / n%:R.
Definition pms_dev S (i : 'I_n) := pms_value S i - pms_mean S.
Definition pms_obj S := \sum_(i < n) pms_dev S i * pms_dev S i.

Lemma pms_obj_ge0 S : 0 <= pms_obj S.
Proof. by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0. Qed.

Lemma pms_dev_sum S : (0 < n)%nat -> \sum_(i < n) pms_dev S i = 0.
Proof.
move=> n0; rewrite /pms_dev sumrB sumr_const card_ord -mulr_natl /pms_mean.
by rewrite [n%:R * _]mulrC divfK ?subrr // pnatr_eq0 -lt0n.
Qed.

Lemma pms_obj_eq0 S : pms_obj S = 0 -> paper_main_kernel x S.
Proof.
move=> H0; exists (pms_mean S) => i.
have nn : forall k : 'I_n, true -> 0 <= pms_dev S k * pms_dev S k.
  by move=> k _; rewrite -expr2 sqr_ge0.
have Hall := psumr_eq0P nn H0.
by have := Hall i isT => /eqP; rewrite -expr2 sqrf_eq0 /pms_dev subr_eq0 => /eqP <-.
Qed.

Lemma pms_value_continuous (i : 'I_n) :
  continuous (fun v : 'rV[R]_(d * d) => pms_value (vec_mx v) i).
Proof. rewrite /pms_value; exact: pmg_form_continuous. Qed.

Lemma pms_mean_continuous :
  continuous (fun v : 'rV[R]_(d * d) => pms_mean (vec_mx v)).
Proof.
rewrite /pms_mean; apply: pmg_continuousM; last exact: pmg_continuous_cst.
by apply: pmg_continuous_sum => j; exact: pms_value_continuous.
Qed.

Lemma pms_dev_continuous (i : 'I_n) :
  continuous (fun v : 'rV[R]_(d * d) => pms_dev (vec_mx v) i).
Proof.
rewrite /pms_dev; apply: pmg_continuousB.
  exact: pms_value_continuous.
exact: pms_mean_continuous.
Qed.

Lemma pms_obj_continuous :
  continuous (fun v : 'rV[R]_(d * d) => pms_obj (vec_mx v)).
Proof.
rewrite /pms_obj; apply: pmg_continuous_sum => i.
by apply: pmg_continuousM; exact: pms_dev_continuous.
Qed.

Lemma pms_value_seg S M (t : R) (i : 'I_n) :
  pms_value (S + t *: (M - S)) i = pms_value S i + t * (pms_value M i - pms_value S i).
Proof. by rewrite /pms_value pms_formD paper_main_form_scale pms_formB. Qed.

Lemma pms_mean_seg S M (t : R) :
  pms_mean (S + t *: (M - S)) = pms_mean S + t * (pms_mean M - pms_mean S).
Proof.
rewrite /pms_mean.
have -> : \sum_(i < n) pms_value (S + t *: (M - S)) i =
    \sum_(i < n) pms_value S i + t * (\sum_(i < n) pms_value M i - \sum_(i < n) pms_value S i).
  by rewrite -sumrB mulr_sumr -big_split /=; apply: eq_bigr => i _; rewrite pms_value_seg.
exact: pms_mean_ring.
Qed.

Lemma pms_dev_seg S M (t : R) (i : 'I_n) :
  pms_dev (S + t *: (M - S)) i = pms_dev S i + t * (pms_dev M i - pms_dev S i).
Proof. by rewrite /pms_dev pms_value_seg pms_mean_seg pms_dev_ring. Qed.

Lemma pms_obj_seg S M (t : R) :
  pms_obj (S + t *: (M - S)) =
  pms_obj S
  + t * (\sum_(i < n) (pms_dev S i * (pms_dev M i - pms_dev S i)
                       + pms_dev S i * (pms_dev M i - pms_dev S i)))
  + t * t * (\sum_(i < n) (pms_dev M i - pms_dev S i) * (pms_dev M i - pms_dev S i)).
Proof.
rewrite /pms_obj !mulr_sumr -!big_split /=; apply: eq_bigr => i _.
by rewrite pms_dev_seg pms_sqr_expand.
Qed.

(* The separating weights: y_i = a_i(S_0) - abar(S_0) for a minimizer S_0
   of F on the trace-one PSD set, and c = F(S_0) > 0 with
   c <= sum_i y_i a_i(S) for every S >= 0 of trace 1. *)
Lemma pms_separation :
  (0 < d)%nat -> (0 < n)%nat ->
  (forall S, paper_main_psd S -> paper_main_kernel x S -> S = 0) ->
  exists (y : 'I_n -> R) (c : R), \sum_(i < n) y i = 0 /\ 0 < c /\
    forall S, paper_main_psd S -> paper_main_trace S = 1 ->
      c <= \sum_(i < n) y i * paper_main_quadratic_form S (paper_main_point x i).
Proof.
move=> d0 n0 Hno.
have [v0 Hv0 Hmin] := pmg_trace_one_min _ _ d0 pms_obj_continuous.
move: Hmin => /= Hmin.
have [HS0 Htr0] : paper_main_psd (vec_mx v0) /\ paper_main_trace (vec_mx v0) = 1 := Hv0.
set S0 : 'M[R]_d := vec_mx v0 in Hmin HS0 Htr0 *.
exists (pms_dev S0), (pms_obj S0); split; first exact: pms_dev_sum.
have F0 : 0 < pms_obj S0.
  rewrite lt0r pms_obj_ge0 andbT; apply/eqP => HF.
  have S00 := Hno S0 HS0 (pms_obj_eq0 _ HF).
  by move: Htr0; rewrite S00 pms_trace0 => /eqP; rewrite eq_sym oner_eq0.
split=> // S HS HtrS.
have a0 : 0 <= \sum_(i < n) (pms_dev S i - pms_dev S0 i) * (pms_dev S i - pms_dev S0 i).
  by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
have Hvar : forall t : R, 0 < t -> t <= 1 ->
    0 <= t * (\sum_(i < n) (pms_dev S0 i * (pms_dev S i - pms_dev S0 i)
                            + pms_dev S0 i * (pms_dev S i - pms_dev S0 i)))
         + t * t * (\sum_(i < n) (pms_dev S i - pms_dev S0 i) * (pms_dev S i - pms_dev S0 i)).
  move=> t t0 t1.
  have := Hmin _ (pms_seg_in _ S0 S t (ltW t0) t1 HS0 Htr0 HS HtrS).
  by rewrite mxvecK pms_obj_seg -addrA lerDl.
have Hc := pms_variational _ _ a0 Hvar.
rewrite big_split /= -mulr2n pmulrn_lge0 // in Hc.
have E : \sum_(i < n) pms_dev S0 i * (pms_dev S i - pms_dev S0 i) =
    \sum_(i < n) pms_dev S0 i * pms_dev S i - \sum_(i < n) pms_dev S0 i * pms_dev S0 i.
  by rewrite -sumrB; apply: eq_bigr => i _; rewrite mulrBr.
rewrite E subr_ge0 in Hc.
have Hyz : \sum_(i < n) pms_dev S0 i * pms_dev S i =
    \sum_(i < n) pms_dev S0 i * pms_value S i.
  have -> : \sum_(i < n) pms_dev S0 i * pms_dev S i =
      \sum_(i < n) pms_dev S0 i * pms_value S i - (\sum_(i < n) pms_dev S0 i) * pms_mean S.
    by rewrite mulr_suml -sumrB; apply: eq_bigr => i _; rewrite /pms_dev mulrBr.
  by rewrite pms_dev_sum // mul0r subr0.
rewrite /pms_obj; apply: le_trans Hc _; rewrite Hyz /pms_value; exact: lexx.
Qed.

End Objective.

(* 4. The existence half and the alternatives. *)

Theorem paper_main_homogeneous_existence n d (x : paper_main_sample n d) :
  (forall S : 'M[R]_d, paper_main_psd S -> paper_main_kernel x S -> S = 0) ->
  paper_main_balanced_pd_event n d x.
Proof.
move=> Hno.
case: d x Hno => [|d'] x Hno; first exact: paper_main_balanced_event_dim0.
case: n x Hno => [|n'] x Hno.
  exfalso; set e : 'cV[R]_d'.+1 := delta_mx ord0 ord0.
  have Hk : paper_main_kernel x (e *m e^T).
    by exists 0 => i; have := ltn_ord i; rewrite ltn0.
  have := Hno _ (paper_main_psd_rank1 _ e) Hk => /matrixP/(_ ord0 ord0)/eqP.
  by rewrite mxE big_ord1 !mxE !eqxx mulf_eq0 !pnatr_eq0.
have [y [c [Hy [c0 Hsep]]]] := pms_separation _ _ x (ltn0Sn _) (ltn0Sn _) Hno.
exists y; split=> //.
set M := \sum_(i < n'.+1) y i *: (paper_main_point x i *m (paper_main_point x i)^T).
split=> [i j | w w0].
  rewrite !summxE; apply: eq_bigr => k _; rewrite !mxE !big_ord1 !mxE.
  by congr (_ * _); exact: mulrC.
set nw : R := (w^T *m w) 0 0.
have nw0 : 0 < nw by exact: pms_sqnorm_gt0.
set Sw : 'M[R]_d'.+1 := nw^-1 *: (w *m w^T).
have HSw : paper_main_psd Sw.
  by apply: paper_main_psd_scale; [rewrite invr_ge0 ltW | exact: paper_main_psd_rank1].
have HtrSw : paper_main_trace Sw = 1.
  by rewrite /Sw pms_trace_scale pms_trace_rank1 -/nw mulVf // gt_eqF.
have := Hsep Sw HSw HtrSw.
have -> : \sum_(i < n'.+1) y i * paper_main_quadratic_form Sw (paper_main_point x i)
    = nw^-1 * paper_main_quadratic_form M w.
  rewrite /M pms_form_sum mulr_sumr; apply: eq_bigr => i _.
  by rewrite /Sw paper_main_form_scale pms_form_rank1 mulrCA.
move=> Hle; have := lt_le_trans c0 Hle.
by rewrite pmulr_rgt0 // invr_gt0.
Qed.

(* lem:homogeneous (ii): one of the alternatives holds; part 4 shows that
   not both do. *)
Theorem paper_main_homogeneous_alternative n d (x : paper_main_sample n d) :
  (exists S : 'M[R]_d, paper_main_psd S /\ S != 0 /\ paper_main_kernel x S)
  \/ paper_main_balanced_pd_event n d x.
Proof.
case: (pselect (exists S : 'M[R]_d, paper_main_psd S /\ S != 0 /\ paper_main_kernel x S)).
  by left.
move=> Hno; right; apply: paper_main_homogeneous_existence => S HS Hk.
case: (eqVneq S 0) => // S0.
by exfalso; apply: Hno; exists S.
Qed.

(* For d > 0 and a spanning sample: the fit event holds exactly when the
   balanced positive definite event fails. *)
Theorem paper_main_fit_alternative n d (x : paper_main_sample n d) :
  (0 < d)%nat -> paper_main_spanning x ->
  (paper_main_fit_event n d x <-> ~ paper_main_balanced_pd_event n d x).
Proof.
move=> d0 Hspan; split=> [Hfit Hbal | Hnot].
  exact: (paper_main_fit_balanced_exclusive _ _ _ d0 Hfit Hbal).
apply/(paper_main_homogeneous_kernel _ _ _ d0 Hspan).
by case: (paper_main_homogeneous_alternative n d x) => // /Hnot.
Qed.
