(* Deterministic geometry for the main results of the paper, part 3: for
   d > 0, the fit event of (P) and the balanced positive definite event of
   cor:alternative are mutually exclusive, as in the exclusion half of
   lem:homogeneous (ii) (paper line 700), with no spanning hypothesis; and
   the honest degenerate cases: at d = 0 both events hold, and at n = 0
   with d > 0 the fit event holds and the balanced event fails.

   The argument: if S >= 0 fits, x_i^T S x_i = d for every i, and M = sum_i
   y_i x_i x_i^T > 0 with sum_i y_i = 0, then <S, M> = sum_i y_i x_i^T S x_i
   = d sum_i y_i = 0, while <M, S> > 0 for S nonzero (part 2). S is nonzero
   because x_0^T S x_0 = d > 0 when n > 0, and when n = 0 the matrix M is
   0 and is not positive definite in dimension d > 0.

   Internal proof workstream (analysis/reports/PROGRESS-main-geometry.md);
   not part of any contract. No Axiom, Parameter or Admitted. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryGram.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* The zero matrix is positive semidefinite. *)
Lemma paper_main_psd0 d : paper_main_psd (0 : 'M[R]_d).
Proof.
split=> [i j | v]; first by rewrite !mxE.
by rewrite paper_main_quadratic_formE mulmx0 mul0mx mxE lexx.
Qed.

(* In dimension d > 0, the zero matrix is not positive definite. *)
Lemma paper_main_pd_neq0 d (M : 'M[R]_d) : (0 < d)%nat -> paper_main_pd M -> M != 0.
Proof.
case: d M => [|d] M // _ [_ HM]; apply/eqP => M0.
have e0 : (delta_mx 0 0 : 'cV[R]_d.+1) != 0.
  by apply/eqP => /matrixP/(_ 0 0)/eqP; rewrite !mxE !eqxx pnatr_eq0.
have := HM _ e0.
by rewrite M0 paper_main_quadratic_formE mulmx0 mul0mx mxE ltxx.
Qed.

(* The pairing of a fit with a weighted sum of the outer products x_i x_i^T
   is d times the sum of the weights. *)
Lemma paper_main_fit_pairing n d (x : paper_main_sample n d) (S : 'M[R]_d)
    (y : 'I_n -> R) :
  (forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = d%:R) ->
  paper_main_pairing S
    (\sum_(i < n) y i *: (paper_main_point x i *m (paper_main_point x i)^T)) =
  d%:R * \sum_(i < n) y i.
Proof.
move=> Hfit; rewrite paper_main_pairing_sum mulr_sumr; apply: eq_bigr => i _.
by rewrite paper_main_pairing_outer Hfit mulrC.
Qed.

(* Mutual exclusion for d > 0. *)
Theorem paper_main_fit_balanced_exclusive n d (x : paper_main_sample n d) :
  (0 < d)%nat ->
  paper_main_fit_event n d x -> paper_main_balanced_pd_event n d x -> False.
Proof.
move=> d0 [S [HS Hfit]] [y [Hy HM]].
have Hpair : paper_main_pairing S
    (\sum_(i < n) y i *: (paper_main_point x i *m (paper_main_point x i)^T)) = 0.
  by rewrite (paper_main_fit_pairing _ _ _ _ _ Hfit) Hy mulr0.
have S0 : S != 0.
  case: n x y Hy HM Hfit Hpair => [|n'] x y Hy HM Hfit Hpair.
    by have := paper_main_pd_neq0 _ _ d0 HM; rewrite big_ord0 eqxx.
  apply: (paper_main_form_neq0 _ S (paper_main_point x (ord0 : 'I_n'.+1))).
  by rewrite (Hfit ord0) pnatr_eq0 -lt0n.
have := paper_main_pairing_pd_psd_gt0 _ _ _ HM HS S0.
by rewrite paper_main_pairingC Hpair ltxx.
Qed.

(* The degenerate cases, stated honestly. *)

(* d = 0: every sample is in both events. *)
Lemma paper_main_fit_event_dim0 n (x : paper_main_sample n 0) :
  paper_main_fit_event n 0 x.
Proof.
exists 0; split; first exact: paper_main_psd0.
by move=> i; rewrite paper_main_quadratic_formE mulmx0 mul0mx mxE.
Qed.

Lemma paper_main_balanced_event_dim0 n (x : paper_main_sample n 0) :
  paper_main_balanced_pd_event n 0 x.
Proof.
exists (fun _ => 0); split; first by rewrite big1.
split=> [i j | v v0]; first by have := ltn_ord i; rewrite ltn0.
by move: v0; rewrite [v]flatmx0 eqxx.
Qed.

(* n = 0: the fit event holds (nothing to fit) and, for d > 0, the
   balanced event fails (the empty combination is the zero matrix). *)
Lemma paper_main_fit_event_n0 d (x : paper_main_sample 0 d) :
  paper_main_fit_event 0 d x.
Proof.
exists 0; split; first exact: paper_main_psd0.
by move=> i; have := ltn_ord i; rewrite ltn0.
Qed.

Lemma paper_main_balanced_event_n0 d (x : paper_main_sample 0 d) :
  (0 < d)%nat -> ~ paper_main_balanced_pd_event 0 d x.
Proof.
move=> d0 [y [_ HM]].
by have := paper_main_pd_neq0 _ _ d0 HM; rewrite big_ord0 eqxx.
Qed.
