(* Deterministic geometry for the main results of the paper, part 4: the
   homogeneous formulation of lem:homogeneous (paper lines 677-737).

   Setting. x is a sample of n points of R^d. The spanning hypothesis of
   the lemma, "x_1, ..., x_n span R^d", is written as: a vector orthogonal
   to every x_i is 0 (paper_main_spanning). The kernel of the paper's map
   D_X (the values x_i^T S x_i projected to the complement of the all-ones
   vector) is the set of S whose values x_i^T S x_i are all equal
   (paper_main_kernel).

   - (i), kernel form: for d > 0 and a spanning sample, (P) is feasible
     if and only if some nonzero S >= 0 is in the kernel.
   - (i), witness form: the same, with S of Frobenius norm 1 and
     Q_x(S) = b 1, that is x_i^T S x_i - Tr S = b for every i.
   - (ii), exclusion half, in kernel form and for every n and d: a nonzero
     S >= 0 in the kernel and a balanced positive definite combination
     cannot coexist, since <S, sum_i y_i x_i x_i^T> = c sum_i y_i = 0 while
     the pairing is positive (part 2). No spanning is used here.
   - (ii), existence half: not in this module; see the progress report.

   Internal proof workstream (analysis/reports/PROGRESS-main-geometry.md);
   not part of any contract. No Axiom, Parameter or Admitted. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryGram PaperMainGeometryExclusion.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* The points x_i span R^d: only 0 is orthogonal to all of them. *)
Definition paper_main_spanning {n d : nat} (x : paper_main_sample n d) : Prop :=
  forall v : 'cV[R]_d,
    (forall i : 'I_n, (paper_main_point x i)^T *m v = 0) -> v = 0.

(* S is in the kernel of D_X: its values at the points are all equal. *)
Definition paper_main_kernel {n d : nat} (x : paper_main_sample n d) (S : 'M[R]_d) : Prop :=
  exists c : R, forall i : 'I_n,
    paper_main_quadratic_form S (paper_main_point x i) = c.

(* The Frobenius norm. *)
Definition paper_main_frobenius {d : nat} (S : 'M[R]_d) : R :=
  Num.sqrt (paper_main_pairing S S).

Section Scaling.
Variable d : nat.
Implicit Types (S M : 'M[R]_d) (v s : 'cV[R]_d).

Lemma paper_main_form_scale (a : R) S v :
  paper_main_quadratic_form (a *: S) v = a * paper_main_quadratic_form S v.
Proof.
rewrite !paper_main_quadratic_formE -scalemxAr -scalemxAl.
by rewrite [fun_of_matrix (_ *: _) _ _]mxE.
Qed.

Lemma paper_main_symmetric_scale (a : R) S :
  paper_main_symmetric S -> paper_main_symmetric (a *: S).
Proof. by move=> Hs i j; rewrite !mxE Hs. Qed.

Lemma paper_main_psd_scale (a : R) S :
  0 <= a -> paper_main_psd S -> paper_main_psd (a *: S).
Proof.
move=> a0 [Hs Hpos]; split; first exact: paper_main_symmetric_scale.
by move=> v; rewrite paper_main_form_scale mulr_ge0.
Qed.

Lemma paper_main_pairing_scale (a : R) S M :
  paper_main_pairing S (a *: M) = a * paper_main_pairing S M.
Proof.
rewrite /paper_main_pairing mulr_sumr; apply: eq_bigr => i _.
rewrite mulr_sumr; apply: eq_bigr => j _.
by rewrite mxE mulrCA.
Qed.

(* <S, S> is a sum of squares: nonnegative, and zero only for S = 0. *)
Lemma paper_main_pairing_self_ge0 S : 0 <= paper_main_pairing S S.
Proof.
apply: sumr_ge0 => i _; apply: sumr_ge0 => j _.
by rewrite -expr2 sqr_ge0.
Qed.

Lemma paper_main_pairing_self_eq0 S : paper_main_pairing S S = 0 -> S = 0.
Proof.
move=> H0.
have Hrows : forall i, true -> \sum_(j < d) S i j * S i j = 0.
  apply: (psumr_eq0P _ H0) => i _; apply: sumr_ge0 => j _; exact: sqr_ge0.
apply/matrixP => i j; rewrite [RHS]mxE.
have nn : forall k : 'I_d, true -> 0 <= S i k * S i k by move=> k _; exact: sqr_ge0.
have Hall := psumr_eq0P nn (Hrows i isT).
by have := Hall j isT => /eqP; rewrite -expr2 sqrf_eq0 => /eqP.
Qed.

Lemma paper_main_pairing_self_gt0 S : S != 0 -> 0 < paper_main_pairing S S.
Proof.
move=> S0; rewrite lt0r paper_main_pairing_self_ge0 andbT.
by apply/eqP => /paper_main_pairing_self_eq0 E; rewrite E eqxx in S0.
Qed.

(* Rank-one matrices are positive semidefinite. *)
Lemma paper_main_psd_rank1 s : paper_main_psd (s *m s^T).
Proof.
split=> [i j | v].
  by rewrite !mxE !big_ord1 !mxE mulrC.
by rewrite paper_main_quadratic_formE paper_main_form_rank1E sqr_ge0.
Qed.

End Scaling.

(* A positive semidefinite matrix vanishing on a spanning family is 0. *)
Lemma paper_main_psd_spanning_zero n d (x : paper_main_sample n d) (S : 'M[R]_d) :
  paper_main_spanning x -> paper_main_psd S ->
  (forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = 0) -> S = 0.
Proof.
move=> Hspan HS H0.
have Hs : S^T = S by apply/paper_main_symmetricP; case: HS.
have Hker (i : 'I_n) : S *m paper_main_point x i = 0.
  exact: (paper_main_psd_form_eq0 _ _ _ HS (H0 i)).
have Hv (v : 'cV[R]_d) : S *m v = 0.
  apply: Hspan => i; rewrite mulmxA.
  have -> : (paper_main_point x i)^T *m S = (S *m paper_main_point x i)^T.
    by rewrite trmx_mul Hs.
  by rewrite Hker trmx0 mul0mx.
apply/matrixP => i j; have := Hv (delta_mx j 0); rewrite -colE.
by move/matrixP/(_ i 0); rewrite [fun_of_matrix (col _ _) _ _]mxE ![fun_of_matrix 0 _ _]mxE.
Qed.

(* lem:homogeneous (i), kernel form. *)
Theorem paper_main_homogeneous_kernel n d (x : paper_main_sample n d) :
  (0 < d)%nat -> paper_main_spanning x ->
  (paper_main_fit_event n d x <->
   exists S : 'M[R]_d, paper_main_psd S /\ S != 0 /\ paper_main_kernel x S).
Proof.
move=> d0 Hspan; split.
- move=> [S [HS Hfit]].
  case: n x Hspan S HS Hfit => [|n'] x Hspan S HS Hfit.
    case: d d0 x Hspan S HS Hfit => [|d'] // _ x _ S _ _.
    exists ((delta_mx 0 0 : 'cV[R]_d'.+1) *m (delta_mx 0 0 : 'cV[R]_d'.+1)^T).
    split; first exact: paper_main_psd_rank1.
    split; last by exists 0 => i; have := ltn_ord i; rewrite ltn0.
    apply/eqP => /matrixP/(_ 0 0)/eqP.
    by rewrite mxE big_ord1 !mxE !eqxx mulf_eq0 !pnatr_eq0.
  exists S; split=> //; split; last by exists d%:R.
  apply: (paper_main_form_neq0 _ S (paper_main_point x (ord0 : 'I_n'.+1))).
  by rewrite (Hfit ord0) pnatr_eq0 -lt0n.
- move=> [S [HS [S0 [c Hc]]]].
  case: n x Hspan Hc => [|n'] x Hspan Hc; first exact: paper_main_fit_event_n0.
  have c0 : 0 <= c by rewrite -(Hc ord0); case: HS => _ Hpos; exact: Hpos.
  have cn0 : c != 0.
    apply/eqP => c_eq0; move/negP: S0; apply; apply/eqP.
    by apply: (paper_main_psd_spanning_zero _ _ _ _ Hspan HS) => i; rewrite Hc.
  exists ((d%:R / c) *: S); split.
    by apply: paper_main_psd_scale => //; apply: divr_ge0 => //; exact: ler0n.
  by move=> i; rewrite paper_main_form_scale Hc (divfK cn0).
Qed.

(* lem:homogeneous (i), witness form: S >= 0 of Frobenius norm 1 with
   x_i^T S x_i - Tr S = b for every i. *)
Theorem paper_main_homogeneous_witness n d (x : paper_main_sample n d) :
  (exists S : 'M[R]_d, paper_main_psd S /\ S != 0 /\ paper_main_kernel x S) <->
  (exists (S : 'M[R]_d) (b : R), paper_main_psd S /\ paper_main_frobenius S = 1 /\
    forall i : 'I_n,
      paper_main_quadratic_form S (paper_main_point x i) - paper_main_trace S = b).
Proof.
split.
- move=> [S [HS [S0 [c Hc]]]].
  have p0 : 0 < paper_main_pairing S S := paper_main_pairing_self_gt0 _ _ S0.
  set r := Num.sqrt (paper_main_pairing S S).
  have r0 : 0 < r by rewrite sqrtr_gt0.
  exists (r^-1 *: S), (c / r - paper_main_trace (r^-1 *: S)); split.
    by apply: paper_main_psd_scale => //; rewrite invr_ge0 ltW.
  split.
    rewrite /paper_main_frobenius paper_main_pairing_scale paper_main_pairingC.
    rewrite paper_main_pairing_scale mulrA -invfM -expr2 /r sqr_sqrtr ?(ltW p0) //.
    by rewrite mulVf ?sqrtr1 // gt_eqF.
  by move=> i; rewrite paper_main_form_scale Hc mulrC.
- move=> [S [b [HS [Hfrob Hb]]]].
  exists S; split=> //; split.
    apply/eqP => S_eq0.
    have : paper_main_frobenius S = 0.
      rewrite /paper_main_frobenius S_eq0 /paper_main_pairing.
      rewrite big1 ?sqrtr0 // => i _; rewrite big1 // => j _.
      by rewrite mxE mul0r.
    by rewrite Hfrob => /eqP; rewrite oner_eq0.
  exists (paper_main_trace S + b) => i.
  by rewrite -(Hb i) addrC subrK.
Qed.
