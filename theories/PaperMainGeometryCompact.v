(* Deterministic geometry for the main results of the paper, part 5: the
   set of positive semidefinite matrices of trace one is compact, and a
   continuous function attains its minimum on it.

   Matrices of 'M[R]_d are read through their row of d*d coordinates
   (vec_mx : 'rV[R]_(d*d) -> 'M[R]_d, MathComp), so that the compactness
   theorems of MathComp-Analysis for row vectors apply: rV_compact for the
   box [-1, 1]^(d*d) built from segment_compact, compact_closedI for the
   closed subset, compact_EVT_min for the minimum.

   - A polynomial function of the coordinates is continuous (sums,
     products, constants, coordinates).
   - The trace-one PSD set is closed (symmetry, the form and the trace are
     continuous constraints), contained in the box (its entries are
     bounded by 1 through the Cauchy-Schwarz inequality of part 2), hence
     compact; for d > 0 it is nonempty.
   - Every continuous real function on it attains its minimum there.

   Internal proof workstream (analysis/reports/PROGRESS-main-geometry.md);
   not part of any contract. No Axiom, Parameter or Admitted. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryGram PaperMainGeometryExclusion PaperMainGeometryHomogeneous.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* 1. Continuity of polynomial functions of the coordinates. *)

Section Toolkit.
Variable N : nat.
Local Notation V := 'rV[R]_N.

Lemma pmg_continuous_cst (c : R) : continuous (fun _ : V => c).
Proof. exact: cst_continuous. Qed.

Lemma pmg_continuous_coord (k : 'I_N) : continuous (fun v : V => v 0 k).
Proof. exact: coord_continuous. Qed.

Lemma pmg_continuousD (f g : V -> R) :
  continuous f -> continuous g -> continuous (fun v => f v + g v).
Proof.
move=> Hf Hg; have -> : (fun v => f v + g v) = (f + g) by [].
by move=> v; exact: (@continuousD _ R^o _ f g v (Hf v) (Hg v)).
Qed.

Lemma pmg_continuousB (f g : V -> R) :
  continuous f -> continuous g -> continuous (fun v => f v - g v).
Proof.
move=> Hf Hg; have -> : (fun v => f v - g v) = (f - g) by [].
by move=> v; exact: (@continuousB _ R^o _ f g v (Hf v) (Hg v)).
Qed.

Lemma pmg_continuousM (f g : V -> R) :
  continuous f -> continuous g -> continuous (fun v => f v * g v).
Proof.
move=> Hf Hg; have -> : (fun v => f v * g v) = (f \* g) by [].
by move=> v; exact: (@continuousM _ _ f g v (Hf v) (Hg v)).
Qed.

Lemma pmg_continuous_sum (I : finType) (F : I -> V -> R) :
  (forall i, continuous (F i)) -> continuous (fun v => \sum_(i : I) F i v).
Proof.
move=> HF; elim: (index_enum I) => [|i r IH].
  have -> : (fun v => \sum_(j <- [::]) F j v) = (fun _ => 0).
    by apply: funext => v; rewrite big_nil.
  exact: pmg_continuous_cst.
have -> : (fun v => \sum_(j <- i :: r) F j v) = (fun v => F i v + \sum_(j <- r) F j v).
  by apply: funext => v; rewrite big_cons.
by apply: pmg_continuousD.
Qed.

(* Closed sublevel and level sets of continuous functions. *)
Lemma pmg_closed_ge (f : V -> R) (c : R) :
  continuous f -> closed [set v : V | c <= f v].
Proof.
move=> Hf.
have := proj1 (continuous_closedP f) Hf [set r : R | c <= r] (@closed_ge _ c).
by [].
Qed.

Lemma pmg_closed_eq (f : V -> R) (c : R) :
  continuous f -> closed [set v : V | f v = c].
Proof.
move=> Hf.
have := proj1 (continuous_closedP f) Hf [set r : R | r = c] (@closed_eq _ c).
by [].
Qed.

(* The box [-1, 1]^N is compact. *)
Definition pmg_box : set V := [set v : V | forall k, `[-1, 1]%classic (v 0 k)].

Lemma pmg_box_compact : compact pmg_box.
Proof.
have H := @rV_compact R N (fun=> `[-1, 1]%classic) (fun _ => @segment_compact _ (-1) 1).
exact: H.
Qed.

End Toolkit.

(* 2. The trace-one PSD set, in coordinates. *)

Section TraceOne.
Variable d : nat.
Local Notation V := 'rV[R]_(d * d).
Local Notation toS := (@vec_mx R d d).

Definition pmg_trace_one : set V :=
  [set v : V | paper_main_psd (toS v) /\ paper_main_trace (toS v) = 1].

Lemma pmg_entry_continuous (i j : 'I_d) : continuous (fun v : V => toS v i j).
Proof.
have -> : (fun v : V => toS v i j) = (fun v : V => v 0 (mxvec_index i j)).
  by apply/funext => v; rewrite mxE.
exact: pmg_continuous_coord.
Qed.

Lemma pmg_form_continuous (w : 'cV[R]_d) :
  continuous (fun v : V => paper_main_quadratic_form (toS v) w).
Proof.
rewrite /paper_main_quadratic_form.
apply: pmg_continuous_sum => i; apply: pmg_continuous_sum => j.
apply: pmg_continuousM; last exact: pmg_continuous_cst.
apply: pmg_continuousM; first exact: pmg_continuous_cst.
exact: pmg_entry_continuous.
Qed.

Lemma pmg_trace_continuous : continuous (fun v : V => paper_main_trace (toS v)).
Proof.
rewrite /paper_main_trace; apply: pmg_continuous_sum => i.
exact: pmg_entry_continuous.
Qed.

Lemma pmg_trace_one_closed : closed pmg_trace_one.
Proof.
have -> : pmg_trace_one =
    ((\bigcap_(i : 'I_d) \bigcap_(j : 'I_d)
        [set v : V | toS v i j - toS v j i = 0]) `&`
     (\bigcap_(w : 'cV[R]_d) [set v : V | 0 <= paper_main_quadratic_form (toS v) w])) `&`
    [set v : V | paper_main_trace (toS v) = 1].
  rewrite predeqE => v; split.
    move=> [[Hsym Hpos] Htr]; split=> //; split.
      by move=> i _ j _ /=; rewrite Hsym subrr.
    by move=> w _ /=; exact: Hpos.
  move=> [[Hsym Hpos] Htr]; split=> //; split.
    by move=> i j; apply/eqP; rewrite -subr_eq0; apply/eqP; exact: (Hsym i Logic.I j Logic.I).
  by move=> w; exact: (Hpos w Logic.I).
apply: closedI; last by apply: pmg_closed_eq; exact: pmg_trace_continuous.
apply: closedI.
  apply: closed_bigI => i _; apply: closed_bigI => j _.
  by apply: pmg_closed_eq; apply: pmg_continuousB; exact: pmg_entry_continuous.
by apply: closed_bigI => w _; apply: pmg_closed_ge; exact: pmg_form_continuous.
Qed.

(* Entries of a PSD matrix are bounded by its trace: S_ii <= Tr S and
   S_ij^2 <= S_ii S_jj. *)
Lemma pmg_diag_le_trace (S : 'M[R]_d) (i : 'I_d) :
  paper_main_psd S -> S i i <= paper_main_trace S.
Proof.
move=> HS; rewrite /paper_main_trace (bigD1 i) //= lerDl.
by apply: sumr_ge0 => j _; exact: (paper_main_psd_diag_ge0 _ S j HS).
Qed.

Lemma pmg_entry_sqr_le (S : 'M[R]_d) (i j : 'I_d) :
  paper_main_psd S -> S i j ^+ 2 <= S i i * S j j.
Proof.
move=> HS.
have := paper_main_psd_cauchy_schwarz _ S (delta_mx i 0 : 'cV[R]_d) (delta_mx j 0 : 'cV[R]_d) HS.
rewrite !paper_main_form_deltaE.
rewrite trmx_delta -mulmxA -colE -rowE.
by rewrite [fun_of_matrix (row _ _) _ _]mxE [fun_of_matrix (col _ _) _ _]mxE.
Qed.

Lemma pmg_trace_one_entry (S : 'M[R]_d) (i j : 'I_d) :
  paper_main_psd S -> paper_main_trace S = 1 -> `[-1, 1]%classic (S i j).
Proof.
move=> HS Htr.
have Hii : S i i <= 1 by rewrite -Htr; exact: (pmg_diag_le_trace S i HS).
have Hjj : S j j <= 1 by rewrite -Htr; exact: (pmg_diag_le_trace S j HS).
have Hi0 := paper_main_psd_diag_ge0 _ S i HS.
have Hj0 := paper_main_psd_diag_ge0 _ S j HS.
have Hsqr : S i j ^+ 2 <= 1.
  apply: le_trans (pmg_entry_sqr_le S i j HS) _.
  by rewrite -[1](mul1r 1); apply: ler_pM.
have Habs : `|S i j| <= 1.
  by rewrite -[1]sqrtr1 -sqrtr_sqr; apply: ler_wsqrtr.
by rewrite /= in_itv /= -ler_norml.
Qed.

Lemma pmg_trace_one_sub_box : pmg_trace_one `<=` pmg_box (d * d).
Proof.
move=> v [HS Htr] k; case: (mxvec_indexP k) => i j.
by have := pmg_trace_one_entry _ i j HS Htr; rewrite mxE.
Qed.

Theorem pmg_trace_one_compact : compact pmg_trace_one.
Proof.
have -> : pmg_trace_one = pmg_box (d * d) `&` pmg_trace_one.
  by rewrite predeqE => v; split=> [Hv | [_ Hv]] //; split=> //; exact: pmg_trace_one_sub_box.
by apply: compact_closedI; [exact: pmg_box_compact | exact: pmg_trace_one_closed].
Qed.

End TraceOne.

(* 3. Nonemptiness for d > 0 and the minimum of a continuous function. *)

Lemma pmg_trace_one_neq0 d : (0 < d)%nat -> pmg_trace_one d !=set0.
Proof.
case: d => // d _.
set e : 'cV[R]_d.+1 := delta_mx ord0 ord0.
have Hdiag (i : 'I_d.+1) : (e *m e^T) i i = (i == ord0)%:R.
  by rewrite mxE big_ord1 !mxE eqxx andbT -natrM; case: (i == ord0).
exists (mxvec (e *m e^T)); split.
  by rewrite mxvecK; exact: paper_main_psd_rank1.
rewrite mxvecK /paper_main_trace (bigD1 ord0) //=.
have -> : \sum_(i < d.+1 | i != ord0) (e *m e^T) i i = 0.
  by apply: big1 => i i0; rewrite Hdiag (negbTE i0).
by rewrite Hdiag eqxx addr0.
Qed.

Theorem pmg_trace_one_min d (f : 'rV[R]_(d * d) -> R) :
  (0 < d)%nat -> continuous f ->
  exists2 v0, pmg_trace_one d v0 & forall v, pmg_trace_one d v -> f v0 <= f v.
Proof.
move=> d0 Hf.
have Hw : {within pmg_trace_one d, continuous f} by apply: continuous_subspaceT.
have [v0 Hv0 Hmin] := compact_EVT_min (pmg_trace_one_neq0 _ d0)
  (pmg_trace_one_compact d) Hw.
exists v0; first by rewrite -in_setE.
by move=> v Hv; apply: Hmin; rewrite in_setE.
Qed.
