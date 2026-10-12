(* The surrogate maximizer and the deterministic comparison of the two
   Gaussian objectives, at Stdlib's R: items M1 and M2 of phase 11
   (notes/phase11-plan.md, sections 3.1, 3.3 and 5; the math plan
   notes/general-fourth-moment-condition-plan.md, sections 4.2 and 4.3;
   lane A).

   Setting. kappa > 1, c = (kappa - 3) / 2 > -1 (cone_shift kappa),
   a0 = min(1, 1 + c) and e = sqrt (1 + c) - 1. For C >= 0, K_C = cond_cone C
   (library/matrix/condition_cone.v): the symmetric d x d matrices S with
   t I <= S <= C t I for some t >= 0. T = cone_map kappa (Gaussian/Cones.v)
   multiplies the diagonal by sqrt (1 + c) = sqrt ((kappa - 1) / 2), and
   diag S = diag_part S. For d x d matrices H and S,
     Phi_H(S)     = 2 <H, T S> - |S|_F^2 - c |diag S|_F^2    (kappa_obj),
     Phi-bar_H(S) = 2 <H, S> - |S|_F^2 - (c / d) (tr S)^2
                  = trace_quad c H S (library/matrix/trace_projection.v).

   M1, the surrogate maximizer X(H) = kappa_argmax kappa C H, the maximizer
   of Phi-bar_H on K_C, an instance of trace_argmax of
   library/matrix/trace_projection.v (projection after the map
   U_c S = S + e (tr S / d) I, which rescales the trace direction only;
   T rescales every diagonal entry).
   - kappa_argmaxP: X is in K_C and satisfies the variational inequality
     <H - X - (c / d) tr(X) I, S - X> <= 0 for every S in K_C;
     kappa_argmax_ge and kappa_argmax_unique: X is the only maximizer, with
     Phi-bar_H(S) + a0 |S - X|_F^2 <= Phi-bar_H(X) on K_C;
     kappa_argmax_quad_sup: the supremum of Phi-bar_H over K_C is
     Phi-bar_H(X) = <H, X> (kappa_argmax_quad).
   - kappa_argmax_sym, kappa_argmax_psd, kappa_argmax_tr_ge0: X is
     symmetric and positive semidefinite, so tr X >= 0.
   - kappa_argmax_norm: |X|_F <= |H|_F / a0; kappa_argmax_lipschitz: X is
     Lipschitz in H with constant 1 / a0.
   - kappa_argmax_conj: X(P H P^T) = P X(H) P^T for every orthogonal P, by
     uniqueness (cond_cone_conj: K_C is invariant under these
     conjugations).
   - The hypotheses of goe_diag_var_tail (library/random_matrix/
     goe_rotation.v) for F(W) = X(W / sqrt 2), so that F(goe_mx a) = X(H)
     with H = G / sqrt d: kappa_argmax_equivariant, kappa_argmax_goe_sym
     and kappa_argmax_goe_measurable (F(goe_mx a) is a Lipschitz function of
     a); kappa_argmax_diag_var_tail is the resulting tail bound.

   M2, the deterministic comparison, for every c > -1 (both signs and
   c = 0). With D = diag X - (tr X / d) I (diag_dev X) and
   E = e diag H - c D (kappa_err kappa H X):
   - kappa_obj_expand: for all H, S, X, with h = S - X,
       Phi_H(S) - Phi_H(X) = 2 <H - X - (c / d) tr(X) I, h> + 2 <E, h>
                             - (|h|_F^2 + c |diag h|_F^2);
     kappa_pen_ge: |h|_F^2 + c |diag h|_F^2 >= a0 |h|_F^2.
   - kappa_obj_gap: if X satisfies the variational inequality at S, then
     Phi_H(S) - Phi_H(X) <= |E|_F^2 / a0; kappa_argmax_gap, at X = X(H) and
     every S in K_C; kappa_argmax_sup, hence
       Phi_H(X) <= sup_(S in K_C) Phi_H(S) <= Phi_H(X) + |E|_F^2 / a0.
   - kappa_obj_quad: the value correction, for every S,
       Phi_H(S) - Phi-bar_H(S) = 2 e <diag H, diag S> - c |D_S|_F^2,
     with D_S = diag S - (tr S / d) I; kappa_argmax_value at X = X(H). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From GaussianAnalysis Require Import euclidean real_spectral measurable_matrix.
From GaussianAnalysis Require Import condition_cone trace_projection.
From GaussianAnalysis Require Import gauss gauss_smoothing goe goe_rotation.
From EllipsoidUniversality.Gaussian Require Import Cones Limit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* 1. The objects of the comparison. *)

(* Phi_H(S) = 2 <H, T S> - |S|_F^2 - c |diag S|_F^2. *)
Definition kappa_obj (kappa : R) {d : nat} (H S : 'M[R]_d) : R :=
  (2 * mxdot H (cone_map kappa S) - mxdot S S -
   cone_shift kappa * mxdot (diag_part S) (diag_part S))%R.

(* X(H), the maximizer of Phi-bar_H on K_C. *)
Definition kappa_argmax (kappa C : R) {d : nat} (H : 'M[R]_d) : 'M[R]_d :=
  trace_argmax (cond_cone C) (cone_shift kappa) H.

(* D = diag X - (tr X / d) I. *)
Definition diag_dev {d : nat} (X : 'M[R]_d) : 'M[R]_d :=
  diag_part X - (\tr X / d%:R) *: 1%:M.

(* E = e diag H - c D. *)
Definition kappa_err (kappa : R) {d : nat} (H X : 'M[R]_d) : 'M[R]_d :=
  (Num.sqrt (1 + cone_shift kappa) - 1) *: diag_part H -
  cone_shift kappa *: diag_dev X.

(* 2. The diagonal. *)

Section diagonal.
Variable d : nat.
Implicit Types (A B : 'M[R]_d).

Lemma diag_partB A B : diag_part (A - B) = diag_part A - diag_part B.
Proof.
by apply/matrixP => i j; rewrite !mxE; case: (i == j); rewrite ?subr0.
Qed.

Lemma mxdot_diag_partr A B : mxdot A (diag_part B) = \sum_i A i i * B i i.
Proof.
by rewrite mxdotC mxdot_diag_partl; apply: eq_bigr => i _; rewrite mulrC.
Qed.

Lemma mxdot_diag_parts A B :
  mxdot (diag_part A) (diag_part B) = \sum_i A i i * B i i.
Proof.
by rewrite mxdot_diag_partl; apply: eq_bigr => i _; rewrite mxE eqxx.
Qed.

Lemma mxtrace_diag_part A : \tr (diag_part A) = \tr A.
Proof. by rewrite /mxtrace; apply: eq_bigr => i _; rewrite mxE eqxx. Qed.

Lemma mxdot_diag_part_le A : mxdot (diag_part A) (diag_part A) <= mxdot A A.
Proof. by rewrite mxdot_diag_part2; exact: diag_sqr_le. Qed.

End diagonal.

(* 3. M2: the comparison of the two objectives, for every kappa > 1. *)

Section objective.
Variables (kappa : R) (d : nat).
Hypothesis k1 : 1 < kappa.
Implicit Types (H S X h : 'M[R]_d).

Local Notation c := (cone_shift kappa).
Local Notation e := (Num.sqrt (1 + cone_shift kappa) - 1).
Local Notation a0 := (Num.min 1 (1 + cone_shift kappa)).

(* T S = S + e diag S. *)
Lemma cone_map_shift S : cone_map kappa S = S + e *: diag_part S.
Proof. by rewrite cone_map_excess -cone_shiftD1. Qed.

Lemma a0_gt0 : 0 < a0.
Proof. by rewrite lt_min ltr01 /=; have := cone_shift_gtN1 _ k1; lra. Qed.

(* |h|_F^2 + c |diag h|_F^2 >= a0 |h|_F^2. *)
Lemma kappa_pen_ge h :
  a0 * mxdot h h <= mxdot h h + c * mxdot (diag_part h) (diag_part h).
Proof.
have q0 := mxdot_ge0 (diag_part h); have qm := mxdot_diag_part_le h.
have m0 := mxdot_ge0 h.
have a1 : a0 <= 1 by rewrite ge_min lexx.
have a2 : a0 <= 1 + c by rewrite ge_min lexx orbT.
by have [c0|c0] := leP 0 c; nra.
Qed.

(* The expansion of Phi_H at X: trace_scale c X = X + (c / d) tr(X) I. *)
Lemma kappa_obj_expand H S X :
  kappa_obj kappa H S - kappa_obj kappa H X =
  2 * mxdot (H - trace_scale c X) (S - X) +
  2 * mxdot (kappa_err kappa H X) (S - X) -
  (mxdot (S - X) (S - X) + c * mxdot (diag_part (S - X)) (diag_part (S - X))).
Proof.
rewrite /kappa_obj /kappa_err /diag_dev /trace_scale !cone_map_shift diag_partB.
rewrite !(mxdotDl, mxdotDr, mxdotNl, mxdotNr, mxdotZl, mxdotZr) !mxdot1l.
rewrite !mxdot_diag_parts !mxdot_diag_partl !mxdot_diag_partr (mxdotC X S).
have dXS : \sum_i X i i * S i i = \sum_i S i i * X i i.
  by apply: eq_bigr => i _; rewrite mulrC.
by rewrite dXS; ring.
Qed.

Lemma kappa_obj_gap H X S :
  mxdot (H - trace_scale c X) (S - X) <= 0 ->
  kappa_obj kappa H S - kappa_obj kappa H X <=
  mxdot (kappa_err kappa H X) (kappa_err kappa H X) / a0.
Proof.
move=> vi; rewrite kappa_obj_expand.
move: (kappa_err kappa H X) => E.
have a0p := a0_gt0; have pen := kappa_pen_ge (S - X).
have sq := mxdot_ge0 (E - a0 *: (S - X)).
rewrite mxdotBl !mxdotBr !mxdotZl !mxdotZr (mxdotC (S - X) E) in sq.
have p1 := mulr_ge0_le0 (ltW a0p) vi.
have p2 := ler_wpM2l (ltW a0p) pen.
by rewrite ler_pdivlMr //; lra.
Qed.

(* The value correction, for every S. *)
Lemma kappa_obj_quad H S :
  kappa_obj kappa H S - trace_quad c H S =
  2 * e * mxdot (diag_part H) (diag_part S) -
  c * mxdot (diag_dev S) (diag_dev S).
Proof.
have dd : mxdot (diag_dev S) (diag_dev S) =
    mxdot (diag_part S) (diag_part S) - \tr S ^+ 2 / d%:R.
  rewrite /diag_dev mxdotBl !mxdotBr !mxdotZl !mxdotZr.
  rewrite (mxdotC (diag_part S) 1%:M) !mxdot1l mxtrace1 mxtrace_diag_part.
  by rewrite mxtrace_divK; ring.
rewrite dd /kappa_obj /trace_quad cone_map_shift mxdotDr mxdotZr.
by rewrite (mxdot_diag_partr H S) (mxdot_diag_parts H S); ring.
Qed.

End objective.

(* 4. M1: the surrogate maximizer on K_C, and M2 at it. *)

Section surrogate_maximizer.
Variables (kappa C : R) (d : nat).
Hypotheses (k1 : 1 < kappa) (C0 : 0 <= C).
Implicit Types (H S W : 'M[R]_d).

Local Notation c := (cone_shift kappa).
Local Notation e := (Num.sqrt (1 + cone_shift kappa) - 1).
Local Notation a0 := (Num.min 1 (1 + cone_shift kappa)).

Let c1 : -1 < cone_shift kappa := cone_shift_gtN1 _ k1.

Let Kc : closed [set v : 'rV[RR]_(d * d) | cond_cone C (vec_mx v)] :=
  cond_cone_vec_closed C0.

Let Kn : cond_cone C !=set0 := ex_intro _ (0 : 'M[RR]_d) (cond_cone0 d C).

Let Kcvx (S T : 'M[RR]_d) (t : RR) : cond_cone C S -> cond_cone C T ->
  0 <= t <= 1 -> cond_cone C (S + t *: (T - S)).
Proof. exact: cond_cone_convex. Qed.

Lemma kappa_argmaxP H : cond_cone C (kappa_argmax kappa C H) /\
  forall S, cond_cone C S ->
    mxdot (H - kappa_argmax kappa C H -
      (c * (\tr (kappa_argmax kappa C H) / d%:R)) *: 1%:M)
      (S - kappa_argmax kappa C H) <= 0.
Proof.
have [KX hX] := trace_argmaxP Kc Kn Kcvx c1 H.
split => // S KS; have := hX S KS.
by rewrite /trace_scale opprD addrA.
Qed.

Lemma kappa_argmax_ge H S : cond_cone C S ->
  trace_quad c H S +
    a0 * mxdot (S - kappa_argmax kappa C H) (S - kappa_argmax kappa C H) <=
  trace_quad c H (kappa_argmax kappa C H).
Proof. by move=> KS; exact: (trace_argmax_ge Kc Kn Kcvx c1 H KS). Qed.

Lemma kappa_argmax_unique H Y : cond_cone C Y ->
  (forall S, cond_cone C S -> trace_quad c H S <= trace_quad c H Y) ->
  kappa_argmax kappa C H = Y.
Proof. by move=> KY hY; exact: (trace_argmax_unique Kc Kn Kcvx c1 KY hY). Qed.

(* Phi-bar_H(X) = <H, X> = |X|_F^2 + (c / d) (tr X)^2. *)
Lemma kappa_argmax_quad H :
  trace_quad c H (kappa_argmax kappa C H) = mxdot H (kappa_argmax kappa C H) /\
  mxdot H (kappa_argmax kappa C H) =
    mxdot (kappa_argmax kappa C H) (kappa_argmax kappa C H) +
    c / d%:R * \tr (kappa_argmax kappa C H) ^+ 2.
Proof.
have Kcone (S : 'M[RR]_d) (k : RR) : cond_cone C S -> 0 <= k ->
    cond_cone C (k *: S).
  by move=> KS k0; exact: cond_coneZ.
by have [h1 h2] := trace_argmax_cone Kc Kn Kcvx c1 H Kcone.
Qed.

Lemma kappa_argmax_quad_sup H :
  sup [set trace_quad c H S | S in cond_cone C] =
  trace_quad c H (kappa_argmax kappa C H).
Proof.
have [KX _] := kappa_argmaxP H.
have ub : ubound [set trace_quad c H S | S in cond_cone C]
    (trace_quad c H (kappa_argmax kappa C H)).
  move=> _ [S KS <-]; have := kappa_argmax_ge H KS.
  have := mulr_ge0 (ltW (a0_gt0 k1)) (mxdot_ge0 (S - kappa_argmax kappa C H)).
  lra.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_sup ub.
  by exists (trace_quad c H (kappa_argmax kappa C H)), (kappa_argmax kappa C H).
apply: sup_upper_bound; last by exists (kappa_argmax kappa C H).
split.
  by exists (trace_quad c H (kappa_argmax kappa C H)), (kappa_argmax kappa C H).
by exists (trace_quad c H (kappa_argmax kappa C H)).
Qed.

Lemma kappa_argmax_sym H : kappa_argmax kappa C H \is symmetricmx.
Proof. by have [[]] := kappa_argmaxP H. Qed.

Lemma kappa_argmax_psd H (x : 'cV[R]_d) :
  0 <= mxdot x (kappa_argmax kappa C H *m x).
Proof.
have [[_ [t t0 ht]] _] := kappa_argmaxP H.
have /andP[h _] := ht x.
exact: le_trans (mulr_ge0 t0 (mxdot_ge0 x)) h.
Qed.

Lemma kappa_argmax_tr_ge0 H : 0 <= \tr (kappa_argmax kappa C H).
Proof.
rewrite /mxtrace; apply: sumr_ge0 => i _.
have := kappa_argmax_psd H (delta_mx i 0).
by rewrite mxdotC mxdot_delta -colE mxE.
Qed.

Lemma kappa_argmax_norm H :
  frobenius (kappa_argmax kappa C H) <= frobenius H / a0.
Proof. exact: (trace_argmax_norm Kc Kn Kcvx c1 H (cond_cone0 d C)). Qed.

Lemma kappa_argmax_lipschitz H H' :
  frobenius (kappa_argmax kappa C H - kappa_argmax kappa C H') <=
  frobenius (H - H') / a0.
Proof. exact: (trace_argmax_lipschitz Kc Kn Kcvx c1 H H'). Qed.

(* K_C is invariant under the orthogonal conjugations. *)
Lemma cond_cone_conj P S : P \is orthogonalmx -> cond_cone C S ->
  cond_cone C (P *m S *m P^T).
Proof.
move=> Po [Ss [t t0 ht]]; split.
  apply/symmetricmxP; rewrite !trmx_mul trmxK.
  by move/symmetricmxP: Ss => ->; rewrite mulmxA.
exists t => // x.
have -> : mxdot x (P *m S *m P^T *m x) =
    mxdot (P^T *m x) (S *m (P^T *m x)).
  by rewrite !mxdot_colE trmx_mul trmxK !mulmxA.
have -> : mxdot x x = mxdot (P^T *m x) (P^T *m x).
  by rewrite mxdot_orthogonalmxl // trmx_orthogonal.
exact: ht.
Qed.

Lemma kappa_argmax_conj H P : P \is orthogonalmx ->
  kappa_argmax kappa C (P *m H *m P^T) = P *m kappa_argmax kappa C H *m P^T.
Proof.
by move=> Po; exact: (trace_argmax_conj Kc Kn Kcvx c1 H cond_cone_conj Po).
Qed.

(* The hypotheses of goe_diag_var_tail for F(W) = X(W / sqrt 2). *)
Lemma kappa_argmax_equivariant :
  conj_equivariant
    (fun W : 'M[RR]_d => kappa_argmax kappa C ((Num.sqrt 2)^-1 *: W)).
Proof.
move=> Q W Qo _ /=.
by rewrite scalemxAl scalemxAr kappa_argmax_conj.
Qed.

Lemma kappa_argmax_goe_sym W : W \is symmetricmx ->
  kappa_argmax kappa C ((Num.sqrt 2)^-1 *: W) \is symmetricmx.
Proof. by move=> _; exact: kappa_argmax_sym. Qed.

Lemma kappa_argmax_goe_measurable :
  measurable_fun [set: 'rV[RR]_(d * d)]
    (fun a => kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx a) : 'M[RR]_d).
Proof.
have a0p := a0_gt0 k1.
have s1 : (Num.sqrt 2)^-1 <= 1 :> RR.
  rewrite invf_le1 ?sqrtr_gt0 ?ltr0n //.
  by rewrite -[X in X <= _]sqrtr1 ler_sqrt ?ler0n // ler1n.
have FL (a b : 'rV[RR]_(d * d)) :
    frobenius (kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx a) -
               kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx b)) <=
    Num.sqrt (2 / d%:R) / a0 * frobenius (a - b).
  apply: le_trans (kappa_argmax_lipschitz _ _) _.
  rewrite -scalerBr -goe_mxB frobeniusZ ger0_norm ?invr_ge0 ?sqrtr_ge0 //.
  rewrite [_ / a0 * _]mulrAC; apply: ler_wpM2r.
    by rewrite invr_ge0; exact: ltW.
  apply: le_trans _ (frobenius_goe_mx (a - b)).
  by rewrite ler_piMl ?frobenius_ge0.
apply/measurable_fun_mxP => i j; apply: continuous_measurable_mx.
apply: (@lipschitz_frobenius_continuous _ _ _
  (Num.sqrt (2 / d%:R) / a0)) => a b.
apply: le_trans _ (FL a b).
have := frobenius_entry
  (kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx a) -
   kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx b)) i j.
move: (kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx a))
  (kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx b)) => A B.
by rewrite !mxE.
Qed.

(* Lemma 5.13 of Koehler and Sohn for X(H), H = goe_mx a / sqrt 2. *)
Lemma kappa_argmax_diag_var_tail (B eps : RR) : 0 <= B -> 0 < eps ->
  (gauss (d * d) [set a | (eps <=
     diag_var (kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx a)))%R] <=
   (2 * B / ((d%:R + 2) * eps))%:E +
   gauss (d * d) [set a | (B * d%:R <
     mxdot (kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx a))
           (kappa_argmax kappa C ((Num.sqrt 2)^-1 *: goe_mx a)))%R])%E.
Proof.
move=> B0 eps0.
exact: (goe_diag_var_tail kappa_argmax_equivariant kappa_argmax_goe_sym
  kappa_argmax_goe_measurable B0 eps0).
Qed.

(* M2 at X = X(H). *)
Lemma kappa_argmax_gap H S : cond_cone C S ->
  kappa_obj kappa H S - kappa_obj kappa H (kappa_argmax kappa C H) <=
  mxdot (kappa_err kappa H (kappa_argmax kappa C H))
        (kappa_err kappa H (kappa_argmax kappa C H)) / a0.
Proof.
move=> KS; have [_ hX] := trace_argmaxP Kc Kn Kcvx c1 H.
exact: (kappa_obj_gap k1 (hX S KS)).
Qed.

Lemma kappa_argmax_sup H :
  kappa_obj kappa H (kappa_argmax kappa C H) <=
    sup [set kappa_obj kappa H S | S in cond_cone C] /\
  sup [set kappa_obj kappa H S | S in cond_cone C] <=
    kappa_obj kappa H (kappa_argmax kappa C H) +
    mxdot (kappa_err kappa H (kappa_argmax kappa C H))
          (kappa_err kappa H (kappa_argmax kappa C H)) / a0.
Proof.
have [KX _] := kappa_argmaxP H.
have ub : ubound [set kappa_obj kappa H S | S in cond_cone C]
    (kappa_obj kappa H (kappa_argmax kappa C H) +
     mxdot (kappa_err kappa H (kappa_argmax kappa C H))
           (kappa_err kappa H (kappa_argmax kappa C H)) / a0).
  by move=> _ [S KS <-]; have := kappa_argmax_gap H KS; lra.
have ne : [set kappa_obj kappa H S | S in cond_cone C] !=set0.
  exists (kappa_obj kappa H (kappa_argmax kappa C H)).
  by exists (kappa_argmax kappa C H).
split; last by apply: ge_sup ub.
apply: sup_upper_bound; last by exists (kappa_argmax kappa C H).
by split => //; exists (kappa_obj kappa H (kappa_argmax kappa C H) +
  mxdot (kappa_err kappa H (kappa_argmax kappa C H))
        (kappa_err kappa H (kappa_argmax kappa C H)) / a0).
Qed.

Lemma kappa_argmax_value H :
  kappa_obj kappa H (kappa_argmax kappa C H) -
    trace_quad c H (kappa_argmax kappa C H) =
  2 * e * mxdot (diag_part H) (diag_part (kappa_argmax kappa C H)) -
  c * mxdot (diag_dev (kappa_argmax kappa C H))
            (diag_dev (kappa_argmax kappa C H)).
Proof. exact: kappa_obj_quad. Qed.

End surrogate_maximizer.
