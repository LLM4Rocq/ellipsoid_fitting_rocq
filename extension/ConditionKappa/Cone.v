(* The transformed cone of bounded condition number and its support
   function, at Stdlib's R: item B1 of phase 11 (notes/phase11-plan.md,
   sections 5 and 6, interface I1; the math plan
   notes/general-fourth-moment-condition-plan.md, section 4.1; lane B).

   This file holds the single shared definition of the cone T K_C, of its
   base and of its support function. GaussianLimit (item M5, lane A),
   GaussianWitness and GaussianGap (item G1, lane B) import it.

   Setting. kappa > 1, c = (kappa - 3) / 2 > -1 (cone_shift kappa) and
   a0 = min(1, 1 + c). For C > 1, K_C = cond_cone C and cond_slice C, its
   slice of trace d (library/matrix/condition_cone.v). T = cone_map kappa
   (Gaussian/Cones.v) multiplies the diagonal by
   sqrt (1 + c) = sqrt ((kappa - 1) / 2); it is invertible, with inverse
   cone_map (kappa_dual kappa) (cone_mapK, cone_mapVK). The condition
   number of a matrix T S of T K_C is measured on S, before T.

   Definitions.
     kcond_cone_vec kappa C d  == T K_C in the coordinates of mxvec: the
                                  mxvec (T S) with S in cond_cone C
     kcond_slice_vec kappa C d == the base of T K_C, T of the trace-d slice:
                                  the mxvec (T S) with S in cond_slice C
     kcond_support kappa C A   == sigma_{C,kappa}(A), the supremum of
                                  <A, T S> over the S of K_C with
                                  |T S|_F <= 1 (interface I1: the unit ball
                                  is taken after T)
   Their transposes tr_set (kcond_cone_vec kappa C d) and
   tr_set (kcond_slice_vec kappa C d), sets of column vectors (tr_set of
   library/comparison/cgmt.v), are the K and B that
   library/comparison/cone_escape.v takes.

   Proved. The lemmas assume kappa > 1 and C > 1 where they use them; some
   lemmas on row vectors assume only 0 <= C or 1 <= C.
   1. The cone of row vectors satisfies the hypotheses of the projection of
      library/convex/moreau.v: kcond_cone_vec0, kcond_cone_vecZ,
      kcond_cone_vec_convex and kcond_cone_vec_closed (T K_C is the
      preimage of cond_cone_vec C under T^-1, which multiplies each
      coordinate by a constant: kcond_cone_vecP). Its base:
      kcond_slice_vec1 (it holds mxvec (T I)), kcond_slice_vec_sub (it lies
      in the cone), kcond_slice_vec_convex, kcond_slice_vec_closed
      (kcond_slice_vecP), and kcond_cone_vec_slice: every nonzero point of
      the cone has a positive multiple in the base.
   2. The norm on the base. kcond_frobenius: for every S,
        a0 |S|_F^2 <= |T S|_F^2 <= max(1, 1 + c) |S|_F^2,
      from |T S|_F^2 = |S|_F^2 + c |diag S|_F^2 (pairing_cone_map). With
      d <= |S|_F^2 <= C d on the slice (cond_slice_frobenius),
      kcond_slice_vec_ge and kcond_slice_vec_le give
        sqrt (a0 d) <= |T S|_F <= sqrt (max(1, 1 + c) C d).
   3. The same for the column vectors, the hypotheses of
      cone_escape_zero_tail and cone_escape_lower_tail: kcond_K0,
      kcond_K_closed, kcond_K_cone, kcond_B_base, kcond_B_sub,
      kcond_B_closed, kcond_B_convex, kcond_B_neq0, kcond_B_le and
      kcond_B_ge, the analogues of cond_K0 to cond_B_ge of
      Condition/GaussianWitness.v, which treats kappa = 3.
   4. The support function. kcond_cone_supE: cone_sup of cone_escape.v for
      tr_set (kcond_cone_vec kappa C d) at h is
      kcond_support kappa C (vec_mx h), the analogue of cond_cone_supE.
      kcond_support_proj: it is the norm of the projection of h onto
      kcond_cone_vec kappa C d. kcond_support_ge0, kcond_support_le: it lies
      in [0, |A|_F]. kcond_support3: at kappa = 3 it is cond_support C.
      Its limit, sigma_{C,kappa} / d -> sqrt alpha(C, kappa) in probability
      under gauss (d * d), interface I1, is kcond_support_cvg of
      GaussianLimit (item M5). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From GaussianAnalysis Require Import euclidean measurable_matrix.
From GaussianAnalysis Require Import cgmt cone_escape moreau condition_cone.
From EllipsoidUniversality.Gaussian Require Import Cones.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* T K_C, in the coordinates of mxvec. *)
Definition kcond_cone_vec (kappa C : R) (d : nat) : set 'rV[R]_(d * d) :=
  [set mxvec (cone_map kappa S) | S in @cond_cone RR d C].

(* T of the trace-d slice of K_C, in the coordinates of mxvec. *)
Definition kcond_slice_vec (kappa C : R) (d : nat) : set 'rV[R]_(d * d) :=
  [set mxvec (cone_map kappa S) | S in @cond_slice RR d C].

(* sigma_{C,kappa}(A) = sup { <A, T S> : S in K_C, |T S|_F <= 1 }. *)
Definition kcond_support (kappa C : R) {d : nat} (A : 'M[R]_d) : R :=
  sup [set mxdot A (cone_map kappa S) |
    S in [set S | @cond_cone RR d C S /\ frobenius (cone_map kappa S) <= 1]].

Section mxvec_pairing.
Variable d : nat.

Local Lemma mxdot_mxvecE (A B : 'M[R]_d) :
  mxdot (mxvec A) (mxvec B) = mxdot A B.
Proof.
rewrite /mxdot big_ord1 (reindex _ (curry_mxvec_bij d d)) /=.
rewrite pair_big /=; apply: eq_bigr => -[i j] _ /=.
by rewrite !mxvecE.
Qed.

Local Lemma frobenius_mxvecE (A : 'M[R]_d) :
  frobenius (mxvec A) = frobenius A.
Proof. by rewrite /frobenius mxdot_mxvecE. Qed.

Local Lemma mxdot_vec_mxE (h : 'rV[R]_(d * d)) (A : 'M[R]_d) :
  mxdot h (mxvec A) = mxdot (vec_mx h) A.
Proof. by rewrite -[in LHS](vec_mxK h) mxdot_mxvecE. Qed.

Local Lemma mxvec_convex (A B : 'M[R]_d) (t : R) :
  mxvec (A + t *: (B - A)) = mxvec A + t *: (mxvec B - mxvec A).
Proof. by rewrite linearD /= linearZ /= linearB. Qed.

Local Lemma cone_map_convex (kappa : R) (A B : 'M[R]_d) (t : R) :
  cone_map kappa (A + t *: (B - A)) =
  cone_map kappa A + t *: (cone_map kappa B - cone_map kappa A).
Proof. by rewrite cone_mapD cone_mapZ cone_mapD cone_mapN. Qed.

Local Lemma cone_map0 (kappa : R) : cone_map kappa (0 : 'M[R]_d) = 0.
Proof.
by apply/matrixP => i j; rewrite cone_mapE !mxE; case: eqP; rewrite ?mulr0.
Qed.

(* The map v |-> mxvec (T (vec_mx v)) multiplies each coordinate by a
   constant, so it is continuous. *)
Local Definition cone_scale (kappa : R) : 'rV[R]_(d * d) :=
  mxvec (\matrix_(i, j)
    (if i == j then Num.sqrt ((kappa - 1) / 2%:R) else 1)).

Local Lemma cone_map_mulmx (kappa : R) (v : 'rV[R]_(d * d)) :
  mxvec (cone_map kappa (vec_mx v)) = v *m diag_mx (cone_scale kappa).
Proof.
apply/rowP => k; case/mxvec_indexP: k => i j.
rewrite mul_mx_diag !mxE /cone_scale !mxvecE cone_mapE !mxE.
by case: eqP => [<-|_]; rewrite ?mulr1 // mulrC.
Qed.

End mxvec_pairing.

Section kcond_cone.
Variables (kappa C : R) (d : nat).

Local Notation Kv := (kcond_cone_vec kappa C d).
Local Notation Bv := (kcond_slice_vec kappa C d).

(* 1. The cone and its base, as sets of row vectors. *)

Lemma kcond_cone_vecP (v : 'rV[R]_(d * d)) : 1 < kappa ->
  Kv v <-> cond_cone C (cone_map (kappa_dual kappa) (vec_mx v)).
Proof.
move=> k1; split => [[S KS <-]|Kv'].
  by rewrite mxvecK cone_mapK.
exists (cone_map (kappa_dual kappa) (vec_mx v)) => //.
by rewrite cone_mapVK // vec_mxK.
Qed.

Lemma kcond_slice_vecP (v : 'rV[R]_(d * d)) : 1 < kappa ->
  Bv v <-> cond_slice C (cone_map (kappa_dual kappa) (vec_mx v)).
Proof.
move=> k1; split => [[S BS <-]|Bv'].
  by rewrite mxvecK cone_mapK.
exists (cone_map (kappa_dual kappa) (vec_mx v)) => //.
by rewrite cone_mapVK // vec_mxK.
Qed.

Lemma kcond_cone_vec0 : Kv 0.
Proof. by exists 0; [exact: cond_cone0 | rewrite cone_map0 linear0]. Qed.

Lemma kcond_cone_vecZ (x : 'rV[R]_(d * d)) (a : R) : Kv x -> 0 <= a ->
  Kv (a *: x).
Proof.
move=> [S KS <-] a0; exists (a *: S); first exact: cond_coneZ.
by rewrite cone_mapZ linearZ.
Qed.

Lemma kcond_cone_vec_convex (x y : 'rV[R]_(d * d)) (t : R) :
  Kv x -> Kv y -> 0 <= t <= 1 -> Kv (x + t *: (y - x)).
Proof.
move=> [S1 K1 <-] [S2 K2 <-] t01; exists (S1 + t *: (S2 - S1)).
  exact: cond_cone_convex.
by rewrite cone_map_convex mxvec_convex.
Qed.

Lemma kcond_cone_vec_closed : 1 < kappa -> 0 <= C -> closed Kv.
Proof.
move=> k1 C0.
have -> : Kv = (fun v => v *m diag_mx (cone_scale d (kappa_dual kappa))) @^-1`
    @cond_cone_vec RR d C.
  apply/seteqP; split => v.
    move/(kcond_cone_vecP v k1).
    by rewrite /= -cone_map_mulmx /cond_cone_vec /= mxvecK.
  rewrite /= -cone_map_mulmx /cond_cone_vec /= mxvecK.
  by move/(kcond_cone_vecP v k1).
apply: (continuous_closedP _).1; first exact: continuous_mulmxr.
exact: cond_cone_vec_closed C0.
Qed.

Lemma kcond_slice_vec1 : 1 <= C -> Bv (mxvec (cone_map kappa 1%:M)).
Proof. by move=> C1; exists 1%:M => //; exact: cond_slice1. Qed.

Lemma kcond_slice_vec_sub (x : 'rV[R]_(d * d)) : Bv x -> Kv x.
Proof. by move=> [S [KS _] <-]; exists S. Qed.

Lemma kcond_slice_vec_convex (x y : 'rV[R]_(d * d)) (t : R) :
  Bv x -> Bv y -> 0 <= t <= 1 -> Bv (x + t *: (y - x)).
Proof.
move=> [S1 [K1 tr1] <-] [S2 [K2 tr2] <-] t01.
exists (S1 + t *: (S2 - S1)).
  split; first exact: cond_cone_convex.
  by rewrite mxtraceD mxtraceZ raddfB /= tr1 tr2 subrr mulr0 addr0.
by rewrite cone_map_convex mxvec_convex.
Qed.

Lemma kcond_slice_vec_closed : 1 < kappa -> 0 <= C -> closed Bv.
Proof.
move=> k1 C0.
have -> : Bv = (fun v => v *m diag_mx (cone_scale d (kappa_dual kappa))) @^-1`
    @cond_slice_vec RR d C.
  apply/seteqP; split => v.
    move/(kcond_slice_vecP v k1).
    by rewrite /= -cone_map_mulmx /cond_slice_vec /= mxvecK.
  rewrite /= -cone_map_mulmx /cond_slice_vec /= mxvecK.
  by move/(kcond_slice_vecP v k1).
apply: (continuous_closedP _).1; first exact: continuous_mulmxr.
exact: cond_slice_vec_closed C0.
Qed.

(* Every nonzero point of the cone has a positive multiple in the base. *)
Lemma kcond_cone_vec_slice (x : 'rV[R]_(d * d)) : Kv x -> x != 0 ->
  exists2 a : R, 0 < a & Bv (a *: x).
Proof.
move=> [S KS <-] x0.
have S0 : mxvec S != 0.
  apply: contraNneq x0 => /eqP; rewrite mxvec_eq0 => /eqP ->.
  by rewrite cone_map0 linear0.
have KS' : @cond_cone_vec RR d C (mxvec S).
  by rewrite /cond_cone_vec /= mxvecK.
have [a a0 Sa] := cond_cone_vec_slice KS' S0.
exists a => //; exists (a *: S); last by rewrite cone_mapZ linearZ.
by move: Sa; rewrite /cond_slice_vec /= linearZ /= mxvecK.
Qed.

(* a0 |S|_F^2 <= |T S|_F^2 <= max(1, 1 + c) |S|_F^2. *)
Lemma kcond_frobenius (S : 'M[R]_d) : 1 < kappa ->
  Num.min 1 (1 + cone_shift kappa) * mxdot S S <=
    mxdot (cone_map kappa S) (cone_map kappa S) <=
  Num.max 1 (1 + cone_shift kappa) * mxdot S S.
Proof.
move=> k1.
have e : mxdot (cone_map kappa S) (cone_map kappa S) =
    mxdot S S + cone_shift kappa * \sum_(i < d) S i i * S i i.
  exact: (pairing_cone_map d kappa S S (ltW k1)).
rewrite e.
set P := mxdot S S; set s := \sum_(i < d) S i i * S i i.
set c := cone_shift kappa.
have sP : s <= P.
  rewrite /s /P /mxdot; apply: ler_sum => i _.
  rewrite (bigD1 i) //= lerDl; apply: sumr_ge0 => j _.
  by rewrite -expr2 sqr_ge0.
have s0 : 0 <= s by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
set m := Num.min 1 (1 + c); set M := Num.max 1 (1 + c).
have m1 : m <= 1 by rewrite /m ge_min lexx.
have mc : m <= 1 + c by rewrite /m ge_min lexx orbT.
have M1 : 1 <= M by rewrite /M le_max lexx.
have Mc : 1 + c <= M by rewrite /M le_max lexx orbT.
have h1 : 0 <= (1 - m) * (P - s) by rewrite mulr_ge0 // subr_ge0.
have h2 : 0 <= (1 + c - m) * s by rewrite mulr_ge0 // subr_ge0.
have h3 : 0 <= (M - 1) * (P - s) by rewrite mulr_ge0 // subr_ge0.
have h4 : 0 <= (M - (1 + c)) * s by rewrite mulr_ge0 // subr_ge0.
by apply/andP; split; lra.
Qed.

Lemma kcond_slice_vec_le : 1 < kappa -> 1 < C -> forall x, Bv x ->
  frobenius x <= Num.sqrt (Num.max 1 (1 + cone_shift kappa) * C * d%:R).
Proof.
move=> k1 C1 _ [S BS <-]; rewrite frobenius_mxvecE /frobenius.
apply: ler_wsqrtr.
have /andP[_ h] := kcond_frobenius S k1.
apply: le_trans h _; rewrite -mulrA ler_wpM2l //.
  by rewrite le_max ler01.
by have /andP[_ ->] := cond_slice_frobenius (lt_trans ltr01 C1) BS.
Qed.

Lemma kcond_slice_vec_ge : 1 < kappa -> 1 < C -> forall x, Bv x ->
  Num.sqrt (Num.min 1 (1 + cone_shift kappa) * d%:R) <= frobenius x.
Proof.
move=> k1 C1 _ [S BS <-]; rewrite frobenius_mxvecE /frobenius.
apply: ler_wsqrtr.
have /andP[h _] := kcond_frobenius S k1.
apply: le_trans h; apply: ler_wpM2l.
  rewrite le_min ler01 /=; have := cone_shift_gtN1 kappa k1; lra.
by have /andP[-> _] := cond_slice_frobenius (lt_trans ltr01 C1) BS.
Qed.

(* 2. The same, for the sets of column vectors of cone_escape.v. *)

Local Notation K := (tr_set Kv).
Local Notation B := (tr_set Bv).

Lemma kcond_K0 : K 0.
Proof. exact: (tr_set0 kcond_cone_vec0). Qed.

Lemma kcond_K_closed : 1 < kappa -> 1 < C -> closed K.
Proof.
move=> k1 C1.
exact: closed_tr_set (kcond_cone_vec_closed k1 (ltW (lt_trans ltr01 C1))).
Qed.

Lemma kcond_K_cone x (a : R) : K x -> 0 <= a -> K (a *: x).
Proof. by apply: tr_set_cone => y b Ky b0; exact: kcond_cone_vecZ. Qed.

Lemma kcond_B_base x : K x -> x != 0 -> exists2 a : R, 0 < a & B (a *: x).
Proof. by apply: tr_set_base => y Ky y0; exact: kcond_cone_vec_slice. Qed.

Lemma kcond_B_sub x : B x -> K x.
Proof. by apply: tr_set_sub => y; exact: kcond_slice_vec_sub. Qed.

Lemma kcond_B_closed : 1 < kappa -> 1 < C -> closed B.
Proof.
move=> k1 C1.
exact: closed_tr_set (kcond_slice_vec_closed k1 (ltW (lt_trans ltr01 C1))).
Qed.

Lemma kcond_B_convex x y (t : R) : B x -> B y -> 0 <= t <= 1 ->
  B (x + t *: (y - x)).
Proof.
by apply: convex_tr_set => u v s Bu Bv' s01; exact: kcond_slice_vec_convex.
Qed.

Lemma kcond_B_neq0 : 1 < C -> B !=set0.
Proof.
move=> C1; apply: tr_set_neq0.
by exists (mxvec (cone_map kappa 1%:M)); exact: kcond_slice_vec1 (ltW C1).
Qed.

Lemma kcond_B_le : 1 < kappa -> 1 < C -> forall x, B x ->
  frobenius x <= Num.sqrt (Num.max 1 (1 + cone_shift kappa) * C * d%:R).
Proof.
move=> k1 C1 _ [v Bv' <-]; rewrite frobenius_trmx.
exact: kcond_slice_vec_le.
Qed.

Lemma kcond_B_ge : 1 < kappa -> 1 < C -> forall x, B x ->
  Num.sqrt (Num.min 1 (1 + cone_shift kappa) * d%:R) <= frobenius x.
Proof.
move=> k1 C1 _ [v Bv' <-]; rewrite frobenius_trmx.
exact: kcond_slice_vec_ge.
Qed.

(* 3. The support function of K is kcond_support kappa C. *)
Lemma kcond_cone_supE (h : 'rV[R]_(d * d)) :
  cone_sup K h = kcond_support kappa C (vec_mx h).
Proof.
rewrite cone_sup_tr_setE /kcond_support; congr sup; apply/seteqP; split.
  move=> _ [_ [[S KS <-] S1] <-]; exists S; last by rewrite mxdot_vec_mxE.
  by split => //; rewrite -frobenius_mxvecE.
move=> _ [S [KS S1] <-]; exists (mxvec (cone_map kappa S)).
  by split; [exists S | rewrite frobenius_mxvecE].
exact: mxdot_vec_mxE.
Qed.

Lemma kcond_support_proj (h : 'rV[R]_(d * d)) : 1 < kappa -> 0 <= C ->
  kcond_support kappa C (vec_mx h) = frobenius (proj Kv h).
Proof.
move=> k1 C0; rewrite -kcond_cone_supE.
exact: (cone_sup_proj (kcond_cone_vec_closed k1 C0) kcond_cone_vec0
  kcond_cone_vec_convex kcond_cone_vecZ).
Qed.

Lemma kcond_support_ge0 (A : 'M[R]_d) : 0 <= kcond_support kappa C A.
Proof.
by have := cone_sup_ge0 kcond_K0 (mxvec A); rewrite kcond_cone_supE mxvecK.
Qed.

Lemma kcond_support_le (A : 'M[R]_d) :
  kcond_support kappa C A <= frobenius A.
Proof.
have := cone_sup_le_norm kcond_K0 (mxvec A).
by rewrite kcond_cone_supE mxvecK frobenius_mxvecE.
Qed.

End kcond_cone.

(* At kappa = 3, T is the identity and sigma_{C,3} is cond_support C. *)
Lemma kcond_support3 (C : R) d (A : 'M[R]_d) :
  kcond_support 3%:R C A = cond_support C A.
Proof.
rewrite /kcond_support /cond_support; congr sup; apply/seteqP; split.
  move=> _ [S [KS S1] <-]; rewrite cone_map3 in S1 *; exists S => //.
  by split => //; rewrite -frobenius_sqr exprn_ile1 // frobenius_ge0.
move=> _ [S [KS S1] <-]; exists S; last by rewrite cone_map3.
split => //; rewrite cone_map3.
by rewrite /frobenius -sqrtr1 ler_sqrt.
Qed.
