(* Deterministic trace-fourth control for the diagonal quadratic block
   (G15, checkpoint A; manuscript lem:diagonal-feature-block, by a fourth
   trace moment in place of matrix Bernstein).
   For square public matrices, with MathComp's trace \tr:
   - tr (A B A B) <= tr (A^2 B^2) for symmetric A, B, from
     tr (X X^T) >= 0 with X = A B - B A (paper_main_trace_abab);
   - for symmetric Z and every v, (v^T Z v)^4 <= (v^T v)^4 tr Z^4. So
     tr Z^4 <= t^4 gives -t I <= Z <= t I, with no spectral theorem
     (paper_main_trace_fourth_box);
   - the rank-one formulas
     tr (u u^T - c I)^2 = (|u|^2 - c)^2 + c^2 (d - 1) and
     tr (u u^T - c I)^4 = (|u|^2 - c)^4 + c^4 (d - 1);
   - the expansion tr (S + M)^4 = tr S^4 + 4 tr (S^3 M) + 4 tr (S^2 M^2)
     + 2 tr (S M S M) + 4 tr (S M^3) + tr M^4;
   - D^T D = sum_i u_i u_i^T for the rows u_i of D, and D^T D <= t I gives
     D D^T <= t I. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadCoefficients
  PaperMainSymmetricBilinear PaperMainConeConditionOperator.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Trace.
Variable d : nat.
Implicit Types (A B M S X Z : 'M[R]_d).

(* 1. The commutator inequality. *)
Lemma pmdb_trace_gram_ge0 X : 0 <= \tr (X *m X^T).
Proof.
rewrite /mxtrace; apply: sumr_ge0 => i _; rewrite mxE.
by apply: sumr_ge0 => j _; rewrite mxE -expr2; exact: sqr_ge0.
Qed.

Theorem paper_main_trace_abab A B :
  A^T = A -> B^T = B -> \tr (A *m B *m A *m B) <= \tr (A *m A *m B *m B).
Proof.
move=> HA HB.
set X := A *m B - B *m A.
have HXt : X^T = - X by rewrite /X linearB /= !trmx_mul HA HB opprB.
have H := pmdb_trace_gram_ge0 X.
rewrite HXt mulmxN raddfN /= oppr_ge0 in H.
have E1 : \tr (A *m B *m B *m A) = \tr (A *m A *m B *m B).
  by rewrite mxtrace_mulC !mulmxA.
have E2 : \tr (B *m A *m A *m B) = \tr (A *m A *m B *m B).
  by rewrite -!mulmxA mxtrace_mulC !mulmxA.
have E3 : \tr (B *m A *m B *m A) = \tr (A *m B *m A *m B).
  by rewrite mxtrace_mulC !mulmxA.
have E : \tr (X *m X) = 2 * \tr (A *m B *m A *m B) - 2 * \tr (A *m A *m B *m B).
  rewrite /X mulmxBl !mulmxBr !raddfB /= !mulmxA E1 E2 E3; ring.
rewrite E in H; lra.
Qed.

(* 2. Trace-fourth control of a quadratic form. *)
Lemma pmdb_form_cs Z (v : 'cV[R]_d) :
  Z^T = Z ->
  ((v^T *m Z *m v) 0 0) ^+ 2 <= (v^T *m v) 0 0 * (v^T *m (Z *m Z) *m v) 0 0.
Proof.
move=> HZ.
have H := pmco_vec_cauchy_schwarz _ v (Z *m v).
have -> : (v^T *m (Z *m Z) *m v) 0 0 = ((Z *m v)^T *m (Z *m v)) 0 0.
  by rewrite trmx_mul HZ !mulmxA.
by rewrite -mulmxA.
Qed.

Lemma pmdb_form_frobenius Z (v : 'cV[R]_d) :
  ((Z *m v)^T *m (Z *m v)) 0 0 <= \tr (Z^T *m Z) * (v^T *m v) 0 0.
Proof.
rewrite [X in X <= _]pmh_vec_dot.
have Hrow : forall a : 'I_d, (Z *m v) a 0 ^+ 2 <=
    (\sum_(b < d) Z a b ^+ 2) * (v^T *m v) 0 0.
  move=> a; have H := pmco_vec_cauchy_schwarz _ ((row a Z)^T) v.
  have E1 : (((row a Z)^T)^T *m v) 0 0 = (Z *m v) a 0.
    by rewrite trmxK !mxE; apply: eq_bigr => b _; rewrite !mxE.
  have E2 : ((((row a Z)^T)^T *m (row a Z)^T)) 0 0 = \sum_(b < d) Z a b ^+ 2.
    by rewrite trmxK mxE; apply: eq_bigr => b _; rewrite !mxE expr2.
  by rewrite E1 E2 in H.
have Htr : \tr (Z^T *m Z) = \sum_(a < d) \sum_(b < d) Z a b ^+ 2.
  rewrite /mxtrace exchange_big; apply: eq_bigr => b _; rewrite mxE.
  by apply: eq_bigr => a _; rewrite !mxE expr2.
rewrite Htr mulr_suml; apply: ler_sum => a _.
by rewrite -expr2; exact: Hrow.
Qed.

Theorem paper_main_trace_fourth_form Z (v : 'cV[R]_d) :
  Z^T = Z ->
  ((v^T *m Z *m v) 0 0) ^+ 4 <= ((v^T *m v) 0 0) ^+ 4 * \tr (Z *m Z *m Z *m Z).
Proof.
move=> HZ.
have HZ2 : (Z *m Z)^T = Z *m Z by rewrite trmx_mul HZ.
set n := (v^T *m v) 0 0.
set q1 := (v^T *m Z *m v) 0 0.
set q2 := (v^T *m (Z *m Z) *m v) 0 0.
set q4 := (v^T *m (Z *m Z *m (Z *m Z)) *m v) 0 0.
have Hn : 0 <= n by rewrite /n; exact: pmh_vec_sqr_ge0.
have H1 : q1 ^+ 2 <= n * q2 by exact: pmdb_form_cs.
have H2 : q2 ^+ 2 <= n * q4 by exact: pmdb_form_cs.
have Hq2 : 0 <= q2.
  have E : v^T *m (Z *m Z) *m v = (Z *m v)^T *m (Z *m v) by rewrite trmx_mul HZ !mulmxA.
  by rewrite /q2 E; exact: pmh_vec_sqr_ge0.
have H4 : q4 <= \tr (Z *m Z *m Z *m Z) * n.
  have E : q4 = (((Z *m Z) *m v)^T *m ((Z *m Z) *m v)) 0 0.
    by rewrite /q4 trmx_mul HZ2 !mulmxA.
  rewrite E; apply: le_trans (pmdb_form_frobenius (Z *m Z) v) _.
  by rewrite HZ2 !mulmxA.
set T := \tr (Z *m Z *m Z *m Z) in H4 *.
have Hq1sq : 0 <= q1 ^+ 2 := sqr_ge0 q1.
have S1 : (q1 ^+ 2) ^+ 2 <= (n * q2) ^+ 2.
  rewrite ler_sqr ?nnegrE //; exact: mulr_ge0.
have S2 : (n * q2) ^+ 2 <= n ^+ 3 * q4.
  rewrite exprMn.
  have := ler_wpM2l (sqr_ge0 n) H2.
  have E : n ^+ 2 * (n * q4) = n ^+ 3 * q4 by ring.
  by rewrite E.
have S3 : n ^+ 3 * q4 <= n ^+ 4 * T.
  have := ler_wpM2l (exprn_ge0 3 Hn) H4.
  have E : n ^+ 3 * (T * n) = n ^+ 4 * T by ring.
  by rewrite E.
have E4 : q1 ^+ 4 = (q1 ^+ 2) ^+ 2 by rewrite -exprM.
by rewrite E4; apply: le_trans S1 (le_trans S2 S3).
Qed.

(* A trace-fourth bound is a Loewner box, with no spectral theorem. *)
Theorem paper_main_trace_fourth_box Z (t : R) :
  Z^T = Z -> 0 <= t -> \tr (Z *m Z *m Z *m Z) <= t ^+ 4 ->
  paper_main_loewner_le ((- t) *: 1%:M) Z /\ paper_main_loewner_le Z (t *: 1%:M).
Proof.
move=> HZ Ht HT.
have HZs : paper_main_symmetric Z by exact/paper_main_symmetricP.
have Hform : forall v : 'cV[R]_d,
    `|(v^T *m Z *m v) 0 0| <= t * (v^T *m v) 0 0.
  move=> v.
  have Hn : 0 <= (v^T *m v) 0 0 by exact: pmh_vec_sqr_ge0.
  have H := paper_main_trace_fourth_form Z v HZ.
  have H' : ((v^T *m Z *m v) 0 0) ^+ 4 <= (t * (v^T *m v) 0 0) ^+ 4.
    apply: le_trans H _; rewrite exprMn mulrC.
    by apply: ler_wpM2r => //; exact: exprn_ge0.
  have Hx : `|(v^T *m Z *m v) 0 0| ^+ 4 <= (t * (v^T *m v) 0 0) ^+ 4.
    by rewrite -normrX ger0_norm ?exprn_even_ge0.
  move: Hx; rewrite ler_pXn2r // ?nnegrE //; exact: mulr_ge0.
have HtI : paper_main_symmetric (t *: (1%:M : 'M[R]_d)).
  by apply: paper_main_symmetric_scale; exact: pmh_symmetric_id.
have HmtI : paper_main_symmetric ((- t) *: (1%:M : 'M[R]_d)).
  by apply: paper_main_symmetric_scale; exact: pmh_symmetric_id.
split; split.
- exact: pmh_symmetricB.
- move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE.
  have := Hform v; rewrite ler_norml => /andP [H1 _]; lra.
- exact: pmh_symmetricB.
- move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE.
  have := Hform v; rewrite ler_norml => /andP [_ H2]; lra.
Qed.

(* 3. Rank-one formulas. *)
Lemma pmdb_rank1_mul (u : 'cV[R]_d) :
  (u *m u^T) *m (u *m u^T) = ((u^T *m u) 0 0) *: (u *m u^T).
Proof.
rewrite -mulmxA (mulmxA u^T u u^T) (mx11_scalar (u^T *m u)) mul_scalar_mx.
by rewrite scalemxAr [((u^T *m u) 0 0)%:M 0 0]mxE eqxx mulr1n.
Qed.

Lemma pmdb_tr_rank1 (u : 'cV[R]_d) : \tr (u *m u^T) = (u^T *m u) 0 0.
Proof. by rewrite mxtrace_mulC trace_mx11. Qed.

Lemma pmdb_tr_scalar (c : R) : \tr (c *: (1%:M : 'M[R]_d)) = c * d%:R.
Proof. by rewrite linearZ /= mxtrace1 -mulr_natr. Qed.

Lemma pmdb_rank1_sq (u : 'cV[R]_d) (c : R) :
  (u *m u^T - c *: 1%:M) *m (u *m u^T - c *: 1%:M) =
  ((u^T *m u) 0 0 - 2 * c) *: (u *m u^T) + (c ^+ 2) *: 1%:M.
Proof.
rewrite mulmxBl !mulmxBr pmdb_rank1_mul -!scalemxAl -!scalemxAr mulmx1 mul1mx.
rewrite mul1mx; apply/matrixP => a b; rewrite !mxE; ring.
Qed.

Theorem paper_main_rank_one_trace_sq (u : 'cV[R]_d) (c : R) :
  \tr ((u *m u^T - c *: 1%:M) *m (u *m u^T - c *: 1%:M)) =
  ((u^T *m u) 0 0 - c) ^+ 2 + c ^+ 2 * (d%:R - 1).
Proof.
rewrite pmdb_rank1_sq raddfD /= linearZ /= pmdb_tr_rank1 pmdb_tr_scalar; ring.
Qed.

Theorem paper_main_rank_one_trace_fourth (u : 'cV[R]_d) (c : R) :
  \tr ((u *m u^T - c *: 1%:M) *m (u *m u^T - c *: 1%:M) *m
       (u *m u^T - c *: 1%:M) *m (u *m u^T - c *: 1%:M)) =
  ((u^T *m u) 0 0 - c) ^+ 4 + c ^+ 4 * (d%:R - 1).
Proof.
set M := u *m u^T - c *: 1%:M.
have -> : M *m M *m M *m M = (M *m M) *m (M *m M) by rewrite !mulmxA.
rewrite /M pmdb_rank1_sq.
set s := (u^T *m u) 0 0.
rewrite mulmxDl !mulmxDr -!scalemxAl -!scalemxAr pmdb_rank1_mul mulmx1 mul1mx.
rewrite mulmx1 !raddfD /= !linearZ /= pmdb_tr_rank1 mxtrace1 -/s.
rewrite -mulr_natr; ring.
Qed.

(* 4. The fourth power of a sum. *)
Lemma pmdb_tr_rot A B M S : \tr (A *m B *m M *m S) = \tr (B *m M *m S *m A).
Proof. by rewrite -!mulmxA mxtrace_mulC !mulmxA. Qed.

Theorem paper_main_trace_fourth_expand S M :
  \tr ((S + M) *m (S + M) *m (S + M) *m (S + M)) =
  \tr (S *m S *m S *m S) + 4 * \tr (S *m S *m S *m M) + 4 * \tr (S *m S *m M *m M) +
  2 * \tr (S *m M *m S *m M) + 4 * \tr (S *m M *m M *m M) + \tr (M *m M *m M *m M).
Proof.
rewrite !mulmxDl !mulmxDr !raddfD /=.
do 3 rewrite ?mulmxDl ?mulmxDr.
rewrite !raddfD /=.
have R1 : \tr (S *m S *m M *m S) = \tr (S *m S *m S *m M).
  by rewrite pmdb_tr_rot pmdb_tr_rot pmdb_tr_rot.
have R2 : \tr (S *m M *m S *m S) = \tr (S *m S *m S *m M).
  by rewrite pmdb_tr_rot pmdb_tr_rot.
have R3 : \tr (M *m S *m S *m S) = \tr (S *m S *m S *m M) by rewrite pmdb_tr_rot.
have R4 : \tr (S *m M *m M *m S) = \tr (S *m S *m M *m M).
  by rewrite pmdb_tr_rot pmdb_tr_rot pmdb_tr_rot.
have R5 : \tr (M *m M *m S *m S) = \tr (S *m S *m M *m M).
  by rewrite pmdb_tr_rot pmdb_tr_rot.
have R6 : \tr (M *m S *m S *m M) = \tr (S *m S *m M *m M) by rewrite pmdb_tr_rot.
have R7 : \tr (M *m S *m M *m S) = \tr (S *m M *m S *m M) by rewrite pmdb_tr_rot.
have R8 : \tr (M *m S *m M *m M) = \tr (S *m M *m M *m M) by rewrite pmdb_tr_rot.
have R9 : \tr (M *m M *m S *m M) = \tr (S *m M *m M *m M).
  by rewrite pmdb_tr_rot pmdb_tr_rot.
have R10 : \tr (M *m M *m M *m S) = \tr (S *m M *m M *m M).
  by rewrite pmdb_tr_rot pmdb_tr_rot pmdb_tr_rot.
rewrite R1 R2 R3 R4 R5 R6 R7 R8 R9 R10; ring.
Qed.

(* 5. The Gram of the rows, and the transfer from D^T D to D D^T. *)
Lemma paper_main_gram_rows N (D : 'M[R]_(N, d)) :
  D^T *m D = \sum_(i < N) (row i D)^T *m row i D.
Proof.
apply/matrixP => a b; rewrite !mxE summxE; apply: eq_bigr => i _.
by rewrite !mxE big_ord1 !mxE.
Qed.

Theorem paper_main_gram_transfer N (D : 'M[R]_(N, d)) (t : R) :
  0 <= t -> paper_main_loewner_le (D^T *m D) (t *: 1%:M) ->
  paper_main_loewner_le (D *m D^T) (t *: 1%:M).
Proof.
move=> Ht [_ HD].
have HtI : paper_main_symmetric (t *: (1%:M : 'M[R]_N)).
  by apply: paper_main_symmetric_scale; exact: pmh_symmetric_id.
have HDD : paper_main_symmetric (D *m D^T).
  by move=> a b; rewrite !mxE; apply: eq_bigr => k _; rewrite !mxE mulrC.
split; first exact: pmh_symmetricB.
move=> w; rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE.
set v := D^T *m w.
have Hv : (w^T *m (D *m D^T) *m w) 0 0 = (v^T *m v) 0 0.
  by rewrite /v trmx_mul trmxK !mulmxA.
have := HD v; rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE.
have E : v^T *m (D^T *m D) *m v = (D *m v)^T *m (D *m v).
  by rewrite [(D *m v)^T]trmx_mul !mulmxA.
rewrite E subr_ge0 => HDv.
have Hcs := pmco_vec_cauchy_schwarz _ w (D *m v).
have Hwv : (w^T *m (D *m v)) 0 0 = (v^T *m v) 0 0.
  by rewrite /v mulmxA -[w^T *m D]trmxK trmx_mul trmxK.
rewrite Hwv in Hcs; rewrite Hv subr_ge0.
have Hw0 : 0 <= (w^T *m w) 0 0 by exact: pmh_vec_sqr_ge0.
have Hv0 : 0 <= (v^T *m v) 0 0 by exact: pmh_vec_sqr_ge0.
have HDv0 : 0 <= ((D *m v)^T *m (D *m v)) 0 0 by exact: pmh_vec_sqr_ge0.
set x := (v^T *m v) 0 0 in Hcs HDv Hv0 *.
set a := (w^T *m w) 0 0 in Hcs Hw0 *.
set y := ((D *m v)^T *m (D *m v)) 0 0 in Hcs HDv HDv0 *.
have H1 : x * x <= (t * a) * x.
  rewrite -expr2; apply: le_trans Hcs _.
  have := ler_wpM2l Hw0 HDv.
  have E2 : a * (t * x) = t * a * x by ring.
  by rewrite E2.
case: (ltrP 0 x) => Hx.
  by rewrite ler_pM2r in H1.
by apply: le_trans Hx _; exact: mulr_ge0.
Qed.

(* 6. The centered Gram of the rows and the operator conclusion. *)
Lemma paper_main_centered_gram_rows N (D : 'M[R]_(N, d)) :
  D^T *m D - (2 * N%:R) *: 1%:M =
  \sum_(i < N) ((row i D)^T *m row i D - 2 *: 1%:M).
Proof.
rewrite paper_main_gram_rows sumrB; congr (_ - _).
by rewrite sumr_const card_ord scalerMnl mulr_natr.
Qed.

Theorem paper_main_diag_block_from_trace N (D : 'M[R]_(N, d)) :
  \tr ((D^T *m D - (2 * N%:R) *: 1%:M) *m (D^T *m D - (2 * N%:R) *: 1%:M) *m
       (D^T *m D - (2 * N%:R) *: 1%:M) *m (D^T *m D - (2 * N%:R) *: 1%:M)) <= N%:R ^+ 4 ->
  paper_main_loewner_le (D^T *m D) ((3 * N%:R) *: 1%:M) /\
  paper_main_loewner_le (D *m D^T) ((3 * N%:R) *: 1%:M).
Proof.
move=> HT.
set Z := D^T *m D - (2 * N%:R) *: 1%:M in HT.
have HZ : Z^T = Z.
  by rewrite /Z linearB /= trmx_mul trmxK linearZ /= trmx1.
have [_ Hup] := paper_main_trace_fourth_box Z N%:R HZ (ler0n _ _) HT.
have H2 : paper_main_loewner_le ((2 * N%:R) *: (1%:M : 'M[R]_d)) ((2 * N%:R) *: 1%:M).
  exact: pmh_loewner_scalar (lexx _).
have Hadd := pmh_loewner_add _ _ _ _ _ Hup H2.
have E1 : Z + (2 * N%:R) *: 1%:M = D^T *m D by rewrite /Z subrK.
have E2 : (N%:R : R) *: (1%:M : 'M[R]_d) + (2 * N%:R) *: 1%:M = (3 * N%:R) *: 1%:M.
  by rewrite -scalerDl; congr (_ *: _); ring.
rewrite E1 E2 in Hadd.
split => //.
apply: paper_main_gram_transfer => //.
by apply: mulr_ge0 => //; exact: ler0n.
Qed.

End Trace.
