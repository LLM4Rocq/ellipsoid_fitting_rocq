(* Deterministic trace-fourth control for the diagonal quadratic block
   (lem:diagonal-feature-block of the paper, by a fourth trace moment in
   place of matrix Bernstein).
   For square public matrices, with MathComp's trace \tr:
   - tr (A B A B) <= tr (A^2 B^2) for symmetric A, B (paper_main_trace_abab,
     from mxtrace_ABAB_le of GaussianAnalysis.matrix.real_spectral);
   - for symmetric Z, tr Z^4 <= t^4 gives -t I <= Z <= t I
     (paper_main_trace_fourth_box, from opnorm_le_trace_exp of
     GaussianAnalysis.matrix.opnorm);
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
From mathcomp Require Import ring_tactic arithmetic_tactic sesquilinear.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.Separation Geometry.HeadFrobenius
  Geometry.HeadFeature Geometry.HeadCorrection Geometry.HeadCoefficients
  Spectral.SymmetricBilinear Cone.ConditionOperator
  Spectral.SymmetricDiagonalization.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Trace.
Variable d : nat.
Implicit Types (A B M S X Z : 'M[R]_d).

(* 1. The commutator inequality. *)
Lemma pmdb_trace_gram_ge0 X : 0 <= \tr (X *m X^T).
Proof. by rewrite -mxdot_trace mxdot_ge0. Qed.

Theorem paper_main_trace_abab A B :
  A^T = A -> B^T = B -> \tr (A *m B *m A *m B) <= \tr (A *m A *m B *m B).
Proof. by move=> /symmetricmxP HA /symmetricmxP HB; exact: mxtrace_ABAB_le. Qed.

Lemma pmdb_form_frobenius Z (v : 'cV[R]_d) :
  ((Z *m v)^T *m (Z *m v)) 0 0 <= \tr (Z^T *m Z) * (v^T *m v) 0 0.
Proof.
rewrite -!mxdot_colE mxtrace_mulC -mxdot_trace -!frobenius_sqr -exprMn.
by rewrite ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 // frobenius_mulmx.
Qed.

(* A trace-fourth bound is a Loewner box. *)
Theorem paper_main_trace_fourth_box Z (t : R) :
  Z^T = Z -> 0 <= t -> \tr (Z *m Z *m Z *m Z) <= t ^+ 4 ->
  paper_main_loewner_le ((- t) *: 1%:M) Z /\ paper_main_loewner_le Z (t *: 1%:M).
Proof.
move=> /symmetricmxP HZ Ht HT; apply/paper_main_loewner_boxP; split => //.
apply/(opnorm_symP HZ Ht)/(opnorm_le_trace_exp HZ (p := 4)) => //.
by rewrite (_ : Z ^+ 4 = Z *m Z *m Z *m Z) // !exprSr expr0 mul1r.
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
