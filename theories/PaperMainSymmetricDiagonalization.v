(* Real orthogonal diagonalization of real symmetric matrices, from the
   spectral theorem symmetric_spectral of the library
   (GaussianAnalysis.matrix.real_spectral). For every symmetric
   A : 'M[R]_n there are O : 'M[R]_n with O^T O = 1 and a real row
   a : 'rV[R]_n with
     A = O^T diag(a) O        (paper_main_symmetric_diagonalization).
   Consequences, for every column x:
     x^T A x = sum_i a_i ((O x)_i)^2,   trace A = sum_i a_i,
     sum_(i,j) A_ij^2 = sum_i a_i^2,   O O^T = 1,
   and |a_i| <= b when (u^T A w)^2 <= b^2 |u|^2 |w|^2 for all u, w
   (paper_main_cone_opnorm_le A b) and 0 <= b. They are the library's
   spectral_form, spectral_trace, spectral_mxdot and spectral_form_abs,
   through the bridges paper_main_symmetricmx (symmetry),
   paper_main_quadratic_form_mxdot (the quadratic form) and
   paper_main_pairing_mxdot (the Frobenius pairing). *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp reals Rstruct arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainConeConditionOperator.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* Dot products of columns. *)

Lemma paper_main_symmetric_dotC {N : nat} (u v : 'cV[R]_N) :
  (u^T *m v) 0 0 = (v^T *m u) 0 0.
Proof. by rewrite -!mxdot_colE mxdotC. Qed.

Lemma paper_main_symmetric_entryB {m n : nat} (A B : 'M[R]_(m, n)) i j :
  (A - B) i j = A i j - B i j.
Proof. by rewrite [in LHS]mxE [X in _ + X]mxE. Qed.

Lemma paper_main_symmetric_dotBl {N : nat} (u u' v : 'cV[R]_N) :
  ((u - u')^T *m v) 0 0 = (u^T *m v) 0 0 - (u'^T *m v) 0 0.
Proof. by rewrite -!mxdot_colE mxdotBl. Qed.

Lemma paper_main_symmetric_dotBr {N : nat} (u v v' : 'cV[R]_N) :
  (u^T *m (v - v')) 0 0 = (u^T *m v) 0 0 - (u^T *m v') 0 0.
Proof. by rewrite -!mxdot_colE mxdotBr. Qed.

(* Bridges to the library. *)

Lemma paper_main_symmetricmx {d : nat} (S : 'M[R]_d) :
  paper_main_symmetric S <-> S \is symmetricmx.
Proof.
split=> [/paper_main_symmetricP/symmetricmxP //|/symmetricmxP ST].
by apply/paper_main_symmetricP.
Qed.

Lemma paper_main_quadratic_form_mxdot {d : nat} (S : 'M[R]_d) (x : 'cV[R]_d) :
  paper_main_quadratic_form S x = mxdot x (S *m x).
Proof. by rewrite paper_main_quadratic_formE mxdot_colE mulmxA. Qed.

Lemma paper_main_pairing_mxdot {d : nat} (S M : 'M[R]_d) :
  paper_main_pairing S M = mxdot S M.
Proof. by []. Qed.

Lemma paper_main_cone_opnorm_leP {d : nat} (Z : 'M[R]_d) (b : R) :
  paper_main_cone_opnorm_le Z b <-> opnorm Z <= `|b|.
Proof.
rewrite -(opnorm_bilinearP _ (normr_ge0 b)).
have E (u v : 'cV[R]_d) :
    ((u^T *m Z *m v) 0 0 ^+ 2 <= b ^+ 2 * ((u^T *m u) 0 0 * (v^T *m v) 0 0)) =
    (`|mxdot u (Z *m v)| <= `|b| * frobenius u * frobenius v).
  rewrite -mulmxA -!mxdot_colE -!frobenius_sqr -[mxdot _ _ ^+ 2]real_normK ?num_real //.
  rewrite -[b ^+ 2]real_normK ?num_real // -!exprMn mulrA.
  by rewrite ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0.
by split=> H u v; [rewrite -E | rewrite E]; exact: H.
Qed.

Lemma paper_main_loewner_boxP {d : nat} (Z : 'M[R]_d) (b : R) :
  (paper_main_loewner_le ((- b) *: 1%:M) Z /\ paper_main_loewner_le Z (b *: 1%:M)) <->
  (Z \is symmetricmx /\ forall x : 'cV[R]_d, `|mxdot x (Z *m x)| <= b * mxdot x x).
Proof.
have symE (c : R) : (Z - c *: 1%:M)^T = Z^T - c *: 1%:M.
  by rewrite linearB /= linearZ /= trmx1.
have symE' (c : R) : (c *: 1%:M - Z)^T = c *: 1%:M - Z^T.
  by rewrite linearB /= linearZ /= trmx1.
have formE (c : R) x :
    paper_main_quadratic_form (Z - c *: 1%:M) x = mxdot x (Z *m x) - c * mxdot x x.
  by rewrite paper_main_quadratic_form_mxdot mulmxBl -scalemxAl mul1mx mxdotBr mxdotZr.
have formE' (c : R) x :
    paper_main_quadratic_form (c *: 1%:M - Z) x = c * mxdot x x - mxdot x (Z *m x).
  by rewrite paper_main_quadratic_form_mxdot mulmxBl -scalemxAl mul1mx mxdotBr mxdotZr.
split=> [[[_ P1] [S2 P2]]|[/symmetricmxP ZT Zb]].
  split.
    apply/symmetricmxP/eqP; move/paper_main_symmetricP: S2; rewrite symE' => /eqP.
    by rewrite eq_sym -subr_eq0 opprB addrC subrKA subr_eq0 => /eqP ->.
  move=> x; have := P1 x; have := P2 x; rewrite formE formE' ler_norml; lra.
split; split.
- by apply/paper_main_symmetricP; rewrite symE ZT.
- by move=> x; rewrite formE; have := Zb x; rewrite ler_norml; lra.
- by apply/paper_main_symmetricP; rewrite symE' ZT.
- by move=> x; rewrite formE'; have := Zb x; rewrite ler_norml; lra.
Qed.

Lemma paper_main_symmetric_orthogonalmx {n : nat} (O : 'M[R]_n) :
  O^T *m O = 1%:M -> O \is orthogonalmx.
Proof. by move=> /mulmx1C OO; apply/orthogonalmxP. Qed.

(* The orthogonal diagonalization. *)

Theorem paper_main_symmetric_diagonalization n (A : 'M[R]_n) :
  paper_main_symmetric A ->
  exists (O : 'M[R]_n) (a : 'rV[R]_n), O^T *m O = 1%:M /\ A = O^T *m diag_mx a *m O.
Proof.
move=> /paper_main_symmetricmx/symmetric_spectral [O Oo [a AE]].
by exists O, a; split => //; exact: orthogonalmxT.
Qed.

(* Consequences. *)

Lemma paper_main_symmetric_orthogonal_tr n (O : 'M[R]_n) :
  O^T *m O = 1%:M -> O *m O^T = 1%:M.
Proof. exact: mulmx1C. Qed.

Lemma paper_main_symmetric_diag_form n (a : 'rV[R]_n) (y : 'cV[R]_n) :
  paper_main_quadratic_form (diag_mx a) y = \sum_(i < n) a 0 i * y i 0 ^+ 2.
Proof.
rewrite paper_main_quadratic_form_mxdot (@spectral_form _ _ _ 1%:M a).
  by rewrite trmx1 mul1mx mulmx1.
by under eq_bigr do rewrite mul1mx.
Qed.

Theorem paper_main_symmetric_form_diagonal n (A O : 'M[R]_n) (a : 'rV[R]_n) :
  A = O^T *m diag_mx a *m O ->
  forall x : 'cV[R]_n,
    paper_main_quadratic_form A x = \sum_(i < n) a 0 i * (O *m x) i 0 ^+ 2.
Proof. by move=> HA x; rewrite paper_main_quadratic_form_mxdot (spectral_form _ HA). Qed.

Theorem paper_main_symmetric_trace_diagonal n (A O : 'M[R]_n) (a : 'rV[R]_n) :
  O^T *m O = 1%:M -> A = O^T *m diag_mx a *m O ->
  paper_main_trace A = \sum_(i < n) a 0 i.
Proof.
by move=> /paper_main_symmetric_orthogonalmx Oo HA; exact: (spectral_trace Oo HA).
Qed.

Theorem paper_main_symmetric_frobenius_diagonal n (A O : 'M[R]_n) (a : 'rV[R]_n) :
  O^T *m O = 1%:M -> A = O^T *m diag_mx a *m O ->
  paper_main_pairing A A = \sum_(i < n) a 0 i ^+ 2.
Proof.
by move=> /paper_main_symmetric_orthogonalmx Oo HA; exact: (spectral_mxdot Oo HA).
Qed.

Theorem paper_main_symmetric_coefficient_bound n (A O : 'M[R]_n) (a : 'rV[R]_n) (b : R) :
  O^T *m O = 1%:M -> A = O^T *m diag_mx a *m O ->
  0 <= b -> paper_main_cone_opnorm_le A b ->
  forall i : 'I_n, `|a 0 i| <= b.
Proof.
move=> /paper_main_symmetric_orthogonalmx Oo HA b0 HB.
apply/(spectral_form_abs b Oo HA) => x.
have := HB x x; rewrite -mulmxA -!mxdot_colE => H.
rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?mxdot_ge0 // real_normK ?num_real //.
by rewrite exprMn [mxdot x x ^+ 2]expr2.
Qed.
