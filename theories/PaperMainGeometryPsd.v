(* Deterministic geometry for the main results of the paper, part 1: the
   Frobenius pairing and the basic facts about positive semidefinite
   matrices, over the definitions of PaperMainDefinitions (the MathComp
   column vectors 'cV[R]_d and matrices 'M[R]_d of the true dimension d,
   paper_main_quadratic_form, paper_main_symmetric, paper_main_psd,
   paper_main_pd).

   - paper_main_pairing S M = sum_{ij} S_{ij} M_{ij}, the paper's <S, M>.
   - The quadratic form is the 1 x 1 matrix product v^T S v; symmetry is
     S^T = S; <S, x x^T> = x^T S x; the pairing is linear in its second
     argument on weighted sums.
   - For S >= 0 and v^T S v = 0, S v = 0 (the discriminant argument on
     t |-> (v + t w)^T S (v + t w) >= 0). *)

From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* The Frobenius pairing sum_{ij} S_{ij} M_{ij}. *)
Definition paper_main_pairing {d : nat} (S M : 'M[R]_d) : R :=
  \sum_(i < d) \sum_(j < d) S i j * M i j.

Section Basics.
Variable d : nat.
Implicit Types (S M : 'M[R]_d) (v w x : 'cV[R]_d).

(* The quadratic form as the entry of the 1 x 1 product v^T S v. *)
Lemma paper_main_quadratic_formE S v :
  paper_main_quadratic_form S v = (v^T *m S *m v) 0 0.
Proof.
rewrite /paper_main_quadratic_form mxE exchange_big /=.
apply: eq_bigr => j _; rewrite mxE mulr_suml.
by apply: eq_bigr => i _; rewrite mxE.
Qed.

(* Symmetry as an equation of matrices. *)
Lemma paper_main_symmetricP S : paper_main_symmetric S <-> S^T = S.
Proof.
split=> [Hs | Hs i j].
  by apply/matrixP => i j; rewrite mxE; exact: Hs.
by rewrite -{1}Hs mxE.
Qed.

(* <S, x x^T> = x^T S x. *)
Lemma paper_main_pairing_outer S x :
  paper_main_pairing S (x *m x^T) = paper_main_quadratic_form S x.
Proof.
rewrite /paper_main_pairing /paper_main_quadratic_form.
apply: eq_bigr => i _; apply: eq_bigr => j _.
by rewrite mxE big_ord1 !mxE mulrCA mulrA.
Qed.

(* <S, sum_i y_i A_i> = sum_i y_i <S, A_i>. *)
Lemma paper_main_pairing_sum n S (y : 'I_n -> R) (A : 'I_n -> 'M[R]_d) :
  paper_main_pairing S (\sum_(i < n) y i *: A i) =
  \sum_(i < n) y i * paper_main_pairing S (A i).
Proof.
rewrite /paper_main_pairing.
have step a b : S a b * (\sum_(i < n) y i *: A i) a b =
    \sum_(i < n) y i * (S a b * A i a b).
  rewrite summxE mulr_sumr; apply: eq_bigr => i _.
  by rewrite mxE mulrCA.
under eq_bigr => a _ do under eq_bigr => b _ do rewrite step.
under eq_bigr => a _ do rewrite exchange_big.
rewrite exchange_big /=; apply: eq_bigr => i _.
rewrite mulr_sumr; apply: eq_bigr => a _.
by rewrite mulr_sumr.
Qed.

(* The pairing is symmetric in its arguments. *)
Lemma paper_main_pairingC S M : paper_main_pairing S M = paper_main_pairing M S.
Proof.
rewrite /paper_main_pairing; apply: eq_bigr => i _; apply: eq_bigr => j _.
by rewrite mulrC.
Qed.

(* The cross term of a symmetric matrix: v^T S w = w^T S v. *)
Lemma paper_main_cross_sym S v w : S^T = S ->
  (v^T *m S *m w) 0 0 = (w^T *m S *m v) 0 0.
Proof.
move=> Hs; transitivity ((v^T *m S *m w)^T 0 0); first by rewrite [in RHS]mxE.
by rewrite !trmx_mul trmxK mulmxA Hs.
Qed.

(* Expansion of the quadratic form along a line. *)
Lemma paper_main_form_line S v w (t : R) : S^T = S ->
  ((v + t *: w)^T *m S *m (v + t *: w)) 0 0 =
  (v^T *m S *m v) 0 0 + t * (w^T *m S *m v) 0 0 + t * (w^T *m S *m v) 0 0 +
  t * t * (w^T *m S *m w) 0 0.
Proof.
move=> Hs.
rewrite [(_ + _)^T]linearD /= [(_ *: _)^T]linearZ /=.
rewrite !mulmxDl !mulmxDr -!scalemxAl -!scalemxAr.
rewrite ![fun_of_matrix (_ + _) _ _]mxE ![fun_of_matrix (_ *: _) _ _]mxE.
rewrite (paper_main_cross_sym S v w Hs).
by rewrite !addrA mulrA.
Qed.

End Basics.

(* The discriminant: if t c + t c + t^2 a >= 0 for every t, with a >= 0,
   then c = 0. Proved in Stdlib's vocabulary after conversion, with the
   auxiliary products that lra needs made explicit. *)
Lemma paper_main_discriminant (a c : R) :
  0 <= a -> (forall t : R, 0 <= t * c + t * c + t * t * a) -> c = 0.
Proof.
move=> a0 H; case: (c =P 0) => [-> // | /eqP c0].
have a10 : 0 < a + 1 := ltr_wpDl a0 ltr01.
have a1 : a + 1 != 0 := lt0r_neq0 a10.
set u := (a + 1)^-1.
have ua : u * a = 1 - u.
  rewrite -(mulVf a1); rewrite -/u.
  by rewrite mulrDr mulr1 addrK.
have u0 : 0 < u by rewrite /u invr_gt0.
have cc : 0 < c * c by rewrite -expr2 lt0r sqrf_eq0 c0 sqr_ge0.
(* Stdlib's vocabulary, with explicit zeros and ones: the operations are
   convertible, the relations go through RleP and RltP. *)
have a0' : Rle (IZR 0) a by apply/RleP.
have u0' : Rlt (IZR 0) u by apply/RltP.
have cc' : Rlt (IZR 0) (Rmult c c) by apply/RltP.
have ua' : Rmult u a = Rminus (IZR 1) u := ua.
have Hq : Rle (IZR 0)
    (Rplus (Rplus (Rmult (Ropp (Rmult c u)) c) (Rmult (Ropp (Rmult c u)) c))
      (Rmult (Rmult (Ropp (Rmult c u)) (Ropp (Rmult c u))) a)).
  by apply/RleP; exact: (H (- (c * u))).
have Hcu : Rlt (IZR 0) (Rmult (Rmult c c) u) by nra.
have Hcuu : Rlt (IZR 0) (Rmult (Rmult (Rmult c c) u) u) by nra.
have Hprod : Rmult (Rmult (Rmult c c) u) (Rmult u a) =
    Rmult (Rmult (Rmult c c) u) (Rminus (IZR 1) u) by rewrite ua'.
exfalso; lra.
Qed.

Section Psd.
Variable d : nat.
Implicit Types (S : 'M[R]_d) (v w : 'cV[R]_d).

(* For S >= 0, a vector of zero quadratic form is in the kernel. *)
Lemma paper_main_psd_form_eq0 S v :
  paper_main_psd S -> paper_main_quadratic_form S v = 0 -> S *m v = 0.
Proof.
move=> [Hsym Hpos] Hv.
have Hs : S^T = S by apply/paper_main_symmetricP.
have Hq w : 0 <= (w^T *m S *m w) 0 0.
  by rewrite -paper_main_quadratic_formE; exact: Hpos.
have Hv' : (v^T *m S *m v) 0 0 = 0 by rewrite -paper_main_quadratic_formE.
have Hc w : (w^T *m S *m v) 0 0 = 0.
  apply: (paper_main_discriminant _ _ (Hq w)) => t.
  by have := Hq (v + t *: w); rewrite paper_main_form_line // Hv' add0r.
apply/matrixP => k j; rewrite [j]ord1 [RHS]mxE.
have := Hc (delta_mx k 0).
by rewrite trmx_delta -mulmxA -rowE [fun_of_matrix (row _ _) _ _]mxE.
Qed.

(* A nonzero quadratic form value forces S <> 0. *)
Lemma paper_main_form_neq0 S v : paper_main_quadratic_form S v != 0 -> S != 0.
Proof.
apply: contra => /eqP ->.
by rewrite /paper_main_quadratic_form; apply/eqP; rewrite big1 // => i _; rewrite big1 // => j _; rewrite mxE mulr0 mul0r.
Qed.

End Psd.
