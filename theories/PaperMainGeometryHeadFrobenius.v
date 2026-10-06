(* The Frobenius pairing and norm of matrices, for the head correction of
   the satisfiable phase (manuscript lem:head-correction-bounds, lines
   971-1061).

   paper_main_pairing S M is sum_ij S_ij M_ij (PaperMainGeometryPsd) and
   paper_main_frobenius S is the square root of paper_main_pairing S S
   (PaperMainGeometryHomogeneous). This module proves the bilinearity of the
   pairing, the Cauchy-Schwarz inequality <S, M>^2 <= <S, S> <M, M>, the bound
   |<S, M>| <= |S|_F |M|_F, the homogeneity of the norm and the two triangle
   inequalities. These finite-dimensional facts are used by
   PaperMainGeometryHeadCorrection. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section HeadFrobenius.
Variable d : nat.
Implicit Types (S M A B : 'M[R]_d) (a : R).

(* 1. Bilinearity of the pairing. *)

Lemma pmh_pairingDl A B M :
  paper_main_pairing (A + B) M = paper_main_pairing A M + paper_main_pairing B M.
Proof.
rewrite /paper_main_pairing -big_split /=; apply: eq_bigr => i _.
rewrite -big_split /=; apply: eq_bigr => j _.
by rewrite mxE mulrDl.
Qed.

Lemma pmh_pairingDr S A B :
  paper_main_pairing S (A + B) = paper_main_pairing S A + paper_main_pairing S B.
Proof.
by rewrite paper_main_pairingC pmh_pairingDl !(paper_main_pairingC _ _ S).
Qed.

Lemma pmh_pairingNl A M : paper_main_pairing (- A) M = - paper_main_pairing A M.
Proof.
rewrite /paper_main_pairing -sumrN; apply: eq_bigr => i _.
rewrite -sumrN; apply: eq_bigr => j _.
by rewrite mxE mulNr.
Qed.

Lemma pmh_pairingNr S A : paper_main_pairing S (- A) = - paper_main_pairing S A.
Proof. by rewrite paper_main_pairingC pmh_pairingNl paper_main_pairingC. Qed.

Lemma pmh_pairingBl A B M :
  paper_main_pairing (A - B) M = paper_main_pairing A M - paper_main_pairing B M.
Proof. by rewrite pmh_pairingDl pmh_pairingNl. Qed.

Lemma pmh_pairingBr S A B :
  paper_main_pairing S (A - B) = paper_main_pairing S A - paper_main_pairing S B.
Proof. by rewrite pmh_pairingDr pmh_pairingNr. Qed.

Lemma pmh_pairingZl a A M :
  paper_main_pairing (a *: A) M = a * paper_main_pairing A M.
Proof.
by rewrite paper_main_pairingC paper_main_pairing_scale paper_main_pairingC.
Qed.

Lemma pmh_pairing0l M : paper_main_pairing 0 M = 0.
Proof.
rewrite /paper_main_pairing big1 // => i _; rewrite big1 // => j _.
by rewrite mxE mul0r.
Qed.

Lemma pmh_pairing0r S : paper_main_pairing S 0 = 0.
Proof. by rewrite paper_main_pairingC pmh_pairing0l. Qed.

Lemma pmh_pairing_suml m (c : 'I_m -> R) (A : 'I_m -> 'M[R]_d) M :
  paper_main_pairing (\sum_(i < m) c i *: A i) M =
  \sum_(i < m) c i * paper_main_pairing (A i) M.
Proof.
rewrite paper_main_pairingC paper_main_pairing_sum.
by apply: eq_bigr => i _; rewrite paper_main_pairingC.
Qed.

(* 2. The Cauchy-Schwarz inequality, from <b S - a M, b S - a M> >= 0 with
   a = <S, M> and b = <M, M>. *)

Theorem pmh_pairing_cauchy_schwarz S M :
  paper_main_pairing S M ^+ 2 <= paper_main_pairing S S * paper_main_pairing M M.
Proof.
have [M0|HM] := eqVneq M 0.
  by rewrite M0 pmh_pairing0r pmh_pairing0l expr2 !mulr0.
have Hb : 0 < paper_main_pairing M M by exact: paper_main_pairing_self_gt0.
have H := paper_main_pairing_self_ge0 _
  (paper_main_pairing M M *: S - paper_main_pairing S M *: M).
rewrite pmh_pairingBl !pmh_pairingBr !pmh_pairingZl !paper_main_pairing_scale in H.
rewrite (paper_main_pairingC _ M S) in H.
nra.
Qed.

(* 3. The Frobenius norm. *)

Lemma pmh_frobenius_ge0 S : 0 <= paper_main_frobenius S.
Proof. exact: sqrtr_ge0. Qed.

Lemma pmh_frobenius_sqr S : paper_main_frobenius S ^+ 2 = paper_main_pairing S S.
Proof.
rewrite /paper_main_frobenius sqr_sqrtr //.
exact: paper_main_pairing_self_ge0.
Qed.

Lemma pmh_frobenius0 : paper_main_frobenius (0 : 'M[R]_d) = 0.
Proof. by rewrite /paper_main_frobenius pmh_pairing0l sqrtr0. Qed.

Lemma pmh_frobenius_gt0 S : S != 0 -> 0 < paper_main_frobenius S.
Proof.
move=> HS; rewrite /paper_main_frobenius sqrtr_gt0.
exact: paper_main_pairing_self_gt0.
Qed.

Lemma pmh_frobeniusZ a S :
  paper_main_frobenius (a *: S) = `|a| * paper_main_frobenius S.
Proof.
rewrite /paper_main_frobenius pmh_pairingZl paper_main_pairing_scale mulrA -expr2.
by rewrite sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Lemma pmh_frobeniusN S : paper_main_frobenius (- S) = paper_main_frobenius S.
Proof. by rewrite -scaleN1r pmh_frobeniusZ normrN normr1 mul1r. Qed.

Lemma pmh_frobeniusB S M :
  paper_main_frobenius (S - M) = paper_main_frobenius (M - S).
Proof. by rewrite -pmh_frobeniusN opprB. Qed.

Lemma pmh_frobenius_normalize S :
  S != 0 -> paper_main_frobenius ((paper_main_frobenius S)^-1 *: S) = 1.
Proof.
move=> HS; have Hp : 0 < paper_main_frobenius S by exact: pmh_frobenius_gt0.
have Hi : 0 <= (paper_main_frobenius S)^-1 by rewrite invr_ge0 ltW.
by rewrite pmh_frobeniusZ (ger0_norm Hi) (mulVf (lt0r_neq0 Hp)).
Qed.

(* 4. The pairing bound and the triangle inequalities. *)

Theorem pmh_pairing_frobenius_bound S M :
  `|paper_main_pairing S M| <= paper_main_frobenius S * paper_main_frobenius M.
Proof.
have H0 := paper_main_pairing_self_ge0 _ S.
rewrite -sqrtr_sqr /paper_main_frobenius -(sqrtrM _ H0).
apply: ler_wsqrtr; exact: pmh_pairing_cauchy_schwarz.
Qed.

Theorem pmh_frobenius_triangle S M :
  paper_main_frobenius (S + M) <= paper_main_frobenius S + paper_main_frobenius M.
Proof.
have HS := pmh_frobenius_ge0 S; have HM := pmh_frobenius_ge0 M.
have HSM : 0 <= paper_main_frobenius S + paper_main_frobenius M by exact: addr_ge0.
have HB := pmh_pairing_frobenius_bound S M.
have Hn := ler_norm (paper_main_pairing S M).
rewrite -[X in _ <= X](ger0_norm HSM) -sqrtr_sqr {1}/paper_main_frobenius.
apply: ler_wsqrtr.
rewrite pmh_pairingDl !pmh_pairingDr (paper_main_pairingC _ M S).
rewrite -(pmh_frobenius_sqr S) -(pmh_frobenius_sqr M).
nra.
Qed.

Theorem pmh_frobenius_reverse_triangle S M :
  `|paper_main_frobenius (S + M) - paper_main_frobenius S| <= paper_main_frobenius M.
Proof.
have H1 := pmh_frobenius_triangle S M.
have H2 := pmh_frobenius_triangle (S + M) (- M).
rewrite addrK pmh_frobeniusN in H2.
rewrite ler_norml; apply/andP; split; lra.
Qed.

End HeadFrobenius.
