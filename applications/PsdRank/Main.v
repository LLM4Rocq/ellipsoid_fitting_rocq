From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint zmodp.
From mathcomp Require Import matrix.
From mathcomp Require Import boolp archimedean.
From mathcomp Require Import reals arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean psd_part psd_splitting.
From GaussianAnalysis.matrix Require Import real_spectral psd_factorization.
From GaussianAnalysis.fourier Require Import boolean_fourier product_smoothing.
From GaussianAnalysis.probability Require Import mixture.
From GaussianApplications Require Import PsdRankDefinitions PsdRankStatement.
From GaussianApplications Require Import PsdNormalizationStatement.
From GaussianApplications Require Import ProductSmoothingStatement.
From GaussianApplications Require Import ProductSmoothingTheorem.
From GaussianApplications.PsdRank Require Import Model.

(**md**************************************************************************)
(* # The final step of the PSD rank bound for shifted matching matrices       *)
(*                                                                            *)
(* Item P6 of phase 13 (AGENTS.md, section Phase 13): the skeleton of the     *)
(* final step of the main theorem of 'Exponential PSD rank of positively      *)
(* shifted matching matrices' (family 126 of the OpenAI math collection,      *)
(* revision 1581d4cbd, source/sections/matching.tex, lines 41-66 and          *)
(* 114-218), a Rocq formalization of the credited argument. It proves         *)
(* psd_rank_statement of PsdRankStatement.v from explicit hypotheses, each    *)
(* named in the statements below. Compiling the skeleton does not validate    *)
(* them; phase 14 proves them, and PsdRankTheorem.v proves the main theorem   *)
(* from psd_rank_from_cell_data with T = 1000, choosing the cell size k from  *)
(* the conditions of the lemmas of the local averaging (Cells.v) and of the   *)
(* realization (Realization.v). The file follows no Lean module: the Lean     *)
(* development of the collection proves a weaker claim by another route       *)
(* (Main.lean).                                                               *)
(*                                                                            *)
(* T10 and T11 are used through their theorems, psd_normalization             *)
(* (matrix/psd_factorization.v) and product_smoothing_theorem                 *)
(* (ProductSmoothingTheorem.v); of T11 only the coefficient conclusion, at    *)
(* one tuple of positive weight, is used.                                     *)
(*                                                                            *)
(* Five accepted statements of packet P are used through their lemmas of      *)
(* boolean_fourier.v: the character algebra (bchar_algebra), the block        *)
(* distance as a metric (blk_dist_metric), Fourier inversion                  *)
(* (fcoef_inversion), the coefficients of a combination of characters         *)
(* (fcoef_expansion), and the translation of low block degree                 *)
(* (low_blk_deg_translate).                                                   *)
(*                                                                            *)
(* The hypothesis of psd_rank_from_cell_data:                                 *)
(* - cell_data, for every R, cells of a fixed size k, a fixed T and constants *)
(*   theta and lambda chosen before rho, with L lambda^2 C_L theta <= 1       *)
(*   (matching-local-smallness) and lambda >= (64 L^4)^T: for every           *)
(*   0 < rho < 1, every even n and every even t >= T with                     *)
(*   k t <= n < k (t + 2), local laws mu, nu and channels pi with             *)
(*   smoothing_hyps and the contraction theta (local-averaging.tex, Lemma     *)
(*   'Local averaging'), the realization U, M of rows and columns by odd sets *)
(*   and perfect matchings with A_n(rho)(U x, M m) = f y on the support of    *)
(*   the product restriction (matching.tex, lines 68-101), and a parity       *)
(*   functional for f at block degree t / T and eps = 1 - rho (parity.tex,    *)
(*   Proposition 'Parity functional', with the expander lemma).               *)
(*                                                                            *)
(* The proof:                                                                 *)
(* - final_step_core: the truncation of each branch to the frequencies within *)
(*   block distance D of the branch, the bound n (16 L^2)^-t on the discarded *)
(*   part (matching-tail), the uniform error 2 n (4 L)^-t + n (16 L^2)^-t     *)
(*   (matching-uniform-error), and the contradiction with the parity          *)
(*   functional, by the character translation of the squares.                 *)
(* - final_step: from a PSD factorization of A_n(rho) of size r <= 2^t, T10   *)
(*   (with B = n) and T11 give the squares (matching-squares) and the         *)
(*   coefficient bound (matching-fourier-bound), and the realization gives f  *)
(*   as a sum of squares (matching-full-squares).                             *)
(* - psd_rank_from_cell_data: K = 2 k; t is the largest even integer with     *)
(*   k t <= n; every factorization has a size r > 2^t >= 2^(n / (2 k)).       *)
(*                                                                            *)
(* Departures from the manuscript, all equivalent:                            *)
(* - D = t / T for a fixed T in place of floor(tau t) with tau = 1/1000, and  *)
(*   lambda >= (64 L^4)^T in place of lambda^tau >= 64 L^4.                   *)
(* - G^(1/2) is replaced by a Gram factor B with G = B^T B (psdmx_gram).      *)
(* - The uniform error comes from 2 <S, E> <= d |S|^2 + |E|^2 / d with        *)
(*   d = (4 L)^-t (mxdot_young).                                              *)
(*                                                                            *)
(* ```                                                                        *)
(*   parity_functional D eps f == a linear functional, nonnegative on the     *)
(*                                squares of the functions of block degree    *)
(*                                at most D, equal to - eps at f, and         *)
(*                                bounded by L^t times the supremum norm      *)
(* cell_data a theta n t D rho == local laws, a realization and a parity      *)
(*                                functional, for t cells of a bits each      *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section sums.
Variable R : realType.

(* The square of the norm of a sum of k matrices is at most k times the sum
   of the squares of their norms. *)
Lemma mxdot_sum_le m n (I : finType) (P : pred I) (X : I -> 'M[R]_(m, n)) :
  mxdot (\sum_(i | P i) X i) (\sum_(i | P i) X i) <=
  #|P|%:R * \sum_(i | P i) mxdot (X i) (X i).
Proof.
have two_le (A B : 'M[R]_(m, n)) : 2 * mxdot A B <= mxdot A A + mxdot B B.
  by have := mxdot_ge0 (A - B); rewrite mxdotBl !mxdotBr (mxdotC B A); lra.
rewrite mxdot_suml; under eq_bigr do rewrite mxdot_sumr.
set a := fun i => mxdot (X i) (X i).
apply: (@le_trans _ _ ((\sum_(i | P i) \sum_(j | P j) (a i + a j)) / 2)).
  rewrite ler_pdivlMr // mulr_suml; apply: ler_sum => i _.
  by rewrite mulr_suml; apply: ler_sum => j _; rewrite mulrC two_le.
rewrite (eq_bigr (fun i => a i *+ #|P| + \sum_(j | P j) a j)).
  by move=> i _; rewrite big_split /= sumr_const.
rewrite big_split /= sumr_const -sumrMnl.
rewrite -mulr2n -[_ *+ 2]mulr_natr mulfK ?pnatr_eq0 // -mulr_natl.
by rewrite mulr1 mulr_natl sumrMnl.
Qed.

Lemma mxdot_mulmx_le m n p (X : 'M[R]_(m, n)) (B : 'M[R]_(p, n)) :
  mxdot (X *m B^T) (X *m B^T) <= mxdot X X * mxdot B B.
Proof.
have := frobenius_mulmx X B^T; rewrite frobenius_trmx => h.
rewrite -!frobenius_sqr -exprMn.
by rewrite lerXn2r ?nnegrE ?frobenius_ge0 ?mulr_ge0 ?frobenius_ge0.
Qed.

(* 2 <A, E> <= d |A|^2 + |E|^2 / d for d > 0. *)
Lemma mxdot_young m n (A E : 'M[R]_(m, n)) (d : R) : 0 < d ->
  `|2 * mxdot A E| <= d * mxdot A A + d^-1 * mxdot E E.
Proof.
move=> d0; have du : d * d^-1 = 1 by rewrite mulfV // gt_eqF.
have hp := mxdot_ge0 (d *: A + E); have hm := mxdot_ge0 (d *: A - E).
rewrite mxdotDl !mxdotDr !mxdotZl !mxdotZr (mxdotC E A) in hp.
rewrite mxdotBl !mxdotBr !mxdotZl !mxdotZr (mxdotC E A) in hm.
rewrite ler_norml; apply/andP; split.
  by rewrite -(ler_pM2l d0) mulrN mulrDr [d * (d^-1 * _)]mulrA du mul1r; lra.
by rewrite -(ler_pM2l d0) mulrDr [d * (d^-1 * _)]mulrA du mul1r; lra.
Qed.

(* A positive semidefinite matrix is a Gram matrix. *)
Lemma psdmx_gram n (G : 'M[R]_n) : psdmx G -> exists B : 'M[R]_n, G = B^T *m B.
Proof.
move=> [Gs Gp]; have [P Po [d GE]] := symmetric_spectral Gs.
have d0 : forall i, 0 <= d 0 i by apply/(spectral_psd Po GE).
exists (diag_mx (\row_i Num.sqrt (d 0 i)) *m P).
rewrite trmx_mul tr_diag_mx mulmxA -[_ *m diag_mx _ *m diag_mx _]mulmxA.
rewrite mulmx_diag GE; congr (_ *m diag_mx _ *m _); apply/rowP => i.
by rewrite !mxE -expr2 sqr_sqrtr.
Qed.

(* tr ((sum_q H_q^T H_q) B^T B) = sum_q |H_q B^T|^2. *)
Lemma mxtrace_gram_sum (I : finType) m k n (H : I -> 'M[R]_(m, n))
    (B : 'M[R]_(k, n)) :
  \tr ((\sum_q (H q)^T *m H q) *m (B^T *m B)) =
  \sum_q mxdot (H q *m B^T) (H q *m B^T).
Proof.
rewrite mulmx_suml raddf_sum; apply: eq_bigr => q _.
by rewrite mxdot_trace trmx_mul trmxK /= -mulmxA mxtrace_mulC !mulmxA.
Qed.

End sums.


Lemma final_step_arith (R : realType) (L n : R) (t : nat) : 0 < L ->
  L ^+ t * (2 * n / (4 * L) ^+ t + n / (16 * L ^+ 2) ^+ t) =
  2 * n / 4 ^+ t + n / (16 * L) ^+ t.
Proof.
move=> L0; have u0 : L ^+ t != 0 by rewrite expf_neq0 // gt_eqF.
have v0 : (4 : R) ^+ t != 0 by rewrite expf_neq0 // pnatr_eq0.
have w0 : (16 : R) ^+ t != 0 by rewrite expf_neq0 // pnatr_eq0.
by rewrite !exprMn; field.
Qed.

(* The tail of matching.tex, (matching-tail): with r <= 2^t and
   lambda^(D + 1) >= (64 L^4)^t, the weight of the discarded coefficients is
   at most n / (16 L^2)^t. *)
Lemma tail_arith (R : realType) (L n lam : R) (t r : nat) :
  0 < L -> 0 <= n -> (r <= 2 ^ t)%N -> (64 * L ^+ 4) ^+ t <= lam ->
  L ^+ t * r%:R / lam * (L ^+ t * Num.sqrt r%:R * n * Num.sqrt (2 ^+ t))
    <= n / (16 * L ^+ 2) ^+ t.
Proof.
move=> L0 n0 rt hl; have u0 : 0 < L ^+ t by rewrite exprn_gt0.
have c0 : 0 < (64 * L ^+ 4) ^+ t.
  by rewrite exprn_gt0 // mulr_gt0 // exprn_gt0.
have lam0 : 0 < lam by apply: lt_le_trans hl.
have r2 : (r%:R : R) <= 2 ^+ t by rewrite -natrX ler_nat.
have sq2 : Num.sqrt (2 ^+ t) * Num.sqrt (2 ^+ t) = (2 : R) ^+ t.
  by rewrite -expr2 sqr_sqrtr // exprn_ge0.
(* r^(3/2) 2^(t/2) <= 4^t *)
have rbd : r%:R * Num.sqrt r%:R * Num.sqrt (2 ^+ t) <= (4 : R) ^+ t.
  have s1 : Num.sqrt (r%:R : R) <= Num.sqrt (2 ^+ t).
    by rewrite ler_sqrt // exprn_ge0.
  apply: le_trans (_ : 2 ^+ t * Num.sqrt (2 ^+ t) * Num.sqrt (2 ^+ t) <= _).
    apply: ler_wpM2r; first exact: sqrtr_ge0.
    by apply: ler_pM => //; rewrite ?ler0n ?sqrtr_ge0.
  by rewrite -mulrA sq2 -exprMn (_ : (2 : R) * 2 = 4) // -natrM.
have -> : L ^+ t * r%:R / lam * (L ^+ t * Num.sqrt r%:R * n * Num.sqrt (2 ^+ t))
    = (L ^+ t * L ^+ t * n) * (r%:R * Num.sqrt r%:R * Num.sqrt (2 ^+ t)) / lam.
  move: (L ^+ t) (r%:R : R) (Num.sqrt (r%:R : R)) (Num.sqrt (2 ^+ t : R)).
  by move=> A B C E'; clear; ring.
have k0 : 0 <= L ^+ t * L ^+ t * n by rewrite mulr_ge0 // mulr_ge0 // ltW.
apply: le_trans (_ : L ^+ t * L ^+ t * n * 4 ^+ t / lam <= _).
  by apply: ler_wpM2r; [rewrite invr_ge0 ltW | exact: ler_wpM2l].
apply: le_trans (_ : _ <= L ^+ t * L ^+ t * n * 4 ^+ t / (64 * L ^+ 4) ^+ t) _.
  apply: ler_wpM2l; first by rewrite mulr_ge0 // exprn_ge0.
  by rewrite lef_pV2 ?posrE.
have e64 : (64 : R) = 4 * 16 by rewrite -natrM.
rewrite e64 !exprMn.
have u1 : L ^+ t != 0 by rewrite gt_eqF.
have v0 : (4 : R) ^+ t != 0 by rewrite expf_neq0 // pnatr_eq0.
have w0 : (16 : R) ^+ t != 0 by rewrite expf_neq0 // pnatr_eq0.
move: u1 v0 w0; move: (L ^+ t) ((4 : R) ^+ t) ((16 : R) ^+ t) => U V W u1 v0 w0.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

Section final_step.
Variables (R : realType) (t a : nat).
Local Notation cube := 'M['F_2]_(t, a).
Local Notation L := (2 ^ a)%N.

Lemma card_cube : #|{: cube}| = (L ^ t)%N.
Proof. by rewrite card_mx card_Fp // mulnC expnM. Qed.

(* The separating functional of the proposition 'Parity functional' for f,
   at block degree D and eps = 1 - rho. *)
Definition parity_functional (D : nat) (eps : R) (f : cube -> R^o) : Prop :=
  exists Phi : (cube -> R^o) -> R,
  [/\ forall g h : cube -> R^o, Phi (fun y => g y + h y) = Phi g + Phi h,
      forall (c : R) (g : cube -> R^o), Phi (fun y => c * g y) = c * Phi g,
      forall g : cube -> R^o, low_blk_deg D g -> 0 <= Phi (fun y => g y ^+ 2),
      Phi f = - eps &
      forall (h : cube -> R^o) (c : R), (forall y, `|h y : R| <= c) ->
        `|Phi h| <= L%:R ^+ t * c].

Lemma final_step_core (Rw r s D : nat) (n eps lambda : R)
    (H : cube -> cube -> 'M[R]_(Rw, r)) (B : 'M[R]_(s, r))
    (f : cube -> R^o) :
  (forall y, f y = \sum_q mxdot (H q y *m B^T) (H q y *m B^T)) ->
  (forall y, f y <= n) ->
  mxdot B B <= r%:R -> (r <= 2 ^ t)%N ->
  \sum_q \sum_p lambda ^+ blk_dist q p * frobenius (fcoef (H q) p) ^+ 2
     <= L%:R ^+ t * Num.sqrt r%:R * n * Num.sqrt (2 ^+ t) ->
  1 <= lambda -> (64 * L%:R ^+ 4) ^+ t <= lambda ^+ D.+1 ->
  parity_functional D eps f ->
  2 * n / 4 ^+ t + n / (16 * L%:R) ^+ t < eps ->
  False.
Proof.
move=> fE fn BB rt hF l1 hl [Phi [PhiD PhiZ Phisq Phif Phinorm]] small.
have [ch0 chD chC chpm] := bchar_algebra t a R.
have [dist_deg dist0 distC dist_tri dist_tr] := blk_dist_metric t a.
have L0 : (0 : R) < L%:R by rewrite ltr0n expn_gt0.
have NE : (#|{: cube}|%:R : R) = L%:R ^+ t by rewrite card_cube natrX.
have chsq (p y : cube) : bchar R p y ^+ 2 = 1.
  by case: (chpm p y) => ->; rewrite ?expr1n ?sqrrN ?expr1n.
(* the truncation K q and the tail E q of the branch q *)
pose Hh q p := fcoef (H q) p.
pose K q y := \sum_(p | (blk_dist q p <= D)%N) bchar R p y *: Hh q p.
pose E q y := \sum_(p | (D < blk_dist q p)%N) bchar R p y *: Hh q p.
pose fstar (y : cube) : R^o := \sum_q mxdot (K q y *m B^T) (K q y *m B^T).
pose E2 := n / (16 * L%:R ^+ 2) ^+ t.
have HKE q y : H q y = K q y + E q y.
  rewrite {1}(fcoef_inversion (H q) y) (bigID (fun p => (blk_dist q p <= D)%N)) /=.
  by congr (_ + _); apply: eq_bigl => p; rewrite ltnNge.
have lpos : 0 < lambda by apply: lt_le_trans l1.
have lD0 : 0 < lambda ^+ D.+1 by rewrite exprn_gt0.
(* Cauchy-Schwarz over the at most L^t characters of the tail, |G| <= r, and
   lambda^(D + 1) <= lambda^(dist q p) on the tail *)
have step q y : mxdot (E q y *m B^T) (E q y *m B^T) <=
    L%:R ^+ t * r%:R / lambda ^+ D.+1 *
    \sum_p lambda ^+ blk_dist q p * frobenius (fcoef (H q) p) ^+ 2.
  rewrite /E mulmx_suml; under eq_bigr do rewrite -scalemxAl.
  apply: le_trans (mxdot_sum_le _ _) _.
  under eq_bigr do rewrite mxdotZl mxdotZr mulrA -expr2 chsq mul1r.
  have cP : (#|(fun i : cube => (D < blk_dist q i)%N)|%:R : R) <= L%:R ^+ t.
    by rewrite -NE ler_nat max_card.
  have S1 : \sum_(i | (D < blk_dist q i)%N)
        mxdot (Hh q i *m B^T) (Hh q i *m B^T) <=
      r%:R / lambda ^+ D.+1 *
      \sum_p lambda ^+ blk_dist q p * frobenius (fcoef (H q) p) ^+ 2.
    rewrite mulr_sumr; apply: (@le_trans _ _ (\sum_(p | (D < blk_dist q p)%N)
      r%:R / lambda ^+ D.+1 *
      (lambda ^+ blk_dist q p * frobenius (fcoef (H q) p) ^+ 2))).
      apply: ler_sum => p pD; apply: le_trans (mxdot_mulmx_le _ _) _.
      rewrite frobenius_sqr; set x := mxdot (fcoef (H q) p) (fcoef (H q) p).
      have x0 : 0 <= x by exact: mxdot_ge0.
      have lle : lambda ^+ D.+1 <= lambda ^+ blk_dist q p.
        exact: ler_weXn2l.
      apply: le_trans (ler_wpM2l x0 BB) _.
      have h1 : r%:R * x <=
          r%:R * x * (lambda ^+ blk_dist q p / lambda ^+ D.+1).
        by rewrite ler_peMr ?mulr_ge0 // ler_pdivlMr // mul1r.
      apply: le_trans (_ : x * r%:R <=
        r%:R * x * (lambda ^+ blk_dist q p / lambda ^+ D.+1)) _.
        by rewrite mulrC.
      move: (r%:R : R) (lambda ^+ blk_dist q p) (lambda ^+ D.+1) => A Lo Ld.
      clearbody x; clear x0 h1; move: x => X.
      by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
    rewrite [X in _ <= X](bigID (fun p => (D < blk_dist q p)%N)) /= lerDl.
    apply: sumr_ge0 => p _; apply: mulr_ge0.
      by rewrite divr_ge0 ?ler0n ?ltW.
    by apply: mulr_ge0; [exact: exprn_ge0 (ltW lpos) | exact: sqr_ge0].
  apply: le_trans (ler_pM _ _ cP S1) _; first by rewrite ler0n.
    by apply: sumr_ge0 => p _; exact: mxdot_ge0.
  by rewrite !mulrA.
have n0 : 0 <= n.
  apply: le_trans (fn 0); rewrite fE; apply: sumr_ge0 => q _.
  exact: mxdot_ge0.
(* the discarded part is uniformly small, matching.tex (matching-tail) *)
have Ebound y : \sum_q mxdot (E q y *m B^T) (E q y *m B^T) <= E2.
  apply: le_trans (ler_sum _ (fun q _ => step q y)) _.
  rewrite -mulr_sumr; apply: le_trans (ler_wpM2l _ hF) _.
    by rewrite divr_ge0 ?mulr_ge0 ?exprn_ge0 ?ler0n ?ltW.
  exact: tail_arith.
(* the uniform error, (matching-uniform-error), from
   2 <S, E> <= d |S|^2 + |E|^2 / d with d = (4 L)^-t *)
have unif y : `|f y - fstar y : R| <= 2 * n / (4 * L%:R) ^+ t + E2.
  have c0 : 0 < (4 * L%:R) ^+ t :> R by rewrite exprn_gt0 // mulr_gt0.
  set d := ((4 * L%:R) ^+ t)^-1; have d0 : 0 < d by rewrite invr_gt0.
  have key q : mxdot (H q y *m B^T) (H q y *m B^T)
      - mxdot (K q y *m B^T) (K q y *m B^T) =
      2 * mxdot (H q y *m B^T) (E q y *m B^T)
      - mxdot (E q y *m B^T) (E q y *m B^T).
    have -> : K q y = H q y - E q y by rewrite (HKE q y) addrK.
    rewrite mulmxBl mxdotBl !mxdotBr (mxdotC (E q y *m B^T) (H q y *m B^T)).
    by rewrite mulr2n mulrDl mul1r; ring.
  rewrite fE /fstar -sumrB; under eq_bigr do rewrite key.
  rewrite sumrB; apply: le_trans (ler_normB _ _) _.
  have hS : \sum_q mxdot (H q y *m B^T) (H q y *m B^T) <= n by rewrite -fE.
  have hE := Ebound y.
  have h1 : `|\sum_q 2 * mxdot (H q y *m B^T) (E q y *m B^T)| <=
      d * n + d^-1 * E2.
    apply: le_trans (ler_norm_sum _ _ _) _.
    apply: le_trans (ler_sum _ (fun q _ =>
      mxdot_young (H q y *m B^T) (E q y *m B^T) d0)) _.
    rewrite big_split /= -!mulr_sumr.
    apply: lerD; first by apply: ler_wpM2l => //; apply: ltW.
    by apply: ler_wpM2l => //; rewrite invr_ge0 ltW.
  have h2 : `|\sum_q mxdot (E q y *m B^T) (E q y *m B^T)| <= E2.
    by rewrite ger0_norm // sumr_ge0 // => q _; exact: mxdot_ge0.
  have dE : d^-1 * E2 = n * d.
    rewrite /E2 /d invrK.
    have -> : 16 * L%:R ^+ 2 = (4 * L%:R) ^+ 2 :> R.
      by rewrite exprMn (_ : (4 : R) ^+ 2 = 16) // -natrX.
    rewrite exprAC; have c1 : (4 * L%:R) ^+ t != 0 :> R by rewrite gt_eqF.
    by move: c1; move: ((4 * L%:R) ^+ t) => C c1; field.
  by rewrite dE in h1; move: h1 h2; set X := `|_|; set Y := `|_|; lra.
(* fstar is a sum of squares of functions of block degree at most D: the
   character chi_q moves the frequencies p of the branch q, within block
   distance D of q, to block degree at most D *)
have Pstar : 0 <= Phi fstar.
  have P0 : Phi (fun _ => 0) = 0.
    rewrite -[RHS](mul0r (Phi (fun _ => 0))) -PhiZ.
    by congr Phi; apply: funext => y; rewrite mul0r.
  have Phi_seq (I : Type) (sq : seq I) (F : I -> cube -> R^o) :
      Phi (fun y => \sum_(k <- sq) F k y) = \sum_(k <- sq) Phi (F k).
    elim: sq => [|k sq IH].
      rewrite big_nil; transitivity (Phi (fun _ => 0)); last exact: P0.
      by congr Phi; apply: funext => y; rewrite big_nil.
    rewrite big_cons -IH -PhiD; congr Phi; apply: funext => y.
    exact: big_cons.
  have lowg q i j :
      low_blk_deg D (fun y => bchar R q y * (K q y *m B^T) i j : R^o).
    apply: (@low_blk_deg_translate t a R R^o D (fun y => (K q y *m B^T) i j : R^o) q) => p pD.
    have -> : (fun y => (K q y *m B^T) i j : R^o) =
        (fun y => \sum_(p' : cube) bchar R p' y *:
          ((if (blk_dist q p' <= D)%N then (Hh q p' *m B^T) i j else 0) : R^o)).
      apply: funext => y; rewrite /K mulmx_suml summxE big_mkcond /=.
      apply: eq_bigr => p' _; case: ifP => _; last by rewrite scaler0.
      by rewrite -scalemxAl mxE.
    by rewrite fcoef_expansion distC leqNgt pD.
  have fsE : fstar = (fun y =>
      \sum_q \sum_i \sum_j (bchar R q y * (K q y *m B^T) i j) ^+ 2 : R^o).
    apply: funext => y; rewrite /fstar; apply: eq_bigr => q _; rewrite /mxdot.
    apply: eq_bigr => i _; apply: eq_bigr => j _.
    by rewrite exprMn chsq mul1r expr2.
  rewrite fsE (Phi_seq _ _ (fun q y =>
    \sum_i \sum_j (bchar R q y * (K q y *m B^T) i j) ^+ 2)).
  apply: sumr_ge0 => q _.
  rewrite (Phi_seq _ _ (fun i y =>
    \sum_j (bchar R q y * (K q y *m B^T) i j) ^+ 2)).
  apply: sumr_ge0 => i _.
  rewrite (Phi_seq _ _ (fun j y => (bchar R q y * (K q y *m B^T) i j) ^+ 2)).
  apply: sumr_ge0 => j _.
  exact: Phisq (lowg q i j).
have Pdiff : `|Phi (fun y => f y + (-1) * fstar y)| <=
    L%:R ^+ t * (2 * n / (4 * L%:R) ^+ t + E2).
  by apply: Phinorm => y; rewrite mulN1r; exact: unif.
rewrite PhiD PhiZ Phif mulN1r in Pdiff.
have arith : L%:R ^+ t * (2 * n / (4 * L%:R) ^+ t + E2) =
    2 * n / 4 ^+ t + n / (16 * L%:R) ^+ t.
  exact: final_step_arith.
rewrite arith in Pdiff.
have e0 : 0 <= eps.
  apply/ltW/(le_lt_trans _ small).
  apply: addr_ge0; apply: divr_ge0;
    by rewrite ?mulr_ge0 ?exprn_ge0 ?mulr_ge0 ?ler0n.
have : eps + Phi fstar <= `|- eps - Phi fstar|.
  by rewrite -opprD normrN ger0_norm ?addr_ge0.
by move: Pdiff small Pstar; set P := Phi fstar; set S := 2 * n / _ + _; lra.
Qed.

(* The final step of the proof of the main theorem (matching.tex, lines
   114-218): a PSD factorization of A_n(rho) of size r <= 2^t, normalized by
   T10 and smoothed by T11, contradicts the realization of the cells by
   matchings and the parity functional. *)
Lemma final_step (n D r : nat)
    (rho lambda theta : R) (X M : finType) (mu : 'I_t -> X -> R)
    (nu : 'I_t -> M -> R) (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R)
    (U : t.-tuple X -> odd_set n) (Mm : t.-tuple M -> perfect_matching n)
    (fy : cube -> R^o) :
  smoothing_hyps mu nu pi theta ->
  1 <= lambda -> L%:R * lambda ^+ 2 * 2 ^+ L.-1 * theta <= 1 ->
  (64 * L%:R ^+ 4) ^+ t <= lambda ^+ D.+1 ->
  (forall m x y, 0 < \prod_(i < t) nu i (tnth m i) ->
     0 < \prod_(i < t) pi i (tnth m i) (row i y) (tnth x i) ->
     shifted_matching_mx rho (U x) (Mm m) = fy y) ->
  parity_functional D (1 - rho) fy -> rho <= 1 ->
  2 * n%:R / 4 ^+ t + n%:R / (16 * L%:R) ^+ t < 1 - rho ->
  psd_factorization (@shifted_matching_mx n R rho) r -> (r <= 2 ^ t)%N ->
  False.
Proof.
move=> hs l1 hlam hl hreal hpar r1 small [F0 [G0 [F0p G0p AE]]] rt.
have [hmu hnu hpi hmix hvar] := hs.
have An (V : odd_set n) (W : perfect_matching n) :
    \tr (F0 V *m G0 W) <= n%:R by rewrite -AE shifted_matching_mx_le.
(* a tuple of local data, hence a perfect matching *)
have [m0 _] : exists m0 : t.-tuple M, true.
  case: (posnP t) => [t0|tpos]; first by exists (tcast (esym t0) [tuple]).
  have [_ s1] := hnu (Ordinal tpos).
  case: (pickP (fun m => nu (Ordinal tpos) m != 0)) => [m _|h].
    by exists [tuple of nseq t m].
  exfalso; move: s1; rewrite big1.
    by move=> m _; apply/eqP; move: (h m) => /= /negbFE.
  by move/esym/eqP; rewrite oner_eq0.
have J0 : (0 < #|{: perfect_matching n}|)%N.
  by apply/card_gt0P; exists (Mm m0).
(* T10: the factors normalized, with row traces at most n *)
have [F' [G' [F'p G'p FGE F'tr G'tr]]] := psd_normalization J0 F0p G0p An.
(* T11, with B = n, for the rows F' (U x) *)
have l0 : 0 < lambda by apply: lt_le_trans l1.
have [Rw [H [Hsq Hpot [m mpos Hfou]]]] :=
  product_smoothing_theorem R X M t a r mu nu pi theta n%:R lambda
    (fun x => F' (U x)) hs (fun x => F'p (U x)) (fun x => F'tr (U x)) l0 hlam.
have [B GE] := psdmx_gram (G'p (Mm m)).
pose w y x := \prod_(i < t) pi i (tnth m i) (row i y) (tnth x i).
have w0 y x : 0 <= w y x.
  apply: prodr_ge0 => i _.
  by have [p0 _] := hpi i (tnth m i) (row i y); exact: p0.
have w1 y : \sum_x w y x = 1.
  rewrite /w (big_tuple_distr (fun i z => pi i (tnth m i) (row i y) z)).
  by rewrite big1 // => i _; have [_ p1] := hpi i (tnth m i) (row i y).
(* (matching-pairing): the averaged row factor pairs with G_M(m) to f *)
have real y : \tr (prod_avg pi (fun x => F' (U x)) m y *m G' (Mm m)) = fy y.
  rewrite /prod_avg mulmx_suml raddf_sum /=.
  transitivity (\sum_x w y x * fy y); last by rewrite -mulr_suml w1 mul1r.
  apply: eq_bigr => x _; rewrite -scalemxAl mxtraceZ FGE -AE.
  have [w00|wpos] := eqVneq (w y x) 0.
    by rewrite /w in w00 *; rewrite w00 !mul0r.
  by rewrite (hreal m x y mpos) // lt_def wpos w0.
(* (matching-full-squares) *)
have fyE y : fy y = \sum_q mxdot (H m q y *m B^T) (H m q y *m B^T).
  by rewrite -(real y) Hsq GE mxtrace_gram_sum.
have fyn y : fy y <= n%:R.
  case: (pickP (fun x => 0 < w y x)) => [x xpos|hx].
    by rewrite -(hreal m x y mpos xpos) shifted_matching_mx_le.
  exfalso; move: (w1 y); rewrite big1.
    move=> x _; apply/eqP; rewrite eq_le w0 andbT leNgt; exact/negbT/hx.
  by move/esym/eqP; rewrite oner_eq0.
have BB : mxdot B B <= r%:R by rewrite mxdot_trace mxtrace_mulC -GE G'tr.
exact: (final_step_core fyE fyn BB rt Hfou l1 hl hpar small).
Qed.

End final_step.

(* (t + 2)^2 <= 4^t for t >= 2. *)
Lemma sq_le_exp4 t : (2 <= t)%N -> (t.+2 ^ 2 <= 4 ^ t)%N.
Proof.
elim: t => [//|t IH] t2; case: t IH t2 => [//|[|t]] IH t2 //.
rewrite (expnS 4 t.+2).
apply: (@leq_trans (4 * t.+4 ^ 2)); last by rewrite leq_mul2l /= IH.
rewrite (_ : 4 = 2 ^ 2)%N // -expnMn leq_exp2r //.
by rewrite mul2n -addnn -[X in (X < _)%N]addn0 ltn_add2l.
Qed.

(* The ingredients of the proof that phase 14 proves, for the size n, the
   number t of cells, the block degree D and the shift rho: the local laws of
   local-averaging.tex with the contraction theta, the realization of the
   cells by matchings (matching.tex, lines 68-101), and the parity functional
   of parity.tex for the function f they realize. *)
Definition cell_data (R : realType) (a : nat) (theta : R) (n t D : nat)
    (rho : R) : Prop :=
  exists (X M : finType) (mu : 'I_t -> X -> R) (nu : 'I_t -> M -> R)
         (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R)
         (U : t.-tuple X -> odd_set n) (Mm : t.-tuple M -> perfect_matching n)
         (fy : 'M['F_2]_(t, a) -> R^o),
  [/\ smoothing_hyps mu nu pi theta,
      forall m x y, 0 < \prod_(i < t) nu i (tnth m i) ->
        0 < \prod_(i < t) pi i (tnth m i) (row i y) (tnth x i) ->
        shifted_matching_mx rho (U x) (Mm m) = fy y &
      parity_functional D (1 - rho) fy].

(* The main statement from T10, T11, the lemmas of packet P, and cell data
   for every large even n, with the constants chosen before rho: a = d - 1
   bits per block, theta with L lambda^2 C_L theta <= 1, lambda with
   lambda >= (64 L^4)^T, the block degree D = t / T, and cells of size k. *)
Theorem psd_rank_from_cell_data (a : nat) :
  (forall R : realType, exists (k T : nat) (theta lambda : R),
     [/\ (0 < k)%N && (0 < T)%N, 1 <= lambda,
         (2 ^ a)%:R * lambda ^+ 2 * 2 ^+ (2 ^ a).-1 * theta <= 1,
         (64 * (2 ^ a)%:R ^+ 4) ^+ T <= lambda &
         forall rho : R, 0 < rho < 1 -> forall n t : nat,
           ~~ odd n -> ~~ odd t -> (T <= t)%N ->
           (k * t <= n)%N -> (n < k * t.+2)%N ->
           cell_data a theta n t (t %/ T) rho]) ->
  psd_rank_statement.
Proof.
move=> hcells R.
have [k [T [theta [lambda [/andP[k0 T0] l1 hlam hlT hc]]]]] := hcells R.
exists (2 * k)%N; split; first by rewrite muln_gt0.
move=> rho /andP[r0 r1]; have e0 : 0 < 1 - rho by rewrite subr_gt0.
(* n0 = k (S + 2), with S >= T, S >= 2 and S > 3 k / (1 - rho) *)
have [N hN] : exists N : nat, 3 * k%:R / (1 - rho) < N%:R.
  exists (Num.bound (3 * k%:R / (1 - rho))); apply: archi_boundP.
  by rewrite divr_ge0 ?mulr_ge0 ?ler0n ?ltW.
pose S := maxn T (maxn N 2).
exists (k * S.+2)%N => n en hn r hf.
(* t, the largest even integer with k t <= n *)
pose t := ((n %/ k)./2).*2.
have te : ~~ odd t by rewrite /t odd_double.
have t_le : (t <= n %/ k)%N.
  by rewrite -[X in (_ <= X)%N](odd_double_half (n %/ k)) leq_addl.
have t_ge : (n %/ k <= t.+1)%N.
  rewrite -[X in (X <= _)%N](odd_double_half (n %/ k)).
  by rewrite -addn1 addnC leq_add2l leq_b1.
have kt : (k * t <= n)%N.
  by apply: leq_trans (leq_mul (leqnn k) t_le) _; rewrite mulnC leq_divM.
have nlt : (n < k * t.+2)%N.
  apply: leq_trans (ltn_ceil n k0) _.
  by rewrite [X in (_ <= X)%N]mulnC leq_mul2r ltnS t_ge orbT.
have tS : (S <= t)%N.
  have : (S.+2 <= n %/ k)%N by rewrite leq_divRL // mulnC.
  by move=> h; have := leq_trans h t_ge; rewrite ltnS => /ltnW.
have tT : (T <= t)%N by apply: leq_trans tS; rewrite leq_maxl.
have tN : (N <= t)%N.
  by apply: leq_trans tS; rewrite /S (leq_trans _ (leq_maxr _ _)) // leq_maxl.
have t2 : (2 <= t)%N.
  by apply: leq_trans tS; rewrite /S (leq_trans _ (leq_maxr _ _)) // leq_maxr.
(* every factorization has a size r > 2^t, and n <= 2 k t *)
case: (leqP r (2 ^ t)) => [rt|rt]; last first.
  apply: (@leq_trans (2 ^ (t * (2 * k)))).
    rewrite leq_exp2l // mulnCA mulnC; apply: ltnW (leq_trans nlt _).
    rewrite (mulnC t k) -mulnA leq_mul2l; apply/orP; right.
    by rewrite muln2 -addnn -addn2 leq_add2l.
  by rewrite expnM leq_exp2r ?muln_gt0 // ltnW.
exfalso; have r01 : 0 < rho < 1 by rewrite r0 r1.
have [X [M [mu [nu [pi [U [Mm [fy [hs hreal hpar]]]]]]]]] :=
  hc rho r01 n t en te tT kt nlt.
(* lambda^(t / T + 1) >= (64 L^4)^t *)
have hl' : (64 * (2 ^ a)%:R ^+ 4) ^+ t <= lambda ^+ (t %/ T).+1.
  set c := 64 * (2 ^ a)%:R ^+ 4 : R.
  have c1 : 1 <= c.
    rewrite /c; apply: mulr_ege1; first by rewrite ler1n.
    by rewrite exprn_ege1 // ler1n expn_gt0.
  apply: le_trans (_ : c ^+ (T * (t %/ T).+1) <= _).
    apply: ler_weXn2l => //; rewrite mulnC; exact: ltnW (ltn_ceil t T0).
  by rewrite exprM lerXn2r ?nnegrE ?exprn_ge0 ?(le_trans ler01 c1)
    ?(le_trans ler01 l1).
(* 2 n 4^-t + n (16 L)^-t < 1 - rho, from n < k (t + 2) and 4^t >= (t + 2)^2 *)
have u0 : (0 : R) < 4 ^+ t by rewrite exprn_gt0.
have hu : (t.+2%:R ^+ 2 : R) <= 4 ^+ t.
  rewrite -natrX (_ : (4 : R) = 4%:R) // -natrX ler_nat.
  exact: sq_le_exp4.
have hw : (4 : R) ^+ t <= (16 * (2 ^ a)%:R) ^+ t.
  rewrite lerXn2r ?nnegrE ?mulr_ge0 ?ler0n //.
  rewrite -[X in X <= _]mulr1 (_ : (4 : R) = 4 * 1) ?mulr1 //.
  rewrite -natrM ler_nat.
  by rewrite (leq_trans _ (leq_pmulr _ (expn_gt0 2 a))).
have hn' : (n%:R : R) < k%:R * t.+2%:R by rewrite -natrM ltr_nat.
have hEt : 3 * k%:R < (1 - rho) * t.+2%:R.
  have : 3 * k%:R / (1 - rho) < t.+2%:R.
    apply: lt_le_trans hN _; rewrite ler_nat (leq_trans tN) //.
    by rewrite -addn2 leq_addr.
  by rewrite ltr_pdivrMr; [exact: e0 | rewrite [_ * (1 - rho)]mulrC].
have key : 3 * n%:R < (1 - rho) * 4 ^+ t.
  have t20 : (0 : R) < t.+2%:R by rewrite ltr0n.
  have k0' : (0 : R) <= k%:R by rewrite ler0n.
  move: hn' hEt hu e0 t20 k0'; set u := (4 : R) ^+ t.
  set tt := (t.+2)%:R : R; set nn := (n%:R : R); set kk := (k%:R : R).
  set E := 1 - rho => hn' hEt hu e0 t20 k0'.
  by clearbody u tt nn kk E; nra.
have w0 : 0 < (16 * (2 ^ a)%:R) ^+ t :> R by apply: lt_le_trans hw.
have h1 : n%:R / (16 * (2 ^ a)%:R) ^+ t <= n%:R / 4 ^+ t :> R.
  by rewrite ler_wpM2l ?ler0n // lef_pV2 ?posrE.
have h2 : 3 * n%:R / 4 ^+ t < 1 - rho :> R by rewrite ltr_pdivrMr // mulrC.
have small' : 2 * n%:R / 4 ^+ t + n%:R / (16 * (2 ^ a)%:R) ^+ t < 1 - rho :> R.
  move: h1 h2; set u := (4 : R) ^+ t.
  set w := (16 * (2 ^ a)%:R : R) ^+ t; set nn := (n%:R : R).
  by rewrite -!mulrA; lra.
exact: (final_step hs l1 hlam hl' hreal hpar
  (ltW r1) small' hf rt).
Qed.
