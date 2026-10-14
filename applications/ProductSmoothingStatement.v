From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum zmodp matrix.
From mathcomp Require Import reals.
From GaussianAnalysis.matrix Require Import euclidean psd_part.
From GaussianAnalysis.fourier Require Import boolean_fourier product_smoothing.

(**md**************************************************************************)
(* # Product smoothing of matrix squares: the statement                       *)
(*                                                                            *)
(* Target T11 of phase 13 (AGENTS.md, section Phase 13; the plan              *)
(* notes/phase13-plan.md, section 2). The statement of a Rocq formalization   *)
(* of the credited argument of the theorem 'Fourier smoothing of matrix       *)
(* squares' of 'Exponential PSD rank of positively shifted matching matrices' *)
(* (family 126 of the OpenAI math collection, revision 1581d4cbd,             *)
(* source/sections/fourier-smoothing.tex, lines 42-98), in a general form.    *)
(* This file holds the statement only. The collection has no Lean version of  *)
(* it.                                                                        *)
(*                                                                            *)
(* Setting. R is any realType; t, a and r are natural numbers, L = 2^a and    *)
(* C_L = 2^(L-1), the constant of the orthogonal splitting (T5). The points   *)
(* and the frequencies are the F_2 matrices 'M['F_2]_(t, a): t blocks, the    *)
(* rows, of a bits. The definitions are those of fourier/boolean_fourier.v    *)
(* (the character, the Fourier coefficient fcoef, normalized by the number of *)
(* points, and the block distance blk_dist, the number of rows where two      *)
(* frequencies differ) and of fourier/product_smoothing.v (prob_vec,          *)
(* prod_avg, smoothing_hyps, weighted_gram); psdmx is that of                 *)
(* matrix/psd_part.v and frobenius the Frobenius norm of matrix/euclidean.v.  *)
(*                                                                            *)
(* - For i < t, mu i is a probability vector on a finite type X, nu i one on  *)
(*   a finite type M, and pi i m z, for m in M and z in 'rV['F_2]_a, a        *)
(*   probability vector on X, the channel. smoothing_hyps mu nu pi theta says *)
(*   that these are probability vectors, that the channels average to mu i    *)
(*   under nu i, and that they contract the variance by theta: for every g :  *)
(*   X -> R and every z, sum_m nu i m (sum_x pi i m z x g x - sum_x mu i x g  *)
(*   x)^2 <= theta sum_x mu i x g x^2.                                        *)
(* - F : t.-tuple X -> 'M[R]_r is positive semidefinite with tr (F x) <= B,   *)
(*   and prod_avg pi F m y = sum_x (prod_i pi i m_i y_i x_i) F x is its       *)
(*   product average, y_i the row i of y.                                     *)
(* - lambda > 0 and L lambda^2 C_L theta <= 1.                                *)
(*                                                                            *)
(* product_smoothing_statement: there are a row dimension Rw and matrices H m *)
(* q y of 'M[R]_(Rw, r), for m in t.-tuple M and q, y in 'M['F_2]_(t, a), one *)
(* family for every history m and branch q, such that                         *)
(*                                                                            *)
(* (a) prod_avg pi F m y = sum_q (H m q y)^T (H m q y) for every m and y;     *)
(*                                                                            *)
(* (b) the mean over m, under the product of the nu i, of sum_q |C_q^m|_F^2   *)
(* is at most 2^t B^2, where C_q^m = weighted_gram lambda (H m q) q = sum_p   *)
(* lambda^(blk_dist q p) Hhat_(q,p) Hhat_(q,p)^T and Hhat_(q,p) = fcoef (H m  *)
(* q) p is the Fourier coefficient of y |-> H m q y at p;                     *)
(*                                                                            *)
(* (c) some m of positive weight, prod_i nu i m_i > 0, has sum_q sum_p        *)
(* lambda^(blk_dist q p) |Hhat_(q,p)|_F^2 <= L^t sqrt r B sqrt (2^t).         *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - Shared witnesses (the user's amendment 4 of 14 October 2026): one family *)
(*   H, with one row dimension for all histories and branches, carries the    *)
(*   sums of squares (a), the averaged potential estimate (b) and, at a tuple *)
(*   of positive weight chosen from the same family, the coefficient estimate *)
(*   (c). The conjunction of an existential form of (a, b) with one of (a, c) *)
(*   would allow two different families, a weaker conclusion; these two forms *)
(*   are corollaries in product_smoothing.v.                                  *)
(* - The coordinate laws mu i and nu i are arbitrary probability vectors on   *)
(*   one type X and one type M, where the manuscript has the uniform laws of  *)
(*   sets X_i and M_i: the application draws subsets of two sizes.            *)
(* - lambda > 0, where the manuscript has lambda > 1, which the proof does    *)
(*   not use; the weights lambda^(blk_dist q p) increase with the distance    *)
(*   only when lambda > 1. The manuscript writes C_q^m = U U^T with U the     *)
(*   concatenation of the lambda^(dist/2) Hhat_(q,p); here the sum is written *)
(*   out, with no square root of lambda.                                      *)
(* - t, a and r may be 0, where the manuscript has t, a, r >= 1, and B > 0 is *)
(*   not assumed: the hypotheses force B >= 0, and the degenerate cases hold. *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition product_smoothing_statement : Prop :=
  forall (R : realType) (X M : finType) (t a r : nat)
         (mu : 'I_t -> X -> R) (nu : 'I_t -> M -> R)
         (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R) (theta B lambda : R)
         (F : t.-tuple X -> 'M[R]_r),
  smoothing_hyps mu nu pi theta ->
  (forall x, psdmx (F x)) -> (forall x, \tr (F x) <= B) ->
  0 < lambda -> (2 ^ a)%:R * lambda ^+ 2 * 2 ^+ (2 ^ a).-1 * theta <= 1 ->
  exists (Rw : nat)
         (H : t.-tuple M -> 'M['F_2]_(t, a) -> 'M['F_2]_(t, a) ->
              'M[R]_(Rw, r)),
    [/\ forall m y, prod_avg pi F m y = \sum_q (H m q y)^T *m H m q y,
        \sum_(m : t.-tuple M) (\prod_(i < t) nu i (tnth m i)) *
           \sum_q frobenius (weighted_gram lambda (H m q) q) ^+ 2
          <= 2 ^+ t * B ^+ 2 &
        exists2 m : t.-tuple M, 0 < \prod_(i < t) nu i (tnth m i) &
          \sum_q \sum_p lambda ^+ blk_dist q p
                         * frobenius (fcoef (H m q) p) ^+ 2
            <= (2 ^ a)%:R ^+ t * Num.sqrt r%:R * B * Num.sqrt (2 ^+ t)].
