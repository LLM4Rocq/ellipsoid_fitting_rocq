From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum zmodp matrix.
From GaussianAnalysis.fourier Require Import boolean_fourier.

(**md**************************************************************************)
(* # Product smoothing of matrix squares: the definitions                     *)
(*                                                                            *)
(* The definitions of the theorem 'Fourier smoothing of matrix squares',      *)
(* target T11 of phase 13 (AGENTS.md, section Phase 13). For each coordinate  *)
(* i < t, mu i is a law on a finite type X, nu i a law on a finite type M of  *)
(* averaging parameters, and pi i m z, for m in M and z in 'rV['F_2]_a, a law *)
(* on X, the channel. Laws on finite types are probability vectors            *)
(* (prob_vec). For m in t.-tuple M and y in 'M['F_2]_(t, a), the product      *)
(* average of F : t.-tuple X -> V draws the coordinates x_i independently     *)
(* from the channels pi i m_i y_i, where y_i is the row i of y:               *)
(*   prod_avg pi F m y = \sum_x (\prod_i pi i m_i y_i x_i) F x.               *)
(* The hypotheses smoothing_hyps mu nu pi theta say that the channels average *)
(* to mu i under nu i, \sum_m nu i m pi i m z x = mu i x, and that they       *)
(* contract the variance by theta: for every g : X -> R,                      *)
(*   \sum_m nu i m (\sum_x pi i m z x g x - \sum_x mu i x g x)^2              *)
(*     <= theta \sum_x mu i x g x^2.                                          *)
(* For a matrix function H on 'M['F_2]_(t, a) and a branch q, with            *)
(* H_p = fcoef H p the Fourier coefficients of boolean_fourier.v, the         *)
(* weighted Gram matrix                                                       *)
(*   weighted_gram lambda H q = \sum_p lambda^(blk_dist q p) H_p H_p^T        *)
(* is the matrix C_q of the manuscript. For lambda > 0 it is positive         *)
(* semidefinite, and its trace is the weighted Fourier mass                   *)
(* \sum_p lambda^(blk_dist q p) |H_p|_F^2.                                    *)
(*                                                                            *)
(* T11 says that, if L lambda^2 C_L theta <= 1 with L = 2^a and               *)
(* C_L = 2^(L - 1), the product averages of a positive semidefinite F with    *)
(* traces at most B are sums of squares \sum_q H_q^T H_q whose weighted Gram  *)
(* matrices have mean squared Frobenius norm at most 2^t B^2, so that the     *)
(* Fourier coefficients of each H_q concentrate near its center q. This file  *)
(* holds the definitions only; T11 is stated in applications/.                *)
(*                                                                            *)
(* A Rocq formalization of the credited argument of the theorem 'Fourier      *)
(* smoothing of matrix squares' of 'Exponential PSD rank of positively        *)
(* shifted matching matrices' (family 126 of the OpenAI math collection,      *)
(* revision 1581d4cbd, source/sections/fourier-smoothing.tex, lines 42-98).   *)
(* It follows no Lean module: the Lean development of family 126 has neither  *)
(* Boolean characters nor product smoothing. Departures from the manuscript,  *)
(* none of which changes the proof:                                           *)
(* - the coordinate laws are arbitrary probability vectors, mu i on one type  *)
(*   X and nu i on one type M, where the manuscript has the uniform laws of   *)
(*   sets X_i and M_i: the application draws subsets of two sizes, and a      *)
(*   uniform law on a set X_i is a probability vector on a type that contains *)
(*   every X_i;                                                               *)
(* - lambda > 0, where the manuscript has lambda > 1: the weights             *)
(*   lambda^(blk_dist q p) increase with the distance only when lambda > 1;   *)
(* - the frequencies and the points are F_2 matrices, as in                   *)
(*   boolean_fourier.v.                                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*                     prob_vec w == w is nonnegative with sum 1              *)
(*              prod_avg pi F m y == \sum_x (\prod_i pi i (tnth m i)          *)
(*                                     (row i y) (tnth x i)) *: F x           *)
(*   smoothing_hyps mu nu pi theta == the laws, the marginal identity and the *)
(*                                   variance contraction above               *)
(*       weighted_gram lambda H q == \sum_p lambda ^+ blk_dist q p *:         *)
(*                                     (fcoef H p *m (fcoef H p)^T)           *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section laws.
Variable R : numDomainType.

(* w is a probability vector on the finite type T. *)
Definition prob_vec (T : finType) (w : T -> R) : Prop :=
  (forall x, 0 <= w x) /\ \sum_x w x = 1.

Variables (X M : finType) (t a : nat).

(* The product average of F: the coordinate i of x is drawn from the law
   pi i (tnth m i) (row i y), independently. *)
Definition prod_avg (V : lmodType R) (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R)
    (F : t.-tuple X -> V) (m : t.-tuple M) (y : 'M['F_2]_(t, a)) : V :=
  \sum_(x : t.-tuple X)
     (\prod_(i < t) pi i (tnth m i) (row i y) (tnth x i)) *: F x.

(* The hypotheses of product smoothing: mu i, nu i and every channel
   pi i m y are probability vectors; the channels average to mu i under nu i;
   and they contract the variance by theta. *)
Definition smoothing_hyps (mu : 'I_t -> X -> R) (nu : 'I_t -> M -> R)
    (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R) (theta : R) : Prop :=
  [/\ forall i, prob_vec (mu i), forall i, prob_vec (nu i),
      forall i m y, prob_vec (pi i m y),
      forall i y x, \sum_m nu i m * pi i m y x = mu i x &
      forall i y (g : X -> R),
        \sum_m nu i m * (\sum_x pi i m y x * g x - \sum_x mu i x * g x) ^+ 2
          <= theta * \sum_x mu i x * g x ^+ 2].

End laws.

Section gram.
Variables (R : numFieldType) (t a r : nat).

(* C_q = \sum_p lambda^(blk_dist q p) \hat H_p \hat H_p^T, the weighted Gram
   matrix of the branch q. *)
Definition weighted_gram (lambda : R) (Rw : nat)
    (H : 'M['F_2]_(t, a) -> 'M[R]_(Rw, r)) (q : 'M['F_2]_(t, a)) : 'M[R]_Rw :=
  \sum_(p : 'M['F_2]_(t, a))
     lambda ^+ blk_dist q p *: (fcoef H p *m (fcoef H p)^T).

End gram.

(* An example: the uniform law of a nonempty finite type. *)
Example prob_vec_uniform (R : numFieldType) (T : finType) :
  (0 < #|T|)%N -> prob_vec (fun _ : T => (#|T|%:R)^-1 : R).
Proof.
move=> T0; split => [x|]; first by rewrite invr_ge0 ler0n.
by rewrite sumr_const -[_ *+ _]mulr_natl mulfV // pnatr_eq0 -lt0n.
Qed.
