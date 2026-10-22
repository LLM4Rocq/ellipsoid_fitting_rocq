From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint zmodp.
From mathcomp Require Import matrix sesquilinear reals boolp.
From mathcomp Require Import ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part.
From GaussianAnalysis.matrix Require Import psd_splitting psd_duality.
From GaussianAnalysis.fourier Require Import boolean_fourier.
From GaussianAnalysis.probability Require Import finite_mean.

(**md**************************************************************************)
(* # Product smoothing of matrix squares                                      *)
(*                                                                            *)
(* The theorem 'Fourier smoothing of matrix squares', target T11 of phase 13  *)
(* (AGENTS.md, section Phase 13), with its definitions. For each coordinate i *)
(* < t, mu i is a law on a finite type X, nu i a law on a finite type M of    *)
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
(* is the matrix C_q of the manuscript.                                       *)
(*                                                                            *)
(* product_smoothing (T11): let L = 2^a, C_L = 2^(L - 1), lambda > 0 with     *)
(* L lambda^2 C_L theta <= 1, and F : t.-tuple X -> 'M[R]_r positive          *)
(* semidefinite with tr (F x) <= B. There are a row dimension Rw and matrices *)
(* H m q y of 'M[R]_(Rw, r), one family for every history m and branch q,     *)
(* such that                                                                  *)
(* - prod_avg pi F m y = \sum_q (H m q y)^T H m q y for every m and y;        *)
(* - the mean over m, under the product of the nu i, of                       *)
(*   \sum_q |weighted_gram lambda (H m q) q|_F^2 is at most 2^t B^2;          *)
(* - some m of positive weight has                                            *)
(*   \sum_q \sum_p lambda^(blk_dist q p) |fcoef (H m q) p|_F^2                *)
(*   <= L^t sqrt r B sqrt (2^t). product_smoothing_potential and              *)
(*   product_smoothing_coef state the second and the third conclusion         *)
(*   separately, each with its own family. t, a and r may be 0, and B > 0 is  *)
(*   not assumed.                                                             *)
(*                                                                            *)
(* The proof. smoothing_step_one is one step of the construction, for one old *)
(* branch q and old functions G x of the input x of the new coordinate. The   *)
(* tagged stack smoothing_stack G m0 Y, built with \mxcol_, has one block for *)
(* each pair (y', x), and its Gram matrix is \sum_x pi m0 y x G x^T G x       *)
(* (smoothing_stack_gram). Its Fourier coefficient at col_mx z p has the      *)
(* blocks N^-1 chi_z(y') sqrt (pi m0 y' x) fcoef (G x) p                      *)
(* (fcoef_smoothing_stack), which give the Gram matrices split_gram m0 z of   *)
(* the new frequencies z. T5 (psd_splitting, here psd_splitting_fin) splits   *)
(* them by projections P_s, chosen for each m0 by constructive indefinite     *)
(* description; the new branches are the P_s times the stack, with the same   *)
(* squares, and their potential at most doubles in mean over m0:              *)
(* split_potential_le after the splitting, then stack_overlap_le and          *)
(* split_gram_overlap_le, by the overlap identity                             *)
(* (fcoef_smoothing_stack_gram), Jensen's inequality, the marginal identity   *)
(* and the variance hypothesis for matrices (contraction_mx). smoothing_param *)
(* iterates the step by induction on t, with the first block processed last   *)
(* ('M['F_2]_(1 + t, a) splits with col_mx), over a finite type P of          *)
(* parameters with nonnegative weights, the inputs of the coordinates not yet *)
(* processed; the base case is F = H^T H (psdmx_factor of                     *)
(* matrix/psd_duality.v). product_smoothing takes P = unit. The coefficient   *)
(* bound follows from the potential at a tuple of positive weight             *)
(* (exists_weight_le), by the trace bound tr C <= sqrt (r |I|) |C|_F for a    *)
(* weighted Gram matrix of r-column matrices indexed by I (mxtrace_gram_le),  *)
(* and by Cauchy-Schwarz over the 2^(t a) branches.                           *)
(*                                                                            *)
(* Proved besides, for any realType R:                                        *)
(* - sum_wsqr_le, frobenius_wsum_le, frobenius_sum_sqr_le: Cauchy-Schwarz     *)
(*   with nonnegative weights, for numbers and for squared Frobenius norms of *)
(*   matrices;                                                                *)
(* - mxtrace_gram, mxtrace_gram_mul, frobenius_gram, mxtrace_gram_le,         *)
(*   psdmx_gram: the trace, the trace of products, the norm, the trace bound  *)
(*   and the positivity of weighted Gram matrices \sum_i w_i h_i h_i^T;       *)
(*   mxtrace_le_frobenius: tr A <= sqrt n |A|_F;                              *)
(* - psd_splitting_fin: T5 for matrices indexed by a nonempty finite type Z,  *)
(*   with constant 2^(|Z| - 1);                                               *)
(* - sum_tuple_cons, prod_tuple_cons, sum_tuple0, sum_prod_prob,              *)
(*   prod_prob_ge0: sums over tuples and product laws; exists_weight_le: a    *)
(*   mean below c is attained below c at a point of positive weight;          *)
(* - contraction_ge0, contraction_mx: theta >= 0, and the variance hypothesis *)
(*   for matrices; prod_avg_cons: the product average along its first         *)
(*   coordinate.                                                              *)
(*                                                                            *)
(* Two examples: after the definitions, the uniform law of a nonempty finite  *)
(* type is a probability vector (prob_vec_uniform); at the end of the file,   *)
(* constant channels pi i m z = mu i satisfy smoothing_hyps mu nu pi 0 for    *)
(* all probability vectors mu i and nu i (smoothing_hyps_const).              *)
(*                                                                            *)
(* A Rocq formalization of the credited argument of the theorem 'Fourier      *)
(* smoothing of matrix squares' of 'Exponential PSD rank of positively        *)
(* shifted matching matrices' (family 126 of the OpenAI math collection,      *)
(* revision 1581d4cbd, source/sections/fourier-smoothing.tex, lines 42-98).   *)
(* It follows no Lean module: the Lean development of family 126 has neither  *)
(* Boolean characters nor product smoothing. Departures from the manuscript,  *)
(* none of which changes the argument:                                        *)
(* - the coordinate laws are arbitrary probability vectors, mu i on one type  *)
(*   X and nu i on one type M, where the manuscript has the uniform laws of   *)
(*   sets X_i and M_i: the application draws subsets of two sizes, and a      *)
(*   uniform law on a set X_i is a probability vector on a type that contains *)
(*   every X_i;                                                               *)
(* - lambda > 0, where the manuscript has lambda > 1: the weights             *)
(*   lambda^(blk_dist q p) increase with the distance only when lambda > 1;   *)
(* - the frequencies and the points are F_2 matrices, as in                   *)
(*   boolean_fourier.v;                                                       *)
(* - the coordinates are processed from the last to the first, which relabels *)
(*   them; the row dimension of a stack is the sum over its |'rV_a| |X|       *)
(*   blocks of the old one, (L |X|)^t r in all, as in the manuscript;         *)
(* - the manuscript's bound tr C <= sqrt (rank C) |C|_F is replaced by        *)
(*   Cauchy-Schwarz on the diagonals of the r x r blocks (mxtrace_gram_le),   *)
(*   with the same constant;                                                  *)
(* - one family carries the three conclusions, as in the manuscript ('the     *)
(*   family can be chosen so that ... Consequently, at least one m satisfies  *)
(*   ...'); the statement in applications/ (T11) fixes this choice of shared  *)
(*   witnesses, the user's amendment 4 of 14 October 2026.                    *)
(*                                                                            *)
(* ```                                                                        *)
(*                     prob_vec w == w is nonnegative with sum 1              *)
(*              prod_avg pi F m y == \sum_x (\prod_i pi i (tnth m i)          *)
(*                                     (row i y) (tnth x i)) *: F x           *)
(*   smoothing_hyps mu nu pi theta == the laws, the marginal identity and the *)
(*                                   variance contraction above               *)
(*       weighted_gram lambda H q == \sum_p lambda ^+ blk_dist q p *:         *)
(*                                     (fcoef H p *m (fcoef H p)^T)           *)
(*       smoothing_stack pi G m0 Y == the tagged stack of one step            *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
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

(* ## The proof of product smoothing *)

Section matrix_tools.
Variable R : realType.
Implicit Types m n : nat.

(* Cauchy-Schwarz with nonnegative weights. *)
Lemma sum_wsqr_le (I : finType) (w z : I -> R) : (forall i, 0 <= w i) ->
  (\sum_i w i * z i) ^+ 2 <= (\sum_i w i) * \sum_i w i * z i ^+ 2.
Proof.
move=> w0; rewrite -subr_ge0.
have E : \sum_i \sum_j w i * w j * (z i - z j) ^+ 2 =
    2 * ((\sum_i w i) * \sum_i w i * z i ^+ 2 - (\sum_i w i * z i) ^+ 2).
  under eq_bigr do under eq_bigr do rewrite sqrrB !mulrDr mulrN.
  have S1 : \sum_i \sum_j w i * w j * z i ^+ 2 =
      (\sum_i w i) * \sum_i w i * z i ^+ 2.
    rewrite mulrC mulr_suml; apply: eq_bigr => i _; rewrite mulr_sumr.
    by apply: eq_bigr => j _; ring.
  have S2 : \sum_i \sum_j w i * w j * z j ^+ 2 =
      (\sum_i w i) * \sum_i w i * z i ^+ 2.
    rewrite mulr_suml; apply: eq_bigr => i _; rewrite mulr_sumr.
    by apply: eq_bigr => j _; ring.
  have S3 : \sum_i \sum_j w i * w j * (z i * z j *+ 2) =
      2 * (\sum_i w i * z i) ^+ 2.
    rewrite expr2 mulr_suml mulr_sumr; apply: eq_bigr => i _.
    rewrite mulr_sumr mulr_sumr; apply: eq_bigr => j _; rewrite -mulr_natl.
    ring.
  under eq_bigr do rewrite big_split /= sumrB.
  rewrite big_split /= sumrB S1 S2 S3; ring.
have : 0 <= \sum_i \sum_j w i * w j * (z i - z j) ^+ 2.
  by apply: sumr_ge0 => i _; apply: sumr_ge0 => j _;
    rewrite mulr_ge0 ?sqr_ge0 ?mulr_ge0.
by rewrite E pmulr_rge0.
Qed.

(* The same for matrices and the squared Frobenius norm. *)
Lemma frobenius_wsum_le (I : finType) (w : I -> R) m n
    (M : I -> 'M[R]_(m, n)) : (forall i, 0 <= w i) ->
  frobenius (\sum_i w i *: M i) ^+ 2 <=
    (\sum_i w i) * \sum_i w i * frobenius (M i) ^+ 2.
Proof.
move=> w0; rewrite frobenius_sqr.
under [X in _ <= _ * X]eq_bigr do rewrite frobenius_sqr /mxdot mulr_sumr.
rewrite [X in _ <= _ * X]exchange_big /= mulr_sumr /mxdot.
apply: ler_sum => j _.
under [X in _ <= _ * X]eq_bigr do rewrite mulr_sumr.
rewrite [X in _ <= _ * X]exchange_big /= mulr_sumr; apply: ler_sum => k _.
rewrite summxE -expr2.
rewrite (eq_bigr (fun i => w i * M i j k)) => [i _|]; first by rewrite mxE.
under [X in _ <= _ * X]eq_bigr do rewrite -expr2.
exact: sum_wsqr_le.
Qed.

(* Gram matrices of families of matrices with weights. *)
Lemma mxtrace_gram_mul (I J : finType) (w : I -> R) (v : J -> R) m n
    (h : I -> 'M[R]_(m, n)) (g : J -> 'M[R]_(m, n)) :
  \tr ((\sum_i w i *: (h i *m (h i)^T)) *m (\sum_j v j *: (g j *m (g j)^T))) =
  \sum_i \sum_j w i * v j * frobenius ((h i)^T *m g j) ^+ 2.
Proof.
rewrite mulmx_suml raddf_sum /=; apply: eq_bigr => i _.
rewrite mulmx_sumr raddf_sum /=; apply: eq_bigr => j _.
rewrite -scalemxAl -scalemxAr !mxtraceZ mulrA frobenius_sqr mxdot_trace.
rewrite trmx_mul trmxK; congr (_ * _).
by rewrite -!mulmxA mxtrace_mulC !mulmxA.
Qed.

Lemma frobenius_gram (I : finType) (w : I -> R) m n
    (h : I -> 'M[R]_(m, n)) :
  frobenius (\sum_i w i *: (h i *m (h i)^T)) ^+ 2 =
  \sum_i \sum_j w i * w j * frobenius ((h i)^T *m h j) ^+ 2.
Proof.
rewrite frobenius_sqr_sym ?mxtrace_gram_mul //.
apply/symmetricmxP; rewrite raddf_sum /=; apply: eq_bigr => i _.
by rewrite linearZ /= trmx_mul trmxK.
Qed.

Lemma mxtrace_gram (I : finType) (w : I -> R) m n (h : I -> 'M[R]_(m, n)) :
  \tr (\sum_i w i *: (h i *m (h i)^T)) = \sum_i w i * frobenius (h i) ^+ 2.
Proof.
rewrite raddf_sum /=; apply: eq_bigr => i _.
by rewrite mxtraceZ frobenius_sqr mxdot_trace.
Qed.

(* The trace of a square matrix is at most sqrt n times its norm. *)
Lemma mxtrace_le_frobenius n (A : 'M[R]_n) :
  \tr A <= Num.sqrt n%:R * frobenius A.
Proof.
have H1 : (\tr A) ^+ 2 <= n%:R * \sum_i A i i ^+ 2.
  have := @sum_wsqr_le 'I_n (fun _ => 1) (fun i => A i i) (fun _ => ler01).
  rewrite sumr_const card_ord /mxtrace; under eq_bigr do rewrite mul1r.
  by under [X in _ <= _ * X -> _]eq_bigr do rewrite mul1r.
have H2 : \sum_i A i i ^+ 2 <= mxdot A A.
  apply: ler_sum => i _; rewrite (bigD1 i) //= -expr2 lerDl.
  by apply: sumr_ge0 => j _; rewrite -expr2 sqr_ge0.
rewrite /frobenius -sqrtrM ?ler0n //; apply: le_trans (real_ler_norm _) _.
  by rewrite num_real.
rewrite -sqrtr_sqr ler_sqrt ?mulr_ge0 ?ler0n ?mxdot_ge0 //.
by apply: le_trans H1 _; rewrite ler_wpM2l ?ler0n.
Qed.

(* The trace of a weighted Gram matrix of n-column matrices indexed by I is
   at most sqrt (n |I|) times its Frobenius norm: no rank argument. *)
Lemma mxtrace_gram_le (I : finType) (w : I -> R) m n (h : I -> 'M[R]_(m, n)) :
  (forall i, 0 <= w i) ->
  \tr (\sum_i w i *: (h i *m (h i)^T)) <=
    Num.sqrt (n%:R * #|I|%:R) * frobenius (\sum_i w i *: (h i *m (h i)^T)).
Proof.
move=> w0; set C := \sum_i _.
set c := fun i => w i * frobenius ((h i)^T *m h i).
have c0 i : 0 <= c i by rewrite /c mulr_ge0 ?frobenius_ge0.
have E1 : \tr C <= Num.sqrt n%:R * \sum_i c i.
  rewrite /C mxtrace_gram mulr_sumr; apply: ler_sum => i _.
  rewrite /c [X in _ <= X]mulrCA; apply: ler_wpM2l; first exact: w0.
  rewrite frobenius_sqr mxdot_trace mxtrace_mulC.
  exact: mxtrace_le_frobenius.
have E2 : \sum_i c i <= Num.sqrt #|I|%:R * Num.sqrt (\sum_i c i ^+ 2).
  have cs : (\sum_i c i) ^+ 2 <= #|I|%:R * \sum_i c i ^+ 2.
    have := @sum_wsqr_le I (fun _ => 1) c (fun _ => ler01).
    rewrite sumr_const; under eq_bigr do rewrite mul1r.
    by under [X in _ <= _ * X -> _]eq_bigr do rewrite mul1r.
  have s0 : 0 <= \sum_i c i ^+ 2 by apply: sumr_ge0 => i _; rewrite sqr_ge0.
  rewrite -sqrtrM ?ler0n // -[X in X <= _]ger0_norm ?sumr_ge0 //.
  by rewrite -sqrtr_sqr ler_sqrt // mulr_ge0 ?ler0n.
have E3 : \sum_i c i ^+ 2 <= frobenius C ^+ 2.
  rewrite /C frobenius_gram; apply: ler_sum => i _.
  rewrite (bigD1 i) //= -[X in X <= _]addr0; apply: lerD.
    by rewrite /c exprMn expr2 mulrA.
  by apply: sumr_ge0 => j _; rewrite !mulr_ge0 ?frobenius_ge0 ?sqr_ge0.
apply: le_trans E1 _; rewrite sqrtrM ?ler0n // -mulrA.
apply: ler_wpM2l; first exact: sqrtr_ge0.
apply: le_trans E2 _; apply: ler_wpM2l; first exact: sqrtr_ge0.
rewrite -[X in _ <= X]ger0_norm ?frobenius_ge0 // -sqrtr_sqr ler_sqrt //.
exact: sqr_ge0.
Qed.

(* The orthogonal splitting (T5, psd_splitting) for matrices indexed by a
   nonempty finite type Z, with constant 2^(|Z| - 1). *)
Lemma psd_splitting_fin n (Z : finType) (A : Z -> 'M[R]_n) :
  (0 < #|Z|)%N -> (forall z, psdmx (A z)) ->
  exists P : Z -> 'M[R]_n,
  [/\ forall s, orthoprojmx (P s), \sum_s P s = 1%:M &
      \sum_z \sum_(s | s != z) frobenius (P s *m A z *m P s) ^+ 2 <=
        2 ^+ #|Z|.-1 * \sum_z \sum_(z' | z' != z) \tr (A z *m A z')].
Proof.
move=> Z0 Ap; have cZ : #|Z| = #|Z|.-1.+1 by rewrite prednK.
pose e (z : Z) : 'I_#|Z|.-1.+1 := cast_ord cZ (enum_rank z).
pose e' (i : 'I_#|Z|.-1.+1) : Z := enum_val (cast_ord (esym cZ) i).
have ee' : cancel e e' by move=> z; rewrite /e /e' cast_ordK enum_rankK.
have e'e : cancel e' e by move=> i; rewrite /e /e' enum_valK cast_ordKV.
have [P' [Po _ Psum Pb]] :=
  @psd_splitting R n _ (fun i => A (e' i)) (fun i => Ap _).
have be' : bijective e' by exact: (Bijective e'e ee').
have re (V : nmodType) (F : Z -> V) : \sum_z F z = \sum_i F (e' i).
  by rewrite (reindex e') //; exact: onW_bij.
have re2 (V : nmodType) (F : Z -> Z -> V) :
    \sum_z \sum_(s | s != z) F z s = \sum_i \sum_(j | j != i) F (e' i) (e' j).
  rewrite re; apply: eq_bigr => i _; rewrite (reindex e') /=.
    exact: (onW_bij _ be').
  by apply: eq_bigl => j; rewrite (inj_eq (can_inj e'e)).
exists (fun z => P' (e z)); split => //.
  by rewrite re; under eq_bigr do rewrite e'e.
rewrite (re2 _ (fun z s => frobenius (P' (e s) *m A z *m P' (e s)) ^+ 2)).
rewrite (re2 _ (fun z z' => \tr (A z *m A z'))).
by under eq_bigr do under eq_bigr do rewrite e'e.
Qed.

Lemma frobenius_sum_sqr_le (I : finType) m n (M : I -> 'M[R]_(m, n)) :
  frobenius (\sum_i M i) ^+ 2 <= #|I|%:R * \sum_i frobenius (M i) ^+ 2.
Proof.
have := @frobenius_wsum_le I (fun _ => 1) m n M (fun _ => ler01).
rewrite sumr_const; under eq_bigr do rewrite scale1r.
by under [X in _ <= _ * X -> _]eq_bigr do rewrite mul1r.
Qed.

Lemma psdmx_gram (I : finType) (w : I -> R) m n (h : I -> 'M[R]_(m, n)) :
  (forall i, 0 <= w i) -> psdmx (\sum_i w i *: (h i *m (h i)^T)).
Proof.
move=> w0; apply: psdmx_sum => i _; split.
  by apply/symmetricmxP; rewrite linearZ /= trmx_mul trmxK.
move=> x; rewrite -scalemxAl mxdotZr mulr_ge0 // -mulmxA mxdotC.
by rewrite mxdot_mulmxl mxdot_ge0.
Qed.

(* The potential after one splitting step, for one parameter. *)
Lemma split_potential_le n (Z : finType) (A P : Z -> 'M[R]_n) (lambda C : R) :
  0 <= lambda ->
  (forall s, orthoprojmx (P s)) -> \sum_s P s = 1%:M ->
  \sum_z \sum_(s | s != z) frobenius (P s *m A z *m P s) ^+ 2 <=
    C * \sum_z \sum_(z' | z' != z) \tr (A z *m A z') ->
  \sum_s frobenius (\sum_z lambda ^+ (s != z) *: (P s *m A z *m P s)) ^+ 2 <=
    #|Z|%:R * (\sum_z frobenius (A z) ^+ 2 +
      lambda ^+ 2 * (C * \sum_z \sum_(z' | z' != z) \tr (A z *m A z'))).
Proof.
move=> lam0 Po Psum Pb.
apply: le_trans (_ : \sum_s #|Z|%:R * \sum_z frobenius
    (lambda ^+ (s != z) *: (P s *m A z *m P s)) ^+ 2 <= _).
  by apply: ler_sum => s _; exact: frobenius_sum_sqr_le.
rewrite -mulr_sumr ler_wpM2l ?ler0n // exchange_big /=.
have E z : \sum_s frobenius (lambda ^+ (s != z) *: (P s *m A z *m P s)) ^+ 2 =
    frobenius (P z *m A z *m P z) ^+ 2 +
    lambda ^+ 2 * \sum_(s | s != z) frobenius (P s *m A z *m P s) ^+ 2.
  rewrite (bigD1 z) //= eqxx expr0 scale1r; congr (_ + _).
  rewrite mulr_sumr; apply: eq_bigr => s sz.
  by rewrite sz expr1 frobeniusZ ger0_norm // exprMn.
under eq_bigr do rewrite E.
rewrite big_split /= -mulr_sumr lerD //.
  apply: ler_sum => z _.
  have QMQ : 1%:M *m A z *m 1%:M = A z by rewrite mulmx1 mul1mx.
  have := frobenius_compress_le Po Psum QMQ.
  apply: le_trans; rewrite (bigD1 z) //= lerDl.
  by apply: sumr_ge0 => s _; rewrite sqr_ge0.
by rewrite ler_wpM2l // exprn_ge0.
Qed.

End matrix_tools.

Section prob_tools.
Variable R : realType.

Lemma sum_tuple_cons (V : nmodType) (T : finType) m
    (f : m.+1.-tuple T -> V) :
  \sum_(x : m.+1.-tuple T) f x =
  \sum_(x0 : T) \sum_(x : m.-tuple T) f [tuple of x0 :: x].
Proof. by rewrite pair_bigA (reindex _ (onW_bij _ (@bij_tuple_cons T m))). Qed.

Lemma prod_tuple_cons (T : finType) m (F : 'I_m.+1 -> T -> R) (x0 : T)
    (x : m.-tuple T) :
  \prod_(i < m.+1) F i (tnth [tuple of x0 :: x] i) =
  F ord0 x0 * \prod_(i < m) F (lift ord0 i) (tnth x i).
Proof.
rewrite big_ord_recl tnth0; congr (_ * _).
by apply: eq_bigr => i _; rewrite tnthS.
Qed.

Lemma sum_tuple0 (V : nmodType) (T : finType) (f : 0.-tuple T -> V) :
  \sum_(x : 0.-tuple T) f x = f [tuple].
Proof. by rewrite (big_pred1 [tuple]) // => x; rewrite inE tuple0 eqxx. Qed.

Lemma sum_prod_prob (T : finType) m (w : 'I_m -> T -> R) :
  (forall i, prob_vec (w i)) ->
  \sum_(x : m.-tuple T) \prod_(i < m) w i (tnth x i) = 1.
Proof.
elim: m w => [|m IH] w w1; first by rewrite sum_tuple0 big_ord0.
rewrite sum_tuple_cons.
under eq_bigr do under eq_bigr do rewrite prod_tuple_cons.
have IH' := IH (fun i => w (lift ord0 i)) (fun i => w1 _).
under eq_bigr do rewrite -mulr_sumr IH' mulr1.
exact: (w1 ord0).2.
Qed.

Lemma prod_prob_ge0 (T : finType) m (w : 'I_m -> T -> R) (x : m.-tuple T) :
  (forall i, prob_vec (w i)) -> 0 <= \prod_(i < m) w i (tnth x i).
Proof. by move=> w1; apply: prodr_ge0 => i _; exact: (w1 i).1. Qed.

(* A mean below c is attained below c at a point of positive weight. *)
Lemma exists_weight_le (I : finType) (w f : I -> R) (c : R) :
  (forall i, 0 <= w i) -> \sum_i w i = 1 -> \sum_i w i * f i <= c ->
  exists2 i, 0 < w i & f i <= c.
Proof.
move=> w0 w1 wf.
case: (pickP [pred i | (0 < w i) && (f i <= c)]) => [i /andP [wi fi]|none].
  by exists i.
have term0 i : 0 <= w i * (f i - c).
  move: (none i); rewrite /= => /negbT; rewrite negb_and -leNgt -ltNge.
  case/orP => [wi|fi]; last by rewrite mulr_ge0 // subr_ge0 ltW.
  by rewrite (@le_anti _ _ (w i) 0) ?mul0r // wi w0.
have sum0 : \sum_i w i * (f i - c) = 0.
  apply/eqP; rewrite eq_le sumr_ge0 ?andbT; first by move=> i _; exact: term0.
  under eq_bigr do rewrite mulrBr.
  by rewrite sumrB -mulr_suml w1 mul1r subr_le0.
have [i wi] : exists i, 0 < w i.
  have : [exists i, 0 < w i].
    apply: contraT => /existsPn H.
    have : \sum_i w i = 0.
      by apply: big1 => i _; apply/eqP; rewrite eq_le w0 andbT leNgt H.
    by rewrite w1 => /eqP; rewrite oner_eq0.
  by case/existsP => i wi; exists i.
have := @psumr_eq0P _ _ _ _ (fun j _ => term0 j) sum0 i isT.
move: (none i); rewrite /= wi /= => /negbT; rewrite -ltNge => fi /eqP.
by rewrite mulf_eq0 subr_eq0 (gt_eqF fi) (gt_eqF wi).
Qed.

End prob_tools.

Section channel_tools.
Variables (R : realType) (X M : finType) (a : nat).
Variables (mu : X -> R) (nu : M -> R) (pi : M -> 'rV['F_2]_a -> X -> R).
Variable theta : R.

Lemma contraction_ge0 z : prob_vec mu -> prob_vec nu ->
  (forall g : X -> R, \sum_m nu m * (\sum_x pi m z x * g x -
     \sum_x mu x * g x) ^+ 2 <= theta * \sum_x mu x * g x ^+ 2) ->
  0 <= theta.
Proof.
move=> [mu0 mu1] [nu0 _] var.
have S0 : \sum_x mu x * (fun _ => 0 : R) x <= 0.
  by rewrite big1 // => x _; rewrite mulr0.
have [x0 mx0 _] := exists_weight_le mu0 mu1 S0.
have := var (fun x => (x == x0)%:R).
rewrite [X in _ <= _ * X](bigD1 x0) //= eqxx expr1n mulr1.
rewrite [X in _ <= _ * (_ + X)]big1 => [x /negbTE ->|].
  by rewrite expr0n mulr0.
rewrite addr0 => H; have : 0 <= theta * mu x0.
  apply: le_trans H; apply: sumr_ge0 => m _.
  exact: mulr_ge0 (nu0 m) (sqr_ge0 _).
by rewrite pmulr_lge0.
Qed.

(* The variance hypothesis for matrix-valued functions, entry by entry. *)
Lemma contraction_mx z m n (Z : X -> 'M[R]_(m, n)) :
  (forall g : X -> R, \sum_m0 nu m0 * (\sum_x pi m0 z x * g x -
     \sum_x mu x * g x) ^+ 2 <= theta * \sum_x mu x * g x ^+ 2) ->
  \sum_m0 nu m0 * frobenius (\sum_x pi m0 z x *: Z x - \sum_x mu x *: Z x) ^+ 2
    <= theta * \sum_x mu x * frobenius (Z x) ^+ 2.
Proof.
move=> var.
under eq_bigr do rewrite frobenius_sqr /mxdot mulr_sumr.
under [X in _ <= _ * X]eq_bigr do rewrite frobenius_sqr /mxdot mulr_sumr.
rewrite exchange_big [X in _ <= _ * X]exchange_big /= mulr_sumr.
apply: ler_sum => i _.
under eq_bigr do rewrite mulr_sumr.
under [X in _ <= _ * X]eq_bigr do rewrite mulr_sumr.
rewrite exchange_big [X in _ <= _ * X]exchange_big /= mulr_sumr.
apply: ler_sum => j _.
apply: le_trans (var (fun x => Z x i j)).
apply: ler_sum => m0 _; rewrite -expr2.
by rewrite !mxE !summxE; under eq_bigr do rewrite mxE;
  under [X in _ - X]eq_bigr do rewrite mxE.
Qed.

End channel_tools.

Section smoothing_stack.
Variables (R : realType) (X M : finType) (a t R0 r : nat).
Variable pi : M -> 'rV['F_2]_a -> X -> R.
Hypothesis pi0 : forall m z x, 0 <= pi m z x.

Local Notation T := ('rV['F_2]_a * X)%type.
Local Notation R1 := (\sum_(i < #|{: T}|) R0)%N.
Local Notation N1 := (#|{: 'rV['F_2]_a}|%:R : R).
Implicit Types (G : X -> 'M['F_2]_(t, a) -> 'M[R]_(R0, r)).

Definition smoothing_stack_blk G (m0 : M) (k : T) (Y : 'M['F_2]_(1 + t, a)) :
    'M[R]_(R0, r) :=
  ((k.1 == usubmx Y)%:R * Num.sqrt (pi m0 k.1 k.2)) *: G k.2 (dsubmx Y).

Definition smoothing_stack G (m0 : M) (Y : 'M['F_2]_(1 + t, a)) :
    'M[R]_(R1, r) :=
  \mxcol_(i < #|{: T}|) smoothing_stack_blk G m0 (enum_val i) Y.

Lemma sum_enum_stack (V : nmodType) (F : T -> V) :
  \sum_(i < #|{: T}|) F (enum_val i) =
  \sum_(y : 'rV['F_2]_a) \sum_(x : X) F (y, x).
Proof.
rewrite pair_big /= (reindex enum_rank) /=.
  exact: (onW_bij _ (Bijective enum_rankK enum_valK)).
by apply: eq_bigr => -[y x] _; rewrite enum_rankK.
Qed.

Lemma smoothing_stack_gram G (m0 : M) Y :
  (smoothing_stack G m0 Y)^T *m smoothing_stack G m0 Y =
  \sum_x pi m0 (usubmx Y) x *: ((G x (dsubmx Y))^T *m G x (dsubmx Y)).
Proof.
rewrite /smoothing_stack tr_mxcol mul_mxrow_mxcol.
rewrite (sum_enum_stack (fun k =>
  (smoothing_stack_blk G m0 k Y)^T *m smoothing_stack_blk G m0 k Y)).
rewrite (bigD1 (usubmx Y)) //= [X in _ + X]big1 => [y /negbTE yY|].
  apply: big1 => x _.
  by rewrite /smoothing_stack_blk /= yY mul0r scale0r trmx0 mul0mx.
rewrite addr0; apply: eq_bigr => x _.
rewrite /smoothing_stack_blk /= eqxx mul1r linearZ /=.
by rewrite linearZ /= -scalemxAl scalerA -expr2 sqr_sqrtr.
Qed.

Lemma fcoef_smoothing_stack G (m0 : M) (z : 'rV['F_2]_a) (p : 'M['F_2]_(t, a)) :
  fcoef (smoothing_stack G m0) (col_mx z p) =
  \mxcol_(i < #|{: T}|) ((N1^-1 * bchar R z (enum_val i).1 *
     Num.sqrt (pi m0 (enum_val i).1 (enum_val i).2)) *:
     fcoef (G (enum_val i).2) p).
Proof.
rewrite /smoothing_stack fcoef_mxcol; apply: eq_mxcol => i.
set k := enum_val i; rewrite fcoef_col_mx.
have E y1 : fcoef (fun y2 => smoothing_stack_blk G m0 k (col_mx y1 y2)) p =
    ((k.1 == y1)%:R * Num.sqrt (pi m0 k.1 k.2)) *: fcoef (G k.2) p.
  rewrite -fcoefZ; apply: eq_fcoef => y2.
  by rewrite /smoothing_stack_blk col_mxKu col_mxKd.
by rewrite (eq_fcoef z E) fcoef_indicator.
Qed.

Lemma fcoef_smoothing_stack_gram G (m0 : M) z p z' p' :
  (fcoef (smoothing_stack G m0) (col_mx z p))^T *m
    fcoef (smoothing_stack G m0) (col_mx z' p') =
  \sum_(y : 'rV['F_2]_a) (N1^-1 ^+ 2 * (bchar R z y * bchar R z' y)) *:
     \sum_x pi m0 y x *: ((fcoef (G x) p)^T *m fcoef (G x) p').
Proof.
rewrite !fcoef_smoothing_stack tr_mxcol mul_mxrow_mxcol.
rewrite (sum_enum_stack (fun k => ((N1^-1 * bchar R z k.1 *
  Num.sqrt (pi m0 k.1 k.2)) *: fcoef (G k.2) p)^T *m ((N1^-1 * bchar R z' k.1 *
  Num.sqrt (pi m0 k.1 k.2)) *: fcoef (G k.2) p'))).
apply: eq_bigr => y _; rewrite scaler_sumr; apply: eq_bigr => x _ /=.
rewrite [X in X *m _]linearZ /= -scalemxAl -scalemxAr !scalerA; congr (_ *: _).
have hs : Num.sqrt (pi m0 y x) * Num.sqrt (pi m0 y x) = pi m0 y x.
  by rewrite -expr2 sqr_sqrtr.
move: hs; set s := Num.sqrt _; set N := _^-1.
by set c := bchar R z y; set c' := bchar R z' y; move=> <-; ring.
Qed.

End smoothing_stack.

Section smoothing_step.
Variables (R : realType) (X M : finType) (a t R0 r : nat).
Variables (mu : X -> R) (nu : M -> R) (pi : M -> 'rV['F_2]_a -> X -> R).
Variables (theta lambda : R).
Hypothesis mu1 : prob_vec mu.
Hypothesis nu1 : prob_vec nu.
Hypothesis pi1 : forall m z, prob_vec (pi m z).
Hypothesis marg : forall z x, \sum_m nu m * pi m z x = mu x.
Hypothesis var : forall z (g : X -> R), \sum_m nu m * (\sum_x pi m z x * g x -
  \sum_x mu x * g x) ^+ 2 <= theta * \sum_x mu x * g x ^+ 2.
Hypothesis lam0 : 0 < lambda.
Hypothesis cond : (2 ^ a)%:R * lambda ^+ 2 * 2 ^+ (2 ^ a).-1 * theta <= 1.

Local Notation T := ('rV['F_2]_a * X)%type.
Local Notation R1 := (\sum_(i < #|{: T}|) R0)%N.
Local Notation N1 := (#|{: 'rV['F_2]_a}|%:R : R).

Lemma card_rV_F2 : #|{: 'rV['F_2]_a}| = (2 ^ a)%N.
Proof. by rewrite card_mx card_ord mul1n. Qed.

Lemma card_rV_F2_gt0 : 0 < N1.
Proof. by rewrite card_rV_F2 ltr0n expn_gt0. Qed.

Lemma channel_ge0 m z x : 0 <= pi m z x.
Proof. exact: (pi1 m z).1 x. Qed.

Lemma channel_mean y (h : X -> R) :
  \sum_m0 nu m0 * \sum_x pi m0 y x * h x = \sum_x mu x * h x.
Proof.
under eq_bigr do rewrite mulr_sumr; rewrite exchange_big /=.
by apply: eq_bigr => x _; rewrite -(marg y x) mulr_suml; apply: eq_bigr => m0 _;
  rewrite mulrA.
Qed.

Lemma sum_rV_F2_const (c : R) : \sum_(y : 'rV['F_2]_a) c = N1 * c.
Proof. by rewrite sumr_const mulr_natl. Qed.

Section fixed_branch.
Variable G : X -> 'M['F_2]_(t, a) -> 'M[R]_(R0, r).
Variable q : 'M['F_2]_(t, a).

Definition stack_coef (m0 : M) (z : 'rV['F_2]_a) (p : 'M['F_2]_(t, a)) :
    'M[R]_(R1, r) :=
  fcoef (smoothing_stack pi G m0) (col_mx z p).

Definition split_gram (m0 : M) (z : 'rV['F_2]_a) : 'M[R]_R1 :=
  \sum_p lambda ^+ blk_dist q p *: (stack_coef m0 z p *m (stack_coef m0 z p)^T).

Lemma weighted_gram_stack (P : 'M[R]_R1) (m0 : M) (s : 'rV['F_2]_a) :
  P \is symmetricmx ->
  weighted_gram lambda (fun Y => P *m smoothing_stack pi G m0 Y) (col_mx s q) =
  \sum_z lambda ^+ (s != z) *: (P *m split_gram m0 z *m P).
Proof.
move=> /symmetricmxP Psym; rewrite /weighted_gram sum_col_mx.
apply: eq_bigr => z _; rewrite /split_gram mulmx_sumr mulmx_suml scaler_sumr.
apply: eq_bigr => p _; rewrite fcoef_mulmxl blk_dist_col_mx blk_dist_row exprD.
rewrite -scalerA; congr (_ *: _).
set c := lambda ^+ blk_dist q p.
set X0 := stack_coef m0 z p *m (stack_coef m0 z p)^T.
have -> : P *m (c *: X0) *m P = c *: (P *m X0 *m P).
  by rewrite -scalemxAr -scalemxAl.
by congr (_ *: _); rewrite /X0 /stack_coef trmx_mul Psym !mulmxA.
Qed.

(* The overlaps of the new Fourier coefficients, in mean over m0. *)
Lemma stack_overlap_le z z' p p' :
  \sum_m0 nu m0 *
    frobenius ((stack_coef m0 z p)^T *m stack_coef m0 z' p') ^+ 2 <=
    N1^-1 ^+ 2 * (if z == z' then 1 else theta) *
    \sum_x mu x * frobenius ((fcoef (G x) p)^T *m fcoef (G x) p') ^+ 2.
Proof.
set Zx := fun x => (fcoef (G x) p)^T *m fcoef (G x) p'.
set E := \sum_x mu x * frobenius (Zx x) ^+ 2.
have [mu0 _] := mu1; have [nu0 _] := nu1; have N10 := card_rV_F2_gt0.
have gram m0 : (stack_coef m0 z p)^T *m stack_coef m0 z' p' = \sum_y
    (N1^-1 ^+ 2 * (bchar R z y * bchar R z' y)) *: \sum_x pi m0 y x *: Zx x.
  exact: fcoef_smoothing_stack_gram channel_ge0 G m0 z p z' p'.
have E0 : 0 <= E by apply: sumr_ge0 => x _; rewrite mulr_ge0 ?sqr_ge0.
have iN0 : 0 <= N1^-1 by rewrite invr_ge0 ltW.
have [zz'|zz'] := eqVneq z z'.
  subst z'; rewrite mulr1.
  have E1 m0 : frobenius ((stack_coef m0 z p)^T *m stack_coef m0 z p') ^+ 2 <=
      N1^-1 ^+ 4 * (N1 * \sum_y \sum_x pi m0 y x * frobenius (Zx x) ^+ 2).
    rewrite gram; under eq_bigr do rewrite bchar_sqr mulr1.
    rewrite -scaler_sumr frobeniusZ ger0_norm ?exprn_ge0 //.
    rewrite exprMn -exprM; apply: ler_wpM2l; first by rewrite exprn_ge0.
    apply: le_trans (frobenius_sum_sqr_le _) _; rewrite ler_wpM2l ?ler0n //.
    apply: ler_sum => y _; have := frobenius_wsum_le Zx (channel_ge0 m0 y).
    by rewrite (pi1 m0 y).2 mul1r.
  apply: le_trans (_ : \sum_m0 nu m0 * (N1^-1 ^+ 4 * (N1 *
      \sum_y \sum_x pi m0 y x * frobenius (Zx x) ^+ 2)) <= _).
    by apply: ler_sum => m0 _; apply: ler_wpM2l.
  have ES : \sum_m0 nu m0 * \sum_y \sum_x pi m0 y x * frobenius (Zx x) ^+ 2 =
      N1 * E.
    under eq_bigr do rewrite mulr_sumr; rewrite exchange_big /=.
    by under eq_bigr do rewrite channel_mean; rewrite sum_rV_F2_const.
  rewrite (eq_bigr (fun m0 => N1^-1 ^+ 4 * N1 * (nu m0 *
      \sum_y \sum_x pi m0 y x * frobenius (Zx x) ^+ 2))) => [m0 _|].
    by ring.
  rewrite -mulr_sumr ES.
  have -> : N1^-1 ^+ 4 * N1 * (N1 * E) = N1^-1 ^+ 2 * E.
    by field by exact: lt0r_neq0 N10.
  by [].
set muZ := \sum_x mu x *: Zx x.
have orth : \sum_y bchar R z y * bchar R z' y = 0.
  by rewrite bchar_orthogonal (negbTE zz').
have gram2 m0 : (stack_coef m0 z p)^T *m stack_coef m0 z' p' = \sum_y
    (N1^-1 ^+ 2 * (bchar R z y * bchar R z' y)) *:
      (\sum_x pi m0 y x *: Zx x - muZ).
  rewrite gram; under [RHS]eq_bigr do rewrite scalerBr.
  by rewrite sumrB -scaler_suml -mulr_sumr orth mulr0 scale0r subr0.
have E2 m0 : frobenius ((stack_coef m0 z p)^T *m stack_coef m0 z' p') ^+ 2 <=
    N1^-1 ^+ 4 * (N1 * \sum_y frobenius (\sum_x pi m0 y x *: Zx x - muZ) ^+ 2).
  rewrite gram2; apply: le_trans (frobenius_sum_sqr_le _) _.
  rewrite mulrCA ler_wpM2l ?ler0n // mulr_sumr; apply: ler_sum => y _.
  rewrite frobeniusZ exprMn real_normK ?num_real // exprMn -exprM.
  by rewrite exprMn !expr2 !bchar_sqr !mulr1.
apply: le_trans (_ : \sum_m0 nu m0 * (N1^-1 ^+ 4 * (N1 *
    \sum_y frobenius (\sum_x pi m0 y x *: Zx x - muZ) ^+ 2)) <= _).
  by apply: ler_sum => m0 _; apply: ler_wpM2l.
rewrite (eq_bigr (fun m0 => N1^-1 ^+ 4 * N1 * (nu m0 *
    \sum_y frobenius (\sum_x pi m0 y x *: Zx x - muZ) ^+ 2))) => [m0 _|].
  by ring.
rewrite -mulr_sumr; under eq_bigr do rewrite mulr_sumr; rewrite exchange_big /=.
apply: le_trans (_ : N1^-1 ^+ 4 * N1 * \sum_(y : 'rV['F_2]_a) (theta * E) <= _).
  apply: ler_wpM2l; first by rewrite mulr_ge0 ?exprn_ge0 // ltW.
  by apply: ler_sum => y _; exact: (contraction_mx Zx (var y)).
rewrite sum_rV_F2_const.
have -> : N1^-1 ^+ 4 * N1 * (N1 * (theta * E)) = N1^-1 ^+ 2 * theta * E.
  by field by exact: lt0r_neq0 N10.
by [].
Qed.

Lemma split_gram_overlap_le z z' :
  \sum_m0 nu m0 * \tr (split_gram m0 z *m split_gram m0 z') <=
    N1^-1 ^+ 2 * (if z == z' then 1 else theta) *
    \sum_x mu x * frobenius (weighted_gram lambda (G x) q) ^+ 2.
Proof.
have [nu0 _] := nu1; have [mu0 _] := mu1.
have w0 p : 0 <= lambda ^+ blk_dist q p by rewrite exprn_ge0 // ltW.
have LHS : \sum_m0 nu m0 * \tr (split_gram m0 z *m split_gram m0 z') =
    \sum_p \sum_p' lambda ^+ blk_dist q p * lambda ^+ blk_dist q p' *
      \sum_m0 nu m0 *
        frobenius ((stack_coef m0 z p)^T *m stack_coef m0 z' p') ^+ 2.
  rewrite /split_gram; under eq_bigr do rewrite mxtrace_gram_mul mulr_sumr.
  rewrite exchange_big /=; apply: eq_bigr => p _.
  under eq_bigr do rewrite mulr_sumr.
  rewrite exchange_big /=; apply: eq_bigr => p' _.
  by rewrite mulr_sumr; apply: eq_bigr => m0 _; ring.
have RHS : \sum_x mu x * frobenius (weighted_gram lambda (G x) q) ^+ 2 =
    \sum_p \sum_p' lambda ^+ blk_dist q p * lambda ^+ blk_dist q p' *
      \sum_x mu x * frobenius ((fcoef (G x) p)^T *m fcoef (G x) p') ^+ 2.
  rewrite /weighted_gram; under eq_bigr do rewrite frobenius_gram mulr_sumr.
  rewrite exchange_big /=; apply: eq_bigr => p _.
  under eq_bigr do rewrite mulr_sumr.
  rewrite exchange_big /=; apply: eq_bigr => p' _.
  by rewrite mulr_sumr; apply: eq_bigr => x _; ring.
rewrite LHS RHS mulr_sumr; apply: ler_sum => p _.
rewrite mulr_sumr; apply: ler_sum => p' _.
rewrite mulrCA; apply: ler_wpM2l; first by rewrite mulr_ge0.
exact: stack_overlap_le.
Qed.

(* One step of product smoothing, for one branch q of the old family G. *)
Lemma smoothing_step_one : exists P : M -> 'rV['F_2]_a -> 'M[R]_R1,
  (forall m0 Y, \sum_s (P m0 s *m smoothing_stack pi G m0 Y)^T *m
     (P m0 s *m smoothing_stack pi G m0 Y)
     = \sum_x pi m0 (usubmx Y) x *: ((G x (dsubmx Y))^T *m G x (dsubmx Y))) /\
  \sum_m0 nu m0 * \sum_s frobenius (weighted_gram lambda
      (fun Y => P m0 s *m smoothing_stack pi G m0 Y) (col_mx s q)) ^+ 2
    <= 2 * \sum_x mu x * frobenius (weighted_gram lambda (G x) q) ^+ 2.
Proof.
have Z0 : (0 < #|{: 'rV['F_2]_a}|)%N by rewrite card_rV_F2 expn_gt0.
have Apsd m0 z : psdmx (split_gram m0 z).
  by apply: psdmx_gram => p; rewrite exprn_ge0 // ltW.
have ex m0 := psd_splitting_fin Z0 (Apsd m0).
pose P m0 := sval (cid (ex m0)).
have PP m0 := svalP (cid (ex m0)).
exists P; split.
  move=> m0 Y; have [Po Psum _] := PP m0; set H := smoothing_stack pi G m0 Y.
  transitivity (H^T *m (\sum_s P m0 s) *m H).
    rewrite mulmx_sumr mulmx_suml; apply: eq_bigr => s _.
    have [/symmetricmxP Ps PPs] := Po s.
    by rewrite trmx_mul Ps /P /= mulmxA -(mulmxA H^T) PPs.
  by rewrite /P /= Psum mulmx1 (smoothing_stack_gram channel_ge0).
set E := \sum_x mu x * frobenius (weighted_gram lambda (G x) q) ^+ 2.
have [nu0 _] := nu1; have [mu0 _] := mu1; have N10 := card_rV_F2_gt0.
have E0 : 0 <= E by apply: sumr_ge0 => x _; rewrite mulr_ge0 ?sqr_ge0.
have theta0 : 0 <= theta := contraction_ge0 mu1 nu1 (var 0).
set C : R := 2 ^+ #|{: 'rV['F_2]_a}|.-1.
have C0 : 0 <= C by rewrite exprn_ge0.
have Hm0 m0 : \sum_s frobenius (weighted_gram lambda
    (fun Y => P m0 s *m smoothing_stack pi G m0 Y) (col_mx s q)) ^+ 2 <=
    N1 * (\sum_z frobenius (split_gram m0 z) ^+ 2 +
      lambda ^+ 2 * (C * \sum_z \sum_(z' | z' != z)
        \tr (split_gram m0 z *m split_gram m0 z'))).
  have [Po Psum Pb] := PP m0.
  under eq_bigr => s _ do rewrite (weighted_gram_stack m0 s (Po s).1).
  exact: split_potential_le (ltW lam0) Po Psum Pb.
have T1 : \sum_m0 nu m0 * \sum_z frobenius (split_gram m0 z) ^+ 2 <=
    N1 * (N1^-1 ^+ 2 * E).
  under eq_bigr => m0 _ do under eq_bigr => z _ do
    rewrite (frobenius_sqr_sym (Apsd m0 z).1).
  under eq_bigr do rewrite mulr_sumr; rewrite exchange_big /= -sum_rV_F2_const.
  apply: ler_sum => z _; have := split_gram_overlap_le z z; rewrite eqxx mulr1.
  by apply: le_trans; apply: ler_sum => m0 _; rewrite mulrC.
have T2 : \sum_m0 nu m0 * \sum_z \sum_(z' | z' != z)
    \tr (split_gram m0 z *m split_gram m0 z')
    <= N1 * (N1 * (N1^-1 ^+ 2 * theta * E)).
  under eq_bigr do rewrite mulr_sumr; rewrite exchange_big /= -sum_rV_F2_const.
  apply: ler_sum => z _.
  under eq_bigr do rewrite mulr_sumr; rewrite exchange_big /= -sum_rV_F2_const.
  apply: le_trans (_ : \sum_(z' | z' != z) N1^-1 ^+ 2 * theta * E <= _).
    apply: ler_sum => z' zz'; have := split_gram_overlap_le z z'.
    by rewrite eq_sym (negbTE zz') => H; apply: le_trans H; apply: ler_sum.
  rewrite [X in _ <= X](bigD1 z) //= lerDr.
  by rewrite !mulr_ge0 ?exprn_ge0 // invr_ge0 ltW.
apply: le_trans (_ : \sum_m0 nu m0 * (N1 *
    (\sum_z frobenius (split_gram m0 z) ^+ 2 +
    lambda ^+ 2 * (C * \sum_z \sum_(z' | z' != z)
      \tr (split_gram m0 z *m split_gram m0 z'))))
    <= _).
  by apply: ler_sum => m0 _; apply: ler_wpM2l => //; exact: Hm0.
rewrite (eq_bigr (fun m0 =>
    N1 * (nu m0 * \sum_z frobenius (split_gram m0 z) ^+ 2) +
    N1 * (lambda ^+ 2 * C) * (nu m0 *
      \sum_z \sum_(z' | z' != z)
        \tr (split_gram m0 z *m split_gram m0 z')))) => [m0 _|].
  by ring.
rewrite big_split /= -!mulr_sumr.
apply: le_trans (_ : N1 * (N1 * (N1^-1 ^+ 2 * E)) + N1 * (lambda ^+ 2 * C) *
    (N1 * (N1 * (N1^-1 ^+ 2 * theta * E))) <= _).
  apply: lerD; first by apply: (ler_wpM2l (ltW N10)); exact: T1.
  apply: (ler_wpM2l _); last exact: T2.
  by rewrite mulr_ge0 ?mulr_ge0 ?exprn_ge0 //; exact: ltW.
have -> : N1 * (N1 * (N1^-1 ^+ 2 * E)) = E by field by exact: lt0r_neq0 N10.
have -> : N1 * (lambda ^+ 2 * C) * (N1 * (N1 * (N1^-1 ^+ 2 * theta * E))) =
    (N1 * lambda ^+ 2 * C * theta) * E by field by exact: lt0r_neq0 N10.
have key : N1 * lambda ^+ 2 * C * theta <= 1 by rewrite /C card_rV_F2.
have -> : 2 * E = E + E by ring.
by rewrite lerD // -[X in _ <= X]mul1r ler_wpM2r.
Qed.

End fixed_branch.

End smoothing_step.

Section flat_cube.
Variable a : nat.
Local Notation flat := 'M['F_2]_(0, a).

Lemma card_flat : #|{: flat}| = 1%N.
Proof. by rewrite card_mx mul0n expn0. Qed.

Lemma sum_flat (V : nmodType) (F : flat -> V) (q : flat) :
  \sum_(y : flat) F y = F q.
Proof.
by rewrite (big_pred1 q) // => y; rewrite inE [y]flatmx0 [q]flatmx0 eqxx.
Qed.

Lemma fcoef_flat (R : numFieldType) (V : lmodType R) (f : flat -> V)
    (p : flat) :
  fcoef f p = f p.
Proof.
rewrite /fcoef (sum_flat _ p) card_flat invr1 scale1r /bchar /bdot big_ord0.
by rewrite expr0 scale1r.
Qed.

Lemma weighted_gram_flat (R : realType) (lambda : R) Rw r
    (H : flat -> 'M[R]_(Rw, r)) (q : flat) :
  weighted_gram lambda H q = H q *m (H q)^T.
Proof.
rewrite /weighted_gram (sum_flat _ q) fcoef_flat.
by rewrite (blk_dist_eq0 q q).2 // expr0 scale1r.
Qed.

End flat_cube.

Section induction_tools.
Variables (R : realType) (X M : finType) (a : nat).

Lemma frobenius_gram_sym m n (H : 'M[R]_(m, n)) :
  frobenius (H *m H^T) = frobenius (H^T *m H).
Proof.
apply/eqP; rewrite -(eqrXn2 (n := 2)) ?frobenius_ge0 //.
rewrite !frobenius_sqr !mxdot_trace !trmx_mul !trmxK.
by rewrite -!mulmxA mxtrace_mulC !mulmxA.
Qed.

Lemma prod_avg_cons (V : lmodType R) t
    (pi : 'I_t.+1 -> M -> 'rV['F_2]_a -> X -> R)
    (F : t.+1.-tuple X -> V) (m : t.+1.-tuple M) (Y : 'M['F_2]_(1 + t, a)) :
  prod_avg pi F m Y =
  \sum_x0 pi ord0 (thead m) (usubmx Y) x0 *:
    prod_avg (fun i => pi (lift ord0 i)) (fun x => F [tuple of x0 :: x])
      [tuple of behead m] (dsubmx Y).
Proof.
rewrite /prod_avg sum_tuple_cons; apply: eq_bigr => x0 _.
rewrite scaler_sumr; apply: eq_bigr => x _; rewrite scalerA; congr (_ *: _).
rewrite big_ord_recl tnth0; congr (_ * _).
  congr (pi _ _ _ _).
  have -> : (ord0 : 'I_t.+1) = lshift t (ord0 : 'I_1) by apply: val_inj.
  by apply/rowP => j; rewrite !mxE.
apply: eq_bigr => i _; rewrite tnthS; congr (pi _ _ _ _).
  by rewrite (tnth_nth (thead m)) [RHS](tnth_nth (thead m)) /= nth_behead.
by apply/rowP => j; rewrite !mxE; congr (Y _ j); apply: val_inj.
Qed.

Lemma smoothing_hyps_tail t (mu : 'I_t.+1 -> X -> R) (nu : 'I_t.+1 -> M -> R)
    (pi : 'I_t.+1 -> M -> 'rV['F_2]_a -> X -> R) theta :
  smoothing_hyps mu nu pi theta ->
  smoothing_hyps (fun i => mu (lift ord0 i)) (fun i => nu (lift ord0 i))
    (fun i => pi (lift ord0 i)) theta.
Proof.
by case=> h1 h2 h3 h4 h5; split=> *;
  [apply: h1|apply: h2|apply: h3|apply: h4|apply: h5].
Qed.

End induction_tools.

Section smoothing_param.
Variables (R : realType) (X M : finType) (a r : nat).

Lemma smoothing_param t (P : finType) (rho : P -> R) (mu : 'I_t -> X -> R)
    (nu : 'I_t -> M -> R) (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R)
    (theta lambda : R) (F : P -> t.-tuple X -> 'M[R]_r) :
  (forall p, 0 <= rho p) -> smoothing_hyps mu nu pi theta ->
  (forall p x, psdmx (F p x)) -> 0 < lambda ->
  (2 ^ a)%:R * lambda ^+ 2 * 2 ^+ (2 ^ a).-1 * theta <= 1 ->
  exists (Rw : nat)
    (H : P -> t.-tuple M -> 'M['F_2]_(t, a) -> 'M['F_2]_(t, a) ->
      'M[R]_(Rw, r)),
    (forall p m y, prod_avg pi (F p) m y = \sum_q (H p m q y)^T *m H p m q y) /\
    \sum_p rho p * \sum_(m : t.-tuple M) (\prod_(i < t) nu i (tnth m i)) *
       \sum_q frobenius (weighted_gram lambda (H p m q) q) ^+ 2
    <= 2 ^+ t * \sum_p rho p * \sum_(x : t.-tuple X)
         (\prod_(i < t) mu i (tnth x i)) * frobenius (F p x) ^+ 2.
Proof.
elim: t P rho mu nu pi F => [|t IH] P rho mu nu pi F rho0 hyps Fpsd lam0 cond.
  have hF p := psdmx_factor (Fpsd p [tuple]).
  pose Hf p := sval (cid (hF p)).
  have HfE p : (Hf p)^T *m Hf p = F p [tuple] := svalP (cid (hF p)).
  exists r, (fun p _ _ _ => Hf p); split.
    move=> p m y; rewrite /prod_avg sum_tuple0 big_ord0 scale1r.
    by rewrite (sum_flat _ (0 : 'M['F_2]_(0, a))) HfE.
  rewrite expr0 mul1r; apply: ler_sum => p _.
  rewrite !sum_tuple0 !big_ord0 !mul1r (sum_flat _ (0 : 'M['F_2]_(0, a))).
  by rewrite weighted_gram_flat frobenius_gram_sym HfE.
have [h1 h2 h3 h4 h5] := hyps.
pose mu' i := mu (lift ord0 i); pose nu' i := nu (lift ord0 i).
pose pi' i := pi (lift ord0 i).
pose rho' (xp : X * P) := mu ord0 xp.1 * rho xp.2.
pose F' (xp : X * P) (x : t.-tuple X) := F xp.2 [tuple of xp.1 :: x].
have rho'0 xp : 0 <= rho' xp by rewrite mulr_ge0 // (h1 ord0).1.
have [Rw0 [H0 [H0sq H0pot]]] := IH (X * P)%type rho' mu' nu' pi' F' rho'0
  (smoothing_hyps_tail hyps) (fun xp x => Fpsd _ _) lam0 cond.
pose G (k : P * t.-tuple M * 'M['F_2]_(t, a)) (x : X) (y : 'M['F_2]_(t, a)) :=
  H0 (x, k.1.1) k.1.2 k.2 y.
have hk k := smoothing_step_one (h1 ord0) (h2 ord0) (h3 ord0) (h4 ord0)
  (h5 ord0) lam0 cond (G k) k.2.
pose Pr k := sval (cid (hk k)).
have PrP k := svalP (cid (hk k)).
pose H p (m : t.+1.-tuple M) (Q Y : 'M['F_2]_(1 + t, a)) :=
  Pr (p, [tuple of behead m], dsubmx Q) (thead m) (usubmx Q) *m
  smoothing_stack (pi ord0) (G (p, [tuple of behead m], dsubmx Q)) (thead m) Y.
exists (\sum_(i < #|{: 'rV['F_2]_a * X}|) Rw0)%N, H; split.
  move=> p m Y; rewrite prod_avg_cons.
  under eq_bigr => x0 _ do rewrite (H0sq (x0, p)) scaler_sumr.
  rewrite exchange_big /= (@sum_col_mx 1 t a).
  rewrite [RHS]exchange_big /=; apply: eq_bigr => q _.
  have [sq _] := PrP (p, [tuple of behead m], q).
  symmetry; transitivity (\sum_s (Pr (p, [tuple of behead m], q) (thead m) s *m
    smoothing_stack (pi ord0) (G (p, [tuple of behead m], q)) (thead m) Y)^T *m
    (Pr (p, [tuple of behead m], q) (thead m) s *m
    smoothing_stack (pi ord0) (G (p, [tuple of behead m], q)) (thead m) Y)).
    by apply: eq_bigr => s _; rewrite /H col_mxKu col_mxKd.
  exact: sq.
pose W p m' q m0 s := frobenius (weighted_gram lambda (fun Y =>
  Pr (p, m', q) m0 s *m smoothing_stack (pi ord0) (G (p, m', q)) m0 Y)
  (col_mx s q)) ^+ 2.
have Hc p m0 (m' : t.-tuple M) s q :
    weighted_gram lambda (H p [tuple of m0 :: m'] (col_mx s q)) (col_mx s q) =
    weighted_gram lambda (fun Y => Pr (p, m', q) m0 s *m
      smoothing_stack (pi ord0) (G (p, m', q)) m0 Y) (col_mx s q).
  rewrite /H col_mxKu col_mxKd.
  rewrite (_ : [tuple of behead [tuple of m0 :: m']] = m') //.
  exact: val_inj.
have A p : \sum_(m : t.+1.-tuple M) (\prod_(i < t.+1) nu i (tnth m i)) *
    \sum_(q : 'M['F_2]_(t.+1, a))
      frobenius (weighted_gram lambda (H p m q) q) ^+ 2
  = \sum_(m' : t.-tuple M) (\prod_(i < t) nu' i (tnth m' i)) *
      \sum_q \sum_m0 nu ord0 m0 * \sum_s W p m' q m0 s.
  rewrite sum_tuple_cons exchange_big /=; apply: eq_bigr => m' _.
  have E2 m0 : \sum_(s : 'rV['F_2]_a) \sum_(q : 'M['F_2]_(t, a)) frobenius
      (weighted_gram lambda (H p [tuple of m0 :: m'] (col_mx s q)) (col_mx s q))
        ^+ 2 = \sum_s \sum_q W p m' q m0 s.
    by apply: eq_bigr => s _; apply: eq_bigr => q _; rewrite (Hc p m0 m' s q).
  under eq_bigr => m0 _ do rewrite prod_tuple_cons (@sum_col_mx 1 t a) E2.
  rewrite /nu' /=.
  move: (W p m') (\prod_(i < t) nu (lift ord0 i) (tnth m' i)) => w c.
  under eq_bigr do rewrite exchange_big /= mulr_sumr.
  rewrite exchange_big /= mulr_sumr; apply: eq_bigr => q _.
  by rewrite mulr_sumr; apply: eq_bigr => m0 _; ring.
have B p m' q : \sum_m0 nu ord0 m0 * \sum_s W p m' q m0 s <=
    2 * \sum_x mu ord0 x *
      frobenius (weighted_gram lambda (H0 (x, p) m' q) q) ^+ 2.
  by have [_ pot] := PrP (p, m', q); exact: pot.
have Ppos m' : 0 <= \prod_(i < t) nu' i (tnth m' i).
  by apply: prodr_ge0 => i _; exact: (h2 _).1.
under eq_bigr do rewrite A.
apply: le_trans (_ : \sum_p rho p * \sum_(m' : t.-tuple M)
    (\prod_(i < t) nu' i (tnth m' i)) * \sum_(q : 'M['F_2]_(t, a)) (2 *
    \sum_x mu ord0 x * frobenius (weighted_gram lambda (H0 (x, p) m' q) q) ^+ 2)
    <= _).
  apply: ler_sum => p _; apply: (ler_wpM2l (rho0 p)); apply: ler_sum => m' _.
  by apply: (ler_wpM2l (Ppos m')); apply: ler_sum => q _; exact: B.
have SP (V : nmodType) (f : X * P -> V) : \sum_xp f xp = \sum_x \sum_p f (x, p).
  by rewrite pair_big; apply: eq_bigr => -[x p].
have E1 : \sum_p rho p * \sum_(m' : t.-tuple M)
    (\prod_(i < t) nu' i (tnth m' i)) * \sum_(q : 'M['F_2]_(t, a)) (2 *
    \sum_x mu ord0 x * frobenius (weighted_gram lambda (H0 (x, p) m' q) q) ^+ 2)
  = 2 * \sum_(xp : X * P) rho' xp * \sum_(m' : t.-tuple M)
    (\prod_(i < t) nu' i (tnth m' i)) *
    \sum_q frobenius (weighted_gram lambda (H0 xp m' q) q) ^+ 2.
  rewrite (SP _ (fun xp => rho' xp * \sum_(m' : t.-tuple M)
    (\prod_(i < t) nu' i (tnth m' i)) *
    \sum_q frobenius (weighted_gram lambda (H0 xp m' q) q) ^+ 2)) /=.
  rewrite exchange_big /= mulr_sumr; apply: eq_bigr => p _.
  rewrite mulr_sumr; under eq_bigr do rewrite mulr_sumr.
  rewrite exchange_big /= mulr_sumr; apply: eq_bigr => m' _.
  rewrite mulr_sumr mulr_sumr.
  transitivity (\sum_(q : 'M['F_2]_(t, a)) \sum_x rho p *
      \prod_(i0 < t) nu' i0 (tnth m' i0) * 2 *
      (mu ord0 x * frobenius (weighted_gram lambda (H0 (x, p) m' q) q) ^+ 2)).
    by apply: eq_bigr => q _; rewrite !mulrA mulr_sumr.
  rewrite mulr_sumr.
  transitivity (\sum_x \sum_(q : 'M['F_2]_(t, a)) 2 * rho' (x, p) *
      \prod_(i0 < t) nu' i0 (tnth m' i0) *
      frobenius (weighted_gram lambda (H0 (x, p) m' q) q) ^+ 2).
    rewrite exchange_big /=; apply: eq_bigr => x _; apply: eq_bigr => q _.
    by rewrite /rho' /=; ring.
  by apply: eq_bigr => x _; rewrite !mulrA mulr_sumr.
have E3 : \sum_(xp : X * P) rho' xp * \sum_(x : t.-tuple X)
    (\prod_(i < t) mu' i (tnth x i)) * frobenius (F' xp x) ^+ 2 =
  \sum_p rho p * \sum_(x : t.+1.-tuple X)
    (\prod_(i < t.+1) mu i (tnth x i)) * frobenius (F p x) ^+ 2.
  rewrite (SP _ (fun xp => rho' xp * \sum_(x : t.-tuple X)
    (\prod_(i < t) mu' i (tnth x i)) * frobenius (F' xp x) ^+ 2)) /=.
  rewrite exchange_big /=; apply: eq_bigr => p _.
  rewrite sum_tuple_cons mulr_sumr; apply: eq_bigr => x0 _.
  rewrite !mulr_sumr; apply: eq_bigr => x _.
  by rewrite prod_tuple_cons /rho' /F' /mu' /=; ring.
rewrite E1 exprS -mulrA; apply: (ler_wpM2l (ler0n _ 2)).
by rewrite -E3.
Qed.

End smoothing_param.

Section product_smoothing_theorem.
Variables (R : realType) (X M : finType) (t a r : nat).

Lemma sum_unit (V : nmodType) (f : unit -> V) : \sum_(u : unit) f u = f tt.
Proof. by rewrite (big_pred1 tt) // => -[]; rewrite inE. Qed.

Theorem product_smoothing (mu : 'I_t -> X -> R) (nu : 'I_t -> M -> R)
    (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R) (theta B lambda : R)
    (F : t.-tuple X -> 'M[R]_r) :
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
Proof.
move=> hyps Fpsd FB lam0 cond; have [h1 h2 _ _ _] := hyps.
have [Rw [H0 [Hsq Hpot]]] := @smoothing_param R X M a r t unit (fun _ => 1)
  mu nu pi theta lambda (fun _ => F) (fun _ => ler01) hyps (fun _ => Fpsd)
  lam0 cond.
set H := H0 tt.
have w0 m : 0 <= \prod_(i < t) nu i (tnth m i) := prod_prob_ge0 m h2.
have w1 : \sum_(m : t.-tuple M) \prod_(i < t) nu i (tnth m i) = 1.
  exact: sum_prod_prob.
have v1 : \sum_(x : t.-tuple X) \prod_(i < t) mu i (tnth x i) = 1.
  exact: sum_prod_prob.
have FB2 x : frobenius (F x) ^+ 2 <= B ^+ 2.
  have f0 := frobenius_ge0 (F x).
  have fB : frobenius (F x) <= B.
    exact: le_trans (psdmx_frobenius_le_trace (Fpsd x)) (FB x).
  by rewrite ler_sqr ?nnegrE // (le_trans f0 fB).
have pot : \sum_(m : t.-tuple M) (\prod_(i < t) nu i (tnth m i)) *
    \sum_q frobenius (weighted_gram lambda (H m q) q) ^+ 2 <= 2 ^+ t * B ^+ 2.
  move: Hpot; rewrite !sum_unit !mul1r => /le_trans; apply.
  apply: ler_wpM2l; first by rewrite exprn_ge0.
  apply: le_trans (_ : \sum_(x : t.-tuple X) (\prod_(i < t) mu i (tnth x i)) *
    B ^+ 2 <= _).
    apply: ler_sum => x _; apply: ler_wpM2l; first exact: prod_prob_ge0.
    exact: FB2.
  by rewrite -mulr_suml v1 mul1r.
exists Rw, H; split => //.
  by move=> m y; exact: Hsq tt m y.
have [m wm fm] := exists_weight_le w0 w1 pot.
exists m => //.
have S0 : \sum_x (\prod_(i < t) mu i (tnth x i)) * (fun _ => 0 : R) x <= 0.
  by rewrite big1 // => x _; rewrite mulr0.
have [x0 _ _] := exists_weight_le (fun x => prod_prob_ge0 x h1) v1 S0.
have B0 : 0 <= B.
  apply: le_trans (frobenius_ge0 _) (le_trans _ (FB x0)).
  exact: psdmx_frobenius_le_trace (Fpsd x0).
set N := #|{: 'M['F_2]_(t, a)}|.
have NE : (N%:R : R) = (2 ^ a)%:R ^+ t.
  rewrite /N card_mx card_ord -natrX; congr (_%:R).
  by rewrite -expnM mulnC.
set C := fun q => frobenius (weighted_gram lambda (H m q) q).
have C0 q : 0 <= C q by exact: frobenius_ge0.
have Tq q : \sum_p lambda ^+ blk_dist q p * frobenius (fcoef (H m q) p) ^+ 2
    <= Num.sqrt (r%:R * N%:R) * C q.
  rewrite -(mxtrace_gram (fun p => lambda ^+ blk_dist q p)
    (fun p => fcoef (H m q) p)).
  by apply: mxtrace_gram_le => p; rewrite exprn_ge0 // ltW.
apply: le_trans (ler_sum _ (fun q _ => Tq q)) _.
rewrite -mulr_sumr.
have CS : \sum_q C q <= Num.sqrt N%:R * Num.sqrt (\sum_q C q ^+ 2).
  have cs : (\sum_q C q) ^+ 2 <= N%:R * \sum_q C q ^+ 2.
    have := @sum_wsqr_le R _ (fun _ => 1) C (fun _ => ler01).
    rewrite sumr_const; under eq_bigr do rewrite mul1r.
    by under [X in _ <= _ * X -> _]eq_bigr do rewrite mul1r.
  have s0 : 0 <= \sum_q C q ^+ 2 by apply: sumr_ge0 => q _; rewrite sqr_ge0.
  rewrite -sqrtrM ?ler0n // -[X in X <= _]ger0_norm ?sumr_ge0 //.
  by rewrite -sqrtr_sqr ler_sqrt // mulr_ge0 ?ler0n.
have Cb : Num.sqrt (\sum_q C q ^+ 2) <= Num.sqrt (2 ^+ t) * B.
  rewrite -[B in _ * B]ger0_norm // -sqrtr_sqr -sqrtrM ?exprn_ge0 //.
  by rewrite ler_sqrt ?mulr_ge0 ?exprn_ge0 ?sqr_ge0.
apply: le_trans (_ : Num.sqrt (r%:R * N%:R) * (Num.sqrt N%:R *
    (Num.sqrt (2 ^+ t) * B)) <= _).
  apply: ler_wpM2l; first exact: sqrtr_ge0.
  by apply: le_trans CS _; apply: ler_wpM2l; [exact: sqrtr_ge0 | exact: Cb].
rewrite sqrtrM ?ler0n // -NE.
have hN : Num.sqrt (N%:R : R) * Num.sqrt N%:R = N%:R.
  by rewrite -expr2 sqr_sqrtr ?ler0n.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
move: hN; set sN := Num.sqrt N%:R; set sr := Num.sqrt r%:R.
by set s2 := Num.sqrt (2 ^+ t) => <-; ring.
Qed.


(* The two conclusions of product_smoothing separately: the averaged potential
   bound, and the coefficient bound at one tuple of positive weight. *)
Corollary product_smoothing_potential (mu : 'I_t -> X -> R)
    (nu : 'I_t -> M -> R)
    (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R) (theta B lambda : R)
    (F : t.-tuple X -> 'M[R]_r) :
  smoothing_hyps mu nu pi theta ->
  (forall x, psdmx (F x)) -> (forall x, \tr (F x) <= B) ->
  0 < lambda -> (2 ^ a)%:R * lambda ^+ 2 * 2 ^+ (2 ^ a).-1 * theta <= 1 ->
  exists (Rw : nat)
         (H : t.-tuple M -> 'M['F_2]_(t, a) -> 'M['F_2]_(t, a) ->
              'M[R]_(Rw, r)),
    (forall m y, prod_avg pi F m y = \sum_q (H m q y)^T *m H m q y) /\
    \sum_(m : t.-tuple M) (\prod_(i < t) nu i (tnth m i)) *
       \sum_q frobenius (weighted_gram lambda (H m q) q) ^+ 2
      <= 2 ^+ t * B ^+ 2.
Proof.
move=> hyps Fpsd FB lam0 cond.
by have [Rw [H [Hsq Hpot _]]] := product_smoothing hyps Fpsd FB lam0 cond;
  exists Rw, H.
Qed.

Corollary product_smoothing_coef (mu : 'I_t -> X -> R) (nu : 'I_t -> M -> R)
    (pi : 'I_t -> M -> 'rV['F_2]_a -> X -> R) (theta B lambda : R)
    (F : t.-tuple X -> 'M[R]_r) :
  smoothing_hyps mu nu pi theta ->
  (forall x, psdmx (F x)) -> (forall x, \tr (F x) <= B) ->
  0 < lambda -> (2 ^ a)%:R * lambda ^+ 2 * 2 ^+ (2 ^ a).-1 * theta <= 1 ->
  exists (m : t.-tuple M) (Rw : nat)
         (H : 'M['F_2]_(t, a) -> 'M['F_2]_(t, a) -> 'M[R]_(Rw, r)),
    [/\ 0 < \prod_(i < t) nu i (tnth m i),
        forall y, prod_avg pi F m y = \sum_q (H q y)^T *m H q y &
        \sum_q \sum_p lambda ^+ blk_dist q p * frobenius (fcoef (H q) p) ^+ 2
          <= (2 ^ a)%:R ^+ t * Num.sqrt r%:R * B * Num.sqrt (2 ^+ t)].
Proof.
move=> hyps Fpsd FB lam0 cond.
have [Rw [H [Hsq _ [m wm Hc]]]] := product_smoothing hyps Fpsd FB lam0 cond.
by exists m, Rw, (H m); split.
Qed.

End product_smoothing_theorem.

(* An example of the hypotheses: constant channels pi i m z = mu i, which
   average to mu i under any law nu i and have no variance term. *)
Example smoothing_hyps_const (R : numDomainType) (X M : finType) (t a : nat)
    (mu : 'I_t -> X -> R) (nu : 'I_t -> M -> R) :
  (forall i, prob_vec (mu i)) -> (forall i, prob_vec (nu i)) ->
  smoothing_hyps mu nu (fun i (_ : M) (_ : 'rV['F_2]_a) => mu i) 0.
Proof.
move=> mu1 nu1; split=> [i|i|i m y|i y x|i y g]; [exact: mu1|exact: nu1|
  exact: mu1|by rewrite -mulr_suml (nu1 i).2 mul1r|].
by under eq_bigr do rewrite subrr expr2 !mulr0; rewrite big1 // mul0r.
Qed.
