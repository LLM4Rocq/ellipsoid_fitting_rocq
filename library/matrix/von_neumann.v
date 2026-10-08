From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From mathcomp Require Import ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.

(**md**************************************************************************)
(* # Von Neumann's trace inequality and the Hoffman-Wielandt inequality       *)
(*                                                                            *)
(* For a real symmetric matrix A of size n, spec A is the row vector of its   *)
(* eigenvalues in decreasing order, obtained by sorting the diagonal of the   *)
(* spectral decomposition of real_spectral.v (sym_spectral_diag). This file   *)
(* is part of item G7 of phase 5 (the semicircle law,                         *)
(* random_matrix/wigner.v): the Hoffman-Wielandt inequality makes the linear  *)
(* statistics of eigenvalues Lipschitz functions of the matrix, so that       *)
(* Gaussian concentration applies to them, and von Neumann's inequality is    *)
(* used in Lemma 5.14 of Koehler and Sohn (arXiv 2608.27372, line 5909).      *)
(*                                                                            *)
(* Main results:                                                              *)
(*                                                                            *)
(* - spec_decr, spec_perm, sum_spec, spec_decomposition: spec A is decreasing *)
(*   and is a permutation of sym_spectral_diag A, so \sum_i f (spec A 0 i)    *)
(*   does not depend on the decomposition; A = P^T diag_mx (spec A) P for     *)
(*   some orthogonal P when A is symmetric.                                   *)
(* - abel_ge0, abel_ge0_sum0: Abel summation, sum_i a_i w_i >= 0 for a        *)
(*   decreasing (and nonnegative, or with sum_i w_i = 0) and w with           *)
(*   nonnegative partial sums; sum_weight_le: for b decreasing and weights 0  *)
(*   <= c_j <= 1 of total k, sum_j b_j c_j is at most the sum of the k        *)
(*   largest b_j.                                                             *)
(* - doubly_stochastic_le, doubly_stochastic_le_mx: for a and b decreasing    *)
(*   and M doubly stochastic, sum_(i, j) a_i b_j M_ij <= sum_i a_i b_i        *)
(*   (without Birkhoff's theorem); orthogonal_sqr_row, orthogonal_sqr_col:    *)
(*   the squared entries of an orthogonal matrix form a doubly stochastic     *)
(*   matrix.                                                                  *)
(* - von_neumann_trace: \tr (A B) <= sum_i spec A 0 i * spec B 0 i for A and  *)
(*   B symmetric.                                                             *)
(* - mxdot_spec: |A|_F^2 = sum_i spec A 0 i ^+ 2; hoffman_wielandt: sum_i     *)
(*   (spec A 0 i - spec B 0 i)^2 <= |A - B|_F^2 for A and B symmetric;        *)
(*   spec_lipschitz: each eigenvalue is 1-Lipschitz for the Frobenius norm;   *)
(*   spec_stat_lipschitz: for f L-Lipschitz, A |-> sum_i f (spec A 0 i) is (L *)
(*   sqrt n)-Lipschitz for the Frobenius norm on symmetric matrices.          *)
(*                                                                            *)
(* ```                                                                        *)
(* spec_seq A == the sorted list of the eigenvalues of A                      *)
(* spec A == the eigenvalues of the symmetric matrix A, in decreasing order   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section spec.
Context {R : realType} {n : nat}.
Implicit Types A B : 'M[R]_n.

(* The eigenvalues of a symmetric matrix, sorted decreasingly. *)
Definition spec_seq A : seq R :=
  sort (fun x y => y <= x) [seq sym_spectral_diag A 0 i | i <- enum 'I_n].

Definition spec A : 'rV[R]_n := \row_i nth 0 (spec_seq A) i.

Lemma size_spec_seq A : size (spec_seq A) = n.
Proof. by rewrite size_sort size_map size_enum_ord. Qed.

Lemma perm_spec_seq A :
  perm_eq (spec_seq A) [seq sym_spectral_diag A 0 i | i <- enum 'I_n].
Proof. by rewrite perm_sort. Qed.

Lemma sorted_spec_seq A : sorted (fun x y : R => y <= x) (spec_seq A).
Proof. by apply: sort_sorted => x y; exact: le_total. Qed.

(* The spectrum is decreasing. *)
Lemma spec_decr A (i j : 'I_n) : (i <= j)%N -> spec A 0 j <= spec A 0 i.
Proof.
move=> ij; rewrite !mxE.
apply: (sorted_leq_nth _ _ 0 (sorted_spec_seq A)) => //.
- by move=> x y z /= yx zy; exact: le_trans zy yx.
- by rewrite inE size_spec_seq.
- by rewrite inE size_spec_seq.
Qed.

(* The spectrum is a permutation of the diagonal of the chosen spectral
   decomposition. *)
Lemma spec_perm A : exists s : 'S_n,
  forall i, spec A 0 i = sym_spectral_diag A 0 (s i).
Proof.
have : perm_eq (spec_seq A) [tuple sym_spectral_diag A 0 i | i < n].
  by apply: (perm_trans (perm_spec_seq A)); exact: perm_refl.
move=> /tuple_permP [p hp]; exists p => i.
by rewrite mxE hp (nth_map i) ?size_enum_ord // nth_ord_enum tnth_mktuple.
Qed.

(* Sums over the spectrum. *)
Lemma sum_spec A (f : R -> R) :
  \sum_i f (spec A 0 i) = \sum_i f (sym_spectral_diag A 0 i).
Proof.
have [p hp] := spec_perm A; under eq_bigr do rewrite hp.
rewrite (reindex_inj (@perm_inj _ p^-1)) /=.
by apply: eq_bigr => i _; rewrite permKV.
Qed.

(* A = P^T diag (spec A) P for some orthogonal P. *)
Lemma spec_decomposition A : A \is symmetricmx ->
  exists2 P : 'M[R]_n, P \is orthogonalmx & A = P^T *m diag_mx (spec A) *m P.
Proof.
move=> Asym; have [p hp] := spec_perm A.
pose P0 := sym_spectralmx A; have P0o := sym_spectralmx_orthogonal A.
exists (perm_mx p *m P0).
  by apply: mul_orthogonalmx => //; exact: perm_mx_orthogonal.
rewrite trmx_mul -!mulmxA [X in _ = _ *m X]mulmxA.
have KE : (perm_mx p)^T *m diag_mx (spec A) *m perm_mx p =
    diag_mx (sym_spectral_diag A).
  rewrite tr_perm_mx -row_permE -[_ *m perm_mx p]trmxK trmx_mul tr_perm_mx.
  rewrite -row_permE; apply/matrixP => i j; rewrite !mxE.
  rewrite (inj_eq (@perm_inj _ _)).
  by have := hp (p^-1%g i); rewrite mxE permKV => ->.
rewrite [X in _ *m X]mulmxA KE mulmxA.
exact: sym_spectralE.
Qed.

End spec.

Section abel.
Context {R : realFieldType}.

(* A sequence decreasing on [0, n) is decreasing between any two indices. *)
Lemma decr_le n (a : nat -> R) : (forall i, (i.+1 < n)%N -> a i.+1 <= a i) ->
  forall i j, (i <= j)%N -> (j < n)%N -> a j <= a i.
Proof.
move=> ha i j; elim: j => [|j IH]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP[/eqP -> //|]; rewrite ltnS => ij jn.
by apply: le_trans (ha _ jn) (IH ij (ltnW jn)).
Qed.

(* Abel summation: if a is decreasing and nonnegative on [0, n) and the
   partial sums of w are nonnegative, then sum_(i < n) a i w i >= 0. *)
Lemma abel_ge0 n (a w : nat -> R) :
  (forall i, (i.+1 < n)%N -> a i.+1 <= a i) ->
  (forall i, (i < n)%N -> 0 <= a i) ->
  (forall k, (k <= n)%N -> 0 <= \sum_(i < k) w i) ->
  0 <= \sum_(i < n) a i * w i.
Proof.
elim: n a => [|n IH] a ha a0 hw; first by rewrite big_ord0.
have -> : \sum_(i < n.+1) a i * w i =
    \sum_(i < n) (a i - a n) * w i + a n * \sum_(i < n.+1) w i.
  rewrite big_ord_recr [X in _ = _ + _ * X]big_ord_recr /= mulrDr addrA.
  congr (_ + _); rewrite mulr_sumr -big_split /=.
  by apply: eq_bigr => i _; rewrite mulrBl subrK.
apply: addr_ge0; last by rewrite mulr_ge0 ?a0 ?hw.
apply: (IH (fun i => a i - a n)).
- by move=> i ilt; rewrite lerD2r ha // ltnS ltnW.
- by move=> i ilt; rewrite subr_ge0 (decr_le ha) // ltnW.
- by move=> k kn; apply: hw; rewrite (leq_trans kn).
Qed.

(* The same with a of any sign, when the sum of w is 0. *)
Lemma abel_ge0_sum0 n (a w : nat -> R) :
  (forall i, (i.+1 < n)%N -> a i.+1 <= a i) ->
  (forall k, (k <= n)%N -> 0 <= \sum_(i < k) w i) -> \sum_(i < n) w i = 0 ->
  0 <= \sum_(i < n) a i * w i.
Proof.
case: n => [|m] ha hw w0; first by rewrite big_ord0.
have -> : \sum_(i < m.+1) a i * w i = \sum_(i < m.+1) (a i - a m) * w i.
  under [RHS]eq_bigr do rewrite mulrBl.
  by rewrite sumrB -mulr_sumr w0 mulr0 subr0.
apply: (@abel_ge0 m.+1 (fun i => a i - a m) w) => //.
- by move=> i ilt; rewrite lerD2r ha.
- by move=> i ilt; rewrite subr_ge0 (decr_le ha) // -ltnS.
Qed.

(* For b decreasing and 0 <= c j <= 1 with sum_j c j = k, the sum of
   b j c j is at most the sum of the k largest b j. *)
Lemma sum_weight_le n k (b c : nat -> R) : (k <= n)%N ->
  (forall i, (i.+1 < n)%N -> b i.+1 <= b i) ->
  (forall j, (j < n)%N -> 0 <= c j <= 1) -> \sum_(j < n) c j = k%:R ->
  \sum_(j < n) b j * c j <= \sum_(j < k) b j.
Proof.
move=> kn hb hc hck.
have sum_ind m : \sum_(i < m) ((i < k)%:R : R) = (minn m k)%:R.
  elim: m => [|m IH]; first by rewrite big_ord0 min0n.
  rewrite big_ord_recr /= IH; case: (ltnP m k) => mk.
    by rewrite (minn_idPl mk) -natrD addn1.
  by rewrite (minn_idPr (leqW mk)) addr0.
have W0 m : (m <= n)%N -> 0 <= \sum_(i < m) ((i < k)%:R - c i).
  move=> mn; rewrite sumrB sum_ind subr_ge0; case: (leqP m k) => mk.
    apply: le_trans (_ : _ <= \sum_(i < m) (1 : R)) _.
      by apply: ler_sum => i _; have /andP[] := hc i (leq_trans (ltn_ord i) mn).
    by rewrite sumr_const card_ord.
  rewrite -hck (big_ord_widen n (fun i => c i) mn) [X in _ <= X]big_mkcond /=.
  rewrite big_mkcond /=; apply: ler_sum => i _; case: ifP => // _.
  by have /andP[] := hc i (ltn_ord i).
have Wn : \sum_(i < n) ((i < k)%:R - c i) = 0.
  by rewrite sumrB sum_ind (minn_idPr kn) hck subrr.
have := @abel_ge0_sum0 n b (fun j => (j < k)%:R - c j) hb W0 Wn.
under eq_bigr do rewrite mulrBr.
rewrite sumrB subr_ge0 => h; apply: (le_trans h).
rewrite (big_ord_widen n (fun i => b i) kn) [X in _ <= X]big_mkcond /=.
rewrite le_eqVlt; apply/orP; left; apply/eqP; apply: eq_bigr => i _.
by case: ifP => _; rewrite ?mulr1 ?mulr0.
Qed.

(* For a and b decreasing and M doubly stochastic,
   sum_(i, j) a i b j M i j <= sum_i a i b i. *)
Lemma doubly_stochastic_le n (a b : nat -> R) (M : 'M[R]_n) :
  (forall i, (i.+1 < n)%N -> a i.+1 <= a i) ->
  (forall i, (i.+1 < n)%N -> b i.+1 <= b i) ->
  (forall i j, 0 <= M i j) -> (forall i, \sum_j M i j = 1) ->
  (forall j, \sum_i M i j = 1) ->
  \sum_(i < n) \sum_(j < n) a i * b j * M i j <= \sum_(i < n) a i * b i.
Proof.
move=> ha hb M0 Mrow Mcol.
case: n M ha hb M0 Mrow Mcol => [|k] M ha hb M0 Mrow Mcol.
  by rewrite !big_ord0.
pose m (i j : nat) := M (inord i) (inord j).
have mE (i j : 'I_k.+1) : m i j = M i j by rewrite /m !inord_val.
have colm (j : nat) : \sum_(i < k.+1) m i j = 1.
  by rewrite -(Mcol (inord j)); apply: eq_bigr => i _; rewrite /m inord_val.
have rowm (i : nat) : \sum_(j < k.+1) m i j = 1.
  by rewrite -(Mrow (inord i)); apply: eq_bigr => j _; rewrite /m inord_val.
have m0 i j : 0 <= m i j by exact: M0.
(* y i = sum_j b j M i j; then sum_i a i (b i - y i) >= 0 by Abel *)
pose y i := \sum_(j < k.+1) b j * m i j.
have -> : \sum_(i < k.+1) \sum_(j < k.+1) a i * b j * M i j =
    \sum_(i < k.+1) a i * y i.
  apply: eq_bigr => i _; rewrite /y mulr_sumr; apply: eq_bigr => j _.
  by rewrite mE mulrA.
rewrite -subr_ge0 -sumrB; under eq_bigr do rewrite -mulrBr.
apply: (@abel_ge0_sum0 k.+1 a (fun i => b i - y i) ha).
  (* the partial sums of y are at most those of b *)
  move=> p pn; rewrite sumrB subr_ge0 /y exchange_big /=.
  under eq_bigr do rewrite -mulr_sumr.
  apply: (@sum_weight_le k.+1 p b (fun j => \sum_(i0 < p) m i0 j) pn hb).
    move=> j _; apply/andP; split.
      by apply: sumr_ge0 => i _; exact: m0.
    rewrite -(colm j) (big_ord_widen k.+1 (fun i => m i j) pn) big_mkcond /=.
    by apply: ler_sum => i _; case: ifP.
  rewrite exchange_big /=; under eq_bigr do rewrite rowm.
  by rewrite sumr_const card_ord.
rewrite sumrB /y exchange_big /=.
under [X in _ - X]eq_bigr do rewrite -mulr_sumr colm mulr1.
by rewrite subrr.
Qed.

(* The same for row vectors a and b, decreasing in the order of 'I_n. *)
Lemma doubly_stochastic_le_mx n (a b : 'rV[R]_n) (M : 'M[R]_n) :
  (forall i j : 'I_n, (i <= j)%N -> a 0 j <= a 0 i) ->
  (forall i j : 'I_n, (i <= j)%N -> b 0 j <= b 0 i) ->
  (forall i j, 0 <= M i j) -> (forall i, \sum_j M i j = 1) ->
  (forall j, \sum_i M i j = 1) ->
  \sum_i \sum_j a 0 i * b 0 j * M i j <= \sum_i a 0 i * b 0 i.
Proof.
case: n a b M => [|k] a b M ha hb M0 Mrow Mcol; first by rewrite !big_ord0.
have := @doubly_stochastic_le k.+1 (fun i => a 0 (inord i))
  (fun i => b 0 (inord i)) M _ _ M0 Mrow Mcol.
move=> h; have := h _ _.
under eq_bigr do under eq_bigr do rewrite !inord_val.
under [X in _ <= X]eq_bigr do rewrite !inord_val.
apply.
- by move=> i ilt; apply: ha; rewrite !inordK // ltnW.
- by move=> i ilt; apply: hb; rewrite !inordK // ltnW.
Qed.

End abel.

Section von_neumann.
Context {R : realType} {n : nat}.
Implicit Types A B : 'M[R]_n.

(* The squared entries of an orthogonal matrix form a doubly stochastic
   matrix. *)
Lemma orthogonal_sqr_row (U : 'M[R]_n) i : U \is orthogonalmx ->
  \sum_j U i j ^+ 2 = 1.
Proof.
move=> /orthogonalmxP UU; have := congr1 (fun M : 'M[R]_n => M i i) UU.
rewrite /= [in X in _ = X -> _]mxE eqxx mulr1n => <-.
by rewrite mxE; apply: eq_bigr => j _; rewrite mxE expr2.
Qed.

Lemma orthogonal_sqr_col (U : 'M[R]_n) j : U \is orthogonalmx ->
  \sum_i U i j ^+ 2 = 1.
Proof.
rewrite -trmx_orthogonal => /(orthogonal_sqr_row j) <-.
by apply: eq_bigr => i _; rewrite mxE.
Qed.

(* von Neumann's trace inequality. *)
Theorem von_neumann_trace A B : A \is symmetricmx -> B \is symmetricmx ->
  \tr (A *m B) <= \sum_i spec A 0 i * spec B 0 i.
Proof.
move=> As Bs; have [P Po AE] := spec_decomposition As.
have [Q Qo BE] := spec_decomposition Bs.
pose U := P *m Q^T.
have Uo : U \is orthogonalmx.
  by apply: mul_orthogonalmx => //; rewrite trmx_orthogonal.
(* tr (A B) = sum_(i, j) a_i b_j U_ij^2 with U = P Q^T *)
have -> : \tr (A *m B) = \sum_i \sum_j spec A 0 i * spec B 0 j * U i j ^+ 2.
  rewrite [in LHS]AE [in LHS]BE -!mulmxA mxtrace_mulC -!mulmxA.
  rewrite [P *m _]mulmxA (_ : Q *m P^T = U^T).
    by rewrite /U trmx_mul trmxK.
  rewrite /mxtrace; apply: eq_bigr => i _.
  rewrite mul_diag_mx !mxE big_distrr /=; apply: eq_bigr => j _.
  rewrite mul_diag_mx !mxE /U.
  set s := \sum_j0 _; set x := (spec_seq A)`_i; set y := (spec_seq B)`_j.
  ring.
pose M := \matrix_(i, j) U i j ^+ 2.
have ME i j : U i j ^+ 2 = M i j by rewrite /M !mxE.
under eq_bigr do under eq_bigr do rewrite ME.
apply: doubly_stochastic_le_mx; try exact: spec_decr.
- by move=> i j; rewrite -ME; exact: sqr_ge0.
- by move=> i; under eq_bigr do rewrite -ME; exact: orthogonal_sqr_row.
- by move=> j; under eq_bigr do rewrite -ME; exact: orthogonal_sqr_col.
Qed.

(* The Frobenius norm is the Euclidean norm of the spectrum. *)
Lemma mxdot_spec A : A \is symmetricmx -> mxdot A A = \sum_i spec A 0 i ^+ 2.
Proof.
move=> As; have [P Po AE] := spec_decomposition As.
exact: (spectral_mxdot Po AE).
Qed.

(* The Hoffman-Wielandt inequality. *)
Theorem hoffman_wielandt A B : A \is symmetricmx -> B \is symmetricmx ->
  \sum_i (spec A 0 i - spec B 0 i) ^+ 2 <= mxdot (A - B) (A - B).
Proof.
move=> As Bs.
have -> : \sum_i (spec A 0 i - spec B 0 i) ^+ 2 = \sum_i spec A 0 i ^+ 2 +
    \sum_i spec B 0 i ^+ 2 - 2 * \sum_i spec A 0 i * spec B 0 i.
  rewrite mulr_sumr -big_split -sumrB /=; apply: eq_bigr => i _.
  by set x := spec A 0 i; set y := spec B 0 i; ring.
rewrite -!mxdot_spec // mxdotBl !mxdotBr (mxdotC B A).
have AB : mxdot A B = \tr (A *m B).
  by rewrite mxdot_trace; move/symmetricmxP: Bs => ->.
have vn := von_neumann_trace As Bs; rewrite -AB in vn.
rewrite (_ : mxdot A A - mxdot A B - (mxdot A B - mxdot B B) =
  mxdot A A + mxdot B B - 2 * mxdot A B); first by ring.
by rewrite lerD2l lerN2 ler_pM2l.
Qed.

(* The sorted spectrum is 1-Lipschitz for the Frobenius norm. *)
Lemma spec_lipschitz A B (i : 'I_n) : A \is symmetricmx -> B \is symmetricmx ->
  `|spec A 0 i - spec B 0 i| <= frobenius (A - B).
Proof.
move=> As Bs; rewrite /frobenius.
apply: le_trans (_ : _ <= Num.sqrt (\sum_j (spec A 0 j - spec B 0 j) ^+ 2)) _.
  rewrite -sqrtr_sqr ler_wsqrtr // (bigD1 i) //= lerDl.
  by apply: sumr_ge0 => j _; exact: sqr_ge0.
by rewrite ler_wsqrtr // hoffman_wielandt.
Qed.

(* A linear statistic of the spectrum of an L-Lipschitz function is
   (L sqrt n)-Lipschitz for the Frobenius norm. *)
Lemma spec_stat_lipschitz (f : R -> R) (L : R) A B :
  A \is symmetricmx -> B \is symmetricmx ->
  (forall x y, `|f x - f y| <= L * `|x - y|) ->
  `|\sum_i f (spec A 0 i) - \sum_i f (spec B 0 i)| <=
    L * Num.sqrt n%:R * frobenius (A - B).
Proof.
move=> As Bs hf.
have L0 : 0 <= L.
  by have := hf 0 1; rewrite sub0r normrN normr1 mulr1; apply: le_trans.
rewrite -sumrB; apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : \sum_i L * `|spec A 0 i - spec B 0 i| <= _).
  by apply: ler_sum => i _; exact: hf.
rewrite -mulr_sumr -mulrA ler_wpM2l //.
(* Cauchy-Schwarz, then Hoffman-Wielandt *)
set x := fun i => spec A 0 i - spec B 0 i.
have cs := sum_cauchy_schwarz (fun i => `|x i|) (fun=> 1).
have e1 : \sum_i `|x i| * 1 = \sum_i `|x i|.
  by apply: eq_bigr => i _; rewrite mulr1.
have e2 : \sum_i `|x i| * `|x i| = \sum_i x i ^+ 2.
  by apply: eq_bigr => i _; rewrite -normrM -expr2 ger0_norm // sqr_ge0.
have e3 : \sum_(i < n) (1 : R) * 1 = n%:R by rewrite mulr1 sumr_const card_ord.
rewrite e1 e2 e3 in cs.
apply: le_trans (_ : Num.sqrt ((\sum_i x i ^+ 2) * n%:R) <= _).
  by rewrite -[X in X <= _]ger0_norm ?sumr_ge0 // -sqrtr_sqr ler_wsqrtr.
rewrite sqrtrM; first by apply: sumr_ge0 => i _; exact: sqr_ge0.
rewrite [X in X <= _]mulrC; apply: ler_wpM2l; first exact: sqrtr_ge0.
by rewrite /frobenius ler_wsqrtr // hoffman_wielandt.
Qed.

End von_neumann.
