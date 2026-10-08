From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear vector interval boolp classical_sets.
From mathcomp Require Import functions reals set_interval topology normedtype.
From mathcomp Require Import sequences derive realfun exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import euclidean real_spectral self_concordant.

(**md**************************************************************************)
(* # The log-determinant barrier                                              *)
(*                                                                            *)
(* -ln det is a self-concordant barrier with parameter n on the trace slices  *)
(* of the cone of positive definite n x n matrices (Nesterov-Nemirovskii,     *)
(* Proposition 5.4.5), and -ln det (A - m I) - ln det (M I - A) is a          *)
(* 2n-self-concordant barrier on the matrices of trace n with m I < A < M I.  *)
(* This is Lemma 2.8 of Koehler and Sohn (arXiv 2608.27372). Matrices are     *)
(* seen as row vectors of size n * n through mxvec, so that                   *)
(* self_concordant.v applies; the inner product of mxvec A and mxvec B is     *)
(* the Frobenius product mxdot A B.                                           *)
(*                                                                            *)
(* ```                                                                        *)
(*              posdefmx A == A is symmetric positive definite:               *)
(*                            0 < x A x^T for every row vector x != 0         *)
(*            pd_slice n s == the matrices A (as mxvec A) that are positive   *)
(*                            definite with trace s                           *)
(*      logdet_barrier n x == - ln (det (vec_mx x)), for x : 'rV[R]_(n * n)   *)
(*         pd_slice2 n m M == the matrices A (as mxvec A) of trace n with     *)
(*                            A - m I and M I - A positive definite           *)
(* logdet_barrier2 n m M x == - ln det (A - m I) - ln det (M I - A)           *)
(*                            + n ln ((1 - m) (M - 1)), with A = vec_mx x     *)
(*         sym_traceless n == the subspace of the mxvec of the symmetric      *)
(*                            matrices of trace 0                             *)
(*            logsum l c t == c - sum_i ln (1 + t l_i), for l : 'rV[R]_k      *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - logdet_line: for A positive definite and U symmetric,                    *)
(*   -ln det (A + t U) = c - sum_i ln (1 + t l_i) whenever A + t U is         *)
(*   positive definite, which happens exactly when every 1 + t l_i is         *)
(*   positive; tr (A^-1 U) and tr ((A^-1 U)^2) are the sums of the l_i and    *)
(*   of their squares (simultaneous diagonalization, congruence_diag).        *)
(* - logsum_sc_barrier: a function that is c - sum_i ln (1 + t l_i), i < k,   *)
(*   along every line through D, and whose first and second derivatives at    *)
(*   each point are a linear and a bilinear form, is a k-self-concordant      *)
(*   barrier on D.                                                            *)
(* - rel_open_convex_pd_slice, logdet_sc_barrier: pd_slice n s is convex and  *)
(*   relatively open with directions sym_traceless n, and logdet_barrier n    *)
(*   is an n-self-concordant barrier on it.                                   *)
(* - logdet_barrier_ge0, logdet_barrier_one: logdet_barrier n >= 0 on         *)
(*   pd_slice n n, with value 0 at the identity (det A <= (tr A / n)^n).      *)
(* - rel_open_convex_pd_slice2, logdet2_sc_barrier: for all m and M,          *)
(*   pd_slice2 n m M is convex and relatively open with directions            *)
(*   sym_traceless n, and logdet_barrier2 n m M is a 2n-self-concordant       *)
(*   barrier on it.                                                           *)
(* - logdet_barrier2_ge0, logdet_barrier2_one: if m < 1 < M, then             *)
(*   logdet_barrier2 n m M >= 0 on pd_slice2 n m M, with value 0 at the       *)
(*   identity.                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section logdet_definitions.
Context {R : realType}.

Definition posdefmx n (A : 'M[R]_n) : Prop :=
  A \is symmetricmx /\ forall x : 'rV[R]_n, x != 0 -> 0 < mxdot x (x *m A).

Definition pd_slice n (s : R) : set 'rV[R]_(n * n) :=
  [set x | posdefmx (vec_mx x) /\ \tr (vec_mx x) = s].

Definition logdet_barrier n (x : 'rV[R]_(n * n)) : R := - ln (\det (vec_mx x)).

Definition pd_slice2 n (m M : R) : set 'rV[R]_(n * n) :=
  [set x | posdefmx (vec_mx x - m%:M) /\ posdefmx (M%:M - vec_mx x) /\
           \tr (vec_mx x) = n%:R].

Definition logdet_barrier2 n (m M : R) (x : 'rV[R]_(n * n)) : R :=
  - ln (\det (vec_mx x - m%:M)) - ln (\det (M%:M - vec_mx x)) +
  n%:R * ln ((1 - m) * (M - 1)).

End logdet_definitions.

Arguments pd_slice {R} n s.
Arguments logdet_barrier {R} n x.
Arguments pd_slice2 {R} n m M.
Arguments logdet_barrier2 {R} n m M x.

Section mxvec_facts.
Context {R : realType}.

(* mxvec is an isometry for the Frobenius products. *)
Lemma mxdot_mxvec m n (A B : 'M[R]_(m, n)) :
  mxdot (mxvec A) (mxvec B) = mxdot A B.
Proof.
rewrite /mxdot big_ord1 (reindex _ (curry_mxvec_bij m n)) /=.
rewrite pair_big /=; apply: eq_bigr => -[i j] _ /=.
by rewrite !mxvecE.
Qed.

Lemma frobenius_mxvec m n (A : 'M[R]_(m, n)) :
  frobenius (mxvec A) = frobenius A.
Proof. by rewrite /frobenius mxdot_mxvec. Qed.

End mxvec_facts.

Section posdef.
Context {R : realType}.
Implicit Types n : nat.

(* The spectral decomposition of a positive definite matrix has positive
   eigenvalues. *)
Lemma posdefmx_spectral n (A : 'M[R]_n) : posdefmx A ->
  exists2 P : 'M[R]_n, P \is orthogonalmx &
    exists2 d : 'rV[R]_n, A = P^T *m diag_mx d *m P & forall i, 0 < d 0 i.
Proof.
move=> [Asym Apos].
have [P Po [d AE]] := symmetric_spectral Asym.
exists P => //; exists d => // i.
have ev := spectral_eigenvector i Po AE.
have u1 := orthogonalmx_row_unit i Po.
rewrite mxdot_trmx in u1.
have x0 : row i P != 0.
  apply/eqP => r0; move: u1; rewrite r0 mxdot0l => /eqP.
  by rewrite eq_sym oner_eq0.
have := Apos _ x0.
have AT : A^T = A by apply/symmetricmxP.
have -> : row i P *m A = d 0 i *: row i P.
  by rewrite -[A]AT -[row i P]trmxK -trmx_mul ev linearZ /= trmxK.
by rewrite mxdotZr u1 mulr1.
Qed.

(* G^T diag(c) G with G invertible is positive definite exactly when the
   c_i are positive. *)
Lemma posdefmx_congruence n (G : 'M[R]_n) (c : 'rV[R]_n) : G \in unitmx ->
  posdefmx (G^T *m diag_mx c *m G) <-> forall i, 0 < c 0 i.
Proof.
move=> Gu.
have GTu : G^T \in unitmx by rewrite unitmx_tr.
have form (x : 'rV[R]_n) : mxdot x (x *m (G^T *m diag_mx c *m G)) =
    \sum_i c 0 i * (x *m G^T) 0 i ^+ 2.
  rewrite !mulmxA mxdotC mxdot_mulmxr mxdotC /mxdot big_ord1.
  move: (x *m G^T) => y.
  apply: eq_bigr => i _; rewrite mul_mx_diag mxE.
  have -> : y 0 i = y ord0 i by [].
  by rewrite expr2; ring.
have Ssym : G^T *m diag_mx c *m G \is symmetricmx.
  by apply/symmetricmxP; rewrite !trmx_mul trmxK tr_diag_mx mulmxA.
split => [[_ pos] i|cpos].
  pose x := (delta_mx 0 i : 'rV[R]_n) *m invmx G^T.
  have xG : x *m G^T = delta_mx 0 i by rewrite -mulmxA mulVmx // mulmx1.
  have x0 : x != 0.
    apply/eqP => x0; move: xG; rewrite x0 mul0mx => /rowP/(_ i).
    by rewrite !mxE !eqxx /= => /eqP; rewrite eq_sym oner_eq0.
  have := pos x x0; rewrite form xG (bigD1 i) //= big1 ?addr0.
    by move=> j ji; rewrite mxE (negbTE ji) andbF /= expr0n /= mulr0.
  by rewrite mxE !eqxx /= expr1n mulr1.
split => // x x0.
have y0 : x *m G^T != 0.
  apply: contra x0 => /eqP y0.
  by rewrite -[x]mulmx1 -(mulmxV GTu) mulmxA y0 mul0mx.
have [i0 [j0 yj]] := matrix0Pn _ y0.
rewrite form (bigD1 j0) //=.
apply: ltr_wpDr.
  by apply: sumr_ge0 => j _; rewrite mulr_ge0 ?sqr_ge0 // ltW.
rewrite mulr_gt0 // exprn_even_gt0 //.
by rewrite (ord1 i0) in yj; rewrite yj orbT.
Qed.

Lemma det_congruence n (G : 'M[R]_n) (c : 'rV[R]_n) :
  \det (G^T *m diag_mx c *m G) = \det G ^+ 2 * \prod_i c 0 i.
Proof. by rewrite !det_mulmx det_tr det_diag; ring. Qed.

(* Simultaneous diagonalization by congruence: for A positive definite and U
   symmetric, A = G^T G and U = G^T diag(l) G with G invertible. *)
Lemma congruence_diag n (A U : 'M[R]_n) : posdefmx A -> U \is symmetricmx ->
  exists (G : 'M[R]_n) (l : 'rV[R]_n),
    [/\ G \in unitmx, A = G^T *m G & U = G^T *m diag_mx l *m G].
Proof.
move=> Apd Usym.
have [Q Qo [a AE apos]] := posdefmx_spectral Apd.
(* A = C^T C with C = diag(sqrt a) Q, and Ci = C^-1 *)
pose sa := \row_i Num.sqrt (a 0 i).
pose isa := \row_i (Num.sqrt (a 0 i))^-1.
pose C := diag_mx sa *m Q.
pose Ci := Q^T *m diag_mx isa.
have QQ : Q *m Q^T = 1%:M by apply/orthogonalmxP.
have QtQ : Q^T *m Q = 1%:M by exact: orthogonalmxT.
have sa0 i : Num.sqrt (a 0 i) != 0 by rewrite sqrtr_eq0 -ltNge apos.
have dd : diag_mx sa *m diag_mx isa = 1%:M.
  rewrite mulmx_diag -diag_const_mx; congr diag_mx; apply/rowP => i.
  by rewrite !mxE mulfV.
have dd' : diag_mx isa *m diag_mx sa = 1%:M.
  rewrite mulmx_diag -diag_const_mx; congr diag_mx; apply/rowP => i.
  by rewrite !mxE mulVf.
have CCi : C *m Ci = 1%:M.
  by rewrite /C /Ci mulmxA -(mulmxA _ Q) QQ mulmx1 dd.
have CiC : Ci *m C = 1%:M.
  by rewrite /C /Ci mulmxA -(mulmxA _ (diag_mx isa)) dd' mulmx1 QtQ.
have AC : A = C^T *m C.
  rewrite AE /C trmx_mul tr_diag_mx -!mulmxA; congr (_ *m _).
  rewrite mulmxA mulmx_diag; congr (diag_mx _ *m _); apply/rowP => i.
  by rewrite !mxE -expr2 sqr_sqrtr // ltW.
(* diagonalize Ci^T U Ci *)
pose S := Ci^T *m U *m Ci.
have Ssym : S \is symmetricmx.
  have UT : U^T = U by apply/symmetricmxP.
  apply/symmetricmxP; rewrite /S !trmx_mul trmxK UT.
  by rewrite !trmxK /Ci !mulmxA.
have [P Po [l SE]] := symmetric_spectral Ssym.
have PtP : P^T *m P = 1%:M by exact: orthogonalmxT.
exists (P *m C), l; split.
- by rewrite unitmx_mul orthogonalmx_unit // (mulmx1_unit CCi).1.
- by rewrite AC [(P *m C)^T]trmx_mul -mulmxA [P^T *m (P *m C)]mulmxA PtP mul1mx.
have key (C0 Ci0 : 'M[R]_n) : Ci0 *m C0 = 1%:M ->
    U = C0^T *m (Ci0^T *m U *m Ci0) *m C0.
  move=> h; rewrite !mulmxA -trmx_mul h trmx1 mul1mx.
  by rewrite -mulmxA h mulmx1.
rewrite {1}(key C Ci CiC) -/S SE.
by rewrite [(P *m C)^T]trmx_mul !mulmxA.
Qed.

End posdef.


Section logdet_line.
Context {R : realType}.
Implicit Types n : nat.

Lemma ln_prod k (F : 'I_k -> R) : (forall i, 0 < F i) ->
  0 < \prod_i F i /\ ln (\prod_i F i) = \sum_i ln (F i).
Proof.
move=> F0; elim/big_rec2: _ => [|i p s _ [p0 hp]]; first by rewrite ln1 ltr01.
by split; [exact: mulr_gt0 | rewrite lnM ?posrE // hp].
Qed.

(* Along a line through a positive definite A in a symmetric direction U,
   -ln det (A + t U) = c - sum_i ln (1 + t l_i), where l is the spectrum of
   U relative to A; A + t U is positive definite exactly when every
   1 + t l_i is positive, and tr (A^-1 U) and tr ((A^-1 U)^2) are the sums
   of the l_i and of their squares. *)
Lemma logdet_line n (A U : 'M[R]_n) : posdefmx A -> U \is symmetricmx ->
  exists (c : R) (l : 'rV[R]_n),
  [/\ forall t : R, posdefmx (A + t *: U) <-> (forall i, 0 < 1 + t * l 0 i),
      forall t : R, posdefmx (A + t *: U) ->
        - ln (\det (A + t *: U)) = c - \sum_i ln (1 + t * l 0 i),
      \tr (invmx A *m U) = \sum_i l 0 i &
      \tr (invmx A *m U *m invmx A *m U) = \sum_i l 0 i ^+ 2].
Proof.
move=> Apd Usym.
have [G [l [Gu AE UE]]] := congruence_diag Apd Usym.
have line (t : R) : A + t *: U = G^T *m diag_mx (\row_i (1 + t * l 0 i)) *m G.
  have -> : diag_mx (\row_i (1 + t * l 0 i)) = 1%:M + t *: diag_mx l.
    apply/matrixP => i j; rewrite !mxE.
    by case: (i == j) => /=; rewrite ?mulr1n ?mulr0n ?mulr0 ?addr0.
  by rewrite mulmxDr mulmxDl mulmx1 -AE -scalemxAr -scalemxAl -UE.
have dG : 0 < \det G ^+ 2.
  by rewrite exprn_even_gt0 //= -unitfE -unitmxE.
(* the traces: invmx A *m U = invmx G *m diag_mx l *m G *)
pose X := invmx G *m diag_mx l *m G.
have Au : A \in unitmx by rewrite AE unitmx_mul unitmx_tr Gu.
have AX : A *m X = U.
  by rewrite AE UE /X !mulmxA -(mulmxA _ G) mulmxV // mulmx1.
have AU : invmx A *m U = X by rewrite -AX mulmxA mulVmx // mul1mx.
have GG : G *m invmx G = 1%:M by rewrite mulmxV.
have T1 : \tr X = \sum_i l 0 i.
  by rewrite /X mxtrace_mulC mulmxA GG mul1mx mxtrace_diag.
have XX : X *m X = invmx G *m diag_mx (\row_i (l 0 i ^+ 2)) *m G.
  rewrite /X -!mulmxA; congr (_ *m _).
  rewrite !mulmxA -(mulmxA _ G (invmx G)) GG mulmx1 mulmx_diag.
  by congr (diag_mx _ *m _); apply/rowP => i; rewrite !mxE expr2.
have T2 : \tr (X *m X) = \sum_i l 0 i ^+ 2.
  rewrite XX mxtrace_mulC mulmxA GG mul1mx mxtrace_diag.
  by apply: eq_bigr => i _; rewrite mxE.
exists (- ln (\det G ^+ 2)), l; split.
- move=> t; rewrite line posdefmx_congruence //.
  by split => h i; have := h i; rewrite mxE.
- move=> t; rewrite line posdefmx_congruence // => pos.
  have pos' i : 0 < 1 + t * l 0 i by have := pos i; rewrite mxE.
  have [p0 pE] := ln_prod pos'.
  rewrite det_congruence.
  under eq_bigr do rewrite mxE.
  by rewrite lnM ?posrE // pE opprD.
- by rewrite AU T1.
by rewrite -(mulmxA _ U) mulmxA AU -mulmxA AU T2.
Qed.

End logdet_line.

Section logsum.
Context {R : realType} (k : nat) (l : 'rV[R]_k) (c : R).

(* The function c - sum_i ln (1 + t l_i) and its first three derivatives. *)
Definition logsum (t : R) : R := c - \sum_i ln (1 + t * l 0 i).
Definition logsum1 (t : R) : R := - \sum_i l 0 i / (1 + t * l 0 i).
Definition logsum2 (t : R) : R := \sum_i (l 0 i / (1 + t * l 0 i)) ^+ 2.
Definition logsum3 (t : R) : R := - 2 * \sum_i (l 0 i / (1 + t * l 0 i)) ^+ 3.

Lemma logsum_derive (t : R) : (forall i, 0 < 1 + t * l 0 i) ->
  [/\ is_derive t 1 logsum (logsum1 t), is_derive t 1 logsum1 (logsum2 t) &
      is_derive t 1 logsum2 (logsum3 t)].
Proof.
move=> pos.
have hg (i : 'I_k) : is_derive t 1 (fun s : R => 1 + s * l 0 i) (l 0 i).
  by apply: is_derive_eq; rewrite add0r mul1r scaler0 add0r [_%:A]mulr1.
have d0 (i : 'I_k) : is_derive t 1 (fun s : R => ln (1 + s * l 0 i))
    (l 0 i / (1 + t * l 0 i)).
  have := @is_derive1_comp R (@ln R) (fun s : R => 1 + s * l 0 i) t _ _
    (is_derive1_ln (pos i)) (hg i).
  by move=> h; apply: is_derive_eq h _; rewrite mulrC.
have d1 (i : 'I_k) : is_derive t 1 (fun s : R => l 0 i / (1 + s * l 0 i))
    (- (l 0 i / (1 + t * l 0 i)) ^+ 2).
  have p0 : 1 + t * l 0 i != 0 by rewrite gt_eqF.
  have := is_deriveZ (l 0 i)
    (@is_deriveV R (fun s : R => 1 + s * l 0 i) t (l 0 i) 1 p0 (hg i)).
  move=> h; apply: is_derive_eq h _.
  by rewrite /GRing.scale /=; field.
have d2 (i : 'I_k) :
    is_derive t 1 (fun s : R => (l 0 i / (1 + s * l 0 i)) ^+ 2)
      (- 2 * (l 0 i / (1 + t * l 0 i)) ^+ 3).
  have := is_deriveX 2 (d1 i).
  move=> h; apply: is_derive_eq h _.
  by rewrite /GRing.scale /=; ring.
have e0 : logsum = cst c - \sum_i (fun s : R => ln (1 + s * l 0 i)).
  by apply/funext => s; rewrite /logsum fct_sumE.
have e1 : logsum1 = - \sum_i (fun s : R => l 0 i / (1 + s * l 0 i)).
  by apply/funext => s; rewrite /logsum1 fct_sumE.
have e2 : logsum2 = \sum_i (fun s : R => (l 0 i / (1 + s * l 0 i)) ^+ 2).
  by apply/funext => s; rewrite /logsum2 fct_sumE.
split.
- rewrite e0; have := is_deriveB (is_derive_cst c t 1) (is_derive_sum d0).
  by move=> h; apply: is_derive_eq h _; rewrite /logsum1 sub0r.
- rewrite e1; have := is_deriveN (is_derive_sum d1).
  move=> h; apply: is_derive_eq h _.
  by rewrite /logsum2 sumrN opprK.
rewrite e2; have := is_derive_sum d2.
move=> h; apply: is_derive_eq h _.
by rewrite /logsum3 mulr_sumr.
Qed.

Lemma logsum2_ge0 (t : R) : 0 <= logsum2 t.
Proof. by apply: sumr_ge0 => i _; rewrite sqr_ge0. Qed.

Lemma logsum_sc (t : R) : logsum3 t ^+ 2 <= 4%:R * logsum2 t ^+ 3.
Proof.
have key (mu : 'I_k -> R) :
    (\sum_i mu i ^+ 3) ^+ 2 <= (\sum_i mu i ^+ 2) ^+ 3.
  set S2 := \sum_i mu i ^+ 2.
  have S20 : 0 <= S2 by apply: sumr_ge0 => i _; rewrite sqr_ge0.
  have le_S2 i : mu i ^+ 2 <= S2.
    rewrite /S2 (bigD1 i) //= lerDl; apply: sumr_ge0 => j _; exact: sqr_ge0.
  (* Cauchy-Schwarz for mu and mu^2, and sum mu^4 <= S2^2 *)
  have cs := sum_cauchy_schwarz mu (fun i => mu i ^+ 2).
  have e3 : \sum_i mu i * mu i ^+ 2 = \sum_i mu i ^+ 3.
    by apply: eq_bigr => i _; rewrite expr2 exprS expr2.
  have e2 : \sum_i mu i * mu i = S2 by apply: eq_bigr => i _; rewrite expr2.
  have q : \sum_i mu i ^+ 2 * mu i ^+ 2 <= S2 * S2.
    rewrite /S2 mulr_suml; apply: ler_sum => i _.
    by rewrite ler_wpM2l ?sqr_ge0 // le_S2.
  rewrite e3 e2 in cs.
  apply: le_trans cs _; rewrite exprS expr2 [S2 * (S2 * S2)]mulrA.
  by rewrite -mulrA ler_wpM2l.
rewrite /logsum3 /logsum2 exprMn sqrrN.
have -> : 2 ^+ 2 = 4%:R :> R by rewrite expr2 -natrM.
by rewrite ler_pM2l ?ltr0n //; exact: (key (fun i => l 0 i / (1 + t * l 0 i))).
Qed.

Lemma logsum_bp (t : R) : logsum1 t ^+ 2 <= k%:R * logsum2 t.
Proof.
rewrite /logsum1 /logsum2 sqrrN.
have := sum_cauchy_schwarz (fun i => l 0 i / (1 + t * l 0 i)) (fun=> 1).
under eq_bigr do rewrite mulr1.
under [X in _ <= _ * X]eq_bigr do rewrite mulr1.
rewrite sumr_const card_ord mulrC => h; apply: le_trans h _.
by rewrite ler_wpM2l ?ler0n //; apply: ler_sum => i _; rewrite expr2.
Qed.

Lemma logsum_blowup : (forall t, 0 <= t < 1 -> forall i, 0 < 1 + t * l 0 i) ->
  ~ (forall i, 0 < 1 + l 0 i) -> logsum t @[t --> (1 : R)^'-] --> +oo.
Proof.
move=> pos npos.
have [i0 hi0] := (existsNP _).2 npos.
have li0 : 1 + l 0 i0 <= 0 by rewrite leNgt; apply/negP.
(* the term i0 gives - ln (1 - t), the others are bounded below *)
pose K := \sum_(i | i != i0) ln (1 + `|l 0 i|).
apply/cvgryPgt => A.
have e0 : 0 < expR (c - K - A) := expR_gt0 _.
have h1 : 1 - expR (c - K - A) < 1 by rewrite ltrBlDr ltrDl.
near=> t.
have t1 : t < 1 by near: t; exact: nbhs_left_lt.
have tg : 1 - expR (c - K - A) < t by near: t; exact: nbhs_left_gt.
have tp : 0 < t by near: t; exact: nbhs_left_gt.
have tt : 0 <= t < 1 by rewrite (ltW tp) t1.
have p := pos t tt.
rewrite /logsum (bigD1 i0) //=.
have b0 : ln (1 + t * l 0 i0) <= ln (1 - t).
  rewrite ler_ln ?posrE ?p ?subr_gt0 //.
  have : t * (1 + l 0 i0) <= 0 by rewrite mulr_ge0_le0 // ltW.
  by rewrite mulrDr mulr1 => h; lra.
have b1 : \sum_(i | i != i0) ln (1 + t * l 0 i) <= K.
  apply: ler_sum => i _; rewrite ler_ln ?posrE ?p ?ltr_wpDr //.
  rewrite lerD2l; apply: le_trans (ler_norm _) _.
  by rewrite normrM ger0_norm ?(ltW tp) // ler_piMl // ltW.
have b2 : ln (1 - t) < c - K - A.
  by rewrite -[X in _ < X]expRK ltr_ln ?posrE ?subr_gt0 // ltrBlDl -ltrBlDr.
lra.
Unshelve. all: by end_near.
Qed.

End logsum.

Section sym_traceless.
Context {R : realType}.
Implicit Types n : nat.

(* The kernel of h |-> mxvec (U - U^T + (tr U) I), U = vec_mx h, is the set
   of the mxvec of the symmetric matrices of trace 0. *)
Definition symtr_map n (h : 'rV[R]_(n * n)) : 'rV[R]_(n * n) :=
  mxvec (vec_mx h - (vec_mx h)^T + (\tr (vec_mx h))%:M).

Lemma symtr_map_is_linear n : linear (@symtr_map n).
Proof.
move=> a u v; rewrite /symtr_map.
have E : vec_mx (a *: u + v) = a *: vec_mx u + vec_mx v :> 'M[R]_n.
  by rewrite linearP.
rewrite E; move: (vec_mx u) (vec_mx v) => U W.
rewrite -linearP; congr mxvec.
rewrite mxtraceD mxtraceZ.
by apply/matrixP => i j; rewrite !mxE; ring.
Qed.

Definition symtr_lin n : {linear 'rV[R]_(n * n) -> 'rV[R]_(n * n)} :=
  HB.pack (@symtr_map n)
    (GRing.isLinear.Build _ _ _ _ (@symtr_map n) (@symtr_map_is_linear n)).

Definition sym_traceless n : {vspace 'rV[R]_(n * n)} :=
  lker (linfun (symtr_lin n)).

Lemma sym_tracelessP n (h : 'rV[R]_(n * n)) :
  h \in sym_traceless n <-> vec_mx h \is symmetricmx /\ \tr (vec_mx h) = 0.
Proof.
rewrite /sym_traceless memv_ker lfunE /= /symtr_map mxvec_eq0.
move: (vec_mx h) => U.
split => [/eqP E|[/symmetricmxP UT tr0]]; last first.
  by rewrite UT tr0 subrr add0r raddf0.
have tr0 : \tr U = 0.
  have := congr1 mxtrace E; rewrite !mxtraceD raddfN /= mxtrace_tr subrr add0r.
  rewrite mxtrace_scalar mxtrace0 => /eqP.
  rewrite mulrn_eq0 => /orP[/eqP n0|/eqP //].
  by rewrite /mxtrace big1 // => -[i ilt] _; exfalso; move: ilt; rewrite n0.
split => //; apply/symmetricmxP.
move: E; rewrite tr0 raddf0 addr0 => /eqP; rewrite subr_eq0 => /eqP.
by move=> /esym.
Qed.

Lemma dim_sym_traceless n : (\dim (sym_traceless n) <= n * n)%N.
Proof.
apply: (leq_trans (dimvS (subvf _))); rewrite dimvf /=.
by rewrite /dim /= mul1n.
Qed.

End sym_traceless.

Section pd_slice.
Context {R : realType}.
Implicit Types n : nat.

(* A positive definite matrix dominates b I for some b > 0. *)
Lemma posdefmx_ge n (A : 'M[R]_n) : posdefmx A ->
  exists2 b : R, 0 < b & forall x : 'rV[R]_n, b * mxdot x x <= mxdot x (x *m A).
Proof.
move=> Apd; have [Asym _] := Apd.
have [P Po [d AE dpos]] := posdefmx_spectral Apd.
pose b := \big[Num.min/1]_i d 0 i.
have b0 : 0 < b.
  by rewrite /b; elim/big_ind: _ => // x y x0 y0; rewrite lt_min x0 y0.
have bd i : b <= d 0 i by rewrite /b (bigD1 i) //= ge_min lexx.
exists b => // x.
have := (spectral_form_ge b Po AE).2 bd x^T.
have AT : A^T = A by apply/symmetricmxP.
by rewrite mxdot_trmx -{1}AT -trmx_mul mxdot_trmx.
Qed.

Lemma posdefmx_convex n (A B : 'M[R]_n) (t : R) : posdefmx A -> posdefmx B ->
  0 <= t <= 1 -> posdefmx (A + t *: (B - A)).
Proof.
move=> [/symmetricmxP As Ap] [/symmetricmxP Bs Bp] /andP[t0 t1].
split.
  by apply/symmetricmxP; rewrite raddfD /= linearZ /= raddfB /= As Bs.
move=> x x0; have a0 := Ap x x0; have b0 := Bp x x0.
rewrite mulmxDr mxdotDr -scalemxAr mxdotZr mulmxBr mxdotBr.
by nra.
Qed.

(* The positive definite matrices form an open set. *)
Lemma posdefmx_open n (A : 'M[R]_n) : posdefmx A ->
  exists2 e : R, 0 < e & forall U, U \is symmetricmx -> frobenius U < e ->
    posdefmx (A + U).
Proof.
move=> Apd; have [As _] := Apd.
have [b b0 hb] := posdefmx_ge Apd.
exists b => // U Us fU.
split.
  move/symmetricmxP: As => As; move/symmetricmxP: Us => Us.
  by apply/symmetricmxP; rewrite raddfD /= As Us.
move=> x x0.
have xx : 0 < mxdot x x by rewrite mxdot_gt0.
have bU : `|mxdot x (x *m U)| <= mxdot x x * frobenius U.
  apply: le_trans (mxdot_le _ _) _.
  apply: le_trans (ler_wpM2l (frobenius_ge0 _) (frobenius_mulmx x U)) _.
  by rewrite mulrA -expr2 frobenius_sqr.
rewrite mulmxDr mxdotDr.
have := hb x; move: bU; rewrite ler_norml => /andP[bU _] h2.
have h1 : mxdot x x * frobenius U < mxdot x x * b by rewrite ltr_pM2l.
by nra.
Qed.

Lemma frobenius_vec_mx n (h : 'rV[R]_(n * n)) :
  frobenius (vec_mx h) <= n%:R * `|h|.
Proof.
have -> : frobenius (vec_mx h) = frobenius h.
  by rewrite -frobenius_mxvec vec_mxK.
apply: le_trans (frobenius_le_mx_norm h) _.
by rewrite mul1n natrM -expr2 sqrtr_sqr ger0_norm ?ler0n.
Qed.

Lemma rel_open_convex_pd_slice n (s : R) :
  rel_open_convex (sym_traceless n) (pd_slice n s).
Proof.
have n1 : 0 < (n%:R : R) + 1 by rewrite ltr_wpDl.
split.
- move=> z y t [zp ztr] [yp ytr] t01; rewrite /pd_slice /=.
  have -> : vec_mx (z + t *: (y - z)) = vec_mx z + t *: (vec_mx y - vec_mx z).
    by rewrite raddfD /= linearZ /= raddfB.
  split; first exact: posdefmx_convex.
  by rewrite mxtraceD mxtraceZ raddfB /= ztr ytr subrr mulr0 addr0.
- move=> z y [[/symmetricmxP zs _] ztr] [[/symmetricmxP ys _] ytr].
  apply/sym_tracelessP; rewrite raddfB /=.
  split; last by rewrite mxtraceD raddfN /= ztr ytr subrr.
  by apply/symmetricmxP; rewrite raddfB /= zs ys.
move=> z [zp ztr].
have [e e0 he] := posdefmx_open zp.
exists (e / (n%:R + 1)); first by rewrite divr_gt0.
move=> h /sym_tracelessP [hs htr] hn.
rewrite /pd_slice /= raddfD /=.
split; last by rewrite mxtraceD ztr htr addr0.
apply: he => //.
apply: le_lt_trans (frobenius_vec_mx h) _.
apply: le_lt_trans (ler_wpM2l (ler0n _ n) (ltW hn)) _.
rewrite mulrA ltr_pdivrMr // mulrC ltr_pM2l //.
by rewrite ltrDl.
Qed.

Lemma rel_open_convex_pd_slice2 n (m M : R) :
  rel_open_convex (sym_traceless n) (pd_slice2 n m M).
Proof.
have n1 : 0 < (n%:R : R) + 1 by rewrite ltr_wpDl.
split.
- move=> z y t [zp1 [zp2 ztr]] [yp1 [yp2 ytr]] t01; rewrite /pd_slice2 /=.
  have -> : vec_mx (z + t *: (y - z)) = vec_mx z + t *: (vec_mx y - vec_mx z).
    by rewrite raddfD /= linearZ /= raddfB.
  move: (vec_mx z) (vec_mx y) zp1 zp2 ztr yp1 yp2 ytr => A B.
  move=> zp1 zp2 ztr yp1 yp2 ytr.
  split.
    have := posdefmx_convex zp1 yp1 t01.
    by congr posdefmx; apply/matrixP => i j; rewrite !mxE; ring.
  split.
    have := posdefmx_convex zp2 yp2 t01.
    by congr posdefmx; apply/matrixP => i j; rewrite !mxE; ring.
  by rewrite mxtraceD mxtraceZ raddfB /= ztr ytr subrr mulr0 addr0.
- move=> z y [zp1 [_ ztr]] [yp1 [_ ytr]].
  have sym (x : 'rV[R]_(n * n)) : posdefmx (vec_mx x - m%:M) ->
      (vec_mx x)^T = vec_mx x.
    move=> [/symmetricmxP xs _]; move: xs; rewrite raddfB /= tr_scalar_mx.
    by move=> /addIr.
  apply/sym_tracelessP; rewrite raddfB /=.
  split; last by rewrite mxtraceD raddfN /= ztr ytr subrr.
  by apply/symmetricmxP; rewrite raddfB /= !sym.
move=> z [zp1 [zp2 ztr]].
have [e1 e10 he1] := posdefmx_open zp1.
have [e2 e20 he2] := posdefmx_open zp2.
exists (Num.min e1 e2 / (n%:R + 1)); first by rewrite divr_gt0 // lt_min e10.
move=> h /sym_tracelessP [hs htr] hn.
have fh : frobenius (vec_mx h) < Num.min e1 e2.
  apply: le_lt_trans (frobenius_vec_mx h) _.
  apply: le_lt_trans (ler_wpM2l (ler0n _ n) (ltW hn)) _.
  rewrite mulrA ltr_pdivrMr // mulrC ltr_pM2l ?lt_min ?e10 //.
  by rewrite ltrDl.
move: fh; rewrite lt_min => /andP[f1 f2].
rewrite /pd_slice2 /= raddfD /=; split.
  by rewrite addrAC; apply: he1.
split; last by rewrite mxtraceD ztr htr addr0.
rewrite opprD addrA; apply: he2; last by rewrite frobeniusN.
by move/symmetricmxP: hs => hs; apply/symmetricmxP; rewrite raddfN /= hs.
Qed.

End pd_slice.

Section logsum_barrier.
Context {R : realType} {N : nat}.

(* A function that is c - sum_i ln (1 + t l_i) along every line through D,
   with first and second derivatives at each point of D given by a linear
   and a bilinear form, is a k-self-concordant barrier on D. *)
Lemma logsum_sc_barrier (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N)
    (B : 'rV[R]_N -> R) k :
  rel_open_convex V D ->
  (forall z, D z -> exists (L : 'rV[R]_N -> R) (Q : 'rV[R]_N -> 'rV[R]_N -> R),
    [/\ forall (c : R) (u v : 'rV[R]_N), L (c *: u + v) = c * L u + L v,
        forall (c : R) (u v w : 'rV[R]_N),
          Q (c *: u + v) w = c * Q u w + Q v w,
        forall (c : R) (u v w : 'rV[R]_N),
          Q w (c *: u + v) = c * Q w u + Q w v &
        forall h, h \in V -> exists (c : R) (l : 'rV[R]_k),
          [/\ forall t, D (z + t *: h) <-> (forall i, 0 < 1 + t * l 0 i),
              forall t, D (z + t *: h) -> B (z + t *: h) = logsum l c t,
              L h = - \sum_i l 0 i & Q h h = \sum_i l 0 i ^+ 2]]) ->
  sc_barrier V D k%:R B.
Proof.
move=> DV Bline.
have der z h c (l : 'rV[R]_k) : h \in V -> D z ->
    (forall t, D (z + t *: h) <-> (forall i, 0 < 1 + t * l 0 i)) ->
    (forall t, D (z + t *: h) -> B (z + t *: h) = logsum l c t) ->
    [/\ is_derive z h B (logsum1 l 0), is_derive z h ('D_h B) (logsum2 l 0) &
        is_derive z h ('D_h ('D_h B)) (logsum3 l 0)].
  move=> hV Dz hD hB.
  have D0 : D (z + 0 *: h) by rewrite scale0r addr0.
  have hd t : D (z + t *: h) -> [/\ is_derive t 1 (logsum l c) (logsum1 l t),
      is_derive t 1 (logsum1 l) (logsum2 l t) &
      is_derive t 1 (logsum2 l) (logsum3 l t)].
    by move=> /hD pos; exact: logsum_derive.
  have := line_derive3 DV hV hB hd D0.
  by rewrite scale0r addr0.
have line z h : D z -> h \in V -> exists (c : R) (l : 'rV[R]_k),
    [/\ forall t, D (z + t *: h) <-> (forall i, 0 < 1 + t * l 0 i),
        forall t, D (z + t *: h) -> B (z + t *: h) = logsum l c t &
        [/\ is_derive z h B (logsum1 l 0),
            is_derive z h ('D_h B) (logsum2 l 0) &
            is_derive z h ('D_h ('D_h B)) (logsum3 l 0)]].
  move=> Dz hV.
  have [L [Q [_ _ _ /(_ h hV) [c [l [hD hB _ _]]]]]] := Bline z Dz.
  by exists c, l; split => //; exact: (der z h c l hV Dz hD hB).
split; last first.
  move=> z h Dz hV; have [c [l [_ _ [[_ ->] [_ ->] _]]]] := line z h Dz hV.
  exact: logsum_bp.
split.
- move=> z h Dz hV; have [c [l [_ _ [[d1 _] [d2 _] [d3 _]]]]] := line z h Dz hV.
  by split.
- move=> z Dz; have [L [Q [Llin Q1 Q2 hl]]] := Bline z Dz.
  exists (\row_j L (delta_mx 0 j)),
    (\matrix_(i, j) Q (delta_mx 0 i) (delta_mx 0 j)).
  move=> h hV; have [c [l [hD hB hL hQ]]] := hl h hV.
  have [[_ ->] [_ ->] _] := der z h c l hV Dz hD hB.
  rewrite -(lin_form_vec Llin) -(bilin_form_mx Q1 Q2) hL hQ /logsum1 /logsum2.
  by split; [congr (- _) |]; apply: eq_bigr => i _; rewrite mul0r addr0 divr1.
- move=> z h Dz hV; have [c [l [_ _ [_ [_ ->] _]]]] := line z h Dz hV.
  exact: logsum2_ge0.
- move=> z h Dz hV; have [c [l [_ _ [_ [_ ->] [_ ->]]]]] := line z h Dz hV.
  exact: logsum_sc.
move=> z h Dz hV seg nD; have [c [l [hD hB _]]] := line z h Dz hV.
have pos t : 0 <= t < 1 -> forall i, 0 < 1 + t * l 0 i.
  by move=> tt; apply/hD/seg.
have npos : ~ (forall i, 0 < 1 + l 0 i).
  move=> h1; apply: nD; rewrite -[h]scale1r; apply/hD => i.
  by rewrite mul1r.
apply: cvg_trans (logsum_blowup c pos npos).
apply: near_eq_cvg; near=> t.
have t1 : t < 1 by near: t; exact: nbhs_left_lt.
have tp : 0 < t by near: t; exact: nbhs_left_gt.
by rewrite hB //; apply: seg; rewrite (ltW tp) t1.
Unshelve. all: by end_near.
Qed.

End logsum_barrier.

Section logdet_barrier_theorems.
Context {R : realType}.
Implicit Types n : nat.

(* The trace forms that give the first two derivatives of -ln det are
   linear. *)
Lemma tr_form_linear n (P : 'M[R]_n) (c : R) (u v : 'rV[R]_(n * n)) :
  \tr (P *m vec_mx (c *: u + v)) =
  c * \tr (P *m vec_mx u) + \tr (P *m vec_mx v).
Proof. by rewrite linearP /= mulmxDr -scalemxAr mxtraceD mxtraceZ. Qed.

Lemma tr_form2_linearl n (P : 'M[R]_n) (c : R) (u v w : 'rV[R]_(n * n)) :
  \tr (P *m vec_mx (c *: u + v) *m P *m vec_mx w) =
  c * \tr (P *m vec_mx u *m P *m vec_mx w) +
  \tr (P *m vec_mx v *m P *m vec_mx w).
Proof.
by rewrite linearP /= mulmxDr -scalemxAr !mulmxDl -!scalemxAl mxtraceD mxtraceZ.
Qed.

Lemma tr_form2_linearr n (P : 'M[R]_n) (c : R) (u v w : 'rV[R]_(n * n)) :
  \tr (P *m vec_mx w *m P *m vec_mx (c *: u + v)) =
  c * \tr (P *m vec_mx w *m P *m vec_mx u) +
  \tr (P *m vec_mx w *m P *m vec_mx v).
Proof. by rewrite linearP /= mulmxDr -scalemxAr mxtraceD mxtraceZ. Qed.

(* Lemma 2.8 of Koehler and Sohn, one-sided: -ln det is an n-self-concordant
   barrier on every trace slice of the positive definite cone. *)
Theorem logdet_sc_barrier n (s : R) :
  sc_barrier (sym_traceless n) (pd_slice n s) n%:R (logdet_barrier n).
Proof.
apply: logsum_sc_barrier; first exact: rel_open_convex_pd_slice.
move=> z [zp ztr].
exists (fun h => - \tr (invmx (vec_mx z) *m vec_mx h)),
  (fun h1 h2 => \tr (invmx (vec_mx z) *m vec_mx h1 *m invmx (vec_mx z) *m
                     vec_mx h2)).
split.
- by move=> c u v; rewrite tr_form_linear opprD mulrN.
- by move=> c u v w; rewrite tr_form2_linearl.
- by move=> c u v w; rewrite tr_form2_linearr.
move=> h /sym_tracelessP [hs htr].
have [c [l [hpd hln h1 h2]]] := logdet_line zp hs.
have E t : vec_mx (z + t *: h) = vec_mx z + t *: vec_mx h.
  by rewrite raddfD /= linearZ.
exists c, l; split.
- move=> t; rewrite -hpd /pd_slice /= E mxtraceD mxtraceZ htr mulr0 addr0 ztr.
  by split => [[]|].
- by move=> t [pd _]; rewrite E in pd; rewrite /logdet_barrier E hln.
- by rewrite h1.
- by rewrite h2.
Qed.

(* Lemma 2.8 of Koehler and Sohn, two-sided. *)
Theorem logdet2_sc_barrier n (m M : R) :
  sc_barrier (sym_traceless n) (pd_slice2 n m M) (2 * n)%:R
    (logdet_barrier2 n m M).
Proof.
rewrite mul2n -addnn.
apply: logsum_sc_barrier; first exact: rel_open_convex_pd_slice2.
move=> z [zp1 [zp2 ztr]].
set A1 := vec_mx z - m%:M; set A2 := M%:M - vec_mx z.
exists (fun h => - \tr (invmx A1 *m vec_mx h) + \tr (invmx A2 *m vec_mx h)),
  (fun h1 h2 => \tr (invmx A1 *m vec_mx h1 *m invmx A1 *m vec_mx h2) +
                \tr (invmx A2 *m vec_mx h1 *m invmx A2 *m vec_mx h2)).
split.
- by move=> c u v; rewrite !tr_form_linear opprD addrACA mulrDr mulrN.
- move=> c u v w; rewrite (tr_form2_linearl (invmx A1)).
  by rewrite (tr_form2_linearl (invmx A2)) mulrDr addrACA.
- move=> c u v w; rewrite (tr_form2_linearr (invmx A1)).
  by rewrite (tr_form2_linearr (invmx A2)) mulrDr addrACA.
move=> h /sym_tracelessP [hs htr].
have hsN : - vec_mx h \is symmetricmx.
  by move/symmetricmxP: hs => hs; apply/symmetricmxP; rewrite raddfN /= hs.
(* the two factors along the line, and their spectra l1 and l2 *)
have [c1 [l1 [hpd1 hln1 h11 h21]]] := logdet_line zp1 hs.
have [c2 [l2 [hpd2 hln2 h12 h22]]] := logdet_line zp2 hsN.
have E1 t : vec_mx (z + t *: h) - m%:M = A1 + t *: vec_mx h.
  by rewrite raddfD /= linearZ /= addrAC.
have E2 t : M%:M - vec_mx (z + t *: h) = A2 + t *: - vec_mx h.
  by rewrite raddfD /= linearZ /= opprD addrA scalerN.
have splitL (F : R -> R) : \sum_(i < n + n) F (row_mx l1 l2 0 i) =
    \sum_i F (l1 0 i) + \sum_i F (l2 0 i).
  rewrite big_split_ord /=; congr (_ + _); apply: eq_bigr => i _.
    by rewrite row_mxEl.
  by rewrite row_mxEr.
exists (c1 + c2 + n%:R * ln ((1 - m) * (M - 1))), (row_mx l1 l2); split.
- move=> t; rewrite /pd_slice2 /= E1 E2 hpd1 hpd2.
  have -> : \tr (vec_mx (z + t *: h)) = n%:R.
    by rewrite raddfD /= linearZ /= mxtraceD mxtraceZ htr mulr0 addr0 ztr.
  split => [[p1 [p2 _]] i|p].
    by case: (split_ordP i) => j ->; rewrite ?row_mxEl ?row_mxEr.
  split; first by move=> i; have := p (lshift n i); rewrite row_mxEl.
  by split => // i; have := p (rshift n i); rewrite row_mxEr.
- move=> t [p1 [p2 _]]; rewrite E1 in p1; rewrite E2 in p2.
  rewrite /logdet_barrier2 E1 E2 hln1 // hln2 // /logsum.
  rewrite (splitL (fun x => ln (1 + t * x))).
  by move: (\sum_i _) (\sum_i _) (n%:R * _) => a b e; ring.
- move: h12; rewrite mulmxN raddfN /= => h12.
  by rewrite (splitL id) /= h11 -h12 opprB addrC.
move: h22; rewrite !mulmxN !mulNmx opprK => h22.
by rewrite (splitL (fun x => x ^+ 2)) /= h21 h22.
Qed.

Lemma posdefmx_scalar n (a : R) : 0 < a -> posdefmx (a%:M : 'M[R]_n).
Proof.
move=> a0; split; first by apply/symmetricmxP; rewrite tr_scalar_mx.
by move=> x x0; rewrite mul_mx_scalar mxdotZr mulr_gt0 // mxdot_gt0.
Qed.

Lemma pd_slice_one n : pd_slice n n%:R (mxvec (1%:M : 'M[R]_n)).
Proof.
rewrite /pd_slice /= mxvecK mxtrace1; split => //.
exact: posdefmx_scalar ltr01.
Qed.

Lemma logdet_barrier_one n : logdet_barrier n (mxvec (1%:M : 'M[R]_n)) = 0.
Proof. by rewrite /logdet_barrier mxvecK det1 ln1 oppr0. Qed.

(* det A <= (tr A / n)^n, in logarithmic form. *)
Lemma logdet_barrier_ge0 n (x : 'rV[R]_(n * n)) : pd_slice n n%:R x ->
  0 <= logdet_barrier n x.
Proof.
move=> [xp xtr]; rewrite /logdet_barrier oppr_ge0.
have [P Po [d AE dpos]] := posdefmx_spectral xp.
have PP : P *m P^T = 1%:M by apply/orthogonalmxP.
have dP : \det P ^+ 2 = 1.
  by rewrite expr2 -{1}det_tr -det_mulmx orthogonalmxT // det1.
have trd : \sum_i d 0 i = n%:R.
  by rewrite -xtr AE mxtrace_mulC mulmxA PP mul1mx mxtrace_diag.
have [p0 pE] := ln_prod dpos.
rewrite AE det_congruence dP mul1r pE.
apply: le_trans (_ : \sum_i (d 0 i - 1) <= 0).
  apply: ler_sum => i _; have := dpos i => di.
  have e : 1 + (d 0 i - 1) = d 0 i by rewrite addrCA subrr addr0.
  by have := @le_ln1Dx R (d 0 i - 1); rewrite e; apply; lra.
by rewrite sumrB trd sumr_const card_ord subrr.
Qed.

Lemma ln_sub_ge (a b : R) : 0 < a -> 0 < b -> 1 - b / a <= ln a - ln b.
Proof.
move=> a0 b0.
have ba : 0 < b / a by rewrite divr_gt0.
have e : 1 + (b / a - 1) = b / a by rewrite addrCA subrr addr0.
have := @le_ln1Dx R (b / a - 1); rewrite e ln_div ?posrE //.
by move=> h; have := h ltac:(lra); lra.
Qed.

Lemma pd_slice2_one n (m M : R) : m < 1 < M ->
  pd_slice2 n m M (mxvec (1%:M : 'M[R]_n)).
Proof.
move=> /andP[m1 M1]; rewrite /pd_slice2 /= mxvecK mxtrace1.
have -> : (1%:M : 'M[R]_n) - m%:M = (1 - m)%:M by rewrite raddfB.
have -> : (M%:M : 'M[R]_n) - 1%:M = (M - 1)%:M by rewrite raddfB.
by split; [|split] => //; apply: posdefmx_scalar; rewrite subr_gt0.
Qed.

Lemma logdet_barrier2_one n (m M : R) : m < 1 < M ->
  logdet_barrier2 n m M (mxvec (1%:M : 'M[R]_n)) = 0.
Proof.
move=> /andP[m1 M1]; rewrite /logdet_barrier2 mxvecK.
have -> : (1%:M : 'M[R]_n) - m%:M = (1 - m)%:M by rewrite raddfB.
have -> : (M%:M : 'M[R]_n) - 1%:M = (M - 1)%:M by rewrite raddfB.
rewrite !det_scalar !lnXn ?subr_gt0 // lnM ?posrE ?subr_gt0 //.
by rewrite mulr_natl mulrnDl -opprD addNr.
Qed.

Lemma logdet_barrier2_ge0 n (m M : R) (x : 'rV[R]_(n * n)) : m < 1 < M ->
  pd_slice2 n m M x -> 0 <= logdet_barrier2 n m M x.
Proof.
move=> /andP[m1 M1] [p1 [p2 xtr]].
have g1 : 0 < 1 - m by rewrite subr_gt0.
have g2 : 0 < M - 1 by rewrite subr_gt0.
have xs : vec_mx x \is symmetricmx.
  move: p1 => [/symmetricmxP xs _]; apply/symmetricmxP; move: xs.
  by rewrite raddfB /= tr_scalar_mx => /addIr.
(* the eigenvalues d_i of A = vec_mx x lie in (m, M) and sum to n *)
have [P Po [d AE]] := symmetric_spectral xs.
have PP : P *m P^T = 1%:M by apply/orthogonalmxP.
have PtP : P^T *m P = 1%:M by exact: orthogonalmxT.
have Pu : P \in unitmx by exact: orthogonalmx_unit.
have dP : \det P ^+ 2 = 1.
  by rewrite expr2 -{1}det_tr -det_mulmx PtP det1.
have trd : \sum_i d 0 i = n%:R.
  by rewrite -xtr AE mxtrace_mulC mulmxA PP mul1mx mxtrace_diag.
have shift (a b : R) : a%:M + b *: vec_mx x =
    P^T *m diag_mx (\row_i (a + b * d 0 i)) *m P.
  have -> : diag_mx (\row_i (a + b * d 0 i)) = a%:M + b *: diag_mx d.
    apply/matrixP => i j; rewrite !mxE.
    by case: (i == j) => /=; rewrite ?mulr1n ?mulr0n ?mulr0 ?addr0.
  rewrite mulmxDr mulmxDl -scalemxAr -scalemxAl -AE mul_mx_scalar.
  by rewrite -scalemxAl PtP scalemx1.
have E1 : vec_mx x - m%:M = P^T *m diag_mx (\row_i (- m + 1 * d 0 i)) *m P.
  by rewrite -shift scale1r addrC raddfN.
have E2 : M%:M - vec_mx x = P^T *m diag_mx (\row_i (M + -1 * d 0 i)) *m P.
  by rewrite -shift scaleN1r.
move: p1 p2; rewrite E1 E2 !posdefmx_congruence // => q1 q2.
have r1 i : 0 < d 0 i - m by have := q1 i; rewrite mxE mul1r addrC.
have r2 i : 0 < M - d 0 i by have := q2 i; rewrite mxE mulN1r.
rewrite /logdet_barrier2 E1 E2 !det_congruence dP !mul1r.
have [_ ->] := ln_prod q1.
have [_ ->] := ln_prod q2.
have S1 : \sum_i ln ((\row_i0 (- m + 1 * d 0 i0)) 0 i) = \sum_i ln (d 0 i - m).
  by apply: eq_bigr => i _; rewrite mxE mul1r addrC.
have S2 : \sum_i ln ((\row_i0 (M + -1 * d 0 i0)) 0 i) = \sum_i ln (M - d 0 i).
  by apply: eq_bigr => i _; rewrite mxE mulN1r.
have K : n%:R * ln ((1 - m) * (M - 1)) =
    \sum_(i < n) (ln (1 - m) + ln (M - 1)).
  by rewrite sumr_const card_ord mulr_natl lnM ?posrE.
rewrite S1 S2 K -!sumrN -!big_split /=.
(* termwise, by ln y <= y - 1 *)
have m1' : 1 - m != 0 by rewrite gt_eqF.
have M1' : M - 1 != 0 by rewrite gt_eqF.
have Z : \sum_i (1 - d 0 i) * ((1 - m)^-1 - (M - 1)^-1) = 0.
  by rewrite -mulr_suml sumrB sumr_const card_ord trd subrr mul0r.
rewrite -[X in X <= _]Z; apply: ler_sum => i _.
have h1 := ln_sub_ge g1 (r1 i).
have h2 := ln_sub_ge g2 (r2 i).
have e : (1 - d 0 i) * ((1 - m)^-1 - (M - 1)^-1) =
    (1 - (d 0 i - m) / (1 - m)) + (1 - (M - d 0 i) / (M - 1)) by field.
by rewrite e; lra.
Qed.

End logdet_barrier_theorems.
