From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix sesquilinear reals.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part.
From GaussianAnalysis.matrix Require Import psd_splitting.

(**md**************************************************************************)
(* # Trace and multiplicity                                                   *)
(*                                                                            *)
(* A positive semidefinite matrix K that fixes the constant vector and        *)
(* commutes with a set of permutation matrices: if every nonzero orthogonal   *)
(* projection that commutes with these permutation matrices and kills the     *)
(* constants has trace at least m, then the quadratic form of K on the        *)
(* vectors orthogonal to the constants is controlled by the trace of K^2.     *)
(* For the w-subsets of 'I_k, every such projection that commutes with the    *)
(* action of all the permutations of 'I_k has trace at least k/2 when k is    *)
(* even and k >= 6.                                                           *)
(*                                                                            *)
(* Main results:                                                              *)
(* - trace_multiplicity: let K in 'M[R]_N be positive semidefinite with       *)
(*   K 1 = 1, where 1 is the constant column vector, and let it commute with  *)
(*   perm_mx s for every s in a list S of permutations of 'I_N. Let m > 0,    *)
(*   and suppose that every Q with Q symmetric, Q Q = Q, Q != 0, Q 1 = 0,     *)
(*   commuting with every perm_mx s for s in S, has trace at least m. Then    *)
(*   <x, K x>^2 <= (tr K^2 - 1) / m |x|^4 for every column vector x           *)
(*   orthogonal to 1. The square avoids a square root. The two hypotheses on  *)
(*   Q, symmetric and then idempotent, say that Q is an orthogonal projection *)
(*   (orthoprojmx of psd_splitting.v), written out. The statement is about    *)
(*   permutation matrices: for an arbitrary family of matrices that commute   *)
(*   with K it is false, since a matrix that does not fix the constants on    *)
(*   both sides can leave no nonzero projection to satisfy the hypothesis.    *)
(* - ksubset_multiplicity: let k be even with 6 <= k, w any number, and Q a   *)
(*   matrix indexed by the w-subsets of 'I_k with Q symmetric, Q Q = Q,       *)
(*   Q != 0 and Q 1 = 0, that commutes with ksubset_mx w s for every          *)
(*   permutation s of 'I_k. Then tr Q >= k %/ 2.                              *)
(*                                                                            *)
(* The file also proves the general results that these proofs use:            *)
(* - sym_eigenproj: for M symmetric and c real, the orthogonal projection E   *)
(*   onto the eigenspace of M for c satisfies M E = c E, commutes with every  *)
(*   matrix that commutes with M, has c^2 tr E <= tr M^2, and is 0 exactly    *)
(*   when c is not an eigenvalue of M.                                        *)
(* - orthoproj_family_trace: c pairwise orthogonal nonzero vectors in the     *)
(*   range of an orthogonal projection Q give c <= tr Q.                      *)
(* - sign_refine: commuting involutions A_0, ..., A_(r-1) that commute with Q *)
(*   and with C have a common eigenvector, with eigenvalues 1 or -1, in the   *)
(*   range of Q and the (-1)-eigenspace of C, as soon as these two meet       *)
(*   outside 0.                                                               *)
(* - perm_map_uniq: a permutation maps a duplicate-free list onto any other   *)
(*   one of the same length; tperm_disjC: disjoint transpositions commute.    *)
(* - kact_exchange, kact_cycle_const: for k >= 3, a single exchange A - x + y *)
(*   of a w-subset A is its image under a 3-cycle, so a function of the       *)
(*   w-subsets that the 3-cycles leave invariant is constant; ksubset_mx_mul: *)
(*   ksubset_mx w s moves the rows of a matrix by kact s^-1.                  *)
(*                                                                            *)
(* These are Rocq formalizations of the credited argument, the step 'From     *)
(* trace to contraction' of the proof of the lemma on local averaging of      *)
(* 'Exponential PSD rank of positively shifted matching matrices' (family 126 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/local-averaging.tex, lines 191-246): the claim of lines    *)
(* 197-223 that every nonzero permutation-invariant subspace orthogonal to    *)
(* the constants has dimension at least k/2, and the bound (k/2) mu^2 <= tr   *)
(* K^2 - 1 of lines 225-234. The Lean development of the collection, which    *)
(* this file reads for routes and conventions:                                *)
(* Lean: simultaneous_sign_eigenvector (Involutions.lean, line 70)            *)
(* Lean: independent_eigenprofiles (Involutions.lean, line 109)               *)
(* Lean: eigenspace_dim_mul_sq_le_trace_square (SpectralMultiplicity.lean,    *)
(*   line 24)                                                                 *)
(* Lean: quadratic_form_le_of_multiplicity (SpectralMultiplicity.lean, line   *)
(*   55)                                                                      *)
(*                                                                            *)
(* Departures. The manuscript counts the dimension of an invariant subspace,  *)
(* and the Lean development the rank of an eigenspace. These statements bound *)
(* the trace of an orthogonal projection instead, so that the proofs need no  *)
(* rank: c pairwise orthogonal nonzero vectors in the range of Q give c <= tr *)
(* Q through orthoprojmxB. The proof of the multiplicity bound follows the    *)
(* route of the audit of the manuscript, not the full simultaneous            *)
(* diagonalization of the pair transpositions. Let tau_p be the transposition *)
(* of 2p and 2p + 1, and C = tau_0 tau_1. If C moves a vector of the range of *)
(* Q, a common sign eigenvector y of the tau_p inside the (-1)-eigenspace of  *)
(* C and its images under the swaps of two pairs give k/2 pairwise orthogonal *)
(* vectors in the range of Q, since two vectors with opposite signs for one   *)
(* tau_p are orthogonal. Otherwise C fixes the range of Q, and so do its      *)
(* conjugates, the products of two disjoint transpositions, and the 3-cycles: *)
(* the alternating group is replaced by single exchanges of the w-subsets,    *)
(* each a 3-cycle. Then every column of Q is constant, and Q = 0 since Q      *)
(* kills the constants. The bound k/2 is the manuscript's. The proof uses     *)
(* only k >= 5, not that k is even; the statement keeps the setting of the    *)
(* manuscript, k even and k >= 6.                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*          ksubset k w == the w-subsets of 'I_k, a finite type               *)
(*   ksubset_mx w s == the 0/1 matrix, indexed by the enumeration of the      *)
(*                     w-subsets, of the permutation that s : {perm 'I_k}     *)
(*                     induces on them: its entry (i, j) is 1 when the i-th   *)
(*                     w-subset is the image under s of the j-th              *)
(*         kact s A == the image s(A) of the w-subset A under s               *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section multiplicity.
Variable R : realType.

(* The w-subsets of 'I_k, and the 0/1 matrix of the permutation that s
   induces on them, indexed by their enumeration. *)
Definition ksubset (k w : nat) := {A : {set 'I_k} | #|A| == w}.

Definition ksubset_mx (k w : nat) (s : {perm 'I_k}) :
    'M[R]_#|{: ksubset k w}| :=
  \matrix_(i < #|{: ksubset k w}|, j < #|{: ksubset k w}|)
    (val (enum_val i : ksubset k w) == s @: val (enum_val j : ksubset k w))%:R.
End multiplicity.

Section trace_mult.
Variable R : realType.

(* The spectral projection of a symmetric M onto the eigenvalue c. *)
Lemma sym_eigenproj n (M : 'M[R]_n) (c : R) : M \is symmetricmx ->
  exists E : 'M[R]_n,
  [/\ orthoprojmx E, M *m E = c *: E,
      (forall X : 'M[R]_n, X *m M = M *m X -> X *m E = E *m X),
      c ^+ 2 * \tr E <= \tr (M *m M) &
      (E == 0) = [forall i, sym_spectral_diag M 0 i != c]].
Proof.
move=> Ms; set U := sym_spectralmx M; set d := sym_spectral_diag M.
have Uo : U \is orthogonalmx := sym_spectralmx_orthogonal M.
have UUT : U *m U^T = 1%:M := orthogonalmxP _ Uo.
have UTU : U^T *m U = 1%:M := orthogonalmxT Uo.
have ME : M = U^T *m diag_mx d *m U := sym_spectralE Ms.
pose f : 'rV[R]_n := map_mx (fun t => ((t == c)%:R : R)) d.
have conj (A B : 'M[R]_n) :
    U^T *m A *m U *m (U^T *m B *m U) = U^T *m (A *m B) *m U.
  by rewrite !mulmxA -(mulmxA (U^T *m A) U U^T) UUT mulmx1.
have unconj (A : 'M[R]_n) : U *m (U^T *m A *m U) *m U^T = A.
  by rewrite !mulmxA UUT mul1mx -mulmxA UUT mulmx1.
have trE (A : 'M[R]_n) : \tr (U^T *m A *m U) = \tr A.
  by rewrite mxtrace_mulC mulmxA UUT mul1mx.
have ff : diag_mx f *m diag_mx f = diag_mx f.
  apply/matrixP => i j; rewrite mul_diag_mx !mxE.
  have [->|_] := eqVneq i j; last by rewrite !mulr0n mulr0.
  by case: (d 0 j == c); rewrite ?mul1r ?mul0r.
have df : diag_mx d *m diag_mx f = c *: diag_mx f.
  apply/matrixP => i j; rewrite mul_diag_mx !mxE.
  have [->|_] := eqVneq i j; last by rewrite !mulr0n !mulr0.
  by have [->|] := eqVneq (d 0 j) c; rewrite ?mulr1 ?mulr0.
exists (U^T *m diag_mx f *m U); split.
- split; last by rewrite conj ff.
  by apply/symmetricmxP; rewrite !trmx_mul trmxK tr_diag_mx mulmxA.
- by rewrite {1}ME conj df -scalemxAr -scalemxAl.
- move=> X XM; pose Y := U *m X *m U^T.
  have XE : X = U^T *m Y *m U.
    by rewrite /Y !mulmxA UTU mul1mx -mulmxA UTU mulmx1.
  have YD : Y *m diag_mx d = diag_mx d *m Y.
    have h1 : X *m M = U^T *m (Y *m diag_mx d) *m U.
      by rewrite {1}XE {1}ME conj.
    have h2 : M *m X = U^T *m (diag_mx d *m Y) *m U.
      by rewrite {1}XE {1}ME conj.
    by rewrite -(unconj (Y *m _)) -(unconj (diag_mx d *m Y)) -h1 -h2 XM.
  have YF := diag_mx_commute_map (fun t => ((t == c)%:R : R)) YD.
  by rewrite {1 2}XE !conj YF.
- rewrite trE ME conj trE /mxtrace mulr_sumr; apply: ler_sum => i _.
  rewrite mul_diag_mx !mxE eqxx !mulr1n.
  have [->|_] := eqVneq (d 0 i) c; first by rewrite mulr1 expr2.
  by rewrite mulr0 -expr2 sqr_ge0.
apply/idP/forallP => [/eqP E0 i|h].
  have : diag_mx f = 0 by rewrite -(unconj (diag_mx f)) E0 mulmx0 mul0mx.
  move/matrixP/(_ i i); rewrite !mxE eqxx mulr1n => /eqP.
  by rewrite pnatr_eq0 eqb0.
have -> : diag_mx f = 0.
  apply/matrixP => a b; rewrite !mxE.
  by have [->|] := eqVneq a b; rewrite ?mulr0n // (negbTE (h b)) mul0rn.
by rewrite mulmx0 mul0mx.
Qed.

Lemma trace_multiplicity (N m : nat) (K : 'M[R]_N) (S : seq {perm 'I_N}) :
  psdmx K -> K *m (const_mx 1 : 'cV[R]_N) = const_mx 1 -> (0 < m)%N ->
  (forall s, s \in S -> perm_mx s *m K = K *m perm_mx s) ->
  (forall Q : 'M[R]_N, Q \is symmetricmx -> Q *m Q = Q -> Q != 0 ->
     Q *m (const_mx 1 : 'cV[R]_N) = 0 ->
     (forall s, s \in S -> perm_mx s *m Q = Q *m perm_mx s) -> m%:R <= \tr Q) ->
  forall x : 'cV[R]_N, mxdot x (const_mx 1) = 0 ->
  mxdot x (K *m x) ^+ 2 <= (\tr (K *m K) - 1) / m%:R * mxdot x x ^+ 2.
Proof.
case: N K S => [|N] K S Kp K1 m0 KS hQ x x1.
  by rewrite /mxdot !big_ord0 expr0n /= mulr0.
set one := (const_mx 1 : 'cV[R]_N.+1).
have [Ksym Kpos] := Kp.
have KT : K^T = K by apply/symmetricmxP.
have oneTone : one^T *m one = N.+1%:R%:M.
  apply/matrixP => i j; rewrite !ord1 !mxE eqxx mulr1n.
  under eq_bigr do rewrite !mxE mulr1.
  by rewrite sumr_const card_ord.
pose J : 'M[R]_N.+1 := N.+1%:R^-1 *: (one *m one^T).
have Jone : J *m one = one.
  rewrite /J -scalemxAl -mulmxA oneTone mul_mx_scalar scalerA.
  by rewrite mulVf ?pnatr_eq0 // scale1r.
have oneK : one^T *m K = one^T by rewrite -[K]KT -trmx_mul K1.
have KJ : K *m J = J by rewrite /J -scalemxAr mulmxA K1.
have JK : J *m K = J by rewrite /J -scalemxAl -mulmxA oneK.
have JJ : J *m J = J by rewrite {2}/J -scalemxAr mulmxA Jone.
have trJ : \tr J = 1.
  rewrite /J mxtraceZ mxtrace_mulC oneTone mxtrace_scalar mulr1n.
  by rewrite mulVf ?pnatr_eq0.
have oneTx : one^T *m x = 0.
  move: x1; rewrite /mxdot; under eq_bigr do rewrite big_ord1 mxE mulr1.
  move=> x1; apply/matrixP => i j; rewrite !ord1 !mxE.
  by rewrite -[RHS]x1; apply: eq_bigr => k _; rewrite !mxE mul1r.
have Jx : J *m x = 0 by rewrite /J -scalemxAl -mulmxA oneTx mulmx0 scaler0.
pose K' := K - J.
have Jsym : J \is symmetricmx.
  by apply/symmetricmxP; rewrite /J linearZ /= trmx_mul trmxK.
have K's : K' \is symmetricmx.
  apply/symmetricmxP; rewrite /K' linearB /=.
  by rewrite (symmetricmxP _ Ksym) (symmetricmxP _ Jsym).
have K'one : K' *m one = 0 by rewrite /K' mulmxBl K1 Jone subrr.
have KK : K *m K = K' *m K' + J.
  by rewrite /K' mulmxBl !mulmxBr KJ JK JJ subrr subr0 addrNK.
have Kx : K *m x = K' *m x by rewrite /K' mulmxBl Jx subr0.
have trKK : \tr (K *m K) - 1 = \tr (K' *m K').
  by rewrite KK mxtraceD trJ addrK.
rewrite Kx trKK.
have a0 : 0 <= mxdot x (K' *m x) by rewrite -Kx Kpos.
set d := sym_spectral_diag K'.
have [i0 _ hmax] := arg_maxP (fun i => d 0 i) (isT : xpredT (ord0 : 'I_N.+1)).
set mu := d 0 i0.
have formle : forall y : 'cV[R]_N.+1, mxdot y (K' *m y) <= mu * mxdot y y.
  exact: (spectral_form_le _ (sym_spectralmx_orthogonal K')
    (sym_spectralE K's)).2 (fun i => hmax i isT).
have b0 : 0 <= mxdot x x := mxdot_ge0 x.
have aleb := formle x.
have [E [Eproj EK' Ecomm Etr Ezero]] := sym_eigenproj mu K's.
have trK'0 : 0 <= \tr (K' *m K').
  by rewrite -{2}(symmetricmxP _ K's) -mxdot_trace mxdot_ge0.
have mule : mu ^+ 2 * m%:R <= \tr (K' *m K').
  have [mu0|mu0] := eqVneq mu 0; first by rewrite mu0 expr0n mul0r.
  have [Esym EE] := Eproj.
  have EK'' : E *m K' = mu *: E.
    apply: trmx_inj; rewrite trmx_mul linearZ /=.
    by rewrite (symmetricmxP _ K's) (symmetricmxP _ Esym) EK'.
  have Eone : E *m one = 0.
    have : mu *: (E *m one) = 0.
      by rewrite scalemxAl -EK'' -mulmxA K'one mulmx0.
    by move/eqP; rewrite scaler_eq0 (negbTE mu0) => /eqP.
  have En0 : E != 0.
    by rewrite Ezero negb_forall; apply/existsP; exists i0; rewrite negbK.
  have Pone (s : {perm 'I_N.+1}) : perm_mx s *m one = one.
    by rewrite -row_permE; apply/matrixP => i j; rewrite !mxE.
  have oneP (s : {perm 'I_N.+1}) : one^T *m perm_mx s = one^T.
    by apply: trmx_inj; rewrite trmx_mul trmxK tr_perm_mx Pone.
  have trE := hQ E Esym EE En0 Eone.
  apply: le_trans Etr; apply: ler_wpM2l; first exact: sqr_ge0.
  apply: trE => s sS; apply: Ecomm.
  rewrite /K' mulmxBl mulmxBr (KS s sS) /J -scalemxAl -scalemxAr mulmxA Pone.
  by rewrite -mulmxA oneP.
have mu2 : mu ^+ 2 <= \tr (K' *m K') / m%:R by rewrite ler_pdivlMr ?ltr0n.
apply: (le_trans (_ : _ <= (mu * mxdot x x) ^+ 2)).
  by rewrite !expr2 ler_pM.
by rewrite exprMn ler_wpM2r ?sqr_ge0.
Qed.

End trace_mult.

Section ksubset_action.
Variables (k w : nat).
Local Notation X := (ksubset k w).

Lemma kact_subproof (s : {perm 'I_k}) (A : X) : #|s @: val A| == w.
Proof. by rewrite card_imset ?(valP A) //; exact: perm_inj. Qed.

(* The w-subset s(A). *)
Definition kact (s : {perm 'I_k}) (A : X) : X :=
  Sub (s @: val A) (kact_subproof s A).

Lemma val_kact s A : val (kact s A) = s @: val A.
Proof. by []. Qed.

Lemma kactM s t A : kact s (kact t A) = kact (t * s) A.
Proof.
apply: val_inj; rewrite !val_kact -imset_comp.
by apply: eq_imset => x; rewrite permM.
Qed.

Lemma kact1 A : kact 1 A = A.
Proof.
by apply: val_inj; rewrite val_kact (eq_imset _ (@perm1 _)) imset_id.
Qed.

Lemma kactK s : cancel (kact s) (kact s^-1).
Proof. by move=> A; rewrite kactM mulgV kact1. Qed.

Lemma kactVK s : cancel (kact s^-1) (kact s).
Proof. by move=> A; rewrite kactM mulVg kact1. Qed.

End ksubset_action.

Section ksubset_exchange.
Variables (k w : nat).
Local Notation X := (ksubset k w).
Local Open Scope group_scope.

(* A single exchange B - x + y is the image of B under a 3-cycle. *)
Lemma kact_exchange (B : X) (x y : 'I_k) : (3 <= k)%N ->
  x \in val B -> y \notin val B ->
  exists a b c : 'I_k, [/\ a != b, b != c, a != c &
    val (kact (tperm a b * tperm b c) B) = y |: (val B :\ x)].
Proof.
move=> k3 xB yB.
have xy : x != y by apply: contraNneq yB => <-.
have img (c : {perm 'I_k}) : c @: val B \subset y |: (val B :\ x) ->
    val (kact c B) = y |: (val B :\ x).
  move=> sub; rewrite val_kact; apply/eqP; rewrite eqEcard sub /=.
  rewrite (card_imset _ (@perm_inj _ c)).
  by rewrite cardsU1 in_setD1 (negbTE yB) andbF (cardsD1 x (sval B)) xB.
have [/existsP [z /andP [zB zy]]|none] :=
    boolP [exists z, (z \notin val B) && (z != y)].
  have zx : z != x by apply: contraNneq zB => ->.
  exists z, y, x; split => //; first by rewrite eq_sym.
  apply: img; apply/subsetP => _ /imsetP [u uB ->]; rewrite permM.
  have uz : u != z by apply: contraNneq zB => <-.
  have uy : u != y by apply: contraNneq yB => <-.
  have zu : z != u by rewrite eq_sym.
  have yu : y != u by rewrite eq_sym.
  rewrite (tpermD zu yu) !inE.
  have [->|ux] := eqVneq u x; first by rewrite tpermR eqxx.
  have xu : x != u by rewrite eq_sym.
  by rewrite (tpermD yu xu) ux uB orbT.
have : ~~ ([set: 'I_k] \subset [set x; y]).
  apply: contraL k3 => /subset_leq_card; rewrite cardsT card_ord cards2 => h.
  by rewrite -leqNgt (leq_trans h) // ltnS leq_b1.
case/subsetPn => z _; rewrite !inE negb_or => /andP [zx zy].
have zB : z \in val B.
  by move/existsPn: none => /(_ z); rewrite zy andbT negbK.
exists x, y, z; split => //; rewrite 1?eq_sym //.
apply: img; apply/subsetP => _ /imsetP [u uB ->]; rewrite permM.
have uy : u != y by apply: contraNneq yB => <-.
have [->|ux] := eqVneq u x; first by rewrite tpermL tpermL !inE zx zB orbT.
have xu : x != u by rewrite eq_sym.
have yu : y != u by rewrite eq_sym.
rewrite (tpermD xu yu) !inE.
have [->|uz] := eqVneq u z; first by rewrite tpermR eqxx.
have zu : z != u by rewrite eq_sym.
by rewrite (tpermD yu zu) ux uB orbT.
Qed.

(* A function of the w-subsets that the 3-cycles leave invariant is
   constant. *)
Lemma kact_cycle_const (U : Type) (f : X -> U) : (3 <= k)%N ->
  (forall (a b c : 'I_k) B, a != b -> b != c -> a != c ->
     f (kact (tperm a b * tperm b c) B) = f B) ->
  forall B B', f B = f B'.
Proof.
move=> k3 hf B B'.
move: {2}#|val B :\: val B'| (leqnn #|val B :\: val B'|) => n.
elim: n B => [|n IH] B hn.
  have sub : val B \subset val B'.
    by rewrite -setD_eq0 -cards_eq0 -leqn0.
  congr f; apply: val_inj; apply/eqP; rewrite eqEcard sub /=.
  by rewrite (eqP (valP B)) (eqP (valP B')).
have [e|[x hx]] := set_0Vmem (val B :\: val B').
  by apply: IH; rewrite e cards0.
have cardD : #|val B' :\: val B| = #|val B :\: val B'|.
  by rewrite !cardsD (eqP (valP B)) (eqP (valP B')) setIC.
have [e|[y hy]] := set_0Vmem (val B' :\: val B).
  move: cardD; rewrite e cards0 => /esym/eqP; rewrite cards_eq0 => /eqP e'.
  by rewrite e' inE in hx.
move: hx hy; rewrite !inE => /andP [xB' xB] /andP [yB yB'].
have [a [b [c [ab bc ac hB1]]]] := kact_exchange k3 xB yB.
rewrite -(hf a b c B ab bc ac); apply: IH.
have -> : val (kact (tperm a b * tperm b c) B) :\: val B' =
    (val B :\: val B') :\ x.
  apply/setP => u; rewrite hB1 !inE.
  have [->|uy] := eqVneq u y; first by rewrite yB' (negbTE yB) andbF.
  by rewrite orFb; case: (u != x); case: (u \in val B'); case: (u \in val B).
by move: hn; rewrite (cardsD1 x (val B :\: val B')) !inE xB' xB.
Qed.

End ksubset_exchange.

Section ksubset_matrix.
Variables (R : realType) (k w : nat).
Local Notation X := (ksubset k w).
Local Notation N := #|{: X}|.
Local Notation T := (@ksubset_mx R k w).

Lemma ksubset_mxE s i j :
  T s i j = (enum_val i == kact s (enum_val j))%:R.
Proof. by rewrite mxE. Qed.

(* The permutation matrix acts on the rows of a matrix by moving the
   subsets. *)
Lemma ksubset_mx_mul n s (M : 'M[R]_(N, n)) i l :
  (T s *m M) i l = M (enum_rank (kact s^-1 (enum_val i))) l.
Proof.
rewrite mxE (bigD1 (enum_rank (kact s^-1 (enum_val i)))) //=.
rewrite ksubset_mxE enum_rankK kactVK eqxx mul1r big1 ?addr0 // => j hj.
rewrite ksubset_mxE; case: eqP => [h|_]; last by rewrite mul0r.
by move: hj; rewrite h kactK enum_valK eqxx.
Qed.

Lemma ksubset_mxM s t : T s *m T t = T (t * s).
Proof.
apply/matrixP => i l; rewrite mxE (bigD1 (enum_rank (kact t (enum_val l)))) //=.
rewrite big1 ?addr0.
  move=> j hj; rewrite [T t j l]ksubset_mxE.
  case: eqP => [h|_]; last by rewrite mulr0.
  by move: hj; rewrite -h enum_valK eqxx.
by rewrite !ksubset_mxE enum_rankK eqxx mulr1 kactM.
Qed.

Lemma ksubset_mx1 : T 1 = 1%:M.
Proof.
by apply/matrixP => i j; rewrite ksubset_mxE kact1 mxE (inj_eq enum_val_inj).
Qed.

Lemma tr_ksubset_mx s : (T s)^T = T s^-1.
Proof.
apply/matrixP => i j; rewrite mxE !ksubset_mxE.
by rewrite -(can_eq (kactK s) (enum_val i)) kactVK eq_sym.
Qed.

Lemma ksubset_mx_orthogonal s : T s \is orthogonalmx.
Proof.
by apply/orthogonalmxP; rewrite tr_ksubset_mx ksubset_mxM mulVg ksubset_mx1.
Qed.

End ksubset_matrix.

Section orthogonal_family.
Variables (R : realType) (N : nat).
Implicit Types (x y : 'cV[R]_N) (Q P : 'M[R]_N).

Local Lemma mxdot_col_scalar x y : x^T *m y = (mxdot x y)%:M.
Proof.
apply/matrixP => i j; rewrite !ord1 !mxE eqxx mulr1n /mxdot.
by apply: eq_bigr => l _; rewrite big_ord1 mxE.
Qed.

(* The trace of an orthogonal projection is nonnegative. *)
Lemma mxtrace_orthoproj_ge0 Q : Q \is symmetricmx -> Q *m Q = Q -> 0 <= \tr Q.
Proof.
by move=> Qs QQ; rewrite -QQ -{2}(symmetricmxP _ Qs) -mxdot_trace mxdot_ge0.
Qed.

(* c pairwise orthogonal nonzero vectors in the range of an orthogonal
   projection Q give c <= tr Q. *)
Lemma orthoproj_family_trace c Q (v : 'I_c -> 'cV[R]_N) :
  Q \is symmetricmx -> Q *m Q = Q ->
  (forall r, v r != 0) -> (forall r, Q *m v r = v r) ->
  (forall r r', r != r' -> mxdot (v r) (v r') = 0) ->
  c%:R <= \tr Q.
Proof.
move=> Qs QQ v0 Qv vorth.
have vv r : mxdot (v r) (v r) != 0 by rewrite mxdot_eq0.
pose a r := (mxdot (v r) (v r))^-1.
pose P := \sum_r a r *: (v r *m (v r)^T).
have vTv r r' :
    (v r)^T *m v r' = (if r == r' then mxdot (v r) (v r) else 0)%:M.
  rewrite mxdot_col_scalar; have [->|rr'] := eqVneq r r'; first by [].
  by rewrite vorth.
have trP : \tr P = c%:R.
  rewrite /P raddf_sum (eq_bigr (fun=> 1)) ?sumr_const ?card_ord // => r _.
  change (\tr (a r *: (v r *m (v r)^T)) = 1).
  by rewrite mxtraceZ mxtrace_mulC vTv eqxx mxtrace_scalar mulr1n mulVf.
have vQ r : (v r)^T *m Q = (v r)^T.
  by rewrite -{1}(symmetricmxP _ Qs) -trmx_mul Qv.
have QP : Q *m P = P.
  by rewrite /P mulmx_sumr; apply: eq_bigr => r _; rewrite -scalemxAr mulmxA Qv.
have PQ : P *m Q = P.
  rewrite /P mulmx_suml; apply: eq_bigr => r _.
  by rewrite -scalemxAl -mulmxA vQ.
have Ps : P \is symmetricmx.
  apply/symmetricmxP; rewrite /P raddf_sum; apply: eq_bigr => r _.
  change ((a r *: (v r *m (v r)^T))^T = a r *: (v r *m (v r)^T)).
  by rewrite linearZ /= trmx_mul trmxK.
have vP r : (v r)^T *m P = (v r)^T.
  rewrite /P mulmx_sumr (bigD1 r) //= big1 ?addr0.
    move=> r' hr'; rewrite -scalemxAr mulmxA vTv eq_sym (negbTE hr').
    by rewrite mul_scalar_mx scale0r scaler0.
  by rewrite -scalemxAr mulmxA vTv eqxx mul_scalar_mx scalerA mulVf ?scale1r.
have PP : P *m P = P.
  rewrite {1}/P mulmx_suml; apply: eq_bigr => r _.
  by rewrite -scalemxAl -mulmxA vP.
have [_ QPP] := orthoprojmxB (conj Qs QQ) (conj Ps PP) PQ QP.
have := mxtrace_orthoproj_ge0
  (orthoprojmxB (conj Qs QQ) (conj Ps PP) PQ QP).1 QPP.
by rewrite raddfB /= trP subr_ge0.
Qed.

End orthogonal_family.

Section sign_refinement.
Variables (R : realType) (N : nat).

(* Refinement inside the (-1)-eigenspace of C: commuting involutions A p,
   p < r, that commute with Q and C, have a common sign eigenvector there. *)
Lemma sign_refine (r : nat) (A : nat -> 'M[R]_N) (Q C : 'M[R]_N)
    (x : 'cV[R]_N) :
  (forall p, (p < r)%N -> A p *m A p = 1%:M) ->
  (forall p q, (p < r)%N -> (q < r)%N -> A p *m A q = A q *m A p) ->
  (forall p, (p < r)%N -> A p *m Q = Q *m A p) ->
  (forall p, (p < r)%N -> A p *m C = C *m A p) ->
  x != 0 -> Q *m x = x -> C *m x = - x ->
  exists y : 'cV[R]_N, [/\ y != 0, Q *m y = y, C *m y = - y &
    forall p, (p < r)%N -> A p *m y = y \/ A p *m y = - y].
Proof.
elim: r => [|r IH] hAA hAc hAQ hAC x0 Qx Cx.
  by exists x; split.
have lt p : (p < r)%N -> (p < r.+1)%N by move=> hp; rewrite ltnS ltnW.
have [y [y0 Qy Cy hy]] := IH (fun p hp => hAA p (lt p hp))
  (fun p q hp hq => hAc p q (lt p hp) (lt q hq)) (fun p hp => hAQ p (lt p hp))
  (fun p hp => hAC p (lt p hp)) x0 Qx Cx.
have Arr : A r *m A r = 1%:M := hAA r (ltnSn r).
set z := y + A r *m y.
have [z0|zn0] := eqVneq z 0.
  have Ary : A r *m y = - y by apply/eqP; rewrite -addr_eq0 addrC -/z z0.
  exists y; split => // p; rewrite ltnS leq_eqVlt => /orP[/eqP->|hp].
    by right.
  exact: hy.
exists z; split => //.
- by rewrite /z mulmxDr Qy mulmxA -(hAQ r (ltnSn r)) -mulmxA Qy.
- by rewrite /z mulmxDr Cy mulmxA -(hAC r (ltnSn r)) -mulmxA Cy mulmxN opprD.
move=> p; rewrite ltnS leq_eqVlt => /orP[/eqP->|hp].
  by left; rewrite /z mulmxDr mulmxA Arr mul1mx addrC.
have Apr : A p *m A r = A r *m A p := hAc p r (lt p hp) (ltnSn r).
case: (hy p hp) => Apy; [left|right];
  rewrite /z mulmxDr mulmxA Apr -mulmxA Apy //.
by rewrite mulmxN opprD.
Qed.

End sign_refinement.

Section perm_facts.

(* A permutation maps a duplicate-free list onto any other of the same
   length. *)
Lemma perm_map_uniq (T : finType) (s t : seq T) :
  uniq s -> uniq t -> size s = size t -> exists g : {perm T}, map g s = t.
Proof.
elim: s t => [|x s IH] [|y t] //=; first by exists 1%g.
move=> /andP[xs us] /andP[yt ut] [sz].
have [g gs] := IH t us ut sz.
exists (g * tperm (g x) y)%g; rewrite permM tpermL; congr (_ :: _).
rewrite -gs; apply/eq_in_map => z zs; rewrite permM tpermD //.
  by rewrite (inj_eq perm_inj); apply: contraNneq xs => ->.
by apply: contraNneq yt => ->; rewrite -gs map_f.
Qed.

(* Disjoint transpositions commute. *)
Lemma tperm_disjC (T : finType) (a b c d : T) :
  a != c -> a != d -> b != c -> b != d ->
  (tperm a b * tperm c d = tperm c d * tperm a b)%g.
Proof.
move=> ac ad bc bd; apply/permP => x; rewrite !permM.
have ca : c != a by rewrite eq_sym.
have da : d != a by rewrite eq_sym.
have cb : c != b by rewrite eq_sym.
have db : d != b by rewrite eq_sym.
case: (tpermP a b x) => [->|->|xa xb].
- by rewrite (tpermD ca da) tpermL (tpermD cb db).
- by rewrite (tpermD cb db) tpermR (tpermD ca da).
have xa' : x != a by apply/eqP.
have xb' : x != b by apply/eqP.
case: (tpermP c d x) => [_|_|_ _].
- by rewrite (tpermD ad bd).
- by rewrite (tpermD ac bc).
by rewrite tpermD // eq_sym.
Qed.

End perm_facts.

Section pairs.
Variable k' : nat.
Local Notation k := k'.+1.
Local Open Scope group_scope.

(* The pair transposition pair_tperm p = (2p 2p+1), the swap of the pairs p
   and q, pair_swap p q = (2p 2q)(2p+1 2q+1), and its action on the indices
   of the pairs. *)
Local Definition pair_tperm (p : nat) : {perm 'I_k} :=
  tperm (inord (2 * p)) (inord (2 * p).+1).
Local Definition pair_swap (p q : nat) : {perm 'I_k} :=
  tperm (inord (2 * p)) (inord (2 * q)) *
  tperm (inord (2 * p).+1) (inord (2 * q).+1).
Local Definition swap_index (p q r : nat) : nat :=
  if r == p then q else if r == q then p else r.

Local Lemma inord_eq (a b : nat) : (a < k)%N -> (b < k)%N ->
  (inord a == inord b :> 'I_k) = (a == b).
Proof. by move=> ha hb; rewrite -val_eqE /= !inordK. Qed.

Local Lemma pair_lt (p : nat) : (p < k %/ 2)%N -> ((2 * p).+1 < k)%N.
Proof.
move=> h; have h2 : (p.+1 * 2 <= k)%N by rewrite -leq_divRL.
apply: leq_trans h2.
by rewrite [(p.+1 * 2)%N]mulnC mulnS addnC addn2.
Qed.

Local Lemma pair_lt0 (p : nat) : (p < k %/ 2)%N -> (2 * p < k)%N.
Proof. by move=> /pair_lt /ltnW. Qed.

Local Lemma even_neq_odd (a b : nat) : (2 * a)%N != (2 * b).+1.
Proof. by apply/eqP => /(congr1 odd); rewrite /= !oddM. Qed.

Local Lemma double_eq (a b : nat) : ((2 * a)%N == (2 * b)%N) = (a == b).
Proof. by rewrite eqn_pmul2l. Qed.

Local Lemma pair_tpermC (p q : nat) : (p < k %/ 2)%N -> (q < k %/ 2)%N ->
  pair_tperm p * pair_tperm q = pair_tperm q * pair_tperm p.
Proof.
move=> hp hq; have [->|pq] := eqVneq p q; first by [].
have [hp0 hp1] := (pair_lt0 hp, pair_lt hp).
have [hq0 hq1] := (pair_lt0 hq, pair_lt hq).
apply: tperm_disjC.
- by rewrite inord_eq // double_eq.
- by rewrite inord_eq // even_neq_odd.
- by rewrite inord_eq // eq_sym even_neq_odd.
- by rewrite inord_eq // eqSS double_eq.
Qed.

Local Lemma pair_tpermK (p : nat) : pair_tperm p * pair_tperm p = 1.
Proof. by rewrite /pair_tperm tperm2. Qed.

Local Lemma pair_swap_disj (p q : nat) : (p < k %/ 2)%N -> (q < k %/ 2)%N ->
  tperm (inord (2 * p)) (inord (2 * q)) *
    tperm (inord (2 * p).+1) (inord (2 * q).+1)
  = tperm (inord (2 * p).+1) (inord (2 * q).+1) *
    tperm (inord (2 * p)) (inord (2 * q))
    :> {perm 'I_k}.
Proof.
move=> hp hq; have [hp0 hp1] := (pair_lt0 hp, pair_lt hp).
have [hq0 hq1] := (pair_lt0 hq, pair_lt hq).
apply: tperm_disjC; rewrite inord_eq // ?even_neq_odd //.
Qed.

Local Lemma pair_swapK (p q : nat) : (p < k %/ 2)%N -> (q < k %/ 2)%N ->
  pair_swap p q * pair_swap p q = 1.
Proof.
move=> hp hq; rewrite /pair_swap.
set t1 := tperm _ _; set t2 := tperm _ _.
have h : t1 * t2 = t2 * t1 by exact: pair_swap_disj.
by rewrite mulgA -[t1 * t2 * t1]mulgA -h mulgA tperm2 mul1g tperm2.
Qed.

(* The values of pair_swap p q on the two points of the pair r. *)
Local Lemma pair_swap_even (p q r : nat) :
  (p < k %/ 2)%N -> (q < k %/ 2)%N -> (r < k %/ 2)%N ->
  pair_swap p q (inord (2 * r)) = inord (2 * swap_index p q r).
Proof.
move=> hp hq hr.
have [hp0 hp1] := (pair_lt0 hp, pair_lt hp).
have [hq0 hq1] := (pair_lt0 hq, pair_lt hq).
have [hr0 hr1] := (pair_lt0 hr, pair_lt hr).
rewrite /pair_swap permM /swap_index.
have [->|rp] := eqVneq r p.
  by rewrite tpermL tpermD // inord_eq // eq_sym ?even_neq_odd //
    eqSS double_eq.
have [->|rq] := eqVneq r q.
  by rewrite tpermR tpermD // inord_eq // eq_sym ?even_neq_odd // double_eq.
rewrite (@tpermD _ _ _ (inord (2 * r))) ?inord_eq // ?double_eq 1?eq_sym //.
by rewrite tpermD // inord_eq // eq_sym even_neq_odd.
Qed.

Local Lemma pair_swap_odd (p q r : nat) :
  (p < k %/ 2)%N -> (q < k %/ 2)%N -> (r < k %/ 2)%N ->
  pair_swap p q (inord (2 * r).+1) = inord (2 * swap_index p q r).+1.
Proof.
move=> hp hq hr.
have [hp0 hp1] := (pair_lt0 hp, pair_lt hp).
have [hq0 hq1] := (pair_lt0 hq, pair_lt hq).
have [hr0 hr1] := (pair_lt0 hr, pair_lt hr).
rewrite /pair_swap permM /swap_index.
rewrite (@tpermD _ _ _ (inord (2 * r).+1)) ?inord_eq // ?even_neq_odd //.
have [->|rp] := eqVneq r p; first by rewrite tpermL.
have [->|rq] := eqVneq r q; first by rewrite tpermR.
by rewrite tpermD // inord_eq // eqSS double_eq 1?eq_sym.
Qed.

Local Lemma pair_swap_tperm (p q r : nat) :
  (p < k %/ 2)%N -> (q < k %/ 2)%N -> (r < k %/ 2)%N ->
  pair_swap p q * pair_tperm r = pair_tperm (swap_index p q r) * pair_swap p q.
Proof.
move=> hp hq hr.
have hs : (swap_index p q r < k %/ 2)%N.
  by rewrite /swap_index; case: eqP => _ //; case: eqP.
have h : (pair_tperm r) ^ (pair_swap p q) = pair_tperm (swap_index p q r).
  by rewrite /pair_tperm tpermJ pair_swap_even // pair_swap_odd.
have siginv : (pair_swap p q)^-1 = pair_swap p q.
  by apply/eqP; rewrite eq_invg_mul pair_swapK.
rewrite -h /conjg siginv.
rewrite -[pair_swap p q * (pair_tperm r * pair_swap p q) * pair_swap p q]mulgA.
rewrite -[pair_tperm r * pair_swap p q * pair_swap p q]mulgA.
by rewrite pair_swapK // mulg1.
Qed.

End pairs.

Section sign_family.
Variables (R : realType) (N h : nat) (A : nat -> 'M[R]_N).
Variables (G : nat -> nat -> 'M[R]_N) (y : 'cV[R]_N) (eps : nat -> bool).
Variables (a b : nat).
Hypothesis Ao : forall p, (p < h)%N -> A p \is orthogonalmx.
Hypothesis Ay : forall p, (p < h)%N -> A p *m y = if eps p then y else - y.
Hypothesis AG : forall q r p, (q < h)%N -> (r < h)%N -> (p < h)%N ->
  A p *m G q r = G q r *m A (swap_index q r p).
Hypotheses (ha : (a < h)%N) (hb : (b < h)%N).
Hypotheses (ea : eps a = false) (eb : eps b = true).

Local Lemma swap_index_lt q r p : (q < h)%N -> (r < h)%N -> (p < h)%N ->
  (swap_index q r p < h)%N.
Proof. by rewrite /swap_index => hq hr hp; case: eqP => _ //; case: eqP. Qed.

Local Definition sign_partner r := if (r == a) || eps r then a else b.
Local Definition sign_vec r := G (sign_partner r) r *m y.

Local Lemma sign_partner_lt r : (sign_partner r < h)%N.
Proof. by rewrite /sign_partner; case: ifP. Qed.

Local Lemma sign_vec_profile r p : (r < h)%N -> (p < h)%N ->
  A p *m sign_vec r =
  if eps (swap_index (sign_partner r) r p) then sign_vec r else - sign_vec r.
Proof.
move=> hr hp.
rewrite /sign_vec mulmxA AG ?sign_partner_lt // -mulmxA.
rewrite Ay ?swap_index_lt ?sign_partner_lt //.
by case: ifP => _ //; rewrite mulmxN.
Qed.

Local Lemma swap_indexL q r : swap_index q r q = r.
Proof. by rewrite /swap_index eqxx. Qed.

Local Lemma swap_indexR q r : swap_index q r r = q.
Proof. by rewrite /swap_index; case: eqP => [->|_]; rewrite ?eqxx. Qed.

Local Lemma swap_indexD q r p : p != q -> p != r -> swap_index q r p = p.
Proof. by rewrite /swap_index => /negbTE-> /negbTE->. Qed.

Local Lemma swap_index_id q p : swap_index q q p = p.
Proof. by rewrite /swap_index; case: eqP. Qed.

Local Lemma sign_partner_a : sign_partner a = a.
Proof. by rewrite /sign_partner eqxx. Qed.

Local Lemma sign_partner_p r : eps r -> sign_partner r = a.
Proof. by rewrite /sign_partner => ->; rewrite orbT. Qed.

Local Lemma sign_partner_m r : r != a -> ~~ eps r -> sign_partner r = b.
Proof. by rewrite /sign_partner => /negbTE-> /negbTE->. Qed.

Local Lemma sign_eigen_orth p (u u' : 'cV[R]_N) : (p < h)%N ->
  A p *m u = u -> A p *m u' = - u' -> mxdot u u' = 0.
Proof.
move=> hp Au Au'.
have : mxdot u u' = - mxdot u u'.
  by rewrite -{1}(mxdot_orthogonalmxl u u' (Ao hp)) Au Au' mxdotNr.
move/eqP; rewrite -subr_eq0 opprK -mulr2n -mulr_natr mulf_eq0 pnatr_eq0 orbF.
by move/eqP.
Qed.

Local Lemma sign_vec_orth r r' : (r < h)%N -> (r' < h)%N -> r != r' ->
  mxdot (sign_vec r) (sign_vec r') = 0.
Proof.
move=> hr hr' rr'.
have sep p : (p < h)%N -> eps (swap_index (sign_partner r) r p) ->
    ~~ eps (swap_index (sign_partner r') r' p) ->
    mxdot (sign_vec r) (sign_vec r') = 0.
  move=> hp e1 e2; apply: (sign_eigen_orth hp).
    by rewrite sign_vec_profile // e1.
  by rewrite sign_vec_profile // (negbTE e2).
have sep' p : (p < h)%N -> ~~ eps (swap_index (sign_partner r) r p) ->
    eps (swap_index (sign_partner r') r' p) ->
    mxdot (sign_vec r) (sign_vec r') = 0.
  move=> hp e1 e2; rewrite mxdotC; apply: (sign_eigen_orth hp).
    by rewrite sign_vec_profile // e2.
  by rewrite sign_vec_profile // (negbTE e1).
have ab : a != b by apply: contraFneq ea => ->.
have ba : b != a by rewrite eq_sym.
have [ra|ra] := eqVneq r a.
  subst r; have r'a : r' != a by rewrite eq_sym.
  rewrite sign_partner_a in sep sep'.
  case er': (eps r').
    apply: (sep' a ha); first by rewrite swap_index_id ea.
    by rewrite sign_partner_p // swap_indexL.
  rewrite sign_partner_m ?er' // in sep.
  apply: (sep b hb); first by rewrite swap_index_id eb.
  by rewrite swap_indexL er'.
have [r'a|r'a] := eqVneq r' a.
  subst r'; rewrite sign_partner_a in sep sep'.
  case er: (eps r).
    apply: (sep a ha); first by rewrite sign_partner_p // swap_indexL.
    by rewrite swap_index_id ea.
  rewrite sign_partner_m ?er // in sep'.
  apply: (sep' b hb); first by rewrite swap_indexL er.
  by rewrite swap_index_id eb.
have ar : a != r by rewrite eq_sym.
have ar' : a != r' by rewrite eq_sym.
case er: (eps r); case er': (eps r').
- rewrite !sign_partner_p // in sep sep'.
  apply: (sep' r hr); first by rewrite swap_indexR ea.
  by rewrite swap_indexD // er.
- rewrite sign_partner_p // (sign_partner_m r'a) ?er' // in sep.
  apply: (sep a ha); first by rewrite swap_indexL er.
  by rewrite swap_indexD // ea.
- rewrite (sign_partner_p er') (sign_partner_m ra) ?er // in sep'.
  apply: (sep' a ha); last by rewrite swap_indexL er'.
  by rewrite swap_indexD // ea.
- have rb : r != b by apply: contraFneq er => ->.
  rewrite (sign_partner_m ra) ?er // (sign_partner_m r'a) ?er' // in sep.
  apply: (sep r hr); first by rewrite swap_indexR eb.
  by rewrite swap_indexD // er.
Qed.

End sign_family.

Section ksubset_main.
Variables (R : realType) (k' w : nat).
Local Notation k := k'.+1.
Local Notation X := (ksubset k w).
Local Notation N := #|{: X}|.
Local Notation T := (@ksubset_mx R k w).
Variable Q : 'M[R]_N.
Hypotheses (k6 : (6 <= k)%N) (Qs : Q \is symmetricmx) (QQ : Q *m Q = Q).
Hypotheses (Q0 : Q != 0) (Q1 : Q *m (const_mx 1 : 'cV[R]_N) = 0).
Hypothesis QT : forall s, T s *m Q = Q *m T s.

(* If the product of the first two pair transpositions fixes the range of Q,
   then so do all 3-cycles, every column of Q is constant, and Q = 0. *)
Local Lemma ksubset_invariant_contra :
  T (pair_tperm k' 1 * pair_tperm k' 0)%g *m Q = Q -> False.
Proof.
move=> hC.
have GM g g' : T g *m Q = Q -> T g' *m Q = Q -> T (g * g')%g *m Q = Q.
  by move=> hg hg'; rewrite -ksubset_mxM -mulmxA hg hg'.
have GV g : T g *m Q = Q -> T g^-1 *m Q = Q.
  by move=> hg; rewrite -{1}hg mulmxA ksubset_mxM mulgV ksubset_mx1 mul1mx.
have GJ g c : T g *m Q = Q -> T (g ^ c)%g *m Q = Q.
  move=> hg; rewrite /conjg -!ksubset_mxM -!mulmxA QT (mulmxA (T g)) hg.
  by rewrite mulmxA QT -mulmxA ksubset_mxM mulVg ksubset_mx1 mulmx1.
have k4 : (3 < k)%N by apply: leq_trans k6.
(* The conjugates of pair_tperm 1 * pair_tperm 0: all products of two disjoint
   transpositions. *)
have Gpair (x1 x2 x3 x4 : 'I_k) : uniq [:: x3; x4; x1; x2] ->
    T (tperm x1 x2 * tperm x3 x4)%g *m Q = Q.
  move=> u.
  have u0 : uniq [:: inord 0; inord 1; inord 2; inord 3 : 'I_k].
    rewrite /= !inE -!val_eqE /= !inordK //; by apply: leq_trans k4.
  have [g /= [g0 g1 g2 g3]] := perm_map_uniq u0 u (erefl 4%N).
  have -> : (tperm x1 x2 * tperm x3 x4)%g =
      ((pair_tperm k' 1 * pair_tperm k' 0) ^ g)%g.
    by rewrite conjMg /pair_tperm !tpermJ g0 g1 g2 g3.
  exact: GJ.
(* The 3-cycles, as (a b)(d e) (d e)(b c). *)
have G3 (a b c : 'I_k) : a != b -> b != c -> a != c ->
    T (tperm a b * tperm b c)%g *m Q = Q.
  move=> ab bc ac.
  have : (1 < #|~: [set a; b; c]|)%N.
    have le3 : (#|[set a; b; c]| <= 3)%N.
      apply: (leq_trans (leq_card_setU _ _)); rewrite cardsU1 !cards1.
      by case: (a \notin [set b]).
    rewrite -(leq_add2l #|[set a; b; c]|) cardsC card_ord.
    apply: leq_trans k6; rewrite -[6%N]/(4 + 2)%N leq_add2r.
    exact: leq_trans le3 _.
  case/card_gt1P => d [e [dA eA de]].
  move: dA eA; rewrite !inE !negb_or.
  move=> /andP [/andP [da db] dc] /andP [/andP [ea eb] ec].
  have h1 : T (tperm a b * tperm d e)%g *m Q = Q.
    by apply: Gpair; rewrite !cons_uniq !inE !negb_or de da db ea eb ab.
  have h2 : T (tperm d e * tperm b c)%g *m Q = Q.
    apply: Gpair; rewrite !cons_uniq !inE !negb_or bc de.
    by rewrite ![b == _]eq_sym ![c == _]eq_sym db eb dc ec.
  have -> : (tperm a b * tperm b c =
      (tperm a b * tperm d e) * (tperm d e * tperm b c))%g.
    by rewrite -mulgA (mulgA (tperm d e)) tperm2 mul1g.
  exact: GM.
have k3 : (2 < k)%N by apply: leq_trans k4.
(* Every column of Q is constant. *)
have fc j (B B' : X) : Q (enum_rank B) j = Q (enum_rank B') j.
  apply: (@kact_cycle_const k w _ (fun B => Q (enum_rank B) j) k3).
  move=> a b c B1 ab bc ac.
  have := GV _ (G3 a b c ab bc ac).
  move/(congr1 (fun M : 'M[R]_N => M (enum_rank B1) j)).
  by rewrite ksubset_mx_mul invgK enum_rankK.
apply/(negP Q0)/eqP/matrixP => i j; rewrite mxE.
have hsum : \sum_l Q l j = 0.
  have := congr1 (fun M : 'cV[R]_N => M j 0) Q1; rewrite !mxE => h0.
  rewrite -[RHS]h0; apply: eq_bigr => l _; rewrite mxE mulr1.
  by rewrite -{1}(symmetricmxP _ Qs) mxE.
have : \sum_l Q l j = N%:R * Q i j.
  rewrite (eq_bigr (fun=> Q i j)) ?sumr_const ?card_ord ?mulr_natl // => l _.
  by rewrite -[l]enum_valK -[i]enum_valK; apply: fc.
rewrite hsum => /esym/eqP; rewrite mulf_eq0 pnatr_eq0 => /orP [|/eqP //].
move=> h; have p : (0 < N)%N := leq_ltn_trans (leq0n i) (ltn_ord i).
by rewrite (eqP h) in p.
Qed.

(* Otherwise a sign refinement gives k/2 orthogonal vectors in the range of
   Q. *)
Local Lemma ksubset_mult_refine (j : 'I_N) :
  T (pair_tperm k' 0) *m T (pair_tperm k' 1) *m col j Q != col j Q ->
  (k %/ 2)%:R <= \tr Q.
Proof.
move=> hj.
have h3 : (3 <= k %/ 2)%N := leq_div2r 2 k6.
have h0 : (0 < k %/ 2)%N by apply: leq_trans h3.
have h1 : (1 < k %/ 2)%N by apply: leq_trans h3.
pose A p := T (pair_tperm k' p).
have Ao p : A p \is orthogonalmx by apply: ksubset_mx_orthogonal.
have AA p : A p *m A p = 1%:M by rewrite /A ksubset_mxM pair_tpermK ksubset_mx1.
have Acomm p q : (p < k %/ 2)%N -> (q < k %/ 2)%N -> A p *m A q = A q *m A p.
  by move=> hp hq; rewrite /A !ksubset_mxM pair_tpermC.
have AQ p : A p *m Q = Q *m A p by apply: QT.
pose C := A 0%N *m A 1%N.
have AC p : (p < k %/ 2)%N -> A p *m C = C *m A p.
  move=> hp; rewrite /C mulmxA (Acomm p 0%N) // -mulmxA (Acomm p 1%N) //.
  by rewrite mulmxA.
have CC : C *m C = 1%:M.
  rewrite /C -mulmxA (mulmxA (A 1%N)) (Acomm 1%N 0%N) //.
  by rewrite -mulmxA AA mulmx1 AA.
have CQ : C *m Q = Q *m C.
  by rewrite /C -mulmxA AQ mulmxA AQ -mulmxA.
(* A vector of the range of Q that C moves, and its part in the
   (-1)-eigenspace of C. *)
set v := col j Q.
have Qv : Q *m v = v by rewrite /v colE mulmxA QQ.
pose x := v - C *m v.
have x0 : x != 0 by rewrite /x subr_eq0 eq_sym.
have Qx : Q *m x = x by rewrite /x mulmxBr Qv mulmxA -CQ -mulmxA Qv.
have Cx : C *m x = - x by rewrite /x mulmxBr mulmxA CC mul1mx opprB.
have [y [y0 Qy Cy hy]] := @sign_refine _ _ (k %/ 2) A Q C x
  (fun p _ => AA p) Acomm (fun p _ => AQ p) AC x0 Qx Cx.
have yNy : (- y == y) = false.
  apply/negbTE; apply: contra y0 => /eqP e.
  have : y *+ 2 == 0 by rewrite mulr2n -{1}e addNr.
  by rewrite -scaler_nat scaler_eq0 pnatr_eq0.
(* The sign profile of y; it differs at 0 and 1, since C y = - y. *)
pose eps p := A p *m y == y.
have Ay p : (p < k %/ 2)%N -> A p *m y = if eps p then y else - y.
  by move=> hp; rewrite /eps; case: (hy p hp) => ->; rewrite ?eqxx ?yNy.
have e01 : eps 0%N != eps 1%N.
  apply/negP => /eqP e; move: Cy; rewrite /C -mulmxA (Ay 1%N) // -e.
  by case e0: (eps 0%N); rewrite ?mulmxN (Ay 0%N) // e0 ?opprK => /eqP;
    rewrite eq_sym yNy.
pose a := if eps 0%N then 1%N else 0%N.
pose b := if eps 0%N then 0%N else 1%N.
have ea : eps a = false.
  rewrite /a; case e0: (eps 0%N) => //.
  by move: e01; rewrite e0; case: (eps 1%N).
have eb : eps b = true.
  rewrite /b; case e0: (eps 0%N) => //.
  by move: e01; rewrite e0; case: (eps 1%N).
have ha : (a < k %/ 2)%N by rewrite /a; case: ifP.
have hb : (b < k %/ 2)%N by rewrite /b; case: ifP.
pose G q r := T (pair_swap k' q r).
have AG q r p : (q < k %/ 2)%N -> (r < k %/ 2)%N -> (p < k %/ 2)%N ->
    A p *m G q r = G q r *m A (swap_index q r p).
  by move=> hq hr hp; rewrite /A /G !ksubset_mxM pair_swap_tperm.
apply: (@orthoproj_family_trace _ _ (k %/ 2) Q
  (fun r : 'I_(k %/ 2) => sign_vec G y eps a b r) Qs QQ).
- move=> r; rewrite /sign_vec /G; apply: contra y0 => /eqP e.
  have := orthogonalmxT
    (ksubset_mx_orthogonal R w (pair_swap k' (sign_partner eps a b r) r)).
  by move=> hT; rewrite -[y]mul1mx -hT -mulmxA e mulmx0.
- by move=> r; rewrite /sign_vec /G mulmxA -QT -mulmxA Qy.
- move=> r r' rr'.
  by apply: (sign_vec_orth (fun p _ => Ao p) Ay AG ha hb ea eb).
Qed.

Local Lemma ksubset_mult_S : (k %/ 2)%:R <= \tr Q.
Proof.
have [/existsP [j hj]|hB] :=
  boolP [exists j,
    T (pair_tperm k' 0) *m T (pair_tperm k' 1) *m col j Q != col j Q].
  exact: (ksubset_mult_refine hj).
exfalso; apply: ksubset_invariant_contra.
rewrite -ksubset_mxM; apply/matrixP => i j.
move/existsPn: hB => /(_ j); rewrite negbK => /eqP.
move/(congr1 (fun M : 'cV[R]_N => M i 0)).
rewrite (colE j Q) mulmxA -(colE j Q).
by rewrite -(colE j (T (pair_tperm k' 0) *m T (pair_tperm k' 1) *m Q)) !mxE.
Qed.

End ksubset_main.

Section ksubset_multiplicity.
Variable R : realType.

Lemma ksubset_multiplicity (k w : nat) (Q : 'M[R]_#|{: ksubset k w}|) :
  ~~ odd k -> (6 <= k)%N ->
  Q \is symmetricmx -> Q *m Q = Q -> Q != 0 ->
  Q *m (const_mx 1 : 'cV[R]_#|{: ksubset k w}|) = 0 ->
  (forall s : {perm 'I_k}, ksubset_mx R w s *m Q = Q *m ksubset_mx R w s) ->
  (k %/ 2)%:R <= \tr Q.
Proof.
move=> _ k6; case: k Q k6 => [|k'] Q // k6.
exact: ksubset_mult_S.
Qed.

End ksubset_multiplicity.

(* The permutations of 'I_6 acting on its 3-subsets: every nonzero orthogonal
   projection that commutes with them and kills the constants has trace at
   least 3. *)
Example ksubset_multiplicity_six (R : realType)
    (Q : 'M[R]_#|{: ksubset 6 3}|) :
  Q \is symmetricmx -> Q *m Q = Q -> Q != 0 ->
  Q *m (const_mx 1 : 'cV[R]_#|{: ksubset 6 3}|) = 0 ->
  (forall s : {perm 'I_6}, ksubset_mx R 3 s *m Q = Q *m ksubset_mx R 3 s) ->
  3%:R <= \tr Q.
Proof. exact: (@ksubset_multiplicity R 6 3 Q isT isT). Qed.
