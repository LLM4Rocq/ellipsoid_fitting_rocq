From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import arithmetic_tactic ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part.
From GaussianAnalysis.matrix Require Import psd_splitting psd_factorization.
From GaussianAnalysis.matrix Require Import nuclear condition_cone.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.convex Require Import logdet_barrier moreau.

(**md**************************************************************************)
(* # Duality for the cone of positive semidefinite matrices                   *)
(*                                                                            *)
(* Let G j, for j < N, be matrices of 'M[R]_n. The evaluation psd_eval G F of *)
(* F in 'M[R]_n is the row of its trace pairings tr (F G j), and the          *)
(* evaluation cone psd_eval_cone G is the image of the positive semidefinite  *)
(* matrices under psd_eval G. This file states the duality of the positive    *)
(* semidefinite cone that the passage from an exact semidefinite lift to a    *)
(* PSD factorization of its slack matrix uses.                                *)
(*                                                                            *)
(* The general statements of this file are compiled Prop definitions, which   *)
(* the user accepted on 15 October 2026 with batch 3 of phase 13 (AGENTS.md,  *)
(* section Phase 13, step 0, items 3 and 4). Each is proved by the lemma of   *)
(* the same name without the suffix _statement; the statement definitions     *)
(* stay until the freezes record them in the acceptance inventory.            *)
(*                                                                            *)
(* - psd_eval_cone_closed_statement: if every G j is positive semidefinite,   *)
(*   the evaluation cone is closed.                                           *)
(* - psdmx_dual_statement: self-duality. A symmetric S is positive            *)
(*   semidefinite if and only if tr (F S) >= 0 for every positive             *)
(*   semidefinite F.                                                          *)
(* - psd_farkas_statement: Farkas's lemma for the evaluation cone. If         *)
(*   every G j is positive semidefinite, y is in the evaluation cone if and   *)
(*   only if <c, y> >= 0 for every c such that sum_j c_j G j is positive      *)
(*   semidefinite.                                                            *)
(* - psd_slack_certificate_statement: the slack certificate. Let B i, for i   *)
(*   in a finite type I, be positive semidefinite, and let s : I -> R vanish  *)
(*   at some i0. Then s i = tr (A B i) for every i and some positive          *)
(*   semidefinite A if and only if sum_i w_i s_i >= 0 for every w of sum one  *)
(*   such that sum_i w_i B i is positive semidefinite.                        *)
(* - psd_slack_certificate_affine_statement: the slack certificate for an     *)
(*   affine subspace L = {X | tr (C l X) = c l for every l < m} and an affine *)
(*   function f X = tr (D X) + d. If the B i are positive semidefinite points *)
(*   of L, f >= 0 at the positive semidefinite points of L and f (B i0) = 0,  *)
(*   then f (B i) = tr (A B i) for every i and some positive semidefinite A.  *)
(*                                                                            *)
(* These are Rocq formalizations of the credited arguments for the            *)
(* cone-factorization step of the proof of the corollary 'Unshifted rank and  *)
(* exact lifts' of 'Exponential PSD rank of positively shifted matching       *)
(* matrices' (family 126 of the OpenAI math collection, revision 1581d4cbd,   *)
(* source/sections/introduction.tex, lines 94-113). The manuscript cites the  *)
(* cone-factorization theorem of Gouveia, Parrilo and Thomas. The Lean        *)
(* development of the collection proves the direction that the corollary      *)
(* needs, with these declarations, which this file follows:                   *)
(* Lean: evaluation (PSDEvaluation.lean, line 10)                             *)
(* Lean: evaluationCone (PSDEvaluation.lean, line 19)                         *)
(* Lean: evaluationCone_isClosed (OrthogonalCone.lean, line 39)               *)
(* Lean: psd_of_trace_nonneg (PSDDuality.lean, line 33)                       *)
(* Lean: exists_psd_evaluation (PSDDuality.lean, line 44)                     *)
(* Lean: affine_slack_certificate (AffineCertificate.lean, line 12)           *)
(*                                                                            *)
(* The proofs. Self-duality tests S against the matrices x x^T. For the       *)
(* closedness, S = sum_j G j is positive semidefinite; let Q be the           *)
(* orthogonal projection onto its kernel (psd_kernel_proj of                  *)
(* matrix/psd_factorization.v). Every G j vanishes on the range of Q, so the  *)
(* compression P F P of F by P = 1 - Q has the same evaluations, and          *)
(* S + Q >= b I for some b > 0 bounds its trace by the sum of the evaluations *)
(* divided by b (psd_eval_compress). A point y of the closure of the cone is  *)
(* thus a limit of evaluations of positive semidefinite matrices of trace at  *)
(* most (sum_j y_j + 1) / b, a compact set in the coordinates of mxvec, and   *)
(* the image of a compact set under the continuous evaluation is closed.      *)
(* Farkas's lemma follows from Moreau's decomposition (cone_projP of          *)
(* convex/moreau.v) and self-duality: the residual q = y - proj y is in the   *)
(* polar cone, so sum_j (- q_j) G j is positive semidefinite, and the         *)
(* hypothesis gives |q|^2 <= 0. The slack certificate applies Farkas's lemma: *)
(* for c with sum_j c_j B j positive semidefinite, the weights                *)
(* w = (c + t e_i0) / (sum_j c_j + t), with t = |sum_j c_j| + 1, sum to one,  *)
(* as in the Lean proof. The affine form checks the hypothesis of the slack   *)
(* certificate.                                                               *)
(*                                                                            *)
(* Departures from the Lean development. Lean proves the closedness by        *)
(* diagonalizing sum_j G j and extracting convergent subsequences; here the   *)
(* compression by the kernel projection and a compact set replace them.       *)
(*                                                                            *)
(* Departures from the Lean statements. The Lean slack certificate takes an   *)
(* affine subspace and an affine map. psd_slack_certificate_statement assumes *)
(* only the sign of the slacks at the positive semidefinite affine            *)
(* combinations of the B i, and the affine form writes the subspace by trace  *)
(* equations and the map by a trace pairing. Farkas's lemma, self-duality and *)
(* the first slack certificate are stated as equivalences; their converse     *)
(* directions are the easy ones.                                              *)
(*                                                                            *)
(* Proved besides:                                                            *)
(* - psd_eval_compress: the compressed representative and its trace bound;    *)
(* - psdmx_factor, psdmx_frobenius_le_trace: a positive semidefinite S is     *)
(*   H^T H, and |S|_F <= tr S;                                                *)
(* - psdmx_outer, mxtrace_outer: x x^T is positive semidefinite, and          *)
(*   tr (x x^T S) = <x, S x>;                                                 *)
(* - psd_evalE, mxdot_psd_eval: <c, psd_eval G F> = tr (F sum_j c_j G j);     *)
(* - psd_eval_cone0, psd_eval_coneZ, psd_eval_cone_convex: the evaluation     *)
(*   cone is a convex cone.                                                   *)
(*                                                                            *)
(* - The example psd_eval_cone_trace: the evaluation cone of the identity     *)
(*   matrix of size n + 1 is the set of nonnegative reals, the traces of the  *)
(*   positive semidefinite matrices.                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*      psd_eval G F == \row_j \tr (F *m G j), the trace pairings of F        *)
(*                      with the matrices G j                                 *)
(*   psd_eval_cone G == [set psd_eval G F | F in [set F | psdmx F]], the      *)
(*                      evaluation cone                                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section evaluation.
Variable R : realType.

(* The trace pairings of F with the matrices G j. *)
Definition psd_eval n N (G : 'I_N -> 'M[R]_n) (F : 'M[R]_n) : 'rV[R]_N :=
  \row_j \tr (F *m G j).

(* The evaluation cone: the evaluations of the positive semidefinite
   matrices. *)
Definition psd_eval_cone n N (G : 'I_N -> 'M[R]_n) : set 'rV[R]_N :=
  [set psd_eval G F | F in [set F : 'M[R]_n | psdmx F]].

End evaluation.

(* The general statements. *)

(* The evaluation cone of positive semidefinite matrices is closed. *)
Definition psd_eval_cone_closed_statement : Prop :=
  forall (R : realType) (n N : nat) (G : 'I_N -> 'M[R]_n),
  (forall j, psdmx (G j)) -> closed (psd_eval_cone G).

(* Self-duality of the positive semidefinite cone. *)
Definition psdmx_dual_statement : Prop :=
  forall (R : realType) (n : nat) (S : 'M[R]_n), S \is symmetricmx ->
  psdmx S <-> (forall F : 'M[R]_n, psdmx F -> 0 <= \tr (F *m S)).

(* Farkas's lemma: the evaluation cone is the dual of the cone of the
   coefficients c such that sum_j c_j G j is positive semidefinite. *)
Definition psd_farkas_statement : Prop :=
  forall (R : realType) (n N : nat) (G : 'I_N -> 'M[R]_n) (y : 'rV[R]_N),
  (forall j, psdmx (G j)) ->
  psd_eval_cone G y <->
  (forall c : 'rV[R]_N, psdmx (\sum_j c 0 j *: G j) -> 0 <= mxdot c y).

(* The slack certificate: slacks with one zero, nonnegative on average at
   the positive semidefinite affine combinations, are the trace pairings
   with a positive semidefinite matrix. *)
Definition psd_slack_certificate_statement : Prop :=
  forall (R : realType) (n : nat) (I : finType) (B : I -> 'M[R]_n)
         (s : I -> R) (i0 : I),
  (forall i, psdmx (B i)) -> s i0 = 0 ->
  (exists2 A : 'M[R]_n, psdmx A & forall i, \tr (A *m B i) = s i) <->
  (forall w : I -> R, \sum_i w i = 1 -> psdmx (\sum_i w i *: B i) ->
     0 <= \sum_i w i * s i).

(* The slack certificate for an affine subspace given by trace equations and
   an affine function given by a trace pairing. *)
Definition psd_slack_certificate_affine_statement : Prop :=
  forall (R : realType) (n m : nat) (I : finType) (C : 'I_m -> 'M[R]_n)
         (c : 'I_m -> R) (D : 'M[R]_n) (d : R) (B : I -> 'M[R]_n) (i0 : I),
  (forall i, psdmx (B i)) -> (forall i l, \tr (C l *m B i) = c l) ->
  (forall X : 'M[R]_n, psdmx X -> (forall l, \tr (C l *m X) = c l) ->
     0 <= \tr (D *m X) + d) ->
  \tr (D *m B i0) + d = 0 ->
  exists2 A : 'M[R]_n, psdmx A &
    forall i, \tr (A *m B i) = \tr (D *m B i) + d.

Section psd_tools.
Variable R : realType.
Implicit Types n : nat.

(* A positive semidefinite matrix is a Gram matrix H^T H. *)
Lemma psdmx_factor n (S : 'M[R]_n) :
  psdmx S -> exists H : 'M[R]_n, H^T *m H = S.
Proof.
move=> [Ssym Sform]; have [P Po [d SE]] := symmetric_spectral Ssym.
have d0 i : 0 <= d 0 i by have [+ _] := spectral_psd Po SE; apply.
exists (diag_mx (\row_i Num.sqrt (d 0 i)) *m P).
rewrite trmx_mul tr_diag_mx SE mulmxA -[_ *m diag_mx _ *m diag_mx _]mulmxA.
rewrite mulmx_diag; congr (_ *m diag_mx _ *m _).
by apply/rowP => i; rewrite !mxE -expr2 sqr_sqrtr.
Qed.

Lemma psdmx_frobenius_le_trace n (S : 'M[R]_n) :
  psdmx S -> frobenius S <= \tr S.
Proof.
move=> /psdmx_factor [H <-]; apply: le_trans (frobenius_mulmx _ _) _.
by rewrite frobenius_trmx -expr2 frobenius_sqr mxdot_trace mxtrace_mulC.
Qed.

Lemma psdmx_outer n (x : 'cV[R]_n) : psdmx (x *m x^T).
Proof.
split; first by apply/symmetricmxP; rewrite trmx_mul trmxK.
by move=> y; rewrite -mulmxA mxdotC mxdot_mulmxl mxdot_ge0.
Qed.

Lemma mxtrace_outer n (x : 'cV[R]_n) (S : 'M[R]_n) :
  \tr (x *m x^T *m S) = mxdot x (S *m x).
Proof.
by rewrite -mulmxA mxtrace_mulC mxdot_colE /mxtrace big_ord1 mulmxA.
Qed.

(* Self-duality of the positive semidefinite cone. *)
Lemma psdmx_dual n (S : 'M[R]_n) : S \is symmetricmx ->
  psdmx S <-> (forall F : 'M[R]_n, psdmx F -> 0 <= \tr (F *m S)).
Proof.
move=> Ss; split => [Sp F Fp|h]; first exact: mxtrace_psd_ge0.
by split => // x; have := h _ (psdmx_outer x); rewrite mxtrace_outer.
Qed.

End psd_tools.

Section evaluation_tools.
Variables (R : realType) (n N : nat) (G : 'I_N -> 'M[R]_n).
Implicit Types (F : 'M[R]_n) (c y : 'rV[R]_N).

Lemma psd_evalE F j : psd_eval G F 0 j = \tr (F *m G j).
Proof. by rewrite mxE. Qed.

Lemma mxdot_psd_eval c F :
  mxdot c (psd_eval G F) = \tr (F *m \sum_j c 0 j *: G j).
Proof.
rewrite /mxdot big_ord1 mulmx_sumr raddf_sum /=.
by apply: eq_bigr => j _; rewrite mxE -scalemxAr mxtraceZ.
Qed.

Lemma psd_eval_cone0 : psd_eval_cone G 0.
Proof.
exists 0; first exact: psdmx0.
by apply/rowP => j; rewrite !mxE mul0mx mxtrace0.
Qed.

Lemma psd_eval_coneZ y (a : R) : psd_eval_cone G y -> 0 <= a ->
  psd_eval_cone G (a *: y).
Proof.
move=> [F Fp <-] a0; exists (a *: F); first exact: psdmxZ.
by apply/rowP => j; rewrite !mxE -scalemxAl mxtraceZ.
Qed.

Lemma psd_eval_cone_convex y y' (t : R) : psd_eval_cone G y ->
  psd_eval_cone G y' -> 0 <= t <= 1 -> psd_eval_cone G (y + t *: (y' - y)).
Proof.
move=> [F Fp <-] [F' F'p <-] /andP[t0 t1].
exists ((1 - t) *: F + t *: F').
  by apply: psdmxD; apply: psdmxZ; rewrite ?subr_ge0.
apply/rowP => j; rewrite !mxE mulmxDl -!scalemxAl raddfD /= !mxtraceZ.
ring.
Qed.

End evaluation_tools.

Section closedness.
Variables (R : realType) (n N : nat) (G : 'I_N -> 'M[R]_n).
Hypothesis Gp : forall j, psdmx (G j).

(* Every evaluation has a representative whose trace is at most a constant
   times the sum of the evaluation: compress by the orthogonal projection
   onto the range of sum_j G j. *)
Lemma psd_eval_compress : exists2 b : R, 0 < b &
  forall F, psdmx F -> exists2 F' : 'M[R]_n, psdmx F' &
    psd_eval G F' = psd_eval G F /\ b * \tr F' <= \sum_j psd_eval G F 0 j.
Proof.
pose S := \sum_j G j.
have Sp : psdmx S by apply: psdmx_sum => j _; exact: Gp.
have [Q [[Qs QQ] SQ SQpd GQ]] := psd_kernel_proj Sp.
have GjQ j : G j *m Q = 0.
  apply: GQ; first exact: Gp.
  have -> : S - G j = \sum_(j' | j' != j) G j'.
    by rewrite /S (bigD1 j) //= addrC addKr.
  by apply: psdmx_sum => j' _; exact: Gp.
have QGj j : Q *m G j = 0.
  have := congr1 trmx (GjQ j); rewrite trmx_mul trmx0.
  by rewrite (symmetricmxP _ Qs) (symmetricmxP _ (Gp j).1).
pose P := 1%:M - Q.
have Ps : P \is symmetricmx.
  by apply/symmetricmxP; rewrite /P linearB /= trmx1 (symmetricmxP _ Qs).
have PG j : P *m G j = G j by rewrite /P mulmxBl mul1mx QGj subr0.
have GP j : G j *m P = G j by rewrite /P mulmxBr mulmx1 GjQ subr0.
have PQ : P *m Q = 0 by rewrite /P mulmxBl mul1mx QQ subrr.
have [b b0 hb] := posdefmx_ge SQpd.
have Ds : (S + Q) \is symmetricmx := SQpd.1.
have Dbp : psdmx (S + Q - b%:M).
  split.
    apply/symmetricmxP; rewrite linearB /= tr_scalar_mx.
    by rewrite (symmetricmxP _ Ds).
  move=> x; rewrite mulmxBl mxdotBr mul_scalar_mx mxdotZr subr_ge0.
  by rewrite (posdefmx_form x Ds) -[mxdot x x]mxdot_trmx; exact: hb.
exists b => // F Fp.
exists (P *m F *m P); first exact: psdmx_conj.
have ev : psd_eval G (P *m F *m P) = psd_eval G F.
  by apply/rowP => j; rewrite !mxE -!mulmxA PG mxtrace_mulC -mulmxA GP.
split => //.
have h := mxtrace_psd_ge0 (psdmx_conj Ps Fp) Dbp.
have e1 : \tr (P *m F *m P *m S) = \sum_j psd_eval G F 0 j.
  rewrite mulmx_sumr raddf_sum /=; apply: eq_bigr => j _.
  by rewrite -ev mxE.
have e2 : \tr (P *m F *m P *m Q) = 0 by rewrite -mulmxA PQ mulmx0 mxtrace0.
move: h; rewrite mulmxBr mulmxDr raddfB raddfD /= e1 e2 addr0.
by rewrite mul_mx_scalar mxtraceZ subr_ge0.
Qed.

(* The evaluation in the coordinates of mxvec, and the vectors of the
   positive semidefinite matrices of trace at most M. *)
Let vev (v : 'rV[R]_(n * n)) : 'rV[R]_N := psd_eval G (vec_mx v).

Let vev_continuous : continuous vev.
Proof.
pose W : 'M[R]_(n * n, N) := \matrix_(k, j) mxvec (G j)^T 0 k.
have -> : vev = fun v => v *m W.
  apply/funext => v; apply/rowP => j; rewrite /vev mxE.
  have -> : \tr (vec_mx v *m G j) = mxdot (vec_mx v) (G j)^T.
    by rewrite mxdot_trace trmxK.
  rewrite mxdotC mxdot_vec_mxr /mxdot big_ord1 mxE.
  by apply: eq_bigr => k _; rewrite mxE mulrC.
exact: continuous_mulmxr.
Qed.

Let VM (M : R) : set 'rV[R]_(n * n) :=
  [set v | psdmx (vec_mx v) /\ \tr (vec_mx v) <= M].

Let VM_bounded M : bounded_set (VM M).
Proof.
exists (Num.max M 0); split; first exact: num_real.
move=> M' M'1 v [vp vM]; apply: le_trans (ltW M'1).
rewrite [leLHS]/Num.Def.normr /=; apply: le_trans (mx_norm_le_frobenius v) _.
have -> : frobenius v = frobenius (vec_mx v) by rewrite /frobenius mxdot_vec_mx.
apply: le_trans (psdmx_frobenius_le_trace vp) _.
by rewrite le_max vM.
Qed.

Let VM_closed M : closed (VM M).
Proof.
have hs (c : 'rV[R]_(n * n)) : closed [set v | 0 <= mxdot v c].
  exact: ((continuous_closedP (fun v : 'rV[R]_(n * n) => mxdot v c)).1
    (@continuous_mxdotv _ _ c) _ (@closed_ge R 0)).
have hl (c : 'rV[R]_(n * n)) : closed [set v | mxdot v c <= M].
  exact: ((continuous_closedP (fun v : 'rV[R]_(n * n) => mxdot v c)).1
    (@continuous_mxdotv _ _ c) _ (@closed_le R M)).
pose E (ij : 'I_n * 'I_n) : 'M[R]_n := delta_mx ij.1 ij.2 - delta_mx ij.2 ij.1.
have pE (v : 'rV[R]_(n * n)) ij :
    mxdot v (mxvec (E ij)) = vec_mx v ij.1 ij.2 - vec_mx v ij.2 ij.1.
  by rewrite mxdotC -mxdot_vec_mxr mxdotC mxdotBr !mxdot_delta.
have tE (v : 'rV[R]_(n * n)) : \tr (vec_mx v) = mxdot v (mxvec 1%:M).
  by rewrite mxdotC -mxdot_vec_mxr mxdot_trace mul1mx mxtrace_tr.
have -> : VM M =
    (\bigcap_(ij in [set: 'I_n * 'I_n])
       ([set v | 0 <= mxdot v (mxvec (E ij))] `&`
        [set v | 0 <= mxdot v (- mxvec (E ij))])) `&`
    (\bigcap_(x in [set: 'cV[R]_n])
       [set v | 0 <= mxdot v (mxvec (x *m x^T))]) `&`
    [set v | mxdot v (mxvec 1%:M) <= M].
  apply/seteqP; split => v.
    move=> [[vs vpsd] vM]; split; first split.
    - move=> ij _; rewrite /= mxdotNr pE; have /symmetricmxP Ve := vs.
      have := congr1 (fun A : 'M[R]_n => A ij.2 ij.1) Ve; rewrite mxE => ->.
      by rewrite subrr oppr0 lexx.
    - by move=> x _; rewrite /= -mxdot_quad_vec.
    - by rewrite /= -tE.
  move=> [[HE Hx] HM]; split; first split.
  - apply/symmetricmxP/matrixP => i j; rewrite mxE.
    have [h1 h2] := HE (j, i) I; move: h1 h2; rewrite /= mxdotNr pE /=.
    rewrite oppr_ge0 subr_ge0 subr_le0 => h1 h2.
    by apply/eqP; rewrite eq_le h1 h2.
  - by move=> x; rewrite mxdot_quad_vec; exact: Hx x I.
  - by rewrite tE.
apply: closedI; first apply: closedI.
- by apply: closed_bigI => ij _; apply: closedI; exact: hs.
- by apply: closed_bigI => x _; exact: hs.
- exact: hl.
Qed.

(* The evaluation cone of positive semidefinite matrices is closed. *)
Theorem psd_eval_cone_closed : closed (psd_eval_cone G).
Proof.
have [b b0 hb] := psd_eval_compress.
move=> y yK.
pose a := \sum_j y 0 j + 1.
pose KM := vev @` VM (a / b).
have KMc : closed KM.
  apply: compact_closed; first exact: norm_hausdorff.
  apply: continuous_compact; first exact: continuous_subspaceT vev_continuous.
  by apply: bounded_closed_compact; [exact: VM_bounded | exact: VM_closed].
have KMK : KM `<=` psd_eval_cone G.
  by move=> _ [v [vp _] <-]; exists (vec_mx v).
apply: KMK; apply: KMc => B By.
have sc : continuous (fun z : 'rV[R]_N => \sum_j z 0 j).
  move=> z; apply: (@continuous_big R^o _ +%R 0 xpredT (@add_continuous R^o)
    _ _ (fun j (w : 'rV[R]_N) => w 0 j)) => j _ w.
  exact: coord_continuous.
have ha : \sum_j y 0 j < a by rewrite /a ltrDl ltr01.
have Uy := @cvgr_lt _ _ _ (nbhs_filter y) _ _ (sc y) _ ha.
have [z [[F Fp Fz] [Bz /= zU]]] := yK _ (filterI By Uy).
have [F' F'p [F'e F'tr]] := hb F Fp.
exists z; split => //.
exists (mxvec F'); last by rewrite /vev mxvecK F'e.
split; first by rewrite mxvecK.
rewrite mxvecK ler_pdivlMr // mulrC; apply: le_trans F'tr _.
by rewrite Fz; exact: ltW.
Qed.

End closedness.

Section farkas.
Variable R : realType.

(* Farkas's lemma for the evaluation cone. *)
Theorem psd_farkas n N (G : 'I_N -> 'M[R]_n) (y : 'rV[R]_N) :
  (forall j, psdmx (G j)) ->
  psd_eval_cone G y <->
  (forall c : 'rV[R]_N, psdmx (\sum_j c 0 j *: G j) -> 0 <= mxdot c y).
Proof.
move=> Gp; split => [[F Fp <-] c cp|h].
  by rewrite mxdot_psd_eval; exact: mxtrace_psd_ge0.
set K := psd_eval_cone G.
have Kc : closed K := psd_eval_cone_closed Gp.
have K0 : K 0 := psd_eval_cone0 G.
have Kn : K !=set0 by exists 0.
have Kcvx := @psd_eval_cone_convex R n N G.
have KZ := @psd_eval_coneZ R n N G.
have [Kp _] := projP Kc Kn Kcvx y.
have [pol orth] := (cone_projP Kc K0 Kcvx KZ y Kp).1 erefl.
set p := proj K y in Kp pol orth *.
have Gs j : G j \is symmetricmx := (Gp j).1.
have cp : psdmx (\sum_j (- (y - p)) 0 j *: G j).
  apply/psdmx_dual => [|F Fp].
    apply/symmetricmxP; rewrite linear_sum /=; apply: eq_bigr => j _.
    by rewrite linearZ /= (symmetricmxP _ (Gs j)).
  rewrite -mxdot_psd_eval mxdotNl oppr_ge0.
  by apply: pol; exists F.
have := h _ cp; rewrite mxdotNl oppr_ge0.
have -> : mxdot (y - p) y = mxdot (y - p) (y - p).
  have e : y = y - p + p by rewrite subrK.
  by rewrite {2}e mxdotDr orth addr0.
rewrite le_eqVlt ltNge mxdot_ge0 orbF mxdot_eq0 subr_eq0 => /eqP ->.
exact: Kp.
Qed.

End farkas.

Section slack.
Variable R : realType.

(* The slack certificate. *)
Theorem psd_slack_certificate n (I : finType) (B : I -> 'M[R]_n)
    (s : I -> R) (i0 : I) :
  (forall i, psdmx (B i)) -> s i0 = 0 ->
  (exists2 A : 'M[R]_n, psdmx A & forall i, \tr (A *m B i) = s i) <->
  (forall w : I -> R, \sum_i w i = 1 -> psdmx (\sum_i w i *: B i) ->
     0 <= \sum_i w i * s i).
Proof.
move=> Bp s0; split => [[A Ap As] w w1 wp|h].
  have -> : \sum_i w i * s i = \tr (A *m \sum_i w i *: B i).
    rewrite mulmx_sumr raddf_sum /=; apply: eq_bigr => i _.
    by rewrite -scalemxAr mxtraceZ As.
  exact: mxtrace_psd_ge0.
pose G (j : 'I_#|I|) := B (enum_val j).
pose y : 'rV[R]_#|I| := \row_j s (enum_val j).
have Gp j : psdmx (G j) := Bp _.
have rk (V : zmodType) (f : 'I_#|I| -> V) :
    \sum_i f (enum_rank i) = \sum_j f j.
  rewrite [RHS](reindex (@enum_rank I)) //.
  exact: onW_bij (@enum_rank_bij I).
have ind (V : lmodType R) (f : I -> V) :
    \sum_i (i == i0)%:R *: f i = f i0.
  rewrite (bigD1 i0) //= eqxx scale1r big1 ?addr0 // => i /negPf ->.
  by rewrite scale0r.
have [A Ap Ay] : psd_eval_cone G y.
  apply/(psd_farkas _ Gp) => c cp.
  pose sc := \sum_j c 0 j; pose t := `|sc| + 1; pose q := sc + t.
  have t0 : 0 <= t by rewrite /t addr_ge0.
  have q0 : 0 < q.
    by rewrite /q /t; have := lerNnormlW (lexx `|sc|); lra.
  pose w i := q^-1 * c 0 (enum_rank i) + q^-1 * ((i == i0)%:R * t).
  have w1 : \sum_i w i = 1.
    rewrite /w big_split /= -!mulr_sumr.
    have -> : \sum_i c 0 (enum_rank i) = sc by exact: (rk _ (fun j => c 0 j)).
    have -> : \sum_i (i == i0)%:R * t = t by exact: (ind R^o (fun=> t)).
    by rewrite -mulrDr mulVf // gt_eqF.
  have wp : psdmx (\sum_i w i *: B i).
    have -> : \sum_i w i *: B i =
        q^-1 *: (\sum_j c 0 j *: G j + t *: B i0).
      rewrite /w; under eq_bigr do rewrite scalerDl -!scalerA.
      rewrite big_split /= -!scaler_sumr scalerDr; congr (_ + _).
        congr (_ *: _); rewrite -(rk _ (fun j => c 0 j *: G j)) /G.
        by apply: eq_bigr => i _; rewrite enum_rankK.
      congr (_ *: _); rewrite -(ind _ (fun i => t *: B i)).
      by apply: eq_bigr => i _; rewrite scalerA.
    apply: psdmxZ; first by rewrite invr_ge0 ltW.
    by apply: psdmxD => //; apply: psdmxZ.
  have := h w w1 wp.
  have -> : \sum_i w i * s i = q^-1 * mxdot c y.
    rewrite /w /mxdot big_ord1.
    under eq_bigr do rewrite mulrDl -!mulrA.
    rewrite big_split /= -!mulr_sumr.
    have -> : \sum_i (i == i0)%:R * (t * s i) = t * s i0.
      exact: (ind R^o (fun i => t * s i)).
    rewrite s0 mulr0 mulr0 addr0; congr (_ * _).
    rewrite -(rk _ (fun j => c 0 j * y 0 j)); apply: eq_bigr => i _.
    by rewrite mxE enum_rankK.
  by rewrite pmulr_rge0 // invr_gt0.
exists A => // i.
have := congr1 (fun z : 'rV[R]_#|I| => z 0 (enum_rank i)) Ay.
by rewrite /= !mxE /G enum_rankK.
Qed.

(* The slack certificate for an affine subspace given by trace equations and
   an affine function given by a trace pairing. *)
Theorem psd_slack_certificate_affine n m (I : finType) (C : 'I_m -> 'M[R]_n)
    (c : 'I_m -> R) (D : 'M[R]_n) (d : R) (B : I -> 'M[R]_n) (i0 : I) :
  (forall i, psdmx (B i)) -> (forall i l, \tr (C l *m B i) = c l) ->
  (forall X : 'M[R]_n, psdmx X -> (forall l, \tr (C l *m X) = c l) ->
     0 <= \tr (D *m X) + d) ->
  \tr (D *m B i0) + d = 0 ->
  exists2 A : 'M[R]_n, psdmx A &
    forall i, \tr (A *m B i) = \tr (D *m B i) + d.
Proof.
move=> Bp BC f0 fi0.
apply/(@psd_slack_certificate n I B (fun i => \tr (D *m B i) + d) i0 Bp fi0).
move=> w w1 wp.
have tr_sum (E : 'M[R]_n) :
    \tr (E *m \sum_i w i *: B i) = \sum_i w i * \tr (E *m B i).
  rewrite mulmx_sumr raddf_sum /=; apply: eq_bigr => i _.
  by rewrite -scalemxAr mxtraceZ.
have XC l : \tr (C l *m \sum_i w i *: B i) = c l.
  rewrite tr_sum (eq_bigr (fun i => w i * c l)) => [i _|]; first by rewrite BC.
  by rewrite -mulr_suml w1 mul1r.
have := f0 _ wp XC; rewrite tr_sum.
have -> : \sum_i w i * (\tr (D *m B i) + d) =
    \sum_i w i * \tr (D *m B i) + d.
  by rewrite (eq_bigr (fun i => w i * \tr (D *m B i) + w i * d)) =>
    [i _|]; [rewrite mulrDr | rewrite big_split /= -mulr_suml w1 mul1r].
done.
Qed.

End slack.

(* An example independent of any application: the evaluation cone of the
   identity matrix of size n + 1 is the set of nonnegative reals, the traces
   of the positive semidefinite matrices. *)
Example psd_eval_cone_trace (R : realType) (n : nat) :
  psd_eval_cone (fun _ : 'I_1 => (1%:M : 'M[R]_n.+1)) = [set y | 0 <= y 0 0].
Proof.
have psd1 : psdmx (1%:M : 'M[R]_n.+1).
  split; first by apply/symmetricmxP; rewrite trmx1.
  by move=> x; rewrite mul1mx mxdot_ge0.
apply/seteqP; split => y /=.
  by move=> [F Fpsd <-]; rewrite mxE; exact: mxtrace_psd_ge0 Fpsd psd1.
move=> y0; have n0 : (0 : R) < n.+1%:R by rewrite ltr0n.
pose F : 'M[R]_n.+1 := (y 0 0 / n.+1%:R) *: 1%:M.
exists F.
  split; first by apply/symmetricmxP; rewrite /F linearZ /= trmx1.
  move=> x; rewrite /F -scalemxAl mul1mx mxdotZr mulr_ge0 ?mxdot_ge0 //.
  by rewrite divr_ge0 // ltW.
apply/rowP => j; rewrite ord1 !mxE mulmx1 mxtraceZ mxtrace1.
by rewrite divfK // gt_eqF.
Qed.
