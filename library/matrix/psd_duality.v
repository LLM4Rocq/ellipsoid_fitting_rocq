From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From mathcomp Require Import topology normedtype.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part.
From GaussianAnalysis.matrix Require Import psd_splitting.

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
(* The general statements of this file are compiled Prop definitions, for     *)
(* review with batch 3 of phase 13 (AGENTS.md, section Phase 13, step 0,      *)
(* items 3 and 4). Each will be proved by the lemma of the same name without  *)
(* the suffix _statement.                                                     *)
(*                                                                            *)
(* - psd_eval_cone_closed_statement: if every G j is positive semidefinite,   *)
(*   the evaluation cone is closed.                                           *)
(* - psdmx_dual_statement: self-duality. A symmetric S is positive            *)
(*   semidefinite if and only if tr (F S) >= 0 for every positive             *)
(*   semidefinite F.                                                          *)
(* - psd_farkas_statement: Farkas's lemma for the evaluation cone. If every G *)
(*   j is positive semidefinite, y is in the evaluation cone if and only if   *)
(*   <c, y> >= 0 for every c such that sum_j c_j G j is positive              *)
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
(* Departures from the Lean statements. The Lean slack certificate takes an   *)
(* affine subspace and an affine map. psd_slack_certificate_statement assumes *)
(* only the sign of the slacks at the positive semidefinite affine            *)
(* combinations of the B i, and the affine form writes the subspace by trace  *)
(* equations and the map by a trace pairing. Farkas's lemma, self-duality and *)
(* the first slack certificate are stated as equivalences; their converse     *)
(* directions are the easy ones.                                              *)
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

(* The general statements, for review. *)

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
