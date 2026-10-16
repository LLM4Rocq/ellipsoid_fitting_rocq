From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype measure lebesgue_measure.
From mathcomp Require Import measurable_realfun numfun lebesgue_integral probability.
From mathcomp Require Import ring_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import lindeberg mixture tuple_rows.

(**md**************************************************************************)
(* # Symmetric laws translated in opposite directions                         *)
(*                                                                            *)
(* For a centrally symmetric row-vector law, an even measurable observation   *)
(* has the same law after translating by m or by -m. Consequently its law     *)
(* under any mixture of those two translations, including weights 0 and 1,    *)
(* equals its law under translation by m. The identity holds for every finite *)
(* independent sample, with no moment or density assumption.                   *)
(*                                                                            *)
(* row_symmetric_law P == P is invariant under x |-> -x on measurable sets    *)
(*        row_shift m == the measurable map x |-> x + m                      *)
(*    row_shift_law P m == the law of X + m when X has law P                  *)
(* sign_shift_law P m hw == w times law(X+m) plus (1-w) times law(X-m),       *)
(*                         where hw proves 0 <= w <= 1                       *)
(*        row_outer x == the matrix x^T x, an even measurable map             *)
(*                                                                            *)
(* The tuple identity applies to observations of outer products. It does not *)
(* identify events involving arbitrary centers or further translations.      *)
(*                                                                            *)
(* Source: the elementary sign coupling in doc/shifted-gaussian.tex,          *)
(* Remark rem:sign-invariance (source SHA-256 d8ad56800c11eae1643bac2756afb220 *)
(* 537771ac60abe908c98514560f16c2a8). Here the observation may be any even     *)
(* measurable map. Product transfer reuses tuple_prod_map; mixing reuses      *)
(* mixture. The squared-coordinate example is independent of fitting.       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section shifts.
Context {R : realType} {d : nat}.

Definition row_symmetric_law (P : probability 'rV[R]_d R) : Prop :=
  forall A : set 'rV[R]_d,
    measurable A -> P ((fun x => - x) @^-1` A) = P A.

Lemma measurable_row_shift (m : 'rV[R]_d) :
  measurable_fun setT (fun x : 'rV[R]_d => x + m).
Proof. by apply: measurable_addmx => //; exact: measurable_cst. Qed.

Definition row_shift (m : 'rV[R]_d) : {mfun 'rV[R]_d >-> 'rV[R]_d} :=
  HB.pack (fun x : 'rV[R]_d => x + m)
    (isMeasurableFun.Build _ _ _ _ _ (measurable_row_shift m)).

Definition row_shift_law (P : probability 'rV[R]_d R) (m : 'rV[R]_d) :=
  distribution P (row_shift m).

Lemma row_shift_lawE (P : probability 'rV[R]_d R) m A :
  row_shift_law P m A = P [set x | A (x + m)].
Proof. by rewrite /row_shift_law /distribution /pushforward /row_shift. Qed.

Lemma symmetric_shift_even (P : probability 'rV[R]_d R) m
    e (U : measurableType e) (f : {mfun 'rV[R]_d >-> U}) A :
  row_symmetric_law P -> (forall x, f (- x) = f x) -> measurable A ->
  row_shift_law P (- m) (f @^-1` A) =
  row_shift_law P m (f @^-1` A).
Proof.
move=> symP evenf mA; rewrite !row_shift_lawE.
have mfA : measurable (f @^-1` A) := measurable_funPTI f mA.
have mB : measurable ((row_shift m) @^-1` (f @^-1` A)) :=
  measurable_funPTI (row_shift m) mfA.
rewrite -(symP _ mB); congr (P _); apply/funext => x /=.
have -> : - x + m = - (x - m) by rewrite opprB addrC.
by rewrite evenf.
Qed.

Definition sign_shift_weights (w : R) (b : bool) := if b then w else 1 - w.

Lemma sign_shift_weightsP w : 0 <= w <= 1 ->
  mixture_weights (sign_shift_weights w).
Proof.
move=> /andP[w0 w1]; split.
  by case=> /=; rewrite /sign_shift_weights // subr_ge0.
by rewrite /sign_shift_weights big_bool /=; ring.
Qed.

Definition sign_shift_law (P : probability 'rV[R]_d R) m w
    (hw : 0 <= w <= 1) :=
  mixture (fun b : bool => row_shift_law P (if b then m else - m))
    (sign_shift_weightsP hw).

Lemma sign_shift_lawE (P : probability 'rV[R]_d R) m w
    (hw : 0 <= w <= 1) A :
  sign_shift_law P m hw A =
  (w%:E * row_shift_law P m A +
    (1 - w)%:E * row_shift_law P (- m) A)%E.
Proof. by rewrite /sign_shift_law mixtureE big_bool. Qed.

Lemma symmetric_sign_shift_even (P : probability 'rV[R]_d R) m w
    (hw : 0 <= w <= 1) e (U : measurableType e)
    (f : {mfun 'rV[R]_d >-> U}) A :
  row_symmetric_law P -> (forall x, f (- x) = f x) -> measurable A ->
  sign_shift_law P m hw (f @^-1` A) =
  row_shift_law P m (f @^-1` A).
Proof.
move=> symP evenf mA; rewrite sign_shift_lawE
  (symmetric_shift_even m symP evenf mA).
have mfA : measurable (f @^-1` A) := measurable_funPTI f mA.
pose p := fine (row_shift_law P m (f @^-1` A)).
have hp : row_shift_law P m (f @^-1` A) = p%:E.
  by rewrite /p fineK //; exact: fin_num_measure.
rewrite hp -!EFinM -EFinD; congr EFin.
by ring.
Qed.

Lemma symmetric_sign_shift_tuple (P : probability 'rV[R]_d R) m w
    (hw : 0 <= w <= 1) e (U : measurableType e)
    (f : {mfun 'rV[R]_d >-> U}) n (A : set (n.-tuple U)) :
  row_symmetric_law P -> (forall x, f (- x) = f x) -> measurable A ->
  tuple_prod (fun=> sign_shift_law P m hw) n
    (tuple_map (fun _ => f) @^-1` A) =
  tuple_prod (fun=> row_shift_law P m) n
    (tuple_map (fun _ => f) @^-1` A).
Proof.
move=> symP evenf mA.
pose Q := distribution (row_shift_law P m) f.
have mf (i : nat) : measurable_fun setT (fun x => f x) := measurable_funPT f.
have h1 (i : nat) B : measurable B ->
    Q B = sign_shift_law P m hw (f @^-1` B).
  move=> mB; symmetry; exact: symmetric_sign_shift_even symP evenf mB.
have h2 (i : nat) B : measurable B -> Q B = row_shift_law P m (f @^-1` B).
  by [].
rewrite -(tuple_prod_map mf h1 mA).
exact: tuple_prod_map mf h2 mA.
Qed.

Lemma measurable_row_outer :
  measurable_fun setT (fun x : 'rV[R]_d => x^T *m x).
Proof. by apply: measurable_mulmx => //; exact: measurable_trmx. Qed.

Definition row_outer : {mfun 'rV[R]_d >-> 'M[R]_d} :=
  HB.pack (fun x : 'rV[R]_d => x^T *m x)
    (isMeasurableFun.Build _ _ _ _ _ measurable_row_outer).

Lemma row_outerN x : row_outer (- x) = row_outer x.
Proof.
by rewrite /row_outer /= [(- x)^T]linearN /= mulNmx mulmxN opprK.
Qed.

Lemma symmetric_sign_shift_outer (P : probability 'rV[R]_d R) m w
    (hw : 0 <= w <= 1) n (A : set (n.-tuple 'M[R]_d)) :
  row_symmetric_law P -> measurable A ->
  tuple_prod (fun=> sign_shift_law P m hw) n
    (tuple_map (fun _ => row_outer) @^-1` A) =
  tuple_prod (fun=> row_shift_law P m) n
    (tuple_map (fun _ => row_outer) @^-1` A).
Proof.
move=> symP mA; exact: symmetric_sign_shift_tuple symP row_outerN mA.
Qed.

(* An application-independent example: each squared coordinate has the same
   distribution under the sign mixture as under a single translation. *)
Lemma symmetric_sign_shift_square_coordinate
    (P : probability 'rV[R]_d R) m w (hw : 0 <= w <= 1)
    (j : 'I_d) (A : set R) :
  row_symmetric_law P -> measurable A ->
  sign_shift_law P m hw [set x | A (x 0 j ^+ 2)] =
  row_shift_law P m [set x | A (x 0 j ^+ 2)].
Proof.
move=> symP mA.
have mf : measurable_fun setT (fun x : 'rV[R]_d => x 0 j ^+ 2).
  by apply: measurable_funX; exact: measurable_mxentry.
pose f : {mfun 'rV[R]_d >-> R} :=
  HB.pack (fun x : 'rV[R]_d => x 0 j ^+ 2)
    (isMeasurableFun.Build _ _ _ _ _ mf).
have evenf x : f (- x) = f x by rewrite /f /= mxE sqrrN.
exact: symmetric_sign_shift_even symP evenf mA.
Qed.

End shifts.
