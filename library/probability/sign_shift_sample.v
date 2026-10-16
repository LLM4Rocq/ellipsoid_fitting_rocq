From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype measure lebesgue_measure.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows mixture.
From GaussianAnalysis.probability Require Import symmetric_shift independent_row_signs symmetrization.

(**md**************************************************************************)
(* # Samples from opposite shifts of a symmetric law                          *)
(*                                                                            *)
(* Let P be a centrally symmetric law of row vectors (row_symmetric_law).     *)
(* A measurable event of n-tuples of rows that is unchanged when the signs    *)
(* of any of the rows are changed (tuple_row_sign) has the same               *)
(* probability for n independent rows of law sign_shift_law P m hw, the       *)
(* mixture with weights w and 1 - w of the translations of P by m and by      *)
(* -m, as for n independent rows of law row_shift_law P m. The                *)
(* coordinates of a row need not be independent, and the weights 0 and 1      *)
(* and the empty sample are included. This extends the identity of            *)
(* symmetric_shift.v for tuples of outer products, with no measurable         *)
(* factorization through the outer products.                                  *)
(*                                                                            *)
(* ```                                                                        *)
(* tuple_row_shift m x == the tuple of the rows of x, each translated by m    *)
(* ```                                                                        *)
(*                                                                            *)
(* - symmetric_sign_shift_sample: the equality for such events.               *)
(* - symmetric_sign_shift_observation: the same for the law of a              *)
(*   measurable map of the sample that is unchanged by the signs of the       *)
(*   rows.                                                                    *)
(* - symmetric_sign_shift_sample_coordinate_square, the example: the          *)
(*   square of one coordinate of one row, a statistic unrelated to            *)
(*   fitting.                                                                 *)
(*                                                                            *)
(* Source: the elementary sign coupling in doc/shifted-gaussian.tex.          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section sample_shifts.
Context {R : realType} {d : nat}.

Definition tuple_row_shift {n} (m : 'rV[R]_d) (x : n.-tuple 'rV[R]_d) :=
  tuple_map (fun _ (z : 'rV[R]_d) => z+m) x.

Lemma measurable_tuple_row_shift n (m : 'rV[R]_d) :
  measurable_fun [set: n.-tuple 'rV[R]_d] (tuple_row_shift m).
Proof. by apply: measurable_tuple_map => i; exact: measurable_row_shift. Qed.

Lemma tuple_row_shift_law (P : probability 'rV[R]_d R) (m : 'rV[R]_d)
    n (A : set (n.-tuple 'rV[R]_d)) : measurable A ->
  tuple_prod (fun=> row_shift_law P m) n A =
    tuple_prod (fun=> P) n (tuple_row_shift m @^-1` A).
Proof.
move=> mA; apply: tuple_prod_map => //.
by move=> i; exact: measurable_row_shift.
Qed.

Lemma sign_component_even_event (P : probability 'rV[R]_d R)
    (m : 'rV[R]_d) n (s : n.-tuple bool) (A : set (n.-tuple 'rV[R]_d)) :
  row_symmetric_law P -> measurable A ->
  (forall t x, A (tuple_row_sign t x) = A x) ->
  tuple_prod (fun i => row_shift_law P (if nth true s i then m else -m)) n A =
    tuple_prod (fun=> row_shift_law P m) n A.
Proof.
move=> symP mA evenA.
pose g i (z : 'rV[R]_d) := z+(if nth true s i then m else -m).
have mg i : measurable_fun setT (g i) := measurable_row_shift _.
have hmap i B : measurable B ->
    row_shift_law P (if nth true s i then m else -m) B = P (g i @^-1` B).
  by move=> mB; rewrite row_shift_lawE.
rewrite (tuple_prod_map mg hmap mA) tuple_row_shift_law //.
have mB : measurable (tuple_row_shift m @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_tuple_row_shift.
rewrite -(independent_tuple_row_sign s (fun _ _ => symP) mB).
congr (tuple_prod _ _ _); apply/funext => x /=.
rewrite -(evenA s (tuple_map g x)).
congr (A _); apply: eq_from_tnth => i.
rewrite /tuple_row_sign /tuple_row_shift /tuple_map !tnth_mktuple /g.
case: (nth true s i); rewrite /rademacher ?scale1r //.
by rewrite !scaleN1r opprB addrC.
Qed.

Theorem symmetric_sign_shift_sample (P : probability 'rV[R]_d R)
    (m : 'rV[R]_d) w (hw : 0 <= w <= 1) n
    (A : set (n.-tuple 'rV[R]_d)) :
  row_symmetric_law P -> measurable A ->
  (forall s x, A (tuple_row_sign s x) = A x) ->
  tuple_prod (fun=> sign_shift_law P m hw) n A =
    tuple_prod (fun=> row_shift_law P m) n A.
Proof.
move=> symP mA evenA.
rewrite /sign_shift_law (@tuple_prod_mixture _ _ R _
  (sign_shift_weights w)
  (fun b : bool => row_shift_law P (if b then m else -m))
  (sign_shift_weightsP hw) true n A mA).
have hcomponent (s : n.-tuple bool) :=
  @sign_component_even_event P m n s A symP mA evenA.
under eq_bigr do rewrite hcomponent.
pose q := fine (tuple_prod (fun=> row_shift_law P m) n A).
have hq : tuple_prod (fun=> row_shift_law P m) n A = q%:E.
  by rewrite /q fineK //; exact: fin_num_measure.
rewrite hq.
have hW := mixture_weights_prod n (sign_shift_weightsP hw).
rewrite (eq_bigr (fun s : n.-tuple bool =>
  ((\prod_(i<n) sign_shift_weights w (tnth s i))*q)%:E)).
  by move=> s _; rewrite EFinM.
by rewrite sumEFin -mulr_suml (mixture_weights_sum hW) mul1r.
Qed.

Corollary symmetric_sign_shift_observation (P : probability 'rV[R]_d R)
    (m : 'rV[R]_d) w (hw : 0 <= w <= 1) n
    disp (T : measurableType disp) (f : n.-tuple 'rV[R]_d -> T)
    (A : set T) :
  row_symmetric_law P -> measurable_fun setT f ->
  (forall s x, f (tuple_row_sign s x) = f x) -> measurable A ->
  tuple_prod (fun=> sign_shift_law P m hw) n (f @^-1` A) =
    tuple_prod (fun=> row_shift_law P m) n (f @^-1` A).
Proof.
move=> symP mf evenf mA; apply: symmetric_sign_shift_sample => //.
- by rewrite -[X in measurable X]setTI; exact: mf.
- by move=> s x; rewrite /preimage /= evenf.
Qed.

Corollary symmetric_sign_shift_sample_coordinate_square
    (P : probability 'rV[R]_d R) (m : 'rV[R]_d) w (hw : 0 <= w <= 1)
    n (i : 'I_n) (j : 'I_d) (A : set R) :
  row_symmetric_law P -> measurable A ->
  tuple_prod (fun=> sign_shift_law P m hw) n
    [set x : n.-tuple 'rV[R]_d | A ((tnth x i) 0 j ^+2)] =
  tuple_prod (fun=> row_shift_law P m) n
    [set x : n.-tuple 'rV[R]_d | A ((tnth x i) 0 j ^+2)].
Proof.
move=> symP mA; apply: symmetric_sign_shift_observation => //.
- apply: measurable_funX.
  exact: measurableT_comp (measurable_mxentry 0 j) (measurable_tnth i).
- move=> s x; rewrite /tuple_row_sign /tuple_map tnth_mktuple.
  by case: (nth true s i); rewrite /rademacher ?scale1r // scaleN1r mxE sqrrN.
Qed.

End sample_shifts.
