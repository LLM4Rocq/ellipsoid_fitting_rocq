From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype realfun measure.
From mathcomp Require Import lebesgue_stieltjes_measure measurable_realfun.
From GaussianAnalysis.gaussian Require Import measurable_matrix.

(**md**************************************************************************)
(* # Measurability of an infimum of continuous functions                      *)
(*                                                                            *)
(* Let D be a nonempty set of indices and F i a continuous real function on  *)
(* a topological space. If the values {F i x | i in D} are bounded below     *)
(* for each x, their infimum has open strict sublevels. The lower bound may  *)
(* depend on x, and D need not be countable or compact.                      *)
(*                                                                            *)
(* - infimum_sublevelE writes each strict sublevel as the union of the       *)
(*   strict sublevels of the members of the family.                          *)
(* - open_infimum_sublevel proves that this union is open.              *)
(* - measurable_infimum_mx gives Borel measurability when the          *)
(*   domain consists of real matrices, including row and column vectors.    *)
(*                                                                            *)
(* Measurability follows from an arbitrary union of open sets, not from     *)
(* an arbitrary union of measurable sets. The example takes the infimum of  *)
(* (X_00 - t)^2 + X_00 over all real t. Its value is X_00, so its natural    *)
(* lower bound depends on the parameter and can be negative.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section sublevels.
Context {R : realType} {T I : Type}.
Variables (D : set I) (F : I -> T -> R).

Lemma infimum_sublevelE : D !=set0 ->
  (forall x, has_lbound [set F i x | i in D]) ->
  forall a : R,
    [set x | inf [set F i x | i in D] < a] =
    \bigcup_(i in D) [set x | F i x < a].
Proof.
move=> [i0 Di0] lb a; apply/seteqP; split=> x /=.
- have S0 : [set F i x | i in D] !=set0 by exists (F i0 x), i0.
  move=> /(inf_lt S0) [v [i Di <-] hia].
  by exists i.
- move=> [i Di hia].
  have hi : inf [set F j x | j in D] <= F i x.
    apply: (ge_inf (lb x)); by exists i.
  exact: le_lt_trans hi hia.
Qed.
End sublevels.

Section continuous_sublevels.
Context {R : realType} {T : topologicalType} {I : Type}.
Variables (D : set I) (F : I -> T -> R).

Lemma open_infimum_sublevel : D !=set0 ->
  (forall i, D i -> continuous (F i)) ->
  (forall x, has_lbound [set F i x | i in D]) ->
  forall a : R, open [set x | inf [set F i x | i in D] < a].
Proof.
move=> D0 Fc lb a; rewrite (infimum_sublevelE D0 lb).
apply: bigcup_open => i Di.
have /continuousP cf := Fc i Di.
change (open ((F i) @^-1` [set r : R | r < a])).
apply: cf.
exact: open_lt.
Qed.
End continuous_sublevels.

Section matrix_measurability.
Context {R : realType} {m n : nat} {I : Type}.
Variables (D : set I) (F : I -> 'M[R]_(m,n) -> R).

Lemma measurable_infimum_mx : D !=set0 ->
  (forall i, D i -> continuous (F i)) ->
  (forall X, has_lbound [set F i X | i in D]) ->
  measurable_fun [set: 'M[R]_(m,n)] (fun X => inf [set F i X | i in D]).
Proof.
move=> D0 Fc lb.
apply: (measurability _ (RGenInftyO.measurableE R)).
move=> _ [_ [a ->] <-]; rewrite setTI preimage_itvNyo.
apply: open_measurable_mx.
exact: open_infimum_sublevel D0 Fc lb a.
Qed.
End matrix_measurability.

Section shifted_square_example.
Context {R : realType} {m n : nat}.

Lemma infimum_shifted_square (X : 'M[R]_(m.+1,n.+1)) :
  inf [set (X 0 0 - t) ^+ 2 + X 0 0 | t in [set: R]] = X 0 0.
Proof.
pose S := [set (X 0 0 - t) ^+ 2 + X 0 0 | t in [set: R]].
have Sm : S (X 0 0).
  by exists (X 0 0) => //; rewrite subrr expr0n add0r.
have lb : lbound S (X 0 0).
  move=> _ [t _ <-].
  by rewrite lerDr sqr_ge0.
have Slb : has_lbound S by exists (X 0 0).
have S0 : S !=set0 by exists (X 0 0).
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (ge_inf Slb Sm).
- exact: (lb_le_inf S0 lb).
Qed.

Lemma measurable_infimum_shifted_square :
  measurable_fun [set: 'M[R]_(m.+1,n.+1)]
    (fun X => inf [set (X 0 0 - t) ^+ 2 + X 0 0 | t in [set: R]]).
Proof.
apply: (eq_measurable_fun (fun X : 'M[R]_(m.+1,n.+1) => X 0 0)).
- by move=> X _; rewrite infimum_shifted_square.
- exact: measurable_mxentry.
Qed.
End shifted_square_example.
