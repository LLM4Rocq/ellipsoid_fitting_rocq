From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.

(**md**************************************************************************)
(* # Continuity of a parameter integral                                       *)
(*                                                                            *)
(* cvg_seqP is the sequential criterion for the limit of a function at a     *)
(* point of a pseudometric space: f x tends to l as x tends to x0 as soon as  *)
(* f (u n) tends to l for every sequence u that tends to x0.                  *)
(*                                                                            *)
(* continuity_under_integral_at: if f x y is, for every y in B, continuous   *)
(* in x at x0, and `|f x y| <= g y for x in a neighbourhood of x0 and y in B, *)
(* with g integrable on B, then x |-> \int[mu]_(y in B) f x y is continuous   *)
(* at x0, by dominated convergence along sequences. MathComp-Analysis states  *)
(* this for a real parameter in an open interval (continuity_under_integral); *)
(* here the parameter ranges over a pseudometric space, such as 'rV[R]_n.     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section cvg_seqP.
Context {R : realType} {X : pseudoMetricType R} {V : pseudoMetricType R}.

Lemma cvg_seqP (h : X -> V) (x0 : X) (l : V) :
  (forall u : nat -> X, u n @[n --> \oo] --> x0 -> h (u n) @[n --> \oo] --> l) ->
  h x @[x --> x0] --> l.
Proof.
move=> H; apply/cvg_ballP => e e0; apply: contrapT => nbh.
have hn n : exists x, ball x0 n.+1%:R^-1 x /\ ~ ball l e (h x).
  apply: contrapT => /forallNP nx; apply: nbh.
  apply/nbhs_ballP; exists n.+1%:R^-1; first by rewrite /= invr_gt0.
  by move=> x bx; apply: contrapT => nhx; exact: (nx x (conj bx nhx)).
have [u uP] := choice hn.
have ux0 : u n @[n --> \oo] --> x0.
  apply/cvg_ballP => d d0; near=> n.
  apply: (le_ball (ltW _) (uP n).1).
  by near: n; exact: (near_infty_natSinv_lt (PosNum d0)).
have /cvg_ballP/(_ e e0)[N _ /(_ N (leqnn N))] := H u ux0.
exact: (uP N).2.
Unshelve. all: by end_near.
Qed.

End cvg_seqP.

Section continuity_under_integral_at.
Context {R : realType} {X : pseudoMetricType R} d {Y : measurableType d}.
Variable mu : {measure set Y -> \bar R}.
Variables (f : X -> Y -> R) (B : set Y) (x0 : X) (U : set X) (g : Y -> R).
Hypothesis mB : measurable B.
Hypothesis Ux0 : nbhs x0 U.
Hypothesis int_f : forall x, U x -> mu.-integrable B (EFin \o f x).
Hypothesis cf : forall y, B y -> {for x0, continuous (f ^~ y)}.
Hypothesis int_g : mu.-integrable B (EFin \o g).
Hypothesis g_ub : forall x, U x -> forall y, B y -> `|f x y| <= g y.

(* A sequence converges when a shift of it does. *)
Let cvg_shiftnW {V : pseudoMetricType R} (v : nat -> V) (l : V) N :
  v (n + N)%N @[n --> \oo] --> l -> v @ \oo --> l.
Proof.
move=> /cvg_ballP H; apply/cvg_ballP => e e0.
have [M _ hM] := H e e0; exists (M + N)%N => // n /= hn.
have Nn : (N <= n)%N := leq_trans (leq_addl _ _) hn.
have := hM (n - N)%N; rewrite subnK //; apply.
by rewrite /= -(leq_add2r N) subnK.
Qed.

Lemma continuity_under_integral_at :
  {for x0, continuous (fun x => \int[mu]_(y in B) f x y)}.
Proof.
apply: cvg_seqP => u ux0.
have [N _ NU] : \forall n \near \oo, U (u n) by exact: (ux0 _ Ux0).
have Ux0' : U x0 := nbhs_singleton Ux0.
have uN : u (n + N)%N @[n --> \oo] --> x0.
  by apply: cvg_comp ux0; exact: cvg_addnr.
apply: (@cvg_shiftnW R _ _ N); rewrite /Rintegral /=.
apply: fine_cvg; rewrite fineK; first exact: (integrable_fin_num mB (int_f Ux0')).
apply: (@dominated_cvg _ _ _ mu B mB (fun n y => (f (u (n + N)%N) y)%:E) _
  (EFin \o g)).
- by move=> n; apply/(measurable_int mu)/int_f/NU; rewrite /= leq_addl.
- move=> y By; apply: cvg_EFin; first exact: nearW.
  by apply: cvg_comp uN (cf By).
- by move=> y _.
- exact: int_g.
- move=> n y By; rewrite /= lee_fin; apply: g_ub => //.
  by apply/NU; rewrite /= leq_addl.
Qed.

End continuity_under_integral_at.
