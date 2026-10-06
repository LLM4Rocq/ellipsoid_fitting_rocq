(* Values of a continuous function at a cluster point, and continuity of
   the coordinate polynomials on 'rV[R]_N: the second part of the compactness
   toolkit for the measurability proofs of the events of paper_main_results.
   It builds on PaperMainMeasurabilityBox.

   For g continuous at the cluster point p of a sequence u: if
   g (u k) <= c + a/(k+1) for all k then g p <= c; if c - a/(k+1) <= g (u k)
   then c <= g p; if |g (u k)| <= a/(k+1) then g p = 0; if g (u k) = c then
   g p = c. Then the continuity of coordinates, constants, sums, differences
   and products of continuous real functions on 'rV[R]_N. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum archimedean interval matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From EllipsoidFitting Require Import PaperMainMeasurabilityBox.

Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section cluster_values.
Variable N : nat.
Local Notation V := 'rV[R]_N.

(* Values along the cluster point: bounds with a tolerance a / (k + 1). *)
Lemma pm_cluster_value_le (u : nat -> V) (p : V) (g : V -> R) (c a : R) :
  {for p, continuous g} -> 0 <= a ->
  (forall B : set V, nbhs p B -> forall k0 : nat, exists k, (k0 <= k)%nat /\ B (u k)) ->
  (forall k, g (u k) <= c + a * k.+1%:R^-1) -> g p <= c.
Proof.
move=> gc a0 clp le; apply: pm_le_of_eps => eps eps0.
have e20 : 0 < eps / 2 by rewrite divr_gt0.
have a1 : 0 < a + 1 by rewrite addrC; exact: ltr_wpDr a0 ltr01.
have ea0 : 0 < eps / 2 / (a + 1) by rewrite divr_gt0.
have [k1 Hk1] := pm_inv_small _ ea0.
have [k [k1k Hk]] := pm_cluster_near _ _ _ _ _ gc e20 clp k1.
have hk := pm_inv_mono _ _ k1k.
have gk := le k.
move: Hk; rewrite ltr_norml => /andP[_ Hk].
have gk2 : g p < g (u k) + eps / 2 by rewrite addrC -ltrBlDr.
have ak : a * k.+1%:R^-1 <= eps / 2.
  apply: (le_trans (ler_wpM2l a0 hk)).
  apply: (le_trans (ler_wpM2l a0 (ltW Hk1))).
  rewrite -[leRHS](divfK (lt0r_neq0 a1)) [X in _ <= X]mulrC.
  by apply: ler_wpM2r; [exact: ltW|rewrite lerDl ler01].
apply: (lt_le_trans gk2); rewrite [in leRHS](splitr eps) addrA lerD2r.
by apply: (le_trans gk); rewrite lerD2l.
Qed.

Lemma pm_cluster_value_ge (u : nat -> V) (p : V) (g : V -> R) (c a : R) :
  {for p, continuous g} -> 0 <= a ->
  (forall B : set V, nbhs p B -> forall k0 : nat, exists k, (k0 <= k)%nat /\ B (u k)) ->
  (forall k, c - a * k.+1%:R^-1 <= g (u k)) -> c <= g p.
Proof.
move=> gc a0 clp ge.
have gc' : {for p, continuous (fun v => - g v)}.
  by first [exact: (continuousN (V := R^o) gc) | exact: (@continuousN _ R^o _ _ _ gc)].
have : - g p <= - c.
  apply: (pm_cluster_value_le _ _ _ _ _ gc' a0 clp) => k.
  by rewrite lerNl opprD opprK; exact: ge.
by rewrite lerNl opprK.
Qed.

Lemma pm_cluster_value_zero (u : nat -> V) (p : V) (g : V -> R) (a : R) :
  {for p, continuous g} -> 0 <= a ->
  (forall B : set V, nbhs p B -> forall k0 : nat, exists k, (k0 <= k)%nat /\ B (u k)) ->
  (forall k, `|g (u k)| <= a * k.+1%:R^-1) -> g p = 0.
Proof.
move=> gc a0 clp small; apply/le_anti/andP; split.
- apply: (pm_cluster_value_le _ _ _ _ _ gc a0 clp) => k; rewrite add0r.
  by have := small k; rewrite ler_norml => /andP[].
- apply: (pm_cluster_value_ge _ _ _ _ _ gc a0 clp) => k; rewrite sub0r.
  by have := small k; rewrite ler_norml => /andP[].
Qed.

Lemma pm_cluster_value_eq (u : nat -> V) (p : V) (g : V -> R) (c : R) :
  {for p, continuous g} ->
  (forall B : set V, nbhs p B -> forall k0 : nat, exists k, (k0 <= k)%nat /\ B (u k)) ->
  (forall k, g (u k) = c) -> g p = c.
Proof.
move=> gc clp eq; apply/le_anti/andP; split.
- by apply: (pm_cluster_value_le _ _ _ _ _ gc (lexx 0) clp) => k; rewrite eq mul0r addr0.
- by apply: (pm_cluster_value_ge _ _ _ _ _ gc (lexx 0) clp) => k; rewrite eq mul0r subr0.
Qed.

(* Continuity of the coordinate polynomials on V. *)
Lemma pm_continuous_coord (k : 'I_N) (p : V) : {for p, continuous (fun v : V => v ord0 k)}.
Proof. exact: coord_continuous. Qed.

Lemma pm_continuous_cst (c : R) (p : V) : {for p, continuous (fun _ : V => c)}.
Proof. exact: cst_continuous. Qed.

Lemma pm_continuous_add (f g : V -> R) (p : V) :
  {for p, continuous f} -> {for p, continuous g} ->
  {for p, continuous (fun v => f v + g v)}.
Proof. by move=> cf cg; first [exact: (continuousD (V := R^o) cf cg) | exact: (@continuousD _ R^o _ _ _ _ cf cg)]. Qed.

Lemma pm_continuous_sub (f g : V -> R) (p : V) :
  {for p, continuous f} -> {for p, continuous g} ->
  {for p, continuous (fun v => f v - g v)}.
Proof. by move=> cf cg; first [exact: (continuousB (V := R^o) cf cg) | exact: (@continuousB _ R^o _ _ _ _ cf cg)]. Qed.

Lemma pm_continuous_mul (f g : V -> R) (p : V) :
  {for p, continuous f} -> {for p, continuous g} ->
  {for p, continuous (fun v => f v * g v)}.
Proof. by move=> cf cg; first [exact: (continuousM cf cg) | exact: (@continuousM R _ _ _ _ cf cg)]. Qed.

Lemma pm_continuous_sum (I : Type) (s : seq I) (h : I -> V -> R) (p : V) :
  (forall i, {for p, continuous (h i)}) ->
  {for p, continuous (fun v => \sum_(i <- s) h i v)}.
Proof.
move=> hc; elim: s => [|i s IH].
- rewrite (_ : (fun v => _) = (fun _ => 0)).
    by apply/funext => v; rewrite big_nil.
  exact: pm_continuous_cst.
- rewrite (_ : (fun v => _) = (fun v => h i v + \sum_(j <- s) h j v)).
    by apply/funext => v; rewrite big_cons.
  exact: pm_continuous_add.
Qed.

End cluster_values.


