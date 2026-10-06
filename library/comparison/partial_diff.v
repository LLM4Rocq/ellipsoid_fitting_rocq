From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun landau.
From GaussianAnalysis.gaussian Require Import gauss_ibp.

(**md**************************************************************************)
(* # Differentiability from continuous partial derivatives                    *)
(*                                                                            *)
(* A real function F on row vectors 'rV[R]_n whose partial derivatives DF j,  *)
(* the derivatives along delta_mx 0 j, exist everywhere and are continuous is *)
(* differentiable at every point (partial_differentiable), and its            *)
(* differential at x is the linear map h |-> \sum_j h_j DF j x                *)
(* (partial_diffE). The proof applies the mean value theorem to F along one   *)
(* coordinate at a time (partial_mvt) and uses the continuity of the partial  *)
(* derivatives at x (partial_approx).                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*   partial_lin x h == \sum_j h_j DF j x, the candidate differential at x    *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section partial_differentiable.
Context {R : realType} {n : nat}.
Variables (F : 'rV[R]_n -> R) (DF : 'I_n -> 'rV[R]_n -> R).
Hypothesis dF : forall j x, is_derive x (delta_mx 0 j) F (DF j x).
Hypothesis cDF : forall j, continuous (DF j).

(* The partial sums of h along the coordinates: the first k coordinates
   of h, the others 0. *)
Let hpart (h : 'rV[R]_n) (k : nat) : 'rV[R]_n :=
  \row_j (if (j < k)%N then h 0 j else 0).

Let hpart0 h : hpart h 0 = 0.
Proof. by apply/rowP => j; rewrite !mxE. Qed.

Let hpartn h : hpart h n = h.
Proof. by apply/rowP => j; rewrite !mxE ltn_ord. Qed.

Lemma partial_derive_line (z : 'rV[R]_n) (j : 'I_n) (t : R) :
  is_derive t 1 (fun s => F (z + s *: delta_mx 0 j))
    (DF j (z + t *: delta_mx 0 j)).
Proof.
apply: (is_derive_transfer (G := F) (b := z + t *: delta_mx 0 j)
  (w := delta_mx 0 j)) => h; congr F.
have -> : h%:A = h by rewrite -[RHS]mulr1.
by rewrite scalerDl addrCA.
Qed.

Lemma partial_mvt (z : 'rV[R]_n) (j : 'I_n) (a : R) :
  exists2 c, `|c| <= `|a| &
    F (z + a *: delta_mx 0 j) - F z = DF j (z + c *: delta_mx 0 j) * a.
Proof.
pose g s := F (z + s *: delta_mx 0 j).
have gd (s : R) : is_derive s 1 g (DF j (z + s *: delta_mx 0 j)).
  exact: partial_derive_line.
have gc (s : R) : {for s, continuous g}.
  by apply: differentiable_continuous; apply/derivable1_diffP; case: (gd s).
have cg (u v : R) : {within `[u, v], continuous g}.
  by apply: continuous_subspaceT => s; exact: gc.
have [a0|a0] := leP 0 a.
  have [c /andP[c0 ca] E] := MVT_segment a0 (fun s _ => gd s) (cg 0 a).
  exists c; first by rewrite !ger0_norm// (le_trans c0).
  by move: E; rewrite /g scale0r addr0 subr0.
have [c /andP[ac c0] E] := MVT_segment (ltW a0) (fun s _ => gd s) (cg a 0).
exists c; first by rewrite !ler0_norm ?lerN2// ltW.
move: E; rewrite /g scale0r addr0 => /(congr1 (fun x => - x)).
by rewrite opprB sub0r mulrN opprK.
Qed.

Let hpartS (h : 'rV[R]_n) (k : 'I_n) :
  hpart h k.+1 = hpart h k + h 0 k *: delta_mx 0 k.
Proof.
apply/rowP => j; rewrite !mxE ltnS leq_eqVlt.
case: (eqVneq j k) => [->|jk]; first by rewrite eqxx ltnn /= mulr1 add0r.
by rewrite (inj_eq val_inj) (negbTE jk) /= mulr0 addr0.
Qed.

Let hpart_norm (h : 'rV[R]_n) (k : 'I_n) (c : R) : `|c| <= `|h 0 k| ->
  `|hpart h k + c *: delta_mx 0 k| <= `|h|.
Proof.
move=> ch.
have -> : forall v : 'rV[R]_n, `|v| = \big[maxr/0]_ij `|v ij.1 ij.2|.
  by move=> v; rewrite -mx_normrE.
apply: bigmax_le => // -[i j] _.
rewrite /= (ord1 i) !mxE; have hj := mx_norm_entry_le h 0 j.
case: (eqVneq j k) => [->|jk].
  rewrite ltnn eqxx /= add0r mulr1.
  exact: (le_trans ch (mx_norm_entry_le h 0 k)).
rewrite andbF mulr0 addr0; case: ifP => // _.
by rewrite normr0 (le_trans (normr_ge0 _) hj).
Qed.

Definition partial_lin (x h : 'rV[R]_n) : R := \sum_j h 0 j * DF j x.

Lemma partial_approx (x : 'rV[R]_n) (e : R) : 0 < e ->
  \forall h \near (0 : 'rV[R]_n),
    `|F (h + x) - F x - partial_lin x h| <= e * `|h|.
Proof.
move=> e0; pose e' := e / n.+1%:R.
have e'0 : 0 < e' by rewrite divr_gt0// ltr0n.
have Hc : \forall y \near x, forall k : 'I_n, `|DF k x - DF k y| <= e'.
  apply: (@filter_forall _ 'I_n (fun k y => `|DF k x - DF k y| <= e') (nbhs x)).
  move=> k; have Hk : DF k @ x --> DF k x by exact: cDF.
  by move/cvgrPdist_le : Hk => /(_ e' e'0).
have [d d0 Hd] := (nbhs_ballP x _).1 Hc.
near=> h.
have hd : `|h| < d by near: h; apply: (@nbhs0_lt _ 'rV[R]_n d d0).
pose u (k : nat) := F (x + hpart h k).
have Fu : F (h + x) - F x = \sum_(k < n) (u k.+1 - u k).
  rewrite -(big_mkord xpredT (fun k => u k.+1 - u k)) telescope_sumr// /u.
  congr (F _ - F _).
    by rewrite addrC; congr (_ + _); apply/esym/hpartn.
  by rewrite -[LHS]addr0; congr (_ + _); apply/esym/hpart0.
have Hk (k : 'I_n) : `|u k.+1 - u k - h 0 k * DF k x| <= `|h 0 k| * e'.
  have [c ch E] := partial_mvt (x + hpart h k) k (h 0 k).
  rewrite /u hpartS addrA E [h 0 k * _]mulrC -mulrBl normrM mulrC ler_wpM2l//.
  have : ball x d (x + hpart h k + c *: delta_mx 0 k).
    rewrite -ball_normE /= -addrA opprD addrA subrr add0r normrN.
    exact: le_lt_trans (hpart_norm ch) hd.
  by move=> /Hd /(_ k); rewrite distrC.
rewrite Fu /partial_lin -sumrB.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: (@le_trans _ _ (\sum_(i < n) `|h 0 i| * e')).
  by apply: ler_sum => i _; exact: Hk.
apply: (@le_trans _ _ (\sum_(i < n) `|h| * e')).
  by apply: ler_sum => i _; apply: ler_wpM2r; [exact: ltW|exact: mx_norm_entry_le].
rewrite sumr_const card_ord -mulr_natl /e'.
have hn : n%:R / n.+1%:R <= 1 :> R by rewrite ler_pdivrMr ?ltr0n// mul1r ler_nat.
have h0 := normr_ge0 h.
have -> : n%:R * (`|h| * (e / n.+1%:R)) = n%:R / n.+1%:R * (e * `|h|) by ring.
by rewrite ler_piMl// mulr_ge0// ltW.
Unshelve. all: by end_near.
Qed.

Lemma partial_lin_is_linear (x : 'rV[R]_n) : linear (partial_lin x : 'rV[R]_n -> R^o).
Proof.
move=> a u v; rewrite /partial_lin.
change (\sum_j (a *: u + v) 0 j * DF j x =
  a * \sum_j u 0 j * DF j x + \sum_j v 0 j * DF j x).
rewrite mulr_sumr -big_split /=.
by apply: eq_bigr => j _; rewrite !mxE mulrDl mulrA.
Qed.

Let continuous_partial_lin (x : 'rV[R]_n) : continuous (partial_lin x : 'rV[R]_n -> R^o).
Proof.
have cs (s : seq 'I_n) :
    continuous (fun h : 'rV[R]_n => (\sum_(j <- s) h 0 j * DF j x : R^o)).
  elim: s => [|j s IH]; first by under eq_fun do rewrite big_nil; exact: cst_continuous.
  under eq_fun do rewrite big_cons.
  move=> y; apply: (@continuousD _ _ _ (fun h : 'rV[R]_n => h 0 j * DF j x : R^o)).
    apply: (@continuousM _ _ (fun h : 'rV[R]_n => h 0 j) (cst (DF j x))).
      exact: coord_continuous.
    exact: cst_continuous.
  exact: IH.
exact: cs.
Qed.

Let partial_diff_aux x :
  'd (F : 'rV[R]_n -> R^o) x = partial_lin x :> ('rV[R]_n -> R^o) /\
  differentiable (F : 'rV[R]_n -> R^o) x.
Proof.
pose lM := GRing.isLinear.Build _ _ _ _ _ (partial_lin_is_linear x).
pose L : {linear 'rV[R]_n -> R^o} := HB.pack (partial_lin x : 'rV[R]_n -> R^o) lM.
have cL : continuous L := @continuous_partial_lin x.
have oL : (F : 'rV[R]_n -> R^o) \o shift x = cst (F x) + L +o_ 0 id.
  apply/eqaddoP => e e0; apply: filterS (partial_approx x e0) => h /=.
  by rewrite opprD addrA.
have dL := diff_unique cL oL.
by split => //; apply/diff_locallyP; rewrite dL.
Qed.

Theorem partial_diffE x :
  'd (F : 'rV[R]_n -> R^o) x = partial_lin x :> ('rV[R]_n -> R^o).
Proof. by have [] := partial_diff_aux x. Qed.

Theorem partial_differentiable x :
  differentiable (F : 'rV[R]_n -> R^o) x.
Proof. by have [] := partial_diff_aux x. Qed.

End partial_differentiable.
