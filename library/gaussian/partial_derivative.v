From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import interval topology normedtype landau derive.
From GaussianAnalysis Require Import gauss_ibp.

(**md**************************************************************************)
(* # Continuous partial derivatives                                           *)
(*                                                                            *)
(* A function F : 'rV[R]_n -> R whose partial derivatives                     *)
(* 'D_(delta_mx 0 j) F exist everywhere and are continuous is differentiable, *)
(* and its differential is v |-> \sum_j v 0 j * 'D_(delta_mx 0 j) F x         *)
(* (differentiable_partials, diff_partials). The proof writes the increment   *)
(* of F as a sum of increments along the coordinates and applies the mean     *)
(* value theorem to each (mean_value_coord, partials_expansion).              *)
(*                                                                            *)
(* ```                                                                        *)
(*   rV_prefix k h == the row vector h with its coordinates of index k or     *)
(*                    more set to 0                                           *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section partials.
Context {R : realType} {n : nat}.
Variables (F : 'rV[R]_n -> R) (DF : 'I_n -> 'rV[R]_n -> R).
Hypothesis F_partial : forall j x, is_derive x (delta_mx 0 j) F (DF j x).
Hypothesis DF_cont : forall j, continuous (DF j).

(* The first k coordinates of h, the others set to 0. *)
Definition rV_prefix k (h : 'rV[R]_n) : 'rV[R]_n :=
  \row_j (if (j < k)%N then h 0 j else 0).

Lemma rV_prefix0 h : rV_prefix 0 h = 0.
Proof. by apply/rowP => j; rewrite !mxE. Qed.

Lemma rV_prefixn h : rV_prefix n h = h.
Proof. by apply/rowP => j; rewrite !mxE ltn_ord. Qed.

Lemma rV_prefixS h (k : 'I_n) :
  rV_prefix k.+1 h = h 0 k *: delta_mx 0 k + rV_prefix k h.
Proof.
apply/rowP => j; rewrite !mxE /= ltnS leq_eqVlt.
case: (eqVneq j k) => [->|jk]; first by rewrite eqxx ltnn /= mulr1 addr0.
by move: jk; rewrite -val_eqE /= => /negbTE ->; rewrite /= mulr0 add0r.
Qed.

Lemma rV_prefix_norm (h : 'rV[R]_n) (k : 'I_n) (c : R) : `|c| <= `|h 0 k| ->
  `|c *: delta_mx 0 k + rV_prefix k h| <= `|h|.
Proof.
move=> ck.
have -> : `|c *: delta_mx 0 k + rV_prefix k h| =
    \big[maxr/0]_ij `|(c *: delta_mx 0 k + rV_prefix k h) ij.1 ij.2|.
  by rewrite -mx_normrE.
apply: bigmax_le => [|[i j] _] /=; first exact: normr_ge0.
rewrite (ord1 i) !mxE /=; case: (eqVneq j k) => [->|jk].
  by rewrite ltnn mulr1 addr0 (le_trans ck) // mx_norm_entry_le.
by rewrite mulr0 add0r; case: (j < k)%N; rewrite ?normr0 ?mx_norm_entry_le.
Qed.

Lemma mean_value_coord (x : 'rV[R]_n) (j : 'I_n) (t : R) :
  exists2 c : R, `|c| <= `|t| &
    F (t *: delta_mx 0 j + x) - F x = t * DF j (c *: delta_mx 0 j + x).
Proof.
pose g (s : R) := F (s *: delta_mx 0 j + x).
have gd (s : R) : is_derive s 1 g (DF j (s *: delta_mx 0 j + x)).
  apply: (is_derive_transfer (G := F) (b := s *: delta_mx 0 j + x)
    (w := delta_mx 0 j)).
  by move=> h; rewrite /g addrA -scalerDl [h%:A]mulr1.
have gc : continuous g.
  move=> s; apply: differentiable_continuous; apply/derivable1_diffP.
  by case: (gd s).
have g0 : g 0 = F x by rewrite /g scale0r add0r.
case: (ltgtP t 0) => [t0|t0|->].
- have [c cI E] := @MVT R g (fun s => DF j (s *: delta_mx 0 j + x)) t 0 t0
    (fun s _ => gd s) (continuous_subspaceT gc).
  exists c; first by move: cI; rewrite in_itv /= => /andP[c1 c2];
    rewrite !ltr0_norm //; lra.
  by rewrite -g0; move: E; rewrite sub0r mulrN /g => E; lra.
- have [c cI E] := @MVT R g (fun s => DF j (s *: delta_mx 0 j + x)) 0 t t0
    (fun s _ => gd s) (continuous_subspaceT gc).
  exists c; first by move: cI; rewrite in_itv /= => /andP[c1 c2];
    rewrite !gtr0_norm //; lra.
  by rewrite -g0; move: E; rewrite subr0 /g => E; lra.
- exists 0; first by rewrite normr0.
  by rewrite scale0r add0r subrr mul0r.
Qed.

Lemma partials_expansion (x : 'rV[R]_n) :
  (fun h : 'rV[R]_n => F (h + x) - F x - \sum_(j < n) h 0 j * DF j x)
    =o_ (0 : 'rV[R]_n) id.
Proof.
apply/eqoP => eps eps0; set e' := eps / (n%:R + 1).
have n10 : 0 < n%:R + 1 :> R by rewrite ltr_pwDr.
have e'0 : 0 < e' by rewrite divr_gt0.
(* Near x, every partial derivative is within e' of its value at x. *)
have : \forall y \near x, forall j : 'I_n, `|DF j x - DF j y| < e'.
  apply: (filter_forall (nbhs_filter x)) => j.
  by have /cvgrPdist_lt := @DF_cont j x; apply.
move=> /nbhs_ballP [d d0 Hd].
have : \forall h \near (0 : 'rV[R]_n), `|h| < d by exact: nbhs0_lt.
apply: filterS => h hd.
(* The increment of F is the sum of its increments along the coordinates. *)
pose u k := F (rV_prefix k h + x).
have tele : F (h + x) - F x = \sum_(k < n) (u k.+1 - u k).
  rewrite -(big_mkord xpredT (fun k => u k.+1 - u k)) telescope_sumr //.
  by rewrite /u rV_prefixn rV_prefix0 add0r.
have step (k : 'I_n) : `|u k.+1 - u k - h 0 k * DF k x| <= `|h| * e'.
  have [c ck E] := mean_value_coord (rV_prefix k h + x) k (h 0 k).
  have -> : u k.+1 = F (h 0 k *: delta_mx 0 k + (rV_prefix k h + x)).
    by rewrite /u rV_prefixS addrA.
  rewrite [u k]/u E -mulrBr normrM.
  apply: ler_pM => //; first exact: mx_norm_entry_le.
  have : ball x d (c *: delta_mx 0 k + (rV_prefix k h + x)).
    rewrite -ball_normE /= addrA opprD addrCA subrr addr0 normrN.
    exact: (le_lt_trans (rV_prefix_norm ck) hd).
  by move=> /Hd /(_ k) /ltW; rewrite distrC.
rewrite tele -sumrB (le_trans (ler_norm_sum _ _ _)) //.
apply: (le_trans (ler_sum _ (fun k _ => step k))).
rewrite sumr_const card_ord -mulr_natl; have h0 := normr_ge0 h.
have : n%:R * e' <= eps by rewrite /e' mulrA ler_pdivrMr //; nra.
nra.
Qed.

Lemma partials_linear (x : 'rV[R]_n) :
  linear (fun v : 'rV[R]_n => \sum_(j < n) v 0 j * DF j x).
Proof.
move=> a u v /=; rewrite /GRing.scale /= mulr_sumr -big_split /=.
by apply: eq_bigr => j _; rewrite !mxE mulrDl mulrA.
Qed.

Lemma continuous_partials_linear (x : 'rV[R]_n) :
  continuous (fun v : 'rV[R]_n => \sum_(j < n) v 0 j * DF j x).
Proof.
apply: continuous_sum => j v.
exact: (cvgM (@coord_continuous R 1 n 0 j v) (cvg_cst _)).
Qed.

Theorem partials_diff_differentiable (x : 'rV[R]_n) :
  differentiable F x /\
  'd F x = (fun v : 'rV[R]_n => \sum_(j < n) v 0 j * DF j x) :> ('rV[R]_n -> R).
Proof.
pose L : {linear 'rV[R]_n -> R} :=
  HB.pack (fun v : 'rV[R]_n => \sum_(j < n) v 0 j * DF j x)
    (GRing.isLinear.Build _ _ _ _ _ (partials_linear x)).
have cL : continuous L := @continuous_partials_linear x.
have E : F \o shift x = cst (F x) + L +o_ (0 : 'rV[R]_n) id.
  apply/eqaddoP; have /eqoP := partials_expansion x.
  move=> H eps eps0; apply: filterS (H eps eps0) => h /=.
  by rewrite opprD addrA.
have dL : 'd F x = L :> ('rV[R]_n -> R) := diff_unique cL E.
split; last exact: dL.
by apply/diff_locallyP; rewrite dL; split.
Qed.

Corollary differentiable_partials (x : 'rV[R]_n) : differentiable F x.
Proof. by case: (partials_diff_differentiable x). Qed.

Corollary diff_partials (x : 'rV[R]_n) :
  'd F x = (fun v : 'rV[R]_n => \sum_(j < n) v 0 j * DF j x) :> ('rV[R]_n -> R).
Proof. by case: (partials_diff_differentiable x). Qed.

End partials.
