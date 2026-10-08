From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import euclidean real_spectral.

(**md**************************************************************************)
(* # Projections onto closed convex sets and Moreau's decomposition           *)
(*                                                                            *)
(* Lemma 5.1 of Koehler and Sohn (arXiv 2608.27372, lines 4894-4921; Bauschke *)
(* and Combettes, section 6.3) in 'rV[R]_N with the Frobenius inner product   *)
(* <x, y> = mxdot x y and |x|^2 = mxdot x x. K is a nonempty closed convex    *)
(* set and C a nonempty closed convex cone: x + t (y - x) is in K for x, y    *)
(* in K and 0 <= t <= 1, and a y is in C for y in C and a >= 0.               *)
(*                                                                            *)
(* ```                                                                        *)
(*   proj K z == the nearest point of K to z, if it exists (xget)             *)
(*   polar C == the polar cone [set u | <u, y> <= 0 for every y in C]         *)
(* ```                                                                        *)
(*                                                                            *)
(* - proj_exists: a nonempty closed set has a nearest point to every z.       *)
(* - proj_variational: p in K is nearest to z iff <z - p, y - p> <= 0 for     *)
(*   every y in K; the nearest point is unique (proj_unique), and projP       *)
(*   gives K (proj K z) and the variational inequality.                       *)
(* - proj_nonexpansive: |proj K z - proj K z'| <= |z - z'|.                   *)
(* - cone_projP: p = proj C z iff p is in C, z - p is in polar C and          *)
(*   <z - p, p> = 0.                                                          *)
(* - moreau, Lemma 5.1: z = proj C z + proj (polar C) z with                  *)
(*   <proj C z, proj (polar C) z> = 0, hence (moreau_norm)                    *)
(*   |z|^2 = |proj C z|^2 + |proj (polar C) z|^2.                             *)
(* - cone_proj_support, (eq:cone-projection-support):                         *)
(*   sup_(y in C, |y| <= 1) <z, y> = |proj C z|.                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section projection.
Context {R : realType} {N : nat}.
Implicit Types (K C : set 'rV[R]_N) (x y z p q u : 'rV[R]_N).

Definition proj K z : 'rV[R]_N := xget 0 [set p | K p /\
  forall y, K y -> mxdot (z - p) (z - p) <= mxdot (z - y) (z - y)].

Definition polar C : set 'rV[R]_N := [set u | forall y, C y -> mxdot u y <= 0].

Lemma continuous_dist2 z :
  continuous (fun y : 'rV[R]_N => mxdot (z - y) (z - y)).
Proof.
have -> : (fun y : 'rV[R]_N => mxdot (z - y) (z - y)) =
    (fun y => ((z - y) *m 1%:M *m (z - y)^T) 0 0).
  by apply/funext => y; rewrite mulmx1 -mxdot_rowE.
move=> y; apply: (@continuous_comp _ _ _ (fun y : 'rV[R]_N => z - y)
  (fun w : 'rV[R]_N => (w *m 1%:M *m w^T) 0 0)).
  apply: (@cvgB _ _ _ (nbhs y) _ (fun=> z) id z y).
    exact: cvg_cst.
  exact: cvg_id.
exact: continuous_form.
Qed.

(* A bound by t b for every 0 < t <= 1 is a bound by 0. *)
Lemma le0_small (a b : R) : (forall t : R, 0 < t <= 1 -> a <= t * b) ->
  a <= 0.
Proof.
move=> h; rewrite leNgt; apply/negP => a0.
have c0 : 0 < 2 * (`|b| + 1) by rewrite mulr_gt0 // ltr_wpDl.
pose t := Num.min 1 (a / (2 * (`|b| + 1))).
have t0 : 0 < t by rewrite lt_min ltr01 divr_gt0.
have t1 : t <= 1 by rewrite ge_min lexx.
have tc : t * (2 * (`|b| + 1)) <= a.
  by rewrite -ler_pdivlMr // ge_min lexx orbT.
have := h t; rewrite t0 t1 => /(_ isT) ha.
have : t * b <= t * `|b| by apply: ler_wpM2l; [exact: ltW|exact: ler_norm].
have : 0 <= t * `|b| by rewrite mulr_ge0 // ltW.
nra.
Qed.

(* A nonempty closed set has a nearest point to every z. *)
Lemma proj_exists K z : closed K -> K !=set0 -> exists2 p, K p &
  forall y, K y -> mxdot (z - p) (z - p) <= mxdot (z - y) (z - y).
Proof.
move=> Kc [y0 Ky0].
set r := mxdot (z - y0) (z - y0).
(* the points of K at most as far as y0, a compact set *)
pose A := [set y | K y /\ mxdot (z - y) (z - y) <= r].
have An : A !=set0 by exists y0.
have Ac : closed A.
  apply: closedI => //.
  have h := (continuous_closedP _).1 (@continuous_dist2 z) _ (@closed_le R r).
  by move: h; congr closed.
have nf (y : 'rV[R]_N) : `|y| <= frobenius y.
  have -> : `|y| = \big[maxr/0]_ij `|y ij.1 ij.2| by rewrite -mx_normrE.
  apply: bigmax_le => [|ij _]; first exact: frobenius_ge0.
  exact: frobenius_entry.
have Ab : bounded_set A.
  exists (frobenius z + Num.sqrt r); split; first exact: num_real.
  move=> M hM y [Ky hy].
  apply: ltW; apply: le_lt_trans hM.
  apply: le_trans (nf y) _.
  have -> : y = z - (z - y) by rewrite opprB addrC subrK.
  apply: le_trans (frobeniusB _ _) _.
  rewrite lerD2l /frobenius.
  by rewrite ler_sqrt // (le_trans (mxdot_ge0 _) hy).
have Acp := bounded_closed_compact Ab Ac.
have [c cA cmin] := compact_EVT_min An Acp
  (continuous_subspaceT (@continuous_dist2 z)).
move: cA; rewrite inE => -[Kc' hc].
exists c => // y Ky.
have [hy|hy] := leP (mxdot (z - y) (z - y)) r.
  by apply: cmin; rewrite inE.
by apply: le_trans hc _; exact: ltW.
Qed.

End projection.

Section convex_projection.
Context {R : realType} {N : nat}.
Variable K : set 'rV[R]_N.
Hypotheses (Kc : closed K) (K0 : K !=set0).
Hypothesis Kcvx : forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
  K (x + t *: (y - x)).

(* The variational characterization of the nearest point. *)
Lemma proj_variational (z p : 'rV[R]_N) : K p ->
  (forall y, K y -> mxdot (z - p) (z - p) <= mxdot (z - y) (z - y)) <->
  (forall y, K y -> mxdot (z - p) (y - p) <= 0).
Proof.
have expand (u v : 'rV[R]_N) (t : R) : mxdot (u - t *: v) (u - t *: v) =
    mxdot u u - 2 * t * mxdot u v + t ^+ 2 * mxdot v v.
  by rewrite !mxdotBl !mxdotBr !mxdotZl !mxdotZr (mxdotC v u); ring.
move=> Kp; split => [hmin y Ky|hvar y Ky].
  (* move from p toward y *)
  apply: (le0_small (b := mxdot (y - p) (y - p) / 2)) => t /andP[t0 t1].
  have t01 : 0 <= t <= 1 by rewrite (ltW t0) t1.
  have := hmin _ (Kcvx Kp Ky t01).
  have -> : z - (p + t *: (y - p)) = (z - p) - t *: (y - p).
    by rewrite opprD addrA.
  rewrite expand => h.
  have h2 : 2 * t * mxdot (z - p) (y - p) <=
      t ^+ 2 * mxdot (y - p) (y - p) by lra.
  have t2 : 0 < 2 * t by rewrite mulr_gt0.
  rewrite -(ler_pM2l t2); apply: le_trans h2 _.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have -> : z - y = (z - p) - 1 *: (y - p) by rewrite scale1r opprB addrA subrK.
rewrite expand expr1n mul1r mulr1.
have := hvar y Ky; have := mxdot_ge0 (y - p).
lra.
Qed.

Lemma proj_unique (z p q : 'rV[R]_N) : K p -> K q ->
  (forall y, K y -> mxdot (z - p) (y - p) <= 0) ->
  (forall y, K y -> mxdot (z - q) (y - q) <= 0) -> p = q.
Proof.
move=> Kp Kq hp hq.
have h1 := hp q Kq; have h2 := hq p Kp.
have e : mxdot (p - q) (p - q) = mxdot (z - q) (p - q) + mxdot (z - p) (q - p).
  by rewrite !mxdotBl !mxdotBr; ring.
have : mxdot (p - q) (p - q) <= 0 by rewrite e; lra.
by move=> h; apply/eqP; rewrite -subr_eq0 -mxdot_eq0 eq_le h mxdot_ge0.
Qed.

Lemma projP (z : 'rV[R]_N) : K (proj K z) /\
  forall y, K y -> mxdot (z - proj K z) (y - proj K z) <= 0.
Proof.
have [p Kp hp] := proj_exists z Kc K0.
have : [set p | K p /\ forall y, K y ->
    mxdot (z - p) (z - p) <= mxdot (z - y) (z - y)] (proj K z).
  by apply: xgetPex; exists p.
move=> [Kq hq]; split => //.
exact: (proj_variational z Kq).1 hq.
Qed.

Lemma proj_eq (z p : 'rV[R]_N) : K p ->
  (forall y, K y -> mxdot (z - p) (y - p) <= 0) -> proj K z = p.
Proof.
move=> Kp hp; have [Kq hq] := projP z.
exact: proj_unique Kq Kp hq hp.
Qed.

Lemma proj_nonexpansive (z z' : 'rV[R]_N) :
  frobenius (proj K z - proj K z') <= frobenius (z - z').
Proof.
have [Kp hp] := projP z; have [Kq hq] := projP z'.
set p := proj K z in Kp hp *; set q := proj K z' in Kq hq *.
have h1 := hp q Kq; have h2 := hq p Kp.
have key : mxdot (p - q) (p - q) <= mxdot (z - z') (p - q).
  have e : mxdot (z - z') (p - q) - mxdot (p - q) (p - q) =
      - (mxdot (z - p) (q - p) + mxdot (z' - q) (p - q)).
    by rewrite !mxdotBl !mxdotBr; ring.
  by rewrite -subr_ge0 e oppr_ge0; lra.
have [->|pq] := eqVneq (p - q) 0; first by rewrite frobenius0 frobenius_ge0.
have f0 : 0 < frobenius (p - q) by rewrite frobenius_gt0.
rewrite -(ler_pM2r f0) -expr2 frobenius_sqr.
apply: le_trans key _; exact: ler_mxdot.
Qed.

End convex_projection.

Section cone_projection.
Context {R : realType} {N : nat}.
Variable C : set 'rV[R]_N.
Hypotheses (Cc : closed C) (C0 : C 0).
Hypothesis Ccvx : forall x y (t : R), C x -> C y -> 0 <= t <= 1 ->
  C (x + t *: (y - x)).
Hypothesis Ccone : forall y (a : R), C y -> 0 <= a -> C (a *: y).

Lemma polar_closed : closed (polar C).
Proof.
have -> : polar C = \bigcap_(y in C) [set u | mxdot u y <= 0].
  by apply/seteqP; split => u hu y Cy; exact: hu y Cy.
apply: closed_bigI => y Cy.
have hc : continuous (fun u : 'rV[R]_N => mxdot u y).
  have -> : (fun u : 'rV[R]_N => mxdot u y) =
      (fun u => \sum_j u 0 j * y 0 j).
    by apply/funext => u; rewrite /mxdot big_ord1.
  apply: (@continuous_big R^o _ +%R 0 xpredT (@add_continuous R^o) _ _
    (fun j (u : 'rV[R]_N) => u 0 j * y 0 j)) => j _ u.
  apply: (continuousM (s := fun v : 'rV[R]_N => v 0 j) (t := fun=> y 0 j)).
    exact: coord_continuous.
  exact: cst_continuous.
have h := (continuous_closedP _).1 hc _ (@closed_le R 0).
by move: h; congr closed.
Qed.

Lemma polar_convex x y (t : R) : polar C x -> polar C y -> 0 <= t <= 1 ->
  polar C (x + t *: (y - x)).
Proof.
move=> px py /andP[t0 t1] w Cw.
rewrite mxdotDl mxdotZl mxdotBl.
have := px w Cw; have := py w Cw.
by nra.
Qed.

Lemma polar0 : polar C 0.
Proof. by move=> y _; rewrite mxdot0l. Qed.

(* p is the projection of z onto C iff z - p is in the polar cone and is
   orthogonal to p. *)
Lemma cone_projP (z p : 'rV[R]_N) : C p ->
  proj C z = p <-> polar C (z - p) /\ mxdot (z - p) p = 0.
Proof.
have Cn : C !=set0 by exists 0.
move=> Cp; split => [hp|[pz pp]].
  have [_ hv] := projP Cc Cn Ccvx z; rewrite hp in hv.
  have h0 := hv 0 C0.
  have h2 := hv (2 *: p) (Ccone Cp (ler0n _ 2)).
  rewrite sub0r mxdotNr in h0.
  have e2 : 2 *: p - p = p by rewrite scaler_nat mulr2n addrK.
  rewrite e2 in h2.
  have e : mxdot (z - p) p = 0 by apply/eqP; rewrite eq_le h2 -oppr_le0 h0.
  split => // y Cy.
  by have := hv y Cy; rewrite mxdotBr e subr0.
apply: proj_eq => // y Cy.
by rewrite mxdotBr pp subr0; exact: pz.
Qed.

(* Lemma 5.1 of Koehler and Sohn. *)
Theorem moreau (z : 'rV[R]_N) :
  z = proj C z + proj (polar C) z /\
  mxdot (proj C z) (proj (polar C) z) = 0.
Proof.
have Cn : C !=set0 by exists 0.
have [Cp hp] := projP Cc Cn Ccvx z.
have [pz pp] := (cone_projP z Cp).1 (erefl _).
have Pn : polar C !=set0 by exists 0; exact: polar0.
(* z - proj C z satisfies the variational inequality of the polar cone *)
have hq : proj (polar C) z = z - proj C z.
  apply: (proj_eq polar_closed Pn polar_convex pz) => u pu.
  have e : z - (z - proj C z) = proj C z by rewrite opprB addrC subrK.
  rewrite e mxdotBr (mxdotC _ (z - proj C z)) pp subr0 mxdotC.
  exact: pu _ Cp.
rewrite hq; split; first by rewrite addrC subrK.
by rewrite mxdotC pp.
Qed.

Lemma moreau_norm (z : 'rV[R]_N) :
  mxdot z z = mxdot (proj C z) (proj C z) +
              mxdot (proj (polar C) z) (proj (polar C) z).
Proof.
have [ez oz] := moreau z.
rewrite {1 2}ez mxdotDl !mxdotDr oz.
by rewrite (mxdotC (proj (polar C) z)) oz addr0 add0r.
Qed.

(* (eq:cone-projection-support) *)
Theorem cone_proj_support (z : 'rV[R]_N) :
  sup [set mxdot z y | y in [set y | C y /\ mxdot y y <= 1]] =
  frobenius (proj C z).
Proof.
have Cn : C !=set0 by exists 0.
have Pn : polar C !=set0 by exists 0; exact: polar0.
have [Cp _] := projP Cc Cn Ccvx z.
have [Pq _] := projP polar_closed Pn polar_convex z.
have [ez oz] := moreau z.
set p := proj C z in Cp ez oz *.
set q := proj (polar C) z in Pq ez oz *.
set S := [set _ | _ in _].
(* <z, y> = <p, y> + <q, y> <= |p| for y in C with |y| <= 1 *)
have ub : ubound S (frobenius p).
  move=> _ [y [Cy y1] <-].
  rewrite ez mxdotDl.
  have hq := Pq y Cy.
  have fy : frobenius y <= 1 by rewrite /frobenius -sqrtr1 ler_sqrt.
  have hp : mxdot p y <= frobenius p.
    apply: le_trans (ler_mxdot p y) _.
    by rewrite -[X in _ <= X]mulr1 ler_wpM2l // frobenius_ge0.
  lra.
(* attained at p / |p|, or at 0 if p = 0 *)
have mem : S (frobenius p).
  have [p0|p0] := eqVneq p 0.
    exists 0; first by split; [exact: C0|rewrite mxdot0l].
    rewrite /mxdot big1 ?p0 ?frobenius0 // => i _.
    by rewrite big1 // => j _; rewrite mxE mulr0.
  have fp : 0 < frobenius p by rewrite frobenius_gt0.
  have fne : frobenius p != 0 by rewrite gt_eqF.
  exists ((frobenius p)^-1 *: p).
    split; first by apply: Ccone Cp _; rewrite invr_ge0 ltW.
    rewrite mxdotZl mxdotZr -frobenius_sqr.
    by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
  rewrite mxdotZr ez mxdotDl (mxdotC q p) oz addr0 -frobenius_sqr.
  by field.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: ge_sup => //; exists (frobenius p).
by apply: ub_le_sup => //; exists (frobenius p).
Qed.

End cone_projection.
