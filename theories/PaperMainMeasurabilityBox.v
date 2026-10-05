(* Compactness of coordinate boxes in 'rV[R]_N and cluster points of
   sequences: the shared prefix of the measurability proofs of the events of
   paper_main_results. Internal proof module of the MathComp-Analysis port,
   written on 30 September 2026 by a Claude Code session (Fable 5.1).
   Nothing here is reviewed or accepted.

   pm_seg m is the segment [-m, m] as the set of x with - m <= x <= m; it is
   closed (closed_ge, closed_le) and compact (transported from
   segment_compact of MathComp-Analysis by subclosed_compact). pm_box m is the
   set of row vectors with every entry in pm_seg m, compact by rV_compact.
   pm_box_cluster: a sequence with all terms in pm_box m has a cluster point
   p in pm_box m in the sense that every neighbourhood of p contains terms of
   arbitrarily large index (compact read through the cluster points of the
   image filter of the sequence). pm_cluster_near turns this into: for g
   continuous at p and eps > 0, terms of arbitrarily large index have
   |g p - g (u k)| < eps. pm_inv_small and pm_inv_mono are the arithmetic of
   the tolerances 1 / (k + 1), and pm_le_of_eps closes a bound from all
   epsilons.

   Stable interface for other modules: the definitions pm_seg, pm_box and the
   lemmas pm_seg_closed, pm_seg_sub_segment, pm_seg_compact, pm_box_compact,
   pm_box_cluster, pm_cluster_near, pm_inv_small, pm_inv_mono, pm_le_of_eps,
   all inside Section compact_box with Variable N : nat (the vector length)
   as their first explicit argument. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum archimedean interval matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.

Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section compact_box.
Variable N : nat.
Local Notation V := 'rV[R]_N.

(* The segment [-m, m] and the box of row vectors with entries in it. *)
Definition pm_seg (m : R) : set R := [set x : R | - m <= x <= m].

Definition pm_box (m : R) : set V := [set v : V | forall k, pm_seg m (v ord0 k)].

Lemma pm_seg_closed (m : R) : closed (pm_seg m).
Proof.
rewrite (_ : pm_seg m = [set x : R | - m <= x] `&` [set x : R | x <= m]).
  by apply/seteqP; split=> x /=; [move/andP|case=> ? ?; apply/andP].
by apply: closedI; [exact: closed_ge|exact: closed_le].
Qed.

Lemma pm_seg_sub_segment (m : R) : pm_seg m `<=` `[- m, m].
Proof. by move=> x /=; rewrite in_itv/=. Qed.

Lemma pm_seg_compact (m : R) : compact (pm_seg m).
Proof.
exact (subclosed_compact (pm_seg_closed m) (@segment_compact _ (- m) m) (pm_seg_sub_segment m)).
Qed.

Lemma pm_box_compact (m : R) : compact (pm_box m).
Proof. by apply: (@rV_compact _ _ (fun=> pm_seg m)) => _; exact: pm_seg_compact. Qed.

(* The cluster point of a sequence in the box: every neighbourhood of it
   contains terms of arbitrarily large index. *)
Lemma pm_box_cluster (u : nat -> V) (m : R) :
  (forall k, pm_box m (u k)) ->
  exists p : V, pm_box m p /\
    forall B : set V, nbhs p B -> forall k0 : nat, exists k, (k0 <= k)%nat /\ B (u k).
Proof.
move=> um.
have uA : (u @ \oo) (pm_box m).
  have h : \forall k \near \oo, pm_box m (u k) by exact: nearW.
  by rewrite nearE in h.
have [p [pK clp]] := pm_box_compact m (u @ \oo) _ uA.
exists p; split=> // B pB k0.
have HA : (u @ \oo) [set y | exists k, (k0 <= k)%nat /\ y = u k].
  by apply: filterS (nbhs_infty_ge k0) => k /= k0k; exists k.
have [y [[k [k0k ->]] By]] := clp _ _ HA pB.
by exists k.
Qed.

(* A frequently attained neighbourhood of a value. *)
Lemma pm_cluster_near (u : nat -> V) (p : V) (g : V -> R) (eps : R) :
  {for p, continuous g} -> 0 < eps ->
  (forall B : set V, nbhs p B -> forall k0 : nat, exists k, (k0 <= k)%nat /\ B (u k)) ->
  forall k0 : nat, exists k, (k0 <= k)%nat /\ `|g p - g (u k)| < eps.
Proof.
move=> gc eps0 clp k0.
have : nbhs p [set v | `|g p - g v| < eps] := cvgr_dist_lt (V := R^o) g (g p) gc eps eps0.
move=> H; have [k [k0k Hk]] := clp _ (H _) k0.
by exists k.
Qed.

(* 1/(k+1) below any positive real, for some k. *)
Lemma pm_inv_small (eps : R) : 0 < eps -> exists k : nat, k.+1%:R^-1 < eps.
Proof.
move=> eps0; exists (Num.bound eps^-1).
have e0 : 0 < eps^-1 by rewrite invr_gt0.
have h := archi_boundP (ltW e0).
rewrite invf_plt ?posrE ?ltr0n//.
by apply: (lt_le_trans h); rewrite ler_nat.
Qed.

Lemma pm_inv_mono (k1 k : nat) : (k1 <= k)%nat -> k.+1%:R^-1 <= (k1.+1%:R^-1 : R).
Proof. by move=> k1k; rewrite lef_pV2 ?posrE ?ltr0n// ler_nat. Qed.

Lemma pm_le_of_eps (a b : R) : (forall eps, 0 < eps -> a < b + eps) -> a <= b.
Proof.
move=> H; rewrite leNgt; apply/negP => ba.
have := H (a - b); rewrite subr_gt0 => /(_ ba).
by rewrite addrCA subrr addr0 ltxx.
Qed.

End compact_box.
