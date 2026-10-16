(* Reindexing asymptotic statements for varying parameter families.
   At dimension q the parameters may have an arbitrary dependent type T q.
   An admissible baseline fills dimensions that are absent from the image
   of the reindexing map. The map must tend to infinity, but need not be
   monotone or injective. Repeated dimensions may carry different data.

   family_sequence_limit u a: the explicit epsilon definition of u -> a.
   family_cofinal p: p(d) tends to infinity as d tends to infinity.
   family_eventually_reindex transfers eventual predicates. In particular,
   the predicate may assert existence of a measurable exceptional cover;
   measurability of its failure set is not needed. family_limit_reindex
   specializes this to convergence of a real statistic to zero.

   The proof selects one failing instance in each nonempty failing fiber,
   using the baseline elsewhere. Finite prefixes have bounded images, so
   the selected family's density has the prescribed limit. Applying the
   original family theorem eliminates all sufficiently large bad fibers. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

Definition family_sequence_limit {R : realType} (u : nat -> R) (a : R) : Prop :=
  forall eps : R, 0 < eps -> exists D : nat, forall d : nat,
    (D <= d)%N -> `|u d - a| < eps.

Lemma family_prefix_escape (p : nat -> nat) (D : nat) :
  exists B : nat, forall d : nat, (B <= p d)%N -> (D <= d)%N.
Proof.
elim: D => [|D [B hB]].
  by exists 0%N.
exists (maxn B (p D).+1) => d.
rewrite geq_max => /andP[dB dD].
have Dd := hB d dB.
move: Dd; rewrite leq_eqVlt => /orP[/eqP Dd|//].
by move: dD; rewrite -Dd ltnn.
Qed.

Lemma family_spliced_limit {R : realType}
    (p : nat -> nat) (u v w : nat -> R) (l : R) :
  family_sequence_limit u l -> family_sequence_limit v l ->
  (forall q, w q = u q \/ exists d, p d = q /\ w q = v d) ->
  family_sequence_limit w l.
Proof.
move=> hu hv hw eps eps0.
have [Du hDu] := hu eps eps0.
have [Dv hDv] := hv eps eps0.
have [B hB] := family_prefix_escape p Dv.
exists (maxn Du B) => q.
rewrite geq_max => /andP[qDu qB].
case: (hw q) => [->|[d [pd ->]]]; first exact: hDu.
apply: hDv; apply: hB.
by rewrite pd.
Qed.


Lemma family_bad_fiber_selector
    (T : nat -> Type) (V : Type)
    (A : forall q, T q -> Prop)
    (stat : forall q, T q -> V)
    (Good : forall q, T q -> Prop)
    (base : forall q, T q)
    (p : nat -> nat) (x : forall d, T (p d)) :
  (forall q, A q (base q)) ->
  (forall d, A (p d) (x d)) ->
  exists s : forall q, T q,
    [/\ (forall q, A q (s q)),
      (forall q, stat q (s q) = stat q (base q) \/
        exists d, p d = q /\ stat q (s q) = stat (p d) (x d)) &
      forall q, Good q (s q) -> forall d, p d = q -> Good (p d) (x d)].
Proof.
move=> Ab Ax.
have H q : exists t : T q,
    [/\ A q t,
      (stat q t = stat q (base q) \/
        exists d, p d = q /\ stat q t = stat (p d) (x d)) &
      Good q t -> forall d, p d = q -> Good (p d) (x d)].
  have [[d [pdq bad]]|none] :=
    pselect (exists d, p d = q /\ ~ Good (p d) (x d)).
  - subst q; exists (x d); split; first exact: Ax.
    + right; by exists d.
    + by move=> good; exfalso; exact: bad good.
  - exists (base q); split; first exact: Ab.
    + by left.
    + move=> _ d pdq.
      have [good|bad] := pselect (Good (p d) (x d)); first exact: good.
      exfalso; apply: none; by exists d.
pose s q := projT1 (cid (H q)).
have hs q := projT2 (cid (H q)).
exists s; split.
- by move=> q; have [h _ _] := hs q.
- by move=> q; have [_ h _] := hs q.
- by move=> q; have [_ _ h] := hs q.
Qed.

Definition family_cofinal (p : nat -> nat) : Prop :=
  forall Q : nat, exists D : nat, forall d : nat, (D <= d)%N -> (Q <= p d)%N.

Theorem family_eventually_reindex {R : realType}
    (T : nat -> Type) (A : forall q, T q -> Prop)
    (stat : forall q, T q -> R) (Good : forall q, T q -> Prop)
    (base : forall q, T q) (alpha : R)
    (p : nat -> nat) (x : forall d, T (p d)) :
  (forall q, A q (base q)) ->
  family_sequence_limit (fun q => stat q (base q)) alpha ->
  (forall s : forall q, T q, (forall q, A q (s q)) ->
    family_sequence_limit (fun q => stat q (s q)) alpha ->
    exists Q : nat, forall q, (Q <= q)%N -> Good q (s q)) ->
  family_cofinal p -> (forall d, A (p d) (x d)) ->
  family_sequence_limit (fun d => stat (p d) (x d)) alpha ->
  exists D : nat, forall d, (D <= d)%N -> Good (p d) (x d).
Proof.
move=> Ab hb hall hp Ax hx.
have [s [As hs Gs]] := @family_bad_fiber_selector T R A stat Good base p x Ab Ax.
have hstat := family_spliced_limit hb hx hs.
have [Q hQ] := hall s As hstat.
have [D hD] := hp Q.
exists D => d dD.
exact: Gs (p d) (hQ (p d) (hD d dD)) d erefl.
Qed.

Theorem family_limit_reindex {R : realType}
    (T : nat -> Type) (A : forall q, T q -> Prop)
    (stat bad : forall q, T q -> R)
    (base : forall q, T q) (alpha : R)
    (p : nat -> nat) (x : forall d, T (p d)) :
  (forall q, A q (base q)) ->
  family_sequence_limit (fun q => stat q (base q)) alpha ->
  (forall s : forall q, T q, (forall q, A q (s q)) ->
    family_sequence_limit (fun q => stat q (s q)) alpha ->
    family_sequence_limit (fun q => bad q (s q)) 0) ->
  family_cofinal p -> (forall d, A (p d) (x d)) ->
  family_sequence_limit (fun d => stat (p d) (x d)) alpha ->
  family_sequence_limit (fun d => bad (p d) (x d)) 0.
Proof.
move=> Ab hb hall hp Ax hx eps eps0.
apply: (@family_eventually_reindex R T A stat
  (fun q z => `|bad q z-0| < eps) base alpha p x Ab hb _ hp Ax hx).
move=> s As hs.
exact: hall s As hs eps eps0.
Qed.

(* Example: a continuous real parameter with a varying natural index. *)
Theorem scalar_parameter_reindexing {R : realType}
    (f : nat -> R -> R) (a : R) (p : nat -> nat) (u : nat -> R) :
  (forall v : nat -> R, family_sequence_limit v a ->
    family_sequence_limit (fun q => f q (v q)) 0) ->
  family_cofinal p -> family_sequence_limit u a ->
  family_sequence_limit (fun d => f (p d) (u d)) 0.
Proof.
move=> hf hp hu.
have hb : family_sequence_limit (fun _ => a) a.
  move=> eps eps0; exists 0%N => d _.
  by rewrite subrr normr0.
apply: (@family_limit_reindex R (fun _ => R) (fun _ _ => True)
  (fun _ z => z) f (fun _ => a) a p u _ hb _ hp _ hu).
- by move=> q.
- move=> v _ hv; exact: hf.
- by move=> d.
Qed.
