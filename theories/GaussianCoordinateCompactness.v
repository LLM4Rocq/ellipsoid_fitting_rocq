From Stdlib Require Import Reals List Lia Lra Classical_Prop.
From mathcomp Require Import boolp.
From EllipsoidFitting Require Import GaussianCoordinateDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port note. This helper module replaces the two names of
   Coquelicot.Compactness that the coordinate modules of theories/ use and
   that GaussianCoordinateDefinitions does not copy: bounded_n and
   compactness_value. Nothing here changed form.

   bounded_n is copied word for word from Coquelicot.Compactness
   (Coquelicot 3.4.4), as printed by Print in the rocq-tools switch, so that
   simpl, destruct and change behave on it as in theories/. It is the only
   Definition of the module; no challenge statement mentions it.

   compactness_value has exactly Coquelicot's statement, double negation
   included. Its proof is classical and elementary: it does not build a
   topology on Tn n R. The one dimensional case (compactness_segment) is a
   least upper bound argument on the set of right endpoints y such that
   [a, y] admits a uniform gauge value; the case of dimension S n follows
   from the case of dimension n applied to every slice and from the one
   dimensional case applied to the slice gauges (compactness_value_gauge).
   The gauge is a relation there, so that no choice principle is needed
   before the sig forms. compactness_value_pos is the positive sig form,
   without the double negation, which the port of GaussianCoordinateTopology
   can use directly; it needs boolp's constructive_indefinite_description,
   the only MathComp name used here. compactness_value_exists is the same
   with an exists and a real valued gauge.

   Assumptions. compactness_segment, compactness_value_gauge and
   compactness_value_exists depend on Stdlib's axioms for R
   (sig_forall_dec, sig_not_dec, functional_extensionality_dep) and on
   MathComp's boolp axioms, through boolp.EM, which is used in place of
   Stdlib's Classical_Prop.classic so that no statement free of Rpower.ln
   rests on classic (build/agent2/REPORT-axioms.md). compactness_value_pos
   and compactness_value also depend on
   boolp.constructive_indefinite_description. All are permitted by
   analysis/README.md and the port guide. *)

(* Copy of Coquelicot.Compactness.bounded_n: every coordinate of x lies
   between the same coordinates of a and b. *)
Fixpoint bounded_n (n : nat) : Tn n R -> Tn n R -> Tn n R -> Prop :=
  match n as n0 return (Tn n0 R -> Tn n0 R -> Tn n0 R -> Prop) with
  | O => fun _ _ _ : Tn O R => True
  | S n0 =>
      fun a b x : Tn (S n0) R =>
      let '(a1, a2) := a in
      let '(b1, b2) := b in
      let '(x1, x2) := x in a1 <= x1 <= b1 /\ bounded_n n0 a2 b2 x2
  end.

(* One dimension. G x e reads "e is an admissible gauge value at x". If
   every point has an admissible positive value, then some e0 > 0 works
   uniformly on [a, b]: every y of [a, b] is within an admissible e of some
   x of [a, b], with e0 <= e. *)
Lemma compactness_segment (a b : R) (G : R -> R -> Prop) :
  (forall x, exists e, 0 < e /\ G x e) ->
  exists e0, 0 < e0 /\ forall y, a <= y <= b ->
    exists x e, a <= x <= b /\ G x e /\ Rabs (y - x) < e /\ e0 <= e.
Proof.
  intros HG.
  destruct (Rle_dec a b) as [Hab | Hab].
  2: { exists 1; split; [lra|]. intros y Hy; lra. }
  (* S y: the segment [a, y] admits a uniform gauge value. *)
  pose (S := fun y => a <= y <= b /\ exists e0, 0 < e0 /\ forall z, a <= z <= y ->
    exists x e, a <= x <= b /\ G x e /\ Rabs (z - x) < e /\ e0 <= e).
  assert (HSa : S a).
  { split; [lra|]. destruct (HG a) as [ea [Hea HGa]].
    exists ea; split; [exact Hea|]. intros z Hz.
    exists a, ea. replace z with a by lra.
    split; [lra|]; split; [exact HGa|]; split; [|lra].
    rewrite Rminus_diag_eq; [rewrite Rabs_R0; exact Hea | reflexivity]. }
  assert (Hbound : bound S).
  { exists b; intros y [Hy _]; lra. }
  destruct (completeness S Hbound (ex_intro _ a HSa)) as [m [Hub Hlub]].
  assert (Ham : a <= m) by (apply Hub; exact HSa).
  assert (Hmb : m <= b) by (apply Hlub; intros y [Hy _]; lra).
  destruct (HG m) as [em [Hem HGm]].
  (* Some y of S lies above m - em, since m - em is not an upper bound. *)
  assert (Hnear : exists y, S y /\ m - em < y).
  { destruct (boolp.EM (exists y, S y /\ m - em < y)) as [H | H];
      [exact H|].
    exfalso.
    assert (Hub' : is_upper_bound S (m - em)).
    { intros y Hy. destruct (Rle_dec y (m - em)) as [Hle | Hgt]; [exact Hle|].
      exfalso; apply H; exists y; split; [exact Hy|lra]. }
    pose proof (Hlub _ Hub'); lra. }
  destruct Hnear as [y [[Hy [ey [Hey Hcov]]] Hmy]].
  (* Then min b (m + em / 2) is in S, with the value min ey em. *)
  assert (HSw : S (Rmin b (m + em / 2))).
  { split.
    - split; [apply Rmin_glb; lra|apply Rmin_l].
    - exists (Rmin ey em); split; [apply Rmin_pos; assumption|].
      intros z Hz.
      destruct (Rle_dec z y) as [Hzy | Hzy].
      + destruct (Hcov z (conj (proj1 Hz) Hzy)) as [x [e [Hx [HGx [Hzx Hee]]]]].
        exists x, e. pose proof (Rmin_l ey em).
        split; [exact Hx|]; split; [exact HGx|]; split; [exact Hzx|lra].
      + exists m, em. split; [lra|]. split; [exact HGm|]. split.
        * assert (Hzw : z <= m + em / 2).
          { pose proof (Rmin_r b (m + em / 2)); lra. }
          apply Rabs_def1; lra.
        * apply Rmin_r. }
  assert (Hwm : Rmin b (m + em / 2) <= m) by (apply Hub; exact HSw).
  (* So m = b, and b itself is in S. *)
  assert (Hmb' : m = b).
  { destruct (Rlt_dec m b) as [Hlt | Hnlt]; [|lra].
    exfalso.
    assert (m < Rmin b (m + em / 2)) by (apply Rmin_glb_lt; lra). lra. }
  assert (HSb : S b).
  { assert (Hwb : Rmin b (m + em / 2) = b).
    { rewrite Hmb'; apply Rmin_left; lra. }
    rewrite <- Hwb; exact HSw. }
  destruct HSb as [_ [e0 [He0 Hcov0]]].
  exists e0; split; [exact He0|]. exact Hcov0.
Qed.

(* The box, with a relational gauge: G t e reads "e is an admissible gauge
   value at t". No choice principle is needed. *)
Lemma compactness_value_gauge n (a b : Tn n R) (G : Tn n R -> R -> Prop) :
  (forall t, exists e, 0 < e /\ G t e) ->
  exists d, 0 < d /\ forall x, bounded_n n a b x ->
    exists t e, bounded_n n a b t /\ G t e /\ close_n n e x t /\ d <= e.
Proof.
  revert a b G; induction n as [|n IH]; intros a b G HG.
  - destruct (HG a) as [e [He HGe]].
    exists e; split; [exact He|]. intros x _. exists a, e.
    simpl. split; [exact I|]. split; [exact HGe|]. split; [exact I|].
    apply Rle_refl.
  - destruct a as [a1 a2], b as [b1 b2].
    (* G1 x1 e: e is a uniform gauge value for the slice at x1. *)
    pose (G1 := fun (x1 e : R) => forall x2, bounded_n n a2 b2 x2 ->
      exists t2 e2, bounded_n n a2 b2 t2 /\ G (x1, t2) e2 /\ close_n n e2 x2 t2 /\
        e <= e2).
    assert (HG1 : forall x1, exists e, 0 < e /\ G1 x1 e).
    { intro x1.
      exact (IH a2 b2 (fun t2 e => G (x1, t2) e) (fun t2 => HG (x1, t2))). }
    destruct (compactness_segment a1 b1 G1 HG1) as [e0 [He0 Hcov]].
    exists e0; split; [exact He0|].
    intros [x1 x2] [Hx1 Hx2].
    destruct (Hcov x1 Hx1) as [t1 [e [Ht1 [HG1t1 [Hx1t1 He0e]]]]].
    destruct (HG1t1 x2 Hx2) as [t2 [e2 [Ht2 [HGt [Hclose Hee2]]]]].
    exists (t1, t2), e2. simpl.
    split; [split; [exact Ht1|exact Ht2]|].
    split; [exact HGt|].
    split; [split; [lra|exact Hclose]|lra].
Qed.

(* The box, with a real valued positive gauge and an exists. *)
Lemma compactness_value_exists n (a b : Tn n R) (delta : Tn n R -> R) :
  (forall t, 0 < delta t) ->
  exists d, 0 < d /\ forall x, bounded_n n a b x ->
    exists t, bounded_n n a b t /\ close_n n (delta t) x t /\ d <= delta t.
Proof.
  intros Hdelta.
  destruct (compactness_value_gauge n a b (fun t e => e = delta t)
    (fun t => ex_intro _ (delta t) (conj (Hdelta t) eq_refl))) as [d [Hd Hcov]].
  exists d; split; [exact Hd|].
  intros x Hx.
  destruct (Hcov x Hx) as [t [e [Ht [He [Hclose Hde]]]]].
  exists t. rewrite <- He. split; [exact Ht|]. split; [exact Hclose|exact Hde].
Qed.

(* Coquelicot's compactness_value without the double negation. *)
Lemma compactness_value_pos n (a b : Tn n R) (delta : Tn n R -> posreal) :
  {d : posreal | forall x : Tn n R, bounded_n n a b x ->
    exists t : Tn n R, bounded_n n a b t /\ close_n n (delta t) x t /\ d <= delta t}.
Proof.
  destruct (cid (compactness_value_exists n a b (fun t => delta t)
    (fun t => cond_pos (delta t)))) as [d [Hd Hcov]].
  exists (mkposreal d Hd). exact Hcov.
Qed.

(* The statement of Coquelicot.Compactness.compactness_value. *)
Lemma compactness_value n (a b : Tn n R) (delta : Tn n R -> posreal) :
  {d : posreal | forall x : Tn n R, bounded_n n a b x ->
    ~ ~ (exists t : Tn n R, bounded_n n a b t /\ close_n n (delta t) x t /\ d <= delta t)}.
Proof.
  destruct (compactness_value_pos n a b delta) as [d Hd].
  exists d. intros x Hx Hnot. exact (Hnot (Hd x Hx)).
Qed.
