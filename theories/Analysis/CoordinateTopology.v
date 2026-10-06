From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.Tuples.
Import ListNotations.
Open Scope R_scope.

(* Topology on d-tuples of reals. coordinates_uniform_space d is a copy of
   Tn d R with the pseudometric structure whose ball of radius e around x
   holds the y with close_n d e y x: each coordinate of y is within e of
   that of x. finite_joint_continuous d F says exactly that
   w |-> F (coordinates_to_list d w) is continuous on this space
   (finite_joint_continuous_filter). Constants are jointly continuous, joint continuity is preserved by
   equality on the lists of length d, by absolute values and by fixing a
   prefix of the coordinates, and it gives continuous sections in the last
   coordinate (finite_joint_continuous_last_section).

   With ssreflect loaded, xs ++ ys would be MathComp's cat and m + n
   ssrnat's addn, so the statements write (xs ++ ys)%list and
   (m + n)%coq_nat, Stdlib's app and Nat.add. *)

(* The type Tn d R with the uniform structure whose balls are close_n.
   The instances below are keyed on the name coordinates_uniform_space, so
   they do not attach any structure to Tn d R itself. *)
Definition coordinates_uniform_space (d : nat) : Type := Tn d R.

(* The instances repeat projections that MathComp's generic instances
   already give; Rocq warns that it ignores them. *)
Set Warnings "-redundant-canonical-projection".
HB.instance Definition _ d := gen_eqMixin (coordinates_uniform_space d).
HB.instance Definition _ d := gen_choiceMixin (coordinates_uniform_space d).
HB.instance Definition _ d :=
  isPointed.Build (coordinates_uniform_space d) (coordinates_of_list d []).
HB.instance Definition _ d := hasNbhs.Build (coordinates_uniform_space d)
  (nbhs_ (entourage_ (fun (x : coordinates_uniform_space d) (e : R)
    (y : coordinates_uniform_space d) => close_n d e y x))).

(* The three axioms of a pseudometric, for the ball
   x e y := close_n d e y x. The order and the addition are MathComp's, as
   the factory requires; they are Stdlib's under the conversions of
   Rstruct. *)
Lemma coordinates_uniform_space_ball_center d (x : coordinates_uniform_space d) (e : R) :
  (0 < e)%R -> close_n d e x x.
Proof. move=> /RltP He; exact: coordinates_close_center. Qed.

Lemma coordinates_uniform_space_ball_sym d (x y : coordinates_uniform_space d) (e : R) :
  close_n d e y x -> close_n d e x y.
Proof. exact: coordinates_close_sym. Qed.

Lemma coordinates_uniform_space_ball_triangle d (x y z : coordinates_uniform_space d)
  (e1 e2 : R) :
  close_n d e1 y x -> close_n d e2 z y -> close_n d (e1 + e2)%R z x.
Proof.
  move=> H1 H2; rewrite -RplusE Rplus_comm.
  exact: (coordinates_close_triangle d e2 e1 z y x H2 H1).
Qed.

HB.instance Definition _ d := Nbhs_isPseudoMetric.Build R (coordinates_uniform_space d)
  erefl (@coordinates_uniform_space_ball_center d)
  (@coordinates_uniform_space_ball_sym d) (@coordinates_uniform_space_ball_triangle d) erefl.
Set Warnings "redundant-canonical-projection".

Lemma finite_joint_continuous_filter d F :
  finite_joint_continuous d F <->
  forall z : coordinates_uniform_space d,
    {for z, continuous (fun w : coordinates_uniform_space d => F (coordinates_to_list d w))}.
Proof.
split.
- move=> HF z A /nbhs_Reals [eps [eps0 HA]].
  have [delta Hd] := HF z (mkposreal eps eps0).
  suff : nbhs z (fun w : coordinates_uniform_space d => A (F (coordinates_to_list d w))) by [].
  apply/nbhs_ballP; exists (pos delta); first by apply/RltP; exact: cond_pos.
  move=> w Hw; apply: HA; exact: Hd w Hw.
- move=> HF z eps.
  have Hl : nbhs (F (coordinates_to_list d z))
      (fun r => Rabs (r - F (coordinates_to_list d z)) < eps).
    by apply/nbhs_Reals; exists eps; split; [exact: cond_pos | done].
  have /nbhs_ballP [delta delta0 Hd] :
      nbhs (z : coordinates_uniform_space d) (fun w : coordinates_uniform_space d =>
        Rabs (F (coordinates_to_list d w) - F (coordinates_to_list d z)) < eps)
    := HF z _ Hl.
  exists (mkposreal delta (elimT RltP delta0)) => w Hw; exact: Hd w Hw.
Qed.

Lemma finite_joint_continuous_ext d (F G : list R -> R) :
  (forall xs, length xs = d -> F xs = G xs) ->
  finite_joint_continuous d F -> finite_joint_continuous d G.
Proof.
  intros He HF z eps; destruct (HF z eps) as [delta Hd].
  exists delta; intros w Hw.
  rewrite <- (He _ (coordinates_to_list_length d w)).
  rewrite <- (He _ (coordinates_to_list_length d z)).
  apply Hd; exact Hw.
Qed.
Lemma finite_joint_continuous_abs d (F : list R -> R) :
  finite_joint_continuous d F -> finite_joint_continuous d (fun xs => Rabs (F xs)).
Proof.
  intros HF z eps; destruct (HF z eps) as [delta Hd].
  exists delta; intros w Hw.
  eapply Rle_lt_trans; [apply Rabs_triang_inv2|exact (Hd w Hw)].
Qed.
Lemma finite_joint_continuous_constant d C :
  finite_joint_continuous d (fun _ => C).
Proof.
  intros z eps; exists eps; intros w Hw.
  rewrite Rminus_diag Rabs_R0; apply cond_pos.
Qed.

Lemma coordinates_close_prefix d e prefix xs ys :
  close_n d e (coordinates_of_list d xs) (coordinates_of_list d ys) ->
  0 < e ->
  close_n (length prefix + d)%coq_nat e
    (coordinates_of_list (length prefix + d)%coq_nat (prefix ++ xs)%list)
    (coordinates_of_list (length prefix + d)%coq_nat (prefix ++ ys)%list).
Proof.
  intros H He; induction prefix as [|a prefix IH]; simpl; [exact H|].
  split; [|exact IH]. rewrite Rminus_diag Rabs_R0; exact He.
Qed.
Lemma coordinates_close_snoc d e xs ys x y :
  length xs = d -> length ys = d ->
  close_n d e (coordinates_of_list d xs) (coordinates_of_list d ys) ->
  Rabs (x-y) < e ->
  close_n (S d) e (coordinates_of_list (S d) (xs ++ [x])%list)
    (coordinates_of_list (S d) (ys ++ [y])%list).
Proof.
  revert xs ys; induction d as [|d IH]; intros xs ys Hx Hy Hclose Hlast.
  - destruct xs, ys; try discriminate; simpl; split; [exact Hlast|exact I].
  - destruct xs as [|u xs], ys as [|v ys]; try discriminate.
    simpl in Hx, Hy, Hclose |- *; destruct Hclose as [H0 Htail]; split; [exact H0|].
    apply IH; try assumption; lia.
Qed.

Lemma finite_joint_continuous_prefix d prefix (F : list R -> R) :
  finite_joint_continuous (length prefix + d)%coq_nat F ->
  finite_joint_continuous d (fun xs => F (prefix ++ xs)%list).
Proof.
  intros HF z eps.
  assert (Hlenz : length (prefix ++ coordinates_to_list d z)%list = (length prefix + d)%coq_nat)
    by (rewrite length_app coordinates_to_list_length; reflexivity).
  destruct (HF (coordinates_of_list _ (prefix ++ coordinates_to_list d z)%list) eps) as [delta Hd].
  rewrite (coordinates_list_roundtrip _ _ Hlenz) in Hd.
  exists delta; intros w Hclose.
  assert (Hlenw : length (prefix ++ coordinates_to_list d w)%list = (length prefix + d)%coq_nat)
    by (rewrite length_app coordinates_to_list_length; reflexivity).
  assert (Hc : close_n (length prefix + d)%coq_nat delta
    (coordinates_of_list _ (prefix ++ coordinates_to_list d w)%list)
    (coordinates_of_list _ (prefix ++ coordinates_to_list d z)%list)).
  { apply coordinates_close_prefix; [rewrite !coordinates_roundtrip; exact Hclose|apply cond_pos]. }
  specialize (Hd _ Hc); rewrite (coordinates_list_roundtrip _ _ Hlenw) in Hd; exact Hd.
Qed.
Lemma finite_joint_continuous_head d (F : list R -> R) x :
  finite_joint_continuous (S d) F -> finite_joint_continuous d (fun xs => F (x::xs)).
Proof. exact (finite_joint_continuous_prefix d [x] F). Qed.

Theorem finite_joint_continuous_last_section d (F : list R -> R) (xs : list R) :
  finite_joint_continuous (S d) F -> length xs = d ->
  forall t : R, {for t, continuous (fun u : R => F (xs ++ [u])%list)}.
Proof.
  intros HF Hlen t; apply continuous_Reals; intros eps Heps.
  assert (Hlen0 : length (xs ++ [t])%list = S d)
    by (rewrite length_app Hlen; simpl; lia).
  destruct (HF (coordinates_of_list _ (xs ++ [t])%list) (mkposreal eps Heps)) as [delta Hd].
  rewrite (coordinates_list_roundtrip _ _ Hlen0) in Hd.
  exists delta; split; [apply cond_pos|]. intros u Hu.
  assert (Hlenu : length (xs ++ [u])%list = S d)
    by (rewrite length_app Hlen; simpl; lia).
  assert (Hc : close_n (S d) delta (coordinates_of_list _ (xs ++ [u])%list)
    (coordinates_of_list _ (xs ++ [t])%list)).
  { apply coordinates_close_snoc; try exact Hlen.
    - apply coordinates_close_center, cond_pos.
    - exact Hu. }
  specialize (Hd _ Hc).
  rewrite (coordinates_list_roundtrip _ _ Hlenu) in Hd.
  exact Hd.
Qed.
