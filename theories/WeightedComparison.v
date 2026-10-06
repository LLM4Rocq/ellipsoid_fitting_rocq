(* Comparison of increments on [0, 1] through derivatives on (0, 1), for
   functions with a derivative at every t of (0, 1), continuous at 0 and
   at 1 within [0, 1]. A nonpositive derivative gives g 1 <= g 0
   (unit_interval_derivative_nonpositive); dg <= dh gives
   g 1 - g 0 <= h 1 - h 0 (unit_interval_primitive_comparison); and
   |dg t| <= K sqrt t gives |g 1 - g 0| <= 2 K / 3
   (sqrt_weighted_endpoint_bound). weighted_comparison_within_Reals states
   a limit within a domain in epsilon-delta form. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* The epsilon-delta reading of a limit within a domain, at a real point,
   for a real function. *)
Lemma weighted_comparison_within_Reals (f : R -> R) (D : R -> Prop) (a l : R) :
  (f @ within D (nbhs a) --> l)%classic <->
  (forall eps, 0 < eps -> exists delta, 0 < delta /\
     forall y, Rabs (y - a) < delta -> D y -> Rabs (f y - l) < eps).
Proof.
  split.
  - intros H eps Heps.
    assert (Hl : nbhs l (fun r => Rabs (r - l) < eps)).
    { apply nbhs_Reals; exists eps; split; [exact Heps | intros r Hr; exact Hr]. }
    pose proof (H _ Hl) as Ha.
    change (nbhs a (fun y => D y -> Rabs (f y - l) < eps)) in Ha.
    apply nbhs_Reals in Ha; exact Ha.
  - intros H A HA; apply nbhs_Reals in HA; destruct HA as [eps [Heps HA]].
    destruct (H eps Heps) as [delta [Hdelta Hd]].
    change (nbhs a (fun y => D y -> A (f y))).
    apply nbhs_Reals; exists delta; split; [exact Hdelta|].
    intros y Hy Dy; apply HA; exact (Hd y Hy Dy).
Qed.

Lemma unit_interval_endpoint_order (f : R -> R) :
  (f @ within (fun t => 0<=t<=1) (nbhs 0) --> f 0)%classic ->
  (f @ within (fun t => 0<=t<=1) (nbhs 1) --> f 1)%classic ->
  (forall x y, 0<x -> x<y -> y<1 -> f y<=f x) ->
  f 1<=f 0.
Proof.
  intros H0 H1 Hmono.
  apply Rnot_lt_le; intro Hgap.
  assert (Heps : 0<(f 1-f 0)/4) by lra.
  destruct (proj1 (weighted_comparison_within_Reals f _ 0 (f 0)) H0 _ Heps) as [d0 [Hd0pos Hd0]].
  destruct (proj1 (weighted_comparison_within_Reals f _ 1 (f 1)) H1 _ Heps) as [d1 [Hd1pos Hd1]].
  set (s:=Rmin d0 (Rmin d1 (1/2))/2).
  assert (Hs : 0<s /\ s<d0 /\ s<d1 /\ s<=1/4).
  { unfold s.
    pose proof (Rmin_l d0 (Rmin d1 (1/2))).
    pose proof (Rmin_r d0 (Rmin d1 (1/2))).
    pose proof (Rmin_l d1 (1/2)). pose proof (Rmin_r d1 (1/2)).
    assert (0<Rmin d0 (Rmin d1 (1/2))) by
      (apply Rmin_pos; [assumption|apply Rmin_pos; lra]). lra. }
  assert (Hnear0 : Rabs (s-0) < d0).
  { rewrite Rminus_0_r Rabs_pos_eq; lra. }
  assert (Hnear1 : Rabs ((1-s)-1) < d1).
  { replace ((1-s)-1) with (-s) by ring.
    rewrite Rabs_Ropp Rabs_pos_eq; lra. }
  pose proof (Hd0 s Hnear0 ltac:(lra)) as Hclose0.
  pose proof (Hd1 (1-s) Hnear1 ltac:(lra)) as Hclose1.
  apply Rabs_lt_between in Hclose0. apply Rabs_lt_between in Hclose1.
  pose proof (Hmono s (1-s) ltac:(lra) ltac:(lra) ltac:(lra)). lra.
Qed.

Lemma unit_interval_derivative_nonpositive (f df : R -> R) :
  (f @ within (fun t => 0<=t<=1) (nbhs 0) --> f 0)%classic ->
  (f @ within (fun t => 0<=t<=1) (nbhs 1) --> f 1)%classic ->
  (forall t, 0<t<1 -> @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, 0<t<1 -> df t<=0) -> f 1<=f 0.
Proof.
  intros H0 H1 Hd Hb.
  apply unit_interval_endpoint_order; [exact H0|exact H1|].
  intros x y Hx Hxy Hy.
  assert (Hmin : Rmin x y=x) by (apply Rmin_left; lra).
  assert (Hmax : Rmax x y=y) by (apply Rmax_right; lra).
  destruct (MVT_gen f x y df) as [c [Hc Heq]].
  - intros z Hz; rewrite Hmin Hmax in Hz; apply Hd; lra.
  - intros z Hz; rewrite Hmin Hmax in Hz.
    apply (proj2 (continuity_pt_filterlim f z)).
    exact (is_derive_continuous f z (df z) (Hd z ltac:(lra))).
  - rewrite Hmin Hmax in Hc.
    pose proof(Hb c ltac:(lra)). assert(df c*(y-x)<=0) by nra. lra.
Qed.

Lemma weighted_sqrt_primitive_derivative (K t : R) :
  0<t -> @is_derive R R^o R^o t 1 (fun u => 2*K/3*u*sqrt u) (K*sqrt t).
Proof.
  intro Ht.
  assert (Hs : 0<sqrt t) by (apply sqrt_lt_R0; exact Ht).
  pose proof (sqrt_def t ltac:(lra)) as Hsq.
  replace (K*sqrt t) with ((2*K/3*1)*sqrt t + (2*K/3*t)*(/(2*sqrt t))).
  - apply (is_derive_mult (fun u => 2*K/3*u) sqrt t (2*K/3*1) (/(2*sqrt t))).
    + exact (is_derive_scal (2*K/3) (fun u => u) t 1 (is_derive_id_R t)).
    + exact (is_derive_Rsqrt t Ht).
  - rewrite <- Hsq at 2. field; lra.
Qed.

Lemma unit_interval_primitive_comparison (g dg h dh : R -> R) :
  (g @ within (fun t => 0<=t<=1) (nbhs 0) --> g 0)%classic ->
  (g @ within (fun t => 0<=t<=1) (nbhs 1) --> g 1)%classic ->
  {for 0, continuous h} -> {for 1, continuous h} ->
  (forall t, 0<t<1 -> @is_derive R R^o R^o t 1 g (dg t)) ->
  (forall t, 0<t<1 -> @is_derive R R^o R^o t 1 h (dh t)) ->
  (forall t, 0<t<1 -> dg t<=dh t) ->
  g 1-g 0<=h 1-h 0.
Proof.
  intros H0 H1 Hh0 Hh1 Hg Hh Hb.
  assert (Hlimit : forall a,
    (g @ within (fun t => 0<=t<=1) (nbhs a) --> g a)%classic ->
    {for a, continuous h} ->
    ((fun t => g t - h t) @ within (fun t => 0<=t<=1) (nbhs a) --> g a - h a)%classic).
  { intros a Hga Hha.
    apply (proj2 (weighted_comparison_within_Reals _ _ a _)); intros eps Heps.
    assert (Heps2 : 0 < eps/2) by lra.
    destruct (proj1 (weighted_comparison_within_Reals g _ a (g a)) Hga _ Heps2) as [d1 [Hd1 Hg1]].
    destruct (proj1 (continuous_Reals h a) Hha _ Heps2) as [d2 [Hd2 Hh2]].
    exists (Rmin d1 d2); split; [apply Rmin_pos; assumption|].
    intros y Hy Dy.
    assert (Hy1 : Rabs (y - a) < d1) by (eapply Rlt_le_trans; [exact Hy|apply Rmin_l]).
    assert (Hy2 : Rabs (y - a) < d2) by (eapply Rlt_le_trans; [exact Hy|apply Rmin_r]).
    pose proof (Hg1 y Hy1 Dy) as Ha1; pose proof (Hh2 y Hy2) as Ha2.
    replace (g y - h y - (g a - h a)) with ((g y - g a) - (h y - h a)) by ring.
    eapply Rle_lt_trans; [apply Rabs_triang|].
    rewrite Rabs_Ropp; lra. }
  assert (Hend : (g 1-h 1)<=(g 0-h 0)).
  { apply (unit_interval_derivative_nonpositive (fun t=>g t-h t) (fun t=>dg t-dh t)).
    - exact (Hlimit 0 H0 Hh0).
    - exact (Hlimit 1 H1 Hh1).
    - intros t Ht; exact (is_derive_minus g h t (dg t) (dh t) (Hg t Ht) (Hh t Ht)).
    - intros t Ht; specialize (Hb t Ht); lra. }
  lra.
Qed.

Theorem sqrt_weighted_endpoint_bound (g dg : R -> R) (K : R) :
  0<=K ->
  (g @ within (fun t => 0<=t<=1) (nbhs 0) --> g 0)%classic ->
  (g @ within (fun t => 0<=t<=1) (nbhs 1) --> g 1)%classic ->
  (forall t, 0<t<1 -> @is_derive R R^o R^o t 1 g (dg t)) ->
  (forall t, 0<t<1 -> Rabs(dg t)<=K*sqrt t) ->
  Rabs(g 1-g 0)<=2*K/3.
Proof.
  intros HK H0 H1 Hg Hb.
  set (h:=fun t:R=>2*K/3*t*sqrt t).
  assert (HC : forall a, 0 <= a -> {for a, continuous h}).
  { intros a Ha; unfold h.
    apply (continuous_mult R (fun t=>2*K/3*t) sqrt a).
    - apply (continuous_mult R (fun _=>2*K/3) (fun t=>t) a).
      + apply (continuous_const R).
      + apply continuous_id.
    - apply continuous_Rsqrt; exact Ha. }
  assert (HD : forall t, 0<t<1 -> @is_derive R R^o R^o t 1 h (K*sqrt t)).
  { intros t Ht; unfold h; apply weighted_sqrt_primitive_derivative; lra. }
  assert (Hends : h 1-h 0 = 2*K/3).
  { unfold h; rewrite sqrt_1 sqrt_0; ring. }
  assert (Hupper : g 1-g 0<=2*K/3).
  { rewrite <-Hends.
    apply (unit_interval_primitive_comparison g dg h (fun t=>K*sqrt t) H0 H1
      (HC 0 ltac:(lra)) (HC 1 ltac:(lra)) Hg HD).
    intros t Ht; pose proof (Hb t Ht); pose proof (Rle_abs (dg t)); lra. }
  assert (Hneg : forall a,
    (g @ within (fun t=>0<=t<=1) (nbhs a) --> g a)%classic ->
    ((fun t=>-g t) @ within (fun t=>0<=t<=1) (nbhs a) --> -g a)%classic).
  { intros a Hga.
    apply (proj2 (weighted_comparison_within_Reals _ _ a _)); intros eps Heps.
    destruct (proj1 (weighted_comparison_within_Reals g _ a (g a)) Hga _ Heps) as [d [Hd Hgd]].
    exists d; split; [exact Hd|].
    intros y Hy Dy.
    replace (- g y - - g a) with (- (g y - g a)) by ring.
    rewrite Rabs_Ropp; exact (Hgd y Hy Dy). }
  assert (Hlower : (-g 1)-(-g 0)<=2*K/3).
  { rewrite <-Hends.
    apply (unit_interval_primitive_comparison (fun t=>-g t) (fun t=>-dg t) h (fun t=>K*sqrt t)
      (Hneg 0 H0) (Hneg 1 H1) (HC 0 ltac:(lra)) (HC 1 ltac:(lra))).
    - intros t Ht; exact (is_derive_opp g t (dg t) (Hg t Ht)).
    - exact HD.
    - intros t Ht; pose proof (Hb t Ht); pose proof (Rle_abs (-dg t)) as Habs; rewrite Rabs_Ropp in Habs; lra. }
  apply Rabs_le; lra.
Qed.
