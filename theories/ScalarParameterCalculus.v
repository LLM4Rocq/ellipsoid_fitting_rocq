(* Port of the inner module ScalarParameterCalculus of
   theories/InterpolationProofs.v, extracted to
   build/agent2/unbundled/ScalarParameterCalculus.v, from Coquelicot to
   MathComp-Analysis.

   Both lemmas keep their names, their arguments in the same order and
   their hypotheses. The only change of form is the derivative: Coquelicot's
   is_derive f x l, for f : R -> R, becomes @is_derive R R^o R^o x 1 f l of
   MathComp-Analysis. Both say that (f (x + h) - f x) / h tends to l when h
   tends to 0 (is_derive_Reals of AnalysisBridge proves the equivalence with
   Stdlib's derivable_pt_lim), so the meaning is unchanged. The arithmetic
   in every statement is Stdlib's, as in the original.

   The two lemmas have the same text as the lemmas of the same names in
   theories/GaussianParameterBounds.v, and their proofs are those of the
   port analysis/GaussianParameterBounds.v. The derivative arguments use
   is_derive_minus, is_derive_const, auto_derive, MVT_cor4 and
   is_derive_Reals of the bridge in place of Coquelicot's lemmas of the same
   names. Stdlib's rewrite A, B ... by tac, which does not parse once
   ssreflect is loaded, is replaced by rewrites with explicit side
   conditions.

   The original imported Classical_Prop but did not use it. This port does
   not import it. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
Open Scope R_scope.

Lemma local_second_derivative_remainder (f df ddf : R -> R) a rho C :
  (forall t, Rabs (t-a) <= rho -> @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, Rabs (t-a) <= rho -> @is_derive R R^o R^o t 1 df (ddf t)) ->
  (forall t, Rabs (t-a) <= rho -> Rabs (ddf t) <= C) ->
  forall b, Rabs (b-a) <= rho ->
    Rabs (f b - f a - (b-a)*df a) <= C * Rabs (b-a)^2.
Proof.
  intros Hd Hdd Hb b Hba.
  assert (HR : forall t, Rabs (t-a) <= rho ->
    @is_derive R R^o R^o t 1 (fun u => f u - f a - (u-a)*df a) (df t - df a)).
  { intros t Ht.
    assert (HL : @is_derive R R^o R^o t 1 (fun u => (u-a)*df a) (df a)).
    { auto_derive; try reflexivity; ring. }
    replace (df t - df a) with ((df t - 0) - df a) by ring.
    apply is_derive_minus.
    - apply is_derive_minus.
      + apply Hd; exact Ht.
      + exact (is_derive_const (f a) t).
    - exact HL. }
  destruct (MVT_cor4 (fun t => f t-f a-(t-a)*df a) (fun t => df t-df a)
    a rho HR b Hba) as [c [Hc Hca]].
  assert (HcR : Rabs (c-a) <= rho) by lra.
  destruct (MVT_cor4 df ddf a rho Hdd c HcR) as [d [Hd' Hda]].
  assert (HdR : Rabs (d-a) <= rho) by lra.
  specialize (Hb d HdR).
  assert (HE : f b-f a-(b-a)*df a = ddf d * (c-a) * (b-a)).
  { rewrite Hd' in Hc; lra. }
  rewrite HE !Rabs_mult.
  pose proof (Rabs_pos (ddf d)); pose proof (Rabs_pos (c-a)); pose proof (Rabs_pos (b-a)).
  assert (Hprod1 : Rabs (ddf d)*Rabs (c-a) <= C*Rabs (c-a)) by nra.
  assert (Hprod2 : C*Rabs (c-a) <= C*Rabs (b-a)) by nra.
  simpl; nra.
Qed.

Lemma quadratic_remainder_derivative (f : R -> R) a df rho K :
  0 < rho ->
  (forall b, Rabs (b-a) <= rho ->
    Rabs (f b - f a - (b-a)*df) <= K * Rabs (b-a)^2) ->
  @is_derive R R^o R^o a 1 f df.
Proof.
  intros Hr Hb; apply is_derive_Reals.
  intros eps Heps.
  assert (Hdelta : 0 < Rmin rho (eps/(Rabs K+1))).
  { apply Rmin_case; [exact Hr | apply Rdiv_lt_0_compat; [exact Heps | pose proof (Rabs_pos K); lra]]. }
  exists (mkposreal _ Hdelta); intros h Hh Hsmall.
  change (Rabs h < Rmin rho (eps/(Rabs K+1))) in Hsmall.
  pose proof (Rmin_l rho (eps/(Rabs K+1))) as Hleft.
  pose proof (Rmin_r rho (eps/(Rabs K+1))) as Hright.
  assert (Hrho : Rabs ((a+h)-a) <= rho) by (replace ((a+h)-a) with h by ring; lra).
  specialize (Hb (a+h) Hrho).
  replace ((a+h)-a) with h in Hb by ring.
  assert (Habs : 0 < Rabs h) by (apply Rabs_pos_lt; exact Hh).
  replace ((f (a+h)-f a)/h-df) with ((f (a+h)-f a-h*df)/h) by (field; exact Hh).
  rewrite (Rabs_div _ _ Hh).
  apply (Rmult_lt_reg_r (Rabs h)); [exact Habs | ].
  replace (Rabs (f (a+h)-f a-h*df) / Rabs h * Rabs h) with
    (Rabs (f (a+h)-f a-h*df)) by (field; lra).
  assert (Hscaled : Rabs h * (Rabs K+1) < eps).
  { assert (Hmul : Rabs h * (Rabs K+1) < (eps/(Rabs K+1))*(Rabs K+1)) by
      (pose proof (Rabs_pos K); nra).
    replace ((eps/(Rabs K+1))*(Rabs K+1)) with eps in Hmul by
      (field; pose proof (Rabs_pos K); lra); exact Hmul. }
  pose proof (Rle_abs K); simpl in Hb; nra.
Qed.
