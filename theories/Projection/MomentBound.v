(* Cauchy-Schwarz and a bounded-test estimate for concrete Gaussian integrals. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation.
Open Scope R_scope.

Lemma paper_main_projection_discriminant A B x : 0<=A -> 0<=B ->
  (forall t, 0<=A+2*t*x+t^2*B) -> x^2<=A*B.
Proof.
intros HA HB H.
destruct(Rlt_dec 0 B) as [Hp|Hz].
- pose proof(H(-x/B)) as HH.
  assert (HE : (A+2*(-x/B)*x+(-x/B)^2*B)*B=A*B-x^2) by (field; lra).
  pose proof(Rmult_le_pos _ _ HH HB); nra.
- assert (HB0 : B=0) by lra; subst B.
  destruct(Req_dec x 0) as [->|Hx]; [nra|].
  pose proof(H(-(A+1)/(2*x))) as HH.
  assert (HE : A+2*(-(A+1)/(2*x))*x+(-(A+1)/(2*x))^2*0= -1) by (field; exact Hx).
  rewrite HE in HH; lra.
Qed.

Lemma paper_main_projection_square_expectation d F G t :
  gaussian_iterated_integrable d (fun xs => F xs^2) ->
  gaussian_iterated_integrable d (fun xs => F xs*G xs) ->
  gaussian_iterated_integrable d (fun xs => G xs^2) ->
  gaussian_iterated_integrable d (fun xs => (F xs+t*G xs)^2) /\
  gaussian_iterated_expectation d (fun xs => (F xs+t*G xs)^2)=
    gaussian_iterated_expectation d (fun xs => F xs^2)+
    2*t*gaussian_iterated_expectation d (fun xs => F xs*G xs)+
    t^2*gaussian_iterated_expectation d (fun xs => G xs^2).
Proof.
intros HF HFG HG.
destruct(gaussian_iterated_scale d _ (2*t) HFG) as [HI1 HE1].
destruct(gaussian_iterated_scale d _ (t^2) HG) as [HI2 HE2].
destruct(gaussian_iterated_add d _ _ HF HI1) as [HI3 HE3].
destruct(gaussian_iterated_add d _ _ HI3 HI2) as [HI4 HE4].
assert (HE : forall xs, F xs^2+(2*t)*(F xs*G xs)+t^2*G xs^2=(F xs+t*G xs)^2) by (intro xs; ring).
split.
- apply (gaussian_iterated_integrable_ext d _ _ (fun xs _ => HE xs) HI4).
- transitivity (gaussian_iterated_expectation d
    (fun xs => F xs^2+(2*t)*(F xs*G xs)+t^2*G xs^2)).
  + apply gaussian_iterated_expectation_ext; intros xs Hxs; symmetry; apply HE.
  + rewrite HE4 HE3 HE1 HE2; reflexivity.
Qed.

Theorem paper_main_projection_cauchy_schwarz d F G :
  gaussian_iterated_integrable d (fun xs => F xs^2) ->
  gaussian_iterated_integrable d (fun xs => F xs*G xs) ->
  gaussian_iterated_integrable d (fun xs => G xs^2) ->
  (gaussian_iterated_expectation d (fun xs => F xs*G xs))^2 <=
    gaussian_iterated_expectation d (fun xs => F xs^2)*
    gaussian_iterated_expectation d (fun xs => G xs^2).
Proof.
intros HF HFG HG; apply paper_main_projection_discriminant.
- apply gaussian_iterated_nonnegative; [exact HF|intros; nra].
- apply gaussian_iterated_nonnegative; [exact HG|intros; nra].
- intro t; destruct(paper_main_projection_square_expectation d F G t HF HFG HG) as [HI HE].
  rewrite <- HE; apply gaussian_iterated_nonnegative; [exact HI|].
  intros xs Hxs; apply pow2_ge_0.
Qed.

Theorem paper_main_projection_weighted_bound d F G V C :
  gaussian_iterated_integrable d (fun xs => F xs^2) ->
  gaussian_iterated_integrable d (fun xs => F xs*G xs) ->
  gaussian_iterated_integrable d (fun xs => G xs^2) ->
  0<=V -> 0<=C ->
  gaussian_iterated_expectation d (fun xs => F xs^2)<=V ->
  (forall xs, List.length xs=d -> Rabs(G xs)<=C) ->
  Rabs(gaussian_iterated_expectation d (fun xs => F xs*G xs))<=C*sqrt V.
Proof.
intros HF HFG HG HV HC HFV HGC.
pose proof(paper_main_projection_cauchy_schwarz d F G HF HFG HG) as HCS.
assert (H0F : 0<=gaussian_iterated_expectation d (fun xs => F xs^2)).
{ apply gaussian_iterated_nonnegative; [exact HF|intros; nra]. }
assert (H0G : 0<=gaussian_iterated_expectation d (fun xs => G xs^2)).
{ apply gaussian_iterated_nonnegative; [exact HG|intros; nra]. }
assert (HGC2 : gaussian_iterated_expectation d (fun xs => G xs^2)<=C^2).
{ rewrite <- (proj2(gaussian_iterated_constant d (C^2))).
  apply gaussian_iterated_monotone; [exact HG|apply gaussian_iterated_constant|].
  intros xs Hxs; pose proof(HGC xs Hxs).
  pose proof(Rabs_pos(G xs)); pose proof(Rsqr_abs(G xs)); unfold Rsqr in *; nra. }
pose proof(Rmult_le_compat _ _ _ _ H0F H0G HFV HGC2) as HP.
pose proof(sqrt_sqrt V HV) as HS; pose proof(sqrt_pos V) as HS0.
pose proof(Rsqr_abs(gaussian_iterated_expectation d (fun xs => F xs*G xs))) as HA.
unfold Rsqr in HA.
pose proof(Rabs_pos(gaussian_iterated_expectation d (fun xs => F xs*G xs))) as HA0.
assert (HB : 0<=C*sqrt V) by (apply Rmult_le_pos; assumption).
assert (HE : (C*sqrt V)^2=C^2*V) by nra.
nra.
Qed.
