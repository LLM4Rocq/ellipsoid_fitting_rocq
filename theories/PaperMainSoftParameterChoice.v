(* Dimension-independent parameter choices for the strict subcritical margin. *)
From Stdlib Require Import Reals Lia Lra Psatz.
From mathcomp Require Import ssreflect.
Open Scope R_scope.

Lemma paper_main_soft_subcritical_gap alpha :
  0 <= alpha -> alpha < 1/4 -> 0 < 1/2-sqrt alpha.
Proof.
intros Ha Hb.
pose proof (sqrt_pos alpha).
pose proof (pow2_sqrt alpha Ha).
nra.
Qed.

Theorem paper_main_soft_parameters alpha kappa L :
  0 <= alpha -> alpha < 1/4 -> 1 <= kappa -> 0 <= L ->
  let g := 1/2-sqrt alpha in
  exists eps A theta,
    0 < eps /\ 0 < A /\ 0 < theta /\
    eps <= g/16 /\ L*eps <= g/16 /\
    ((4+4/eps)*ln 2)*(alpha+1)/A <= g/16 /\
    (800/3)*kappa^3*A^2*theta <= g/16.
Proof.
intros Ha Hb Hk HL g.
assert (Hg : 0 < g) by (apply paper_main_soft_subcritical_gap; assumption).
pose (eps := g/(16*(L+1))).
assert (Hden : 0 < 16*(L+1)) by lra.
assert (Heps : 0 < eps) by (unfold eps; apply Rdiv_lt_0_compat; assumption).
assert (Heq : eps*(16*(L+1))=g) by (unfold eps; field; lra).
assert (HepsB : eps <= g/16) by nra.
assert (HLeps : L*eps <= g/16) by nra.
pose (E := (4+4/eps)*ln 2).
assert (Hln : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
assert (HE : 0 < E).
{ unfold E; apply Rmult_lt_0_compat; last exact Hln.
  assert (0 < 4/eps) by (apply Rdiv_lt_0_compat; lra); lra. }
pose (A := 1+16*E*(alpha+1)/g).
assert (HAeq : A*g=g+16*E*(alpha+1)) by (unfold A; field; lra).
assert (HA : 0 < A) by nra.
assert (Hentropy : E*(alpha+1)/A <= g/16).
{ apply (Rmult_le_reg_r A); [exact HA|].
  replace (E*(alpha+1)/A*A) with (E*(alpha+1)) by (field; lra).
  nra. }
pose (T := (800/3)*kappa^3*A^2).
assert (HT : 0 <= T) by (unfold T; pose proof (pow_le kappa 3 ltac:(lra)); nra).
pose (theta := g/(1+16*T)).
assert (Htheta : 0 < theta) by (unfold theta; apply Rdiv_lt_0_compat; lra).
assert (Hteq : theta*(1+16*T)=g) by (unfold theta; field; lra).
exists eps,A,theta; repeat split; try assumption.
unfold T in Hteq; nra.
Qed.

Lemma paper_main_soft_scaled_error d kappa A theta :
  0 < d ->
  (200/3)*kappa^3*(A*d*sqrt d+A*d*sqrt d)^2*theta/(d^2*sqrt d) =
    (800/3)*kappa^3*A^2*theta*sqrt d.
Proof.
intro Hd.
pose proof (sqrt_lt_R0 d Hd) as Hs.
pose proof (pow2_sqrt d (Rlt_le _ _ Hd)) as Hsq.
assert (Hden : 0 < d^2*sqrt d).
{ apply Rmult_lt_0_compat; [apply pow_lt; exact Hd|exact Hs]. }
apply (Rmult_eq_reg_r (d^2*sqrt d)); [|lra].
replace ((200/3)*kappa^3*(A*d*sqrt d+A*d*sqrt d)^2*theta/(d^2*sqrt d)*(d^2*sqrt d))
  with ((200/3)*kappa^3*(A*d*sqrt d+A*d*sqrt d)^2*theta) by (field; lra).
nra.
Qed.

Theorem paper_main_soft_scaled_margin alpha kappa L eps A theta d D q w lr ls scale :
  0 <= alpha -> alpha < 1/4 -> 1 <= kappa -> 0 <= L ->
  0 < d -> 0 <= D -> D <= d^2 -> 0 <= q -> q <= alpha*d^2 ->
  0 < eps -> 0 < A -> 0 < theta ->
  eps <= (1/2-sqrt alpha)/16 -> L*eps <= (1/2-sqrt alpha)/16 ->
  ((4+4/eps)*ln 2)*(alpha+1)/A <= (1/2-sqrt alpha)/16 ->
  (800/3)*kappa^3*A^2*theta <= (1/2-sqrt alpha)/16 ->
  lr <= ((4+4/eps)*ln 2)*q -> ls <= ((4+4/eps)*ln 2)*D ->
  (1/2-(1/2-sqrt alpha)/16)*d <= w ->
  0 < scale -> 1 <= scale*sqrt d ->
  ((1/2-sqrt alpha)/2)*sqrt d <=
    scale*(w-eps*sqrt D-sqrt q) -lr/(A*d*sqrt d)-ls/(A*d*sqrt d)-
    (200/3)*kappa^3*(A*d*sqrt d+A*d*sqrt d)^2*theta/(d^2*sqrt d)-
    (L*sqrt d)*eps.
Proof.
intros Ha Hb Hk HL Hd HD0 HD Hq0 Hq He HA Ht HeB HLe HE HT Hlr Hls Hw Hscale HscaleB.
pose (g := 1/2-sqrt alpha).
assert (Hg : 0 < g) by (apply paper_main_soft_subcritical_gap; assumption).
fold g in HeB,HLe,HE,HT,Hw |- *.
pose (E := (4+4/eps)*ln 2).
fold E in HE,Hlr,Hls.
assert (Hln : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
assert (HE0 : 0 <= E).
{ unfold E; assert (0 < 4/eps) by (apply Rdiv_lt_0_compat; lra); nra. }
pose proof (sqrt_lt_R0 d Hd) as Hs.
pose proof (sqrt_pos D) as HSD.
pose proof (sqrt_pos q) as HSq.
pose proof (sqrt_pos alpha) as HSa.
pose proof (pow2_sqrt D HD0) as HSD2.
pose proof (pow2_sqrt q Hq0) as HSq2.
pose proof (pow2_sqrt alpha Ha) as HSa2.
pose proof (pow2_sqrt d (Rlt_le _ _ Hd)) as Hs2.
assert (HSDd : sqrt D <= d) by nra.
assert (HSprod : (sqrt alpha*d)^2 = alpha*d^2) by (rewrite Rpow_mult_distr HSa2; reflexivity).
assert (HSprod0 : 0 <= sqrt alpha*d) by (apply Rmult_le_pos; lra).
assert (HSqd : sqrt q <= sqrt alpha*d) by nra.
assert (Hwidth : (7*g/8)*d <= w-eps*sqrt D-sqrt q).
{ unfold g in *; nra. }
assert (Hmargin : (7*g/8)*sqrt d <= scale*(w-eps*sqrt D-sqrt q)).
{ pose proof (Rmult_le_compat_l scale _ _ (Rlt_le _ _ Hscale) Hwidth) as HH.
  pose proof (Rmult_le_compat_r ((7*g/8)*sqrt d) _ _ ltac:(nra) HscaleB) as HH2.
  replace (scale*(7*g/8*d)) with (((7*g/8)*sqrt d)*(scale*sqrt d)) in HH.
  - nra.
  - replace (scale*(7*g/8*d)) with (scale*(7*g/8*(sqrt d)^2)) by (rewrite Hs2; reflexivity).
    ring. }
assert (Hentropy : lr/(A*d*sqrt d)+ls/(A*d*sqrt d) <= (g/16)*sqrt d).
{ assert (Hden : 0 < A*d*sqrt d) by (repeat apply Rmult_lt_0_compat; assumption).
  apply (Rmult_le_reg_r (A*d*sqrt d)); [exact Hden|].
  replace ((lr/(A*d*sqrt d)+ls/(A*d*sqrt d))*(A*d*sqrt d)) with (lr+ls) by (field; lra).
  assert (HE' : E*(alpha+1) <= (g/16)*A).
  { pose proof (Rmult_le_compat_r A _ _ (Rlt_le _ _ HA) HE) as HH.
    replace (E*(alpha+1)/A*A) with (E*(alpha+1)) in HH by (field; lra).
    exact HH. }
  pose proof (Rmult_le_compat_r (d^2) _ _ ltac:(nra) HE') as HH.
  pose proof (Rmult_le_compat_l E _ _ HE0 Hq) as HQ'.
  pose proof (Rmult_le_compat_l E _ _ HE0 HD) as HD'.
  replace ((g/16)*sqrt d*(A*d*sqrt d)) with ((g/16)*A*d^2).
  - nra.
  - replace ((g/16)*sqrt d*(A*d*sqrt d)) with ((g/16)*A*d*(sqrt d)^2) by ring.
    rewrite Hs2; ring. }
rewrite (paper_main_soft_scaled_error d kappa A theta Hd).
pose proof (Rmult_le_compat_r (sqrt d) _ _ (Rlt_le _ _ Hs) HT) as HT'.
pose proof (Rmult_le_compat_r (sqrt d) _ _ (Rlt_le _ _ Hs) HLe) as HL'.
nra.
Qed.

Lemma paper_main_soft_gaussian_scale d :
  0 < d -> 1 <= sqrt(2/d)*sqrt d.
Proof.
intro Hd.
assert (Hx : 0 < 2/d) by (apply Rdiv_lt_0_compat; lra).
pose proof (sqrt_pos (2/d)) as Hx0.
pose proof (sqrt_pos d) as Hd0.
pose proof (pow2_sqrt (2/d) (Rlt_le _ _ Hx)) as Hx2.
pose proof (pow2_sqrt d (Rlt_le _ _ Hd)) as Hd2.
assert (Heq : (sqrt(2/d)*sqrt d)^2=2).
{ rewrite Rpow_mult_distr Hx2 Hd2; field; lra. }
assert (Hge : 0 <= sqrt(2/d)*sqrt d) by (apply Rmult_le_pos; assumption).
nra.
Qed.

Lemma paper_main_soft_margin_after_clipping g d margin loss :
  (g/2)*sqrt d <= margin -> loss <= (g/8)*sqrt d ->
  (g/4)*sqrt d <= margin-loss-(g/8)*sqrt d.
Proof. intros; lra. Qed.
