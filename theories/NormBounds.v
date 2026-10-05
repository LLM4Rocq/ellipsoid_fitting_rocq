From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

Lemma norm_cap_from_energy (theta D E x : R) :
  0 < theta -> 0 < D -> 0 < E ->
  x ^ 2 <= (theta ^ 2 / D) * E ->
  Rabs (x / sqrt E) <= theta / sqrt D.
Proof.
  intros Htheta HD HE Hx.
  assert (Hse : 0 < sqrt E) by (apply sqrt_lt_R0; exact HE).
  assert (Hsd : 0 < sqrt D) by (apply sqrt_lt_R0; exact HD).
  assert (Hse2 : sqrt E * sqrt E = E) by (apply sqrt_def; lra).
  assert (Hsd2 : sqrt D * sqrt D = D) by (apply sqrt_def; lra).
  assert (Hxd : x * x * D <= theta * theta * E).
  { pose proof (Rmult_le_compat_r D _ _ (Rlt_le _ _ HD) Hx) as H.
    replace (theta ^ 2 / D * E * D) with (theta ^ 2 * E) in H by (field; lra).
    nra. }
  assert (Hsq : Rsqr (Rabs x * sqrt D) <= Rsqr (theta * sqrt E)).
  { rewrite !Rsqr_mult, <- Rsqr_abs, !Rsqr_sqrt by lra.
    unfold Rsqr; nra. }
  assert (Hbound : Rabs x * sqrt D <= theta * sqrt E).
  { apply Rsqr_incr_0_var; [exact Hsq | nra]. }
  unfold Rdiv.
  rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq (sqrt E)) by lra.
  apply (Rmult_le_reg_r (sqrt E * sqrt D)); [nra |].
  replace (Rabs x * / sqrt E * (sqrt E * sqrt D)) with
    (Rabs x * sqrt D) by (field; lra).
  replace (theta * / sqrt D * (sqrt E * sqrt D)) with
    (theta * sqrt E) by (field; lra).
  exact Hbound.
Qed.

Lemma norm_tiny_from_energy (D E : R) :
  0 < D -> 0 <= E -> E <= 1 / D ^ 4 -> sqrt E <= 1 / D ^ 2.
Proof.
  intros HD HE Htiny.
  apply Rsqr_incr_0_var.
  - rewrite Rsqr_sqrt by exact HE.
    replace (Rsqr (1 / D ^ 2)) with (1 / D ^ 4) by
      (unfold Rsqr; simpl; field; lra).
    exact Htiny.
  - apply Rlt_le, Rdiv_lt_0_compat; [lra | apply pow_lt; exact HD].
Qed.
