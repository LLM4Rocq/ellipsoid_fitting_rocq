(* Fixed parameter choices for the supercritical loss contradiction. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import PaperMainGordonEntropy PaperMainGordonEntropyMargin.
Open Scope R_scope.

Lemma paper_main_unsat_div_le a b t : 0<b -> a<=t*b -> a/b<=t.
Proof.
intros Hb H; apply (Rmult_le_reg_r b); [exact Hb|].
replace (a/b*b) with a by (field; lra); exact H.
Qed.

Theorem paper_main_unsat_net_parameters e L c : 0<e -> 0<=L -> 0<c ->
  exists delta beta eta, 0<delta /\ 0<beta /\ 0<eta /\
    4*(L+1)*delta<=e/16 /\ 2*eta=e/32 /\
    3*paper_main_gordon_entropy_constant (delta/(L+3))/(c*beta)<=e/16.
Proof.
intros He HL Hc.
set (delta := e/(64*(L+1))).
assert (Hd : 0<delta) by (unfold delta; apply Rdiv_lt_0_compat; lra).
set (E := paper_main_gordon_entropy_constant (delta/(L+3))).
assert (HE : 0<E) by (unfold E; apply paper_main_gordon_entropy_constant_positive; apply Rdiv_lt_0_compat; lra).
set (beta := 1+48*E/(c*e)).
assert (Hb : 0<beta).
{ unfold beta; assert (0<48*E/(c*e)) by (apply Rdiv_lt_0_compat; nra); lra. }
exists delta,beta,(e/64); repeat split; try lra.
- unfold delta; right; field; lra.
- apply paper_main_unsat_div_le; [nra|].
  assert (HB : (beta-1)*c*e=48*E) by (unfold beta; field; lra).
  change (3*E<=e/16*(c*beta)).
  nra.
Qed.

Theorem paper_main_unsat_cutoff_parameters e L C : 0<e -> 0<=L -> 0<=C ->
  exists eps tau, 0<eps /\ 0<tau /\ tau<=1/8 /\
    eps/2+tau^2<=eps /\ 2*C*eps<=e/32 /\ 16*L*tau<=e/16.
Proof.
intros He HL HC.
set (eps := e/(64*(C+1))).
assert (Heps : 0<eps) by (unfold eps; apply Rdiv_lt_0_compat; lra).
set (a := e/(256*(L+1))).
assert (Ha : 0<a) by (unfold a; apply Rdiv_lt_0_compat; lra).
assert (Hs : 0<sqrt(eps/2)) by (apply sqrt_lt_R0; lra).
set (tau := Rmin (1/8) (Rmin (sqrt(eps/2)) a)).
assert (Ht : 0<tau).
{ unfold tau,Rmin; repeat destruct Rle_dec; lra. }
assert (Ht1 : tau<=1/8) by (unfold tau; apply Rmin_l).
assert (Ht2 : tau<=sqrt(eps/2)).
{ eapply Rle_trans; [unfold tau; apply Rmin_r|apply Rmin_l]. }
assert (Ht3 : tau<=a).
{ eapply Rle_trans; [unfold tau; apply Rmin_r|apply Rmin_r]. }
exists eps,tau; repeat split; try assumption.
- pose proof(pow2_sqrt (eps/2) ltac:(lra)); nra.
- assert (HE : eps*(64*(C+1))=e) by (unfold eps; field; lra).
  nra.
- assert (HA : a*(256*(L+1))=e) by (unfold a; field; lra).
  pose proof(Rmult_le_compat_l (256*(L+1)) _ _ ltac:(lra) Ht3).
  nra.
Qed.

Lemma paper_main_unsat_error_budget e L delta beta eta C eps tau E c p :
  0<e -> 4*(L+1)*delta<=e/16 -> 3*E/(c*beta)<=e/16 ->
  2*eta=e/32 -> 2*C*eps<=e/32 -> 16*L*tau<=e/16 -> p<=1/4 ->
  16*L*tau+4*(L+1)*delta+3*E/(c*beta) <
    e*(1-p)-(2*eta+2*C*eps)-e/4.
Proof. intros; nra. Qed.
