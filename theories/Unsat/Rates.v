(* Fixed-rank orientation unions are dominated by quadratic Gaussian
   tails: scalar rates for the unsatisfiable phase. Deterministic.
   - paper_main_unsat_orientation_exponent: for d >= 1 and d >= 4 C / a,
     exp(C (d + 1)) exp(-a d^2) <= exp(-a d^2 / 2).
   - paper_main_unsat_quadratic_rate: exp(-a d^2 / 2) <= 2 / (a d) for
     d >= 1.
   - paper_main_unsat_orientation_union_limit: a nonnegative sequence that
     is eventually at most K exp(C (d + 1)) exp(-a d^2), with a > 0, tends
     to 0.
   - paper_main_unsat_fixed_rank: if r <= R and d >= R^2 + 1, then r < d
     and r <= sqrt d + 1. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From EllipsoidFitting Require Import Analysis.ContinuousTupleMeasurability
  PaperMainDefinitions.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

Lemma paper_main_unsat_orientation_exponent C a d :
  0<=C -> 0<a -> 1<=d -> 4*C/a<=d ->
  exp(C*(d+1))*exp(-a*d^2)<=exp(-a*d^2/2).
Proof.
intros HC Ha Hd Hlarge; rewrite <-exp_plus.
assert (Hexp : C*(d+1)+ -a*d^2<= -a*d^2/2).
{
pose proof(Rmult_le_compat_r a _ _ ltac:(Stdlib.micromega.Lra.lra) Hlarge) as HH.
replace (4*C/a*a) with (4*C) in HH by (field; Stdlib.micromega.Lra.lra).
pose proof(Rmult_le_compat_r d _ _ ltac:(Stdlib.micromega.Lra.lra) HH).
pose proof(Rmult_le_compat_l C _ _ HC Hd); Stdlib.micromega.Lra.nra. }
destruct (Rle_lt_or_eq_dec _ _ Hexp) as [Hlt|Heq].
- left; apply exp_increasing; exact Hlt.
- rewrite Heq; reflexivity.
Qed.

Lemma paper_main_unsat_quadratic_rate a d :
  0<a -> 1<=d -> exp(-a*d^2/2)<=2/(a*d).
Proof.
intros Ha Hd; set(t:=a*d^2/2).
pose proof(exp_ineq1_le t) as HE; pose proof(exp_pos(-t)) as HP.
assert (HI : exp t * exp (-t) = 1).
{ rewrite <-exp_plus; replace(t + -t) with 0 by ring; exact exp_0. }
pose proof(Rmult_le_compat_r (exp(-t)) _ _ ltac:(Stdlib.micromega.Lra.lra) HE) as HH.
assert (Hd2 : d<=d^2) by Stdlib.micromega.Lra.nra.
assert (Ht : a*d/2<=t).
{ pose proof(Rmult_le_compat_l a _ _ ltac:(Stdlib.micromega.Lra.lra) Hd2); unfold t; Stdlib.micromega.Lra.lra. }
pose proof(Rmult_le_compat_r (exp(-t)) _ _ ltac:(Stdlib.micromega.Lra.lra) Ht) as HM.
replace(-a*d^2/2) with (-t) by (unfold t; Stdlib.micromega.Lra.nra).
apply (Rmult_le_reg_r (a*d)); [Stdlib.micromega.Lra.nra|].
replace (2/(a*d)*(a*d)) with 2 by (field; split; Stdlib.micromega.Lra.lra); Stdlib.micromega.Lra.nra.
Qed.

Theorem paper_main_unsat_orientation_union_limit (p : nat -> \bar R) K C a :
  0<=K -> 0<=C -> 0<a -> (forall d, (0<=p d)%E) ->
  (exists D, forall d, Nat.le D d ->
    (p d<=((K*exp(C*(INR d+1))*exp(-a*(INR d)^2))%Rcoq)%:E)%E) ->
  paper_main_tends_to p 0.
Proof.
move=> HK HC Ha Hp [D HD] eps Heps.
have He : (0<eps)%Rcoq by exact/RltP.
have [J HJ] := INR_unbounded (4*C/a).
have [Q HQ] := INR_unbounded (2*K/(a*eps)).
exists (Nat.max D (S(Nat.max J Q))) => d Hd.
have Hdn : Nat.le (Nat.max D (S(Nat.max J Q))) d by exact: (elimT ssrnat.leP Hd).
have Hd1 : (1<=INR d)%Rcoq by apply (le_INR 1); lia.
have Hlarge : (4*C/a<=INR d)%Rcoq by have := le_INR J d ltac:(lia); Stdlib.micromega.Lra.lra.
have Hlarge2 : (2*K/(a*eps)<INR d)%Rcoq by have := le_INR Q d ltac:(lia); Stdlib.micromega.Lra.lra.
have HE := paper_main_unsat_orientation_exponent C a (INR d) HC Ha Hd1 Hlarge.
have HR := paper_main_unsat_quadratic_rate a (INR d) Ha Hd1.
have HM := Rmult_le_compat_l K _ _ HK (Rle_trans _ _ _ HE HR).
have HB : (K*(2/(a*INR d))<eps)%Rcoq.
{ apply (Rmult_lt_reg_r (a*INR d)); [Stdlib.micromega.Lra.nra|].
  replace (K*(2/(a*INR d))*(a*INR d)) with (2*K) by (field; split; Stdlib.micromega.Lra.lra).
  have H := Rmult_lt_compat_l (a*eps) _ _ ltac:(Stdlib.micromega.Lra.nra) Hlarge2.
  replace ((a*eps)*(2*K/(a*eps))) with (2*K) in H by (field; split; Stdlib.micromega.Lra.lra).
  Stdlib.micromega.Lra.nra. }
rewrite sube0 (gee0_abs (Hp d)).
apply: le_lt_trans (HD d ltac:(lia)) _; rewrite lte_fin; apply/RltP.
change (K*exp(C*(INR d+1))*exp(-a*INR d^2)<eps).
Stdlib.micromega.Lra.nra.
Qed.

Lemma paper_main_unsat_fixed_rank R d r :
  (r<=R)%coq_nat -> Nat.le (Nat.add (Nat.mul R R) 1) d ->
  (r<d)%coq_nat /\ (INR r<=sqrt(INR d)+1)%Rcoq.
Proof.
intros Hr Hd; split; [destruct R; simpl in *; nia|].
pose proof(le_INR _ _ Hr) as HR.
pose proof(le_INR _ _ Hd) as HD.
rewrite plus_INR mult_INR in HD; change (INR 1) with 1 in HD.
pose proof(pow2_sqrt (INR d) (pos_INR d)).
pose proof(sqrt_pos(INR d)); pose proof(pos_INR R); Stdlib.micromega.Lra.nra.
Qed.
