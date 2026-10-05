(* Simultaneous finite orientation families and their logarithmic size.

   Quantifier order: the family depends only on the dimension d and the
   scale tau, never on data.
   1. For tau > 0, a choice over the A27 nets (PaperMainOrientationNet) gives
      s : nat -> nat and Os : nat -> nat -> 'M_d such that for every r <= d:
      s r > 0, each Os r k (k < s r) is orthogonal, every orthogonal O has some
      k < s r with ||P_r(O) - P_r(Os r k)||_F <= tau, and
      ln (s r) <= paper_main_orientation_entropy r tau * (d + 1). r = 0 is included.
   2. paper_main_orientation_entropy r tau is nondecreasing in r for tau > 0, so
      for r <= rmax every ln (s r) <= C (d + 1) with
      C = paper_main_orientation_entropy rmax tau >= 0, independent of d.
   3. Hence s r <= exp (C (d + 1)) and the total count over r <= rmax is at most
      (rmax + 1) exp (C (d + 1)).
   4. For eps0 > 0 there is rmax with 1 / eps0^2 <= rmax (INR_unbounded). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums PaperMainDefinitions
  PaperMainGeometryHomogeneous GaussianProbabilityProductContinuity PaperMainOrientationNet.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 2. Entropy monotonicity. *)

Lemma paper_main_orientation_entropy_nonneg (r : nat) (tau : R) :
  (0 < tau)%Rcoq -> (0 <= paper_main_orientation_entropy r tau)%Rcoq.
Proof.
move=> Ht; rewrite /paper_main_orientation_entropy.
have Hln2 : (0 < ln 2)%Rcoq by rewrite -ln_1; apply: ln_increasing; lra.
have H8 : (0 <= 8 * INR r / tau)%Rcoq.
  apply: Rmult_le_pos; [apply: Rmult_le_pos; [lra|exact: pos_INR]|].
  by apply: Rlt_le; apply: Rinv_0_lt_compat.
by apply: Rmult_le_pos; [apply: Rmult_le_pos; lra|exact: pos_INR].
Qed.

Lemma paper_main_orientation_entropy_monotone (r r' : nat) (tau : R) :
  (0 < tau)%Rcoq -> (r <= r')%N ->
  (paper_main_orientation_entropy r tau <= paper_main_orientation_entropy r' tau)%Rcoq.
Proof.
move=> Ht Hr; rewrite /paper_main_orientation_entropy.
have Hln2 : (0 < ln 2)%Rcoq by rewrite -ln_1; apply: ln_increasing; lra.
have Hinv : (0 < / tau)%Rcoq by apply: Rinv_0_lt_compat.
have HrR : (INR r <= INR r')%Rcoq by apply: le_INR; apply/ssrnat.leP.
have Hr1 : (INR (r + 1) <= INR (r' + 1))%Rcoq.
  by apply: le_INR; apply/ssrnat.leP; rewrite leq_add2r.
have H0 := pos_INR r.
have Ha : ((4 + 8 * INR r / tau) * ln 2 <= (4 + 8 * INR r' / tau) * ln 2)%Rcoq.
  apply: Rmult_le_compat_r; first lra.
  rewrite /Rdiv; have := Rmult_le_compat_r (/ tau) _ _ (Rlt_le _ _ Hinv) HrR; lra.
have Ha0 : (0 <= (4 + 8 * INR r / tau) * ln 2)%Rcoq.
  apply: Rmult_le_pos; last lra.
  rewrite /Rdiv; have := Rmult_le_pos _ _ H0 (Rlt_le _ _ Hinv); lra.
by apply: Rmult_le_compat => //; exact: pos_INR.
Qed.

(* 1. The simultaneous family, for every rank r <= d. *)

Theorem paper_main_orientation_family (d : nat) (tau : R) :
  (0 < tau)%Rcoq ->
  exists (s : nat -> nat) (Os : nat -> nat -> 'M[R]_d),
    forall r, (r <= d)%N ->
      (0 < s r)%N /\
      (forall k, (k < s r)%N -> (Os r k)^T *m Os r k = 1%:M) /\
      (forall O : 'M[R]_d, O^T *m O = 1%:M -> exists k, (k < s r)%N /\
         paper_main_frobenius (paper_main_orientation_projector r O -
           paper_main_orientation_projector r (Os r k)) <= tau) /\
      (ln (INR (s r)) <= paper_main_orientation_entropy r tau * INR (d + 1))%Rcoq.
Proof.
move=> Ht.
pose Q := fun (r : nat) (p : nat * (nat -> 'M[R]_d)) => (r <= d)%N ->
  (0 < p.1)%N /\
  (forall k, (k < p.1)%N -> (p.2 k)^T *m p.2 k = 1%:M) /\
  (forall O : 'M[R]_d, O^T *m O = 1%:M -> exists k, (k < p.1)%N /\
     paper_main_frobenius (paper_main_orientation_projector r O -
       paper_main_orientation_projector r (p.2 k)) <= tau) /\
  (ln (INR p.1) <= paper_main_orientation_entropy r tau * INR (d + 1))%Rcoq.
have HQ : forall r, exists p, Q r p.
  move=> r; case: (leqP r d) => Hr.
    have [s0 [Os0 H]] := paper_main_orientation_net r d tau Hr Ht.
    by exists (s0, Os0) => _.
  by exists (1%N, fun _ => 1%:M) => Hr'; exfalso; move: Hr'; rewrite leqNgt Hr.
have [f Hf] := choice HQ.
exists (fun r => (f r).1), (fun r => (f r).2) => r Hr.
exact: Hf r Hr.
Qed.

(* 3. Uniform and total cardinality for r <= rmax, with C = entropy at rmax. *)

Theorem paper_main_orientation_family_uniform (d rmax : nat) (tau : R) :
  (0 < tau)%Rcoq -> (rmax <= d)%N ->
  exists (s : nat -> nat) (Os : nat -> nat -> 'M[R]_d),
    (0 <= paper_main_orientation_entropy rmax tau)%Rcoq /\
    (forall r, (r <= rmax)%N ->
      (0 < s r)%N /\
      (forall k, (k < s r)%N -> (Os r k)^T *m Os r k = 1%:M) /\
      (forall O : 'M[R]_d, O^T *m O = 1%:M -> exists k, (k < s r)%N /\
         paper_main_frobenius (paper_main_orientation_projector r O -
           paper_main_orientation_projector r (Os r k)) <= tau) /\
      (ln (INR (s r)) <= paper_main_orientation_entropy rmax tau * INR (d + 1))%Rcoq /\
      (INR (s r) <= exp (paper_main_orientation_entropy rmax tau * INR (d + 1)))%Rcoq) /\
    (INR (\sum_(r < rmax.+1) s r) <=
      INR (rmax + 1) * exp (paper_main_orientation_entropy rmax tau * INR (d + 1)))%Rcoq.
Proof.
move=> Ht Hrd.
have [s [Os Hfam]] := paper_main_orientation_family d tau Ht.
set C := paper_main_orientation_entropy rmax tau.
have HC : (0 <= C)%Rcoq by exact: paper_main_orientation_entropy_nonneg.
have Hd1 : (0 <= INR (d + 1))%Rcoq by exact: pos_INR.
have Hper : forall r, (r <= rmax)%N ->
    (0 < s r)%N /\
    (forall k, (k < s r)%N -> (Os r k)^T *m Os r k = 1%:M) /\
    (forall O : 'M[R]_d, O^T *m O = 1%:M -> exists k, (k < s r)%N /\
       paper_main_frobenius (paper_main_orientation_projector r O -
         paper_main_orientation_projector r (Os r k)) <= tau) /\
    (ln (INR (s r)) <= C * INR (d + 1))%Rcoq /\
    (INR (s r) <= exp (C * INR (d + 1)))%Rcoq.
  move=> r Hr.
  have [Hs [HO [Hcov Hent]]] := Hfam r (leq_trans Hr Hrd).
  have Hmono := paper_main_orientation_entropy_monotone r rmax tau Ht Hr.
  have Hln : (ln (INR (s r)) <= C * INR (d + 1))%Rcoq.
    apply: Rle_trans Hent _; apply: Rmult_le_compat_r => //.
  split => //; split => //; split => //; split => //.
  have Hspos : (0 < INR (s r))%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
  rewrite -(exp_ln _ Hspos).
  case: (Rle_lt_or_eq_dec _ _ Hln) => [Hlt|->]; last exact: Rle_refl.
  by left; apply: exp_increasing.
exists s, Os; split => //; split => //.
rewrite INRE natr_sum (INRE (rmax + 1)); apply/RleP.
apply: (@le_trans _ _ (\sum_(r < rmax.+1) exp (C * INR (d + 1)))).
  apply: ler_sum => r _.
  have Hr : (r <= rmax)%N by rewrite -ltnS ltn_ord.
  have [_ [_ [_ [_ Hexp]]]] := Hper r Hr.
  by rewrite -INRE; apply/RleP.
set E := exp (C * INR (d + 1)).
rewrite sumr_const card_ord.
have -> : ((rmax + 1)%:R * E)%Rcoq = E *+ rmax.+1 by rewrite RmultE mulr_natl addn1.
exact: lexx.
Qed.

(* 4. A finite rank bound at the cutoff eps0. *)

Lemma paper_main_orientation_rank_bound (eps0 : R) :
  0 < eps0 -> exists rmax : nat,
    1 / eps0 ^+ 2 <= rmax%:R /\ (1 / eps0 ^ 2 <= INR rmax)%Rcoq.
Proof.
move=> He.
have [n Hn] := INR_unbounded (1 / eps0 ^ 2)%Rcoq.
exists n.
have Hle : (1 / eps0 ^ 2 <= INR n)%Rcoq by apply: Rlt_le.
split => //.
by rewrite -INRE; apply/RleP; rewrite -RpowE -RdivE.
Qed.
