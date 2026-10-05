(* Uniformity over deletion sets for fixed head data. For n rows and k <= n
   deletions, the deletion sets J with |J| >= n - k number
   sum_(j <= k) C(n, j) (paper_main_projected_count_admissible), and this
   count is at most exp (k (1 + ln (n / k))) for 1 <= k
   (paper_main_projected_count_entropy), from
   sum_(j <= k) C(n, j) t^k <= (1 + t)^n <= exp (t n) at t = k / n. With the
   head matrix F of all rows fixed and F_J = S_J F, the union of the section
   events of PaperMainProjectedBulkComplement over all admissible J is a
   measurable event of probability at most count * exp (- u^2 / 2), off
   which every admissible J, unit direction v in A and head parameter h
   have a restricted residual above sqrt (|J| - q - 1) - w(A) - u
   (paper_main_projected_union_tail). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finset binomial.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainGordonProcessCovariance PaperMainGordonSetWidth
  PaperMainGaussianFeatureCoordinates PaperMainProjectedBulkLaw PaperMainProjectedBulkEscape
  PaperMainProjectedBulkComplement.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Counting deletion sets. *)

Lemma paper_main_projected_count_small n k :
  #|[set D : {set 'I_n} | (#|D| <= k)%N]%SET| = (\sum_(j < k.+1) 'C(n, j))%N.
Proof.
elim: k => [|k IH].
  rewrite big_ord_recl big_ord0 addn0.
  have -> : [set D : {set 'I_n} | (#|D| <= 0)%N]%SET =
      [set D : {set 'I_n} | #|D| == 0%N]%SET.
    by apply/setP => D; rewrite !inE leqn0.
  by rewrite card_draws card_ord.
rewrite big_ord_recr /= -IH.
have -> : [set D : {set 'I_n} | (#|D| <= k.+1)%N]%SET =
    ([set D : {set 'I_n} | (#|D| <= k)%N] :|: [set D : {set 'I_n} | #|D| == k.+1])%SET.
  by apply/setP => D; rewrite !inE leq_eqVlt ltnS orbC.
rewrite cardsU.
have -> : ([set D : {set 'I_n} | (#|D| <= k)%N] :&: [set D : {set 'I_n} | #|D| == k.+1])%SET =
    (finset.set0 : {set {set 'I_n}}).
  apply/setP => D; rewrite !inE.
  by case: eqP => [->|_]; rewrite ?ltnn ?andbF ?andbT.
by rewrite cards0 subn0 card_draws card_ord.
Qed.

Lemma paper_main_projected_card_setC n (J : {set 'I_n}) : #|~: J| = (n - #|J|)%N.
Proof. by rewrite cardsCs finset.setCK card_ord. Qed.

Lemma paper_main_projected_count_admissible n k :
  #|[set J : {set 'I_n} | (n - k <= #|J|)%N]%SET| = (\sum_(j < k.+1) 'C(n, j))%N.
Proof.
rewrite -paper_main_projected_count_small.
have -> : [set D : {set 'I_n} | (#|D| <= k)%N]%SET =
    [set ~: J | J in [set J : {set 'I_n} | (n - k <= #|J|)%N]]%SET.
  apply/setP => D; rewrite inE; apply/idP/imsetP.
    move=> HD; exists (~: D); last by rewrite finset.setCK.
    rewrite inE paper_main_projected_card_setC.
    have HDn : (#|D| <= n)%N by rewrite -[X in (_ <= X)%N](card_ord n) max_card.
    by rewrite leq_sub2l.
  move=> [J HJ ->]; rewrite inE in HJ.
  rewrite paper_main_projected_card_setC leq_subLR addnC -leq_subLR.
  exact: HJ.
by rewrite card_imset //; exact: finset.setC_inj.
Qed.

(* The entropy bound for the count. *)

Lemma paper_main_projected_binomial_partial n k (t : R) :
  (k <= n)%N -> 0 < t -> t <= 1 ->
  (\sum_(j < k.+1) 'C(n, j))%:R * t ^+ k <= (1 + t) ^+ n.
Proof.
move=> Hkn Ht0 Ht1.
have Ht0' : 0 <= t by apply/ltW.
have Hpow : forall j, (j <= k)%N -> t ^+ k <= t ^+ j.
  move=> j Hj.
  rewrite -(subnKC Hj) exprD.
  have H1 := exprn_ile1 (k - j) Ht0' Ht1.
  have H2 : 0 <= t ^+ j by apply: exprn_ge0.
  by rewrite -[X in _ <= X]mulr1 ler_wpM2l.
rewrite exprDn natr_sum mulr_suml.
apply: (le_trans (y := \sum_(j < k.+1) t ^+ j *+ 'C(n, j))).
  apply: ler_sum => j _.
  have -> : t ^+ j *+ 'C(n, j) = 'C(n, j)%:R * t ^+ j by rewrite mulr_natl.
  have Hc : (0 : R) <= ('C(n, j))%:R by exact: ler0n.
  have Hj : t ^+ k <= t ^+ j by apply: Hpow; rewrite -ltnS.
  by rewrite ler_wpM2l.
have -> : \sum_(i < n.+1) 1 ^+ (n - i) * t ^+ i *+ 'C(n, i) =
    \sum_(i < n.+1) t ^+ i *+ 'C(n, i).
  by apply: eq_bigr => i _; rewrite expr1n mul1r.
rewrite (big_ord_widen n.+1 (fun j => t ^+ j *+ 'C(n, j))) //.
rewrite [X in _ <= X](bigID (fun j : 'I_n.+1 => (j < k.+1)%N)) /= lerDl.
apply: sumr_ge0 => j _; rewrite mulrn_wge0 //; exact: exprn_ge0.
Qed.

Lemma paper_main_projected_exp_mul (x : R) (n : nat) : (exp (x * INR n) = exp x ^ n)%Rcoq.
Proof.
elim: n => [|n IH]; first by rewrite /= Rmult_0_r exp_0.
by rewrite S_INR Rmult_plus_distr_l Rmult_1_r exp_plus IH /= Rmult_comm.
Qed.

Theorem paper_main_projected_count_entropy n k : (0 < k)%N -> (k <= n)%N ->
  ((\sum_(j < k.+1) 'C(n, j))%:R <= exp (INR k * (1 + ln (INR n / INR k))))%Rcoq.
Proof.
move=> Hk Hkn.
have HkR : (0 < INR k)%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
have HnR : (0 < INR n)%Rcoq.
  apply: lt_0_INR; apply/ssrnat.ltP; exact: (leq_trans Hk Hkn).
have HknR : (INR k <= INR n)%Rcoq by apply: le_INR; apply/ssrnat.leP.
set t := (INR k / INR n)%Rcoq.
have Ht0 : (0 < t)%Rcoq by apply: Rdiv_lt_0_compat.
have Ht1 : (t <= 1)%Rcoq.
  rewrite /t; apply: (Rmult_le_reg_r (INR n)) => //.
  by rewrite /Rdiv Rmult_assoc Rinv_l; lra.
have H := paper_main_projected_binomial_partial n k t Hkn
  (introT (@RltP _ _) Ht0) (introT (@RleP _ _) Ht1).
move/RleP: H; rewrite -!RpowE -RmultE => H.
rewrite -RplusE in H.
set C := (\sum_(j < k.+1) 'C(n, j))%:R in H *.
have Hexp1 : (1 + t <= exp t)%Rcoq by apply: exp_ineq1_le.
have H2 : ((1 + t) ^ n <= exp t ^ n)%Rcoq by apply: pow_incr; lra.
rewrite -paper_main_projected_exp_mul in H2.
have Htn : (t * INR n = INR k)%Rcoq by rewrite /t; field; lra.
rewrite Htn in H2.
have Htk : (0 < t ^ k)%Rcoq by apply: pow_lt.
have HC : (C * t ^ k <= exp (INR k))%Rcoq := Rle_trans _ _ _ H H2.
have Hnk : (0 < INR n / INR k)%Rcoq by apply: Rdiv_lt_0_compat.
have Hinv : (/ t ^ k = exp (INR k * ln (INR n / INR k)))%Rcoq.
  rewrite -(ln_pow _ Hnk k) (exp_ln _ (pow_lt _ k Hnk)).
  rewrite -pow_inv /t; congr (_ ^ _); field; lra.
have -> : (exp (INR k * (1 + ln (INR n / INR k))) =
    exp (INR k) * exp (INR k * ln (INR n / INR k)))%Rcoq.
  by rewrite -exp_plus; congr exp; ring.
rewrite -Hinv.
apply: (Rmult_le_reg_r (t ^ k)) => //.
rewrite Rmult_assoc Rinv_l; lra.
Qed.

(* Finite unions over a list. *)

Lemma paper_main_projected_union_mem {I : Type} {X : Type} (L : seq I) (G : I -> set X) x :
  (\big[setU/set0]_(J <- L) G J) x <-> exists J, List.In J L /\ G J x.
Proof.
elim: L => [|J L IH]; first by rewrite big_nil; split => // -[J [[]]].
rewrite big_cons; split.
  case=> [HJ|Hx]; first by exists J; split => //; left.
  by have [J' [HJ' Hx']] := proj1 IH Hx; exists J'; split => //; right.
move=> [J' [[<-|HJ'] Hx]]; first by left.
by right; apply/IH; exists J'.
Qed.

Lemma paper_main_projected_union_list {I : Type} {dX : measure_display} {X : measurableType dX}
    (P : probability X R) (L : seq I) (G : I -> set X) (b : R) :
  (forall J, List.In J L -> measurable (G J)) ->
  (forall J, List.In J L -> (P (G J) <= b%:E)%E) ->
  measurable (\big[setU/set0]_(J <- L) G J) /\
  (P (\big[setU/set0]_(J <- L) G J) <= ((size L)%:R * b)%:E)%E.
Proof.
elim: L => [|J L IH] HM HB.
  rewrite big_nil; split; first exact: measurable0.
  by rewrite measure0 /= mul0r.
have HM' : forall J', List.In J' L -> measurable (G J') by move=> J' HJ'; apply: HM; right.
have HB' : forall J', List.In J' L -> (P (G J') <= b%:E)%E by move=> J' HJ'; apply: HB; right.
have [mU PU] := IH HM' HB'.
have mJ : measurable (G J) by apply: HM; left.
rewrite big_cons; split; first exact: measurableU.
apply: le_trans (measureU2 _ mJ mU) _.
apply: le_trans (leeD (HB J (or_introl erefl)) PU) _.
by rewrite -EFinD lee_fin /= mulrSr mulrDl mul1r addrC.
Qed.

(* The uniform event over all deletion sets with |J| >= n - k, for the
   fixed head matrix F of all n rows (F_J = S_J F). *)

Theorem paper_main_projected_union_tail n D q k (F : 'M[R]_(n, q))
    (A : (nat -> R) -> Prop) (u : R) :
  (exists v, A v) -> (forall v, A v -> paper_main_gordon_dot D v v = 1) ->
  (0 <= paper_main_gordon_set_width D A)%Rcoq -> (0 < u)%Rcoq ->
  exists B : set ((n * D).-tuple (measurableTypeR R)),
    measurable B /\
    (gaussian_product_law (n * D) B <=
      ((INR (\sum_(j < k.+1) 'C(n, j)) * exp (- u ^ 2 / 2))%Rcoq)%:E)%E /\
    forall x, ~ B x -> forall J : {set 'I_n}, (n - k <= #|J|)%N ->
      forall (v : nat -> R) (h : 'cV[R]_q), A v ->
        (sqrt (INR (#|J| - q) - 1) - paper_main_gordon_set_width D A - u <
         sqrt (paper_main_projected_sqnorm (paper_main_projected_selector J *m
           paper_main_projected_bulk_vector n D x v +
           (paper_main_projected_selector J *m F) *m h)))%Rcoq.
Proof.
move=> HA HAu Hw Hu.
have Hch : forall J : {set 'I_n}, exists BJ : set ((n * D).-tuple (measurableTypeR R)),
    measurable BJ /\
    (gaussian_product_law (n * D) BJ <= ((exp (- u ^ 2 / 2))%Rcoq)%:E)%E /\
    [set x | exists (v : nat -> R) (h : 'cV[R]_q), A v /\
      (sqrt (paper_main_projected_sqnorm (paper_main_projected_selector J *m
         paper_main_projected_bulk_vector n D x v +
         (paper_main_projected_selector J *m F) *m h)) <=
       sqrt (INR (#|J| - q) - 1) - paper_main_gordon_set_width D A - u)%Rcoq] `<=` BJ.
  move=> J.
  exact: (paper_main_projected_section_tail n D q J (paper_main_projected_selector J *m F)
    A u HA HAu Hw Hu).
have [BJ HBJ] := choice Hch.
set L := enum [set J : {set 'I_n} | (n - k <= #|J|)%N]%SET.
exists (\big[setU/set0]_(J <- L) BJ J).
have [mU PU] := paper_main_projected_union_list (gaussian_product_law (n * D)) L BJ
  (exp (- u ^ 2 / 2))%Rcoq (fun J _ => proj1 (HBJ J)) (fun J _ => proj1 (proj2 (HBJ J))).
split => //; split.
  apply: le_trans PU _; rewrite lee_fin.
  have -> : size L = (\sum_(j < k.+1) 'C(n, j))%N.
    by rewrite /L -cardE paper_main_projected_count_admissible.
  by rewrite INRE.
move=> x Hx J HJ v h Hv.
apply: Rnot_le_lt => Hle.
apply: Hx; apply/paper_main_projected_union_mem.
exists J; split.
  have Hin : forall (T0 : eqType) (y : T0) (s0 : seq T0), y \in s0 -> List.In y s0.
    move=> T0 y; elim => [|z s0 IH] //=; rewrite inE => /orP [/eqP ->|H]; first by left.
    by right; exact: IH.
  by apply: Hin; rewrite /L mem_enum inE.
apply: (proj2 (proj2 (HBJ J))).
by exists v, h.
Qed.

(* The PSD sphere of size m + 1 in R^D, D = paper_main_symmetric_dimension m,
   with the entropy bound for 1 <= k <= n deletions:
   P(B) <= exp (k (1 + ln (n / k)) - u^2 / 2). *)

Corollary paper_main_projected_psd_union_tail n m q k (F : 'M[R]_(n, q)) (u : R) :
  (0 < k)%N -> (k <= n)%N -> (0 < u)%Rcoq ->
  exists B : set ((n * paper_main_symmetric_dimension m).-tuple (measurableTypeR R)),
    measurable B /\
    (gaussian_product_law (n * paper_main_symmetric_dimension m) B <=
      ((exp (INR k * (1 + ln (INR n / INR k)) - u ^ 2 / 2))%Rcoq)%:E)%E /\
    forall x, ~ B x -> forall J : {set 'I_n}, (n - k <= #|J|)%N ->
      forall (v : nat -> R) (h : 'cV[R]_q), paper_main_projected_psd_set m v ->
        (sqrt (INR (#|J| - q) - 1) -
           paper_main_gordon_set_width (paper_main_symmetric_dimension m)
             (paper_main_projected_psd_set m) - u <
         sqrt (paper_main_projected_sqnorm (paper_main_projected_selector J *m
           paper_main_projected_bulk_vector n (paper_main_symmetric_dimension m) x v +
           (paper_main_projected_selector J *m F) *m h)))%Rcoq.
Proof.
move=> Hk Hkn Hu.
have [HA HAu] := paper_main_projected_psd_set_unit m.
have [Hw _] := paper_main_projected_psd_width m.
have [B [mB [PB HB]]] := paper_main_projected_union_tail n
  (paper_main_symmetric_dimension m) q k F (paper_main_projected_psd_set m) u HA HAu Hw Hu.
exists B; split => //; split => //.
apply: le_trans PB _; rewrite lee_fin; apply/RleP.
have Hc := paper_main_projected_count_entropy n k Hk Hkn.
rewrite -INRE in Hc.
have He := exp_pos (- u ^ 2 / 2)%Rcoq.
have Hsplit : (exp (INR k * (1 + ln (INR n / INR k)) - u ^ 2 / 2) =
    exp (INR k * (1 + ln (INR n / INR k))) * exp (- u ^ 2 / 2))%Rcoq.
  rewrite -exp_plus; congr exp; rewrite /Rminus.
  by rewrite /Rdiv Ropp_mult_distr_l.
rewrite Hsplit.
by apply: Rmult_le_compat_r; [apply: Rlt_le | ].
Qed.
