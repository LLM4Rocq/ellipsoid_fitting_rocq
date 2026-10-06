(* Measurability of the original bulk distance event and conditioning over
   the head data.

   Setting: a standard Gaussian bulk array x with n rows of D coordinates,
   a set A of unit vectors in R^D, and a head matrix F of all n rows with
   q columns. For a deletion set J (rows kept), the residual is
   S_J G v + F_J c with F_J = S_J F, for v in A and head coefficients c.

   1. Uniform margins: the fixed-head section bound and the deletion-set
      union bound hold with a strictly positive margin off the bad set.
   2. The residual is Lipschitz in (v, c). Every small residual is
      witnessed by a point of a finite net of A and a scaled grid point
      for c, at some scale 1/(m+1).
   3. The distance events. distance_lt t: some v in A and some c give a
      residual of norm < t. distance_le t: distance_lt (t + 1/(m+1)) for
      every m, i.e. the infimum over v in A and c is <= t. Both are
      measurable jointly in the head x bulk product space, for a
      head-feature map Fh with measurable entries. No measurable choice of
      a projector or eigenbasis is used: the complement basis of
      Projected.BulkComplement is chosen only after the head is
      fixed, inside the section bound.
   4. The bad event: some J with |J| >= n - k has distance_le at the
      threshold sqrt (|J| - q - 1) - b. For a fixed head matrix and any
      b >= w(A) + u it has probability at most
      (sum_{j <= k} C(n, j)) * exp (- u^2 / 2). Conditioning over the head
      data (paper_main_split_coordinates_section_bound) gives the same bound
      for the joint event under the (kk + n * D)-dimensional Gaussian law
      and under the product law.
   5. The PSD sphere instance with b = sqrt (D / 2) + u and the entropy
      bound exp (k (1 + ln (n / k)) - u^2 / 2).

   The cases q = 0 (no head columns) and kk = 0 (no head coordinates) are
   included; no case split is needed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finset binomial.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Analysis.FiniteSumAlgebra GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability Gordon.ProcessCovariance
  Gordon.SetWidth Gordon.Escape Gaussian.Symmetric.Coordinates
  Projected.BulkLaw Projected.BulkEscape Projected.BulkComplement
  Projected.BulkUnion Spectral.SymmetricDiagonalization Cone.ConditionOperator
  Head.Law Gordon.Nets Gordon.Cover Gordon.NetExistence Spectral.Duality
  Head.SmallBallPZ Head.SectionMeasurable.
From EllipsoidFitting Require Import Analysis.RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Uniform margins. *)

Theorem paper_main_projected_section_margin n D q (J : {set 'I_n}) (F : 'M[R]_(#|J|, q))
    (A : (nat -> R) -> Prop) (u : R) :
  (exists v, A v) -> (forall v, A v -> paper_main_gordon_dot D v v = 1) ->
  (0 <= paper_main_gordon_set_width D A)%Rcoq -> (0 < u)%Rcoq ->
  exists B : set ((n * D).-tuple (measurableTypeR R)),
    measurable B /\
    (gaussian_product_law (n * D) B <= ((exp (- u ^ 2 / 2))%Rcoq)%:E)%E /\
    forall x, ~ B x -> exists eps : R, (0 < eps)%Rcoq /\
      forall (v : nat -> R) (h : 'cV[R]_q), A v ->
        (sqrt (INR (#|J| - q) - 1) - paper_main_gordon_set_width D A - u + eps <=
         sqrt (paper_main_projected_sqnorm (paper_main_projected_selector J *m
           paper_main_projected_bulk_vector n D x v + F *m h)))%Rcoq.
Proof.
move=> HA HAu Hw Hu.
have [s [U [Hs [HU Hsec]]]] := paper_main_projected_section n D q J F.
case: (posnP s) => Hs0.
  have H0 : (#|J| - q = 0)%N by apply/eqP; rewrite -leqn0 -Hs0.
  exists set0; split; first exact: measurable0.
  split.
    rewrite measure0 lee_fin; apply/RleP; apply: Rlt_le; exact: exp_pos.
  move=> x _.
  have Hsq : (sqrt (INR (#|J| - q) - 1) = 0)%Rcoq.
    by rewrite H0; apply: sqrt_neg_0; rewrite /=; lra.
  exists (- (sqrt (INR (#|J| - q) - 1) - paper_main_gordon_set_width D A - u))%Rcoq.
  split; first by rewrite Hsq; lra.
  move=> v h Hv.
  have := sqrt_pos (paper_main_projected_sqnorm (paper_main_projected_selector J *m
    paper_main_projected_bulk_vector n D x v + F *m h)).
  move=> Hpos; apply: Rle_trans Hpos; right; ring.
have Hs' : (0 < s)%coq_nat by apply/ssrnat.ltP.
have [mB PB] := paper_main_projected_escape_tail s n D U A u Hs' HU HA HAu Hu.
eexists; split; first exact: mB.
split; first exact: PB.
move=> x /= Hx.
have Hx' := Rnot_le_lt _ _ Hx.
set e := paper_main_gordon_escape s D A (tval (paper_main_projected_map s n D U x)) in Hx' *.
have H3 : (sqrt (INR (#|J| - q) - 1) <= sqrt (INR s - 1))%Rcoq.
  apply: sqrt_le_1_alt.
  have := le_INR _ _ (ssrnat.leP Hs); lra.
exists (e - (sqrt (INR (#|J| - q) - 1) - paper_main_gordon_set_width D A - u))%Rcoq.
split; first lra.
move=> v h Hv.
have H1 := paper_main_gordon_escape_le s D A v
  (tval (paper_main_projected_map s n D U x)) Hv.
have H2 := Hsec x v h.
have H4 := Rle_trans _ _ _ H1 H2.
rewrite Rplus_minus.
exact: H4.
Qed.

Theorem paper_main_projected_union_margin n D q k (F : 'M[R]_(n, q))
    (A : (nat -> R) -> Prop) (u : R) :
  (exists v, A v) -> (forall v, A v -> paper_main_gordon_dot D v v = 1) ->
  (0 <= paper_main_gordon_set_width D A)%Rcoq -> (0 < u)%Rcoq ->
  exists B : set ((n * D).-tuple (measurableTypeR R)),
    measurable B /\
    (gaussian_product_law (n * D) B <=
      ((INR (\sum_(j < k.+1) 'C(n, j)) * exp (- u ^ 2 / 2))%Rcoq)%:E)%E /\
    forall x, ~ B x -> forall J : {set 'I_n}, (n - k <= #|J|)%N ->
      exists eps : R, (0 < eps)%Rcoq /\
        forall (v : nat -> R) (h : 'cV[R]_q), A v ->
          (sqrt (INR (#|J| - q) - 1) - paper_main_gordon_set_width D A - u + eps <=
           sqrt (paper_main_projected_sqnorm (paper_main_projected_selector J *m
             paper_main_projected_bulk_vector n D x v +
             (paper_main_projected_selector J *m F) *m h)))%Rcoq.
Proof.
move=> HA HAu Hw Hu.
have Hch : forall J : {set 'I_n}, exists BJ : set ((n * D).-tuple (measurableTypeR R)),
    measurable BJ /\
    (gaussian_product_law (n * D) BJ <= ((exp (- u ^ 2 / 2))%Rcoq)%:E)%E /\
    forall x, ~ BJ x -> exists eps : R, (0 < eps)%Rcoq /\
      forall (v : nat -> R) (h : 'cV[R]_q), A v ->
        (sqrt (INR (#|J| - q) - 1) - paper_main_gordon_set_width D A - u + eps <=
         sqrt (paper_main_projected_sqnorm (paper_main_projected_selector J *m
           paper_main_projected_bulk_vector n D x v +
           (paper_main_projected_selector J *m F) *m h)))%Rcoq.
  move=> J.
  exact: (paper_main_projected_section_margin n D q J (paper_main_projected_selector J *m F)
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
move=> x Hx J HJ.
apply: (proj2 (proj2 (HBJ J))) => HxJ.
apply: Hx; apply/paper_main_projected_union_mem.
exists J; split => //.
have Hin : forall (T0 : eqType) (y : T0) (s0 : seq T0), y \in s0 -> List.In y s0.
  move=> T0 y; elim => [|z s0 IH] //=; rewrite inE => /orP [/eqP ->|H]; first by left.
  by right; exact: IH.
by apply: Hin; rewrite /L mem_enum inE.
Qed.

(* Euclidean norms of column vectors: triangle and reverse triangle
   inequalities. *)

Definition paper_main_projected_norm {m : nat} (a : 'cV[R]_m) : R :=
  sqrt (paper_main_projected_sqnorm a).

Lemma paper_main_projected_norm_triangle {m : nat} (a b : 'cV[R]_m) :
  (paper_main_projected_norm (a + b) <=
   paper_main_projected_norm a + paper_main_projected_norm b)%Rcoq.
Proof.
rewrite /paper_main_projected_norm.
have Hsa := paper_main_projected_sqnorm_ge0 a.
have Hsb := paper_main_projected_sqnorm_ge0 b.
set sa := paper_main_projected_sqnorm a in Hsa *.
set sb := paper_main_projected_sqnorm b in Hsb *.
set d := (a^T *m b) 0 0.
have Hexp : paper_main_projected_sqnorm (a + b) = (sa + 2 * d + sb)%Rcoq.
  rewrite /paper_main_projected_sqnorm /sa /sb /d.
  have Ht : (a + b)^T = a^T + b^T by apply/matrixP => i j; rewrite !mxE.
  have addE : forall (X Y : 'M[R]_(1, 1)), (X + Y) 0 0 = X 0 0 + Y 0 0.
    by move=> X Y; rewrite mxE.
  rewrite Ht mulmxDl !mulmxDr !addE (paper_main_symmetric_dotC b a).
  rewrite /paper_main_projected_sqnorm -!RplusE.
  set X := (a^T *m b) 0 0.
  set Y := (a^T *m a) 0 0.
  set Z := (b^T *m b) 0 0.
  lra.
have HCS := pmco_vec_cauchy_schwarz m a b.
move/RleP: HCS => HCS.
have HCS' : (d * d <= sa * sb)%Rcoq.
  move: HCS; rewrite /d /sa /sb /paper_main_projected_sqnorm expr2 -!RmultE.
  set X := (a^T *m b) 0 0; set Y := (a^T *m a) 0 0; set Z := (b^T *m b) 0 0.
  by [].
have Ha0 := sqrt_pos sa; have Hb0 := sqrt_pos sb.
move/RleP: Hsa => Hsa; move/RleP: Hsb => Hsb.
have Ha2 : (sqrt sa * sqrt sa = sa)%Rcoq := sqrt_sqrt sa Hsa.
have Hb2 : (sqrt sb * sqrt sb = sb)%Rcoq := sqrt_sqrt sb Hsb.
set P := (sqrt sa * sqrt sb)%Rcoq.
have HP0 : (0 <= P)%Rcoq by apply: Rmult_le_pos.
have HP2 : (P * P = sa * sb)%Rcoq.
  rewrite /P; transitivity ((sqrt sa * sqrt sa) * (sqrt sb * sqrt sb))%Rcoq; first ring.
  by rewrite Ha2 Hb2.
have Hd : (d <= P)%Rcoq.
  apply: Rnot_lt_le => Hlt.
  have : (P * P < d * d)%Rcoq by nra.
  lra.
rewrite Hexp.
have H1 : (sa + 2 * d + sb <= (sqrt sa + sqrt sb) * (sqrt sa + sqrt sb))%Rcoq.
  have -> : ((sqrt sa + sqrt sb) * (sqrt sa + sqrt sb) =
      (sqrt sa * sqrt sa) + 2 * P + (sqrt sb * sqrt sb))%Rcoq by rewrite /P; ring.
  rewrite Ha2 Hb2; lra.
have H2 := sqrt_le_1_alt _ _ H1.
by rewrite sqrt_square in H2; lra.
Qed.

Lemma paper_main_projected_norm_reverse {m : nat} (a b : 'cV[R]_m) :
  (paper_main_projected_norm a <= paper_main_projected_norm b +
     paper_main_projected_norm (a - b))%Rcoq.
Proof.
have := paper_main_projected_norm_triangle b (a - b).
by rewrite addrC subrK addrC.
Qed.

Lemma paper_main_projected_norm_entry {m : nat} (a : 'cV[R]_m) (L : R) :
  (0 <= L)%Rcoq -> (forall i : 'I_m, (Rabs (a i ord0) <= L)%Rcoq) ->
  (paper_main_projected_norm a <= sqrt (INR m) * L)%Rcoq.
Proof.
move=> HL Ha.
rewrite /paper_main_projected_norm.
have Hs : (paper_main_projected_sqnorm a <= INR m * (L * L))%Rcoq.
  rewrite /paper_main_projected_sqnorm mxE.
  apply/RleP.
  apply: (le_trans (y := \sum_(i < m) (L * L)%Rcoq)).
    apply: ler_sum => i _; rewrite mxE; apply/RleP.
    have Hi := Ha i.
    have H0 := Rabs_pos (a i ord0).
    have Hsq : (a i ord0 * a i ord0 = Rabs (a i ord0) * Rabs (a i ord0))%Rcoq.
      by rewrite -Rabs_mult Rabs_right //; nra.
    rewrite -RmultE.
    have -> : a i 0 = a i ord0 by [].
    rewrite Hsq; apply: Rmult_le_compat => //.
  by rewrite sumr_const card_ord -mulr_natl INRE.
have HmL : (0 <= INR m * (L * L))%Rcoq by apply: Rmult_le_pos; [apply: pos_INR | nra].
apply: Rle_trans (sqrt_le_1_alt _ _ Hs) _.
have H1 : (0 <= L * L)%Rcoq by nra.
rewrite (sqrt_mult _ _ (pos_INR m) H1) sqrt_square //; lra.
Qed.

(* The residual is Lipschitz in (v, c), for fixed bulk array x and head
   matrix F. *)

Definition paper_main_projected_residual n D q (J : {set 'I_n}) (F : 'M[R]_(#|J|, q))
    (x : (n * D).-tuple (measurableTypeR R)) (v : nat -> R) (c : 'cV[R]_q) : 'cV[R]_#|J| :=
  paper_main_projected_selector J *m paper_main_projected_bulk_vector n D x v + F *m c.

Definition paper_main_projected_bulk_size n D (x : (n * D).-tuple (measurableTypeR R)) : R :=
  finite_sum (fun l => Rabs (List.nth l (tval x) 0)) (List.seq 0 (n * D)).

Definition paper_main_projected_head_size {m q : nat} (F : 'M[R]_(m, q)) : R :=
  (\sum_(k < m) \sum_(i < q) Rabs (F k i))%R.

Lemma paper_main_projected_selector_apply {n : nat} (J : {set 'I_n}) (z : 'cV[R]_n)
    (k : 'I_#|J|) :
  (paper_main_projected_selector J *m z) k 0 = z (enum_val k) 0.
Proof.
rewrite mxE (bigD1 (enum_val k)) //= big1 ?addr0.
  by move=> i Hi; rewrite /paper_main_projected_selector mxE eq_sym (negbTE Hi) mul0r.
by rewrite /paper_main_projected_selector mxE eqxx mul1r.
Qed.

Lemma paper_main_projected_bulk_entry_bound n D (x : (n * D).-tuple (measurableTypeR R))
    (w : nat -> R) (delta : R) (i : 'I_n) :
  (0 <= delta)%Rcoq -> (forall j, (j < D)%N -> (Rabs (w j) <= delta)%Rcoq) ->
  (Rabs (paper_main_projected_bulk_vector n D x w i ord0) <=
   delta * (INR D * paper_main_projected_bulk_size n D x))%Rcoq.
Proof.
move=> Hd Hw.
rewrite /paper_main_projected_bulk_vector mxE.
set X := paper_main_projected_bulk_size n D x.
apply: Rle_trans (finite_sum_abs_le _ _) _.
apply: Rle_trans (_ : (finite_sum (fun _ => delta * X) (List.seq 0 D) <= _)%Rcoq).
  apply: finite_sum_le => j Hj.
  have HjD : (j < D)%N by apply/ssrnat.ltP; have := in_seq_lt _ _ Hj; lia.
  rewrite -RmultE Rabs_mult; apply: Rmult_le_compat; try exact: Rabs_pos.
    exact: Hw.
  rewrite /X /paper_main_projected_bulk_size.
  apply: (finite_sum_member (fun l => Rabs (List.nth l (tval x) 0))).
    by move=> l _; exact: Rabs_pos.
  apply/List.in_seq; split; first lia.
  have Hi : (i < n)%N := ltn_ord i.
  apply/ssrnat.ltP.
  apply: (@leq_trans (i.+1 * D)); first by rewrite mulSnr ltn_add2l.
  by rewrite leq_mul2r Hi orbT.
by rewrite finite_sum_const List.length_seq; right; ring.
Qed.

Lemma paper_main_projected_head_entry {m q : nat} (F : 'M[R]_(m, q)) (k : 'I_m) (i : 'I_q) :
  (Rabs (F k i) <= paper_main_projected_head_size F)%Rcoq.
Proof.
apply/RleP; rewrite /paper_main_projected_head_size.
rewrite (bigD1 k) //= (bigD1 i) //= -addrA lerDl.
apply: addr_ge0; first by apply: sumr_ge0 => j _; apply/RleP; exact: Rabs_pos.
apply: sumr_ge0 => k' _; apply: sumr_ge0 => j _; apply/RleP; exact: Rabs_pos.
Qed.

Lemma paper_main_projected_head_apply_bound {m q : nat} (F : 'M[R]_(m, q)) (c : 'cV[R]_q)
    (delta : R) (k : 'I_m) :
  (0 <= delta)%Rcoq -> (forall i : 'I_q, (Rabs (c i ord0) <= delta)%Rcoq) ->
  (Rabs ((F *m c) k ord0) <= delta * (INR q * paper_main_projected_head_size F))%Rcoq.
Proof.
move=> Hd Hc.
rewrite mxE RabsE.
apply/RleP.
apply: (le_trans (ler_norm_sum _ _ _)).
apply: (le_trans (y := \sum_(i < q) (delta * paper_main_projected_head_size F)%Rcoq)).
  apply: ler_sum => i _; rewrite normrM mulrC -RmultE.
  apply/RleP; apply: Rmult_le_compat.
  - rewrite -RabsE; exact: Rabs_pos.
  - rewrite -RabsE; exact: Rabs_pos.
  - have := Hc i; rewrite RabsE; by [].
  - have := paper_main_projected_head_entry F k i; rewrite RabsE; by [].
rewrite sumr_const card_ord -mulr_natl INRE -!RmultE.
by apply/RleP; right; ring.
Qed.

Lemma paper_main_projected_bulk_vector_sub n D (x : (n * D).-tuple (measurableTypeR R))
    (v v' : nat -> R) :
  paper_main_projected_bulk_vector n D x v - paper_main_projected_bulk_vector n D x v' =
  paper_main_projected_bulk_vector n D x (fun j => (v j - v' j)%Rcoq).
Proof.
apply/matrixP => i j; rewrite !mxE.
rewrite -RminusE -finite_sum_minus; apply: finite_sum_ext => l _.
by rewrite -!RmultE; ring.
Qed.

Theorem paper_main_projected_residual_lipschitz n D q (J : {set 'I_n}) (F : 'M[R]_(#|J|, q))
    (x : (n * D).-tuple (measurableTypeR R)) (v v' : nat -> R) (c c' : 'cV[R]_q)
    (delta : R) :
  (0 <= delta)%Rcoq ->
  (forall j, (j < D)%N -> (Rabs (v j - v' j) <= delta)%Rcoq) ->
  (forall i : 'I_q, (Rabs (c i ord0 - c' i ord0) <= delta)%Rcoq) ->
  (paper_main_projected_norm (paper_main_projected_residual n D q J F x v c) <=
   paper_main_projected_norm (paper_main_projected_residual n D q J F x v' c') +
   delta * (sqrt (INR #|J|) * (INR D * paper_main_projected_bulk_size n D x +
     INR q * paper_main_projected_head_size F)))%Rcoq.
Proof.
move=> Hd Hv Hc.
set X := paper_main_projected_bulk_size n D x.
set LF := paper_main_projected_head_size F.
have Hrev := paper_main_projected_norm_reverse (paper_main_projected_residual n D q J F x v c)
  (paper_main_projected_residual n D q J F x v' c').
have Hdiff : paper_main_projected_residual n D q J F x v c -
    paper_main_projected_residual n D q J F x v' c' =
  paper_main_projected_selector J *m
    paper_main_projected_bulk_vector n D x (fun j => (v j - v' j)%Rcoq) +
  F *m (c - c').
  rewrite /paper_main_projected_residual -paper_main_projected_bulk_vector_sub.
  rewrite mulmxBr mulmxBr.
  by rewrite opprD addrACA.
rewrite Hdiff in Hrev.
have Htri := paper_main_projected_norm_triangle
  (paper_main_projected_selector J *m
    paper_main_projected_bulk_vector n D x (fun j => (v j - v' j)%Rcoq))
  (F *m (c - c')).
have HX0 : (0 <= X)%Rcoq.
  by apply: finite_sum_nonnegative => l _; exact: Rabs_pos.
have HLF0 : (0 <= LF)%Rcoq.
  apply/RleP; apply: sumr_ge0 => k _; apply: sumr_ge0 => i _.
  by apply/RleP; exact: Rabs_pos.
have H1 : (paper_main_projected_norm (paper_main_projected_selector J *m
    paper_main_projected_bulk_vector n D x (fun j => (v j - v' j)%Rcoq)) <=
    sqrt (INR #|J|) * (delta * (INR D * X)))%Rcoq.
  apply: paper_main_projected_norm_entry.
    by apply: Rmult_le_pos => //; apply: Rmult_le_pos => //; exact: pos_INR.
  move=> k.
  have -> : (paper_main_projected_selector J *m
      paper_main_projected_bulk_vector n D x (fun j => (v j - v' j)%Rcoq)) k ord0 =
    paper_main_projected_bulk_vector n D x (fun j => (v j - v' j)%Rcoq) (enum_val k) ord0.
    exact: paper_main_projected_selector_apply.
  exact: paper_main_projected_bulk_entry_bound.
have H2 : (paper_main_projected_norm (F *m (c - c')) <=
    sqrt (INR #|J|) * (delta * (INR q * LF)))%Rcoq.
  apply: paper_main_projected_norm_entry.
    by apply: Rmult_le_pos => //; apply: Rmult_le_pos => //; exact: pos_INR.
  move=> k; apply: paper_main_projected_head_apply_bound => // i.
  by rewrite !mxE -RminusE.
have Hs := sqrt_pos (INR #|J|).
apply: (Rle_trans _ _ _ Hrev).
apply: Rplus_le_compat_l.
apply: (Rle_trans _ _ _ Htri).
apply: Rle_trans (Rplus_le_compat _ _ _ _ H1 H2) _.
right; ring.
Qed.

(* Countable witness families: finite nets of A at every scale 1/(m+1), and
   finite grids of [-1, 1]^q at every scale. *)

Lemma paper_main_projected_dot_coordinate d (w : nat -> R) (eps : R) (j : nat) :
  (0 <= eps)%Rcoq -> (paper_main_gordon_dot d w w <= eps ^ 2)%Rcoq -> (j < d)%N ->
  (Rabs (w j) <= eps)%Rcoq.
Proof.
move=> He Hw Hj.
have Hm := finite_sum_member (fun i => (w i * w i)%Rcoq) (List.seq 0 d) j
  (fun i _ => Rle_0_sqr (w i)).
have Hin : List.In j (List.seq 0 d) by apply/List.in_seq; split; [lia | apply/ssrnat.ltP].
have H1 : (w j * w j <= eps * eps)%Rcoq.
  apply: Rle_trans (Hm Hin) _; move: Hw; rewrite /paper_main_gordon_dot /=; lra.
have H0 := Rabs_pos (w j).
have Hsq : (Rabs (w j) * Rabs (w j) = w j * w j)%Rcoq.
  by rewrite -Rabs_mult Rabs_right //; nra.
nra.
Qed.

Lemma paper_main_projected_net_family D (A : (nat -> R) -> Prop) :
  (exists v, A v) -> (forall v, A v -> paper_main_gordon_dot D v v = 1) ->
  exists (s : nat -> nat) (net : nat -> nat -> nat -> R),
    (forall m t, (t < s m)%N -> A (net m t)) /\
    (forall m v, A v -> exists t, (t < s m)%N /\
      forall j, (j < D)%N -> (Rabs (v j - net m t j) <= / INR m.+1)%Rcoq).
Proof.
move=> HA HAu.
have Hch : forall m : nat, exists sv : nat * (nat -> nat -> R),
    (0 < sv.1)%coq_nat /\
    paper_main_gordon_finite_net D A sv.2 (List.seq 0 sv.1) (/ INR m.+1).
  move=> m.
  have Hm : (0 < / INR m.+1)%Rcoq by apply: Rinv_0_lt_compat; apply: lt_0_INR; lia.
  have [s [v [Hs Hnet]]] := paper_main_gordon_finite_net_exists D A (/ INR m.+1) Hm HA HAu.
  by exists (s, v).
have [f Hf] := choice Hch.
exists (fun m => (f m).1), (fun m => (f m).2); split.
  move=> m t Ht; have [_ [Hin _]] := Hf m.
  apply: Hin; apply/List.in_seq; split; first lia.
  by apply/ssrnat.ltP.
move=> m v Hv; have [_ [_ Hcov]] := Hf m.
have [t [Ht Hd]] := Hcov v Hv.
exists t; split.
  by apply/ssrnat.ltP; have := proj1 (List.in_seq _ _ _) Ht; lia.
move=> j Hj.
have He : (0 <= / INR m.+1)%Rcoq.
  by apply: Rlt_le; apply: Rinv_0_lt_compat; apply: lt_0_INR; lia.
exact: (paper_main_projected_dot_coordinate D (fun i => v i - (f m).2 t i) _ j He Hd Hj).
Qed.

Lemma paper_main_projected_grid_family q :
  exists cent : nat -> list R, forall (m : nat) (u : nat -> R),
    (forall i, (i < q)%N -> (Rabs (u i) <= 1)%Rcoq) ->
    exists xs, List.In xs (paper_main_gordon_grid q (cent m)) /\
      forall i, (i < q)%N -> (Rabs (u i - List.nth i xs 0) < / INR m.+1)%Rcoq.
Proof.
have Hch : forall m : nat, exists centers : list R,
    forall y, (-1 <= y <= 1)%Rcoq -> exists c, List.In c centers /\ (Rabs (y - c) < / INR m.+1)%Rcoq.
  move=> m; apply: paper_main_gordon_interval_cover.
  by apply: Rinv_0_lt_compat; apply: lt_0_INR; lia.
have [cent Hcent] := choice Hch.
exists cent => m u Hu.
have [xs [Hxs Hd]] := paper_main_gordon_grid_cover q (cent m) (/ INR m.+1) (Hcent m) u
  (fun i Hi => Hu i (introT (@ssrnat.ltP _ _) Hi)).
exists xs; split => // i Hi.
exact: (Hd i (elimT (@ssrnat.ltP _ _) Hi)).
Qed.

(* Every small residual is witnessed by a net point and a grid point. *)

Definition paper_main_projected_grid_point (q M : nat) (xs : list R) : 'cV[R]_q :=
  \col_(i < q) (INR M * List.nth i xs 0)%Rcoq.

Theorem paper_main_projected_witness n D q (J : {set 'I_n}) (F : 'M[R]_(#|J|, q))
    (x : (n * D).-tuple (measurableTypeR R)) (A : (nat -> R) -> Prop)
    (s : nat -> nat) (net : nat -> nat -> nat -> R) (cent : nat -> list R) (t : R) :
  (forall m v, A v -> exists tt, (tt < s m)%N /\
    forall j, (j < D)%N -> (Rabs (v j - net m tt j) <= / INR m.+1)%Rcoq) ->
  (forall (m : nat) (u : nat -> R), (forall i, (i < q)%N -> (Rabs (u i) <= 1)%Rcoq) ->
    exists xs, List.In xs (paper_main_gordon_grid q (cent m)) /\
      forall i, (i < q)%N -> (Rabs (u i - List.nth i xs 0) < / INR m.+1)%Rcoq) ->
  forall (v : nat -> R) (c : 'cV[R]_q), A v ->
  (paper_main_projected_norm (paper_main_projected_residual n D q J F x v c) < t)%Rcoq ->
  exists m M tt xs, (tt < s m)%N /\ List.In xs (paper_main_gordon_grid q (cent m)) /\
    (paper_main_projected_norm (paper_main_projected_residual n D q J F x (net m tt)
      (paper_main_projected_grid_point q M xs)) < t)%Rcoq.
Proof.
move=> Hnet Hgrid v c Hv Hlt.
set K := (sqrt (INR #|J|) * (INR D * paper_main_projected_bulk_size n D x +
  INR q * paper_main_projected_head_size F))%Rcoq.
have HK : (0 <= K)%Rcoq.
  apply: Rmult_le_pos; first exact: sqrt_pos.
  apply: Rplus_le_le_0_compat; apply: Rmult_le_pos; try exact: pos_INR.
    by apply: finite_sum_nonnegative => l _; exact: Rabs_pos.
  apply/RleP; apply: sumr_ge0 => k _; apply: sumr_ge0 => i _.
  by apply/RleP; exact: Rabs_pos.
set nr := paper_main_projected_norm (paper_main_projected_residual n D q J F x v c) in Hlt.
set gap := (t - nr)%Rcoq.
have Hgap : (0 < gap)%Rcoq by rewrite /gap; lra.
set delta := (gap / (K + 1))%Rcoq.
have Hdelta : (0 < delta)%Rcoq by apply: Rdiv_lt_0_compat; lra.
have HdK : (delta * K < gap)%Rcoq.
  rewrite /delta.
  have -> : (gap / (K + 1) * K = gap * (K / (K + 1)))%Rcoq by field; lra.
  have : (K / (K + 1) < 1)%Rcoq.
    apply: (Rmult_lt_reg_r (K + 1)); first lra.
    by rewrite /Rdiv Rmult_assoc Rinv_l; lra.
  nra.
set Sc := (\sum_(i < q) Rabs (c i ord0))%R.
have HSc0 : (0 <= Sc)%Rcoq.
  by apply/RleP; apply: sumr_ge0 => i _; apply/RleP; exact: Rabs_pos.
have [M HM] := INR_unbounded (Sc + 1)%Rcoq.
have HM1 : (1 <= INR M)%Rcoq by lra.
have HcM : forall i : 'I_q, (Rabs (c i ord0) <= INR M)%Rcoq.
  move=> i; apply: Rle_trans (_ : (Sc <= _)%Rcoq); last by lra.
  apply/RleP; rewrite /Sc (bigD1 i) //= lerDl.
  by apply: sumr_ge0 => j _; apply/RleP; exact: Rabs_pos.
have [m Hm] := INR_unbounded ((INR M + 1) / delta)%Rcoq.
have Hm1 : (0 < INR m.+1)%Rcoq by apply: lt_0_INR; lia.
have Hmd : (INR M / INR m.+1 <= delta /\ / INR m.+1 <= delta)%Rcoq.
  have HmS : ((INR M + 1) / delta < INR m.+1)%Rcoq by rewrite S_INR; lra.
  have H1 : (INR M + 1 < delta * INR m.+1)%Rcoq.
    have := Rmult_lt_compat_l delta _ _ Hdelta HmS.
    have -> : (delta * ((INR M + 1) / delta) = INR M + 1)%Rcoq by field; lra.
    by [].
  split.
    apply: (Rmult_le_reg_r (INR m.+1)) => //.
    rewrite /Rdiv Rmult_assoc Rinv_l; lra.
  apply: (Rmult_le_reg_r (INR m.+1)) => //.
  rewrite Rinv_l; lra.
have [Hmd1 Hmd2] := Hmd.
have [tt [Htt Hvt]] := Hnet m v Hv.
pose u := fun i : nat => oapp (fun i' : 'I_q => (c i' ord0 / INR M)%Rcoq) 0%Rcoq (insub i).
have HuE : forall i : 'I_q, u i = (c i ord0 / INR M)%Rcoq by move=> i; rewrite /u valK.
have HM0 : (0 < INR M)%Rcoq by lra.
have Hu : forall i, (i < q)%N -> (Rabs (u i) <= 1)%Rcoq.
  move=> i Hi.
  have -> : i = Ordinal Hi by [].
  rewrite HuE.
  have Hc := HcM (Ordinal Hi).
  have H1 := Rle_abs (c (Ordinal Hi) ord0).
  have H2 := Rle_abs (- c (Ordinal Hi) ord0); rewrite Rabs_Ropp in H2.
  apply: Rabs_le; split.
    apply: (Rmult_le_reg_r (INR M)) => //.
    rewrite /Rdiv Rmult_assoc Rinv_l; lra.
  apply: (Rmult_le_reg_r (INR M)) => //.
  rewrite /Rdiv Rmult_assoc Rinv_l; lra.
have [xs [Hxs Hxd]] := Hgrid m u Hu.
exists m, M, tt, xs; split => //; split => //.
have Hlip := paper_main_projected_residual_lipschitz n D q J F x (net m tt) v
  (paper_main_projected_grid_point q M xs) c delta (Rlt_le _ _ Hdelta).
have Hvt' : forall j, (j < D)%N -> (Rabs (net m tt j - v j) <= delta)%Rcoq.
  by move=> j Hj; rewrite Rabs_minus_sym; apply: Rle_trans (Hvt j Hj) Hmd2.
have Hct : forall i : 'I_q,
    (Rabs (paper_main_projected_grid_point q M xs i ord0 - c i ord0) <= delta)%Rcoq.
  move=> i.
  rewrite /paper_main_projected_grid_point mxE.
  have Hx := Hxd i (ltn_ord i); rewrite HuE in Hx.
  have -> : (INR M * List.nth i xs 0 - c i ord0 =
      - INR M * (c i ord0 / INR M - List.nth i xs 0))%Rcoq by field; lra.
  rewrite Rabs_mult Rabs_Ropp (Rabs_right (INR M) (Rle_ge _ _ (pos_INR M))).
  apply: Rle_trans (Hmd1).
  have := Rmult_lt_compat_l (INR M) _ _ HM0 Hx.
  rewrite /Rdiv; lra.
have Hfin := Hlip Hvt' Hct.
rewrite -/nr -/K in Hfin.
have : (nr + delta * K < t)%Rcoq by rewrite /gap in HdK; lra.
lra.
Qed.

(* Joint measurability of the residual in the head x bulk product space,
   for a head-feature map Fh with measurable entries. *)

Lemma paper_main_projected_selector_apply_mx {n p : nat} (J : {set 'I_n}) (Z : 'M[R]_(n, p))
    (k : 'I_#|J|) (i : 'I_p) :
  (paper_main_projected_selector J *m Z) k i = Z (enum_val k) i.
Proof.
rewrite mxE (bigD1 (enum_val k)) //= big1 ?addr0.
  by move=> l Hl; rewrite /paper_main_projected_selector mxE eq_sym (negbTE Hl) mul0r.
by rewrite /paper_main_projected_selector mxE eqxx mul1r.
Qed.

Lemma paper_main_projected_residual_entry n D q (J : {set 'I_n}) (F : 'M[R]_(n, q))
    (x : (n * D).-tuple (measurableTypeR R)) (v : nat -> R) (c : 'cV[R]_q) (k : 'I_#|J|) :
  paper_main_projected_residual n D q J (paper_main_projected_selector J *m F) x v c k ord0 =
  ((\sum_(j < D) v j * List.nth (enum_val k * D + j) (tval x) 0) +
   \sum_(i < q) F (enum_val k) i * c i ord0)%R.
Proof.
rewrite /paper_main_projected_residual mxE.
have -> : (paper_main_projected_selector J *m paper_main_projected_bulk_vector n D x v) k ord0 =
    paper_main_projected_bulk_vector n D x v (enum_val k) ord0.
  exact: paper_main_projected_selector_apply.
rewrite /paper_main_projected_bulk_vector mxE finite_sum_seqE.
congr (_ + _)%R.
rewrite mxE; apply: eq_bigr => i _.
by rewrite paper_main_projected_selector_apply_mx.
Qed.

Lemma paper_main_projected_residual_measurable kk n D q (J : {set 'I_n})
    (Fh : kk.-tuple (measurableTypeR R) -> 'M[R]_(n, q)) (v : nat -> R) (c : 'cV[R]_q) :
  (forall a i, measurable_fun [set: kk.-tuple (measurableTypeR R)]
     ((fun h => Fh h a i) : _ -> measurableTypeR R)) ->
  measurable_fun [set: kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R)]
    ((fun p => paper_main_projected_sqnorm (paper_main_projected_residual n D q J
       (paper_main_projected_selector J *m Fh p.1) p.2 v c)) : _ -> measurableTypeR R).
Proof.
move=> HF.
have Hcoord : forall l, measurable_fun
    [set: kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R)]
    ((fun p => List.nth l (tval p.2) 0) : _ -> measurableTypeR R).
  move=> l.
  exact: (measurableT_comp (paper_main_head_small_ball_coord_measurable (n * D) l)
    measurable_snd).
have HFp : forall a i, measurable_fun
    [set: kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R)]
    ((fun p => Fh p.1 a i) : _ -> measurableTypeR R).
  by move=> a i; exact: (measurableT_comp (HF a i) measurable_fst).
have Hentry : forall k : 'I_#|J|, measurable_fun
    [set: kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R)]
    ((fun p => paper_main_projected_residual n D q J
       (paper_main_projected_selector J *m Fh p.1) p.2 v c k ord0) : _ -> measurableTypeR R).
  move=> k.
  have -> : (fun p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) =>
      paper_main_projected_residual n D q J (paper_main_projected_selector J *m Fh p.1)
        p.2 v c k ord0) =
    (fun p => ((\sum_(j < D) v j * List.nth (enum_val k * D + j) (tval p.2) 0) +
      \sum_(i < q) Fh p.1 (enum_val k) i * c i ord0)%R).
    by apply/funext => p; rewrite paper_main_projected_residual_entry.
  apply: measurable_funD.
    apply: measurable_sum => j; apply: measurable_funM; first exact: measurable_cst.
    exact: Hcoord.
  apply: measurable_sum => i; apply: measurable_funM; first exact: HFp.
  exact: measurable_cst.
have -> : (fun p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) =>
    paper_main_projected_sqnorm (paper_main_projected_residual n D q J
      (paper_main_projected_selector J *m Fh p.1) p.2 v c)) =
  (fun p => (\sum_(k < #|J|) paper_main_projected_residual n D q J
      (paper_main_projected_selector J *m Fh p.1) p.2 v c k ord0 *
    paper_main_projected_residual n D q J
      (paper_main_projected_selector J *m Fh p.1) p.2 v c k ord0)%R).
  apply/funext => p; rewrite /paper_main_projected_sqnorm mxE.
  by apply: eq_bigr => k _; rewrite mxE.
apply: measurable_sum => k; apply: measurable_funM; exact: Hentry.
Qed.

Lemma paper_main_projected_residual_lt_measurable kk n D q (J : {set 'I_n})
    (Fh : kk.-tuple (measurableTypeR R) -> 'M[R]_(n, q)) (v : nat -> R) (c : 'cV[R]_q)
    (t : R) :
  (forall a i, measurable_fun [set: kk.-tuple (measurableTypeR R)]
     ((fun h => Fh h a i) : _ -> measurableTypeR R)) ->
  measurable [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
    (paper_main_projected_norm (paper_main_projected_residual n D q J
       (paper_main_projected_selector J *m Fh p.1) p.2 v c) < t)%Rcoq].
Proof.
move=> HF.
have mG := paper_main_projected_residual_measurable kk n D q J Fh v c HF.
case: (Rle_lt_dec t 0) => Ht.
  have -> : [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
      (paper_main_projected_norm (paper_main_projected_residual n D q J
         (paper_main_projected_selector J *m Fh p.1) p.2 v c) < t)%Rcoq] = set0.
    apply/seteqP; split => p //= Hp.
    have H0 := sqrt_pos (paper_main_projected_sqnorm (paper_main_projected_residual n D q J
      (paper_main_projected_selector J *m Fh p.1) p.2 v c)).
    have := Rle_lt_trans _ _ _ H0 Hp; lra.
  exact: measurable0.
set G := fun p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) =>
  paper_main_projected_sqnorm (paper_main_projected_residual n D q J
    (paper_main_projected_selector J *m Fh p.1) p.2 v c).
have -> : [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
    (paper_main_projected_norm (paper_main_projected_residual n D q J
       (paper_main_projected_selector J *m Fh p.1) p.2 v c) < t)%Rcoq] =
  ~` [set p | ((t * t)%Rcoq <= G p)%R].
  apply/seteqP; split => p /=.
    move=> Hp /RleP Hle.
    have H1 := sqrt_le_1_alt _ _ Hle.
    rewrite sqrt_square in H1; first lra.
    have := Rle_lt_trans _ _ _ H1 Hp; lra.
  move=> Hp.
  have Hlt : (G p < t * t)%Rcoq by apply: Rnot_le_lt => H; apply: Hp; apply/RleP.
  have HG0 : (0 <= G p)%Rcoq by apply/RleP; exact: paper_main_projected_sqnorm_ge0.
  have H2 : (sqrt (G p) < sqrt (t * t))%Rcoq by apply: sqrt_lt_1_alt; split.
  rewrite sqrt_square in H2; first lra.
  exact: H2.
apply: measurableC.
exact: (paper_main_head_section_le_measurable (fun _ => (t * t)%Rcoq) G (measurable_cst _) mG).
Qed.

(* The distance events. For a head matrix F_J and a bulk array x,
   distance_lt t says that some v in A and some head coefficients c give a
   residual of norm < t: the distance from S_J G v to the range of F_J,
   minimized over v in A, is < t. distance_le t is the infimum version:
   distance_lt (t + 1/(m+1)) for every m. *)

Definition paper_main_projected_distance_lt n D q (J : {set 'I_n}) (F : 'M[R]_(#|J|, q))
    (x : (n * D).-tuple (measurableTypeR R)) (A : (nat -> R) -> Prop) (t : R) : Prop :=
  exists (v : nat -> R) (c : 'cV[R]_q), A v /\
    (paper_main_projected_norm (paper_main_projected_residual n D q J F x v c) < t)%Rcoq.

Definition paper_main_projected_distance_le n D q (J : {set 'I_n}) (F : 'M[R]_(#|J|, q))
    (x : (n * D).-tuple (measurableTypeR R)) (A : (nat -> R) -> Prop) (t : R) : Prop :=
  forall m : nat, paper_main_projected_distance_lt n D q J F x A (t + / INR m.+1)%Rcoq.

Lemma paper_main_projected_distance_margin n D q (J : {set 'I_n}) (F : 'M[R]_(#|J|, q))
    (x : (n * D).-tuple (measurableTypeR R)) (A : (nat -> R) -> Prop) (t : R) :
  ~ paper_main_projected_distance_le n D q J F x A t ->
  exists eps : R, (0 < eps)%Rcoq /\ forall (v : nat -> R) (c : 'cV[R]_q), A v ->
    (t + eps <= paper_main_projected_norm (paper_main_projected_residual n D q J F x v c))%Rcoq.
Proof.
move=> H.
have [m Hm] : exists m,
    ~ paper_main_projected_distance_lt n D q J F x A (t + / INR m.+1)%Rcoq.
  by apply/existsNP => Hall; apply: H.
exists (/ INR m.+1)%Rcoq; split; first by apply: Rinv_0_lt_compat; apply: lt_0_INR; lia.
move=> v c Hv; apply: Rnot_lt_le => Hlt; apply: Hm; by exists v, c.
Qed.

Lemma paper_main_projected_margin_not_le n D q (J : {set 'I_n}) (F : 'M[R]_(#|J|, q))
    (x : (n * D).-tuple (measurableTypeR R)) (A : (nat -> R) -> Prop) (t eps : R) :
  (0 < eps)%Rcoq ->
  (forall (v : nat -> R) (c : 'cV[R]_q), A v ->
    (t + eps <= paper_main_projected_norm (paper_main_projected_residual n D q J F x v c))%Rcoq) ->
  ~ paper_main_projected_distance_le n D q J F x A t.
Proof.
move=> He Hm Hle.
have [m Hm'] := INR_unbounded (/ eps)%Rcoq.
have Hm1 : (0 < INR m.+1)%Rcoq by apply: lt_0_INR; lia.
have HmS : (/ eps < INR m.+1)%Rcoq by rewrite S_INR; lra.
have H1 : (1 < eps * INR m.+1)%Rcoq.
  have := Rmult_lt_compat_l eps _ _ He HmS.
  by rewrite Rinv_r; lra.
have Hinv : (/ INR m.+1 < eps)%Rcoq.
  apply: (Rmult_lt_reg_r (INR m.+1)) => //.
  rewrite Rinv_l; lra.
have [v [c [Hv Hlt]]] := Hle m.
have := Hm v c Hv.
lra.
Qed.

(* Joint measurability of the distance events in the head x bulk space:
   the strict event is a countable union of residual events at net points
   of A and scaled grid points (paper_main_projected_witness), and the
   infimum event is a countable intersection of strict events. *)

Lemma paper_main_projected_distance_lt_measurable kk n D q (J : {set 'I_n})
    (Fh : kk.-tuple (measurableTypeR R) -> 'M[R]_(n, q)) (A : (nat -> R) -> Prop) (t : R) :
  (forall v, A v -> paper_main_gordon_dot D v v = 1) ->
  (forall a i, measurable_fun [set: kk.-tuple (measurableTypeR R)]
     ((fun h => Fh h a i) : _ -> measurableTypeR R)) ->
  measurable [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
    paper_main_projected_distance_lt n D q J (paper_main_projected_selector J *m Fh p.1) p.2 A t].
Proof.
move=> HAu HF.
case: (pselect (exists v, A v)) => HA; last first.
  have -> : [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
      paper_main_projected_distance_lt n D q J (paper_main_projected_selector J *m Fh p.1)
        p.2 A t] = set0.
    apply/seteqP; split => p //= [v [c [Hv _]]]; apply: HA; by exists v.
  exact: measurable0.
have [s [net [Hin Hcov]]] := paper_main_projected_net_family D A HA HAu.
have [cent Hcent] := paper_main_projected_grid_family q.
pose base (m M tt i : nat) :=
  if (tt < s m)%N && (i < List.length (paper_main_gordon_grid q (cent m)))%N then
    [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
      (paper_main_projected_norm (paper_main_projected_residual n D q J
        (paper_main_projected_selector J *m Fh p.1) p.2 (net m tt)
        (paper_main_projected_grid_point q M
          (List.nth i (paper_main_gordon_grid q (cent m)) [::]))) < t)%Rcoq]
  else set0.
have -> : [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
    paper_main_projected_distance_lt n D q J (paper_main_projected_selector J *m Fh p.1)
      p.2 A t] =
  \bigcup_m \bigcup_M \bigcup_tt \bigcup_i base m M tt i.
  apply/seteqP; split => p /=.
    move=> [v [c [Hv Hlt]]].
    have [m [M [tt [xs [Htt [Hxs Hlt']]]]]] := paper_main_projected_witness n D q J
      (paper_main_projected_selector J *m Fh p.1) p.2 A s net cent t Hcov Hcent v c Hv Hlt.
    have [i [Hi Hnth]] := List.In_nth _ _ [::] Hxs.
    exists m => //; exists M => //; exists tt => //; exists i => //.
    rewrite /base Htt (introT ssrnat.ltP Hi) /= Hnth.
    exact: Hlt'.
  move=> [m _ [M _ [tt _ [i _]]]]; rewrite /base.
  case: ifP => // /andP [Htt _] Hlt.
  exists (net m tt), (paper_main_projected_grid_point q M
    (List.nth i (paper_main_gordon_grid q (cent m)) [::])).
  split => //; exact: Hin.
apply: bigcup_measurable => m _; apply: bigcup_measurable => M _.
apply: bigcup_measurable => tt _; apply: bigcup_measurable => i _.
rewrite /base; case: ifP => _; last exact: measurable0.
exact: paper_main_projected_residual_lt_measurable.
Qed.

Lemma paper_main_projected_distance_le_measurable kk n D q (J : {set 'I_n})
    (Fh : kk.-tuple (measurableTypeR R) -> 'M[R]_(n, q)) (A : (nat -> R) -> Prop) (t : R) :
  (forall v, A v -> paper_main_gordon_dot D v v = 1) ->
  (forall a i, measurable_fun [set: kk.-tuple (measurableTypeR R)]
     ((fun h => Fh h a i) : _ -> measurableTypeR R)) ->
  measurable [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
    paper_main_projected_distance_le n D q J (paper_main_projected_selector J *m Fh p.1) p.2 A t].
Proof.
move=> HAu HF.
have -> : [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
    paper_main_projected_distance_le n D q J (paper_main_projected_selector J *m Fh p.1)
      p.2 A t] =
  \bigcap_m [set p | paper_main_projected_distance_lt n D q J
    (paper_main_projected_selector J *m Fh p.1) p.2 A (t + / INR m.+1)%Rcoq].
  apply/seteqP; split => p /=.
    by move=> H m _; exact: H.
  by move=> H m; exact: H m I.
apply: bigcap_measurable; first by exists 0%N.
move=> m _.
exact: paper_main_projected_distance_lt_measurable.
Qed.

(* The bad event for at most k deleted rows, at threshold
   sqrt (|J| - q - 1) - b: some J with |J| >= n - k has distance_le at
   that threshold. F is the head matrix of all n rows and F_J = S_J F. *)

Definition paper_main_projected_bad n D q k (F : 'M[R]_(n, q))
    (x : (n * D).-tuple (measurableTypeR R)) (A : (nat -> R) -> Prop) (b : R) : Prop :=
  exists J : {set 'I_n}, (n - k <= #|J|)%N /\
    paper_main_projected_distance_le n D q J (paper_main_projected_selector J *m F) x A
      (sqrt (INR (#|J| - q) - 1) - b)%Rcoq.

Lemma paper_main_projected_in_mem {T0 : eqType} (y : T0) (s0 : seq T0) :
  List.In y s0 <-> y \in s0.
Proof.
elim: s0 => [|z s0 IH] //=; rewrite inE; split.
  by case=> [->|H]; [rewrite eqxx | rewrite (proj1 IH H) orbT].
by case/orP => [/eqP ->|H]; [left | right; exact: (proj2 IH H)].
Qed.

Lemma paper_main_projected_bigsetU_measurable {I : Type} {dX : measure_display}
    {X : measurableType dX} (L : seq I) (G : I -> set X) :
  (forall J, measurable (G J)) -> measurable (\big[setU/set0]_(J <- L) G J).
Proof.
move=> HG; elim: L => [|J L IH]; first by rewrite big_nil; exact: measurable0.
by rewrite big_cons; exact: measurableU.
Qed.

Lemma paper_main_projected_bad_measurable kk n D q k
    (Fh : kk.-tuple (measurableTypeR R) -> 'M[R]_(n, q)) (A : (nat -> R) -> Prop) (b : R) :
  (forall v, A v -> paper_main_gordon_dot D v v = 1) ->
  (forall a i, measurable_fun [set: kk.-tuple (measurableTypeR R)]
     ((fun h => Fh h a i) : _ -> measurableTypeR R)) ->
  measurable [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
    paper_main_projected_bad n D q k (Fh p.1) p.2 A b].
Proof.
move=> HAu HF.
set L := enum [set J : {set 'I_n} | (n - k <= #|J|)%N]%SET.
have -> : [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
    paper_main_projected_bad n D q k (Fh p.1) p.2 A b] =
  \big[setU/set0]_(J <- L)
    [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
      paper_main_projected_distance_le n D q J (paper_main_projected_selector J *m Fh p.1)
        p.2 A (sqrt (INR (#|J| - q) - 1) - b)%Rcoq].
  apply/seteqP; split => p /=.
    move=> [J [HJ Hle]]; apply/paper_main_projected_union_mem; exists J; split => //.
    by apply/paper_main_projected_in_mem; rewrite /L mem_enum inE.
  move/paper_main_projected_union_mem => [J [HJ Hle]]; exists J; split => //.
  by move/paper_main_projected_in_mem: HJ; rewrite /L mem_enum inE.
apply: paper_main_projected_bigsetU_measurable => J.
exact: paper_main_projected_distance_le_measurable.
Qed.

(* The bad event contains every attained small residual, and off the bad
   event every admissible J has a uniform margin. *)

Lemma paper_main_projected_not_bad_margin n D q k (F : 'M[R]_(n, q))
    (x : (n * D).-tuple (measurableTypeR R)) (A : (nat -> R) -> Prop) (b : R) :
  ~ paper_main_projected_bad n D q k F x A b ->
  forall J : {set 'I_n}, (n - k <= #|J|)%N ->
    exists eps : R, (0 < eps)%Rcoq /\ forall (v : nat -> R) (c : 'cV[R]_q), A v ->
      (sqrt (INR (#|J| - q) - 1) - b + eps <=
       paper_main_projected_norm (paper_main_projected_residual n D q J
         (paper_main_projected_selector J *m F) x v c))%Rcoq.
Proof.
move=> Hn J HJ.
apply: paper_main_projected_distance_margin => Hle.
by apply: Hn; exists J.
Qed.

(* Conditional bound for an arbitrary fixed head matrix F of all n rows,
   at any offset b >= w(A) + u. *)

Theorem paper_main_projected_fixed_head_tail n D q k (F : 'M[R]_(n, q))
    (A : (nat -> R) -> Prop) (u b : R) :
  (exists v, A v) -> (forall v, A v -> paper_main_gordon_dot D v v = 1) ->
  (0 <= paper_main_gordon_set_width D A)%Rcoq -> (0 < u)%Rcoq ->
  (paper_main_gordon_set_width D A + u <= b)%Rcoq ->
  measurable [set x : (n * D).-tuple (measurableTypeR R) |
    paper_main_projected_bad n D q k F x A b] /\
  (gaussian_product_law (n * D) [set x | paper_main_projected_bad n D q k F x A b] <=
     ((INR (\sum_(j < k.+1) 'C(n, j)) * exp (- u ^ 2 / 2))%Rcoq)%:E)%E.
Proof.
move=> HA HAu Hw Hu Hb.
have mE : measurable [set x : (n * D).-tuple (measurableTypeR R) |
    paper_main_projected_bad n D q k F x A b].
  have H := paper_main_projected_bad_measurable 0 n D q k (fun _ => F) A b HAu
    (fun a i => measurable_cst _).
  have -> : [set x : (n * D).-tuple (measurableTypeR R) |
      paper_main_projected_bad n D q k F x A b] =
    xsection [set p : 0.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
      paper_main_projected_bad n D q k ((fun _ => F) p.1) p.2 A b] [tuple].
    by apply/seteqP; split => x; rewrite /xsection /= inE.
  exact: measurable_xsection.
split => //.
have [B [mB [PB HB]]] := paper_main_projected_union_margin n D q k F A u HA HAu Hw Hu.
apply: le_trans PB.
apply: le_measure; rewrite ?inE //.
move=> x Hx; apply: contrapT => HxB.
have [J [HJ Hle]] := Hx.
have [eps [He Heps]] := HB x HxB J HJ.
apply: (paper_main_projected_margin_not_le n D q J (paper_main_projected_selector J *m F) x A
  (sqrt (INR (#|J| - q) - 1) - b)%Rcoq eps He _ Hle).
move=> v c Hv.
have H1 := Heps v c Hv.
apply: Rle_trans H1; lra.
Qed.

(* Conditioning over the head data: kk head coordinates and a head-feature
   map Fh with measurable entries, independent of the n * D bulk
   coordinates. The joint bad event is measurable and has probability at
   most count * exp (- u^2 / 2), both under the split coordinates of the
   (kk + n * D)-dimensional Gaussian law and under the product law. *)

Theorem paper_main_projected_conditional_tail kk n D q k
    (Fh : kk.-tuple (measurableTypeR R) -> 'M[R]_(n, q)) (A : (nat -> R) -> Prop) (u b : R) :
  (exists v, A v) -> (forall v, A v -> paper_main_gordon_dot D v v = 1) ->
  (0 <= paper_main_gordon_set_width D A)%Rcoq -> (0 < u)%Rcoq ->
  (paper_main_gordon_set_width D A + u <= b)%Rcoq ->
  (forall a i, measurable_fun [set: kk.-tuple (measurableTypeR R)]
     ((fun h => Fh h a i) : _ -> measurableTypeR R)) ->
  measurable [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
    paper_main_projected_bad n D q k (Fh p.1) p.2 A b] /\
  (gaussian_product_law (Nat.add kk (n * D))
    (paper_main_split_coordinates kk (n * D) @^-1`
      [set p | paper_main_projected_bad n D q k (Fh p.1) p.2 A b]) <=
   ((INR (\sum_(j < k.+1) 'C(n, j)) * exp (- u ^ 2 / 2))%Rcoq)%:E)%E /\
  ((gaussian_product_law kk \x gaussian_product_law (n * D))%E
      [set p | paper_main_projected_bad n D q k (Fh p.1) p.2 A b] <=
   ((INR (\sum_(j < k.+1) 'C(n, j)) * exp (- u ^ 2 / 2))%Rcoq)%:E)%E.
Proof.
move=> HA HAu Hw Hu Hb HF.
have mE := paper_main_projected_bad_measurable kk n D q k Fh A b HAu HF.
have Hsplit : (gaussian_product_law (Nat.add kk (n * D))
    (paper_main_split_coordinates kk (n * D) @^-1`
      [set p | paper_main_projected_bad n D q k (Fh p.1) p.2 A b]) <=
   ((INR (\sum_(j < k.+1) 'C(n, j)) * exp (- u ^ 2 / 2))%Rcoq)%:E)%E.
  apply: paper_main_split_coordinates_section_bound => // h.
  have -> : xsection [set p : kk.-tuple (measurableTypeR R) * (n * D).-tuple (measurableTypeR R) |
      paper_main_projected_bad n D q k (Fh p.1) p.2 A b] h =
    [set x | paper_main_projected_bad n D q k (Fh h) x A b].
    by apply/seteqP; split => x; rewrite /xsection /= inE.
  exact: (proj2 (paper_main_projected_fixed_head_tail n D q k (Fh h) A u b HA HAu Hw Hu Hb)).
split => //; split => //.
by rewrite -paper_main_split_coordinates_law.
Qed.

(* The PSD sphere instance: D = paper_main_symmetric_dimension m, offset
   b = sqrt (D / 2) + u >= w + u, and 1 <= k <= n deletions. The joint
   bad event has probability at most exp (k (1 + ln (n / k)) - u^2 / 2). *)

Corollary paper_main_projected_psd_conditional_tail kk n m q k
    (Fh : kk.-tuple (measurableTypeR R) -> 'M[R]_(n, q)) (u : R) :
  (0 < k)%N -> (k <= n)%N -> (0 < u)%Rcoq ->
  (forall a i, measurable_fun [set: kk.-tuple (measurableTypeR R)]
     ((fun h => Fh h a i) : _ -> measurableTypeR R)) ->
  measurable [set p : kk.-tuple (measurableTypeR R) *
      (n * paper_main_symmetric_dimension m).-tuple (measurableTypeR R) |
    paper_main_projected_bad n (paper_main_symmetric_dimension m) q k (Fh p.1) p.2
      (paper_main_projected_psd_set m)
      (sqrt (INR (paper_main_symmetric_dimension m) / 2) + u)%Rcoq] /\
  (gaussian_product_law (Nat.add kk (n * paper_main_symmetric_dimension m))
    (paper_main_split_coordinates kk (n * paper_main_symmetric_dimension m) @^-1`
      [set p | paper_main_projected_bad n (paper_main_symmetric_dimension m) q k (Fh p.1) p.2
        (paper_main_projected_psd_set m)
        (sqrt (INR (paper_main_symmetric_dimension m) / 2) + u)%Rcoq]) <=
   ((exp (INR k * (1 + ln (INR n / INR k)) - u ^ 2 / 2))%Rcoq)%:E)%E /\
  ((gaussian_product_law kk \x gaussian_product_law (n * paper_main_symmetric_dimension m))%E
    [set p | paper_main_projected_bad n (paper_main_symmetric_dimension m) q k (Fh p.1) p.2
      (paper_main_projected_psd_set m)
      (sqrt (INR (paper_main_symmetric_dimension m) / 2) + u)%Rcoq] <=
   ((exp (INR k * (1 + ln (INR n / INR k)) - u ^ 2 / 2))%Rcoq)%:E)%E.
Proof.
move=> Hk Hkn Hu HF.
have [HA HAu] := paper_main_projected_psd_set_unit m.
have [Hw Hw2] := paper_main_projected_psd_width m.
have Hb : (paper_main_gordon_set_width (paper_main_symmetric_dimension m)
    (paper_main_projected_psd_set m) + u <=
    sqrt (INR (paper_main_symmetric_dimension m) / 2) + u)%Rcoq by lra.
have [mE [PE PP]] := paper_main_projected_conditional_tail kk n
  (paper_main_symmetric_dimension m) q k Fh (paper_main_projected_psd_set m) u _ HA HAu Hw Hu
  Hb HF.
have Hcount : (((INR (\sum_(j < k.+1) 'C(n, j)) * exp (- u ^ 2 / 2))%Rcoq)%:E <=
    ((exp (INR k * (1 + ln (INR n / INR k)) - u ^ 2 / 2))%Rcoq)%:E)%E.
  rewrite lee_fin; apply/RleP.
  have Hc := paper_main_projected_count_entropy n k Hk Hkn.
  rewrite -INRE in Hc.
  have He := exp_pos (- u ^ 2 / 2)%Rcoq.
  have Hsplit : (exp (INR k * (1 + ln (INR n / INR k)) - u ^ 2 / 2) =
      exp (INR k * (1 + ln (INR n / INR k))) * exp (- u ^ 2 / 2))%Rcoq.
    rewrite -exp_plus; congr exp; rewrite /Rminus.
    by rewrite /Rdiv Ropp_mult_distr_l.
  rewrite Hsplit.
  by apply: Rmult_le_compat_r; [apply: Rlt_le | ].
split => //; split; [exact: le_trans PE Hcount | exact: le_trans PP Hcount].
Qed.
