(* Rotation of full data rows by a fixed orthogonal matrix.

   Conventions: an orientation is O : 'M[R]_d with O^T *m O = 1%:M (then also
   O *m O^T = 1%:M). A sample of N data rows of d coordinates is an
   (N * d)-tuple with coordinate b of row i at position i * d + b. The
   rotated sample has rows O x_i.
   1. The rotation is the covariance image of the block-diagonal loading
      L (k, l) = O (k mod d, l mod d) [k / d = l / d], whose rows are
      orthonormal in R^(N d). The A23 exact law (PaperMainProjectedBulkLaw)
      with arrays of width 1 is the law of any covariance image with
      orthonormal rows, so the rotation keeps the actual Gaussian product
      law for every measurable event. No smooth-test restriction and no
      data-dependent rotation is used.
   2. Point evaluation: row i of the rotated sample is O x_i. The centered
      quadratic value is invariant under conjugation:
      (O g)^T H (O g) - Tr H - b = g^T (O^T H O) g - Tr (O^T H O) - b.
   3. Pullbacks of measurable events by a finite list of rotations have
      union probability at most (number of rotations) times the common
      bound (PaperMainGaussianUnion). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums GaussianCovarianceDefinitions
  GaussianCovarianceLinear GaussianProbabilityProductDefinitions GaussianProbabilityProductMeasure
  GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainSampling PaperMainMatrixDuality
  PaperMainProjectedBulkLaw PaperMainGaussianUnion PaperMainHeadSmallBallNet
  PaperMainGeometryHomogeneous PaperMainConeConditionOperator
  PaperMainHybridFiniteArray PaperMainHybridFiniteMean PaperMainHybridFiniteTail.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

(* 1. Block sums and the block-diagonal loading. *)

Lemma paper_main_orientation_block_sum (f : nat -> R) N d :
  finite_sum f (List.seq 0 (N * d)) =
  finite_sum (fun i => finite_sum (fun q => f (i * d + q)%N) (List.seq 0 d)) (List.seq 0 N).
Proof.
elim: N => [|N IH]; first by [].
rewrite mulSnr -plusE finite_sum_seq_split IH finite_sum_seq_S.
by congr (_ + _).
Qed.

Definition paper_main_orientation_entry {d : nat} (O : 'M[R]_d) (i j : nat) : R :=
  if insub i is Some a then (if insub j is Some b then O a b else 0) else 0.

Lemma paper_main_orientation_entry_ord {d : nat} (O : 'M[R]_d) (a b : 'I_d) :
  paper_main_orientation_entry O a b = O a b.
Proof. by rewrite /paper_main_orientation_entry !valK. Qed.

Lemma paper_main_orientation_divmod a b d :
  (b < d)%N -> ((a * d + b) %/ d = a /\ (a * d + b) %% d = b)%N.
Proof.
move=> Hb; have Hd : (0 < d)%N by apply: leq_ltn_trans Hb.
split; first by rewrite divnMDl // divn_small // addn0.
by rewrite modnMDl modn_small.
Qed.

Definition paper_main_orientation_loading {d : nat} (O : 'M[R]_d) (k l : nat) : R :=
  if (k %/ d == l %/ d)%N then paper_main_orientation_entry O (k %% d) (l %% d) else 0.

Lemma paper_main_orientation_loading_block {d : nat} (O : 'M[R]_d) (k i q : nat) :
  (q < d)%N ->
  paper_main_orientation_loading O k (i * d + q) =
  if (k %/ d == i)%N then paper_main_orientation_entry O (k %% d) q else 0.
Proof.
move=> Hq; have [Ea Eb] := paper_main_orientation_divmod i q d Hq.
by rewrite /paper_main_orientation_loading Ea Eb.
Qed.

(* Rows of the loading are orthonormal in R^(N d). *)

Lemma paper_main_orientation_loading_orthonormal N d (O : 'M[R]_d) :
  O^T *m O = 1%:M ->
  paper_main_projected_orthonormal (N * d) (N * d) (paper_main_orientation_loading O).
Proof.
move=> HO a a' Ha Ha'.
have HO' : O *m O^T = 1%:M by apply: mulmx1C.
have Hd : (0 < d)%N.
  rewrite lt0n; apply/eqP => Hd0; move: Ha; rewrite Hd0 muln0; lia.
have Hqa : (a %% d < d)%N by rewrite ltn_pmod.
have Hqa' : (a' %% d < d)%N by rewrite ltn_pmod.
have Hia : (a %/ d < N)%N by rewrite ltn_divLR //; apply/ssrnat.ltP.
have Hia' : (a' %/ d < N)%N by rewrite ltn_divLR //; apply/ssrnat.ltP.
rewrite /gaussian_covariance_entry paper_main_orientation_block_sum.
set c := (O *m O^T) (Ordinal Hqa) (Ordinal Hqa').
have Hin : forall i, finite_sum (fun q => (paper_main_orientation_loading O a (i * d + q) *
      paper_main_orientation_loading O a' (i * d + q))%Rcoq) (List.seq 0 d) =
    (if (a %/ d == i) && (a' %/ d == i) then c else 0).
  move=> i.
  transitivity (finite_sum (fun q =>
      ((if (a %/ d == i)%N then paper_main_orientation_entry O (a %% d) q else 0) *
       (if (a' %/ d == i)%N then paper_main_orientation_entry O (a' %% d) q else 0))%Rcoq)
      (List.seq 0 d)).
    apply: finite_sum_ext => q Hq.
    have Hqd : (q < d)%N by apply/ssrnat.ltP; have := proj2 (proj1 (List.in_seq _ _ _) Hq); lia.
    by rewrite !paper_main_orientation_loading_block.
  case: (a %/ d == i); case: (a' %/ d == i) => /=.
  - rewrite paper_main_finite_sum_public /c !mxE.
    apply: eq_bigr => q _; rewrite mxE.
    by rewrite -(paper_main_orientation_entry_ord O (Ordinal Hqa))
      -(paper_main_orientation_entry_ord O (Ordinal Hqa')) RmultE.
  - rewrite (finite_sum_ext _ (fun _ => 0%Rcoq)) ?finite_sum_zero // => q _; ring.
  - rewrite (finite_sum_ext _ (fun _ => 0%Rcoq)) ?finite_sum_zero // => q _; ring.
  - rewrite (finite_sum_ext _ (fun _ => 0%Rcoq)) ?finite_sum_zero // => q _; ring.
rewrite (finite_sum_ext _ _ _ (fun i _ => Hin i)).
have Hout : finite_sum (fun i => if (a %/ d == i) && (a' %/ d == i) then c else 0)
    (List.seq 0 N) = (if (a %/ d == a' %/ d)%N then c else 0).
  rewrite paper_main_finite_sum_public (bigD1 (Ordinal Hia)) //= big1 ?addr0.
    move=> i Hi.
    have -> : (a %/ d == i)%N = false.
      apply/negbTE; apply: contra Hi => /eqP E; apply/eqP; apply: val_inj => /=; exact: esym E.
    by [].
  by rewrite eqxx /= eq_sym.
rewrite Hout /c HO' mxE.
case: (Nat.eqb_spec a a') => [Heq|Hne].
  subst a'.
  have -> : Ordinal Hqa = Ordinal Hqa' by apply: val_inj.
  by rewrite !eqxx.
case E1: (a %/ d == a' %/ d)%N => //.
have E2 : (Ordinal Hqa == Ordinal Hqa') = false.
  apply/negbTE/eqP => [[E]]; apply: Hne.
  by rewrite (divn_eq a d) (divn_eq a' d) (eqP E1) E.
by rewrite E2.
Qed.

(* 2. The rotation map and its exact law. *)

Definition paper_main_orientation_rotate N d (O : 'M[R]_d) (x : (N * d).-tuple T) :
    (N * d).-tuple T :=
  tcast (muln1 (N * d)) (paper_main_projected_map (N * d) (N * d) 1
    (paper_main_orientation_loading O) (tcast (esym (muln1 (N * d))) x)).

Lemma paper_main_orientation_rotate_measurable N d (O : 'M[R]_d) :
  measurable_fun [set: (N * d).-tuple T] (paper_main_orientation_rotate N d O).
Proof.
apply: (measurableT_comp (paper_main_tcast_measurable _ _ _)).
apply: (measurableT_comp (paper_main_projected_map_measurable _ _ _ _)).
exact: paper_main_tcast_measurable.
Qed.

Theorem paper_main_orientation_rotate_law N d (O : 'M[R]_d) (E : set ((N * d).-tuple T)) :
  O^T *m O = 1%:M -> measurable E ->
  gaussian_product_law (N * d) (paper_main_orientation_rotate N d O @^-1` E) =
  gaussian_product_law (N * d) E.
Proof.
move=> HO mE.
set E1 := tcast (muln1 (N * d)) @^-1` E.
have mE1 : measurable E1.
  by have := paper_main_tcast_measurable _ _ (muln1 (N * d)) measurableT E mE; rewrite setTI.
set E2 := paper_main_projected_map (N * d) (N * d) 1 (paper_main_orientation_loading O) @^-1` E1.
have mE2 : measurable E2.
  have := paper_main_projected_map_measurable (N * d) (N * d) 1
    (paper_main_orientation_loading O) measurableT E1 mE1.
  by rewrite setTI.
change (gaussian_product_law (N * d) (tcast (esym (muln1 (N * d))) @^-1` E2) =
  gaussian_product_law (N * d) E).
rewrite paper_main_tcast_law /E2.
rewrite (paper_main_projected_law (N * d) (N * d) 1 _ E1
  (paper_main_orientation_loading_orthonormal N d O HO) mE1).
exact: paper_main_tcast_law.
Qed.

(* 3. Point evaluation: row i of the rotated sample is O x_i. *)

Lemma paper_main_orientation_rotate_nth N d (O : 'M[R]_d) (x : (N * d).-tuple T)
    (i : nat) (a : 'I_d) :
  (i < N)%N ->
  List.nth (i * d + a)%N (tval (paper_main_orientation_rotate N d O x)) 0 =
  \sum_(b < d) O a b * List.nth (i * d + b)%N (tval x) 0.
Proof.
move=> Hi.
have Hk : (i * d + a < N * d * 1)%coq_nat.
  have := ltn_ord a; move: Hi => /ssrnat.ltP Hi /ssrnat.ltP Ha.
  rewrite -?multE -?plusE; nia.
rewrite /paper_main_orientation_rotate val_tcast paper_main_projected_map_val
  /paper_main_projected_image /gaussian_covariance_image.
rewrite (nth_map_seq _ _ _ Hk) /gaussian_covariance_row val_tcast.
have Hload : forall k l, paper_main_projected_loading 1 (paper_main_orientation_loading O) k l =
    paper_main_orientation_loading O k l.
  move=> k l; rewrite /paper_main_projected_loading !Nat.div_1_r !Nat.mod_1_r Nat.eqb_refl.
  exact: Rmult_1_r.
rewrite muln1 paper_main_orientation_block_sum.
have [Ea Eb] := paper_main_orientation_divmod i a d (ltn_ord a).
have Hin : forall i', finite_sum (fun q =>
      (paper_main_projected_loading 1 (paper_main_orientation_loading O) (i * d + a) (i' * d + q) *
       List.nth (i' * d + q)%N (tval x) 0)%Rcoq) (List.seq 0 d) =
    if (i == i')%N then \sum_(b < d) O a b * List.nth (i * d + b)%N (tval x) 0 else 0.
  move=> i'.
  rewrite paper_main_finite_sum_public.
  case: (eqVneq i i') => [<-|Hne].
    apply: eq_bigr => q _.
    by rewrite Hload paper_main_orientation_loading_block // Ea Eb eqxx
      paper_main_orientation_entry_ord RmultE.
  rewrite big1 // => q _.
  rewrite Hload paper_main_orientation_loading_block // Ea.
  by rewrite (negbTE Hne) RmultE mul0r.
rewrite (finite_sum_ext _ _ _ (fun i' _ => Hin i')) paper_main_finite_sum_public.
have Hi' : (i < N)%N := Hi.
rewrite (bigD1 (Ordinal Hi')) //=.
rewrite [X in X + _]/= eqxx [X in _ + X]big1 ?addr0 //.
move=> i' Hne.
have -> : (i == i')%N = false.
  apply/negbTE; apply: contra Hne => /eqP E; apply/eqP; apply: val_inj => /=; exact: esym E.
by [].
Qed.

Lemma paper_main_orientation_rotate_point N d (O : 'M[R]_d) (x : (N * d).-tuple T) (i : 'I_N) :
  paper_main_point (paper_main_orientation_rotate N d O x) i = O *m paper_main_point x i.
Proof.
apply/matrixP => a b; rewrite [b]ord1 !mxE paper_main_orientation_rotate_nth //.
by apply: eq_bigr => c _; rewrite mxE.
Qed.

(* 4. The centered quadratic value under conjugation. *)

Lemma paper_main_orientation_form_mx {d : nat} (S : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form S v = (v^T *m S *m v) 0 0.
Proof.
rewrite /paper_main_quadratic_form mxE exchange_big /=.
apply: eq_bigr => j _; rewrite mxE big_distrl /=.
by apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma paper_main_orientation_head_value {d : nat} (O H : 'M[R]_d) (b : R) (g : 'cV[R]_d) :
  O^T *m O = 1%:M ->
  paper_main_head_small_ball_value H b (O *m g) =
  paper_main_head_small_ball_value (O^T *m H *m O) b g.
Proof.
move=> HO; have HO' : O *m O^T = 1%:M by apply: mulmx1C.
rewrite /paper_main_head_small_ball_value !paper_main_orientation_form_mx.
have -> : (O *m g)^T *m H *m (O *m g) = g^T *m (O^T *m H *m O) *m g.
  by rewrite trmx_mul !mulmxA.
have -> : paper_main_trace (O^T *m H *m O) = paper_main_trace H.
  change (\tr (O^T *m H *m O) = \tr H).
  by rewrite mxtrace_mulC mulmxA HO' mul1mx.
by [].
Qed.

(* 5. Finite lists of rotations: pullbacks of events with a common bound. *)

Theorem paper_main_orientation_union N d (Os : nat -> 'M[R]_d) (s : nat)
    (E : nat -> set ((N * d).-tuple T)) (p : R) :
  (forall k, (k < s)%N -> (Os k)^T *m Os k = 1%:M) ->
  (forall k, (k < s)%N -> measurable (E k)) ->
  (forall k, (k < s)%N -> (gaussian_product_law (N * d) (E k) <= p%:E)%E) ->
  measurable (paper_main_finite_event_union (List.seq 0 s)
    (fun k => paper_main_orientation_rotate N d (Os k) @^-1` E k)) /\
  (gaussian_product_law (N * d) (paper_main_finite_event_union (List.seq 0 s)
    (fun k => paper_main_orientation_rotate N d (Os k) @^-1` E k)) <=
   ((INR s * p)%Rcoq)%:E)%E.
Proof.
move=> HO mE PE.
have Hs : forall k, List.In k (List.seq 0 s) -> (k < s)%N.
  move=> k /List.in_seq [_ Hk]; apply/ssrnat.ltP; lia.
have mR : forall k, List.In k (List.seq 0 s) ->
    measurable (paper_main_orientation_rotate N d (Os k) @^-1` E k).
  move=> k Hk.
  have := paper_main_orientation_rotate_measurable N d (Os k) measurableT (E k) (mE k (Hs k Hk)).
  by rewrite setTI.
split; first exact: paper_main_gaussian_union_measurable.
have := paper_main_gaussian_union_bound (N * d) (List.seq 0 s) _ p mR.
rewrite List.length_seq; apply => k Hk.
rewrite (paper_main_orientation_rotate_law N d (Os k) (E k) (HO k (Hs k Hk)) (mE k (Hs k Hk))).
exact: PE (Hs k Hk).
Qed.

(* 6. Pullback of the A26 finite-prior data tail by a finite list of
   orientations, each with its own admissible finite prior. *)

Theorem paper_main_orientation_finite_data_tail (gamma beta eta : R) :
  (1 / 4 < gamma)%Rcoq -> (0 < beta)%Rcoq -> (0 < eta)%Rcoq ->
  exists (C kappa e c : R) (d0 : nat),
    (0 <= C)%Rcoq /\ (0 < kappa)%Rcoq /\ (kappa <= gamma / 2)%Rcoq /\
    (0 < e)%Rcoq /\ (0 < c)%Rcoq /\
    forall (d N r mi s : nat) (Os : nat -> 'M[R]_(r + S mi)%coq_nat) (Is : nat -> list nat)
      (Hs : nat -> nat -> 'M[R]_r) (bs : nat -> nat -> R) (Bs : nat -> nat -> 'M[R]_(S mi))
      (eps Sf t : R),
      (d0 <= d)%N ->
      (Rabs (INR N - gamma * INR d ^ 2) <= kappa * INR d ^ 2)%Rcoq ->
      (INR r <= sqrt (INR d) + 1)%Rcoq -> (r + mi + 1 <= d)%N ->
      (0 <= eps)%Rcoq -> (0 <= Sf)%Rcoq -> (0 < t)%Rcoq ->
      (forall k, (k < s)%N -> (Os k)^T *m Os k = 1%:M) ->
      (forall k, (k < s)%N -> Is k <> nil) ->
      (forall k j, (k < s)%N -> In j (Is k) -> paper_main_symmetric (Hs k j)) ->
      (forall k j, (k < s)%N -> In j (Is k) -> paper_main_psd (Bs k j)) ->
      (forall k j, (k < s)%N -> In j (Is k) ->
         (1 / 4 <= paper_main_frobenius (Hs k j) ^ 2 + paper_main_frobenius (Bs k j) ^ 2)%Rcoq) ->
      (forall k j, (k < s)%N -> In j (Is k) -> paper_main_cone_opnorm_le (Bs k j) eps) ->
      (forall k j, (k < s)%N -> In j (Is k) ->
         (paper_main_frobenius (Bs k j) ^ 2 <= Sf ^ 2)%Rcoq) ->
      measurable (paper_main_finite_event_union (List.seq 0 s) (fun k =>
        paper_main_orientation_rotate N (r + S mi)%coq_nat (Os k) @^-1`
        [set x | (paper_main_hybrid_finite_data N r mi beta (Is k) (Hs k) (bs k) (Bs k) (tval x) <=
          (e * (1 - exp (- c * INR d ^ 2)) - (2 * eta + C * eps * Sf) - t)%Rcoq)%R])) /\
      (gaussian_product_law (N * (r + S mi)%coq_nat)
        (paper_main_finite_event_union (List.seq 0 s) (fun k =>
          paper_main_orientation_rotate N (r + S mi)%coq_nat (Os k) @^-1`
          [set x | (paper_main_hybrid_finite_data N r mi beta (Is k) (Hs k) (bs k) (Bs k) (tval x) <=
            (e * (1 - exp (- c * INR d ^ 2)) - (2 * eta + C * eps * Sf) - t)%Rcoq)%R])) <=
       ((INR s * exp (- (INR N * t ^ 2) / 2))%Rcoq)%:E)%E.
Proof.
move=> Hg Hb He.
have [C [kappa [e [c [d0 [HC [Hk [Hk2 [He' [Hc Htail]]]]]]]]]] :=
  paper_main_hybrid_finite_data_tail gamma beta eta Hg Hb He.
exists C, kappa, e, c, d0; do 5 (split => //).
move=> d N r mi s Os Is Hs bs Bs eps Sf t Hd HN Hr Hmi Heps HS Ht HO HI HHs HBs Hn HOp HF.
apply: (paper_main_orientation_union N (r + S mi)%coq_nat Os s _
  (exp (- (INR N * t ^ 2) / 2)) HO).
- move=> k Hks.
  exact: (Htail d N r mi (Is k) (Hs k) (bs k) (Bs k) eps Sf t Hd HN Hr Hmi (HI k Hks) Heps HS Ht
    (HHs k ^~ Hks) (HBs k ^~ Hks) (Hn k ^~ Hks) (HOp k ^~ Hks) (HF k ^~ Hks)).1.
- move=> k Hks.
  exact: (Htail d N r mi (Is k) (Hs k) (bs k) (Bs k) eps Sf t Hd HN Hr Hmi (HI k Hks) Heps HS Ht
    (HHs k ^~ Hks) (HBs k ^~ Hks) (Hn k ^~ Hks) (HOp k ^~ Hks) (HF k ^~ Hks)).2.
Qed.
