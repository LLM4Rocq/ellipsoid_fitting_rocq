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

(* 6. Pullback of the A26 finite-prior data tail by a finite list of
   orientations, each with its own admissible finite prior. *)
