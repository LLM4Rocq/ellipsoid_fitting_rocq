(* A finite union over ranks and orientations contains the fits.

   Sample space: paper_main_sample N d with the product law
   paper_main_probability N d = gaussian_product_law (N * d).
   1. Finite unions of measurable events with event-dependent bounds have
      probability at most the sum of the bounds
      (paper_main_orientation_union_bound_var; PaperMainGaussianUnion has
      the case of a common bound).
   2. For a family s : nat -> nat and events Ev r k, the union over
      r <= rmax and k < s r is measurable with probability at most
      sum_r s_r p when every event has probability at most p
      (paper_main_orientation_family_union_bound).
   3. paper_main_orientation_union_fit. Suppose that for every rank
      r <= rmax and every orthogonal O there is an event E: measurable, of
      probability at most p, and containing every sample x with a feature
      Gram bound K I (any K >= 0 with K <= N L^2) that admits an admissible
      candidate in orientation O with quadratic risk at most 16 L tau. Take
      the finite family of orientations of
      paper_main_orientation_family_uniform, which does not depend on the
      sample, choose one such event for each member, and use the witness
      paper_main_orientation_fit_witness. Then the union F of the chosen
      events is measurable, has probability at most
        (rmax + 1) exp (C (d + 1)) p
      with C = paper_main_orientation_entropy rmax tau, and contains every
      fit with such a Gram bound. r = 0 and out-of-range indices are
      included (out of range the chosen event is arbitrary and unused). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGaussianUnion PaperMainFeatureGramBlocks PaperMainFeatureLossControl PaperMainMatrixDuality
  PaperMainOrientationNet PaperMainOrientationWitness PaperMainOrientationFamily.
From EllipsoidFitting Require Import RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

(* 1. Finite unions with event-dependent bounds. *)

Lemma paper_main_orientation_union_bound_var D S (E : nat -> set (D.-tuple T)) (b : nat -> R) :
  (forall i, List.In i S -> measurable (E i)) ->
  (forall i, List.In i S -> (gaussian_product_law D (E i) <= (b i)%:E)%E) ->
  (gaussian_product_law D (paper_main_finite_event_union S E) <= (finite_sum b S)%:E)%E.
Proof.
elim: S => [|i S IH] HM HB.
  by rewrite /= measure0.
have HMT : forall j, List.In j S -> measurable (E j) by move=> j Hj; apply: HM; right.
have HBT : forall j, List.In j S -> (gaussian_product_law D (E j) <= (b j)%:E)%E.
  by move=> j Hj; apply: HB; right.
have H0 := HB i (List.in_eq i S).
have HT := IH HMT HBT.
rewrite /=.
apply: le_trans; first exact: (measureU2 _ (HM i (List.in_eq i S))
  (paper_main_gaussian_union_measurable D S E HMT)).
apply: le_trans; first exact: (leeD H0 HT).
by rewrite -EFinD.
Qed.

(* 2. The union over a finite family of members. *)

Definition paper_main_orientation_family_union {D : nat} (rmax : nat) (s : nat -> nat)
    (Ev : nat -> nat -> set (D.-tuple T)) : set (D.-tuple T) :=
  paper_main_finite_event_union (List.seq 0 rmax.+1)
    (fun r => paper_main_finite_event_union (List.seq 0 (s r)) (Ev r)).

Lemma paper_main_orientation_family_union_member {D : nat} (rmax : nat) (s : nat -> nat)
    (Ev : nat -> nat -> set (D.-tuple T)) (r k : nat) (x : D.-tuple T) :
  (r <= rmax)%N -> (k < s r)%N -> Ev r k x -> paper_main_orientation_family_union rmax s Ev x.
Proof.
move=> /ssrnat.leP Hr /ssrnat.ltP Hk Hx.
apply/paper_main_finite_event_union_member; exists r; split.
  by apply/List.in_seq; lia.
apply/paper_main_finite_event_union_member; exists k; split => //.
by apply/List.in_seq; lia.
Qed.

Theorem paper_main_orientation_family_union_bound {D : nat} (rmax : nat) (s : nat -> nat)
    (Ev : nat -> nat -> set (D.-tuple T)) (p : R) :
  (forall r k, (r <= rmax)%N -> (k < s r)%N -> measurable (Ev r k)) ->
  (forall r k, (r <= rmax)%N -> (k < s r)%N -> (gaussian_product_law D (Ev r k) <= p%:E)%E) ->
  measurable (paper_main_orientation_family_union rmax s Ev) /\
  (gaussian_product_law D (paper_main_orientation_family_union rmax s Ev) <=
    ((INR (\sum_(r < rmax.+1) s r) * p)%Rcoq)%:E)%E.
Proof.
move=> HM HB.
have Hr : forall r, List.In r (List.seq 0 rmax.+1) -> (r <= rmax)%N.
  by move=> r /List.in_seq [_ H]; apply/ssrnat.leP; lia.
have Hk : forall r k, List.In k (List.seq 0 (s r)) -> (k < s r)%N.
  by move=> r k /List.in_seq [_ H]; apply/ssrnat.ltP; lia.
have Hin : forall r, List.In r (List.seq 0 rmax.+1) ->
    measurable (paper_main_finite_event_union (List.seq 0 (s r)) (Ev r)).
  move=> r Hr'; apply: paper_main_gaussian_union_measurable => k Hk'.
  exact: HM (Hr r Hr') (Hk r k Hk').
have Hinb : forall r, List.In r (List.seq 0 rmax.+1) ->
    (gaussian_product_law D (paper_main_finite_event_union (List.seq 0 (s r)) (Ev r)) <=
      ((INR (s r) * p)%Rcoq)%:E)%E.
  move=> r Hr'.
  have := paper_main_gaussian_union_bound D (List.seq 0 (s r)) (Ev r) p
    (fun k Hk' => HM r k (Hr r Hr') (Hk r k Hk')) (fun k Hk' => HB r k (Hr r Hr') (Hk r k Hk')).
  by rewrite List.length_seq.
split; first exact: paper_main_gaussian_union_measurable.
apply: le_trans; first exact: (paper_main_orientation_union_bound_var D _ _
  (fun r => (INR (s r) * p)%Rcoq) Hin Hinb).
rewrite lee_fin; apply/RleP.
rewrite finite_sum_seqE INRE natr_sum.
right; rewrite RmultE mulr_suml; apply: eq_bigr => i _.
by rewrite INRE RmultE.
Qed.

(* 3. The finite union over ranks and orientations contains the fits. *)

Theorem paper_main_orientation_union_fit d (eps0 eps tau L p : R) (rmax N : nat) :
  0 < eps0 -> 0 <= eps -> 0 < tau -> tau <= 1 / 8 -> eps0 + tau ^+ 2 <= eps -> 0 <= L ->
  1 / eps0 ^+ 2 <= rmax%:R -> (rmax < d)%N -> (0 < N)%N -> (0 <= p)%Rcoq ->
  (forall r, (r <= rmax)%N -> forall O : 'M[R]_d, O^T *m O = 1%:M ->
    exists E : set (paper_main_sample N d), measurable E /\
      (paper_main_probability N d E <= p%:E)%E /\
      forall (x : paper_main_sample N d) (K : R), 0 <= K ->
        paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
        (K <= INR N * L ^ 2)%Rcoq ->
        (exists (A : 'M[R]_d) (b : R), paper_main_orientation_admissible r O eps L A b /\
           (paper_main_quadratic_risk N d x A b <= 16 * L * tau)%Rcoq) ->
        E x) ->
  exists F : set (paper_main_sample N d), measurable F /\
    (paper_main_probability N d F <=
      ((INR (rmax + 1) * exp (paper_main_orientation_entropy rmax tau * (INR d + 1)) * p)%Rcoq)%:E)%E /\
    forall (x : paper_main_sample N d) (K : R), 0 <= K ->
      paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
      (K <= INR N * L ^ 2)%Rcoq -> paper_main_fit_event N d x -> F x.
Proof.
move=> He0 He Ht Ht8 Heps HL HR HRd HN Hp Hin.
have HtR : (0 < tau)%Rcoq by apply/RltP.
have [s [Os [HC [Hfam Htot]]]] := paper_main_orientation_family_uniform d rmax tau HtR (ltnW HRd).
pose Q := fun (rk : nat * nat) (E : set (paper_main_sample N d)) =>
  (rk.1 <= rmax)%N -> (rk.2 < s rk.1)%N ->
  measurable E /\ (paper_main_probability N d E <= p%:E)%E /\
  forall (x : paper_main_sample N d) (K : R), 0 <= K ->
    paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
    (K <= INR N * L ^ 2)%Rcoq ->
    (exists (A : 'M[R]_d) (b : R),
       paper_main_orientation_admissible rk.1 (Os rk.1 rk.2) eps L A b /\
       (paper_main_quadratic_risk N d x A b <= 16 * L * tau)%Rcoq) ->
    E x.
have HQ : forall rk, exists E, Q rk E.
  move=> [r k].
  case: (boolP (r <= rmax)%N) => Hr; last by exists set0 => Hr'; rewrite Hr' in Hr.
  case: (boolP (k < s r)%N) => Hk; last by exists set0 => _ Hk'; rewrite Hk' in Hk.
  have HOk := (Hfam r Hr).2.1 k Hk.
  have [E HE] := Hin r Hr (Os r k) HOk.
  by exists E.
have [f Hf] := choice HQ.
pose Ev := fun r k => f (r, k).
have HEv : forall r k, (r <= rmax)%N -> (k < s r)%N -> Q (r, k) (Ev r k).
  by move=> r k _ _; exact: Hf.
have [mF PF] := paper_main_orientation_family_union_bound rmax s Ev p
  (fun r k Hr Hk => (HEv r k Hr Hk Hr Hk).1) (fun r k Hr Hk => (HEv r k Hr Hk Hr Hk).2.1).
exists (paper_main_orientation_family_union rmax s Ev).
split => //; split.
  apply: le_trans PF _.
  rewrite lee_fin; apply/RleP.
  have E1 : (INR d + 1 = INR (d + 1))%Rcoq by rewrite addn1 S_INR.
  rewrite E1.
  by apply: Rmult_le_compat_r.
move=> x K HK HG HKN Hfit.
have [r [k [A [b [Hr [Hk [Hadm Hrisk]]]]]]] := paper_main_orientation_fit_witness d eps0 eps tau L K
  rmax s Os N x He0 He (ltW Ht) Ht8 Heps HL HK HR HRd (fun r Hr => (Hfam r Hr).1)
  (fun r k Hr Hk => (Hfam r Hr).2.1 k Hk) (fun r Hr => (Hfam r Hr).2.2.1) HN HG HKN Hfit.
apply: (paper_main_orientation_family_union_member rmax s Ev r k x Hr Hk).
exact: ((HEv r k Hr Hk Hr Hk).2.2 x K HK HG HKN (ex_intro _ A (ex_intro _ b (conj Hadm Hrisk)))).
Qed.
