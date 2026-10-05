(* NB trace events for the lower edge (G16, lower edge, part 8).
   Let T m = pmlo_T N ('I_d * 'I_d) (pmnb_X d xs) kap m.
   - pmnbv_reg: xs |-> tr (T L)^p is regular (continuous with a polynomial
     bound), entry by entry.
   - pmnbv_form_trace, pmnbv_opb_trace: for a symmetric Z with
     tr Z^(2^(j+1)) <= t^(2^(j+1)), |v^T Z v| <= t |v|^2; with the
     exponent 2^(j+2), also the operator bound pmlo_opb Z t.
   - pmnbv_event: the event t^p < tr (T L)^p. It is measurable, Markov
     bounds its probability by E tr (T L)^p / t^p (pmnbv_event_markov),
     and pmnct_moment_le bounds the moment (pmnbv_event_le).
   - pmnbv_union: the union of the events for T 1, ..., T K. Its
     probability is at most the sum of the bounds (pmnbv_union_le).
   - Outside the union, for 1 <= t: |v^T T m v| <= t |v|^2 for m <= K
     (pmnbv_out_form); for the exponent 2^(j+2), pmlo_opb (T m) t for
     0 < m <= K (pmnbv_out_opb).
   - pmnbv_box: outside the union, with K = 2^(k+1), operator bounds on
     T 1 - s and on the remainders Psi m + s Psi (m-1) give
     -theta <= T 1 - s <= theta (pmlo_cheb_box).
   No probability premise. *)
From Stdlib Require Import Reals Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments
  PaperMainGeometryHeadCoefficients PaperMainDiagonalBlockTrace PaperMainDiagonalBlockMoment
  PaperMainSquareFreeDiagonal PaperMainSquarefreeWalkExpansion PaperMainSquarefreeEdgeUpper
  PaperMainSquarefreeEdgeLower PaperMainSquarefreeWalkNB PaperMainSquarefreeWalkNBMarks
  PaperMainSquarefreeWalkNBMoment.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope nat_scope.

(* 1. Regularity of the NB trace, entry by entry. *)
Section Regular.
Local Open Scope ring_scope.
Variables (N d : nat) (kap : R).

Lemma pmnbv_mreg_ext {m k} (A B : list R -> 'M[R]_(m, k)) :
  (forall xs, A xs = B xs) -> pmdm_mreg (N * d) A -> pmdm_mreg (N * d) B.
Proof.
move=> E HA a b; apply: (pmdf_regular_ext _ (fun xs => A xs a b)) => [xs|]; first by rewrite E.
exact: HA.
Qed.

Lemma pmnbv_mreg_sumT (I : finType) {m k} (A : I -> list R -> 'M[R]_(m, k)) :
  (forall i, pmdm_mreg (N * d) (A i)) -> pmdm_mreg (N * d) (fun xs => \sum_i A i xs).
Proof.
move=> HA a b.
apply: (pmdf_regular_ext _ (fun xs => \sum_(i <- index_enum I) A i xs a b)) => [xs|].
  by rewrite summxE.
by apply: pmsw_reg_seq => i; exact: HA.
Qed.

Lemma pmnbv_mreg_exp (A : list R -> 'M[R]_N) p :
  pmdm_mreg (N * d) A -> pmdm_mreg (N * d) (fun xs => A xs ^+ p).
Proof.
move=> HA; elim: p => [|p IH].
  apply: (pmnbv_mreg_ext (fun _ => 1%:M)) => [xs|]; first by rewrite expr0.
  exact: pmdm_mreg_const.
apply: (pmnbv_mreg_ext (fun xs => A xs *m A xs ^+ p)) => [xs|]; first by rewrite exprS mulmxE.
exact: pmdm_mreg_mul.
Qed.

Lemma pmnbv_X_reg (u : 'I_N) (c : 'I_d * 'I_d) :
  pmdf_regular (N * d) (fun xs => pmnb_X d xs u c).
Proof.
rewrite /pmnb_X; apply: pmdm_reg_scale; apply: pmdm_reg_mul; apply: pmdm_reg_nth;
  exact: pmdm_index_lt (ltn_ord u) (ltn_ord _).
Qed.

Lemma pmnbv_P_reg (c : 'I_d * 'I_d) :
  pmdm_mreg (N * d) (fun xs => pmlo_P N ('I_d * 'I_d)%type (pmnb_X d xs) kap c).
Proof.
move=> i j.
apply: (pmdf_regular_ext _ (fun xs =>
  if i == j then 0 else kap * (pmnb_X d xs i c * pmnb_X d xs j c))) => [xs|].
  by rewrite mxE.
case: (i == j); first exact: pmdm_reg_const.
by apply: pmdm_reg_scale; apply: pmdm_reg_mul; exact: pmnbv_X_reg.
Qed.

Lemma pmnbv_T_reg L :
  pmdm_mreg (N * d) (fun xs => pmlo_T N ('I_d * 'I_d)%type (pmnb_X d xs) kap L) /\
  forall c, pmdm_mreg (N * d) (fun xs => pmlo_Tc N ('I_d * 'I_d)%type (pmnb_X d xs) kap L c).
Proof.
elim: L => [|L [IH1 IH2]].
  split.
    apply: (pmnbv_mreg_ext (fun _ => 1%:M)) => [xs|]; first by rewrite pmlo_T0.
    exact: pmdm_mreg_const.
  move=> c; apply: (pmnbv_mreg_ext (fun _ => 0)) => [xs|]; first by rewrite pmlo_Tc0.
  exact: pmdm_mreg_const.
have Hc c : pmdm_mreg (N * d) (fun xs => pmlo_P N ('I_d * 'I_d)%type (pmnb_X d xs) kap c *m
    (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d xs) kap L -
     pmlo_Tc N ('I_d * 'I_d)%type (pmnb_X d xs) kap L c)).
  by apply: pmdm_mreg_mul; [exact: pmnbv_P_reg | exact: pmdm_mreg_sub].
split.
  apply: (pmnbv_mreg_ext (fun xs => \sum_c pmlo_P N ('I_d * 'I_d)%type (pmnb_X d xs) kap c *m
    (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d xs) kap L -
     pmlo_Tc N ('I_d * 'I_d)%type (pmnb_X d xs) kap L c))) => [xs|].
    by rewrite pmlo_TS; apply: eq_bigr => c _; rewrite pmlo_TcS.
  exact: pmnbv_mreg_sumT.
move=> c; apply: (pmnbv_mreg_ext _ _ _ (Hc c)) => xs.
by rewrite pmlo_TcS.
Qed.

Lemma pmnbv_reg L p : pmdf_regular (N * d)
  (fun xs => \tr (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d xs) kap L ^+ p)).
Proof.
by apply: pmdm_mreg_tr; apply: pmnbv_mreg_exp; exact: (pmnbv_T_reg L).1.
Qed.

End Regular.

(* 2. From a trace bound to form and operator bounds. *)
Section Forms.
Local Open Scope ring_scope.
Variable n : nat.

Lemma pmnbv_form_trace (Z : 'M[R]_n) (t : R) j (v : 'cV[R]_n) : Z^T = Z -> 0 <= t ->
  \tr (Z ^+ (2 ^ j.+1)) <= t ^+ (2 ^ j.+1) ->
  `|(v^T *m Z *m v) 0 0| <= t * (v^T *m v) 0 0.
Proof.
move=> HZ Ht HT.
have Hn : 0 <= (v^T *m v) 0 0 by exact: pmh_vec_sqr_ge0.
have HL0 : (0 < 2 ^ j.+1)%N by rewrite expn_gt0.
have Hev : ~~ odd (2 ^ j.+1)%N by rewrite oddX.
have H := pmeu_form_pow _ Z v j HZ.
have H' : ((v^T *m Z *m v) 0 0) ^+ (2 ^ j.+1) <= (t * (v^T *m v) 0 0) ^+ (2 ^ j.+1).
  apply: le_trans H _; rewrite exprMn mulrC.
  by apply: ler_wpM2r => //; exact: exprn_ge0.
have Hx : `|(v^T *m Z *m v) 0 0| ^+ (2 ^ j.+1) <= (t * (v^T *m v) 0 0) ^+ (2 ^ j.+1).
  by rewrite -normrX ger0_norm ?exprn_even_ge0.
move: Hx; rewrite ler_pXn2r // ?nnegrE //; exact: mulr_ge0.
Qed.

Lemma pmnbv_opb_trace (Z : 'M[R]_n) (t : R) j : Z^T = Z -> 0 <= t ->
  \tr (Z ^+ (2 ^ j.+2)) <= t ^+ (2 ^ j.+2) -> pmlo_opb n Z t.
Proof.
move=> HZ Ht HT; split => // v.
(* |Z v|^2 = v^T Z^2 v, with the trace bound for Z^2. *)
have HZ2 : (Z *m Z)^T = Z *m Z by rewrite trmx_mul HZ.
have HT2 : \tr ((Z *m Z) ^+ (2 ^ j.+1)) <= (t ^+ 2) ^+ (2 ^ j.+1).
  by rewrite mulmxE -expr2 -!exprM -expnS.
have H := pmnbv_form_trace (Z *m Z) (t ^+ 2) j v HZ2 (exprn_ge0 2 Ht) HT2.
apply: le_trans (ler_norm _) _.
have -> : (Z *m v)^T *m (Z *m v) = v^T *m (Z *m Z) *m v by rewrite trmx_mul HZ !mulmxA.
exact: H.
Qed.

End Forms.

(* 3. The trace events and Markov. *)
Section Event.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition pmnbv_F (N d : nat) (kap : R) (L p : nat) (xs : list R) : R :=
  \tr (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d xs) kap L ^+ p).

Lemma pmnbv_F_ge0 N d kap L j xs : 0 <= pmnbv_F N d kap L (2 ^ j.+1) xs.
Proof.
rewrite /pmnbv_F expnS mul2n -addnn exprD -mulmxE.
have HX := pmeu_trmx_exp _ (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d xs) kap L) (2 ^ j)
  (pmnb_T_sym N _ (pmnb_X d xs) kap L).
by rewrite -{2}HX; exact: pmdb_trace_gram_ge0.
Qed.

Definition pmnbv_event (N d : nat) (kap : R) (L p : nat) (t : R) :
    set (paper_main_sample N d) :=
  [set x | t ^+ p < pmnbv_F N d kap L p (tval x)].

Lemma pmnbv_event_list N d kap L p t :
  pmnbv_event N d kap L p t = [set x | Rlt (t ^+ p) (pmnbv_F N d kap L p (tval x))].
Proof.
by apply/seteqP; split => x /=; rewrite /pmnbv_event /=; move/RltP.
Qed.

Theorem pmnbv_event_measurable N d kap L p t : measurable (pmnbv_event N d kap L p t).
Proof.
rewrite pmnbv_event_list; have [HC _] := pmnbv_reg N d kap L p.
exact: (pmsd_gt_measurable (N * d) (pmnbv_F N d kap L p) (t ^+ p) HC).
Qed.

Definition pmnbv_Xr N d kap L p (x : (N * d).-tuple (measurableTypeR R)) : measurableTypeR R :=
  pmnbv_F N d kap L p (tval x).

Lemma pmnbv_Xr_measurable N d kap L p :
  measurable_fun [set: (N * d).-tuple (measurableTypeR R)] (pmnbv_Xr N d kap L p).
Proof.
have [HC _] := pmnbv_reg N d kap L p.
exact: (gpp_joint_measurable (N * d) (pmnbv_F N d kap L p) HC).
Qed.

Theorem pmnbv_event_markov N d kap L p (t : R) : 0 < t ->
  (forall xs, 0 <= pmnbv_F N d kap L p xs) ->
  (paper_main_probability N d (pmnbv_event N d kap L p t) <=
   (gaussian_iterated_expectation (N * d) (pmnbv_F N d kap L p) / t ^+ p)%:E)%E.
Proof.
move=> Ht Hge.
have HR := pmnbv_reg N d kap L p.
have [HC _] := HR.
have [_ HE] := pmdf_actual (N * d) (pmnbv_F N d kap L p) HR.
pose X : {RV gaussian_product_law (N * d) >-> (R : realType)} :=
  @MeasurableFun.Pack _ _ _ (R : realType) (pmnbv_Xr N d kap L p)
  (MeasurableFun.Class (isMeasurableFun.Build _ _ _ (R : realType) _
  (pmnbv_Xr_measurable N d kap L p))).
have Ht' : 0 < t ^+ p by rewrite exprn_gt0.
have HM := @markov _ _ _ _ X id (t ^+ p) Ht' (@measurable_id _ _ setT)
  (fun r Hr => Hr) (fun r s _ _ Hrs => Hrs).
have HEX : ('E_(gaussian_product_law (N * d))[(id \o (fun x => `|x|%R)) \o X] =
    (gaussian_iterated_expectation (N * d) (pmnbv_F N d kap L p))%:E)%E.
  rewrite unlock -HE; apply: eq_integral => x _ /=.
  by rewrite /pmnbv_Xr ger0_norm.
have Hset : [set x | ((t ^+ p)%:E <= `|(X x)%:E|)%E] =
    [set x : (N * d).-tuple (measurableTypeR R) |
      Rle (t ^+ p) (pmnbv_F N d kap L p (tval x))].
  apply/seteqP; split => x /=.
    by rewrite lee_fin /pmnbv_Xr ger0_norm //; move/RleP.
  by rewrite lee_fin /pmnbv_Xr ger0_norm //; move/RleP.
rewrite Hset HEX in HM.
have Hsub : pmnbv_event N d kap L p t `<=`
    [set x : (N * d).-tuple (measurableTypeR R) | Rle (t ^+ p) (pmnbv_F N d kap L p (tval x))].
  rewrite pmnbv_event_list => x /= Hx; exact: Rlt_le.
have HP : (paper_main_probability N d (pmnbv_event N d kap L p t) <=
    gaussian_product_law (N * d) [set x : (N * d).-tuple (measurableTypeR R) |
      Rle (t ^+ p)%R (pmnbv_F N d kap L p (tval x))])%E.
  rewrite /paper_main_probability; apply: le_measure; rewrite ?inE //.
    exact: pmnbv_event_measurable.
  exact: (pmsd_ge_measurable (N * d) (pmnbv_F N d kap L p) (t ^+ p) HC).
apply: (le_trans HP).
have HM' : (gaussian_product_law (N * d) [set x : (N * d).-tuple (measurableTypeR R) |
      Rle (t ^+ p)%R (pmnbv_F N d kap L p (tval x))] <=
    ((t ^+ p)^-1)%:E * (gaussian_iterated_expectation (N * d) (pmnbv_F N d kap L p))%:E)%E.
  by rewrite lee_pdivlMl.
by apply: (le_trans HM'); rewrite -EFinM lee_fin mulrC.
Qed.

(* The moment bound of PaperMainSquarefreeWalkNBMoment. *)
Definition pmnbv_bound (lam theta c0 : R) (N d m q : nat) : R :=
  ((pmnm_F (q.+1 * m.+1) q.+1)%:R * ((q.+1 * m.+1).+1 ^ 2)%:R *
  (1 + (N * (2 * (q.+1 * m.+1) * d * (4 * (q.+1 * m.+1)) ^ 4))%:R * lam^-1 ^+ 4)
    ^+ (q.+1 * m.+1) *
  (N%:R * (1 + theta * (1 + ((2 * ((q.+1 * m.+1).-1 + 4))%:R +
    ((q.+1 * m.+1).-1 + 2)%:R * (c0 + (2 * (q.+1 * m.+1))%:R) ^+ 2))) ^+ (q.+1 * m.+1) +
   N%:R * (1 + 13%:R * c0 ^+ 2) ^+ 2 + ((4 * (q.+1 * m.+1)) ^ 4)%:R))%R.

Theorem pmnbv_event_le (lam theta c0 : R) N d m q j (t : R) : q.+1 = (2 ^ j.+1)%N ->
  (0 < N)%N -> (0 < d)%N -> (N <= d ^ 2)%N -> 0 < lam -> 0 < theta <= 1 -> 0 <= c0 ->
  (N * 'C(d, 2))%:R <= lam ^+ 4 -> N%:R <= lam ^+ 2 -> d%:R <= c0 * lam ->
  ((4 * (q.+1 * m.+1)) ^ 2)%:R <= lam * theta ^+ 294 ->
  ((4 * (q.+1 * m.+1)) ^ 2 * 4 ^ 45 <= d)%N -> 0 < t ->
  (paper_main_probability N d (pmnbv_event N d (lam^-1 ^+ 2)%R m.+1 q.+1 t) <=
   (pmnbv_bound lam theta c0 N d m q / t ^+ q.+1)%:E)%E.
Proof.
move=> Hq HN Hd HNd Hl Ht Hc0 HNM HN2 Hdl HB HB45 Htp.
have Hge xs : 0 <= pmnbv_F N d (lam^-1 ^+ 2) m.+1 q.+1 xs by rewrite Hq; exact: pmnbv_F_ge0.
apply: (le_trans (pmnbv_event_markov N d (lam^-1 ^+ 2) m.+1 q.+1 t Htp Hge)).
rewrite lee_fin; apply: ler_wpM2r; first by rewrite invr_ge0 exprn_ge0 // ltW.
exact: (pmnct_moment_le lam theta c0 N d m q HN Hd HNd Hl Ht Hc0 HNM HN2 Hdl HB HB45).
Qed.

(* 4. The union over the lengths 1, ..., K. *)
Definition pmnbv_union (N d : nat) (kap : R) (K p : nat) (t : R) :
    set (paper_main_sample N d) :=
  \big[setU/set0]_(m < K) pmnbv_event N d kap m.+1 p t.

Theorem pmnbv_union_measurable N d kap K p t : measurable (pmnbv_union N d kap K p t).
Proof.
by apply: bigsetU_measurable => m _; exact: pmnbv_event_measurable.
Qed.

Theorem pmnbv_union_sum N d kap K p t :
  (paper_main_probability N d (pmnbv_union N d kap K p t) <=
   \sum_(m < K) paper_main_probability N d (pmnbv_event N d kap m.+1 p t))%E.
Proof.
rewrite /paper_main_probability.
apply: (@content_subadditive _ _ _ (gaussian_product_law (N * d)) _
  (fun m => pmnbv_event N d kap m.+1 p t) K).
- by move=> m _; exact: pmnbv_event_measurable.
- exact: pmnbv_union_measurable.
- by [].
Qed.

Theorem pmnbv_union_le (lam theta c0 : R) N d K q j (t : R) : q.+1 = (2 ^ j.+1)%N ->
  (0 < N)%N -> (0 < d)%N -> (N <= d ^ 2)%N -> 0 < lam -> 0 < theta <= 1 -> 0 <= c0 ->
  (N * 'C(d, 2))%:R <= lam ^+ 4 -> N%:R <= lam ^+ 2 -> d%:R <= c0 * lam ->
  ((4 * (q.+1 * K)) ^ 2)%:R <= lam * theta ^+ 294 ->
  ((4 * (q.+1 * K)) ^ 2 * 4 ^ 45 <= d)%N -> 0 < t ->
  (paper_main_probability N d (pmnbv_union N d (lam^-1 ^+ 2)%R K q.+1 t) <=
   (\sum_(m < K) pmnbv_bound lam theta c0 N d m q / t ^+ q.+1)%:E)%E.
Proof.
move=> Hq HN Hd HNd Hl Ht Hc0 HNM HN2 Hdl HB HB45 Htp.
apply: (le_trans (pmnbv_union_sum N d (lam^-1 ^+ 2) K q.+1 t)).
rewrite -sumEFin; apply: lee_sum => m _.
have Hmono : ((4 * (q.+1 * m.+1)) ^ 2 <= (4 * (q.+1 * K)) ^ 2)%N.
  by rewrite leq_exp2r // !leq_mul2l /= ltn_ord.
apply: (pmnbv_event_le lam theta c0 N d m q j t Hq HN Hd HNd Hl Ht Hc0 HNM HN2 Hdl) => //.
  by apply: le_trans HB; rewrite ler_nat.
by apply: leq_trans HB45; rewrite leq_mul2r Hmono orbT.
Qed.

(* 5. Outside the union. *)
Lemma pmnbv_out N d kap K p t (x : paper_main_sample N d) :
  ~ pmnbv_union N d kap K p t x ->
  forall m, (m < K)%N -> pmnbv_F N d kap m.+1 p (tval x) <= t ^+ p.
Proof.
move=> Hx m Hm; rewrite leNgt; apply/negP => Hlt; apply: Hx.
exact: (bigsetU_sup (F := fun m => pmnbv_event N d kap m.+1 p t) Hm).
Qed.

Theorem pmnbv_out_form N d kap K j t (x : paper_main_sample N d) : 1 <= t ->
  ~ pmnbv_union N d kap K (2 ^ j.+1) t x ->
  forall m (v : 'cV[R]_N), (m <= K)%N ->
  `|(v^T *m pmlo_T N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap m *m v) 0 0| <=
  t * (v^T *m v) 0 0.
Proof.
move=> Ht1 Hx [|m] v Hm.
  (* T 0 = 1. *)
  have Hn := pmh_vec_sqr_ge0 _ v.
  rewrite pmlo_T0 mulmx1 ger0_norm //.
  by rewrite -[X in X <= _]mul1r; apply: ler_wpM2r.
apply: pmnbv_form_trace.
- exact: pmnb_T_sym.
- exact: le_trans ler01 Ht1.
- exact: (pmnbv_out N d kap K (2 ^ j.+1) t x Hx m Hm).
Qed.

Theorem pmnbv_out_opb N d kap K j t (x : paper_main_sample N d) : 0 <= t ->
  ~ pmnbv_union N d kap K (2 ^ j.+2) t x ->
  forall m, (0 < m <= K)%N ->
  pmlo_opb N (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap m) t.
Proof.
move=> Ht Hx [|m] // /andP [_ Hm].
apply: pmnbv_opb_trace.
- exact: pmnb_T_sym.
- exact: Ht.
- exact: (pmnbv_out N d kap K (2 ^ j.+2) t x Hx m Hm).
Qed.

(* 6. The Chebyshev box outside the union. *)
Theorem pmnbv_box N d kap s k j (t beta rho theta : R) (x : paper_main_sample N d) :
  0 <= s <= 1 -> 1 <= t -> ~ pmnbv_union N d kap (2 ^ k.+1) (2 ^ j.+1) t x ->
  pmlo_opb N (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap 1 - s *: 1%:M) beta ->
  0 <= rho ->
  (forall m, (0 < m < 2 ^ k.+1)%N ->
     pmlo_opb N (pmlo_Psi N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap s m +
       s *: pmlo_Psi N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap s m.-1) rho) ->
  0 <= theta -> 2 ^+ (2 ^ k.+1) * t + pmlo_rho beta rho (2 ^ k.+1) <= theta ^+ (2 ^ k.+1) ->
  paper_main_loewner_le ((- theta) *: 1%:M)
    (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap 1 - s *: 1%:M) /\
  paper_main_loewner_le (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap 1 - s *: 1%:M)
    (theta *: 1%:M).
Proof.
move=> Hs Ht1 Hx HB Hr HR Hth Hbound.
apply: (pmlo_cheb_box N _ s t beta rho theta
  (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap)
  (fun m => pmlo_Psi N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap s m +
     s *: pmlo_Psi N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap s m.-1) k) => //.
- by rewrite linearB /= linearZ /= trmx1 pmnb_T_sym.
- by rewrite pmlo_T0 mulmx1.
- move=> m; exact: pmlo_knh.
- exact: le_trans ler01 Ht1.
- move=> m v Hm; exact: (pmnbv_out_form N d kap (2 ^ k.+1) j t x Ht1 Hx m v Hm).
Qed.

End Event.
