(* Robustness of the mixture theorems in total variation, at Stdlib's R:
   item R1 of phase 9 (notes/phase6-three-extensions.md, section 3.2;
   notes/optional-items-plan.md, item R1; lane A). Required as
   From EllipsoidUniversality.Countable Require Import Robust.

   Proved here.
   - robust_statement_holds : robust_statement and
     robust_interpolation_holds : robust_interpolation_statement. Let nu_d
     be the point law of the countable family (rob_nu, a cmixture of
     product laws, equal to robust_point_law by rob_nuE) and Q_d that of
     its truncation of Countable/Truncation (rob_Q, a finite mixture). For
     every law P of a point and every measurable set E of samples, the
     samples of n i.i.d. points of law P and the samples of the family
     differ by at most n (tv(P, nu_d) + 2 r_d) on E (robust_transfer).
     From P to Q_d, tuple_prod_tv gives n tv(P, Q_d), and tv(P, Q_d) <=
     tv(P, nu_d) + r_d (rob_nu_Q_tv). The samples of Q_d have the law
     mixture_probability of the truncated family (rob_Q_sample, by
     tuple_prod_mixture and tuple_prod_rows), and trunc_coupling bounds the
     last step by n r_d. When d^2 tv(P_d, nu_d) -> 0 and n_d / d^2 ->
     alpha, the error tends to 0 (robust_err_small), so the limits and the
     small probabilities of countable_theorem carry over (robust_tends),
     with its constants. The samples are read as lists of points by
     robust_points, whose image of a measurable set is measurable
     (robust_points_image, measurable_robust_image).
   - rob_nu_sample, the exact identity (phase 10, item I): for every
     measurable set E of samples, the samples of n i.i.d. points of law
     nu_d have the law countable_mixture_probability, by
     tuple_prod_cmixture of library/probability/countable_mixture.v and
     tuple_prod_rows. Hence robust_transfer_tv: the samples of law P and
     those of the family differ by at most n tv(P, nu_d) on E, with no
     truncation term (tuple_prod_tv). The proofs of the statements above
     keep the route through the truncation.
   - contamination_holds : contamination_statement.
     (a) The contaminated components s < N keep their laws, with weights
     multiplied by 1 - lambda / n, and the component N, the zero point, has
     the weight lambda / n. On every measurable set the two point laws
     differ by lambda / n times the difference of two numbers of [0, 1]
     (contaminated_tv_set), so n tv <= lambda (contaminated_tv).
     (b) Labels that contain N give the fit event probability 0, since that
     point is 0 and x^T S x = 0 for it (contaminated_null). The other label
     tuples are those of the family, with weights multiplied by
     (1 - lambda / n)^n (sum_tuple_lift, contaminated_lift). So the
     probability of a positive definite fit of value one is (1 - lambda /
     n)^n times that of the family (contaminated_probability). Below the
     threshold the latter tends to 1 by mixture_theorem, and (1 - lambda /
     n)^n tends to expR (- lambda) (pow_one_sub_dist, contaminated_limit).
   - robust_theorem_holds : robust_theorem_statement. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import esum exp ereal measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis Require Import lindeberg.
From GaussianAnalysis.probability Require Import mixture countable_mixture.
From GaussianAnalysis.probability Require Import tuple_rows total_variation.
From GaussianAnalysis.probability Require Import conditioning.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality Require Import RobustDefinitions.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Countable Require Import Truncation.
From EllipsoidUniversality Require Import MixtureStatement MixtureTheorem.
From EllipsoidUniversality Require Import CountableMixtureStatement.
From EllipsoidUniversality Require Import RobustStatement.
From EllipsoidUniversality.Sat Require Import ApproximateFit.
Require Import EllipsoidUniversality.Countable.Theorem.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).
Local Notation pt d := (d.-tuple (measurableTypeR R)).

(* 1. Reading a sample as the list of its points, and back. *)
Section reshape.
Variables (n d : nat).

Lemma rf_row_proof (k : 'I_(n * d)) : (k %/ d < n)%N.
Proof.
have : (k < n * d)%N := ltn_ord k.
move: (nat_of_ord k) => m.
case: (posnP d) => [->|d0]; first by rewrite muln0.
by rewrite ltn_divLR.
Qed.

Lemma rf_col_proof (k : 'I_(n * d)) : (k %% d < d)%N.
Proof.
have : (k < n * d)%N := ltn_ord k.
move: (nat_of_ord k) => m.
case: (posnP d) => [->|d0]; first by rewrite muln0.
by move=> _; exact: ltn_pmod.
Qed.

(* The sample whose points are the d-tuples of y. *)
Definition rows_flat (y : n.-tuple (pt d)) : paper_main_sample n d :=
  [tuple tnth (tnth y (Ordinal (rf_row_proof k))) (Ordinal (rf_col_proof k))
     | k < n * d].

Lemma rows_flatK (y : n.-tuple (pt d)) : tuple_rows n d (rows_flat y) = y.
Proof.
apply: eq_from_tnth => i; apply: eq_from_tnth => j.
rewrite !tnth_mktuple.
have hj := ltn_ord j.
have d0 : (0 < d)%N by apply: leq_ltn_trans (leq0n j) hj.
congr (tnth (tnth y _) _); apply: val_inj => /=.
- by rewrite divnMDl // divn_small // addn0.
- by rewrite modnMDl modn_small.
Qed.

Lemma tuple_rowsK (x : paper_main_sample n d) :
  rows_flat (tuple_rows n d x) = x.
Proof.
apply: eq_from_tnth => k; rewrite !tnth_mktuple.
by congr tnth; apply: val_inj => /=; rewrite -divn_eq.
Qed.

Lemma measurable_rows_flat :
  measurable_fun [set: n.-tuple (pt d)] rows_flat.
Proof.
apply/measurable_fun_tnthP => k /=.
apply: (eq_measurable_fun (fun y : n.-tuple (pt d) =>
  tnth (tnth y (Ordinal (rf_row_proof k))) (Ordinal (rf_col_proof k)))).
  by move=> y _; rewrite /= /rows_flat tnth_mktuple.
exact: measurableT_comp (measurable_tnth _) (measurable_tnth _).
Qed.

Lemma robust_pointsE (x : paper_main_sample n d) :
  robust_points n d x = tuple_rows n d x.
Proof.
apply: eq_from_tnth => i; rewrite !tnth_mktuple.
apply: eq_from_tnth => j; rewrite !tnth_mktuple.
by rewrite (tnth_nth 0) List_nthE.
Qed.

Lemma robust_points_image (E : set (paper_main_sample n d)) :
  robust_points n d @` E = rows_flat @^-1` E.
Proof.
apply/seteqP; split => y.
- by move=> [x Ex <-]; rewrite /preimage /= robust_pointsE tuple_rowsK.
- by move=> Ey; exists (rows_flat y) => //; rewrite robust_pointsE rows_flatK.
Qed.

Lemma measurable_robust_image (E : set (paper_main_sample n d)) :
  measurable E -> measurable (robust_points n d @` E).
Proof.
move=> mE; rewrite robust_points_image -[X in measurable X]setTI.
exact: measurable_rows_flat.
Qed.

Lemma robust_points_preimage (E : set (paper_main_sample n d)) :
  tuple_rows n d @^-1` (robust_points n d @` E) = E.
Proof.
rewrite robust_points_image; apply/seteqP; split => x;
  by rewrite /preimage /= tuple_rowsK.
Qed.

End reshape.

(* 2. The point law of a countable family, and that of its truncation of
   Countable/Truncation. *)
Section point_laws.
Variables (K : R) (w : nat -> nat -> R).
Variable (mu : nat -> nat -> nat -> probability (measurableTypeR R) R).
Hypothesis hfam : countable_mixture_family K w mu.

Local Notation Nt := (trunc_N K w mu hfam).
Local Notation wt := (trunc_w K w mu hfam).
Local Notation mut := (trunc_mu K w mu hfam).
Local Notation rt := (trunc_r K w mu hfam).

(* nu_d, the countable mixture of the product laws of the components. *)
Definition rob_nu d : probability (pt d) RR :=
  cmixture (fun s => tuple_prod (mu d s) d) (trunc_weights K w mu hfam d).

Lemma rob_nuE d (A : set (pt d)) :
  robust_point_law (w d) (mu d) d A = rob_nu d A.
Proof.
have [w0 _] := hfam d.
rewrite /robust_point_law /rob_nu /= cmixtureE nneseries_esum.
  by move=> s _; rewrite mule_ge0 // lee_fin; exact: w0.
by congr esum; apply/seteqP; split.
Qed.

Lemma rob_tvE d (P : probability (pt d) RR) :
  robust_tv d P (robust_point_law (w d) (mu d) d) =
  (tv_dist P (rob_nu d))%:E.
Proof.
rewrite tv_distE /robust_tv; congr ereal_sup; apply/seteqP; split => _ [A mA <-];
  by exists A => //; rewrite rob_nuE.
Qed.

(* The truncated family is a finite mixture of product laws. *)
Lemma rob_Qw d : mixture_weights (fun s : 'I_(Nt d) => wt d s).
Proof.
have [w0 [w1 _]] := trunc_family K w mu hfam d.
by split => [s|]; [exact: w0 (ltn_ord s) | exact: w1].
Qed.

Definition rob_Q d : probability (pt d) RR :=
  mixture (fun s : 'I_(Nt d) => tuple_prod (mut d s) d) (rob_Qw d).

(* The samples of the point law of the truncation have the law
   mixture_probability of the truncated family. *)
Lemma rob_Q_sample n d (E : set (paper_main_sample n d)) : measurable E ->
  robust_sample_law n d (rob_Q d) E =
  mixture_probability (Nt d) (wt d) (mut d) n d E.
Proof.
move=> mE.
have mB := measurable_robust_image n d E mE.
have i0 : 'I_(Nt d) by exists 0%N.
rewrite /robust_sample_law (tuple_prod_mixture _ (rob_Qw d) i0 mB).
rewrite /mixture_probability; apply: eq_bigr => s _; congr (_ * _)%E.
rewrite /mixture_labelled_law -[in RHS](robust_points_preimage n d E).
rewrite -(tuple_prod_rows _ mB).
have -> : tuple_prod (fun k => tuple_prod (mut d (nth i0 s k)) d) n =
    tuple_prod (fun i => tuple_prod (fun j =>
      mut d (mixture_label s ((i * d + j) %/ d)) ((i * d + j) %% d)) d) n.
  apply: eq_tuple_prod => i hi; apply: eq_tuple_prod => j hj.
  rewrite /mixture_label.
  have d0 : (0 < d)%N by apply: leq_ltn_trans (leq0n j) hj.
  rewrite divnMDl // divn_small // addn0 modnMDl modn_small //.
  by rewrite (nth_map i0) ?size_tuple.
by [].
Qed.

(* The point laws of the family and of its truncation are within r_d in
   total variation: they share the components s <= cut d, and their tails
   have mass at most r_d. *)
Lemma rob_nu_Q_tv d : tv_dist (rob_nu d) (rob_Q d) <= rt d.
Proof.
apply: tv_dist_le => A mA.
set c := trunc_cut K w mu hfam d.
have [w0 [w1 _]] := hfam d.
pose f (s : nat) := ((w d s)%:E * tuple_prod (mu d s) d A)%E.
have f0 s : (0 <= f s)%E by rewrite mule_ge0 // lee_fin.
have fle s : (f s <= (w d s)%:E)%E.
  rewrite /f -[X in (_ <= X)%E]mule1 lee_wpmul2l ?lee_fin //.
  exact: probability_le1.
pose S := (\sum_(s < c.+1) f s)%E.
pose a := (\sum_(s <oo | (c < s)%N) f s)%E.
pose b := ((rt d)%:E * tuple_prod (trunc_tail K w mu hfam d) d A)%E.
have hnu : rob_nu d A = (S + a)%E.
  rewrite /rob_nu /= cmixtureE (nneseries_split 0 c.+1) ?add0n.
    by move=> k _; exact: f0.
  by rewrite big_mkord eseries_cond; congr (_ + _)%E.
have hQ : rob_Q d A = (S + b)%E.
  rewrite /rob_Q /= mixtureE big_ord_recr /=; congr (_ + _)%E.
    apply: eq_bigr => s _.
    by rewrite /trunc_w /trunc_mu /= -ltnS ltn_ord.
  by rewrite /trunc_w /trunc_mu /= ltnn eqxx.
have [ta _] := cmixture_tailE (trunc_weights K w mu hfam d) c.
have a0 : (0 <= a)%E by apply: nneseries_ge0 => s _ _; exact: f0.
have ar : (a <= (rt d)%:E)%E.
  rewrite /trunc_r -/c -ta; apply: lee_nneseries.
    by move=> i _ _; exact: f0.
  by move=> i _; exact: fle.
have r0 := trunc_r_ge0 K w mu hfam d.
have b0 : (0 <= b)%E by rewrite mule_ge0 // lee_fin.
have br : (b <= (rt d)%:E)%E.
  rewrite /b -[X in (_ <= X)%E]mule1 lee_wpmul2l ?lee_fin //.
  exact: probability_le1.
have fa : a \is a fin_num by rewrite ge0_fin_numE // (le_lt_trans ar) ?ltry.
have fb : b \is a fin_num by rewrite ge0_fin_numE // (le_lt_trans br) ?ltry.
have fS : S \is a fin_num.
  have : rob_nu d A \is a fin_num by exact: fin_num_measure.
  by rewrite hnu fin_numD => /andP[].
rewrite hnu hQ !fineD //.
have ha : 0 <= fine a <= rt d.
  by rewrite fine_ge0 //= -lee_fin fineK.
have hb : 0 <= fine b <= rt d.
  by rewrite fine_ge0 //= -lee_fin fineK.
rewrite opprD addrACA subrr add0r.
move: ha hb; clearbody S a b.
move: (fine a) (fine b) => x y hx hy.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

(* The transfer: the samples of n i.i.d. points of any law P and the
   samples of the family differ by at most n (tv (P, nu_d) + 2 r_d) on
   every measurable set. *)
Lemma robust_transfer n d (P : probability (pt d) RR)
    (E : set (paper_main_sample n d)) : measurable E ->
  (`|robust_sample_law n d P E -
     countable_mixture_probability (w d) (mu d) n d E| <=
   (n%:R * (tv_dist P (rob_nu d) + 2 * rt d))%:E)%E.
Proof.
move=> mE.
have mB := measurable_robust_image n d E mE.
have h1 := tuple_prod_tv (fun=> P) (fun=> rob_Q d) mB.
rewrite sumr_const card_ord in h1.
have h2 := trunc_coupling K w mu hfam n d E mE.
have h3 := rob_Q_sample n d E mE.
have htv : tv_dist P (rob_Q d) <= tv_dist P (rob_nu d) + rt d.
  apply: le_trans (tv_dist_triangle P (rob_nu d) (rob_Q d)) _.
  by rewrite lerD2l; exact: rob_nu_Q_tv.
rewrite /robust_sample_law in h3 *.
rewrite h3 in h1.
have fX : tuple_prod (fun=> P) n (robust_points n d @` E) \is a fin_num.
  exact: fin_num_measure.
have fY : mixture_probability (Nt d) (wt d) (mut d) n d E \is a fin_num.
  by rewrite -h3; exact: fin_num_measure.
move: h1 h2 fX fY.
set X := tuple_prod (fun=> P) n _.
set Y := mixture_probability _ _ _ n d E.
set Z := countable_mixture_probability _ _ n d E.
move=> h1 h2 fX fY.
have fZ : Z \is a fin_num.
  clearbody X Y Z.
  by clear h1; move: h2 fY; case: Z => [z||]; case: Y => [y||] //=.
move: h1 h2; rewrite -(fineK fX) -(fineK fY) -(fineK fZ) /= !lee_fin.
move=> h1 h2.
have hn : tv_dist P (rob_Q d) *+ n <= n%:R * (tv_dist P (rob_nu d) + rt d).
  rewrite -[X in X <= _]mulr_natl.
  by apply: ler_wpM2l; [exact: ler0n | exact: htv].
apply: le_trans (ler_distD (fine Y) _ _) _.
rewrite [`|fine Y - fine Z|]distrC.
apply: le_trans (lerD (le_trans h1 hn) h2) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(* The exact identity: the samples of n i.i.d. points of the point law nu_d
   of the countable family have the law countable_mixture_probability. *)
Lemma rob_nu_sample n d (E : set (paper_main_sample n d)) : measurable E ->
  robust_sample_law n d (rob_nu d) E =
  countable_mixture_probability (w d) (mu d) n d E.
Proof.
move=> mE.
have mB := measurable_robust_image n d E mE.
rewrite /robust_sample_law /rob_nu (tuple_prod_cmixture _ _ mB).
rewrite /countable_mixture_probability; apply: eq_esum => s _; congr (_ * _)%E.
rewrite /countable_labelled_law -[in RHS](robust_points_preimage n d E).
rewrite -(tuple_prod_rows _ mB).
have -> : tuple_prod (fun k => tuple_prod (mu d (nth 0%N s k)) d) n =
    tuple_prod (fun i => tuple_prod (fun j =>
      mu d (nth 0%N s ((i * d + j) %/ d)) ((i * d + j) %% d)) d) n.
  apply: eq_tuple_prod => i hi; apply: eq_tuple_prod => j hj.
  have d0 : (0 < d)%N by apply: leq_ltn_trans (leq0n j) hj.
  by rewrite divnMDl // divn_small // addn0 modnMDl modn_small.
by [].
Qed.

(* The transfer without truncation terms: on every measurable set of
   samples, the samples of n i.i.d. points of law P and those of the
   family differ by at most n tv(P, nu_d). *)
Lemma robust_transfer_tv n d (P : probability (pt d) RR)
    (E : set (paper_main_sample n d)) : measurable E ->
  (`|robust_sample_law n d P E -
     countable_mixture_probability (w d) (mu d) n d E| <=
   (n%:R * tv_dist P (rob_nu d))%:E)%E.
Proof.
move=> mE.
have mB := measurable_robust_image n d E mE.
rewrite -rob_nu_sample //.
have h := tuple_prod_tv (fun=> P) (fun=> rob_nu d) mB.
by rewrite sumr_const card_ord -mulr_natl in h.
Qed.

(* The probabilities of the countable family are finite. *)
Lemma cmp_fin n d (E : set (paper_main_sample n d)) : measurable E ->
  countable_mixture_probability (w d) (mu d) n d E \is a fin_num.
Proof.
move=> mE.
have mB := measurable_robust_image n d E mE.
have h2 := trunc_coupling K w mu hfam n d E mE.
have fY : mixture_probability (Nt d) (wt d) (mut d) n d E \is a fin_num.
  rewrite -(rob_Q_sample n d E mE) /robust_sample_law.
  exact: fin_num_measure.
move: h2 fY; set Y := mixture_probability _ _ _ n d E.
set Z := countable_mixture_probability _ _ n d E.
by clearbody Y Z; case: Z => [z||]; case: Y => [y||] //=.
Qed.

(* The error of the transfer tends to 0 when n d / d^2 -> alpha and
   d^2 tv(P d, nu_d) -> 0. *)
Lemma robust_err_small (P : forall d, probability (pt d) RR)
    (n : nat -> nat) (alpha : R) :
  0 < alpha -> universality_density_tends_to n alpha -> robust_close w mu P ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    (n d)%:R * (tv_dist (P d) (rob_nu d) + 2 * rt d) <= eps.
Proof.
move=> a0 hn hP eps e0.
have e4 : 0 < eps / 4 by rewrite divr_gt0.
have ea : 0 < eps / (4 * alpha) by rewrite divr_gt0 // mulr_gt0.
have [D1 h1] := af_ev_density n alpha a0 hn.
have [D2 h2] := hP (eps / (4 * alpha)) ea.
have [D3 h3] := trunc_nr_small K w mu hfam n alpha a0 hn _ e4.
exists (maxn D1 (maxn D2 D3)) => d; rewrite !geq_max => /andP[d1 /andP[d2 d3]].
have [d0 [nlo nhi]] := h1 d d1.
have tv0 := tv_dist_ge0 (P d) (rob_nu d).
have htv : d%:R ^+ 2 * tv_dist (P d) (rob_nu d) < eps / (4 * alpha).
  have := h2 d d2; rewrite rob_tvE -EFinM -EFinB abse_EFin lte_fin subr0.
  by rewrite ger0_norm // mulr_ge0 // exprn_ge0.
have hr := h3 d d3.
have hn1 : (n d)%:R * tv_dist (P d) (rob_nu d) <= eps / 2.
  apply: le_trans (_ : 2 * alpha * (d%:R ^+ 2 * tv_dist (P d) (rob_nu d))
    <= _).
    by rewrite mulrA; apply: ler_wpM2r.
  apply: le_trans (_ : 2 * alpha * (eps / (4 * alpha)) <= _).
    by apply: ler_wpM2l; [rewrite mulr_ge0 // ltW | exact: ltW].
  have an : alpha != 0 by rewrite gt_eqF.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
move: hn1 hr; set x := (n d)%:R * tv_dist _ _; set y := (n d)%:R * rt d.
have -> : (n d)%:R * (tv_dist (P d) (rob_nu d) + 2 * rt d) = x + 2 * y.
  by rewrite /x /y; ring.
by clearbody x y; move=> hx hy; lra.
Qed.

(* The limits carry over from the countable family to the samples of P. *)
Lemma robust_tends (P : forall d, probability (pt d) RR) (n : nat -> nat)
    (alpha : R) (E : forall d, set (paper_main_sample (n d) d)) (l : R) :
  0 < alpha -> universality_density_tends_to n alpha -> robust_close w mu P ->
  (forall d, measurable (E d)) ->
  paper_main_tends_to
    (fun d => countable_mixture_probability (w d) (mu d) (n d) d (E d)) l ->
  paper_main_tends_to (fun d => robust_sample_law (n d) d (P d) (E d)) l.
Proof.
move=> a0 hn hP mE h.
apply: (tends_to_transfer _ _
  (fun d => (n d)%:R * (tv_dist (P d) (rob_nu d) + 2 * rt d)) l _ _ _ h).
- by move=> d; exact: robust_transfer.
- by move=> d; exact: cmp_fin.
- exact: (robust_err_small P n alpha a0 hn hP).
Qed.

End point_laws.

(* 3. The robust statements, from the countable theorem. *)
Theorem robust_statement_holds : robust_statement.
Proof.
move=> kappa K alpha k1 K0 a0.
have [hsat hunsat herr] := countable_statement_holds kappa K alpha k1 K0 a0.
split.
- move=> ha; have [c [c1 [m1 [m2 hc]]]] := hsat ha.
  exists c; split => // w mu hfam h4 P hP n hn.
  have [p1 p2] := hc w mu hfam h4 n hn.
  split.
    exact: (robust_tends K w mu hfam P n alpha
      (fun d => universality_pd_fit_event (n d) d) 1 a0 hn hP
      (fun d => m1 (n d) d) p1).
  exact: (robust_tends K w mu hfam P n alpha
    (fun d => universality_conditioned_fit_event (n d) d c) 1 a0 hn hP
    (fun d => m2 (n d) d) p2).
- move=> ha; have [_ [m hc]] := hunsat ha.
  move=> w mu hfam h4 P hP n hn.
  exact: (robust_tends K w mu hfam P n alpha
    (fun d => paper_main_fit_event (n d) d) 0 a0 hn hP
    (fun d => m (n d) d) (hc w mu hfam h4 n hn)).
- have [m hc] := herr.
  move=> w mu hfam h4 P hP n hn eps e0.
  exact: (robust_tends K w mu hfam P n alpha
    (fun d => universality_error_event (n d) d
       (universality_e_star alpha kappa) eps) 0 a0 hn hP
    (fun d => m (n d) d eps) (hc w mu hfam h4 n hn eps e0)).
Qed.

Theorem robust_interpolation_holds : robust_interpolation_statement.
Proof.
move=> K alpha K0 a0 ah.
have [C [C0 hC]] := countable_interpolation_holds K alpha K0 a0 ah.
exists C; split => // w mu hfam P hP n hn eps e0.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have [D1 h1] := hC w mu hfam n hn _ e2.
have [D2 h2] := robust_err_small K w mu hfam P n alpha a0 hn hP _ e2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have [E [mE PE hE]] := h1 d d1.
exists E; split => //.
have hc := robust_transfer K w mu hfam (n d) d (P d) E mE.
have hr := h2 d d2.
have fZ := cmp_fin K w mu hfam (n d) d E mE.
have fX : robust_sample_law (n d) d (P d) E \is a fin_num.
  have mB := measurable_robust_image (n d) d E mE.
  by rewrite /robust_sample_law; exact: fin_num_measure.
move: hc PE hr fX fZ.
set X := robust_sample_law _ _ _ E.
set Z := countable_mixture_probability _ _ _ _ E.
set e := (n d)%:R * _ => hc PE hr fX fZ.
move: hc PE; rewrite -(fineK fX) -(fineK fZ) /= !lee_fin.
rewrite ler_norml => /andP[_ h] PE.
by move: hr; clearbody X Z e; lra.
Qed.

(* 4. The contamination of a finite family. *)

(* A sum over the tuples of N + 1 labels whose terms vanish on the tuples
   that contain the last label is the sum over the tuples of N labels. *)
Lemma sum_tuple_lift (N n : nat) (F : n.-tuple 'I_N.+1 -> \bar R) :
  (forall s, ord_max \in s -> F s = 0%E) ->
  (\sum_(s : n.-tuple 'I_N.+1) F s =
   \sum_(s : n.-tuple 'I_N) F (map_tuple (lift ord_max) s))%E.
Proof.
move=> h0.
rewrite (bigID (fun s => ord_max \in s)) /= big1 ?add0e; first by move=> s /h0.
have hinj : injective (fun s : n.-tuple 'I_N => map_tuple (lift ord_max) s).
  move=> s1 s2 /(congr1 val) /= e; apply: val_inj.
  by apply: inj_map e; exact: lift_inj.
transitivity (\sum_(s in [set map_tuple (lift ord_max) x
                         | x in [set: n.-tuple 'I_N]]%SET) F s)%E.
  apply: eq_bigl => s; apply/idP/imsetP.
  - move=> hs.
    have hl (i : 'I_n) : (tnth s i < N)%N.
      have hi : tnth s i != ord_max.
        by apply: contra hs => /eqP <-; exact: mem_tnth.
      by rewrite ltn_neqAle -ltnS ltn_ord andbT.
    exists [tuple Ordinal (hl i) | i < n]; first by rewrite finset.in_setT.
    apply: eq_from_tnth => i; rewrite tnth_map tnth_mktuple.
    by apply: val_inj; rewrite [RHS]lift_max.
  - move=> [s' _ ->]; apply/negP => /mapP [j _ /eqP].
    by rewrite (negbTE (neq_lift _ _)).
rewrite big_imset /=; first by move=> x y _ _; exact: hinj.
by apply: eq_bigl => x; rewrite finset.in_setT.
Qed.

(* Given labels that contain the last one, the point of that label is 0, and
   there is no positive definite fit of value one. *)
Lemma contaminated_null n d N
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    (s : n.-tuple 'I_N.+1) :
  measurable (universality_pd_fit_event n d) -> ord_max \in s ->
  mixture_labelled_law N.+1 (contaminated_laws N mu) n d s
    (universality_pd_fit_event n d) = 0%E.
Proof.
move=> mE /tnthP [i hi].
set P := mixture_labelled_law _ _ n d s.
set E := universality_pd_fit_event n d.
pose A (k : 'I_(n * d)) : set (measurableTypeR R) :=
  if (k %/ d == i)%N then [set 0] else setT.
have mA k : measurable (A k) by rewrite /A; case: ifP.
pose Z := tuple_box A.
have mZ : measurable Z by exact: measurable_tuple_box.
have PZ : P Z = 1%E.
  rewrite /P /mixture_labelled_law /Z tuple_prod_box //.
  rewrite big1 // => k _; rewrite /A; case: ifP => [/eqP hk|_].
    have hl : mixture_label s (k %/ d) = N.
      rewrite /mixture_label hk (nth_map ord_max) ?size_tuple // -tnth_nth.
      by rewrite -hi.
    by rewrite /contaminated_laws hl ltnn /= diracE mem_set.
  exact: probability_setT.
have EZ : E `&` Z = set0.
  apply/seteqP; split => // x [[S [_ hS]] hZ].
  have h0 (c : 'I_d) : paper_main_point x i c 0 = 0.
    have d0 : (0 < d)%N by apply: leq_ltn_trans (leq0n c) (ltn_ord c).
    have := hZ (row_index i c).
    rewrite /A /= divnMDl // divn_small // addn0 eqxx => hc.
    have hc' : tnth x (row_index i c) = 0 := hc.
    rewrite mxE List_nthE.
    exact: (etrans (esym (tnth_nth 0 x (row_index i c))) hc').
  have hq : paper_main_quadratic_form S (paper_main_point x i) = 0.
    rewrite /paper_main_quadratic_form big1 // => a _.
    by rewrite big1 // => b _; rewrite h0 !mul0r.
  by have := hS i; rewrite hq => /esym /eqP; rewrite oner_eq0.
have hU : P (E `|` Z) = (P E + P Z)%E := measureU P mE mZ EZ.
have le1 : (P (E `|` Z) <= 1)%E by apply: probability_le1; exact: measurableU.
have fE : P E \is a fin_num by exact: fin_num_measure.
have PE0 : (0 <= P E)%E by exact: measure_ge0.
move: le1 PE0; rewrite hU PZ -(fineK fE) -EFinD !lee_fin => h1 h2.
by congr EFin; apply/eqP; rewrite eq_le h2 andbT -(lerD2r 1) add0r.
Qed.

(* Given labels that avoid the last one, the weights are those of the family
   times 1 - lambda / n, and the law of the sample is that of the family. *)
Lemma contaminated_lift n d N lambda (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    (s : n.-tuple 'I_N) (E : set (paper_main_sample n d)) :
  ((\prod_(i < n) contaminated_weights lambda n N w
      (tnth (map_tuple (lift ord_max) s) i))%:E *
   mixture_labelled_law N.+1 (contaminated_laws N mu) n d
     (map_tuple (lift ord_max) s) E =
   ((1 - lambda / n%:R) ^+ n)%:E *
   ((\prod_(i < n) w (tnth s i))%:E * mixture_labelled_law N mu n d s E))%E.
Proof.
have hw : \prod_(i < n) contaminated_weights lambda n N w
    (tnth (map_tuple (lift ord_max) s) i) =
    (1 - lambda / n%:R) ^+ n * \prod_(i < n) w (tnth s i).
  rewrite (eq_bigr (fun i => (1 - lambda / n%:R) * w (tnth s i))); last first.
    by rewrite big_split /= prodr_const card_ord.
  by move=> i _; rewrite tnth_map /contaminated_weights lift_max ltn_ord.
have hl : mixture_labelled_law N.+1 (contaminated_laws N mu) n d
    (map_tuple (lift ord_max) s) = mixture_labelled_law N mu n d s.
  rewrite /mixture_labelled_law; apply: eq_tuple_prod => k hk.
  have hlab : mixture_label (map_tuple (lift ord_max) s) (k %/ d) =
      mixture_label s (k %/ d).
    rewrite /mixture_label /= -map_comp; congr nth.
    by apply: eq_map => j /=; exact: lift_max.
  have d0 : (0 < d)%N by move: hk; case: (d) => //; rewrite muln0.
  have kn : (k %/ d < n)%N by rewrite ltn_divLR.
  have hN : (mixture_label s (k %/ d) < N)%N.
    have : nth 0%N (map val s) (k %/ d) \in map val s.
      by apply: mem_nth; rewrite size_map size_tuple.
    by rewrite /mixture_label => /mapP [j _ ->]; exact: ltn_ord.
  by rewrite hlab /contaminated_laws hN.
by rewrite hw hl EFinM muleA.
Qed.

(* The probability of a positive definite fit of value one for the samples
   of the contaminated family: (1 - lambda / n)^n times that of the family. *)
Lemma contaminated_probability n d N lambda (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R) :
  measurable (universality_pd_fit_event n d) ->
  mixture_probability N.+1 (contaminated_weights lambda n N w)
    (contaminated_laws N mu) n d (universality_pd_fit_event n d) =
  (((1 - lambda / n%:R) ^+ n)%:E *
   mixture_probability N w mu n d (universality_pd_fit_event n d))%E.
Proof.
move=> mE.
rewrite /mixture_probability (sum_tuple_lift N n).
  by move=> s hs; rewrite contaminated_null // mule0.
rewrite fin_num_sume_distrr //.
  move=> s t _ _; apply: fin_num_adde_defl.
  by rewrite fin_numM //; exact: fin_num_measure.
by apply: eq_bigr => s _; rewrite contaminated_lift.
Qed.

(* The number of points tends to infinity. *)
Lemma density_large (n : nat -> nat) (alpha : R) : 0 < alpha ->
  universality_density_tends_to n alpha ->
  forall M : R, exists D : nat, forall d, (D <= d)%N -> M <= (n d)%:R.
Proof.
move=> a0 hn M.
have [D1 h1] := af_ev_density n alpha a0 hn.
have [D2 h2] := af_ev_ge (2 * M / alpha).
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have [d0 [nlo _]] := h1 d d1.
have hd := h2 d d2.
apply: le_trans nlo.
have d1' : 1 <= d%:R :> R by rewrite ler1n.
have an : alpha != 0 by rewrite gt_eqF.
have hM : alpha / 2 * (2 * M / alpha) = M by field.
rewrite -[X in X <= _]hM.
apply: ler_wpM2l; first by rewrite divr_ge0 // ltW.
apply: le_trans hd _.
by rewrite expr2 ler_peMr // (le_trans ler01 d1').
Qed.

(* (1 - lambda / n)^n p tends to expR (- lambda) when p tends to 1 and n to
   infinity. *)
Lemma contaminated_limit (lambda alpha : R) (n : nat -> nat)
    (p : nat -> \bar R) :
  0 < lambda -> 0 < alpha -> universality_density_tends_to n alpha ->
  paper_main_tends_to p 1 ->
  paper_main_tends_to
    (fun d => (((1 - lambda / (n d)%:R) ^+ (n d))%:E * p d)%E)
    (expR (- lambda)).
Proof.
move=> l0 a0 hn hp eps e0.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have [D1 h1] := hp _ e2.
have [D2 h2] : exists D2 : nat, forall d, (D2 <= d)%N ->
    lambda + 2 * lambda ^+ 2 / eps + 1 <= (n d)%:R.
  exact: density_large n alpha a0 hn _.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have hpd := h1 d d1.
have nd := h2 d d2.
have fp : p d \is a fin_num by move: hpd; case: (p d).
move: hpd; rewrite -(fineK fp) -EFinB -EFinM -EFinB !abse_EFin !lte_fin => hq.
have ln : lambda < (n d)%:R.
  apply: lt_le_trans nd; rewrite -addrA ltrDl.
  by rewrite ltr_wpDl // divr_ge0 // ?mulr_ge0 // ?exprn_ge0 // ltW.
have hdist := pow_one_sub_dist (ltW l0) ln.
have /andP[hlo hhi] := pow_one_sub_bounds (ltW l0) ln.
have hsmall : lambda ^+ 2 / ((n d)%:R - lambda) < eps / 2.
  have nl : 0 < (n d)%:R - lambda by rewrite subr_gt0.
  rewrite ltr_pdivrMr //.
  have h : 2 * lambda ^+ 2 / eps + 1 <= (n d)%:R - lambda.
    by rewrite lerBrDl addrA.
  apply: lt_le_trans (_ : eps / 2 * (2 * lambda ^+ 2 / eps + 1) <= _).
    have en : eps != 0 by rewrite gt_eqF.
    rewrite mulrDr mulr1 (_ : eps / 2 * (2 * lambda ^+ 2 / eps) = lambda ^+ 2).
      by field.
    by rewrite ltrDl.
  by apply: ler_wpM2l => //; exact: ltW.
have ha0 : 0 <= (1 - lambda / (n d)%:R) ^+ n d.
  by apply: le_trans hlo; exact: expR_ge0.
have ha1 : (1 - lambda / (n d)%:R) ^+ n d <= 1.
  apply: le_trans hhi _; rewrite expR_le1 oppr_le0; exact: ltW.
move: ha0 ha1 hdist hq hsmall.
set a := (1 - lambda / (n d)%:R) ^+ n d; set q := fine (p d).
set e := expR (- lambda); set r := lambda ^+ 2 / _.
move=> ha0 ha1 hdist hq hsmall.
have -> : a * q - e = a * (q - 1) + (a - e) by ring.
apply: le_lt_trans (ler_normD _ _) _.
rewrite normrM (ger0_norm ha0).
have : a * `|q - 1| <= `|q - 1| by rewrite ler_piMl.
by clearbody a q e r; move=> h; lra.
Qed.

(* An esum over nat whose terms vanish from M on is a finite sum. *)
Lemma esum_nat_fin (f : nat -> \bar R) (M : nat) :
  (forall s, (0 <= f s)%E) -> (forall s, (M <= s)%N -> f s = 0%E) ->
  (\esum_(s in [set: nat]) f s = \sum_(s < M) f s)%E.
Proof.
move=> f0 fM.
have -> : [set: nat] = [set x | xpredT x] by apply/seteqP; split.
rewrite -nneseries_esum; first by move=> s _; exact: f0.
rewrite (nneseries_split 0 M); first by move=> k _; exact: f0.
rewrite add0n big_mkord eseries0 ?adde0 // => i hi _; exact: fM.
Qed.

(* Part (a) on one set: the contaminated point law and the point law of the
   family differ by at most lambda / n. *)
Lemma contaminated_tv_set n d N (lambda : R) (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    (A : set (pt d)) :
  (forall s, (s < N)%N -> 0 <= w s) -> \sum_(s < N) w s = 1 ->
  0 < lambda -> lambda <= n%:R -> measurable A ->
  (`|robust_point_law (contaminated_weights lambda n N w)
       (contaminated_laws N mu) d A -
     robust_point_law (finite_weights N w) mu d A| <=
   (lambda / n%:R)%:E)%E.
Proof.
move=> w0 w1 l0 ln mA.
have n0 : 0 < n%:R :> R by apply: lt_le_trans ln.
set b := lambda / n%:R.
have b0 : 0 <= b by rewrite divr_ge0 // ltW.
have b1 : b <= 1 by rewrite ler_pdivrMr // mul1r.
pose q s := fine (tuple_prod (mu s) d A).
have hq s : tuple_prod (mu s) d A = (q s)%:E.
  by rewrite /q fineK //; exact: fin_num_measure.
have q0 s : 0 <= q s by rewrite /q fine_ge0 // measure_ge0.
have q1 s : q s <= 1 by rewrite -lee_fin -hq probability_le1.
pose z := fine (tuple_prod (contaminated_laws N mu N) d A).
have hz : tuple_prod (contaminated_laws N mu N) d A = z%:E.
  by rewrite /z fineK //; exact: fin_num_measure.
have z0 : 0 <= z by rewrite /z fine_ge0 // measure_ge0.
have z1 : z <= 1 by rewrite -lee_fin -hz probability_le1.
have hP : robust_point_law (contaminated_weights lambda n N w)
    (contaminated_laws N mu) d A =
    ((\sum_(s < N) (1 - b) * w s * q s) + b * z)%:E.
  rewrite /robust_point_law (esum_nat_fin _ N.+1).
  - move=> s; apply: mule_ge0 => //; rewrite lee_fin /contaminated_weights.
    case: ifPn => hs; first by rewrite mulr_ge0 ?subr_ge0 // w0.
    by case: ifP.
  - move=> s hs; rewrite /contaminated_weights ltnNge (ltnW hs) /= gtn_eqF //.
    by rewrite mul0e.
  rewrite big_ord_recr /= EFinD -sumEFin EFinM -hz; congr (_ + _)%E.
    apply: eq_bigr => s _.
    have hl : contaminated_laws N mu s = mu s.
      by apply/funext => j; rewrite /contaminated_laws ltn_ord.
    by rewrite hl hq /contaminated_weights ltn_ord -EFinM.
  by rewrite /contaminated_weights ltnn eqxx.
have hQ : robust_point_law (finite_weights N w) mu d A =
    (\sum_(s < N) w s * q s)%:E.
  rewrite /robust_point_law (esum_nat_fin _ N).
  - move=> s; apply: mule_ge0 => //; rewrite lee_fin /finite_weights.
    by case: ifPn => // hs; exact: w0.
  - by move=> s hs; rewrite /finite_weights ltnNge hs /= mul0e.
  rewrite -sumEFin; apply: eq_bigr => s _.
  by rewrite hq /finite_weights ltn_ord -EFinM.
rewrite hP hQ -EFinB abse_EFin lee_fin.
have hS : \sum_(s < N) (1 - b) * w s * q s =
    (1 - b) * \sum_(s < N) w s * q s.
  by rewrite mulr_sumr; apply: eq_bigr => s _; rewrite mulrA.
have S0 : 0 <= \sum_(s < N) w s * q s.
  by apply: sumr_ge0 => s _; rewrite mulr_ge0 // w0.
have S1 : \sum_(s < N) w s * q s <= 1.
  rewrite -w1; apply: ler_sum => s _.
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; [exact: w0 | exact: q1].
rewrite hS; move: S0 S1; move: (\sum_(s < N) w s * q s) => S S0 S1.
have -> : (1 - b) * S + b * z - S = b * (z - S) by ring.
rewrite normrM (ger0_norm b0) -[X in _ <= X]mulr1; apply: ler_wpM2l => //.
by rewrite ler_norml; apply/andP; split; clearbody b q z; lra.
Qed.

(* Part (a): n times the total variation distance is at most lambda. *)
Lemma contaminated_tv n d N (lambda : R) (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R) :
  (forall s, (s < N)%N -> 0 <= w s) -> \sum_(s < N) w s = 1 ->
  0 < lambda -> lambda <= n%:R ->
  ((n%:R)%:E *
   robust_tv d
     (robust_point_law (contaminated_weights lambda n N w)
        (contaminated_laws N mu) d)
     (robust_point_law (finite_weights N w) mu d) <= lambda%:E)%E.
Proof.
move=> w0 w1 l0 ln.
have n0 : 0 < n%:R :> R by apply: lt_le_trans ln.
have htv : (robust_tv d
    (robust_point_law (contaminated_weights lambda n N w)
       (contaminated_laws N mu) d)
    (robust_point_law (finite_weights N w) mu d) <= (lambda / n%:R)%:E)%E.
  by apply: ge_ereal_sup => _ [A mA <-]; exact: contaminated_tv_set.
apply: le_trans (lee_wpmul2l _ htv) _; first by rewrite lee_fin ltW.
by rewrite -EFinM mulrC divfK ?gt_eqF.
Qed.

(* 5. The theorem. *)
Theorem contamination_holds : contamination_statement.
Proof.
move=> kappa K alpha lambda k1 K0 a0 ha l0 N w mu hfam h4 n hn.
split.
  move=> d ln; have [w0 [w1 _]] := hfam d.
  exact: contaminated_tv.
have [hsat _ _] := (proj1 mixture_theorem) kappa K alpha k1 K0 a0.
have [c [_ [mE [_ hc]]]] := hsat ha.
have [p1 _] := hc N w mu hfam h4 n hn.
have -> : (fun d => mixture_probability (N d).+1
    (contaminated_weights lambda (n d) (N d) (w d))
    (contaminated_laws (N d) (mu d)) (n d) d
    (universality_pd_fit_event (n d) d)) =
  (fun d => (((1 - lambda / (n d)%:R) ^+ (n d))%:E *
    mixture_probability (N d) (w d) (mu d) (n d) d
      (universality_pd_fit_event (n d) d))%E).
  by apply/funext => d; exact: contaminated_probability.
exact: (contaminated_limit _ _ _ _ l0 a0 hn p1).
Qed.

Theorem robust_theorem_holds : robust_theorem_statement.
Proof.
split; [exact: robust_statement_holds | exact: robust_interpolation_holds |
  exact: contamination_holds].
Qed.
