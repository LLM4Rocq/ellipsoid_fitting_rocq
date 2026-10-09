(* The finite-mixture theorem for countable mixtures of product laws, at
   Stdlib's R: item K3 of phase 8 (notes/three-extensions-plan.md, sections
   1.3 and 5.2; lane A). Theorem is a keyword, so this module is required
   by its full name, Require Import EllipsoidUniversality.Countable.Theorem,
   not by the From form.

   Proved here.
   - countable_statement_holds : countable_mixture_statement and
     countable_interpolation_holds : countable_interpolation_statement,
     hence countable_theorem_holds : countable_theorem_statement. At each
     dimension d the countable family is replaced by its truncation of
     Countable/Truncation.v (trunc_N, trunc_w, trunc_mu), a finite family
     with the same K and kappa (trunc_family, trunc_fourth), to which
     mixture_theorem applies. The probabilities of a measurable set of
     samples under the two families differ by at most n_d r_d
     (trunc_coupling), and n_d r_d tends to 0 (trunc_nr_small), since
     r_d <= (d + 1)^-3 and n_d <= 2 alpha d^2 for d large. Limits and
     small probabilities therefore carry over (tends_to_transfer,
     countable_transfer). The constants c and C are those of the finite
     theorem.
   - countable_of_finite : countable_theorem_statement ->
     mixture_theorem_statement. A finite family is a countable one, with
     weights zero from N d on and the law mu d 0 j for the components
     s >= N d (fin_cw, fin_cmu, fin_cfamily, fin_cfourth), and the
     probabilities of measurable sets of samples are the same
     (fin_cprobability, by label_coupling with a tail of mass zero). So
     the countable statements contain the frozen finite ones, as the
     header of CountableMixtureStatement says. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype sequences esum.
From mathcomp Require Import ereal measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis Require Import lindeberg.
From GaussianAnalysis.probability Require Import mixture countable_mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions MixtureStatement.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality Require Import CountableMixtureStatement.
From EllipsoidUniversality Require Import MixtureTheorem.
From EllipsoidUniversality.Sat Require Import ApproximateFit.
From EllipsoidUniversality.Countable Require Import Truncation.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* 1. The coupling error n_d r_d tends to 0. *)
Lemma trunc_nr_small (K : R) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : countable_mixture_family K w mu) (n : nat -> nat) (alpha : R) :
  0 < alpha -> universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    (n d)%:R * trunc_r K w mu hfam d <= eps.
Proof.
move=> a0 hn eps e0.
have [D1 h1] := af_ev_density n alpha a0 hn.
have [D2 h2] := af_ev_ge (2 * alpha / eps).
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have [d0 [_ nhi]] := h1 d d1.
have hd := h2 d d2.
have r0 := trunc_r_ge0 K w mu hfam d.
have rle := trunc_r_le K w mu hfam d.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
set x := (n d)%:R in nhi *; set r := trunc_r K w mu hfam d in r0 rle *.
have x0 : 0 <= x by rewrite /x ler0n.
(* n r <= 2 alpha d^2 / (d + 1)^3 <= 2 alpha / d <= eps *)
apply: (@le_trans _ _ ((2 * alpha * d%:R ^+ 2) * ((d.+1%:R) ^+ 3)^-1)).
  by apply: ler_pM.
have d1p : 0 < (d.+1%:R ^+ 3 : RR) by rewrite exprn_gt0 // ltr0n.
rewrite ler_pdivrMr //.
have h : 2 * alpha <= eps * d%:R.
  by move: hd; rewrite ler_pdivrMr // [d%:R * _]mulrC.
apply: (@le_trans _ _ (eps * d%:R * d%:R ^+ 2)).
  by rewrite ler_wpM2r // exprn_ge0 // ltW.
rewrite -mulrA -exprS ler_pM2l //.
by rewrite ler_pXn2r ?nnegrE ?ler0n // ler_nat.
Qed.

(* 2. Two sequences of finite values whose distance tends to 0 have the
   same limit. *)
Lemma tends_to_transfer (a b : nat -> \bar R) (c : nat -> R) (l : R) :
  (forall d, (`|a d - b d| <= (c d)%:E)%E) -> (forall d, b d \is a fin_num) ->
  (forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
     c d <= eps) ->
  paper_main_tends_to b l -> paper_main_tends_to a l.
Proof.
move=> hab bf hc hb eps e0.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have [D1 h1] := hb _ e2.
have [D2 h2] := hc _ e2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have hb1 := h1 d d1.
have hc2 := h2 d d2.
have hd := hab d.
have af : a d \is a fin_num.
  move: hd; have := bf d; case: (b d) => [y _||] //.
  by case: (a d) => [x||] //=.
move: hb1 hd; rewrite -(fineK af) -(fineK (bf d)) /= !lte_fin lee_fin.
move=> hb1 hd.
have tri : `|fine (a d) - l| <=
    `|fine (a d) - fine (b d)| + `|fine (b d) - l|.
  by rewrite (le_trans _ (ler_normD _ _)) // addrA subrK.
by apply: le_lt_trans tri _; lra.
Qed.

(* 3. The transfer from the truncated families. *)
Section countable_transfer.
Variables (K : R) (w : nat -> nat -> R).
Variable (mu : nat -> nat -> nat -> probability (measurableTypeR R) R).
Hypothesis hfam : countable_mixture_family K w mu.
Variables (n : nat -> nat) (alpha : R).
Hypotheses (a0 : 0 < alpha) (hn : universality_density_tends_to n alpha).

Local Notation Nt := (trunc_N K w mu hfam).
Local Notation wt := (trunc_w K w mu hfam).
Local Notation mut := (trunc_mu K w mu hfam).

Lemma trunc_probability_fin d (E : set (paper_main_sample (n d) d)) :
  measurable E ->
  mixture_probability (Nt d) (wt d) (mut d) (n d) d E \is a fin_num.
Proof.
move=> mE.
have [w0 [w1 _]] := trunc_family K w mu hfam d.
have hw : mixture_weights (fun s : 'I_(Nt d) => wt d s).
  by split => [s|]; [exact: w0 (ltn_ord s) | exact: w1].
pose P := mixture (fun s : (n d).-tuple 'I_(Nt d) =>
  mixture_labelled_law (Nt d) (mut d) (n d) d s) (mixture_weights_prod (n d) hw).
have -> : mixture_probability (Nt d) (wt d) (mut d) (n d) d E = P E by [].
exact: fin_num_measure.
Qed.

Lemma countable_transfer (E : forall d, set (paper_main_sample (n d) d))
    (l : R) : (forall d, measurable (E d)) ->
  paper_main_tends_to
    (fun d => mixture_probability (Nt d) (wt d) (mut d) (n d) d (E d)) l ->
  paper_main_tends_to
    (fun d => countable_mixture_probability (w d) (mu d) (n d) d (E d)) l.
Proof.
move=> mE h.
apply: (tends_to_transfer _ _ (fun d => (n d)%:R * trunc_r K w mu hfam d) l
  _ _ _ h).
- by move=> d; exact: trunc_coupling.
- by move=> d; exact: trunc_probability_fin.
- exact: (trunc_nr_small K w mu hfam n alpha a0 hn).
Qed.

End countable_transfer.

(* 4. The theorem for countable mixtures. *)
Theorem countable_statement_holds : countable_mixture_statement.
Proof.
move=> kappa K alpha k1 K0 a0.
have [hsat hunsat herr] := (proj1 mixture_theorem) kappa K alpha k1 K0 a0.
split.
- move=> ha; have [c [c1 [m1 [m2 hc]]]] := hsat ha.
  exists c; split => //; split => //; split => //.
  move=> w mu hfam h4 n hn.
  have [p1 p2] := hc _ _ _ (trunc_family K w mu hfam)
    (trunc_fourth K w mu hfam kappa h4) n hn.
  split.
    apply: (countable_transfer K w mu hfam n alpha a0 hn) p1.
    by move=> d; exact: m1.
  apply: (countable_transfer K w mu hfam n alpha a0 hn) p2.
  by move=> d; exact: m2.
- move=> ha; have [e0 [m hc]] := hunsat ha.
  split => //; split => //.
  move=> w mu hfam h4 n hn.
  apply: (countable_transfer K w mu hfam n alpha a0 hn).
    by move=> d; exact: m.
  exact: hc _ _ _ (trunc_family K w mu hfam)
    (trunc_fourth K w mu hfam kappa h4) n hn.
- have [m hc] := herr.
  split => // w mu hfam h4 n hn eps e0.
  apply: (countable_transfer K w mu hfam n alpha a0 hn).
    by move=> d; exact: m.
  exact: hc _ _ _ (trunc_family K w mu hfam)
    (trunc_fourth K w mu hfam kappa h4) n hn eps e0.
Qed.

Theorem countable_interpolation_holds : countable_interpolation_statement.
Proof.
move=> K alpha K0 a0 ah.
have [C [C0 hC]] := (proj2 mixture_theorem) K alpha K0 a0 ah.
exists C; split => // w mu hfam n hn eps e0.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have [D1 h1] := hC _ _ _ (trunc_family K w mu hfam) n hn (eps / 2) e2.
have [D2 h2] := trunc_nr_small K w mu hfam n alpha a0 hn (eps / 2) e2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have [E [mE PE hE]] := h1 d d1.
exists E; split => //.
(* the countable probability of E is at most eps / 2 + n r_d *)
have hc := trunc_coupling K w mu hfam (n d) d E mE.
have ff := trunc_probability_fin K w mu hfam n d E mE.
have hr : (n d)%:R * trunc_r K w mu hfam d <= eps / 2 := h2 d d2.
move: hc PE ff.
set X := countable_mixture_probability _ _ _ _ E.
set Y := mixture_probability _ _ _ _ _ E => hc PE ff.
have xf : X \is a fin_num.
  clearbody X Y.
  by move: hc PE ff; case: X => [x||]; case: Y => [y||] //=.
move: hc PE; rewrite -(fineK xf) -(fineK ff) /= !lee_fin.
rewrite ler_norml => /andP[_ h] PE.
lra.
Qed.

Theorem countable_theorem_holds : countable_theorem_statement.
Proof.
exact: (conj countable_statement_holds countable_interpolation_holds).
Qed.

(* 5. A finite family is a countable one: the weights are zero from N d on,
   and the probabilities of the sets of samples do not change. Hence the
   countable statements contain the frozen finite ones. *)
Section finite_as_countable.
Variables (K : R) (N : nat -> nat) (w : nat -> nat -> R).
Variable (mu : nat -> nat -> nat -> probability (measurableTypeR R) R).
Hypothesis hfam : mixture_family K N w mu.

Definition fin_cw d (s : nat) : R := if (s < N d)%N then w d s else 0.

Definition fin_cmu d (s j : nat) : probability (measurableTypeR R) R :=
  if (s < N d)%N then mu d s j else mu d 0%N j.

Lemma fin_N_gt0 d : (0 < N d)%N.
Proof.
have [_ [w1 _]] := hfam d.
rewrite lt0n; apply/negP => /eqP N0.
by move: w1; rewrite N0 big_ord0 => /eqP; rewrite eq_sym oner_eq0.
Qed.

Lemma fin_cw_series d (F : nat -> \bar R) : (forall s, (0 <= F s)%E) ->
  (\sum_(s <oo) (fin_cw d s)%:E * F s =
   \sum_(s < N d) (w d s)%:E * F s)%E.
Proof.
move=> F0.
have [w0 _] := hfam d.
have t0 k : (0 <= k)%N -> (0 <= (fin_cw d k)%:E * F k)%E.
  move=> _; rewrite mule_ge0 // lee_fin /fin_cw; case: ifP => // kN.
  exact: w0.
rewrite (nneseries_split 0 (N d) t0) add0n.
have -> : (\sum_(N d <= k <oo) (fin_cw d k)%:E * F k = 0)%E.
  by apply: eseries0 => k Nk _; rewrite /fin_cw ltnNge Nk /= mul0e.
rewrite adde0 big_mkord; apply: eq_bigr => k _.
by rewrite /fin_cw ltn_ord.
Qed.

Lemma fin_cfamily : countable_mixture_family K fin_cw fin_cmu.
Proof.
move=> d; have [w0 [w1 hc]] := hfam d.
split; [|split].
- by move=> s; rewrite /fin_cw; case: ifP => // sN; exact: w0.
- have := fin_cw_series d (fun=> 1%E) (fun=> lee01).
  under eq_eseriesr do rewrite mule1.
  move=> ->; under eq_bigr do rewrite mule1.
  by rewrite sumEFin w1.
- move=> s j jd; rewrite /fin_cmu; case: ifP => sN; first exact: hc.
  exact: hc (fin_N_gt0 d) jd.
Qed.

Lemma fin_cfourth (kappa : R) : mixture_fourth_moment kappa N w mu ->
  countable_fourth_moment kappa fin_cw fin_cmu.
Proof.
move=> h4 d j jd.
have E0 s : (0 <= 'E_(fin_cmu d s j)[universality_power 4])%E.
  rewrite unlock; apply: integral_ge0 => x _.
  by rewrite lee_fin /universality_power exprn_even_ge0.
rewrite (fin_cw_series d _ E0) -(h4 d j jd).
by apply: eq_bigr => s _; rewrite /fin_cmu ltn_ord.
Qed.

Lemma fin_cprobability n d (E : set (paper_main_sample n d)) : measurable E ->
  countable_mixture_probability (fin_cw d) (fin_cmu d) n d E =
  mixture_probability (N d) (w d) (mu d) n d E.
Proof.
move=> mE.
have N0 := fin_N_gt0 d.
have hp : cmixture_weights (fin_cw d).
  by have [h1 [h2 _]] := fin_cfamily d; split.
have [w0 [w1 hc]] := hfam d.
pose m := (N d).-1.
have mN : (m < N d)%N by rewrite /m ltn_predL.
have qp k : (k <= m)%N -> w d k = fin_cw d k.
  by move=> km; rewrite /fin_cw (leq_ltn_trans km mN).
(* every label tuple of 'I_(N d) has its labels at most m *)
have QQ (t : n.-tuple 'I_(N d)) :
    all (fun k : 'I_(N d) => (k <= m)%N) t ->
    mixture_labelled_law (N d) (mu d) n d t E =
    countable_labelled_law (fin_cmu d) n d
      (map_tuple (@nat_of_ord (N d)) t) E.
  move=> _; rewrite /mixture_labelled_law /countable_labelled_law.
  congr (tuple_prod _ _ E); apply/funext => k.
  rewrite /mixture_label /fin_cmu /=.
  have -> : (nth 0%N (map val t) (k %/ d) < N d)%N.
    have [kn|kn] := ltnP (k %/ d) n.
      by rewrite (nth_map (Ordinal N0)) ?size_tuple // ltn_ord.
    by rewrite nth_default // size_map size_tuple.
  by [].
have h := label_coupling hp mE mN w0 w1 qp QQ.
(* the weights above m vanish *)
have r0 : cmixture_tail (fin_cw d) m = 0.
  rewrite /cmixture_tail eseries0 // => s _ ms.
  by rewrite /fin_cw ltnNge -(ltn_predK mN) ms.
have hw : mixture_weights (fun s : 'I_(N d) => w d s).
  by split => [s|]; [exact: w0 (ltn_ord s) | exact: w1].
pose P := mixture (fun s : n.-tuple 'I_(N d) =>
  mixture_labelled_law (N d) (mu d) n d s) (mixture_weights_prod n hw).
have Yf : mixture_probability (N d) (w d) (mu d) n d E \is a fin_num.
  have -> : mixture_probability (N d) (w d) (mu d) n d E = P E by [].
  exact: fin_num_measure.
move: h; rewrite r0 subr0 expr1n subrr => h.
have h' : (`|countable_mixture_probability (fin_cw d) (fin_cmu d) n d E -
    mixture_probability (N d) (w d) (mu d) n d E| <= 0%:E)%E := h.
move: Yf h'; set Y := mixture_probability _ _ _ _ _ E.
set X := countable_mixture_probability _ _ _ _ E => Yf h''.
have h0 : (`|X - Y| = 0)%E by apply/eqP; rewrite eq_le h'' abse_ge0.
move/eqP: h0; rewrite abse_eq0 => /eqP h0.
by have := subeK X Yf; rewrite h0 add0e => <-.
Qed.

End finite_as_countable.

Theorem countable_of_finite :
  countable_theorem_statement -> mixture_theorem_statement.
Proof.
move=> [hS hI]; split.
- move=> kappa K alpha k1 K0 a0.
  have [hsat hunsat herr] := hS kappa K alpha k1 K0 a0.
  have hP (N : nat -> nat) w mu (hfam : mixture_family K N w mu) n
      (E : forall d, set (paper_main_sample (n d) d)) :
      (forall d, measurable (E d)) ->
      (fun d => countable_mixture_probability (fin_cw N w d) (fin_cmu N mu d)
                  (n d) d (E d)) =
      (fun d => mixture_probability (N d) (w d) (mu d) (n d) d (E d)).
    move=> mE; apply/funext => d.
    exact: fin_cprobability K N w mu hfam (n d) d (E d) (mE d).
  split.
  + move=> ha; have [c [c1 [m1 [m2 hc]]]] := hsat ha.
    exists c; split => //; split => //; split => //.
    move=> N w mu hfam h4 n hn.
    have [p1 p2] := hc _ _ (fin_cfamily K N w mu hfam)
      (fin_cfourth K N w mu hfam kappa h4) n hn.
    rewrite -(hP N w mu hfam n _ (fun d => m1 (n d) d)).
    rewrite -(hP N w mu hfam n _ (fun d => m2 (n d) d)).
    by split.
  + move=> ha; have [e0 [m hc]] := hunsat ha.
    split => //; split => // N w mu hfam h4 n hn.
    rewrite -(hP N w mu hfam n _ (fun d => m (n d) d)).
    exact: hc _ _ (fin_cfamily K N w mu hfam)
      (fin_cfourth K N w mu hfam kappa h4) n hn.
  + have [m hc] := herr.
    split => // N w mu hfam h4 n hn eps e0.
    rewrite -(hP N w mu hfam n _ (fun d => m (n d) d eps)).
    exact: hc _ _ (fin_cfamily K N w mu hfam)
      (fin_cfourth K N w mu hfam kappa h4) n hn eps e0.
- move=> K alpha K0 a0 ah.
  have [C [C0 hC]] := hI K alpha K0 a0 ah.
  exists C; split => // N w mu hfam n hn eps e0.
  have [D hD] := hC _ _ (fin_cfamily K N w mu hfam) n hn eps e0.
  exists D => d dD; have [E [mE PE hE]] := hD d dD.
  exists E; split => //.
  by rewrite -(fin_cprobability K N w mu hfam (n d) d E mE).
Qed.
