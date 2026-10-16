(* Positive definite fits for arbitrary shifts on a negligible coordinate
   block. The complementary fit and all-target interpolation event are
   combined with a head-target bound by a union bound. No independence of
   the two blocks, symmetry, or measurable selection of a fitting matrix
   is assumed. Source: doc/shifted-gaussian.tex, sparse shifts. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import esum sequences ereal measure lebesgue_measure measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.analysis Require Import family_reindexing.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.probability Require Import lindeberg mixture countable_mixture tuple_rows isotropic_mixtures independent_row_signs.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.random_matrix Require Import isotropic_rows symmetric_reserve.
From EllipsoidUniversality.Sat Require Import AprioriSparse Universality.
From EllipsoidUniversality.Mixture Require Import Flat.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting.Gaussian.Law Require Import LibraryBridge.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions CountableMixtureDefinitions.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Shifted Require Import Translations SparseRows SparseInputs
  SparseTargets SparseTargetBounds SparseInterpolation SparseBlockSamples GaussianTargets GaussianExistence
  GaussianRows SignMixture MixtureRows MainMoment ResidualLaws ConditionTranslation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma measurable_sparse_pd_fit n h p (m : 'rV[RR]_h) :
  measurable (sample_translate (sparse_block_shift p m) @^-1`
    universality_pd_fit_event n (h+p)).
Proof.
rewrite -[X in measurable X]setTI.
exact: measurable_sample_translate (measurable_pd_fit_event _ _).
Qed.

Lemma sparse_pd_probability_from_covers n h p
    (P : probability (paper_main_sample n (h+p)) RR)
    (pi : set (paper_main_sample n p) -> \bar RR)
    (m : 'rV[RR]_h) (c L e1 e2 : R)
    (B : set (paper_main_sample n (h+p))) :
  (forall A : set (paper_main_sample n p), measurable A ->
    P ((@sparse_sample_tail n h p) @^-1` A) = pi A) ->
  sparse_joint_cover pi c L e1 -> measurable B -> (P B <= e2%:E)%E ->
  (forall x, universality_conditioned_fit_event n p c (sparse_sample_tail x) ->
    mixture_interpolation n p L (sparse_sample_tail x) -> ~ B x ->
    universality_pd_fit_event n (h+p)
      (sample_translate (sparse_block_shift p m) x)) ->
  (P (~` (sample_translate (sparse_block_shift p m) @^-1`
    universality_pd_fit_event n (h+p))) <= (e1+e2)%:E)%E.
Proof.
move=> law [E [mE PE good]] mB PB fit.
pose A := sample_translate (sparse_block_shift p m) @^-1`
  universality_pd_fit_event n (h+p).
have mA : measurable A := @measurable_sparse_pd_fit n h p m.
have mT : measurable ((@sparse_sample_tail n h p) @^-1` E).
  rewrite -[X in measurable X]setTI; exact: measurable_sparse_sample_pick mE.
have inclusion : ~` A `<=` ((@sparse_sample_tail n h p) @^-1` E) `|` B.
  move=>x nx; apply: contrapT=>out.
  have nE : ~ E (sparse_sample_tail x) by move=>ex; apply: out; left.
  have nB : ~ B x by move=>bx; apply: out; right.
  have [fx ix] := good _ nE.
  apply: nx; exact: fit fx ix nB.
have bound : (P (~` A) <= P (((@sparse_sample_tail n h p) @^-1` E) `|` B))%E.
  apply: le_measure; rewrite ?inE //.
  - exact: measurableC mA.
  - exact: measurableU mT mB.
apply: le_trans bound _; apply: le_trans (measureU2 P mT mB) _.
have PT : (P ((@sparse_sample_tail n h p) @^-1` E) <= e1%:E)%E.
  by rewrite (law E mE).
rewrite EFinD; exact: leeD PT PB.
Qed.


(* These law identities need only valid weights. In particular, the local
   coordinate laws do not have to be extended to a family indexed by the
   physical dimension. *)
Section local_finite_law.
Variables (N : nat) (w : nat -> R)
  (mu : nat -> nat -> probability (measurableTypeR R) R).
Hypothesis hw : mixture_weights (fun s : 'I_N => w s).

Lemma sparse_finite_sample_row_tuple_law n d (A : set (n.-tuple 'rV[RR]_d)) :
  measurable A ->
  mixture_probability N w mu n d (sample_row_tuple @^-1` A) =
    tuple_prod (fun=> mixture (fun s : 'I_N => point_law d (mu s)) hw) n A.
Proof.
move=> mA; have [s0 _] := mixture_weights_inhabited hw.
rewrite (tuple_prod_mixture _ hw s0 mA).
rewrite /mixture_probability; apply: eq_bigr=>s _; congr (_ * _)%E.
rewrite /mixture_labelled_law.
have E : sample_row_tuple = (fun x : paper_main_sample n d =>
  tuple_map (fun=> row_of_tuple d) (tuple_rows n d x)).
  by apply/funext=>x; exact: sample_row_tupleE.
rewrite E.
rewrite (@flat_map_law _ n d _ _ (fun i => point_law d
  (flat_row (fun k => mu (mixture_label s (k %/ d)) (k %% d)) d i))
  (row_of_tuple d) A).
- exact: measurable_row_of_tuple.
- by move=> i B mB; rewrite /point_law /distribution /pushforward.
- exact: mA.
- refine (f_equal (fun Q : probability (n.-tuple 'rV[RR]_d) RR => Q A) _).
  apply: eq_tuple_prod=>i hi.
  pose ii : 'I_n := Ordinal hi.
  have es : nth s0 s i = tnth s ii by rewrite (tnth_nth s0) /ii.
  rewrite es /point_law (@flat_row_label_prod N mu n d s ii).
  by [].
Qed.

Lemma sparse_finite_flat_probability n d (A : set (paper_main_sample n d)) :
  measurable A ->
  iid_row_sample_law (mixture (fun s : 'I_N => point_law d (mu s)) hw) n A =
    mixture_probability N w mu n d A.
Proof.
move=>mA; rewrite iid_row_sample_lawE.
have mB : measurable ((@sample_of_row_tuple n d) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_sample_of_row_tuple.
rewrite -(sparse_finite_sample_row_tuple_law mB).
congr (mixture_probability _ _ _ _ _ _); apply/funext=>x /=.
by rewrite sample_row_tupleK.
Qed.

Lemma sparse_finite_matrix_probability n d (A : set 'M[RR]_(n,d)) :
  measurable A ->
  mixture_probability N w mu n d ((@sample_point_matrix n d) @^-1` A) =
    independent_row_matrix_law
      (fun=> mixture (fun s : 'I_N => point_law d (mu s)) hw) n A.
Proof.
move=>mA; rewrite independent_row_matrix_lawE.
have mB : measurable (row_tuple_matrix n @^-1` A).
  exact (measurable_funPTI (row_tuple_matrix n) mA).
rewrite -(sparse_finite_sample_row_tuple_law mB).
by [].
Qed.
End local_finite_law.

Section local_countable_law.
Variables (w : nat -> R)
  (mu : nat -> nat -> probability (measurableTypeR R) R).
Hypothesis hw : cmixture_weights w.

Lemma sparse_countable_sample_row_tuple_law n d (A : set (n.-tuple 'rV[RR]_d)) :
  measurable A ->
  countable_mixture_probability w mu n d (sample_row_tuple @^-1` A) =
    tuple_prod (fun=> cmixture (fun s => point_law d (mu s)) hw) n A.
Proof.
move=>mA; rewrite (tuple_prod_cmixture _ hw mA).
rewrite /countable_mixture_probability; apply: eq_esum=>s _; congr (_ * _)%E.
rewrite /countable_labelled_law.
have E : sample_row_tuple = (fun x : paper_main_sample n d =>
  tuple_map (fun=> row_of_tuple d) (tuple_rows n d x)).
  by apply/funext=>x; exact: sample_row_tupleE.
rewrite E.
rewrite (@flat_map_law _ n d _ _ (fun i => point_law d
  (flat_row (fun k => mu (nth 0%N s (k %/ d)) (k %% d)) d i))
  (row_of_tuple d) A).
- exact: measurable_row_of_tuple.
- by move=>i B mB; rewrite /point_law /distribution /pushforward.
- exact: mA.
- refine (f_equal (fun Q : probability (n.-tuple 'rV[RR]_d) RR => Q A) _).
  apply: eq_tuple_prod=>i hi; rewrite /point_law.
  have Ep : tuple_prod (flat_row
      (fun k => mu (nth 0%N s (k %/ d)) (k %% d)) d i) d =
      tuple_prod (mu (nth 0%N s i)) d.
    apply: eq_tuple_prod=>j hj.
    have d0 : (0<d)%N := leq_ltn_trans (leq0n j) hj.
    by rewrite /flat_row divnMDl // divn_small // addn0 modnMDl modn_small.
  by rewrite Ep.
Qed.

Lemma sparse_countable_flat_probability n d (A : set (paper_main_sample n d)) :
  measurable A ->
  iid_row_sample_law (cmixture (fun s => point_law d (mu s)) hw) n A =
    countable_mixture_probability w mu n d A.
Proof.
move=>mA; rewrite iid_row_sample_lawE.
have mB : measurable ((@sample_of_row_tuple n d) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_sample_of_row_tuple.
rewrite -(sparse_countable_sample_row_tuple_law mB).
congr (countable_mixture_probability _ _ _ _ _); apply/funext=>x /=.
by rewrite sample_row_tupleK.
Qed.

Lemma sparse_countable_matrix_probability n d (A : set 'M[RR]_(n,d)) :
  measurable A ->
  countable_mixture_probability w mu n d ((@sample_point_matrix n d) @^-1` A) =
    independent_row_matrix_law (fun=> cmixture (fun s => point_law d (mu s)) hw) n A.
Proof.
move=>mA; rewrite independent_row_matrix_lawE.
have mB : measurable (row_tuple_matrix n @^-1` A).
  exact (measurable_funPTI (row_tuple_matrix n) mA).
rewrite -(sparse_countable_sample_row_tuple_law mB).
by [].
Qed.
End local_countable_law.


Lemma sparse_sample_dimensions_positive (p n : nat -> nat) (alpha : R) :
  0 < alpha -> family_cofinal p ->
  family_sequence_limit (fun d => (n d)%:R/(p d)%:R^+2 : RR) alpha ->
  exists D, forall d, (D<=d)%N -> (0<p d)%N /\ (0<n d)%N.
Proof.
move=>a0 hp hn.
have a20 : 0<alpha/2 by rewrite divr_gt0.
have [Dp hDp] := hp 1%N; have [Dn hDn] := hn (alpha/2) a20.
exists (maxn Dp Dn)=>d; rewrite geq_max=>/andP[dp dn].
have p0 : (0<p d)%N := hDp d dp.
have hd := hDn d dn; rewrite ltr_norml in hd; move: hd=>/andP[hl _].
have hq : (0:RR)<(n d)%:R/(p d)%:R^+2 by lra.
have n0 : (0<n d)%N.
  by case: (n d) hq=>[|k] //; rewrite mul0r ltxx.
by split.
Qed.

Definition sparse_finite_tail h (t : sparse_finite_parameters) :=
  SparseFiniteParameters (sparse_finite_n t) (sparse_finite_components t)
    (sparse_finite_weights t) (fun s j => sparse_finite_laws t s (h+j)%N).

Lemma sparse_finite_tail_admissible K kappa h p t :
  sparse_finite_admissible K kappa (h+p) t ->
  sparse_finite_admissible K kappa p (sparse_finite_tail h t).
Proof.
rewrite /sparse_finite_admissible /sparse_finite_tail /=.
move=>[[hw [hs hc]] hf]; split.
- split=>//; split=>// s j sN jp.
  apply: hc sN _; by rewrite ltn_add2l.
- move=>j jp; apply: hf; by rewrite ltn_add2l.
Qed.

Definition sparse_countable_tail h (t : sparse_countable_parameters) :=
  SparseCountableParameters (sparse_countable_n t) (sparse_countable_weights t)
    (fun s j => sparse_countable_laws t s (h+j)%N).

Lemma sparse_countable_tail_admissible K kappa h p t :
  sparse_countable_admissible K kappa (h+p) t ->
  sparse_countable_admissible K kappa p (sparse_countable_tail h t).
Proof.
rewrite /sparse_countable_admissible /sparse_countable_tail /=.
move=>[[hw [hs hc]] hf]; split.
- split=>//; split=>// s j jp.
  apply: hc; by rewrite ltn_add2l.
- move=>j jp; apply: hf; by rewrite ltn_add2l.
Qed.


Lemma measurable_sparse_target_atleast n h p (L delta : R) (m : 'rV[RR]_h) :
  measurable [set x : paper_main_sample n (h+p) |
    delta <= sparse_sample_target_size L m x].
Proof.
have := (@measurable_sparse_sample_target_size n h p L m) measurableT _
  (measurable_itv `[(delta : RR), +oo[).
rewrite setTI; congr measurable; apply/seteqP.
by split=>x /=; rewrite in_itv /= andbT.
Qed.

Theorem sparse_pd_limit_of_inputs (n h p : nat -> nat)
    (P : forall d, probability (paper_main_sample (n d) (h d+p d)) RR)
    (pi : forall d, set (paper_main_sample (n d) (p d)) -> \bar RR)
    (m : forall d, 'rV[RR]_(h d)) (D L : R) :
  1<=D -> 0<=L ->
  (exists d0, forall d, (d0<=d)%N -> (0<n d)%N /\ (0<p d)%N) ->
  (forall d A, measurable A ->
    P d ((@sparse_sample_tail (n d) (h d) (p d)) @^-1` A) = pi d A) ->
  (forall eps : R, 0<eps -> exists d0, forall d, (d0<=d)%N ->
    sparse_joint_cover (pi d) D L eps) ->
  (forall eps delta : R, 0<eps -> 0<delta -> exists d0, forall d, (d0<=d)%N ->
    (P d [set x | (delta <= sparse_sample_target_size L (m d) x)%R] <= eps%:E)%E) ->
  paper_main_tends_to (fun d => P d
    (sample_translate (sparse_block_shift (p d) (m d)) @^-1`
      universality_pd_fit_event (n d) (h d+p d))) 1.
Proof.
move=> D1 L0 [Dn hDn] law cover target eps eps0.
have D0 : 0<D := lt_le_trans ltr01 D1.
have gap0 : 0<(2*D)^-1 by rewrite invr_gt0 mulr_gt0.
have e40 : 0<eps/4 by rewrite divr_gt0.
have [Dc hDc] := cover (eps/4) e40.
have [Dt hDt] := target (eps/4) ((2*D)^-1) e40 gap0.
exists (maxn Dn (maxn Dc Dt))=>d; rewrite !geq_max=>/andP[dn /andP[dc dt]].
have [n0 p0] := hDn d dn.
pose B : set (paper_main_sample (n d) (h d+p d)) :=
  [set x | (2*D)^-1 <= sparse_sample_target_size L (m d) x].
have mB : measurable B.
  exact: measurable_sparse_target_atleast.
have PB : (P d B <= (eps/4)%:E)%E := hDt d dt.
have fit x :
    universality_conditioned_fit_event (n d) (p d) D (sparse_sample_tail x) ->
    mixture_interpolation (n d) (p d) L (sparse_sample_tail x) -> ~ B x ->
    universality_pd_fit_event (n d) (h d+p d)
      (sample_translate (sparse_block_shift (p d) (m d)) x).
  move=>fx ix nx; apply: sparse_block_sample_pd_fit n0 p0 D1 L0 fx ix _.
  apply: ltW; rewrite ltNge; apply/negP=>hb; exact: nx hb.
have Pc := sparse_pd_probability_from_covers (law d) (hDc d dc) mB PB fit.
pose A := sample_translate (sparse_block_shift (p d) (m d)) @^-1`
  universality_pd_fit_event (n d) (h d+p d).
have mA : measurable A := @measurable_sparse_pd_fit (n d) (h d) (p d) (m d).
have close : (`|P d A-1%:E| <= (eps/4+eps/4)%:E)%E.
  apply: (prob_close_one _ _ (P d) A (~` A) _ mA (measurableC mA))=>//.
apply: le_lt_trans close _; rewrite lte_fin.
change (is_true ((eps/4+eps/4 : RR)<eps)); clear -eps0; lra.
Qed.


Lemma sparse_finite_admissible_weights K kappa q t :
  sparse_finite_admissible K kappa q t ->
  mixture_weights (fun s : 'I_(sparse_finite_components t) => sparse_finite_weights t s).
Proof.
move=>[[hw [hs _]] _]; split=>// s; exact: hw (ltn_ord s).
Qed.

Lemma sparse_countable_admissible_weights K kappa q t :
  sparse_countable_admissible K kappa q t -> cmixture_weights (sparse_countable_weights t).
Proof. by move=>[[hw [hs _]] _]; split. Qed.

Theorem finite_sparse_shift_pd_of_target (kappa K alpha : R)
    (base : nat -> sparse_finite_parameters) (h p : nat -> nat)
    (t : nat -> sparse_finite_parameters) (m : forall d, 'rV[RR]_(h d)) :
  1<kappa -> 0<K -> 0<alpha -> alpha<universality_alpha_star kappa ->
  (forall q, sparse_finite_admissible K kappa q (base q)) ->
  family_sequence_limit (fun q => (sparse_finite_n (base q))%:R/q%:R^+2 : RR) alpha ->
  family_cofinal p ->
  (forall d, sparse_finite_admissible K kappa (h d+p d) (t d)) ->
  family_sequence_limit (fun d => (sparse_finite_n (t d))%:R/(p d)%:R^+2 : RR) alpha ->
  (forall L : R, 0<=L -> forall eps delta : R, 0<eps -> 0<delta ->
    exists d0, forall d, (d0<=d)%N ->
    (sparse_finite_probability (h d+p d) (t d)
      [set x | (delta<=sparse_sample_target_size L (m d) x)%R] <= eps%:E)%E) ->
  paper_main_tends_to (fun d => sparse_finite_probability (h d+p d) (t d)
    (sample_translate (sparse_block_shift (p d) (m d)) @^-1`
      universality_pd_fit_event (sparse_finite_n (t d)) (h d+p d))) 1.
Proof.
move=>k1 K0 a0 below Ab hb hp At hn target.
have [c [L [c1 L0 input]]] := finite_sparse_input_constants k1 K0 a0 below.
have tailA d := sparse_finite_tail_admissible (At d).
have covers := input base Ab hb p (fun d => sparse_finite_tail (h d) (t d)) hp tailA hn.
pose n d := sparse_finite_n (t d).
have hw d := sparse_finite_admissible_weights (At d).
pose P d := iid_row_sample_law
  (mixture (fun s : 'I_(sparse_finite_components (t d)) =>
    point_law (h d+p d) (sparse_finite_laws (t d) s)) (hw d)) (n d).
have law d A : measurable A -> P d A = sparse_finite_probability (h d+p d) (t d) A.
  move=>mA; exact: (@sparse_finite_flat_probability (sparse_finite_components (t d))
    (sparse_finite_weights (t d)) (sparse_finite_laws (t d)) (hw d)
    (n d) (h d+p d) A mA).
pose pi d := sparse_finite_probability (p d) (sparse_finite_tail (h d) (t d)).
have law_tail d A : measurable A ->
    P d ((@sparse_sample_tail (n d) (h d) (p d)) @^-1` A) = pi d A.
  move=>mA.
  have mB : measurable ((@sparse_sample_tail (n d) (h d) (p d)) @^-1` A).
    rewrite -[X in measurable X]setTI; exact: measurable_sparse_sample_pick mA.
  rewrite (law d _ mB).
  rewrite /pi /sparse_finite_probability /sparse_finite_tail /= /sparse_sample_tail.
  apply: finite_sparse_sample_law=>//.
  exact: rshift_inj.
have dims : exists d0, forall d, (d0<=d)%N -> (0<n d)%N /\ (0<p d)%N.
  have [d0 hd] := sparse_sample_dimensions_positive a0 hp hn.
  exists d0=>d dd; have [p0 n0] := hd d dd; by split.
have targets : forall eps delta : R, 0<eps -> 0<delta ->
    exists d0, forall d, (d0<=d)%N ->
      (P d [set x | (delta<=sparse_sample_target_size L (m d) x)%R] <= eps%:E)%E.
  move=>eps delta ep dp; have [d0 hd] := target L (ltW L0) eps delta ep dp.
  exists d0=>d dd.
  have mB := @measurable_sparse_target_atleast (n d) (h d) (p d) L delta (m d).
  rewrite (law d _ mB); exact: hd.
have result := sparse_pd_limit_of_inputs c1 (ltW L0) dims law_tail covers targets.
move=>eps ep; have [d0 hd] := result eps ep; exists d0=>d dd.
have mA := @measurable_sparse_pd_fit (n d) (h d) (p d) (m d).
rewrite -(law d _ mA); exact: hd.
Qed.


Theorem countable_sparse_shift_pd_of_target (kappa K alpha : R)
    (base : nat -> sparse_countable_parameters) (h p : nat -> nat)
    (t : nat -> sparse_countable_parameters) (m : forall d, 'rV[RR]_(h d)) :
  1<kappa -> 0<K -> 0<alpha -> alpha<universality_alpha_star kappa ->
  (forall q, sparse_countable_admissible K kappa q (base q)) ->
  family_sequence_limit (fun q => (sparse_countable_n (base q))%:R/q%:R^+2 : RR) alpha ->
  family_cofinal p ->
  (forall d, sparse_countable_admissible K kappa (h d+p d) (t d)) ->
  family_sequence_limit (fun d => (sparse_countable_n (t d))%:R/(p d)%:R^+2 : RR) alpha ->
  (forall L : R, 0<=L -> forall eps delta : R, 0<eps -> 0<delta ->
    exists d0, forall d, (d0<=d)%N ->
    (sparse_countable_probability (h d+p d) (t d)
      [set x | (delta<=sparse_sample_target_size L (m d) x)%R] <= eps%:E)%E) ->
  paper_main_tends_to (fun d => sparse_countable_probability (h d+p d) (t d)
    (sample_translate (sparse_block_shift (p d) (m d)) @^-1`
      universality_pd_fit_event (sparse_countable_n (t d)) (h d+p d))) 1.
Proof.
move=>k1 K0 a0 below Ab hb hp At hn target.
have [c [L [c1 L0 input]]] := countable_sparse_input_constants k1 K0 a0 below.
have tailA d := sparse_countable_tail_admissible (At d).
have covers := input base Ab hb p (fun d => sparse_countable_tail (h d) (t d)) hp tailA hn.
pose n d := sparse_countable_n (t d).
have hw d := sparse_countable_admissible_weights (At d).
pose P d := iid_row_sample_law
  (cmixture (fun s => point_law (h d+p d) (sparse_countable_laws (t d) s))
    (hw d)) (n d).
have law d A : measurable A -> P d A = sparse_countable_probability (h d+p d) (t d) A.
  move=>mA; exact: (@sparse_countable_flat_probability (sparse_countable_weights (t d)) (sparse_countable_laws (t d)) (hw d)
    (n d) (h d+p d) A mA).
pose pi d := sparse_countable_probability (p d) (sparse_countable_tail (h d) (t d)).
have law_tail d A : measurable A ->
    P d ((@sparse_sample_tail (n d) (h d) (p d)) @^-1` A) = pi d A.
  move=>mA.
  have mB : measurable ((@sparse_sample_tail (n d) (h d) (p d)) @^-1` A).
    rewrite -[X in measurable X]setTI; exact: measurable_sparse_sample_pick mA.
  rewrite (law d _ mB).
  rewrite /pi /sparse_countable_probability /sparse_countable_tail /= /sparse_sample_tail.
  apply: countable_sparse_sample_law=>//.
  exact: rshift_inj.
have dims : exists d0, forall d, (d0<=d)%N -> (0<n d)%N /\ (0<p d)%N.
  have [d0 hd] := sparse_sample_dimensions_positive a0 hp hn.
  exists d0=>d dd; have [p0 n0] := hd d dd; by split.
have targets : forall eps delta : R, 0<eps -> 0<delta ->
    exists d0, forall d, (d0<=d)%N ->
      (P d [set x | (delta<=sparse_sample_target_size L (m d) x)%R] <= eps%:E)%E.
  move=>eps delta ep dp; have [d0 hd] := target L (ltW L0) eps delta ep dp.
  exists d0=>d dd.
  have mB := @measurable_sparse_target_atleast (n d) (h d) (p d) L delta (m d).
  rewrite (law d _ mB); exact: hd.
have result := sparse_pd_limit_of_inputs c1 (ltW L0) dims law_tail covers targets.
move=>eps ep; have [d0 hd] := result eps ep; exists d0=>d dd.
have mA := @measurable_sparse_pd_fit (n d) (h d) (p d) (m d).
rewrite -(law d _ mA); exact: hd.
Qed.


Definition sparse_sample_head_matrix n h p (x : paper_main_sample n (h+p)) :=
  @sample_point_matrix n h (sparse_sample_head x).

Lemma measurable_sparse_sample_head_matrix n h p :
  measurable_fun [set: paper_main_sample n (h+p)] (@sparse_sample_head_matrix n h p).
Proof.
exact: measurableT_comp (@measurable_sample_point_matrix n h)
  (@measurable_sparse_sample_pick n (h+p) h (lshift p)).
Qed.

Lemma sparse_sample_head_matrix_row n h p (x : paper_main_sample n (h+p))
    (i : 'I_n) :
  row i (sparse_sample_head_matrix x) = (paper_main_point (sparse_sample_head x) i)^T.
Proof.
by apply/rowP=>j; rewrite /sparse_sample_head_matrix mxE sample_point_matrixE !mxE.
Qed.

Lemma sparse_sample_target_matrix n h p (m : 'rV[RR]_h)
    (x : paper_main_sample n (h+p)) (L : R) :
  sparse_sample_target_size L m x = shifted_interpolation_size p L
    (fun i => sparse_head_normalized_target p m (row i (sparse_sample_head_matrix x))).
Proof.
rewrite /sparse_sample_target_size; congr (shifted_interpolation_size _ _ _).
by apply/funext=>i; rewrite sparse_sample_head_matrix_row.
Qed.

Lemma sparse_finite_head_matrix_probability n h p N (w : nat -> R) mu
    (hw : mixture_weights (fun s : 'I_N => w s)) (A : set 'M[RR]_(n,h)) :
  measurable A ->
  mixture_probability N w mu n (h+p) ((@sparse_sample_head_matrix n h p) @^-1` A) =
    independent_row_matrix_law
      (fun=>mixture (fun s : 'I_N => point_law h (mu s)) hw) n A.
Proof.
move=>mA; rewrite -(@sparse_finite_matrix_probability N w mu hw n h A mA).
change (mixture_probability N w mu n (h+p)
  ((@sparse_sample_head n h p) @^-1` ((@sample_point_matrix n h) @^-1` A)) =
  mixture_probability N w mu n h ((@sample_point_matrix n h) @^-1` A)).
rewrite /sparse_sample_head; apply: finite_sparse_sample_law.
- exact: lshift_inj.
- by move=>s j.
- rewrite -[X in measurable X]setTI; exact: measurable_sample_point_matrix mA.
Qed.

Lemma sparse_countable_head_matrix_probability n h p (w : nat -> R) mu
    (hw : cmixture_weights w) (A : set 'M[RR]_(n,h)) :
  measurable A ->
  countable_mixture_probability w mu n (h+p)
    ((@sparse_sample_head_matrix n h p) @^-1` A) =
    independent_row_matrix_law (fun=>cmixture (fun s=>point_law h (mu s)) hw) n A.
Proof.
move=>mA; rewrite -(@sparse_countable_matrix_probability w mu hw n h A mA).
change (countable_mixture_probability w mu n (h+p)
  ((@sparse_sample_head n h p) @^-1` ((@sample_point_matrix n h) @^-1` A)) =
  countable_mixture_probability w mu n h ((@sample_point_matrix n h) @^-1` A)).
rewrite /sparse_sample_head; apply: countable_sparse_sample_law.
- exact: lshift_inj.
- by move=>s j.
- rewrite -[X in measurable X]setTI; exact: measurable_sample_point_matrix mA.
Qed.

(* The target concentration is uniform in the shift magnitude. The
   head and complement can share a mixture label: only their separate
   marginals are used in the preceding union-bound argument. *)
Theorem finite_sparse_shift_pd (kappa K alpha : R)
    (base : nat -> sparse_finite_parameters) (h p : nat -> nat)
    (t : nat -> sparse_finite_parameters) (m : forall d, 'rV[RR]_(h d)) :
  1<kappa -> 0<K -> 0<alpha -> alpha<universality_alpha_star kappa ->
  (forall q, sparse_finite_admissible K kappa q (base q)) ->
  family_sequence_limit (fun q => (sparse_finite_n (base q))%:R/q%:R^+2 : RR) alpha ->
  family_cofinal p ->
  (forall d, sparse_finite_admissible K kappa (h d+p d) (t d)) ->
  family_sequence_limit (fun d => (h d)%:R/(p d)%:R : RR) 0 ->
  family_sequence_limit (fun d => (sparse_finite_n (t d))%:R/(p d)%:R^+2 : RR) alpha ->
  paper_main_tends_to (fun d => sparse_finite_probability (h d+p d) (t d)
    (sample_translate (sparse_block_shift (p d) (m d)) @^-1`
      universality_pd_fit_event (sparse_finite_n (t d)) (h d+p d))) 1.
Proof.
move=>k1 K0 a0 below Ab hb hp At hh hn.
apply: (@finite_sparse_shift_pd_of_target kappa K alpha base h p t m
  k1 K0 a0 below Ab hb hp At hn).
move=>L L0 eps delta ep dp.
have hw d := sparse_finite_admissible_weights (At d).
have hnu d (i : 'I_(sparse_finite_components (t d))) j :
    (j<h d)%N -> mixture_component_law K (sparse_finite_laws (t d) i j).
  move=>jh; have [[_ [_ hc]] _] := At d.
  apply: hc (ltn_ord i) _; exact: leq_trans jh (leq_addr _ _).
have targets := @sparse_finite_iid_target_size_small K L alpha
  (fun d=>sparse_finite_n (t d)) h p
  (fun d=>[the finType of 'I_(sparse_finite_components (t d))])
  (fun d (i : 'I_(sparse_finite_components (t d)))=>sparse_finite_weights (t d) i)
  (fun d (i : 'I_(sparse_finite_components (t d)))=>sparse_finite_laws (t d) i)
  hw hnu m K0 L0 hp hh hn.
have [d0 hd] := targets eps delta ep dp; exists d0=>d dd.
pose B : set 'M[RR]_(sparse_finite_n (t d),h d) :=
  [set H | delta<=shifted_interpolation_size (p d) L
    (sparse_matrix_target (p d) (m d) H)].
have mB : measurable B.
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ler=>//.
  exact: measurable_sparse_matrix_size.
have eqset : [set x : paper_main_sample (sparse_finite_n (t d)) (h d+p d) |
    delta<=sparse_sample_target_size L (m d) x] =
    (@sparse_sample_head_matrix (sparse_finite_n (t d)) (h d) (p d)) @^-1` B.
  apply/seteqP; split=>x; by rewrite /preimage /B /= sparse_sample_target_matrix.
rewrite eqset /sparse_finite_probability
  (@sparse_finite_head_matrix_probability (sparse_finite_n (t d)) (h d) (p d)
    (sparse_finite_components (t d)) (sparse_finite_weights (t d))
    (sparse_finite_laws (t d)) (hw d) B mB).
exact: hd.
Qed.

Theorem countable_sparse_shift_pd (kappa K alpha : R)
    (base : nat -> sparse_countable_parameters) (h p : nat -> nat)
    (t : nat -> sparse_countable_parameters) (m : forall d, 'rV[RR]_(h d)) :
  1<kappa -> 0<K -> 0<alpha -> alpha<universality_alpha_star kappa ->
  (forall q, sparse_countable_admissible K kappa q (base q)) ->
  family_sequence_limit (fun q => (sparse_countable_n (base q))%:R/q%:R^+2 : RR) alpha ->
  family_cofinal p ->
  (forall d, sparse_countable_admissible K kappa (h d+p d) (t d)) ->
  family_sequence_limit (fun d => (h d)%:R/(p d)%:R : RR) 0 ->
  family_sequence_limit (fun d => (sparse_countable_n (t d))%:R/(p d)%:R^+2 : RR) alpha ->
  paper_main_tends_to (fun d => sparse_countable_probability (h d+p d) (t d)
    (sample_translate (sparse_block_shift (p d) (m d)) @^-1`
      universality_pd_fit_event (sparse_countable_n (t d)) (h d+p d))) 1.
Proof.
move=>k1 K0 a0 below Ab hb hp At hh hn.
apply: (@countable_sparse_shift_pd_of_target kappa K alpha base h p t m
  k1 K0 a0 below Ab hb hp At hn).
move=>L L0 eps delta ep dp.
have hw d := sparse_countable_admissible_weights (At d).
have hnu d i j :
    (j<h d)%N -> mixture_component_law K (sparse_countable_laws (t d) i j).
  move=>jh; have [[_ [_ hc]] _] := At d.
  apply: hc; exact: leq_trans jh (leq_addr _ _).
have targets := @sparse_countable_iid_target_size_small K L alpha
  (fun d=>sparse_countable_n (t d)) h p
  (fun d=>sparse_countable_weights (t d))
  (fun d=>sparse_countable_laws (t d)) hw hnu m K0 L0 hp hh hn.
have [d0 hd] := targets eps delta ep dp; exists d0=>d dd.
pose B : set 'M[RR]_(sparse_countable_n (t d),h d) :=
  [set H | delta<=shifted_interpolation_size (p d) L
    (sparse_matrix_target (p d) (m d) H)].
have mB : measurable B.
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ler=>//.
  exact: measurable_sparse_matrix_size.
have eqset : [set x : paper_main_sample (sparse_countable_n (t d)) (h d+p d) |
    delta<=sparse_sample_target_size L (m d) x] =
    (@sparse_sample_head_matrix (sparse_countable_n (t d)) (h d) (p d)) @^-1` B.
  apply/seteqP; split=>x; by rewrite /preimage /B /= sparse_sample_target_matrix.
rewrite eqset /sparse_countable_probability
  (@sparse_countable_head_matrix_probability (sparse_countable_n (t d)) (h d) (p d)
    (sparse_countable_weights (t d)) (sparse_countable_laws (t d)) (hw d) B mB).
exact: hd.
Qed.
