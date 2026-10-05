(* The head-section width is large for every head of a typical sample.

   paper_main_head_width_coercive_probability_fixed: let N(d) <= C d^2 and
   let k0 >= 1 be such that the Gaussian condition width
   paper_main_gaussian_condition_width n k0 is eventually at least
   (1/2 - eps/2) d, where d = S n. There are measurable events A_d with
   probability tending to 0 such that, for every large d and every sample x
   outside A_d whose head Gram matrix is coercive with constant c d, every
   head h whose features are those of m <= K d ln d distinct points of x
   has head-section width at least (1/2 - eps) d for kappa = 2 k0^2.
   A_d is the union of four events of vanishing probability
   (paper_main_head_exception_union_limit): the exception of
   paper_main_head_width_regular_probability_fixed, the failure of the
   bound on the Gram matrix of the raw head and data features, a large
   data radius and a large data coherence. Outside A_d the selected points
   satisfy paper_main_head_regular: the diagonal bound comes from the
   coercivity (paper_main_head_coercive_diagonal) and the off-diagonal
   bound from the coherence.
   paper_main_head_width_coercive_probability_uniform chooses kappa from
   eps alone, before N, C, K and c. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainAsymptotics
  PaperMainGeometryPsd PaperMainGeometryHeadCoefficients PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadFeature PaperMainHeadWidthRegular PaperMainHeadWidthProbability
  PaperMainHeadSectionWidthLaw PaperMainHeadDataLog PaperMainDataCoherenceLimit
  PaperMainDataSampleTail PaperMainGaussianDataRadius PaperMainGaussianDataRadiusLimit
  PaperMainGaussianConditionWidth PaperMainGaussianConditionWidthBound.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma paper_main_head_coercive_diagonal N (G : 'M[R]_N) mu :
  paper_main_head_coercive G mu -> forall i : 'I_N, mu <= G i i.
Proof.
move=> HG i.
have H := HG (delta_mx i 0).
rewrite trmx_delta -mulmxA -!rowE -!colE !mxE eqxx /= mulr1 in H.
exact H.
Qed.

Lemma paper_main_head_exception_union_limit (N : nat -> nat)
    (A B : forall d, set (paper_main_sample (N d) d)) :
  (forall d, measurable (A d)) -> (forall d, measurable (B d)) ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d (A d)) 0 ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d (B d)) 0 ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d (A d `|` B d)) 0.
Proof.
move=> mA mB HA HB eps Heps.
have HepsR : (0 < eps)%Rcoq by exact/RltP.
have He : 0 < (eps/4)%Rcoq by apply/RltP; change (0 < eps/4)%Rcoq; lra.
have [DA HDA] := HA (eps/4)%Rcoq He.
have [DB HDB] := HB (eps/4)%Rcoq He.
exists (Nat.max DA DB) => d Hdd.
have HddN : Nat.le (Nat.max DA DB) d by exact: (elimT ssrnat.leP Hdd).
have HdA : (DA <= d)%N by apply/ssrnat.leP; lia.
have HdB : (DB <= d)%N by apply/ssrnat.leP; lia.
have HP := HDA d HdA; have HQ := HDB d HdB.
have HP0 : (0 <= paper_main_probability (N d) d (A d))%E by exact: measure_ge0.
have HQ0 : (0 <= paper_main_probability (N d) d (B d))%E by exact: measure_ge0.
have HU0 : (0 <= paper_main_probability (N d) d (A d `|` B d))%E by exact: measure_ge0.
rewrite sube0 (gee0_abs HP0) in HP.
rewrite sube0 (gee0_abs HQ0) in HQ.
rewrite sube0 (gee0_abs HU0).
have HU := measureU2 (gaussian_product_law (N d*d)%N) (mA d) (mB d).
apply: le_lt_trans HU _.
apply: le_lt_trans (leeD (ltW HP) (ltW HQ)) _.
rewrite -EFinD lte_fin; apply/RltP; rewrite -RplusE.
change (eps/4+eps/4 < eps)%Rcoq; lra.
Qed.

Theorem paper_main_head_width_coercive_probability_fixed (N : nat -> nat) C K c k0 eps :
  (0 <= C)%Rcoq -> (0 <= K)%Rcoq -> (0 < c)%Rcoq -> (0 < eps)%Rcoq ->
  (exists D, forall d, Nat.le D d -> (INR (N d) <= C*(INR d)^2)%Rcoq) ->
  (1 <= k0)%Rcoq ->
  (exists D0, forall n, Nat.le D0 n ->
    ((1/2-eps/2)*INR (S n) <= paper_main_gaussian_condition_width n k0)%Rcoq) ->
  exists A : forall d, set (paper_main_sample (N d) d),
    (forall d, measurable (A d)) /\
    paper_main_tends_to (fun d => paper_main_probability (N d) d (A d)) 0 /\
    exists D, forall n, Nat.le D n -> forall x, ~ A (S n) x ->
      paper_main_head_coercive
        (paper_main_head_gram (fun i : 'I_(N (S n)) => paper_main_head_feature x i)) (c*(S n)%:R) ->
      forall m (h : paper_main_sample m (S n)) (s : 'I_m -> 'I_(N (S n))),
        injective s -> (INR m <= K*INR (S n)*Rpower.ln(INR (S n)))%Rcoq ->
        (forall k : 'I_m, paper_main_head_feature h k = paper_main_head_feature x (s k)) ->
        ((1/2-eps)*INR (S n) <= fine (paper_main_head_section_width n m (2*k0^2)%Rcoq h))%Rcoq.
Proof.
move=> HC HK Hc Heps HN Hk0 Hbase.
have [L [HL [ER [mER [HER [DR HDR]]]]]] := paper_main_head_data_log_probability N C K HC HK HN.
have [AW [mAW [HAW [DW HDW]]]] :=
  paper_main_head_width_regular_probability_fixed N K c c 73%Rcoq L C k0 eps
    HK Hc Hc ltac:(lra) ltac:(lra) HC Heps HN Hk0 Hbase.
pose R d := paper_main_data_radius_event (N d) d (2*sqrt(INR d))%Rcoq.
have mR d : measurable (R d) by exact: paper_main_data_radius_event_measurable.
have HR : paper_main_tends_to (fun d => paper_main_probability (N d) d (R d)) 0.
{ exact: paper_main_data_radius_tends_to_zero N C HC HN. }
pose B d := if (2 <= d)%N then
  paper_main_data_coherence_event (N d) d (paper_main_coherence_threshold (INR d)) else set0.
have mB d : measurable (B d).
{ rewrite /B; case Hdd: (2 <= d)%N; last exact: measurable0.
  have HddN : Nat.le 2 d by exact: (elimT ssrnat.leP Hdd).
  have Hd : (1 < INR d)%Rcoq by change (INR 1 < INR d)%Rcoq; apply lt_INR; lia.
  exact: (proj1 (paper_main_data_coherence_log_tail (N d) d Hd)). }
have HB : paper_main_tends_to (fun d => paper_main_probability (N d) d (B d)) 0.
{ apply: (paper_main_tends_to_zero_squeeze _
    (fun d => paper_main_probability (N d) d
      (paper_main_data_coherence_event (N d) d (paper_main_coherence_threshold (INR d))))).
  - move=> d; exact: measure_ge0.
  - move=> d; rewrite /B; case: ifP => _; first exact: lexx.
    rewrite /paper_main_probability measure0; exact: measure_ge0.
  - exact: paper_main_data_coherence_log_tends_to_zero N C HC HN. }
pose A d := ((AW d `|` ER d) `|` R d) `|` B d.
have mAR d : measurable (AW d `|` ER d) by apply: measurableU; [exact: (mAW d)|exact: (mER d)].
have mARR d : measurable ((AW d `|` ER d) `|` R d) by apply: measurableU; [exact: (mAR d)|exact: (mR d)].
have mA d : measurable (A d) by apply: measurableU; [exact: (mARR d)|exact: (mB d)].
have HAR := paper_main_head_exception_union_limit N AW ER mAW mER HAW HER.
have HARR := paper_main_head_exception_union_limit N (fun d => AW d `|` ER d) R mAR mR HAR HR.
have HAlim := paper_main_head_exception_union_limit N (fun d => (AW d `|` ER d) `|` R d) B mARR mB HARR HB.
exists A; split; first exact mA; split; first exact HAlim.
have [DL HDL] := INR_unbounded (exp 1).
exists (Nat.max DW (Nat.max DR (Nat.max DL 2))) => n Hn x Hx HG m h s Hs Hm Hrow.
have HAw : ~ AW (S n) x by move=> HH; apply: Hx; left; left; left.
have HEr : ~ ER (S n) x by move=> HH; apply: Hx; left; left; right.
have HRx : ~ R (S n) x by move=> HH; apply: Hx; left; right.
have HBx : ~ B (S n) x by move=> HH; apply: Hx; right.
have Htwo : (2 <= S n)%N by apply/ssrnat.leP; lia.
rewrite /B Htwo in HBx.
have Hd : (1 < INR (S n))%Rcoq by change (INR 1 < INR (S n))%Rcoq; apply lt_INR; lia.
have Hlarge : (exp 1 < INR (S n))%Rcoq by have := le_INR DL (S n) ltac:(lia); lra.
have Hlog : (1 <= Rpower.ln(INR (S n)))%Rcoq.
{ rewrite -(ln_exp 1); apply Rlt_le,ln_increasing; first exact: exp_pos; exact Hlarge. }
have Hrad := paper_main_data_radius_good (N (S n)) (S n) x HRx.
have Hcoh := paper_main_data_coherence_log_good (N (S n)) (S n) x Hd Hlog Hrad HBx.
have Hraw := HDR (S n) ltac:(lia) x HEr m s Hm Hs.
apply: (HDW n ltac:(lia) x HAw m h s _ Hrow).
rewrite /paper_main_head_regular; split; first exact Hs.
split.
- apply/RleP; rewrite -!RmultE -!INRE; exact Hm.
split; first exact HG.
split.
- move=> k.
  have HH := paper_main_head_coercive_diagonal _ _ _ HG (s k).
  by rewrite /paper_main_head_gram mxE in HH.
split.
- move=> k l Hlk.
  have Hne : (s k : nat) <> (s l : nat).
  { move=> Heq; have Hkl : k = l by apply Hs; apply/val_inj; exact Heq.
    move: Hlk; by rewrite Hkl eqxx. }
  have HH := Hcoh (s k) (s l) (elimT ssrnat.ltP (ltn_ord (s k)))
    (elimT ssrnat.ltP (ltn_ord (s l))) Hne.
  apply/RleP; rewrite -RabsE -RmultE; exact HH.
- move: Hraw.
  by rewrite !RmultE RpowE INRE.
Qed.

(* Kappa is chosen before the head-size budget and all data constants. *)
Theorem paper_main_head_width_coercive_probability_uniform eps :
  (0 < eps)%Rcoq -> exists kappa, (1 <= kappa)%Rcoq /\
  forall (N : nat -> nat) C K c,
    (0 <= C)%Rcoq -> (0 <= K)%Rcoq -> (0 < c)%Rcoq ->
    (exists D, forall d, Nat.le D d -> (INR (N d) <= C*(INR d)^2)%Rcoq) ->
    exists A : forall d, set (paper_main_sample (N d) d),
    (forall d, measurable (A d)) /\
    paper_main_tends_to (fun d => paper_main_probability (N d) d (A d)) 0 /\
    exists D, forall n, Nat.le D n -> forall x, ~ A (S n) x ->
      paper_main_head_coercive
        (paper_main_head_gram (fun i : 'I_(N (S n)) => paper_main_head_feature x i)) (c*(S n)%:R) ->
      forall m (h : paper_main_sample m (S n)) (s : 'I_m -> 'I_(N (S n))),
        injective s -> (INR m <= K*INR (S n)*Rpower.ln(INR (S n)))%Rcoq ->
        (forall k : 'I_m, paper_main_head_feature h k = paper_main_head_feature x (s k)) ->
        ((1/2-eps)*INR (S n) <= fine (paper_main_head_section_width n m kappa h))%Rcoq.
Proof.
move=> Heps.
have [k0 [Hk0 Hbase]] := paper_main_gaussian_condition_width_large (eps/2)%Rcoq ltac:(lra).
exists (2*k0^2)%Rcoq; split; first nra.
move=> N C K c HC HK Hc HN.
exact: paper_main_head_width_coercive_probability_fixed N C K c k0 eps
  HC HK Hc Heps HN Hk0 Hbase.
Qed.
