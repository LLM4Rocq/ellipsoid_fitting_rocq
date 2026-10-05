(* An exponentially rare exceptional event for each fixed ordered head,
   in the subcritical regime. d = n + 1 and W_i is the feature of row i.
   - paper_main_head_size_width: every head of m rows of the sample has
     head-section width at least a.
   - paper_main_head_list_positive: some P with the cone condition
     paper_main_head_condition kappa is orthogonal to the W_i, i in J, and
     every unit dual vector t vanishing on J with entries at most
     theta / sqrt d has such a P with positive support score
     paper_main_support_score.
   - paper_main_head_subcritical_fixed_event: for 0 <= alpha < 1/4,
     kappa >= 1 and L >= 0 there are theta, c > 0 such that, for large n,
     every N <= alpha d^2 and every list J of distinct rows below N have a
     measurable event E of probability at most exp(-c d sqrt d), outside
     which paper_main_head_list_positive holds as soon as every coordinate
     is below d^(1/4) in absolute value, every head of |J| rows has width
     at least (1/2 - (1/2 - sqrt alpha)/16) d, and the features satisfy
     the operator bound L sqrt d.
   The proof moves J to the first rows with the row permutation of
   paper_main_head_selection_perm_exists. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology ereal measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral measurable_realfun probability.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductContinuity
  SoftDefinitions PaperMainGeometryPsd GaussianProbabilityProductDefinitions PaperMainDefinitions
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadFeature PaperMainGeometryHeadWidth
  PaperMainHeadTailSupportSplit PaperMainHeadSelectionLaw PaperMainHeadSectionWidthLaw
  PaperMainHeadSectionApprox PaperMainDataSampleTail PaperMainHeadSoftTail
  PaperMainHeadCompactEvent PaperMainHeadCompactEventSelection
  PaperMainHeadSubcriticalEvent PaperMainHeadSubcriticalGood.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_head_size_width n N m kappa a (x : paper_main_sample N (S n)) :=
  forall (h : paper_main_sample m (S n)) (s : 'I_m -> 'I_N),
    injective s -> (forall k : 'I_m, paper_main_head_feature h k = paper_main_head_feature x (s k)) ->
    a <= fine (paper_main_head_section_width n m kappa h).

Definition paper_main_head_list_positive n N (J : list nat) kappa theta
    (x : paper_main_sample N (S n)) :=
  (exists P : 'M[R]_(S n), paper_main_head_condition kappa P /\
    forall i, List.In i J -> paper_main_pairing (paper_main_head_feature x i) P = 0%R) /\
  forall t : nat -> R, euclidean_norm t (List.seq 0 N) = 1 ->
    (forall i, List.In i J -> t i = 0) ->
    (forall i, Rabs(t i) <= theta/sqrt(INR (S n))) ->
    exists P : 'M[R]_(S n), paper_main_head_condition kappa P /\
      (forall i, List.In i J -> paper_main_pairing (paper_main_head_feature x i) P = 0%R) /\
      0 < paper_main_support_score (S n) N (paper_main_head_feature x) t P.

Theorem paper_main_head_subcritical_fixed_event alpha kappa L :
  0 <= alpha -> alpha < 1/4 -> 1 <= kappa -> 0 <= L ->
  exists theta c, 0 < theta /\ 0 < c /\
  exists D, forall n, Nat.le D n -> forall N (J : list nat),
    INR N <= alpha*(INR (S n))^2 ->
    List.NoDup J -> List.incl J (List.seq 0 N) ->
    exists E : set (paper_main_sample N (S n)), measurable E /\
      (paper_main_probability N (S n) E <= (exp(-c*INR (S n)*sqrt(INR (S n))))%:E)%E /\
      forall x, ~ E x ->
        ~ paper_main_data_coordinate_event N (S n) (sqrt(sqrt(INR (S n)))) x ->
        paper_main_head_size_width n N (List.length J) kappa
          ((1/2-(1/2-sqrt alpha)/16)*INR (S n)) x ->
        paper_main_head_section_operator_bound N (fun i => paper_main_head_feature x i)
          (L*sqrt(INR (S n))) ->
        paper_main_head_list_positive n N J kappa theta x.
Proof.
move=> Ha Hab Hk HL.
have [theta [c [Ht [Hc [D HD]]]]] := paper_main_head_subcritical_bad_probability alpha kappa L Ha Hab Hk HL.
exists theta,c; split; first exact Ht; split; first exact Hc.
exists D => n Hn N J HN HJu HJa.
have Hsize : (List.length J <= N)%coq_nat.
{ have HH := NoDup_incl_length HJu HJa; rewrite List.length_seq in HH; exact HH. }
have HsizeMC : (size J <= N)%N by apply/ssrnat.leP; exact Hsize.
have [q EN] : exists q, N = (size J+q)%N.
{ exists (N-size J)%N; by rewrite addnC subnK. }
subst N.
have HJuMC : uniq J by apply/paper_main_head_NoDup_uniq.
have HJaMC : all (fun i => i < size J+q)%N J by apply/paper_main_head_incl_all.
have [pi [Hhead Htail]] := paper_main_head_selection_perm_exists (size J) q J HJuMC (Logic.eq_refl _) HJaMC.
have Hq : INR q <= alpha*(INR (S n))^2.
{ have HleN : (q <= size J+q)%N by exact: leq_addl.
  have Hle := le_INR q (size J+q)%N (elimT ssrnat.leP HleN); lra. }
have [mE HE] := HD n Hn (size J) q pi Hq.
exists (paper_main_head_selection (size J) q (S n) pi @^-1`
  paper_main_head_subcritical_bad n (size J) q alpha kappa theta L).
split; first exact mE; split; first exact HE.
move=> x Hbad Hcoord Hwidth Hop.
pose h := (paper_main_head_selection (size J) q (S n) pi x).1.
pose s := fun k : 'I_(size J) => pi (lshift q k).
have Hs : injective s.
{ move=> i j Hij; apply/val_inj; exact: (congr1 val (perm_inj Hij)). }
have HW : forall k : 'I_(size J), paper_main_head_feature h k = paper_main_head_feature x (s k).
{ move=> k; exact: paper_main_head_selection_head_feature. }
have Hwidthh := Hwidth h s Hs HW.
split.
- have Hpos : (0 < fine (paper_main_head_section_width n (size J) kappa h))%R.
  { apply/RltP; change (0 < fine (paper_main_head_section_width n (size J) kappa h)).
    have Hd : 0 < INR (S n) by apply lt_0_INR; lia.
    have Hsa := sqrt_pos alpha.
    change ((1/2-(1/2-sqrt alpha)/16)*INR (S n) <=
      fine (paper_main_head_section_width n (size J) kappa h)) in Hwidthh.
    nra. }
  have [P HP] := paper_main_head_section_width_positive n (size J) kappa h Hpos.
  have [Hcond [_ HK]] := (paper_main_head_selection_head_section n (size J) q kappa J pi x P
    (Logic.eq_refl _) Hhead).1 HP.
  by exists P.
- exact: paper_main_head_subcritical_selected_good n (size J) q alpha kappa theta L J pi x
    Ha Hab Hk HL HJuMC (Logic.eq_refl _) HJaMC Hhead Htail Hwidthh Hop Hcoord Hbad.
Qed.
