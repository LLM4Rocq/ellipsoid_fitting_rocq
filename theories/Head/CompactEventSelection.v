(* The compact value of a split sample and the tail duals of the full
   sample.

   Fix a full sample x of N = k + q rows of R^(S n), with features
   W i = paper_main_head_feature x i, an injective head J (uniq J,
   size J = k, rows below N) and its ordered complement
   C = paper_main_head_complement N J (the other rows, increasing). Let pi be
   a row permutation sending the first k positions to J in order and the last
   q positions to C in order (paper_main_head_selection_perm_exists), so the
   head and tail blocks of the permuted sample have the features
   W (nth J t) and W (nth C u).
   - Zero extension and restriction. For y on the tail coordinates u < q,
     paper_main_head_extension C y is y (index i C) at i in C and 0 elsewhere,
     in particular 0 on J. For a full t, its restriction is t (nth C u). For
     t vanishing on J, the restriction keeps the Euclidean norm and the
     combination:
       sum_(i < N) t_i W_i = sum_(u < q) t (nth C u) W (nth C u),
     which is the tail combination of the split value. So a unit t vanishing
     on J with |t_i| <= theta / sqrt (S n), a tail dual of
     paper_main_support_all, restricts to a vector of the capped unit dual
     set paper_main_head_capped_dual q (S n) theta
     (paper_main_head_restriction_capped).
   - Head constraints. The section of the head block is
     {S | condition, |S|_F = 1, <W_j, S> = 0 for every j in J}
     (paper_main_head_selection_head_section).
   - paper_main_head_compact_tail_duals: if c <= the compact value
     paper_main_head_compact_value at the blocks of x, with c > 0, then
     every such tail dual t has, for each eps > 0, a matrix S of this section
     with paper_main_support_score (S n) N W t S > c - eps; in particular a
     positive score (paper_main_head_compact_tail_duals_pos). This is the
     hypothesis of paper_main_support_all on capped tails, in section form.
   - paper_main_head_compact_operator_from_full: a full-sample operator
     bound |sum_i c_i W_i|_F <= A |c|, also a hypothesis of
     paper_main_support_all, gives the operator bound of the tail block for
     every fixed head.
   The head J is fixed, not chosen from the data. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  GaussianProbabilityDefinitions GaussianProbabilityProductDefinitions
  Gaussian.Law.ProductBasics PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadFrobenius Geometry.HeadFeature
  Geometry.HeadCorrection Geometry.HeadWidth Spectral.Duality
  Gordon.ProcessCovariance Gordon.Bilinear Gaussian.Sample.Deletion Head.Law
  Data.SampleTail Head.SelectionLaw Head.TailSupportSplit
  Head.SectionMeasurable Head.SectionMinimax Head.SectionApprox
  Head.CompactEvent.
From EllipsoidFitting Require Import Analysis.RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Lists: Stdlib and ssreflect forms. *)

Lemma paper_main_head_In_mem (i : nat) (J : seq nat) : List.In i J <-> i \in J.
Proof.
elim: J => [|j J IH] //=; rewrite inE; split.
- by case => [->|/IH ->]; rewrite ?eqxx ?orbT.
- by case/orP => [/eqP ->|/IH]; [left | right].
Qed.

Lemma paper_main_head_NoDup_uniq (J : seq nat) : List.NoDup J <-> uniq J.
Proof.
elim: J => [|j J IH] /=; first by split => // _; exact: List.NoDup_nil.
split.
- move=> H; inversion H as [|j' J' Hj HJ]; subst.
  apply/andP; split; last by apply/IH.
  by apply/negP => /paper_main_head_In_mem.
- move=> /andP [Hj HJ]; constructor; last by apply/IH.
  by move=> /paper_main_head_In_mem H; rewrite H in Hj.
Qed.

Lemma paper_main_head_incl_all (N : nat) (J : seq nat) :
  List.incl J (List.seq 0 N) <-> all (fun i => i < N)%N J.
Proof.
split.
- move=> H; apply/allP => i /paper_main_head_In_mem Hi.
  have /List.in_seq [_ Hlt] := H i Hi; apply/ssrnat.ltP; lia.
- move=> /allP H i /paper_main_head_In_mem Hi.
  apply/List.in_seq; split; first lia.
  by have /ssrnat.ltP := H i Hi; lia.
Qed.

(* The ordered complement. *)

Lemma paper_main_head_complement_mem N (J : seq nat) (i : nat) :
  (i \in paper_main_head_complement N J) = (i < N)%N && (i \notin J).
Proof. by rewrite mem_filter mem_iota add0n leq0n andbC. Qed.

Lemma paper_main_head_complement_uniq N (J : seq nat) :
  uniq (paper_main_head_complement N J).
Proof. exact: (filter_uniq _ (iota_uniq 0 N)). Qed.

Lemma paper_main_head_complement_size k q (J : seq nat) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  size (paper_main_head_complement (k + q) J) = q.
Proof.
move=> HJu HJs HJa.
have HJsub : {subset J <= iota 0 (k + q)}.
  by move=> i Hi; rewrite mem_iota /= add0n; exact: (allP HJa).
have HL : perm_eq (J ++ paper_main_head_complement (k + q) J) (iota 0 (k + q)).
  rewrite /paper_main_head_complement.
  apply: (@perm_trans _ ([seq i <- iota 0 (k + q) | i \in J] ++
      [seq i <- iota 0 (k + q) | i \notin J])).
    rewrite perm_cat2r; apply: uniq_perm => //.
    - by apply: filter_uniq; exact: iota_uniq.
    - move=> i; rewrite mem_filter /=; apply/idP/andP => [Hi | [] //].
      by split=> //; exact: HJsub.
  by apply/permPl; exact: (perm_filterC (mem J) (iota 0 (k + q))).
have := perm_size HL; rewrite size_cat size_iota HJs => /eqP.
by rewrite eqn_add2l => /eqP.
Qed.

Lemma paper_main_head_complement_sum {M : zmodType} N (J : seq nat) (F : nat -> M) :
  (forall i, (i < N)%N -> i \in J -> F i = 0) ->
  \sum_(i < N) F i =
    \sum_(0 <= u < size (paper_main_head_complement N J))
      F (nth 0%N (paper_main_head_complement N J) u).
Proof.
move=> H0.
rewrite -(big_mkord xpredT F) {1}/index_iota subn0 (bigID (fun i => i \in J)) /=.
rewrite big1_seq ?add0r; last first.
  by rewrite -big_filter (big_nth 0%N).
by move=> i /andP [HiJ Hi]; apply: H0 => //; move: Hi; rewrite mem_iota add0n.
Qed.

(* Zero extension and restriction. *)

Definition paper_main_head_extension (C : seq nat) (y : nat -> R) : nat -> R :=
  fun i => if i \in C then y (index i C) else 0.

Lemma paper_main_head_extension_nth (C : seq nat) (y : nat -> R) (u : nat) :
  uniq C -> (u < size C)%N -> paper_main_head_extension C y (nth 0%N C u) = y u.
Proof.
move=> HC Hu; rewrite /paper_main_head_extension mem_nth //.
by rewrite index_uniq.
Qed.

Lemma paper_main_head_extension_out (C : seq nat) (y : nat -> R) (i : nat) :
  i \notin C -> paper_main_head_extension C y i = 0.
Proof. by rewrite /paper_main_head_extension => /negbTE ->. Qed.

Lemma paper_main_head_extension_head N (J : seq nat) (y : nat -> R) (i : nat) :
  List.In i J -> paper_main_head_extension (paper_main_head_complement N J) y i = 0.
Proof.
move=> /paper_main_head_In_mem Hi; apply: paper_main_head_extension_out.
by rewrite paper_main_head_complement_mem Hi andbF.
Qed.

(* Combinations, norms and caps under restriction. *)

Lemma paper_main_head_restriction_sum {M : zmodType} k q (J : seq nat) (F : nat -> M) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  (forall i, (i < k + q)%N -> i \in J -> F i = 0) ->
  \sum_(i < k + q) F i =
    \sum_(u < q) F (nth 0%N (paper_main_head_complement (k + q) J) u).
Proof.
move=> HJu HJs HJa H0.
rewrite (paper_main_head_complement_sum (k + q) J F H0).
by rewrite (paper_main_head_complement_size k q J HJu HJs HJa) big_mkord.
Qed.

Lemma paper_main_head_restriction_combination {d : nat} k q (J : seq nat)
    (W : nat -> 'M[R]_d) (t : nat -> R) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  (forall i, List.In i J -> t i = 0) ->
  paper_main_support_combination d (k + q) W t =
  paper_main_head_section_combination q
    (fun u => t (nth 0%N (paper_main_head_complement (k + q) J) u))
    (fun u => W (nth 0%N (paper_main_head_complement (k + q) J) u)).
Proof.
move=> HJu HJs HJa Ht.
rewrite /paper_main_support_combination /paper_main_head_section_combination.
apply: (paper_main_head_restriction_sum k q J (fun i => t i *: W i) HJu HJs HJa).
by move=> i _ /paper_main_head_In_mem Hi; rewrite (Ht i Hi) scale0r.
Qed.

Lemma paper_main_head_restriction_norm k q (J : seq nat) (t : nat -> R) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  (forall i, List.In i J -> t i = 0) ->
  euclidean_norm t (List.seq 0 (k + q)) =
  euclidean_norm (fun u => t (nth 0%N (paper_main_head_complement (k + q) J) u))
    (List.seq 0 q).
Proof.
move=> HJu HJs HJa Ht.
rewrite /euclidean_norm /squared_norm !finite_sum_seqE; congr sqrt.
apply: (paper_main_head_restriction_sum k q J (fun i => pow (t i) 2%N) HJu HJs HJa).
by move=> i _ /paper_main_head_In_mem Hi; rewrite (Ht i Hi) RpowE expr0n.
Qed.

Lemma paper_main_head_restriction_capped k q n (theta : R) (J : seq nat) (t : nat -> R) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  euclidean_norm t (List.seq 0 (k + q)) = 1 ->
  (forall i, List.In i J -> t i = 0) ->
  (forall i, Rle (Rabs (t i)) (Rdiv theta (sqrt (INR (S n))))) ->
  paper_main_head_capped_dual q (S n) theta
    (fun u => t (nth 0%N (paper_main_head_complement (k + q) J) u)).
Proof.
move=> HJu HJs HJa H1 Ht Hcap; split; last by move=> u _; exact: Hcap.
rewrite -paper_main_gordon_euclidean_squared.
by rewrite -(paper_main_head_restriction_norm k q J t HJu HJs HJa Ht) H1 RpowE expr1n.
Qed.

(* Restriction after zero extension, and the combination of a zero extension. *)

Lemma paper_main_head_extension_restriction k q (J : seq nat) (y : nat -> R) (u : nat) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J -> (u < q)%N ->
  paper_main_head_extension (paper_main_head_complement (k + q) J) y
    (nth 0%N (paper_main_head_complement (k + q) J) u) = y u.
Proof.
move=> HJu HJs HJa Hu; apply: paper_main_head_extension_nth.
  exact: paper_main_head_complement_uniq.
by rewrite (paper_main_head_complement_size k q J HJu HJs HJa).
Qed.

Theorem paper_main_head_extension_combination {d : nat} k q (J : seq nat)
    (W : nat -> 'M[R]_d) (y : nat -> R) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  paper_main_support_combination d (k + q) W
    (paper_main_head_extension (paper_main_head_complement (k + q) J) y) =
  paper_main_head_section_combination q y
    (fun u => W (nth 0%N (paper_main_head_complement (k + q) J) u)).
Proof.
move=> HJu HJs HJa.
have Ht0 : forall i, List.In i J ->
    paper_main_head_extension (paper_main_head_complement (k + q) J) y i = 0.
  by move=> i Hi; exact: paper_main_head_extension_head.
rewrite (paper_main_head_restriction_combination k q J W _ HJu HJs HJa Ht0).
apply: eq_bigr => u _.
by rewrite (paper_main_head_extension_restriction k q J y u HJu HJs HJa (ltn_ord u)).
Qed.

(* The blocks of a row permutation with head J and tail C. *)

Lemma paper_main_head_selection_tail_combination n k q (J : seq nat) (pi : 'S_(k + q))
    (x : paper_main_sample (k + q) (S n)) (y : nat -> R) :
  (forall u : 'I_q,
    nat_of_ord (pi (rshift k u)) = nth 0%N (paper_main_head_complement (k + q) J) u) ->
  paper_main_head_section_combination q y
    (fun i => paper_main_head_feature (paper_main_head_selection k q (S n) pi x).2 i) =
  paper_main_head_section_combination q y
    (fun u => paper_main_head_feature x (nth 0%N (paper_main_head_complement (k + q) J) u)).
Proof.
move=> Hpi; apply: eq_bigr => u _.
by rewrite (paper_main_head_selection_tail_feature k q (S n) pi x u) Hpi.
Qed.

Lemma paper_main_head_selection_head_section n k q (kappa : R) (J : seq nat)
    (pi : 'S_(k + q)) (x : paper_main_sample (k + q) (S n)) (P : 'M[R]_(S n)) :
  size J = k ->
  (forall t : 'I_k, nat_of_ord (pi (lshift q t)) = nth 0%N J t) ->
  paper_main_head_section kappa
    (fun i : 'I_k => paper_main_head_feature (paper_main_head_selection k q (S n) pi x).1 i) P <->
  paper_main_head_condition kappa P /\ paper_main_frobenius P = 1 /\
    (forall j, List.In j J -> paper_main_pairing (paper_main_head_feature x j) P = 0).
Proof.
move=> HJs Hpi.
have HW : forall i : 'I_k,
    paper_main_head_feature (paper_main_head_selection k q (S n) pi x).1 i =
    paper_main_head_feature x (nth 0%N J i).
  by move=> i; rewrite (paper_main_head_selection_head_feature k q (S n) pi x i) Hpi.
split.
- move=> [Hc [H1 H0]]; split => //; split => // j /paper_main_head_In_mem Hj.
  have Hi : (index j J < k)%N by rewrite -HJs index_mem.
  by have := H0 (Ordinal Hi); rewrite HW /= nth_index.
- move=> [Hc [H1 H0]]; split => //; split => // i.
  rewrite HW; apply: H0; apply/paper_main_head_In_mem.
  by apply: mem_nth; rewrite HJs.
Qed.

(* Main consequence: section points with a large score for the tail duals. *)

Theorem paper_main_head_compact_tail_duals n k q (kappa theta c eps : R) (J : seq nat)
    (pi : 'S_(k + q)) (x : paper_main_sample (k + q) (S n)) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  (forall t : 'I_k, nat_of_ord (pi (lshift q t)) = nth 0%N J t) ->
  (forall u : 'I_q,
    nat_of_ord (pi (rshift k u)) = nth 0%N (paper_main_head_complement (k + q) J) u) ->
  0 < c -> 0 < eps ->
  c <= paper_main_head_compact_value n k q kappa theta
    (paper_main_head_selection k q (S n) pi x).1 (paper_main_head_selection k q (S n) pi x).2 ->
  forall t : nat -> R,
    euclidean_norm t (List.seq 0 (k + q)) = 1 ->
    (forall i, List.In i J -> t i = 0) ->
    (forall i, Rle (Rabs (t i)) (Rdiv theta (sqrt (INR (S n))))) ->
    exists P : 'M[R]_(S n),
      paper_main_head_condition kappa P /\ paper_main_frobenius P = 1 /\
      (forall i, List.In i J -> paper_main_pairing (paper_main_head_feature x i) P = 0) /\
      c - eps < paper_main_support_score (S n) (k + q) (fun i => paper_main_head_feature x i) t P.
Proof.
move=> HJu HJs HJa Hh Ht Hc He Hv t H1 Ht0 Hcap.
set C := paper_main_head_complement (k + q) J.
set y := fun u => t (nth 0%N C u).
set W := fun i : 'I_k => paper_main_head_feature (paper_main_head_selection k q (S n) pi x).1 i.
set V := fun i => paper_main_head_feature (paper_main_head_selection k q (S n) pi x).2 i.
have Hy : paper_main_head_capped_dual q (S n) theta y.
  exact: (paper_main_head_restriction_capped k q n theta J t HJu HJs HJa H1 Ht0 Hcap).
have Hcomb : paper_main_head_section_combination q y V =
    paper_main_support_combination (S n) (k + q) (fun i => paper_main_head_feature x i) t.
  rewrite /V (paper_main_head_selection_tail_combination n k q J pi x y Ht).
  by rewrite (paper_main_head_restriction_combination k q J _ t HJu HJs HJa Ht0).
(* The compact value is at most the support at y. *)
set E := [set paper_main_head_support (paper_main_head_section_combination q y' V)
  (paper_main_head_section kappa W) | y' in paper_main_head_capped_dual q (S n) theta].
have Hlb : has_lbound E.
  exists (- paper_main_head_section_tail_norm q V) => _ [y' Hy' <-].
  have := paper_main_head_section_value_bound kappa q W V y' (fun i Hi =>
    paper_main_head_section_unit_coord q y' i Hi (paper_main_head_capped_dual_unit _ _ _ _ Hy')).
  by rewrite ler_norml => /andP [].
have Hsup : c <= paper_main_head_support (paper_main_head_section_combination q y V)
    (paper_main_head_section kappa W).
  apply: le_trans Hv _.
  rewrite /paper_main_head_compact_value -/W -/V.
  by apply: (ge_inf Hlb); exists y.
(* A section point nearly attains the support. *)
have [P [HS HSc]] : exists P, paper_main_head_section kappa W P /\
    c - eps < paper_main_pairing (paper_main_head_section_combination q y V) P.
  apply/not_existsP => Hno.
  have HA : exists P, paper_main_head_section kappa W P.
    apply/not_existsP => Hempty.
    have HE : ~ (exists P, paper_main_head_section kappa W P).
      by move=> [P0 HP0]; apply: (Hempty P0).
    move: Hsup; rewrite (paper_main_head_section_support_empty kappa W _ HE) => Hc0.
    by have := lt_le_trans Hc Hc0; rewrite ltxx.
  have Hle : paper_main_head_support (paper_main_head_section_combination q y V)
      (paper_main_head_section kappa W) <= c - eps.
    apply: ge_sup; first by case: HA => P HS; eexists; exists P.
    move=> _ [P HS <-]; rewrite leNgt; apply/negP => HSc.
    by apply: (Hno P); split.
  have Hlt : c - eps < c by rewrite ltrBlDr ltrDl.
  by have := le_lt_trans (le_trans Hsup Hle) Hlt; rewrite ltxx.
exists P.
have [Hcond [HS1 HS0]] := (paper_main_head_selection_head_section n k q kappa J pi x P HJs Hh).1 HS.
split => //; split => //; split => //.
by rewrite paper_main_support_score_pairing -Hcomb.
Qed.

Corollary paper_main_head_compact_tail_duals_pos n k q (kappa theta c : R) (J : seq nat)
    (pi : 'S_(k + q)) (x : paper_main_sample (k + q) (S n)) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  (forall t : 'I_k, nat_of_ord (pi (lshift q t)) = nth 0%N J t) ->
  (forall u : 'I_q,
    nat_of_ord (pi (rshift k u)) = nth 0%N (paper_main_head_complement (k + q) J) u) ->
  0 < c ->
  c <= paper_main_head_compact_value n k q kappa theta
    (paper_main_head_selection k q (S n) pi x).1 (paper_main_head_selection k q (S n) pi x).2 ->
  forall t : nat -> R,
    euclidean_norm t (List.seq 0 (k + q)) = 1 ->
    (forall i, List.In i J -> t i = 0) ->
    (forall i, Rle (Rabs (t i)) (Rdiv theta (sqrt (INR (S n))))) ->
    exists P : 'M[R]_(S n),
      paper_main_head_condition kappa P /\ paper_main_frobenius P = 1 /\
      (forall i, List.In i J -> paper_main_pairing (paper_main_head_feature x i) P = 0) /\
      Rlt 0 (paper_main_support_score (S n) (k + q) (fun i => paper_main_head_feature x i) t P).
Proof.
move=> HJu HJs HJa Hh Ht Hc Hv t H1 Ht0 Hcap.
have Hc2 : 0 < c / 2 by rewrite divr_gt0.
have [P [Hcond [HS1 [HS0 HSc]]]] := paper_main_head_compact_tail_duals n k q kappa theta c
  (c / 2) J pi x HJu HJs HJa Hh Ht Hc Hc2 Hv t H1 Ht0 Hcap.
exists P; split => //; split => //; split => //.
by apply/RltP; apply: lt_trans HSc; rewrite {1}(splitr c) addrK.
Qed.

(* The full-sample operator bound gives the operator bound of the tail block. *)

Theorem paper_main_head_compact_operator_from_full n k q (A : R) (J : seq nat)
    (pi : 'S_(k + q)) (x : paper_main_sample (k + q) (S n)) :
  uniq J -> size J = k -> all (fun i => i < k + q)%N J ->
  (forall u : 'I_q,
    nat_of_ord (pi (rshift k u)) = nth 0%N (paper_main_head_complement (k + q) J) u) ->
  0 <= A ->
  (forall c : nat -> R,
    paper_main_frobenius (paper_main_support_combination (S n) (k + q)
      (fun i => paper_main_head_feature x i) c) <= A * euclidean_norm c (List.seq 0 (k + q))) ->
  paper_main_head_section_operator_bound q
    (fun i => paper_main_head_feature (paper_main_head_selection k q (S n) pi x).2 i) A.
Proof.
move=> HJu HJs HJa Ht HA Hfull; split => // y.
set C := paper_main_head_complement (k + q) J.
set t := paper_main_head_extension C y.
have Ht0 : forall i, List.In i J -> t i = 0.
  by move=> i Hi; exact: paper_main_head_extension_head.
rewrite (paper_main_head_selection_tail_combination n k q J pi x y Ht).
rewrite -(paper_main_head_extension_combination k q J _ y HJu HJs HJa).
apply: le_trans (Hfull t) _.
rewrite (paper_main_head_restriction_norm k q J t HJu HJs HJa Ht0).
have -> : euclidean_norm (fun u => t (nth 0%N C u)) (List.seq 0 q) =
    euclidean_norm y (List.seq 0 q).
  rewrite /euclidean_norm /squared_norm; congr sqrt; apply: finite_sum_ext => u Hu.
  have Hu' : (u < q)%N by apply/paper_main_head_section_seq_lt.
  by rewrite /t (paper_main_head_extension_restriction k q J y u HJu HJs HJa Hu').
exact: lexx.
Qed.
