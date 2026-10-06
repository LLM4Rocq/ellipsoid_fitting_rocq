(* Non-backtracking walks for the lower spectral edge of the square-free
   block: the walk expansion of the NB matrices T L of
   SquareFree.EdgeLower. For X : 'I_N -> C -> R over a finite
   column type C, a walk of length L+1 from i to j has rows i, t, j
   (t of length L) and columns cs (length L+1); it is NB when consecutive
   rows differ (pmsw_steps) and consecutive columns differ (pmnb_cnb).
   - pmnb_Tc_walks, pmnb_T_walks: T (L+1) i j = kap^(L+1) times the sum
     over NB walks from i to j of prod_s X r_s c_s X r_(s+1) c_s
     (pmnb_prod).
   - pmnb_T_sym: T L is symmetric, by reversal of walks.
   - pmnb_power_LW, pmnb_trace_LW: (T (m+1))^(q+1) i j = kap^((q+1)(m+1))
     times the sum over walks of q+1 segments of m+1 steps, whose columns
     are NB inside each segment (pmnb_segs); the junction rows are summed.
   - Square-free instance: columns are ordered pairs (a, b) and
     X_(u,(a,b)) = [a < b] x_ua x_ub (pmnb_X), so a column is an unordered
     pair. pmnb_trace_moment: E tr T(m+1)^(q+1) = kap^((q+1)(m+1)) times
     the sum over closed walks of q+1 NB segments with increasing pairs of
     the walk-word moments pmsw_moment (N d) (pmsw_word i rs i cs).
   These are exact identities. *)
From Stdlib Require Import Reals List Lia FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  GaussianProbabilityProductDefinitions PaperMainDefinitions
  Data.FeatureMomentsCoordinates Data.FeatureMoments Feature.GramBlocks
  DiagonalBlock.Moment SquareFree.WalkMoments SquareFree.WalkExpansion
  SquareFree.EdgeLower.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Sums over lists. *)
Lemma pmnb_seqs_cat (T : Type) (s : seq T) p q (F : seq T -> R) :
  \sum_(w <- pmsw_seqs s (p + q)) F w =
  \sum_(y <- pmsw_seqs s p) \sum_(z <- pmsw_seqs s q) F (y ++ z).
Proof.
elim: p F => [|p IH] F; first by rewrite add0n pmsw_seqs_sum0.
rewrite addSn !pmsw_seqs_sumS; apply: eq_bigr => x _.
exact: IH (fun z => F (x :: z)).
Qed.

(* 2. Walks. The product is defined over any ring, so that its operations
   are the ring operations. *)
Definition pmnb_cnb (C : eqType) (cs : seq C) : bool :=
  if cs is c :: cs' then path (fun a b : C => a != b) c cs' else true.

Fixpoint pmnb_prod {F : pzRingType} {N : nat} {C : Type} (X : 'I_N -> C -> F)
    (i : 'I_N) (t : seq 'I_N) (j : 'I_N) (cs : seq C) {struct t} : F :=
  match t, cs with
  | k :: t', c :: cs' => X i c * X k c * pmnb_prod X k t' j cs'
  | [::], c :: _ => X i c * X j c
  | _, [::] => 1
  end.

Section Walks.
Variables (N : nat) (C : finType) (X : 'I_N -> C -> R) (kap : R).

Lemma pmnb_Tc_walks L c (i j : 'I_N) :
  pmlo_Tc N C X kap L.+1 c i j = kap ^+ L.+1 *
  \sum_(t <- pmsw_seqs (index_enum 'I_N) L) \sum_(cs <- pmsw_seqs (index_enum C) L)
    (pmsw_steps N i t j && pmnb_cnb C (c :: cs))%:R * pmnb_prod X i t j (c :: cs).
Proof.
elim: L c i j => [|L IH] c i j.
  rewrite pmlo_TcS pmlo_T0 pmlo_Tc0 subr0 mulmx1 !pmsw_seqs_sum0 /= mxE expr1 andbT.
  by case: eqP => _; rewrite ?mul0r ?mulr0 ?mul1r.
rewrite pmlo_TcS mxE.
rewrite pmsw_seqs_sumS mulr_sumr; apply: eq_bigr => u _.
rewrite [fun_of_matrix (_ - _) _ _]mxE mxE pmlo_TS summxE.
rewrite [fun_of_matrix (- _) _ _]mxE.
rewrite (eq_bigr _ (fun c' _ => IH c' u j)) IH.
set S := fun c' : C => \sum_(t <- pmsw_seqs (index_enum 'I_N) L)
  \sum_(cs <- pmsw_seqs (index_enum C) L)
    (pmsw_steps N u t j && pmnb_cnb C (c' :: cs))%:R * pmnb_prod X u t j (c' :: cs).
have E : \sum_(t <- pmsw_seqs (index_enum 'I_N) L)
    \sum_(cs <- pmsw_seqs (index_enum C) L.+1)
      (pmsw_steps N i (u :: t) j && pmnb_cnb C (c :: cs))%:R *
      pmnb_prod X i (u :: t) j (c :: cs) =
    (i != u)%:R * (X i c * X u c) * \sum_c' (c != c')%:R * S c'.
  rewrite (eq_bigr (fun t => \sum_c' \sum_(cs <- pmsw_seqs (index_enum C) L)
      (pmsw_steps N i (u :: t) j && pmnb_cnb C (c :: c' :: cs))%:R *
      pmnb_prod X i (u :: t) j (c :: c' :: cs))); first by move=> t _; rewrite pmsw_seqs_sumS.
  rewrite exchange_big mulr_sumr; apply: eq_bigr => c' _.
  rewrite /S !mulr_sumr; apply: eq_bigr => t _; rewrite !mulr_sumr; apply: eq_bigr => cs _.
  rewrite /= -!andbA -!mulnb !natrM; ring.
rewrite E /S.
case: (eqVneq i u) => [Hiu|Hiu]; first by rewrite /= !mul0r mulr0.
rewrite /= mul1r.
rewrite -mulr_sumr -mulrBr (bigD1 c) //= [_ + \sum_(i0 | i0 != c) _]addrC addrK.
rewrite [X in _ = _ * (_ * X)](bigD1 c) //= eqxx mul0r add0r.
set G := fun i0 : C => \sum_(t <- pmsw_seqs (index_enum 'I_N) L)
  \sum_(cs <- pmsw_seqs (index_enum C) L)
    (pmsw_steps N u t j && path (fun a b : C => a != b) i0 cs)%:R * pmnb_prod X u t j (i0 :: cs).
rewrite [X in _ = _ * (_ * X)](eq_bigr (fun i0 => G i0));
  first by move=> i0 Hi0; rewrite eq_sym Hi0 mul1r.
set Sg := \sum_(i0 | i0 != c) G i0.
rewrite !exprS; set Q := kap ^+ L; set Y := X i c * X u c.
ring.
Qed.

Lemma pmnb_T_walks L (i j : 'I_N) :
  pmlo_T N C X kap L.+1 i j = kap ^+ L.+1 *
  \sum_(t <- pmsw_seqs (index_enum 'I_N) L) \sum_(cs <- pmsw_seqs (index_enum C) L.+1)
    (pmsw_steps N i t j && pmnb_cnb C cs)%:R * pmnb_prod X i t j cs.
Proof.
rewrite pmlo_TS summxE (eq_bigr _ (fun c _ => pmnb_Tc_walks L c i j)) -mulr_sumr.
congr (_ * _); rewrite exchange_big /=; apply: eq_bigr => t _.
by rewrite pmsw_seqs_sumS.
Qed.

(* Reversal of walks. *)
Lemma pmnb_steps_path (i : 'I_N) t (j : 'I_N) :
  pmsw_steps N i t j = path (fun a b : 'I_N => a != b) i (rcons t j).
Proof.
elim: t i => [|k t IH] i /=; first by rewrite andbT.
by rewrite IH.
Qed.

Lemma pmnb_steps_rev (i : 'I_N) t (j : 'I_N) : pmsw_steps N j (rev t) i = pmsw_steps N i t j.
Proof.
rewrite !pmnb_steps_path.
have := rev_path (fun a b : 'I_N => a != b) i (rcons t j).
rewrite last_rcons belast_rcons rev_cons => ->.
by apply: eq_path => a b; rewrite eq_sym.
Qed.

Lemma pmnb_cnb_rev (cs : seq C) : pmnb_cnb C (rev cs) = pmnb_cnb C cs.
Proof.
case: cs => [//|c cs].
rewrite /pmnb_cnb (lastI c cs) rev_rcons.
rewrite rev_path; apply: eq_path => a b /=.
by rewrite eq_sym.
Qed.

Lemma pmnb_prod_rcons t (i k j : 'I_N) cs c : size cs = (size t).+1 ->
  pmnb_prod X i (rcons t k) j (rcons cs c) = pmnb_prod X i t k cs * (X k c * X j c).
Proof.
elim: t i cs => [|k' t IH] i [|c0 cs] //=.
  by case: cs => [|? ?] //= _; rewrite mulrA.
by move=> [Hs]; rewrite IH //; ring.
Qed.

Lemma pmnb_prod_rev t (i j : 'I_N) cs : size cs = (size t).+1 ->
  pmnb_prod X j (rev t) i (rev cs) = pmnb_prod X i t j cs.
Proof.
elim: t i cs => [|k t IH] i [|c cs] //=.
  by case: cs => [|? ?] //= _; rewrite mulrC.
move=> [Hs]; rewrite !rev_cons pmnb_prod_rcons ?size_rev //.
by rewrite IH //; ring.
Qed.

Lemma pmnb_seqs_mem (T : eqType) (s : seq T) L t :
  (t \in pmsw_seqs s L) = (size t == L) && all (mem s) t.
Proof.
elim: L t => [|L IH] t /=; first by rewrite inE; case: t.
apply/allpairsP/andP => [[[x u] /= [Hx Hu ->]] | [Hsz Hall]].
  by move: Hu; rewrite IH /= => /andP [/eqP -> Hu]; rewrite eqxx Hx.
case: t Hsz Hall => [//|x u] /= Hsz /andP [Hx Hu].
by exists (x, u); split => //=; rewrite IH -eqSS Hsz.
Qed.

Lemma pmnb_seqs_uniq (T : eqType) (s : seq T) L : uniq s -> uniq (pmsw_seqs s L).
Proof.
move=> Hs; elim: L => [|L IH] //=.
apply: allpairs_uniq => //.
by move=> [x u] [y w] _ _ /= [-> ->].
Qed.

Lemma pmnb_seqs_rev (T : finType) L (F : seq T -> R) :
  \sum_(t <- pmsw_seqs (index_enum T) L) F (rev t) =
  \sum_(t <- pmsw_seqs (index_enum T) L) F t.
Proof.
rewrite -(big_map rev xpredT F); apply: perm_big.
apply: uniq_perm.
- by rewrite (map_inj_uniq (can_inj revK)) pmnb_seqs_uniq // index_enum_uniq.
- by rewrite pmnb_seqs_uniq // index_enum_uniq.
move=> t; apply/mapP/idP => [[u Hu ->] | Ht].
  move: Hu; rewrite !pmnb_seqs_mem size_rev => /andP [-> _] /=.
  by apply/allP => x _; exact: mem_index_enum.
exists (rev t); last by rewrite revK.
move: Ht; rewrite !pmnb_seqs_mem size_rev => /andP [-> _] /=.
by apply/allP => x _; exact: mem_index_enum.
Qed.

Lemma pmnb_T_sym L : (pmlo_T N C X kap L)^T = pmlo_T N C X kap L.
Proof.
case: L => [|L]; first by rewrite pmlo_T0 trmx1.
apply/matrixP => i j; rewrite mxE !pmnb_T_walks; congr (_ * _).
rewrite -pmnb_seqs_rev; apply: eq_big_seq => t Ht.
rewrite -pmnb_seqs_rev; apply: eq_big_seq => cs Hcs.
move: Ht Hcs; rewrite !pmnb_seqs_mem => /andP [/eqP Ht _] /andP [/eqP Hcs _].
rewrite pmnb_steps_rev pmnb_cnb_rev pmnb_prod_rev //.
by rewrite Ht Hcs.
Qed.

(* 3. Powers: closed walks of NB segments. A list of columns is cut into
   q segments of length seg, each with distinct consecutive columns. *)
Fixpoint pmnb_segs (seg q : nat) (cs : seq C) : bool :=
  if q is q'.+1 then pmnb_cnb C (take seg cs) && pmnb_segs seg q' (drop seg cs) else true.

Definition pmnb_LW (m q : nat) (i j : 'I_N) : R :=
  \sum_(rs <- pmsw_seqs (index_enum 'I_N) (m + q * m.+1))
    \sum_(cs <- pmsw_seqs (index_enum C) (q.+1 * m.+1))
      (pmsw_steps N i rs j && pmnb_segs m.+1 q.+1 cs)%:R * pmnb_prod X i rs j cs.

Lemma pmnb_steps_cat (i : 'I_N) us (k : 'I_N) rs (j : 'I_N) :
  pmsw_steps N i (us ++ k :: rs) j = pmsw_steps N i us k && pmsw_steps N k rs j.
Proof.
elim: us i => [|u us IH] i //=.
by rewrite IH andbA.
Qed.

Lemma pmnb_prod_cat (i : 'I_N) us (k : 'I_N) rs (j : 'I_N) cs cs' :
  size cs = (size us).+1 ->
  pmnb_prod X i (us ++ k :: rs) j (cs ++ cs') = pmnb_prod X i us k cs * pmnb_prod X k rs j cs'.
Proof.
elim: us i cs => [|u us IH] i [|c cs] //=; first by case: cs => [|? ?] //= _.
by move=> [Hs]; rewrite IH // mulrA.
Qed.

Lemma pmnb_power_LW m q (i j : 'I_N) :
  (pmlo_T N C X kap m.+1 ^+ q.+1) i j = kap ^+ (q.+1 * m.+1) * pmnb_LW m q i j.
Proof.
elim: q i => [|q IH] i.
  rewrite expr1 pmnb_T_walks /pmnb_LW mul0n addn0 mul1n; congr (_ * _).
  apply: eq_big_seq => rs _; apply: eq_big_seq => cs Hcs.
  move: Hcs; rewrite pmnb_seqs_mem => /andP [/eqP Hcs _].
  by rewrite /= andbT take_oversize // Hcs.
rewrite exprS -mulmxE mxE.
(* Cutting the first segment off a walk of q + 2 segments. *)
have E : pmnb_LW m q.+1 i j = \sum_k
    (\sum_(us <- pmsw_seqs (index_enum 'I_N) m) \sum_(cs <- pmsw_seqs (index_enum C) m.+1)
      (pmsw_steps N i us k && pmnb_cnb C cs)%:R * pmnb_prod X i us k cs) * pmnb_LW m q k j.
  rewrite /pmnb_LW.
  have -> : (m + q.+1 * m.+1 = m + (m + q * m.+1).+1)%N by rewrite mulSn addSn.
  have -> : (q.+2 * m.+1 = m.+1 + q.+1 * m.+1)%N by rewrite mulSn.
  rewrite pmnb_seqs_cat.
  under eq_bigr => us _ do rewrite pmsw_seqs_sumS.
  rewrite exchange_big; apply: eq_bigr => k _.
  rewrite mulr_suml; apply: eq_big_seq => us Hus.
  move: Hus; rewrite pmnb_seqs_mem => /andP [/eqP Hus _].
  rewrite mulr_suml.
  under eq_bigr => t _ do rewrite pmnb_seqs_cat.
  rewrite exchange_big; apply: eq_big_seq => cs1 Hcs1.
  move: Hcs1; rewrite pmnb_seqs_mem => /andP [/eqP Hcs1 _].
  rewrite mulr_sumr; apply: eq_bigr => t _.
  rewrite mulr_sumr; apply: eq_bigr => cs2 _.
  rewrite pmnb_steps_cat pmnb_prod_cat ?Hus ?Hcs1 //.
  rewrite /pmnb_segs -/pmnb_segs take_size_cat ?drop_size_cat ?Hcs1 //.
  by rewrite -!mulnb !natrM; ring.
rewrite E mulr_sumr; apply: eq_bigr => k _.
rewrite IH pmnb_T_walks.
have -> : (q.+2 * m.+1 = m.+1 + q.+1 * m.+1)%N by rewrite mulSn.
rewrite exprD.
set A := \sum_(us <- _) _.
set P1 := kap ^+ m.+1; set P2 := kap ^+ (q.+1 * m.+1); set Lw := pmnb_LW m q k j.
ring.
Qed.

Lemma pmnb_trace_LW m q :
  \tr (pmlo_T N C X kap m.+1 ^+ q.+1) = kap ^+ (q.+1 * m.+1) * \sum_(i < N) pmnb_LW m q i i.
Proof.
rewrite /mxtrace mulr_sumr; apply: eq_bigr => i _.
exact: pmnb_power_LW.
Qed.

End Walks.

(* 4. The square-free instance. The columns are ordered pairs (a, b); only
   increasing pairs carry weight, so a column is an unordered pair a < b. *)
Definition pmnb_X {F : pzRingType} (d : nat) (xs : list F) {N : nat} (u : 'I_N)
    (c : 'I_d * 'I_d) : F :=
  ((c.1 < c.2)%N)%:R * (List.nth (u * d + c.1) xs 0 * List.nth (u * d + c.2) xs 0).

Section Instance.
Variables N d : nat.

Lemma pmnb_X_prod (xs : list R) (i : 'I_N) t (j : 'I_N) (cs : seq ('I_d * 'I_d)) :
  size cs = (size t).+1 ->
  pmnb_prod (pmnb_X d xs) i t j cs =
  (all (fun c : 'I_d * 'I_d => (c.1 < c.2)%N) cs)%:R * pmsw_mono (pmsw_word N d i t j cs) xs.
Proof.
elim: t i cs => [|k t IH] i [|c cs] //=.
  case: cs => [|? ?] //= _.
  rewrite pmsw_edge_mono /pmnb_X andbT.
  by case: (c.1 < c.2)%N; rewrite /= ?mul1r ?mul0r //; ring.
move=> [Hs]; rewrite IH // !pmsw_mono_cons1 /pmnb_X /pmsw_coord.
by case: (c.1 < c.2)%N => /=; rewrite ?mul1r ?mul0r ?mulr0 //; ring.
Qed.

Theorem pmnb_trace_moment (kap : R) m q :
  gaussian_iterated_expectation (N * d)
    (fun xs => \tr (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d xs) kap m.+1 ^+ q.+1)) =
  kap ^+ (q.+1 * m.+1) * \sum_(i < N)
    \sum_(rs <- pmsw_seqs (index_enum 'I_N) (m + q * m.+1))
    \sum_(cs <- pmsw_seqs (index_enum ('I_d * 'I_d)%type) (q.+1 * m.+1))
      [&& pmsw_steps N i rs i, pmnb_segs _ m.+1 q.+1 cs & all (fun c : 'I_d * 'I_d => (c.1 < c.2)%N) cs]%:R *
      pmsw_moment (N * d) (pmsw_word N d i rs i cs).
Proof.
set K := (q.+1 * m.+1)%N.
pose B (i : 'I_N) rs cs := [&& pmsw_steps N i rs i, pmnb_segs ('I_d * 'I_d)%type m.+1 q.+1 cs
  & all (fun c : 'I_d * 'I_d => (c.1 < c.2)%N) cs].
have R3 (i : 'I_N) rs : pmdf_regular (N * d) (fun xs =>
    \sum_(cs <- pmsw_seqs (index_enum ('I_d * 'I_d)%type) K)
      (B i rs cs)%:R * pmsw_mono (pmsw_word N d i rs i cs) xs).
  by apply: pmsw_reg_seq => cs; apply: pmdm_reg_scale; exact: pmsw_word_reg.
have R2 (i : 'I_N) : pmdf_regular (N * d) (fun xs =>
    \sum_(rs <- pmsw_seqs (index_enum 'I_N) (m + q * m.+1))
    \sum_(cs <- pmsw_seqs (index_enum ('I_d * 'I_d)%type) K)
      (B i rs cs)%:R * pmsw_mono (pmsw_word N d i rs i cs) xs).
  by apply: pmsw_reg_seq => rs; exact: R3.
have R1 : pmdf_regular (N * d) (fun xs => \sum_(i < N)
    \sum_(rs <- pmsw_seqs (index_enum 'I_N) (m + q * m.+1))
    \sum_(cs <- pmsw_seqs (index_enum ('I_d * 'I_d)%type) K)
      (B i rs cs)%:R * pmsw_mono (pmsw_word N d i rs i cs) xs).
  by apply: pmdm_reg_sum => i; exact: R2.
(* The trace as a sum of monomials. *)
transitivity (gaussian_iterated_expectation (N * d) (fun xs => kap ^+ K * \sum_(i < N)
    \sum_(rs <- pmsw_seqs (index_enum 'I_N) (m + q * m.+1))
    \sum_(cs <- pmsw_seqs (index_enum ('I_d * 'I_d)%type) K)
      (B i rs cs)%:R * pmsw_mono (pmsw_word N d i rs i cs) xs)).
  apply: gaussian_iterated_expectation_ext => xs _.
  rewrite pmnb_trace_LW /pmnb_LW; congr (_ * _); apply: eq_bigr => i _.
  apply: eq_big_seq => rs Hrs; apply: eq_big_seq => cs Hcs.
  move: Hrs Hcs; rewrite !pmnb_seqs_mem => /andP [/eqP Hrs _] /andP [/eqP Hcs _].
  rewrite pmnb_X_prod; first by rewrite Hrs Hcs mulSn addSn.
  rewrite /B; case: (pmsw_steps N i rs i); case: (pmnb_segs _ _ _ cs);
    case: (all _ cs); by rewrite /= ?mul1r ?mul0r.
(* Linearity, then the moment of each monomial. *)
apply: (etrans (pmdm_E_scale _ (kap ^+ K) _ R1)); congr (_ * _).
apply: (etrans (pmdm_E_sum _ _ _ R2)); apply: eq_bigr => i _.
apply: (etrans (pmsw_E_seq _ _ _ _ (R3 i))); apply: eq_bigr => rs _.
apply: (etrans (pmsw_E_seq _ _ _ _
  (fun cs => pmdm_reg_scale _ _ _ (pmsw_word_reg N d i rs i cs)))).
apply: eq_bigr => cs _.
apply: (etrans (pmdm_E_scale _ _ _ (pmsw_word_reg N d i rs i cs))).
by rewrite paper_main_gaussian_monomial_moment // pmsw_word_bound.
Qed.

End Instance.
