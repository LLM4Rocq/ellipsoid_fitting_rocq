(* The exact walk expansion of the square-free feature Gram (G16,
   checkpoint A2).
   For a list xs of N * d coordinates, x_ia = List.nth (i * d + a) xs 0, and
   G_ij = sum_(a != b) x_ia x_ib x_ja x_jb (pmsw_G). This is the Gram
   V V^T of the G14 square-free block, whose sqrt 2 normalization over
   a < b becomes the sum over ordered pairs a != b
   (paper_main_squarefree_gram_list). W is G without its diagonal.
   - For any matrix A, an entry of A^(K+1) is the sum over row lists t of
     length K of the path products A_(i t_1) A_(t_1 t_2) ... A_(t_K j)
     (pmsw_power_path).
   - A path product of G is the sum over label lists ps of K + 1 ordered
     pairs p_s = (a_s, b_s), a_s != b_s, of the monomial of the walk word
     (i_s d + a_s, i_s d + b_s, i_(s+1) d + a_s, i_(s+1) d + b_s)_s
     (pmsw_path_G). For W, the walk also has distinct consecutive rows.
   - E tr G^(K+1) and E tr W^(K+1) are the sums over closed walks and labels
     of prod_c moment_factor (multiplicity of c in the word)
     (paper_main_squarefree_trace_walks and paper_main_squarefree_offdiag_walks,
     with PaperMainSquarefreeWalkMoments); the same identities hold for the
     actual sample under gaussian_product_law (N * d).
   These are exact identities. No counting estimate and no probability
   premise. *)
From Stdlib Require Import Reals List Lia FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct
  GaussianProbabilityProductDefinitions PaperMainDefinitions
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments
  PaperMainFeatureGramBlocks PaperMainDiagonalBlockMoment PaperMainSquarefreeWalkMoments.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Lists of a fixed length over a finite list. *)
Fixpoint pmsw_seqs {T : Type} (s : seq T) (K : nat) : seq (seq T) :=
  if K is K'.+1 then [seq x :: t | x <- s, t <- pmsw_seqs s K'] else [:: [::]].

Lemma pmsw_seqs_sum0 (T : Type) (s : seq T) (F : seq T -> R) :
  \sum_(w <- pmsw_seqs s 0) F w = F [::].
Proof. by rewrite /= big_cons big_nil addr0. Qed.

Lemma pmsw_seqs_sumS (T : Type) (s : seq T) K (F : seq T -> R) :
  \sum_(w <- pmsw_seqs s K.+1) F w = \sum_(x <- s) \sum_(t <- pmsw_seqs s K) F (x :: t).
Proof. by rewrite /= big_allpairs_dep. Qed.

Lemma pmsw_seqs_size (T : eqType) (s : seq T) K w : w \in pmsw_seqs s K -> size w = K.
Proof.
elim: K w => [|K IH] w /=; first by rewrite inE => /eqP ->.
by case/allpairsP => [[x t] [_ Ht ->]] /=; rewrite (IH t Ht).
Qed.

Arguments pmsw_seqs_size {T s K w}.

(* 2. Linearity and regularity of sums over lists. *)
Section ListSums.
Variable D : nat.

Lemma pmsw_reg_seq (T : Type) (s : seq T) (F : T -> list R -> R) :
  (forall x, pmdf_regular D (F x)) -> pmdf_regular D (fun xs => \sum_(x <- s) F x xs).
Proof.
move=> HF; elim: s => [|x s IH].
  apply: (pmdf_regular_ext _ (fun _ => 0)) => [xs|]; first by rewrite big_nil.
  exact: pmdm_reg_const.
apply: (pmdf_regular_ext _ (fun xs => F x xs + \sum_(y <- s) F y xs)) => [xs|].
  by rewrite big_cons.
exact: pmdm_reg_add.
Qed.

Lemma pmsw_E_seq (T : Type) (s : seq T) (F : T -> list R -> R) :
  (forall x, pmdf_regular D (F x)) ->
  gaussian_iterated_expectation D (fun xs => \sum_(x <- s) F x xs) =
  \sum_(x <- s) gaussian_iterated_expectation D (F x).
Proof.
move=> HF; elim: s => [|x s IH].
  have -> : (fun xs => \sum_(x <- [::]) F x xs) = (fun _ => 0).
    by apply: functional_extensionality => xs; rewrite big_nil.
  by rewrite pmdm_E_const big_nil.
have -> : (fun xs => \sum_(y <- x :: s) F y xs) =
    (fun xs => F x xs + \sum_(y <- s) F y xs).
  by apply: functional_extensionality => xs; rewrite big_cons.
rewrite pmdm_E_add; [exact: HF | exact: pmsw_reg_seq |].
by rewrite IH big_cons.
Qed.

End ListSums.

(* 3. Entries of matrix powers as sums of path products. *)
Fixpoint pmsw_path {N} (A : 'M[R]_N) (i : 'I_N) (t : seq 'I_N) (j : 'I_N) : R :=
  if t is k :: t' then (A i k * pmsw_path A k t' j)%R else A i j.

Lemma pmsw_power_path N (A : 'M[R]_N) K (i j : 'I_N) :
  (A ^+ K.+1) i j = \sum_(t <- pmsw_seqs (index_enum 'I_N) K) pmsw_path A i t j.
Proof.
elim: K i j => [|K IH] i j; first by rewrite expr1 pmsw_seqs_sum0.
rewrite exprS mxE pmsw_seqs_sumS; apply: eq_bigr => k _.
by rewrite IH mulr_sumr.
Qed.

Lemma pmsw_trace_path N (A : 'M[R]_N) K :
  \tr (A ^+ K.+1) = \sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K) pmsw_path A i t i.
Proof. by apply: eq_bigr => i _; rewrite pmsw_power_path. Qed.

(* 4. The square-free Gram on lists. *)
Section Gram.
Variables N d : nat.

Definition pmsw_coord (i a : nat) : nat := (i * d + a)%N.

Definition pmsw_edge (i j : nat) (p : 'I_d * 'I_d) : seq nat :=
  [:: pmsw_coord i p.1; pmsw_coord i p.2; pmsw_coord j p.1; pmsw_coord j p.2].

Definition pmsw_pairs : seq ('I_d * 'I_d) :=
  [seq p <- index_enum ('I_d * 'I_d)%type | p.1 != p.2].

Definition pmsw_G (xs : list R) : 'M[R]_N :=
  \matrix_(i, j) \sum_(p <- pmsw_pairs) pmsw_mono (pmsw_edge i j p) xs.

Definition pmsw_W (xs : list R) : 'M[R]_N :=
  \matrix_(i, j) if i == j then 0 else pmsw_G xs i j.

Lemma pmsw_edge_mono (i j : nat) (p : 'I_d * 'I_d) xs :
  pmsw_mono (pmsw_edge i j p) xs =
  List.nth (i * d + p.1) xs 0 * List.nth (i * d + p.2) xs 0 *
  (List.nth (j * d + p.1) xs 0 * List.nth (j * d + p.2) xs 0).
Proof. by rewrite /pmsw_edge !pmsw_mono_cons1 pmsw_mono_nil mulr1 !mulrA. Qed.

Lemma pmsw_pairs_sum (F : 'I_d -> 'I_d -> R) :
  \sum_(p <- pmsw_pairs) F p.1 p.2 =
  \sum_(a < d) \sum_(b < d) (if a != b then F a b else 0).
Proof.
by rewrite /pmsw_pairs big_filter big_mkcond /= pair_big /=.
Qed.

(* The G14 Gram on an actual sample. *)
Lemma paper_main_squarefree_gram_list (x : paper_main_sample N d) :
  paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T =
  pmsw_G (tval x).
Proof.
apply/matrixP => i j; rewrite paper_main_squarefree_gram_entry mxE.
pose F (a b : 'I_d) := paper_main_point x i a 0 * paper_main_point x i b 0 *
  (paper_main_point x j a 0 * paper_main_point x j b 0).
have HF a b : F a b = F b a by rewrite /F; ring.
have Hs := pmfg_sum_sym d F HF.
have -> : \sum_(p <- pmsw_pairs) pmsw_mono (pmsw_edge i j p) (tval x) =
    \sum_(p <- pmsw_pairs) F p.1 p.2.
  by apply: eq_bigr => p _; rewrite pmsw_edge_mono /F /paper_main_point !mxE.
rewrite pmsw_pairs_sum.
have -> : \sum_(a < d) \sum_(b < d) (if a != b then F a b else 0) =
    \sum_(a < d) \sum_(b < d) F a b - \sum_(a < d) F a a.
  rewrite -sumrB; apply: eq_bigr => a _.
  rewrite (bigD1 a) //= eqxx add0r [in RHS](bigD1 a) //= [F a a + _]addrC addrK.
  by apply: eq_bigr => b Hb; rewrite eq_sym Hb.
by rewrite Hs [\sum_(a < d) F a a + _]addrC addrK.
Qed.

(* Walk words: the coordinates of the edges along a walk. *)
Fixpoint pmsw_word (i : 'I_N) (t : seq 'I_N) (j : 'I_N) (ps : seq ('I_d * 'I_d)) : seq nat :=
  match t, ps with
  | k :: t', p :: ps' => pmsw_edge i k p ++ pmsw_word k t' j ps'
  | [::], p :: _ => pmsw_edge i j p
  | _, [::] => [::]
  end.

(* Distinct consecutive rows along i, t, j. *)
Fixpoint pmsw_steps (i : 'I_N) (t : seq 'I_N) (j : 'I_N) : bool :=
  if t is k :: t' then (i != k) && pmsw_steps k t' j else i != j.

Lemma pmsw_path_G xs (i : 'I_N) t (j : 'I_N) :
  pmsw_path (pmsw_G xs) i t j =
  \sum_(ps <- pmsw_seqs pmsw_pairs (size t).+1) pmsw_mono (pmsw_word i t j ps) xs.
Proof.
elim: t i => [|k t IH] i.
  rewrite [size _]/= pmsw_seqs_sumS /= mxE.
  by apply: eq_bigr => p _; rewrite big_cons big_nil addr0.
rewrite [size _]/= pmsw_seqs_sumS [pmsw_path _ _ _ _]/= IH mxE.
rewrite mulr_suml; apply: eq_bigr => p _; rewrite mulr_sumr; apply: eq_bigr => ps _.
exact: (esym (pmsw_mono_cat (pmsw_edge i k p) (pmsw_word k t j ps) xs)).
Qed.

Lemma pmsw_path_W xs (i : 'I_N) t (j : 'I_N) :
  pmsw_path (pmsw_W xs) i t j = (pmsw_steps i t j)%:R * pmsw_path (pmsw_G xs) i t j.
Proof.
elim: t i => [|k t IH] i /=.
  by rewrite !mxE; case: eqP => _; rewrite ?mul0r ?mul1r.
rewrite IH !mxE; case: (i =P k) => _ /=; first by rewrite !mul0r.
by rewrite mulrCA.
Qed.

Lemma pmsw_word_bound (i : 'I_N) t (j : 'I_N) ps :
  all (fun c => (c < N * d)%N) (pmsw_word i t j ps).
Proof.
have Hc (k : 'I_N) (a : 'I_d) : (pmsw_coord k a < N * d)%N.
  exact: pmdm_index_lt (ltn_ord k) (ltn_ord a).
elim: t i ps => [|k t IH] i [|p ps] //=.
  by rewrite !Hc.
by rewrite /= !Hc IH.
Qed.

Lemma pmsw_word_reg (i : 'I_N) t (j : 'I_N) ps :
  pmdf_regular (N * d) (pmsw_mono (pmsw_word i t j ps)).
Proof. exact: pmsw_mono_reg (pmsw_word_bound i t j ps). Qed.

(* 5. The expected traces. *)
Lemma pmsw_trace_expand K xs :
  \tr (pmsw_G xs ^+ K.+1) =
  \sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs.
Proof.
rewrite pmsw_trace_path; apply: eq_bigr => i _; apply: eq_big_seq => t Ht.
by rewrite pmsw_path_G (pmsw_seqs_size Ht).
Qed.

Lemma pmsw_offdiag_expand K xs :
  \tr (pmsw_W xs ^+ K.+1) =
  \sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    (pmsw_steps i t i)%:R *
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs.
Proof.
rewrite pmsw_trace_path; apply: eq_bigr => i _; apply: eq_big_seq => t Ht.
by rewrite pmsw_path_W pmsw_path_G (pmsw_seqs_size Ht).
Qed.

Lemma pmsw_trace_reg K : pmdf_regular (N * d) (fun xs => \tr (pmsw_G xs ^+ K.+1)).
Proof.
apply: (pmdf_regular_ext _ (fun xs => \sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs)) => [xs|].
  by rewrite pmsw_trace_expand.
apply: pmdm_reg_sum => i; apply: pmsw_reg_seq => t; apply: pmsw_reg_seq => ps.
exact: pmsw_word_reg.
Qed.

Lemma pmsw_offdiag_reg K : pmdf_regular (N * d) (fun xs => \tr (pmsw_W xs ^+ K.+1)).
Proof.
apply: (pmdf_regular_ext _ (fun xs => \sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    (pmsw_steps i t i)%:R *
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs)) => [xs|].
  by rewrite pmsw_offdiag_expand.
apply: pmdm_reg_sum => i; apply: pmsw_reg_seq => t; apply: pmdm_reg_scale.
by apply: pmsw_reg_seq => ps; exact: pmsw_word_reg.
Qed.

Theorem paper_main_squarefree_trace_walks K :
  gaussian_iterated_expectation (N * d) (fun xs => \tr (pmsw_G xs ^+ K.+1)) =
  \sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_moment (N * d) (pmsw_word i t i ps).
Proof.
have R3 i t : pmdf_regular (N * d) (fun xs =>
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs).
  by apply: pmsw_reg_seq => ps; exact: pmsw_word_reg.
have R2 i : pmdf_regular (N * d) (fun xs => \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs).
  by apply: pmsw_reg_seq => t; exact: R3.
transitivity (gaussian_iterated_expectation (N * d) (fun xs =>
  \sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs)).
  apply: gaussian_iterated_expectation_ext => xs _.
  rewrite pmsw_trace_path; apply: eq_bigr => i _; apply: eq_big_seq => t Ht.
  by rewrite pmsw_path_G (pmsw_seqs_size Ht).
rewrite (pmdm_E_sum _ _ _ R2); apply: eq_bigr => i _.
rewrite (pmsw_E_seq _ _ _ _ (R3 i)); apply: eq_bigr => t _.
rewrite (pmsw_E_seq _ _ _ _ (fun ps => pmsw_word_reg i t i ps)); apply: eq_bigr => ps _.
exact: paper_main_gaussian_monomial_moment (pmsw_word_bound i t i ps).
Qed.

Theorem paper_main_squarefree_offdiag_walks K :
  gaussian_iterated_expectation (N * d) (fun xs => \tr (pmsw_W xs ^+ K.+1)) =
  \sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    (pmsw_steps i t i)%:R *
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_moment (N * d) (pmsw_word i t i ps).
Proof.
have R3 i t : pmdf_regular (N * d) (fun xs =>
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs).
  by apply: pmsw_reg_seq => ps; exact: pmsw_word_reg.
have R3' i t : pmdf_regular (N * d) (fun xs => (pmsw_steps i t i)%:R *
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs).
  exact: pmdm_reg_scale (R3 i t).
have R2 i : pmdf_regular (N * d) (fun xs => \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    (pmsw_steps i t i)%:R *
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs).
  by apply: pmsw_reg_seq => t; exact: R3'.
transitivity (gaussian_iterated_expectation (N * d) (fun xs =>
  \sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
    (pmsw_steps i t i)%:R *
    \sum_(ps <- pmsw_seqs pmsw_pairs K.+1) pmsw_mono (pmsw_word i t i ps) xs)).
  apply: gaussian_iterated_expectation_ext => xs _.
  rewrite pmsw_trace_path; apply: eq_bigr => i _; apply: eq_big_seq => t Ht.
  by rewrite pmsw_path_W pmsw_path_G (pmsw_seqs_size Ht).
rewrite (pmdm_E_sum _ _ _ R2); apply: eq_bigr => i _.
rewrite (pmsw_E_seq _ _ _ _ (R3' i)); apply: eq_bigr => t _.
rewrite (pmdm_E_scale _ _ _ (R3 i t)); congr (_ * _).
rewrite (pmsw_E_seq _ _ _ _ (fun ps => pmsw_word_reg i t i ps)); apply: eq_bigr => ps _.
exact: paper_main_gaussian_monomial_moment (pmsw_word_bound i t i ps).
Qed.


(* 6. The actual sample. *)
Definition paper_main_squarefree_offdiag (x : paper_main_sample N d) : 'M[R]_N :=
  \matrix_(i, j) if i == j then 0 else
    (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T) i j.

Lemma paper_main_squarefree_offdiag_list (x : paper_main_sample N d) :
  paper_main_squarefree_offdiag x = pmsw_W (tval x).
Proof.
apply/matrixP => i j.
by rewrite /paper_main_squarefree_offdiag paper_main_squarefree_gram_list !mxE.
Qed.

Theorem paper_main_squarefree_trace_law K :
  (gaussian_product_law (N * d)).-integrable setT (fun x =>
    (\tr ((paper_main_squarefree_block N d x *m
      (paper_main_squarefree_block N d x)^T) ^+ K.+1))%:E) /\
  (\int[gaussian_product_law (N * d)]_x
    (\tr ((paper_main_squarefree_block N d x *m
      (paper_main_squarefree_block N d x)^T) ^+ K.+1))%:E =
   (\sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
      \sum_(ps <- pmsw_seqs pmsw_pairs K.+1)
        pmsw_moment (N * d) (pmsw_word i t i ps))%R%:E)%E.
Proof.
have -> : (fun x : paper_main_sample N d =>
    (\tr ((paper_main_squarefree_block N d x *m
      (paper_main_squarefree_block N d x)^T) ^+ K.+1))%:E) =
    (fun x => (\tr (pmsw_G (tval x) ^+ K.+1))%:E).
  by apply: functional_extensionality => x; rewrite paper_main_squarefree_gram_list.
have [HI HE] := pmdf_actual (N * d) _ (pmsw_trace_reg K).
by split => //; rewrite HE paper_main_squarefree_trace_walks.
Qed.

Theorem paper_main_squarefree_offdiag_law K :
  (gaussian_product_law (N * d)).-integrable setT (fun x =>
    (\tr (paper_main_squarefree_offdiag x ^+ K.+1))%:E) /\
  (\int[gaussian_product_law (N * d)]_x (\tr (paper_main_squarefree_offdiag x ^+ K.+1))%:E =
   (\sum_(i < N) \sum_(t <- pmsw_seqs (index_enum 'I_N) K)
      (pmsw_steps i t i)%:R *
      \sum_(ps <- pmsw_seqs pmsw_pairs K.+1)
        pmsw_moment (N * d) (pmsw_word i t i ps))%R%:E)%E.
Proof.
have -> : (fun x : paper_main_sample N d =>
    (\tr (paper_main_squarefree_offdiag x ^+ K.+1))%:E) =
    (fun x => (\tr (pmsw_W (tval x) ^+ K.+1))%:E).
  by apply: functional_extensionality => x; rewrite paper_main_squarefree_offdiag_list.
have [HI HE] := pmdf_actual (N * d) _ (pmsw_offdiag_reg K).
by split => //; rewrite HE paper_main_squarefree_offdiag_walks.
Qed.

End Gram.
