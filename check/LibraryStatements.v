(* The general statements of phase 13 accepted by the user, stated in full
   as the acceptance inventory of scripts/check_sources.py records them,
   and proved by their library lemmas. The statements of one library file
   are read in a module with the Require, Import and Open Scope commands
   of that file at the commit of their acceptance, where the inventory
   printed them. make check compiles this file; its code is fixed by
   scripts/check_sources.py. *)

(* The Require commands of each file are inside its module, so that the
   imports end with the module. *)
Set Warnings "-require-in-module".

(* library/probability/finite_mean.v, accepted at 46e45c84b99a *)
Module accepted_finite_mean.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import arithmetic_tactic ring_tactic.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Require Import GaussianAnalysis.probability.finite_mean.

Lemma unif_mean_union_accepted : forall (R : realFieldType) (T I : finType) (P : I -> pred T), @unif_mean R T (fun x : T => [exists i, P i x]%:R : R) <= \sum_i @unif_mean R T (fun x : T => (P i x)%:R : R).
Proof. exact: @unif_mean_union. Qed.

Lemma unif_mean_indicatorN_accepted : forall (R : realFieldType) (T : finType) (P : pred T), (0 < #|T|)%N -> @unif_mean R T (fun x : T => (~~ P x)%:R : R) = 1 - @unif_mean R T (fun x : T => (P x)%:R : R).
Proof. exact: @unif_mean_indicatorN. Qed.

Lemma unif_mean_markov_accepted : forall (R : realFieldType) (T : finType) (f : T -> R) (t : R), (forall x : T, 0 <= f x) -> t * @unif_mean R T (fun x : T => (t <= f x)%R%:R : R) <= @unif_mean R T f.
Proof. exact: @unif_mean_markov. Qed.

Lemma unif_mean_cutoff_accepted : forall (R : realFieldType) (T : finType) (f : T -> R) (M t : R), 0 <= t -> (forall x : T, f x <= M) -> @unif_mean R T f <= t + M * @unif_mean R T (fun x : T => (t <= f x)%R%:R : R).
Proof. exact: @unif_mean_cutoff. Qed.

Lemma unif_chebyshev_accepted : forall (R : realFieldType) (T : finType) (f : T -> R) (t : R), 0 < t -> @unif_mean R T (fun x : T => (t <= `|f x - @unif_mean R T f|)%R%:R : R) <= @unif_var R T f / t ^+ 2.
Proof. exact: @unif_chebyshev. Qed.

Lemma unif_mean_tuple_prod_ord_accepted : forall (R : realFieldType) (T : finType) (m : nat) (g : 'I_m -> T -> R), @unif_mean R (tuple_tuple_of__canonical__fintype_Finite m T) (fun t : m.-tuple T => \prod_(i < m) g i (@tnth m T t i)) = \prod_(i < m) @unif_mean R T (g i).
Proof. exact: @unif_mean_tuple_prod_ord. Qed.

Lemma unif_mean_tuple_prod_set_accepted : forall (R : realFieldType) (T : finType) (m : nat) (J : {set 'I_m}) (g : T -> R), (0 < #|T|)%N -> @unif_mean R (tuple_tuple_of__canonical__fintype_Finite m T) (fun t : m.-tuple T => \prod_(i in J) g (@tnth m T t i)) = @unif_mean R T g ^+ #|J|.
Proof. exact: @unif_mean_tuple_prod_set. Qed.

End accepted_finite_mean.

(* library/probability/binomial_mean.v, accepted at 46e45c84b99a *)
Module accepted_binomial_mean.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals ereal measure numfun.
From mathcomp Require Import lebesgue_integral binomial_distribution.
From mathcomp Require Import ring_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Require Import GaussianAnalysis.probability.binomial_mean.

Lemma binomial_mean0_accepted : forall (R : numDomainType) (p : R) (f : nat -> R), @binomial_mean R 0 p f = f 0%N.
Proof. exact: @binomial_mean0. Qed.

Lemma binomial_meanS_accepted : forall (R : numDomainType) (m : nat) (p : R) (f : nat -> R), @binomial_mean R m.+1 p f = (1 - p) * @binomial_mean R m p f + p * @binomial_mean R m p (fun j : nat => f j.+1).
Proof. exact: @binomial_meanS. Qed.

Lemma eq_binomial_mean_accepted : forall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R), (forall j : nat, (j <= m)%N -> f j = g j) -> @binomial_mean R m p f = @binomial_mean R m p g.
Proof. exact: @eq_binomial_mean. Qed.

Lemma binomial_mean_cst_accepted : forall (R : numDomainType) (m : nat) (p c : R), @binomial_mean R m p (fun=> c) = c.
Proof. exact: @binomial_mean_cst. Qed.

Lemma binomial_meanD_accepted : forall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R), @binomial_mean R m p (fun j : nat => f j + g j) = @binomial_mean R m p f + @binomial_mean R m p g.
Proof. exact: @binomial_meanD. Qed.

Lemma binomial_meanZ_accepted : forall (R : numDomainType) (m : nat) (p c : R) (f : nat -> R), @binomial_mean R m p (fun j : nat => c * f j) = c * @binomial_mean R m p f.
Proof. exact: @binomial_meanZ. Qed.

Lemma ler_binomial_mean_accepted : forall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R), 0 <= p <= 1 -> (forall j : nat, (j <= m)%N -> f j <= g j) -> @binomial_mean R m p f <= @binomial_mean R m p g.
Proof. exact: @ler_binomial_mean. Qed.

Lemma binomial_mean_id_accepted : forall (R : numDomainType) (m : nat) (p : R), @binomial_mean R m p [eta @Algebra.natmul R 1] = m%:R * p.
Proof. exact: @binomial_mean_id. Qed.

Lemma binomial_mean_sqr_dev_accepted : forall (R : numDomainType) (m : nat) (p : R), @binomial_mean R m p (fun j : nat => (j%:R - m%:R * p) ^+ 2) = m%:R * p * (1 - p).
Proof. exact: @binomial_mean_sqr_dev. Qed.

Lemma binomial_chebyshev_accepted : forall (R : realFieldType) (m : nat) (p t : R), 0 <= p <= 1 -> 0 < t -> @binomial_mean R m p (fun j : nat => (t <= `|j%:R - m%:R * p|)%R%:R) <= m%:R * p * (1 - p) / t ^+ 2.
Proof. exact: @binomial_chebyshev. Qed.

Lemma binomial_mean_last_accepted : forall (R : numDomainType) (m : nat) (p : R) (f : nat -> R), 0 <= p <= 1 -> (forall j : nat, (j <= m)%N -> 0 <= f j) -> p ^+ m * f m <= @binomial_mean R m p f.
Proof. exact: @binomial_mean_last. Qed.

Lemma binomial_mean_trials_accepted : forall (R : numDomainType) (m m' : nat) (p : R) (f : nat -> R), 0 <= p <= 1 -> {homo f : i j / (i <= j)%N >-> i <= j} -> (m <= m')%N -> @binomial_mean R m p f <= @binomial_mean R m' p f.
Proof. exact: @binomial_mean_trials. Qed.

Lemma unif_mean_binomial_mean_accepted : forall (R : realFieldType) (T : finType) (m : nat) (p : R) (f : nat -> T -> R), @unif_mean R T (fun x : T => @binomial_mean R m p (f^~ x)) = @binomial_mean R m p (fun j : nat => @unif_mean R T (f j)).
Proof. exact: @unif_mean_binomial_mean. Qed.

Lemma binomial_meanE_accepted : forall (R : realType) (m : nat) (p : R) (f : nat -> R), @binomial_mean R m p f = \sum_(j < m.+1) @binomial_pmf R m p (nat_of_ord j) * f (nat_of_ord j).
Proof. exact: @binomial_meanE. Qed.

Lemma integral_binomial_mean_accepted : forall (R : realType) (m : nat) (p : R) (f : nat -> R), 0 <= p <= 1 -> (\int[@binomial_prob R m p]_j (f j)%:E)%E = (@binomial_mean R m p f)%:E.
Proof. exact: @integral_binomial_mean. Qed.

End accepted_binomial_mean.

(* library/probability/commuting_operators.v, accepted at 46e45c84b99a *)
Module accepted_commuting_operators.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum boolp.
From GaussianAnalysis.probability Require Import finite_mean binomial_mean.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Require Import GaussianAnalysis.probability.commuting_operators.

Lemma homo_iter_accepted : forall (disp : Order.disp_t) (T : preorderType disp) (A : T -> T) (m : nat), {homo A : x y / (x <= y)%O} -> {homo @iter T m A : x y / (x <= y)%O}.
Proof. exact: @homo_iter. Qed.

Lemma iter_le_subcomm_accepted : forall (disp : Order.disp_t) (T : preorderType disp) (A B : T -> T) (x : T), {homo A : y z / (y <= z)%O} -> {homo B : y z / (y <= z)%O} -> (forall y : T, (B (A y) <= A (B y))%O) -> (B x <= A x)%O -> forall m : nat, (@iter T m B x <= @iter T m A x)%O.
Proof. exact: @iter_le_subcomm. Qed.

Lemma monotone_iter_le_accepted : forall (R : numDomainType) (X : Type) (A B : (X -> R) -> X -> R) (f : X -> R), @monotone_op R X A -> @monotone_op R X B -> (forall (g : X -> R) (x : X), B (A g) x <= A (B g) x) -> (forall x : X, B f x <= A f x) -> forall (m : nat) (x : X), @iter (X -> R) m B f x <= @iter (X -> R) m A f x.
Proof. exact: @monotone_iter_le. Qed.

Lemma iter_scale_accepted : forall (R : numDomainType) (X : Type) (A : (X -> R) -> X -> R) (c : R), @linear_op R X A -> forall (m : nat) (f : X -> R) (x : X), @iter (X -> R) m (fun (g : X -> R) (y : X) => c * A g y) f x = c ^+ m * @iter (X -> R) m A f x.
Proof. exact: @iter_scale. Qed.

Lemma iter_mix_binomial_accepted : forall (R : numDomainType) (X : Type) (A B : (X -> R) -> X -> R) (p : R), @linear_op R X A -> @linear_op R X B -> (forall f : X -> R, A (B f) = B (A f)) -> forall (m : nat) (f : X -> R) (x : X), @iter (X -> R) m (fun (g : X -> R) (y : X) => p * A g y + (1 - p) * B g y) f x = @binomial_mean R m p (fun j : nat => @iter (X -> R) j A (@iter (X -> R) (m - j) B f) x).
Proof. exact: @iter_mix_binomial. Qed.

Lemma binomial_mix_le_iter_accepted : forall (R : numDomainType) (X : Type) (A B C : (X -> R) -> X -> R) (p : R) (f : X -> R), 0 <= p <= 1 -> @linear_op R X A -> @linear_op R X B -> @linear_op R X C -> @monotone_op R X A -> @monotone_op R X B -> @monotone_op R X C -> (forall g : X -> R, A (B g) = B (A g)) -> (forall (g : X -> R) (x : X), A (C g) x <= C (A g) x) -> (forall (g : X -> R) (x : X), B (C g) x <= C (B g) x) -> (forall x : X, p * A f x + (1 - p) * B f x <= C f x) -> forall (m : nat) (x : X), @binomial_mean R m p (fun j : nat => @iter (X -> R) j A (@iter (X -> R) (m - j) B f) x) <= @iter (X -> R) m C f x.
Proof. exact: @binomial_mix_le_iter. Qed.

Lemma meet_avg_linear_accepted : forall (R : realFieldType) (T C : finType) (E : C -> {set T}), @linear_op R {set T} (@meet_avg R T C E).
Proof. exact: @meet_avg_linear. Qed.

Lemma meet_avg_monotone_accepted : forall (R : realFieldType) (T C : finType) (E : C -> {set T}), @monotone_op R {set T} (@meet_avg R T C E).
Proof. exact: @meet_avg_monotone. Qed.

Lemma meet_avg_cst_accepted : forall (R : realFieldType) (T C : finType) (E : C -> {set T}) (a : R) (S0 : {set T}), (0 < #|C|)%N -> @meet_avg R T C E (fun=> a) S0 = a.
Proof. exact: @meet_avg_cst. Qed.

Lemma meet_avgC_accepted : forall (R : realFieldType) (T C D : finType) (E : C -> {set T}) (F : D -> {set T}) (f : {set T} -> R), @meet_avg R T C E (@meet_avg R T D F f) = @meet_avg R T D F (@meet_avg R T C E f).
Proof. exact: @meet_avgC. Qed.

Lemma iter_meet_avg_accepted : forall (R : realFieldType) (T C : finType) (E : C -> {set T}) (m : nat) (f : {set T} -> R) (S : {set T}), @iter ({set T} -> R) m (@meet_avg R T C E) f S = @unif_mean R (tuple_tuple_of__canonical__fintype_Finite m C) (fun t : m.-tuple C => f (S :&: \bigcap_(c <- t) E c)).
Proof. exact: @iter_meet_avg. Qed.

End accepted_commuting_operators.

(* library/fourier/boolean_fourier.v, accepted at 46e45c84b99a *)
Module accepted_boolean_fourier.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint zmodp.
From mathcomp Require Import matrix.
From GaussianAnalysis.matrix Require Import euclidean.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Require Import GaussianAnalysis.fourier.boolean_fourier.

Lemma bchar_algebra_accepted : forall (t a : nat) (R : pzRingType), [/\ forall y : matrix 'F_2 t a, @bchar t a R 0 y = 1, forall p q y : matrix 'F_2 t a, @bchar t a R (p + q) y = @bchar t a R p y * @bchar t a R q y, forall p y : matrix 'F_2 t a, @bchar t a R p y = @bchar t a R y p & forall p y : matrix 'F_2 t a, @bchar t a R p y = 1 \/ @bchar t a R p y = -1].
Proof. exact: @bchar_algebra. Qed.

Lemma bchar_orthogonal_accepted : forall (t a : nat) (R : pzRingType), forall p q : matrix 'F_2 t a, \sum_y @bchar t a R p y * @bchar t a R q y = (if p == q then #|{: matrix 'F_2 t a}|%:R else 0).
Proof. exact: @bchar_orthogonal. Qed.

Lemma bchar_delta_accepted : forall (t a : nat) (R : pzRingType), forall (i : 'I_t) (j : 'I_a) (y : matrix 'F_2 t a), @bchar t a R (@delta_mx (fintype_ordinal__canonical__GRing_PzSemiRing (Zp_trunc (pdiv 2))) t a i j) y = (-1) ^+ nat_of_ord (y i j).
Proof. exact: @bchar_delta. Qed.

Lemma blk_dist_metric_accepted : forall t a : nat, [/\ forall p q : matrix 'F_2 t a, @blk_dist t a p q = @blk_deg t a (p + q), forall p q : matrix 'F_2 t a, @blk_dist t a p q = 0%N <-> p = q, forall p q : matrix 'F_2 t a, @blk_dist t a p q = @blk_dist t a q p, forall p q s : matrix 'F_2 t a, (@blk_dist t a p s <= @blk_dist t a p q + @blk_dist t a q s)%N & forall p q s : matrix 'F_2 t a, @blk_dist t a (p + s) (q + s) = @blk_dist t a p q].
Proof. exact: @blk_dist_metric. Qed.

Lemma fcoef_inversion_accepted : forall (t a : nat) (R : numFieldType), forall (V : lmodType R) (f : matrix 'F_2 t a -> V) (y : matrix 'F_2 t a), f y = \sum_p @bchar t a R p y *: @fcoef t a R V f p.
Proof. exact: @fcoef_inversion. Qed.

Lemma fcoef_expansion_accepted : forall (t a : nat) (R : numFieldType), forall (V : lmodType R) (c : matrix 'F_2 t a -> V) (q : matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => \sum_p @bchar t a R p y *: c p) q = c q.
Proof. exact: @fcoef_expansion. Qed.

Lemma fcoef_plancherel_accepted : forall (t a : nat) (R : numFieldType), forall (V W Z : lmodType R) (b : V -> W -> Z), (forall w : W, linear (b^~ w)) -> (forall v : V, linear (b v)) -> forall (f : matrix 'F_2 t a -> V) (g : matrix 'F_2 t a -> W), #|{: matrix 'F_2 t a}|%:R^-1 *: \sum_y b (f y) (g y) = \sum_p b (@fcoef t a R V f p) (@fcoef t a R W g p).
Proof. exact: @fcoef_plancherel. Qed.

Lemma fcoef_linear_accepted : forall (t a : nat) (R : numFieldType), forall (V : lmodType R) (c : R) (f g : matrix 'F_2 t a -> V) (p : matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => c *: f y + g y) p = c *: @fcoef t a R V f p + @fcoef t a R V g p.
Proof. exact: @fcoef_linear. Qed.

Lemma fcoef_comp_linear_accepted : forall (t a : nat) (R : numFieldType), forall (V W : lmodType R) (h : V -> W), linear h -> forall (f : matrix 'F_2 t a -> V) (p : matrix 'F_2 t a), @fcoef t a R W (fun y : matrix 'F_2 t a => h (f y)) p = h (@fcoef t a R V f p).
Proof. exact: @fcoef_comp_linear. Qed.

Lemma fcoef_mulmx_accepted : forall (t a : nat) (R : numFieldType), forall (m n k l : nat) (A : matrix R m n) (f : matrix 'F_2 t a -> matrix R n k) (B : matrix R k l) (p : matrix 'F_2 t a), @fcoef t a R (matrix_matrix__canonical__GRing_Lmodule R m l) (fun y : matrix 'F_2 t a => A *m f y *m B) p = A *m @fcoef t a R (matrix_matrix__canonical__GRing_Lmodule R n k) f p *m B.
Proof. exact: @fcoef_mulmx. Qed.

Lemma fcoef_norm_le_accepted : forall (t a : nat) (R : numFieldType), forall (f : matrix 'F_2 t a -> R^o) (c : R) (p : matrix 'F_2 t a), (forall y : matrix 'F_2 t a, `|f y : R| <= c) -> `|@fcoef t a R (GRing.GRing_regular__canonical__GRing_Lmodule R) f p : R| <= c.
Proof. exact: @fcoef_norm_le. Qed.

Lemma fcoef_translate_accepted : forall (t a : nat) (R : numFieldType), forall (V : lmodType R) (f : matrix 'F_2 t a -> V) (p q : matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => @bchar t a R q y *: f y) (p + q) = @fcoef t a R V f p.
Proof. exact: @fcoef_translate. Qed.

Lemma low_blk_deg_expansion_accepted : forall (t a : nat) (R : numFieldType), forall (V : lmodType R) (D : nat) (f : matrix 'F_2 t a -> V), @low_blk_deg t a R V D f <-> (forall y : matrix 'F_2 t a, f y = \sum_(p | (@blk_deg t a p <= D)%N) @bchar t a R p y *: @fcoef t a R V f p).
Proof. exact: @low_blk_deg_expansion. Qed.

Lemma low_blk_deg_translate_accepted : forall (t a : nat) (R : numFieldType), forall (V : lmodType R) (D : nat) (f : matrix 'F_2 t a -> V) (q : matrix 'F_2 t a), (forall p : matrix 'F_2 t a, (D < @blk_dist t a p q)%N -> @fcoef t a R V f p = 0) -> @low_blk_deg t a R V D (fun y : matrix 'F_2 t a => @bchar t a R q y *: f y).
Proof. exact: @low_blk_deg_translate. Qed.

Lemma blk_dist_row_accepted : forall (a : nat) (s z : matrix 'F_2 1 a), @blk_dist 1 a s z = (s != z).
Proof. exact: @blk_dist_row. Qed.

Lemma bchar_col_mx_accepted : forall t1 t2 a : nat, forall (R : pzRingType) (p1 y1 : matrix 'F_2 t1 a) (p2 y2 : matrix 'F_2 t2 a), @bchar (t1 + t2) a R (@col_mx 'F_2 t1 t2 a p1 p2) (@col_mx 'F_2 t1 t2 a y1 y2) = @bchar t1 a R p1 y1 * @bchar t2 a R p2 y2.
Proof. exact: @bchar_col_mx. Qed.

Lemma blk_col_mx_accepted : forall t1 t2 a : nat, forall (p1 q1 : matrix 'F_2 t1 a) (p2 q2 : matrix 'F_2 t2 a), @blk_deg (t1 + t2) a (@col_mx 'F_2 t1 t2 a p1 p2) = (@blk_deg t1 a p1 + @blk_deg t2 a p2)%N /\ @blk_dist (t1 + t2) a (@col_mx 'F_2 t1 t2 a p1 p2) (@col_mx 'F_2 t1 t2 a q1 q2) = (@blk_dist t1 a p1 q1 + @blk_dist t2 a p2 q2)%N.
Proof. exact: @blk_col_mx. Qed.

Lemma fcoef_col_mx_accepted : forall t1 t2 a : nat, forall (R : numFieldType) (V : lmodType R) (f : matrix 'F_2 (t1 + t2) a -> V) (p1 : matrix 'F_2 t1 a) (p2 : matrix 'F_2 t2 a), @fcoef (t1 + t2) a R V f (@col_mx 'F_2 t1 t2 a p1 p2) = @fcoef t1 a R V (fun y1 : matrix 'F_2 t1 a => @fcoef t2 a R V (fun y2 : matrix 'F_2 t2 a => f (@col_mx 'F_2 t1 t2 a y1 y2)) p2) p1.
Proof. exact: @fcoef_col_mx. Qed.

End accepted_boolean_fourier.

(* library/matrix/psd_factorization.v, accepted at 46e45c84b99a *)
Module accepted_psd_factorization.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix sesquilinear boolp classical_sets reals.
From mathcomp Require Import topology normedtype derive exp.
From mathcomp Require Import arithmetic_tactic ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part.
From GaussianAnalysis.matrix Require Import psd_splitting.
From GaussianAnalysis.convex Require Import logdet_barrier moreau.
Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Require Import GaussianAnalysis.matrix.psd_factorization.

Lemma psd_factorization_ge0_accepted : forall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat), @psd_factorization R I J A r -> forall (i : I) (j : J), 0 <= A i j.
Proof. exact: @psd_factorization_ge0. Qed.

Lemma psd_factorization_size_gt0_accepted : forall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat), @psd_factorization R I J A r -> (exists (i : I) (j : J), A i j != 0) -> (0 < r)%N.
Proof. exact: @psd_factorization_size_gt0. Qed.

Lemma psd_factorization_restrict_accepted : forall (R : realType) (I J I' J' : finType) (A : I -> J -> R) (r : nat) (f : I' -> I) (g : J' -> J), @psd_factorization R I J A r -> @psd_factorization R I' J' (fun (i : I') (j : J') => A (f i) (g j)) r.
Proof. exact: @psd_factorization_restrict. Qed.

Lemma psd_factorization_widen_accepted : forall (R : realType) (I J : finType) (A : I -> J -> R) (r s : nat), (r <= s)%N -> @psd_factorization R I J A r -> @psd_factorization R I J A s.
Proof. exact: @psd_factorization_widen. Qed.

Lemma psd_factorization_shift_accepted : forall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat) (rho : R), 0 <= rho -> @psd_factorization R I J A r -> @psd_factorization R I J (fun (i : I) (j : J) => A i j + rho) r.+1.
Proof. exact: @psd_factorization_shift. Qed.

Lemma psd_factorization_nonneg_accepted : forall (R : realType) (I J : finType) (r : nat) (a : I -> 'I_r -> R) (b : J -> 'I_r -> R), (forall (i : I) (k : 'I_r), 0 <= a i k) -> (forall (j : J) (k : 'I_r), 0 <= b j k) -> @psd_factorization R I J (fun (i : I) (j : J) => \sum_(k < r) a i k * b j k) r.
Proof. exact: @psd_factorization_nonneg. Qed.

End accepted_psd_factorization.

(* library/combinatorics/binomial_bounds.v, accepted at 46e45c84b99a *)
Module accepted_binomial_bounds.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum rat reals.
From mathcomp Require Import sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope nat_scope.
Require Import GaussianAnalysis.combinatorics.binomial_bounds.

Lemma central_bin_le_accepted : forall n : nat, (3 * n).+1 * 'C(2 * n, n) ^ 2 <= 16 ^ n.
Proof. exact: @central_bin_le. Qed.

Lemma central_bin_ge_accepted : forall n : nat, 0 < n -> 16 ^ n <= 4 * n * 'C(2 * n, n) ^ 2.
Proof. exact: @central_bin_ge. Qed.

Lemma half_bin_ge_accepted : forall h : nat, 4 ^ h <= 2 * h.+1 * 'C(h, h./2) ^ 2.
Proof. exact: @half_bin_ge. Qed.

Lemma leq_bin_half_accepted : forall n k : nat, 'C(n, k) <= 'C(n, n./2).
Proof. exact: @leq_bin_half. Qed.

Lemma bin_near_half_accepted : forall h g T : nat, 6 * T <= h -> h <= 2 * (g + T) -> 2 * g <= h + 2 * T -> 'C(h, h./2) <= 2 ^ T.+1 * 'C(h, g).
Proof. exact: @bin_near_half. Qed.

Lemma bin_sqr_central_accepted : forall u j : nat, j <= u -> 'C(u, j) ^ 2 * 'C(2 * u, u) = 'C(2 * j, j) * 'C(2 * (u - j), u - j) * 'C(2 * u, 2 * j).
Proof. exact: @bin_sqr_central. Qed.

Lemma bin_sqr_ratio_accepted : forall u j : nat, j <= u -> 'C(u, j) ^ 4 * j.+1 * (u - j).+1 <= 4 * u.+1 * 'C(2 * u, 2 * j) ^ 2.
Proof. exact: @bin_sqr_ratio. Qed.

Lemma bin_partial_sum_accepted : forall (R : realType) (N M : nat), M <= N -> ((\sum_(j < M.+1) 'C(N, nat_of_ord j)%:R : R) <= ((@expR R 1 * N%:R / M%:R) ^+ M : R))%R.
Proof. exact: @bin_partial_sum. Qed.

End accepted_binomial_bounds.

(* library/matrix/psd_duality.v, accepted at 46e45c84b99a *)
Module accepted_psd_duality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import arithmetic_tactic ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part.
From GaussianAnalysis.matrix Require Import psd_splitting psd_factorization.
From GaussianAnalysis.matrix Require Import nuclear condition_cone.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.convex Require Import logdet_barrier moreau.
Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Require Import GaussianAnalysis.matrix.psd_duality.

Lemma psd_eval_cone_closed_accepted : forall (R : realType) (n N : nat) (G : 'I_N -> matrix R n n), (forall j : 'I_N, @psdmx R n (G j)) -> @closed (matrix_matrix__canonical__topology_structure_Topological 1 N (numFieldTopology.Real_sort__canonical__topology_structure_Topological R)) (@psd_eval_cone R n N G).
Proof. exact: @psd_eval_cone_closed. Qed.

Lemma psdmx_dual_accepted : forall (R : realType) (n : nat) (S : matrix R n n), S \is symmetricmx -> @psdmx R n S <-> (forall F : matrix R n n, @psdmx R n F -> 0 <= \tr (F *m S)).
Proof. exact: @psdmx_dual. Qed.

Lemma psd_farkas_accepted : forall (R : realType) (n N : nat) (G : 'I_N -> matrix R n n) (y : matrix R 1 N), (forall j : 'I_N, @psdmx R n (G j)) -> @psd_eval_cone R n N G y <-> (forall c : matrix R 1 N, @psdmx R n (\sum_j c 0 j *: G j) -> 0 <= @mxdot R 1 N c y).
Proof. exact: @psd_farkas. Qed.

Lemma psd_slack_certificate_accepted : forall (R : realType) (n : nat) (I : finType) (B : I -> matrix R n n) (s : I -> R) (i0 : I), (forall i : I, @psdmx R n (B i)) -> s i0 = 0 -> (exists2 A : matrix R n n, @psdmx R n A & forall i : I, \tr (A *m B i) = s i) <-> (forall w : I -> R, \sum_i w i = 1 -> @psdmx R n (\sum_i w i *: B i) -> 0 <= \sum_i w i * s i).
Proof. exact: @psd_slack_certificate. Qed.

Lemma psd_slack_certificate_affine_accepted : forall (R : realType) (n m : nat) (I : finType) (C : 'I_m -> matrix R n n) (c : 'I_m -> R) (D : matrix R n n) (d : R) (B : I -> matrix R n n) (i0 : I), (forall i : I, @psdmx R n (B i)) -> (forall (i : I) (l : 'I_m), \tr (C l *m B i) = c l) -> (forall X : matrix R n n, @psdmx R n X -> (forall l : 'I_m, \tr (C l *m X) = c l) -> 0 <= \tr (D *m X) + d) -> \tr (D *m B i0) + d = 0 -> exists2 A : matrix R n n, @psdmx R n A & forall i : I, \tr (A *m B i) = \tr (D *m B i) + d.
Proof. exact: @psd_slack_certificate_affine. Qed.

End accepted_psd_duality.

(* Every accepted statement, for one axiom report. *)
Definition library_statements_accepted :=
  (accepted_finite_mean.unif_mean_union_accepted,
   accepted_finite_mean.unif_mean_indicatorN_accepted,
   accepted_finite_mean.unif_mean_markov_accepted,
   accepted_finite_mean.unif_mean_cutoff_accepted,
   accepted_finite_mean.unif_chebyshev_accepted,
   accepted_finite_mean.unif_mean_tuple_prod_ord_accepted,
   accepted_finite_mean.unif_mean_tuple_prod_set_accepted,
   accepted_binomial_mean.binomial_mean0_accepted,
   accepted_binomial_mean.binomial_meanS_accepted,
   accepted_binomial_mean.eq_binomial_mean_accepted,
   accepted_binomial_mean.binomial_mean_cst_accepted,
   accepted_binomial_mean.binomial_meanD_accepted,
   accepted_binomial_mean.binomial_meanZ_accepted,
   accepted_binomial_mean.ler_binomial_mean_accepted,
   accepted_binomial_mean.binomial_mean_id_accepted,
   accepted_binomial_mean.binomial_mean_sqr_dev_accepted,
   accepted_binomial_mean.binomial_chebyshev_accepted,
   accepted_binomial_mean.binomial_mean_last_accepted,
   accepted_binomial_mean.binomial_mean_trials_accepted,
   accepted_binomial_mean.unif_mean_binomial_mean_accepted,
   accepted_binomial_mean.binomial_meanE_accepted,
   accepted_binomial_mean.integral_binomial_mean_accepted,
   accepted_commuting_operators.homo_iter_accepted,
   accepted_commuting_operators.iter_le_subcomm_accepted,
   accepted_commuting_operators.monotone_iter_le_accepted,
   accepted_commuting_operators.iter_scale_accepted,
   accepted_commuting_operators.iter_mix_binomial_accepted,
   accepted_commuting_operators.binomial_mix_le_iter_accepted,
   accepted_commuting_operators.meet_avg_linear_accepted,
   accepted_commuting_operators.meet_avg_monotone_accepted,
   accepted_commuting_operators.meet_avg_cst_accepted,
   accepted_commuting_operators.meet_avgC_accepted,
   accepted_commuting_operators.iter_meet_avg_accepted,
   accepted_boolean_fourier.bchar_algebra_accepted,
   accepted_boolean_fourier.bchar_orthogonal_accepted,
   accepted_boolean_fourier.bchar_delta_accepted,
   accepted_boolean_fourier.blk_dist_metric_accepted,
   accepted_boolean_fourier.fcoef_inversion_accepted,
   accepted_boolean_fourier.fcoef_expansion_accepted,
   accepted_boolean_fourier.fcoef_plancherel_accepted,
   accepted_boolean_fourier.fcoef_linear_accepted,
   accepted_boolean_fourier.fcoef_comp_linear_accepted,
   accepted_boolean_fourier.fcoef_mulmx_accepted,
   accepted_boolean_fourier.fcoef_norm_le_accepted,
   accepted_boolean_fourier.fcoef_translate_accepted,
   accepted_boolean_fourier.low_blk_deg_expansion_accepted,
   accepted_boolean_fourier.low_blk_deg_translate_accepted,
   accepted_boolean_fourier.blk_dist_row_accepted,
   accepted_boolean_fourier.bchar_col_mx_accepted,
   accepted_boolean_fourier.blk_col_mx_accepted,
   accepted_boolean_fourier.fcoef_col_mx_accepted,
   accepted_psd_factorization.psd_factorization_ge0_accepted,
   accepted_psd_factorization.psd_factorization_size_gt0_accepted,
   accepted_psd_factorization.psd_factorization_restrict_accepted,
   accepted_psd_factorization.psd_factorization_widen_accepted,
   accepted_psd_factorization.psd_factorization_shift_accepted,
   accepted_psd_factorization.psd_factorization_nonneg_accepted,
   accepted_binomial_bounds.central_bin_le_accepted,
   accepted_binomial_bounds.central_bin_ge_accepted,
   accepted_binomial_bounds.half_bin_ge_accepted,
   accepted_binomial_bounds.leq_bin_half_accepted,
   accepted_binomial_bounds.bin_near_half_accepted,
   accepted_binomial_bounds.bin_sqr_central_accepted,
   accepted_binomial_bounds.bin_sqr_ratio_accepted,
   accepted_binomial_bounds.bin_partial_sum_accepted,
   accepted_psd_duality.psd_eval_cone_closed_accepted,
   accepted_psd_duality.psdmx_dual_accepted,
   accepted_psd_duality.psd_farkas_accepted,
   accepted_psd_duality.psd_slack_certificate_accepted,
   accepted_psd_duality.psd_slack_certificate_affine_accepted).

Print Assumptions library_statements_accepted.
