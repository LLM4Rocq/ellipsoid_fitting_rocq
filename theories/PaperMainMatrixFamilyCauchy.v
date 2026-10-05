(* Finite matrix-family Cauchy bounds for non-backtracking remainder words. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadFrobenius PaperMainConeConditionOperator PaperMainSquarefreeEdgeLower
  PaperMainSymmetricDiagonalization.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma paper_main_family_scalar_cauchy (I : finType) (a b : I -> R) :
  (\sum_i a i*b i)^+2 <= (\sum_i (a i)^+2)*(\sum_i (b i)^+2).
Proof.
have Efg (f g : I -> R) :
  (((\col_i f (enum_val i)) : 'cV[R]_#|I|)^T *m (\col_i g (enum_val i))) 0 0 =
  \sum_i f i*g i.
{ rewrite pmh_vec_dot.
  under eq_bigr do rewrite !mxE.
  rewrite (big_enum_val (fun i : I => f i*g i)).
  reflexivity. }
have EE (f : I -> R) : (\sum_i f i*f i) = \sum_i (f i)^+2.
{ apply: eq_bigr=>i _; by rewrite expr2. }
have H := pmco_vec_cauchy_schwarz #|I| (\col_i a (enum_val i)) (\col_i b (enum_val i)).
by rewrite !Efg !EE in H.
Qed.

Lemma paper_main_family_vector_cauchy (I : finType) n (a b : I -> 'cV[R]_n) :
  (\sum_c ((a c)^T *m b c) 0 0)^+2 <=
    (\sum_c ((a c)^T *m a c) 0 0)*(\sum_c ((b c)^T *m b c) 0 0).
Proof.
have H := paper_main_family_scalar_cauchy [the finType of (I * 'I_n)%type]
  (fun p => a p.1 p.2 0) (fun p => b p.1 p.2 0).
have Ep (f : I -> 'I_n -> R) :
  (\sum_p f p.1 p.2) = \sum_c \sum_i f c i.
{ by rewrite pair_bigA. }
rewrite (Ep (fun c i => a c i 0*b c i 0))
  (Ep (fun c i => (a c i 0)^+2)) (Ep (fun c i => (b c i 0)^+2)) in H.
have Eab (f g : I -> 'cV[R]_n) :
  (\sum_c \sum_(i<n) f c i 0*g c i 0) = \sum_c ((f c)^T *m g c) 0 0.
{ apply: eq_bigr=>c _; by rewrite pmh_vec_dot. }
have Es (f : I -> 'cV[R]_n) :
  (\sum_c \sum_(i<n) (f c i 0)^+2) = \sum_c ((f c)^T *m f c) 0 0.
{ apply: eq_bigr=>c _; rewrite pmh_vec_dot; apply: eq_bigr=>i _; by rewrite expr2. }
by rewrite Eab !Es in H.
Qed.

Lemma paper_main_family_product_form (I : finType) n (A B : I -> 'M[R]_n) (u v : 'cV[R]_n) :
  (\sum_c (((A c)^T *m u)^T *m (B c *m v)) 0 0) =
  (u^T *m (\sum_c A c *m B c) *m v) 0 0.
Proof.
rewrite mulmx_sumr mulmx_suml summxE.
apply: eq_bigr=>c _; by rewrite trmx_mul trmxK !mulmxA.
Qed.

Theorem paper_main_family_matrix_cauchy (I : finType) n (A B : I -> 'M[R]_n) (u v : 'cV[R]_n) :
  ((u^T *m (\sum_c A c *m B c) *m v) 0 0)^+2 <=
    (u^T *m (\sum_c A c *m (A c)^T) *m u) 0 0 *
    (v^T *m (\sum_c (B c)^T *m B c) *m v) 0 0.
Proof.
have H := paper_main_family_vector_cauchy I n (fun c => (A c)^T *m u) (fun c => B c *m v).
rewrite !paper_main_family_product_form in H.
have EB : (\sum_c ((B c *m v)^T *m (B c *m v)) 0 0) =
  (v^T *m (\sum_c (B c)^T *m B c) *m v) 0 0.
{ rewrite mulmx_sumr mulmx_suml summxE.
  apply: eq_bigr=>c _; by rewrite trmx_mul !mulmxA. }
by rewrite EB in H.
Qed.

Theorem paper_main_opnorm_to_action n (M : 'M[R]_n) c :
  0 <= c -> paper_main_cone_opnorm_le M c -> pmlo_opb n M c.
Proof.
by move=> c0 /paper_main_cone_opnorm_leP; rewrite ger0_norm // => Mc; apply/pmlo_opbP.
Qed.

Lemma paper_main_family_energy_nonnegative (I : finType) n
    (A : I -> 'M[R]_n) (u : 'cV[R]_n) :
  0 <= (u^T *m (\sum_c A c *m (A c)^T) *m u) 0 0.
Proof.
rewrite -(paper_main_family_product_form I n A (fun c => (A c)^T) u u).
apply: sumr_ge0=>c _; exact: pmh_vec_sqr_ge0.
Qed.

Theorem paper_main_family_matrix_opbound (I : finType) n
    (A B : I -> 'M[R]_n) a b c :
  0 <= a -> 0 <= b -> 0 <= c -> a*b <= c^+2 ->
  (forall u : 'cV[R]_n,
    (u^T *m (\sum_i A i *m (A i)^T) *m u) 0 0 <= a*(u^T *m u) 0 0) ->
  (forall v : 'cV[R]_n,
    (v^T *m (\sum_i (B i)^T *m B i) *m v) 0 0 <= b*(v^T *m v) 0 0) ->
  pmlo_opb n (\sum_i A i *m B i) c.
Proof.
move=> Ha Hb Hc Habc HA HB; apply: paper_main_opnorm_to_action=>// u v.
apply: le_trans (paper_main_family_matrix_cauchy I n A B u v) _.
have Hu := pmh_vec_sqr_ge0 n u.
have Hv := pmh_vec_sqr_ge0 n v.
have EA := paper_main_family_energy_nonnegative I n A u.
have EB := paper_main_family_energy_nonnegative I n (fun i => (B i)^T) v.
have EE : (\sum_i (B i)^T *m ((B i)^T)^T) = \sum_i (B i)^T *m B i.
{ apply: eq_bigr=>i _; by rewrite trmxK. }
rewrite EE in EB.
apply: le_trans (ler_pM EA EB (HA u) (HB v)) _.
have -> : a*(u^T *m u) 0 0*(b*(v^T *m v) 0 0) =
  (a*b)*((u^T *m u) 0 0*(v^T *m v) 0 0) by ring.
by apply: ler_wpM2r; first exact: mulr_ge0.
Qed.
