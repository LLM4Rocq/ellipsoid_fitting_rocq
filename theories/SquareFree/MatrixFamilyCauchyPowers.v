(* Matrix-family energy bounds and products used in column-power errors. *)
From Stdlib Require Import Reals List FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions
  Geometry.HeadCoefficients Geometry.HeadFrobenius Cone.ConditionOperator
  SquareFree.EdgeLower SquareFree.MatrixFamilyCauchy.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Definition pmfc_energy (I : finType) n (F : I -> 'M[R]_n) (u : 'cV[R]_n) : R :=
  \sum_i ((F i *m u)^T *m (F i *m u)) 0 0.
Definition pmfc_energy_bound (I : finType) n (F : I -> 'M[R]_n) b : Prop :=
  0 <= b /\ forall u, pmfc_energy I n F u <= b^+2*(u^T *m u) 0 0.

Lemma pmfc_energy_form (I : finType) n (F : I -> 'M[R]_n) u :
  pmfc_energy I n F u = (u^T *m (\sum_i (F i)^T *m F i) *m u) 0 0.
Proof.
rewrite /pmfc_energy mulmx_sumr mulmx_suml summxE.
apply: eq_bigr=>i _; by rewrite trmx_mul !mulmxA.
Qed.

Lemma pmfc_energy_bound_mul_left (I : finType) n (A B : I -> 'M[R]_n) a b :
  0 <= a -> (forall i, pmlo_opb n (A i) a) -> pmfc_energy_bound I n B b ->
  pmfc_energy_bound I n (fun i => A i *m B i) (a*b).
Proof.
move=> Ha HA [Hb HB]; split; first exact: mulr_ge0.
move=>u; apply: le_trans (_ : a^+2*pmfc_energy I n B u <= _).
- rewrite /pmfc_energy mulr_sumr; apply: ler_sum=>i _.
  rewrite -mulmxA; exact: (proj2 (HA i)).
- rewrite exprMn -[a^+2*b^+2*_]mulrA; apply: ler_wpM2l; first exact: sqr_ge0.
  exact: HB.
Qed.

Theorem pmfc_energy_bound_power (I : finType) n (F : I -> 'M[R]_n) b :
  (forall i, pmlo_opb n (F i) b) -> pmfc_energy_bound I n F b ->
  forall p, pmfc_energy_bound I n (fun i => (F i)^+p.+1) (b^+p.+1).
Proof.
move=> HF Hb; have Hb0 := proj1 Hb.
elim=>[|p IH]; first by rewrite !expr1.
have H := pmfc_energy_bound_mul_left I n F (fun i => (F i)^+p.+1) b (b^+p.+1) Hb0 HF IH.
rewrite -exprS in H.
have EE : (fun i => F i *m (F i)^+p.+1) = (fun i => (F i)^+p.+2).
{ apply: functional_extensionality=>i; rewrite [in RHS]exprS mulmxE.
  reflexivity. }
by rewrite EE in H.
Qed.

Theorem pmfc_energy_product (I : finType) n (A B : I -> 'M[R]_n) a b :
  pmfc_energy_bound I n (fun i => (A i)^T) a -> pmfc_energy_bound I n B b ->
  pmlo_opb n (\sum_i A i *m B i) (a*b).
Proof.
move=> [Ha HA] [Hb HB].
apply: (paper_main_family_matrix_opbound I n A B (a^+2) (b^+2) (a*b));
  try exact: sqr_ge0; try exact: mulr_ge0.
- by rewrite exprMn.
- move=>u; have H := HA u; rewrite pmfc_energy_form in H.
  have EE : (\sum_i ((A i)^T)^T *m (A i)^T) = \sum_i A i *m (A i)^T.
  { apply: eq_bigr=>i _; by rewrite trmxK. }
  by rewrite EE in H.
- move=>v; have H := HB v; by rewrite pmfc_energy_form in H.
Qed.

Lemma pmfc_vector_difference_bound n (u v : 'cV[R]_n) :
  ((u-v)^T *m (u-v)) 0 0 <= 2*(u^T *m u) 0 0+2*(v^T *m v) 0 0.
Proof.
rewrite !pmh_vec_dot !mulr_sumr -big_split /=.
apply: ler_sum=>i _; rewrite !mxE.
have H := sqr_ge0 (u i 0+v i 0); nra.
Qed.

Theorem pmfc_energy_bound_sub (I : finType) n (F G : I -> 'M[R]_n) a b c :
  pmfc_energy_bound I n F a -> pmfc_energy_bound I n G b ->
  0 <= c -> 2*a^+2+2*b^+2 <= c^+2 ->
  pmfc_energy_bound I n (fun i => F i-G i) c.
Proof.
move=> [Ha HF] [Hb HG] Hc Habc; split=>// u.
have H1 : pmfc_energy I n (fun i => F i-G i) u <=
  2*pmfc_energy I n F u+2*pmfc_energy I n G u.
{ rewrite /pmfc_energy !mulr_sumr -big_split /=.
  apply: ler_sum=>i _; rewrite mulmxBl; exact: pmfc_vector_difference_bound. }
apply: le_trans H1 _.
apply: le_trans (_ : 2*(a^+2*(u^T *m u) 0 0)+2*(b^+2*(u^T *m u) 0 0) <= _).
- apply: lerD; apply: ler_wpM2l; try exact: ler0n; [exact: HF|exact: HG].
- rewrite !mulrA -mulrDl; apply: ler_wpM2r; first exact: pmh_vec_sqr_ge0.
  by rewrite -!mulrA -!expr2.
Qed.

Lemma pmfc_opb_identity n : pmlo_opb n (1%:M : 'M[R]_n) 1.
Proof. split; first exact: ler01. by move=>v; rewrite mul1mx expr1n mul1r. Qed.
