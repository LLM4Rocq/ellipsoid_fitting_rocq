(* Finite soft minimax on contained nets and the compact head-section
   minimax of PaperMainHeadSectionMinimax. Write
     f(y, S) = <sum_(i < q) y_i V_i, S>,
     minimax = inf_(y in Y) sup_(S in section) f(y, S),
   with the actual section paper_main_head_section kappa W and the actual
   linear map y |-> sum_(i < q) y_i V_i. Hypotheses, all explicit:
   - an upper operator bound |sum_(i < q) y_i V_i|_F <= L |y|_2 for every y
     (paper_main_head_section_operator_bound q V L, which includes 0 <= L);
   - Y is nonempty and z is a dual eps-net of Y contained in Y
     (paper_main_gordon_finite_net q Y z (seq 0 r) eps);
   - B t lies in the section for t < s, and s > 0.
   Then, for beta, gamma > 0,
     finite_minimax f(z, B) - L eps <= minimax,
     soft_minimax beta gamma f(z, B) - ln s / gamma - L eps <= minimax.
   The dual net error is L eps, not eps sum_i |V_i|_F, and the soft-max
   entropy error is ln s / gamma. No unit hypothesis on Y is used here.
   A Frobenius eps'-net B of the section contained in the section
   (paper_main_head_section_net) approximates every support:
     0 <= support Z - max_t <Z, B t> <= eps' |Z|_F.
   If moreover Y consists of unit vectors for paper_main_gordon_dot q, the
   points z a (a < r) lie in Y and B is such a net, then
     minimax <= finite_minimax f(z, B) + L eps'
             <= soft_minimax beta gamma f(z, B) + ln r / beta + L eps'.
   Empty cases are separate lemmas: the minimax is 0 for an empty Y (the
   infimum of the empty set), and also for an empty section (every support
   is 0). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadWidth
  PaperMainGordonProcessCovariance PaperMainGordonBilinear PaperMainGordonNets
  PaperMainHeadSectionMeasurable PaperMainHeadSectionMinimax.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope R_scope.

(* Scalar facts, stated with the standard real operations. *)

Lemma paper_main_head_section_euclidean_le q (u : nat -> R) (eps : R) :
  0 <= eps -> paper_main_gordon_dot q u u <= eps ^ 2 ->
  euclidean_norm u (List.seq 0 q) <= eps.
Proof.
intros He Hd.
pose proof (paper_main_gordon_euclidean_squared q u) as H2.
assert (H0 : 0 <= euclidean_norm u (List.seq 0 q)) by apply sqrt_pos.
nra.
Qed.

Lemma paper_main_head_section_euclidean_unit q (u : nat -> R) :
  paper_main_gordon_dot q u u = 1 -> euclidean_norm u (List.seq 0 q) = 1.
Proof.
intros H1; unfold euclidean_norm.
rewrite paper_main_gordon_squared_norm_dot H1; exact sqrt_1.
Qed.

Local Open Scope ring_scope.

Lemma paper_main_head_section_seq_ne (s : nat) : (0 < s)%N -> List.seq 0 s <> nil.
Proof. by case: s. Qed.

(* The operator bound and contained section nets. *)

Definition paper_main_head_section_operator_bound {d : nat} (q : nat) (V : nat -> 'M[R]_d)
    (L : R) : Prop :=
  0 <= L /\ forall y : nat -> R,
    paper_main_frobenius (paper_main_head_section_combination q y V) <=
      L * euclidean_norm y (List.seq 0 q).

Definition paper_main_head_section_net {d m : nat} (kappa : R) (W : 'I_m -> 'M[R]_d)
    (B : nat -> 'M[R]_d) (s : nat) (eps : R) : Prop :=
  (forall t, (t < s)%N -> paper_main_head_section kappa W (B t)) /\
  (forall P, paper_main_head_section kappa W P ->
    exists t, (t < s)%N /\ paper_main_frobenius (P - B t) <= eps).

(* Linearity of the combination and the dual net error L eps. *)

Lemma paper_main_head_section_combinationB {d : nat} q (y y' : nat -> R)
    (V : nat -> 'M[R]_d) :
  paper_main_head_section_combination q y V - paper_main_head_section_combination q y' V =
  paper_main_head_section_combination q (fun i => Rminus (y i) (y' i)) V.
Proof.
rewrite /paper_main_head_section_combination -sumrB.
by apply: eq_bigr => i _; rewrite RminusE scalerBl.
Qed.

Lemma paper_main_head_section_dual_error {d : nat} q (V : nat -> 'M[R]_d) (L eps : R)
    (y y' : nat -> R) :
  paper_main_head_section_operator_bound q V L -> 0 <= eps ->
  Rle (paper_main_gordon_dot q (fun i => Rminus (y i) (y' i)) (fun i => Rminus (y i) (y' i)))
    (pow eps 2%N) ->
  paper_main_frobenius (paper_main_head_section_combination q y V -
    paper_main_head_section_combination q y' V) <= L * eps.
Proof.
move=> [HL HV] He Hd.
rewrite paper_main_head_section_combinationB.
apply: le_trans (HV _) _; apply: (ler_wpM2l HL).
have He' : Rle 0 eps by apply/RleP.
by apply/RleP; apply: paper_main_head_section_euclidean_le.
Qed.

(* A contained finite family and a Frobenius net of the section. *)

Lemma paper_main_head_section_net_max_le {d m : nat} (kappa : R) (W : 'I_m -> 'M[R]_d)
    (B : nat -> 'M[R]_d) (s : nat) (Z : 'M[R]_d) :
  (0 < s)%N -> (forall t, (t < s)%N -> paper_main_head_section kappa W (B t)) ->
  finite_max (fun t => paper_main_pairing Z (B t)) (List.seq 0 s) <=
    paper_main_head_support Z (paper_main_head_section kappa W).
Proof.
move=> Hs HB.
have Hne := paper_main_head_section_seq_ne s Hs.
apply/RleP; apply: finite_max_upper => // t Ht.
apply/RleP; apply: (pmh_support_ge _ Z _ (B t) (@paper_main_head_section_unit d m kappa W)).
by apply: HB; apply/paper_main_head_section_seq_lt.
Qed.

Lemma paper_main_head_section_net_support_le {d m : nat} (kappa : R) (W : 'I_m -> 'M[R]_d)
    (B : nat -> 'M[R]_d) (s : nat) (eps : R) (Z : 'M[R]_d) :
  (0 < s)%N -> paper_main_head_section_net kappa W B s eps ->
  paper_main_head_support Z (paper_main_head_section kappa W) <=
    finite_max (fun t => paper_main_pairing Z (B t)) (List.seq 0 s) +
    eps * paper_main_frobenius Z.
Proof.
move=> Hs [HB Hcov].
have HB0 := HB 0%N Hs.
apply: ge_sup; first by exists (paper_main_pairing Z (B 0%N)), (B 0%N).
move=> _ [P HP <-].
have [t [Ht HPt]] := Hcov P HP.
have -> : paper_main_pairing Z P = paper_main_pairing Z (B t) + paper_main_pairing Z (P - B t).
  by rewrite pmh_pairingBr addrC subrK.
apply: lerD.
  apply/RleP; apply: (finite_max_member (fun t => paper_main_pairing Z (B t))).
  exact/paper_main_head_section_seq_lt.
apply: le_trans (ler_norm _) _.
apply: le_trans (pmh_pairing_frobenius_bound _ Z (P - B t)) _.
rewrite [X in X <= _]mulrC; apply: ler_wpM2r; [exact: pmh_frobenius_ge0 | exact: HPt].
Qed.

(* The lower bounds: hard and soft. *)

Lemma paper_main_head_section_net_point {d m : nat} (kappa : R) q (Y : (nat -> R) -> Prop)
    (W : 'I_m -> 'M[R]_d) (V : nat -> 'M[R]_d) (L eps : R) (r s : nat)
    (z : nat -> nat -> R) (B : nat -> 'M[R]_d) (y : nat -> R) :
  (0 < s)%N -> 0 <= eps -> paper_main_head_section_operator_bound q V L ->
  paper_main_gordon_finite_net q Y z (List.seq 0 r) eps ->
  (forall t, (t < s)%N -> paper_main_head_section kappa W (B t)) -> Y y ->
  finite_minimax
    (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
    (List.seq 0 r) (List.seq 0 s) - L * eps <=
  paper_main_head_support (paper_main_head_section_combination q y V)
    (paper_main_head_section kappa W).
Proof.
move=> Hs He HV [_ Hcov] HB Hy.
have Hsec : exists P, paper_main_head_section kappa W P by exists (B 0%N); exact: HB.
have [a [Ha Hda]] := Hcov y Hy.
have H1 : finite_minimax
    (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
    (List.seq 0 r) (List.seq 0 s) <=
  finite_max (fun t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
    (List.seq 0 s).
  apply/RleP; rewrite /finite_minimax.
  exact: (finite_min_member (fun a => finite_max (fun t =>
    paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t)) (List.seq 0 s))
    _ a Ha).
have H2 := paper_main_head_section_net_max_le kappa W B s
  (paper_main_head_section_combination q (z a) V) Hs HB.
have H3 := paper_main_head_section_support_le kappa W
  (paper_main_head_section_combination q (z a) V) (paper_main_head_section_combination q y V) Hsec.
have H4 : paper_main_frobenius (paper_main_head_section_combination q (z a) V -
    paper_main_head_section_combination q y V) <= L * eps.
  rewrite pmh_frobeniusB.
  exact: (paper_main_head_section_dual_error q V L eps y (z a) HV He Hda).
rewrite lerBlDr.
apply: le_trans H1 _; apply: le_trans H2 _; apply: le_trans H3 _.
by rewrite lerD2l.
Qed.

Theorem paper_main_head_section_net_minimax_lower {d m : nat} (kappa : R) q
    (Y : (nat -> R) -> Prop) (W : 'I_m -> 'M[R]_d) (V : nat -> 'M[R]_d) (L eps : R)
    (r s : nat) (z : nat -> nat -> R) (B : nat -> 'M[R]_d) :
  (exists y, Y y) -> (0 < s)%N -> 0 <= eps -> paper_main_head_section_operator_bound q V L ->
  paper_main_gordon_finite_net q Y z (List.seq 0 r) eps ->
  (forall t, (t < s)%N -> paper_main_head_section kappa W (B t)) ->
  finite_minimax
    (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
    (List.seq 0 r) (List.seq 0 s) - L * eps <=
  paper_main_head_section_minimax kappa q Y W V.
Proof.
move=> [y0 Hy0] Hs He HV Hz HB.
apply: lb_le_inf.
  by exists (paper_main_head_support (paper_main_head_section_combination q y0 V)
    (paper_main_head_section kappa W)), y0.
move=> _ [y Hy <-].
exact: (paper_main_head_section_net_point kappa q Y W V L eps r s z B y Hs He HV Hz HB Hy).
Qed.

Theorem paper_main_head_section_soft_minimax_lower {d m : nat} (kappa : R) q
    (Y : (nat -> R) -> Prop) (W : 'I_m -> 'M[R]_d) (V : nat -> 'M[R]_d)
    (L eps beta gamma : R) (r s : nat) (z : nat -> nat -> R) (B : nat -> 'M[R]_d) :
  (exists y, Y y) -> (0 < s)%N -> 0 <= eps -> 0 < beta -> 0 < gamma ->
  paper_main_head_section_operator_bound q V L ->
  paper_main_gordon_finite_net q Y z (List.seq 0 r) eps ->
  (forall t, (t < s)%N -> paper_main_head_section kappa W (B t)) ->
  soft_minimax beta gamma
    (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
    (List.seq 0 r) (List.seq 0 s) - ln (INR s) / gamma - L * eps <=
  paper_main_head_section_minimax kappa q Y W V.
Proof.
move=> HY Hs He Hb Hg HV Hz HB.
have Hr := paper_main_gordon_net_nonempty q Y z (List.seq 0 r) eps HY Hz.
have Hsne := paper_main_head_section_seq_ne s Hs.
have Hb' : Rlt 0 beta by apply/RltP.
have Hg' : Rlt 0 gamma by apply/RltP.
have [_ Hup] := soft_minimax_bounds beta gamma
  (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
  (List.seq 0 r) (List.seq 0 s) Hb' Hg' Hr Hsne.
rewrite List.length_seq in Hup.
apply: le_trans (paper_main_head_section_net_minimax_lower kappa q Y W V L eps r s z B
  HY Hs He HV Hz HB).
rewrite lerD2r lerBlDr.
by apply/RleP; rewrite RplusE RdivE in Hup.
Qed.

(* The upper bounds, for unit dual points and a Frobenius net of the section. *)

Theorem paper_main_head_section_net_minimax_upper {d m : nat} (kappa : R) q
    (Y : (nat -> R) -> Prop) (W : 'I_m -> 'M[R]_d) (V : nat -> 'M[R]_d) (L eps : R)
    (r s : nat) (z : nat -> nat -> R) (B : nat -> 'M[R]_d) :
  (forall y, Y y -> paper_main_gordon_dot q y y = 1) -> (0 < r)%N -> (0 < s)%N ->
  paper_main_head_section_operator_bound q V L ->
  (forall a, List.In a (List.seq 0 r) -> Y (z a)) ->
  paper_main_head_section_net kappa W B s eps ->
  paper_main_head_section_minimax kappa q Y W V <=
  finite_minimax
    (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
    (List.seq 0 r) (List.seq 0 s) + L * eps.
Proof.
move=> HU Hr Hs [HL HV] Hz Hnet.
have [HB Hcov] := Hnet.
have He : 0 <= eps.
  have [t [_ Ht]] := Hcov (B 0%N) (HB 0%N Hs).
  exact: le_trans (pmh_frobenius_ge0 _ _) Ht.
have Hrne := paper_main_head_section_seq_ne r Hr.
have [a [Ha Heq]] := finite_min_attained (fun a => finite_max (fun t =>
  paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t)) (List.seq 0 s))
  _ Hrne.
rewrite /finite_minimax Heq.
have Hnorm : forall y, Y y ->
    paper_main_frobenius (paper_main_head_section_combination q y V) <= L.
  move=> y Hy; apply: le_trans (HV y) _.
  by rewrite (paper_main_head_section_euclidean_unit q y (HU y Hy)) mulr1.
set E := [set paper_main_head_support (paper_main_head_section_combination q y V)
  (paper_main_head_section kappa W) | y in Y].
have Hlb : lbound E (- L).
  move=> _ [y Hy <-].
  have := paper_main_head_section_support_bound kappa W
    (paper_main_head_section_combination q y V).
  rewrite ler_norml => /andP [H1 _].
  apply: le_trans H1; rewrite lerN2; exact: Hnorm.
have HEa : E (paper_main_head_support (paper_main_head_section_combination q (z a) V)
    (paper_main_head_section kappa W)) by exists (z a); first exact: Hz.
have H1 : paper_main_head_section_minimax kappa q Y W V <=
    paper_main_head_support (paper_main_head_section_combination q (z a) V)
      (paper_main_head_section kappa W).
  rewrite /paper_main_head_section_minimax -/E.
  exact: (ge_inf (ex_intro _ (- L) Hlb) HEa).
apply: le_trans H1 _.
apply: le_trans (paper_main_head_section_net_support_le kappa W B s eps _ Hs Hnet) _.
rewrite lerD2l [X in X <= _]mulrC; apply: ler_wpM2r; first exact: He.
exact: Hnorm (Hz a Ha).
Qed.

Theorem paper_main_head_section_soft_minimax_upper {d m : nat} (kappa : R) q
    (Y : (nat -> R) -> Prop) (W : 'I_m -> 'M[R]_d) (V : nat -> 'M[R]_d)
    (L eps beta gamma : R) (r s : nat) (z : nat -> nat -> R) (B : nat -> 'M[R]_d) :
  (forall y, Y y -> paper_main_gordon_dot q y y = 1) -> (0 < r)%N -> (0 < s)%N ->
  0 < beta -> 0 < gamma -> paper_main_head_section_operator_bound q V L ->
  (forall a, List.In a (List.seq 0 r) -> Y (z a)) ->
  paper_main_head_section_net kappa W B s eps ->
  paper_main_head_section_minimax kappa q Y W V <=
  soft_minimax beta gamma
    (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
    (List.seq 0 r) (List.seq 0 s) + ln (INR r) / beta + L * eps.
Proof.
move=> HU Hr Hs Hb Hg HV Hz Hnet.
have Hrne := paper_main_head_section_seq_ne r Hr.
have Hsne := paper_main_head_section_seq_ne s Hs.
have Hb' : Rlt 0 beta by apply/RltP.
have Hg' : Rlt 0 gamma by apply/RltP.
have [Hlow _] := soft_minimax_bounds beta gamma
  (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
  (List.seq 0 r) (List.seq 0 s) Hb' Hg' Hrne Hsne.
rewrite List.length_seq in Hlow.
apply: le_trans (paper_main_head_section_net_minimax_upper kappa q Y W V L eps r s z B
  HU Hr Hs HV Hz Hnet) _.
rewrite lerD2r -lerBlDr.
by apply/RleP; rewrite RminusE RdivE in Hlow.
Qed.

(* Empty cases. *)

Lemma paper_main_head_section_minimax_empty_dual {d m : nat} (kappa : R) q
    (Y : (nat -> R) -> Prop) (W : 'I_m -> 'M[R]_d) (V : nat -> 'M[R]_d) :
  ~ (exists y, Y y) -> paper_main_head_section_minimax kappa q Y W V = 0.
Proof.
move=> HY; rewrite /paper_main_head_section_minimax.
have -> : [set paper_main_head_support (paper_main_head_section_combination q y V)
    (paper_main_head_section kappa W) | y in Y] = set0.
  apply/seteqP; split=> x //.
  by case=> y Hy _; apply: HY; exists y.
exact: inf0.
Qed.
