(* The metric projection onto the positive semidefinite cone and the Moreau
   decomposition, for the public matrices and the Frobenius pairing: the
   geometric input of manuscript lem:psd-width and lem:widthcone (the
   positive part of a symmetric matrix), without the spectral theorem.

   For every Z : 'M[R]_d there is a PSD matrix P closest to Z in Frobenius
   distance (pmcp_projection_exists: a compact minimization over PSD S with
   <S, S> <= (2 |Z|_F)^2, inside a box, extended to the whole cone by the
   triangle inequality). It is characterized by the variational inequality
   <Z - P, S - P> <= 0 for all PSD S (pmcp_min_variational,
   pmcp_variational_min), hence unique (pmcp_variational_unique).
   paper_main_psd_projection Z chooses it. For symmetric Z:
   - Moreau decomposition: P = proj Z and N = P - Z are PSD with Z = P - N
     and <P, N> = 0 (paper_main_psd_moreau), and such a pair is unique
     (paper_main_psd_moreau_unique);
   - proj (-Z) = N (paper_main_psd_projection_opp);
   - |Z|_F^2 = |P|_F^2 + |N|_F^2 (paper_main_psd_moreau_norm).
   For all Z, Y: |proj Z - proj Y|_F <= |Z - Y|_F and
   | |proj Z|_F - |proj Y|_F | <= |Z - Y|_F. Every result holds for every d,
   including d = 0. Nothing from the paper is assumed. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryCompact PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadFeature PaperMainGeometryHeadSpectral
  PaperMainGeometryHeadWidthCompact.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ConeProjection.
Variable d : nat.
Local Notation V := 'rV[R]_(d * d).
Local Notation toS := (@vec_mx R d d).
Implicit Types (A B P N S X Y Z : 'M[R]_d) (v : V).

Lemma pmcp_sub_expand X Y :
  paper_main_pairing (X - Y) (X - Y) =
  paper_main_pairing X X - 2 * paper_main_pairing X Y + paper_main_pairing Y Y.
Proof. by rewrite pmh_pairingBl !pmh_pairingBr (paper_main_pairingC _ Y X); ring. Qed.

Lemma pmcp_psd0 : paper_main_psd (0 : 'M[R]_d).
Proof. by rewrite -(scale0r (1%:M : 'M[R]_d)); apply: pmh_psd_scalar. Qed.

(* Closed and compact sets of rows. *)
Lemma pmcp_psd_closed : closed [set v : V | paper_main_psd (toS v)].
Proof.
have -> : [set v : V | paper_main_psd (toS v)] =
    (\bigcap_(i : 'I_d) \bigcap_(j : 'I_d) [set v : V | toS v i j - toS v j i = 0]) `&`
    (\bigcap_(u : 'cV[R]_d) [set v : V | 0 <= paper_main_quadratic_form (toS v) u]).
  rewrite predeqE => v; split.
    move=> [Hsym Hpos]; split.
      by move=> i _ j _ /=; rewrite Hsym subrr.
    by move=> u _ /=; exact: Hpos.
  move=> [Hsym Hpos]; split.
    by move=> i j; apply/eqP; rewrite -subr_eq0; apply/eqP; exact: (Hsym i Logic.I j Logic.I).
  by move=> u; exact: (Hpos u Logic.I).
apply: closedI.
  apply: closed_bigI => i _; apply: closed_bigI => j _.
  by apply: pmg_closed_eq; apply: pmg_continuousB; exact: pmg_entry_continuous.
by apply: closed_bigI => u _; apply: pmg_closed_ge; exact: pmg_form_continuous.
Qed.

Lemma pmcp_dist_continuous Z :
  continuous (fun v : V => paper_main_pairing (Z - toS v) (Z - toS v)).
Proof.
rewrite /paper_main_pairing.
apply: pmg_continuous_sum => i; apply: pmg_continuous_sum => j.
have -> : (fun v : V => (Z - toS v) i j * (Z - toS v) i j) =
    (fun v : V => (Z i j - toS v i j) * (Z i j - toS v i j)).
  by apply/funext => v; rewrite !mxE.
by apply: pmg_continuousM; apply: pmg_continuousB;
  first [exact: pmg_continuous_cst | exact: pmg_entry_continuous].
Qed.

Lemma pmcp_sq_continuous : continuous (fun v : V => paper_main_pairing (toS v) (toS v)).
Proof.
rewrite /paper_main_pairing.
apply: pmg_continuous_sum => i; apply: pmg_continuous_sum => j.
by apply: pmg_continuousM; exact: pmg_entry_continuous.
Qed.

Definition pmcp_ball (r : R) : set V :=
  [set v : V | paper_main_psd (toS v) /\ paper_main_pairing (toS v) (toS v) <= r ^+ 2].

Lemma pmcp_ball_compact (r : R) : 0 <= r -> compact (pmcp_ball r).
Proof.
move=> Hr.
set box := [set v : V | forall k, `[-r, r]%classic (v 0 k)].
have Hbox : compact box.
  have H := @rV_compact R (d * d) (fun=> `[-r, r]%classic)
    (fun _ => @segment_compact _ (-r) r).
  exact: H.
have Hsub : pmcp_ball r `<=` box.
  move=> v [_ Hn] k; case: (mxvec_indexP k) => i j.
  have := pmhw_entry_sqr_le _ (toS v) i j; rewrite mxE => Hsq.
  by rewrite /= in_itv /=; apply/andP; split; nra.
have -> : pmcp_ball r = box `&` pmcp_ball r.
  by rewrite predeqE => v; split=> [Hv | [_ Hv]] //; split=> //; exact: Hsub.
apply: compact_closedI => //.
have -> : pmcp_ball r = [set v : V | paper_main_psd (toS v)] `&`
    [set v : V | 0 <= r ^+ 2 - paper_main_pairing (toS v) (toS v)].
  by rewrite predeqE => v; split => -[H1 H2]; split => //; move: H2; rewrite /= subr_ge0.
apply: closedI; first exact: pmcp_psd_closed.
apply: pmg_closed_ge; apply: pmg_continuousB; first exact: pmg_continuous_cst.
exact: pmcp_sq_continuous.
Qed.

(* Existence of a nearest PSD matrix. *)
Theorem pmcp_projection_exists Z :
  exists P, paper_main_psd P /\
    forall S, paper_main_psd S -> paper_main_pairing (Z - P) (Z - P) <=
                                  paper_main_pairing (Z - S) (Z - S).
Proof.
set r := 2 * paper_main_frobenius Z.
have HZ0 := pmh_frobenius_ge0 _ Z.
have Hr : 0 <= r by rewrite /r mulr_ge0 // ler0n.
have Hne : pmcp_ball r !=set0.
  exists (mxvec (0 : 'M[R]_d)); rewrite /pmcp_ball /= mxvecK; split; first exact: pmcp_psd0.
  by rewrite pmh_pairing0l sqr_ge0.
have Hf : {within pmcp_ball r,
    continuous (fun v : V => paper_main_pairing (Z - toS v) (Z - toS v))}.
  by apply: continuous_subspaceT; exact: pmcp_dist_continuous.
have [v0 Hv0 Hmin] := compact_EVT_min Hne (pmcp_ball_compact r Hr) Hf.
move: Hv0; rewrite in_setE => -[HP0 _].
have Hmin0 : paper_main_pairing (Z - toS v0) (Z - toS v0) <= paper_main_pairing Z Z.
  have := Hmin (mxvec (0 : 'M[R]_d)); rewrite mxvecK subr0; apply.
  rewrite in_setE /pmcp_ball /= mxvecK; split; first exact: pmcp_psd0.
  by rewrite pmh_pairing0l sqr_ge0.
exists (toS v0); split => // S HS.
have [Hb|Hb] := lerP (paper_main_pairing S S) (r ^+ 2).
  have := Hmin (mxvec S); rewrite mxvecK; apply.
  by rewrite in_setE; split; rewrite ?mxvecK.
have HS0 := pmh_frobenius_ge0 _ S.
have HSq := pmh_frobenius_sqr _ S.
have Hlt : r < paper_main_frobenius S by nra.
have Htri := pmh_frobenius_triangle _ (S - Z) Z.
rewrite subrK pmh_frobeniusB in Htri.
have HZS0 := pmh_frobenius_ge0 _ (Z - S).
have HZS := pmh_frobenius_sqr _ (Z - S).
have HZq := pmh_frobenius_sqr _ Z.
have Hge : paper_main_frobenius Z <= paper_main_frobenius (Z - S) by rewrite /r in Hlt; lra.
have : paper_main_pairing Z Z <= paper_main_pairing (Z - S) (Z - S) by nra.
lra.
Qed.

(* The variational characterization. *)
Theorem pmcp_min_variational Z P :
  paper_main_psd P ->
  (forall S, paper_main_psd S -> paper_main_pairing (Z - P) (Z - P) <=
                                 paper_main_pairing (Z - S) (Z - S)) ->
  forall S, paper_main_psd S -> paper_main_pairing (Z - P) (S - P) <= 0.
Proof.
move=> HP Hmin S HS.
have Ha := paper_main_pairing_self_ge0 _ (S - P).
have Hc : 0 <= - (2 * paper_main_pairing (Z - P) (S - P)).
  apply: (pms_variational _ _ Ha) => t Ht0 Ht1.
  have Hseg := pms_seg_psd _ _ _ _ (ltW Ht0) Ht1 HP HS.
  have := Hmin _ Hseg.
  have -> : Z - (P + t *: (S - P)) = (Z - P) - t *: (S - P).
    by apply/matrixP => i j; rewrite !mxE; ring.
  rewrite (pmcp_sub_expand (Z - P) (t *: (S - P))) paper_main_pairing_scale pmh_pairingZl.
  rewrite paper_main_pairing_scale => H; lra.
lra.
Qed.

Theorem pmcp_variational_unique Z P1 P2 :
  paper_main_psd P1 -> paper_main_psd P2 ->
  (forall S, paper_main_psd S -> paper_main_pairing (Z - P1) (S - P1) <= 0) ->
  (forall S, paper_main_psd S -> paper_main_pairing (Z - P2) (S - P2) <= 0) ->
  P1 = P2.
Proof.
move=> H1 H2 V1 V2.
have A1 := V1 P2 H2; have A2 := V2 P1 H1.
have E12 : P1 - P2 = - (P2 - P1) by rewrite opprB.
rewrite E12 pmh_pairingNr in A2.
have E : paper_main_pairing (Z - P1) (P2 - P1) - paper_main_pairing (Z - P2) (P2 - P1) =
    paper_main_pairing (P2 - P1) (P2 - P1).
  rewrite -pmh_pairingBl.
  have -> : Z - P1 - (Z - P2) = P2 - P1 by apply/matrixP => i j; rewrite !mxE; ring.
  done.
have Hle : paper_main_pairing (P2 - P1) (P2 - P1) <= 0 by lra.
have H0 : paper_main_pairing (P2 - P1) (P2 - P1) = 0.
  by apply/eqP; rewrite eq_le Hle paper_main_pairing_self_ge0.
have := paper_main_pairing_self_eq0 _ _ H0.
by move/eqP; rewrite subr_eq0 => /eqP.
Qed.

(* The projection onto the PSD cone. *)
Definition paper_main_psd_projection Z : 'M[R]_d :=
  projT1 (cid (pmcp_projection_exists Z)).

Lemma paper_main_psd_projection_spec Z :
  paper_main_psd (paper_main_psd_projection Z) /\
  forall S, paper_main_psd S ->
    paper_main_pairing (Z - paper_main_psd_projection Z) (Z - paper_main_psd_projection Z) <=
    paper_main_pairing (Z - S) (Z - S).
Proof. exact: (projT2 (cid (pmcp_projection_exists Z))). Qed.

Lemma paper_main_psd_projection_psd Z : paper_main_psd (paper_main_psd_projection Z).
Proof. by case: (paper_main_psd_projection_spec Z). Qed.

Theorem paper_main_psd_projection_variational Z S :
  paper_main_psd S ->
  paper_main_pairing (Z - paper_main_psd_projection Z) (S - paper_main_psd_projection Z) <= 0.
Proof.
have [HP Hmin] := paper_main_psd_projection_spec Z.
exact: pmcp_min_variational.
Qed.

Theorem paper_main_psd_projection_unique Z P :
  paper_main_psd P ->
  (forall S, paper_main_psd S -> paper_main_pairing (Z - P) (S - P) <= 0) ->
  P = paper_main_psd_projection Z.
Proof.
move=> HP HV; apply: (pmcp_variational_unique _ _ _ HP (paper_main_psd_projection_psd Z) HV).
exact: paper_main_psd_projection_variational.
Qed.

(* The Moreau decomposition. *)
Definition paper_main_psd_negative_part Z : 'M[R]_d := paper_main_psd_projection Z - Z.

Theorem paper_main_psd_moreau Z :
  paper_main_symmetric Z ->
  [/\ paper_main_psd (paper_main_psd_projection Z),
      paper_main_psd (paper_main_psd_negative_part Z),
      Z = paper_main_psd_projection Z - paper_main_psd_negative_part Z &
      paper_main_pairing (paper_main_psd_projection Z) (paper_main_psd_negative_part Z) = 0].
Proof.
move=> HZ.
have HP := paper_main_psd_projection_psd Z.
have HV := paper_main_psd_projection_variational Z.
set P := paper_main_psd_projection Z in HP HV *.
have Horth : paper_main_pairing (Z - P) P = 0.
  have h0 := HV 0 pmcp_psd0.
  rewrite sub0r pmh_pairingNr in h0.
  have h2 := HV (2%:R *: P) (paper_main_psd_scale _ _ _ (ler0n _ 2) HP).
  have E2 : 2%:R *: P - P = P by rewrite scaler_nat mulr2n addrK.
  rewrite E2 in h2.
  by apply/eqP; rewrite eq_le h2 -oppr_le0 h0.
split => //.
- split; first by apply: pmh_symmetricB => //; case: HP.
  move=> w.
  have Hw := HV (P + w *m w^T) (pms_psd_add _ _ _ HP (paper_main_psd_rank1 _ w)).
  rewrite (addrC P (w *m w^T)) addrK paper_main_pairing_outer in Hw.
  rewrite /paper_main_psd_negative_part -/P.
  have -> : P - Z = - (Z - P) by rewrite opprB.
  by rewrite pmh_formN oppr_ge0.
- by rewrite /paper_main_psd_negative_part opprB addrC subrK.
- rewrite /paper_main_psd_negative_part.
  have -> : P - Z = - (Z - P) by rewrite opprB.
  by rewrite pmh_pairingNr paper_main_pairingC Horth oppr0.
Qed.

Theorem paper_main_psd_moreau_unique Z P N :
  paper_main_psd P -> paper_main_psd N -> Z = P - N -> paper_main_pairing P N = 0 ->
  P = paper_main_psd_projection Z /\ N = paper_main_psd_negative_part Z.
Proof.
move=> HP HN HZ Horth.
have HV : forall S, paper_main_psd S -> paper_main_pairing (Z - P) (S - P) <= 0.
  move=> S HS.
  have -> : Z - P = - N by rewrite HZ; apply/matrixP => i j; rewrite !mxE; ring.
  rewrite pmh_pairingNl pmh_pairingBr (paper_main_pairingC _ N P) Horth subr0 oppr_le0.
  exact: pmh_pairing_psd_ge0.
have HPe := paper_main_psd_projection_unique _ _ HP HV.
split => //.
rewrite /paper_main_psd_negative_part -HPe HZ.
by apply/matrixP => i j; rewrite !mxE; ring.
Qed.

Theorem paper_main_psd_projection_opp Z :
  paper_main_symmetric Z ->
  paper_main_psd_projection (- Z) = paper_main_psd_negative_part Z.
Proof.
move=> HZ.
have [HP HN HZd Horth] := paper_main_psd_moreau _ HZ.
have Hm : - Z = paper_main_psd_negative_part Z - paper_main_psd_projection Z.
  by rewrite {1}HZd opprB.
have Ho : paper_main_pairing (paper_main_psd_negative_part Z) (paper_main_psd_projection Z) = 0.
  by rewrite paper_main_pairingC.
by have [<- _] := paper_main_psd_moreau_unique _ _ _ HN HP Hm Ho.
Qed.

Theorem paper_main_psd_moreau_norm Z :
  paper_main_symmetric Z ->
  paper_main_pairing Z Z =
  paper_main_pairing (paper_main_psd_projection Z) (paper_main_psd_projection Z) +
  paper_main_pairing (paper_main_psd_negative_part Z) (paper_main_psd_negative_part Z).
Proof.
move=> HZ.
have [_ _ HZd Horth] := paper_main_psd_moreau _ HZ.
by rewrite {1 2}HZd pmcp_sub_expand Horth mulr0 subr0.
Qed.

Corollary paper_main_psd_moreau_frobenius Z :
  paper_main_symmetric Z ->
  paper_main_frobenius Z ^+ 2 =
  paper_main_frobenius (paper_main_psd_projection Z) ^+ 2 +
  paper_main_frobenius (paper_main_psd_negative_part Z) ^+ 2.
Proof. by move=> HZ; rewrite !pmh_frobenius_sqr; exact: paper_main_psd_moreau_norm. Qed.

(* The projection and its norm are 1-Lipschitz. *)
Theorem paper_main_psd_projection_lipschitz Z Y :
  paper_main_frobenius (paper_main_psd_projection Z - paper_main_psd_projection Y) <=
  paper_main_frobenius (Z - Y).
Proof.
set P := paper_main_psd_projection Z; set Q := paper_main_psd_projection Y.
have V1 := paper_main_psd_projection_variational Z _ (paper_main_psd_projection_psd Y).
have V2 := paper_main_psd_projection_variational Y _ (paper_main_psd_projection_psd Z).
rewrite -/P -/Q in V1 V2.
have EQP : Q - P = - (P - Q) by rewrite opprB.
rewrite EQP pmh_pairingNr in V1.
have E : paper_main_pairing (P - Q) (P - Q) =
    paper_main_pairing (Z - Y) (P - Q) - paper_main_pairing (Z - P) (P - Q) +
    paper_main_pairing (Y - Q) (P - Q).
  rewrite -pmh_pairingBl -pmh_pairingDl.
  have -> : Z - Y - (Z - P) + (Y - Q) = P - Q by apply/matrixP => i j; rewrite !mxE; ring.
  done.
have Hle : paper_main_pairing (P - Q) (P - Q) <= paper_main_pairing (Z - Y) (P - Q) by lra.
have CS := pmh_pairing_frobenius_bound _ (Z - Y) (P - Q).
have Hn := ler_norm (paper_main_pairing (Z - Y) (P - Q)).
have Hx := pmh_frobenius_sqr _ (P - Q).
have Hx0 := pmh_frobenius_ge0 _ (P - Q).
have Hz0 := pmh_frobenius_ge0 _ (Z - Y).
nra.
Qed.

Corollary paper_main_psd_projection_norm_lipschitz Z Y :
  `|paper_main_frobenius (paper_main_psd_projection Z) -
    paper_main_frobenius (paper_main_psd_projection Y)| <= paper_main_frobenius (Z - Y).
Proof.
have H := pmh_frobenius_reverse_triangle _ (paper_main_psd_projection Y)
  (paper_main_psd_projection Z - paper_main_psd_projection Y).
rewrite (addrC (paper_main_psd_projection Y)) subrK in H.
exact: le_trans H (paper_main_psd_projection_lipschitz Z Y).
Qed.

End ConeProjection.
