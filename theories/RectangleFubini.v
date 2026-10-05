(* Fubini's theorem for a jointly continuous function on a rectangle, with
   the lemmas on parameter integrals that lead to it. This is the port of
   theories/RectangleFubini.v from Coquelicot to MathComp-Analysis.

   Translation of the vocabulary.
   - Coquelicot's continuity_2d_pt f x y becomes the definition of the same
     name in AnalysisIntegralDefinitions: continuity at (x, y) of
     p |-> f p.1 p.2 for the product topology of R * R. It says the same
     thing.
   - Coquelicot's pointwise continuity [continuous g x] becomes MathComp's
     {for x, continuous g} (difference 5 of analysis/README.md). It says the
     same thing.
   - Coquelicot's RInt g a b becomes oriented_integral g a b, and ex_RInt g a b
     becomes segment_integrable g a b (AnalysisIntegralDefinitions,
     difference 3 of analysis/README.md). The first is the oriented Lebesgue
     integral over the segment, the second is Lebesgue integrability on the
     segment, which includes Borel measurability. On a function continuous
     everywhere they agree with Coquelicot's Riemann notions. Such a function
     satisfies both integrability predicates. Its integrals agree too:
     Coquelicot's RInt_Reals equates RInt with Stdlib's RiemannInt, and a
     check compiled during the review of this port proved RiemannInt equal
     to oriented_integral on such a function, for either order of the end
     points. That check is not part of this module, because Stdlib's lemmas
     on RiemannInt add the axiom Classical_Prop.classic.
     Every function that the original lemmas integrate is continuous
     everywhere, with one exception: the slices f u in the hypothesis of
     rectangle_parameter_integral_derivative. There the meaning changes, as
     the comment above that lemma explains.
   - Coquelicot's is_derive g x l, for g : R -> R, becomes MathComp's
     @is_derive R R^o R^o x 1 g l: the derivative of g at x in the direction
     1 exists and equals l. Both are equivalent to Stdlib's
     derivable_pt_lim g x l: for Coquelicot this is its lemma
     is_derive_Reals, and for MathComp it is AnalysisBridge.is_derive_Reals,
     stated with the same convention as here. So the two say the same thing.
     A caller may need to write the types R R^o R^o, because R itself is not
     a normedModType.

   Every lemma of the original keeps its name, its argument order and its
   hypotheses, translated as above. The proofs differ. Continuity and
   differentiation of a parameter integral come from MathComp's
   continuity_under_integral and differentiation_under_integral, dominated
   by a constant, which exists because a jointly continuous function is
   bounded on a compact rectangle. The primitive and the final identity come
   from MathComp's fundamental theorems of calculus, continuous_FTC1 and
   continuous_FTC2, extended here to the oriented integral.

   The module adds helper lemmas for its own proofs and for the ports of the
   modules that import it.
   - continuity_2d_pt_mult, continuity_2d_pt_plus, continuity_2d_pt_minus,
     continuity_2d_pt_opp, continuity_2d_pt_const, continuity_2d_pt_id1,
     continuity_2d_pt_id2, continuity_2d_pt_ext, continuity_1d_2d_pt_comp
     and continuity_2d_pt_filterlim keep the names, the argument order and
     the statements of Coquelicot's lemmas on continuity_2d_pt. In the last
     one, Coquelicot's filterlim becomes MathComp's limit of a function.
   - The lemmas prefixed with rectangle_ give the boundedness of a jointly
     continuous function on a rectangle, the integrability of continuous
     functions on segments, and the rules of oriented_integral: point, swap,
     Chasles (for end points in any order), extension, scaling, sum,
     difference, opposite, constants, and the two fundamental theorems of
     calculus. *)

From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive realfun exp.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral ftc.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* Slices and transposition. *)

Lemma rectangle_continuous_slice_left (f : R -> R -> R) x y :
  continuity_2d_pt f x y -> {for x, continuous (fun u => f u y)}.
Proof.
move=> h.
have hp : {for x, continuous (fun u : R => (u, y))}.
  rewrite /prop_for /continuous_at.
  by apply: (@cvg_pair _ _ _ _ (nbhs x) (nbhs y)); [exact: cvg_id | exact: cvg_cst].
exact: (continuous_comp hp h).
Qed.

Lemma rectangle_continuous_slice_right (f : R -> R -> R) x y :
  continuity_2d_pt f x y -> {for y, continuous (fun v => f x v)}.
Proof.
move=> h.
have hp : {for y, continuous (fun v : R => (x, v))}.
  rewrite /prop_for /continuous_at.
  by apply: (@cvg_pair _ _ _ _ (nbhs x) (nbhs y)); [exact: cvg_cst | exact: cvg_id].
exact: (continuous_comp hp h).
Qed.

Lemma rectangle_continuous_transpose (f : R -> R -> R) x y :
  continuity_2d_pt f x y -> continuity_2d_pt (fun u v => f v u) y x.
Proof.
move=> h; rewrite /continuity_2d_pt.
exact: (continuous_comp (@swap_continuous R R (y, x)) h).
Qed.

(* Coquelicot's rules for continuity_2d_pt, with their names, argument order
   and statements. *)

Lemma continuity_2d_pt_mult (f g : R -> R -> R) x y :
  continuity_2d_pt f x y -> continuity_2d_pt g x y ->
  continuity_2d_pt (fun u v => f u v * g u v) x y.
Proof. by move=> hf hg; exact: (continuousM (K := R) hf hg). Qed.

Lemma continuity_2d_pt_id1 x y : continuity_2d_pt (fun u _ => u) x y.
Proof. exact: cvg_fst. Qed.

Lemma continuity_2d_pt_id2 x y : continuity_2d_pt (fun _ v => v) x y.
Proof. exact: cvg_snd. Qed.

(* The hypothesis on f is Stdlib's continuity_pt, as in Coquelicot. *)
Lemma continuity_1d_2d_pt_comp (f : R -> R) (g : R -> R -> R) x y :
  continuity_pt f (g x y) -> continuity_2d_pt g x y ->
  continuity_2d_pt (fun u v => f (g u v)) x y.
Proof. by move=> /continuity_ptE hf hg; exact: (continuous_comp hg hf). Qed.

(* Helpers: joint continuity, integrability on segments, bounds. *)

Lemma rectangle_joint_continuous (f : R -> R -> R) :
  (forall x y, continuity_2d_pt f x y) ->
  continuous (fun p : R * R => f p.1 p.2).
Proof. by move=> H [x y]; exact: H. Qed.

(* A continuous function is integrable on every segment. *)
Lemma rectangle_continuous_segment_integrable (g : R -> R) c d :
  continuous g -> segment_integrable g c d.
Proof.
move=> hg; rewrite /segment_integrable.
apply: continuous_compact_integrable; first exact: segment_compact.
exact/continuous_subspaceT.
Qed.

(* A jointly continuous function is bounded on every closed rectangle. *)
Lemma rectangle_bound (f : R -> R -> R) a b c d :
  (forall x y, continuity_2d_pt f x y) ->
  exists M, forall u v, a <= u <= b -> c <= v <= d -> Rabs (f u v) <= M.
Proof.
move=> H.
pose g := fun p : R * R => (f p.1 p.2 : R^o).
have cA : compact (`[a, b]%classic `*` `[c, d]%classic : set (R * R)).
  by apply: compact_setX; exact: segment_compact.
have cg : {within `[a, b]%classic `*` `[c, d]%classic, continuous g}.
  exact/continuous_subspaceT/rectangle_joint_continuous.
have /compact_bounded [M [_ HM]] := continuous_compact cg cA.
exists (M + 1) => u v hu hv.
have hM : (M < M + 1)%R by rewrite ltrDl ltr01.
have H2 : (g @` (`[a, b]%classic `*` `[c, d]%classic)) (f u v).
  exists (u, v) => //; split => /=; rewrite in_itv /=; apply/andP; split;
    apply/RleP; lra.
have /RleP := HM _ hM _ H2.
by rewrite RabsE.
Qed.

(* The oriented integral is a signed integral over the segment between the
   end points. *)
Lemma rectangle_oriented_integral_segment (g : R -> R) c d :
  oriented_integral g c d =
  (if Rle_dec c d then 1 else -1) *
  Rintegral lebesgue_measure `[Rmin c d, Rmax c d]%classic g.
Proof.
rewrite /oriented_integral; case: Rle_dec => h /=.
- by rewrite Rmin_left // Rmax_right // Rmult_1_l.
- rewrite Rmin_right ?Rmax_left; try lra; ring.
Qed.

Lemma rectangle_segment_memE (a b x : R) :
  `[a, b]%classic x -> a <= x <= b.
Proof. by rewrite /= in_itv /= => /andP [/RleP h1 /RleP h2]. Qed.

Lemma rectangle_open_mem (a b x : R) :
  `]a, b[%classic x -> a < x < b.
Proof. by rewrite /= in_itv /= => /andP [/RltP h1 /RltP h2]. Qed.

(* Integrals of slices and parameter integrals. *)

Lemma rectangle_slice_integrable (f : R -> R -> R) :
  (forall x y, continuity_2d_pt f x y) ->
  forall x c d, segment_integrable (f x) c d.
Proof.
move=> H x c d; apply: rectangle_continuous_segment_integrable => y.
exact: rectangle_continuous_slice_right.
Qed.

Lemma rectangle_parameter_integral_continuous (f : R -> R -> R) (c d x : R) :
  (forall u v, continuity_2d_pt f u v) ->
  {for x, continuous (fun u : R => oriented_integral (f u) c d)}.
Proof.
move=> H.
set s := (if Rle_dec c d then 1 else -1).
pose B := `[Rmin c d, Rmax c d]%classic : set R.
pose F := fun u => Rintegral lebesgue_measure B (f u).
have -> : (fun u => oriented_integral (f u) c d) = (fun u => s * F u).
  by apply/funext => u; rewrite rectangle_oriented_integral_segment.
have [M HM] := rectangle_bound f (x - 1) (x + 1) (Rmin c d) (Rmax c d) H.
pose l := x - 1; pose r := x + 1.
have hF : {in `]l, r[, continuous F}.
  apply: (@continuity_under_integral R _ _ lebesgue_measure f B _ l r _ _ (cst M)).
  - exact: measurable_itv.
  - by move=> u _; exact: rectangle_slice_integrable.
  - apply: aeW => v _ u _; exact: rectangle_continuous_slice_left.
  - apply: continuous_compact_integrable; first exact: segment_compact.
    exact/continuous_subspaceT/cst_continuous.
  - move=> u /rectangle_open_mem hu; apply: aeW => v /rectangle_segment_memE hv.
    apply/RleP; rewrite -RabsE; apply: HM; rewrite /l /r in hu; lra.
have hFx : {for x, continuous F}.
  apply: hF; apply/mem_set; rewrite /= in_itv /=; apply/andP; split;
    apply/RltP; rewrite /l /r; lra.
exact: (continuousM (@cst_continuous _ _ s x) hFx).
Qed.

(* This lemma changes meaning. Its slices f u need not be continuous, since
   only df is assumed jointly continuous. Its hypothesis
   segment_integrable (f u) c d is Lebesgue integrability on the segment,
   with Borel measurability, and it neither implies nor follows from
   Coquelicot's ex_RInt (f u) c d (difference 3 of analysis/README.md). The
   indicator of a subset of the Cantor set that is not a Borel set is
   Riemann integrable but not Borel measurable. The function
   v |-> / sqrt (Rabs v) on [-1, 1] is Lebesgue integrable but unbounded, so
   not Riemann integrable. The two hypotheses agree when the slices are
   continuous. The only use of the lemma here,
   rectangle_iterated_primitive_derivative, applies it to slices that are
   continuous everywhere, and no module of theories/ other than
   GaussianCoordinateProofs, which keeps its own copy, uses it. *)
Lemma rectangle_parameter_integral_derivative
  (f df : R -> R -> R) (c d x : R) :
  (forall u v : R, @is_derive R R^o R^o u 1 (fun z : R => f z v) (df u v)) ->
  (forall u v, continuity_2d_pt df u v) ->
  (forall u, segment_integrable (f u) c d) ->
  @is_derive R R^o R^o x 1 (fun u : R => oriented_integral (f u) c d)
    (oriented_integral (df x) c d).
Proof.
move=> HD HC HI.
set s := (if Rle_dec c d then 1 else -1).
pose B := `[Rmin c d, Rmax c d]%classic : set R.
pose F := fun u => Rintegral lebesgue_measure B (f u).
have -> : (fun u => oriented_integral (f u) c d) = (fun u => s * F u).
  by apply/funext => u; rewrite rectangle_oriented_integral_segment.
rewrite rectangle_oriented_integral_segment -/s.
have [M HM] := rectangle_bound df (x - 1) (x + 1) (Rmin c d) (Rmax c d) HC.
have M0 : 0 <= M.
  apply: (Rle_trans _ _ _ (Rabs_pos (df x (Rmin c d)))); apply: HM.
    lra.
  by split; [lra | exact: (Rle_trans _ _ _ (Rmin_l c d) (Rmax_l c d))].
pose l := x - 1; pose r := x + 1.
have hx : `]l, r[%classic x.
  by rewrite /= in_itv /=; apply/andP; split; apply/RltP; rewrite /l /r; lra.
have Hd1 : forall u v, partial1of2 f u v = df u v.
  by move=> u v; rewrite partial1of2E; case: (HD u v).
have mB : measurable (B : set (measurableTypeR R)) by exact: measurable_itv.
have intf : forall u, `]l, r[%classic u ->
    lebesgue_measure.-integrable B (EFin \o f u).
  by move=> u _; exact: HI.
have derf1 : forall u v, `]l, r[%classic u -> B v ->
    @derivable R R^o R^o (f^~ v) u 1.
  by move=> u v _ _; case: (HD u v).
have G0 : forall v : R, (0 <= cst M v)%R by move=> v; apply/RleP.
have intG : lebesgue_measure.-integrable B (EFin \o cst M).
  apply: continuous_compact_integrable; first exact: segment_compact.
  exact/continuous_subspaceT/cst_continuous.
have Gub : forall u v, `]l, r[%classic u -> B v ->
    (`|partial1of2 f u v| <= cst M v)%R.
  move=> u v /rectangle_open_mem hu /rectangle_segment_memE hv.
  rewrite Hd1; apply/RleP; rewrite -RabsE; apply: HM; rewrite /l /r in hu; lra.
have hd := derivable_under_integral mB hx intf derf1 G0 intG Gub.
have hv := differentiation_under_integral mB hx intf derf1 G0 intG Gub.
have hFd : @is_derive R R^o R^o x 1 F (Rintegral lebesgue_measure B (df x)).
  apply: DeriveDef; first exact: hd.
  rewrite -derive1E; rewrite /F hv.
  by apply: eq_Rintegral => v _; rewrite Hd1.
exact: (is_deriveZ s hFd).
Qed.

(* Rules of the oriented integral. *)

Lemma rectangle_oriented_point (g : R -> R) a : oriented_integral g a a = 0.
Proof.
rewrite /oriented_integral; case: Rle_dec => h /=; last lra.
by rewrite set_itv1 Rintegral_set1.
Qed.

Lemma rectangle_oriented_swap (g : R -> R) a b :
  oriented_integral g b a = - oriented_integral g a b.
Proof.
case: (Req_dec a b) => [<-|hne].
  by rewrite rectangle_oriented_point Ropp_0.
rewrite /oriented_integral.
by case: Rle_dec => hba /=; case: Rle_dec => hab /=; lra.
Qed.

Lemma rectangle_chasles (g : R -> R) (a b c : R) : a <= b -> b <= c ->
  segment_integrable g a c ->
  oriented_integral g a b + oriented_integral g b c = oriented_integral g a c.
Proof.
move=> hab hbc; rewrite /segment_integrable Rmin_left ?Rmax_right; try lra.
move=> hint.
rewrite /oriented_integral.
case: Rle_dec => h1 /=; last lra.
case: Rle_dec => h2 /=; last lra.
case: Rle_dec => h3 /=; last lra.
have := @Rintegral_itvB R g (BLeft a) (BRight c) b hint.
rewrite !bnd_simp => H.
have /H : (a <= b)%R by apply/RleP.
move=> /(_ _) H'.
have /H' : (b <= c)%R by apply/RleP.
have hbc' : lebesgue_measure.-integrable `]b, c]%classic (EFin \o g).
  apply: (integrableS _ _ _ hint) => //; apply: subset_itvr; rewrite bnd_simp.
  exact/RleP.
rewrite (Rintegral_itv_obnd_cbnd hbc') => E.
rewrite -E.
rewrite RplusE.
rewrite addrC.
rewrite subrK.
reflexivity.
Qed.

(* With l <= a and l <= z, the oriented integral from a to z is a difference
   of integrals from l. *)
Lemma rectangle_oriented_from_left (g : R -> R) (l a z : R) :
  continuous g -> l <= a -> l <= z ->
  oriented_integral g a z =
  Rintegral lebesgue_measure `[l, z]%classic g -
  Rintegral lebesgue_measure `[l, a]%classic g.
Proof.
move=> hg ha hz.
have e1 b : l <= b ->
    Rintegral lebesgue_measure `[l, b]%classic g = oriented_integral g l b.
  by move=> hb; rewrite /oriented_integral; case: Rle_dec.
rewrite (e1 z hz) (e1 a ha).
case: (Rle_dec a z) => h0.
- rewrite -(rectangle_chasles g l a z ha h0); last lra.
  exact: rectangle_continuous_segment_integrable.
- have hza : z <= a by lra.
  rewrite -(rectangle_chasles g l z a hz hza).
    exact: rectangle_continuous_segment_integrable.
  rewrite (rectangle_oriented_swap g z a); lra.
Qed.

(* The first fundamental theorem of calculus for the oriented integral of a
   continuous function, from any base point a. *)
Lemma rectangle_oriented_primitive_derivative (g : R -> R) (a x : R) :
  continuous g ->
  @is_derive R R^o R^o x 1 (fun z : R => oriented_integral g a z) (g x).
Proof.
move=> hg.
pose l := Rmin (x - 1) a.
have hla : l <= a by apply: Rmin_r.
have hlx : l < x by rewrite /l; move: (Rmin_l (x - 1) a); lra.
pose F := fun z : R =>
  (\int[lebesgue_measure]_(t in [set` Interval (BLeft l) (BRight z)]) (g t))%R.
pose r := x + 1.
have hint : lebesgue_measure.-integrable [set` Interval (BLeft l) (BRight r)]
    (EFin \o g).
  apply: continuous_compact_integrable; first exact: segment_compact.
  exact/continuous_subspaceT.
have hx1 : (x < r)%R by apply/RltP; rewrite /r; lra.
have hFTC : @derivable R R^o R^o F x 1 /\ derive1 (F : R^o -> R^o) x = g x.
  apply: (@continuous_FTC1 R g (BLeft l) x r hx1 hint).
  - by rewrite /= lte_fin; apply/RltP.
  - exact: hg.
case: hFTC => dF DF.
have hF : @is_derive R R^o R^o x 1 F (g x).
  apply: DeriveDef; first exact: dF.
  by rewrite -derive1E DF.
have hG : @is_derive R R^o R^o x 1 (fun z => F z - F a) (g x).
  have -> : g x = (g x - 0)%R by rewrite subr0.
  exact: is_deriveB.
apply: (near_eq_is_derive _ hG).
have /RltP hlx' := hlx.
near=> z.
have hlz : l < z.
  apply/RltP; near: z; exact: lt_nbhsr.
rewrite /F (rectangle_oriented_from_left g l a z hg hla (Rlt_le _ _ hlz)).
by rewrite RminusE.
Unshelve. all: by end_near.
Qed.

(* The second fundamental theorem of calculus for the oriented integral. *)
Lemma rectangle_oriented_FTC (F K : R -> R) a b :
  (forall x : R, @is_derive R R^o R^o x 1 F (K x)) -> continuous K ->
  oriented_integral K a b = F b - F a.
Proof.
move=> HF HK.
have key : forall a' b', a' < b' ->
    Rintegral lebesgue_measure `[a', b']%classic K = F b' - F a'.
  move=> a' b' hab.
  have hab' : (a' < b')%R by apply/RltP.
  have hc : forall x : R^o, {for x, continuous (F : R^o -> R^o)}.
    move=> x; apply: differentiable_continuous; rewrite -derivable1_diffP.
    by case: (HF x).
  have hd : derivable_oo_LRcontinuous (F : R -> R^o) a' b'.
    split.
    - by move=> x _; case: (HF x).
    - exact: cvg_at_right_filter (hc a').
    - exact: cvg_at_left_filter (hc b').
  have hK : {in `]a', b'[%R, (F : R -> R^o)^`() =1 K}.
    by move=> x _; rewrite derive1E; case: (HF x).
  have := @continuous_FTC2 R K F a' b' hab' (continuous_subspaceT HK) hd hK.
  by rewrite /Rintegral => ->; rewrite -EFinB /= RminusE.
case: (Rtotal_order a b) => [hab | [<- | hba]].
- rewrite /oriented_integral; case: Rle_dec => h /=; last lra.
  exact: key.
- by rewrite rectangle_oriented_point Rminus_diag_eq.
- rewrite -(Ropp_involutive (oriented_integral K a b)) -rectangle_oriented_swap.
  rewrite /oriented_integral; case: Rle_dec => h /=; last lra.
  rewrite key //; lra.
Qed.

Lemma rectangle_oriented_zero c d : oriented_integral (fun _ => 0) c d = 0.
Proof.
have mD : measurable (`[Rmin c d, Rmax c d]%classic : set (measurableTypeR R)).
  exact: measurable_itv.
rewrite rectangle_oriented_integral_segment (Rintegral_cst _ mD) mul0r.
by rewrite RmultE mulr0.
Qed.

(* More rules of the oriented integral, for the modules that import this
   one. Coquelicot's RInt_ext asks for f x = g x on the open segment; here
   the equality is asked on the closed segment. The other rules keep
   Coquelicot's hypotheses, with ex_RInt translated to segment_integrable. *)

Lemma rectangle_segment_measurable a b :
  measurable (`[Rmin a b, Rmax a b]%classic : set (measurableTypeR R)).
Proof. exact: measurable_itv. Qed.

Lemma rectangle_segment_integrableE (f : R -> R) a b : a <= b ->
  segment_integrable f a b =
  lebesgue_measure.-integrable `[a, b]%classic (EFin \o f).
Proof. by move=> h; rewrite /segment_integrable Rmin_left // Rmax_right. Qed.

(* A function integrable on [a, b] and on [b, c] is integrable on [a, c]. *)
Lemma rectangle_integrable_union (f : R -> R) a b c : a <= b -> b <= c ->
  lebesgue_measure.-integrable `[a, b]%classic (EFin \o f) ->
  lebesgue_measure.-integrable `[b, c]%classic (EFin \o f) ->
  lebesgue_measure.-integrable `[a, c]%classic (EFin \o f).
Proof.
move=> hab hbc iab ibc.
have /RleP hab' := hab; have /RleP hbc' := hbc.
have E : `[a, c]%classic = `[a, b]%classic `|` `]b, c]%classic.
  by apply: itv_bndbnd_setU; rewrite bnd_simp.
have mA : measurable (`[a, b]%classic : set (measurableTypeR R)).
  exact: measurable_itv.
have mB : measurable (`]b, c]%classic : set (measurableTypeR R)).
  exact: measurable_itv.
have ibc2 : lebesgue_measure.-integrable `]b, c]%classic (EFin \o f).
  apply: (integrableS _ _ _ ibc) => //.
  by apply: subset_itvr; rewrite bnd_simp.
have aA := integrable_abse iab; have aB := integrable_abse ibc2.
case/integrableP: iab => mfA iA; case/integrableP: ibc2 => mfB iB.
rewrite E; apply/integrableP; split.
  by apply/measurable_funU.
rewrite ge0_integral_setU //.
- apply/measurable_funU => //; split.
  + by case/integrableP: aA.
  + by case/integrableP: aB.
- apply: lt_disjoint => x y; rewrite !in_itv /= => /andP [_ hx] /andP [hy _].
  exact: (Order.POrderTheory.le_lt_trans hx hy).
- exact: lte_add_pinfty.
Qed.

(* Chasles's relation for end points in any order, with Coquelicot's
   hypotheses. *)
Lemma rectangle_oriented_chasles (f : R -> R) a b c :
  segment_integrable f a b -> segment_integrable f b c ->
  oriented_integral f a b + oriented_integral f b c = oriented_integral f a c.
Proof.
move=> hab hbc.
have sw := rectangle_oriented_swap f.
case: (Rle_dec a b) => h1; case: (Rle_dec b c) => h2.
- apply: rectangle_chasles => //.
  have hac : a <= c by lra.
  rewrite (rectangle_segment_integrableE f a c hac).
  rewrite (rectangle_segment_integrableE f a b h1) in hab.
  rewrite (rectangle_segment_integrableE f b c h2) in hbc.
  exact: (rectangle_integrable_union f a b c).
- have hcb : c <= b by lra.
  rewrite (sw c b).
  case: (Rle_dec a c) => h3.
  + have := rectangle_chasles f a c b h3 hcb hab; lra.
  + have hca : c <= a by lra.
    have hbc' : segment_integrable f c b.
      by rewrite /segment_integrable Rmin_comm Rmax_comm.
    have := rectangle_chasles f c a b hca h1 hbc'.
    rewrite (sw c a); lra.
- have hba : b <= a by lra.
  rewrite (sw b a).
  case: (Rle_dec a c) => h3.
  + have := rectangle_chasles f b a c hba h3 hbc; lra.
  + have hca : c <= a by lra.
    have hab' : segment_integrable f b a.
      by rewrite /segment_integrable Rmin_comm Rmax_comm.
    have := rectangle_chasles f b c a h2 hca hab'.
    rewrite (sw c a); lra.
- have hba : b <= a by lra.
  have hcb : c <= b by lra.
  have hca : segment_integrable f c a.
    have hca' : c <= a by lra.
    rewrite (rectangle_segment_integrableE f c a hca').
    rewrite /segment_integrable (Rmin_right _ _ hba) (Rmax_left _ _ hba) in hab.
    rewrite /segment_integrable (Rmin_right _ _ hcb) (Rmax_left _ _ hcb) in hbc.
    exact: (rectangle_integrable_union f c b a).
  have := rectangle_chasles f c b a hcb hba hca.
  rewrite (sw b a) (sw c b) (sw c a); lra.
Qed.

Lemma rectangle_oriented_ext (f g : R -> R) a b :
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  oriented_integral f a b = oriented_integral g a b.
Proof.
move=> hfg; rewrite !rectangle_oriented_integral_segment.
congr (_ * _); apply: eq_Rintegral => x /set_mem /rectangle_segment_memE hx.
exact: hfg.
Qed.

Lemma rectangle_oriented_scal (f : R -> R) a b k :
  segment_integrable f a b ->
  oriented_integral (fun x => k * f x) a b = k * oriented_integral f a b.
Proof.
move=> hf; rewrite !rectangle_oriented_integral_segment.
rewrite (RintegralZl k (rectangle_segment_measurable a b) hf).
set I := Rintegral _ _ _; rewrite -RmultE; ring.
Qed.

Lemma rectangle_oriented_minus (f g : R -> R) a b :
  segment_integrable f a b -> segment_integrable g a b ->
  oriented_integral (fun x => f x - g x) a b =
  oriented_integral f a b - oriented_integral g a b.
Proof.
move=> hf hg; rewrite !rectangle_oriented_integral_segment.
rewrite (RintegralB (rectangle_segment_measurable a b) hf hg).
set I := Rintegral _ _ _; set J := Rintegral _ _ _; rewrite -RminusE; ring.
Qed.

(* Primitives in the first variable. *)

Lemma rectangle_primitive_derivative (f : R -> R -> R) (a x y : R) :
  (forall u v, continuity_2d_pt f u v) ->
  @is_derive R R^o R^o x 1 (fun z : R => oriented_integral (fun t => f t y) a z)
    (f x y).
Proof.
move=> H; apply: (rectangle_oriented_primitive_derivative (fun t => f t y)).
by move=> t; apply: rectangle_continuous_slice_left.
Qed.

Lemma rectangle_primitive_integrable (f : R -> R -> R) a x c d :
  (forall u v, continuity_2d_pt f u v) ->
  segment_integrable (fun y => oriented_integral (fun t => f t y) a x) c d.
Proof.
move=> H; apply: rectangle_continuous_segment_integrable => y.
apply: (rectangle_parameter_integral_continuous (fun y t => f t y) a x y).
by move=> u v; apply: rectangle_continuous_transpose.
Qed.

Lemma rectangle_iterated_primitive_derivative (f : R -> R -> R) (a c d x : R) :
  (forall u v, continuity_2d_pt f u v) ->
  @is_derive R R^o R^o x 1
    (fun z : R =>
       oriented_integral (fun y => oriented_integral (fun t => f t y) a z) c d)
    (oriented_integral (f x) c d).
Proof.
move=> H.
apply: (rectangle_parameter_integral_derivative
  (fun z y => oriented_integral (fun t => f t y) a z) f c d x).
- by move=> u v; apply: rectangle_primitive_derivative.
- exact: H.
- by move=> u; apply: rectangle_primitive_integrable.
Qed.

(* Fubini's theorem on a rectangle. *)

Theorem continuous_rectangle_fubini (f : R -> R -> R) a b c d :
  (forall x y, continuity_2d_pt f x y) ->
  oriented_integral (fun x => oriented_integral (f x) c d) a b =
  oriented_integral (fun y => oriented_integral (fun x => f x y) a b) c d.
Proof.
move=> H.
have HD : forall x, @is_derive R R^o R^o x 1
    (fun z : R =>
       oriented_integral (fun y => oriented_integral (fun t => f t y) a z) c d)
    (oriented_integral (f x) c d).
  by move=> x; exact: rectangle_iterated_primitive_derivative.
have HK : continuous (fun z => oriented_integral (f z) c d).
  by move=> x; exact: rectangle_parameter_integral_continuous.
rewrite (rectangle_oriented_FTC _ _ a b HD HK).
have -> : (fun y => oriented_integral (fun t => f t y) a a) = (fun _ => 0).
  by apply/funext => y; exact: rectangle_oriented_point.
by rewrite rectangle_oriented_zero Rminus_0_r.
Qed.
