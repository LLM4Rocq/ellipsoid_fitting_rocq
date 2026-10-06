(* Rules for the oriented integral of AnalysisIntegralDefinitions.
   oriented_integral g a b is the Lebesgue integral over the segment
   between a and b, with a minus sign when b < a, and segment_integrable
   g a b is Lebesgue integrability on that segment, which includes Borel
   measurability.
   - A continuous function is integrable on every segment
     (rectangle_continuous_segment_integrable), and integrability on
     [a, b] and on [b, c] gives integrability on [a, c]
     (rectangle_integrable_union).
   - The oriented integral as a signed Lebesgue integral
     (rectangle_oriented_integral_segment, rectangle_oriented_from_left),
     the point and swap rules (rectangle_oriented_point,
     rectangle_oriented_swap), Chasles's relation for end points in order
     (rectangle_chasles) or in any order (rectangle_oriented_chasles),
     extensionality on the segment (rectangle_oriented_ext), scaling
     (rectangle_oriented_scal) and difference (rectangle_oriented_minus).
   - The fundamental theorems of calculus for a continuous g:
     z |-> oriented_integral g a z has the derivative g z
     (rectangle_oriented_primitive_derivative), and oriented_integral K a b
     is F b - F a when F has the continuous derivative K
     (rectangle_oriented_FTC). They come from MathComp's continuous_FTC1
     and continuous_FTC2. *)

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

(* Integrability on segments, and the oriented integral as a signed
   integral. *)

(* A continuous function is integrable on every segment. *)
Lemma rectangle_continuous_segment_integrable (g : R -> R) c d :
  continuous g -> segment_integrable g c d.
Proof.
move=> hg; rewrite /segment_integrable.
apply: continuous_compact_integrable; first exact: segment_compact.
exact/continuous_subspaceT.
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

(* More rules of the oriented integral. rectangle_oriented_ext asks for
   f x = g x on the closed segment between the end points. *)

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

(* Chasles's relation for end points in any order. *)
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
