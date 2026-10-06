(* Jointly continuous functions of d coordinates are measurable on d-tuples
   of reals (gpp_joint_measurable). The proof rounds each coordinate down to
   the grid of mesh 1/(n+1) (gpp_round, gpp_grid). The rounded function is
   constant on each of the countably many measurable fibers of the rounding,
   hence measurable (gpp_grid_measurable), and it converges pointwise to the
   function as n grows. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint rat.
From mathcomp Require Import archimedean.
From mathcomp Require Import boolp classical_sets functions cardinality reals Rstruct.
From mathcomp Require Import topology Rstruct_topology sequences.
From mathcomp Require Import normedtype.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.CoordinateTuples.
From EllipsoidFitting Require Import Gaussian.ProductLawBasics.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Delimit Scope R_scope with Rcoq.

Definition gpp_grid d n (z : d.-tuple int) : list R :=
  map (fun k : int => k%:~R / n.+1%:R) (tval z).

Definition gpp_round d n (x : d.-tuple (measurableTypeR R)) : d.-tuple int :=
  [tuple Num.floor (tnth x i * n.+1%:R) | i < d].

Lemma gpp_round_fiber d n (z : d.-tuple int) :
  measurable [set x : d.-tuple (measurableTypeR R) | gpp_round d n x = z].
Proof.
have -> : [set x : d.-tuple (measurableTypeR R) | gpp_round d n x = z] =
  \bigcap_(i : 'I_d) [set x : d.-tuple (measurableTypeR R) |
    Rfloor (tnth x i * n.+1%:R) = (tnth z i)%:~R].
  apply/seteqP; split=> x.
  - move=> hx i _; have := congr1 (fun t => tnth t i) hx.
    by rewrite /gpp_round tnth_mktuple => <-.
  - move=> hx; apply: eq_from_tnth => i; rewrite /gpp_round tnth_mktuple.
    apply: (intr_inj (R := R)); exact: (hx i I).
apply: fin_bigcap_measurable; first exact: finite_finset.
move=> i _.
have mR : measurable_fun [set: measurableTypeR R] (@Rfloor R).
  apply: nondecreasing_measurable => //; exact: le_Rfloor.
have mh : measurable_fun [set: d.-tuple (measurableTypeR R)]
    (fun x => Rfloor (tnth x i * n.+1%:R)).
  apply: measurableT_comp mR _.
  apply: measurable_funM; [exact: measurable_tnth | exact: measurable_cst].
by have := mh measurableT [set (tnth z i)%:~R] (measurable_set1 _);
  rewrite setTI.
Qed.

Lemma gpp_round_error n (x : R) :
  Rabs (Rfloor (x * n.+1%:R) / n.+1%:R - x) < n.+1%:R^-1.
Proof.
have h0 : (0 < n.+1%:R :> R) by rewrite ltr0n.
have h1 := elimT RleP (Rfloor_le (x * n.+1%:R)).
have h2 := elimT RltP (lt_succ_Rfloor (x * n.+1%:R)).
have hpos := elimT RltP h0.
pose a : R := n.+1%:R.
pose y : R := Rfloor (x * a).
change (0 < a)%Rcoq in hpos.
change (y <= x * a)%Rcoq in h1.
change (x * a < y + 1)%Rcoq in h2.
apply/RltP.
change (Rabs (y / a - x) < / a)%Rcoq.
apply Rabs_def1; apply (Rmult_lt_reg_r a); try exact hpos.
- replace ((y / a - x) * a)%Rcoq
    with (y - x * a)%Rcoq by (field; lra).
  replace (/ a * a)%Rcoq with 1%Rcoq by (field; lra).
  lra.
- replace ((y / a - x) * a)%Rcoq
    with (y - x * a)%Rcoq by (field; lra).
  replace (- / a * a)%Rcoq with (-1)%Rcoq by (field; lra).
  lra.
Qed.

Lemma gpp_grid_length d n (z : d.-tuple int) : length (gpp_grid d n z) = d.
Proof. change (size (gpp_grid d n z) = d); by rewrite /gpp_grid size_map size_tuple. Qed.

Lemma gpp_grid_nth d n (x : d.-tuple (measurableTypeR R)) (i : 'I_d) :
  List.nth i (gpp_grid d n (gpp_round d n x)) 0%R =
  Rfloor (tnth x i * n.+1%:R) / n.+1%:R.
Proof.
rewrite gpp_nthE /gpp_grid.
rewrite (nth_map 0%Z) ?size_tuple ?ltn_ord //.
by rewrite -(tnth_nth 0%Z) /gpp_round tnth_mktuple.
Qed.

Lemma gpp_grid_measurable d n (F : list R -> R) :
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    ((fun x => F (gpp_grid d n (gpp_round d n x))) : _ -> measurableTypeR R).
Proof.
move=> _ B mB; rewrite setTI.
change (measurable (fun x : d.-tuple (measurableTypeR R) =>
  B (F (gpp_grid d n (gpp_round d n x))))).
have -> : (fun x : d.-tuple (measurableTypeR R) =>
    B (F (gpp_grid d n (gpp_round d n x)))) =
  \bigcup_(z : d.-tuple int)
    (if F (gpp_grid d n z) \in B then [set x | gpp_round d n x = z] else set0).
  apply/seteqP; split=> x.
  - move=> hx; exists (gpp_round d n x) => //; by rewrite mem_set.
  - move=> [z _]; case: ifP => // hz hx.
    rewrite hx.
    by move: hz; rewrite inE.
apply: countable_bigcupT_measurable; first exact: countableP.
move=> z; case: ifP => // _; exact: gpp_round_fiber.
Qed.

Lemma gpp_joint_measurable d (F : list R -> R) :
  finite_joint_continuous d F ->
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    ((fun x => F (tval x)) : _ -> measurableTypeR R).
Proof.
move=> HC.
apply: (@measurable_fun_cvg _ _ R setT
  (fun n x => F (gpp_grid d n (gpp_round d n x)))).
- move=> n; exact: gpp_grid_measurable.
- move=> x _; apply/cvgrPdist_lt => eps eps0.
  have hx : length (tval x) = d := size_tuple x.
  have [delta Hd] := HC (coordinates_of_list d (tval x))
    (mkposreal eps (elimT RltP eps0)).
  have hm := (proj1 (@cvgrPdist_lt R R^o nat \oo _
    (fun n => @harmonic R n) 0) (@cvg_harmonic R)).
  have hd0 : (0 < (pos delta)) by apply/RltP; exact: cond_pos.
  have hm' : \forall n \near \oo, `|0 - harmonic n| < (pos delta) :=
    hm ltac:(typeclasses eauto) (pos delta) hd0.
  apply: (filterS _ hm').
  move=> n hn.
  have hmesh : (harmonic n < (pos delta) :> R).
    move: hn; by rewrite sub0r normrN ger0_norm //; exact: harmonic_ge0.
  have hg := gpp_grid_length d n (gpp_round d n x).
  have hclose : close_n d delta
      (coordinates_of_list d (gpp_grid d n (gpp_round d n x)))
      (coordinates_of_list d (tval x)).
  { apply/(coordinates_close_lists d delta _ _ hg hx).
    move=> i hi.
    have hi' : (i < d)%N by apply/ltP.
    have he := gpp_round_error n (tnth x (Ordinal hi')).
    have hval := gpp_grid_nth d n x (Ordinal hi').
    change (Rabs (List.nth (Ordinal hi') (gpp_grid d n (gpp_round d n x)) 0%R -
      List.nth (Ordinal hi') (tval x) 0%R) < delta)%Rcoq.
    rewrite hval gpp_nthE -(tnth_nth 0%R).
    exact: (Rlt_trans _ _ _ (elimT RltP he) (elimT RltP hmesh)). }
  have hf := Hd _ hclose.
  rewrite (coordinates_list_roundtrip d _ hg) (coordinates_list_roundtrip d _ hx) in hf.
  apply/RltP; rewrite -RabsE Rabs_minus_sym; exact: hf.
Qed.
