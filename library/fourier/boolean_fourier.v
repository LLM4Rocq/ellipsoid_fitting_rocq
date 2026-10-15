From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint zmodp.
From mathcomp Require Import matrix.
From GaussianAnalysis.matrix Require Import euclidean.

(**md**************************************************************************)
(* # Real Fourier analysis on Boolean products                                *)
(*                                                                            *)
(* The Boolean product 'M['F_2]_(t, a) holds t blocks, its rows, of a bits    *)
(* each, and is a group under addition. A frequency p and a point y have the  *)
(* F_2 pairing p . y = \sum_i \sum_j p_ij y_ij and the character              *)
(* chi_p (y) = (-1)^(p . y), with the values 1 and -1 in any ring. A function *)
(* f with values in a module V over a numFieldType R has the Fourier          *)
(* coefficients                                                               *)
(*   fcoef f p = 2^(-t a) \sum_y chi_p (y) f (y),                             *)
(* normalized by the number 2^(t a) of points, so that the inversion formula  *)
(* f (y) = \sum_p chi_p (y) fcoef f p has no factor. Real functions take      *)
(* their values in R^o, matrix functions in 'M[R]_(m, n). The block degree of *)
(* p is the number of its nonzero rows, and the block distance of p and q the *)
(* number of rows where they differ. A function has block degree at most D    *)
(* (low_blk_deg D f) if its coefficients vanish at every frequency of block   *)
(* degree larger than D; the zero function has every block degree.            *)
(*                                                                            *)
(* This file holds the definitions and the lemmas of packet P of phase 13,    *)
(* whose statements the user accepted on 15 October 2026 (AGENTS.md, section  *)
(* Phase 13, step 0, items 3 and 4); make check proves each accepted text, as *)
(* the acceptance inventory records it, by its lemma. The characters take     *)
(* their values in any ring (pzRingType), and the coefficients are over a     *)
(* numFieldType:                                                              *)
(* - bchar_algebra: chi_0 = 1, chi_(p + q) = chi_p chi_q,                     *)
(*   chi_p (y) = chi_y (p), and chi_p (y) is 1 or -1.                         *)
(* - bchar_orthogonal: \sum_y chi_p (y) chi_q (y) is 2^(t a) if p = q, and 0  *)
(*   otherwise.                                                               *)
(* - bchar_delta: at the one-bit frequency delta_mx i j, the character is     *)
(*   y |-> (-1)^(y_ij), with the exponent written as nat_of_ord (y i j).      *)
(* - blk_dist_metric: the block distance is a metric, invariant under         *)
(*   translation, and the distance of p and q is the block degree of p + q.   *)
(* - blk_dist_row: on one block, the distance of s and z is 1 if s != z, and  *)
(*   0 otherwise.                                                             *)
(* - fcoef_inversion: the inversion formula.                                  *)
(* - fcoef_expansion: the coefficients of y |-> \sum_p chi_p (y) c_p are the  *)
(*   c_p, so the characters form a basis.                                     *)
(* - fcoef_plancherel: Plancherel's identity                                  *)
(*   2^(-t a) \sum_y b (f y) (g y) = \sum_p b (fcoef f p) (fcoef g p) for     *)
(*   every bilinear map b, for example mxdot or (H, G) |-> H^T G.             *)
(* - fcoef_linear, fcoef_comp_linear and fcoef_mulmx: the coefficient is      *)
(*   linear in the function, and it commutes with every linear map of the     *)
(*   values, in particular with constant matrix factors on both sides.        *)
(* - fcoef_norm_le: the coefficients of a real function are bounded by the    *)
(*   supremum of its absolute value.                                          *)
(* - fcoef_translate: multiplication by chi_q translates the frequency p to   *)
(*   p + q.                                                                   *)
(* - low_blk_deg_expansion: f has block degree at most D if and only if it is *)
(*   the sum of its terms of block degree at most D.                          *)
(* - low_blk_deg_translate: if the coefficients of f vanish at block distance *)
(*   larger than D from q, then chi_q f has block degree at most D. Its       *)
(*   squares are those of f, since chi_q (y)^2 = 1.                           *)
(* - bchar_col_mx, blk_col_mx and fcoef_col_mx: when col_mx splits            *)
(*   'M['F_2]_(t1 + t2, a) into two groups of blocks, the character is the    *)
(*   product of the two characters, block degrees and distances add, and a    *)
(*   coefficient is an iterated coefficient.                                  *)
(*                                                                            *)
(* Proved besides the lemmas of packet P:                                     *)
(* - F2_cases, natF2_0, natF2_1, addF2_11, oppF2, oppmxF2, addmxF2_eq0 and    *)
(*   addmxF2K: the arithmetic of 'F_2 and of its matrices, where -p = p;      *)
(*   signF2D: (-1)^(u + v) = (-1)^u (-1)^v for u and v in 'F_2, in any ring.  *)
(* - linear0_prop, linearD_prop, linearZ_prop and linear_sum_prop: a map that *)
(*   satisfies the predicate linear sends 0 to 0 and commutes with sums and   *)
(*   scalings. The lemmas of packet P take plain maps with this predicate,    *)
(*   not the structure {linear U -> W}, so that a bilinear map is a curried   *)
(*   function with one hypothesis for each argument, and a map such as        *)
(*   H |-> A *m H *m B needs no instance.                                     *)
(* - bdotE, bdotC, bdotDl, bdotDr, bdot0l, bdot_delta and bdot_col_mx: the    *)
(*   pairing is mxdot of matrix/euclidean.v at 'F_2 (bdotE), so it is         *)
(*   symmetric and bilinear and bdot p (delta_mx i j) = p i j, by the lemmas  *)
(*   on mxdot; it adds along col_mx.                                          *)
(* - bchar0, bcharD, bcharC, bcharDr, bchar_sign and bchar_sqr: the character *)
(*   algebra; bchar_int: the characters in R are the images of the characters *)
(*   in int; sum_bchar_int and sum_bchar: \sum_y chi_p (y) is 2^(t a) if      *)
(*   p = 0 and 0 otherwise, first in int, where a sum equal to its opposite   *)
(*   vanishes, then in any ring.                                              *)
(* - blk_distE, blk_dist_eq0, blk_distC, blk_dist_triangle,                   *)
(*   blk_dist_translate, blk_deg_col_mx and blk_dist_col_mx: the block degree *)
(*   and the block distance.                                                  *)
(* - fcoefZ, fcoef_mulmxl, fcoef_entry, fcoef_mxcol and fcoef_indicator: the  *)
(*   coefficient of a scaled function and of A *m f y, an entry of a          *)
(*   coefficient as the coefficient of the entry, the coefficients of a block *)
(*   column \mxcol_i B_i y as the block column of the coefficients, and the   *)
(*   coefficients of y |-> [y = y0] c v, which are 2^(-t a) chi_p (y0) c v.   *)
(* - card_cube_neq0, sum_bchar_freq, eq_fcoef, card_col_mx and sum_col_mx:    *)
(*   the number of points is nonzero in R, the orthogonality of the           *)
(*   characters as functions of the frequency, a coefficient depends only on  *)
(*   the values of the function, and a sum over 'M['F_2]_(t1 + t2, a) is a    *)
(*   double sum along col_mx.                                                 *)
(*                                                                            *)
(* The file ends with two examples: on one bit, the nonzero character is      *)
(* y |-> (-1)^y (bchar_one_bit); the coefficients of a character are 1 at its *)
(* frequency and 0 elsewhere (fcoef_bchar).                                   *)
(*                                                                            *)
(* A Rocq formalization of the credited argument of the Fourier analysis in   *)
(* the section 'Fourier concentration of squares under product averages' of   *)
(* 'Exponential PSD rank of positively shifted matching matrices' (family 126 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/fourier-smoothing.tex, lines 12-40), which its theorem     *)
(* 'Fourier smoothing of matrix squares' (lines 42-98, in                     *)
(* product_smoothing.v), the parity functional and the final step of the main *)
(* proof use (source/sections/parity.tex, lines 107-117 and 271-283;          *)
(* source/sections/matching.tex, lines 148-193). It follows no Lean module:   *)
(* the Lean development of family 126 has no Boolean characters. Departures   *)
(* from the manuscript:                                                       *)
(* - the frequencies, the manuscript's Lambda^t with Lambda = (F_2)^a, and    *)
(*   the points, Y_1 x ... x Y_t with each Y_i identified with (F_2)^a, are   *)
(*   both 'M['F_2]_(t, a), with the block p_i as the row i of p;              *)
(* - the coefficients are defined for functions with values in any module     *)
(*   over a numFieldType, where the manuscript has real matrices, and the     *)
(*   characters with values in any ring.                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*          bdot p y == \sum_i \sum_j p i j * y i j, the pairing, in 'F_2     *)
(*       bchar R p y == (-1) ^+ bdot p y, the character chi_p at y, in R      *)
(*         blk_deg p == the number of nonzero rows of p                       *)
(*      blk_dist p q == the number of rows where p and q differ               *)
(*         fcoef f p == the Fourier coefficient of f at p,                    *)
(*                      2^(-t a) *: \sum_y bchar R p y *: f y                 *)
(*   low_blk_deg D f == fcoef f p = 0 for every p with D < blk_deg p          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section boolean_cube.
Variables t a : nat.
Local Notation cube := 'M['F_2]_(t, a).
Implicit Types p q s y z : cube.

(* The F_2 pairing of a frequency p and a point y. *)
Definition bdot p y : 'F_2 := \sum_(i < t) \sum_(j < a) p i j * y i j.

(* The character chi_p : y |-> (-1)^(p . y), with values in any ring. *)
Definition bchar (R : pzRingType) p y : R := (-1) ^+ (nat_of_ord (bdot p y)).

(* The block degree of p: the number of its nonzero rows (blocks). *)
Definition blk_deg p : nat := #|[set i : 'I_t | row i p != 0]|.

(* The block distance of p and q: the number of rows where they differ. *)
Definition blk_dist p q : nat := #|[set i : 'I_t | row i p != row i q]|.

Section coefficients.
Variable R : numFieldType.

(* The Fourier coefficient at p of a function with values in an R-module,
   normalized by the number of points. *)
Definition fcoef (V : lmodType R) (f : cube -> V) p : V :=
  (#|{: cube}|%:R)^-1 *: \sum_(y : cube) bchar R p y *: f y.

(* f has block degree at most D: its coefficients vanish at every frequency
   of block degree larger than D. *)
Definition low_blk_deg (V : lmodType R) (D : nat) (f : cube -> V) : Prop :=
  forall p, (D < blk_deg p)%N -> fcoef f p = 0.

End coefficients.

End boolean_cube.

(* ## Proofs *)

(* The arithmetic of 'F_2 and of its matrices. *)
Section F2.

Lemma F2_cases (u : 'F_2) : u = 0 \/ u = 1.
Proof. by case: u => [[|[|n]]] // Hu; [left|right]; apply/val_inj. Qed.

Lemma natF2_0 : nat_of_ord (0 : 'F_2) = 0%N.
Proof. by []. Qed.

Lemma natF2_1 : nat_of_ord (1 : 'F_2) = 1%N.
Proof. by []. Qed.

Lemma addF2_11 : (1 + 1 : 'F_2) = 0.
Proof. by apply/val_inj. Qed.

Lemma oppF2 (u : 'F_2) : - u = u.
Proof. exact: oppr_pchar2 (pchar_Fp (isT : prime 2)) u. Qed.

Lemma oppmxF2 m n (p : 'M['F_2]_(m, n)) : - p = p.
Proof. by apply/matrixP => i j; rewrite mxE oppF2. Qed.

Lemma addmxF2_eq0 m n (p q : 'M['F_2]_(m, n)) : (p + q == 0) = (p == q).
Proof. by rewrite addr_eq0 oppmxF2. Qed.

Lemma addmxF2K m n (p q : 'M['F_2]_(m, n)) : p + q + q = p.
Proof. by rewrite -addrA -{2}(oppmxF2 q) subrr addr0. Qed.

Lemma signF2D (R : pzRingType) (u v : 'F_2) :
  (-1) ^+ (nat_of_ord (u + v)) =
    (-1) ^+ (nat_of_ord u) * (-1) ^+ (nat_of_ord v) :> R.
Proof.
by case: (F2_cases u) => ->; case: (F2_cases v) => ->;
  rewrite ?add0r ?addr0 ?addF2_11 ?natF2_0 ?natF2_1 ?expr0 ?expr1 ?mul1r
    ?mulr1 ?mulrNN ?mulr1.
Qed.

End F2.

(* The maps that satisfy the predicate linear. *)
Section linear_prop.
Variable R : pzRingType.
Variables U W : lmodType R.
Implicit Type h : U -> W.

Lemma linear0_prop h : linear h -> h 0 = 0.
Proof.
move=> hl; rewrite -[X in h X](subrr (0 : U)).
by rewrite (zmod_morphism_linear hl) subrr.
Qed.

Lemma linearD_prop h u v : linear h -> h (u + v) = h u + h v.
Proof. by move=> hl; have := hl 1 u v; rewrite !scale1r. Qed.

Lemma linearZ_prop h c u : linear h -> h (c *: u) = c *: h u.
Proof. by move=> hl; rewrite (scalable_linear hl). Qed.

Lemma linear_sum_prop h (I : Type) (r : seq I) (P : pred I) (F : I -> U) :
  linear h -> h (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) h (F i).
Proof.
move=> hl; elim/big_rec2: _ => [|i y x _ <-]; first exact: linear0_prop.
exact: linearD_prop.
Qed.

End linear_prop.

Section boolean_cube_proofs.
Variables t a : nat.
Local Notation cube := 'M['F_2]_(t, a).
Implicit Types p q s y z : cube.

(* The pairing is mxdot of matrix/euclidean.v at 'F_2. *)
Lemma bdotE p y : bdot p y = mxdot p y.
Proof. by []. Qed.

Lemma bdotC p y : bdot p y = bdot y p.
Proof. by rewrite !bdotE mxdotC. Qed.

Lemma bdotDl p q y : bdot (p + q) y = bdot p y + bdot q y.
Proof. by rewrite !bdotE mxdotDl. Qed.

Lemma bdotDr p y z : bdot p (y + z) = bdot p y + bdot p z.
Proof. by rewrite !bdotE mxdotDr. Qed.

Lemma bdot0l y : bdot 0 y = 0.
Proof. by rewrite bdotE mxdot0l. Qed.

Lemma bdot_delta p i j : bdot p (delta_mx i j) = p i j.
Proof. by rewrite bdotE mxdot_delta. Qed.

Section characters_proofs.
Variable R : pzRingType.

Lemma bchar0 y : bchar R 0 y = 1.
Proof. by rewrite /bchar bdot0l expr0. Qed.

Lemma bcharD p q y : bchar R (p + q) y = bchar R p y * bchar R q y.
Proof. by rewrite /bchar bdotDl signF2D. Qed.

Lemma bcharC p y : bchar R p y = bchar R y p.
Proof. by rewrite /bchar bdotC. Qed.

Lemma bcharDr p y z : bchar R p (y + z) = bchar R p y * bchar R p z.
Proof. by rewrite bcharC bcharD !(bcharC _ p). Qed.

Lemma bchar_sign p y : bchar R p y = 1 \/ bchar R p y = -1.
Proof.
by rewrite /bchar; case: (F2_cases (bdot p y)) => ->; [left|right];
  rewrite ?natF2_0 ?natF2_1 ?expr0 ?expr1.
Qed.

Lemma bchar_sqr p y : bchar R p y * bchar R p y = 1.
Proof. by case: (bchar_sign p y) => ->; rewrite ?mulr1 ?mulrNN ?mulr1. Qed.

Lemma bchar_algebra :
  [/\ forall y, bchar R 0 y = 1,
      forall p q y, bchar R (p + q) y = bchar R p y * bchar R q y,
      forall p y, bchar R p y = bchar R y p &
      forall p y, bchar R p y = 1 \/ bchar R p y = -1].
Proof.
by split; [exact: bchar0 | exact: bcharD | exact: bcharC | exact: bchar_sign].
Qed.

Lemma bchar_delta (i : 'I_t) (j : 'I_a) y :
  bchar R (delta_mx i j) y = (-1) ^+ nat_of_ord (y i j).
Proof. by rewrite bcharC /bchar bdot_delta. Qed.

Lemma bchar_int p y : bchar R p y = (bchar int p y)%:~R.
Proof. by rewrite /bchar rmorphXn rmorphN1. Qed.

End characters_proofs.

Lemma sum_bchar_int p :
  \sum_(y : cube) bchar int p y = if p == 0 then #|{: cube}|%:R else 0.
Proof.
case: eqP => [->|/eqP p0].
  rewrite (eq_bigr (fun _ => 1)) => [y _|]; first exact: bchar0.
  by rewrite sumr_const.
have [i [j pij]] : exists i j, p i j = 1.
  have : [exists i, [exists j, p i j != 0]].
    apply: contraNT p0 => /existsPn H; apply/eqP/matrixP => i j.
    by move: (H i) => /existsPn /(_ j); rewrite negbK mxE => /eqP.
  case/existsP => i /existsP [j pij]; exists i, j.
  by case: (F2_cases (p i j)) pij => // ->; rewrite eqxx.
set S := \sum_(y : cube) _.
have SN : S = - S.
  rewrite {1}/S (reindex_inj (addIr (delta_mx i j : cube))) /= -sumrN.
  apply: eq_bigr => y _; rewrite bcharDr [bchar _ p (delta_mx i j)]/bchar.
  by rewrite bdot_delta pij natF2_1 expr1 mulrN1.
by move/eqP: SN; rewrite -addr_eq0 -mulr2n mulrn_eq0 /= => /eqP.
Qed.

Section orthogonality_proofs.
Variable R : pzRingType.

Lemma sum_bchar p :
  \sum_(y : cube) bchar R p y = if p == 0 then #|{: cube}|%:R else 0.
Proof.
rewrite (eq_bigr _ (fun y _ => bchar_int R p y)) -rmorph_sum sum_bchar_int.
by case: ifP => _; rewrite ?rmorph0 ?rmorph_nat.
Qed.

Lemma bchar_orthogonal p q : \sum_(y : cube) bchar R p y * bchar R q y =
  if p == q then #|{: cube}|%:R else 0.
Proof.
rewrite (eq_bigr _ (fun y _ => esym (bcharD R p q y))) sum_bchar.
by rewrite addmxF2_eq0.
Qed.

End orthogonality_proofs.

Lemma blk_distE p q : blk_dist p q = blk_deg (p + q).
Proof. by apply: eq_card => i; rewrite !inE linearD /= addmxF2_eq0. Qed.

Lemma blk_dist_eq0 p q : blk_dist p q = 0%N <-> p = q.
Proof.
split => [/eqP|->]; last first.
  by apply/eqP; rewrite cards_eq0; apply/eqP/setP => i; rewrite !inE eqxx.
rewrite cards_eq0 => /eqP E; apply/row_matrixP => i.
by apply/eqP; move/setP/(_ i): E; rewrite !inE => /negbFE.
Qed.

Lemma blk_distC p q : blk_dist p q = blk_dist q p.
Proof. by apply: eq_card => i; rewrite !inE eq_sym. Qed.

Lemma blk_dist_triangle p q s :
  (blk_dist p s <= blk_dist p q + blk_dist q s)%N.
Proof.
apply: leq_trans (leq_card_setU _ _); apply/subset_leq_card/subsetP => i.
rewrite !inE; apply: contraR; rewrite negb_or !negbK.
by case/andP => /eqP -> /eqP ->.
Qed.

Lemma blk_dist_translate p q s : blk_dist (p + s) (q + s) = blk_dist p q.
Proof. by apply: eq_card => i; rewrite !inE !linearD /= (inj_eq (addIr _)). Qed.

Lemma blk_dist_metric :
  [/\ forall p q, blk_dist p q = blk_deg (p + q),
      forall p q, blk_dist p q = 0%N <-> p = q,
      forall p q, blk_dist p q = blk_dist q p,
      forall p q s, (blk_dist p s <= blk_dist p q + blk_dist q s)%N &
      forall p q s, blk_dist (p + s) (q + s) = blk_dist p q].
Proof.
split; [exact: blk_distE | exact: blk_dist_eq0 | exact: blk_distC |
  exact: blk_dist_triangle | exact: blk_dist_translate].
Qed.

Section coefficients_proofs.
Variable R : numFieldType.
Local Notation N := (#|{: cube}|%:R : R).

Lemma card_cube_neq0 : N != 0.
Proof. by rewrite pnatr_eq0 card_mx card_ord expn_eq0. Qed.

Lemma sum_bchar_freq y z :
  \sum_(p : cube) bchar R p y * bchar R p z = if y == z then N else 0.
Proof.
rewrite (eq_bigr (fun p => bchar R y p * bchar R z p)) => [p _|].
  by rewrite !(bcharC _ p).
exact: bchar_orthogonal.
Qed.

Lemma eq_fcoef (V : lmodType R) (f g : cube -> V) p :
  f =1 g -> fcoef f p = fcoef g p.
Proof. by move=> fg; rewrite /fcoef; under eq_bigr do rewrite fg. Qed.

Lemma fcoef_inversion (V : lmodType R) (f : cube -> V) y :
  f y = \sum_(p : cube) bchar R p y *: fcoef f p.
Proof.
rewrite /fcoef.
under eq_bigr do rewrite scalerA mulrC -scalerA scaler_sumr.
rewrite -scaler_sumr exchange_big /=.
under eq_bigr => z _ do under eq_bigr => p _ do rewrite scalerA.
under eq_bigr => z _ do rewrite -scaler_suml sum_bchar_freq.
rewrite (bigD1 y) //= eqxx big1 => [z zy|].
  by rewrite eq_sym (negbTE zy) scale0r.
by rewrite addr0 scalerA mulVf ?scale1r // card_cube_neq0.
Qed.

Lemma fcoef_expansion (V : lmodType R) (c : cube -> V) q :
  fcoef (fun y => \sum_(p : cube) bchar R p y *: c p) q = c q.
Proof.
rewrite /fcoef; under eq_bigr do rewrite scaler_sumr.
rewrite exchange_big /=.
under eq_bigr => p _ do under eq_bigr => y _ do rewrite scalerA.
under eq_bigr => p _ do rewrite -scaler_suml bchar_orthogonal.
rewrite (bigD1 q) //= eqxx big1 => [p pq|].
  by rewrite eq_sym (negbTE pq) scale0r.
by rewrite addr0 scalerA mulVf ?scale1r // card_cube_neq0.
Qed.

Lemma fcoef_plancherel (V W Z : lmodType R) (b : V -> W -> Z) :
  (forall w, linear (b^~ w)) -> (forall v, linear (b v)) ->
  forall (f : cube -> V) (g : cube -> W),
  (#|{: cube}|%:R)^-1 *: \sum_(y : cube) b (f y) (g y) =
    \sum_(p : cube) b (fcoef f p) (fcoef g p).
Proof.
move=> bl br f g; rewrite /fcoef.
under [RHS]eq_bigr => p _ do
  rewrite (linearZ_prop _ _ (bl _)) (linear_sum_prop _ _ _ (bl _)).
under [RHS]eq_bigr => p _ do
  under eq_bigr => y _ do rewrite (linearZ_prop _ _ (bl _)).
rewrite -scaler_sumr exchange_big /=; congr (_ *: _); apply: eq_bigr => y _.
rewrite {1}(fcoef_inversion g y) (linear_sum_prop _ _ _ (br _)).
by apply: eq_bigr => p _; rewrite (linearZ_prop _ _ (br _)).
Qed.

Lemma fcoef_linear (V : lmodType R) (c : R) (f g : cube -> V) p :
  fcoef (fun y => c *: f y + g y) p = c *: fcoef f p + fcoef g p.
Proof.
rewrite /fcoef scalerA mulrC -scalerA -scalerDr.
congr (_ *: _); rewrite scaler_sumr -big_split /=.
by apply: eq_bigr => y _; rewrite scalerDr !scalerA mulrC.
Qed.

Lemma fcoef_comp_linear (V W : lmodType R) (h : V -> W) : linear h ->
  forall (f : cube -> V) p, fcoef (fun y => h (f y)) p = h (fcoef f p).
Proof.
move=> hl f p; rewrite /fcoef (linearZ_prop _ _ hl) (linear_sum_prop _ _ _ hl).
by congr (_ *: _); apply: eq_bigr => y _; rewrite (linearZ_prop _ _ hl).
Qed.

Lemma fcoef_mulmx m n k l (A : 'M[R]_(m, n)) (f : cube -> 'M[R]_(n, k))
    (B : 'M[R]_(k, l)) p :
  fcoef (fun y => A *m f y *m B) p = A *m fcoef f p *m B.
Proof.
apply: (@fcoef_comp_linear _ _ (fun M : 'M[R]_(n, k) => A *m M *m B)).
by move=> c u v; rewrite mulmxDr mulmxDl -scalemxAr -scalemxAl.
Qed.

Lemma fcoef_norm_le (f : cube -> R^o) (c : R) p :
  (forall y, `|f y : R| <= c) -> `|fcoef f p : R| <= c.
Proof.
move=> fc; have sE (x : R) (v : R^o) : x *: v = x * v :> R by [].
rewrite /fcoef sE normrM ger0_norm ?invr_ge0 ?ler0n //.
rewrite ler_pdivrMl ?lt_def ?card_cube_neq0 ?ler0n //.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: (@le_trans _ _ (\sum_(y : cube) c)).
  apply: ler_sum => y _; rewrite sE normrM.
  by have [->|->] := bchar_sign R p y; rewrite ?normr1 ?normrN1 mul1r.
by rewrite sumr_const mulr_natl.
Qed.

Lemma fcoef_translate (V : lmodType R) (f : cube -> V) p q :
  fcoef (fun y => bchar R q y *: f y) (p + q) = fcoef f p.
Proof.
rewrite /fcoef; congr (_ *: _); apply: eq_bigr => y _.
by rewrite scalerA bcharD -mulrA bchar_sqr mulr1.
Qed.

Lemma low_blk_deg_expansion (V : lmodType R) (D : nat) (f : cube -> V) :
  low_blk_deg D f <->
  forall y, f y = \sum_(p : cube | (blk_deg p <= D)%N) bchar R p y *: fcoef f p.
Proof.
split => [lowf y|fE p Dp].
  rewrite {1}(fcoef_inversion f y) (bigID (fun p : cube => (blk_deg p <= D)%N)).
  rewrite /= [X in _ + X]big1 ?addr0 // => p; rewrite -ltnNge => Dp.
  by rewrite lowf // scaler0.
pose c (q : cube) := if (blk_deg q <= D)%N then fcoef f q else 0.
have -> : fcoef f p = fcoef (fun y => \sum_(q : cube) bchar R q y *: c q) p.
  apply: eq_fcoef => y; rewrite fE big_mkcond /=.
  by apply: eq_bigr => q _; rewrite /c; case: ifP; rewrite ?scaler0.
by rewrite fcoef_expansion /c leqNgt Dp.
Qed.

Lemma low_blk_deg_translate (V : lmodType R) (D : nat) (f : cube -> V) q :
  (forall p, (D < blk_dist p q)%N -> fcoef f p = 0) ->
  low_blk_deg D (fun y => bchar R q y *: f y).
Proof.
move=> fq s Ds; rewrite -[s in fcoef _ s](addmxF2K s q) fcoef_translate.
by apply: fq; rewrite blk_distE addmxF2K.
Qed.

End coefficients_proofs.

End boolean_cube_proofs.

Lemma blk_dist_row a (s z : 'rV['F_2]_a) : blk_dist s z = (s != z).
Proof.
rewrite /blk_dist; case: (s =P z) => [->|/eqP sz].
  by apply/eqP; rewrite cards_eq0; apply/eqP/setP => i; rewrite !inE eqxx.
rewrite (_ : [set i | _] = setT) ?cardsT ?card_ord //.
by apply/setP => i; rewrite !inE !row_id.
Qed.

Section blocks_proofs.
Variables t1 t2 a : nat.

Lemma bdot_col_mx (p1 y1 : 'M['F_2]_(t1, a)) (p2 y2 : 'M['F_2]_(t2, a)) :
  bdot (col_mx p1 p2) (col_mx y1 y2) = bdot p1 y1 + bdot p2 y2.
Proof.
rewrite /bdot big_split_ord /=; congr (_ + _); apply: eq_bigr => i _;
  by apply: eq_bigr => j _; rewrite ?col_mxEu ?col_mxEd.
Qed.

Lemma bchar_col_mx (R : pzRingType) (p1 y1 : 'M['F_2]_(t1, a))
    (p2 y2 : 'M['F_2]_(t2, a)) :
  bchar R (col_mx p1 p2) (col_mx y1 y2) = bchar R p1 y1 * bchar R p2 y2.
Proof. by rewrite /bchar bdot_col_mx signF2D. Qed.

Lemma blk_deg_col_mx (p1 : 'M['F_2]_(t1, a)) (p2 : 'M['F_2]_(t2, a)) :
  blk_deg (col_mx p1 p2) = (blk_deg p1 + blk_deg p2)%N.
Proof.
rewrite /blk_deg -!sum1dep_card big_split_ord /=.
by congr (_ + _)%N; apply: eq_bigl => i; rewrite ?rowKu ?rowKd.
Qed.

Lemma blk_dist_col_mx (p1 q1 : 'M['F_2]_(t1, a)) (p2 q2 : 'M['F_2]_(t2, a)) :
  blk_dist (col_mx p1 p2) (col_mx q1 q2) = (blk_dist p1 q1 + blk_dist p2 q2)%N.
Proof.
rewrite /blk_dist -!sum1dep_card big_split_ord /=.
by congr (_ + _)%N; apply: eq_bigl => i; rewrite ?rowKu ?rowKd.
Qed.

Lemma blk_col_mx (p1 q1 : 'M['F_2]_(t1, a)) (p2 q2 : 'M['F_2]_(t2, a)) :
  blk_deg (col_mx p1 p2) = (blk_deg p1 + blk_deg p2)%N /\
  blk_dist (col_mx p1 p2) (col_mx q1 q2) = (blk_dist p1 q1 + blk_dist p2 q2)%N.
Proof. by rewrite blk_deg_col_mx blk_dist_col_mx. Qed.

Lemma card_col_mx : #|{: 'M['F_2]_(t1 + t2, a)}| =
  (#|{: 'M['F_2]_(t1, a)}| * #|{: 'M['F_2]_(t2, a)}|)%N.
Proof. by rewrite !card_mx mulnDl expnD. Qed.

Lemma sum_col_mx (V : nmodType) (F : 'M['F_2]_(t1 + t2, a) -> V) :
  \sum_(y : 'M['F_2]_(t1 + t2, a)) F y =
  \sum_(y1 : 'M['F_2]_(t1, a)) \sum_(y2 : 'M['F_2]_(t2, a)) F (col_mx y1 y2).
Proof.
rewrite pair_bigA /= (reindex (fun u : 'M['F_2]_(t1, a) * 'M['F_2]_(t2, a) =>
  col_mx u.1 u.2)) //=.
exists (fun y => (usubmx y, dsubmx y)) => [[y1 y2] _|y _] /=.
  by rewrite col_mxKu col_mxKd.
by rewrite vsubmxK.
Qed.

Lemma fcoef_col_mx (R : numFieldType) (V : lmodType R)
    (f : 'M['F_2]_(t1 + t2, a) -> V) (p1 : 'M['F_2]_(t1, a))
    (p2 : 'M['F_2]_(t2, a)) :
  fcoef f (col_mx p1 p2) =
    fcoef (fun y1 => fcoef (fun y2 => f (col_mx y1 y2)) p2) p1.
Proof.
rewrite /fcoef sum_col_mx card_col_mx natrM invfM -scalerA; congr (_ *: _).
rewrite scaler_sumr; apply: eq_bigr => y1 _.
rewrite scalerA mulrC -scalerA; congr (_ *: _).
rewrite scaler_sumr; apply: eq_bigr => y2 _.
by rewrite bchar_col_mx scalerA.
Qed.

End blocks_proofs.

(* Coefficients of scalings, of products by constant matrices, of entries,
   of block columns and of indicators of points. *)
Section coefficient_tools.
Variables (R : numFieldType) (t a : nat).
Local Notation cube := 'M['F_2]_(t, a).
Implicit Types p q y : cube.

Lemma fcoefZ (V : lmodType R) (c : R) (f : cube -> V) p :
  fcoef (fun y => c *: f y) p = c *: fcoef f p.
Proof.
rewrite /fcoef [RHS]scalerA mulrC -scalerA [X in _ = _ *: X]scaler_sumr.
by congr (_ *: _); apply: eq_bigr => y _; rewrite !scalerA mulrC.
Qed.

Lemma fcoef_mulmxl m n k (A : 'M[R]_(m, n)) (f : cube -> 'M[R]_(n, k)) p :
  fcoef (fun y => A *m f y) p = A *m fcoef f p.
Proof.
by rewrite -[RHS]mulmx1 -fcoef_mulmx; apply: eq_fcoef => y; rewrite mulmx1.
Qed.

Lemma fcoef_entry m n (f : cube -> 'M[R]_(m, n)) p i j :
  (fcoef f p) i j = fcoef (fun y => f y i j : R^o) p.
Proof.
rewrite /fcoef mxE summxE; congr (_ * _); apply: eq_bigr => y _.
by rewrite mxE.
Qed.

Lemma fcoef_mxcol (s : nat) (p_ : 'I_s -> nat) k
    (B : forall i, cube -> 'M[R]_(p_ i, k)) p :
  fcoef (fun y => \mxcol_i B i y) p = \mxcol_i fcoef (B i) p.
Proof.
apply/matrixP => u v; rewrite [RHS]mxE !fcoef_entry.
have E : (fun y => (\mxcol_i B i y) u v : R^o) =1
    (fun y => B (tagnat.sig1 u) y (tagnat.sig2 u) v : R^o).
  by move=> y; rewrite mxE.
exact: (@eq_fcoef t a R R^o _ _ p E).
Qed.

Lemma fcoef_indicator (V : lmodType R) (y0 : cube) (c : R) (v : V) p :
  fcoef (fun y => ((y0 == y)%:R * c) *: v) p =
    ((#|{: cube}|%:R)^-1 * bchar R p y0 * c) *: v.
Proof.
rewrite /fcoef (bigD1 y0) //= eqxx mul1r big1 => [y /negbTE|].
  by rewrite eq_sym => ->; rewrite mul0r scale0r scaler0.
by rewrite addr0 !scalerA.
Qed.

End coefficient_tools.

(* Examples: on one bit, the nonzero character is y |-> (-1)^y; the
   coefficients of a character are 1 at its frequency and 0 elsewhere. *)
Example bchar_one_bit (R : pzRingType) (y : 'F_2) :
  bchar R (const_mx 1 : 'M['F_2]_(1, 1)) (const_mx y) = (-1) ^+ nat_of_ord y.
Proof. by rewrite /bchar /bdot !big_ord1 !mxE mul1r. Qed.

Example fcoef_bchar (R : numFieldType) t a (p q : 'M['F_2]_(t, a)) :
  fcoef (fun y => bchar R q y : R^o) p = (p == q)%:R.
Proof.
rewrite -(@fcoef_expansion t a R R^o (fun s => (s == q)%:R)).
apply: eq_fcoef => y; rewrite (bigD1 q) //= eqxx big1 => [s sq|].
  by rewrite (negbTE sq) scaler0.
by rewrite addr0 [_ *: _]mulr1.
Qed.
