From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum zmodp matrix.

(**md**************************************************************************)
(* # Real Fourier analysis on Boolean products                                *)
(*                                                                            *)
(* The Boolean product 'M['F_2]_(t, a) holds t blocks, its rows, of a bits    *)
(* each, and is a group under addition. A frequency p and a point y have the  *)
(* F_2 pairing p . y = \sum_i \sum_j p_ij y_ij and the character              *)
(* chi_p (y) = (-1)^(p . y), with the values 1 and -1 in any ring. A function *)
(* f with values in a module V over a number field R has the Fourier          *)
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
(* This file holds the definitions and, as Prop definitions, the general      *)
(* statements of packet P of phase 13, for the user's review (AGENTS.md,      *)
(* section Phase 13, step 0, items 3 and 4). Their proofs come after the      *)
(* review. The characters take their values in any ring (pzRingType), and the *)
(* coefficients are over a numFieldType:                                      *)
(* - bchar_algebra_statement: chi_0 = 1, chi_(p + q) = chi_p chi_q,           *)
(*   chi_p (y) = chi_y (p), and chi_p (y) is 1 or -1.                         *)
(* - bchar_orthogonal_statement: \sum_y chi_p (y) chi_q (y) is 2^(t a) if     *)
(*   p = q, and 0 otherwise.                                                  *)
(* - blk_dist_metric_statement: the block distance is a metric, invariant     *)
(*   under translation, and the distance of p and q is the block degree of    *)
(*   p + q.                                                                   *)
(* - blk_dist_row_statement: on one block, the distance of s and z is 1 if    *)
(*   s != z, and 0 otherwise.                                                 *)
(* - fcoef_inversion_statement: the inversion formula.                        *)
(* - fcoef_expansion_statement: the coefficients of                           *)
(*   y |-> \sum_p chi_p (y) c_p are the c_p, so the characters form a basis.  *)
(* - fcoef_plancherel_statement: Plancherel's identity                        *)
(*   2^(-t a) \sum_y b (f y) (g y) = \sum_p b (fcoef f p) (fcoef g p) for     *)
(*   every bilinear map b, for example mxdot or (H, G) |-> H^T G.             *)
(* - fcoef_linear_statement, fcoef_comp_linear_statement and                  *)
(*   fcoef_mulmx_statement: the coefficient is linear in the function, and it *)
(*   commutes with every linear map of the values, in particular with         *)
(*   constant matrix factors on both sides.                                   *)
(* - fcoef_norm_le_statement: the coefficients of a real function are bounded *)
(*   by the supremum of its absolute value.                                   *)
(* - fcoef_translate_statement: multiplication by chi_q translates the        *)
(*   frequency p to p + q.                                                    *)
(* - low_blk_deg_expansion_statement: f has block degree at most D if and     *)
(*   only if it is the sum of its terms of block degree at most D.            *)
(* - low_blk_deg_translate_statement: if the coefficients of f vanish at      *)
(*   block distance larger than D from q, then chi_q f has block degree at    *)
(*   most D. Its squares are those of f, since chi_q (y)^2 = 1.               *)
(* - bchar_col_mx_statement, blk_col_mx_statement and fcoef_col_mx_statement: *)
(*   when col_mx splits 'M['F_2]_(t1 + t2, a) into two groups of blocks, the  *)
(*   character is the product of the two characters, block degrees and        *)
(*   distances add, and a coefficient is an iterated coefficient.             *)
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
(*   over a number field, where the manuscript has real matrices, and the     *)
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

Import GRing.Theory Num.Theory.
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

Section characters.
Variable R : pzRingType.

(* The characters form a symmetric bicharacter with values 1 and -1. *)
Definition bchar_algebra_statement : Prop :=
  [/\ forall y, bchar R 0 y = 1,
      forall p q y, bchar R (p + q) y = bchar R p y * bchar R q y,
      forall p y, bchar R p y = bchar R y p &
      forall p y, bchar R p y = 1 \/ bchar R p y = -1].

(* Orthogonality of the characters for the counting measure. *)
Definition bchar_orthogonal_statement : Prop :=
  forall p q, \sum_(y : cube) bchar R p y * bchar R q y =
    if p == q then #|{: cube}|%:R else 0.

End characters.

(* The block distance is a metric, invariant under translation, and the
   distance of p and q is the block degree of p + q. *)
Definition blk_dist_metric_statement : Prop :=
  [/\ forall p q, blk_dist p q = blk_deg (p + q),
      forall p q, blk_dist p q = 0%N <-> p = q,
      forall p q, blk_dist p q = blk_dist q p,
      forall p q s, (blk_dist p s <= blk_dist p q + blk_dist q s)%N &
      forall p q s, blk_dist (p + s) (q + s) = blk_dist p q].

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

(* Fourier inversion. *)
Definition fcoef_inversion_statement : Prop :=
  forall (V : lmodType R) (f : cube -> V) y,
  f y = \sum_(p : cube) bchar R p y *: fcoef f p.

(* The coefficients of a combination of characters are its weights. *)
Definition fcoef_expansion_statement : Prop :=
  forall (V : lmodType R) (c : cube -> V) q,
  fcoef (fun y => \sum_(p : cube) bchar R p y *: c p) q = c q.

(* Plancherel's identity for every bilinear map b. *)
Definition fcoef_plancherel_statement : Prop :=
  forall (V W Z : lmodType R) (b : V -> W -> Z),
  (forall w, linear (b^~ w)) -> (forall v, linear (b v)) ->
  forall (f : cube -> V) (g : cube -> W),
  (#|{: cube}|%:R)^-1 *: \sum_(y : cube) b (f y) (g y) =
    \sum_(p : cube) b (fcoef f p) (fcoef g p).

(* The coefficient is linear in the function. *)
Definition fcoef_linear_statement : Prop :=
  forall (V : lmodType R) (c : R) (f g : cube -> V) p,
  fcoef (fun y => c *: f y + g y) p = c *: fcoef f p + fcoef g p.

(* The coefficient commutes with the linear maps of the values. *)
Definition fcoef_comp_linear_statement : Prop :=
  forall (V W : lmodType R) (h : V -> W), linear h ->
  forall (f : cube -> V) p, fcoef (fun y => h (f y)) p = h (fcoef f p).

(* The coefficient commutes with constant matrix factors. *)
Definition fcoef_mulmx_statement : Prop :=
  forall m n k l (A : 'M[R]_(m, n)) (f : cube -> 'M[R]_(n, k))
    (B : 'M[R]_(k, l)) p,
  fcoef (fun y => A *m f y *m B) p = A *m fcoef f p *m B.

(* A coefficient of a real function is bounded by the supremum of its
   absolute value. *)
Definition fcoef_norm_le_statement : Prop :=
  forall (f : cube -> R^o) (c : R) p,
  (forall y, `|f y : R| <= c) -> `|fcoef f p : R| <= c.

(* Multiplication by chi_q translates the frequency p to p + q. *)
Definition fcoef_translate_statement : Prop :=
  forall (V : lmodType R) (f : cube -> V) p q,
  fcoef (fun y => bchar R q y *: f y) (p + q) = fcoef f p.

(* f has block degree at most D iff it is the sum of its terms of block
   degree at most D. *)
Definition low_blk_deg_expansion_statement : Prop :=
  forall (V : lmodType R) (D : nat) (f : cube -> V),
  low_blk_deg D f <->
  forall y, f y = \sum_(p : cube | (blk_deg p <= D)%N) bchar R p y *: fcoef f p.

(* If the spectrum of f lies within block distance D of q, then chi_q f has
   block degree at most D. *)
Definition low_blk_deg_translate_statement : Prop :=
  forall (V : lmodType R) (D : nat) (f : cube -> V) q,
  (forall p, (D < blk_dist p q)%N -> fcoef f p = 0) ->
  low_blk_deg D (fun y => bchar R q y *: f y).

End coefficients.

End boolean_cube.

(* On one block, the distance of s and z is 1 if s != z and 0 otherwise. *)
Definition blk_dist_row_statement : Prop :=
  forall a (s z : 'rV['F_2]_a), blk_dist s z = (s != z).

Section blocks.
Variables t1 t2 a : nat.

(* Splitting the blocks with col_mx: the character is a product, ... *)
Definition bchar_col_mx_statement : Prop :=
  forall (R : pzRingType) (p1 y1 : 'M['F_2]_(t1, a))
    (p2 y2 : 'M['F_2]_(t2, a)),
  bchar R (col_mx p1 p2) (col_mx y1 y2) = bchar R p1 y1 * bchar R p2 y2.

(* ... block degrees and distances add, ... *)
Definition blk_col_mx_statement : Prop :=
  forall (p1 q1 : 'M['F_2]_(t1, a)) (p2 q2 : 'M['F_2]_(t2, a)),
  blk_deg (col_mx p1 p2) = (blk_deg p1 + blk_deg p2)%N /\
  blk_dist (col_mx p1 p2) (col_mx q1 q2) = (blk_dist p1 q1 + blk_dist p2 q2)%N.

(* ... and a coefficient is an iterated coefficient. *)
Definition fcoef_col_mx_statement : Prop :=
  forall (R : numFieldType) (V : lmodType R)
    (f : 'M['F_2]_(t1 + t2, a) -> V) (p1 : 'M['F_2]_(t1, a))
    (p2 : 'M['F_2]_(t2, a)),
  fcoef f (col_mx p1 p2) =
    fcoef (fun y1 => fcoef (fun y2 => f (col_mx y1 y2)) p2) p1.

End blocks.

(* An example: on one bit, the nonzero character is y |-> (-1)^y. *)
Example bchar_one_bit (R : pzRingType) (y : 'F_2) :
  bchar R (const_mx 1 : 'M['F_2]_(1, 1)) (const_mx y) = (-1) ^+ nat_of_ord y.
Proof. by rewrite /bchar /bdot !big_ord1 !mxE mul1r. Qed.
