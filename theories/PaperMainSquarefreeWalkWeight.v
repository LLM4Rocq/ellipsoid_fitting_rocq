(* Multiplicities and weights of square-free walk words.
   For a word w of coordinate indices below D, with n_c = count of c in w:
   - pmsw_moment D w <= (size w) ^ (sum_c (n_c / 2 - [n_c > 0]))
     (pmsw_moment_le), from (m - 1)!! <= m ^ (m / 2 - 1) for even m >= 2.
     The exponent is the multiplicity excess. When every n_c is even, it is
     0 exactly when every occurring coordinate occurs twice.
   - For the walk words of PaperMainSquarefreeWalkExpansion: the steps of a
     walk i, t, j are the consecutive row pairs (pmsw_rows). The coordinate
     r * d + c occurs in the edge of a step (i, k) with labels p = (a, b)
     exactly ([i = r] + [k = r]) ([a = c] + [b = c]) times
     (pmsw_count_edge), so along a walk its multiplicity is the sum of
     these over the steps (pmsw_count_word): the degree of row r in the
     steps whose labels contain c. The moment vanishes unless all these
     degrees are even (pmsw_word_moment_even). A walk word has 4 entries
     per step (pmsw_word_size). *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianDefinitions PaperMainDiagonalBlockMoment
  PaperMainSquarefreeWalkMoments PaperMainSquarefreeWalkExpansion.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. The weight of a word. *)
Lemma pmsw_mf_le_pow n : moment_factor n.+1.*2 <= (n.+1.*2)%:R ^+ n.
Proof.
elim: n => [|n IH].
  by rewrite doubleS pmdm_mfS pmdm_mf0 expr0 mulr1 mulr1n.
rewrite (doubleS n.+1) pmdm_mfS exprS.
have H0 : 0 <= moment_factor n.+1.*2 by apply: ltW; exact: pmsw_mf_even_double.
have H1 : (n.+1.*2.+1)%:R <= (n.+2.*2)%:R :> R by rewrite ler_nat doubleS.
have H2 : (n.+1.*2)%:R ^+ n <= (n.+2.*2)%:R ^+ n :> R.
  apply: lerXn2r.
  - by rewrite nnegrE ler0n.
  - by rewrite nnegrE ler0n.
  - by rewrite ler_nat leq_double.
apply: ler_pM; [exact: ler0n | exact: H0 | exact: H1 | exact: le_trans IH H2].
Qed.

Lemma pmsw_mf_count_le S m : ~~ odd m -> (m <= S)%N ->
  moment_factor m <= S%:R ^+ (m./2 - (0 < m))%N.
Proof.
move=> Hm HmS.
have Em : m = (m./2).*2 by rewrite -{1}(odd_double_half m) (negbTE Hm).
move: HmS; rewrite Em; case: (m./2) => [|n] HmS.
  by rewrite pmdm_mf0 expr0.
rewrite doubleK subn1 /=.
apply: (le_trans (pmsw_mf_le_pow n)).
by apply: lerXn2r; rewrite ?nnegrE ?ler0n // ler_nat.
Qed.

Theorem pmsw_moment_le D w :
  pmsw_moment D w <=
  (size w)%:R ^+ (\sum_(c < D) ((count_mem (c : nat) w)./2 - (0 < count_mem (c : nat) w)))%N.
Proof.
case Hodd: [exists c : 'I_D, odd (count_mem (c : nat) w)].
  case/existsP: Hodd => c Hc.
  by rewrite (paper_main_monomial_moment_odd D w c Hc) exprn_ge0 // ler0n.
have Hev (c : 'I_D) : ~~ odd (count_mem (c : nat) w).
  apply/negP => Hc; move/negbT: Hodd; rewrite negb_exists => /forallP /(_ c).
  by rewrite Hc.
rewrite /pmsw_moment (big_morph _ (exprD (size w)%:R) (expr0 _)).
apply: ler_prod => c _; apply/andP; split; first exact: pmsw_mf_ge0.
by apply: pmsw_mf_count_le => //; exact: count_size.
Qed.

(* 2. Coordinates and edges. *)
Lemma pmsw_coord_eq d (i r : nat) (a c : 'I_d) :
  (pmsw_coord d i a == pmsw_coord d r c) = (i == r) && (a == c).
Proof.
rewrite /pmsw_coord; apply/eqP/andP => [H | [/eqP -> /eqP -> //]].
have Hd : (0 < d)%N by exact: leq_ltn_trans (leq0n a) (ltn_ord a).
have Hm := congr1 (fun n => n %% d) H.
have Hq := congr1 (fun n => n %/ d) H.
rewrite /= !modnMDl !modn_small ?ltn_ord // in Hm.
rewrite /= !divnMDl // !divn_small ?ltn_ord // !addn0 in Hq.
by split; apply/eqP => //; apply: val_inj.
Qed.

Lemma pmsw_count_edge d (i k r : nat) (p : 'I_d * 'I_d) (c : 'I_d) :
  count_mem (pmsw_coord d r c) (pmsw_edge d i k p) =
  (((i == r) + (k == r)) * ((p.1 == c) + (p.2 == c)))%N.
Proof.
rewrite /pmsw_edge /= !pmsw_coord_eq.
by case: (i == r); case: (k == r); case: (p.1 == c); case: (p.2 == c).
Qed.

(* 3. Multiplicities along walks. *)
Definition pmsw_rows N (i : 'I_N) (t : seq 'I_N) (j : 'I_N) : seq ('I_N * 'I_N) :=
  zip (i :: t) (rcons t j).

Lemma pmsw_rows_cons N (i k : 'I_N) t j :
  pmsw_rows N i (k :: t) j = (i, k) :: pmsw_rows N k t j.
Proof. by []. Qed.

Theorem pmsw_count_word N d (r : nat) (c : 'I_d) (i : 'I_N) t (j : 'I_N) ps :
  size ps = (size t).+1 ->
  count_mem (pmsw_coord d r c) (pmsw_word N d i t j ps) =
  (\sum_(ep <- zip (pmsw_rows N i t j) ps)
    ((ep.1.1 == r :> nat) + (ep.1.2 == r :> nat)) * ((ep.2.1 == c) + (ep.2.2 == c)))%N.
Proof.
elim: t i ps => [|k t IH] i [|p ps] // Hs.
  case: ps Hs => // _.
  rewrite [pmsw_word _ _ _ _ _ _]/= pmsw_count_edge.
  by rewrite /pmsw_rows /= big_cons big_nil addn0.
have Ew : pmsw_word N d i (k :: t) j (p :: ps) =
    pmsw_edge d i k p ++ pmsw_word N d k t j ps by [].
have Hs' : size ps = (size t).+1 by case: Hs.
rewrite Ew count_cat pmsw_count_edge (IH k ps Hs').
by rewrite pmsw_rows_cons /= big_cons.
Qed.

Lemma pmsw_word_coord_lt N d (r : 'I_N) (c : 'I_d) : (pmsw_coord d r c < N * d)%N.
Proof. exact: pmdm_index_lt (ltn_ord r) (ltn_ord c). Qed.

Theorem pmsw_word_moment_even N d (i : 'I_N) t (j : 'I_N) ps :
  size ps = (size t).+1 ->
  pmsw_moment (N * d) (pmsw_word N d i t j ps) != 0 ->
  forall (r : 'I_N) (c : 'I_d),
  ~~ odd (\sum_(ep <- zip (pmsw_rows N i t j) ps)
    ((ep.1.1 == r :> nat) + (ep.1.2 == r :> nat)) * ((ep.2.1 == c) + (ep.2.2 == c)))%N.
Proof.
move=> Hs Hm r c; rewrite -(pmsw_count_word N d r c i t j ps Hs).
apply/negP => Hodd; move/eqP: Hm; apply.
exact: (paper_main_monomial_moment_odd (N * d) _ (Ordinal (pmsw_word_coord_lt N d r c)) Hodd).
Qed.

Lemma pmsw_word_size N d (i : 'I_N) t (j : 'I_N) ps : size ps = (size t).+1 ->
  size (pmsw_word N d i t j ps) = (4 * size ps)%N.
Proof.
elim: t i ps => [|k t IH] i [|p ps] // Hs.
  by case: ps Hs.
have Hs' : size ps = (size t).+1 by case: Hs.
have Ew : pmsw_word N d i (k :: t) j (p :: ps) =
    pmsw_edge d i k p ++ pmsw_word N d k t j ps by [].
by rewrite Ew size_cat (IH k ps Hs') /= mulnS.
Qed.
