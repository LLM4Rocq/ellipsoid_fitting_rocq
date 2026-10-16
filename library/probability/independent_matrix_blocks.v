From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype measure lebesgue_measure.
From mathcomp Require Import measurable_realfun numfun lebesgue_integral probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows conditioning.
From GaussianAnalysis.probability Require Import independent_row_signs.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.

(**md**************************************************************************)
(* # Independent vertical matrix blocks                                       *)
(*                                                                            *)
(* A matrix with independent, possibly nonidentically distributed rows has    *)
(* independent upper and lower blocks. The reserve block is listed first in  *)
(* the joint law, to match its use with a statistic of the main upper block. *)
(* The statistic is any measurable map. Coordinates within each row may be  *)
(* dependent, and no moments, densities, or positive dimensions are needed. *)
(*                                                                            *)
(* independent_row_matrix_blocks_law == joint law of (lower, upper) blocks   *)
(* independent_row_matrix_statistic_law == law of (lower, f upper)            *)
(*                                                                            *)
(* The proof uses the existing tuple product, concatenation, and row-matrix  *)
(* convention. Product-measure uniqueness carries the separate image laws.  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section tuple_concatenation_law.
Context {e} {T : measurableType e} {R : realType}.

Lemma tuple_prod_cat_law (mu : nat -> probability T R) N k
    (A : set ((N+k).-tuple T)) : measurable A ->
  tuple_prod mu (N+k) A =
  (tuple_prod mu N \x tuple_prod (fun i => mu (N+i)%N) k)%E
    ((fun z : N.-tuple T * k.-tuple T => [tuple of z.1 ++ z.2]) @^-1` A).
Proof.
move=> mA.
pose cat : {mfun (N.-tuple T * k.-tuple T)%type >-> (N+k).-tuple T} :=
  HB.pack (fun z : N.-tuple T * k.-tuple T => [tuple of z.1 ++ z.2])
    (isMeasurableFun.Build _ _ _ _ _ (@measurable_tuple_cat e T N k)).
apply: (@measure_tuple_box_unique _ T (N+k) R (tuple_prod mu (N+k))
  (distribution (tuple_prod mu N \x tuple_prod (fun i=>mu (N+i)%N) k)%E cat)) => //.
- by rewrite /= probability_setT ltry.
- move=> B mB; rewrite /= tuple_prod_box //.
  change ((\prod_(i < N+k) mu i (B i))%E =
    (tuple_prod mu N \x tuple_prod (fun i=>mu (N+i)%N) k)%E
      (cat @^-1` tuple_box B)).
  have -> : cat @^-1` tuple_box B =
      tuple_box (fun i => B (lshift k i)) `*`
      tuple_box (fun j => B (rshift N j)).
    apply/seteqP; split=> [[x y] /= h|[x y] [/= hx hy] i].
    - split=> i; [have := h (lshift k i)|have := h (rshift N i)];
        by rewrite /cat /= ?tnth_lshift ?tnth_rshift.
    - rewrite -[i]splitK; case: (fintype.split i)=>j /=;
        rewrite /cat /= ?tnth_lshift ?tnth_rshift; [exact: hx|exact: hy].
  rewrite product_measure1E.
  + by apply: measurable_tuple_box => i; exact: mB.
  + by apply: measurable_tuple_box => i; exact: mB.
  by rewrite /= !tuple_prod_box // big_split_ord.
Qed.

End tuple_concatenation_law.

Section product_images.
Context {a b c d : measure_display} {T : measurableType a} {U : measurableType b}.
Context {V : measurableType c} {W : measurableType d} {R : realType}.

Lemma product_distribution_swap_law (P : probability T R) (Q : probability U R)
    (f : {mfun T >-> V}) (g : {mfun U >-> W}) (A : set (W*V)) :
  measurable A ->
  (P \x Q)%E ((fun z : T*U => (g z.2,f z.1)) @^-1` A) =
    (distribution Q g \x distribution P f)%E A.
Proof.
move=> mA.
have mh : measurable_fun setT (fun z : T*U => (g z.2,f z.1)).
  apply: measurable_fun_pair.
  - exact: measurableT_comp (measurable_funPT g) measurable_snd.
  - exact: measurableT_comp (measurable_funPT f) measurable_fst.
pose h : {mfun (T*U)%type >-> (W*V)%type} :=
  HB.pack (fun z : T*U => (g z.2,f z.1)) (isMeasurableFun.Build _ _ _ _ _ mh).
symmetry; apply: (@product_measure_unique _ _ W V R
  (distribution Q g) (distribution P f) (distribution (P \x Q)%E h)) => //.
move=> B C mB mC.
change ((P \x Q)%E (h @^-1` (B `*` C)) = Q (g @^-1` B) * P (f @^-1` C))%E.
have -> : h @^-1` (B `*` C) = (f @^-1` C) `*` (g @^-1` B).
  by apply/seteqP; split=> -[x y] /= [h1 h2]; split.
rewrite product_measure1E.
- exact (measurable_funPTI f mC).
- exact (measurable_funPTI g mB).
by rewrite muleC.
Qed.

End product_images.

Section single_row.
Context {R : realType} {d : nat}.

Lemma independent_row_matrix_single_law (mu : nat -> probability 'rV[R]_d R)
    (A : set 'rV[R]_d) : measurable A ->
  independent_row_matrix_law mu 1 A = mu 0%N A.
Proof.
move=> mA; rewrite independent_row_matrix_lawE.
have em (x : 1.-tuple 'rV[R]_d) : restricted_isometry.tuple_mx x = tnth x ord0.
  by apply/matrixP=> i j; rewrite (ord1 i) /restricted_isometry.tuple_mx mxE.
have -> : (@restricted_isometry.tuple_mx R 1 d) @^-1` A = tuple_box (fun _=>A).
  apply/seteqP; split=> x /= h.
  - by move=> i; rewrite (ord1 i); move: h; rewrite em.
  - by rewrite em; exact: (h ord0).
by rewrite tuple_prod_box // big_ord1.
Qed.

End single_row.

Section independent_blocks.
Context {R : realType} {d : nat}.
Variable mu : nat -> probability 'rV[R]_d R.
Variables N k : nat.

Lemma row_tuple_matrix_cat (x : N.-tuple 'rV[R]_d) (y : k.-tuple 'rV[R]_d) :
  row_tuple_matrix (N+k) [tuple of x ++ y] =
    col_mx (row_tuple_matrix N x) (row_tuple_matrix k y).
Proof.
apply/matrixP=> i j; rewrite -[i]splitK; case: (fintype.split i)=>h /=;
  rewrite /row_tuple_matrix /restricted_isometry.tuple_mx /=
    ?col_mxEu ?col_mxEd !mxE ?tnth_lshift ?tnth_rshift; by [].
Qed.

Lemma measurable_independent_matrix_blocks :
  measurable_fun [set: 'M[R]_(N+k,d)] (fun H => (dsubmx H,usubmx H)).
Proof.
by apply: measurable_fun_pair; [exact: measurable_dsubmx|exact: measurable_usubmx].
Qed.

Theorem independent_row_matrix_blocks_law (A : set ('M[R]_(k,d)*'M[R]_(N,d))) :
  measurable A ->
  independent_row_matrix_law mu (N+k)
    ((fun H => (dsubmx H,usubmx H)) @^-1` A) =
  (independent_row_matrix_law (fun i => mu (N+i)%N) k \x
    independent_row_matrix_law mu N)%E A.
Proof.
move=> mA.
have mB : measurable ((fun H : 'M[R]_(N+k,d) => (dsubmx H,usubmx H)) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_independent_matrix_blocks.
have mC : measurable (row_tuple_matrix (N+k) @^-1`
    ((fun H : 'M[R]_(N+k,d) => (dsubmx H,usubmx H)) @^-1` A)).
  exact (measurable_funPTI (row_tuple_matrix (N+k)) mB).
rewrite independent_row_matrix_lawE.
rewrite (@tuple_prod_cat_law _ _ R mu N k _ mC).
have -> : (fun z : N.-tuple 'rV[R]_d * k.-tuple 'rV[R]_d =>
    [tuple of z.1 ++ z.2]) @^-1`
    ((@restricted_isometry.tuple_mx R (N+k) d) @^-1`
    ((fun H : 'M[R]_(N+k,d) => (dsubmx H,usubmx H)) @^-1` A)) =
    (fun z : N.-tuple 'rV[R]_d * k.-tuple 'rV[R]_d =>
      (row_tuple_matrix k z.2,row_tuple_matrix N z.1)) @^-1` A.
  apply/funext=> -[x y] /=.
  change (A (dsubmx (row_tuple_matrix (N+k) [tuple of x ++ y]),
    usubmx (row_tuple_matrix (N+k) [tuple of x ++ y])) =
    A (row_tuple_matrix k y,row_tuple_matrix N x)).
  by rewrite row_tuple_matrix_cat col_mxKd col_mxKu.
exact: product_distribution_swap_law.
Qed.

Lemma measurable_independent_matrix_statistic e (T : measurableType e)
    (f : {mfun 'M[R]_(N,d) >-> T}) :
  measurable_fun [set: 'M[R]_(N+k,d)] (fun H => (dsubmx H,f (usubmx H))).
Proof.
apply: measurable_fun_pair; first exact: measurable_dsubmx.
apply: measurableT_comp (measurable_funPT f) _.
exact: measurable_usubmx.
Qed.

Theorem independent_row_matrix_statistic_law e (T : measurableType e)
    (f : {mfun 'M[R]_(N,d) >-> T}) (A : set ('M[R]_(k,d)*T)) :
  measurable A ->
  independent_row_matrix_law mu (N+k)
    ((fun H => (dsubmx H,f (usubmx H))) @^-1` A) =
  (independent_row_matrix_law (fun i => mu (N+i)%N) k \x
    distribution (independent_row_matrix_law mu N) f)%E A.
Proof.
move=> mA.
have mg : measurable_fun setT (fun z : 'M[R]_(k,d)*'M[R]_(N,d) => (z.1,f z.2)).
  apply: measurable_fun_pair; first exact: measurable_fst.
  exact: measurableT_comp (measurable_funPT f) measurable_snd.
have mB : measurable ((fun z : 'M[R]_(k,d)*'M[R]_(N,d) => (z.1,f z.2)) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: mg.
rewrite (independent_row_matrix_blocks_law mB).
pose g : {mfun ('M[R]_(k,d)*'M[R]_(N,d))%type >-> ('M[R]_(k,d)*T)%type} :=
  HB.pack (fun z : 'M[R]_(k,d)*'M[R]_(N,d) => (z.1,f z.2))
    (isMeasurableFun.Build _ _ _ _ _ mg).
symmetry; apply: (@product_measure_unique _ _ _ _ R
  (independent_row_matrix_law (fun i=>mu (N+i)%N) k)
  (distribution (independent_row_matrix_law mu N) f)
  (distribution (independent_row_matrix_law (fun i=>mu (N+i)%N) k \x
    independent_row_matrix_law mu N)%E g)) => //.
move=> B C mBC mC.
change ((independent_row_matrix_law (fun i=>mu (N+i)%N) k \x
    independent_row_matrix_law mu N)%E (g @^-1` (B `*` C)) =
  independent_row_matrix_law (fun i=>mu (N+i)%N) k B *
  independent_row_matrix_law mu N (f @^-1` C))%E.
have -> : g @^-1` (B `*` C) = B `*` (f @^-1` C) by [].
by rewrite product_measure1E //; exact (measurable_funPTI f mC).
Qed.

(* Events on disjoint row blocks factor, including empty blocks. *)
Corollary independent_matrix_block_events (A : set 'M[R]_(k,d))
    (B : set 'M[R]_(N,d)) : measurable A -> measurable B ->
  independent_row_matrix_law mu (N+k)
    [set H | A (dsubmx H) /\ B (usubmx H)] =
  (independent_row_matrix_law (fun i=>mu (N+i)%N) k A *
    independent_row_matrix_law mu N B)%E.
Proof.
move=> mA mB.
rewrite (independent_row_matrix_blocks_law (measurableX mA mB)).
by rewrite product_measure1E.
Qed.

End independent_blocks.

Section duplicated_row_example.
Context {R : realType}.

(* Each row has two identical Gaussian coordinates. These coordinates are
   fully dependent, while events on the two independently drawn rows factor. *)
Example duplicated_row_block_events (A B : set 'rV[R]_2) :
  measurable A -> measurable B ->
  independent_row_matrix_law (fun=> @duplicated_gaussian_row R) 2
    [set H : 'M[R]_(1+1,2) | A (dsubmx H) /\ B (usubmx H)] =
  (@duplicated_gaussian_row R A * @duplicated_gaussian_row R B)%E.
Proof.
move=> mA mB.
rewrite (@independent_matrix_block_events R 2
  (fun=> @duplicated_gaussian_row R) 1 1 A B mA mB).
by rewrite !independent_row_matrix_single_law.
Qed.

End duplicated_row_example.
