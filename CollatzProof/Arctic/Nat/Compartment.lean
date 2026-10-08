/-
# The basics of Definition 10.1: relevant indices, components, types

The definitions of Definition 10.1 on value automata `ValAuto Q` (`ValueAuto.lean`). Here `û`, `v̂` and `B_b` are the vectors $u$, $c$ and the matrices $N_b$ of Definition 10.1.
They depend neither on $\mathcal T$ (`S_T`) nor on rewriting rules (statements about automata only).
The lift `Ñ` (Lemma 10.6) is not an interpretation, so the objects of Section 11 and Appendix D are treated in this general form.

* **Paths** (§1): `Conn A i j` (a word `w` with `(B_w)_{ij} ≥ 1`; the empty word gives `i = j`). `Reach` (reachable from `supp û`), `CoReach`
  (can reach `supp v̂`), and the **relevant indices** `Rel` (Definition 10.1(a)).
* **Path-closed sets** (§2): `PathConvex A S` (the indices on a path between two points of `S` lie in `S`). The set of relevant indices
  `relSet A` and the strongly connected components `sccOf A q` are path-closed. For a path-closed set the product of the restrictions is the restriction of the product
  (`DxN_restrict`: "`D^K_w` is a principal submatrix of `B_w` and equals the product of the restrictions"). The value does not change under the restriction to the relevant indices
  (`aval_restrictRel`).
* **Components** (§3): `IsComp A C` (a strongly connected component of relevant indices with an internal edge, Definition 10.1(b)), `compMat A C` (`D^C_b`),
  `DC A C w` (`D^C_w`, the product of the restrictions), strong connectivity `Rigid.SC` of Appendix D (`sc_compMat`), and `g ≥ 1` from an internal edge
  (`one_le_gComp`). `g_C` is the diagonal definition `Rigid.gDiag` of Appendix D (the equivalence with a spectral definition is
  `isRigid_iff_spectral` in `RigidSpec.lean`).
* **Types** (§4): `AC A C := D^C_0 + D^C_1`, `L*_C` (`LStar`), survivable (`Survivable`), a word that kills (`Kills`), 0/1
  (`ZeroOne`), bounded complexity (`BoundedCx`), the paraphrase `RhoLt` of `ρ(A_C) < c` (for some `L ≥ 1` the sum of the entries of `A^L` is
  less than `c^L`; the sum of the entries is a submultiplicative norm, so by Gelfand's formula this is equivalent to `ρ < c`; the equivalence with the spectral radius
  is not proved), and the types (Z), (P), (L), (Hb), (Hu).
* `π_C`, `u*`, Lemma 10.7, the counting and (A^rel) of the remark after Corollary 10.9 are in `CompartmentPi.lean`.
-/
import CollatzProof.Arctic.Nat.ValueAuto
import CollatzProof.Arctic.Nat.RigidBound
import CollatzProof.Arctic.MinIdeal

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix

set_option linter.unusedSectionVars false

section Paths

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## §1 Paths and relevant indices -/

theorem DxN_apply_cons (D : Fin 2 → Matrix Q Q ℕ) (b : Fin 2) (w : List (Fin 2)) (i j : Q) :
    Rigid.DxN D (b :: w) i j = ∑ k, D b i k * Rigid.DxN D w k j := by
  rw [DxN_cons', Matrix.mul_apply]

theorem le_DxN_append (D : Fin 2 → Matrix Q Q ℕ) (w w' : List (Fin 2)) (i k j : Q) :
    Rigid.DxN D w i k * Rigid.DxN D w' k j ≤ Rigid.DxN D (w ++ w') i j := by
  rw [DxN_append', Matrix.mul_apply]
  exact Finset.single_le_sum (f := fun k => Rigid.DxN D w i k * Rigid.DxN D w' k j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem one_le_DxN_append {D : Fin 2 → Matrix Q Q ℕ} {w w' : List (Fin 2)} {i k j : Q}
    (h1 : 1 ≤ Rigid.DxN D w i k) (h2 : 1 ≤ Rigid.DxN D w' k j) : 1 ≤ Rigid.DxN D (w ++ w') i j :=
  le_trans (by nlinarith) (le_DxN_append D w w' i k j)

theorem exists_mid_of_append {D : Fin 2 → Matrix Q Q ℕ} {w w' : List (Fin 2)} {i j : Q}
    (h : 1 ≤ Rigid.DxN D (w ++ w') i j) : ∃ k, 1 ≤ Rigid.DxN D w i k ∧ 1 ≤ Rigid.DxN D w' k j := by
  rw [DxN_append', Matrix.mul_apply] at h
  by_contra hc
  push Not at hc
  have : ∑ k, Rigid.DxN D w i k * Rigid.DxN D w' k j = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rcases Nat.lt_or_ge (Rigid.DxN D w i k) 1 with h1 | h1
      · simp [Nat.lt_one_iff.1 h1]
      · simp [Nat.lt_one_iff.1 (hc k h1)]
  omega

variable (A : ValAuto Q)

/-- `j` is reachable from `i` by a word: `(B_w)_{ij} ≥ 1` for some word `w` (the empty word gives `i = j`). -/
def Conn (i j : Q) : Prop := ∃ w : List (Fin 2), 1 ≤ Rigid.DxN A.B w i j

theorem conn_refl (i : Q) : Conn A i i := ⟨[], by simp⟩

theorem conn_trans {i k j : Q} (h1 : Conn A i k) (h2 : Conn A k j) : Conn A i j := by
  obtain ⟨w, hw⟩ := h1
  obtain ⟨w', hw'⟩ := h2
  exact ⟨w ++ w', one_le_DxN_append hw hw'⟩

theorem conn_of_DxN {w : List (Fin 2)} {i j : Q} (h : 1 ≤ Rigid.DxN A.B w i j) : Conn A i j := ⟨w, h⟩

theorem conn_of_edge {b : Fin 2} {i j : Q} (h : 1 ≤ A.B b i j) : Conn A i j :=
  ⟨[b], by simpa [Rigid.DxN] using h⟩

/-- The indices reachable from `supp û`. -/
def Reach (q : Q) : Prop := ∃ i, 1 ≤ A.u i ∧ Conn A i q

/-- The indices that can reach `supp v̂`. -/
def CoReach (q : Q) : Prop := ∃ j, Conn A q j ∧ 1 ≤ A.v j

/-- **Relevant indices** (Definition 10.1(a)): the indices reachable from `supp û` by a path of binary digits that can reach
`supp v̂`. -/
def Rel (q : Q) : Prop := Reach A q ∧ CoReach A q

theorem reach_of_conn {q q' : Q} (h : Reach A q) (hc : Conn A q q') : Reach A q' := by
  obtain ⟨i, hi, hiq⟩ := h
  exact ⟨i, hi, conn_trans A hiq hc⟩

theorem coReach_of_conn {q q' : Q} (h : CoReach A q') (hc : Conn A q q') : CoReach A q := by
  obtain ⟨j, hj, hjv⟩ := h
  exact ⟨j, conn_trans A hc hj, hjv⟩

/-- An index on a path between two relevant indices is relevant. -/
theorem rel_of_between {x y m : Q} (hx : Rel A x) (hy : Rel A y) (h1 : Conn A x m) (h2 : Conn A m y) :
    Rel A m :=
  ⟨reach_of_conn A hx.1 h1, coReach_of_conn A hy.2 h2⟩

/-! ## §2 Path-closed sets and restrictions -/

/-- A path-closed set: the indices on a path between two points of `S` lie in `S`. -/
def PathConvex (S : Finset Q) : Prop := ∀ x ∈ S, ∀ y ∈ S, ∀ m, Conn A x m → Conn A m y → m ∈ S

open Classical in
/-- The set of relevant indices. -/
noncomputable def relSet : Finset Q := Finset.univ.filter (Rel A)

theorem mem_relSet {q : Q} : q ∈ relSet A ↔ Rel A q := by
  classical
  simp [relSet]

theorem relSet_convex : PathConvex A (relSet A) := by
  intro x hx y hy m h1 h2
  rw [mem_relSet] at hx hy ⊢
  exact rel_of_between A hx hy h1 h2

open Classical in
/-- The strongly connected component of `q` (the set of indices that can reach `q` and be reached from it). -/
noncomputable def sccOf (q : Q) : Finset Q := Finset.univ.filter (fun x => Conn A q x ∧ Conn A x q)

theorem mem_sccOf {q x : Q} : x ∈ sccOf A q ↔ Conn A q x ∧ Conn A x q := by
  classical
  simp [sccOf]

theorem self_mem_sccOf (q : Q) : q ∈ sccOf A q := (mem_sccOf A).2 ⟨conn_refl A q, conn_refl A q⟩

theorem sccOf_convex (q : Q) : PathConvex A (sccOf A q) := by
  intro x hx y hy m h1 h2
  rw [mem_sccOf] at hx hy ⊢
  exact ⟨conn_trans A hx.1 h1, conn_trans A h2 hy.2⟩

theorem conn_of_mem_sccOf {q x y : Q} (hx : x ∈ sccOf A q) (hy : y ∈ sccOf A q) : Conn A x y := by
  rw [mem_sccOf] at hx hy
  exact conn_trans A hx.2 hy.1

/-- The strongly connected component of a relevant index consists of relevant indices. -/
theorem rel_of_mem_sccOf {q x : Q} (hq : Rel A q) (hx : x ∈ sccOf A q) : Rel A x := by
  rw [mem_sccOf] at hx
  exact rel_of_between A hq hq hx.1 hx.2

/-- Strongly connected components are equivalence classes: if `x ∈ sccOf A q`, then `sccOf A x = sccOf A q` (required for Section 12). -/
theorem sccOf_eq_of_mem {q x : Q} (hx : x ∈ sccOf A q) : sccOf A x = sccOf A q := by
  rw [mem_sccOf] at hx
  ext y
  rw [mem_sccOf, mem_sccOf]
  exact ⟨fun h => ⟨conn_trans A hx.1 h.1, conn_trans A h.2 hx.2⟩,
    fun h => ⟨conn_trans A hx.2 h.1, conn_trans A h.2 hx.1⟩⟩

/-- An index on a path of positive weight is relevant (required for Section 12). -/
theorem rel_of_pos_path {i j k : Q} {w w' : List (Fin 2)} (hu : 1 ≤ A.u i)
    (h1 : 1 ≤ Rigid.DxN A.B w i k) (h2 : 1 ≤ Rigid.DxN A.B w' k j) (hv : 1 ≤ A.v j) : Rel A k :=
  ⟨⟨i, hu, conn_of_DxN A h1⟩, ⟨j, conn_of_DxN A h2, hv⟩⟩

open Classical in
/-- A potential on the DAG of components: the number of indices reachable from `q` (required for Section 12; of the type of the arctic `UpperPath.reachCard`). -/
noncomputable def reachCnt (q : Q) : ℕ := (Finset.univ.filter (Conn A q)).card

/-- Passing to another component strictly decreases the number of reachable indices. -/
theorem reachCnt_lt {i j : Q} (h : Conn A i j) (hj : j ∉ sccOf A i) : reachCnt A j < reachCnt A i := by
  classical
  unfold reachCnt
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact conn_trans A h hx
  · have hi : i ∈ Finset.univ.filter (Conn A i) := by simp [conn_refl]
    have hji : Conn A j i := by simpa using hsub hi
    exact hj ((mem_sccOf A).2 ⟨h, hji⟩)

/-- The restriction of the digit matrices to a set `S`. -/
def restrictB (S : Finset Q) (b : Fin 2) : Matrix S S ℕ := (A.B b).submatrix Subtype.val Subtype.val

/-- **The product of the restrictions is the restriction of the product** (for a path-closed set): `D^S_w = (B_w)|_{S×S}`. -/
theorem DxN_restrict {S : Finset Q} (hS : PathConvex A S) :
    ∀ w : List (Fin 2), Rigid.DxN (restrictB A S) w = (Rigid.DxN A.B w).submatrix Subtype.val Subtype.val
  | [] => by
    ext x y
    simp only [DxN_nil', Matrix.submatrix_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · have h' : x.1 ≠ y.1 := fun h' => h (Subtype.ext h')
      simp [h, h']
  | b :: w => by
    ext x y
    rw [DxN_cons', Matrix.mul_apply, DxN_restrict hS w]
    simp only [Matrix.submatrix_apply, restrictB]
    rw [DxN_apply_cons]
    rw [Finset.sum_coe_sort S (fun k => A.B b x.1 k * Rigid.DxN A.B w k y.1)]
    refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
    by_contra hne
    have h1 : 1 ≤ A.B b x.1 k := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    have h2 : 1 ≤ Rigid.DxN A.B w k y.1 := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    exact hk (hS x.1 x.2 y.1 y.2 k (conn_of_edge A h1) (conn_of_DxN A h2))

/-- The automaton restricted to the relevant indices (the restriction $\mathcal N^{\mathrm{rel}}$ of Definition 10.1(a)). -/
noncomputable def restrictRel : ValAuto (relSet A) where
  B := restrictB A (relSet A)
  u x := A.u x.1
  v x := A.v x.1

/-- **The value does not change under the restriction to the relevant indices**. -/
theorem aval_restrictRel (ω : List (Fin 2)) : aval (restrictRel A) ω = aval A ω := by
  rw [aval_eq_sum, aval_eq_sum]
  simp only [restrictRel, DxN_restrict A (relSet_convex A), Matrix.submatrix_apply]
  rw [Finset.sum_coe_sort (relSet A) (fun i => ∑ j : relSet A, A.u i * Rigid.DxN A.B ω i j * A.v j)]
  refine Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => ?_) |>.trans ?_
  · refine Finset.sum_eq_zero fun j _ => ?_
    by_contra hne
    apply hi
    rw [mem_relSet]
    have hu : 1 ≤ A.u i := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    have hB : 1 ≤ Rigid.DxN A.B ω i j := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    have hv : 1 ≤ A.v j := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    exact ⟨⟨i, hu, conn_refl A i⟩, ⟨j, conn_of_DxN A hB, hv⟩⟩
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_coe_sort (relSet A) (fun j => A.u i * Rigid.DxN A.B ω i j * A.v j)]
    refine Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ?_)
    by_contra hne
    apply hj
    rw [mem_relSet]
    have hu : 1 ≤ A.u i := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    have hB : 1 ≤ Rigid.DxN A.B ω i j := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    have hv : 1 ≤ A.v j := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    exact ⟨⟨i, hu, conn_of_DxN A hB⟩, ⟨j, conn_refl A j, hv⟩⟩

/-- A lower bound for the value: a path through the index `a` (the placement step in Section 11).
`aval A (p ++ ω ++ s) ≥ (û B_p)_a (B_ω)_{aa} (B_s v̂)_a`. -/
theorem aval_ge_path (p ω s : List (Fin 2)) (a : Q) :
    (A.u ᵥ* Rigid.DxN A.B p) a * Rigid.DxN A.B ω a a * (Rigid.DxN A.B s *ᵥ A.v) a ≤
      aval A (p ++ ω ++ s) := by
  have key : ∀ i j, Rigid.DxN A.B p i a * Rigid.DxN A.B ω a a * Rigid.DxN A.B s a j ≤
      Rigid.DxN A.B (p ++ ω ++ s) i j := by
    intro i j
    calc Rigid.DxN A.B p i a * Rigid.DxN A.B ω a a * Rigid.DxN A.B s a j
        ≤ Rigid.DxN A.B (p ++ ω) i a * Rigid.DxN A.B s a j :=
          Nat.mul_le_mul_right _ (le_DxN_append _ _ _ _ _ _)
      _ ≤ Rigid.DxN A.B (p ++ ω ++ s) i j := le_DxN_append _ _ _ _ _ _
  have e1 : (A.u ᵥ* Rigid.DxN A.B p) a = ∑ i, A.u i * Rigid.DxN A.B p i a := rfl
  have e2 : (Rigid.DxN A.B s *ᵥ A.v) a = ∑ j, Rigid.DxN A.B s a j * A.v j := rfl
  rw [aval_eq_sum, e1, e2, Finset.sum_mul, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  calc A.u i * Rigid.DxN A.B p i a * Rigid.DxN A.B ω a a * (Rigid.DxN A.B s a j * A.v j)
      = A.u i * (Rigid.DxN A.B p i a * Rigid.DxN A.B ω a a * Rigid.DxN A.B s a j) * A.v j := by ring
    _ ≤ A.u i * Rigid.DxN A.B (p ++ ω ++ s) i j * A.v j :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (key i j))

/-- A relevant index `a` has a word `p` from the start to `a` (`(û B_p)_a ≥ 1`) and a word `s` from `a` to the exit (`(B_s v̂)_a ≥ 1`)
(the words `p₀`, `s` of the placement step in Section 11). -/
theorem rel_exists_words {a : Q} (h : Rel A a) :
    ∃ p s : List (Fin 2), 1 ≤ (A.u ᵥ* Rigid.DxN A.B p) a ∧ 1 ≤ (Rigid.DxN A.B s *ᵥ A.v) a := by
  obtain ⟨⟨i, hi, p, hp⟩, ⟨j, ⟨s, hs⟩, hj⟩⟩ := h
  refine ⟨p, s, ?_, ?_⟩
  · simp only [vecMul, dotProduct]
    exact le_trans (by nlinarith) (Finset.single_le_sum (f := fun k => A.u k * Rigid.DxN A.B p k a)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  · simp only [mulVec, dotProduct]
    exact le_trans (by nlinarith) (Finset.single_le_sum (f := fun k => Rigid.DxN A.B s a k * A.v k)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))

/-! ## §3 Components -/

/-- An internal edge: two points `x, y` of `C` and a digit `b` with `(B_b)_{xy} ≥ 1`. -/
def HasEdge (C : Finset Q) : Prop := ∃ x ∈ C, ∃ y ∈ C, ∃ b : Fin 2, 1 ≤ A.B b x y

/-- **Component** (Definition 10.1(b)): a strongly connected component of relevant indices with an internal edge. The strongly connected components of the relevant indices
are strongly connected components of the whole automaton (`relSet_convex`), so we write them as `sccOf A q` (with `q` relevant). -/
def IsComp (C : Finset Q) : Prop := (∃ q, Rel A q ∧ C = sccOf A q) ∧ HasEdge A C

/-- The digit matrices `D^C_b` of a component (the `C × C` principal submatrix of `B_b`). -/
abbrev compMat (C : Finset Q) : Fin 2 → Matrix C C ℕ := restrictB A C

/-- `D^C_w` (the product of the restrictions). -/
abbrev DC (C : Finset Q) (w : List (Fin 2)) : Matrix C C ℕ := Rigid.DxN (compMat A C) w

theorem DC_append (C : Finset Q) (w w' : List (Fin 2)) : DC A C (w ++ w') = DC A C w * DC A C w' :=
  DxN_append' _ w w'

theorem DC_eq_submatrix (q : Q) (w : List (Fin 2)) :
    DC A (sccOf A q) w = (Rigid.DxN A.B w).submatrix Subtype.val Subtype.val :=
  DxN_restrict A (sccOf_convex A q) w

theorem DC_apply (q : Q) (w : List (Fin 2)) (x y : sccOf A q) :
    DC A (sccOf A q) w x y = Rigid.DxN A.B w x.1 y.1 := by
  rw [DC_eq_submatrix]; rfl

/-- The pair of matrices of a component is strongly connected (`Rigid.SC` of Appendix D). -/
theorem sc_compMat (q : Q) : Rigid.SC (compMat A (sccOf A q)) := by
  intro x y
  obtain ⟨c, hc⟩ := conn_of_mem_sccOf A x.2 y.2
  refine ⟨c, ?_⟩
  rw [Rigid.Dx_apply]
  have : Rigid.DxN (compMat A (sccOf A q)) c x y = Rigid.DxN A.B c x.1 y.1 := DC_apply A q c x y
  rw [this]
  exact_mod_cast hc

/-- A strongly connected component with an internal edge has `g ≥ 1` (the diagonal `g` of Appendix D). -/
theorem one_le_gComp (q : Q) (h : HasEdge A (sccOf A q)) : 1 ≤ Rigid.gDiag (compMat A (sccOf A q)) := by
  obtain ⟨x, hx, y, hy, b, hb⟩ := h
  obtain ⟨c, hc⟩ := conn_of_mem_sccOf A hy hx
  refine Rigid.one_le_gDiag _ ⟨b :: c, by simp, ⟨x, hx⟩, ?_⟩
  rw [Rigid.Dx_apply]
  have : Rigid.DxN (compMat A (sccOf A q)) (b :: c) ⟨x, hx⟩ ⟨x, hx⟩ = Rigid.DxN A.B (b :: c) x x :=
    DC_apply A q (b :: c) ⟨x, hx⟩ ⟨x, hx⟩
  rw [this]
  have h2 : 1 ≤ Rigid.DxN A.B ([b] ++ c) x x :=
    one_le_DxN_append (by simpa [Rigid.DxN] using hb) hc
  exact_mod_cast h2

/-- The restriction to a component without internal edges is 0 (required for Section 12). -/
theorem compMat_eq_zero_of_not_hasEdge (q : Q) (h : ¬ HasEdge A (sccOf A q)) (b : Fin 2) :
    compMat A (sccOf A q) b = 0 := by
  ext x y
  simp only [restrictB, Matrix.submatrix_apply, Matrix.zero_apply]
  by_contra hne
  exact h ⟨x.1, x.2, y.1, y.2, b, Nat.one_le_iff_ne_zero.2 hne⟩

/-- The real product of a word on a component (`Rigid.Dx` of Appendix D) is the principal submatrix of `B_w` cast to the reals (the form passed to `heavy_family` in Section 11). -/
theorem Dx_compMat (q : Q) (w : List (Fin 2)) :
    Rigid.Dx (compMat A (sccOf A q)) w = ((Rigid.DxN A.B w).submatrix Subtype.val Subtype.val).map (Nat.cast : ℕ → ℝ) := by
  rw [Rigid.Dx_eq_map]
  have h := DC_eq_submatrix A q w
  unfold DC at h
  rw [h]

/-- `g_C` (the diagonal definition `Rigid.gDiag` of Appendix D). -/
noncomputable abbrev gComp (C : Finset Q) : ℝ := Rigid.gDiag (compMat A C)

/-! ## §4 Types of components -/

/-- `A_C := D^C_0 + D^C_1`. -/
def AC (C : Finset Q) : Matrix C C ℕ := compMat A C 0 + compMat A C 1

/-- `L*_C := {w : D^C_w ≠ 0}`. -/
def LStar (C : Finset Q) : Set (List (Fin 2)) := {w | DC A C w ≠ 0}

/-- Survivable: `L*_C` contains all words. -/
def Survivable (C : Finset Q) : Prop := ∀ w, DC A C w ≠ 0

/-- A word that kills: `D^C_z = 0`. -/
def Kills (C : Finset Q) (z : List (Fin 2)) : Prop := DC A C z = 0

/-- 0/1: all entries of `D^C_w` are 0 or 1. -/
def ZeroOne (C : Finset Q) : Prop := ∀ w x y, DC A C w x y ≤ 1

open Classical in
/-- Bounded complexity: the number of words of length `r` in `L*_C` is bounded independently of `r`. -/
def BoundedCx (C : Finset Q) : Prop :=
  ∃ M : ℕ, ∀ r : ℕ, ((Finset.univ : Finset (Fin r → Fin 2)).filter (fun x => DC A C (List.ofFn x) ≠ 0)).card ≤ M

theorem not_survivable_iff (C : Finset Q) : ¬ Survivable A C ↔ ∃ z, Kills A C z := by
  simp [Survivable, Kills]

end Paths

section Rho

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The sum of the entries of a matrix. -/
def esum (X : Matrix K K ℕ) : ℕ := ∑ i, ∑ j, X i j

/-- A paraphrase of `ρ(X) < c`: for some `L ≥ 1` the sum of the entries of `X^L` is less than `c^L` (the sum of the entries is a submultiplicative norm, so
by Gelfand's formula this is equivalent to `ρ(X) < c`; the equivalence with the spectral radius is not proved). -/
def RhoLt (X : Matrix K K ℕ) (c : ℕ) : Prop := ∃ L, 1 ≤ L ∧ esum (X ^ L) < c ^ L

/-- Exponential decay of the sum of the entries of `X^L` compared with `2^L`. -/
def Decay2 (X : Matrix K K ℕ) : Prop :=
  ∃ θ c : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ L, (esum (X ^ L) : ℝ) ≤ c * (2 * θ) ^ L

theorem esum_mul_le (X Y : Matrix K K ℕ) : esum (X * Y) ≤ esum X * esum Y := by
  unfold esum
  simp only [Matrix.mul_apply]
  calc ∑ i, ∑ j, ∑ k, X i k * Y k j = ∑ i, ∑ k, X i k * ∑ j, Y k j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, ∑ k, X i k * ∑ k', ∑ j, Y k' j := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ ?_
        exact Finset.single_le_sum (f := fun k' => ∑ j, Y k' j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ = (∑ i, ∑ k, X i k) * ∑ k', ∑ j, Y k' j := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm

theorem esum_pow_mul_le (X : Matrix K K ℕ) (L₀ q r : ℕ) : esum (X ^ (q * L₀ + r)) ≤ esum (X ^ L₀) ^ q * esum (X ^ r) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * L₀ + r = L₀ + (q * L₀ + r) by ring, pow_add]
    calc esum (X ^ L₀ * X ^ (q * L₀ + r)) ≤ esum (X ^ L₀) * esum (X ^ (q * L₀ + r)) := esum_mul_le _ _
      _ ≤ esum (X ^ L₀) * (esum (X ^ L₀) ^ q * esum (X ^ r)) := Nat.mul_le_mul_left _ ih
      _ = esum (X ^ L₀) ^ (q + 1) * esum (X ^ r) := by ring

/-- Exponential decay from the paraphrase of `ρ < 2`. -/
theorem decay2_of_rhoLt {X : Matrix K K ℕ} (h : RhoLt X 2) : Decay2 X := by
  obtain ⟨L₀, hL₀, hlt⟩ := h
  set s := esum (X ^ L₀)
  -- `θ₀ := s / 2^{L₀} < 1`; by Bernoulli, `θ^{L₀} ≥ θ₀` for some `θ ∈ [1/2, 1)`
  have h2pos : (0 : ℝ) < 2 ^ L₀ := by positivity
  set θ₀ : ℝ := s / 2 ^ L₀
  have hθ₀ : θ₀ < 1 := by
    rw [div_lt_one h2pos]; exact_mod_cast hlt
  set t : ℝ := (1 - θ₀) / L₀
  have hL₀r : (1 : ℝ) ≤ L₀ := by exact_mod_cast hL₀
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hθ₀0 : 0 ≤ θ₀ := div_nonneg hs0 h2pos.le
  have ht1 : t ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  set θ : ℝ := max (1 / 2) (1 - t)
  have hθ1 : θ < 1 := max_lt (by norm_num) (by linarith)
  have hθh : 1 / 2 ≤ θ := le_max_left _ _
  have hθpow : θ₀ ≤ θ ^ L₀ := by
    have hb := one_add_mul_le_pow (a := -t) (by linarith) L₀
    have : 1 + (L₀ : ℝ) * -t = θ₀ := by
      simp only [t]; field_simp; ring
    calc θ₀ = 1 + (L₀ : ℝ) * -t := this.symm
      _ ≤ (1 + -t) ^ L₀ := hb
      _ ≤ θ ^ L₀ := pow_le_pow_left₀ (by linarith) (by simp only [θ]; exact le_max_of_le_right (by linarith)) _
  -- `W := max_{r < L₀} esum (X^r)`
  set W : ℕ := (Finset.range L₀).sup (fun r => esum (X ^ r))
  refine ⟨θ, W, by linarith, hθ1, fun L => ?_⟩
  have h2θ : 1 ≤ 2 * θ := by linarith
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < L₀ ∧ L = q * L₀ + r :=
    ⟨L / L₀, L % L₀, Nat.mod_lt _ (by omega), (Nat.div_add_mod' L L₀).symm⟩
  have hW : esum (X ^ r) ≤ W := Finset.le_sup (f := fun r => esum (X ^ r)) (Finset.mem_range.2 hr)
  have hsq : (s : ℝ) ^ q ≤ (2 * θ) ^ (q * L₀) := by
    rw [pow_mul', mul_pow]
    refine pow_le_pow_left₀ hs0 ?_ q
    have : (s : ℝ) = 2 ^ L₀ * θ₀ := by simp only [θ₀]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hθpow (by positivity)
  calc (esum (X ^ (q * L₀ + r)) : ℝ) ≤ (s : ℝ) ^ q * W := by
        have := esum_pow_mul_le X L₀ q r
        have h' : esum (X ^ L₀) ^ q * esum (X ^ r) ≤ s ^ q * W := Nat.mul_le_mul_left _ hW
        exact_mod_cast this.trans h'
    _ ≤ (2 * θ) ^ (q * L₀) * W := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg _)
    _ ≤ (2 * θ) ^ (q * L₀) * (2 * θ) ^ r * W := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ h2θ)
    _ = W * (2 * θ) ^ (q * L₀ + r) := by rw [pow_add]; ring

/-- The paraphrase of `ρ < 2` from exponential decay. -/
theorem rhoLt_of_decay2 {X : Matrix K K ℕ} (h : Decay2 X) : RhoLt X 2 := by
  obtain ⟨θ, c, hθ0, hθ1, hb⟩ := h
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := 1 / (|c| + 1)) (by positivity) hθ1
  refine ⟨n + 1, by omega, ?_⟩
  have h1 := hb (n + 1)
  have hθn : θ ^ (n + 1) ≤ θ ^ n := pow_le_pow_of_le_one hθ0 hθ1.le (by omega)
  have hc : c * θ ^ (n + 1) < 1 := by
    calc c * θ ^ (n + 1) ≤ |c| * θ ^ (n + 1) := mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * θ ^ n := mul_le_mul_of_nonneg_left hθn (abs_nonneg c)
      _ ≤ |c| * (1 / (|c| + 1)) := mul_le_mul_of_nonneg_left hn.le (abs_nonneg c)
      _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
  have : (esum (X ^ (n + 1)) : ℝ) < 2 ^ (n + 1) := by
    calc (esum (X ^ (n + 1)) : ℝ) ≤ c * (2 * θ) ^ (n + 1) := h1
      _ = (c * θ ^ (n + 1)) * 2 ^ (n + 1) := by ring
      _ < 1 * 2 ^ (n + 1) := mul_lt_mul_of_pos_right hc (by positivity)
      _ = 2 ^ (n + 1) := one_mul _
  exact_mod_cast this

theorem decay2_iff_rhoLt (X : Matrix K K ℕ) : Decay2 X ↔ RhoLt X 2 := ⟨rhoLt_of_decay2, decay2_of_rhoLt⟩

/-- If all column sums are at least `c`, multiplying from the left multiplies the sum of the entries by at least `c`. -/
theorem esum_mul_ge_of_colSum {X Y : Matrix K K ℕ} {c : ℕ} (h : ∀ k, c ≤ ∑ i, X i k) :
    c * esum Y ≤ esum (X * Y) := by
  have e : esum (X * Y) = ∑ k, (∑ i, X i k) * ∑ j, Y k j := by
    simp only [esum, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    calc ∑ i, ∑ j, ∑ k, X i k * Y k j = ∑ i, ∑ k, ∑ j, X i k * Y k j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, X i k * Y k j := Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, X i k * Y k j := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [e, esum, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => Nat.mul_le_mul_right _ (h k)

/-- A matrix whose column sums are all at least `c` does not satisfy `ρ < c` (for a non-empty index type). -/
theorem not_rhoLt_of_colSum [Nonempty K] {X : Matrix K K ℕ} {c : ℕ} (h : ∀ k, c ≤ ∑ i, X i k) :
    ¬ RhoLt X c := by
  rintro ⟨L, _, hL⟩
  have key : ∀ L, c ^ L * esum (1 : Matrix K K ℕ) ≤ esum (X ^ L) := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [pow_succ', pow_succ', mul_assoc]
      exact (Nat.mul_le_mul_left _ ih).trans (esum_mul_ge_of_colSum h)
  have h1 : 1 ≤ esum (1 : Matrix K K ℕ) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty K)
    unfold esum
    calc 1 = (1 : Matrix K K ℕ) x x := by simp
      _ ≤ ∑ j, (1 : Matrix K K ℕ) x j :=
          Finset.single_le_sum (f := fun j => (1 : Matrix K K ℕ) x j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
      _ ≤ ∑ i, ∑ j, (1 : Matrix K K ℕ) i j :=
          Finset.single_le_sum (f := fun i => ∑ j, (1 : Matrix K K ℕ) i j)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  have := key L
  have : c ^ L ≤ esum (X ^ L) := le_trans (by nlinarith) this
  omega

end Rho

section Types

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- Type (Z): survivable, and all `D^C_w` are 0/1 (a component in `Q_{\mathrm s}`). -/
def TypeZ (C : Finset Q) : Prop := Survivable A C ∧ ZeroOne A C
/-- Type (P): survivable and not 0/1 (positive rate). -/
def TypeP (C : Finset Q) : Prop := Survivable A C ∧ ¬ ZeroOne A C
/-- Type (L): not survivable and `ρ(A_C) < 2`. -/
def TypeL (C : Finset Q) : Prop := ¬ Survivable A C ∧ RhoLt (AC A C) 2
/-- Type (Hb): not survivable, `ρ(A_C) ≥ 2`, bounded complexity. -/
def TypeHb (C : Finset Q) : Prop := ¬ Survivable A C ∧ ¬ RhoLt (AC A C) 2 ∧ BoundedCx A C
/-- Type (Hu): not survivable, `ρ(A_C) ≥ 2`, unbounded complexity. -/
def TypeHu (C : Finset Q) : Prop := ¬ Survivable A C ∧ ¬ RhoLt (AC A C) 2 ∧ ¬ BoundedCx A C

/-- Every component has one of the five types. -/
theorem type_cases (C : Finset Q) : TypeZ A C ∨ TypeP A C ∨ TypeL A C ∨ TypeHb A C ∨ TypeHu A C := by
  unfold TypeZ TypeP TypeL TypeHb TypeHu
  by_cases h1 : Survivable A C <;> by_cases h2 : ZeroOne A C <;> by_cases h3 : RhoLt (AC A C) 2 <;>
    by_cases h4 : BoundedCx A C <;> simp [h1, h2, h3, h4]

end Types

end Collatz.Arctic.NatQ5
