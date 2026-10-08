/-
# Lemma D.4: idempotents of minimal rank and the finite group `H_P`

The parts of Lemma D.4 that Proposition D.5 and Section 11 use,
in Lean.

* **§1 The abstract form**: for a compact set `S` of non-negative matrices closed under multiplication and an idempotent `P` of minimal rank in `S`,
  `H_P := {P Y P : Y ∈ S}` is a group with identity `P` (`HP_right_inv`, `HP_left_inv`), and it is **finite** (`HP_finite`).
  For finiteness, the coordinates `coord` with respect to a pivot basis of `P` (`RigidCone.lean`) map `H_P` to a bounded group of non-negative
  `r_0 × r_0` matrices, and **the zero pattern** `pat` (the positions of the non-zero entries) is shown to be injective on `H_P` (the quotient of two elements with the same pattern is diagonal,
  and by boundedness it is the identity; `HP_pat_inj`). The later arguments use only finiteness. The monomial action and the bound `≤ r_0!` on the order are in `RigidOrder.lean`.
  Moreover there is `h ≥ 1` with `A^h = P` for all elements (`HP_pow_eq`), and distinct elements are uniformly apart (`HP_discrete`).
* **§2 `S̄ := closure {E_x}`**: compact, closed under multiplication, non-negative, with bounded entries, and `‖Y‖ ≥ c > 0` (the closure of `uniform_lower`).
* **The Lean form of the existence of the idempotent** (`exists_minRank_idem`): `S̄` contains a non-negative idempotent `P ≠ 0` of minimal rank (**the
  Ellis–Numakura lemma** of Mathlib, `exists_idempotent_in_compact_subsemigroup`, applied to `Y₀ S̄`), and there is `a` with `P_{aa} > 0`.
  An earlier argument constructed `E_χ = P + R` (`PR = RP = 0`, `ρ(R) < 1`) by the continuity of eigenvalues; here this is **not constructed**:
  since `P ∈ S̄`, for every `ε > 0` there is a word `χ` with `‖E_χ - P‖ < ε` (`exists_word_near`). As `H_P` is finite and discrete,
  this suffices for the exact product over the separating word in Proposition D.5 (`RigidSep.lean`).
-/
import CollatzProof.Arctic.Nat.RigidLower
import CollatzProof.Arctic.Nat.RigidCone

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix Filter Topology Set

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] [DecidableEq K]

/-! ## §0 A small lemma on matrices -/

theorem matrix_eq_of_mulVec {A C : Matrix K K ℝ} (h : ∀ v, A *ᵥ v = C *ᵥ v) : A = C := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem range_le_of_eq_mul {P Q X : Matrix K K ℝ} (h : Q = P * X) :
    LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin := by
  rintro _ ⟨v, rfl⟩
  exact ⟨X *ᵥ v, by simp [Matrix.mulVec_mulVec, h]⟩

theorem idem_pow {P : Matrix K K ℝ} (hPP : P * P = P) (q : ℕ) (hq : 1 ≤ q) : P ^ q = P := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ q _ ih => rw [pow_succ, ih, hPP]

/-! ## §1 The abstract form: idempotents of minimal rank and `H_P` -/

/-- `H_P := {P Y P : Y ∈ S}`. -/
def HP (P : Matrix K K ℝ) (S : Set (Matrix K K ℝ)) : Set (Matrix K K ℝ) := (fun Y => P * Y * P) '' S

section Abstract

variable {S : Set (Matrix K K ℝ)} {P : Matrix K K ℝ}
  (hSc : IsCompact S) (hSm : ∀ Y ∈ S, ∀ Z ∈ S, Y * Z ∈ S) (hS0 : ∀ Y ∈ S, ∀ i j, 0 ≤ Y i j)
  (hPS : P ∈ S) (hPP : P * P = P) (hPmin : ∀ Y ∈ S, P.rank ≤ Y.rank)

include hSm hPS in
theorem HP_subset : HP P S ⊆ S := by
  rintro _ ⟨Y, hY, rfl⟩
  exact hSm _ (hSm _ hPS _ hY) _ hPS

include hPP in
theorem HP_left_P {A : Matrix K K ℝ} (hA : A ∈ HP P S) : P * A = A := by
  obtain ⟨Y, -, rfl⟩ := hA
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]

include hPP in
theorem HP_right_P {A : Matrix K K ℝ} (hA : A ∈ HP P S) : A * P = A := by
  obtain ⟨Y, -, rfl⟩ := hA
  rw [Matrix.mul_assoc, hPP]

include hPS hPP in
theorem P_mem_HP : P ∈ HP P S := ⟨P, hPS, by show P * P * P = P; rw [hPP, hPP]⟩

include hSm hPS hPP in
theorem HP_mul_mem {A C : Matrix K K ℝ} (hA : A ∈ HP P S) (hC : C ∈ HP P S) : A * C ∈ HP P S := by
  obtain ⟨Y, hY, rfl⟩ := hA
  obtain ⟨Z, hZ, rfl⟩ := hC
  refine ⟨Y * P * Z, hSm _ (hSm _ hY _ hPS) _ hZ, ?_⟩
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P P (Z * P), hPP]

include hSc in
theorem HP_isCompact : IsCompact (HP P S) :=
  hSc.image ((continuous_const.mul continuous_id).mul continuous_const)

include hSm hPS hPP hPmin in
/-- The only idempotent of `H_P` is `P` (minimality of the rank). -/
theorem HP_idem_eq {Q : Matrix K K ℝ} (hQ : Q ∈ HP P S) (hQQ : Q * Q = Q) : Q = P := by
  have hQS : Q ∈ S := HP_subset hSm hPS hQ
  have h1 : P * Q = Q := HP_left_P hPP hQ
  have h2 : Q * P = Q := HP_right_P hPP hQ
  have hle : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin := range_le_of_eq_mul h1.symm
  have heq : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hle (hPmin Q hQS)
  refine matrix_eq_of_mulVec fun v => ?_
  have hPv : P *ᵥ v ∈ LinearMap.range Q.mulVecLin := heq ▸ ⟨v, rfl⟩
  obtain ⟨u, hu⟩ := hPv
  rw [Matrix.mulVecLin_apply] at hu
  calc Q *ᵥ v = (Q * P) *ᵥ v := by rw [h2]
    _ = Q *ᵥ (P *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = Q *ᵥ (Q *ᵥ u) := by rw [hu]
    _ = Q *ᵥ u := by rw [Matrix.mulVec_mulVec, hQQ]
    _ = P *ᵥ v := hu

include hSc hSm hPS hPP hPmin in
/-- Every element of `H_P` has a right inverse (Ellis–Numakura applied to `A H_P`). -/
theorem HP_right_inv {A : Matrix K K ℝ} (hA : A ∈ HP P S) : ∃ A' ∈ HP P S, A * A' = P := by
  set T := (fun Z => A * Z) '' HP P S with hT
  have hTne : T.Nonempty := ⟨A * P, P, P_mem_HP hPS hPP, rfl⟩
  have hTc : IsCompact T := (HP_isCompact hSc).image (continuous_const.mul continuous_id)
  have hTm : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ T := by
    rintro _ ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩
    refine ⟨Z * A * Z', HP_mul_mem hSm hPS hPP (HP_mul_mem hSm hPS hPP hZ hA) hZ', ?_⟩
    simp only [Matrix.mul_assoc]
  obtain ⟨Q, ⟨Z, hZ, rfl⟩, hQQ⟩ :=
    exists_idempotent_in_compact_subsemigroup (fun r => continuous_id.mul continuous_const) T hTne hTc hTm
  exact ⟨Z, hZ, HP_idem_eq hSm hPS hPP hPmin (HP_mul_mem hSm hPS hPP hA hZ) hQQ⟩

include hSc hSm hPS hPP hPmin in
/-- A right inverse is also a left inverse (`H_P` is a group). -/
theorem HP_left_inv {A A' : Matrix K K ℝ} (hA : A ∈ HP P S) (hA' : A' ∈ HP P S) (h : A * A' = P) :
    A' * A = P := by
  obtain ⟨A'', hA'', h'⟩ := HP_right_inv hSc hSm hPS hPP hPmin hA'
  have : A'' = A := by
    calc A'' = P * A'' := (HP_left_P hPP hA'').symm
      _ = A * A' * A'' := by rw [h]
      _ = A * (A' * A'') := Matrix.mul_assoc _ _ _
      _ = A * P := by rw [h']
      _ = A := HP_right_P hPP hA
  rw [← this, h']

include hSc hSm hPS hPP hPmin in
theorem HP_inv {A : Matrix K K ℝ} (hA : A ∈ HP P S) : ∃ A' ∈ HP P S, A * A' = P ∧ A' * A = P := by
  obtain ⟨A', hA', h⟩ := HP_right_inv hSc hSm hPS hPP hPmin hA
  exact ⟨A', hA', h, HP_left_inv hSc hSm hPS hPP hPmin hA hA' h⟩

/-! ### Pivot coordinates -/

section Coord

variable (B : PivotBasis P)

/-- The pivot coordinates of `A`: `(coord A)_{ji} := (A f_i)(k_j)`. -/
def coord (A : Matrix K K ℝ) : Matrix (Fin B.r) (Fin B.r) ℝ := Matrix.of fun j i => (A *ᵥ B.f i) (B.k j)

theorem coord_apply (A : Matrix K K ℝ) (j i : Fin B.r) : coord B A j i = (A *ᵥ B.f i) (B.k j) := rfl

theorem coord_spec {A : Matrix K K ℝ} (hPA : P * A = A) (i : Fin B.r) :
    A *ᵥ B.f i = ∑ j, coord B A j i • B.f j :=
  B.expand _ (by rw [Matrix.mulVec_mulVec, hPA])

theorem coord_mul {A A' : Matrix K K ℝ} (hPA : P * A = A) (hPA' : P * A' = A') :
    coord B (A * A') = coord B A * coord B A' := by
  ext j i
  rw [coord_apply, ← Matrix.mulVec_mulVec, coord_spec B hPA' i, Matrix.mulVec_sum, Matrix.mul_apply]
  simp_rw [Matrix.mulVec_smul, coord_spec B hPA]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, B.eval_sum, mul_comm]

theorem coord_P : coord B P = 1 := by
  ext j i
  rw [coord_apply, (B.inCone i).2, B.delta, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

include hPP in
theorem coord_inj {A A' : Matrix K K ℝ} (hAP : A * P = A) (hA'P : A' * P = A')
    (hPA : P * A = A) (hPA' : P * A' = A') (h : coord B A = coord B A') : A = A' := by
  refine matrix_eq_of_mulVec fun z => ?_
  have hfix : P *ᵥ (P *ᵥ z) = P *ᵥ z := by rw [Matrix.mulVec_mulVec, hPP]
  have e : ∀ X : Matrix K K ℝ, X * P = X → P * X = X →
      X *ᵥ z = ∑ i, (P *ᵥ z) (B.k i) • ∑ j, coord B X j i • B.f j := by
    intro X hXP hPX
    calc X *ᵥ z = X *ᵥ (P *ᵥ z) := by rw [Matrix.mulVec_mulVec, hXP]
      _ = X *ᵥ ∑ i, (P *ᵥ z) (B.k i) • B.f i := by rw [← B.expand _ hfix]
      _ = _ := by
          rw [Matrix.mulVec_sum]
          simp_rw [Matrix.mulVec_smul, coord_spec B hPX]
  rw [e A hAP hPA, e A' hA'P hPA', h]

theorem coord_nonneg {A : Matrix K K ℝ} (hA : ∀ i j, 0 ≤ A i j) (j i : Fin B.r) : 0 ≤ coord B A j i := by
  rw [coord_apply, mulVec_apply']
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hA _ _) ((B.inCone i).1 l)

theorem coord_le {A : Matrix K K ℝ} (hA : ∀ i j, 0 ≤ A i j) (j i : Fin B.r) :
    coord B A j i ≤ nrm A * ∑ i', ∑ l, B.f i' l := by
  have hF : ∀ l, B.f i l ≤ ∑ i', ∑ l', B.f i' l' := by
    intro l
    calc B.f i l ≤ ∑ l', B.f i l' :=
          Finset.single_le_sum (f := fun l' => B.f i l') (fun l' _ => (B.inCone i).1 l') (Finset.mem_univ l)
      _ ≤ ∑ i', ∑ l', B.f i' l' :=
          Finset.single_le_sum (f := fun i' => ∑ l', B.f i' l')
            (fun i' _ => Finset.sum_nonneg fun l' _ => (B.inCone i').1 l') (Finset.mem_univ i)
  have hF0 : 0 ≤ ∑ i', ∑ l, B.f i' l :=
    Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun l _ => (B.inCone i').1 l
  rw [coord_apply, mulVec_apply']
  calc ∑ l, A (B.k j) l * B.f i l ≤ ∑ l, A (B.k j) l * ∑ i', ∑ l', B.f i' l' :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hF l) (hA _ _)
    _ = (∑ l, A (B.k j) l) * ∑ i', ∑ l', B.f i' l' := by rw [Finset.sum_mul]
    _ ≤ nrm A * ∑ i', ∑ l', B.f i' l' := by
        refine mul_le_mul_of_nonneg_right ?_ hF0
        rw [nrm_of_nonneg hA]
        exact Finset.single_le_sum (f := fun i' => ∑ l, A i' l)
          (fun i' _ => Finset.sum_nonneg fun l _ => hA _ _) (Finset.mem_univ _)

end Coord

include hSc hSm hS0 hPS hPP hPmin in
/-- **Injectivity of the pattern**: two elements of `H_P` whose pivot coordinates have the same non-zero positions are equal. -/
theorem HP_pat_inj (B : PivotBasis P) {A C : Matrix K K ℝ} (hA : A ∈ HP P S) (hC : C ∈ HP P S)
    (hpat : ∀ j i, coord B A j i ≠ 0 → coord B C j i ≠ 0)
    (hpat' : ∀ j i, coord B C j i ≠ 0 → coord B A j i ≠ 0) : A = C := by
  classical
  -- Boundedness of `H_P`
  obtain ⟨M, hM⟩ := (HP_isCompact hSc (P := P)).bddAbove_image continuous_nrm.continuousOn
  set F := ∑ i', ∑ l, B.f i' l
  have hbd : ∀ A ∈ HP P S, ∀ j i, coord B A j i ≤ M * F := by
    intro A hA j i
    have hF0 : 0 ≤ F := Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun l _ => (B.inCone i').1 l
    exact (coord_le B (hS0 A (HP_subset hSm hPS hA)) j i).trans
      (mul_le_mul_of_nonneg_right (hM ⟨A, hA, rfl⟩) hF0)
  have hnn : ∀ A ∈ HP P S, ∀ j i, 0 ≤ coord B A j i :=
    fun A hA j i => coord_nonneg B (hS0 A (HP_subset hSm hPS hA)) j i
  -- Powers
  have hpowmem : ∀ X ∈ HP P S, ∀ n : ℕ, X ^ (n + 1) ∈ HP P S := by
    intro X hX n
    induction n with
    | zero => simpa using hX
    | succ n ih => rw [pow_succ]; exact HP_mul_mem hSm hPS hPP ih hX
  have hpowcoord : ∀ X ∈ HP P S, ∀ n : ℕ, coord B (X ^ (n + 1)) = coord B X ^ (n + 1) := by
    intro X hX n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, coord_mul B (HP_left_P hPP (hpowmem X hX n)) (HP_left_P hPP hX), ih, ← pow_succ]
  -- A diagonal element with bounded powers has diagonal entries at most 1
  have hdiag_le : ∀ X ∈ HP P S, (∀ j l, j ≠ l → coord B X j l = 0) → ∀ j, coord B X j j ≤ 1 := by
    intro X hX hoff j
    have hd : coord B X = Matrix.diagonal fun j => coord B X j j := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · rw [Matrix.diagonal_apply_ne _ hab, hoff a b hab]
    by_contra hc
    push Not at hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M * F) hc
    have h1 := hbd _ (hpowmem X hX n) j j
    rw [hpowcoord X hX n, hd, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Pi.pow_apply] at h1
    have h2 : coord B X j j ^ n ≤ coord B X j j ^ (n + 1) :=
      pow_le_pow_right₀ hc.le (Nat.le_succ n)
    linarith
  -- For `A`, `C` whose patterns are contained in each other and the inverse `C'` of `C`, `A C'` is diagonal
  have hoffdiag : ∀ A ∈ HP P S, ∀ C ∈ HP P S, (∀ j i, coord B A j i ≠ 0 → coord B C j i ≠ 0) →
      ∀ C' ∈ HP P S, C * C' = P → ∀ j l, j ≠ l → coord B (A * C') j l = 0 := by
    intro A hA C hC hpat C' hC' hCC' j l hjl
    have h1 : (coord B C * coord B C') j l = 0 := by
      rw [← coord_mul B (HP_left_P hPP hC) (HP_left_P hPP hC'), hCC', coord_P, Matrix.one_apply_ne hjl]
    rw [Matrix.mul_apply] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hnn C hC j i) (hnn C' hC' i l)).mp h1
    rw [coord_mul B (HP_left_P hPP hA) (HP_left_P hPP hC'), Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hAji : coord B A j i = 0
    · rw [hAji, zero_mul]
    · have hCji : coord B C j i ≠ 0 := hpat j i hAji
      have := h2 i (Finset.mem_univ i)
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hCji
      · rw [h, mul_zero]
  obtain ⟨A', hA', hAA', hA'A⟩ := HP_inv hSc hSm hPS hPP hPmin hA
  obtain ⟨C', hC', hCC', hC'C⟩ := HP_inv hSc hSm hPS hPP hPmin hC
  set X := A * C'
  set Y := C * A'
  have hX : X ∈ HP P S := HP_mul_mem hSm hPS hPP hA hC'
  have hY : Y ∈ HP P S := HP_mul_mem hSm hPS hPP hC hA'
  have hXoff := hoffdiag A hA C hC hpat C' hC' hCC'
  have hYoff := hoffdiag C hC A hA hpat' A' hA' hAA'
  have hXY : X * Y = P := by
    calc X * Y = A * (C' * C) * A' := by simp only [X, Y, Matrix.mul_assoc]
      _ = A * A' := by rw [hC'C, HP_right_P hPP hA]
      _ = P := hAA'
  have hprod : ∀ j, coord B X j j * coord B Y j j = 1 := by
    intro j
    have h1 : (coord B X * coord B Y) j j = 1 := by
      rw [← coord_mul B (HP_left_P hPP hX) (HP_left_P hPP hY), hXY, coord_P, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single j] at h1
    · exact h1
    · intro i _ hij; rw [hXoff j i (Ne.symm hij), zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hX1 : coord B X = 1 := by
    ext j l
    by_cases hjl : j = l
    · subst hjl
      rw [Matrix.one_apply_eq]
      have a1 := hdiag_le X hX hXoff j
      have a2 := hdiag_le Y hY hYoff j
      have a3 := hprod j
      have a4 := hnn X hX j j
      have a5 := hnn Y hY j j
      nlinarith
    · rw [Matrix.one_apply_ne hjl, hXoff j l hjl]
  have hXP : X = P :=
    coord_inj hPP B (HP_right_P hPP hX) hPP (HP_left_P hPP hX) hPP (by rw [hX1, coord_P])
  calc A = A * P := (HP_right_P hPP hA).symm
    _ = A * (C' * C) := by rw [hC'C]
    _ = X * C := by simp only [X, Matrix.mul_assoc]
    _ = P * C := by rw [hXP]
    _ = C := HP_left_P hPP hC

include hSc hSm hS0 hPS hPP hPmin in
/-- **`H_P` is finite**: the zero pattern of the coordinates is injective on `H_P`. -/
theorem HP_finite : (HP P S).Finite := by
  classical
  obtain ⟨B⟩ := nonempty_pivotBasis (hS0 P hPS) hPP
  let pat : Matrix K K ℝ → Finset (Fin B.r × Fin B.r) :=
    fun A => Finset.univ.filter fun p => coord B A p.1 p.2 ≠ 0
  refine Set.Finite.of_injOn (f := pat) (t := Set.univ) (Set.mapsTo_univ _ _) ?_ Set.finite_univ
  intro A hA C hC hpat
  have e : ∀ j i, coord B A j i ≠ 0 ↔ coord B C j i ≠ 0 := fun j i => by
    have := congrArg (fun s => (j, i) ∈ s) hpat
    simpa [pat] using this
  exact HP_pat_inj hSc hSm hS0 hPS hPP hPmin B hA hC (fun j i => (e j i).mp) (fun j i => (e j i).mpr)

include hSc hSm hS0 hPS hPP hPmin in
/-- There is `h ≥ 1` with **`A^h = P` for all elements**. -/
theorem HP_pow_eq : ∃ h : ℕ, 1 ≤ h ∧ ∀ A ∈ HP P S, A ^ h = P := by
  classical
  have hfin := HP_finite hSc hSm hS0 hPS hPP hPmin
  have hpowmem : ∀ X ∈ HP P S, ∀ n : ℕ, X ^ (n + 1) ∈ HP P S := by
    intro X hX n
    induction n with
    | zero => simpa using hX
    | succ n ih => rw [pow_succ]; exact HP_mul_mem hSm hPS hPP ih hX
  -- The order of each element
  have hord : ∀ A ∈ HP P S, ∃ d : ℕ, 1 ≤ d ∧ A ^ d = P := by
    intro A hA
    have : Finite (HP P S) := hfin.to_subtype
    obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨A ^ (n + 1), hpowmem A hA n⟩ : HP P S))
    have heq' : A ^ (i + 1) = A ^ (j + 1) := congrArg Subtype.val heq
    -- Arrange `i < j`
    have key : ∀ a b : ℕ, a < b → A ^ (a + 1) = A ^ (b + 1) → ∃ d : ℕ, 1 ≤ d ∧ A ^ d = P := by
      intro a b hab he
      obtain ⟨Bl, hBl, -, hBlA⟩ := HP_inv hSc hSm hPS hPP hPmin (hpowmem A hA a)
      refine ⟨b - a, by omega, ?_⟩
      have hd : A ^ (b - a) ∈ HP P S := by
        have := hpowmem A hA (b - a - 1)
        rwa [show b - a - 1 + 1 = b - a by omega] at this
      calc A ^ (b - a) = P * A ^ (b - a) := (HP_left_P hPP hd).symm
        _ = Bl * A ^ (a + 1) * A ^ (b - a) := by rw [hBlA]
        _ = Bl * A ^ (b + 1) := by rw [Matrix.mul_assoc, ← pow_add, show a + 1 + (b - a) = b + 1 by omega]
        _ = Bl * A ^ (a + 1) := by rw [he]
        _ = P := hBlA
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h heq'
    · exact key j i h heq'.symm
  choose! d hd1 hdP using hord
  set Fs := hfin.toFinset
  refine ⟨∏ A ∈ Fs, d A, ?_, fun A hA => ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun A hA =>
      (Nat.one_le_iff_ne_zero.mp (hd1 A (hfin.mem_toFinset.mp hA))))
  · have hAF : A ∈ Fs := hfin.mem_toFinset.mpr hA
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem d hAF
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exfalso
        have : ∏ A ∈ Fs, d A = 0 := by rw [hq, h0, mul_zero]
        exact (Finset.prod_ne_zero_iff.mpr fun A' hA' =>
          Nat.one_le_iff_ne_zero.mp (hd1 A' (hfin.mem_toFinset.mp hA'))) this
      · exact h0
    rw [hq, pow_mul, hdP A hA, idem_pow hPP q hq1]

include hSc hSm hS0 hPS hPP hPmin in
/-- **Discreteness**: distinct elements of `H_P` are uniformly apart. -/
theorem HP_discrete : ∃ dH : ℝ, 0 < dH ∧ ∀ A ∈ HP P S, ∀ C ∈ HP P S, nrm (A - C) < dH → A = C := by
  classical
  have hfin := HP_finite hSc hSm hS0 hPS hPP hPmin
  set E : Set ℝ := (fun p : Matrix K K ℝ × Matrix K K ℝ => nrm (p.1 - p.2)) ''
    ((HP P S ×ˢ HP P S) ∩ {p | p.1 ≠ p.2})
  have hE : E.Finite := ((hfin.prod hfin).subset inter_subset_left).image _
  rcases E.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun A hA C hC _ => ?_⟩
    by_contra hAC
    have : nrm (A - C) ∈ E := ⟨(A, C), ⟨⟨hA, hC⟩, hAC⟩, rfl⟩
    rw [he] at this; exact this
  · obtain ⟨e0, he0, hmin⟩ := Set.exists_min_image E id hE hne
    obtain ⟨⟨A0, C0⟩, ⟨-, hne0⟩, rfl⟩ := he0
    refine ⟨nrm (A0 - C0), nrm_pos_of_ne hne0, fun A hA C hC hlt => ?_⟩
    by_contra hAC
    have := hmin (nrm (A - C)) ⟨(A, C), ⟨⟨hA, hC⟩, hAC⟩, rfl⟩
    simp only [id] at this
    linarith

end Abstract

/-! ## §2 `S̄ := closure {E_x}` -/

/-- The closure `S̄` of `{E_x : x a word}`. -/
def Sbar (D : Fin 2 → Matrix K K ℕ) (g : ℝ) : Set (Matrix K K ℝ) := closure (range (Ex D g))

section Sbar

variable {D : Fin 2 → Matrix K K ℕ} {g : ℝ}

theorem Ex_mem_Sbar (x : List (Fin 2)) : Ex D g x ∈ Sbar D g := subset_closure ⟨x, rfl⟩

theorem one_mem_Sbar : (1 : Matrix K K ℝ) ∈ Sbar D g := by
  simpa using Ex_mem_Sbar (D := D) (g := g) []

theorem Sbar_mul_mem {Y Z : Matrix K K ℝ} (hY : Y ∈ Sbar D g) (hZ : Z ∈ Sbar D g) :
    Y * Z ∈ Sbar D g := by
  refine map_mem_closure₂ (f := fun A B : Matrix K K ℝ => A * B) continuous_mul hY hZ ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact ⟨x ++ y, Ex_append D g x y⟩

theorem isClosed_entry_le (B : ℝ) : IsClosed {Y : Matrix K K ℝ | ∀ i j, Y i j ≤ B} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le ((continuous_apply j).comp (continuous_apply i)) continuous_const

theorem isClosed_entry_ge (B : ℝ) : IsClosed {Y : Matrix K K ℝ | ∀ i j, B ≤ Y i j} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))

theorem Sbar_nonneg (hg : 0 ≤ g) : ∀ Y ∈ Sbar D g, ∀ i j, 0 ≤ Y i j := by
  intro Y hY
  refine closure_minimal ?_ (isClosed_entry_ge 0) hY
  rintro _ ⟨x, rfl⟩
  exact Ex_nonneg D hg x

theorem Sbar_entry_le {B : ℝ} (hB : ∀ x i j, Ex D g x i j ≤ B) : ∀ Y ∈ Sbar D g, ∀ i j, Y i j ≤ B := by
  intro Y hY
  refine closure_minimal ?_ (isClosed_entry_le B) hY
  rintro _ ⟨x, rfl⟩
  exact hB x

theorem Sbar_nrm_ge {c : ℝ} (hc : ∀ x, c ≤ nrm (Ex D g x)) : ∀ Y ∈ Sbar D g, c ≤ nrm Y := by
  intro Y hY
  refine closure_minimal (t := {Y | c ≤ nrm Y}) ?_ (isClosed_le continuous_const continuous_nrm) hY
  rintro _ ⟨x, rfl⟩
  exact hc x

theorem isCompact_box (B : ℝ) : IsCompact {Y : Matrix K K ℝ | ∀ i j, Y i j ∈ Icc 0 B} := by
  have := isCompact_univ_pi (fun _ : K => isCompact_univ_pi (fun _ : K => isCompact_Icc (a := (0 : ℝ)) (b := B)))
  have e : {Y : Matrix K K ℝ | ∀ i j, Y i j ∈ Icc 0 B} =
      (Set.univ.pi fun _ : K => Set.univ.pi fun _ : K => Icc (0 : ℝ) B) := by
    ext Y
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [e]; exact this

theorem Sbar_isCompact (hg : 0 ≤ g) {B : ℝ} (hB : ∀ x i j, Ex D g x i j ≤ B) : IsCompact (Sbar D g) :=
  (isCompact_box B).of_isClosed_subset isClosed_closure fun Y hY i j =>
    ⟨Sbar_nonneg hg Y hY i j, Sbar_entry_le hB Y hY i j⟩

/-- If `P ∈ S̄`, then for every `ε > 0` there is a word `χ` with `‖E_χ - P‖ < ε`. -/
theorem exists_word_near {P : Matrix K K ℝ} (hP : P ∈ Sbar D g) {ε : ℝ} (hε : 0 < ε) :
    ∃ χ : List (Fin 2), nrm (Ex D g χ - P) < ε := by
  have hU : IsOpen {Y : Matrix K K ℝ | nrm (Y - P) < ε} :=
    isOpen_lt (continuous_nrm.comp (continuous_id.sub continuous_const)) continuous_const
  have hPU : P ∈ {Y : Matrix K K ℝ | nrm (Y - P) < ε} := by
    simp only [Set.mem_ofPred_eq, sub_self]
    have : nrm (0 : Matrix K K ℝ) = 0 := by simp [nrm]
    rw [this]; exact hε
  obtain ⟨_, hY, ⟨χ, rfl⟩⟩ := mem_closure_iff.mp hP _ hU hPU
  exact ⟨χ, hY⟩

end Sbar

/-! ## §3 The idempotent of minimal rank in `S̄` (Lemma D.4 (ii)) -/

variable (D : Fin 2 → Matrix K K ℕ)

/-- **The Lean form of Lemma D.4 (ii)**: `S̄` contains an idempotent `P` of minimal rank, and `P ≠ 0`. -/
theorem exists_minRank_idem (hSC : SC D) {g : ℝ} (hR : RigidAt D g) :
    ∃ P ∈ Sbar D g, P * P = P ∧ (∀ Y ∈ Sbar D g, P.rank ≤ Y.rank) ∧ P ≠ 0 := by
  classical
  have hg0 : 0 ≤ g := by linarith [hR.one_lt]
  obtain ⟨L, hL⟩ := Ex_entry_bound D hSC hR.one_lt.le hR.diag_le
  have hSc : IsCompact (Sbar D g) := Sbar_isCompact hg0 hL
  -- The minimal rank
  have hex : ∃ r, ∃ Y ∈ Sbar D g, Y.rank = r := ⟨_, 1, one_mem_Sbar, rfl⟩
  obtain ⟨Y0, hY0, hY0r⟩ := Nat.find_spec hex
  have hmin : ∀ Y ∈ Sbar D g, Y0.rank ≤ Y.rank := fun Y hY => by
    rw [hY0r]; exact Nat.find_min' hex ⟨Y, hY, rfl⟩
  -- Ellis–Numakura for `Y₀ S̄`
  set T := (fun Y => Y0 * Y) '' Sbar D g
  have hTne : T.Nonempty := ⟨Y0 * 1, 1, one_mem_Sbar, rfl⟩
  have hTc : IsCompact T := hSc.image (continuous_const.mul continuous_id)
  have hTm : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ T := by
    rintro _ ⟨Y, hY, rfl⟩ _ ⟨Y', hY', rfl⟩
    exact ⟨Y * Y0 * Y', Sbar_mul_mem (Sbar_mul_mem hY hY0) hY', by simp only [Matrix.mul_assoc]⟩
  obtain ⟨P, ⟨Y, hY, rfl⟩, hPP⟩ :=
    exists_idempotent_in_compact_subsemigroup (fun r => continuous_id.mul continuous_const) T hTne hTc hTm
  have hPS : Y0 * Y ∈ Sbar D g := Sbar_mul_mem hY0 hY
  refine ⟨Y0 * Y, hPS, hPP, fun Y' hY' => ?_, ?_⟩
  · exact (Matrix.rank_mul_le_left _ _).trans (hmin Y' hY')
  · obtain ⟨c, hc, hcx⟩ := uniform_lower D hSC hR
    intro h0
    have := Sbar_nrm_ge hcx _ hPS
    rw [h0] at this
    have h1 : nrm (0 : Matrix K K ℝ) = 0 := by simp [nrm]
    linarith

/-- A non-negative idempotent `P ≠ 0` has `a` with `P_{aa} > 0` (a pivot). -/
theorem exists_diag_pos {P : Matrix K K ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (hPP : P * P = P) (hP : P ≠ 0) :
    ∃ a, 0 < P a a := by
  obtain ⟨B⟩ := nonempty_pivotBasis hP0 hPP
  by_cases hr : B.r = 0
  · exfalso
    apply hP
    ext i k
    have hfix : P *ᵥ pcol P k = pcol P k := (pcol_inCone hP0 hPP k).2
    have := congrFun (B.expand _ hfix) i
    have hz : (∑ j : Fin B.r, pcol P k (B.k j) • B.f j) = 0 := by
      have : IsEmpty (Fin B.r) := by rw [hr]; infer_instance
      simp
    rw [hz] at this
    simpa [pcol] using this
  · exact ⟨B.k ⟨0, Nat.pos_of_ne_zero hr⟩, B.diag_pos _⟩

end Collatz.Arctic.NatQ5.Rigid
