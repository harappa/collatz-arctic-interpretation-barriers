/-
# The rest of Lemma D.4 (iii): `H_P` acts monomially, has order `≤ r_0!`, and its elements have rank `r_0`

The statement: `H_P` is a group with identity `P` and `|H_P| ≤ r_0!`; its elements are non-negative matrices of rank `r_0`, and they permute the pivot
generators `f_i` as `A f_i = λ_i f_{σ_A(i)}` (`λ_i > 0`, `σ_A` a permutation; monomial action).

`RigidIdem.lean` proves only the group property, finiteness, `A^h = P` and discreteness (all that is used downstream). Here we prove the rest of the statement:
* `HP_rank`: the elements have rank `rank P`.
* `HP_monomial`: in the pivot coordinates, every column has exactly one non-zero entry (a non-negative matrix with a non-negative inverse). Hence
  `A f_i = λ_i f_{σ(i)}`, `λ_i > 0`, `σ` a permutation.
* `HP_ncard_le`: `|H_P| ≤ (rank P)!` (`A ↦ σ_A` is injective, by the injectivity of the pattern `HP_pat_inj`).
-/
import CollatzProof.Arctic.Nat.RigidIdem

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix Set

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] [DecidableEq K]

section Abstract

variable {S : Set (Matrix K K ℝ)} {P : Matrix K K ℝ}
  (hSc : IsCompact S) (hSm : ∀ Y ∈ S, ∀ Z ∈ S, Y * Z ∈ S) (hS0 : ∀ Y ∈ S, ∀ i j, 0 ≤ Y i j)
  (hPS : P ∈ S) (hPP : P * P = P) (hPmin : ∀ Y ∈ S, P.rank ≤ Y.rank)

include hSm hPS hPmin in
/-- The elements of `H_P` have rank `rank P`. -/
theorem HP_rank {A : Matrix K K ℝ} (hA : A ∈ HP P S) : A.rank = P.rank := by
  apply le_antisymm
  · obtain ⟨Y, -, rfl⟩ := hA
    show (P * Y * P).rank ≤ P.rank
    rw [Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left _ _
  · exact hPmin _ (HP_subset hSm hPS hA)

include hSc hSm hS0 hPS hPP hPmin in
/-- Every column of the pivot coordinates has exactly one non-zero entry. -/
theorem coord_col_unique (B : PivotBasis P) {A : Matrix K K ℝ} (hA : A ∈ HP P S) (i : Fin B.r) :
    ∃! j, coord B A j i ≠ 0 := by
  obtain ⟨A', hA', hAA', hA'A⟩ := HP_inv hSc hSm hPS hPP hPmin hA
  have h1 : coord B A * coord B A' = 1 := by
    rw [← coord_mul B (HP_left_P hPP hA) (HP_left_P hPP hA'), hAA', coord_P]
  have h2 : coord B A' * coord B A = 1 := by
    rw [← coord_mul B (HP_left_P hPP hA') (HP_left_P hPP hA), hA'A, coord_P]
  have hnn : ∀ j i, 0 ≤ coord B A j i := coord_nonneg B (hS0 A (HP_subset hSm hPS hA))
  have hnn' : ∀ j i, 0 ≤ coord B A' j i := coord_nonneg B (hS0 A' (HP_subset hSm hPS hA'))
  have hex : ∃ j, coord B A j i ≠ 0 := by
    by_contra hc
    push Not at hc
    have : (coord B A' * coord B A) i i = 0 := by
      rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun j _ => by rw [hc j, mul_zero]
    rw [h2, Matrix.one_apply_eq] at this
    exact one_ne_zero this
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hj, fun j' hj' => ?_⟩
  by_contra hne
  have key : ∀ m l, coord B A m i ≠ 0 → m ≠ l → coord B A' i l = 0 := by
    intro m l hm hml
    have h3 : (coord B A * coord B A') m l = 0 := by rw [h1, Matrix.one_apply_ne hml]
    rw [Matrix.mul_apply] at h3
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (hnn m k) (hnn' k l)).mp h3 i (Finset.mem_univ i)
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h hm
    · exact h
  have hrow : ∀ l, coord B A' i l = 0 := by
    intro l
    by_cases hl : j = l
    · exact key j' l hj' fun h => hne (h.trans hl.symm)
    · exact key j l hj hl
  have : (coord B A' * coord B A) i i = 0 := by
    rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun k _ => by rw [hrow k, zero_mul]
  rw [h2, Matrix.one_apply_eq] at this
  exact one_ne_zero this

include hSc hSm hS0 hPS hPP hPmin in
/-- **Monomial action**: `A f_i = λ_i f_{σ(i)}`, `λ_i > 0`, `σ` a permutation. -/
theorem HP_monomial (B : PivotBasis P) {A : Matrix K K ℝ} (hA : A ∈ HP P S) :
    ∃ (σ : Equiv.Perm (Fin B.r)) (lam : Fin B.r → ℝ), (∀ i, 0 < lam i) ∧
      (∀ i j, coord B A j i ≠ 0 ↔ j = σ i) ∧ ∀ i, A *ᵥ B.f i = lam i • B.f (σ i) := by
  classical
  have hu := fun i => coord_col_unique hSc hSm hS0 hPS hPP hPmin B hA i
  choose σf hσf huniq using hu
  have hnn : ∀ j i, 0 ≤ coord B A j i := coord_nonneg B (hS0 A (HP_subset hSm hPS hA))
  have hiff : ∀ i j, coord B A j i ≠ 0 ↔ j = σf i :=
    fun i j => ⟨fun h => huniq i j h, fun h => h ▸ hσf i⟩
  -- `σf` is injective
  have hinj : Function.Injective σf := by
    intro i i' he
    by_contra hii
    obtain ⟨A', hA', hAA', hA'A⟩ := HP_inv hSc hSm hPS hPP hPmin hA
    have hnn' : ∀ j i, 0 ≤ coord B A' j i := coord_nonneg B (hS0 A' (HP_subset hSm hPS hA'))
    have h2 : coord B A' * coord B A = 1 := by
      rw [← coord_mul B (HP_left_P hPP hA') (HP_left_P hPP hA), hA'A, coord_P]
    have h3 : (coord B A' * coord B A) i i' = 0 := by rw [h2, Matrix.one_apply_ne hii]
    rw [Matrix.mul_apply] at h3
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (hnn' i k) (hnn k i')).mp h3 (σf i) (Finset.mem_univ _)
    have h5 : coord B A' i (σf i) = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h (by rw [he]; exact hσf i')
    have h6 : (coord B A' * coord B A) i i = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = σf i
      · rw [hk, h5, zero_mul]
      · have : coord B A k i = 0 := by
          by_contra hc; exact hk ((hiff i k).mp hc)
        rw [this, mul_zero]
    rw [h2, Matrix.one_apply_eq] at h6
    exact one_ne_zero h6
  set σ := Equiv.ofBijective σf hinj.bijective_of_finite
  refine ⟨σ, fun i => coord B A (σf i) i, fun i => lt_of_le_of_ne (hnn _ _) (Ne.symm (hσf i)),
    fun i j => hiff i j, fun i => ?_⟩
  rw [coord_spec B (HP_left_P hPP hA) i, Finset.sum_eq_single (σf i)]
  · rfl
  · intro j _ hj
    have : coord B A j i = 0 := by by_contra hc; exact hj ((hiff i j).mp hc)
    rw [this, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

include hSc hSm hS0 hPS hPP hPmin in
/-- **`|H_P| ≤ (rank P)!`**. -/
theorem HP_ncard_le : (HP P S).ncard ≤ (P.rank).factorial := by
  classical
  obtain ⟨B⟩ := nonempty_pivotBasis (hS0 P hPS) hPP
  have hmono := fun A (hA : A ∈ HP P S) => HP_monomial hSc hSm hS0 hPS hPP hPmin B hA
  let Φ : Matrix K K ℝ → Equiv.Perm (Fin B.r) := fun A =>
    if hA : A ∈ HP P S then (hmono A hA).choose else 1
  have hinj : InjOn Φ (HP P S) := by
    intro A hA C hC he
    simp only [Φ, dite_eq_left hA, hC, dite_true] at he
    have hA' := (hmono A hA).choose_spec
    have hC' := (hmono C hC).choose_spec
    obtain ⟨_, -, hAiff, -⟩ := hA'
    obtain ⟨_, -, hCiff, -⟩ := hC'
    refine HP_pat_inj hSc hSm hS0 hPS hPP hPmin B hA hC (fun j i h => ?_) (fun j i h => ?_)
    · rw [hCiff, ← he]; exact (hAiff i j).mp h
    · rw [hAiff, he]; exact (hCiff i j).mp h
  have h1 := Set.ncard_le_ncard_of_injOn Φ (Set.mapsTo_univ _ _) hinj Set.finite_univ
  rw [Set.ncard_univ, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  rw [B.rank_eq hPP]
  exact h1

end Abstract

end Collatz.Arctic.NatQ5.Rigid
