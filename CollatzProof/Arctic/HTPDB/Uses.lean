/-
Numbers of uses of the 2 dynamic rules of the system $\mathcal H$ along the orbits of the point family.
The $H$ version of `FamilyUses.lean` for $T$ (the dynamic rules in Proposition 6.7).

The first rule of the canonical derivation `canDerivH x` is determined by the residue class: for $x \equiv 0 \pmod 4$ it is `ff. → 0.` (`ffRule`), followed by
sweep rules; for $x \equiv 7 \pmod 8$ it is `ttt. → 22.` (`tttRule`), followed by the sweep rules of two sweeps (the sweep rules are
carry rules and left-end rules only, not dynamic rules). Hence, by the residue classes along orbits `SpecHClass` ($\equiv 0 \bmod 4$ if the `i`-th letter is $\mathsf a$,
$\equiv 7 \bmod 8$ if it is $\mathsf b$), the number of uses along an orbit of the family (`hSteps β` steps from `hR β + 2^m t`) reduces to
counting letters of the letter word `lettersOf β`.
* `usesOrbit_ff`, `usesOrbit_ttt`: `ff.` is used as many times as there are letters $\mathsf a$ (`= |β|`, once per block), `ttt.` as many times as there are letters $\mathsf b$
  (`= 2#X + 3#Y ≥ 2|β|`).
* `hUse_ff`, `hUse_ttt`: the event holds for every `t` (probability 1), so `HUseR` holds with `c = 1`.
* `specDynUseH`: the frozen `SpecDynUseH` (`SpecHModel` is not used; `SpecHClass` suffices).
-/
import CollatzProof.Arctic.HTPDB.Spec
import CollatzProof.Arctic.FamilyUses
import CollatzProof.Arctic.FamilyExp

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel

namespace UsesH

/-! ## Numbers of uses at one point -/

open Letter in
/-- The sweep rules (carry rules and left-end rules) are not dynamic rules. -/
lemma sweep_not_dyn : ∀ (l : List ℕ) (d : ℕ), ∀ ρ ∈ sweepRules l d, ρ ≠ ffRule ∧ ρ ≠ tttRule := by
  intro l
  induction l with
  | nil =>
    intro d ρ hρ
    simp only [sweepRules, List.mem_singleton] at hρ
    subst hρ
    unfold leftRule ffRule tttRule
    split_ifs <;> simp
  | cons b bs ih =>
    intro d ρ hρ
    simp only [sweepRules, List.mem_cons] at hρ
    rcases hρ with rfl | hρ
    · unfold aRule ffRule tttRule
      simp
    · exact ih _ ρ hρ

lemma ff_ne_ttt : ffRule ≠ tttRule := by decide

/-- A point of class $\mathsf a$: `ff.` once, `ttt.` zero times. -/
lemma count_of_A {x : ℕ} (hx : x % 4 = 0) :
    (canDerivH x).count ffRule = 1 ∧ (canDerivH x).count tttRule = 0 := by
  unfold canDerivH
  simp only [hx, ↓reduceIte]
  refine ⟨?_, ?_⟩
  · rw [List.count_cons_self, List.count_eq_zero_of_not_mem (fun hm => (sweep_not_dyn _ _ _ hm).1 rfl)]
  · rw [List.count_cons_of_ne ff_ne_ttt,
      List.count_eq_zero_of_not_mem (fun hm => (sweep_not_dyn _ _ _ hm).2 rfl)]

/-- A point of class $\mathsf b$: `ff.` zero times, `ttt.` once. -/
lemma count_of_B {x : ℕ} (hx : x % 8 = 7) :
    (canDerivH x).count ffRule = 0 ∧ (canDerivH x).count tttRule = 1 := by
  have h4 : ¬ x % 4 = 0 := by omega
  unfold canDerivH
  simp only [h4, hx, ↓reduceIte]
  refine ⟨?_, ?_⟩
  · rw [List.count_cons_of_ne (Ne.symm ff_ne_ttt), List.count_eq_zero_of_not_mem]
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (sweep_not_dyn _ _ _ hm).1 rfl
    · exact (sweep_not_dyn _ _ _ hm).1 rfl
  · rw [List.count_cons_self, List.count_eq_zero_of_not_mem]
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (sweep_not_dyn _ _ _ hm).2 rfl
    · exact (sweep_not_dyn _ _ _ hm).2 rfl

/-! ## Numbers of letters -/

/-- Removes the first block of a block sequence (with the prefix `u6_`, to avoid ambiguity with `HModel.lettersOf_cons` (`HModel/Terras2.lean`) when both
namespaces are opened). -/
lemma u6_lettersOf_cons (x : Bool) (β : List Bool) :
    lettersOf (x :: β) =
      (if x then [true, false, false] else [true, false, false, false]) ++ lettersOf β := by
  simp [lettersOf, List.flatMap_cons]

/-- There is one letter $\mathsf a$ per block. -/
lemma count_true_lettersOf (β : List Bool) : (lettersOf β).count true = β.length := by
  induction β with
  | nil => simp [lettersOf]
  | cons x β ih =>
    rw [u6_lettersOf_cons, List.count_append, ih]
    cases x <;> simp <;> omega

/-- There are at least 2 letters $\mathsf b$ per block (2 in $X$, 3 in $Y$). -/
lemma count_false_lettersOf (β : List Bool) : 2 * β.length ≤ (lettersOf β).count false := by
  induction β with
  | nil => simp [lettersOf]
  | cons x β ih =>
    rw [u6_lettersOf_cons, List.count_append]
    cases x <;> simp <;> omega

/-! ## Numbers of uses along the orbits of the family -/

/-- By the residue classes along orbits, the number of uses of `ff.` along an orbit of the family is the number of letters $\mathsf a$. -/
lemma usesOrbit_ff (hC : SpecHClass) (β : List Bool) (t : ℕ) :
    Gen.usesOrbitG Hmap canDerivH ffRule (hR β + 2 ^ (parityOf β).length * t) (hSteps β)
      = (lettersOf β).count true := by
  unfold Gen.usesOrbitG
  rw [← fam_sum_getD (lettersOf β) true]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have h := hC β t i hi
  by_cases hl : (lettersOf β).getD i false = true
  · simp only [hl, ↓reduceIte] at h ⊢
    exact (count_of_A h).1
  · simp only [hl] at h ⊢
    exact (count_of_B h).1

/-- By the residue classes along orbits, the number of uses of `ttt.` along an orbit of the family is the number of letters $\mathsf b$. -/
lemma usesOrbit_ttt (hC : SpecHClass) (β : List Bool) (t : ℕ) :
    Gen.usesOrbitG Hmap canDerivH tttRule (hR β + 2 ^ (parityOf β).length * t) (hSteps β)
      = (lettersOf β).count false := by
  unfold Gen.usesOrbitG
  rw [← fam_sum_getD (lettersOf β) false]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have h := hC β t i hi
  by_cases hl : (lettersOf β).getD i false = true
  · simp only [hl, ↓reduceIte] at h ⊢
    exact (count_of_A h).2
  · simp only [hl] at h
    simp only [Bool.not_eq_true] at hl
    simp only [hl, ↓reduceIte]
    exact (count_of_B h).2

/-! ## Events of probability 1 -/

open Classical in
/-- An event that holds for every choice of length `k` has probability 1. -/
lemma prσ_eq_one (β₀ : List Bool) (k : ℕ) {E : List Bool → Prop}
    (h : ∀ β ∈ blockChoices k, E (β₀ ++ β)) : Prσ β₀ k E = 1 := by
  unfold Prσ
  rw [Finset.filter_true_of_mem h]
  exact (fam_moments k).1

end UsesH

open UsesH

/-- **Uses of `ff.`** (from `SpecHClass`): along an orbit of the family, `ff.` is used `|β₀| + k ≥ k` times (for every `t`). -/
theorem hUse_ff (hC : SpecHClass) : Gen.HUseR Hmap hR hSteps canDerivH ffRule := by
  intro β₀
  refine ⟨1, one_pos, fun ε hε => ⟨0, fun k _ => ?_⟩⟩
  have h1 := prσ_eq_one β₀ k (E := fun β => ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      (1 : ℚ) * k ≤ (Gen.usesOrbitG Hmap canDerivH ffRule (hR β + 2 ^ (parityOf β).length * t)
        (hSteps β) : ℚ)) (fun β hβ t _ => by
      rw [usesOrbit_ff hC, count_true_lettersOf, List.length_append,
        (fam_mem_blockChoices β k).mp hβ]
      push_cast
      linarith)
  linarith

/-- **Uses of `ttt.`** (from `SpecHClass`): along an orbit of the family, `ttt.` is used `2#X + 3#Y ≥ 2k` times (for every `t`). -/
theorem hUse_ttt (hC : SpecHClass) : Gen.HUseR Hmap hR hSteps canDerivH tttRule := by
  intro β₀
  refine ⟨1, one_pos, fun ε hε => ⟨0, fun k _ => ?_⟩⟩
  have h1 := prσ_eq_one β₀ k (E := fun β => ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      (1 : ℚ) * k ≤ (Gen.usesOrbitG Hmap canDerivH tttRule (hR β + 2 ^ (parityOf β).length * t)
        (hSteps β) : ℚ)) (fun β hβ t _ => by
      rw [usesOrbit_ttt hC]
      have h2 := count_false_lettersOf (β₀ ++ β)
      rw [List.length_append, (fam_mem_blockChoices β k).mp hβ] at h2
      have h3 : (k : ℚ) ≤ ((lettersOf (β₀ ++ β)).count false : ℚ) := by
        exact_mod_cast (show k ≤ (lettersOf (β₀ ++ β)).count false by omega)
      linarith)
  linarith

/-- **Output on the dynamic rules** (the 2 dynamic rules): the frozen `SpecDynUseH`. -/
theorem specDynUseH : SpecDynUseH :=
  fun _ hC => ⟨hUse_ff hC, hUse_ttt hC⟩

end Collatz.Arctic.HTPDB
