/-
Uses of the left-end rules of the system $\mathcal H$, part 1: the combinatorial part.
The decision on the real mantissa is in `LeftUseReal.lean`; the main theorems `hUse_left` and `specLeftUseH` are in `LeftUseMain.lean`.

Adapted from `HLUDet.lean` for $T$ (`hlu_uses_left_odd`, `hlu_parity_blockEnd`, `hlu_P_odd`,
`hlu_usesOrbit_ge_boundary`).

Correspondence with the paper: the $H$ version of the left-end part of Proposition 6.7 (ii) and its proof (Section 7, uses of the left-end rules of $\mathcal H$).
* For a point `n` of a step $\mathsf a$ (`n ≡ 0 (mod 4)`, `n ≥ 4`), the canonical derivation `canDerivH n = ff. → 0.` + the sweep of the digit 0,
  `sweepRules (tailBitsLSB (n/4)) 0`, uses `leftRule d` (once) exactly when the top window of `y = n/4` is `3y / 2^{⌊log₂ y⌋} = 3 + d`
  (`hluH_count_left_A`; the lemma `hlu_sweep_count` for $T$ is used as it is, with `d = 0`).
* Blocks begin with a step $\mathsf a$: the boundary point is the point of the orbit after `hSteps (β.take i)` steps (a **step** index, different from the bit index
  `blockEnd β i`), and its letter is $\mathsf a$ (`hluH_letter_boundary`). By `SpecHClass` the boundary points are
  `≡ 0 (mod 4)` (`hluH_P_mod4`).
* The step indices `hSteps (β.take i)` of the boundary points increase strictly in `i` and are less than `hSteps β` (`hluH_hSteps_take_strict`,
  `hluH_hSteps_take_lt`). Hence the number of uses of a left-end rule is at least the number of boundary points with top window `3 + d`
  (`hluH_usesOrbitG_ge_boundary`).
-/
import CollatzProof.Arctic.HTPDB.Spec
import CollatzProof.Arctic.HLUDet

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel

/-! ## Left-end rules at points of a step $\mathsf a$ -/

open Letter in
/-- The dynamic rule `ff. → 0.` is not a left-end rule. -/
lemma hluH_ff_ne_left (e : ℕ) : ffRule ≠ leftRule e := by
  unfold ffRule leftRule
  split_ifs <;> simp

/-- **Left-end rules at points of a step $\mathsf a$** (the $H$ version of the left-end part of Proposition 6.7 (ii)): the canonical derivation of `n ≡ 0 (mod 4)`, `n ≥ 4`
uses `leftRule d` (once) exactly when the top window of `y = n/4` is `3y / 2^{⌊log₂ y⌋} = 3 + d`. -/
theorem hluH_count_left_A (n d : ℕ) (hn : 4 ≤ n) (h4 : n % 4 = 0) (hd : d ≤ 2) :
    (canDerivH n).count (leftRule d)
      = if 3 * (n / 4) / 2 ^ Nat.log 2 (n / 4) = 3 + d then 1 else 0 := by
  have hy : 1 ≤ n / 4 := by omega
  unfold canDerivH
  simp only [h4, ↓reduceIte]
  rw [List.count_cons, hlu_sweep_count (n / 4) hy 0 (Nat.zero_le _) d hd, Nat.add_zero]
  have : (ffRule == leftRule d) = false := by simpa using hluH_ff_ne_left d
  rw [this]
  simp

/-! ## Letter words and block boundaries -/

/-- The first block of `lettersOf`. -/
lemma hluH_lettersOf_cons (x : Bool) (β : List Bool) :
    lettersOf (x :: β) = (if x then [true, false, false] else [true, false, false, false]) ++ lettersOf β := by
  simp [lettersOf]

/-- `lettersOf` preserves concatenation. -/
lemma hluH_lettersOf_append (β₁ β₂ : List Bool) :
    lettersOf (β₁ ++ β₂) = lettersOf β₁ ++ lettersOf β₂ := by
  simp [lettersOf, List.flatMap_append]

/-- The number of steps is additive under concatenation. -/
lemma hluH_hSteps_append (β₁ β₂ : List Bool) : hSteps (β₁ ++ β₂) = hSteps β₁ + hSteps β₂ := by
  unfold hSteps
  rw [hluH_lettersOf_append, List.length_append]

/-- A block has at least 3 steps. -/
lemma hluH_hSteps_ge (β : List Bool) : 3 * β.length ≤ hSteps β := by
  induction β with
  | nil => simp [hSteps, lettersOf]
  | cons x β ih =>
    unfold hSteps at ih ⊢
    rw [hluH_lettersOf_cons, List.length_append, List.length_cons]
    cases x <;> simp <;> omega

/-- The step index of a boundary point is less than the total number of steps (at least one block remains). -/
lemma hluH_hSteps_take_lt (β : List Bool) (i : ℕ) (hi : i < β.length) :
    hSteps (β.take i) < hSteps β := by
  have h := hluH_hSteps_append (β.take i) (β.drop i)
  rw [List.take_append_drop] at h
  have h3 := hluH_hSteps_ge (β.drop i)
  rw [List.length_drop] at h3
  omega

/-- The step indices of the boundary points increase strictly. -/
lemma hluH_hSteps_take_strict (β : List Bool) (i j : ℕ) (hij : i < j) (hj : j ≤ β.length) :
    hSteps (β.take i) < hSteps (β.take j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
  rw [List.take_add, hluH_hSteps_append]
  have h := hluH_hSteps_ge ((β.drop i).take (k + 1))
  rw [List.length_take, List.length_drop] at h
  have : 1 ≤ min (k + 1) (β.length - i) := by omega
  omega

/-- Blocks begin with a step $\mathsf a$: the letter at position `hSteps (β.take i)` of the letter word is $\mathsf a$ (`true`). -/
lemma hluH_letter_boundary (β : List Bool) (i : ℕ) (hi : i < β.length) :
    (lettersOf β).getD (hSteps (β.take i)) false = true := by
  have e : lettersOf β = lettersOf (β.take i) ++ lettersOf (β.drop i) := by
    rw [← hluH_lettersOf_append, List.take_append_drop]
  rw [e]
  unfold hSteps
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.drop_eq_getElem_cons hi,
    hluH_lettersOf_cons]
  cases β[i] <;> simp

/-- The boundary point `P_i = H^{hSteps (β.take i)} x₀` is `≡ 0 (mod 4)` (by `SpecHClass`). -/
theorem hluH_P_mod4 (hC : SpecHClass) (β : List Bool) (t i : ℕ) (hi : i < β.length) :
    Hmap^[hSteps (β.take i)] (hR β + 2 ^ (parityOf β).length * t) % 4 = 0 := by
  have h := hC β t _ (hluH_hSteps_take_lt β i hi)
  simp only [hluH_letter_boundary β i hi, ↓reduceIte] at h
  exact h

/-- The boundary points are at least 8 (by `orbit_dom` of `SpecHModel`, `t ≥ 1`). -/
theorem hluH_P_ge (hM : SpecHModel) (β : List Bool) (t i : ℕ) (ht : 1 ≤ t) (hi : i < β.length) :
    8 ≤ Hmap^[hSteps (β.take i)] (hR β + 2 ^ (parityOf β).length * t) :=
  (hM.orbit_dom β t ht _ (hluH_hSteps_take_lt β i hi)).1

/-- **Uses of left-end rules at the boundary points** (the $H$ version of the left-end part of the proof of Proposition 6.7 (ii)): for `t ≥ 1`, the number of
block indices `i` such that the top window of `y = P_i/4` for the boundary point `P_i` is `3 + d` is at most the number of uses of `leftRule d`
in the `hSteps β` steps from `x₀`. -/
theorem hluH_usesOrbitG_ge_boundary (hM : SpecHModel) (hC : SpecHClass) (β : List Bool) (t d : ℕ)
    (ht : 1 ≤ t) (hd : d ≤ 2) :
    ((Finset.range β.length).filter (fun i =>
        3 * (Hmap^[hSteps (β.take i)] (hR β + 2 ^ (parityOf β).length * t) / 4)
          / 2 ^ Nat.log 2 (Hmap^[hSteps (β.take i)] (hR β + 2 ^ (parityOf β).length * t) / 4)
          = 3 + d)).card
      ≤ Gen.usesOrbitG Hmap canDerivH (leftRule d) (hR β + 2 ^ (parityOf β).length * t) (hSteps β) := by
  unfold Gen.usesOrbitG
  rw [hlu_list_sum_range]
  refine hlu_card_le_sum _ _ (fun i => hSteps (β.take i)) _ _ (fun i hi => hluH_hSteps_take_lt β i hi)
    (fun i j hij hj => hluH_hSteps_take_strict β i j hij hj.le) ?_
  intro i hi hp
  have h4 := hluH_P_mod4 hC β t i hi
  have h8 := hluH_P_ge hM β t i ht hi
  rw [hluH_count_left_A _ d (by omega) h4 hd]
  simp [hp]

end Collatz.Arctic.HTPDB
