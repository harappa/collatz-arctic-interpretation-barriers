/-
Numerical bounds for the assembly of Theorem 6.8 of the paper: width, number and exceptional length of the partition at the starting point (`part_numeric`).
Cutting into `M := ⌈4/ε⌉` pieces, each interval has width at most `εN₀`, and there are at most `ε⁻²` intervals (`ε ≤ 1/16`).
-/
import Mathlib

namespace Collatz.Arctic

lemma ceil_four_div_pos {ε : ℝ} (hε : 0 < ε) : 1 ≤ ⌈4 / ε⌉₊ := by
  have : (0 : ℝ) < 4 / ε := by positivity
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)

/-- `x / M ≤ ε x / 4` (division of natural numbers, `M = ⌈4/ε⌉`). -/
lemma div_ceil_le {ε : ℝ} (hε : 0 < ε) (x : ℕ) : ((x / ⌈4 / ε⌉₊ : ℕ) : ℝ) ≤ ε * x / 4 := by
  have hM : (4 / ε : ℝ) ≤ ⌈4 / ε⌉₊ := Nat.le_ceil _
  have hMpos : (0 : ℝ) < ⌈4 / ε⌉₊ := by
    have := ceil_four_div_pos hε; exact_mod_cast this
  calc ((x / ⌈4 / ε⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) / ⌈4 / ε⌉₊ := Nat.cast_div_le
    _ ≤ (x : ℝ) / (4 / ε) := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hM
    _ = ε * x / 4 := by field_simp

/-- **Numerical conditions for the partition at the starting point.** If `m ≥ 8k` and `4(K + s + 12) ≤ 8εk`, then the widths of the pieces and the exceptional length are at most `εN₀`,
and the number `2⌈4/ε⌉ + 3` of intervals is at most `ε⁻²`. -/
theorem part_numeric {ε : ℝ} (hε : 0 < ε) (hε16 : ε ≤ 1 / 16) (K s F m k : ℕ) (hmk : 8 * k ≤ m)
    (hk : 4 * ((K : ℝ) + s + 12) ≤ ε * (8 * k)) :
    ((((K - 1) + s + (F / ⌈4 / ε⌉₊ + 1) + 11 * (k / ⌈4 / ε⌉₊ + 1) : ℕ) : ℝ) ≤
        ε * (((K - 1) + F + s + m : ℕ) : ℝ)) ∧
      ((((K - 1) + s + s : ℕ) : ℝ) ≤ ε * (((K - 1) + F + s + m : ℕ) : ℝ)) ∧
      ((⌈4 / ε⌉₊ + ⌈4 / ε⌉₊ + 3 : ℕ) : ℝ) ≤ ε⁻¹ ^ 2 := by
  have hF := div_ceil_le hε F
  have hk' := div_ceil_le hε k
  have hmk' : (8 : ℝ) * k ≤ m := by exact_mod_cast hmk
  have hN : ((((K - 1) + F + s + m : ℕ) : ℝ)) ≥ F + s + m := by push_cast; have := Nat.zero_le (K - 1); push_cast; linarith [(Nat.cast_nonneg (K - 1) : (0 : ℝ) ≤ ((K - 1 : ℕ) : ℝ))]
  have hK1 : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    nlinarith
  · push_cast
    nlinarith
  · have hc := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 4 / ε)
    push_cast
    have he : ε⁻¹ ^ 2 = 1 / ε ^ 2 := by rw [inv_pow, one_div]
    rw [he, le_div_iff₀ (by positivity)]
    have h4 : (4 / ε) * ε ^ 2 = 4 * ε := by field_simp
    nlinarith

end Collatz.Arctic
