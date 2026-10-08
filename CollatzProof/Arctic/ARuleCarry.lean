/-
Components of the formalization of Proposition 3.7 and Proposition 6.7 (iii) (quadratic use of the carry rules A): the shapes of the low binary digits, and
the number of carry rules A in the sweep of a ternary digit (the carry chain).

* For odd `n`, the number of carry rules `aRule b d` in the canonical derivation equals the number of positions where
  `(digit, carry) = (b, d)` in the chain that reads the digits of `y = (n-1)/2` (from the bottom, `tailBitsLSB y`) starting with carry 2 (`uses_aRule_odd`).
* Three shapes with periodic low digits: `y = 2^L z` (`L` zeros at the bottom), `y + 1 = 2^L (z + 1)` (`L` ones),
  `5y + 2 = 16^j (5Q + 2)` (`j` copies of the period `0110` (from the bottom) of the binary expansion of `-2/5`).
* Along the chain, a run of 0s keeps carry 0 and uses `f0 → 0f` (`aRule 0 0`); a run of 1s keeps carry 2 and uses `t2 → 2t`
  (`aRule 1 2`). The period `0110`, starting from carry 1, uses `aRule 0 1`, `aRule 1 0`, `aRule 1 1`, `aRule 0 2`
  once each and returns to carry 1.
-/
import CollatzProof.Arctic.Main

namespace Collatz.Arctic.ARule

/-! ### Shapes of the low digits -/

/-- `L` zeros at the bottom: `y = 2^L z` (`z ≥ 1`). -/
lemma tailBitsLSB_zeros : ∀ (L y z : ℕ), 1 ≤ z → y = 2 ^ L * z →
    tailBitsLSB y = List.replicate L 0 ++ tailBitsLSB z := by
  intro L
  induction L with
  | zero => intro y z _ h; simp [h]
  | succ L ih =>
    intro y z hz h
    have hpos : 1 ≤ 2 ^ L * z := Nat.mul_pos (Nat.two_pow_pos L) hz
    rw [h, pow_succ, show 2 ^ L * 2 * z = 2 * (2 ^ L * z) + 0 by ring,
      tailBitsLSB_two_mul_add _ 0 hpos (by norm_num), ih _ z hz rfl]
    simp [List.replicate_succ]

/-- `L` ones at the bottom: `y + 1 = 2^L (z + 1)` (`z ≥ 1`). -/
lemma tailBitsLSB_ones : ∀ (L y z : ℕ), 1 ≤ z → y + 1 = 2 ^ L * (z + 1) →
    tailBitsLSB y = List.replicate L 1 ++ tailBitsLSB z := by
  intro L
  induction L with
  | zero => intro y z _ h; simp [show y = z by simpa using h]
  | succ L ih =>
    intro y z hz h
    have hX : 2 ≤ 2 ^ L * (z + 1) := by
      have : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      nlinarith
    have h2 : 2 ^ (L + 1) * (z + 1) = 2 * (2 ^ L * (z + 1)) := by rw [pow_succ]; ring
    rw [h2] at h
    obtain ⟨y', rfl⟩ : ∃ y', y = 2 * y' + 1 := ⟨y / 2, by omega⟩
    rw [tailBitsLSB_two_mul_add _ 1 (by omega) (by norm_num), ih y' z hz (by omega)]
    simp [List.replicate_succ]

/-- `j` repetitions of `0 1 1 0` (from the bottom) (the period of the binary expansion of `-2/5`). -/
def pat : ℕ → List ℕ
  | 0 => []
  | j + 1 => 0 :: 1 :: 1 :: 0 :: pat j

lemma tailBitsLSB_16 (y : ℕ) (hy : 1 ≤ y) :
    tailBitsLSB (16 * y + 6) = 0 :: 1 :: 1 :: 0 :: tailBitsLSB y := by
  have e1 : 16 * y + 6 = 2 * (8 * y + 3) + 0 := by ring
  have e2 : 8 * y + 3 = 2 * (4 * y + 1) + 1 := by ring
  have e3 : 4 * y + 1 = 2 * (2 * y) + 1 := by ring
  have e4 : 2 * y = 2 * y + 0 := by ring
  rw [e1, tailBitsLSB_two_mul_add _ 0 (by omega) (by norm_num), e2,
    tailBitsLSB_two_mul_add _ 1 (by omega) (by norm_num), e3,
    tailBitsLSB_two_mul_add _ 1 (by omega) (by norm_num), e4,
    tailBitsLSB_two_mul_add _ 0 (by omega) (by norm_num)]

/-- `j` copies of the period `0110` at the bottom: `5y + 2 = 16^j (5Q + 2)` (`Q ≥ 1`; `y ≡ -2/5 mod 16^j`). -/
lemma tailBitsLSB_pat : ∀ (j y Q : ℕ), 1 ≤ Q → 5 * y + 2 = 16 ^ j * (5 * Q + 2) →
    tailBitsLSB y = pat j ++ tailBitsLSB Q := by
  intro j
  induction j with
  | zero => intro y Q _ h; simp [pat, show y = Q by simp at h; omega]
  | succ j ih =>
    intro y Q hQ h
    have hX : 7 ≤ 16 ^ j * (5 * Q + 2) := by
      have : 1 ≤ 16 ^ j := Nat.one_le_pow _ _ (by norm_num)
      nlinarith
    have h2 : 16 ^ (j + 1) * (5 * Q + 2) = 16 * (16 ^ j * (5 * Q + 2)) := by rw [pow_succ]; ring
    rw [h2] at h
    obtain ⟨y', rfl⟩ : ∃ y', y = 16 * y' + 6 := ⟨y / 16, by omega⟩
    rw [tailBitsLSB_16 y' (by omega), ih y' Q hQ (by omega)]
    rfl

/-! ### Counts in the sweep -/

lemma count_le_cons (ρ x : Rule) (l : List Rule) : l.count ρ ≤ (x :: l).count ρ := by
  rw [List.count_cons]; omega

/-- Sweeping a run of 0s with carry 0 uses `aRule 0 0` as many times as the length of the run. -/
lemma count_sweep_zeros : ∀ (L : ℕ) (rest : List ℕ),
    L ≤ (sweepRules (List.replicate L 0 ++ rest) 0).count (aRule 0 0) := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro rest
    have : sweepRules (List.replicate (L + 1) 0 ++ rest) 0 =
        aRule 0 0 :: sweepRules (List.replicate L 0 ++ rest) 0 := rfl
    rw [this, List.count_cons_self]
    have := ih rest
    omega

/-- Sweeping a run of 1s with carry 2 uses `aRule 1 2` as many times as the length of the run. -/
lemma count_sweep_ones : ∀ (L : ℕ) (rest : List ℕ),
    L ≤ (sweepRules (List.replicate L 1 ++ rest) 2).count (aRule 1 2) := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro rest
    have : sweepRules (List.replicate (L + 1) 1 ++ rest) 2 =
        aRule 1 2 :: sweepRules (List.replicate L 1 ++ rest) 2 := rfl
    rw [this, List.count_cons_self]
    have := ih rest
    omega

/-- The four carry rules used when sweeping the period `0110` starting from carry 1. -/
def patRules : List Rule := [aRule 0 1, aRule 1 0, aRule 1 1, aRule 0 2]

/-- Sweeping `j` copies of the period `0110` starting from carry 1 uses each rule of `patRules` at least `j` times. -/
lemma count_sweep_pat (ρ : Rule) (hρ : ρ ∈ patRules) : ∀ (j : ℕ) (rest : List ℕ),
    j ≤ (sweepRules (pat j ++ rest) 1).count ρ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro rest
    have h4 : sweepRules (pat (j + 1) ++ rest) 1 = patRules ++ sweepRules (pat j ++ rest) 1 := rfl
    rw [h4, List.count_append]
    have := List.count_pos_iff.mpr hρ
    have := ih rest
    omega

/-- For odd `n`, the number of uses of a carry rule is its count in the list obtained by sweeping the digits of `(n-1)/2` starting from carry 2
(the leading `t. → 2.` is not a carry rule). -/
lemma uses_aRule_odd (b d n : ℕ) (hn : n % 2 = 1) :
    uses (aRule b d) n = (sweepRules (tailBitsLSB ((n - 1) / 2)) 2).count (aRule b d) := by
  unfold uses canDeriv
  have hev : ¬ n % 2 = 0 := by omega
  simp only [hev, ↓reduceIte]
  rw [List.count_cons_of_ne]
  intro h
  have := congrArg Rule.lhs h
  simp only [aRule, List.cons.injEq] at this
  obtain ⟨-, h2, -⟩ := this
  unfold digL at h2
  split_ifs at h2

end Collatz.Arctic.ARule
