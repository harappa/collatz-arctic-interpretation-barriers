/-
Components of the quadratic use of the carry rules $A$ for the system $\mathcal H$ (Lemma 7.3):
the number of carry rules in `canDerivH`, the formula for one step of $H$, and the carry families $Z_H$ (`aRule 0 0`) and $O_H$ (`aRule 1 2`).
The $H$ version of `ARuleFamily.lean` for $T$ (families Z, O). The frame for the families is the general form `Gen.Quad.quad_of_familyG` (`Gen/Quad.lean`).

The families are taken near the 2-adic periodic points of $H$ (numerically checked by the script `check_hmodel.py` of Appendix C).
* **Family $Z_H$** (`famZH`, the fixed point 0 of the step $\mathsf a$, $3n/4$): stage `k` is `n = 4^(k+1) z` (`z ≥ 1`). A point of stage `k+1` moves to stage `k`
  in one step $\mathsf a$ (`z ↦ 3z`). For a point of stage `k+1`, `n/4 = 2^(2k+2) z` ends with `2k+2` zeros, so with carry 0 its sweep
  uses `f0 → 0f` (`aRule 0 0`) at least `2k+2` times. (A point of stage `k+1` has the form `4^(k+2) z`, and a point of stage `k`
  the form `4^(k+1) z`.)
* **Family $O_H$** (`famOH`, the fixed point $-1$ of the step $\mathsf b$, $(9n+1)/8$): stage `k` is `n + 1 = 8^(k+1) (z + 1)` (`z ≥ 1`). A point of stage `k+1` moves
  to stage `k` in one step $\mathsf b$ (`z ↦ 9z + 8`). For a point of stage `k+1`, `m = (n-7)/8` satisfies `m + 1 = 2^(3k+3) (z + 1)`, so it ends with
  `3k+3` ones, and the first sweep (carry 2) uses `t2 → 2t` (`aRule 1 2`) at least `3k+3` times.
* The family $F_H$ (the cycle $3/5 \leftrightarrow 4/5$) and `quadH` for the six carry rules are in `ARuleFive.lean`.
-/
import CollatzProof.Arctic.Gen.Quad
import CollatzProof.Arctic.HTPDB.Spec

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel

namespace ARuleH

/-! ## One step of $H$ -/

/-- A step $\mathsf a$ (with the prefix `u6_`, to avoid ambiguity with `HModel.Hmap_A` (`HModel/Terras.lean`) when both namespaces are opened). -/
lemma u6_Hmap_A {n : ℕ} (h : n % 4 = 0) : Hmap n = 3 * (n / 4) := by
  simp only [Hmap, h, ↓reduceIte]

/-- A step $\mathsf b$ (with the prefix for the same reason as `u6_Hmap_A`). -/
lemma u6_Hmap_B {n : ℕ} (h : n % 8 = 7) : Hmap n = (9 * n + 1) / 8 := by
  have h4 : ¬ n % 4 = 0 := by omega
  simp only [Hmap, h4, h, ↓reduceIte]

/-! ## The number of carry rules in a canonical derivation -/

lemma aRule_ne_ff (b d : ℕ) : aRule b d ≠ ffRule := by
  intro h
  have := congrArg (fun r : Rule => r.lhs.length) h
  simp [aRule, ffRule] at this

lemma aRule_ne_ttt (b d : ℕ) : aRule b d ≠ tttRule := by
  intro h
  have := congrArg (fun r : Rule => r.lhs.length) h
  simp [aRule, tttRule] at this

/-- A point of class $\mathsf a$: the number of a carry rule is its number in the sweep of the digits of `n/4` starting with carry 0. -/
lemma count_aRule_A (b d n : ℕ) (hn : n % 4 = 0) :
    (canDerivH n).count (aRule b d) = (sweepRules (tailBitsLSB (n / 4)) 0).count (aRule b d) := by
  unfold canDerivH
  simp only [hn, ↓reduceIte]
  rw [List.count_cons_of_ne (Ne.symm (aRule_ne_ff b d))]

/-- A point of class $\mathsf b$: the number of a carry rule is the sum of its numbers in the two sweeps of the digits of `m = (n-7)/8` and of `3m + 2`,
both starting with carry 2 (the left digit 2 crosses `bin'(m)`, then the right digit 2 crosses `bin'(3m+2)`). -/
lemma count_aRule_B (b d n : ℕ) (hn : n % 8 = 7) :
    (canDerivH n).count (aRule b d) =
      (sweepRules (tailBitsLSB ((n - 7) / 8)) 2).count (aRule b d) +
        (sweepRules (tailBitsLSB (3 * ((n - 7) / 8) + 2)) 2).count (aRule b d) := by
  have h4 : ¬ n % 4 = 0 := by omega
  unfold canDerivH
  simp only [h4, hn, ↓reduceIte]
  rw [List.count_cons_of_ne (Ne.symm (aRule_ne_ttt b d)), List.count_append]

/-! ## Family $Z_H$ (the fixed point 0 of the step $\mathsf a$: `n = 4^(k+1) z`, rule `f0 → 0f` = `aRule 0 0`) -/

/-- Stage `k` of the family $Z_H$: `n = 4^(k+1) z` (`z ≥ 1`). -/
def famZH (k n : ℕ) : Prop := ∃ z, 1 ≤ z ∧ n = 4 ^ (k + 1) * z

lemma four_pow_eq (k : ℕ) : 4 ^ (k + 1) = 2 ^ (2 * k + 2) := by
  rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]; norm_num

lemma famZH_step (k n : ℕ) (h : famZH (k + 1) n) :
    famZH k (Hmap^[1] n) ∧ ∀ i < 1, HDom (Hmap^[i] n) := by
  obtain ⟨z, hz, rfl⟩ := h
  set X := 4 ^ (k + 1) * z with hX
  have hX4 : 4 ≤ X := by
    have : 4 ≤ 4 ^ (k + 1) := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hX]; nlinarith
  have h4 : 4 ^ (k + 1 + 1) * z = 4 * X := by rw [hX, pow_succ]; ring
  rw [h4]
  refine ⟨⟨3 * z, by omega, ?_⟩, ?_⟩
  · show Hmap (4 * X) = _
    rw [u6_Hmap_A (by omega), show 4 * X / 4 = X by omega, hX]; ring
  · intro i hi
    interval_cases i
    show HDom (4 * X)
    exact ⟨by omega, Or.inl (by omega)⟩

lemma famZH_use (k n : ℕ) (h : famZH (k + 1) n) : k ≤ (canDerivH n).count (aRule 0 0) := by
  obtain ⟨z, hz, rfl⟩ := h
  set X := 2 ^ (2 * k + 2) * z with hX
  have hn : 4 ^ (k + 1 + 1) * z = 4 * X := by rw [pow_succ, four_pow_eq, hX]; ring
  rw [hn, count_aRule_A _ _ _ (by omega), show 4 * X / 4 = X by omega,
    ARule.tailBitsLSB_zeros (2 * k + 2) _ z hz hX]
  have := ARule.count_sweep_zeros (2 * k + 2) (tailBitsLSB z)
  omega

lemma famZH_ex (k : ℕ) : ∃ n, k ≤ n ∧ famZH k n ∧ lenT n ≤ 20 * k + 20 := by
  have h1 : k + 1 < 4 ^ (k + 1) := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ (2 * k + 2 + 1) = 2 * 4 ^ (k + 1) := by
    rw [four_pow_eq, pow_succ]; ring
  refine ⟨4 ^ (k + 1), by omega, ⟨1, le_rfl, by ring⟩, ?_⟩
  have := ARule.lenT_le_of_lt (n := 4 ^ (k + 1)) (L := 2 * k + 2) (by rw [h2]; omega)
  omega

/-- Quadratic use of `aRule 0 0` from the family $Z_H$. -/
theorem quadZH : Gen.QuadR Hmap HDom canDerivH (aRule 0 0) :=
  Gen.Quad.quad_of_familyG (s := 1) (a := 20) (b := 20) (R := famZH) le_rfl
    (fun k n h => (famZH_step k n h).1) (fun k n h => (famZH_step k n h).2) famZH_use famZH_ex

/-! ## Family $O_H$ (the fixed point $-1$ of the step $\mathsf b$: `n + 1 = 8^(k+1) (z + 1)`, rule `t2 → 2t` = `aRule 1 2`) -/

/-- Stage `k` of the family $O_H$: `n + 1 = 8^(k+1) (z + 1)` (`z ≥ 1`). -/
def famOH (k n : ℕ) : Prop := ∃ z, 1 ≤ z ∧ n + 1 = 8 ^ (k + 1) * (z + 1)

lemma eight_pow_eq (k : ℕ) : 8 ^ (k + 1) = 2 ^ (3 * k + 3) := by
  rw [show 3 * k + 3 = 3 * (k + 1) by ring, pow_mul]; norm_num

lemma famOH_X (k z : ℕ) (hz : 1 ≤ z) : 16 ≤ 8 ^ (k + 1) * (z + 1) := by
  have : 8 ≤ 8 ^ (k + 1) := by
    calc 8 = 8 ^ 1 := by norm_num
      _ ≤ 8 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

lemma famOH_step (k n : ℕ) (h : famOH (k + 1) n) :
    famOH k (Hmap^[1] n) ∧ ∀ i < 1, HDom (Hmap^[i] n) := by
  obtain ⟨z, hz, hn⟩ := h
  set X := 8 ^ (k + 1) * (z + 1) with hX
  have hX16 : 16 ≤ X := famOH_X k z hz
  have h2 : 8 ^ (k + 1 + 1) * (z + 1) = 8 * X := by rw [hX, pow_succ]; ring
  rw [h2] at hn
  refine ⟨⟨9 * z + 8, by omega, ?_⟩, ?_⟩
  · show Hmap n + 1 = _
    have : 8 ^ (k + 1) * (9 * z + 8 + 1) = 9 * X := by rw [hX]; ring
    rw [this, u6_Hmap_B (by omega)]; omega
  · intro i hi
    interval_cases i
    show HDom n
    exact ⟨by omega, Or.inr (by omega)⟩

lemma famOH_use (k n : ℕ) (h : famOH (k + 1) n) : k ≤ (canDerivH n).count (aRule 1 2) := by
  obtain ⟨z, hz, hn⟩ := h
  set X := 8 ^ (k + 1) * (z + 1) with hX
  have hX16 : 16 ≤ X := famOH_X k z hz
  have h2 : 8 ^ (k + 1 + 1) * (z + 1) = 8 * X := by rw [hX, pow_succ]; ring
  rw [h2] at hn
  have hm : (n - 7) / 8 + 1 = 2 ^ (3 * k + 3) * (z + 1) := by
    rw [← eight_pow_eq, ← hX]; omega
  rw [count_aRule_B _ _ _ (by omega), ARule.tailBitsLSB_ones (3 * k + 3) _ z hz hm]
  have := ARule.count_sweep_ones (3 * k + 3) (tailBitsLSB z)
  omega

lemma famOH_ex (k : ℕ) : ∃ n, k ≤ n ∧ famOH k n ∧ lenT n ≤ 20 * k + 20 := by
  have h1 : k + 1 < 8 ^ (k + 1) := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ (3 * k + 3 + 1) = 2 * 8 ^ (k + 1) := by
    rw [eight_pow_eq, pow_succ]; ring
  refine ⟨2 * 8 ^ (k + 1) - 1, by omega, ⟨1, le_rfl, by omega⟩, ?_⟩
  have := ARule.lenT_le_of_lt (n := 2 * 8 ^ (k + 1) - 1) (L := 3 * k + 3) (by rw [h2]; omega)
  omega

/-- Quadratic use of `aRule 1 2` from the family $O_H$. -/
theorem quadOH : Gen.QuadR Hmap HDom canDerivH (aRule 1 2) :=
  Gen.Quad.quad_of_familyG (s := 1) (a := 20) (b := 20) (R := famOH) le_rfl
    (fun k n h => (famOH_step k n h).1) (fun k n h => (famOH_step k n h).2) famOH_use famOH_ex

end ARuleH

end Collatz.Arctic.HTPDB
