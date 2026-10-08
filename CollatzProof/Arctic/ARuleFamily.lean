/-
Components of the formalization of Proposition 3.7 and Proposition 6.7 (iii) (quadratic use of the carry rules A): the frame of point families, and two families.

* **The family frame** (`quad_of_family`): for sets of points `R k` indexed by natural numbers, if a point of `R (k+1)` moves to a point of `R k` in `s` steps
  (with all intermediate points at least 2) and a point of `R (k+1)` uses the rule `ρ` at least `k` times, then the orbit segment of `s k` steps of a point of `R k` uses `ρ`
  at least `k(k-1)/2` times. If `R k` contains a point of length at most `12k + 12`, the number of uses exceeds any linear function of the length of the starting point.
* The families are taken near the 2-adic periodic points of `T` (Terras correspondence: if `n ≡ x₀ mod 2^K` then `T^i n ≡ T^i x₀ mod 2^(K-i)`).
  An averaging argument would move the top bits of the starting point uniformly; here we exhibit points whose low bits are periodic
  (the top bits do not affect the lower bound on the number of uses).
  - **Family Z** (`famZ`, periodic point 1): level `k` is `n = 1 + 4^(k+1) z` (`z ≥ 1`). A point of level `k+1` moves to level `k` in two steps, odd then even
    (`z ↦ 3z`). For a point of level `k+1`, `(n-1)/2 = 2^(2k+3) z` has `2k+3` zeros at the bottom, the carry drops 2, 1, 0,
    and `f0 → 0f` (`aRule 0 0`) is used at least `2k+1` times.
  - **Family O** (`famO`, periodic point -1): level `k` is `n + 1 = 2^(k+1) (z + 1)` (`z ≥ 1`). A point of level `k+1` moves to level `k`
    in one odd step (`z ↦ 3z + 2`). For a point of level `k+1`, `(n-1)/2` has `k+1` ones at the bottom, the carry stays 2, and `t2 → 2t`
    (`aRule 1 2`) is used at least `k+1` times.
  - Family F (periodic point 1/5) is in `ARuleFive.lean`.
-/
import CollatzProof.Arctic.ARuleCarry
import CollatzProof.Arctic.AutoStatement

namespace Collatz.Arctic.ARule

/-! ### Lemmas on orbits and numbers of uses -/

lemma T_odd {n : ℕ} (h : n % 2 = 1) : T n = (3 * n + 1) / 2 := by
  have hev : ¬ n % 2 = 0 := by omega
  unfold T; simp only [hev, ↓reduceIte]

lemma T_even {n : ℕ} (h : n % 2 = 0) : T n = n / 2 := by
  unfold T; simp only [h, ↓reduceIte]

lemma usesOrbit_add (ρ : Rule) : ∀ (a n b : ℕ),
    usesOrbit ρ n (a + b) = usesOrbit ρ n a + usesOrbit ρ (T^[a] n) b := by
  intro a
  induction a with
  | zero => intro n b; simp [usesOrbit_zero]
  | succ a ih =>
    intro n b
    rw [show a + 1 + b = (a + b) + 1 by omega, usesOrbit_succ, usesOrbit_succ, ih,
      Function.iterate_succ_apply]
    ring

lemma uses_le_usesOrbit (ρ : Rule) (n s : ℕ) (hs : 1 ≤ s) : uses ρ n ≤ usesOrbit ρ n s := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [usesOrbit_succ]; omega

lemma orbit_append {n a b : ℕ} (h1 : ∀ i < a, 2 ≤ T^[i] n) (h2 : ∀ i < b, 2 ≤ T^[i] (T^[a] n)) :
    ∀ i < a + b, 2 ≤ T^[i] n := by
  intro i hi
  by_cases hia : i < a
  · exact h1 i hia
  · have := h2 (i - a) (by omega)
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)] at this

/-- A form of `orbit_append` that takes the intermediate point as an equation (rewriting the iterate `T^[a]` with `rw` can unfold `T`
in definitional comparisons and not terminate, so the equation is passed as an explicit term). -/
lemma orbit_append' {n a b m : ℕ} (h1 : ∀ i < a, 2 ≤ T^[i] n) (he : T^[a] n = m)
    (h2 : ∀ i < b, 2 ≤ T^[i] m) : ∀ i < a + b, 2 ≤ T^[i] n :=
  orbit_append h1 (fun i hi => he ▸ h2 i hi)

lemma lenT_le_of_lt {n L : ℕ} (h : n < 2 ^ (L + 1)) : lenT n ≤ L := by
  unfold lenT binTail
  simp only [List.length_map, List.length_drop, List.length_reverse]
  have := (Nat.digits_length_le_iff (by norm_num : 1 < 2) n).mpr h
  omega

/-! ### The family frame -/

/-- Quadratic lower bound on a family: the `s k`-step segment of a point of `R k n` has all points at least 2 and uses `ρ` at least `k(k-1)/2` times. -/
theorem family_bound {ρ : Rule} {s : ℕ} {R : ℕ → ℕ → Prop} (hs : 1 ≤ s)
    (hstep : ∀ k n, R (k + 1) n → R k (T^[s] n))
    (horb : ∀ k n, R (k + 1) n → ∀ i < s, 2 ≤ T^[i] n)
    (huse : ∀ k n, R (k + 1) n → k ≤ uses ρ n) :
    ∀ k n, R k n → (∀ i < s * k, 2 ≤ T^[i] n) ∧ k * k ≤ 2 * usesOrbit ρ n (s * k) + k := by
  intro k
  induction k with
  | zero => intro n _; simp
  | succ k ih =>
    intro n hR
    obtain ⟨h1, h2⟩ := ih (T^[s] n) (hstep k n hR)
    rw [show s * (k + 1) = s + s * k by ring]
    refine ⟨orbit_append (horb k n hR) h1, ?_⟩
    rw [usesOrbit_add]
    have := huse k n hR
    have := uses_le_usesOrbit ρ n s hs
    nlinarith

/-- The family frame: if each level of the family contains a point of length at most `12k + 12`, then for starting points at least `N` there are orbit segments
on which the number of uses of `ρ` exceeds any linear function `C (lenT n + 1)` of the length of the starting point. -/
theorem quad_of_family {ρ : Rule} {s : ℕ} {R : ℕ → ℕ → Prop} (hs : 1 ≤ s)
    (hstep : ∀ k n, R (k + 1) n → R k (T^[s] n))
    (horb : ∀ k n, R (k + 1) n → ∀ i < s, 2 ≤ T^[i] n)
    (huse : ∀ k n, R (k + 1) n → k ≤ uses ρ n)
    (hex : ∀ k, ∃ n, k ≤ n ∧ R k n ∧ lenT n ≤ 12 * k + 12) (C N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ m, (∀ i < m, 2 ≤ T^[i] n) ∧ C * (lenT n + 1) < usesOrbit ρ n m := by
  obtain ⟨n, hkn, hR, hlen⟩ := hex (N + 26 * C + 30)
  obtain ⟨horb', huses⟩ := family_bound hs hstep horb huse _ n hR
  refine ⟨n, by omega, _, horb', ?_⟩
  set k := N + 26 * C + 30 with hk
  have h1 : C * (lenT n + 1) ≤ C * (12 * k + 13) := Nat.mul_le_mul_left _ (by omega)
  have h2 : (26 * C + 30) * k ≤ k * k := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-! ### Family Z (periodic point 1: `n ≡ 1 mod 4^(k+1)`, rule `f0 → 0f` = `aRule 0 0`) -/

/-- Level `k` of family Z: `n = 1 + 4^(k+1) z` (`z ≥ 1`). -/
def famZ (k n : ℕ) : Prop := ∃ z, 1 ≤ z ∧ n = 1 + 4 ^ (k + 1) * z

lemma famZ_step (k n : ℕ) (h : famZ (k + 1) n) : famZ k (T^[2] n) ∧ ∀ i < 2, 2 ≤ T^[i] n := by
  obtain ⟨z, hz, rfl⟩ := h
  set X := 4 ^ (k + 1) * z with hX
  have hX1 : 1 ≤ X := Nat.mul_pos (by positivity) hz
  have h4 : 4 ^ (k + 1 + 1) * z = 4 * X := by rw [hX, pow_succ]; ring
  rw [h4]
  have e1 : T (1 + 4 * X) = 2 + 6 * X := by rw [T_odd (by omega)]; omega
  have e2 : T (2 + 6 * X) = 1 + 3 * X := by rw [T_even (by omega)]; omega
  refine ⟨⟨3 * z, by omega, ?_⟩, ?_⟩
  · show T (T (1 + 4 * X)) = _
    rw [e1, e2, hX]; ring
  · intro i hi
    interval_cases i
    · show 2 ≤ 1 + 4 * X; omega
    · show 2 ≤ T (1 + 4 * X); omega

lemma famZ_use (k n : ℕ) (h : famZ (k + 1) n) : k ≤ uses (aRule 0 0) n := by
  obtain ⟨z, hz, rfl⟩ := h
  have hpow : 4 ^ (k + 1 + 1) = 2 ^ (2 * k + 3) * 2 := by
    rw [← pow_succ, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  set Y := 2 ^ (2 * k + 3) * z with hY
  have hn : 1 + 4 ^ (k + 1 + 1) * z = 1 + 2 * Y := by rw [hpow, hY]; ring
  have hy : (1 + 2 * Y - 1) / 2 = Y := by omega
  rw [hn, uses_aRule_odd _ _ _ (by omega), hy,
    tailBitsLSB_zeros (2 * k + 3) _ z hz hY,
    show 2 * k + 3 = (2 * k + 1) + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
  have : sweepRules (0 :: 0 :: (List.replicate (2 * k + 1) 0 ++ tailBitsLSB z)) 2 =
      aRule 0 2 :: aRule 0 1 :: sweepRules (List.replicate (2 * k + 1) 0 ++ tailBitsLSB z) 0 := rfl
  rw [List.cons_append, List.cons_append, this]
  have := count_sweep_zeros (2 * k + 1) (tailBitsLSB z)
  have := count_le_cons (aRule 0 0) (aRule 0 1)
    (sweepRules (List.replicate (2 * k + 1) 0 ++ tailBitsLSB z) 0)
  have := count_le_cons (aRule 0 0) (aRule 0 2)
    (aRule 0 1 :: sweepRules (List.replicate (2 * k + 1) 0 ++ tailBitsLSB z) 0)
  omega

lemma famZ_ex (k : ℕ) : ∃ n, k ≤ n ∧ famZ k n ∧ lenT n ≤ 12 * k + 12 := by
  have h1 : k + 1 < 4 ^ (k + 1) := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ (2 * k + 2 + 1) = 2 * 4 ^ (k + 1) := by
    rw [show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by ring, pow_succ, pow_mul]; norm_num; ring
  refine ⟨1 + 4 ^ (k + 1), by omega, ⟨1, le_rfl, by ring⟩, ?_⟩
  have := lenT_le_of_lt (n := 1 + 4 ^ (k + 1)) (L := 2 * k + 2) (by rw [h2]; omega)
  omega

theorem quadZ (C N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ m, (∀ i < m, 2 ≤ T^[i] n) ∧ C * (lenT n + 1) < usesOrbit (aRule 0 0) n m :=
  quad_of_family (s := 2) (R := famZ) (by norm_num) (fun k n h => (famZ_step k n h).1)
    (fun k n h => (famZ_step k n h).2) famZ_use famZ_ex C N

/-! ### Family O (periodic point -1: `n ≡ -1 mod 2^(k+2)`, rule `t2 → 2t` = `aRule 1 2`) -/

/-- Level `k` of family O: `n + 1 = 2^(k+1) (z + 1)` (`z ≥ 1`). -/
def famO (k n : ℕ) : Prop := ∃ z, 1 ≤ z ∧ n + 1 = 2 ^ (k + 1) * (z + 1)

lemma famO_X (k z : ℕ) (hz : 1 ≤ z) : 4 ≤ 2 ^ (k + 1) * (z + 1) := by
  have : 2 ≤ 2 ^ (k + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

lemma famO_step (k n : ℕ) (h : famO (k + 1) n) : famO k (T^[1] n) ∧ ∀ i < 1, 2 ≤ T^[i] n := by
  obtain ⟨z, hz, hn⟩ := h
  set X := 2 ^ (k + 1) * (z + 1) with hX
  have hX4 : 4 ≤ X := famO_X k z hz
  have h2 : 2 ^ (k + 1 + 1) * (z + 1) = 2 * X := by rw [hX, pow_succ]; ring
  rw [h2] at hn
  refine ⟨⟨3 * z + 2, by omega, ?_⟩, ?_⟩
  · show T n + 1 = _
    have : 2 ^ (k + 1) * (3 * z + 2 + 1) = 3 * X := by rw [hX]; ring
    rw [this, T_odd (by omega)]; omega
  · intro i hi
    interval_cases i
    show 2 ≤ n; omega

lemma famO_use (k n : ℕ) (h : famO (k + 1) n) : k ≤ uses (aRule 1 2) n := by
  obtain ⟨z, hz, hn⟩ := h
  set X := 2 ^ (k + 1) * (z + 1) with hX
  have hX4 : 4 ≤ X := famO_X k z hz
  have h2 : 2 ^ (k + 1 + 1) * (z + 1) = 2 * X := by rw [hX, pow_succ]; ring
  rw [h2] at hn
  rw [uses_aRule_odd _ _ _ (by omega), tailBitsLSB_ones (k + 1) _ z hz (by omega)]
  have := count_sweep_ones (k + 1) (tailBitsLSB z)
  omega

lemma famO_ex (k : ℕ) : ∃ n, k ≤ n ∧ famO k n ∧ lenT n ≤ 12 * k + 12 := by
  have h1 : k + 2 < 2 ^ (k + 2) := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := pow_succ 2 (k + 1)
  refine ⟨2 ^ (k + 2) - 1, ?_, ⟨1, le_rfl, ?_⟩, ?_⟩
  · omega
  · omega
  · have := lenT_le_of_lt (n := 2 ^ (k + 2) - 1) (L := k + 1)
      (by rw [show k + 1 + 1 = k + 2 by ring]; omega)
    omega

theorem quadO (C N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ m, (∀ i < m, 2 ≤ T^[i] n) ∧ C * (lenT n + 1) < usesOrbit (aRule 1 2) n m :=
  quad_of_family (s := 1) (R := famO) le_rfl (fun k n h => (famO_step k n h).1)
    (fun k n h => (famO_step k n h).2) famO_use famO_ex C N

end Collatz.Arctic.ARule
