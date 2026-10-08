/-
Lemma 6.4 (digits of the end point), in counting form.

Setting: `Q` odd, `z ≥ 0`. `t = T0·2^(n-K) + 2^w·u + ρ` with `T0`, `ρ` fixed and `u` ranging over `[0, 2^(n-K-w))`.
`y := z + Q t`, `h := ⌊y / 2^n⌋`, `ϖ := y mod 2^n`.

* (i) `mid_bits_bijOn`, `mid_bits_card`: the part of `ϖ` in the bit positions `[w, n-K)`, `⌊(y mod 2^(n-K)) / 2^w⌋`, is,
  as a function of `u`, a bijection of `[0, 2^(n-K-w))` (exactly uniform: each value is taken by exactly one `u`).
  The only hypotheses are that `Q` is odd and `K + w ≤ n` (conditions such as `T0 ∈ [2^(K-1), 2^K)`, `ρ < 2^w`, `2^w Q < 2^n` are not needed).
* (ii) `end_digits_tv_sharp`, `end_digits_tv`: the sum of absolute differences between the law of `h mod 2^b` (over `u`) and the uniform distribution on `[0, 2^b)`
  (twice the total variation distance) is bounded by counting. Instead of `b := ⌊log₂(Q 2^(-K))⌋ - Δ` we assume `2^(b+Δ+K) ≤ Q`
  (that `b` satisfies it; `end_digits_tv_log` is the form with that `b`). The conclusion is
  `∑_j |cnt_j / N - 1/2^b| ≤ 3/2^Δ + 2^(w+2) Q / 2^n` (`end_digits_tv_sharp`), which is at most twice the total variation bound
  `2^(1-Δ) + 2^(w+1) Q 2^(-n) + 2^(K+2)/Q` (`end_digits_tv`). The third term `2^(K+2)/Q` is not needed.
  The only hypotheses are `K + w ≤ n` and `2^(b+Δ+K) ≤ Q` (oddness of `Q`, `T0`, `ρ`, `2^w Q < 2^n` are not needed).

Outline of the proof of (ii): `y(u) = A + D u` (`D = 2^w Q`). The fiber of a value `m` of `h` has at most `⌊2^n/D⌋ + 1` points, and for `m` other than the two extremes
at least `⌊2^n/D⌋` points (`ap_fiber_le`, `ap_fiber_ge`). The number of elements of residue `j` in an interval of length `Λ` is `Λ/M ± 1`
(`card_filter_mod_Ico_bounds`). From these two, the weight of each residue class is within `3⌊2^n/D⌋ + Λ/M + 1` of the average
(`residue_dev`, general form). Substituting `Λ ≤ N D / 2^n + 2` and simplifying gives the constants.
The general lemmas (`ap_fiber_le`, `ap_fiber_ge`, `card_filter_mod_Ico_bounds`, `residue_dev`, `ap_floor_mod_dev`) are in
`CollatzProof/Arctic/EndDigitsCount.lean`.
-/
import CollatzProof.Arctic.EndDigitsCount

namespace Collatz.Arctic

open Finset

namespace EndDigits

/-! ### (i) Bijection of the middle bits -/

/-- Extracting digits: the part at positions `w` and above of `(a + 2^w b) mod 2^(w+r)` is `(⌊a/2^w⌋ + b) mod 2^r`. -/
lemma mod_pow_div_pow (a b w r : ℕ) :
    (a + 2 ^ w * b) % 2 ^ (w + r) / 2 ^ w = (a / 2 ^ w + b) % 2 ^ r := by
  rw [pow_add, Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ (by positivity)]

/-- A linear function with odd slope is a bijection of residues modulo `2^r`. -/
lemma affine_mod_bijOn (c Q r : ℕ) (hQ : Q % 2 = 1) :
    Set.BijOn (fun u => (c + Q * u) % 2 ^ r) ↑(range (2 ^ r)) ↑(range (2 ^ r)) := by
  have hmaps : Set.MapsTo (fun u => (c + Q * u) % 2 ^ r) ↑(range (2 ^ r)) ↑(range (2 ^ r)) := by
    intro u _
    simp only [coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ (by positivity)
  refine ((Finset.finite_toSet _).injOn_iff_bijOn_of_mapsTo hmaps).1 ?_
  intro u1 hu1 u2 hu2 h
  simp only [coe_range, Set.mem_Iio] at hu1 hu2
  have hcop : Nat.Coprime (2 ^ r) Q :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 (Nat.odd_iff.2 hQ))
  have h1 : Q * u1 ≡ Q * u2 [MOD 2 ^ r] := Nat.ModEq.add_left_cancel' c h
  exact (Nat.ModEq.cancel_left_of_coprime hcop h1).eq_of_lt_of_lt hu1 hu2

/-- **Lemma 6.4 (i)**: the part of `ϖ` in the bit positions `[w, n-K)` is a bijection of `u ∈ [0, 2^(n-K-w))`. -/
theorem mid_bits_bijOn (Q z T0 ρ n K w : ℕ) (hQ : Q % 2 = 1) (hKw : K + w ≤ n) :
    Set.BijOn (fun u => (z + Q * (T0 * 2 ^ (n - K) + 2 ^ w * u + ρ)) % 2 ^ (n - K) / 2 ^ w)
      ↑(range (2 ^ (n - K - w))) ↑(range (2 ^ (n - K - w))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hKw
  have e2 : K + w + r - K - w = r := by omega
  have e1 : K + w + r - K = w + r := by omega
  rw [e2, e1]
  have key : ∀ u, (z + Q * (T0 * 2 ^ (w + r) + 2 ^ w * u + ρ)) % 2 ^ (w + r) / 2 ^ w
      = ((z + Q * ρ) / 2 ^ w + Q * u) % 2 ^ r := by
    intro u
    rw [← mod_pow_div_pow]
    have : z + Q * (T0 * 2 ^ (w + r) + 2 ^ w * u + ρ)
        = (z + Q * ρ + 2 ^ w * (Q * u)) + 2 ^ (w + r) * (Q * T0) := by ring
    rw [this, Nat.add_mul_mod_self_left]
  simp only [key]
  exact affine_mod_bijOn _ Q r hQ

/-- **Lemma 6.4 (i), counting form**: each value `v < 2^(n-K-w)` is taken by exactly one `u`. -/
theorem mid_bits_card (Q z T0 ρ n K w : ℕ) (hQ : Q % 2 = 1) (hKw : K + w ≤ n)
    (v : ℕ) (hv : v < 2 ^ (n - K - w)) :
    #{u ∈ range (2 ^ (n - K - w)) |
        (z + Q * (T0 * 2 ^ (n - K) + 2 ^ w * u + ρ)) % 2 ^ (n - K) / 2 ^ w = v} = 1 := by
  have hb := mid_bits_bijOn Q z T0 ρ n K w hQ hKw
  obtain ⟨u0, hu0, hfu0⟩ := hb.surjOn (by simpa using hv)
  rw [Finset.card_eq_one]
  refine ⟨u0, ?_⟩
  ext u
  simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hu, hfu⟩
    exact hb.injOn (by simpa using hu) hu0 (by simp only at hfu0 ⊢; rw [hfu, hfu0])
  · rintro rfl
    exact ⟨by simpa using hu0, hfu0⟩

/-! ### (ii) Specialization to the setting of Lemma 6.4 -/

/-- **Lemma 6.4 (ii), sharp form**: with `N := 2^(n-K-w)` and `cnt_j := #{u < N : ⌊y(u)/2^n⌋ mod 2^b = j}`,
`∑_j |cnt_j / N - 1/2^b| ≤ 3/2^Δ + 2^(w+2) Q / 2^n` (the left side is twice the total variation distance).
The only hypotheses are `K + w ≤ n` and `2^(b+Δ+K) ≤ Q` (satisfied by `b = ⌊log₂(Q 2^(-K))⌋ - Δ`). -/
theorem end_digits_tv_sharp (Q z T0 ρ n K w b Δ : ℕ) (hKw : K + w ≤ n)
    (hb : 2 ^ (b + Δ + K) ≤ Q) :
    ∑ j ∈ range (2 ^ b),
      |(#{u ∈ range (2 ^ (n - K - w)) |
          (z + Q * (T0 * 2 ^ (n - K) + 2 ^ w * u + ρ)) / 2 ^ n % 2 ^ b = j} : ℚ)
          / 2 ^ (n - K - w) - 1 / 2 ^ b|
      ≤ 3 / 2 ^ Δ + 2 ^ (w + 2) * Q / 2 ^ n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hKw
  have e2 : K + w + r - K - w = r := by omega
  have e1 : K + w + r - K = w + r := by omega
  rw [e2, e1]
  have key : ∀ u, z + Q * (T0 * 2 ^ (w + r) + 2 ^ w * u + ρ)
      = (z + Q * (T0 * 2 ^ (w + r) + ρ)) + 2 ^ w * Q * u := by intro u; ring
  simp only [key]
  have hQ1 : 1 ≤ Q := le_trans Nat.one_le_two_pow hb
  have h := ap_floor_mod_dev (z + Q * (T0 * 2 ^ (w + r) + ρ)) (2 ^ w * Q) (2 ^ (K + w + r))
    (2 ^ r) (2 ^ b) (by positivity) (by positivity) (by positivity) (by positivity)
  push_cast at h
  have hbq : (2 : ℚ) ^ b * 2 ^ Δ * 2 ^ K ≤ Q := by
    rw [← pow_add, ← pow_add]; exact_mod_cast hb
  have hQ : (0 : ℚ) < Q := by exact_mod_cast hQ1
  have hX : (1 : ℚ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hY : (1 : ℚ) ≤ 2 ^ Δ := one_le_pow₀ (by norm_num)
  have hZ : (1 : ℚ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hR : (0 : ℚ) < 2 ^ r := by positivity
  calc _ ≤ _ := h
    _ = 3 * 2 ^ b * 2 ^ K / Q + Q / (2 ^ K * 2 ^ r) + 2 / 2 ^ r + 2 ^ b / 2 ^ r := by
        rw [pow_add, pow_add]
        field_simp
    _ ≤ 3 / 2 ^ Δ + 4 * Q / (2 ^ K * 2 ^ r) := by
        have p1 : 3 * (2 : ℚ) ^ b * 2 ^ K / Q ≤ 3 / 2 ^ Δ := by
          rw [div_le_div_iff₀ hQ (by positivity)]
          nlinarith
        have p2 : 2 / (2 : ℚ) ^ r ≤ 2 * Q / (2 ^ K * 2 ^ r) := by
          rw [div_le_div_iff₀ hR (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right hX (by positivity : (0 : ℚ) ≤ 2 ^ Δ * 2 ^ K),
            mul_le_mul_of_nonneg_right hY (by positivity : (0 : ℚ) ≤ 2 ^ K)]
        have p3 : (2 : ℚ) ^ b / 2 ^ r ≤ Q / (2 ^ K * 2 ^ r) := by
          rw [div_le_div_iff₀ hR (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℚ) ≤ 2 ^ b * 2 ^ K)]
        have e : 4 * (Q : ℚ) / (2 ^ K * 2 ^ r) = Q / (2 ^ K * 2 ^ r) + 2 * Q / (2 ^ K * 2 ^ r)
            + Q / (2 ^ K * 2 ^ r) := by ring
        linarith
    _ = 3 / 2 ^ Δ + 2 ^ (w + 2) * Q / 2 ^ (K + w + r) := by
        rw [pow_add, pow_add, pow_add]
        field_simp
        ring

/-- **Lemma 6.4 (ii), form with three terms**: the total variation distance `(1/2) ∑_j |cnt_j / N - 1/2^b|` is
at most `2^(1-Δ) + 2^(w+1) Q 2^(-n) + 2^(K+2)/Q` (writing `2^(1-Δ)` as `2 / 2^Δ`). -/
theorem end_digits_tv (Q z T0 ρ n K w b Δ : ℕ) (hKw : K + w ≤ n)
    (hb : 2 ^ (b + Δ + K) ≤ Q) :
    ∑ j ∈ range (2 ^ b),
      |(#{u ∈ range (2 ^ (n - K - w)) |
          (z + Q * (T0 * 2 ^ (n - K) + 2 ^ w * u + ρ)) / 2 ^ n % 2 ^ b = j} : ℚ)
          / 2 ^ (n - K - w) - 1 / 2 ^ b|
      ≤ 2 * (2 / 2 ^ Δ + 2 ^ (w + 1) * Q / 2 ^ n + 2 ^ (K + 2) / Q) := by
  refine (end_digits_tv_sharp Q z T0 ρ n K w b Δ hKw hb).trans ?_
  have h1 : (3 : ℚ) / 2 ^ Δ ≤ 4 / 2 ^ Δ := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have h2 : (0 : ℚ) ≤ 2 ^ (K + 2) / Q := by positivity
  have h3 : (2 : ℚ) ^ (w + 2) * Q / 2 ^ n = 2 * (2 ^ (w + 1) * Q / 2 ^ n) := by ring
  have h4 : (4 : ℚ) / 2 ^ Δ = 2 * (2 / 2 ^ Δ) := by ring
  linarith

/-- **Lemma 6.4 (ii), form with explicit `b`**: `b := ⌊log₂ ⌊Q/2^K⌋⌋ - Δ` (`= ⌊log₂(Q 2^(-K))⌋ - Δ` if `Q ≥ 2^K`),
when `Δ ≤ ⌊log₂ ⌊Q/2^K⌋⌋` (that is, `b ≥ 0`). If `Q < 2^K` then `b = Δ = 0` and the left side is 0. -/
theorem end_digits_tv_log (Q z T0 ρ n K w Δ : ℕ) (hKw : K + w ≤ n)
    (hΔ : Δ ≤ Nat.log 2 (Q / 2 ^ K)) :
    ∑ j ∈ range (2 ^ (Nat.log 2 (Q / 2 ^ K) - Δ)),
      |(#{u ∈ range (2 ^ (n - K - w)) |
          (z + Q * (T0 * 2 ^ (n - K) + 2 ^ w * u + ρ)) / 2 ^ n % 2 ^ (Nat.log 2 (Q / 2 ^ K) - Δ)
            = j} : ℚ) / 2 ^ (n - K - w) - 1 / 2 ^ (Nat.log 2 (Q / 2 ^ K) - Δ)|
      ≤ 2 * (2 / 2 ^ Δ + 2 ^ (w + 1) * Q / 2 ^ n + 2 ^ (K + 2) / Q) := by
  rcases Nat.eq_zero_or_pos (Q / 2 ^ K) with h0 | hpos
  · -- Q < 2^K: b = 0, and residues modulo 1 are trivial
    rw [h0, Nat.log_zero_right] at hΔ ⊢
    simp only [Nat.zero_sub, pow_zero, Nat.mod_one, range_one, sum_singleton, filter_true,
      card_range, div_one]
    push_cast
    rw [div_self (by positivity), sub_self, abs_zero]
    positivity
  · refine end_digits_tv Q z T0 ρ n K w _ Δ hKw ?_
    have h1 := Nat.pow_log_le_self 2 hpos.ne'
    have h2 := Nat.div_mul_le_self Q (2 ^ K)
    rw [Nat.sub_add_cancel hΔ, pow_add]
    exact le_trans (Nat.mul_le_mul_right _ h1) h2

end EndDigits

end Collatz.Arctic
