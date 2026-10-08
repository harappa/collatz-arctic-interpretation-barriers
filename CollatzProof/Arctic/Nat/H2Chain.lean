/-
# Lemmas 11.5 and 11.6: backward chains, splitting into three parts, and the invariant of `δ`

Lemma 11.5 (division of periodic intervals and backward chains) and the arithmetic of Lemma 11.6 (pumping by the word itself).
Independent of interpretations (only `Collatz.Arctic.T`).
(Section 11.2.)

* **Lemma 11.5 (i)** (§1, `div_split`): if `N = U 2^{h+ℓ} + Θ 2^h + V ≡ c (mod q)` (`c < q`), then
  `N = q (⌊U/q⌋ 2^{h+ℓ} + ⌊(Θ + 2^ℓ (U mod q))/q⌋ 2^h + X) + c` with `X < 2^h`.
* **One step** (§2, `back_step`): for `y` not divisible by 3, with `j ≤ 3` and `n = (2^{j+1} y - 1)/3` (an odd number not divisible by 3),
  `T^{j+1}(n) = y`.
* **Lemma 11.5 (ii)** (§3, the main theorem `back_chain`): if `U ≥ 3^A`, the starting point of a chain of `A` steps is
  `n = ⌊U/3^A⌋ 2^{h+M+ℓ} + Θ' 2^{h+M} + V'` with `Θ' = ⌊(Θ + 2^ℓ (U mod 3^A))/3^A⌋`, `M ≤ 4A`, `T^M(n) = y`, and
  the intermediate points are at least 2. **The real form `Θ_A = ⌊2^ℓ θ_A⌋` of an earlier argument is replaced by the integer expression `Θ'`** (`δ_k ∈ [0, 1]` is the same as the remainder `R_k ≤ 3^k - 1`;
  `delta_inv` is the real form).
* **The floor** (§4, `floor_shift`): the floor of `R X + a` (`a ≤ R`) divided by `3^A R` is `⌊X/3^A⌋` (if the division is not exact).
* **Pumping** (§5, Lemma 11.6): the periodic word `wpow w k`, `X_k = 2^{Lk} X_0` (`valW_wpow`), `v_3(ν) = v_3(X_0)` (`nu_core`), and
  the reduction to lowest terms (`reduced_frac`).
* **Assembly** (§6, the main theorem `back_chain_word`): the word of the starting point of the chain of `y_m = val(1 p w^k w^m s)` is
  `bin'(⌊U/3^A⌋) ++ dig N D 0 (Lm) ++ bitsF (|s| + M) V'`. `N/D` (in lowest terms, the power of 3 in the denominator is `α ≥ A - v_3(X_0)`, and the part prime to 3
  divides `2^L - 1`) does not depend on `m`. This is the form used by Theorem 11.8.

Auxiliary declarations are in the namespace `Collatz.Arctic.NatQ5.W2a`, the main theorems in `Collatz.Arctic.NatQ5`.
`sorry`, `axiom` and `native_decide` are not used.
-/
import CollatzProof.Arctic.Nat.H2Bin

namespace Collatz.Arctic.NatQ5.W2a

open Collatz.Arctic Collatz.Arctic.NatQ5

/-! ## §1 Lemma 11.5 (i) (dividing a periodic interval by `q`) -/

/-- **Lemma 11.5 (i)**: if `N := U 2^{h+ℓ} + Θ 2^h + V` (`Θ < 2^ℓ`, `V < 2^h`) has `N mod q = c` (`c < q`), then
`N = q (⌊U/q⌋ 2^{h+ℓ} + Q 2^h + X) + c` with `Q = ⌊(Θ + 2^ℓ (U mod q))/q⌋ < 2^ℓ` and `X < 2^h`. -/
theorem div_split (q c U Θ V h ℓ : ℕ) (hq : 0 < q) (_hc : c < q) (hΘ : Θ < 2 ^ ℓ) (hV : V < 2 ^ h)
    (hN : (U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V) % q = c) :
    ∃ X < 2 ^ h, U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V =
        q * (U / q * 2 ^ (h + ℓ) + (Θ + 2 ^ ℓ * (U % q)) / q * 2 ^ h + X) + c ∧
      (Θ + 2 ^ ℓ * (U % q)) / q < 2 ^ ℓ := by
  rw [pow_add] at hN ⊢
  set A := 2 ^ h with hA
  set B := 2 ^ ℓ with hB
  have hApos : 0 < A := by positivity
  set ε := U % q with hε
  set U' := U / q with hU'
  have hUdec : q * U' + ε = U := Nat.div_add_mod U q
  have hεq : ε < q := Nat.mod_lt _ hq
  set Mm := Θ + B * ε with hMm
  set Qq := Mm / q with hQq
  set r' := Mm % q with hr'
  have hMdec : q * Qq + r' = Mm := Nat.div_add_mod Mm q
  have hr'q : r' < q := Nat.mod_lt _ hq
  set Z := r' * A + V with hZ
  have hN1 : U * (A * B) + Θ * A + V = q * (U' * (A * B) + Qq * A) + Z := by
    have e1 : U * (A * B) + Θ * A + V = q * U' * (A * B) + Mm * A + V := by
      rw [← hUdec, hMm]; ring
    rw [e1, ← hMdec, hZ]; ring
  have hZc : Z % q = c := by
    rw [hN1, Nat.mul_add_mod] at hN; exact hN
  have hZdec : q * (Z / q) + c = Z := by rw [← hZc]; exact Nat.div_add_mod Z q
  have hZlt : Z < q * A := by
    have : (r' + 1) * A ≤ q * A := Nat.mul_le_mul_right _ (by omega)
    rw [hZ]; nlinarith
  refine ⟨Z / q, ?_, ?_, ?_⟩
  · by_contra hge
    push Not at hge
    have : q * A ≤ q * (Z / q) := Nat.mul_le_mul_left _ hge
    omega
  · rw [hN1]; nth_rw 1 [← hZdec]; ring
  · rw [hQq, Nat.div_lt_iff_lt_mul hq, hMm]
    have : B * ε + B ≤ B * q := by
      have := Nat.mul_le_mul_left B (show ε + 1 ≤ q by omega); linarith
    omega

/-! ## §2 One step -/

theorem T_two_mul (x : ℕ) : Collatz.Arctic.T (2 * x) = x := by
  unfold Collatz.Arctic.T; split_ifs with h <;> omega

/-- `T^i(2^{i+k} y) = 2^k y` (even steps). -/
theorem T_iterate_two_pow (i k y : ℕ) : Collatz.Arctic.T^[i] (2 ^ (i + k) * y) = 2 ^ k * y := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    have : 2 ^ (i + 1 + k) * y = 2 * (2 ^ (i + k) * y) := by rw [show i + 1 + k = (i + k) + 1 by ring, pow_succ]; ring
    rw [this, T_two_mul, ih]

theorem T_of_odd' {n : ℕ} (h : n % 2 = 1) : Collatz.Arctic.T n = (3 * n + 1) / 2 := by
  unfold Collatz.Arctic.T; simp [h]

/-- **One step** (the single step of Lemma 11.5 (ii)): if `y = U 2^{h+ℓ} + Θ 2^h + V` is not divisible by 3 and `U ≥ 3`, then with `j ≤ 3` and
`n = ⌊U/3⌋ 2^{h+j+1+ℓ} + ⌊(Θ + 2^ℓ (U mod 3))/3⌋ 2^{h+j+1} + V'`, `n` is an odd number not divisible by 3,
`3n + 1 = 2^{j+1} y`, `T^{j+1}(n) = y`, and the intermediate points are at least 2. -/
theorem back_step (U Θ V h ℓ : ℕ) (hU : 3 ≤ U) (hΘ : Θ < 2 ^ ℓ) (hV : V < 2 ^ h)
    (hy : ¬ 3 ∣ U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V) :
    ∃ j n V' : ℕ, j ≤ 3 ∧
      n = U / 3 * 2 ^ (h + (j + 1) + ℓ) + (Θ + 2 ^ ℓ * (U % 3)) / 3 * 2 ^ (h + (j + 1)) + V' ∧
      (Θ + 2 ^ ℓ * (U % 3)) / 3 < 2 ^ ℓ ∧ V' < 2 ^ (h + (j + 1)) ∧ ¬ 3 ∣ n ∧
      3 * n + 1 = 2 ^ (j + 1) * (U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V) ∧
      Collatz.Arctic.T^[j + 1] n = U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V ∧
      ∀ i < j + 1, 2 ≤ Collatz.Arctic.T^[i] n := by
  set y := U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V with hydef
  -- `j ≤ 3` with `2^{j+1} y ≡ 4, 7 (mod 9)` (by cases on `y mod 9`)
  have hj : ∃ j ≤ 3, (2 ^ (j + 1) * y) % 9 = 4 ∨ (2 ^ (j + 1) * y) % 9 = 7 := by
    have : y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 7 ∨ y % 9 = 8 := by omega
    rcases this with h9 | h9 | h9 | h9 | h9 | h9
    · exact ⟨1, by norm_num, by norm_num; omega⟩
    · exact ⟨0, by norm_num, by norm_num; omega⟩
    · exact ⟨1, by norm_num, by norm_num; omega⟩
    · exact ⟨2, by norm_num, by norm_num; omega⟩
    · exact ⟨3, by norm_num, by norm_num; omega⟩
    · exact ⟨0, by norm_num, by norm_num; omega⟩
  obtain ⟨j, hj3, hj9⟩ := hj
  set h' := h + (j + 1) with hh'
  have hx : 2 ^ (j + 1) * y = U * 2 ^ (h' + ℓ) + Θ * 2 ^ h' + 2 ^ (j + 1) * V := by
    rw [hydef, hh', show h + (j + 1) + ℓ = (h + ℓ) + (j + 1) by ring, pow_add, pow_add, pow_add]; ring
  have hV' : 2 ^ (j + 1) * V < 2 ^ h' := by
    rw [hh', pow_add 2 h (j + 1), mul_comm (2 ^ h)]; exact Nat.mul_lt_mul_of_pos_left hV (by positivity)
  have hmod : (U * 2 ^ (h' + ℓ) + Θ * 2 ^ h' + 2 ^ (j + 1) * V) % 3 = 1 := by
    rw [← hx]; omega
  obtain ⟨X, hX, hsplit, hQ⟩ := div_split 3 1 U Θ (2 ^ (j + 1) * V) h' ℓ (by norm_num) (by norm_num) hΘ hV' hmod
  set n := U / 3 * 2 ^ (h' + ℓ) + (Θ + 2 ^ ℓ * (U % 3)) / 3 * 2 ^ h' + X with hn
  have h3n : 3 * n + 1 = 2 ^ (j + 1) * y := by rw [hx, hsplit]
  have hn3 : ¬ 3 ∣ n := by omega
  have hnodd : n % 2 = 1 := by
    have : 2 ^ (j + 1) * y = 2 * (2 ^ j * y) := by rw [pow_succ]; ring
    omega
  have hTn : Collatz.Arctic.T n = 2 ^ j * y := by
    rw [T_of_odd' hnodd, h3n, pow_succ]
    rw [show 2 ^ j * 2 * y = 2 * (2 ^ j * y) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  have hy0 : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · exact absurd (h0 ▸ dvd_zero 3) hy
    · exact h0
  refine ⟨j, n, X, hj3, rfl, hQ, hX, hn3, h3n, ?_, ?_⟩
  · rw [Function.iterate_succ_apply, hTn]
    have := T_iterate_two_pow j 0 y
    simpa using this
  · intro i hi
    rcases i with _ | i
    · simp only [Function.iterate_zero, id]
      have h1 : 1 ≤ U / 3 := by omega
      have h2 : 2 ≤ 2 ^ (h' + ℓ) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (h' + ℓ) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ≤ U / 3 * 2 ^ (h' + ℓ) := by nlinarith
      omega
    · rw [Function.iterate_succ_apply, hTn]
      have hij : i + (j - i) = j := by omega
      rw [← hij, T_iterate_two_pow]
      have : 2 ≤ 2 ^ (j - i) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith

/-- The core identity of the induction along the chain: `⌊(⌊(Θ + 2^ℓ (U mod 3))/3⌋ + 2^ℓ (⌊U/3⌋ mod 3^A))/3^A⌋ = ⌊(Θ + 2^ℓ (U mod 3^{A+1}))/3^{A+1}⌋`. -/
theorem theta_step (Θ ℓ U A : ℕ) :
    ((Θ + 2 ^ ℓ * (U % 3)) / 3 + 2 ^ ℓ * (U / 3 % 3 ^ A)) / 3 ^ A =
      (Θ + 2 ^ ℓ * (U % 3 ^ (A + 1))) / 3 ^ (A + 1) := by
  have hmod : U % 3 ^ (A + 1) = U % 3 + 3 * (U / 3 % 3 ^ A) := by
    rw [pow_succ', Nat.mod_mul]
  rw [hmod, pow_succ', ← Nat.div_div_eq_div_mul]
  congr 1
  have : Θ + 2 ^ ℓ * (U % 3 + 3 * (U / 3 % 3 ^ A)) = (Θ + 2 ^ ℓ * (U % 3)) + 3 * (2 ^ ℓ * (U / 3 % 3 ^ A)) := by
    ring
  rw [this, Nat.add_mul_div_left _ _ (by norm_num)]

end Collatz.Arctic.NatQ5.W2a

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic W2a

/-! ## §3 Lemma 11.5 (ii) (backward chains) -/

/-- **Backward chains** (Lemma 11.5 (ii)): if `y = U 2^{h+ℓ} + Θ 2^h + V` (`U ≥ 3^A`,
`Θ < 2^ℓ`, `V < 2^h`) is not divisible by 3, then there are `M ≤ 4A` and `n` not divisible by 3 with
`n = ⌊U/3^A⌋ 2^{h+M+ℓ} + Θ' 2^{h+M} + V'`, `Θ' := ⌊(Θ + 2^ℓ (U mod 3^A))/3^A⌋ < 2^ℓ`, `V' < 2^{h+M}`,
`T^M(n) = y` and `T^i(n) ≥ 2` (`i < M`). The quantity `h_A = h + Σ(j_k + 1)` of an earlier argument is `h + M`. -/
theorem back_chain (A : ℕ) : ∀ (U Θ V h ℓ : ℕ), 3 ^ A ≤ U → Θ < 2 ^ ℓ → V < 2 ^ h →
    ¬ 3 ∣ U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V →
    ∃ n M V' : ℕ, M ≤ 4 * A ∧
      n = U / 3 ^ A * 2 ^ (h + M + ℓ) + (Θ + 2 ^ ℓ * (U % 3 ^ A)) / 3 ^ A * 2 ^ (h + M) + V' ∧
      (Θ + 2 ^ ℓ * (U % 3 ^ A)) / 3 ^ A < 2 ^ ℓ ∧ V' < 2 ^ (h + M) ∧ ¬ 3 ∣ n ∧
      Collatz.Arctic.T^[M] n = U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V ∧
      ∀ i < M, 2 ≤ Collatz.Arctic.T^[i] n := by
  induction A with
  | zero =>
    intro U Θ V h ℓ _ hΘ hV hy
    refine ⟨U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V, 0, V, le_rfl, ?_, ?_, hV, hy, rfl, fun i hi => absurd hi (by omega)⟩
    · simp [Nat.mod_one]
    · simpa [Nat.mod_one] using hΘ
  | succ A ih =>
    intro U Θ V h ℓ hU hΘ hV hy
    have hU3 : 3 ≤ U := le_trans (by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ (A + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) hU
    obtain ⟨j, n₁, V₁, hj3, hn₁, hΘ₁, hV₁, hn₁3, _, hT₁, hmid₁⟩ := back_step U Θ V h ℓ hU3 hΘ hV hy
    have hU' : 3 ^ A ≤ U / 3 := by
      rw [Nat.le_div_iff_mul_le (by norm_num), ← pow_succ]; exact hU
    obtain ⟨n, M', V', hM', hn, hΘ', hV', hn3, hT, hmid⟩ :=
      ih (U / 3) ((Θ + 2 ^ ℓ * (U % 3)) / 3) V₁ (h + (j + 1)) ℓ hU' hΘ₁ hV₁ (hn₁ ▸ hn₁3)
    have hdiv : U / 3 / 3 ^ A = U / 3 ^ (A + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
    have hθ := theta_step Θ ℓ U A
    have hhM : h + (j + 1) + M' = h + ((j + 1) + M') := by ring
    refine ⟨n, (j + 1) + M', V', by omega, ?_, ?_, ?_, hn3, ?_, ?_⟩
    · rw [hn, hdiv, hθ, hhM]
    · rw [← hθ]; exact hΘ'
    · rw [← hhM]; exact hV'
    · rw [Function.iterate_add_apply, hT, ← hn₁]; exact hT₁
    · intro i hi
      by_cases hiM : i < M'
      · exact hmid i hiM
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + M' := ⟨i - M', by omega⟩
        rw [Function.iterate_add_apply, hT, ← hn₁]
        exact hmid₁ i' (by omega)

end Collatz.Arctic.NatQ5

namespace Collatz.Arctic.NatQ5.W2a

open Collatz.Arctic Collatz.Arctic.NatQ5

/-! ## §4 The invariant of `δ` and moving the floor -/

/-- **The invariant of `δ`** (the real form): if `δ ∈ [0, 1]`, then `(Θ + δ + 2^ℓ E)/3^A = Θ' + δ'` with
`Θ' = ⌊(Θ + 2^ℓ E)/3^A⌋` and `δ' ∈ [0, 1]` (`δ' < 1` if `δ < 1`). A restatement of the fact that `Θ'` of `back_chain` is the real `Θ_A` of an earlier argument. -/
theorem delta_inv (A ℓ Θ E : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    ∃ δ' : ℝ, 0 ≤ δ' ∧ δ' ≤ 1 ∧ (δ < 1 → δ' < 1) ∧
      ((Θ : ℝ) + δ + 2 ^ ℓ * E) / 3 ^ A = (((Θ + 2 ^ ℓ * E) / 3 ^ A : ℕ) : ℝ) + δ' := by
  set X := Θ + 2 ^ ℓ * E with hX
  have hpos : (0 : ℝ) < 3 ^ A := by positivity
  have hdec : 3 ^ A * (X / 3 ^ A) + X % 3 ^ A = X := Nat.div_add_mod X (3 ^ A)
  have hR : X % 3 ^ A < 3 ^ A := Nat.mod_lt _ (by positivity)
  have hR' : ((X % 3 ^ A : ℕ) : ℝ) + 1 ≤ 3 ^ A := by
    have : X % 3 ^ A + 1 ≤ 3 ^ A := hR
    exact_mod_cast this
  refine ⟨(((X % 3 ^ A : ℕ) : ℝ) + δ) / 3 ^ A, by positivity, ?_, ?_, ?_⟩
  · rw [div_le_one hpos]; linarith
  · intro hδ
    rw [div_lt_one hpos]; linarith
  · have hXr : ((X : ℕ) : ℝ) = 3 ^ A * ((X / 3 ^ A : ℕ) : ℝ) + ((X % 3 ^ A : ℕ) : ℝ) := by
      exact_mod_cast hdec.symm
    have : (Θ : ℝ) + δ + 2 ^ ℓ * E = ((X : ℕ) : ℝ) + δ := by rw [hX]; push_cast; ring
    rw [this, hXr]
    field_simp
    ring

/-- **Moving the floor**: if `1 ≤ R`, `a ≤ R` and `3^A R ∤ R X + a`, then `⌊(R X + a)/(3^A R)⌋ = ⌊X/3^A⌋`. -/
theorem floor_shift (R a X A : ℕ) (hR : 1 ≤ R) (ha : a ≤ R) (hnd : ¬ 3 ^ A * R ∣ R * X + a) :
    (R * X + a) / (3 ^ A * R) = X / 3 ^ A := by
  rw [mul_comm (3 ^ A) R, ← Nat.div_div_eq_div_mul, Nat.mul_add_div (by omega)]
  rcases Nat.lt_or_ge a R with hlt | hge
  · rw [Nat.div_eq_of_lt hlt, add_zero]
  · have haR : a = R := le_antisymm ha hge
    subst haR
    rw [Nat.div_self (by omega)]
    apply Nat.succ_div_of_not_dvd
    intro hd
    apply hnd
    rw [show a * X + a = a * (X + 1) by ring, mul_comm (3 ^ A) a]
    exact Nat.mul_dvd_mul_left a hd

/-! ## §5 Periodic words (Lemma 11.6) -/

/-- `w^k` (`k` copies of `w`). -/
def wpow (w : List (Fin 2)) (k : ℕ) : List (Fin 2) := (List.replicate k w).flatten

theorem wpow_zero (w : List (Fin 2)) : wpow w 0 = [] := rfl

theorem wpow_succ (w : List (Fin 2)) (k : ℕ) : wpow w (k + 1) = wpow w k ++ w := by
  simp [wpow, List.replicate_succ']

@[simp] theorem wpow_length (w : List (Fin 2)) (k : ℕ) : (wpow w k).length = w.length * k := by
  induction k with
  | zero => simp [wpow]
  | succ k ih => rw [wpow_succ, List.length_append, ih]; ring

/-- `X_k = 2^{Lk} X_0`: `(2^L - 1) valW r (w^k) + val(w) = 2^{Lk} ((2^L - 1) r + val(w))` (`L = |w|`).
With `r = valW 1 p` this is `X_k := (2^L - 1) val(1 p w^k) + val(w)`; with `r = 0`, `(2^L - 1) val(w^m) + val(w) = 2^{Lm} val(w)`. -/
theorem valW_wpow (w : List (Fin 2)) (r k : ℕ) :
    (2 ^ w.length - 1) * valW r (wpow w k) + valW 0 w =
      2 ^ (w.length * k) * ((2 ^ w.length - 1) * r + valW 0 w) := by
  obtain ⟨R, hR⟩ : ∃ R, 2 ^ w.length = R + 1 := ⟨2 ^ w.length - 1, by have := Nat.one_le_two_pow (n := w.length); omega⟩
  have hR' : 2 ^ w.length - 1 = R := by omega
  rw [hR']
  induction k with
  | zero => simp [wpow, valW]
  | succ k ih =>
    rw [wpow_succ, valW_append, valW_eq (valW r (wpow w k)), mul_add, Nat.mul_succ, pow_add, hR]
    rw [show R * (valW r (wpow w k) * (R + 1)) + R * valW 0 w + valW 0 w =
      (R + 1) * (R * valW r (wpow w k) + valW 0 w) by ring, ih]
    ring

/-- **The core of Lemma 11.6 (ii)**: if `R U + a = 2^e X_0` (`X_0 ≠ 0`, `v_3(X_0) < A`, `a ≤ R`), then `ν := a + R (U mod 3^A)` satisfies
`v_3(ν) = v_3(X_0)` and `0 < ν < 3^A R`. -/
theorem nu_core (R a U A e X0 : ℕ) (ha : a ≤ R) (hX : R * U + a = 2 ^ e * X0) (hX0 : X0 ≠ 0)
    (hA : padicValNat 3 X0 < A) :
    padicValNat 3 (a + R * (U % 3 ^ A)) = padicValNat 3 X0 ∧ 0 < a + R * (U % 3 ^ A) ∧
      a + R * (U % 3 ^ A) < 3 ^ A * R := by
  set b0 := padicValNat 3 X0 with hb0
  set ν := a + R * (U % 3 ^ A) with hν
  have hUdec : 3 ^ A * (U / 3 ^ A) + U % 3 ^ A = U := Nat.div_add_mod U (3 ^ A)
  have hsum : ν + 3 ^ A * (R * (U / 3 ^ A)) = 2 ^ e * X0 := by
    have : ν + 3 ^ A * (R * (U / 3 ^ A)) = R * (3 ^ A * (U / 3 ^ A) + U % 3 ^ A) + a := by
      rw [hν]; ring
    rw [this, hUdec, hX]
  have hcop : Nat.Coprime (3 ^ (b0 + 1)) (2 ^ e) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have hd0 : 3 ^ b0 ∣ 2 ^ e * X0 := Dvd.dvd.mul_left pow_padicValNat_dvd _
  have hnd1 : ¬ 3 ^ (b0 + 1) ∣ 2 ^ e * X0 := fun h =>
    pow_succ_padicValNat_not_dvd hX0 (hcop.dvd_of_dvd_mul_left h)
  have hA0 : 3 ^ b0 ∣ 3 ^ A * (R * (U / 3 ^ A)) := Dvd.dvd.mul_right (pow_dvd_pow 3 (by omega)) _
  have hA1 : 3 ^ (b0 + 1) ∣ 3 ^ A * (R * (U / 3 ^ A)) := Dvd.dvd.mul_right (pow_dvd_pow 3 (by omega)) _
  have hν0 : 3 ^ b0 ∣ ν := by
    have := hsum ▸ hd0
    exact (Nat.dvd_add_left hA0).1 this
  have hν1 : ¬ 3 ^ (b0 + 1) ∣ ν := by
    intro h
    apply hnd1
    rw [← hsum]
    exact Nat.dvd_add h hA1
  have hνne : ν ≠ 0 := by
    intro h; rw [h] at hν1; exact hν1 (dvd_zero _)
  refine ⟨?_, Nat.pos_of_ne_zero hνne, ?_⟩
  · apply le_antisymm
    · by_contra hlt
      push Not at hlt
      exact hν1 ((padicValNat_dvd_iff_le hνne).2 hlt)
    · exact (padicValNat_dvd_iff_le hνne).1 hν0
  · have hE : U % 3 ^ A + 1 ≤ 3 ^ A := Nat.mod_lt _ (by positivity)
    have hle : ν ≤ 3 ^ A * R := by
      have : R * (U % 3 ^ A + 1) ≤ R * 3 ^ A := Nat.mul_le_mul_left R hE
      rw [hν]; nlinarith
    rcases Nat.lt_or_ge ν (3 ^ A * R) with h | h
    · exact h
    · exfalso
      have heq : ν = 3 ^ A * R := le_antisymm hle h
      apply hν1
      rw [heq]
      exact Dvd.dvd.mul_right (pow_dvd_pow 3 (by omega)) _

/-- **Reduction to lowest terms**: if `0 < ν < 3^A R` and `v_3(ν) = b_0`, then `N/D = ν/(3^A R)` in lowest terms satisfies
`0 < N < D`, `D = 3^α D''` (`3 ∤ D''`, `D'' ∣ R`), `α ≥ A - b_0` and `⌊2^ℓ ν/(3^A R)⌋ = ⌊2^ℓ N/D⌋`. -/
theorem reduced_frac (ν R A b0 : ℕ) (hν0 : 0 < ν) (hνlt : ν < 3 ^ A * R) (hb : padicValNat 3 ν = b0) :
    ∃ N D α D'' : ℕ, N * (3 ^ A * R) = ν * D ∧ N.Coprime D ∧ 0 < N ∧ N < D ∧ D = 3 ^ α * D'' ∧
      ¬ 3 ∣ D'' ∧ D'' ∣ R ∧ A - b0 ≤ α ∧ ∀ ℓ, 2 ^ ℓ * ν / (3 ^ A * R) = 2 ^ ℓ * N / D := by
  set Δ := 3 ^ A * R with hΔ
  have hR0 : R ≠ 0 := by rintro rfl; simp [hΔ] at hνlt
  have hΔ0 : Δ ≠ 0 := by rw [hΔ]; positivity
  set g := Nat.gcd ν Δ with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hν0
  set N := ν / g with hN
  set D := Δ / g with hD
  have hνg : N * g = ν := Nat.div_mul_cancel (Nat.gcd_dvd_left ν Δ)
  have hΔg : D * g = Δ := Nat.div_mul_cancel (Nat.gcd_dvd_right ν Δ)
  have hD0 : D ≠ 0 := by rintro h; rw [h, zero_mul] at hΔg; exact hΔ0 hΔg.symm
  have hcop : N.Coprime D := Nat.coprime_div_gcd_div_gcd hgpos
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, zero_mul] at hνg; omega
    · exact h
  have hND : N < D := by
    have : N * g < D * g := by rw [hνg, hΔg]; exact hνlt
    exact Nat.lt_of_mul_lt_mul_right this
  set α := padicValNat 3 D with hα
  set D'' := D / 3 ^ α with hD''
  have hDsplit : D = 3 ^ α * D'' := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have hD''3 : ¬ 3 ∣ D'' := by
    intro h3
    apply pow_succ_padicValNat_not_dvd (p := 3) hD0
    rw [← hα, pow_succ]
    conv_rhs => rw [hDsplit]
    exact Nat.mul_dvd_mul_left _ h3
  have hD''R : D'' ∣ R := by
    have h1 : D'' ∣ Δ := by
      rw [← hΔg, hDsplit]; exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
    have hcop3 : Nat.Coprime D'' (3 ^ A) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hD''3))
    exact hcop3.dvd_of_dvd_mul_left h1
  have hαge : A - b0 ≤ α := by
    have hvΔ : padicValNat 3 Δ = A + padicValNat 3 R := by
      rw [hΔ, padicValNat.mul (by positivity) hR0, padicValNat.prime_pow]
    have hvΔ' : padicValNat 3 Δ = padicValNat 3 D + padicValNat 3 g := by
      rw [← hΔg, padicValNat.mul hD0 hgpos.ne']
    have hvg : padicValNat 3 g ≤ b0 := by
      rw [← hb]
      have : 3 ^ padicValNat 3 g ∣ ν := (pow_padicValNat_dvd (p := 3) (n := g)).trans (Nat.gcd_dvd_left ν Δ)
      exact (padicValNat_dvd_iff_le hν0.ne').1 this
    omega
  refine ⟨N, D, α, D'', ?_, hcop, hNpos, hND, hDsplit, hD''3, hD''R, hαge, ?_⟩
  · rw [← hνg, ← hΔg]; ring
  · intro ℓ
    rw [← hνg, ← hΔg, ← mul_assoc, Nat.mul_div_mul_right _ _ hgpos]

/-! ### §5.1 Values of words -/

/-- `val(1 p w^k w^m s) = U 2^{|s| + Lm} + val(w^m) 2^{|s|} + val(s)` (`U = val(1 p w^k)`). -/
theorem valW_pkms (p w s : List (Fin 2)) (k m : ℕ) :
    valW 1 (p ++ wpow w k ++ wpow w m ++ s) =
      valW 1 (p ++ wpow w k) * 2 ^ (s.length + w.length * m) + valW 0 (wpow w m) * 2 ^ s.length + valW 0 s := by
  rw [valW_append, valW_append 1 (p ++ wpow w k), valW_eq (valW _ (wpow w m)), valW_eq (valW 1 _),
    wpow_length, pow_add]
  ring

/-- If `k = 2A`, then `val(1 p w^k) ≥ 3^A` (`|w| ≥ 1`; "`k` large enough that `U_0 ≥ 3^A`"). -/
theorem three_pow_le_valW_wpow (p w : List (Fin 2)) (A : ℕ) (hL : 1 ≤ w.length) :
    3 ^ A ≤ valW 1 (p ++ wpow w (2 * A)) := by
  have h1 := two_pow_le_valW_one (p ++ wpow w (2 * A))
  have h2 : 2 * A ≤ (p ++ wpow w (2 * A)).length := by
    rw [List.length_append, wpow_length]; nlinarith
  calc 3 ^ A ≤ 4 ^ A := Nat.pow_le_pow_left (by norm_num) A
    _ = 2 ^ (2 * A) := by rw [pow_mul]; norm_num
    _ ≤ 2 ^ (p ++ wpow w (2 * A)).length := Nat.pow_le_pow_right (by norm_num) h2
    _ ≤ _ := h1

end Collatz.Arctic.NatQ5.W2a

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic W2a

/-! ## §6 Assembly: the chain of `val(1 p w^k w^m s)` (the form used by Theorem 11.8) -/

/-- **Assembly** (the form used by Theorem 11.8, Step 4): let `L = |w| ≥ 1`, `U := val(1 p w^k) ≥ 3^A`, and
`v_3(X_0) < A` for `X_0 := (2^L - 1) val(1p) + val(w)`. Then there is a fraction `N/D` in lowest terms, independent of `m`
(`0 < N < D`, `D = 3^α D''`, `3 ∤ D''`, `D'' ∣ 2^L - 1`, `α ≥ A - v_3(X_0)`), such that for every `m`,
if `y_m := val(1 p w^k w^m s)` is not divisible by 3, there are `n` not divisible by 3, `M ≤ 4A` and `V' < 2^{|s|+M}` with
`bin'(n) = bin'(⌊U/3^A⌋) ++ dig N D 0 (Lm) ++ bitsF (|s|+M) V'`, `T^M(n) = y_m` and `T^i(n) ≥ 2` (`i < M`).
In the notation `n_A = val(1 τ R_m β)` of an earlier argument: `1τ` is the binary expansion of `⌊U/3^A⌋`, `R_m` the first `Lm` digits of the expansion of `θ_A = N/D`, and `β` a word of length
`|s| + M ≤ |s| + 4A` (bounded independently of `m`). -/
theorem back_chain_word (p w s : List (Fin 2)) (k A : ℕ) (hL : 1 ≤ w.length)
    (hU : 3 ^ A ≤ valW 1 (p ++ wpow w k))
    (hA : padicValNat 3 ((2 ^ w.length - 1) * valW 1 p + valW 0 w) < A) :
    ∃ N D α D'' : ℕ, N.Coprime D ∧ 0 < N ∧ N < D ∧ D = 3 ^ α * D'' ∧ ¬ 3 ∣ D'' ∧
      D'' ∣ 2 ^ w.length - 1 ∧ A - padicValNat 3 ((2 ^ w.length - 1) * valW 1 p + valW 0 w) ≤ α ∧
      ∀ m : ℕ, ¬ 3 ∣ valW 1 (p ++ wpow w k ++ wpow w m ++ s) →
        ∃ n M V' : ℕ, M ≤ 4 * A ∧ V' < 2 ^ (s.length + M) ∧
          binWord n = binWord (valW 1 (p ++ wpow w k) / 3 ^ A) ++ dig N D 0 (w.length * m) ++
            bitsF (s.length + M) V' ∧
          ¬ 3 ∣ n ∧ Collatz.Arctic.T^[M] n = valW 1 (p ++ wpow w k ++ wpow w m ++ s) ∧
          ∀ i < M, 2 ≤ Collatz.Arctic.T^[i] n := by
  set L := w.length with hLdef
  set R := 2 ^ L - 1 with hRdef
  set a := valW 0 w with ha
  set r := valW 1 p with hr
  set U := valW 1 (p ++ wpow w k) with hUdef
  set X0 := R * r + a with hX0
  have h2L : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hR1 : 1 ≤ R := by omega
  have haR : a ≤ R := by have h := valW_lt w; rw [← hLdef] at h; omega
  have hr1 : 1 ≤ r := by have := two_pow_le_valW_one p; have := Nat.one_le_two_pow (n := p.length); omega
  have hX0ne : X0 ≠ 0 := by
    have : 1 ≤ R * r := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hUr : U = valW r (wpow w k) := by rw [hUdef, valW_append]
  have hXk : R * U + a = 2 ^ (L * k) * X0 := by rw [hUr]; exact valW_wpow w r k
  obtain ⟨hνv, hν0, hνlt⟩ := nu_core R a U A (L * k) X0 haR hXk hX0ne hA
  set ν := a + R * (U % 3 ^ A) with hν
  obtain ⟨N, D, α, D'', _, hcop, hN0, hND, hDsplit, hD''3, hD''R, hαge, hfloor⟩ :=
    reduced_frac ν R A (padicValNat 3 X0) hν0 hνlt hνv
  refine ⟨N, D, α, D'', hcop, hN0, hND, hDsplit, hD''3, hD''R, hαge, ?_⟩
  intro m hy
  set ℓ := L * m with hℓ
  set Θ0 := valW 0 (wpow w m) with hΘ0
  have hΘ0lt : Θ0 < 2 ^ ℓ := by have := valW_lt (wpow w m); rwa [wpow_length] at this
  have hVlt : valW 0 s < 2 ^ s.length := valW_lt s
  have hyeq := valW_pkms p w s k m
  rw [← hUdef] at hyeq
  rw [hyeq] at hy
  obtain ⟨n, M, V', hM, hn, hΘ', hV', hn3, hT, hmid⟩ :=
    back_chain A U Θ0 (valW 0 s) s.length ℓ hU hΘ0lt hVlt hy
  -- `Θ' = ⌊2^ℓ ν/(3^A R)⌋ = ⌊2^ℓ N/D⌋`
  have hRΘ : R * Θ0 + a = 2 ^ ℓ * a := by
    have := valW_wpow w 0 m
    simpa [hΘ0, hℓ] using this
  have hkey : R * (Θ0 + 2 ^ ℓ * (U % 3 ^ A)) + a = 2 ^ ℓ * ν := by
    rw [hν, mul_add, add_right_comm, hRΘ]; ring
  have hRodd : ¬ 2 ∣ R := by
    have : 2 ∣ 2 ^ L := dvd_pow_self 2 (by omega)
    omega
  have hcop2 : Nat.Coprime (3 ^ A * R) (2 ^ ℓ) := by
    apply Nat.Coprime.pow_right
    exact Nat.coprime_mul_iff_left.2 ⟨Nat.Coprime.pow_left _ (by norm_num),
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hRodd)⟩
  have hnd : ¬ 3 ^ A * R ∣ R * (Θ0 + 2 ^ ℓ * (U % 3 ^ A)) + a := by
    rw [hkey]
    intro hd
    have := hcop2.dvd_of_dvd_mul_left hd
    have := Nat.le_of_dvd hν0 this
    omega
  have hΘeq : (Θ0 + 2 ^ ℓ * (U % 3 ^ A)) / 3 ^ A = 2 ^ ℓ * N / D := by
    rw [← floor_shift R a _ A hR1 haR hnd, hkey, hfloor]
  have hU1 : 1 ≤ U / 3 ^ A := by
    rw [Nat.le_div_iff_mul_le (by positivity), one_mul]; exact hU
  refine ⟨n, M, V', hM, hV', ?_, hn3, by rw [hyeq]; exact hT, hmid⟩
  rw [hn, binWord_split _ _ _ _ _ hU1 hΘ' hV', hΘeq, bitsF_floor N D ℓ hND]

end Collatz.Arctic.NatQ5
