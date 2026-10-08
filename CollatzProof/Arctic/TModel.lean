/-
The Terras correspondence for `T` (the deterministic part of the block model of `T`, Lemma 6.1).

For a parity word `σ` (`true` = odd step), the state `(m, r, c, a)` is built one step at a time (`terrasStep`).
The invariant is `T^[m] (r + 2^m t) = c + 3^a t` (for all `t`). To make the parity of the next step equal to `b`,
the lowest bit `t0 := (b + c) mod 2` of `t` is chosen and added to `r`. Results:

* `terrasState_fst`, `terrasA_eq`: `m = |σ|`, and `a` is the number of odd steps of `σ`.
* `terrasR_lt`, `terrasC_lt`: `r_σ < 2^m`, `c_σ < 3^{a_σ}`.
* `terras_iter`: `T^[m] (r_σ + 2^m t) = c_σ + 3^{a_σ} t` (the map `x_0 = r_σ + 2^m t ↦ x_σ = c_σ + 3^{a_σ} t` of Lemma 6.1).
* `terras_parity`: the parities of the first `m` steps of the orbit of `x_0` are `σ`.
* `terras_prefix`: residues and orbits for concatenated words (the end point of the first part is the starting point of the second part).
* `terras_orbit_ge`: lower bound `2^{m-i} t ≤ T^[i] x_0` on the points of the orbit (corollary: if `t ≥ 1`, the points of the segment are at least 2).
* `binTail_add_mul`: the digit list of the canonical string of `x_0` is `bin'(t)` followed by the `m` digits of `r_σ` (`bitsMSB`).
  `bitsMSB_add_mul`: splitting a digit representation into top and bottom.

Numerical check (outside this file, by `#eval`): `X' = 10110110` gives `(r, c, a) = (249, 238, 5)`, and `Y' = 10110110110` gives
`(2041, 2182, 7)`. This is consistent with the affine constants `γ_{X'} = 421`, `γ_{Y'} = 5069` via `(3^a r + γ)/2^m = c`.
-/
import CollatzProof.Arctic.Canon

namespace Collatz.Arctic

/-! ### Definitions -/

/-- One step building the state `(m, r, c, a)` of the Terras correspondence along a parity word (`true` = odd step).
To keep `T^[m] (r + 2^m t) = c + 3^a t`, choose the lowest bit `t0` of `t` so that the parity of the next step is `b`. -/
def terrasStep (s : ℕ × ℕ × ℕ × ℕ) (b : Bool) : ℕ × ℕ × ℕ × ℕ :=
  let t0 := ((if b then 1 else 0) + s.2.2.1) % 2
  (s.1 + 1, s.2.1 + 2 ^ s.1 * t0, T (s.2.2.1 + 3 ^ s.2.2.2 * t0), s.2.2.2 + (if b then 1 else 0))

/-- The Terras state `(m, r_σ, c_σ, a_σ)` of the word `σ`. -/
def terrasState (σ : List Bool) : ℕ × ℕ × ℕ × ℕ := σ.foldl terrasStep (0, 0, 0, 0)

/-- The residue `r_σ` (the number that follows `σ` modulo `2^m`). -/
def terrasR (σ : List Bool) : ℕ := (terrasState σ).2.1

/-- The end point constant `c_σ`. -/
def terrasC (σ : List Bool) : ℕ := (terrasState σ).2.2.1

/-- The number of odd steps `a_σ`. -/
def terrasA (σ : List Bool) : ℕ := (terrasState σ).2.2.2

/-- The `m`-digit binary representation of `r < 2^m` (from the most significant digit, padded at the top with `f`). -/
def bitsMSB : ℕ → ℕ → Word
  | 0, _ => []
  | m + 1, r => bitL (r / 2 ^ m % 2) :: bitsMSB m (r % 2 ^ m)

/-! ### The one-step formulas -/

/-- The lowest bit added to `t` at the next step. -/
def terrasT0 (σ : List Bool) (b : Bool) : ℕ := ((if b then 1 else 0) + terrasC σ) % 2

lemma terrasState_snoc (σ : List Bool) (b : Bool) :
    terrasState (σ ++ [b]) = terrasStep (terrasState σ) b := by
  simp [terrasState, List.foldl_append]

/-- `m = |σ|`. -/
theorem terrasState_fst (σ : List Bool) : (terrasState σ).1 = σ.length := by
  induction σ using List.reverseRecOn with
  | nil => rfl
  | append_singleton σ b ih => simp [terrasState_snoc, terrasStep, ih]

lemma terrasR_snoc (σ : List Bool) (b : Bool) :
    terrasR (σ ++ [b]) = terrasR σ + 2 ^ σ.length * terrasT0 σ b := by
  simp [terrasR, terrasState_snoc, terrasStep, terrasState_fst, terrasT0, terrasC]

lemma terrasC_snoc (σ : List Bool) (b : Bool) :
    terrasC (σ ++ [b]) = T (terrasC σ + 3 ^ terrasA σ * terrasT0 σ b) := by
  simp [terrasC, terrasState_snoc, terrasStep, terrasT0, terrasA]

lemma terrasA_snoc (σ : List Bool) (b : Bool) :
    terrasA (σ ++ [b]) = terrasA σ + (if b then 1 else 0) := by
  simp [terrasA, terrasState_snoc, terrasStep]

lemma terrasT0_le (σ : List Bool) (b : Bool) : terrasT0 σ b ≤ 1 := by
  unfold terrasT0; omega

lemma three_pow_mod_two (A : ℕ) : 3 ^ A % 2 = 1 := by
  rw [Nat.pow_mod]; norm_num

/-- The parity of the next point `c + 3^a t0` is `b`. -/
lemma terras_next_parity (σ : List Bool) (b : Bool) :
    (terrasC σ + 3 ^ terrasA σ * terrasT0 σ b) % 2 = if b then 1 else 0 := by
  have h3 := three_pow_mod_two (terrasA σ)
  have h0 := terrasT0_le σ b
  unfold terrasT0 at h0 ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h | h <;> rw [h] <;> cases b <;> simp_all <;> omega

lemma T_of_even (y : ℕ) (hy : y % 2 = 0) : T y = y / 2 := by
  simp [T, hy]

lemma T_of_odd (y : ℕ) (hy : y % 2 = 1) : T y = (3 * y + 1) / 2 := by
  simp [T, hy]

/-- Adding `2k` to an even point shifts its image under `T` by `k`. -/
lemma T_add_even (y k : ℕ) (hy : y % 2 = 0) : T (y + 2 * k) = T y + k := by
  unfold T; split_ifs <;> omega

/-- Adding `2k` to an odd point shifts its image under `T` by `3k`. -/
lemma T_add_odd (y k : ℕ) (hy : y % 2 = 1) : T (y + 2 * k) = T y + 3 * k := by
  unfold T; split_ifs <;> omega

/-! ### Basic properties -/

/-- `a_σ` is the number of odd steps of `σ`. -/
theorem terrasA_eq (σ : List Bool) : terrasA σ = σ.count true := by
  induction σ using List.reverseRecOn with
  | nil => rfl
  | append_singleton σ b ih =>
    rw [terrasA_snoc, ih, List.count_append, List.count_singleton]
    cases b <;> simp

theorem terrasA_append (σ₁ σ₂ : List Bool) : terrasA (σ₁ ++ σ₂) = terrasA σ₁ + terrasA σ₂ := by
  simp [terrasA_eq, List.count_append]

/-- `r_σ < 2^m`. -/
theorem terrasR_lt (σ : List Bool) : terrasR σ < 2 ^ σ.length := by
  induction σ using List.reverseRecOn with
  | nil => simp [terrasR, terrasState]
  | append_singleton σ b ih =>
    rw [terrasR_snoc, List.length_append, List.length_singleton, pow_succ]
    have := terrasT0_le σ b
    have : 2 ^ σ.length * terrasT0 σ b ≤ 2 ^ σ.length * 1 := Nat.mul_le_mul_left _ this
    omega

/-- `c_σ < 3^{a_σ}`. -/
theorem terrasC_lt (σ : List Bool) : terrasC σ < 3 ^ terrasA σ := by
  induction σ using List.reverseRecOn with
  | nil => simp [terrasC, terrasA, terrasState]
  | append_singleton σ b ih =>
    rw [terrasC_snoc, terrasA_snoc]
    have hp := terras_next_parity σ b
    have h0 := terrasT0_le σ b
    have hle : 3 ^ terrasA σ * terrasT0 σ b ≤ 3 ^ terrasA σ * 1 := Nat.mul_le_mul_left _ h0
    set y := terrasC σ + 3 ^ terrasA σ * terrasT0 σ b with hy
    set P := 3 ^ terrasA σ with hP
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hp ⊢
      rw [T_of_even _ hp]; omega
    · simp only [↓reduceIte] at hp ⊢
      rw [pow_succ, T_of_odd _ hp]; omega

/-- The joining formula: `r_{σb} + 2^{m+1} t = r_σ + 2^m (t0 + 2t)`. -/
lemma terrasR_snoc_add (σ : List Bool) (b : Bool) (t : ℕ) :
    terrasR (σ ++ [b]) + 2 ^ (σ ++ [b]).length * t
      = terrasR σ + 2 ^ σ.length * (terrasT0 σ b + 2 * t) := by
  rw [terrasR_snoc, List.length_append, List.length_singleton, pow_succ]
  ring

/-- **The Terras correspondence**: `T^[m] (r_σ + 2^m t) = c_σ + 3^{a_σ} t`. -/
theorem terras_iter (σ : List Bool) :
    ∀ t, T^[σ.length] (terrasR σ + 2 ^ σ.length * t) = terrasC σ + 3 ^ terrasA σ * t := by
  induction σ using List.reverseRecOn with
  | nil => intro t; simp [terrasR, terrasC, terrasA, terrasState]
  | append_singleton σ b ih =>
    intro t
    rw [terrasR_snoc_add, List.length_append, List.length_singleton,
      Function.iterate_succ_apply', ih, terrasC_snoc, terrasA_snoc]
    have hp := terras_next_parity σ b
    have e : terrasC σ + 3 ^ terrasA σ * (terrasT0 σ b + 2 * t)
        = (terrasC σ + 3 ^ terrasA σ * terrasT0 σ b) + 2 * (3 ^ terrasA σ * t) := by ring
    rw [e]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hp ⊢
      rw [T_add_even _ _ hp]
    · simp only [↓reduceIte] at hp ⊢
      rw [T_add_odd _ _ hp, pow_succ]
      ring

/-- The parities of the first `m` steps of the orbit are `σ`. -/
theorem terras_parity (σ : List Bool) :
    ∀ t, ∀ i < σ.length,
      T^[i] (terrasR σ + 2 ^ σ.length * t) % 2 = if σ.getD i false then 1 else 0 := by
  induction σ using List.reverseRecOn with
  | nil => intro t i hi; simp at hi
  | append_singleton σ b ih =>
    intro t i hi
    rw [terrasR_snoc_add]
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [ih _ i h, List.getD_append _ _ _ _ h]
    · subst h
      rw [terras_iter σ, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      have hp := terras_next_parity σ b
      have e : terrasC σ + 3 ^ terrasA σ * (terrasT0 σ b + 2 * t)
          = (terrasC σ + 3 ^ terrasA σ * terrasT0 σ b) + 2 * (3 ^ terrasA σ * t) := by ring
      rw [e]
      simp only [List.getD_cons_zero]
      omega

/-! ### Concatenating words -/

/-- The residue of a concatenated word is the residue of the first word plus `2^{|σ₁|}` times an `|σ₂|`-digit number. -/
theorem terrasR_append (σ₁ σ₂ : List Bool) :
    ∃ r' < 2 ^ σ₂.length, terrasR (σ₁ ++ σ₂) = terrasR σ₁ + 2 ^ σ₁.length * r' := by
  induction σ₂ using List.reverseRecOn with
  | nil => exact ⟨0, by simp, by simp⟩
  | append_singleton σ₂ b ih =>
    obtain ⟨r', hr', hR⟩ := ih
    refine ⟨r' + 2 ^ σ₂.length * terrasT0 (σ₁ ++ σ₂) b, ?_, ?_⟩
    · rw [List.length_append, List.length_singleton, pow_succ]
      have h0 := terrasT0_le (σ₁ ++ σ₂) b
      have : 2 ^ σ₂.length * terrasT0 (σ₁ ++ σ₂) b ≤ 2 ^ σ₂.length * 1 := Nat.mul_le_mul_left _ h0
      omega
    · rw [← List.append_assoc, terrasR_snoc, hR, List.length_append, pow_add]
      ring

/-- The orbit for concatenated words: the point reached after the first part `σ₁` is the image of `r' + 2^{|σ₂|} t` under the Terras correspondence of `σ₁`. -/
theorem terras_prefix (σ₁ σ₂ : List Bool) :
    ∃ r' < 2 ^ σ₂.length, terrasR (σ₁ ++ σ₂) = terrasR σ₁ + 2 ^ σ₁.length * r' ∧
      ∀ t, T^[σ₁.length] (terrasR (σ₁ ++ σ₂) + 2 ^ (σ₁ ++ σ₂).length * t)
        = terrasC σ₁ + 3 ^ terrasA σ₁ * (r' + 2 ^ σ₂.length * t) := by
  obtain ⟨r', hr', hR⟩ := terrasR_append σ₁ σ₂
  refine ⟨r', hr', hR, fun t => ?_⟩
  have e : terrasR (σ₁ ++ σ₂) + 2 ^ (σ₁ ++ σ₂).length * t
      = terrasR σ₁ + 2 ^ σ₁.length * (r' + 2 ^ σ₂.length * t) := by
    rw [hR, List.length_append, pow_add]; ring
  rw [e, terras_iter]

/-! ### Lower bound on the points of the orbit -/

/-- Lower bound on the points of the orbit: for `i ≤ m`, `2^{m-i} t ≤ T^[i] (r_σ + 2^m t)`. -/
theorem terras_orbit_ge (σ : List Bool) :
    ∀ t, ∀ i ≤ σ.length, 2 ^ (σ.length - i) * t ≤ T^[i] (terrasR σ + 2 ^ σ.length * t) := by
  induction σ using List.reverseRecOn with
  | nil => intro t i hi; simp at hi; subst hi; simp
  | append_singleton σ b ih =>
    intro t i hi
    have hlen : (σ ++ [b]).length = σ.length + 1 := by simp
    rw [hlen] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with h | h
    · have hi' : i ≤ σ.length := Nat.lt_succ_iff.mp h
      rw [terrasR_snoc_add, hlen]
      refine le_trans ?_ (ih _ i hi')
      rw [show σ.length + 1 - i = (σ.length - i) + 1 by omega, pow_succ, mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    · subst h
      have hit := terras_iter (σ ++ [b]) t
      rw [hlen] at hit
      rw [hlen, hit, Nat.sub_self, pow_zero, one_mul]
      calc t ≤ 3 ^ terrasA (σ ++ [b]) * t := Nat.le_mul_of_pos_left _ (by positivity)
        _ ≤ _ := Nat.le_add_left _ _

/-- Corollary: if `t ≥ 1`, the points `x_0, …, T^[m-1] x_0` of the orbit segment are at least 2. -/
theorem terras_orbit_two_le (σ : List Bool) (t : ℕ) (ht : 1 ≤ t) :
    ∀ i < σ.length, 2 ≤ T^[i] (terrasR σ + 2 ^ σ.length * t) := by
  intro i hi
  refine le_trans ?_ (terras_orbit_ge σ t i hi.le)
  have h2 : 2 ≤ 2 ^ (σ.length - i) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (σ.length - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 = 2 * 1 := by norm_num
    _ ≤ 2 ^ (σ.length - i) * t := Nat.mul_le_mul h2 ht

/-! ### Digits of the canonical string -/

theorem bitsMSB_length (m r : ℕ) : (bitsMSB m r).length = m := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih => simp [bitsMSB, ih]

/-- The digit list of `x_0 = r + 2^m t` (without the leading 1) is `bin'(t)` followed by the `m` digits of `r`. -/
theorem binTail_add_mul (m : ℕ) : ∀ r t : ℕ, 1 ≤ t → r < 2 ^ m →
    binTail (r + 2 ^ m * t) = binTail t ++ bitsMSB m r := by
  induction m with
  | zero => intro r t _ hr; simp at hr; subst hr; simp [bitsMSB]
  | succ m ih =>
    intro r t ht hr
    have hq : r / 2 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hr; omega
    have hdm := Nat.mod_add_div r (2 ^ m)
    have e : r + 2 ^ (m + 1) * t = r % 2 ^ m + 2 ^ m * (2 * t + r / 2 ^ m) := by
      rw [pow_succ]
      calc r + 2 ^ m * 2 * t = (r % 2 ^ m + 2 ^ m * (r / 2 ^ m)) + 2 ^ m * 2 * t := by rw [hdm]
        _ = _ := by ring
    have ht' : 1 ≤ 2 * t + r / 2 ^ m := le_trans (by omega : 1 ≤ 2 * t) (Nat.le_add_right _ _)
    rw [e, ih (r % 2 ^ m) (2 * t + r / 2 ^ m) ht' (Nat.mod_lt _ (by positivity)),
      binTail_two_mul_add t _ ht hq]
    simp [bitsMSB, Nat.mod_eq_of_lt hq]

/-- `bitsMSB m r = bin'(2^m + r)`. -/
lemma bitsMSB_eq_binTail (m r : ℕ) (hr : r < 2 ^ m) : bitsMSB m r = binTail (r + 2 ^ m) := by
  have := binTail_add_mul m r 1 (le_refl 1) hr
  rw [mul_one] at this
  rw [this, binTail_one, List.nil_append]

/-- An `(m₁ + m₂)`-digit representation is the top `m₁` digits followed by the bottom `m₂` digits. -/
theorem bitsMSB_add_mul (m₁ m₂ r₁ r₂ : ℕ) (h₁ : r₁ < 2 ^ m₁) (h₂ : r₂ < 2 ^ m₂) :
    bitsMSB (m₁ + m₂) (r₂ + 2 ^ m₂ * r₁) = bitsMSB m₁ r₁ ++ bitsMSB m₂ r₂ := by
  have hlt : r₂ + 2 ^ m₂ * r₁ < 2 ^ (m₁ + m₂) := by
    have : 2 ^ m₂ * (r₁ + 1) ≤ 2 ^ m₂ * 2 ^ m₁ := Nat.mul_le_mul_left _ h₁
    rw [pow_add, mul_comm (2 ^ m₁)]
    rw [mul_add, mul_one] at this
    omega
  rw [bitsMSB_eq_binTail _ _ hlt, bitsMSB_eq_binTail _ _ h₁]
  have e : r₂ + 2 ^ m₂ * r₁ + 2 ^ (m₁ + m₂) = r₂ + 2 ^ m₂ * (r₁ + 2 ^ m₁) := by
    rw [pow_add]; ring
  rw [e, binTail_add_mul m₂ r₂ _ (by have := Nat.one_le_two_pow (n := m₁); omega) h₂]

end Collatz.Arctic
