/-
The law of large numbers for the expansion in the block model of `T` (the expansion of the point family, Section 6.1, used in the proof of Theorem 6.8).
The definition of the point family and the counting of blocks are in `Family.lean`, the probability `Prσ` in `CoreHyp.lean`.

Blocks `X'` (multiplier `3^5/2^8 = 243/256`) with weight 3/10 and `Y'` (`3^7/2^{11} = 2187/2048`) with weight 7/10 are placed
independently. If `#X' ≤ k/2` among the remaining `k` blocks, then `(243·2187)/(256·2048) = 531441/524288` and
`(531441/524288)^{64} ≥ 2` give `2^{m + ⌈k/256⌉} ≤ 3^a` (the contribution of the initial blocks `β₀` is absorbed when `k` is large).
`#X'` is binomial with weight 3/10, and by Chebyshev (`Σ w (X - 3k/10)² = 21k/100`) the probability of `#X' > k/2` is
at most `21/(4k)`.

* `fam_expand_det`, `fam_expand_event`: the deterministic part.
* `fam_mem_blockChoices`, `fam_sum_succ`: splitting the sum over all block sequences at the first block.
* `fam_moments`, `fam_variance`: total weight 1, the first and second moments, the variance.
* `fam_pr_ge`: a lower bound on `Prσ` from an upper bound on the weight of the bad event.
* `fam_expansion_lln`: **the law of large numbers for the expansion** (`c = 1/256`).
-/
import CollatzProof.Arctic.Family

namespace Collatz.Arctic

/-! ## Deterministic bound on the expansion -/

/-- If `x ≤ y` (`#X' ≤ #Y'`) and `64 q ≤ y` then `2^{q + 8x + 11y} ≤ 3^{5x + 7y}`.
From `(243·2187)/(256·2048) = 531441/524288` and `(531441/524288)^{64} ≥ 2`. -/
theorem fam_expand_det (x y q : ℕ) (hxy : x ≤ y) (hq : 64 * q ≤ y) :
    2 ^ (q + (8 * x + 11 * y)) ≤ 3 ^ (5 * x + 7 * y) := by
  have hA : 2 ^ q * 524288 ^ y ≤ 531441 ^ y := by
    have h64 : 2 * 524288 ^ 64 ≤ 531441 ^ 64 := by norm_num
    calc 2 ^ q * 524288 ^ y = 2 ^ q * 524288 ^ (64 * q) * 524288 ^ (y - 64 * q) := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hq]
      _ = (2 * 524288 ^ 64) ^ q * 524288 ^ (y - 64 * q) := by rw [mul_pow, ← pow_mul]
      _ ≤ (531441 ^ 64) ^ q * 531441 ^ (y - 64 * q) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left h64 _) (Nat.pow_le_pow_left (by norm_num) _)
      _ = 531441 ^ y := by rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hq]
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hxy
  have hB : 2048 ^ z * 531441 ^ z ≤ 2187 ^ z * 524288 ^ z := by
    rw [← mul_pow, ← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) _
  have e2 : 2 ^ (q + (8 * x + 11 * (x + z))) = 2 ^ q * 524288 ^ x * 2048 ^ z := by
    rw [show 8 * x + 11 * (x + z) = 19 * x + 11 * z by ring, pow_add, pow_add, pow_mul, pow_mul]
    norm_num
    ring
  have e3 : 3 ^ (5 * x + 7 * (x + z)) = 531441 ^ x * 2187 ^ z := by
    rw [show 5 * x + 7 * (x + z) = 12 * x + 7 * z by ring, pow_add, pow_mul, pow_mul]
    norm_num
  rw [e2, e3]
  have hP : 0 < 524288 ^ z * 531441 ^ z := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hP
  calc 2 ^ q * 524288 ^ x * 2048 ^ z * (524288 ^ z * 531441 ^ z)
      = (2 ^ q * 524288 ^ (x + z)) * (2048 ^ z * 531441 ^ z) := by rw [pow_add]; ring
    _ ≤ 531441 ^ (x + z) * (2187 ^ z * 524288 ^ z) := Nat.mul_le_mul hA hB
    _ = 531441 ^ x * 2187 ^ z * (524288 ^ z * 531441 ^ z) := by rw [pow_add]; ring

/-- The deterministic part: if the remaining blocks `β` satisfy `2 #X' ≤ k` and `k ≥ 256 s + 255` (`s = |σ₀|`), then the whole sequence
`β₀ ++ β` satisfies `2^{m + ⌈k/256⌉} ≤ 3^a`. -/
theorem fam_expand_event (β₀ β : List Bool) (hk : 256 * (parityOf β₀).length + 255 ≤ β.length)
    (hx : 2 * β.count true ≤ β.length) :
    2 ^ ((parityOf (β₀ ++ β)).length + ⌈(1 / 256 : ℚ) * β.length⌉₊)
      ≤ 3 ^ terrasA (parityOf (β₀ ++ β)) := by
  set C := ⌈(1 / 256 : ℚ) * β.length⌉₊ with hC
  have hC1 : (C : ℚ) < (1 / 256 : ℚ) * β.length + 1 := Nat.ceil_lt_add_one (by positivity)
  have hC2 : 256 * C < β.length + 256 := by
    have : (256 * C : ℚ) < β.length + 256 := by linarith
    exact_mod_cast this
  obtain ⟨h1, h2, _⟩ := fam_parityOf_counts β
  have hl := fam_length_eq_count β
  rw [fam_parityOf_append, List.length_append, terrasA_append, h1, terrasA_eq (parityOf β), h2]
  have hdet := fam_expand_det (β.count true) (β.count false) ((parityOf β₀).length + C)
    (by omega) (by omega)
  calc 2 ^ ((parityOf β₀).length + (8 * β.count true + 11 * β.count false) + C)
      = 2 ^ ((parityOf β₀).length + C + (8 * β.count true + 11 * β.count false)) := by
        congr 1; ring
    _ ≤ 3 ^ (5 * β.count true + 7 * β.count false) := hdet
    _ ≤ 3 ^ (terrasA (parityOf β₀) + (5 * β.count true + 7 * β.count false)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)

/-! ## Moments of the weights of block sequences -/

theorem fam_mem_blockChoices (β : List Bool) (k : ℕ) : β ∈ blockChoices k ↔ β.length = k := by
  unfold blockChoices
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨g, rfl⟩; simp
  · intro h; subst h; exact ⟨β.get, List.ofFn_get β⟩

theorem fam_blockChoices_succ (k : ℕ) :
    blockChoices (k + 1)
      = (blockChoices k).image (List.cons true) ∪ (blockChoices k).image (List.cons false) := by
  ext β
  simp only [Finset.mem_union, Finset.mem_image, fam_mem_blockChoices]
  cases β with
  | nil => simp
  | cons x β => cases x <;> simp

/-- Split a sum over length `k + 1` at the first block. -/
theorem fam_sum_succ (k : ℕ) (f : List Bool → ℚ) :
    ∑ β ∈ blockChoices (k + 1), f β
      = ∑ β ∈ blockChoices k, f (true :: β) + ∑ β ∈ blockChoices k, f (false :: β) := by
  rw [fam_blockChoices_succ, Finset.sum_union, Finset.sum_image, Finset.sum_image]
  · intro a _ b _ h; exact List.cons_injective h
  · intro a _ b _ h; exact List.cons_injective h
  · rw [Finset.disjoint_left]
    intro β h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨a, _, rfl⟩ := h1
    obtain ⟨b, _, h⟩ := h2
    simp at h

lemma fam_wt_cons (x : Bool) (β : List Bool) :
    wtβ (x :: β) = (if x then (3 / 10 : ℚ) else 7 / 10) * wtβ β := by
  simp [wtβ]

lemma fam_wt_nonneg (β : List Bool) : 0 ≤ wtβ β := by
  unfold wtβ
  apply List.prod_nonneg
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨x, _, rfl⟩ := ha
  split_ifs <;> norm_num

/-- Total weight, first and second moments: `Σ w = 1`, `Σ w X = 3k/10`, `Σ w X² = 21k/100 + 9k²/100` (`X = #X'`). -/
theorem fam_moments (k : ℕ) :
    ∑ β ∈ blockChoices k, wtβ β = 1 ∧
    ∑ β ∈ blockChoices k, wtβ β * (β.count true : ℚ) = 3 * k / 10 ∧
    ∑ β ∈ blockChoices k, wtβ β * (β.count true : ℚ) ^ 2 = 21 * k / 100 + 9 * k ^ 2 / 100 := by
  induction k with
  | zero =>
    have : blockChoices 0 = {[]} := by
      ext β; simp [fam_mem_blockChoices]
    simp [this, wtβ]
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have c1 : ∀ β : List Bool, (true :: β).count true = β.count true + 1 := by intro β; simp
    have c2 : ∀ β : List Bool, (false :: β).count true = β.count true := by intro β; simp
    simp only [fam_sum_succ, fam_wt_cons, c1, c2, ite_true, Bool.false_eq_true, ite_false]
    push_cast
    refine ⟨?_, ?_, ?_⟩
    · rw [← Finset.mul_sum, ← Finset.mul_sum, h0]; norm_num
    · have e1 : ∀ β : List Bool, 3 / 10 * wtβ β * ((β.count true : ℚ) + 1)
          = 3 / 10 * (wtβ β * (β.count true : ℚ)) + 3 / 10 * wtβ β := by intro β; ring
      have e2 : ∀ β : List Bool, 7 / 10 * wtβ β * (β.count true : ℚ)
          = 7 / 10 * (wtβ β * (β.count true : ℚ)) := by intro β; ring
      simp only [e1, e2, Finset.sum_add_distrib, ← Finset.mul_sum, h0, h1]
      ring
    · have e1 : ∀ β : List Bool, 3 / 10 * wtβ β * ((β.count true : ℚ) + 1) ^ 2
          = 3 / 10 * (wtβ β * (β.count true : ℚ) ^ 2) + 3 / 5 * (wtβ β * (β.count true : ℚ))
            + 3 / 10 * wtβ β := by intro β; ring
      have e2 : ∀ β : List Bool, 7 / 10 * wtβ β * (β.count true : ℚ) ^ 2
          = 7 / 10 * (wtβ β * (β.count true : ℚ) ^ 2) := by intro β; ring
      simp only [e1, e2, Finset.sum_add_distrib, ← Finset.mul_sum, h0, h1, h2]
      ring

/-- Variance: `Σ w (X - 3k/10)² = 21k/100`. -/
theorem fam_variance (k : ℕ) :
    ∑ β ∈ blockChoices k, wtβ β * ((β.count true : ℚ) - 3 * k / 10) ^ 2 = (21 * k / 100 : ℚ) := by
  obtain ⟨h0, h1, h2⟩ := fam_moments k
  have e : ∀ β : List Bool, wtβ β * ((β.count true : ℚ) - 3 * k / 10) ^ 2
      = wtβ β * (β.count true : ℚ) ^ 2 - 2 * (3 * (k : ℚ) / 10) * (wtβ β * (β.count true : ℚ))
        + (3 * (k : ℚ) / 10) ^ 2 * wtβ β := by intro β; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h0, h1, h2]
  ring

/-! ## (7) The law of large numbers for the expansion -/

/-- Lower bound on `Prσ`: if the weight on the bad event is bounded above by `g` and `Σ g ≤ B`, then the probability is at least `1 - B`
(the total weight is 1). -/
theorem fam_pr_ge (β₀ : List Bool) (k : ℕ) (E : List Bool → Prop) (g : List Bool → ℚ) (B : ℚ)
    (hg0 : ∀ β ∈ blockChoices k, 0 ≤ g β)
    (hg : ∀ β ∈ blockChoices k, ¬ E (β₀ ++ β) → wtβ β ≤ g β)
    (hB : ∑ β ∈ blockChoices k, g β ≤ B) :
    1 - B ≤ Prσ β₀ k E := by
  classical
  unfold Prσ
  have h := Finset.sum_filter_add_sum_filter_not (blockChoices k) (fun β => E (β₀ ++ β)) wtβ
  rw [(fam_moments k).1] at h
  have h1 : ∑ β ∈ (blockChoices k).filter (fun β => ¬ E (β₀ ++ β)), wtβ β
      ≤ ∑ β ∈ (blockChoices k).filter (fun β => ¬ E (β₀ ++ β)), g β := by
    apply Finset.sum_le_sum
    intro β hβ
    rw [Finset.mem_filter] at hβ
    exact hg β hβ.1 hβ.2
  have h2 : ∑ β ∈ (blockChoices k).filter (fun β => ¬ E (β₀ ++ β)), g β
      ≤ ∑ β ∈ blockChoices k, g β :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun β hβ _ => hg0 β hβ)
  linarith

/-- **(7) The law of large numbers for the expansion**: with `c = 1/256` and the initial blocks `β₀` fixed, with probability at least `1 - ε`,
`2^{m + ⌈ck⌉} ≤ 3^a` (it holds deterministically on the event `#X' ≤ k/2`, whose probability is bounded by Chebyshev). -/
theorem fam_expansion_lln : ∃ c : ℚ, 0 < c ∧ ∀ (β₀ : List Bool) (ε : ℚ), 0 < ε → ∃ k₀ : ℕ,
    ∀ k ≥ k₀, 1 - ε ≤ Prσ β₀ k (fun β =>
      2 ^ ((parityOf β).length + ⌈c * k⌉₊) ≤ 3 ^ terrasA (parityOf β)) := by
  refine ⟨1 / 256, by norm_num, ?_⟩
  intro β₀ ε hε
  refine ⟨max (256 * (parityOf β₀).length + 256) (⌈21 / (4 * ε)⌉₊ + 1), ?_⟩
  intro k hk
  have hk1 : 256 * (parityOf β₀).length + 256 ≤ k := le_of_max_le_left hk
  have hk2 : ⌈21 / (4 * ε)⌉₊ + 1 ≤ k := le_of_max_le_right hk
  have hkq : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk2' : 21 / (4 * ε) < k := by
    have h1 := Nat.le_ceil (21 / (4 * ε))
    have h2 : ((⌈21 / (4 * ε)⌉₊ + 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast hk2
    push_cast at h2
    linarith
  set D : List Bool → ℚ := fun β => ((β.count true : ℚ) - 3 * k / 10) ^ 2 * (25 / (k : ℚ) ^ 2)
    with hD
  apply fam_pr_ge β₀ k _ (fun β => wtβ β * D β) ε
  · intro β _
    exact mul_nonneg (fam_wt_nonneg β) (by rw [hD]; positivity)
  · intro β hβ hbad
    rw [fam_mem_blockChoices] at hβ
    apply le_mul_of_one_le_right (fam_wt_nonneg β)
    -- on the bad event, `2 #X' > k`
    have hx : k < 2 * β.count true := by
      by_contra hc
      apply hbad
      have := fam_expand_event β₀ β (by omega) (by omega)
      rwa [hβ] at this
    have hxq : (k : ℚ) + 1 ≤ 2 * (β.count true : ℚ) := by exact_mod_cast hx
    have hpos : (k : ℚ) / 5 ≤ (β.count true : ℚ) - 3 * k / 10 := by linarith
    have hsq : ((k : ℚ) / 5) ^ 2 ≤ ((β.count true : ℚ) - 3 * k / 10) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hpos 2
    rw [hD]
    simp only
    rw [← mul_div_assoc, one_le_div₀ (by positivity)]
    nlinarith
  calc _ = 21 * k / 100 * (25 / (k : ℚ) ^ 2) := by
        rw [hD, ← fam_variance k, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro β _
        ring
    _ ≤ ε := by
        rw [div_lt_iff₀ (by positivity)] at hk2'
        rw [show (21 * k / 100 * (25 / (k : ℚ) ^ 2)) = 21 / (4 * k) by field_simp; ring]
        rw [div_le_iff₀ (by positivity)]
        linarith

end Collatz.Arctic
