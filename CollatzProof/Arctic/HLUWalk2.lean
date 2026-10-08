/-
The probabilistic half of the probabilistic part of the hypothesis `HLeftUse` and the main theorem `walk_equid`. The deterministic half
(irrationality of `log₂ 3`, the finite form of density `walk_dense`, the window count `walk_count_ge`) is in `HLUWalk.lean`.

Correspondence with the paper: Proposition B.9 (i). The log of the mantissa of the block boundary points is `{a_{≤i} log₂3 + log₂t}`, and the random walk
must enter each of the three intervals at least `c'k` times, for every `t`.
Instead of bounding the discrepancy by Weyl (Fourier) sums, we only need a lower bound, which the following window argument gives.
* `walk_sum_append`: the weight of a block choice is a product, so a sum over length `a + m` splits into the first `a` blocks and the rest (independence).
* `walk_Y_moments`: among `W` disjoint windows (of length `B`), the number `Y_W` of windows consisting of `Y'` only has mean `Wq`
  and variance `W(q - q²)` (`q = (7/10)^B`).
* `walk_equid`: take the `B` of `walk_dense` and `W = ⌊k/B⌋`. By Chebyshev, `Y_W ≥ Wq/2` with probability at least `1 - ε`;
  on that event, by `walk_count_ge`, for every `φ` at least `Y_W ≥ qk/(4B)` indices lie in the arc. `c = q/(4B)` depends only on `lo`, `hi`
  (`B` is determined by `lo`, `hi` and `log₂ 3` only).
-/
import CollatzProof.Arctic.HLUWalk

namespace Collatz.Arctic

/-! ## Splitting sums over independent blocks -/

/-- Split a sum over block choices of length `a + m` into the first `a` blocks and the remaining `m` blocks (independence). -/
theorem walk_sum_append (a m : ℕ) (F G : List Bool → ℚ) :
    ∑ β ∈ blockChoices (a + m), wtβ β * (F (β.take a) * G (β.drop a)) =
      (∑ β ∈ blockChoices a, wtβ β * F β) * (∑ β ∈ blockChoices m, wtβ β * G β) := by
  induction a generalizing F with
  | zero =>
    have h0 : blockChoices 0 = {[]} := by
      ext β
      simp [fam_mem_blockChoices]
    rw [Nat.zero_add, h0, Finset.sum_singleton, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    simp [wtβ]
    ring
  | succ a ih =>
    rw [show a + 1 + m = (a + m) + 1 by omega, fam_sum_succ, fam_sum_succ]
    have L : ∀ x : Bool, ∑ β ∈ blockChoices (a + m),
        wtβ (x :: β) * (F ((x :: β).take (a + 1)) * G ((x :: β).drop (a + 1)))
        = (if x then (3 / 10 : ℚ) else 7 / 10) *
          ((∑ β ∈ blockChoices a, wtβ β * F (x :: β)) * ∑ β ∈ blockChoices m, wtβ β * G β) := by
      intro x
      rw [← ih (fun β => F (x :: β)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      rw [List.take_succ_cons, List.drop_succ_cons, fam_wt_cons]
      ring
    have R : ∀ x : Bool, ∑ β ∈ blockChoices a, wtβ (x :: β) * F (x :: β)
        = (if x then (3 / 10 : ℚ) else 7 / 10) * ∑ β ∈ blockChoices a, wtβ β * F (x :: β) := by
      intro x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      rw [fam_wt_cons]
      ring
    rw [L true, L false, R true, R false]
    simp only [↓reduceIte, Bool.false_eq_true]
    ring

/-- Sum of a quantity depending only on the first `a` blocks. -/
theorem walk_sum_take (a m : ℕ) (F : List Bool → ℚ) :
    ∑ β ∈ blockChoices (a + m), wtβ β * F (β.take a) = ∑ β ∈ blockChoices a, wtβ β * F β := by
  have h := walk_sum_append a m F (fun _ => 1)
  simp only [mul_one] at h
  rw [h, (fam_moments m).1, mul_one]

/-- Sum of a quantity depending only on the blocks after the first `a`. -/
theorem walk_sum_drop (a m : ℕ) (G : List Bool → ℚ) :
    ∑ β ∈ blockChoices (a + m), wtβ β * G (β.drop a) = ∑ β ∈ blockChoices m, wtβ β * G β := by
  have h := walk_sum_append a m (fun _ => 1) G
  simp only [one_mul, mul_one] at h
  rw [h, (fam_moments a).1, one_mul]

/-! ## Moments of the number of windows consisting of `Y'` only -/

/-- Indicator that all blocks are `Y'` (`false`). -/
def walkInd (β : List Bool) : ℚ := if β.count true = 0 then 1 else 0

/-- The probability that a block choice of length `B` consists of `Y'` only is `(7/10)^B`. -/
theorem walk_ind_sum (B : ℕ) :
    ∑ β ∈ blockChoices B, wtβ β * walkInd β = (7 / 10 : ℚ) ^ B := by
  induction B with
  | zero =>
    have h0 : blockChoices 0 = {[]} := by
      ext β
      simp [fam_mem_blockChoices]
    simp [h0, wtβ, walkInd]
  | succ B ih =>
    rw [fam_sum_succ]
    have e1 : ∀ β : List Bool, wtβ (true :: β) * walkInd (true :: β) = 0 := by
      intro β
      simp [walkInd]
    have e2 : ∀ β : List Bool, wtβ (false :: β) * walkInd (false :: β)
        = 7 / 10 * (wtβ β * walkInd β) := by
      intro β
      simp only [walkInd, fam_wt_cons, List.count_cons, Bool.false_eq_true, ↓reduceIte]
      simp
    simp only [e1, e2, Finset.sum_const_zero, zero_add, ← Finset.mul_sum, ih, pow_succ]
    ring

/-- The number of windows consisting of `Y'` only, `Y_W(β) := #{w < W : the window [wB, wB + B) is all Y'}` (rational-valued). -/
def walkY (B W : ℕ) (β : List Bool) : ℚ :=
  ∑ w ∈ Finset.range W, walkInd ((β.drop (w * B)).take B)

theorem walk_Y_eq_card (B W : ℕ) (β : List Bool) :
    walkY B W β = (((Finset.range W).filter (walkGood B β)).card : ℚ) := by
  unfold walkY walkInd
  rw [Finset.sum_boole]
  rfl

/-- Split off the first window: `Y_{W+1}(β) = 1[the first B blocks are all Y'] + Y_W(rest of β)`. -/
theorem walk_Y_succ (B W : ℕ) (β : List Bool) :
    walkY B (W + 1) β = walkInd (β.take B) + walkY B W (β.drop B) := by
  unfold walkY
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro w _
    rw [List.drop_drop, show B + w * B = (w + 1) * B by ring]

/-- **Moments**: if `W B ≤ n`, then `Y_W` has mean `Wq` and variance `W(q - q²)` (`q = (7/10)^B`). -/
theorem walk_Y_moments (B W : ℕ) : ∀ n, W * B ≤ n →
    ∑ β ∈ blockChoices n, wtβ β * (walkY B W β - W * (7 / 10 : ℚ) ^ B) = 0 ∧
    ∑ β ∈ blockChoices n, wtβ β * (walkY B W β - W * (7 / 10 : ℚ) ^ B) ^ 2
      = W * ((7 / 10 : ℚ) ^ B - ((7 / 10 : ℚ) ^ B) ^ 2) := by
  induction W with
  | zero =>
    intro n _
    simp [walkY]
  | succ W ih =>
    intro n hn
    rw [add_one_mul] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = B + m := ⟨n - B, by omega⟩
    obtain ⟨g1, g2⟩ := ih m (by omega)
    set q : ℚ := (7 / 10 : ℚ) ^ B with hq
    -- mean and variance of the indicator of the first window
    have hw1 := (fam_moments B).1
    have f1 : ∑ β ∈ blockChoices B, wtβ β * (walkInd β - q) = 0 := by
      have e : ∀ β, wtβ β * (walkInd β - q) = wtβ β * walkInd β - q * wtβ β := by
        intro β; ring
      simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, walk_ind_sum, hw1]
      ring
    have f2 : ∑ β ∈ blockChoices B, wtβ β * (walkInd β - q) ^ 2 = q - q ^ 2 := by
      have e : ∀ β, wtβ β * (walkInd β - q) ^ 2
          = (1 - 2 * q) * (wtβ β * walkInd β) + q ^ 2 * wtβ β := by
        intro β
        unfold walkInd
        split_ifs <;> ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, walk_ind_sum, hw1]
      ring
    -- split into the first window and the rest
    have hpt : ∀ β : List Bool, walkY B (W + 1) β - ((W + 1 : ℕ) : ℚ) * q
        = (walkInd (β.take B) - q) + (walkY B W (β.drop B) - W * q) := by
      intro β
      rw [walk_Y_succ]
      push_cast
      ring
    have t1 : ∑ β ∈ blockChoices (B + m), wtβ β * (walkInd (β.take B) - q)
        = ∑ β ∈ blockChoices B, wtβ β * (walkInd β - q) :=
      walk_sum_take B m (fun β => walkInd β - q)
    have t2 : ∑ β ∈ blockChoices (B + m), wtβ β * (walkY B W (β.drop B) - W * q)
        = ∑ β ∈ blockChoices m, wtβ β * (walkY B W β - W * q) :=
      walk_sum_drop B m (fun β => walkY B W β - W * q)
    have t3 : ∑ β ∈ blockChoices (B + m), wtβ β * (walkInd (β.take B) - q) ^ 2
        = ∑ β ∈ blockChoices B, wtβ β * (walkInd β - q) ^ 2 :=
      walk_sum_take B m (fun β => (walkInd β - q) ^ 2)
    have t4 : ∑ β ∈ blockChoices (B + m),
        wtβ β * ((walkInd (β.take B) - q) * (walkY B W (β.drop B) - W * q))
        = (∑ β ∈ blockChoices B, wtβ β * (walkInd β - q)) *
          ∑ β ∈ blockChoices m, wtβ β * (walkY B W β - W * q) :=
      walk_sum_append B m (fun β => walkInd β - q) (fun β => walkY B W β - W * q)
    have t5 : ∑ β ∈ blockChoices (B + m), wtβ β * (walkY B W (β.drop B) - W * q) ^ 2
        = ∑ β ∈ blockChoices m, wtβ β * (walkY B W β - W * q) ^ 2 :=
      walk_sum_drop B m (fun β => (walkY B W β - W * q) ^ 2)
    constructor
    · have e : ∀ β : List Bool, wtβ β * (walkY B (W + 1) β - ((W + 1 : ℕ) : ℚ) * q)
          = wtβ β * (walkInd (β.take B) - q) + wtβ β * (walkY B W (β.drop B) - W * q) := by
        intro β
        rw [hpt]
        ring
      rw [Finset.sum_congr rfl (fun β _ => e β), Finset.sum_add_distrib, t1, t2, f1, g1]
      ring
    · have e : ∀ β : List Bool, wtβ β * (walkY B (W + 1) β - ((W + 1 : ℕ) : ℚ) * q) ^ 2
          = wtβ β * (walkInd (β.take B) - q) ^ 2
            + 2 * (wtβ β * ((walkInd (β.take B) - q) * (walkY B W (β.drop B) - W * q)))
            + wtβ β * (walkY B W (β.drop B) - W * q) ^ 2 := by
        intro β
        rw [hpt]
        ring
      rw [Finset.sum_congr rfl (fun β _ => e β), Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, t3, t4, t5, f2, f1, g2]
      push_cast
      ring

/-! ## Main theorem -/

/-- **Finite form of the equidistribution of the random walk** (the probabilistic part of `HLeftUse`): for an arc `[lo, hi)` (`0 ≤ lo < hi ≤ 1`)
there is `c > 0` depending only on `lo`, `hi` such that, for a fixed initial block sequence `β₀`, for large `k`, with probability at least `1 - ε`,
**for every `φ`**, at least `ck` of the indices `i < |β|` of the whole block choice `β` satisfy `{a_i log₂3 + φ} ∈ [lo, hi)`
(`a_i = oddPrefix β i`). -/
theorem walk_equid (lo hi : ℝ) (h0 : 0 ≤ lo) (hlh : lo < hi) (h1 : hi ≤ 1) :
    ∃ c : ℚ, 0 < c ∧ ∀ (β₀ : List Bool) (ε : ℚ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      1 - ε ≤ Prσ β₀ k (fun β => ∀ φ : ℝ, (c : ℝ) * k ≤
        (((Finset.range β.length).filter (fun i =>
          lo ≤ Int.fract ((oddPrefix β i : ℝ) * Real.logb 2 3 + φ) ∧
          Int.fract ((oddPrefix β i : ℝ) * Real.logb 2 3 + φ) < hi)).card : ℝ)) := by
  obtain ⟨B, hB⟩ := walk_dense _ walk_irrational_seven lo hi h0 hlh h1
  have hBpos : 0 < B := by
    obtain ⟨j, hj, -⟩ := hB 0
    omega
  have hBq : (0 : ℚ) < B := by exact_mod_cast hBpos
  set q : ℚ := (7 / 10 : ℚ) ^ B with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨q / (4 * B), by positivity, ?_⟩
  intro β₀ ε hε
  refine ⟨B * (⌈4 / (q * ε)⌉₊ + 1), ?_⟩
  intro k hk
  set W := k / B with hW
  have hWB : W * B ≤ k := Nat.div_mul_le_self k B
  have hkW : k < W * B + B := by
    have e1 := Nat.div_add_mod k B
    have e2 := Nat.mod_lt k hBpos
    rw [mul_comm, ← hW] at e1
    omega
  have hW1 : ⌈4 / (q * ε)⌉₊ + 1 ≤ W :=
    (Nat.le_div_iff_mul_le hBpos).mpr (by rw [mul_comm]; exact hk)
  have hWq : (1 : ℚ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hW4 : 4 / (q * ε) < W := by
    have e1 := Nat.le_ceil (4 / (q * ε))
    have e2 : ((⌈4 / (q * ε)⌉₊ + 1 : ℕ) : ℚ) ≤ W := by exact_mod_cast hW1
    push_cast at e2
    linarith
  have hmom := (walk_Y_moments B W k hWB).2
  rw [← hq] at hmom
  apply fam_pr_ge β₀ k _ (fun β => wtβ β * ((walkY B W β - W * q) ^ 2 * (4 / (W * q) ^ 2))) ε
  · intro β _
    exact mul_nonneg (fam_wt_nonneg β) (by positivity)
  · intro β hβ hbad
    rw [fam_mem_blockChoices] at hβ
    -- on the bad event `Y_W < Wq/2`
    have hY : walkY B W β < W * q / 2 := by
      by_contra hc
      push Not at hc
      apply hbad
      intro φ
      have hcnt := walk_count_ge lo hi B hB β₀ β W (by omega) φ
      have hck : q / (4 * B) * k ≤ W * q / 2 := by
        have hk2 : (k : ℚ) ≤ 2 * W * B := by
          have : (k : ℚ) < W * B + B := by exact_mod_cast hkW
          nlinarith
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have key : q / (4 * B) * k ≤ (((Finset.range W).filter (walkGood B β)).card : ℚ) := by
        rw [← walk_Y_eq_card]
        linarith
      have key' : ((q / (4 * B) * k : ℚ) : ℝ)
          ≤ ((((Finset.range W).filter (walkGood B β)).card : ℕ) : ℝ) := by
        exact_mod_cast key
      calc ((q / (4 * B) : ℚ) : ℝ) * k = ((q / (4 * B) * k : ℚ) : ℝ) := by push_cast; ring
        _ ≤ _ := key'
        _ ≤ _ := by exact_mod_cast hcnt
    apply le_mul_of_one_le_right (fam_wt_nonneg β)
    have hWq0 : (0 : ℚ) < W * q := by positivity
    have ha : walkY B W β - W * q / 2 < 0 := by linarith
    have hb : walkY B W β - 3 * (W * q) / 2 < 0 := by linarith
    have hsq : (W * q / 2) ^ 2 ≤ (walkY B W β - W * q) ^ 2 := by
      nlinarith [mul_pos_of_neg_of_neg ha hb]
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith
  · -- Chebyshev: `Σ g = W(q - q²)·4/(Wq)² ≤ 4/(Wq) ≤ ε`
    have hsum : ∑ β ∈ blockChoices k, wtβ β * ((walkY B W β - W * q) ^ 2 * (4 / (W * q) ^ 2))
        = (∑ β ∈ blockChoices k, wtβ β * (walkY B W β - W * q) ^ 2) * (4 / (W * q) ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro β _
      ring
    rw [hsum, hmom]
    have hWpos : (0 : ℚ) < W := by linarith
    have e : (W : ℚ) * (q - q ^ 2) * (4 / (W * q) ^ 2) = 4 * (1 - q) / (W * q) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have : 4 < W * (q * ε) := by
      rwa [div_lt_iff₀ (by positivity)] at hW4
    nlinarith

end Collatz.Arctic
