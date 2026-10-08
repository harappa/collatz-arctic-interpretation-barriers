/-
The deterministic half of the probabilistic part of the hypothesis `HLeftUse`: a lower bound on the number of times the random walk
`a_i θ` (`a_i := oddPrefix β i`) with steps `5θ`, `7θ` (`θ = log₂ 3`) enters the arc `[lo, hi)`.

Correspondence with the paper: Proposition B.9 (i). The log of the mantissa of the block boundary points is `{a_{≤i} log₂3 + log₂t}`, and the random walk
must enter each of the three intervals at least `c'k` times, for every `t`.

Instead of a discrepancy (Fourier) estimate we use the following window argument (it directly gives the form holding simultaneously for all `φ = log₂ t`).
* `walk_irrational_logb`: `log₂ 3` is irrational (parity of `3^b = 2^a`).
* `walk_dense`: for irrational `α` there is `B` such that, from every `y`, the fractional part of some `y + jα` (`j < B`)
  lies in the arc `[lo, hi)` (Dirichlet's approximation theorem `|qα - p| < hi - lo` and the arithmetic progression with step `qα - p`).
* `walk_count_ge`: if the window `[wB, wB + B)` of block indices consists of `Y'` only (`false`, 7 odd steps), then inside the window
  `a_i θ + φ` moves as `y + j·7θ`, so for every `φ` the window contains an index in the arc. Hence the number of indices in the arc
  is at least the number of windows consisting of `Y'` only (independent of `φ`).
The probabilistic half (the law of large numbers for the number of windows consisting of `Y'` only, and the main theorem `walk_equid`) is in `HLUWalk2.lean`.
-/
import CollatzProof.Arctic.FamilyExp

namespace Collatz.Arctic

/-! ## `log₂ 3` is irrational -/

theorem walk_irrational_logb : Irrational (Real.logb 2 3) := by
  rw [irrational_iff_ne_rational]
  intro a b hb h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : (b : ℝ) * Real.log 3 = a * Real.log 2 := by
    rw [Real.logb, div_eq_div_iff hl2.ne' (by exact_mod_cast hb)] at h
    linarith
  have h2 : (b.natAbs : ℝ) * Real.log 3 = a.natAbs * Real.log 2 := by
    have := congrArg abs h1
    rw [abs_mul, abs_mul, abs_of_pos hl2, abs_of_pos hl3] at this
    rw [Nat.cast_natAbs, Nat.cast_natAbs]
    push_cast
    exact this
  have h3 : ((3 ^ b.natAbs : ℕ) : ℝ) = ((2 ^ a.natAbs : ℕ) : ℝ) := by
    push_cast
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_pow, Real.log_pow, h2]
  have h4 : 3 ^ b.natAbs = 2 ^ a.natAbs := by exact_mod_cast h3
  have hn : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
  rcases Nat.eq_zero_or_pos a.natAbs with hm | hm
  · rw [hm, pow_zero] at h4
    exact hn ((Nat.pow_eq_one.mp h4).resolve_left (by norm_num))
  · have h5 : 2 ∣ 3 ^ b.natAbs := h4 ▸ dvd_pow_self 2 hm.ne'
    have : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h5
    omega

/-- `7 log₂ 3` is irrational (one step `Y'`). -/
theorem walk_irrational_seven : Irrational (7 * Real.logb 2 3) := by
  have := walk_irrational_logb.natCast_mul (m := 7) (by norm_num)
  simpa using this

/-! ## Arithmetic progressions enter the arc -/

/-- A sequence moving up by the step `s` (`0 < s < hi - lo`) enters the arc `[lo, hi)` within `⌈1/s⌉₊` steps. -/
theorem walk_step_up (lo hi s y : ℝ) (h0 : 0 ≤ lo) (h1 : hi ≤ 1) (hs : 0 < s) (hsl : s < hi - lo) :
    ∃ i : ℕ, i ≤ ⌈1 / s⌉₊ ∧ lo ≤ Int.fract (y + i * s) ∧ Int.fract (y + i * s) < hi := by
  set m : ℤ := ⌈y - lo⌉ with hm
  have hm1 : y - lo ≤ m := Int.le_ceil _
  have hm2 : (m : ℝ) < y - lo + 1 := Int.ceil_lt_add_one _
  set x : ℝ := (lo + m - y) / s with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hs.le
  refine ⟨⌈x⌉₊, ?_, ?_⟩
  · apply Nat.ceil_mono
    rw [hx]
    exact div_le_div_of_nonneg_right (by linarith) hs.le
  have hc1 : x ≤ ⌈x⌉₊ := Nat.le_ceil x
  have hc2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have e1 : lo + m - y ≤ ⌈x⌉₊ * s := by
    have := mul_le_mul_of_nonneg_right hc1 hs.le
    rwa [hx, div_mul_cancel₀ _ hs.ne'] at this
  have e2 : (⌈x⌉₊ : ℝ) * s < lo + m - y + s := by
    have := mul_lt_mul_of_pos_right hc2 hs
    rwa [add_mul, hx, div_mul_cancel₀ _ hs.ne', one_mul] at this
  have hfl : ⌊y + ⌈x⌉₊ * s⌋ = m := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  rw [← Int.self_sub_floor, hfl]
  constructor <;> linarith

/-- A sequence moving down by the step `-g` (`0 < g < hi - lo`) enters the arc `[lo, hi)` within `⌊1/g⌋₊ + 1` steps. -/
theorem walk_step_down (lo hi g y : ℝ) (h0 : 0 ≤ lo) (h1 : hi ≤ 1) (hg : 0 < g) (hgl : g < hi - lo) :
    ∃ i : ℕ, i ≤ ⌊1 / g⌋₊ + 1 ∧ lo ≤ Int.fract (y - i * g) ∧ Int.fract (y - i * g) < hi := by
  set m : ℤ := ⌊y - hi⌋ with hm
  have hm1 : (m : ℝ) ≤ y - hi := Int.floor_le _
  have hm2 : y - hi < m + 1 := Int.lt_floor_add_one _
  set x : ℝ := (y - hi - m) / g with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hg.le
  refine ⟨⌊x⌋₊ + 1, ?_, ?_⟩
  · have : ⌊x⌋₊ ≤ ⌊1 / g⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) hg.le)
    omega
  have hc1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hc2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have e1 : (⌊x⌋₊ : ℝ) * g ≤ y - hi - m := by
    have := mul_le_mul_of_nonneg_right hc1 hg.le
    rwa [hx, div_mul_cancel₀ _ hg.ne'] at this
  have e2 : y - hi - m < (⌊x⌋₊ : ℝ) * g + g := by
    have := mul_lt_mul_of_pos_right hc2 hg
    rwa [add_mul, hx, div_mul_cancel₀ _ hg.ne', one_mul] at this
  have e3 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) * g = (⌊x⌋₊ : ℝ) * g + g := by push_cast; ring
  have hfl : ⌊y - ((⌊x⌋₊ + 1 : ℕ) : ℝ) * g⌋ = m := by
    rw [Int.floor_eq_iff, e3]
    constructor <;> linarith
  rw [← Int.self_sub_floor, hfl, e3]
  constructor <;> linarith

/-- An arithmetic progression with step `s ≠ 0` (`|s| < hi - lo`) enters the arc `[lo, hi)` within `⌈1/|s|⌉₊ + 1` steps. -/
theorem walk_step (lo hi s y : ℝ) (h0 : 0 ≤ lo) (h1 : hi ≤ 1) (hs : s ≠ 0) (hsl : |s| < hi - lo) :
    ∃ i : ℕ, i ≤ ⌈1 / |s|⌉₊ + 1 ∧ lo ≤ Int.fract (y + i * s) ∧ Int.fract (y + i * s) < hi := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · rw [abs_of_neg hneg] at hsl ⊢
    obtain ⟨i, hi', h2⟩ := walk_step_down lo hi (-s) y h0 h1 (by linarith) hsl
    refine ⟨i, le_trans hi' (by have := Nat.floor_le_ceil (1 / -s); omega), ?_⟩
    have e : y + i * s = y - i * -s := by ring
    rw [e]
    exact h2
  · rw [abs_of_pos hpos] at hsl ⊢
    obtain ⟨i, hi', h2⟩ := walk_step_up lo hi s y h0 h1 hpos hsl
    exact ⟨i, by omega, h2⟩

/-- **A finite form of density**: for irrational `α` there is `B` such that, from every `y`, the fractional part of some
`y + jα` (`j < B`) lies in the arc `[lo, hi)` (Dirichlet's approximation theorem). -/
theorem walk_dense (α : ℝ) (hα : Irrational α) (lo hi : ℝ) (h0 : 0 ≤ lo) (hlh : lo < hi)
    (h1 : hi ≤ 1) :
    ∃ B : ℕ, ∀ y : ℝ, ∃ j < B, lo ≤ Int.fract (y + j * α) ∧ Int.fract (y + j * α) < hi := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlh)
  obtain ⟨q, hq0, -, hq⟩ := Real.exists_nat_abs_mul_sub_round_le α (Nat.succ_pos n)
  set s : ℝ := (q : ℝ) * α - round ((q : ℝ) * α) with hs
  have hs0 : s ≠ 0 := by
    intro h
    exact (hα.natCast_mul hq0.ne').ne_int (round ((q : ℝ) * α)) (by rw [hs] at h; linarith)
  have hsl : |s| < hi - lo := by
    calc |s| ≤ 1 / (((n + 1 : ℕ) : ℝ) + 1) := hq
      _ ≤ 1 / ((n : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          push_cast
          linarith
      _ < hi - lo := hn
  refine ⟨(⌈1 / |s|⌉₊ + 2) * q, fun y => ?_⟩
  obtain ⟨i, hi', hlo, hhi⟩ := walk_step lo hi s y h0 h1 hs0 hsl
  refine ⟨i * q, Nat.mul_lt_mul_of_pos_right (by omega) hq0, ?_⟩
  have e : y + ((i * q : ℕ) : ℝ) * α = (y + i * s) + ((i * round ((q : ℝ) * α) : ℤ) : ℝ) := by
    rw [hs]
    push_cast
    ring
  rw [e, Int.fract_add_intCast]
  exact ⟨hlo, hhi⟩

/-! ## Prefix sums of the numbers of odd steps -/

/-- The number of odd steps of the first `i` blocks of the block choice `β` (5 for `X'` (true), 7 for `Y'` (false)). -/
def oddPrefix (β : List Bool) (i : ℕ) : ℕ := ((β.take i).map (fun x => if x then 5 else 7)).sum

/-- The sum of the numbers of odd steps and the number of `X'`: `Σ + 2·#X' = 7·length`. -/
theorem walk_sum_map (l : List Bool) :
    (l.map (fun x => if x then (5 : ℕ) else 7)).sum + 2 * l.count true = 7 * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => cases x <;> simp <;> omega

theorem walk_oddPrefix_append (β₀ β : List Bool) (i : ℕ) :
    oddPrefix (β₀ ++ β) (β₀.length + i) = oddPrefix β₀ β₀.length + oddPrefix β i := by
  unfold oddPrefix
  rw [List.take_length_add_append, List.take_length, List.map_append, List.sum_append]

theorem walk_oddPrefix_add (β : List Bool) (a j : ℕ) :
    oddPrefix β (a + j) = oddPrefix β a + oddPrefix (β.drop a) j := by
  unfold oddPrefix
  rw [List.take_add, List.map_append, List.sum_append]

/-- If the first `B` blocks are all `Y'`, the number of odd steps of the first `j ≤ B` blocks is `7j`. -/
theorem walk_oddPrefix_allY (γ : List Bool) (B j : ℕ) (h : (γ.take B).count true = 0)
    (hj : j ≤ B) (hl : j ≤ γ.length) : oddPrefix γ j = 7 * j := by
  have h1 := walk_sum_map (γ.take j)
  have h2 : (γ.take j).count true = 0 := by
    have hs : (γ.take j).Sublist (γ.take B) := by
      have e : γ.take j = (γ.take B).take j := by rw [List.take_take, Nat.min_eq_left hj]
      rw [e]
      exact List.take_sublist _ _
    have := hs.count_le true
    omega
  have h3 : (γ.take j).length = j := by rw [List.length_take]; omega
  unfold oddPrefix
  omega

/-! ## Deterministic lower bound on the number of indices in the arc -/

/-- The window `w` (the blocks with indices `[wB, wB + B)`) consists of `Y'` (`false`) only. -/
def walkGood (B : ℕ) (β : List Bool) (w : ℕ) : Prop := ((β.drop (w * B)).take B).count true = 0

instance walkGood.decPred (B : ℕ) (β : List Bool) : DecidablePred (walkGood B β) :=
  fun w => inferInstanceAs (Decidable (((β.drop (w * B)).take B).count true = 0))

/-- **Deterministic lower bound on the number of indices in the arc**: under `hB` (the `B` of `walk_dense`), the number of windows
of the remaining blocks `β` (`W B ≤ |β|`) consisting of `Y'` only is at most the number of indices `i` of the whole `β₀ ++ β` for which the fractional part of `a_i θ + φ` lies in the arc `[lo, hi)`
(for every `φ`; inside a window `a_i θ + φ = y + j·7θ` moves). -/
theorem walk_count_ge (lo hi : ℝ) (B : ℕ)
    (hB : ∀ y : ℝ, ∃ j < B, lo ≤ Int.fract (y + j * (7 * Real.logb 2 3)) ∧
      Int.fract (y + j * (7 * Real.logb 2 3)) < hi)
    (β₀ β : List Bool) (W : ℕ) (hW : W * B ≤ β.length) (φ : ℝ) :
    ((Finset.range W).filter (walkGood B β)).card ≤
      ((Finset.range (β₀ ++ β).length).filter (fun i =>
        lo ≤ Int.fract ((oddPrefix (β₀ ++ β) i : ℝ) * Real.logb 2 3 + φ) ∧
        Int.fract ((oddPrefix (β₀ ++ β) i : ℝ) * Real.logb 2 3 + φ) < hi)).card := by
  choose J hJB hJ using hB
  set y : ℕ → ℝ := fun w =>
    ((oddPrefix β₀ β₀.length + oddPrefix β (w * B) : ℕ) : ℝ) * Real.logb 2 3 + φ with hy
  apply Finset.card_le_card_of_injOn (fun w => β₀.length + (w * B + J (y w)))
  · intro w hw
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwW, hgood⟩ := hw
    have hJw := hJB (y w)
    have hle : w * B + B ≤ W * B := by
      have := Nat.mul_le_mul_right B (show w + 1 ≤ W by omega)
      rwa [add_one_mul] at this
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    beta_reduce
    refine ⟨by rw [List.length_append]; omega, ?_⟩
    have ho : oddPrefix (β₀ ++ β) (β₀.length + (w * B + J (y w)))
        = oddPrefix β₀ β₀.length + oddPrefix β (w * B) + 7 * J (y w) := by
      rw [walk_oddPrefix_append, walk_oddPrefix_add,
        walk_oddPrefix_allY (β.drop (w * B)) B (J (y w)) hgood hJw.le
          (by rw [List.length_drop]; omega)]
      ring
    have e : ((oddPrefix (β₀ ++ β) (β₀.length + (w * B + J (y w))) : ℕ) : ℝ) * Real.logb 2 3 + φ
        = y w + (J (y w) : ℝ) * (7 * Real.logb 2 3) := by
      rw [ho, hy]
      push_cast
      ring
    rw [e]
    exact hJ (y w)
  · intro w _ v _ hwv
    simp only at hwv
    have hwJ := hJB (y w)
    have hvJ := hJB (y v)
    rcases lt_trichotomy w v with h | h | h
    · have := Nat.mul_le_mul_right B (show w + 1 ≤ v by omega)
      rw [add_one_mul] at this
      omega
    · exact h
    · have := Nat.mul_le_mul_right B (show v + 1 ≤ w by omega)
      rw [add_one_mul] at this
      omega

end Collatz.Arctic
