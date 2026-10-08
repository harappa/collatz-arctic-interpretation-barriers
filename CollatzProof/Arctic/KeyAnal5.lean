/-
Analytic ingredients of the swap argument (Appendix B.2), part 5: the Doeblin bound (`SpecDoeblin`; step (c) of the proof of Theorem B.7).

Let `Y_n` be the number of `Y'` (`false`, weight 7/10) among `n` blocks, `P_n(x) := Pr(Y_n ≡ x mod N)` (`x ∈ ℤ/N`),
and `D_n := Σ_x |P_n(x) - 1/N|` (twice the total variation distance). All computations are in `ℚ`; the result is moved to `ℝ` at the end.
* `ka_P_conv`: splitting into the first `N` blocks and the rest gives `P_{N+n} = P_N * P_n` (convolution modulo `N`, `HLUWalk2.walk_sum_append`).
* `ka_P_lower`: `P_N(x) ≥ (3/10)^N` (there is a sequence of `x` blocks `Y'` and `N - x` blocks `X'`).
* `ka_D_step`: `D_{N+n} ≤ (1 - N(3/10)^N) D_n` (from `P_N - (3/10)^N ≥ 0` and the fact that a convolution with the uniform law is uniform).
* `specDoeblin`: from `n = ⌊n/N⌋ N + (n mod N)` and `D_r ≤ 2`.
-/
import CollatzProof.Arctic.KeyAnal
import CollatzProof.Arctic.HLUWalk2

namespace Collatz.Arctic

open Finset

/-- `P_n(x) = Pr(Y_n ≡ x mod N)` (`Y_n` is the number of `Y'`). -/
noncomputable def kaP (N n : ℕ) (x : ZMod N) : ℚ :=
  ∑ β ∈ blockChoices n, wtβ β * (if ((β.count false : ℕ) : ZMod N) = x then 1 else 0)

/-- `D_n = Σ_x |P_n(x) - 1/N|`. -/
noncomputable def kaDist (N n : ℕ) [NeZero N] : ℚ := ∑ x : ZMod N, |kaP N n x - 1 / N|

lemma ka_P_nonneg (N n : ℕ) (x : ZMod N) : 0 ≤ kaP N n x :=
  sum_nonneg (fun β _ => mul_nonneg (fam_wt_nonneg β) (by split_ifs <;> norm_num))

lemma ka_P_total (N n : ℕ) [NeZero N] : ∑ x : ZMod N, kaP N n x = 1 := by
  unfold kaP
  rw [Finset.sum_comm]
  simp only [← mul_sum, sum_ite_eq, mem_univ, ite_true, mul_one]
  exact (fam_moments n).1

/-- The convolution obtained by splitting into the first `N` blocks and the rest. -/
lemma ka_P_conv (N n : ℕ) [NeZero N] (x : ZMod N) :
    kaP N (N + n) x = ∑ a : ZMod N, kaP N N a * kaP N n (x - a) := by
  have hsplit : ∀ β : List Bool, (if ((β.count false : ℕ) : ZMod N) = x then (1 : ℚ) else 0) =
      ∑ a : ZMod N, (if (((β.take N).count false : ℕ) : ZMod N) = a then 1 else 0) *
        (if (((β.drop N).count false : ℕ) : ZMod N) = x - a then 1 else 0) := by
    intro β
    have hc : β.count false = (β.take N).count false + (β.drop N).count false := by
      rw [← List.count_append, List.take_append_drop]
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    rw [hc, Nat.cast_add]
    exact if_congr ⟨fun h => by rw [← h]; ring, fun h => by rw [h]; ring⟩ rfl rfl
  have key : ∀ a : ZMod N, kaP N N a * kaP N n (x - a) = ∑ β ∈ blockChoices (N + n), wtβ β *
      ((if (((β.take N).count false : ℕ) : ZMod N) = a then 1 else 0) *
        (if (((β.drop N).count false : ℕ) : ZMod N) = x - a then 1 else 0)) := by
    intro a
    have h := walk_sum_append N n (fun β => if ((β.count false : ℕ) : ZMod N) = a then (1 : ℚ) else 0)
      (fun β => if ((β.count false : ℕ) : ZMod N) = x - a then (1 : ℚ) else 0)
    unfold kaP
    rw [h]
  simp only [key]
  unfold kaP
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun β _ => ?_)
  rw [← mul_sum, hsplit β]

lemma ka_wt_append (l₁ l₂ : List Bool) : wtβ (l₁ ++ l₂) = wtβ l₁ * wtβ l₂ := by
  simp [wtβ, List.map_append, List.prod_append]

lemma ka_wt_replicate (m : ℕ) (b : Bool) :
    wtβ (List.replicate m b) = (if b then (3 / 10 : ℚ) else 7 / 10) ^ m := by
  simp [wtβ, List.map_replicate, List.prod_replicate]

/-- `P_N(x) ≥ (3/10)^N`. -/
lemma ka_P_lower (N : ℕ) [NeZero N] (x : ZMod N) : (3 / 10 : ℚ) ^ N ≤ kaP N N x := by
  set m := x.val with hm
  have hmN : m ≤ N := (ZMod.val_lt x).le
  set β := List.replicate m false ++ List.replicate (N - m) true with hβ
  have hmem : β ∈ blockChoices N := by
    rw [fam_mem_blockChoices, hβ, List.length_append, List.length_replicate, List.length_replicate]
    omega
  have hcount : ((β.count false : ℕ) : ZMod N) = x := by
    simp [hβ, List.count_replicate]
    rw [hm, ZMod.natCast_zmod_val]
  have hwt : (3 / 10 : ℚ) ^ N ≤ wtβ β := by
    rw [hβ, ka_wt_append, ka_wt_replicate, ka_wt_replicate]
    simp only [Bool.false_eq_true, ↓reduceIte]
    calc (3 / 10 : ℚ) ^ N = (3 / 10) ^ m * (3 / 10) ^ (N - m) := by
          rw [← pow_add, Nat.add_sub_cancel' hmN]
      _ ≤ (7 / 10) ^ m * (3 / 10) ^ (N - m) := by
          gcongr
          norm_num
  unfold kaP
  calc (3 / 10 : ℚ) ^ N ≤ wtβ β * (if ((β.count false : ℕ) : ZMod N) = x then 1 else 0) := by
        rw [hcount, ite_eq_left rfl, mul_one]
        exact hwt
    _ ≤ _ := single_le_sum (f := fun β => wtβ β * (if ((β.count false : ℕ) : ZMod N) = x then 1 else 0))
        (fun β _ => mul_nonneg (fam_wt_nonneg β) (by split_ifs <;> norm_num)) hmem

lemma ka_D_le_two (N n : ℕ) [NeZero N] : kaDist N n ≤ 2 := by
  unfold kaDist
  calc ∑ x : ZMod N, |kaP N n x - 1 / N| ≤ ∑ x : ZMod N, (kaP N n x + 1 / N) := by
        refine sum_le_sum (fun x _ => ?_)
        have h0 := ka_P_nonneg N n x
        have h1 : (0 : ℚ) ≤ 1 / N := by positivity
        rw [abs_le]
        constructor <;> linarith
    _ = 2 := by
        rw [sum_add_distrib, ka_P_total, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
        have : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
        field_simp
        ring

/-- One contraction step: `D_{N+n} ≤ (1 - N(3/10)^N) D_n`. -/
lemma ka_D_step (N n : ℕ) [NeZero N] :
    kaDist N (N + n) ≤ (1 - N * (3 / 10 : ℚ) ^ N) * kaDist N n := by
  set b : ℚ := (3 / 10 : ℚ) ^ N with hb
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcard : (Fintype.card (ZMod N) : ℚ) = N := by rw [ZMod.card]
  -- `P_{N+n}(x) - 1/N = Σ_a (P_N(a) - b)(P_n(x - a) - 1/N)`.
  have hrep : ∀ x : ZMod N, kaP N (N + n) x - 1 / N =
      ∑ a : ZMod N, (kaP N N a - b) * (kaP N n (x - a) - 1 / N) := by
    intro x
    have hshift : ∑ a : ZMod N, kaP N n (x - a) = 1 := by
      rw [← ka_P_total N n]
      exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun a => rfl)
    have e : ∀ a : ZMod N, (kaP N N a - b) * (kaP N n (x - a) - 1 / N) =
        kaP N N a * kaP N n (x - a) - kaP N N a * (1 / N) - b * kaP N n (x - a) + b * (1 / N) := by
      intro a; ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, ka_P_total, hshift,
      sum_const, card_univ, nsmul_eq_mul, hcard, ka_P_conv]
    field_simp
    ring
  have hpos : ∀ a : ZMod N, 0 ≤ kaP N N a - b := fun a => by
    have := ka_P_lower N a; rw [hb]; linarith
  unfold kaDist
  calc ∑ x : ZMod N, |kaP N (N + n) x - 1 / N|
      ≤ ∑ x : ZMod N, ∑ a : ZMod N, (kaP N N a - b) * |kaP N n (x - a) - 1 / N| := by
        refine sum_le_sum (fun x _ => ?_)
        rw [hrep x]
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl (fun a _ => ?_)))
        rw [abs_mul, abs_of_nonneg (hpos a)]
    _ = ∑ a : ZMod N, (kaP N N a - b) * ∑ x : ZMod N, |kaP N n x - 1 / N| := by
        rw [Finset.sum_comm]
        refine sum_congr rfl (fun a _ => ?_)
        rw [← mul_sum]
        congr 1
        exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun x => rfl)
    _ = (1 - N * b) * ∑ x : ZMod N, |kaP N n x - 1 / N| := by
        rw [← sum_mul, sum_sub_distrib, ka_P_total, sum_const, card_univ, nsmul_eq_mul, hcard]

theorem specDoeblin : SpecDoeblin := by
  intro N n hN1
  have : NeZero N := ⟨by omega⟩
  set c : ℚ := 1 - N * (3 / 10 : ℚ) ^ N with hc
  -- `0 ≤ 1 - N(3/10)^N`.
  have hc0 : 0 ≤ c := by
    have h := sum_le_sum (fun a (_ : a ∈ (univ : Finset (ZMod N))) => ka_P_lower N a)
    rw [ka_P_total, sum_const, card_univ, ZMod.card, nsmul_eq_mul] at h
    rw [hc]
    linarith
  have hk : ∀ k r : ℕ, kaDist N (k * N + r) ≤ 2 * c ^ k := by
    intro k r
    induction k with
    | zero => simpa using ka_D_le_two N r
    | succ k ih =>
      rw [show (k + 1) * N + r = N + (k * N + r) by ring]
      calc kaDist N (N + (k * N + r)) ≤ c * kaDist N (k * N + r) := ka_D_step N _
        _ ≤ c * (2 * c ^ k) := mul_le_mul_of_nonneg_left ih hc0
        _ = 2 * c ^ (k + 1) := by ring
  have hmain : kaDist N n ≤ 2 * c ^ (n / N) := by
    have := hk (n / N) (n % N)
    rwa [Nat.div_add_mod' n N] at this
  -- move to `ℝ`.
  have hfilter : ∀ y ∈ range N, ∑ β ∈ (blockChoices n).filter (fun β => β.count false % N = y),
      (wtβ β : ℝ) = ((kaP N n (y : ZMod N) : ℚ) : ℝ) := by
    intro y hy
    rw [mem_range] at hy
    unfold kaP
    rw [sum_filter]
    push_cast
    refine sum_congr rfl (fun β _ => ?_)
    have : (β.count false % N = y) ↔ (((β.count false : ℕ) : ZMod N) = (y : ZMod N)) := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hy]
    by_cases h : β.count false % N = y
    · rw [ite_eq_left h, ite_eq_left (this.mp h), Rat.cast_one, mul_one]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (this.mpr h')), Rat.cast_zero, mul_zero]
  rw [sum_congr rfl (fun y hy => by rw [hfilter y hy])]
  have hcast : ∑ y ∈ range N, |((kaP N n (y : ZMod N) : ℚ) : ℝ) - 1 / N| = ((kaDist N n : ℚ) : ℝ) := by
    unfold kaDist
    rw [← ka_sum_zmod N (fun x => |kaP N n x - 1 / N|)]
    push_cast
    rfl
  rw [hcast]
  have : ((2 * c ^ (n / N) : ℚ) : ℝ) = 2 * (1 - N * (3 / 10 : ℝ) ^ N) ^ (n / N) := by
    rw [hc]; push_cast; ring
  rw [← this]
  exact_mod_cast hmain

end Collatz.Arctic
