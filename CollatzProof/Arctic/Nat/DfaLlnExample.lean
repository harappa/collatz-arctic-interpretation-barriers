/-
# Natural-number interpretations of 𝒯 (Section 12.4), part (5): checks of non-vacuity

Small examples in which the hypotheses of `DfaLln*.lean` can be met and `statMean` takes the expected value.

* **Example 1 (period 2, two states)**: `flip x _ = !x` (the state is flipped whatever the input), `φ x _ = [x = true]`, `J = 0`.
  The closed class is all of `{false, true}`, with period 2 (two cyclic classes). Read from `false`, the state at the position `p` is
  `true` when `p` is odd, so `mexp false L = ⌊L/2⌋` and `mexp true L = ⌈L/2⌉` (the starting state makes a difference).
  The stationary mean is `1/2` from both (`ex1_statMean`, `ex1_statMean_true`). This checks that, in a periodic class, `statMean` does
  not depend on the cyclic class of the starting state.
* **Example 2 (one state, a following window)**: `J = 1`, `φ _ v = [v = [true]]` (the next digit is 1). `mexp () L = L/2` and
  `statMean = 1/2` (`ex2_statMean`). This checks a function that depends on the window.
* In both, the right-hand side of `stat_mean_pos` holds, consistently with `statMean > 0`.
-/
import CollatzProof.Arctic.Nat.DfaLln

namespace Collatz.Arctic.NatQ5.W3d.Example

open Collatz.Arctic Collatz.Arctic.Dfa Filter Topology

/-! ## Example 1: a DFA of period 2 -/

/-- The DFA that flips the state whatever the input. -/
def flip (x : Bool) (_ : Bool) : Bool := !x

/-- A function of the state: 1 at `true`. -/
noncomputable def φ₁ (x : Bool) (_ : List Bool) : ℝ := if x then 1 else 0

theorem run_flip (x : Bool) (u : List Bool) :
    run flip x u = if u.length % 2 = 0 then x else !x := by
  induction u generalizing x with
  | nil => simp
  | cons b u ih =>
    rw [run_cons, ih]
    simp only [flip, List.length_cons]
    rcases Nat.mod_two_eq_zero_or_one u.length with h | h
    · have h' : ¬ (u.length + 1) % 2 = 0 := by omega
      simp only [h, h', ↓reduceIte]
    · have h' : ¬ u.length % 2 = 0 := by omega
      have h'' : (u.length + 1) % 2 = 0 := by omega
      simp only [h', h'', ↓reduceIte, Bool.not_not]

theorem reach_flip (x y : Bool) : Reach flip x y := by
  refine ⟨if x = y then [] else [false], ?_⟩
  by_cases h : x = y
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [run_flip]
    cases x <;> cases y <;> simp_all

theorem rec_flip : Recurrent flip false := fun q _ => reach_flip q false

theorem hφ₁ : ∀ x v, |φ₁ x v| ≤ 1 := by
  intro x v; unfold φ₁; split_ifs <;> norm_num

/-- The term at the position `p < L`. -/
theorem mexp_ex1 (x : Bool) (L : ℕ) :
    mexp flip 0 φ₁ x L = ∑ p ∈ Finset.range L, if (p % 2 = 0) = (x = false) then (0 : ℝ) else 1 := by
  unfold mexp
  rw [← avg_const (L + 0) (∑ p ∈ Finset.range L, if (p % 2 = 0) = (x = false) then (0 : ℝ) else 1)]
  refine avg_congr (fun w hw => Finset.sum_congr rfl (fun p hp => ?_))
  have hp' := Finset.mem_range.mp hp
  have hl : (w.take p).length = p := by rw [List.length_take]; omega
  unfold φ₁
  rw [run_flip, hl]
  rcases Nat.mod_two_eq_zero_or_one p with h | h <;> cases x <;> simp [h]

theorem sum_odd (L : ℕ) :
    (∑ p ∈ Finset.range L, if p % 2 = 0 then (0 : ℝ) else 1) = ((L / 2 : ℕ) : ℝ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one L with h | h
    · simp only [h, ↓reduceIte, add_zero]
      rw [show (L + 1) / 2 = L / 2 by omega]
    · have h' : ¬ L % 2 = 0 := by omega
      simp only [h', ↓reduceIte]
      rw [show (L + 1) / 2 = L / 2 + 1 by omega]
      push_cast; ring

theorem mexp_ex1_false (L : ℕ) : mexp flip 0 φ₁ false L = ((L / 2 : ℕ) : ℝ) := by
  rw [mexp_ex1, ← sum_odd]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp

theorem mexp_ex1_true (L : ℕ) : mexp flip 0 φ₁ true L = (((L + 1) / 2 : ℕ) : ℝ) := by
  rw [mexp_ex1]
  have e : ∀ p, (if (p % 2 = 0) = (true = false) then (0 : ℝ) else 1) =
      1 - (if p % 2 = 0 then (0 : ℝ) else 1) := by
    intro p
    rcases Nat.mod_two_eq_zero_or_one p with h | h <;> simp [h]
  simp_rw [e]
  rw [Finset.sum_sub_distrib, sum_odd, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have : (L + 1) / 2 + L / 2 = L := by omega
  have h2 : (((L + 1) / 2 : ℕ) : ℝ) + ((L / 2 : ℕ) : ℝ) = L := by exact_mod_cast this
  linarith

/-- The expectations differ for different starting states (different cyclic classes): for length 1, 0 from `false` and 1 from `true`. -/
theorem ex1_mexp_one : mexp flip 0 φ₁ false 1 = 0 ∧ mexp flip 0 φ₁ true 1 = 1 := by
  rw [mexp_ex1_false, mexp_ex1_true]
  norm_num

/-- **The stationary mean of Example 1 is `1/2`**. -/
theorem ex1_statMean : statMean flip 0 φ₁ false = 1 / 2 := by
  refine tendsto_nhds_unique (tendsto_statMean 0 rec_flip hφ₁) (tendsto_div_of_abs_sub_le (K := 1) ?_)
  intro L
  rw [mexp_ex1_false]
  have h1 : 2 * (L / 2) ≤ L := Nat.mul_div_le L 2
  have h2 : L ≤ 2 * (L / 2) + 1 := by omega
  have h1' : 2 * ((L / 2 : ℕ) : ℝ) ≤ L := by exact_mod_cast h1
  have h2' : (L : ℝ) ≤ 2 * ((L / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-- It is also `1/2` with the state `true` of the other cyclic class as the base point (`statMean_eq_of_reach`). -/
theorem ex1_statMean_true : statMean flip 0 φ₁ true = 1 / 2 := by
  rw [statMean_eq_of_reach 0 rec_flip (reach_flip false true) hφ₁, ex1_statMean]

/-- Consistency with `stat_mean_pos`. -/
theorem ex1_pos : 0 < statMean flip 0 φ₁ false := by
  refine (stat_mean_pos 0 rec_flip hφ₁ (fun x v _ _ => ?_)).2 ⟨true, [], reach_flip false true, rfl, ?_⟩
  · unfold φ₁; split_ifs <;> norm_num
  · unfold φ₁; norm_num

/-! ## Example 2: a DFA with one state and a following window -/

/-- The DFA with one state. -/
def one (_ : Unit) (_ : Bool) : Unit := ()

/-- 1 if the next digit is 1. -/
noncomputable def φ₂ (_ : Unit) (v : List Bool) : ℝ := if v = [true] then 1 else 0

theorem rec_one : Recurrent one () := fun q _ => ⟨[], by cases q; rfl⟩

theorem hφ₂ : ∀ x v, |φ₂ x v| ≤ 1 := by
  intro x v; unfold φ₂; split_ifs <;> norm_num

theorem avg_next_one {p n : ℕ} (hp : p < n) :
    avg n (fun w => if (w.drop p).take 1 = [true] then (1 : ℝ) else 0) = 1 / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = p + (m + 1) := ⟨n - p - 1, by omega⟩
  rw [avg_drop p (m + 1) (fun v => if v.take 1 = [true] then (1 : ℝ) else 0)]
  have := avg_ind_take (n := m + 1) [true] (by simp)
  simpa using this

theorem mexp_ex2 (L : ℕ) : mexp one 1 φ₂ () L = L / 2 := by
  unfold mexp wsum φ₂
  rw [avg_sum]
  rw [Finset.sum_congr rfl (fun p hp => avg_next_one (n := L + 1) (by
    have := Finset.mem_range.mp hp; omega))]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- **The stationary mean of Example 2 is `1/2`** (the frequency of the next digit being 1). -/
theorem ex2_statMean : statMean one 1 φ₂ () = 1 / 2 := by
  refine tendsto_nhds_unique (tendsto_statMean 1 rec_one hφ₂) (tendsto_div_of_abs_sub_le (K := 0) ?_)
  intro L
  rw [mexp_ex2]
  simp only [abs_nonpos_iff]
  ring

end Collatz.Arctic.NatQ5.W3d.Example
