/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for the proof of Theorem 10.10 (Sections 12.6–12.9)

We check with a concrete automaton and concrete numbers that the premises of the main theorems of Sections 12.6–12.9 can be satisfied. Outside the closure of the
main theorems. No evaluation outside the kernel is used.

* §1 **The premises of the core statement can be satisfied**: for the example `laneAuto 0` (it satisfies (M) and (H2^prod); `NonVacuityW2e.lean`)
  the premises of `W3CoreStmt` hold, and the conclusion (orbit segments on which the number of uses exceeds the value) follows for a concrete automaton (`ex_w3core`).
* §2 **The setting `Setup` is not empty**: `liftT (laneAuto 0)` has a setting (`ex_setup`; `DecompStmtT0` from the decomposition data `W3c.decompData`).
  Its set of configurations `𝔎` is not empty (`ex_Kset`). So the case distinction (case A / case B) is a statement on a non-empty set.
* §3 **`DecompStmtT0` is stronger than `DecompStmt` but consistent**: the decomposition data `W3c.decompData` satisfy `t₀ ≥ |τ'| + |u♯|`
  (`decompStmtT0`).
* §4 **The premises of the arithmetic lemmas can be satisfied**: the comparison `compare` (`V₀ < V₁` with concrete numbers), the sum of the numbers of bad `u`
  (`bad_sum`), the length ratio `len_ratio`, and the existence of a good element (`exists_avoid`).
-/
import CollatzProof.Arctic.Nat.Final
import CollatzProof.Arctic.Nat.NonVacuityW2e

namespace Collatz.Arctic.NatQ5.W3h.Example

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W2e.NonVacuity

/-! ## §1 The premises of the core statement -/

theorem ex_premises : H2Prod (laneAuto 0) ∧ AutoMono3 (liftT (laneAuto 0)) :=
  ⟨h2Prod_lane0, liftT_mono3 autoMono_lane0⟩

/-- The conclusion of the core statement for `laneAuto 0`. -/
theorem ex_w3core : ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
    (∀ i < m, 2 ≤ T^[i] n) ∧ aval (laneAuto 0) (binWord n) < usesOrbit ρ n m :=
  w3CoreStmt _ (laneAuto 0) ex_premises.1 ex_premises.2

/-! ## §2 Settings and the set of configurations -/

theorem ex_setup : Nonempty (Setup (liftT (laneAuto 0))) :=
  W3h.exists_setup decompStmtT0 (liftT (laneAuto 0)) h2Prod_lane0

theorem ex_Kset : ∃ S : Setup (liftT (laneAuto 0)), S.Kset.Nonempty := by
  obtain ⟨S⟩ := ex_setup
  exact ⟨S, S.Kset_nonempty⟩

/-! ## §3 `DecompStmtT0` -/

theorem ex_decompT0 : DecompStmtT0 ∧ W3c.DecompStmt := ⟨decompStmtT0, decompStmt_of_T0 decompStmtT0⟩

/-! ## §4 Arithmetic lemmas -/

/-- Comparison: `N₀ = 100`, `N₁ = 200`, `κ = 1/2`, `C_lo = 1`, `c_* = 1`, `ε = 1/8`, degree 1. -/
theorem ex_compare : (112 : ℝ) < 175 :=
  compare (N₀ := 100) (N₁ := 200) (Clo := 1) (C₁ := 1) (cs := 1) (ε := 1 / 8) (κ := 1 / 2) (dlo := 1) (d₁ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨le_rfl, Or.inr ⟨rfl, le_rfl⟩⟩

/-- The sum of the numbers of bad `u` (`F = 10`, `L_c = 2`, `η₀ = 1`, `ε_F = 0`, `TV = 0`). -/
theorem ex_bad_sum :
    (((1 / 2 ^ (2 + 4) * 2 ^ 10 : ℚ)) : ℝ) + 0 / (1 / 8) * 2 ^ 10 + ((1 / 2 ^ (2 + 4) * 2 ^ 10 : ℚ) : ℝ) +
      (((1 / 2 ^ (2 + 4) + (3 / 2 ^ (2 + 6) + 0)) * 2 ^ 10 : ℚ) : ℝ) < 2 ^ (10 - 2) :=
  bad_sum 10 2 (by norm_num) (η₀ := 1) (εF := 0) (TV := 0) one_pos (by norm_num) (by norm_num)

/-- The length ratio (`N₀ = 34`, `N₁ = 36`, `k = 1`, `j = 2`, `c = 2`, `κ = 1/17`). -/
theorem ex_len_ratio : (1 + 1 / 17 : ℝ) * ((34 : ℕ) : ℝ) ≤ ((36 : ℕ) : ℝ) :=
  len_ratio (N₀ := 34) (N₁ := 36) (k := 1) (j := 2) (c := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Existence of a good element: `G = {0, 1, 2}`, and the bad sets are `{0}`, `{1}`, `∅`, `∅`. -/
theorem ex_avoid : ∃ u ∈ ({0, 1, 2} : Finset ℕ), u ∉ ({0} : Finset ℕ) ∧ u ∉ ({1} : Finset ℕ) ∧
    u ∉ (∅ : Finset ℕ) ∧ u ∉ (∅ : Finset ℕ) :=
  exists_avoid _ _ _ _ _ (x := 3) (by norm_num) (by norm_num)

end Collatz.Arctic.NatQ5.W3h.Example
