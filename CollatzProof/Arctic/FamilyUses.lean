/-
The numbers of uses of the dynamic rules along the point family of the block model of `T` (Proposition 6.7 (i), the dynamic rules).
The definition of the point family is in `Family.lean`.

The first rule of the canonical derivation `canDeriv x` (`Statement.lean`) is determined by parity: for even `x` only `f. → .`, for odd `x`
`t. → 2.` followed by the sweep rules (`sweepRules`, only carry rules A and left-end rules). Hence the numbers of uses along an orbit segment are counts in the parity
word `σ = parityOf β` (`terras_parity`).

* `fam_uses_odd`, `fam_uses_even`: the numbers of uses at one point.
* `fam_usesOrbit_odd`, `fam_usesOrbit_even`: in `m` steps from `x₀ = famX0`, `t. → 2.` is used as many times as the number of odd steps of `σ`,
  and `f. → .` as many times as the number of even steps.
* `fam_usesOrbit_odd_ge`, `fam_usesOrbit_even_ge`: each block has at least 5 odd steps and at least 3 even steps, so
  both are at least `3 |β|` (each at least `3k` times, as in Proposition 6.7 (i)).
-/
import CollatzProof.Arctic.Family

namespace Collatz.Arctic

/-! ## (6) Numbers of uses of the dynamic rules -/

open Letter in
/-- The sweep rules (carry rules A and left-end rules) are not dynamic rules. -/
lemma fam_sweep_not_dyn : ∀ (l : List ℕ) (d : ℕ), ∀ ρ ∈ sweepRules l d,
    ρ ≠ ⟨[t, rgt], [d2, rgt]⟩ ∧ ρ ≠ ⟨[f, rgt], [rgt]⟩ := by
  intro l
  induction l with
  | nil =>
    intro d ρ hρ
    simp only [sweepRules, List.mem_singleton] at hρ
    subst hρ
    unfold leftRule
    split_ifs <;> simp
  | cons b bs ih =>
    intro d ρ hρ
    simp only [sweepRules, List.mem_cons] at hρ
    rcases hρ with rfl | hρ
    · unfold aRule digL
      split_ifs <;> simp
    · exact ih _ ρ hρ

open Letter in
/-- The odd-step rule `t. → 2.` is used exactly once in the canonical derivation of an odd point and not at all for an even point. -/
theorem fam_uses_odd (x : ℕ) :
    uses ⟨[t, rgt], [d2, rgt]⟩ x = if x % 2 = 0 then 0 else 1 := by
  unfold uses canDeriv
  split_ifs with h
  · simp
  · rw [List.count_cons, List.count_eq_zero_of_not_mem]
    · simp
    · intro hm
      exact (fam_sweep_not_dyn _ _ _ hm).1 rfl

open Letter in
/-- The even-step rule `f. → .` is used exactly once in the canonical derivation of an even point and not at all for an odd point. -/
theorem fam_uses_even (x : ℕ) :
    uses ⟨[f, rgt], [rgt]⟩ x = if x % 2 = 0 then 1 else 0 := by
  unfold uses canDeriv
  split_ifs with h
  · simp
  · rw [List.count_cons, List.count_eq_zero_of_not_mem]
    · simp
    · intro hm
      exact (fam_sweep_not_dyn _ _ _ hm).2 rfl

lemma fam_sum_getD (σ : List Bool) (c : Bool) :
    ((List.range σ.length).map (fun i => if σ.getD i false = c then 1 else 0)).sum = σ.count c := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, ih, List.count_cons]
    cases b <;> cases c <;> simp <;> omega

/-- Count the numbers of uses from the parities along an orbit segment. -/
lemma fam_usesOrbit_parity (ρ : Rule) (σ : List Bool) (t : ℕ) (c : Bool)
    (hρ : ∀ x, uses ρ x = if x % 2 = (if c then 1 else 0) then 1 else 0) :
    usesOrbit ρ (terrasR σ + 2 ^ σ.length * t) σ.length = σ.count c := by
  unfold usesOrbit
  rw [← fam_sum_getD σ c]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [hρ, terras_parity σ t i hi]
  cases c <;> cases σ.getD i false <;> simp

open Letter in
/-- **(6)**: in the canonical derivations of `m` steps from `x₀`, the odd-step rule `t. → 2.` is used as many times as the number of odd steps of `σ`. -/
theorem fam_usesOrbit_odd (β₀ β : List Bool) (n K τ u : ℕ) :
    usesOrbit ⟨[t, rgt], [d2, rgt]⟩ (famX0 β₀ β n K τ u) (parityOf β).length
      = (parityOf β).count true :=
  fam_usesOrbit_parity _ _ _ true (fun x => by rw [fam_uses_odd]; simp only [ite_true]; split_ifs <;> omega)

open Letter in
/-- **(6)**: the even-step rule `f. → .` is used as many times as the number of even steps of `σ`. -/
theorem fam_usesOrbit_even (β₀ β : List Bool) (n K τ u : ℕ) :
    usesOrbit ⟨[f, rgt], [rgt]⟩ (famX0 β₀ β n K τ u) (parityOf β).length
      = (parityOf β).count false :=
  fam_usesOrbit_parity _ _ _ false (fun x => by rw [fam_uses_even]; simp)

open Letter in
/-- **Corollary of (6)**: `t. → 2.` is used at least `3 |β|` times (each block has at least 5 odd steps). -/
theorem fam_usesOrbit_odd_ge (β₀ β : List Bool) (n K τ u : ℕ) :
    3 * β.length ≤ usesOrbit ⟨[t, rgt], [d2, rgt]⟩ (famX0 β₀ β n K τ u) (parityOf β).length := by
  rw [fam_usesOrbit_odd, (fam_parityOf_counts β).2.1, fam_length_eq_count]
  omega

open Letter in
/-- **Corollary of (6)**: `f. → .` is used at least `3 |β|` times (each block has at least 3 even steps). -/
theorem fam_usesOrbit_even_ge (β₀ β : List Bool) (n K τ u : ℕ) :
    3 * β.length ≤ usesOrbit ⟨[f, rgt], [rgt]⟩ (famX0 β₀ β n K τ u) (parityOf β).length := by
  rw [fam_usesOrbit_even, (fam_parityOf_counts β).2.2, fam_length_eq_count]
  omega

end Collatz.Arctic
