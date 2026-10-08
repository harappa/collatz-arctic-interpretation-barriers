/-
# Natural-number interpretations of 𝒯 (Sections 12.5 and 12.7): common parts, sums of probabilities on the side of `σ`

Lemmas on weighted sums over the choices of blocks, used both by the event (ii) of the top window (`W3Top.lean`, Proposition 12.19) and by the chains of
groups (`W3Gap.lean`, Section 12.7).

* `prσ_eq_sum`: `Prσ` written as a weighted sum of indicators (`Prσ` is the filter under `open Classical`).
* `prσ_nonneg`, `prσ_le_one`: probabilities lie between 0 and 1 (the total weight is 1, `fam_moments`).
* `wtβ_append`, `wtβ_replicate`: the weights are products.
* `prσ_exists_le`: the union bound `Pr(∃ j ∈ S, E_j) ≤ Σ_{j ∈ S} Pr(E_j)`.
* `expect_ind`: the expectation of a weighted sum of indicators is the weighted sum of the probabilities.
* `prσ_markov`: Markov's inequality (for rational values; `HTWProb.htw_markov` is for natural-number values).
* `sum_split`: splitting a sum over length `a + m` into the first `a` and the rest (`HTWProb.htw_sum_split` for functions of the whole sequence).

All auxiliary declarations are in the namespace `Collatz.Arctic.NatQ5.W3b`. No `sorry`, `axiom` or `native_decide` is used.
-/
import CollatzProof.Arctic.HTWProb
import CollatzProof.Arctic.Nat.H2Bin

namespace Collatz.Arctic.NatQ5.W3b

open Collatz.Arctic Finset
open Classical

/-! ## §1 `Prσ` as a sum -/

/-- `Prσ` is a weighted sum of indicators. -/
theorem prσ_eq_sum (β₀ : List Bool) (k : ℕ) (E : List Bool → Prop) :
    Prσ β₀ k E = ∑ β ∈ blockChoices k, wtβ β * (if E (β₀ ++ β) then 1 else 0) := by
  unfold Prσ
  rw [sum_filter]
  refine sum_congr rfl (fun β _ => ?_)
  split_ifs <;> ring

/-- The total weight is 1. -/
theorem sum_wt (k : ℕ) : ∑ β ∈ blockChoices k, wtβ β = 1 := (fam_moments k).1

theorem prσ_nonneg (β₀ : List Bool) (k : ℕ) (E : List Bool → Prop) : 0 ≤ Prσ β₀ k E := by
  unfold Prσ
  exact sum_nonneg (fun β _ => fam_wt_nonneg β)

theorem prσ_le_one (β₀ : List Bool) (k : ℕ) (E : List Bool → Prop) : Prσ β₀ k E ≤ 1 := by
  rw [← sum_wt k]
  unfold Prσ
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun β _ _ => fam_wt_nonneg β)

/-- A weighted sum of indicators is at most 1. -/
theorem sum_ind_le_one (k : ℕ) (F : List Bool → Prop) :
    ∑ β ∈ blockChoices k, wtβ β * (if F β then (1 : ℚ) else 0) ≤ 1 := by
  calc ∑ β ∈ blockChoices k, wtβ β * (if F β then (1 : ℚ) else 0)
      ≤ ∑ β ∈ blockChoices k, wtβ β := by
        refine sum_le_sum (fun β _ => ?_)
        have := fam_wt_nonneg β
        split_ifs <;> nlinarith
    _ = 1 := sum_wt k

/-! ## §2 The weights are products -/

theorem wtβ_append (l₁ l₂ : List Bool) : wtβ (l₁ ++ l₂) = wtβ l₁ * wtβ l₂ := by
  unfold wtβ
  rw [List.map_append, List.prod_append]

theorem wtβ_replicate (j : ℕ) (x : Bool) :
    wtβ (List.replicate j x) = (if x then (3 / 10 : ℚ) else 7 / 10) ^ j := by
  unfold wtβ
  rw [List.map_replicate, List.prod_replicate]

/-! ## §3 The union bound and expectations -/

/-- **Union bound**: `Pr(∃ j ∈ S, E_j) ≤ Σ_{j ∈ S} Pr(E_j)`. -/
theorem prσ_exists_le {ι : Type*} (β₀ : List Bool) (k : ℕ) (S : Finset ι)
    (E : ι → List Bool → Prop) :
    Prσ β₀ k (fun β => ∃ j ∈ S, E j β) ≤ ∑ j ∈ S, Prσ β₀ k (E j) := by
  simp only [prσ_eq_sum]
  rw [sum_comm]
  refine sum_le_sum (fun β _ => ?_)
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (fam_wt_nonneg β)
  split_ifs with h
  · obtain ⟨j, hj, hE⟩ := h
    calc (1 : ℚ) = if E j (β₀ ++ β) then 1 else 0 := by simp only [hE, ↓reduceIte]
      _ ≤ ∑ i ∈ S, (if E i (β₀ ++ β) then (1 : ℚ) else 0) :=
        single_le_sum (f := fun i => if E i (β₀ ++ β) then (1 : ℚ) else 0)
          (fun i _ => by split_ifs <;> norm_num) hj
  · exact sum_nonneg (fun i _ => by split_ifs <;> norm_num)

/-- The expectation of a weighted sum of indicators is the weighted sum of the probabilities. -/
theorem expect_ind {ι : Type*} (β₀ : List Bool) (k : ℕ) (S : Finset ι) (w : ι → ℚ)
    (E : ι → List Bool → Prop) :
    ∑ β ∈ blockChoices k, wtβ β * ∑ R ∈ S, w R * (if E R (β₀ ++ β) then 1 else 0) =
      ∑ R ∈ S, w R * Prσ β₀ k (E R) := by
  simp only [prσ_eq_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun R _ => sum_congr rfl (fun β _ => ?_))
  ring

/-- **Markov's inequality** (rational values): if `X ≥ 0`, then `Pr(X > θ) ≤ E[X]/θ`. -/
theorem prσ_markov (β₀ : List Bool) (k : ℕ) (X : List Bool → ℚ) (hX : ∀ β, 0 ≤ X β)
    (θ : ℚ) (hθ : 0 < θ) :
    Prσ β₀ k (fun β => θ < X β) ≤ (∑ β ∈ blockChoices k, wtβ β * X (β₀ ++ β)) / θ := by
  rw [prσ_eq_sum, le_div_iff₀ hθ, sum_mul]
  refine sum_le_sum (fun β _ => ?_)
  have hw := fam_wt_nonneg β
  split_ifs with h
  · nlinarith
  · have := hX (β₀ ++ β)
    nlinarith

/-- `Pr(X ≤ θ) ≥ 1 - E[X]/θ`. -/
theorem prσ_markov_le (β₀ : List Bool) (k : ℕ) (X : List Bool → ℚ) (hX : ∀ β, 0 ≤ X β)
    (θ : ℚ) (hθ : 0 < θ) :
    1 - (∑ β ∈ blockChoices k, wtβ β * X (β₀ ++ β)) / θ ≤ Prσ β₀ k (fun β => X β ≤ θ) := by
  have h1 := prσ_markov β₀ k X hX θ hθ
  have h2 : Prσ β₀ k (fun β => X β ≤ θ) + Prσ β₀ k (fun β => θ < X β) = 1 := by
    simp only [prσ_eq_sum]
    rw [← sum_add_distrib]
    refine (sum_congr rfl (fun β _ => ?_)).trans (sum_wt k)
    by_cases h : X (β₀ ++ β) ≤ θ
    · have h' : ¬ θ < X (β₀ ++ β) := not_lt.mpr h
      simp only [h, h', ↓reduceIte]; ring
    · have h' : θ < X (β₀ ++ β) := lt_of_not_ge h
      simp only [h, h', ↓reduceIte]; ring
  linarith

/-! ## §4 Splitting sums -/

/-- Splitting a sum over length `a + m` into a double sum over the first `a` blocks and the remaining `m` (for functions of the whole sequence). -/
theorem sum_split (a m : ℕ) (H : List Bool → ℚ) :
    ∑ β ∈ blockChoices (a + m), wtβ β * H β =
      ∑ β₁ ∈ blockChoices a, wtβ β₁ * ∑ β₂ ∈ blockChoices m, wtβ β₂ * H (β₁ ++ β₂) := by
  have h := htw_sum_split a m (fun β₁ β₂ => H (β₁ ++ β₂))
  simp only [List.take_append_drop] at h
  rw [h]
  refine sum_congr rfl (fun β₁ _ => ?_)
  rw [mul_sum]

end Collatz.Arctic.NatQ5.W3b
