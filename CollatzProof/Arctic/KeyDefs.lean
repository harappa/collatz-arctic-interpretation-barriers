/-
Common Lean definitions of the swap argument (Appendix B.2 of the paper). For a measure on the group `G = ZMod (2^V)`,
`μ : ZMod (2^V) → ℝ`:
* `keyF V λ μ x = μ(x + J_λ)` (`J_λ = {0, …, λ-1}`), `keyQ V λ μ = Σ_x (F_μ(x) - λ 2^{-V})^2` (the `Q_λ` of Proposition B.6).
* `keyCell V ℓ μ u = μ(C_u)`, `C_u = {u h, …, u h + h - 1}`, `h = 2^{V-ℓ}` (the cells of Proposition B.6).
* `keyLaw V I z₀ a`: the law of `z₀ + Σ_j e_j a_j` for `e ∈ {0,1}^I` uniform (the `μ_w` of Proposition B.6).
-/
import Mathlib

namespace Collatz.Arctic

/-- `F_μ(x) := μ(x + J_λ)`. -/
noncomputable def keyF (V lam : ℕ) (μ : ZMod (2 ^ V) → ℝ) (x : ZMod (2 ^ V)) : ℝ :=
  ∑ y ∈ Finset.range lam, μ (x + (y : ZMod (2 ^ V)))

/-- `Q_λ(μ) := Σ_x (F_μ(x) - λ 2^{-V})^2`. -/
noncomputable def keyQ (V lam : ℕ) (μ : ZMod (2 ^ V) → ℝ) : ℝ :=
  ∑ x : ZMod (2 ^ V), (keyF V lam μ x - (lam : ℝ) / 2 ^ V) ^ 2

/-- The measure of the cell `C_u = {u 2^{V-ℓ}, …, u 2^{V-ℓ} + 2^{V-ℓ} - 1}`. -/
noncomputable def keyCell (V ℓ : ℕ) (μ : ZMod (2 ^ V) → ℝ) (u : ℕ) : ℝ :=
  ∑ y ∈ Finset.range (2 ^ (V - ℓ)), μ ((u * 2 ^ (V - ℓ) + y : ℕ) : ZMod (2 ^ V))

/-- The law of `z₀ + Σ_j e_j a_j` for `e ∈ {0,1}^I` uniform. -/
noncomputable def keyLaw (V I : ℕ) (z₀ : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V)) :
    ZMod (2 ^ V) → ℝ := fun x =>
  ((Finset.univ.filter (fun e : Fin I → Bool => z₀ + ∑ j, (if e j then a j else 0) = x)).card : ℝ) / 2 ^ I

end Collatz.Arctic
