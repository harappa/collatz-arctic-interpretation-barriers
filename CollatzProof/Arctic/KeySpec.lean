/-
Statements of the analytic parts of the swap argument (Appendix B.2 of the paper). The assembly of KEY (`KeyMain`) takes them as hypotheses
(arguments), and they are proved separately (`KeyAnal*`).
* `SpecCells`: part of Proposition B.6 (from the L² quantity of intervals to the total variation over cells).
* `SpecQavg`: Proposition B.6 (for signs `o_j` and the average over `w`, `E_w Q_λ(μ_w) = 2^{-M}(λ - λ^2 2^{-V})`, with `w` uniform on a residue class modulo 8).
* `SpecNine`: a lemma in the proof of Theorem B.7 (`y ↦ 9^y mod 2^k` is a bijection from `ℤ/2^{k-3}` onto `1 + 8ℤ`).
* `SpecDoeblin`: a lemma in the proof of Theorem B.7 (twice the total variation distance from uniform of the law of the number of `Y'` modulo `N` is at most `2(1 - N(3/10)^N)^{⌊n/N⌋}`).
-/
import CollatzProof.Arctic.KeyDefs
import CollatzProof.Arctic.CoreHyp
namespace Collatz.Arctic
open Classical
/-- Proposition B.6 (from the L² quantity to cells) -/
def SpecCells : Prop := ∀ (V ℓ d : ℕ), 1 ≤ ℓ → 1 ≤ d → ℓ + d ≤ V →
  ∀ (μ : ZMod (2 ^ V) → ℝ), (∀ x, 0 ≤ μ x) → (∑ x, μ x = 1) → ∀ t : ℝ, 0 < t →
    ∑ u ∈ Finset.range (2 ^ ℓ), |keyCell V ℓ μ u - 1 / 2 ^ ℓ| ≤
      2 / 2 ^ d + keyQ V (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d)) μ / (t * (2 ^ (V - ℓ - d) + 1)) + 2 ^ ℓ * t
/-- Proposition B.6 (the L² identity) -/
def SpecQavg : Prop := ∀ (V ℓ d I : ℕ), 1 ≤ ℓ → 1 ≤ d → ℓ + d + 3 ≤ V →
  ∀ (o : Fin I → ℤ) (ω : Fin I → ZMod (2 ^ V)) (v : Fin I → ℕ) (z₀ : ZMod (2 ^ V) → ZMod (2 ^ V))
    (w₀ : ZMod (2 ^ V)),
    (∀ j, o j = -1 ∨ o j = 0 ∨ o j = 1) → (∀ j, (ω j).val % 2 = 1) → (∀ i j, i < j → v j < v i) →
    (∀ j, ℓ + d + 3 ≤ v j ∧ v j ≤ V) → w₀.val % 2 = 1 →
    (∑ w ∈ Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8),
        keyQ V (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d))
          (keyLaw V I (z₀ w) (fun j => (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) * w))) /
      ((Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8)).card : ℝ) =
    (1 / 2 ^ (Finset.univ.filter (fun j => o j ≠ 0)).card) *
      ((2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) - (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) ^ 2 / 2 ^ V)
/-- A lemma in the proof of Theorem B.7 (powers of 9) -/
def SpecNine : Prop := ∀ k : ℕ, 3 ≤ k →
  Set.BijOn (fun y : ℕ => 9 ^ y % 2 ^ k) ↑(Finset.range (2 ^ (k - 3))) {x | x < 2 ^ k ∧ x % 8 = 1}
/-- A lemma in the proof of Theorem B.7 (the law of the number of Y' modulo N) -/
def SpecDoeblin : Prop := ∀ N n : ℕ, 1 ≤ N →
  ∑ y ∈ Finset.range N, |∑ β ∈ (blockChoices n).filter (fun β => β.count false % N = y), (wtβ β : ℝ)
    - 1 / N| ≤ 2 * (1 - N * (3 / 10 : ℝ) ^ N) ^ (n / N)
end Collatz.Arctic
