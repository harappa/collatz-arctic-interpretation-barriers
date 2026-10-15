/-
Deriving `HTerrasWin` from `HKeyTop` (the swap argument): the names for `T` of the probabilistic part. The deterministic part is in `HTWCut.lean`,
the main theorem in `HTWFromKey.lean`. Steps 2 and 3 of the proof of Theorem B.8.

Since revision r5 the proofs are in the general layer `Gen/HTWProb.lean` (a copy with the residue `R` as a parameter). This file keeps the names
cited in the paper and those used by `Nat/W3bBase.lean` and `Nat/W3Gap.lean`, as thin theorems for the model `Gen.tModel` of `T` (with unchanged statements).

* `htw_sum_split`: split a weighted sum over block choices of length `a + m` into a double sum over the first `a` blocks and the remaining `m` blocks
  (the weight is a product; the version of `HLUWalk2.walk_sum_append` for general functions).
* `htw_bad_le`: fix the blocks `γ` of the chunk. If the law of the bits of the chunk is within total variation distance `τ` of uniform (`HKeyTop`)
  and the proportion of bad uniform words (property `P`) is at most `η`, then the bits of the chunk are bad with probability at most `2τ + η`.
* `htw_cut_prob`: the chunk `[|β₀| + j, |β₀| + j + K)` (`j ≥ n₀`) is bad with probability at most `2τ + η` (apply `HKeyTop` with the `j` blocks
  before the chunk, and average over the blocks `γ` of the chunk).
* `htw_markov`: Markov's inequality for the expectation (weighted counting).

-/
import CollatzProof.Arctic.HTWCut
import CollatzProof.Arctic.Gen.HTWProb
import CollatzProof.Arctic.HTWKey
import CollatzProof.Arctic.HLUWalk2
import CollatzProof.Arctic.HLUMain

namespace Collatz.Arctic

open Finset

/-- Split a weighted sum over block choices of length `a + m` into a double sum over the first `a` blocks and the remaining `m` blocks. -/
theorem htw_sum_split (a m : ℕ) (H : List Bool → List Bool → ℚ) :
    ∑ β ∈ blockChoices (a + m), wtβ β * H (β.take a) (β.drop a) =
      ∑ β₁ ∈ blockChoices a, ∑ β₂ ∈ blockChoices m, wtβ β₁ * (wtβ β₂ * H β₁ β₂) :=
  Gen.htw_sum_split a m H

open Classical in
/-- **Probability that one chunk is bad** (the blocks `γ` of the chunk fixed): if the law of the bits of the chunk is within total variation distance `τ` of uniform
and the proportion of uniform words with property `P` is at most `η`, then the bits of the chunk have property `P` with probability at most `2τ + η`. -/
theorem htw_bad_le (β₀ γ : List Bool) (n : ℕ) (τ η : ℚ) (P : Word → Prop) [DecidablePred P]
    (hkey : ∑ u ∈ Finset.range (2 ^ (parityOf γ).length),
      |(∑ β ∈ (blockChoices n).filter (fun β =>
          terrasR (parityOf (β₀ ++ β ++ γ)) / 2 ^ (parityOf (β₀ ++ β)).length = u), wtβ β)
        - 1 / 2 ^ (parityOf γ).length| ≤ 2 * τ)
    (hP : (((Finset.range (2 ^ (parityOf γ).length)).filter
        (fun u => P (bitsMSB (parityOf γ).length u))).card : ℚ) ≤ η * 2 ^ (parityOf γ).length) :
    ∑ β ∈ blockChoices n,
      wtβ β * (if P (bitsMSB (parityOf γ).length (htwCutVal β₀ β γ)) then 1 else 0) ≤ 2 * τ + η :=
  Gen.htw_bad_le Gen.tModel.R Gen.tModel.R_lt β₀ γ n τ η P hkey hP

open Classical in
/-- **Probability that a chunk is bad**: the chunk `[|β₀| + j, |β₀| + j + K)` (`n₀ ≤ j`, `j + K ≤ k`) is bad with probability at most `2τ + η`.
`hkey` is the conclusion of `HKeyTop` for `K` and `τ`, `hbad` the law of large numbers for the window frequencies of uniform words. -/
theorem htw_cut_prob (β₀ : List Bool) (K J : ℕ) (δ' τ η : ℚ) (n₀ : ℕ)
    (hkey : ∀ n ≥ n₀, ∀ (β₀ γ : List Bool), γ.length = K →
      ∑ u ∈ Finset.range (2 ^ (parityOf γ).length),
        |(∑ β ∈ (blockChoices n).filter (fun β =>
            terrasR (parityOf (β₀ ++ β ++ γ)) / 2 ^ (parityOf (β₀ ++ β)).length = u), wtβ β)
          - 1 / 2 ^ (parityOf γ).length| ≤ 2 * τ)
    (hbad : ∀ γ : List Bool, γ.length = K →
      (((Finset.range (2 ^ (parityOf γ).length)).filter (fun u =>
        ¬ WinClose (bitsMSB (parityOf γ).length u) 0 (parityOf γ).length J δ')).card : ℚ) ≤
        η * 2 ^ (parityOf γ).length)
    (k j : ℕ) (hj : n₀ ≤ j) (hjk : j + K ≤ k) :
    ∑ β ∈ blockChoices k,
      wtβ β * (if htwGood K J δ' (β₀ ++ β) (β₀.length + j) then 0 else 1) ≤ 2 * τ + η :=
  Gen.htw_cut_prob Gen.tModel.R Gen.tModel.R_lt β₀ K J δ' τ η n₀ hkey hbad k j hj hjk

open Classical in
/-- **Markov's inequality** (weighted counting): if the expectation of `X` is at most `T c`, then `X ≤ θ T` with probability at least `1 - c/θ`. -/
theorem htw_markov (β₀ : List Bool) (k : ℕ) (X : List Bool → ℕ) (T : ℕ) (hT : 0 < T) (θ c : ℚ)
    (hθ : 0 < θ) (hsum : ∑ β ∈ blockChoices k, wtβ β * (X (β₀ ++ β) : ℚ) ≤ T * c) :
    1 - c / θ ≤ Prσ β₀ k (fun β => (X β : ℚ) ≤ θ * T) :=
  Gen.htw_markov β₀ k X T hT θ c hθ hsum

end Collatz.Arctic
