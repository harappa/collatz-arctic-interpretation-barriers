/-
The statement of `HKeyTop`, the central claim of the route to `HTerrasWin` by the swap argument (Theorem B.7 of the paper). **The statement is frozen** (proved as `KeyFinal.hKeyTop`; it is an intermediate proposition and does not affect the faithfulness of the statements of the main theorems; the written argument of Appendix B.2 has had an internal independent review).

* Claim: after the first blocks `β₀`, choose `n` blocks `β` independently (`X'` with probability 3/10, `Y'` with 7/10; the paper's `k` blocks), and then put
  `K` fixed blocks `γ`. The law of the bits of the Terras residue `r` of the whole parity word in the part of `γ` (the quotient of `r` by `2^{|parityOf(β₀++β)|}`,
  with `|parityOf γ|` digits) is within total variation distance `τ` of uniform when `n` is large (uniformly in `β₀` and `γ`).
* Instead of the Fourier argument on the phases of swaps (Appendix C of Paper II), the plan was to use that the swap `X'Y' ↔ Y'X'` acts on `r` as an exact translation
  (by `-2^{|P|+9} 3^{-(a_P+7)}` modulo `2^m`; Lemma B.5), the L² identity for indicator functions of intervals (Proposition B.6), and the mixing of `#Y'` modulo `2^V`
  (Doeblin) (the plan at the time the statement was written; it was carried out, see `KeyFinal.hKeyTop`).
* `HTerrasWin` was expected to follow from `HKeyTop` (split the interval of blocks into pieces of `K` blocks, use the window frequencies of the bits of each piece,
  and apply Markov's inequality to the number of bad pieces); this is `HTWFromKey.hTerrasWin_of_key`.
-/
import CollatzProof.Arctic.CoreHyp

namespace Collatz.Arctic

open Classical in
/-- **Hypothesis `HKeyTop`** (the central claim of the swap argument: uniformity of the top bits of a single piece; Theorem B.7). -/
def HKeyTop : Prop :=
  ∀ (K : ℕ) (τ : ℚ), 0 < τ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (β₀ γ : List Bool), γ.length = K →
    ∑ u ∈ Finset.range (2 ^ (parityOf γ).length),
      |(∑ β ∈ (blockChoices n).filter (fun β =>
          terrasR (parityOf (β₀ ++ β ++ γ)) / 2 ^ (parityOf (β₀ ++ β)).length = u), wtβ β)
        - 1 / 2 ^ (parityOf γ).length| ≤ 2 * τ

end Collatz.Arctic
