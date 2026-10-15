/-
**`HTerrasWin` follows from `HKeyTop`** (the swap argument; Theorem B.8). The Fourier argument of the companion paper
(Paper II, Appendix C) is replaced by `HKeyTop` (uniformity of the top bits of a single chunk).

Since revision r5 the proof is `Gen.hTerrasWinR_of_key` in `Gen/HTWFromKey.lean` (a copy with the residue `R` as a parameter; of the residue it
uses only `R_lt` and `R_prefix`). This file has the thin theorems for the model `Gen.tModel` of `T`, with unchanged statements (the frozen
`HTerrasWin` and `HKeyTop` are instances of the general forms by `Gen.hTerrasWin_iff` and `Gen.hKeyTop_iff`).

Outline of the proof (`Gen/HTWFromKey.lean`):
1. **Chunks**: split the interval `[i₁, i₂)` of block indices into chunks `[i₁ + tK, i₁ + (t+1)K)` of `K` blocks (`t < T`,
   `T = ⌊(i₂ - i₁)/K⌋`) and discard the final remainder. By Terras consistency, the bits of a chunk are the expansion of the quotient of the residue up to the end
   of the chunk by `2^{L_a}` (`htw_bits_split`).
2. **Probability that a chunk is good**: if at least `n₀` random blocks precede the chunk, then by `HKeyTop` the law of the bits is within `τ` of uniform,
   and the window frequencies of a uniform word are within `δ/2` with probability at least `1 - η` (`win_bad_count`). Hence a chunk is bad with probability
   at most `2τ + η` (`htw_cut_prob`). Chunks meeting the first `n₀` blocks of the interval are counted as bad.
3. **Markov**: the expected number of bad chunks is at most `T(2τ + η)`; with `θ = δ/44`, with probability at least `1 - (2τ + η)/θ = 1 - ε` it is
   at most `θT` (`htw_markov`).
4. **Deterministic part** (`htw_det`): if at most `n₀ + θT` chunks are bad, the lengths of the bad chunks, the remainder and the boundary windows add up to at most
   `δ/2` times the number of windows of the interval, and the window frequencies of the whole interval are within `δ` of uniform (`htw_combine`).
5. No union bound is used (one interval at a time). `k₀` does not depend on `β₀`; it depends only on `ε₀`, `ε`, `δ`, `J` and the `n₀` of `HKeyTop`.

-/
import CollatzProof.Arctic.HTWProb
import CollatzProof.Arctic.Gen.HTWFromKey
import CollatzProof.Arctic.CoreU

namespace Collatz.Arctic

open Finset

open Classical in
/-- **Deterministic part** (assembling the chunks): split the interval `[i₁, i₂)` of block indices into chunks of `K` blocks
`[i₁ + tK, i₁ + (t+1)K)` (`t < T`, `TK ≤ i₂ - i₁ < (T+1)K`). If at most `B` chunks are bad and
`11K + 11KB + TJ + 1 ≤ (δ/2)(8(i₂ - i₁) + 1 - J)`, the window frequencies of the interval are within `δ` of uniform (`Gen.htw_det`). -/
theorem htw_det (β : List Bool) {K J T i₁ i₂ : ℕ} (hJ : 1 ≤ J) {δ : ℚ} (hδ : 0 < δ)
    (hT1 : T * K ≤ i₂ - i₁) (hT2 : i₂ - i₁ < T * K + K) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ β.length)
    (hJW : J ≤ 8 * (i₂ - i₁)) (B : ℚ)
    (hB : ((((range T).filter (fun t => ¬ htwGood K J (δ / 2) β (i₁ + t * K))).card : ℕ) : ℚ) ≤ B)
    (harith : 11 * (K : ℚ) + 11 * K * B + T * J + 1 ≤
      δ / 2 * ((8 * (i₂ - i₁) + 1 - J : ℕ) : ℚ)) :
    WinClose (bitsMSB (parityOf β).length (terrasR (parityOf β)))
      ((parityOf β).length - blockEnd β i₂) ((parityOf β).length - blockEnd β i₁) J δ :=
  Gen.htw_det Gen.tModel.R Gen.tModel.R_lt Gen.tModel.R_prefix β hJ hδ hT1 hT2 hi hi₂ hJW B hB harith

/-- **`HTerrasWin` follows from `HKeyTop`** (the swap argument; the instance of `Gen.hTerrasWinR_of_key` for `T`). -/
theorem hTerrasWin_of_key (hkey : HKeyTop) : HTerrasWin :=
  Gen.hTerrasWin_iff.mpr
    (Gen.hTerrasWinR_of_key Gen.tModel.R Gen.tModel.R_lt Gen.tModel.R_prefix (Gen.hKeyTop_iff.mp hkey))

end Collatz.Arctic
