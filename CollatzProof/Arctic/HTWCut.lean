/-
Deriving `HTerrasWin` from `HKeyTop` (the swap argument): the names for `T` of the deterministic part. The main theorem is in `HTWFromKey.lean`,
the probabilistic part in `HTWProb.lean`. This is the proof of Theorem B.8 (window frequencies).

Since revision r5 the proofs are in the general layer `Gen/HTWCut.lean` (a copy with the residue `R` as a parameter; the deviation of the empirical
distribution of windows and the passage from chunks to intervals do not depend on the residue). This file keeps only the names cited in the paper
and the names used by other files (`Nat/W3Gap.lean`, `Nat/W3hTail.lean`, `KeyMain3.lean`, `HTWProb.lean`, `HTWFromKey.lean`); the definitions are
unchanged, and the theorems are thin theorems for the model `Gen.tModel` of `T` (residue `terrasR (parityOf ·)`), with unchanged statements.

* `htwDev`: the deviation from the uniform distribution of the empirical distribution of the windows of length `J` starting in the set `S` (the sum of absolute differences, times `|S|`).
* `htw_combine`: split the interval `[A, p 0)` into chunks `[p (t+1), p t)` (`t < T`, `p` decreasing) and a remainder `[A, p T)`. If the window frequencies of the good chunks
  (`G`) are within `δ'`, the total deviation is at most `2δ'N + 2 × (remainder + total length of the bad chunks + boundary windows `TJ` + 1)`
  (from chunk frequencies to interval frequencies).
* Chunks: the bits of the chunk `[a, a + K)` of block indices (positions `[m - L_{a+K}, m - L_a)` in the expansion of `r_σ` from the top) are
  the `htwLen`-digit expansion of the quotient `htwVal` of the residue up to the chunk by `2^{L_a}` (Terras consistency, `htw_bits_split`).
  A chunk is good (`htwGood`) if the window frequencies of that expansion are within `δ` of uniform. The quantity of `HKeyTop` is `htwCutVal`.

-/
import CollatzProof.Arctic.Gen.HTWCut

namespace Collatz.Arctic

open Finset

/-! ## Deviation of the empirical distribution of windows -/

/-- The deviation from the uniform distribution of the empirical distribution of the windows of length `J` starting in the set `S` (the sum of absolute differences, times `|S|`). -/
def htwDev (w : Word) (J : ℕ) (S : Finset ℕ) : ℚ :=
  ∑ v ∈ wordsOfLen J, |∑ i ∈ S, ((if window w i J = v then (1 : ℚ) else 0) - 1 / 2 ^ J)|

/-! ## From chunks to intervals -/

/-- **From chunks to intervals**: split the interval `[A, p 0)` into chunks `[p (t+1), p t)` (`t < T`) and a remainder `[A, p T)`. If the
window frequencies of the good chunks (`t ∈ G`) are within `δ'`, the total deviation is at most `2δ'N` plus twice the sum of the remainder, the
lengths of the bad chunks and the boundary windows (at most `TJ`) (`Gen.htw_combine`). -/
theorem htw_combine (w : Word) {J : ℕ} (hJ : 1 ≤ J) {δ' : ℚ} (hδ' : 0 ≤ δ') {A T : ℕ} {p : ℕ → ℕ}
    (hanti : ∀ t < T, p (t + 1) ≤ p t) (hA : A ≤ p T)
    (G : Finset ℕ) (hG : G ⊆ range T) (hgood : ∀ t ∈ G, WinClose w (p (t + 1)) (p t) J δ') :
    htwDev w J (Ico A (p 0 + 1 - J)) ≤
      2 * δ' * ((p 0 + 1 - J - A : ℕ) : ℚ) +
        2 * ((p T - A + ∑ t ∈ range T \ G, (p t - p (t + 1)) + T * J + 1 : ℕ) : ℚ) :=
  Gen.htw_combine w hJ hδ' hanti hA G hG hgood

/-! ## Chunks -/

/-- The quantity of `HKeyTop`: the quotient of the residue of `β₀ ++ β ++ γ` by `2^{|parityOf (β₀ ++ β)|}` (the bits of the part `γ`). -/
def htwCutVal (β₀ β γ : List Bool) : ℕ :=
  terrasR (parityOf (β₀ ++ β ++ γ)) / 2 ^ (parityOf (β₀ ++ β)).length

/-- The value of the chunk `[a, a + K)` of block indices: the quotient of the residue up to the end of the chunk by `2^{L_a}`. -/
def htwVal (K : ℕ) (β : List Bool) (a : ℕ) : ℕ :=
  terrasR (parityOf (β.take (a + K))) / 2 ^ (parityOf (β.take a)).length

/-- The number of bits of the chunk `[a, a + K)`. -/
def htwLen (K : ℕ) (β : List Bool) (a : ℕ) : ℕ := (parityOf ((β.drop a).take K)).length

/-- The chunk `[a, a + K)` is good: the window frequencies of the bits of the chunk are within `δ` of uniform. -/
def htwGood (K J : ℕ) (δ : ℚ) (β : List Bool) (a : ℕ) : Prop :=
  WinClose (bitsMSB (htwLen K β a) (htwVal K β a)) 0 (htwLen K β a) J δ

theorem htw_blockEnd_add (β : List Bool) (a K : ℕ) :
    blockEnd β (a + K) = blockEnd β a + htwLen K β a :=
  Gen.htw_blockEnd_add β a K

/-- The interval `[i, i + d)` of block indices (inside `β`) has at least `8d` bits. -/
theorem htw_blockEnd_ge (β : List Bool) (i d : ℕ) (h : i + d ≤ β.length) :
    blockEnd β i + 8 * d ≤ blockEnd β (i + d) :=
  Gen.htw_blockEnd_ge β i d h

/-- **The bits of a chunk** (Terras consistency): the `m`-digit expansion of `r_σ` is `X ++ (the expansion of the value of the chunk) ++ Y`,
with `|X| = m - L_{a+K}` (`Gen.htw_bits_split`). -/
theorem htw_bits_split (β : List Bool) (a K : ℕ) :
    ∃ X Y : Word, bitsMSB (parityOf β).length (terrasR (parityOf β)) =
      X ++ bitsMSB (htwLen K β a) (htwVal K β a) ++ Y ∧
      X.length = (parityOf β).length - blockEnd β (a + K) :=
  Gen.htw_bits_split Gen.tModel.R Gen.tModel.R_lt Gen.tModel.R_prefix β a K

end Collatz.Arctic
