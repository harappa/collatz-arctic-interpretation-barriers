/-
The statements of the hypotheses from which `AutoCore` is assembled; all three are proved (Appendix B and Section 6; see `Summary.lean`). **These statements are frozen** (two internal independent reviews, with no major or moderate findings).

`AutoCore` (`AutoStatement.lean`) is assembled from the following three hypotheses of finite form (`CoreFinal.autoCore_of_hyps`).
They form layer D (window frequencies) and layer E (limits of random max-plus products) of the assembly.

* `HSP` (layer E; proved as `hsp_holds`, Corollary B.4 in Appendix B.1): for the process restricted to a strongly connected component `C` and started from a set `S` of start indices that never dies, the proportion of words for which the value of every live index is
  at least `(Λ_C - ε)L` is at least `1 - ε` (for large `L`). This is the finite form (Corollary B.4) of an almost-sure convergence statement,
  weakened to convergence in probability (since the process never dies, the survival event is everything). `Λ_C` is `RateDefs.rate`.
  If `S ⊆ C` never dies then neither does `C`, and −∞ is never read as 0, so `rate` is the (Fekete) limit of the maximal expectation of the whole process,
  which equals `Λ_C`. `StrongConnIn` allows the empty word,
  which matters only for a one-point component, and then `NeverDies` forces a self-loop. `S.Nonempty` follows from `NeverDies`
  (redundant, harmless). Independent of Collatz.
* `HTerrasWin` (layer D; proved as `hTerrasWin`, Theorem B.8 in Appendix B.2): in the model of `T` (Section 6.1), with probability close to 1 the frequencies of the windows of bits over an interval of block indices are close to uniform
  (Theorem B.8; proved by the swap argument of Appendix B.2, not by the Fourier argument of Appendix C of Paper II). Windows are counted here if they lie inside the interval; one may also count the windows whose lowest position
  lies in the interval. The difference is `J - 1` windows, asymptotically negligible against the number of windows of the interval (about `8ε₀k`). Uniformity
  in the interval is equivalent to the form for every deterministic sequence of intervals (by a subsequence argument).
* `HLeftUse` (layer D; proved as `hLeftUse`, Proposition 6.7(ii) in Section 6.4, from Proposition B.9 in Appendix B.3): with probability close to 1, every left-end rule is used at least `c'k` times, for every `t` (Proposition 6.7;
  the discrepancy of the walk of the logarithms `{a_{≤i} log₂3 + log₂t}` of the mantissas of the block boundary points,
  Proposition B.9). It is a statement about the frequency of top windows of the block boundary points. The written argument fixes `t`, but the size of the Weyl sums
  does not depend on `t`, and by the Erdős–Turán inequality the discrepancy is small simultaneously for all translations `log₂ t`, which gives the form
  uniform in `t` (second internal review).

Probabilities are written as sums of weights over the choices of blocks of the model of `T` (`X'` with probability 3/10 and `Y'` with 7/10, independently) (`Prσ`).
-/
import CollatzProof.Arctic.Config
import CollatzProof.Arctic.TModel

namespace Collatz.Arctic

open Matrix

/-! ## The model of `T` (Section 6.1) -/

/-- The block `X' = 10110110` (8 steps, 5 of them odd; `true` = odd step). -/
def blkX : List Bool := [true, false, true, true, false, true, true, false]

/-- The block `Y' = 10110110110` (11 steps, 7 of them odd). -/
def blkY : List Bool := [true, false, true, true, false, true, true, false, true, true, false]

/-- The parity word of a choice of blocks (`true` = `X'`; the first block gives the first steps). -/
def parityOf (β : List Bool) : List Bool := β.flatMap (fun x => if x then blkX else blkY)

/-- The weight of a choice of blocks (`X'` has 3/10 and `Y'` has 7/10; `p = 0.3` as in Section 6.1). -/
def wtβ (β : List Bool) : ℚ := (β.map (fun x => if x then (3 / 10 : ℚ) else 7 / 10)).prod

/-- All choices of `k` blocks. -/
def blockChoices (k : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin k → Bool)).image List.ofFn

open Classical in
/-- The probability on the side of `σ`: the probability of the event `E` for the whole choice of blocks `β₀ ++ β`, when the first
blocks `β₀` are fixed and the remaining `k` blocks are chosen independently. -/
noncomputable def Prσ (β₀ : List Bool) (k : ℕ) (E : List Bool → Prop) : ℚ :=
  ∑ β ∈ (blockChoices k).filter (fun β => E (β₀ ++ β)), wtβ β

/-- The number `L_i` of bits of the first `i` blocks. -/
def blockEnd (β : List Bool) (i : ℕ) : ℕ := (parityOf (β.take i)).length

/-! ## The hypotheses -/

/-- Strongly connected within the set `C` of indices (any two indices are joined by a path of finite edges, of either digit, that stays inside `C`). -/
def StrongConnIn {D : ℕ} (A : Interp D) (C : Finset (Fin D)) : Prop :=
  ∀ i ∈ C, ∀ j ∈ C, ∃ w : Word, IsDigits w ∧ ev (restrictI C A) w i j ≠ 0

/-- The process restricted to `C` and started from the set `S` of start indices dies on no digit word. -/
def NeverDies {D : ℕ} (A : Interp D) (C S : Finset (Fin D)) : Prop :=
  ∀ w : Word, IsDigits w → ∃ i ∈ S, ∃ j, ev (restrictI C A) w i j ≠ 0

/-- The value at the index `j` after reading the word `w` in the process restricted to `C`, started with value 0 on `S` and `-∞` elsewhere. -/
def rowVal {D : ℕ} (A : Interp D) (C S : Finset (Fin D)) (w : Word) (j : Fin D) : Arc :=
  ∑ i ∈ S, ev (restrictI C A) w i j

open Classical in
/-- **Hypothesis HSP** (layer E; the finite form, Corollary B.4; proved, Appendix B.1). -/
def HSP : Prop :=
  ∀ (D : ℕ) (A : Interp D) (C S : Finset (Fin D)), StrongConnIn A C → S ⊆ C → S.Nonempty →
    NeverDies A C S → ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀,
      (1 - ε) * 2 ^ L ≤ ((((wordsOfLen L).filter (fun w => ∀ j (v : ℕ), rowVal A C S w j = Arc.fin v →
        (rate A C - ε) * L ≤ v)).card : ℕ) : ℝ)

/-- **Hypothesis HTerrasWin** (layer D; Theorem B.8; proved, Appendix B.2): fix the first blocks `β₀` and choose `k` more. The probability that the frequencies of the windows of length `J`
of the bits of an interval `[i₁, i₂)` of block indices (of width at least `ε₀k`; the positions `[m - L_{i₂}, m - L_{i₁})` of the representation of `r_σ` from the top)
are within `δ` of uniform is at least `1 - ε` when `k` is large (uniformly in the interval). -/
def HTerrasWin : Prop :=
  ∀ (β₀ : List Bool) (J : ℕ) (δ ε₀ ε : ℚ), 0 < δ → 0 < ε₀ → 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    ∀ i₁ i₂ : ℕ, β₀.length ≤ i₁ → (i₁ : ℚ) + ε₀ * k ≤ i₂ → i₂ ≤ β₀.length + k →
      1 - ε ≤ Prσ β₀ k (fun β =>
        WinClose (bitsMSB (parityOf β).length (terrasR (parityOf β)))
          ((parityOf β).length - blockEnd β i₂) ((parityOf β).length - blockEnd β i₁) J δ)

/-- **Hypothesis HLeftUse** (layer D; the uses of the left-end rules, Proposition 6.7(ii); proved, Section 6.4 and Appendix B.3): for fixed first blocks `β₀` there is a constant
`c > 0` such that, when `k` is large, with probability at least `1 - ε`, for every `t ≥ 2^m`,
each left-end rule is used at least `c k` times in the canonical derivation from `x₀ = r_σ + 2^m t` to `T^m x₀`. -/
def HLeftUse : Prop :=
  ∀ β₀ : List Bool, ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ d ≤ 2,
    1 - ε ≤ Prσ β₀ k (fun β => ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      c * k ≤ (usesOrbit (leftRule d)
        (terrasR (parityOf β) + 2 ^ (parityOf β).length * t) (parityOf β).length : ℚ))

end Collatz.Arctic
