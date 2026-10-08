/-
Definition of the rate `Λ_C` of a component (Section 6.3, Appendix B.1; used in the proof of Lemma 6.5).
`fmax` is the function `f_C` of the paper: the largest weight of a path that reads the word and stays in `C`, or 0 if there is none.

* The largest entry of the product of the matrices restricted to a set of indices `C`, read as 0 if it is `-∞` (`fmax`), is subadditive
  (`fmax(uv) ≤ fmax(u) + fmax(v)`). One could cut at a negative constant instead; since rates are used only for surviving components (whose largest entry is always finite),
  cutting at 0 gives the same value.
* The rate is the infimum of `avgMax L / L`, where `avgMax L` is the average over uniform words of length `L` (equal to the limit by Fekete's lemma).
* On a surviving component this equals the almost sure growth rate (the limit of the expectations); this is not used
  (Appendix B.1). The hypothesis for the lower bound (the finite form, Corollary B.4) is stated with this `rate`.
-/
import CollatzProof.Arctic.Window

namespace Collatz.Arctic

/-- The digit matrices restricted to a set of indices `C` (`-∞` outside `C × C`). -/
def restrictI {D : ℕ} (C : Finset (Fin D)) (A : Interp D) : Interp D :=
  fun s i j => if i ∈ C ∧ j ∈ C then A s i j else 0

/-- The largest entry of a matrix (arctic sum). -/
def maxEnt {D : ℕ} (M : AMat D) : Arc := ∑ i, ∑ j, M i j

/-- Read an arctic value as a natural number (`-∞` as 0). -/
def natOr0 (a : Arc) : ℕ := (Arc.val a).unbotD 0

/-- The largest entry of the product along the word `w` restricted to `C` (`-∞` as 0). -/
def fmax {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (w : Word) : ℕ :=
  natOr0 (maxEnt (ev (restrictI C A) w))

/-- The average of `fmax` over uniform words of length `L`. -/
def avgMax {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (L : ℕ) : ℚ :=
  (∑ w ∈ wordsOfLen L, (fmax A C w : ℚ)) / 2 ^ L

/-- The rate of a component `C`, `Λ_C := inf_{L ≥ 1} avgMax L / L` (equal to the limit by Fekete's lemma). -/
noncomputable def rate {D : ℕ} (A : Interp D) (C : Finset (Fin D)) : ℝ :=
  ⨅ L : ℕ, ((avgMax A C (L + 1) : ℚ) : ℝ) / ((L + 1 : ℕ) : ℝ)

end Collatz.Arctic
