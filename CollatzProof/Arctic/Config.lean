/-
Common definitions for the assembly (Theorem 6.8): supports of the automaton, types of words, rates of classes, the rate `α_z(I)` of a configuration.
Rates and configurations as at the beginning of Section 6.3; used in Lemmas 6.5, 6.6 and Theorem 6.8.

* The set of indices is `Fin D`. The digit matrices are `A Letter.f` (0) and `A Letter.t` (1). The support is the set of positions of finite entries.
* The idempotent `E` of the minimal ideal, the classes `Cls E hE`, the rows `beta` and the components `comp` are in `MinIdeal.lean` and `Transport.lean` (Lemmas 6.2 and 6.3).
* The rate of a class `j` is `classRate j := rate A (C(j))` (`RateDefs.lean`).
* `α_z(I) := max{Λ_{C(j)} : j ∈ I, j ≤ p for some p ∈ I that exits by z}` (the paper's
  `α_z(I) = max{Λ_I(p) : p ∈ I, p exits by z}` with `Λ_I(p) = max{Λ_{C(j)} : j ≤ p, j ∈ I}`, merged into one maximum).
  It is the supremum of a finite set (0 if the set is empty).
-/
import CollatzProof.Arctic.TransportStay
import CollatzProof.Arctic.RateDefs

namespace Collatz.Arctic

open MinIdeal Matrix

variable {D : ℕ}

/-- The support of a matrix (positions of the finite entries). -/
def suppRel (M : AMat D) : BRel (Fin D) := fun i j => M i j ≠ 0

/-- The support of the matrix of the digit 0 (`f`). -/
def B0 (A : Interp D) : BRel (Fin D) := suppRel (A Letter.f)

/-- The support of the matrix of the digit 1 (`t`). -/
def B1 (A : Interp D) : BRel (Fin D) := suppRel (A Letter.t)

/-- Digit words (words in `f` and `t` only). -/
def IsDigits (w : Word) : Prop := ∀ s ∈ w, s = Letter.f ∨ s = Letter.t

/-- A digit letter as a `Bool` (`f ↦ false`, `t ↦ true`; the words of `typ` in `TransportStay.lean`). -/
def toBool (s : Letter) : Bool := decide (s = Letter.t)

/-- The value vector `u ⊗ A_w` after reading the word `w` from the row vector `u`. -/
def vecAfter (u : Fin D → Arc) (A : Interp D) (w : Word) : Fin D → Arc := u ᵥ* ev A w

/-- The support of a value vector. -/
def suppV (v : Fin D → Arc) : Set (Fin D) := {j | v j ≠ 0}

section Classes

variable {E : BRel (Fin D)} (hE : E * E = E)

open Classical in
/-- The rate `Λ_{C(j)}` of a class `j` (the rate of the component `C(j)`). -/
noncomputable def classRate (A : Interp D) (j : Cls E hE) : ℝ :=
  rate A (Set.toFinset (comp (B0 A) (B1 A) hE j))

/-- The class `p` exits by the word `z`: reading `z` from some index of `β_p` reaches the support of `c`. -/
def Exitable (A : Interp D) (c : Fin D → Arc) (z : Word) (p : Cls E hE) : Prop :=
  ∃ k, beta hE p k ∧ ∃ j, ev A z k j ≠ 0 ∧ c j ≠ 0

/-- In the configuration `I`, the set of rates of occupied classes `j ∈ I` below some class `p ∈ I` that exits. -/
def visibleRates (A : Interp D) (c : Fin D → Arc) (z : Word) (I : Set (Cls E hE)) : Set ℝ :=
  {r | ∃ j ∈ I, ∃ p ∈ I, j ≤ p ∧ Exitable hE A c z p ∧ r = classRate hE A j}

/-- The rate `α_z(I)` of a configuration (the supremum of a finite set; 0 if it is empty). -/
noncomputable def alphaZ (A : Interp D) (c : Fin D → Arc) (z : Word) (I : Set (Cls E hE)) : ℝ :=
  sSup (visibleRates hE A c z I)

end Classes

end Collatz.Arctic
