/-
Main part of the assembly of Theorem 6.8 of the paper: existence of a good point on the point family (`good_point`).
Proof of Theorem 6.8: intersect the events for `σ` (`sigma_good`) and the events for `t` (`exists_good_x`), and obtain
the upper bound at the starting point (Lemma 6.5) and the lower bound at the end point (Lemma 6.6) at one point.
-/
import CollatzProof.Arctic.CorePoint
import CollatzProof.Arctic.CoreGood
import CollatzProof.Arctic.CoreLowFam
import CollatzProof.Arctic.CoreSigma
import CollatzProof.Arctic.CoreArith
import CollatzProof.Arctic.FamilyUses

namespace Collatz.Arctic

open MinIdeal Matrix Classical

variable {D : ℕ}

theorem isDigits_binTail (n : ℕ) : IsDigits (binTail n) := by
  intro s hs
  unfold binTail at hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
  split_ifs <;> simp

/-- `LowerAt` is monotone in the constant `Cst`. -/
theorem lowerAt_mono {E : BRel (Fin D)} (u : Fin D → Arc) (A : Interp D) (hE : E * E = E)
    (us z : Word) (ε Cst Cst' : ℝ) (h : Cst ≤ Cst') (ω : Word) :
    Lower.LowerAt u A hE us z ε Cst ω → Lower.LowerAt u A hE us z ε Cst' ω := by
  intro hl p hp j hj hjp b hb v hv
  have := hl p hp j hj hjp b hb v hv
  linarith

/-- `α_z(I) ≥ 0`. -/
theorem alphaZ_nonneg {E : BRel (Fin D)} (hE : E * E = E) (A : Interp D) (c : Fin D → Arc) (z : Word)
    (I : Set (Cls E hE)) : 0 ≤ alphaZ hE A c z I :=
  Real.sSup_nonneg (by rintro r ⟨j, -, -, -, -, -, rfl⟩; exact rate_nonneg _ _)

end Collatz.Arctic
