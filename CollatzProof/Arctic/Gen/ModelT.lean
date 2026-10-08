/-
Check of the statements of the generic layer for $T$: the `SwapR` and `QuadR` of `Model.lean` have the existing lemmas for $T$
(`KeyTerras.km_swap_one`, `ARuleFive.aRule_quad`) as instances.

Separated from `Model.lean` because it imports the proofs for $T$. Not in the closure of the main theorem for $H$ (a file for checking).
-/
import CollatzProof.Arctic.Gen.Model
import CollatzProof.Arctic.KeyTerras
import CollatzProof.Arctic.ARuleFive

namespace Collatz.Arctic.Gen

open Collatz.Arctic

/-- The translation by swaps for $T$ is `SwapR tModel.R 9 7` (Lemma B.5 (ii); `km_swap_one` applied to block sequences). -/
theorem tModel_swap : SwapR tModel.R 9 7 := by
  intro φ χ
  have e1 : parityOf (φ ++ [true, false] ++ χ) = parityOf φ ++ blkX ++ blkY ++ parityOf χ := by
    simp [parityOf]
  have e2 : parityOf (φ ++ [false, true] ++ χ) = parityOf φ ++ blkY ++ blkX ++ parityOf χ := by
    simp [parityOf]
  simp only [tModel]
  rw [e2, e1]
  exact km_swap_one _ _ _ rfl

/-- The quadratic use of the carry rules of $T$ has the form `QuadR` (it is `ARule.aRule_quad` itself). -/
theorem tModel_quad (b d : ℕ) (hb : b < 2) (hd : d ≤ 2) :
    QuadR T (fun n => 2 ≤ n) canDeriv (aRule b d) :=
  ARule.aRule_quad b d hb hd

end Collatz.Arctic.Gen
