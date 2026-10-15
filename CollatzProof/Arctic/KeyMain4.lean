/-
**Theorem B.7 (KEY)** and its finite form **`HKeyTop`** in the swap argument: the names for `T`.
The analytic ingredients (`SpecCells`, `SpecQavg`, `SpecNine`, `SpecDoeblin` of `KeySpec.lean`: (Q3), Proposition B.6,
the order of 9 and the Doeblin bound) are taken as hypotheses (discharged by the proofs in `KeyAnal*.lean`).

Since revision r5 the proofs are in the general layer `Gen/KeyMain4.lean` (a copy with the residue `R` and the swap constants `e₂`, `e₃` as
parameters). This file has only thin theorems for the model `Gen.tModel` of `T` (residue `terrasR (parityOf ·)`) and the swap translation
`Gen.tModel_swap` (`e₂ = 9`, `e₃ = 7`, Lemma B.5), with unchanged statements (`Gen.tModel.R β` is definitionally `terrasR (parityOf β)`).

* `km_key_pos`: Theorem B.7 (`ℓ ≥ 1`). The choice of the constants and the outline of the proof are in the comments of `Gen/KeyMain4.lean`.
* `km_key_upto`: uniformly in `ℓ ≤ L₀`.
* `hKeyTop_of_specs`: the finite form `HKeyTop`.

`KeyMain3.lean` (the formula for a single `(β_e, L)`, cited in the paper), which the proof for `T` used before this change, is not used here;
the root module `Paper.lean` keeps it in its import closure.

-/
import CollatzProof.Arctic.Gen.KeyMain4
import CollatzProof.Arctic.Gen.ModelT
import CollatzProof.Arctic.HTWKey

namespace Collatz.Arctic

open Finset

/-- **Theorem B.7 (KEY)**, `ℓ ≥ 1` (the instance of `Gen.km_key_pos` for `T`). -/
theorem km_key_pos (hC : SpecCells) (hQ : SpecQavg) (hN : SpecNine) (hD : SpecDoeblin)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ β₀ γ : List Bool, (parityOf γ).length = ℓ →
      ∑ u ∈ Finset.range (2 ^ ℓ),
        |∑ β ∈ (blockChoices n).filter (fun β =>
            terrasR (parityOf (β₀ ++ β ++ γ)) / 2 ^ (parityOf (β₀ ++ β)).length = u), (wtβ β : ℝ)
          - 1 / 2 ^ ℓ| ≤ 2 * τ :=
  Gen.km_key_pos Gen.tModel.R_lt (by norm_num) Gen.tModel_swap hC hQ hN hD ℓ hℓ τ hτ

/-- Theorem B.7 uniformly in `ℓ ≤ L₀` (the instance of `Gen.km_key_upto` for `T`). -/
theorem km_key_upto (hC : SpecCells) (hQ : SpecQavg) (hN : SpecNine) (hD : SpecDoeblin)
    (τ : ℝ) (hτ : 0 < τ) (L₀ : ℕ) :
    ∃ n₀ : ℕ, ∀ ℓ ≤ L₀, ∀ n ≥ n₀, ∀ β₀ γ : List Bool, (parityOf γ).length = ℓ →
      ∑ u ∈ Finset.range (2 ^ ℓ),
        |∑ β ∈ (blockChoices n).filter (fun β =>
            terrasR (parityOf (β₀ ++ β ++ γ)) / 2 ^ (parityOf (β₀ ++ β)).length = u), (wtβ β : ℝ)
          - 1 / 2 ^ ℓ| ≤ 2 * τ :=
  Gen.km_key_upto Gen.tModel.R_lt (by norm_num) Gen.tModel_swap hC hQ hN hD τ hτ L₀

/-- **The finite form `HKeyTop`**: given the analytic ingredients ((Q3), Proposition B.6, the order of 9 and the Doeblin bound),
`HKeyTop` holds (the instance of `Gen.hKeyTopR_of_specs` for `T`). -/
theorem hKeyTop_of_specs (hC : SpecCells) (hQ : SpecQavg) (hN : SpecNine) (hD : SpecDoeblin) :
    HKeyTop :=
  Gen.hKeyTop_iff.mpr (Gen.hKeyTopR_of_specs Gen.tModel.R_lt (by norm_num) Gen.tModel_swap hC hQ hN hD)

end Collatz.Arctic
