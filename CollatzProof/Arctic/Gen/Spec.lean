/-
Statements of the outputs of the generic layer. **The statements are frozen**.

The files of the generic layer prove these `Prop`s as theorems (e.g. `theorem specAutoRule : SpecAutoRule`). The assembly takes them
as hypotheses (`htpdb_of_specs` in `HTPDB/Spec.lean`). The notes give the names of the corresponding theorems for $T$.

* `SpecAutoRule`: the assembly at the level of the model (the one-rule form of `CoreFinal.autoCore_of_hyps`).
* `SpecKeyOfSwap`: the swap argument (`KeyMain4.hKeyTop_of_specs` with the residue as an argument; the swap exponent `ν₂` (the argument `e₂`) is 8 for $H$ and 9 for $T$).
* `SpecWinOfKey`: `HTWFromKey.hTerrasWin_of_key` with the residue as an argument.
* `SpecQuadRule` (the general part for the carry rules): the general form of `ARuleMain.autoCore_aRule` (a linear upper bound for values and quadratic use).
-/
import CollatzProof.Arctic.Gen.Model

namespace Collatz.Arctic.Gen

open Collatz.Arctic

/-- Output of the assembly: from the hypotheses on window frequencies and on the uses of the rule `ρ`, the conclusion of `AutoCore` for `ρ` (`HSP` does not depend on Collatz). -/
def SpecAutoRule : Prop :=
  ∀ (M : BlockModel) (cd : ℕ → List Rule) (ρ : Rule), HSP → HTerrasWinR M.R →
    HUseR M.f M.R M.steps cd ρ → AutoRuleG M.f M.dom cd ρ

/-- Output of the swap argument: from the translation by swaps (`ν₂ = e₂ ∈ {8, 9}`), the uniformity of the top bits of a single chunk. -/
def SpecKeyOfSwap : Prop :=
  ∀ R : List Bool → ℕ, (∀ β, R β < 2 ^ (parityOf β).length) →
    (∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁) →
    ∀ e₂ e₃ : ℕ, 8 ≤ e₂ → e₂ ≤ 9 → SwapR R e₂ e₃ → HKeyTopR R

/-- Output for the window frequencies: from the uniformity of a single chunk, the window frequencies on intervals of block indices. -/
def SpecWinOfKey : Prop :=
  ∀ R : List Bool → ℕ, (∀ β, R β < 2 ^ (parityOf β).length) →
    (∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁) →
    HKeyTopR R → HTerrasWinR R

/-- Output for the carry rules (general part): from quadratic use, the conclusion of `AutoCore` for that rule (it uses neither that values do not increase nor that they are
finite). -/
def SpecQuadRule : Prop :=
  ∀ (f : ℕ → ℕ) (dom : ℕ → Prop) (cd : ℕ → List Rule) (ρ : Rule),
    QuadR f dom cd ρ → AutoRuleG f dom cd ρ

end Collatz.Arctic.Gen
