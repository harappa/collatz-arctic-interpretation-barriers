/-
Statements of the main theorem on rule removal for $R_H$ (Theorem 3.1(ii)) and of the intermediate statement `AutoCoreRH` (Proposition 7.5).
**These statements are frozen** (after an internal independent review).

* `ArcticBarrierRH` (Theorem 3.1(ii), the case $R_H$): an arctic interpretation (of any dimension) that weakly orients all **ten used rules** (`usedRH`) and has
  all `(M_s)₀₀` finite strictly orients none of the used rules.
  It differs from `Statement.ArcticBarrierST` and `HTPDB.ArcticBarrierHT` only in the set of rules (it is definitionally equal to
  `NonVacuity.BarrierFor usedRH`; `RH/NonVacuity.lean`). The form with the premise on the used rules only is the strongest: an interpretation
  that weakly orients a larger subsystem of the 12 rules, which also contains `L0 → L` or `Lf → L`, in particular weakly orients `usedRH`.
* `ArcticBarrierRHSub` (the last sentence of Theorem 3.1(ii)): let `R'` be obtained from `R_H` by removing zero or more of `L0 → L`, `Lf → L`
  (`usedRH ⊆ R' ⊆ rulesRH`, removing none included; a stronger form without the hypothesis (CF) of Question 4.4). An interpretation that weakly orients all rules of `R'` can strictly orient only the remaining
  `L0 → L`, `Lf → L`. It follows from `ArcticBarrierRH` by `arcticBarrierRHSub_of` (logic only).
  For all 12 rules, `L0 → L` and `Lf → L` can actually be strictly oriented (the 2-dimensional example in `RH/NonVacuity.lean`), so
  the restriction to `usedRH` cannot be dropped.
* `AutoCoreRH`: the intermediate statement between the value level and the numbers of uses: `Gen.AutoCoreG` applied to the map $H$, its domain (the same as for $\mathcal H$:
  `HModel.Hmap`, `HModel.HDom`), the used rules and the canonical derivations `canDerivRH`. The automaton value `autoVal`
  still reads `binTail n` (without the leading one); the leading `t` of the canonical string of $R_H$ is absorbed into the start vector
  (the bridge `SpecBridgeRH` in `RH/Spec.lean`: `u` = row 0 of `(I L ⊗ I t)`).
  - The values of `Hmap` outside the domain `HDom` (the identity) play no role: the slope hypothesis concerns only points of `HDom`, and all orbit points in the conclusion lie in `HDom`.
-/
import CollatzProof.Arctic.Gen.Model
import CollatzProof.Arctic.HModel.Defs
import CollatzProof.Arctic.RH.Defs

namespace Collatz.Arctic.RH

open Collatz.Arctic

/-- **Statement of the main theorem** (Theorem 3.1(ii), $R_H$, rule removal): an arctic interpretation (of any dimension) with all
`(M_s)₀₀` finite that weakly orients all ten used rules strictly orients none of the used rules. -/
def ArcticBarrierRH : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I → (∀ ρ ∈ usedRH, Weak I ρ) →
    ∀ ρ ∈ usedRH, ¬ Strict I ρ

/-- **The form of the last sentence of Theorem 3.1(ii)**: for an arctic interpretation with all `(M_s)₀₀` finite that weakly orients all rules of `R'`,
where `usedRH ⊆ R' ⊆ rulesRH`, the only rules of `R'` it strictly orients are `L0 → L` and `Lf → L`. -/
def ArcticBarrierRHSub : Prop :=
  ∀ R' : List Rule, (∀ ρ ∈ usedRH, ρ ∈ R') → (∀ ρ ∈ R', ρ ∈ rulesRH) →
    ∀ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I → (∀ ρ ∈ R', Weak I ρ) →
      ∀ ρ ∈ R', Strict I ρ → ρ = l0Rule ∨ ρ = lfRule

/-- The form of the last sentence of Theorem 3.1(ii) from `ArcticBarrierRH` (logic only). -/
theorem arcticBarrierRHSub_of (h : ArcticBarrierRH) : ArcticBarrierRHSub := by
  intro R' hused hsub d hd I hfin hweak ρ hρ hs
  rcases rulesRH_cases' ρ (hsub ρ hρ) with hu | h0 | hf
  · exact absurd hs (h d hd I hfin (fun σ hσ => hweak σ (hused σ hσ)) ρ hu)
  · exact Or.inl h0
  · exact Or.inr hf

/-- **The intermediate statement** (value level and numbers of uses; the map $H$ and its domain, the used rules, the canonical derivations of $R_H$). -/
def AutoCoreRH : Prop := Gen.AutoCoreG HModel.Hmap HModel.HDom usedRH canDerivRH

end Collatz.Arctic.RH
