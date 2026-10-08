/-
Statements of the outputs of the units for $R_H$, and their assembly (Section 7). **These statements are frozen** (after an internal independent review).

The barrier for $R_H$ uses the theorems proved for $\mathcal H$ (block model, swap argument, window frequencies, uses of the left-end, dynamic and carry
rules) **unchanged**; only the following three units are new (proved in `RH/Canon`, `Bridge`, `Count`).
* `SpecCanonRH` (`RH/Canon`): correctness of the canonical derivations `canRH n →* canRH (Hmap n)` (`HDom n`), and that their rules lie in `usedRH`.
  Adapted from `HTPDB/Canon.lean` (the $R_H$ version of the sweep `sweep_chain`: the base case takes the two steps `aRule 1 d` and `leftRuleRH`).
* `SpecBridgeRH` (`RH/Bridge`): for the canonical strings `canRH`, which read the leading one as the symbol `t`, the form of `Gen.barrier_of_autoCoreG`
  (the general form with the map, domain, rules and canonical derivations as parameters). The value bridge is
  `Φ(canRH n) = autoVal (row 0 of I L ⊗ I t) I (column 0 of I .) n`. Adapted from `Gen/SysBridge.lean`.
* `SpecCountRH` (`RH/Count`): the numbers of uses in the canonical derivations of $R_H$ are at least those of the corresponding rules of $\mathcal H$
  (`canDerivRH n = (canDerivH n).flatMap liftRH`, `liftRH (/d) = [aRule 1 d, L((3 + d)/2)]`; Lemma 7.4).
  Correspondence: `ff.`, `ttt.`, `aRule b d` to the same rules, `L1 → Lt` to `/0 → /t`, `L2 → Ltf` to `/1 → /ff`.

Assembly: the intermediate statement `AutoCoreRH` of $R_H$ follows from the intermediate statement `HTPDB.AutoCoreH` of $\mathcal H$ by the comparison
of numbers of uses alone (`autoRuleG_of_count`, `autoCoreRH_of_autoCoreH`, logic only; the conclusion of `AutoCoreG` is monotone in the numbers of uses).
`AutoCoreH` is obtained by applying the frozen assembly `HTPDB.autoCoreH_of_specs` for $\mathcal H$ to existing theorems (`hsp_holds`, `HModel.specH*`,
`Gen.spec*`, `HTPDB.spec*`, all unconditional) (`autoCoreH_holds`). The only hypotheses left in `rh_of_specs` are the three above.
-/
import CollatzProof.Arctic.HTPDB.LeftUseMain
import CollatzProof.Arctic.HTPDB.Uses
import CollatzProof.Arctic.HTPDB.ARuleFive
import CollatzProof.Arctic.HModel.Swap
import CollatzProof.Arctic.Gen.Final
import CollatzProof.Arctic.Gen.KeyMain4
import CollatzProof.Arctic.Gen.HTWFromKey
import CollatzProof.Arctic.Gen.Quad
import CollatzProof.Arctic.HSPMain
import CollatzProof.Arctic.RH.Statement

namespace Collatz.Arctic.RH

open Collatz.Arctic HModel HTPDB

/-! ## Statements of the outputs of the units -/

/-- Output of `RH/Canon`: correctness of the canonical derivations (when `HDom n`), and every rule they use is a used rule (for all `n`). -/
structure SpecCanonRH : Prop where
  chain : ∀ n, HDom n → Chain (canDerivRH n) (canRH n) (canRH (Hmap n))
  sub : ∀ n, ∀ σ ∈ canDerivRH n, σ ∈ usedRH

/-- Output of `RH/Bridge`: the general form of rule removal for the canonical strings `canRH` (`Gen.barrier_of_autoCoreG` with `can`
replaced by `canRH`). -/
def SpecBridgeRH : Prop :=
  ∀ (f : ℕ → ℕ) (dom : ℕ → Prop) (rules : List Rule) (cd : ℕ → List Rule),
    Gen.AutoCoreG f dom rules cd →
    (∀ n, dom n → Chain (cd n) (canRH n) (canRH (f n))) →
    (∀ n, dom n → ∀ σ ∈ cd n, σ ∈ rules) →
    ∀ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I → (∀ ρ ∈ rules, Weak I ρ) →
      ∀ ρ ∈ rules, ¬ Strict I ρ

/-- Output of `RH/Count`: comparison of numbers of uses (in the canonical derivation of each point, the number for the rule of $\mathcal H$ ≤ the number for the rule of $R_H$). -/
structure SpecCountRH : Prop where
  ff_le : ∀ n, (canDerivH n).count ffRule ≤ (canDerivRH n).count ffRule
  ttt_le : ∀ n, (canDerivH n).count tttRule ≤ (canDerivRH n).count tttRule
  aRule_le : ∀ n b d, b < 2 → d ≤ 2 →
    (canDerivH n).count (aRule b d) ≤ (canDerivRH n).count (aRule b d)
  left1_le : ∀ n, (canDerivH n).count (leftRule 0) ≤ (canDerivRH n).count (leftRuleRH 1)
  left2_le : ∀ n, (canDerivH n).count (leftRule 1) ≤ (canDerivRH n).count (leftRuleRH 2)

/-! ## The intermediate statement transfers by the comparison of numbers of uses (logic only) -/

/-- From the comparison of numbers of uses at each point, the comparison along orbit segments. -/
theorem usesOrbitG_le_of_count {f : ℕ → ℕ} {cd cd' : ℕ → List Rule} {ρ ρ' : Rule}
    (h : ∀ n, (cd n).count ρ ≤ (cd' n).count ρ') (n m : ℕ) :
    Gen.usesOrbitG f cd ρ n m ≤ Gen.usesOrbitG f cd' ρ' n m := by
  unfold Gen.usesOrbitG
  exact List.sum_le_sum (fun i _ => h _)

/-- The conclusion of `AutoCoreG` for one rule transfers by the comparison of numbers of uses (its right-hand side is monotone in the numbers of uses). -/
theorem autoRuleG_of_count {f : ℕ → ℕ} {dom : ℕ → Prop} {cd cd' : ℕ → List Rule} {ρ ρ' : Rule}
    (h : ∀ n, (cd n).count ρ ≤ (cd' n).count ρ') (hρ : Gen.AutoRuleG f dom cd ρ) :
    Gen.AutoRuleG f dom cd' ρ' := by
  intro D u A c κ hfin hsl N
  obtain ⟨n, hn, m, hm, hlt⟩ := hρ D u A c κ hfin hsl N
  refine ⟨n, hn, m, hm, hlt.trans_le ?_⟩
  rw [Arc.fin_le_fin]
  exact Nat.add_le_add_left (usesOrbitG_le_of_count h n m) _

/-- **The intermediate statement of $R_H$ from that of $\mathcal H$** (logic only; Proposition 7.5): the map, domain and automata are the same, and
the numbers of uses of the used rules are at least those of the corresponding rules of $\mathcal H$ (`SpecCountRH`). The carry rules, `ff.` and `ttt.` transfer
from the same rules, `L1 → Lt` from `/0 → /t`, and `L2 → Ltf` from `/1 → /ff`. -/
theorem autoCoreRH_of_autoCoreH (c3 : SpecCountRH) (h : AutoCoreH) : AutoCoreRH := by
  have hH : ∀ ρ ∈ rulesHT, Gen.AutoRuleG Hmap HDom canDerivH ρ :=
    fun ρ hρ D u A c κ hfin hsl N => h D u A c κ hfin hsl ρ hρ N
  refine Gen.autoCoreG_of_rules (fun ρ hρ => ?_)
  rcases usedRH_cases ρ hρ with ⟨b, d, hb, hd, rfl⟩ | rfl | rfl | rfl | rfl
  · refine autoRuleG_of_count (fun n => c3.aRule_le n b d hb hd) (hH _ ?_)
    interval_cases b <;> interval_cases d <;> decide
  · exact autoRuleG_of_count c3.ff_le (hH _ (by decide))
  · exact autoRuleG_of_count c3.ttt_le (hH _ (by decide))
  · exact autoRuleG_of_count c3.left1_le (hH _ (by decide))
  · exact autoRuleG_of_count c3.left2_le (hH _ (by decide))

/-! ## Assembly -/

/-- The intermediate statement of $\mathcal H$ (unconditional; Theorem 5.5): apply the frozen assembly `HTPDB.autoCoreH_of_specs` to the unit theorems for $\mathcal H$ and
`hsp_holds` (in the same way as `htpdbBarriers` in `HTPDB/Final.lean`). -/
theorem autoCoreH_holds : AutoCoreH :=
  autoCoreH_of_specs hsp_holds specHModel specHClass specHBoundary specHSwap Gen.specAutoRule
    Gen.specKeyOfSwap Gen.specWinOfKey Gen.specQuadRule specLeftUseH specDynUseH specQuadH

/-- **Assembly**: the main theorem (Theorem 3.1(ii), $R_H$) from the outputs of the three units for $R_H$. These three are the only hypotheses left. -/
theorem rh_of_specs (c1 : SpecCanonRH) (c2 : SpecBridgeRH) (c3 : SpecCountRH) : ArcticBarrierRH :=
  c2 Hmap HDom usedRH canDerivRH (autoCoreRH_of_autoCoreH c3 autoCoreH_holds) c1.chain
    (fun n _ => c1.sub n)

/-- The form of the last sentence of Theorem 3.1(ii), from the same hypotheses. -/
theorem rhSub_of_specs (c1 : SpecCanonRH) (c2 : SpecBridgeRH) (c3 : SpecCountRH) :
    ArcticBarrierRHSub :=
  arcticBarrierRHSub_of (rh_of_specs c1 c2 c3)

end Collatz.Arctic.RH
