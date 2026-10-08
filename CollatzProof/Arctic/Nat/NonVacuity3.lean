/-
# Checks of the statements for $\mathcal T$, part 3: the rule-by-rule form of (b), the statement for the left-end rules, negative controls

Incorporates the remarks of an internal review of the statements. A check file outside the closure of the main theorem (it may import
`NatExample.lean`). No `sorry`, `axiom` declaration or `native_decide` is used (computations by `decide +kernel`).

* §7 The rule-by-rule form of (b): for each rule `ρ` there are another rule `σ ≠ ρ` and a monotone interpretation of dimension 2 that weakly orients all rules except `σ` and strictly
  orients `ρ` (`strict_each_drop`). The removed rule `σ` is not even weakly oriented (consistent with the main theorem).
  For `ρ ≠ f1 → 0t` this is `IYAH` of Example 4.3 of Yolcu–Aaronson–Heule (`σ = f1 → 0t`); for `ρ = f1 → 0t` it is the witness `IF1` of dimension 2
  (`σ = t. → 2.`, found by a SAT search in an internal review). So for every rule the conclusion of the main theorem fails once the weak orientation of
  one of the 11 rules is dropped.
* §8 Checks of the statement `NatBarrierSTB` for the left-end rules: the premises can be satisfied by a non-monotone interpretation (`INoMono`); the rules of `B`
  can be strictly oriented in the system without one rule (`IYAH`, `IF1`); for the rules other than `B`, the statement without monotonicity is false (`INoMono` strictly orients all 8 rules
  other than `B`: `noMono_strict_nonB`). So the set of rules for which a barrier without monotonicity can hold is exactly `B`.
  The part of `NatBarrierST` on `B` follows from `NatBarrierSTB` (`natBarrierST_B_of_STB`).
* §9 Negative controls: claims that do not hold are decided false by `decide +kernel`; this is kept in the form of
  theorems stating the negations.
* §10 `IP3` agrees entrywise with `NatExample.IT` of Proposition 9.5 of the paper.
-/
import CollatzProof.Arctic.Nat.NonVacuity2
import CollatzProof.Arctic.Nat.BridgeTop
import CollatzProof.Arctic.NatExample

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter

/-! ## §7 The rule-by-rule form of (b) -/

/-- A monotone interpretation of dimension 2 that weakly orients $\mathcal T$ without `t. → 2.` and strictly orients `f1 → 0t` (found by a SAT search in an internal review:
`[f] = (I, (1,0))`, `[t] = ([[1,1],[0,1]], (2,0))`, `[0] = (diag(1,3), (0,3))`, `[1] = ([[1,1],[0,3]], (2,3))`,
`[2] = ([[1,3],[0,3]], (2,3))`, `[/] = ([[2,3],[0,0]], (3,3))`, `[.] = ([[2,2],[0,0]], (2,0))`). -/
def IF1 : Letter → NAff 2
  | .f => ⟨!![1, 0; 0, 1], ![1, 0]⟩
  | .t => ⟨!![1, 1; 0, 1], ![2, 0]⟩
  | .d0 => ⟨!![1, 0; 0, 3], ![0, 3]⟩
  | .d1 => ⟨!![1, 1; 0, 3], ![2, 3]⟩
  | .d2 => ⟨!![1, 3; 0, 3], ![2, 3]⟩
  | .lft => ⟨!![2, 3; 0, 0], ![3, 3]⟩
  | .rgt => ⟨!![2, 2; 0, 0], ![2, 0]⟩

theorem IF1_mono : NMono IF1 := fun s => by cases s <;> decide

theorem IF1_weak : ∀ ρ ∈ rulesST.erase rTdot, NWeak IF1 ρ := by decide +kernel

theorem IF1_strict_F1 : NStrict IF1 rF1 := by decide +kernel

theorem IF1_not_weak_Tdot : ¬ NWeak IF1 rTdot := by decide +kernel

/-- The rules strictly oriented by `IF1`: `f. → .`, `f1 → 0t`, `t0 → 1t`, `t1 → 2f`, `t2 → 2t` and the 3 left-end rules. -/
theorem IF1_strict_set : [rFdot, rF1, rT0, rT1, rT2, rL0, rL1, rL2].all (fun ρ => decide (NStrict IF1 ρ)) ∧
    [rF0, rF2].all (fun ρ => decide (¬ NStrict IF1 ρ)) := by decide +kernel

theorem not_barrier_drop_Tdot_F1 : ¬ NatBarrierFor (rulesST.erase rTdot) :=
  not_barrierFor IF1 IF1_mono IF1_weak rF1 (by decide) IF1_strict_F1

/-- **The rule-by-rule form of (b)**: for each rule `ρ` there are another rule `σ ≠ ρ` and a monotone interpretation of dimension 2 that weakly orients all of the remaining 10 rules
without `σ`, strictly orients `ρ`, and does not even weakly orient `σ`. -/
theorem strict_each_drop : ∀ ρ ∈ rulesST, ∃ σ ∈ rulesST, σ ≠ ρ ∧ ∃ I : Letter → NAff 2,
    NMono I ∧ (∀ τ ∈ rulesST.erase σ, NWeak I τ) ∧ ¬ NWeak I σ ∧ NStrict I ρ := by
  intro ρ hρ
  by_cases h : ρ = rF1
  · subst h
    exact ⟨rTdot, by decide, by decide, IF1, IF1_mono, IF1_weak, IF1_not_weak_Tdot, IF1_strict_F1⟩
  · exact ⟨rF1, by decide, fun e => h e.symm, IYAH, IYAH_mono, fun τ hτ => (IYAH_strict τ hτ).1,
      IYAH_not_weak_F1, IYAH_strict ρ ((List.mem_erase_of_ne h).2 hρ)⟩

/-- Corollary: for every rule `ρ`, the barrier fails at `ρ` for the system without some rule other than `ρ`. -/
theorem not_barrier_each : ∀ ρ ∈ rulesST, ∃ σ ∈ rulesST, σ ≠ ρ ∧ ρ ∈ rulesST.erase σ ∧
    ¬ NatBarrierFor (rulesST.erase σ) := by
  intro ρ hρ
  obtain ⟨σ, hσ, hne, I, hm, hw, -, hs⟩ := strict_each_drop ρ hρ
  have hmem : ρ ∈ rulesST.erase σ := (List.mem_erase_of_ne (Ne.symm hne)).2 hρ
  exact ⟨σ, hσ, hne, hmem, not_barrierFor I hm hw ρ hmem hs⟩

/-! ## §8 Checks of the statement `NatBarrierSTB` for the left-end rules -/

theorem rulesSTB_eq_leftST : rulesSTB = leftST := rfl

theorem rulesSTB_eq_leftRule : rulesSTB = [leftRule 0, leftRule 1, leftRule 2] := by decide

/-- The premises can be satisfied by a non-monotone interpretation: `INoMono` (only `[/]` is not monotone) weakly orients the 11 rules and, consistently with the conclusion,
strictly orients no rule of `B`. -/
theorem STB_premises_noMono : ¬ NMono INoMono ∧ (∀ ρ ∈ rulesST, NWeak INoMono ρ) ∧
    ∀ ρ ∈ rulesSTB, ¬ NStrict INoMono ρ :=
  ⟨INoMono_not_mono, INoMono_weak, INoMono_not_strict_left⟩

/-- **Sharpness**: each of the 8 rules other than `B` is strictly oriented by the non-monotone interpretation `INoMono`, which weakly orients the 11 rules. -/
theorem noMono_strict_nonB : ∀ ρ ∈ rulesST, ρ ∉ rulesSTB → NStrict INoMono ρ := by decide +kernel

/-- The rules of `B` can be strictly oriented in a system without one rule (even by a monotone interpretation): `IYAH` (without `f1 → 0t`) and
`IF1` (without `t. → 2.`). -/
theorem STB_drop_strict : (∀ ρ ∈ rulesSTB, NStrict IYAH ρ) ∧ (∀ ρ ∈ rulesSTB, NStrict IF1 ρ) := by
  decide +kernel

/-- The part of `NatBarrierST` on `B` (the monotone case) follows from `NatBarrierSTB`. -/
theorem natBarrierST_B_of_STB (h : NatBarrierSTB) :
    ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), NMono I → (∀ ρ ∈ rulesST, NWeak I ρ) →
      ∀ ρ ∈ rulesSTB, ¬ NStrict I ρ := by
  intro d _ I _ hw
  exact h d I hw

/-! ## §9 Negative controls (claims that do not hold are decided false by `decide +kernel`) -/

theorem ctrl_ILen_not_strict_Tdot : ¬ NStrict ILen rTdot := by decide +kernel

theorem ctrl_ILen_not_weak_all : ¬ ∀ ρ ∈ rulesST, NWeak ILen ρ := by decide +kernel

theorem ctrl_IYAH_not_weak_all : ¬ ∀ ρ ∈ rulesST, NWeak IYAH ρ := by decide +kernel

theorem ctrl_IF1_not_weak_all : ¬ ∀ ρ ∈ rulesST, NWeak IF1 ρ := by decide +kernel

theorem ctrl_IP3_not_strict_Fdot : ¬ NStrict IP3 rFdot := by decide +kernel

theorem ctrl_INoMono_not_mono : ¬ NMono INoMono := INoMono_not_mono

theorem ctrl_INoMono_not_strict_B : ¬ ∃ ρ ∈ rulesSTB, NStrict INoMono ρ := by decide +kernel

/-! ## §10 `IP3` and `NatExample.IT` of Proposition 9.5 of the paper -/

/-- `IP3` agrees entrywise with `NatExample.IT` (`interp 1 0`) (the `NAff` of `NatExample.lean` is a copy that differs only in the namespace). -/
theorem IP3_eq_IT : ∀ s, (IP3 s).M = (NatExample.IT s).M ∧ (IP3 s).v = (NatExample.IT s).v := by
  intro s
  cases s <;> decide +kernel

end Collatz.Arctic.NatQ5
