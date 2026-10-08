/-
# Checks of the statement `NatBarrierST` (Theorem 9.2 (i) of the paper, $\mathcal T$), part 2: possibility of strict orientation, subsystems, monotonicity

Continuation of `NonVacuity.lean`. No `sorry`, `axiom` declaration or `native_decide` is used (computations by `decide +kernel`).

* §4 (b) Strict orientation is possible by definition: for **each** of the 11 rules there is a monotone interpretation of dimension 1 that strictly orients it
  (the weak orientation of the other rules is not required), including the two commutation rules (`f0 → 0f`, `t2 → 2t`). In the arctic case the two
  commutation rules are strictly oriented by no interpretation (`not_strict_swap` in the arctic `NonVacuity3`; Proposition 4.5 of the paper), so
  this part of the natural-number statement is not trivial by definition (a difference from the arctic case).
* §5 (c) The barrier fails for subsystems: the general form `NatBarrierFor` with the set of rules as a parameter (`NatBarrierST` is a special case,
  `Iff.rfl`). For the following subsystems there is a monotone interpretation that weakly orients all remaining rules and strictly orients some rule:
  - $\mathcal T$ without `f1 → 0t`: the interpretation of dimension 2 of Example 4.3 of Yolcu–Aaronson–Heule (it strictly orients **all** of the remaining 10 rules; a proof in one step).
  - $\mathcal T$ without `t. → 2.`: the length interpretation (1 for binary digits, 2 for ternary digits, 0 for the ends; dimension 1). It strictly orients `f. → .` and `/0 → /t`.
  - $\mathcal T$ without `f2 → 1f`: dimension 1 (it strictly orients `t1 → 2f`, `/0 → /t`, `/1 → /ff`).
  - The systems without a group of rules (the dynamic rules, the carry rules `A`, the left-end rules): dimension 1.
  None of the examples weakly orients the removed rule (consistent with the main theorem). So the truth of the statement is not decided by the definitions alone; it depends on the combination
  of the 11 rules (the Collatz dynamics).
* §6 (d) Without monotonicity the statement is false: the form without monotonicity `NatBarrierForNoMono rulesST` does not hold. In an interpretation of dimension 1, only `/` is
  not monotone (`[/](y) = 0`), the other letters are monotone, all 11 rules are weakly oriented, and the 2 dynamic rules and the 6 carry rules `A` are strictly oriented.
  In this interpretation `Φ(can n) = 0` for all `n`, and the link from strict orientation to a decrease of `Φ` (Lemma 10.2 of the paper) is broken.
  This is the $\mathcal T$ version of the remark in Section 6 of Paper II (without monotonicity the dynamic rules of $R_H$ can be strictly oriented).
-/
import CollatzProof.Arctic.Nat.NonVacuity

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter

/-! ## §4 (b) Strict orientation is possible by definition -/

/-- The names of the 11 rules (in the order of `rulesST`, numbered 0 to 10). -/
def rFdot : Rule := ⟨[f, rgt], [rgt]⟩
def rTdot : Rule := ⟨[t, rgt], [d2, rgt]⟩
def rF0 : Rule := ⟨[f, d0], [d0, f]⟩
def rF1 : Rule := ⟨[f, d1], [d0, t]⟩
def rF2 : Rule := ⟨[f, d2], [d1, f]⟩
def rT0 : Rule := ⟨[t, d0], [d1, t]⟩
def rT1 : Rule := ⟨[t, d1], [d2, f]⟩
def rT2 : Rule := ⟨[t, d2], [d2, t]⟩
def rL0 : Rule := ⟨[lft, d0], [lft, t]⟩
def rL1 : Rule := ⟨[lft, d1], [lft, f, f]⟩
def rL2 : Rule := ⟨[lft, d2], [lft, f, t]⟩

theorem rulesST_eq : rulesST = [rFdot, rTdot, rF0, rF1, rF2, rT0, rT1, rT2, rL0, rL1, rL2] := rfl

/-- An interpretation of dimension 1: `y ↦ a_s y + c_s` for the letter `s`. -/
def wI1 (a c : Letter → ℕ) : Letter → NAff 1 := fun s => ⟨Matrix.of fun _ _ => a s, fun _ => c s⟩

theorem mono_wI1 {a c : Letter → ℕ} (h : ∀ s, 1 ≤ a s) : NMono (wI1 a c) := fun s => h s

/-- 1 for the letter `x` only. -/
def ind (x : Letter) : Letter → ℕ := fun s => if s = x then 1 else 0

/-- 2 for the letter `x`, 1 for the others (slopes). -/
def dbl (x : Letter) : Letter → ℕ := fun s => if s = x then 2 else 1

theorem mono_one : ∀ s : Letter, 1 ≤ (fun _ => 1 : Letter → ℕ) s := fun _ => le_rfl
theorem mono_dbl (x : Letter) : ∀ s, 1 ≤ dbl x s := fun s => by unfold dbl; split_ifs <;> omega

/-- **(b)**: for each of the 11 rules there is a monotone interpretation of dimension 1 that strictly orients it. The commutation rules `f0 → 0f`, `t2 → 2t` are handled
by a letter of slope 2 and a letter with constant term 1 (`[f0](y) = 2y + 2 > 2y + 1 = [0f](y)`), the others by the constant term 1 of a single letter. -/
theorem strict_each : ∀ ρ ∈ rulesST, ∃ I : Letter → NAff 1, NMono I ∧ NStrict I ρ := by
  intro ρ hρ
  simp only [rulesST, List.mem_cons, List.mem_nil_iff, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨wI1 (fun _ => 1) (ind f), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind t), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (dbl f) (ind d0), mono_wI1 (mono_dbl f), by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d1), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d2), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d0), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d1), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (dbl t) (ind d2), mono_wI1 (mono_dbl t), by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d0), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d1), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d2), mono_wI1 mono_one, by decide +kernel⟩

/-! ## §5 (c) The barrier fails for subsystems -/

/-- The general form with the set of rules as a parameter. -/
def NatBarrierFor (R : List Rule) : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), NMono I → (∀ ρ ∈ R, NWeak I ρ) → ∀ ρ ∈ R, ¬ NStrict I ρ

theorem natBarrierST_iff_for : NatBarrierST ↔ NatBarrierFor rulesST := Iff.rfl

/-- A counterexample refutes the general form. -/
theorem not_barrierFor {R : List Rule} {d : ℕ} [NeZero d] (I : Letter → NAff d) (hm : NMono I)
    (hw : ∀ ρ ∈ R, NWeak I ρ) (ρ : Rule) (hρ : ρ ∈ R) (hs : NStrict I ρ) : ¬ NatBarrierFor R :=
  fun h => h d I hm hw ρ hρ hs

theorem IYAH_mono : NMono IYAH := fun s => by cases s <;> decide

/-- Example 4.3 of Yolcu–Aaronson–Heule: all 10 rules of $\mathcal T$ without `f1 → 0t` are strictly oriented (a proof in one step). -/
theorem IYAH_strict : ∀ ρ ∈ rulesST.erase rF1, NStrict IYAH ρ := by decide +kernel

/-- The interpretation of Example 4.3 of Yolcu–Aaronson–Heule does not even weakly orient the removed rule `f1 → 0t` (consistent with the main theorem). -/
theorem IYAH_not_weak_F1 : ¬ NWeak IYAH rF1 := by decide +kernel

theorem not_barrier_drop_F1 : ¬ NatBarrierFor (rulesST.erase rF1) :=
  not_barrierFor IYAH IYAH_mono (fun ρ hρ => (IYAH_strict ρ hρ).1) rFdot (by decide)
    (IYAH_strict rFdot (by decide))

/-- The length interpretation: 1 for binary digits, 2 for ternary digits, 0 for the ends (all slopes 1). -/
def lenC : Letter → ℕ
  | .f => 1
  | .t => 1
  | .d0 => 2
  | .d1 => 2
  | .d2 => 2
  | .lft => 0
  | .rgt => 0

def ILen : Letter → NAff 1 := wI1 (fun _ => 1) lenC

theorem ILen_weak : ∀ ρ ∈ rulesST.erase rTdot, NWeak ILen ρ := by decide +kernel

theorem ILen_strict : NStrict ILen rFdot ∧ NStrict ILen rL0 := by decide +kernel

theorem ILen_not_weak_Tdot : ¬ NWeak ILen rTdot := by decide +kernel

theorem not_barrier_drop_Tdot : ¬ NatBarrierFor (rulesST.erase rTdot) :=
  not_barrierFor ILen (mono_wI1 mono_one) ILen_weak rFdot (by decide) ILen_strict.1

/-- $\mathcal T$ without `f2 → 1f`: constant term 1 for `d0` and `d1` (all slopes 1). -/
def IDropF2 : Letter → NAff 1 := wI1 (fun _ => 1) fun s => if s = d0 ∨ s = d1 then 1 else 0

theorem IDropF2_weak : ∀ ρ ∈ rulesST.erase rF2, NWeak IDropF2 ρ := by decide +kernel

theorem IDropF2_strict : NStrict IDropF2 rT1 ∧ NStrict IDropF2 rL0 ∧ NStrict IDropF2 rL1 := by
  decide +kernel

theorem IDropF2_not_weak_F2 : ¬ NWeak IDropF2 rF2 := by decide +kernel

theorem not_barrier_drop_F2 : ¬ NatBarrierFor (rulesST.erase rF2) :=
  not_barrierFor IDropF2 (mono_wI1 mono_one) IDropF2_weak rT1 (by decide) IDropF2_strict.1

/-- Groups of rules: the dynamic rules `D_T`, the carry rules `A`, the left-end rules `B` (the division of Yolcu–Aaronson–Heule, §3.2). -/
def dynST : List Rule := [rFdot, rTdot]
def aST : List Rule := [rF0, rF1, rF2, rT0, rT1, rT2]
def leftST : List Rule := [rL0, rL1, rL2]

theorem rulesST_split : rulesST = dynST ++ aST ++ leftST := rfl

/-- The system `A ∪ B` without the dynamic rules: constant term 1 for the ternary digits. The 3 left-end rules are strictly oriented. -/
theorem not_barrier_noDyn : ¬ NatBarrierFor (aST ++ leftST) :=
  not_barrierFor (wI1 (fun _ => 1) fun s => if s = d0 ∨ s = d1 ∨ s = d2 then 1 else 0)
    (mono_wI1 mono_one) (by decide +kernel) rL0 (by decide) (by decide +kernel)

/-- The system `D_T ∪ B` without the carry rules: constant term 1 for `d1`. `/1 → /ff` is strictly oriented. -/
theorem not_barrier_noA : ¬ NatBarrierFor (dynST ++ leftST) :=
  not_barrierFor (wI1 (fun _ => 1) (ind d1)) (mono_wI1 mono_one) (by decide +kernel) rL1 (by decide)
    (by decide +kernel)

/-- The system `D_T ∪ A` without the left-end rules: constant term 1 for the binary digits. The 2 dynamic rules are strictly oriented. -/
theorem not_barrier_noLeft : ¬ NatBarrierFor (dynST ++ aST) :=
  not_barrierFor (wI1 (fun _ => 1) fun s => if s = f ∨ s = t then 1 else 0)
    (mono_wI1 mono_one) (by decide +kernel) rFdot (by decide) (by decide +kernel)

/-! ## §6 (d) Without monotonicity the statement is false -/

/-- The form without monotonicity. -/
def NatBarrierForNoMono (R : List Rule) : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), (∀ ρ ∈ R, NWeak I ρ) → ∀ ρ ∈ R, ¬ NStrict I ρ

theorem barrierFor_of_noMono {R : List Rule} (h : NatBarrierForNoMono R) : NatBarrierFor R :=
  fun d _ I _ hw => h d I hw

/-- Slopes: 2 for `f` and `t`, 0 for `/`, 1 for the others. -/
def nmA : Letter → ℕ
  | .f => 2
  | .t => 2
  | .lft => 0
  | _ => 1

/-- Constant terms: 1 for the ternary digits, 2 for `.`, 0 for the others. -/
def nmC : Letter → ℕ
  | .d0 => 1
  | .d1 => 1
  | .d2 => 1
  | .rgt => 2
  | _ => 0

/-- `[f](y) = [t](y) = 2y`, `[d](y) = y + 1`, `[/](y) = 0`, `[.](y) = y + 2`. -/
def INoMono : Letter → NAff 1 := wI1 nmA nmC

/-- Only `/` is not monotone. -/
theorem INoMono_mono_except_lft : (INoMono lft).M 0 0 = 0 ∧ ∀ s, s ≠ lft → 1 ≤ (INoMono s).M 0 0 := by
  refine ⟨rfl, fun s hs => ?_⟩
  cases s <;> first | exact absurd rfl hs | decide

theorem INoMono_not_mono : ¬ NMono INoMono := fun h => by
  have := h lft
  revert this
  decide

theorem INoMono_weak : ∀ ρ ∈ rulesST, NWeak INoMono ρ := by decide +kernel

/-- The 2 dynamic rules and the 6 carry rules `A` are strictly oriented (both sides of the 3 left-end rules are 0, so they are only weakly oriented). -/
theorem INoMono_strict : ∀ ρ ∈ dynST ++ aST, NStrict INoMono ρ := by decide +kernel

theorem INoMono_not_strict_left : ∀ ρ ∈ leftST, ¬ NStrict INoMono ρ := by decide +kernel

/-- **(d)**: without monotonicity the statement for $\mathcal T$ is false. -/
theorem not_barrier_noMono : ¬ NatBarrierForNoMono rulesST := fun h =>
  h 1 INoMono INoMono_weak rFdot (by decide) (INoMono_strict rFdot (by decide))

/-- In this interpretation `Φ(can n) = 0` (`[/]` is the constant 0). Strict orientation does not give a decrease of `Φ(can ·)`. -/
theorem INoMono_phi_can (n : ℕ) : PhiN INoMono (can n) = 0 := by
  rw [phiN_eq]
  show ((INoMono lft).comp (evN INoMono (binTail n ++ [rgt]))).v 0 = 0
  simp [NAff.comp, INoMono, wI1, nmA, nmC, mulVec, dotProduct]

end Collatz.Arctic.NatQ5
