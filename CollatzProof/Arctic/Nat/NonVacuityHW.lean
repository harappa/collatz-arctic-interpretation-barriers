/-
# Corollary 10.12 (the corner form of [HW06]): non-vacuity checks

The premises of the statements `HWBarrierST` and `HWBarrierSTrev` of `HWCorner.lean` can be satisfied, the conclusion is a claim about the corner entries only, and
the statements become false without the condition on the diagonal. Outside the closure of the main theorem. Computations by `decide +kernel` (no `native_decide`).

* §1 $\mathcal T$: the family `homFam IP3` (5 × 5) of homogeneous matrices of the monotone interpretation `IP3` of dimension 4 of Proposition 9.5 of the paper (`NonVacuity.lean`)
  and `J = {0, d}` (the index `some 0` and the homogeneous index `none`; the form `E_{\{1,d\}}` of HW06 with `d = 5`) satisfy the premises (`IP3_hw_premises`;
  the diagonal and the weak orientation by direct computation). As the conclusion says, the four corners are equal for all 11 rules (`IP3_hw_corners_eq`), but at an entry
  outside the corners some rule decreases strictly (`IP3_hw_offcorner`: the entry `(1, d)` of `f. → .`, `2 > 1`). The non-affine family `NRev` (`NonVacuityW1.lean`;
  no index is a sink) with `J = {1}` also satisfies the premises (`NRev_hw_premises`).
* §2 $\mathcal T^{\mathrm{rev}}$: the family of homogeneous matrices of `IP3rev` (`NonVacuityRev.lean`, a monotone interpretation of dimension 4 for $\mathcal T^{\mathrm{rev}}$) with `J = {0, d}`
  satisfies the premises (`IP3rev_hw_premises`), and the four corners are equal for all 11 rules (`IP3rev_hw_corners_eq`).
* §3 The condition on the diagonal cannot be dropped: the family of homogeneous matrices of `INoMono` (`NonVacuity2.lean`, the interpretation of dimension 1 in which only `/` is
  not monotone) with `J = {0, d}` weakly orients the 11 rules, the condition on the diagonal fails only at the index 0 of `/` (`INoMono_hw_diag`), and `f. → .` decreases
  strictly at the corner `(0, d)`. Hence the statement without the condition on the diagonal is false (`not_hw_noDiag`). The same holds for the reversed system with `INoMonoRev`
  (only `.` is not monotone) (`not_hw_noDiag_rev`).
-/
import CollatzProof.Arctic.Nat.HWCorner
import CollatzProof.Arctic.Nat.NonVacuityRev
import CollatzProof.Arctic.Nat.NonVacuityW1

namespace Collatz.Arctic.NatQ5.HW

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix Letter

/-- The pair of indices of `E_{\{1,d\}}` of HW06: the index `some 0` (the index 1 of the paper) and the homogeneous index `none` (the index `D + 1` of the paper). -/
abbrev Jcorner (d : ℕ) [NeZero d] : Finset (Option (Fin d)) := {some 0, none}

/-! ## §1 $\mathcal T$ -/

/-- The diagonal entries of `homFam IP3` at `J = {0, d}` are at least 1 (direct computation). -/
theorem IP3_hw_diag : ∀ s, ∀ i ∈ Jcorner 4, 1 ≤ homFam IP3 s i i := by
  intro s; cases s <;> decide +kernel

/-- `homFam IP3` weakly orients the 11 rules of $\mathcal T$ entrywise (direct computation). -/
theorem IP3_hw_weak : ∀ ρ ∈ rulesST, GWeak (homFam IP3) ρ := by decide +kernel

/-- **The premises of `HWBarrierST` can be satisfied** (a 5 × 5 family of the form `E_{\{1,5\}}` of HW06). -/
theorem IP3_hw_premises : (∀ s, ∀ i ∈ Jcorner 4, 1 ≤ homFam IP3 s i i) ∧ ∀ ρ ∈ rulesST, GWeak (homFam IP3) ρ :=
  ⟨IP3_hw_diag, IP3_hw_weak⟩

/-- The four corner entries are equal (the double quantification over `J × J` does not get a `Decidable` instance by composition, so the four corners are listed). -/
def CornersEq {d : ℕ} (N : Letter → Matrix (Option (Fin d)) (Option (Fin d)) ℕ) [NeZero d] (ρ : Rule) : Prop :=
  NW N ρ.rhs (some 0) (some 0) = NW N ρ.lhs (some 0) (some 0) ∧ NW N ρ.rhs (some 0) none = NW N ρ.lhs (some 0) none ∧
    NW N ρ.rhs none (some 0) = NW N ρ.lhs none (some 0) ∧ NW N ρ.rhs none none = NW N ρ.lhs none none

instance {d : ℕ} (N : Letter → Matrix (Option (Fin d)) (Option (Fin d)) ℕ) [NeZero d] (ρ : Rule) :
    Decidable (CornersEq N ρ) := by
  unfold CornersEq; infer_instance

theorem cornersEq_iff {d : ℕ} (N : Letter → Matrix (Option (Fin d)) (Option (Fin d)) ℕ) [NeZero d] (ρ : Rule) :
    CornersEq N ρ ↔ ∀ i ∈ Jcorner d, ∀ j ∈ Jcorner d, NW N ρ.rhs i j = NW N ρ.lhs i j := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ i hi j hj
    simp only [Jcorner, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> assumption
  · intro h
    exact ⟨h _ (by simp) _ (by simp), h _ (by simp) _ (by simp), h _ (by simp) _ (by simp), h _ (by simp) _ (by simp)⟩

/-- As the conclusion says, the four corners are equal for all 11 rules (a direct computation that does not use the theorem). -/
theorem IP3_hw_corners_eq :
    ∀ ρ ∈ rulesST, ∀ i ∈ Jcorner 4, ∀ j ∈ Jcorner 4, NW (homFam IP3) ρ.rhs i j = NW (homFam IP3) ρ.lhs i j := by
  have h : ∀ ρ ∈ rulesST, CornersEq (homFam IP3) ρ := by decide +kernel
  exact fun ρ hρ => (cornersEq_iff _ ρ).1 (h ρ hρ)

/-- The conclusion is about the corners only: at the entry `(1, d)` outside the corners, `f. → .` decreases strictly (`1 < 2`). -/
theorem IP3_hw_offcorner :
    NW (homFam IP3) rFdot.rhs (some 1) none = 1 ∧ NW (homFam IP3) rFdot.lhs (some 1) none = 2 := by
  decide +kernel

/-- The main theorem applied (the conclusion at the corners from the premises alone). -/
theorem IP3_hw_apply :
    ∀ ρ ∈ rulesST, ∀ i ∈ Jcorner 4, ∀ j ∈ Jcorner 4, ¬ NW (homFam IP3) ρ.rhs i j < NW (homFam IP3) ρ.lhs i j :=
  hwBarrierST (Option (Fin 4)) (homFam IP3) (Jcorner 4) IP3_hw_premises.1 IP3_hw_premises.2

/-- The non-affine family `NRev` (no index is a sink, `NRev_no_sink`) with `J = {1}` also satisfies the premises. -/
theorem NRev_hw_premises : (∀ s, ∀ i ∈ ({1} : Finset (Fin 2)), 1 ≤ NRev s i i) ∧ ∀ ρ ∈ rulesST, GWeak NRev ρ := by
  refine ⟨fun s => ?_, NRev_weak⟩
  cases s <;> decide +kernel

/-! ## §2 $\mathcal T^{\mathrm{rev}}$ -/

theorem IP3rev_hw_diag : ∀ s, ∀ i ∈ Jcorner 4, 1 ≤ homFam W5.IP3rev s i i := by
  intro s; cases s <;> decide +kernel

theorem IP3rev_hw_weak : ∀ ρ ∈ rulesSTrev, GWeak (homFam W5.IP3rev) ρ := by decide +kernel

/-- **The premises of `HWBarrierSTrev` can be satisfied**. -/
theorem IP3rev_hw_premises :
    (∀ s, ∀ i ∈ Jcorner 4, 1 ≤ homFam W5.IP3rev s i i) ∧ ∀ ρ ∈ rulesSTrev, GWeak (homFam W5.IP3rev) ρ :=
  ⟨IP3rev_hw_diag, IP3rev_hw_weak⟩

/-- As the conclusion says, the four corners are equal for all 11 rules of $\mathcal T^{\mathrm{rev}}$ (direct computation). -/
theorem IP3rev_hw_corners_eq : ∀ ρ ∈ rulesSTrev, ∀ i ∈ Jcorner 4, ∀ j ∈ Jcorner 4,
    NW (homFam W5.IP3rev) ρ.rhs i j = NW (homFam W5.IP3rev) ρ.lhs i j := by
  have h : ∀ ρ ∈ rulesSTrev, CornersEq (homFam W5.IP3rev) ρ := by decide +kernel
  exact fun ρ hρ => (cornersEq_iff _ ρ).1 (h ρ hρ)

/-! ## §3 The condition on the diagonal cannot be dropped -/

/-- The condition on the diagonal of `homFam INoMono` at `J = {0, d}` fails only at the index 0 of `/`. -/
theorem INoMono_hw_diag :
    homFam INoMono lft (some 0) (some 0) = 0 ∧ ∀ s, s ≠ lft → ∀ i ∈ Jcorner 1, 1 ≤ homFam INoMono s i i := by
  refine ⟨rfl, fun s hs => ?_⟩
  cases s <;> first | exact absurd rfl hs | decide +kernel

/-- **The statement without the condition on the diagonal is false**: `homFam INoMono` weakly orients the 11 rules and decreases `f. → .` strictly at the corner `(0, d)`. -/
theorem not_hw_noDiag : ¬ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (J : Finset ι),
    (∀ ρ ∈ rulesST, GWeak N ρ) → ∀ ρ ∈ rulesST, ∀ i ∈ J, ∀ j ∈ J, ¬ NW N ρ.rhs i j < NW N ρ.lhs i j := by
  intro h
  exact h (Option (Fin 1)) (homFam INoMono) (Jcorner 1) (fun ρ hρ => gweak_of_nweak (INoMono_weak ρ hρ)) rFdot
    (by decide) (some 0) (by decide) none (by decide) (by decide +kernel)

/-- Reversed system: the condition on the diagonal of `homFam INoMonoRev` fails only at the index 0 of `.`. -/
theorem INoMonoRev_hw_diag :
    homFam W5.INoMonoRev rgt (some 0) (some 0) = 0 ∧
      ∀ s, s ≠ rgt → ∀ i ∈ Jcorner 1, 1 ≤ homFam W5.INoMonoRev s i i := by
  refine ⟨rfl, fun s hs => ?_⟩
  cases s <;> first | exact absurd rfl hs | decide +kernel

/-- **The statement without the condition on the diagonal is false for the reversed system as well**: `homFam INoMonoRev` weakly orients the 11 rules of $\mathcal T^{\mathrm{rev}}$
and decreases `0f → f0` strictly at the corner `(0, d)`. -/
theorem not_hw_noDiag_rev : ¬ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (J : Finset ι),
    (∀ ρ ∈ rulesSTrev, GWeak N ρ) → ∀ ρ ∈ rulesSTrev, ∀ i ∈ J, ∀ j ∈ J, ¬ NW N ρ.rhs i j < NW N ρ.lhs i j := by
  intro h
  exact h (Option (Fin 1)) (homFam W5.INoMonoRev) (Jcorner 1)
    (fun ρ hρ => gweak_of_nweak (W5.INoMonoRev_weak ρ hρ)) ⟨[d0, f], [f, d0]⟩ (by decide) (some 0) (by decide) none
    (by decide) (by decide +kernel)

end Collatz.Arctic.NatQ5.HW
