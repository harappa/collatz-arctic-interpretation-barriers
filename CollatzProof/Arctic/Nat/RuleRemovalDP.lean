/-
# The rule removal processor ([GTS05, Theorem 30]) on essential problems (Corollary 9.3 (iii), Proposition 9.4 (iv), r4)

An external review of revision r3 (2.1): Corollary 9.3 (iii) of r3 covered the rule removal processor only on essential
problems that contain all rules of the system, while Section 8.3 used it for the step "Take the monotone reduction pair"
of Mint, on problems from which rules that are not usable have been deleted (only `U ⊆ R'`). Here: if the marked symbol
`h#` is also monotone (`(M)₀₀ ≥ 1`), no usable rule and no pair of the essential SCC is removed on any essential problem.

* Statements `MRRBarrierDP`, `MRRBarrierDPrev`: the unmarked letters other than `h` and `h#` are monotone; `U` is weakly
  oriented entrywise and the pairs weakly in the first row (implied by entrywise). Then no rule of `U` (interpretation of
  the unmarked letters) and no pair (first row) is strictly oriented. Rules outside `U` (they contain `h`) enter neither
  the hypotheses nor the conclusion; removing them keeps the problem essential.
* Proof: interpret `h` by `J (h#)` (`ofDP`) and truncate it to row 0 (`truncAt`, `BridgeDP.lean`). This keeps `(M)₀₀`, so
  the result is monotone and weakly orients `U` and the top rules (the pairs with the mark removed) entrywise, that is,
  all 11 rules; `NatBarrierST` (`NatBarrierSTrev`) applies. The rules of `U` do not contain `h`, so their maps are
  unchanged. The pairs: `NatBarrierDP` (`NatBarrierDPrev`).
* `h#` must be monotone (Proposition 9.4 (iv)): the unmarked letters as in Proposition 9.4 (ii) (`INoMono`, `INoMonoRev`)
  and `h#` the constant 0 weakly orient the pairs (both sides are 0) and strictly orient all rules of `U`
  (`JMarkConst_facts`, `JMarkConstRev_facts`, the reviewer's witness).
-/
import CollatzProof.Arctic.Nat.Final
import CollatzProof.Arctic.Nat.BridgeDP
import CollatzProof.Arctic.Nat.NonVacuity2
import CollatzProof.Arctic.Nat.NonVacuityRev

namespace Collatz.Arctic.NatQ5.MRR

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W5 Matrix Letter DLetter

/-! ## §1 Statements -/

/-- **Forward**: `h = /`. A natural-number affine interpretation in which the unmarked letters other than `/` and `/#`
are monotone, and which weakly orients `U = D_T ∪ A` entrywise and the pairs of `P_B` in the first row, strictly orients no rule of `U` and no pair of `P_B`. -/
def MRRBarrierDP : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : DLetter → NAff d),
    (∀ s, s ≠ lft → 1 ≤ (J (plain s)).M 0 0) → 1 ≤ (J (mark lft)).M 0 0 →
    (∀ ρ ∈ usableST, NWeakD J ρ.plain) → (∀ π ∈ pairsPB, NWeakTopD J π) →
    (∀ ρ ∈ usableST, ¬ NStrict (fun s => J (plain s)) ρ) ∧ ∀ π ∈ pairsPB, ¬ NStrictTopD J π

/-- **Reversed**: `h = .`. `U = A^rev ∪ B^rev`, the pairs `P_D^rev`. -/
def MRRBarrierDPrev : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : DLetter → NAff d),
    (∀ s, s ≠ rgt → 1 ≤ (J (plain s)).M 0 0) → 1 ≤ (J (mark rgt)).M 0 0 →
    (∀ ρ ∈ usableSTrev, NWeakD J ρ.plain) → (∀ π ∈ pairsPDrev, NWeakTopD J π) →
    (∀ ρ ∈ usableSTrev, ¬ NStrict (fun s => J (plain s)) ρ) ∧ ∀ π ∈ pairsPDrev, ¬ NStrictTopD J π

/-- The forward form without the monotonicity of `h#` (false by Proposition 9.4 (iv)). -/
def MRRBarrierDPNoMark : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : DLetter → NAff d),
    (∀ s, s ≠ lft → 1 ≤ (J (plain s)).M 0 0) →
    (∀ ρ ∈ usableST, NWeakD J ρ.plain) → (∀ π ∈ pairsPB, NWeakTopD J π) →
    ∀ ρ ∈ usableST, ¬ NStrict (fun s => J (plain s)) ρ

/-- The reversed form without the monotonicity of `h#` (false by Proposition 9.4 (iv)). -/
def MRRBarrierDPrevNoMark : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : DLetter → NAff d),
    (∀ s, s ≠ rgt → 1 ≤ (J (plain s)).M 0 0) →
    (∀ ρ ∈ usableSTrev, NWeakD J ρ.plain) → (∀ π ∈ pairsPDrev, NWeakTopD J π) →
    ∀ ρ ∈ usableSTrev, ¬ NStrict (fun s => J (plain s)) ρ

/-! ## §2 Proofs -/

/-- The truncated interpretation `truncAt h (ofDP h J)` agrees with the interpretation of the unmarked letters on strings that do not contain `h`. -/
theorem evN_flat_free {d : ℕ} [NeZero d] (h : Letter) (J : DLetter → NAff d) (w : Word) (hw : h ∉ w) :
    evN (truncAt h (ofDP h J)) w = evN (fun s => J (plain s)) w := by
  rw [evN_truncAt_of_not_mem h _ w hw, evN_ofDP_free h J w hw]

/-- Monotonicity of the truncated interpretation: monotone if the unmarked letters other than `h` and `h#` are. -/
theorem nmono_flat {d : ℕ} [NeZero d] (h : Letter) (J : DLetter → NAff d)
    (hmono : ∀ s, s ≠ h → 1 ≤ (J (plain s)).M 0 0) (hmark : 1 ≤ (J (mark h)).M 0 0) :
    NMono (truncAt h (ofDP h J)) := by
  intro s
  by_cases hs : s = h
  · subst hs
    simpa [truncAt, trunc0, ofDP] using hmark
  · simpa [truncAt, ofDP, hs] using hmono s hs

theorem mrrBarrierDP : MRRBarrierDP := by
  intro d _ J hmono hmark hU hP
  refine ⟨?_, natBarrierDP_final d J hU hP⟩
  have hW : ∀ σ ∈ rulesST, NWeak (truncAt lft (ofDP lft J)) σ := by
    intro σ hσ
    rcases W5.rulesST_split σ hσ with h1 | h2
    · exact (nweak_truncAt_head lft _ (W5.rulesSTB_head σ h1)).2
        ((nweakTopD_dp_iff lft J (W5.rulesSTB_head σ h1)).1 (hP _ (W5.pairsPB_eq ▸ List.mem_map_of_mem h1)))
    · exact (nweak_truncAt_free lft _ (W5.rulesST_take_free σ h2).1 (W5.rulesST_take_free σ h2).2).2
        ((nweakD_plain_iff_ofDP lft J (W5.rulesST_take_free σ h2).1 (W5.rulesST_take_free σ h2).2).1
          (hU σ (W5.usableST_eq ▸ h2)))
  intro ρ hρ hs
  rw [W5.usableST_eq] at hρ
  have hfree := W5.rulesST_take_free ρ hρ
  refine natBarrierST_final d _ (nmono_flat lft J hmono hmark) hW ρ (List.mem_of_mem_take hρ) ?_
  unfold NStrict NWeak at hs ⊢
  rw [evN_flat_free lft J _ hfree.1, evN_flat_free lft J _ hfree.2]
  exact hs

theorem mrrBarrierDPrev : MRRBarrierDPrev := by
  intro d _ J hmono hmark hU hP
  refine ⟨?_, natBarrierDPrev_final d J hU hP⟩
  have hW : ∀ σ ∈ rulesSTrev, NWeak (truncAt rgt (ofDP rgt J)) σ := by
    intro σ hσ
    rcases W5.rulesSTrev_split σ hσ with h1 | h2
    · exact (nweak_truncAt_head rgt _ (W5.rulesSTrevTop_head σ h1)).2
        ((nweakTopD_dp_iff rgt J (W5.rulesSTrevTop_head σ h1)).1 (hP _ (W5.pairsPDrev_eq ▸ List.mem_map_of_mem h1)))
    · exact (nweak_truncAt_free rgt _ (W5.rulesSTrev_drop_free σ h2).1 (W5.rulesSTrev_drop_free σ h2).2).2
        ((nweakD_plain_iff_ofDP rgt J (W5.rulesSTrev_drop_free σ h2).1 (W5.rulesSTrev_drop_free σ h2).2).1
          (hU σ (W5.usableSTrev_eq ▸ h2)))
  intro ρ hρ hs
  rw [W5.usableSTrev_eq] at hρ
  have hfree := W5.rulesSTrev_drop_free ρ hρ
  refine natBarrierSTrev_final d _ (nmono_flat rgt J hmono hmark) hW ρ (List.mem_of_mem_drop hρ) ?_
  unfold NStrict NWeak at hs ⊢
  rw [evN_flat_free rgt J _ hfree.1, evN_flat_free rgt J _ hfree.2]
  exact hs

/-! ## §3 The monotonicity of `h#` cannot be dropped (Proposition 9.4 (iv)) -/

/-- The unmarked letters as in `INoMono` (`[f](y) = [t](y) = 2y`, `[d](y) = y + 1`, `[/](y) = 0`, `[.](y) = y + 2`), the
marked letters by the constant 0. -/
def JMarkConst : DLetter → NAff 1
  | mark _ => ⟨0, 0⟩
  | plain s => INoMono s

/-- The unmarked letters as in `INoMonoRev` (`[f](y) = [t](y) = y + 1`, `[d](y) = 2y + 1`, `[/](y) = y + 2`,
`[.](y) = 0`), the marked letters by the constant 0. -/
def JMarkConstRev : DLetter → NAff 1
  | mark _ => ⟨0, 0⟩
  | plain s => INoMonoRev s

/-- `JMarkConst`: the unmarked letters other than `/` are monotone, `/#` is not. It weakly orients `U` and `P_B`
entrywise and strictly orients all 8 rules of `U`. -/
theorem JMarkConst_facts :
    (∀ s, s ≠ lft → 1 ≤ (JMarkConst (plain s)).M 0 0) ∧ (JMarkConst (mark lft)).M 0 0 = 0 ∧
    (∀ ρ ∈ usableST, NWeakD JMarkConst ρ.plain) ∧ (∀ π ∈ pairsPB, NWeakD JMarkConst π) ∧
    ∀ ρ ∈ usableST, NStrict (fun s => JMarkConst (plain s)) ρ :=
  ⟨INoMono_mono_except_lft.2, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `JMarkConstRev`: the unmarked letters other than `.` are monotone, `.#` is not. It weakly orients `A^rev ∪ B^rev`
and `P_D^rev` entrywise and strictly orients all 9 rules of `A^rev ∪ B^rev`. -/
theorem JMarkConstRev_facts :
    (∀ s, s ≠ rgt → 1 ≤ (JMarkConstRev (plain s)).M 0 0) ∧ (JMarkConstRev (mark rgt)).M 0 0 = 0 ∧
    (∀ ρ ∈ usableSTrev, NWeakD JMarkConstRev ρ.plain) ∧ (∀ π ∈ pairsPDrev, NWeakD JMarkConstRev π) ∧
    ∀ ρ ∈ usableSTrev, NStrict (fun s => JMarkConstRev (plain s)) ρ :=
  ⟨INoMonoRev_mono_except_rgt.2, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nweakTopD_of_nweakD {d : ℕ} [NeZero d] {J : DLetter → NAff d} {π : DRule} (h : NWeakD J π) :
    NWeakTopD J π :=
  ⟨fun j => h.1 0 j, h.2 0⟩

theorem not_mrrNoMark : ¬ MRRBarrierDPNoMark := fun h =>
  h 1 JMarkConst JMarkConst_facts.1 JMarkConst_facts.2.2.1
    (fun π hπ => nweakTopD_of_nweakD (JMarkConst_facts.2.2.2.1 π hπ)) rFdot (by decide)
    (JMarkConst_facts.2.2.2.2 rFdot (by decide))

theorem not_mrrNoMark_rev : ¬ MRRBarrierDPrevNoMark := fun h =>
  h 1 JMarkConstRev JMarkConstRev_facts.1 JMarkConstRev_facts.2.2.1
    (fun π hπ => nweakTopD_of_nweakD (JMarkConstRev_facts.2.2.2.1 π hπ)) _ (List.mem_cons_self ..)
    (JMarkConstRev_facts.2.2.2.2 _ (List.mem_cons_self ..))

end Collatz.Arctic.NatQ5.MRR
