/-
Checks that the statements of the main theorems for the system $\mathcal H$ are not vacuous (see Proposition 4.5 and Section 14).
It uses the tools of `NonVacuity*.lean` for the system $\mathcal T$; the existing files are not changed. The proofs are only `decide` and citations of lemmas for $\mathcal T$.
This file is for checking and is not in the closure of the main theorems (it imports `Summary` of $\mathcal T$).

* §1 Instances of the general form: the five statements are instances of `NonVacuity.BarrierFor`, `BarrierDPFor`, `BarrierBZFor` (`Iff.rfl`).
  The agreement with the definitions of Koprowski–Waldmann 2009 (§1 of `NonVacuity`, checked for $\mathcal T$) can be cited as it is.
* §2 The hypotheses can be satisfied (weight interpretations of dimension 1).
* §3 Whether strict orientation is possible by definition: the 9 rules other than the two commutation rules (`f d0 → d0 f`, `t d2 → d2 t`), and each pair of `P_B` and
  `P_D^rev`, are strictly oriented by some interpretation. The two commutation rules are strictly oriented by no interpretation
  (`not_strict_swap` for $\mathcal T$).
* §4 Counterexamples for subsystems: the system without the dynamic rules (`A ∪ B`, shared with $\mathcal T$), the system without the left-end rules (`D_H ∪ A`),
  and the dependency pair problems with the dynamic rules (for the reversed problem, the left-end rules) removed from `U` admit interpretations orienting everything weakly and some rule strictly.
  Hence the truth of the statements depends on the Collatz dynamics (the combination of the dynamic rules and the left-end rules).
* §5 Recomputation of the dependency pairs and the usable rules (dependency pairs for string rewriting as in Zantema 2005, the closure of Definition 10 of Giesl–Thiemann–Schneider-Kamp–Falke 2006; `decide`).
* §6 Rule removal for the reversed system (the mirror used by the tools) follows from `ArcticBarrierHT` by transposition (in implication form; Theorem 3.1 for the reversed system is obtained by applying it to `arcticBarrierHT`).
* §7 Small checks on the domain of `AutoCoreH`.
-/
import CollatzProof.Arctic.NonVacuity4
import CollatzProof.Arctic.HTPDB.Statement
import CollatzProof.Arctic.HTPDB.DPStatement

namespace Collatz.Arctic.HTPDB

namespace NonVacuityH

open Collatz.Arctic Collatz.Arctic.NonVacuity Letter DLetter

/-! ## §1 Instances of the general form -/

theorem HT_iff : ArcticBarrierHT ↔ BarrierFor rulesHT := Iff.rfl
theorem HDP_iff : ArcticBarrierHDP ↔ BarrierDPFor lettersPB usableHT pairsPB := Iff.rfl
theorem HDPrev_iff : ArcticBarrierHDPrev ↔ BarrierDPFor lettersPDrev usableHTrev pairsPDrevH := Iff.rfl
theorem HBZ_iff : ArcticBarrierHBZ ↔ BarrierBZFor lettersPB usableHT pairsPB := Iff.rfl
theorem HBZrev_iff : ArcticBarrierHBZrev ↔ BarrierBZFor lettersPDrev usableHTrev pairsPDrevH := Iff.rfl

/-! ## §2 The hypotheses can be satisfied -/

theorem usableHT_ne : ∀ ρ ∈ usableHT, ρ.plain.lhs ≠ [] ∧ ρ.plain.rhs ≠ [] := by decide
theorem usableHTrev_ne : ∀ ρ ∈ usableHTrev, ρ.plain.lhs ≠ [] ∧ ρ.plain.rhs ≠ [] := by decide
theorem pairsPDrevH_ne : ∀ π ∈ pairsPDrevH, π.lhs ≠ [] ∧ π.rhs ≠ [] := by decide

/-- All hypotheses of `ArcticBarrierHT` can be satisfied (weights 3 for `/`, 5 for `.`, 0 for the other letters). -/
theorem hyp_HT_sat : ∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧ ∀ ρ ∈ rulesHT, Weak I ρ :=
  ⟨1, Nat.one_pos, wI wLR, fin00_wI _, fun ρ hρ => (weak_wI _ ρ).2 (by revert ρ; decide)⟩

theorem hyp_HDP_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SomewhereFinite hd J lettersPB ∧
    (∀ ρ ∈ usableHT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :=
  ⟨1, Nat.one_pos, wJ wLRD, sf_wJ _ _,
    fun ρ hρ => (weakA_wJ _ _ _).2 (by revert ρ; decide),
    fun π hπ => (weakTop_wJ _ _ _).2 (by revert π; decide)⟩

theorem hyp_HDPrev_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SomewhereFinite hd J lettersPDrev ∧
    (∀ ρ ∈ usableHTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :=
  ⟨1, Nat.one_pos, wJ wLRD, sf_wJ _ _,
    fun ρ hρ => (weakA_wJ _ _ _).2 (by revert ρ; decide),
    fun π hπ => (weakTop_wJ _ _ _).2 (by revert π; decide)⟩

theorem hyp_HBZ_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    AbsPositive hd J lettersPB ∧
    (∀ ρ ∈ usableHT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :=
  ⟨1, Nat.one_pos, wJZ wLRD, ap_wJZ _ _,
    fun ρ hρ => (weakA_wJZ _ (usableHT_ne ρ hρ).1 (usableHT_ne ρ hρ).2).2 (by revert ρ; decide),
    fun π hπ => (weakTop_wJZ _ (pairsPB_ne π hπ).1 (pairsPB_ne π hπ).2).2 (by revert π; decide)⟩

theorem hyp_HBZrev_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    AbsPositive hd J lettersPDrev ∧
    (∀ ρ ∈ usableHTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :=
  ⟨1, Nat.one_pos, wJZ wLRD, ap_wJZ _ _,
    fun ρ hρ => (weakA_wJZ _ (usableHTrev_ne ρ hρ).1 (usableHTrev_ne ρ hρ).2).2
      (by revert ρ; decide),
    fun π hπ => (weakTop_wJZ _ (pairsPDrevH_ne π hπ).1 (pairsPDrevH_ne π hπ).2).2
      (by revert π; decide)⟩

/-! ## §3 Whether strict orientation is possible by definition -/

/-- The 9 rules other than the two commutation rules strictly decrease the number of some letter (the 2 dynamic rules: the number of `f`, resp. `t`). -/
theorem strict_HT_ind : ∀ ρ ∈ rulesHT, ρ ≠ ⟨[f, d0], [d0, f]⟩ → ρ ≠ ⟨[t, d2], [d2, t]⟩ →
    ∃ x ∈ [f, t, d0, d1, d2, lft, rgt], (ρ.rhs.map (ind x)).sum < (ρ.lhs.map (ind x)).sum := by
  decide

/-- Complete classification of the strict orientability of the rules of $\mathcal H$: exactly the 9 rules other than the two commutation
rules are strictly oriented by some interpretation (for the two commutation rules the conclusion of the main theorem is trivial). -/
theorem strict_possible_iff_HT : ∀ ρ ∈ rulesHT,
    (∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧ Strict I ρ) ↔
      (ρ ≠ ⟨[f, d0], [d0, f]⟩ ∧ ρ ≠ ⟨[t, d2], [d2, t]⟩) := by
  intro ρ hρ
  constructor
  · rintro ⟨d, hd, I, hfin, hs⟩
    refine ⟨?_, ?_⟩
    · rintro rfl; exact not_strict_swap hd I hfin f d0 hs
    · rintro rfl; exact not_strict_swap hd I hfin t d2 hs
  · rintro ⟨h1, h2⟩
    obtain ⟨x, -, hx⟩ := strict_HT_ind ρ hρ h1 h2
    exact ⟨1, Nat.one_pos, wI (ind x), fin00_wI _, (strict_wI _ _).2 hx⟩

/-- `P_B` is the same as for $\mathcal T$: every pair is strictly oriented in the first row by some interpretation (`𝔸_ℕ`). -/
theorem strict_possible_HDP : ∀ π ∈ pairsPB, ∃ J : DLetter → AffFun Arc 1,
    SomewhereFinite Nat.one_pos J lettersPB ∧ StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) :=
  strict_possible_DP

/-- `P_B` (below zero). -/
theorem strict_possible_HBZ : ∀ π ∈ pairsPB, ∃ J : DLetter → AffFun ArcZ 1,
    AbsPositive Nat.one_pos J lettersPB ∧ StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) :=
  strict_possible_BZ

theorem strict_PDrevH_ind : ∀ π ∈ pairsPDrevH, ∃ x ∈ dletters,
    (π.rhs.map (indD x)).sum < (π.lhs.map (indD x)).sum := by decide

/-- Every pair of `P_D^rev` is strictly oriented in the first row by some interpretation (`𝔸_ℕ`). -/
theorem strict_possible_HDPrev : ∀ π ∈ pairsPDrevH, ∃ J : DLetter → AffFun Arc 1,
    SomewhereFinite Nat.one_pos J lettersPDrev ∧
      StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ
  obtain ⟨x, -, hx⟩ := strict_PDrevH_ind π hπ
  exact ⟨wJ (indD x), sf_wJ _ _, (strictTop_wJ _ _ _).2 hx⟩

/-- `P_D^rev` (below zero). -/
theorem strict_possible_HBZrev : ∀ π ∈ pairsPDrevH, ∃ J : DLetter → AffFun ArcZ 1,
    AbsPositive Nat.one_pos J lettersPDrev ∧
      StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ
  obtain ⟨x, -, hx⟩ := strict_PDrevH_ind π hπ
  exact ⟨wJZ (indD x), ap_wJZ _ _,
    (strictTop_wJZ _ (pairsPDrevH_ne π hπ).1 (pairsPDrevH_ne π hπ).2).2 hx⟩

/-! ## §4 Counterexamples for subsystems (all rules weakly, some rule strictly) -/

/-- The system without the dynamic rules is `A ∪ B`, shared with $\mathcal T$ (`NonVacuity.not_barrier_AB`). -/
theorem rulesHT_AB : rulesHT.drop 2 = rulesAB := by decide

theorem not_barrier_HT_AB : ¬ BarrierFor (rulesHT.drop 2) := by
  rw [rulesHT_AB]; exact not_barrier_AB

/-- The system `D_H ∪ A` without the left-end rules (8 rules, the same as `usableHT`). -/
def rulesDAH : List Rule := rulesHT.take 8

theorem rulesDAH_eq : rulesDAH = usableHT := by decide

/-- `D_H ∪ A`: the number of binary digits orients the carry rules weakly and the 2 dynamic rules strictly. -/
theorem DAH_oriented : Fin00 Nat.one_pos (wI wBit) ∧ (∀ ρ ∈ rulesDAH, Weak (wI wBit) ρ) ∧
    ∀ ρ ∈ rulesHT.take 2, Strict (wI wBit) ρ :=
  ⟨fin00_wI _, fun ρ hρ => (weak_wI _ ρ).2 (by revert ρ; decide),
    fun ρ hρ => (strict_wI _ ρ).2 (by revert ρ; decide)⟩

theorem not_barrier_DAH : ¬ BarrierFor rulesDAH := fun h =>
  h 1 Nat.one_pos (wI wBit) DAH_oriented.1 DAH_oriented.2.1 ffRule (by decide)
    (DAH_oriented.2.2 _ (by decide))

/-- Removing the dynamic rules from the forward `U` gives `A`, as for $\mathcal T$ (`NonVacuity.not_barrierDP_A`, `not_barrierBZ_A`). -/
theorem usableHT_A : usableHT.drop 2 = usableA := by decide

theorem not_barrierHDP_A : ¬ BarrierDPFor lettersPB (usableHT.drop 2) pairsPB := by
  rw [usableHT_A]; exact not_barrierDP_A

theorem not_barrierHBZ_A : ¬ BarrierBZFor lettersPB (usableHT.drop 2) pairsPB := by
  rw [usableHT_A]; exact not_barrierBZ_A

/-- `A^rev`, obtained by removing the left-end rules from the reversed `U`, is the same as for $\mathcal T$. -/
theorem usableHTrev_A : usableHTrev.take 6 = usableArev := by decide

/-- Reversed (`𝔸_ℕ`): for `(P_D^rev, A^rev)`, the number of binary digits orients `A^rev` weakly and all of `P_D^rev` strictly. -/
theorem not_barrierHDPrev_A : ¬ BarrierDPFor lettersPDrev usableArev pairsPDrevH := by
  intro h
  have hU : ∀ ρ ∈ usableArev, (ρ.plain.rhs.map wBitD).sum ≤ (ρ.plain.lhs.map wBitD).sum := by decide
  have hS : ∀ π ∈ pairsPDrevH, (π.rhs.map wBitD).sum < (π.lhs.map wBitD).sum := by decide
  exact h 1 Nat.one_pos (wJ wBitD) (sf_wJ _ _) (fun ρ hρ => (weakA_wJ _ _ _).2 (hU ρ hρ))
    (fun π hπ => (weakTop_wJ _ _ _).2 (le_of_lt (hS π hπ))) _ (List.mem_cons_self ..)
    ((strictTop_wJ _ _ _).2 (hS _ (List.mem_cons_self ..)))

/-- Reversed (below zero): the same. -/
theorem not_barrierHBZrev_A : ¬ BarrierBZFor lettersPDrev usableArev pairsPDrevH := by
  intro h
  have hU : ∀ ρ ∈ usableArev, (ρ.plain.rhs.map wBitD).sum ≤ (ρ.plain.lhs.map wBitD).sum := by decide
  have hS : ∀ π ∈ pairsPDrevH, (π.rhs.map wBitD).sum < (π.lhs.map wBitD).sum := by decide
  have hP := List.mem_cons_self (a := (⟨[mark rgt, plain f, plain f], [mark rgt, plain d0]⟩ : DRule))
    (l := pairsPDrevH.tail)
  exact h 1 Nat.one_pos (wJZ wBitD) (ap_wJZ _ _)
    (fun ρ hρ => (weakA_wJZ _ (usableArev_ne ρ hρ).1 (usableArev_ne ρ hρ).2).2 (hU ρ hρ))
    (fun π hπ => (weakTop_wJZ _ (pairsPDrevH_ne π hπ).1 (pairsPDrevH_ne π hπ).2).2
      (le_of_lt (hS π hπ)))
    _ hP ((strictTop_wJZ _ (pairsPDrevH_ne _ hP).1 (pairsPDrevH_ne _ hP).2).2 (hS _ hP))

/-! ## §5 Recomputation of the dependency pairs and the usable rules -/

/-- The reversed system of $\mathcal H$. -/
def rulesHTrev : List Rule := rulesHT.map revRule

/-- There are 14 forward dependency pairs (6 from the carry rules and 8 from the left-end rules; none from the dynamic rules) and 11 reversed ones. -/
theorem dps_HT_len : (dpsOf rulesHT).length = 14 := by decide
theorem dps_HTrev_len : (dpsOf rulesHTrev).length = 11 := by decide

/-- The dependency pairs whose right-hand side has root `/#` are exactly `P_B`, and the only pairs entering `/#` are those leaving `/#`. -/
theorem dps_HT_PB :
    (dpsOf rulesHT).filter (fun π => π.rhs.head? = some (mark lft)) = pairsPB := by decide

theorem dps_HT_into_PB : ∀ π ∈ dpsOf rulesHT,
    π.rhs.head? = some (mark lft) → π.lhs.head? = some (mark lft) := by decide

/-- The dependency pairs whose right-hand side has root `.#` are exactly `P_D^rev`, and the only pairs entering `.#` are those leaving `.#`. -/
theorem dps_HTrev_PD :
    (dpsOf rulesHTrev).filter (fun π => π.rhs.head? = some (mark rgt)) = pairsPDrevH := by decide

theorem dps_HTrev_into_PD : ∀ π ∈ dpsOf rulesHTrev,
    π.rhs.head? = some (mark rgt) → π.lhs.head? = some (mark rgt) := by decide

/-- Recomputation of the usable rules. -/
theorem usable_HT : usableOf rulesHT pairsPB = usableHT := by decide
theorem usable_HTrev : usableOf rulesHTrev pairsPDrevH = usableHTrev := by decide

/-- The closure is stable after 7 iterations. -/
theorem close_stable_HT : ∀ x ∈ closeIter rulesHT (pairsPB.flatMap fun π => plainSyms π.rhs) 8,
    x ∈ closeIter rulesHT (pairsPB.flatMap fun π => plainSyms π.rhs) 7 := by decide

theorem close_stable_HTrev :
    ∀ x ∈ closeIter rulesHTrev (pairsPDrevH.flatMap fun π => plainSyms π.rhs) 8,
      x ∈ closeIter rulesHTrev (pairsPDrevH.flatMap fun π => plainSyms π.rhs) 7 := by decide

/-! ## §6 Rule removal for the reversed system (in implication form) -/

/-- The barrier for rule removal for the 11 rules of the reversed system $\mathcal H^{\mathrm{rev}}$ follows from
`ArcticBarrierHT` by transposition (`Weak`, `Strict`, `Fin00` are invariant under transposition). -/
theorem barrier_HTrev_of (hHT : ArcticBarrierHT) : BarrierFor rulesHTrev := by
  intro d hd I hfin hw ρ hρ hs
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hρ
  exact hHT d hd (transI I) (fun s => hfin s)
    (fun τ hτ => (weak_rev_iff I τ).1 (hw _ (List.mem_map_of_mem hτ))) σ hσ
    ((strict_rev_iff I σ).1 hs)

/-! ## §7 Small checks on the domain of `AutoCoreH` -/

/-- `HDom`: `7` is not in it (no dynamic rule applies to `can 7 = /tt.`), `8`, `12`, `15` are, and `9` is not. -/
example : ¬ HModel.HDom 7 ∧ HModel.HDom 8 ∧ HModel.HDom 12 ∧ HModel.HDom 15 ∧ ¬ HModel.HDom 9 := by
  unfold HModel.HDom; decide

/-- For the classes outside the domain (`n ≡ 1, 2, 3, 5, 6 mod 8`) the canonical derivation is empty (no dynamic rule applies at the right end). For `n = 0, 4, 7`
the class is `≡ 0 mod 4` or `≡ 7 mod 8`, so it is not empty (e.g. `canDerivH 0 = [ffRule, leftRule 0]`). Every use is guarded by `HDom`. -/
example : canDerivH 9 = [] ∧ canDerivH 10 = [] ∧ canDerivH 11 = [] ∧ canDerivH 13 = [] ∧
    canDerivH 14 = [] := by decide

end NonVacuityH

end Collatz.Arctic.HTPDB
