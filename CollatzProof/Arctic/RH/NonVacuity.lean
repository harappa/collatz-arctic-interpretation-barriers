/-
Checks of the non-vacuity of the main statement for $R_H$ (Propositions 4.3 and 4.5; Section 14).
Uses the tools of the files `NonVacuity*.lean` for $\mathcal T$ and $\mathcal H$; existing files are not changed. The proofs use only `decide` and
existing lemmas. This file serves only as a check and is not in the closure of the main theorem (it imports `Summary` for
$\mathcal T$).

* §1 Instance of the general form: `ArcticBarrierRH` is `NonVacuity.BarrierFor usedRH` (`Iff.rfl`). The agreement with the definitions of Koprowski–Waldmann 2009
  (§1 of `NonVacuity`, checked for $\mathcal T$) therefore applies verbatim.
* §2 The premises are satisfiable (dimension 1, all 12 rules).
* §3 Is strict orientation possible by definition? The 10 rules other than the two commutation rules (`f0 → 0f`, `t2 → 2t`) are strictly
  oriented by some interpretation. The two commutation rules are strictly oriented by no interpretation (`not_strict_swap`).
* §4 **The barrier fails once `L0 → L`, `Lf → L` are included**: the 2-dimensional interpretation `ILeft` weakly orients all 12 rules and strictly orients `L0 → L` and
  `Lf → L` (it strictly orients no used rule, consistent with the main theorem). Hence the restriction of the set of rules of the main theorem
  to `usedRH` cannot be dropped, and in the general arctic form without (CF) (`ArcticBarrierRHSub`) the case that only the remaining
  `L0 → L`, `Lf → L` are strictly oriented actually occurs. `ILeft` does not satisfy (CF) (column 0 of `M_f` has two finite
  entries), so whether this bound is attained under (CF) is open (Question 4.4; the search in the internal review was discontinued).
* §5 Counterexamples for subsystems: the system without the dynamic rules (`A ∪ {L1, L2}`, and also `X` with `L0`, `Lf` added) and the system without the left-end rules
  (`A ∪ D_H`) can be weakly oriented with some used rule strictly oriented. Hence the truth of the statement depends on the Collatz dynamics.
* §6 Rule removal for the reversed system (as an implication).
* §7 Small checks of the intermediate statement.
-/
import CollatzProof.Arctic.HTPDB.NonVacuity
import CollatzProof.Arctic.RH.Statement

namespace Collatz.Arctic.RH

namespace NonVacuityRH

open Collatz.Arctic Collatz.Arctic.NonVacuity Collatz.Arctic.HTPDB Letter

/-! ## §1 Instance of the general form -/

theorem RH_iff : ArcticBarrierRH ↔ BarrierFor usedRH := Iff.rfl

/-! ## §2 The premises are satisfiable -/

/-- All 12 rules (hence the 10 used rules) are weakly oriented (weight 3 on `L`, 5 on `.`, 0 on the others). -/
theorem hyp_RH_sat : ∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧ ∀ ρ ∈ rulesRH, Weak I ρ :=
  ⟨1, Nat.one_pos, wI wLR, fin00_wI _, fun ρ hρ => (weak_wI _ ρ).2 (by revert ρ; decide)⟩

theorem hyp_RH_sat_used :
    ∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧ ∀ ρ ∈ usedRH, Weak I ρ := by
  obtain ⟨d, hd, I, hfin, hw⟩ := hyp_RH_sat
  exact ⟨d, hd, I, hfin, fun ρ hρ => hw ρ (usedRH_sub ρ hρ)⟩

/-! ## §3 Is strict orientation possible by definition? -/

/-- Each of the 10 rules other than the two commutation rules strictly decreases the number of occurrences of some symbol. -/
theorem strict_RH_ind : ∀ ρ ∈ rulesRH, ρ ≠ ⟨[f, d0], [d0, f]⟩ → ρ ≠ ⟨[t, d2], [d2, t]⟩ →
    ∃ x ∈ [f, t, d0, d1, d2, lft, rgt], (ρ.rhs.map (ind x)).sum < (ρ.lhs.map (ind x)).sum := by
  decide

/-- Complete classification of the strict orientability of the rules of $R_H$: the rules strictly oriented by some interpretation are exactly the
10 rules other than the two commutation rules (8 of them are used rules; for the two commutation rules the conclusion of the main theorem is trivial). -/
theorem strict_possible_iff_RH : ∀ ρ ∈ rulesRH,
    (∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧ Strict I ρ) ↔
      (ρ ≠ ⟨[f, d0], [d0, f]⟩ ∧ ρ ≠ ⟨[t, d2], [d2, t]⟩) := by
  intro ρ hρ
  constructor
  · rintro ⟨d, hd, I, hfin, hs⟩
    refine ⟨?_, ?_⟩
    · rintro rfl; exact not_strict_swap hd I hfin f d0 hs
    · rintro rfl; exact not_strict_swap hd I hfin t d2 hs
  · rintro ⟨h1, h2⟩
    obtain ⟨x, -, hx⟩ := strict_RH_ind ρ hρ h1 h2
    exact ⟨1, Nat.one_pos, wI (ind x), fin00_wI _, (strict_wI _ _).2 hx⟩

/-! ## §4 The barrier fails once `L0 → L`, `Lf → L` are included -/

/-- A 2-dimensional interpretation. Index 0 is free (every symbol is a self-loop of weight 0), and `L` leads to index 1 (weight 0). Index 1 means inside the run of
`f`, `0` right after `L`: `f` and `0` go `1 → 1` and `1 → 0` with weight 1, the other symbols (`t`, `1`, `2`, `.`) go `1 → 0` with weight 0,
and `L` has no edge from index 1. Entries not mentioned are −∞ (the `0` of `Arc`). -/
def ILeft : Interp 2 := fun s =>
  match s with
  | Letter.f => !![Arc.fin 0, 0; Arc.fin 1, Arc.fin 1]
  | Letter.d0 => !![Arc.fin 0, 0; Arc.fin 1, Arc.fin 1]
  | Letter.lft => !![Arc.fin 0, Arc.fin 0; 0, 0]
  | _ => !![Arc.fin 0, 0; Arc.fin 0, 0]

theorem ILeft_fin00 : Fin00 (by norm_num : 0 < 2) ILeft := by
  intro s; cases s <;> decide

/-- `ILeft` weakly orients all 12 rules. -/
theorem ILeft_weak : ∀ ρ ∈ rulesRH, Weak ILeft ρ := by
  unfold Weak; intro ρ hρ; simp only [Fin.forall_fin_two]; revert ρ; decide

/-- `ILeft` strictly orients `L0 → L`. -/
theorem ILeft_strict_l0 : Strict ILeft l0Rule := by
  unfold Strict; simp only [Fin.forall_fin_two]; decide

/-- `ILeft` strictly orients `Lf → L`. -/
theorem ILeft_strict_lf : Strict ILeft lfRule := by
  unfold Strict; simp only [Fin.forall_fin_two]; decide

/-- `ILeft` strictly orients none of the used rules (consistent with the main theorem). -/
theorem ILeft_not_strict_used : ∀ ρ ∈ usedRH, ¬ Strict ILeft ρ := by
  unfold Strict; intro ρ hρ; simp only [Fin.forall_fin_two]; revert ρ; decide

/-- The barrier for all 12 rules is false (Proposition 4.3). -/
theorem not_barrier_rulesRH : ¬ BarrierFor rulesRH := fun h =>
  h 2 (by norm_num) ILeft ILeft_fin00 ILeft_weak l0Rule (by decide) ILeft_strict_l0

/-- It is also false for the used rules together with `L0 → L` alone, or with `Lf → L` alone. -/
theorem not_barrier_used_l0 : ¬ BarrierFor (usedRH ++ [l0Rule]) := fun h =>
  h 2 (by norm_num) ILeft ILeft_fin00
    (fun ρ hρ => ILeft_weak ρ (by
      rcases List.mem_append.mp hρ with h' | h'
      · exact usedRH_sub ρ h'
      · rw [List.mem_singleton] at h'; subst h'; decide))
    l0Rule (by decide) ILeft_strict_l0

theorem not_barrier_used_lf : ¬ BarrierFor (usedRH ++ [lfRule]) := fun h =>
  h 2 (by norm_num) ILeft ILeft_fin00
    (fun ρ hρ => ILeft_weak ρ (by
      rcases List.mem_append.mp hρ with h' | h'
      · exact usedRH_sub ρ h'
      · rw [List.mem_singleton] at h'; subst h'; decide))
    lfRule (by decide) ILeft_strict_lf

/-! ## §5 Counterexamples for subsystems (all rules weakly, some used rule strictly) -/

/-- The used rules without the dynamic rules, `A ∪ {L1 → Lt, L2 → Ltf}`. -/
theorem usedRH_take_eight : usedRH.take 8 = rulesRH.take 6 ++ [leftRuleRH 1, leftRuleRH 2] := by decide

/-- `A ∪ {L1, L2}` and `X` (`rulesRH.take 10`, containing `L0`, `Lf`): the number of ternary digits weakly orients A and `Lf → L` and
strictly orients `L0`, `L1`, `L2`. -/
theorem X_oriented : Fin00 Nat.one_pos (wI wDig) ∧ (∀ ρ ∈ rulesRH.take 10, Weak (wI wDig) ρ) ∧
    ∀ ρ ∈ [l0Rule, leftRuleRH 1, leftRuleRH 2], Strict (wI wDig) ρ :=
  ⟨fin00_wI _, fun ρ hρ => (weak_wI _ ρ).2 (by revert ρ; decide),
    fun ρ hρ => (strict_wI _ ρ).2 (by revert ρ; decide)⟩

theorem not_barrier_noDyn : ¬ BarrierFor (usedRH.take 8) := fun h =>
  h 1 Nat.one_pos (wI wDig) X_oriented.1
    (fun ρ hρ => X_oriented.2.1 ρ (by revert ρ; decide)) (leftRuleRH 1) (by decide)
    (X_oriented.2.2 _ (by decide))

theorem not_barrier_X : ¬ BarrierFor (rulesRH.take 10) := fun h =>
  h 1 Nat.one_pos (wI wDig) X_oriented.1 X_oriented.2.1 (leftRuleRH 1) (by decide)
    (X_oriented.2.2 _ (by decide))

/-- The used rules without the left-end rules, `A ∪ D_H` (the same rules as `usableHT` of $\mathcal H$). -/
def usedDA : List Rule := usedRH.take 6 ++ usedRH.drop 8

theorem usedDA_perm : (∀ ρ ∈ usedDA, ρ ∈ usableHT) ∧ ∀ ρ ∈ usableHT, ρ ∈ usedDA := by decide

/-- `A ∪ D_H`: the number of binary digits weakly orients A and strictly orients the two dynamic rules. -/
theorem DA_oriented_RH : Fin00 Nat.one_pos (wI wBit) ∧ (∀ ρ ∈ usedDA, Weak (wI wBit) ρ) ∧
    ∀ ρ ∈ [ffRule, tttRule], Strict (wI wBit) ρ :=
  ⟨fin00_wI _, fun ρ hρ => (weak_wI _ ρ).2 (by revert ρ; decide),
    fun ρ hρ => (strict_wI _ ρ).2 (by revert ρ; decide)⟩

theorem not_barrier_noLeft : ¬ BarrierFor usedDA := fun h =>
  h 1 Nat.one_pos (wI wBit) DA_oriented_RH.1 DA_oriented_RH.2.1 ffRule (by decide)
    (DA_oriented_RH.2.2 _ (by decide))

/-! ## §6 Rule removal for the reversed system (as an implication) -/

/-- The barrier for the used rules of the reversed system $R_H^{\mathrm{rev}}$ follows from `ArcticBarrierRH` by transposition
(`Weak`, `Strict`, `Fin00` are invariant under transposition). -/
theorem barrier_RHrev_of (hRH : ArcticBarrierRH) : BarrierFor (usedRH.map revRule) := by
  intro d hd I hfin hw ρ hρ hs
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hρ
  exact hRH d hd (transI I) (fun s => hfin s)
    (fun τ hτ => (weak_rev_iff I τ).1 (hw _ (List.mem_map_of_mem hτ))) σ hσ
    ((strict_rev_iff I σ).1 hs)

/-! ## §7 Small checks of the intermediate statement -/

/-- `AutoCoreRH` has the same map and domain as `AutoCoreH`; only the rules and the canonical derivations differ. -/
example : AutoCoreRH = Gen.AutoCoreG HModel.Hmap HModel.HDom usedRH canDerivRH := rfl

/-- `HDom` is the same as for $\mathcal H$ (`7` is not in it; the formula of `canDerivRH` for a $\mathsf b$-step uses `m = (n-7)/8 ≥ 1`). -/
example : ¬ HModel.HDom 7 ∧ HModel.HDom 8 ∧ HModel.HDom 12 ∧ HModel.HDom 15 ∧ ¬ HModel.HDom 9 := by
  unfold HModel.HDom; decide

/-- A small check of `canRH n = L bin(n) .` (examples of `canRH_eq_bin`). -/
example : canRH 7 = [lft, t, t, t, rgt] ∧ canRH 8 = [lft, t, f, f, f, rgt] := by decide

end NonVacuityRH

end Collatz.Arctic.RH
