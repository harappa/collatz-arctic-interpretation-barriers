/-
# Checks of the statements `NatBarrierSTrev` and `NatBarrierSTrevTop` for $\mathcal T^{\mathrm{rev}}$ (Theorem 9.2 (i), (ii) of the paper): non-vacuity

Of the type of `Nat/NonVacuity*.lean`. We look for errors on the side of the statement (`StatementRev.lean`, written while it was a draft; it is now frozen): errors in the transcription of rules, vacuous premises, conclusions
trivial by definition, a confusion about whether monotonicity is needed, deviations from the conventions of the frozen forward statement. Outside the closure of the main theorem. Existing files are
not changed. No `sorry`, `axiom` declaration or `native_decide` is used (computations by `decide +kernel`).

* §1 Check of the rules: `rulesSTrev` agrees with the list of the reversed rules numbered 0 to 10 (`rulesSTrev_eq_table`), and equals the arctic `NonVacuity.rulesSTrev`,
  `Rule.rev` and `ruleRev` (`rulesSTrev_eq_arctic`, `rulesSTrev_eq_RuleRev`). It has no rule in common with $\mathcal T$.
  The top rules are the rules 0 and 1 of `rulesSTrev`.
* §2 "The rules used": each of the 11 rules is used by the mirrored canonical derivations (`rulesSTrev_used`), and conversely the rules of the mirrored derivations are among the 11 rules.
  Equivalence with the statement written with "the rules used" (`natBarrierSTrev_iff_used`). A small example of a mirrored derivation (`n = 3`).
* §3 (a) The premises are satisfiable: the identity interpretation (in every dimension); the monotone `IP3rev` of dimension 4 (the image of `IP3` under the transformation of §7;
  the small values of `Φ^rev(n) = 1 + 2^{ℓ(n)-1}[3 ∣ n]` grow on `3 ∣ n`). The premises of the statement for the top rules can also be satisfied by a non-monotone interpretation.
* §4 (b) Strict orientation is possible by definition: for each of the 11 rules, a monotone interpretation of dimension 1 that strictly orients it.
* §5 (d) Without monotonicity the statement is false: the interpretation `INoMonoRev` of dimension 1 in which only `.` is not monotone (`[.] = 0`; the mirror of the forward `INoMono`)
  weakly orients the 11 rules and strictly orients all 9 rules other than the top rules.
  So the set of rules of `NatBarrierSTrevTop` cannot be enlarged. The 2 top rules are not strictly oriented (consistent with the statement).
* §6 (c) The barrier fails for subsystems: monotone interpretations of dimension 1 for the systems without `.t → .2`, without `1f → t0`, and without `2f → f1`
  (three examples of dimension 1), and the two interpretations of Lemma 3.15 of Yolcu–Aaronson–Heule (as printed on p. 20; they strictly orient all 8 rules of $(\mathcal T \setminus B)^{\mathrm{rev}}$
  and all 9 rules of $(\mathcal T \setminus D_T)^{\mathrm{rev}}$, respectively).
* §6b Direct check of the direction of composition (internal review of the statement): the 20 composed values printed in Theorem 4.1 of Yolcu–Aaronson–Heule are reproduced by `evN`, and
  not with the opposite direction (`I41_printed`). The counterpart of the forward `yah_ex43_values` (Example 4.3 of Yolcu–Aaronson–Heule).
* §7 For the subclass of condition (U) (not treated in the paper), `NatBarrierSTrev` follows directly from the frozen forward statement `NatBarrierST`
  (by transposition and the exchange of index 0 with the homogeneous index; an independent route that does not pass through the value-level core, as a check that the conventions of the two statements
  (the direction of composition, the component of the strict comparison) agree).
* §8 Negative controls: claims that do not hold are decided false by `decide +kernel`.
-/
import CollatzProof.Arctic.Nat.BridgeRev
import CollatzProof.Arctic.Nat.NonVacuity3
import CollatzProof.Arctic.NonVacuity4

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter

namespace W5

/-! ## §1 Check of the rules -/

/-- The list of the reversed rules (numbered 0 to 10). -/
theorem rulesSTrev_eq_table : rulesSTrev =
    [⟨[rgt, f], [rgt]⟩, ⟨[rgt, t], [rgt, d2]⟩,
      ⟨[d0, f], [f, d0]⟩, ⟨[d1, f], [t, d0]⟩, ⟨[d2, f], [f, d1]⟩,
      ⟨[d0, t], [t, d1]⟩, ⟨[d1, t], [f, d2]⟩, ⟨[d2, t], [t, d2]⟩,
      ⟨[d0, lft], [t, lft]⟩, ⟨[d1, lft], [f, f, lft]⟩, ⟨[d2, lft], [t, f, lft]⟩] := by
  decide

/-- The same as the arctic reversed system (`rulesSTrev` of `NonVacuity4.lean`, `revRule`). -/
theorem rulesSTrev_eq_arctic : rulesSTrev = NonVacuity.rulesSTrev := rfl

/-- The same when written with `Rule.rev` of `DPBridge.lean`. -/
theorem rulesSTrev_eq_RuleRev : rulesSTrev = rulesST.map Rule.rev := rfl

theorem rulesSTrev_length : rulesSTrev.length = 11 := by decide

theorem rulesSTrev_nodup : rulesSTrev.Nodup := by decide

/-- No rule in common with $\mathcal T$. -/
theorem rulesSTrev_disjoint : ∀ ρ ∈ rulesSTrev, ρ ∉ rulesST := by decide

/-- The top rules are the rules 0 and 1 of `rulesSTrev`. -/
theorem rulesSTrevTop_eq_take : rulesSTrevTop = rulesSTrev.take 2 := by decide

/-! ## §2 "The rules used" -/

/-- Each of the 11 rules is used by the mirrored canonical derivations (the witnesses `n` are those of the forward `rulesST_used`). -/
theorem rulesSTrev_used : ∀ ρ ∈ rulesSTrev, UsedSTrev ρ := by
  intro ρ' hρ'
  obtain ⟨ρ, hρ, rfl⟩ := mem_rulesSTrev hρ'
  obtain ⟨n, hn, hmem⟩ := rulesST_used ρ hρ
  exact ⟨n, hn, List.mem_map_of_mem hmem⟩

theorem usedRev_mem {ρ : Rule} (h : UsedSTrev ρ) : ρ ∈ rulesSTrev := by
  obtain ⟨n, -, hn⟩ := h
  exact canDerivRev_sub n ρ hn

theorem usedSTrev_iff (ρ : Rule) : UsedSTrev ρ ↔ ρ ∈ rulesSTrev := ⟨usedRev_mem, rulesSTrev_used ρ⟩

/-- A small example of a mirrored derivation: from `rev (can 3) = . t /` to `. 2 /` (`.t → .2`), then to `. t f /` (`2/ → tf/`) `= rev (can 5)`. -/
theorem canDerivRev_three : canDerivRev 3 = [⟨[rgt, t], [rgt, d2]⟩, ⟨[d2, lft], [t, f, lft]⟩] ∧
    (can 3).reverse = [rgt, t, lft] ∧ (can (T 3)).reverse = [rgt, t, f, lft] := by
  decide +kernel

end W5

open W5

/-- The statement written with "the rules used" is equivalent to `NatBarrierSTrev`. -/
theorem natBarrierSTrev_iff_used : NatBarrierSTrev ↔ NatBarrierSTrevUsed := by
  constructor
  · intro h d _ I hmono hweak ρ hρ
    exact h d I hmono (fun σ hσ => hweak σ (rulesSTrev_used σ hσ)) ρ (usedRev_mem hρ)
  · intro h d _ I hmono hweak ρ hρ
    exact h d I hmono (fun σ hσ => hweak σ (usedRev_mem hσ)) ρ (rulesSTrev_used ρ hρ)

namespace W5

/-! ## §3 (a) The premises are satisfiable -/

/-- In every dimension `d ≥ 1` the identity interpretation is monotone and weakly orients all 11 rules of $\mathcal T^{\mathrm{rev}}$. -/
theorem premises_id_rev (d : ℕ) [NeZero d] :
    NMono (fun _ : Letter => NAff.id d) ∧ ∀ ρ ∈ rulesSTrev, NWeak (fun _ : Letter => NAff.id d) ρ := by
  refine ⟨(premises_id d).1, fun ρ _ => ?_⟩
  rw [NWeak, evN_idI, evN_idI]
  exact ⟨fun _ _ => le_rfl, fun _ => le_rfl⟩

/-- The image of `IP3` (the example of dimension 4 of Proposition 9.5 of the paper for $\mathcal T$) under the transformation of §7 (`N''_s := P N_s^T P`, where `P` exchanges index 0 and
the homogeneous index; `uInterp IP3rev = IP3` in §7). A monotone interpretation of dimension 4 of $\mathcal T^{\mathrm{rev}}$. -/
def IP3rev : Letter → NAff 4
  | .f => ⟨!![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0], 0⟩
  | .t => ⟨!![1, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 2], 0⟩
  | .d0 => ⟨!![1, 0, 0, 0; 0, 4, 4, 4; 0, 0, 0, 0; 0, 0, 0, 0], 0⟩
  | .d1 => ⟨!![1, 0, 0, 0; 0, 0, 0, 0; 0, 4, 4, 4; 0, 0, 0, 0], 0⟩
  | .d2 => ⟨!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 4, 4, 4], 0⟩
  | .lft => ⟨!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], ![0, 0, 1, 0]⟩
  | .rgt => ⟨!![1, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], ![1, 0, 0, 0]⟩

theorem IP3rev_mono : NMono IP3rev := fun s => by cases s <;> decide

theorem IP3rev_weak : ∀ ρ ∈ rulesSTrev, NWeak IP3rev ρ := by decide +kernel

theorem IP3rev_not_strict : ∀ ρ ∈ rulesSTrev, ¬ NStrict IP3rev ρ := by decide +kernel

/-- Small values of `Φ^rev(n) = 1 + 2^{ℓ(n)-1}[3 ∣ n]` (the same as `Φ(can n)` for `IP3`; they grow with the length on the multiples of 3). -/
theorem IP3rev_phi_values :
    PhiN IP3rev (can 3).reverse = 3 ∧ PhiN IP3rev (can 6).reverse = 5 ∧ PhiN IP3rev (can 12).reverse = 9 ∧
    PhiN IP3rev (can 24).reverse = 17 ∧ PhiN IP3rev (can 5).reverse = 1 ∧ PhiN IP3rev (can 7).reverse = 1 := by
  decide +kernel

/-- `IP3rev` does not weakly orient the 11 rules in the direction of $\mathcal T$ (it is an interpretation of the reversed system, not of the forward one). -/
theorem IP3rev_not_weak_ST : ¬ ∀ ρ ∈ rulesST, NWeak IP3rev ρ := by decide +kernel

/-- A non-monotone interpretation of dimension 1: `[f] = [.] = y`, `[t] = [d_i] = 1`, `[/] = 0` (based on the transpose of `NRev`). -/
def INRev : Letter → NAff 1 := wI1 (fun s => if s = f ∨ s = rgt then 1 else 0)
  (fun s => if s = t ∨ s = d0 ∨ s = d1 ∨ s = d2 then 1 else 0)

theorem INRev_not_mono : ¬ NMono INRev := fun h => by
  have := h t
  revert this
  decide

theorem INRev_weak : ∀ ρ ∈ rulesSTrev, NWeak INRev ρ := by decide +kernel

/-- **The premises of the statement for the top rules can be satisfied by a non-monotone interpretation**: `INRev` strictly orients neither top rule (consistent with the conclusion). -/
theorem INRev_not_strict_top : ∀ ρ ∈ rulesSTrevTop, ¬ NStrict INRev ρ := by decide +kernel

/-- `INRev` strictly orients `1/ → ff/`, which is not a top rule (no contradiction with `NatBarrierSTrev`, as `INRev` is not monotone). -/
theorem INRev_strict_L1 : NStrict INRev ⟨[d1, lft], [f, f, lft]⟩ := by decide +kernel

/-! ## §4 (b) Strict orientation is possible by definition -/

/-- **(b)**: for each of the 11 rules of $\mathcal T^{\mathrm{rev}}$ there is a monotone interpretation of dimension 1 that strictly orients it (the weak orientation of the other rules
is not required). The commutation rules `0f → f0`, `2t → t2` are handled by a letter of slope 2 and a letter with constant term 1 (`[0f](y) = 2y + 2 > 2y + 1 = [f0](y)`;
the roles of the letters are exchanged compared with the forward `strict_each`), the others by the constant term 1 of a single letter. -/
theorem strict_each_rev : ∀ ρ ∈ rulesSTrev, ∃ I : Letter → NAff 1, NMono I ∧ NStrict I ρ := by
  intro ρ hρ
  rw [rulesSTrev_eq_table] at hρ
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨wI1 (fun _ => 1) (ind f), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind t), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (dbl d0) (ind f), mono_wI1 (mono_dbl d0), by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d1), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d2), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d0), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d1), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (dbl d2) (ind t), mono_wI1 (mono_dbl d2), by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d0), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d1), mono_wI1 mono_one, by decide +kernel⟩
  · exact ⟨wI1 (fun _ => 1) (ind d2), mono_wI1 mono_one, by decide +kernel⟩

/-- The interpretations of the forward `strict_each` for the commutation rules do not strictly orient the reversed commutation rules (the direction of composition matters). -/
theorem strict_swap_direction :
    ¬ NStrict (wI1 (dbl f) (ind d0)) ⟨[d0, f], [f, d0]⟩ ∧ ¬ NStrict (wI1 (dbl t) (ind d2)) ⟨[d2, t], [t, d2]⟩ := by
  decide +kernel

/-! ## §5 (d) Without monotonicity the statement is false -/

/-- Slopes: 0 for `.`, 2 for the ternary digits, 1 for the others. -/
def nmAr : Letter → ℕ
  | .rgt => 0
  | .d0 => 2
  | .d1 => 2
  | .d2 => 2
  | _ => 1

/-- Constant terms: 2 for `/`, 0 for `.`, 1 for the others. -/
def nmCr : Letter → ℕ
  | .lft => 2
  | .rgt => 0
  | _ => 1

/-- `[f](y) = [t](y) = y + 1`, `[d](y) = 2y + 1`, `[/](y) = y + 2`, `[.](y) = 0` (only `.` is not monotone; the mirror of the forward
`INoMono`, in which only `/` is not monotone). -/
def INoMonoRev : Letter → NAff 1 := wI1 nmAr nmCr

theorem INoMonoRev_mono_except_rgt : (INoMonoRev rgt).M 0 0 = 0 ∧ ∀ s, s ≠ rgt → 1 ≤ (INoMonoRev s).M 0 0 := by
  refine ⟨rfl, fun s hs => ?_⟩
  cases s <;> first | exact absurd rfl hs | decide

theorem INoMonoRev_not_mono : ¬ NMono INoMonoRev := fun h => by
  have := h rgt
  revert this
  decide

theorem INoMonoRev_weak : ∀ ρ ∈ rulesSTrev, NWeak INoMonoRev ρ := by decide +kernel

/-- **Sharpness**: each of the 9 rules other than the top rules is strictly oriented by the non-monotone interpretation `INoMonoRev`, which weakly orients the 11 rules. -/
theorem noMono_strict_nonTop : ∀ ρ ∈ rulesSTrev, ρ ∉ rulesSTrevTop → NStrict INoMonoRev ρ := by decide +kernel

/-- The 2 top rules are not strictly oriented (even by `INoMonoRev`) (consistent with `NatBarrierSTrevTop`). -/
theorem INoMonoRev_not_strict_top : ∀ ρ ∈ rulesSTrevTop, ¬ NStrict INoMonoRev ρ := by decide +kernel

/-- In this interpretation `Φ^rev(n) = 0` (`[.]` is the constant 0). Strict orientation does not give a decrease of `Φ^rev`. -/
theorem INoMonoRev_phi (n : ℕ) : PhiN INoMonoRev (can n).reverse = 0 := by
  rw [can_reverse, phiN_eq]
  show ((INoMonoRev rgt).comp (evN INoMonoRev ((binTail n).reverse ++ [lft]))).v 0 = 0
  simp [NAff.comp, INoMonoRev, wI1, nmAr, nmCr, mulVec, dotProduct]

end W5

/-- **(d)**: without monotonicity the statement for $\mathcal T^{\mathrm{rev}}$ is false. -/
theorem not_barrierRev_noMono : ¬ NatBarrierForNoMono rulesSTrev := fun h =>
  h 1 INoMonoRev INoMonoRev_weak ⟨[d0, f], [f, d0]⟩ (by decide) (noMono_strict_nonTop _ (by decide) (by decide))

theorem natBarrierSTrev_iff_for : NatBarrierSTrev ↔ NatBarrierFor rulesSTrev := Iff.rfl

/-- The part of `NatBarrierSTrev` on the top rules (the monotone case) follows from `NatBarrierSTrevTop`. -/
theorem natBarrierSTrev_top_of_top (h : NatBarrierSTrevTop) :
    ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), NMono I → (∀ ρ ∈ rulesSTrev, NWeak I ρ) →
      ∀ ρ ∈ rulesSTrevTop, ¬ NStrict I ρ := by
  intro d _ I _ hw
  exact h d I hw

namespace W5

/-! ## §6 (c) The barrier fails for subsystems -/

/-- Monotone, dimension 1: all slopes 1, constant term 1 for the ternary digits. Weakly orients $\mathcal T^{\mathrm{rev}}$ without `.t → .2`, and strictly orients the 3 rules of `B^rev`. -/
def IDropTdot : Letter → NAff 1 := wI1 (fun _ => 1) (fun s => if s = d0 ∨ s = d1 ∨ s = d2 then 1 else 0)

theorem IDropTdot_mono : NMono IDropTdot := mono_wI1 mono_one

theorem IDropTdot_weak : ∀ ρ ∈ rulesSTrev.erase ⟨[rgt, t], [rgt, d2]⟩, NWeak IDropTdot ρ := by decide +kernel

theorem IDropTdot_strict :
    ∀ ρ ∈ [(⟨[d0, lft], [t, lft]⟩ : Rule), ⟨[d1, lft], [f, f, lft]⟩, ⟨[d2, lft], [t, f, lft]⟩], NStrict IDropTdot ρ := by
  decide +kernel

theorem IDropTdot_not_weak : ¬ NWeak IDropTdot ⟨[rgt, t], [rgt, d2]⟩ := by decide +kernel

/-- Monotone, dimension 1: all slopes 1, constant term 1 for `0`. Weakly orients $\mathcal T^{\mathrm{rev}}$ without `1f → t0`, and strictly orients `0t → t1` and `0/ → t/`. -/
def IDropF1 : Letter → NAff 1 := wI1 (fun _ => 1) (ind d0)

theorem IDropF1_weak : ∀ ρ ∈ rulesSTrev.erase ⟨[d1, f], [t, d0]⟩, NWeak IDropF1 ρ := by decide +kernel

theorem IDropF1_strict : NStrict IDropF1 ⟨[d0, t], [t, d1]⟩ ∧ NStrict IDropF1 ⟨[d0, lft], [t, lft]⟩ := by
  decide +kernel

theorem IDropF1_not_weak : ¬ NWeak IDropF1 ⟨[d1, f], [t, d0]⟩ := by decide +kernel

/-- Monotone, dimension 1: all slopes 1, constant term 1 for `0` and `1`. Weakly orients $\mathcal T^{\mathrm{rev}}$ without `2f → f1`, and strictly orients `1t → f2`, `0/ → t/` and
`1/ → ff/`. -/
def IDropF2 : Letter → NAff 1 := wI1 (fun _ => 1) (fun s => if s = d0 ∨ s = d1 then 1 else 0)

theorem IDropF2_weak : ∀ ρ ∈ rulesSTrev.erase ⟨[d2, f], [f, d1]⟩, NWeak IDropF2 ρ := by decide +kernel

theorem IDropF2_strict : NStrict IDropF2 ⟨[d1, t], [f, d2]⟩ ∧ NStrict IDropF2 ⟨[d0, lft], [t, lft]⟩ ∧
    NStrict IDropF2 ⟨[d1, lft], [f, f, lft]⟩ := by
  decide +kernel

theorem IDropF2_not_weak : ¬ NWeak IDropF2 ⟨[d2, f], [f, d1]⟩ := by decide +kernel

/-- The barrier fails for subsystems (three ways of removing a rule). -/
theorem not_barrierRev_drop :
    ¬ NatBarrierFor (rulesSTrev.erase ⟨[rgt, t], [rgt, d2]⟩) ∧ ¬ NatBarrierFor (rulesSTrev.erase ⟨[d1, f], [t, d0]⟩) ∧
      ¬ NatBarrierFor (rulesSTrev.erase ⟨[d2, f], [f, d1]⟩) :=
  ⟨not_barrierFor IDropTdot IDropTdot_mono IDropTdot_weak ⟨[d0, lft], [t, lft]⟩ (by decide)
      (IDropTdot_strict _ (by decide)),
    not_barrierFor IDropF1 (mono_wI1 mono_one) IDropF1_weak ⟨[d0, t], [t, d1]⟩ (by decide) IDropF1_strict.1,
    not_barrierFor IDropF2 (mono_wI1 mono_one) IDropF2_weak ⟨[d1, t], [f, d2]⟩ (by decide) IDropF2_strict.1⟩

/-- **The first interpretation of Lemma 3.15 of Yolcu–Aaronson–Heule** (as printed on p. 20: `[f](x) = [t](x) = 2x + 1`, `[▷](x) = x`,
`[0](x) = [1](x) = [2](x) = 2x`; `[◁]` is not printed, as it does not occur in $(\mathcal T \setminus B)^{\mathrm{rev}}$, and we put `[/] = y`):
monotone, of dimension 1, it strictly orients all 8 rules of $(\mathcal T \setminus B)^{\mathrm{rev}}$ (the 2 top rules and the 6 rules of `A^rev`). It does not even weakly orient
the 3 rules of `B^rev` (consistent with `NatBarrierSTrev`). The remark of the first version that `[.]` was chosen here and not checked against the printed values was outdated by
a check against the primary source in an internal review of the statement: `[.] = y` agrees with the printed `[▷] = x`. -/
def IL315 : Letter → NAff 1 :=
  wI1 (fun s => if s = lft ∨ s = rgt then 1 else 2) (fun s => if s = f ∨ s = t then 1 else 0)

theorem IL315_mono : NMono IL315 := fun s => by cases s <;> decide

theorem IL315_strict : ∀ ρ ∈ rulesSTrev.take 8, NStrict IL315 ρ := by decide +kernel

theorem IL315_not_weak_B : ∀ ρ ∈ rulesSTrev.drop 8, ¬ NWeak IL315 ρ := by decide +kernel

/-- **Check of the direction of composition (indirect)**: the same interpretation does not even weakly orient the 6 forward carry rules `A` (`[f0] = 4y + 1 < 4y + 2 = [0f]`).
The interpretation that Yolcu–Aaronson–Heule apply to the reversed system orients `A^rev` only with the direction of composition of `evN` (`[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]`) (indirect evidence that presupposes that the proof of Yolcu–Aaronson–Heule
is correct; the direct check is `I41_printed` of §6b). -/
theorem IL315_not_weak_A_forward : ∀ ρ ∈ (rulesST.drop 2).take 6, ¬ NWeak IL315 ρ := by decide +kernel

/-- `[.]` of `IL315` is the printed `[▷](x) = x` of Yolcu–Aaronson–Heule. -/
theorem IL315_rgt : (IL315 rgt).M 0 0 = 1 ∧ (IL315 rgt).v 0 = 0 := by decide

/-- **The second interpretation of Lemma 3.15 of Yolcu–Aaronson–Heule** (p. 20, for $(\mathcal T \setminus D_T)^{\mathrm{rev}}$: `[f](x) = [t](x) = [◁](x) = x + 1`,
`[0](x) = [1](x) = [2](x) = 4x`; `[▷]` does not occur, and we put `y`; `IL315b` of an internal review of the statement): monotone, of dimension 1, it strictly orients all
9 rules of `X^rev`, and does not even weakly orient the forward `X`. -/
def IL315b : Letter → NAff 1 :=
  wI1 (fun s => if s = d0 ∨ s = d1 ∨ s = d2 then 4 else 1) (fun s => if s = f ∨ s = t ∨ s = lft then 1 else 0)

theorem IL315b_strict : NMono IL315b ∧ ∀ ρ ∈ rulesSTrev.drop 2, NStrict IL315b ρ :=
  ⟨fun s => by cases s <;> decide, by decide +kernel⟩

theorem IL315b_forward_fails : ¬ ∀ ρ ∈ rulesST.drop 2, NWeak IL315b ρ := by decide +kernel

/-! ## §6b Direct check of the direction of composition: the printed values of Theorem 4.1 of Yolcu–Aaronson–Heule (internal review of the statement) -/

/-- The interpretation of dimension 2 in the proof of Theorem 4.1 of Yolcu–Aaronson–Heule (pp. 23–24, `SN(W')`, `W' = {f. → 0.} ∪ X`). The proof shows the reversed problem
`SN({.f → .0} / X^rev)`. Matrices and constant terms as printed (`/` = `◁`, `.` = `▷`; `I41` of an internal review of the statement). -/
def I41 : Letter → NAff 2
  | .f => ⟨!![1, 0; 0, 1], ![1, 1]⟩
  | .t => ⟨!![1, 0; 0, 0], ![1, 0]⟩
  | .lft => ⟨!![1, 0; 0, 0], ![0, 0]⟩
  | .rgt => ⟨!![1, 2; 0, 0], ![0, 0]⟩
  | .d0 => ⟨!![1, 0; 0, 1], ![2, 0]⟩
  | .d1 => ⟨!![1, 0; 1, 0], ![2, 2]⟩
  | .d2 => ⟨!![1, 0; 1, 0], ![2, 2]⟩

/-- An affine map of dimension 2 as the list `[M₀₀, M₀₁, M₁₀, M₁₁, v₀, v₁]`. -/
def affL (F : NAff 2) : List ℕ := [F.M 0 0, F.M 0 1, F.M 1 0, F.M 1 1, F.v 0, F.v 1]

/-- **The 20 composed values printed in Theorem 4.1 of Yolcu–Aaronson–Heule** (both sides of the 10 rules of `W'^rev`) are reproduced by `evN` (`[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]`).
A direct check that the interpretations of the reversed system of Yolcu–Aaronson–Heule themselves use the direction of `evN` (the forward check is `yah_ex43_values` of `NonVacuity.lean`,
Example 4.3 of Yolcu–Aaronson–Heule). -/
theorem I41_printed :
    affL (evN I41 [rgt, f]) = [1, 2, 0, 0, 3, 0] ∧ affL (evN I41 [rgt, d0]) = [1, 2, 0, 0, 2, 0] ∧
    affL (evN I41 [d0, f]) = [1, 0, 0, 1, 3, 1] ∧ affL (evN I41 [f, d0]) = [1, 0, 0, 1, 3, 1] ∧
    affL (evN I41 [d1, f]) = [1, 0, 1, 0, 3, 3] ∧ affL (evN I41 [t, d0]) = [1, 0, 0, 0, 3, 0] ∧
    affL (evN I41 [d2, f]) = [1, 0, 1, 0, 3, 3] ∧ affL (evN I41 [f, d1]) = [1, 0, 1, 0, 3, 3] ∧
    affL (evN I41 [d0, t]) = [1, 0, 0, 0, 3, 0] ∧ affL (evN I41 [t, d1]) = [1, 0, 0, 0, 3, 0] ∧
    affL (evN I41 [d1, t]) = [1, 0, 1, 0, 3, 3] ∧ affL (evN I41 [f, d2]) = [1, 0, 1, 0, 3, 3] ∧
    affL (evN I41 [d2, t]) = [1, 0, 1, 0, 3, 3] ∧ affL (evN I41 [t, d2]) = [1, 0, 0, 0, 3, 0] ∧
    affL (evN I41 [d0, lft]) = [1, 0, 0, 0, 2, 0] ∧ affL (evN I41 [t, lft]) = [1, 0, 0, 0, 1, 0] ∧
    affL (evN I41 [d1, lft]) = [1, 0, 1, 0, 2, 2] ∧ affL (evN I41 [f, f, lft]) = [1, 0, 0, 0, 2, 2] ∧
    affL (evN I41 [d2, lft]) = [1, 0, 1, 0, 2, 2] ∧ affL (evN I41 [t, f, lft]) = [1, 0, 0, 0, 2, 0] := by
  decide +kernel

/-- With the opposite direction of composition (reading the reversed word with `evN`) the printed values are not obtained. -/
theorem I41_other_order_fails : (evN I41 [f, rgt]).v 0 ≠ 3 ∧ (evN I41 [lft, d1]).v 1 ≠ 2 := by decide +kernel

/-- The printed relations: extended monotone, strictly orients `▷f → ▷0` and `0◁ → t◁`, and weakly orients the rest of `X^rev`. -/
theorem I41_rel : NMono I41 ∧ NStrict I41 ⟨[rgt, f], [rgt, d0]⟩ ∧ NStrict I41 ⟨[d0, lft], [t, lft]⟩ ∧
    ∀ ρ ∈ rulesSTrev.drop 2, NWeak I41 ρ :=
  ⟨fun s => by cases s <;> decide, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The same interpretation does not weakly orient the forward `X` under `evN`. -/
theorem I41_forward_fails : ¬ ∀ ρ ∈ rulesST.drop 2, NWeak I41 ρ := by decide +kernel

/-- **The pair of checks of printed values of Yolcu–Aaronson–Heule**: both the forward Example 4.3 ($\mathcal T$ without `f1 → 0t`) and the reversed Theorem 4.1 (`{.f → .0} / X^rev`) are
reproduced by the same `evN`. -/
theorem yah_printed_both :
    ((evN IYAH [f, rgt]).M = !![2, 0; 1, 0] ∧ (evN IYAH [f, rgt]).v = ![2, 1]) ∧
    affL (evN I41 [rgt, f]) = [1, 2, 0, 0, 3, 0] :=
  ⟨yah_ex43_values.1, I41_printed.1⟩

/-! ## §7 The subclass of condition (U) follows from the frozen statement (not treated in the paper) -/

variable {d : ℕ}

/-- Condition (U): `(M_s)₀₀ = 1` and `(M_s)_{j0} = 0` (`j ≠ 0`) for all letters. -/
def CondU [NeZero d] (I : Letter → NAff d) : Prop := ∀ s, (I s).M 0 0 = 1 ∧ ∀ j : Fin d, j ≠ 0 → (I s).M j 0 = 0

/-- The exchange `P` of index 0 (`some 0`) and the homogeneous index (`none`). -/
def swap0 (d : ℕ) [NeZero d] : Option (Fin d) ≃ Option (Fin d) := Equiv.swap (some 0) none

/-- The family `N''_s := P N_s^T P`. -/
def uFam [NeZero d] (I : Letter → NAff d) : Letter → Matrix (Option (Fin d)) (Option (Fin d)) ℕ :=
  fun s => (transFam I s).submatrix (swap0 d) (swap0 d)

/-- Under (U) the homogeneous index of `N''` is a sink (row `none` is `e_none^T`). -/
theorem uFam_sink [NeZero d] {I : Letter → NAff d} (hU : CondU I) (x : Letter) (q : Option (Fin d)) :
    uFam I x none q = if q = none then 1 else 0 := by
  have hn : swap0 d none = some 0 := Equiv.swap_apply_right _ _
  have h0 : swap0 d (some 0) = none := Equiv.swap_apply_left _ _
  show homN (I x) (swap0 d q) (swap0 d none) = _
  rw [hn]
  rcases q with _ | j
  · rw [hn]; simpa using (hU x).1
  · by_cases hj : j = 0
    · subst hj; rw [h0]; simp
    · have hs : swap0 d (some j) = some j :=
        Equiv.swap_apply_of_ne_of_ne (by simpa using hj) (by simp)
      rw [hs]
      simpa using (hU x).2 j hj

/-- The forward interpretation (the affine form of `N''`). -/
def uInterp [NeZero d] (I : Letter → NAff d) : Letter → NAff d := ofHom (Equiv.refl (Fin d)) (uFam I)

theorem gweak_uFam_iff [NeZero d] (I : Letter → NAff d) (ρ : Rule) : GWeak (uFam I) ρ ↔ GWeak (transFam I) ρ := by
  unfold GWeak
  rw [show uFam I = fun s => (transFam I s).submatrix (swap0 d) (swap0 d) from rfl, NW_submatrix, NW_submatrix]
  simp only [Matrix.submatrix_apply]
  constructor
  · intro h p q
    have := h ((swap0 d).symm p) ((swap0 d).symm q)
    simpa using this
  · intro h p q
    exact h _ _

theorem uInterp_mono [NeZero d] (I : Letter → NAff d) : NMono (uInterp I) := by
  intro s
  show 1 ≤ homN (I s) (swap0 d (some 0)) (swap0 d (some 0))
  rw [show swap0 d (some 0) = none from Equiv.swap_apply_left _ _]
  simp

/-- The value of `uInterp` is `Φ^rev`: `Φ''(w) = (N'_w)_{d0} = Φ(w^rev)`. -/
theorem phiN_uInterp [NeZero d] {I : Letter → NAff d} (hU : CondU I) (w : Word) :
    PhiN (uInterp I) w = PhiN I w.reverse := by
  have hn : swap0 d none = some 0 := Equiv.swap_apply_right _ _
  have h0 : swap0 d (some 0) = none := Equiv.swap_apply_left _ _
  rw [phiN_reverse_eq_transFam]
  unfold uInterp
  rw [phiN_ofHom _ _ (uFam_sink hU)]
  unfold uFam
  rw [NW_submatrix]
  simp only [Matrix.submatrix_apply, Equiv.refl_apply]
  rw [h0, hn]

theorem nweak_uInterp_iff [NeZero d] {I : Letter → NAff d} (hU : CondU I) (ρ : Rule) :
    NWeak (uInterp I) ρ ↔ NWeak I (ruleRev ρ) := by
  unfold uInterp
  rw [nweak_ofHom_iff _ _ (uFam_sink hU), gweak_uFam_iff, nweak_rev_iff_transpose]

theorem nstrict_uInterp_iff [NeZero d] {I : Letter → NAff d} (hU : CondU I) (ρ : Rule) :
    NStrict (uInterp I) ρ ↔ NStrict I (ruleRev ρ) := by
  unfold NStrict
  rw [nweak_uInterp_iff hU, ← phiN_eq, ← phiN_eq, ← phiN_eq, ← phiN_eq, phiN_uInterp hU, phiN_uInterp hU]
  rfl

end W5

open W5

/-- **The subclass (U)**: for interpretations that satisfy condition (U), the conclusion of `NatBarrierSTrev` follows directly from the frozen forward statement `NatBarrierST`
(without the value-level core). -/
theorem natBarrierSTrevU_of_natBarrierST (h : NatBarrierST) :
    ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), CondU I → (∀ ρ ∈ rulesSTrev, NWeak I ρ) →
      ∀ ρ ∈ rulesSTrev, ¬ NStrict I ρ := by
  intro d _ I hU hweak ρ' hρ' hs
  obtain ⟨ρ, hρ, rfl⟩ := mem_rulesSTrev hρ'
  refine h d (uInterp I) (uInterp_mono I) (fun σ hσ => ?_) ρ hρ ((nstrict_uInterp_iff hU ρ).2 hs)
  exact (nweak_uInterp_iff hU σ).2 (hweak _ (ruleRev_mem_rulesSTrev hσ))

namespace W5

theorem IP3rev_condU : CondU IP3rev := by
  intro s
  cases s <;> decide +kernel

/-- `IP3rev` lies in the subclass (U), and its image under the transformation is `IP3` (the transformation of §7 goes back and forth between `IP3` and `IP3rev`). -/
theorem uInterp_IP3rev : ∀ s, (uInterp IP3rev s).M = (IP3 s).M ∧ (uInterp IP3rev s).v = (IP3 s).v := by
  intro s
  cases s <;> decide +kernel

/-! ## §8 Negative controls (claims that do not hold are decided false by `decide +kernel`) -/

theorem ctrl_IP3_not_weak_rev : ¬ ∀ ρ ∈ rulesSTrev, NWeak IP3 ρ := by decide +kernel

theorem ctrl_IP3rev_not_strict_Fdot : ¬ NStrict IP3rev ⟨[rgt, f], [rgt]⟩ := by decide +kernel

theorem ctrl_INoMonoRev_not_strict_top : ¬ ∃ ρ ∈ rulesSTrevTop, NStrict INoMonoRev ρ := by decide +kernel

theorem ctrl_IL315_not_weak_all : ¬ ∀ ρ ∈ rulesSTrev, NWeak IL315 ρ := by decide +kernel

theorem ctrl_INRev_not_strict_Fdot : ¬ NStrict INRev ⟨[rgt, f], [rgt]⟩ := by decide +kernel

end W5

end Collatz.Arctic.NatQ5
