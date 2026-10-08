/-
The relation between the canonical derivations of $R_H$ and $\mathcal H$, and the comparison of numbers of uses (Lemma 7.4).
Proves **`specCountRH : SpecCountRH`** (the frozen statement in `RH/Spec.lean`).

* `liftRH`: replaces the left-end rule `/d → /bin'(3 + d)` (`leftRule d`) of $\mathcal H$ by the two steps of $R_H$
  `aRule 1 d` (crossing the leading `t`) and `leftRuleRH ((3 + d)/2)` (`L1 → Lt` or `L2 → Ltf`), and keeps the other rules.
* `canDerivRH_eq`: **`canDerivRH n = (canDerivH n).flatMap liftRH`** (for all `n`). It follows from the relation of sweeps
  `sweepRulesRH bs d = (sweepRules bs d).flatMap liftRH` (the lower digits are binary, `d ≤ 2`).
* `count_le_flatMap`: if `ρ' ∈ g ρ`, then `l.count ρ ≤ (l.flatMap g).count ρ'` for every list `l`. It is applied to
  `ff.`, `ttt.`, `aRule b d` (unchanged by `liftRH`) and to the pairs `/0 → /t` and `L1 → Lt`, `/1 → /ff` and `L2 → Ltf`.
  (In fact the number of uses of `L1` equals that of `/0`, and that of `L2` equals the sum of those of `/1` and `/2`; small `n` are checked in `RH/Check.lean` and
  by the Python script of Appendix C. The statement needs only the inequalities.)
-/
import CollatzProof.Arctic.RH.Spec
import CollatzProof.Arctic.Main

namespace Collatz.Arctic.RH

open Collatz.Arctic HModel HTPDB

/-- Lifting: sends a rule of a canonical derivation of $\mathcal H$ to a list of rules of $R_H$ (only the left-end rules `/d` become two steps). -/
def liftRH (σ : Rule) : List Rule :=
  if σ = leftRule 0 then [aRule 1 0, leftRuleRH 1]
  else if σ = leftRule 1 then [aRule 1 1, leftRuleRH 2]
  else if σ = leftRule 2 then [aRule 1 2, leftRuleRH 2]
  else [σ]

/-- The carry rules are unchanged by `liftRH` (their left-hand sides start with a binary digit, not with the `/` of the left-end rules). -/
lemma liftRH_aRule (b d : ℕ) : liftRH (aRule b d) = [aRule b d] := by
  have h : ∀ e, aRule b d ≠ leftRule e := by
    intro e h
    have := congrArg (fun ρ : Rule => ρ.lhs.head?) h
    simp only [aRule, leftRule] at this
    unfold bitL at this
    split_ifs at this <;> simp_all
  simp [liftRH, h]

lemma liftRH_ff : liftRH ffRule = [ffRule] := by decide
lemma liftRH_ttt : liftRH tttRule = [tttRule] := by decide

/-- Relation of sweeps: `sweepRulesRH bs d = (sweepRules bs d).flatMap liftRH` (the lower digits are binary, `d ≤ 2`). -/
lemma sweepRulesRH_eq : ∀ (bs : List ℕ) (d : ℕ), (∀ b ∈ bs, b < 2) → d ≤ 2 →
    sweepRulesRH bs d = (sweepRules bs d).flatMap liftRH
  | [], d, _, hd => by
    interval_cases d <;> decide
  | b :: bs, d, hbs, hd => by
    have hb : b < 2 := hbs b List.mem_cons_self
    simp only [sweepRulesRH, sweepRules, List.flatMap_cons, liftRH_aRule, List.singleton_append]
    congr 1
    exact sweepRulesRH_eq bs _ (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb')) (by omega)

/-- **Relation of the canonical derivations** (Lemma 7.4): `canDerivRH n = (canDerivH n).flatMap liftRH` (for all `n`). -/
theorem canDerivRH_eq (n : ℕ) : canDerivRH n = (canDerivH n).flatMap liftRH := by
  unfold canDerivRH canDerivH
  split_ifs
  · simp [List.flatMap_cons, liftRH_ff, sweepRulesRH_eq _ 0 (tailBitsLSB_lt _) (by norm_num)]
  · simp [List.flatMap_cons, List.flatMap_append, liftRH_ttt,
      sweepRulesRH_eq _ 2 (tailBitsLSB_lt _) le_rfl]
  · rfl

/-- If `ρ' ∈ g ρ`, then the number of occurrences of `ρ` in `l` is at most that of `ρ'` in `l.flatMap g`. -/
lemma count_le_flatMap {g : Rule → List Rule} {ρ ρ' : Rule} (h : ρ' ∈ g ρ) :
    ∀ l : List Rule, l.count ρ ≤ (l.flatMap g).count ρ'
  | [] => by simp
  | σ :: l => by
    rw [List.flatMap_cons, List.count_append, List.count_cons]
    have ih := count_le_flatMap h l
    by_cases hσ : σ = ρ
    · subst hσ
      have : 0 < (g σ).count ρ' := List.count_pos_iff.mpr h
      simp; omega
    · have : (σ == ρ) = false := by simpa using hσ
      simp [this]; omega

/-- **Output of this unit**: the frozen `SpecCountRH`. -/
theorem specCountRH : SpecCountRH where
  ff_le n := by rw [canDerivRH_eq]; exact count_le_flatMap (by decide) _
  ttt_le n := by rw [canDerivRH_eq]; exact count_le_flatMap (by decide) _
  aRule_le n b d _ _ := by
    rw [canDerivRH_eq]
    exact count_le_flatMap (by rw [liftRH_aRule]; exact List.mem_singleton_self _) _
  left1_le n := by rw [canDerivRH_eq]; exact count_le_flatMap (by decide) _
  left2_le n := by rw [canDerivRH_eq]; exact count_le_flatMap (by decide) _

end Collatz.Arctic.RH
