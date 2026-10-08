/-
Correctness of the canonical derivations of $R_H$ (Lemma 2.3 for $R_H$).
Proves **`specCanonRH : SpecCanonRH`** (the frozen statement in `RH/Spec.lean`).

* `sweep_chainRH`: for `y ≥ 1`, `d ≤ 2`, `L t bin'(y) d R →* L t bin'(3y + d) R`. Adapted from `Canon.sweep_chain` for $\mathcal T$
  (induction on `y = 2y' + b`, `3y + d = 2(3y' + d') + b'`). The differences: the prefix is `L t` (it contains the leading one as the symbol
  `t`), and the base case `y = 1` takes two steps: the digit `d` crosses the leading `t` by `aRule 1 d` (`t d → d' b'`,
  `3 + d = 2d' + b'`), then `L d' → L bin(d')` is applied at the left end (`leftRuleRH d'`, `d' = (3 + d)/2 ∈ {1, 2}`).
  The result `L bin(d') b'` is `L t bin'(3 + d)` (`3 + d ∈ {3, 4, 5}`).
* `canDerivRH_chain`: if `HDom n`, then `canRH n →* canRH (Hmap n)` (adapted from `canDerivH_chain` in `HTPDB/Canon.lean`).
  An $\mathsf a$-step (`n = 4y`) is `ff. → 0.` followed by one sweep; a $\mathsf b$-step (`n = 8m + 7`, `m ≥ 1`) is `ttt. → 22.` followed by
  two sweeps (the left 2 crosses `bin'(m)`, the right 2 crosses `bin'(3m + 2)`; joined by `Gen.Chain.append`).
* `canDerivRH_sub`: every rule of a canonical derivation is a used rule (for all `n`). The left-end rule at the end of a sweep is
  `leftRuleRH ((3 + d)/2)`, and `(3 + d)/2 ∈ {1, 2}` when `d ≤ 2` (`L0 → L` does not occur; `Lf → L` is not in the rule lists).
-/
import CollatzProof.Arctic.RH.Spec
import CollatzProof.Arctic.Gen.SysBridge

namespace Collatz.Arctic.RH

open Collatz.Arctic HModel HTPDB

/-- Sweep: for `y ≥ 1`, `d ≤ 2`, `L t bin'(y) d R →* L t bin'(3y + d) R`. -/
theorem sweep_chainRH : ∀ y : ℕ, 1 ≤ y → ∀ d : ℕ, d ≤ 2 → ∀ R : Word,
    Chain (sweepRulesRH (tailBitsLSB y) d) (Letter.lft :: Letter.t :: (binTail y ++ digL d :: R))
      (Letter.lft :: Letter.t :: (binTail (3 * y + d) ++ R)) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy d hd R
    by_cases h1 : y = 1
    · -- base case: cross the leading `t` by `aRule 1 d`, then `leftRuleRH ((3 + d)/2)` at the left end
      subst h1
      rw [tailBitsLSB_one, binTail_one]
      simp only [sweepRulesRH]
      refine Chain.cons (w := Letter.lft :: digL ((3 * 1 + d) / 2) :: bitL ((3 * 1 + d) % 2) :: R)
        ⟨[Letter.lft], R, by simp [aRule, bitL], by simp [aRule]⟩ (chain_single ?_)
      interval_cases d
      · exact ⟨[], Letter.t :: R, by simp [leftRuleRH, digL, bitL], by simp [leftRuleRH, binTail_three]⟩
      · exact ⟨[], Letter.f :: R, by simp [leftRuleRH, digL, bitL], by simp [leftRuleRH, binTail_four]⟩
      · exact ⟨[], Letter.t :: R, by simp [leftRuleRH, digL, bitL], by simp [leftRuleRH, binTail_five]⟩
    · -- y = 2y' + b, y' ≥ 1
      set y' := y / 2 with hy'
      set b := y % 2 with hb
      have hyy : y = 2 * y' + b := by omega
      have hy'1 : 1 ≤ y' := by omega
      have hb2 : b < 2 := by omega
      have hlt : y' < y := by omega
      set d' := (3 * b + d) / 2 with hd'
      set b' := (3 * b + d) % 2 with hb'
      have hd'2 : d' ≤ 2 := by omega
      have hb'2 : b' < 2 := by omega
      rw [hyy, tailBitsLSB_two_mul_add y' b hy'1 hb2, binTail_two_mul_add y' b hy'1 hb2]
      simp only [sweepRulesRH]
      refine Chain.cons (w := Letter.lft :: Letter.t :: (binTail y' ++ digL d' :: bitL b' :: R)) ?_ ?_
      · refine ⟨Letter.lft :: Letter.t :: binTail y', R, ?_, ?_⟩ <;> simp [aRule, hd', hb']
      · have h3 : 3 * (2 * y' + b) + d = 2 * (3 * y' + d') + b' := by omega
        rw [h3, binTail_two_mul_add (3 * y' + d') b' (by omega) hb'2]
        have := ih y' hlt hy'1 d' hd'2 (bitL b' :: R)
        simpa [List.append_assoc] using this

/-- **Correctness of the canonical derivations** ($R_H$): if `HDom n`, then `canRH n →* canRH (Hmap n)`. -/
theorem canDerivRH_chain (n : ℕ) (hn : HDom n) :
    Chain (canDerivRH n) (canRH n) (canRH (Hmap n)) := by
  obtain ⟨h8, hcls⟩ := hn
  unfold canDerivRH Hmap canRH
  by_cases h4 : n % 4 = 0
  · -- $\mathsf a$-step: `ff. → 0.` followed by a sweep
    simp only [h4, ↓reduceIte]
    set y := n / 4 with hy
    have hy1 : 1 ≤ y := by omega
    have hn2 : n = 2 * (2 * y + 0) + 0 := by omega
    rw [hn2, binTail_two_mul_add (2 * y + 0) 0 (by omega) (by norm_num),
      binTail_two_mul_add y 0 hy1 (by norm_num)]
    refine Chain.cons (w := Letter.lft :: Letter.t :: (binTail y ++ digL 0 :: [Letter.rgt])) ?_ ?_
    · refine ⟨Letter.lft :: Letter.t :: binTail y, [], ?_, ?_⟩ <;> simp [ffRule, bitL, digL]
    · have := sweep_chainRH y hy1 0 (by norm_num) [Letter.rgt]
      simpa only [Nat.add_zero] using this
  · -- $\mathsf b$-step: `ttt. → 22.` followed by two sweeps
    have h7 : n % 8 = 7 := by omega
    simp only [h4, h7, ↓reduceIte]
    have hH : (9 * n + 1) / 8 = 3 * (3 * ((n - 7) / 8) + 2) + 2 := by omega
    rw [hH]
    set m := (n - 7) / 8 with hm
    have hm1 : 1 ≤ m := by omega
    have hn2 : n = 2 * (2 * (2 * m + 1) + 1) + 1 := by omega
    rw [hn2, binTail_two_mul_add (2 * (2 * m + 1) + 1) 1 (by omega) (by norm_num),
      binTail_two_mul_add (2 * m + 1) 1 (by omega) (by norm_num),
      binTail_two_mul_add m 1 hm1 (by norm_num)]
    refine Chain.cons
      (w := Letter.lft :: Letter.t :: (binTail m ++ digL 2 :: [Letter.d2, Letter.rgt])) ?_ ?_
    · refine ⟨Letter.lft :: Letter.t :: binTail m, [], ?_, ?_⟩ <;> simp [tttRule, bitL, digL]
    · refine Gen.Chain.append (sweep_chainRH m hm1 2 le_rfl [Letter.d2, Letter.rgt]) ?_
      exact sweep_chainRH (3 * m + 2) (by omega) 2 le_rfl [Letter.rgt]

/-- The carry rules are used rules. -/
lemma aRule_mem_usedRH {b d : ℕ} (hb : b < 2) (hd : d ≤ 2) : aRule b d ∈ usedRH := by
  interval_cases b <;> interval_cases d <;> decide

/-- The rules of a sweep are used rules (the lower digits are binary, `d ≤ 2`). -/
lemma sweepRulesRH_mem : ∀ (bs : List ℕ) (d : ℕ), (∀ b ∈ bs, b < 2) → d ≤ 2 →
    ∀ σ ∈ sweepRulesRH bs d, σ ∈ usedRH
  | [], d, _, hd => by
    intro σ hσ
    simp only [sweepRulesRH, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact aRule_mem_usedRH (by norm_num) hd
    · interval_cases d <;> decide
  | b :: bs, d, hbs, hd => by
    intro σ hσ
    simp only [sweepRulesRH, List.mem_cons] at hσ
    have hb : b < 2 := hbs b List.mem_cons_self
    rcases hσ with rfl | hσ
    · exact aRule_mem_usedRH hb hd
    · exact sweepRulesRH_mem bs _ (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb')) (by omega) σ hσ

/-- Every rule used in a canonical derivation is a used rule (for all `n`). -/
theorem canDerivRH_sub (n : ℕ) : ∀ σ ∈ canDerivRH n, σ ∈ usedRH := by
  unfold canDerivRH
  split_ifs
  · intro σ hσ
    simp only [List.mem_cons] at hσ
    rcases hσ with rfl | hσ
    · decide
    · exact sweepRulesRH_mem _ 0 (tailBitsLSB_lt _) (by norm_num) σ hσ
  · intro σ hσ
    simp only [List.mem_cons, List.mem_append] at hσ
    rcases hσ with rfl | hσ | hσ
    · decide
    · exact sweepRulesRH_mem _ 2 (tailBitsLSB_lt _) le_rfl σ hσ
    · exact sweepRulesRH_mem _ 2 (tailBitsLSB_lt _) le_rfl σ hσ
  · intro σ hσ
    simp at hσ

/-- **Output of this unit**: the frozen `SpecCanonRH`. -/
theorem specCanonRH : SpecCanonRH := ⟨canDerivRH_chain, canDerivRH_sub⟩

end Collatz.Arctic.RH
