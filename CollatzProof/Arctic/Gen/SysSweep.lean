/-
General form of the sweeps in the canonical chains of dependency pairs.
Continuation of `Gen/SysBridge.lean` (split off because of the limit of 20 KB per file).

`DPCanon.dsweep` and `dsweep_rev` fix the usable rules and the root rules to `usableST`, `rootPB` (forward) and
`usableSTrev`, `rootPDrev` (reversed) of the system $\mathcal T$. Here `U` and `P` are arguments:
* forward `dsweepG`: assumes that the carry rules are in `U` and the left-end rules are in `P` (a left-end rule is a step of a dependency pair at the root).
* reversed `dsweep_revG`: assumes that the reversed carry rules and the reversed left-end rules are all in `U` (everything is below the root).
  The prefix part `Q` is arbitrary (in a step $\mathsf b$ of $H$, the other remaining digit 2 goes into `Q = [d2]`).
The proofs are the same as in the source (induction on `y = 2y' + b`).
-/
import CollatzProof.Arctic.Gen.SysBridge

namespace Collatz.Arctic.Gen

open Collatz.Arctic

/-- Sweep (forward, chain of dependency pairs): for `y ≥ 1`, `d ≤ 2`, `bin'(y) d R →* bin'(3y + d) R`
(the general form of `DPCanon.dsweep`; the left-end rule is a step of a dependency pair at the root). -/
theorem dsweepG {U P : List Rule} (hA : ∀ b d, b < 2 → d ≤ 2 → aRule b d ∈ U)
    (hL : ∀ d, d ≤ 2 → leftRule d ∈ P) :
    ∀ y : ℕ, 1 ≤ y → ∀ d : ℕ, d ≤ 2 → ∀ R : Word,
      DChain U P (sweepRules (tailBitsLSB y) d) (binTail y ++ digL d :: R)
        (binTail (3 * y + d) ++ R) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy d hd R
    by_cases h1 : y = 1
    · subst h1
      rw [tailBitsLSB_one, binTail_one]
      simp only [sweepRules]
      interval_cases d
      · exact DChain.root_single R (hL 0 (by norm_num)) (by simp [leftRule, digL])
          (by simp [leftRule, binTail_three])
      · exact DChain.root_single R (hL 1 (by norm_num)) (by simp [leftRule, digL])
          (by simp [leftRule, binTail_four])
      · exact DChain.root_single R (hL 2 (by norm_num)) (by simp [leftRule, digL])
          (by simp [leftRule, binTail_five])
    · set y' := y / 2 with hy'
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
      simp only [sweepRules]
      refine DChain.under (w := binTail y' ++ digL d' :: bitL b' :: R) (hA b d hb2 hd) ?_ ?_
      · refine ⟨binTail y', R, ?_, ?_⟩ <;> simp [aRule, hd', hb']
      · have h3 : 3 * (2 * y' + b) + d = 2 * (3 * y' + d') + b' := by omega
        rw [h3, binTail_two_mul_add (3 * y' + d') b' (by omega) hb'2]
        have := ih y' hlt hy'1 d' hd'2 (bitL b' :: R)
        simpa [List.append_assoc] using this

/-- Sweep (reversed, chain of dependency pairs): `Q d rev(bin'(y)) / →* Q rev(bin'(3y + d)) /` (everything below the root;
the general form of `DPCanon.dsweep_rev`). -/
theorem dsweep_revG {U P : List Rule} (hA : ∀ b d, b < 2 → d ≤ 2 → (aRule b d).rev ∈ U)
    (hL : ∀ d, d ≤ 2 → (leftRule d).rev ∈ U) :
    ∀ y : ℕ, 1 ≤ y → ∀ d : ℕ, d ≤ 2 → ∀ Q : Word,
      DChain U P ((sweepRules (tailBitsLSB y) d).map Rule.rev)
        (Q ++ digL d :: ((binTail y).reverse ++ [Letter.lft]))
        (Q ++ ((binTail (3 * y + d)).reverse ++ [Letter.lft])) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy d hd Q
    by_cases h1 : y = 1
    · subst h1
      rw [tailBitsLSB_one, binTail_one]
      simp only [sweepRules, List.map_cons, List.map_nil]
      refine DChain.under_single (hL d hd) ⟨Q, [], ?_, ?_⟩
      · interval_cases d <;> simp [leftRule, digL, Rule.rev]
      · interval_cases d <;> simp [leftRule, Rule.rev, binTail_three, binTail_four, binTail_five]
    · set y' := y / 2 with hy'
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
      simp only [sweepRules, List.map_cons]
      refine DChain.under (w := Q ++ bitL b' :: digL d' :: ((binTail y').reverse ++ [Letter.lft]))
        (hA b d hb2 hd) ?_ ?_
      · refine ⟨Q, (binTail y').reverse ++ [Letter.lft], ?_, ?_⟩ <;>
          simp [aRule, Rule.rev, hd', hb']
      · have h3 : 3 * (2 * y' + b) + d = 2 * (3 * y' + d') + b' := by omega
        rw [h3, binTail_two_mul_add (3 * y' + d') b' (by omega) hb'2]
        have := ih y' hlt hy'1 d' hd'2 (Q ++ [bitL b'])
        simpa [List.append_assoc] using this

end Collatz.Arctic.Gen
