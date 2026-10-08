/-
Canonical chains of dependency pairs (the canonical chains in the proof of Theorem 3.3 of the paper).

* For the system: `Canon.sweep_chain` transported to the string after `lft#`. With exactly the list of rules `canDeriv n`, a chain from `bin'(n) .`
  to `bin'(T n) .` (`dcanDeriv`). The left-end rules are steps of dependency pairs (`P_B`) at the root; the others (`D_T ∪ A`) are below the root.
* For the reversal: a chain from `rev(bin'(n)) /` to `rev(bin'(T n)) /` after `rgt#` (`dcanDeriv_rev`). The list of rules is
  `canDeriv n` reversed; the dynamic rules are steps of dependency pairs (`P_D^rev`) at the root, and `A^rev ∪ B^rev` are below the root.
* `pairsPB` and `pairsPDrev` are the `dp` of the root rules (`pairsPB_eq`, `pairsPDrev_eq`).
-/
import CollatzProof.Arctic.DPBridge

namespace Collatz.Arctic

open Matrix

/-! ### Canonical chains of dependency pairs -/

/-- The root rules for the system (the 3 left-end rules). With `dp lft` they become the dependency pairs of `P_B`. -/
def rootPB : List Rule := [leftRule 0, leftRule 1, leftRule 2]

/-- The root rules for the reversal (the reversed dynamic rules). With `dp rgt` they become the dependency pairs of `P_D^rev`. -/
def rootPDrev : List Rule :=
  [Rule.rev ⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩,
   Rule.rev ⟨[Letter.t, Letter.rgt], [Letter.d2, Letter.rgt]⟩]

lemma pairsPB_eq : pairsPB = rootPB.map (dp Letter.lft) := by decide

lemma pairsPDrev_eq : pairsPDrev = rootPDrev.map (dp Letter.rgt) := by decide

lemma DChain.root_single {U P : List Rule} {ρ : Rule} {u v : Word} (q : Word) (hρ : ρ ∈ P)
    (hu : u = ρ.lhs.tail ++ q) (hv : v = ρ.rhs.tail ++ q) : DChain U P [ρ] u v := by
  subst hu hv
  exact DChain.root q hρ (DChain.nil _)

lemma DChain.under_single {U P : List Rule} {ρ : Rule} {u v : Word} (hρ : ρ ∈ U)
    (h : Step ρ u v) : DChain U P [ρ] u v :=
  DChain.under hρ h (DChain.nil _)

lemma aRule_mem_usableST {b d : ℕ} (hb : b < 2) (hd : d ≤ 2) : aRule b d ∈ usableST := by
  interval_cases b <;> interval_cases d <;> decide

lemma aRule_rev_mem_usableSTrev {b d : ℕ} (hb : b < 2) (hd : d ≤ 2) :
    (aRule b d).rev ∈ usableSTrev := by
  interval_cases b <;> interval_cases d <;> decide

lemma leftRule_rev_mem_usableSTrev {d : ℕ} (hd : d ≤ 2) : (leftRule d).rev ∈ usableSTrev := by
  interval_cases d <;> decide

/-- The sweep (for the system, as a chain of dependency pairs): for `y ≥ 1` and `d ≤ 2`, `bin'(y) d R →* bin'(3y + d) R`
(`Canon.sweep_chain` transported to the string after `lft#`; the left-end rule is a step of a dependency pair at the root). -/
theorem dsweep : ∀ y : ℕ, 1 ≤ y → ∀ d : ℕ, d ≤ 2 → ∀ R : Word,
    DChain usableST rootPB (sweepRules (tailBitsLSB y) d) (binTail y ++ digL d :: R)
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
      · exact DChain.root_single R (by decide) (by simp [leftRule, digL])
          (by simp [leftRule, binTail_three])
      · exact DChain.root_single R (by decide) (by simp [leftRule, digL])
          (by simp [leftRule, binTail_four])
      · exact DChain.root_single R (by decide) (by simp [leftRule, digL])
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
      refine DChain.under (w := binTail y' ++ digL d' :: bitL b' :: R)
        (aRule_mem_usableST hb2 hd) ?_ ?_
      · refine ⟨binTail y', R, ?_, ?_⟩ <;> simp [aRule, hd', hb']
      · have h3 : 3 * (2 * y' + b) + d = 2 * (3 * y' + d') + b' := by omega
        rw [h3, binTail_two_mul_add (3 * y' + d') b' (by omega) hb'2]
        have := ih y' hlt hy'1 d' hd'2 (bitL b' :: R)
        simpa [List.append_assoc] using this

/-- The canonical chain of dependency pairs (for the system): for `n ≥ 2` the list of rules `canDeriv n` is a chain from `bin'(n) .` to `bin'(T n) .`. -/
theorem dcanDeriv (n : ℕ) (hn : 2 ≤ n) :
    DChain usableST rootPB (canDeriv n) (binTail n ++ [Letter.rgt])
      (binTail (T n) ++ [Letter.rgt]) := by
  set y := n / 2 with hy
  have hy1 : 1 ≤ y := by omega
  unfold canDeriv T
  by_cases hev : n % 2 = 0
  · have hn2 : n = 2 * y + 0 := by omega
    simp only [hev, ↓reduceIte]
    rw [hn2, binTail_two_mul_add y 0 hy1 (by norm_num)]
    have : (2 * y + 0) / 2 = y := by omega
    rw [this]
    refine DChain.under_single (by decide) ⟨binTail y, [], ?_, ?_⟩ <;> simp [bitL]
  · have hn2 : n = 2 * y + 1 := by omega
    simp only [hev, ↓reduceIte]
    have hsub : (n - 1) / 2 = y := by omega
    rw [hsub]
    have hT : (3 * n + 1) / 2 = 3 * y + 2 := by omega
    rw [hT, hn2, binTail_two_mul_add y 1 hy1 (by norm_num)]
    refine DChain.under (w := binTail y ++ digL 2 :: [Letter.rgt]) (by decide) ?_ ?_
    · refine ⟨binTail y, [], ?_, ?_⟩ <;> simp [bitL, digL]
    · exact dsweep y hy1 2 (le_refl 2) [Letter.rgt]

/-- The sweep (for the reversal, as a chain of dependency pairs): `P d rev(bin'(y)) / →* P rev(bin'(3y + d)) /` (all steps below the root). -/
theorem dsweep_rev : ∀ y : ℕ, 1 ≤ y → ∀ d : ℕ, d ≤ 2 → ∀ P : Word,
    DChain usableSTrev rootPDrev ((sweepRules (tailBitsLSB y) d).map Rule.rev)
      (P ++ digL d :: ((binTail y).reverse ++ [Letter.lft]))
      (P ++ ((binTail (3 * y + d)).reverse ++ [Letter.lft])) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy d hd P
    by_cases h1 : y = 1
    · subst h1
      rw [tailBitsLSB_one, binTail_one]
      simp only [sweepRules, List.map_cons, List.map_nil]
      refine DChain.under_single (leftRule_rev_mem_usableSTrev hd) ⟨P, [], ?_, ?_⟩
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
      refine DChain.under (w := P ++ bitL b' :: digL d' :: ((binTail y').reverse ++ [Letter.lft]))
        (aRule_rev_mem_usableSTrev hb2 hd) ?_ ?_
      · refine ⟨P, (binTail y').reverse ++ [Letter.lft], ?_, ?_⟩ <;>
          simp [aRule, Rule.rev, hd', hb']
      · have h3 : 3 * (2 * y' + b) + d = 2 * (3 * y' + d') + b' := by omega
        rw [h3, binTail_two_mul_add (3 * y' + d') b' (by omega) hb'2]
        have := ih y' hlt hy'1 d' hd'2 (P ++ [bitL b'])
        simpa [List.append_assoc] using this

/-- The canonical chain of dependency pairs (for the reversal): for `n ≥ 2` the reversed list of rules of `canDeriv n` is a chain
from `rev(bin'(n)) /` to `rev(bin'(T n)) /` (the dynamic rules are steps of dependency pairs at the root). -/
theorem dcanDeriv_rev (n : ℕ) (hn : 2 ≤ n) :
    DChain usableSTrev rootPDrev ((canDeriv n).map Rule.rev)
      ((binTail n).reverse ++ [Letter.lft]) ((binTail (T n)).reverse ++ [Letter.lft]) := by
  set y := n / 2 with hy
  have hy1 : 1 ≤ y := by omega
  unfold canDeriv T
  by_cases hev : n % 2 = 0
  · have hn2 : n = 2 * y + 0 := by omega
    simp only [hev, ↓reduceIte, List.map_cons, List.map_nil]
    rw [hn2, binTail_two_mul_add y 0 hy1 (by norm_num)]
    have : (2 * y + 0) / 2 = y := by omega
    rw [this]
    exact DChain.root_single ((binTail y).reverse ++ [Letter.lft]) (by decide)
      (by simp [Rule.rev, bitL]) (by simp [Rule.rev])
  · have hn2 : n = 2 * y + 1 := by omega
    simp only [hev, ↓reduceIte, List.map_cons]
    have hsub : (n - 1) / 2 = y := by omega
    rw [hsub]
    have hT : (3 * n + 1) / 2 = 3 * y + 2 := by omega
    rw [hT, hn2, binTail_two_mul_add y 1 hy1 (by norm_num)]
    have hrest := dsweep_rev y hy1 2 (le_refl 2) []
    simp only [List.nil_append] at hrest
    have hu : (binTail y ++ [bitL 1]).reverse ++ [Letter.lft] =
        (Rule.rev ⟨[Letter.t, Letter.rgt], [Letter.d2, Letter.rgt]⟩).lhs.tail ++
          ((binTail y).reverse ++ [Letter.lft]) := by simp [Rule.rev, bitL]
    rw [hu]
    refine DChain.root _ (by decide) ?_
    simpa [Rule.rev, digL] using hrest

/-- The letters of `bin'(n)` are `f` or `t`. -/
lemma binTail_letters (n : ℕ) : ∀ s ∈ binTail n, s = Letter.f ∨ s = Letter.t := by
  intro s hs
  rw [binTail_eq] at hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
  unfold bitL
  split_ifs <;> simp

/-- The root rules of the reversal are the reversed dynamic rules. -/
lemma rootPDrev_mem {σ : Rule} (hσ : σ ∈ rootPDrev) : ∃ τ ∈ rulesST, σ = τ.rev := by
  simp only [rootPDrev, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl
  · exact ⟨_, by decide, rfl⟩
  · exact ⟨_, by decide, rfl⟩

/-- The number of occurrences in the reversed list of rules is the original number of uses. -/
lemma count_rev (τ : Rule) (n : ℕ) : ((canDeriv n).map Rule.rev).count τ.rev = uses τ n :=
  List.count_map_of_injective _ _ Rule.rev_injective _

end Collatz.Arctic
