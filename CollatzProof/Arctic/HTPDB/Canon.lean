/-
Correctness of the canonical derivations of the system $\mathcal H$ (Lemma 2.3 (ii)).

* `canDerivH_chain`: if `HDom n` ($n \ge 8$ and $n \equiv 0 \bmod 4$ or $n \equiv 7 \bmod 8$), the list of rules `canDerivH n`
  is a derivation from `can n` to `can (Hmap n)`.
  - A step $\mathsf a$ ($n = 4y$, $y \ge 2$): `binTail n = binTail y ++ [f, f]`. After `ff. → 0.`, `Canon.sweep_chain y 0 [rgt]`
    gives `can (3y)`.
  - A step $\mathsf b$ ($n = 8m + 7$, $m \ge 1$): `binTail n = binTail m ++ [t, t, t]`. After `ttt. → 22.`, the left digit 2
    crosses `bin'(m)` by `sweep_chain m 2 [d2, rgt]`, and then the right digit 2 crosses, by `sweep_chain (3m+2) 2 [rgt]`,
    `bin'(3m+2)`. $3(3m+2) + 2 = 9m + 8 = (9n+1)/8$. The chains are concatenated by `Gen.Chain.append`.
  - Adapted from `Canon.canDeriv_chain` ($T$). $n = 7$ is outside `HDom` (`ttt.` does not apply to `can 7 = /tt.`).
* `canDerivH_sub`: every rule of a canonical derivation belongs to `rulesHT` (for all `n`; adapted from `Main.canDeriv_sub`).
-/
import CollatzProof.Arctic.Gen.SysBridge
import CollatzProof.Arctic.HModel.Defs
import CollatzProof.Arctic.HTPDB.Defs

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel

private lemma aRule_mem_rulesHT' {b d : ℕ} (hb : b < 2) (hd : d ≤ 2) : aRule b d ∈ rulesHT := by
  interval_cases b <;> interval_cases d <;> decide

private lemma leftRule_mem_rulesHT' (d : ℕ) : leftRule d ∈ rulesHT := by
  unfold leftRule
  split_ifs <;> decide

/-- Every rule used by a canonical derivation belongs to `rulesHT`. -/
theorem canDerivH_sub (n : ℕ) : ∀ σ ∈ canDerivH n, σ ∈ rulesHT := by
  have hsw : ∀ (bs : List ℕ) (d : ℕ), (∀ b ∈ bs, b < 2) → d ≤ 2 →
      ∀ σ ∈ sweepRules bs d, σ ∈ rulesHT :=
    Gen.sweepRules_memG (fun _ _ hb hd => aRule_mem_rulesHT' hb hd)
      (fun d _ => leftRule_mem_rulesHT' d)
  unfold canDerivH
  split_ifs
  · intro σ hσ
    simp only [List.mem_cons] at hσ
    rcases hσ with rfl | hσ
    · decide
    · exact hsw _ 0 (tailBitsLSB_lt _) (by norm_num) σ hσ
  · intro σ hσ
    simp only [List.mem_cons, List.mem_append] at hσ
    rcases hσ with rfl | hσ | hσ
    · decide
    · exact hsw _ 2 (tailBitsLSB_lt _) le_rfl σ hσ
    · exact hsw _ 2 (tailBitsLSB_lt _) le_rfl σ hσ
  · intro σ hσ
    simp at hσ

/-- **Correctness of the canonical derivations** ($H$): if `HDom n`, then `can n →* can (Hmap n)`. -/
theorem canDerivH_chain (n : ℕ) (hn : HDom n) : Chain (canDerivH n) (can n) (can (Hmap n)) := by
  obtain ⟨h8, hcls⟩ := hn
  unfold canDerivH Hmap can
  by_cases h4 : n % 4 = 0
  · -- A step $\mathsf a$: `ff. → 0.`, then a sweep
    simp only [h4, ↓reduceIte]
    set y := n / 4 with hy
    have hy1 : 1 ≤ y := by omega
    have hn2 : n = 2 * (2 * y + 0) + 0 := by omega
    rw [hn2, binTail_two_mul_add (2 * y + 0) 0 (by omega) (by norm_num),
      binTail_two_mul_add y 0 hy1 (by norm_num)]
    refine Chain.cons (w := Letter.lft :: (binTail y ++ digL 0 :: [Letter.rgt])) ?_ ?_
    · refine ⟨Letter.lft :: binTail y, [], ?_, ?_⟩ <;> simp [ffRule, bitL, digL]
    · have := sweep_chain y hy1 0 (by norm_num) [Letter.rgt]
      simpa only [Nat.add_zero] using this
  · -- A step $\mathsf b$: `ttt. → 22.`, then two sweeps
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
    refine Chain.cons (w := Letter.lft :: (binTail m ++ digL 2 :: [Letter.d2, Letter.rgt])) ?_ ?_
    · refine ⟨Letter.lft :: binTail m, [], ?_, ?_⟩ <;> simp [tttRule, bitL, digL]
    · refine Gen.Chain.append (sweep_chain m hm1 2 le_rfl [Letter.d2, Letter.rgt]) ?_
      exact sweep_chain (3 * m + 2) (by omega) 2 le_rfl [Letter.rgt]

end Collatz.Arctic.HTPDB
