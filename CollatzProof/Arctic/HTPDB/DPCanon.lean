/-
The canonical dependency pair chains of the system $\mathcal H$ (forward and reversed; used in the proofs of Theorems 3.3 and 3.4).

* Forward, `dcanDerivH`: if `HDom n`, the list of rules `canDerivH n` itself gives a dependency pair chain from `bin'(n) .` to `bin'(Hmap n) .`
  (after `lft#`). The left-end steps are root steps by pairs (`rootPB`, whose `dp lft` is `P_B`), once per step $\mathsf a$ and
  twice per step $\mathsf b$. The dynamic rules and the carry rules (`usableHT = D_H ∪ A`) act below the root. The sweeps are `Gen.dsweepG`; the two sweeps of a step $\mathsf b$
  are concatenated by `Gen.DChain.append`.
* Reversed, `dcanDerivH_rev`: a chain from `rev(bin'(n)) /` to `rev(bin'(Hmap n)) /` after `rgt#`. The list of rules is
  `canDerivH n` with every rule reversed (in the same order). The reversed dynamic rules are root steps by pairs (`rootPDrevH`, whose `dp rgt` is
  `pairsPDrevH`), once per step; `A^rev ∪ B^rev` (`usableHTrev`) acts below the root. In a step $\mathsf b$, after `.#ttt → .#22`,
  the right digit 2 (the one adjacent to the binary digits) crosses first, while the other 2 stays in the prefix `Q = [d2]`; it then crosses with `Q = []`
  (`Gen.dsweep_revG`).
* Adapted from `DPCanon.dcanDeriv`, `dcanDeriv_rev`, `rootPDrev_mem`, `count_rev` ($T$).
-/
import CollatzProof.Arctic.Gen.SysSweep
import CollatzProof.Arctic.HModel.Defs
import CollatzProof.Arctic.HTPDB.DPStatement

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel

private lemma aRule_mem_usableHT' {b d : ℕ} (hb : b < 2) (hd : d ≤ 2) : aRule b d ∈ usableHT := by
  interval_cases b <;> interval_cases d <;> decide

private lemma leftRule_mem_rootPB' {d : ℕ} (hd : d ≤ 2) : leftRule d ∈ rootPB := by
  interval_cases d <;> decide

private lemma aRule_rev_mem_usableHTrev' {b d : ℕ} (hb : b < 2) (hd : d ≤ 2) :
    (aRule b d).rev ∈ usableHTrev := by
  rw [usableHTrev_eq]; exact aRule_rev_mem_usableSTrev hb hd

private lemma leftRule_rev_mem_usableHTrev' {d : ℕ} (hd : d ≤ 2) : (leftRule d).rev ∈ usableHTrev := by
  rw [usableHTrev_eq]; exact leftRule_rev_mem_usableSTrev hd

/-- **Canonical dependency pair chain (forward, $H$)**: if `HDom n`, then `bin'(n) . →* bin'(Hmap n) .`. -/
theorem dcanDerivH (n : ℕ) (hn : HDom n) :
    DChain usableHT rootPB (canDerivH n) (binTail n ++ [Letter.rgt])
      (binTail (Hmap n) ++ [Letter.rgt]) := by
  have hsw := Gen.dsweepG (U := usableHT) (P := rootPB)
    (fun _ _ hb hd => aRule_mem_usableHT' hb hd) (fun _ hd => leftRule_mem_rootPB' hd)
  obtain ⟨h8, hcls⟩ := hn
  unfold canDerivH Hmap
  by_cases h4 : n % 4 = 0
  · -- A step $\mathsf a$
    simp only [h4, ↓reduceIte]
    set y := n / 4 with hy
    have hy1 : 1 ≤ y := by omega
    have hn2 : n = 2 * (2 * y + 0) + 0 := by omega
    rw [hn2, binTail_two_mul_add (2 * y + 0) 0 (by omega) (by norm_num),
      binTail_two_mul_add y 0 hy1 (by norm_num)]
    refine DChain.under (w := binTail y ++ digL 0 :: [Letter.rgt]) (by decide) ?_ ?_
    · refine ⟨binTail y, [], ?_, ?_⟩ <;> simp [ffRule, bitL, digL]
    · have := hsw y hy1 0 (by norm_num) [Letter.rgt]
      simpa only [Nat.add_zero] using this
  · -- A step $\mathsf b$
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
    refine DChain.under (w := binTail m ++ digL 2 :: [Letter.d2, Letter.rgt]) (by decide) ?_ ?_
    · refine ⟨binTail m, [], ?_, ?_⟩ <;> simp [tttRule, bitL, digL]
    · refine Gen.DChain.append (hsw m hm1 2 le_rfl [Letter.d2, Letter.rgt]) ?_
      exact hsw (3 * m + 2) (by omega) 2 le_rfl [Letter.rgt]

/-- **Canonical dependency pair chain (reversed, $H$)**: if `HDom n`, then `rev(bin'(n)) / →* rev(bin'(Hmap n)) /`. -/
theorem dcanDerivH_rev (n : ℕ) (hn : HDom n) :
    DChain usableHTrev rootPDrevH ((canDerivH n).map Rule.rev)
      ((binTail n).reverse ++ [Letter.lft]) ((binTail (Hmap n)).reverse ++ [Letter.lft]) := by
  have hsw := Gen.dsweep_revG (U := usableHTrev) (P := rootPDrevH)
    (fun _ _ hb hd => aRule_rev_mem_usableHTrev' hb hd) (fun _ hd => leftRule_rev_mem_usableHTrev' hd)
  obtain ⟨h8, hcls⟩ := hn
  unfold canDerivH Hmap
  by_cases h4 : n % 4 = 0
  · -- A step $\mathsf a$: the root pair `.#ff → .#0`, then a sweep (no prefix)
    simp only [h4, ↓reduceIte, List.map_cons]
    set y := n / 4 with hy
    have hy1 : 1 ≤ y := by omega
    have hn2 : n = 2 * (2 * y + 0) + 0 := by omega
    rw [hn2, binTail_two_mul_add (2 * y + 0) 0 (by omega) (by norm_num),
      binTail_two_mul_add y 0 hy1 (by norm_num)]
    have hrest := hsw y hy1 0 (by norm_num) []
    simp only [List.nil_append, Nat.add_zero] at hrest
    have hu : (binTail y ++ [bitL 0] ++ [bitL 0]).reverse ++ [Letter.lft] =
        (Rule.rev ffRule).lhs.tail ++ ((binTail y).reverse ++ [Letter.lft]) := by
      simp [Rule.rev, ffRule, bitL]
    rw [hu]
    refine DChain.root _ (by decide) ?_
    exact hrest
  · -- A step $\mathsf b$: after the root pair `.#ttt → .#22`, the right 2 crosses leaving the prefix `[d2]`, then the left 2 crosses
    have h7 : n % 8 = 7 := by omega
    simp only [h4, h7, ↓reduceIte, List.map_cons, List.map_append]
    have hH : (9 * n + 1) / 8 = 3 * (3 * ((n - 7) / 8) + 2) + 2 := by omega
    rw [hH]
    set m := (n - 7) / 8 with hm
    have hm1 : 1 ≤ m := by omega
    have hn2 : n = 2 * (2 * (2 * m + 1) + 1) + 1 := by omega
    rw [hn2, binTail_two_mul_add (2 * (2 * m + 1) + 1) 1 (by omega) (by norm_num),
      binTail_two_mul_add (2 * m + 1) 1 (by omega) (by norm_num),
      binTail_two_mul_add m 1 hm1 (by norm_num)]
    have hr1 := hsw m hm1 2 le_rfl [Letter.d2]
    have hr2 := hsw (3 * m + 2) (by omega) 2 le_rfl []
    simp only [List.nil_append] at hr2
    have hu : (binTail m ++ [bitL 1] ++ [bitL 1] ++ [bitL 1]).reverse ++ [Letter.lft] =
        (Rule.rev tttRule).lhs.tail ++ ((binTail m).reverse ++ [Letter.lft]) := by
      simp [Rule.rev, tttRule, bitL]
    rw [hu]
    refine DChain.root _ (by decide) ?_
    exact Gen.DChain.append hr1 hr2

/-- The reversed root rules are the reversed dynamic rules. -/
theorem rootPDrevH_mem {σ : Rule} (hσ : σ ∈ rootPDrevH) : ∃ τ ∈ rulesHT, σ = τ.rev := by
  simp only [rootPDrevH, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl
  · exact ⟨_, by decide, rfl⟩
  · exact ⟨_, by decide, rfl⟩

/-- The number of occurrences in the reversed list of rules equals the number in the original list. -/
theorem count_revH (τ : Rule) (n : ℕ) :
    ((canDerivH n).map Rule.rev).count τ.rev = (canDerivH n).count τ :=
  List.count_map_of_injective _ _ Rule.rev_injective _

end Collatz.Arctic.HTPDB
