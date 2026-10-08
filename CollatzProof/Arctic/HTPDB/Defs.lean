/-
The rules and canonical derivations of the system $\mathcal H$ (`SRS_Standard/Yolcu_21/collatz-T-5or7mod8` of the TPDB).
**The statements are frozen.**

* The letters are of the same type `Letter` as for the system $\mathcal T$ (`b0` = `f`, `b1` = `t`, `t0..t2` = `d0..d2`, `&` = `lft`, `$` = `rgt`).
  The unary term $s_1(s_2(\cdots(x)))$ is read as the string $s_1 s_2 \cdots$ (the same convention as in the transcription `rulesST`). The transcription is checked by
  the script `check_systems.py` of Appendix C (it compares the `.ari` file with the source of this file).
* 11 rules: 2 dynamic rules (`ff. → 0.`: $3n/4$ for $n \equiv 0 \bmod 4$; `ttt. → 22.`: for $n \equiv 7 \bmod 8$,
  $(9n+1)/8$), and the same 6 carry rules $A$ and 3 left-end rules as $\mathcal T$ (`rulesHT.drop 2 = rulesST.drop 2`).
* The canonical string is the same `can n` as for $\mathcal T$ (the leading 1 is absorbed into `lft`). The canonical derivation `canDerivH n` (Lemma 2.3 (ii)):
  one dynamic rule, then the ternary digits are moved to the left end, leftmost first (`Statement.sweepRules`). A step $\mathsf b$ creates two digits 2;
  the left digit crosses `bin'(m)` ($m = (n-7)/8$), then the right digit crosses `bin'(3m+2)`. Correctness,
  `can n →* can (Hmap n)` (when `HModel.HDom n`), is proved in `HTPDB/Canon.lean`.
-/
import CollatzProof.Arctic.Statement

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic

open Letter in
/-- The dynamic rule `ff. → 0.` (a step $\mathsf a$). -/
def ffRule : Rule := ⟨[f, f, rgt], [d0, rgt]⟩

open Letter in
/-- The dynamic rule `ttt. → 22.` (a step $\mathsf b$). -/
def tttRule : Rule := ⟨[t, t, t, rgt], [d2, d2, rgt]⟩

open Letter in
/-- The 11 rules of $\mathcal H$ (in the order of `collatz-T-5or7mod8.ari`). -/
def rulesHT : List Rule :=
  [ ⟨[f, f, rgt], [d0, rgt]⟩, ⟨[t, t, t, rgt], [d2, d2, rgt]⟩,          -- dynamic rules D_H
    ⟨[f, d0], [d0, f]⟩, ⟨[f, d1], [d0, t]⟩, ⟨[f, d2], [d1, f]⟩,       -- carry rules A
    ⟨[t, d0], [d1, t]⟩, ⟨[t, d1], [d2, f]⟩, ⟨[t, d2], [d2, t]⟩,
    ⟨[lft, d0], [lft, t]⟩, ⟨[lft, d1], [lft, f, f]⟩, ⟨[lft, d2], [lft, f, t]⟩ ]  -- left-end rules B

/-- The list of rules used by the canonical derivation `can n →* can (Hmap n)` (when `HModel.HDom n`). -/
def canDerivH (n : ℕ) : List Rule :=
  if n % 4 = 0 then ffRule :: sweepRules (tailBitsLSB (n / 4)) 0
  else if n % 8 = 7 then tttRule ::
      (sweepRules (tailBitsLSB ((n - 7) / 8)) 2 ++ sweepRules (tailBitsLSB (3 * ((n - 7) / 8) + 2)) 2)
  else []

/-! ## Checks -/

/-- The two named dynamic rules are the first 2 rules of `rulesHT`. -/
theorem rulesHT_take_two : rulesHT.take 2 = [ffRule, tttRule] := by decide

/-- The 6 carry rules $A$ and the 3 left-end rules are shared with $\mathcal T$ (this reduces their check to the frozen transcription of $\mathcal T$). -/
theorem rulesHT_drop_two : rulesHT.drop 2 = rulesST.drop 2 := by decide

theorem rulesHT_length : rulesHT.length = 11 := by decide

/-- A small example: from `can 12 = /tff.`, the rules `ff. → 0.`, `t0 → 1t`, `/1 → /ff` give `can 9 = /fft.`. -/
example : canDerivH 12 = [ffRule, aRule 1 0, leftRule 1] := by decide

/-- A small example: from `can 15 = /ttt.`, the rules `ttt. → 22.`, `/2 → /ft` (`m = 1`), `t2 → 2t`, `f2 → 1f`, `/1 → /ff`
(`3m + 2 = 5`) give `can 17 = /ffft.`. -/
example : canDerivH 15 = [tttRule, leftRule 2, aRule 1 2, aRule 0 2, leftRule 1] := by decide

/-- Classification of the rules (carry rules $A$, the 2 dynamic rules, left-end rules). -/
theorem rulesHT_cases (ρ : Rule) (h : ρ ∈ rulesHT) :
    (∃ b d, b < 2 ∧ d ≤ 2 ∧ ρ = aRule b d) ∨ ρ = ffRule ∨ ρ = tttRule ∨ ∃ d ≤ 2, ρ = leftRule d := by
  simp only [rulesHT, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl ⟨0, 0, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨0, 1, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨0, 2, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 0, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 1, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 2, by norm_num, by norm_num, by decide⟩
  · exact Or.inr (Or.inr (Or.inr ⟨0, by norm_num, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨1, by norm_num, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨2, by norm_num, by decide⟩))

end Collatz.Arctic.HTPDB
