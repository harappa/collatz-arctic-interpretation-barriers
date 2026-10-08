/-
Rules and canonical derivations of the 12-rule system $R_H$ of Section 6 of Paper II
(this paper: Table 3 in Section 2.3, and Lemma 2.3(iii) in Section 2.4).

* The symbols are those of type `Letter`, as for $\mathcal T$ and $\mathcal H$: `L` = `lft`, `.` = `rgt`, `f`, `t` = binary 0, 1,
  `0`, `1`, `2` = `d0`, `d1`, `d2`. Strings are written from left to right as in Paper II. The transcription is checked by a script
  of Appendix C (`computations/check_systems.py`), which compares the rule list of this file with that of Paper II.
* The 12 rules (in the order of Paper II): the six carry rules `bd → d'b'` (`aRule b d`, as for $\mathcal T$), the four left-end rules
  `L0 → L`, `L1 → Lt`, `L2 → Ltf`, `Lf → L`, and the two dynamic rules (`ffRule`, `tttRule`, as for $\mathcal H$).
* The canonical string `canRH n = L t bin'(n) .` (for all `n`) **contains the leading one as the symbol `t`** (for $\mathcal T$ and $\mathcal H$,
  `can n = / bin'(n) .` absorbs the leading one into `/`). For `n ≥ 1` it equals `L bin(n) .` (`canRH_eq_bin`).
* The canonical derivation `canDerivRH n` proceeds in the same order as `HTPDB.canDerivH n` (one dynamic rule, then the ternary digits are moved to the left end, the leftmost first).
  A digit also crosses the leading `t`, by the carry rule `aRule 1 d` (the digit after crossing is `(3 + d)/2 ∈ {1, 2}`), and at the left end it uses `L1 → Lt` or
  `L2 → Ltf`. The left-end rule `/d → /bin'(3 + d)` of $\mathcal H$ thus becomes the two steps `aRule 1 d` and
  `leftRuleRH ((3 + d)/2)`. The rules `L0 → L` and `Lf → L` are not used (the remark after Lemma 2.3).
  Correctness, `canRH n →* canRH (Hmap n)` when `HModel.HDom n`, is proved in `RH/Canon.lean`. The formula for a $\mathsf b$-step uses `m = (n-7)/8 ≥ 1`
  (`n = 7` is outside `HDom`; `canRH 7 = Lttt.` has another derivation, which this formula does not give).
* **The used rules** `usedRH`: the 10 rules obtained from the 12 rules by removing `L0 → L` and `Lf → L` (the rules occurring in
  canonical derivations; $R_H^{\mathrm u}$ in Theorem 3.1(ii)).
-/
import CollatzProof.Arctic.HTPDB.Defs

namespace Collatz.Arctic.RH

open Collatz.Arctic HTPDB

open Letter in
/-- The left-end rule `L0 → L` (not used). -/
def l0Rule : Rule := ⟨[lft, d0], [lft]⟩

open Letter in
/-- The left-end rule `Lf → L` (not used). -/
def lfRule : Rule := ⟨[lft, f], [lft]⟩

open Letter in
/-- The left-end rules `L d → L bin(d)` of $R_H$ (`d = 0`: `L0 → L`, `1`: `L1 → Lt`, `2`: `L2 → Ltf`). -/
def leftRuleRH (d : ℕ) : Rule :=
  if d = 0 then ⟨[lft, d0], [lft]⟩
  else if d = 1 then ⟨[lft, d1], [lft, t]⟩
  else ⟨[lft, d2], [lft, t, f]⟩

open Letter in
/-- The 12 rules of $R_H$ (in the order of Paper II). -/
def rulesRH : List Rule :=
  [ ⟨[f, d0], [d0, f]⟩, ⟨[f, d1], [d0, t]⟩, ⟨[f, d2], [d1, f]⟩,        -- carry rules A (bd → d'b')
    ⟨[t, d0], [d1, t]⟩, ⟨[t, d1], [d2, f]⟩, ⟨[t, d2], [d2, t]⟩,
    ⟨[lft, d0], [lft]⟩, ⟨[lft, d1], [lft, t]⟩, ⟨[lft, d2], [lft, t, f]⟩,   -- left-end rules
    ⟨[lft, f], [lft]⟩,
    ⟨[f, f, rgt], [d0, rgt]⟩, ⟨[t, t, t, rgt], [d2, d2, rgt]⟩ ]          -- dynamic rules D_H

open Letter in
/-- **The used rules** (10 rules): `rulesRH` without `L0 → L` and `Lf → L` (in the same order). -/
def usedRH : List Rule :=
  [ ⟨[f, d0], [d0, f]⟩, ⟨[f, d1], [d0, t]⟩, ⟨[f, d2], [d1, f]⟩,
    ⟨[t, d0], [d1, t]⟩, ⟨[t, d1], [d2, f]⟩, ⟨[t, d2], [d2, t]⟩,
    ⟨[lft, d1], [lft, t]⟩, ⟨[lft, d2], [lft, t, f]⟩,
    ⟨[f, f, rgt], [d0, rgt]⟩, ⟨[t, t, t, rgt], [d2, d2, rgt]⟩ ]

/-- The canonical string `canRH n = L t bin'(n) .` (equal to `L bin(n) .` for `n ≥ 1`; it contains the leading one as the symbol `t`). -/
def canRH (n : ℕ) : Word := Letter.lft :: Letter.t :: (binTail n ++ [Letter.rgt])

/-- The list of rules used while a ternary digit `d` crosses the binary digits (listed from the least significant one, without the leading one), then crosses the leading `t`
(`aRule 1 d`), and finally uses `L ((3 + d')/2)` at the left end (the $R_H$ version of `Statement.sweepRules`). -/
def sweepRulesRH : List ℕ → ℕ → List Rule
  | [], d => [aRule 1 d, leftRuleRH ((3 + d) / 2)]
  | b :: bs, d => aRule b d :: sweepRulesRH bs ((3 * b + d) / 2)

/-- The list of rules used in the canonical derivation `canRH n →* canRH (Hmap n)` (when `HModel.HDom n`). -/
def canDerivRH (n : ℕ) : List Rule :=
  if n % 4 = 0 then ffRule :: sweepRulesRH (tailBitsLSB (n / 4)) 0
  else if n % 8 = 7 then tttRule ::
      (sweepRulesRH (tailBitsLSB ((n - 7) / 8)) 2 ++
        sweepRulesRH (tailBitsLSB (3 * ((n - 7) / 8) + 2)) 2)
  else []

/-! ## Checks -/

theorem rulesRH_length : rulesRH.length = 12 := by decide
theorem usedRH_length : usedRH.length = 10 := by decide

/-- The six carry rules are those of $\mathcal T$ (hence of $\mathcal H$). -/
theorem rulesRH_take_six : rulesRH.take 6 = (rulesST.drop 2).take 6 := by decide

/-- The six carry rules are `aRule b d` (`b < 2`, `d ≤ 2`). -/
theorem rulesRH_take_six_aRule :
    rulesRH.take 6 = [aRule 0 0, aRule 0 1, aRule 0 2, aRule 1 0, aRule 1 1, aRule 1 2] := by decide

/-- The four left-end rules. -/
theorem rulesRH_left : (rulesRH.drop 6).take 4 = [l0Rule, leftRuleRH 1, leftRuleRH 2, lfRule] := by decide

/-- The two dynamic rules are those of $\mathcal H$. -/
theorem rulesRH_drop_ten : rulesRH.drop 10 = [ffRule, tttRule] := by decide

theorem rulesRH_dyn_eq_HT : rulesRH.drop 10 = rulesHT.take 2 := by decide

theorem leftRuleRH_zero : leftRuleRH 0 = l0Rule := by decide

/-- `usedRH` is `rulesRH` without `L0 → L` and `Lf → L`. -/
theorem usedRH_eq_filter : usedRH = rulesRH.filter (fun ρ => ρ ≠ l0Rule ∧ ρ ≠ lfRule) := by decide

theorem usedRH_sub : ∀ ρ ∈ usedRH, ρ ∈ rulesRH := by decide

theorem l0Rule_not_used : l0Rule ∉ usedRH := by decide
theorem lfRule_not_used : lfRule ∉ usedRH := by decide

/-- The 12 rules are the 10 used rules together with `L0 → L` and `Lf → L`. -/
theorem rulesRH_cases' : ∀ ρ ∈ rulesRH, ρ ∈ usedRH ∨ ρ = l0Rule ∨ ρ = lfRule := by decide

/-- Classification of the used rules (carry rules, the two dynamic rules, `L1 → Lt`, `L2 → Ltf`). -/
theorem usedRH_cases (ρ : Rule) (h : ρ ∈ usedRH) :
    (∃ b d, b < 2 ∧ d ≤ 2 ∧ ρ = aRule b d) ∨ ρ = ffRule ∨ ρ = tttRule ∨
      ρ = leftRuleRH 1 ∨ ρ = leftRuleRH 2 := by
  simp only [usedRH, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨0, 0, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨0, 1, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨0, 2, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 0, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 1, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 2, by norm_num, by norm_num, by decide⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by decide))))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))

/-- The canonical string is `L bin(n) .` (`n ≥ 1`; `bin(n)` lists the binary digits including the leading one, most significant first). -/
theorem canRH_eq_bin (n : ℕ) (hn : 1 ≤ n) :
    canRH n = Letter.lft :: ((Nat.digits 2 n).reverse.map bitL ++ [Letter.rgt]) := by
  have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hlast : (Nat.digits 2 n).getLast hne = 1 := by
    have h1 := Nat.getLast_digit_ne_zero 2 (show n ≠ 0 by omega)
    have h2 : (Nat.digits 2 n).getLast hne < 2 :=
      Nat.digits_lt_base (by norm_num) (List.getLast_mem hne)
    omega
  have hsplit := List.dropLast_append_getLast hne
  rw [hlast] at hsplit
  have hrev : (Nat.digits 2 n).reverse = 1 :: (Nat.digits 2 n).dropLast.reverse := by
    conv_lhs => rw [← hsplit]
    simp
  unfold canRH binTail
  rw [hrev]
  simp [bitL]
  rfl

/-- A small example: `canRH 12 = Lttff.` (`12 = 1100₂`). -/
example : canRH 12 = [Letter.lft, Letter.t, Letter.t, Letter.f, Letter.f, Letter.rgt] := by decide

/-- A small example: from `Lttff.`, the rules `ff. → 0.`, `t0 → 1t`, `t1 → 2f`, `L2 → Ltf` give `Ltfft. = canRH 9`. -/
example : canDerivRH 12 = [ffRule, aRule 1 0, aRule 1 1, leftRuleRH 2] := by decide

/-- A small example: from `Ltfff.` (8), the rules `ff. → 0.`, `f0 → 0f`, `t0 → 1t`, `L1 → Lt` give `Lttf. = canRH 6`. -/
example : canDerivRH 8 = [ffRule, aRule 0 0, aRule 1 0, leftRuleRH 1] := by decide

/-- A small example: from `Ltttt.` (15, `m = 1`), `ttt. → 22.` gives `Lt22.`; the left 2 crosses `t` and `L2 → Ltf` gives
`Ltft2.` (`bin(5) = tft`); the right 2 crosses `tft` and `L2 → Ltf` gives `Ltffft. = canRH 17`. -/
example : canDerivRH 15 = [tttRule, aRule 1 2, leftRuleRH 2, aRule 1 2, aRule 0 2, aRule 1 1,
    leftRuleRH 2] := by decide

/-- The rules of canonical derivations are used rules (all small `n`; for general `n` see `RH/Canon.lean`). -/
example : ∀ n < 64, ∀ σ ∈ canDerivRH n, σ ∈ usedRH := by decide

/-- Each of the 10 used rules occurs in the canonical derivation of a small point of `HDom` (`8, 12, 15, 20`). -/
example : ∀ ρ ∈ usedRH, ρ ∈ canDerivRH 8 ∨ ρ ∈ canDerivRH 12 ∨ ρ ∈ canDerivRH 15 ∨
    ρ ∈ canDerivRH 20 := by decide

/-- The canonical derivations of the classes outside the domain (`n ≡ 1, 2, 3, 5, 6 mod 8`) are empty. -/
example : canDerivRH 9 = [] ∧ canDerivRH 10 = [] ∧ canDerivRH 11 = [] ∧ canDerivRH 13 = [] ∧
    canDerivRH 14 = [] := by decide

end Collatz.Arctic.RH
