/-
Names following the numbering of the paper (the arctic barrier), part 4: Proposition 9.5 of Section 9 (Proposition 10.1 of revision r2; the natural-number example, `NatExample.lean`, `NatExample2.lean`).
Imported by the root module `Paper.lean`.
-/
import CollatzProof.Arctic.NatExample2

namespace Collatz.Arctic.Paper

open Collatz.Arctic

/-- **Proposition 9.5** ($\mathcal T$, `r_in = 1`, `r_out = 0`). (i) The 11 rules are weakly oriented, the first components of `v` of the two sides
agree, no rule is strictly oriented, and `(M_s)₁₁ = 1`. (ii) The formula for the values; they do not increase along $T$. (iii) The residue component (entered from the left end at the index `2 + r_in`
and left through the index `2 + r_out` of `v_.`; the Lean indices start at 0). -/
theorem paper_prop_9_5_T :
    (∀ ρ ∈ rulesST, NatExample.NWeak NatExample.IT ρ) ∧
    (∀ ρ ∈ rulesST, (NatExample.evN NatExample.IT ρ.lhs).v 0 = (NatExample.evN NatExample.IT ρ.rhs).v 0) ∧
    (∀ ρ ∈ rulesST, ¬ NatExample.NStrict NatExample.IT ρ) ∧ (∀ s, (NatExample.IT s).M 0 0 = 1) ∧
    (∀ n, 1 ≤ n → NatExample.PhiN NatExample.IT (can n) =
      1 + if n % 3 = 0 then 2 ^ ((Nat.digits 2 n).length - 1) else 0) ∧
    (∀ n, 2 ≤ n → NatExample.PhiN NatExample.IT (can (T n)) ≤ NatExample.PhiN NatExample.IT (can n)) ∧
    NatExample.ResidueComponent NatExample.IT ∧ (NatExample.IT Letter.lft).M 0 (NatExample.resIdx 1) = 1 ∧
    (NatExample.IT Letter.rgt).v (NatExample.resIdx 0) = 1 :=
  NatExample.prop_10_1_T

/-- **Proposition 9.5** ($\mathcal H$, `r_in = 1`, `r_out = 1`; the values do not increase along $H$ at the points of the domain `HModel.HDom`). -/
theorem paper_prop_9_5_H :
    (∀ ρ ∈ HTPDB.rulesHT, NatExample.NWeak NatExample.IH ρ) ∧
    (∀ ρ ∈ HTPDB.rulesHT, (NatExample.evN NatExample.IH ρ.lhs).v 0 = (NatExample.evN NatExample.IH ρ.rhs).v 0) ∧
    (∀ ρ ∈ HTPDB.rulesHT, ¬ NatExample.NStrict NatExample.IH ρ) ∧ (∀ s, (NatExample.IH s).M 0 0 = 1) ∧
    (∀ n, 1 ≤ n → NatExample.PhiN NatExample.IH (can n) =
      1 + if n % 3 = 1 then 2 ^ ((Nat.digits 2 n).length - 1) else 0) ∧
    (∀ n, HModel.HDom n →
      NatExample.PhiN NatExample.IH (can (HModel.Hmap n)) ≤ NatExample.PhiN NatExample.IH (can n)) ∧
    NatExample.ResidueComponent NatExample.IH ∧ (NatExample.IH Letter.lft).M 0 (NatExample.resIdx 1) = 1 ∧
    (NatExample.IH Letter.rgt).v (NatExample.resIdx 1) = 1 :=
  NatExample.prop_10_1_H

/-- **Proposition 9.5** ($R_H$, 12 rules, `r_in = 0`, `r_out = 1`, `L` is `lft`). -/
theorem paper_prop_9_5_RH :
    (∀ ρ ∈ RH.rulesRH, NatExample.NWeak NatExample.IRH ρ) ∧
    (∀ ρ ∈ RH.rulesRH, (NatExample.evN NatExample.IRH ρ.lhs).v 0 = (NatExample.evN NatExample.IRH ρ.rhs).v 0) ∧
    (∀ ρ ∈ RH.rulesRH, ¬ NatExample.NStrict NatExample.IRH ρ) ∧ (∀ s, (NatExample.IRH s).M 0 0 = 1) ∧
    (∀ n, 1 ≤ n → NatExample.PhiN NatExample.IRH (RH.canRH n) =
      1 + if n % 3 = 1 then 2 ^ (Nat.digits 2 n).length else 0) ∧
    (∀ n, HModel.HDom n →
      NatExample.PhiN NatExample.IRH (RH.canRH (HModel.Hmap n)) ≤ NatExample.PhiN NatExample.IRH (RH.canRH n)) ∧
    NatExample.ResidueComponent NatExample.IRH ∧ (NatExample.IRH Letter.lft).M 0 (NatExample.resIdx 0) = 1 ∧
    (NatExample.IRH Letter.rgt).v (NatExample.resIdx 1) = 1 :=
  NatExample.prop_10_1_RH

/-- **The remark after Proposition 9.5** (the form of Paper I, unnumbered): with the start and end vectors `e₁ + e₂`, reading all
binary digits, including the leading one, gives `φ(n) = 1 + 2^{ℓ(n)}[3 ∣ n]`, and `φ(T n) ≤ φ(n)` for `n ≥ 2`. -/
theorem paper_prop_9_5_remark :
    (∀ n, 1 ≤ n → NatExample.phiI n = 1 + if n % 3 = 0 then 2 ^ (Nat.digits 2 n).length else 0) ∧
    (∀ n, 2 ≤ n → NatExample.phiI (T n) ≤ NatExample.phiI n) :=
  NatExample.prop_10_1_remark

end Collatz.Arctic.Paper
