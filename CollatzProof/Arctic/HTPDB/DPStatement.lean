/-
The statements of the main theorems in dependency pair form for the system $\mathcal H$ (the case $\mathcal H$ of Theorems 3.3 and 3.4).
**The statements are frozen.**

* The forward problem `(P_B, U)`: `P_B` consists of the same 3 marked left-end rules as for the system $\mathcal T$ (`DPStatement.pairsPB`), and
  `U = D_H ∪ A` (`usableHT`, the first 8 rules of `rulesHT`).
* The problem of the reversed system `(P_D^rev, A^rev ∪ B^rev)`: `P_D^rev = {.#ff → .#0, .#ttt → .#22}` (`pairsPDrevH`); the usable rules are
  the same `A^rev ∪ B^rev` as for $\mathcal T$ (`usableHTrev`, whose content is that of `usableSTrev`).
* The comparisons, somewhere finite, absolutely positive and the lists of letters (`lettersPB`, `lettersPDrev`) use the same definitions as the statements for $\mathcal T$
  (`DPStatement.lean`). The recomputation of the dependency pairs and the usable rules (dependency pairs as in Zantema 2005, usable rules as in Giesl–Thiemann–Schneider-Kamp–Falke 2006)
  is in `HTPDB/NonVacuity.lean`.
* Root rules (`rootPDrevH`): the rules of the root steps of the reversed canonical chains (the reversed dynamic rules). `pairsPDrevH` is their `dp rgt`.
-/
import CollatzProof.Arctic.HTPDB.Defs
import CollatzProof.Arctic.DPBridge

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic Letter DLetter

/-- The usable rules `U = D_H ∪ A` (the 2 dynamic rules and the 6 carry rules). -/
def usableHT : List Rule :=
  [ ⟨[f, f, rgt], [d0, rgt]⟩, ⟨[t, t, t, rgt], [d2, d2, rgt]⟩,
    ⟨[f, d0], [d0, f]⟩, ⟨[f, d1], [d0, t]⟩, ⟨[f, d2], [d1, f]⟩,
    ⟨[t, d0], [d1, t]⟩, ⟨[t, d1], [d2, f]⟩, ⟨[t, d2], [d2, t]⟩ ]

/-- The essential SCC `P_D^rev` of the reversed system (the marked dynamic rules `.#ff → .#0`, `.#ttt → .#22`). -/
def pairsPDrevH : List DRule :=
  [ ⟨[mark rgt, plain f, plain f], [mark rgt, plain d0]⟩,
    ⟨[mark rgt, plain t, plain t, plain t], [mark rgt, plain d2, plain d2]⟩ ]

/-- The usable rules `A^rev ∪ B^rev` of the reversed system (the carry rules and the left-end rules with both sides reversed). -/
def usableHTrev : List Rule :=
  [ ⟨[d0, f], [f, d0]⟩, ⟨[d1, f], [t, d0]⟩, ⟨[d2, f], [f, d1]⟩,
    ⟨[d0, t], [t, d1]⟩, ⟨[d1, t], [f, d2]⟩, ⟨[d2, t], [t, d2]⟩,
    ⟨[d0, lft], [t, lft]⟩, ⟨[d1, lft], [f, f, lft]⟩, ⟨[d2, lft], [t, f, lft]⟩ ]

/-- The reversed root rules (the reversed dynamic rules); `dp rgt` turns them into `pairsPDrevH`. -/
def rootPDrevH : List Rule := [Rule.rev ffRule, Rule.rev tttRule]

/-- **Statement of Theorem 3.3 ($\mathcal H$, forward, `𝔸_ℕ`)**. -/
def ArcticBarrierHDP : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SomewhereFinite hd J lettersPB →
    (∀ ρ ∈ usableHT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Statement of Theorem 3.3 ($\mathcal H$, reversed, `𝔸_ℕ`)**. -/
def ArcticBarrierHDPrev : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SomewhereFinite hd J lettersPDrev →
    (∀ ρ ∈ usableHTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Statement of Theorem 3.4 ($\mathcal H$, forward, below zero `𝔸_ℤ`)**. -/
def ArcticBarrierHBZ : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J lettersPB →
    (∀ ρ ∈ usableHT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Statement of Theorem 3.4 ($\mathcal H$, reversed, below zero `𝔸_ℤ`)**. -/
def ArcticBarrierHBZrev : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J lettersPDrev →
    (∀ ρ ∈ usableHTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-! ## Checks -/

/-- `U` consists of the first 8 rules of `rulesHT`. -/
theorem usableHT_eq : usableHT = rulesHT.take 8 := by decide

/-- The reversed usable rules are the same as for $\mathcal T$. -/
theorem usableHTrev_eq : usableHTrev = usableSTrev := by decide

/-- `P_D^rev` is the `dp rgt` of the root rules. -/
theorem pairsPDrevH_eq : pairsPDrevH = rootPDrevH.map (dp Letter.rgt) := by decide

end Collatz.Arctic.HTPDB
