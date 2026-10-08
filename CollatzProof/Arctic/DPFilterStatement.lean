/-
Statements of the arctic barrier for dependency pairs with argument filters (the remark on argument filters after Theorem 3.4 of the paper).
The frozen statements (`DPStatement.lean`, `HTPDB/DPStatement.lean`) are not changed; these are separate definitions.

* The form of Giesl–Thiemann–Schneider-Kamp–Falke (JAR 37 (2006)): Definition 11 (argument filter `π`), Definition 20 (regarded positions),
  Definition 21 (usable rules with a filter, `U_R(P, π)`) and Theorem 26 (the reduction pair processor with a filter). In a string rewriting system
  the symbols are unary, and there are two cases: `π(s) = []` (the argument is dropped), or the argument is regarded (`[1]`, or the collapse `1`). The usable rules depend
  only on the set `F` of the symbols whose argument is dropped (in Definition 20 a collapse counts as regarding the argument).
* The reduction pair of Theorem 26 compares terms of the filtered signature `F_π`. Read on the original symbols, a symbol whose argument is dropped becomes a constant symbol, with
  `M_s = −∞` (all entries of the matrix are −∞, and `[s]` is the constant `c_s`), and a collapsed symbol is the identity (`M_s` is the identity matrix, `c_s = −∞`).
  The filter `π_Pol` induced by an interpretation (at the beginning of Section 7 of Giesl et al. 2006) and Theorem 47 there are read in the same way.
  - `𝔸_ℕ`: for a symbol whose argument is dropped, somewhere finiteness in the sense of Koprowski–Waldmann 2009 means that `c_s[1]` is finite; this is included in the somewhere finiteness of the frozen statements.
    The identity is somewhere finite as well. Hence `ArcticBarrierDPFilt`, `DPrevFilt`, `HDPFilt`, `HDPrevFilt` include collapsing filters.
  - below zero: the identity is not absolutely positive (`c_s[1] = −∞`). Hence the four statements, such as `ArcticBarrierBZFilt`, that require absolute positivity
    of all symbols do not include collapsing filters. The forms that include them are the `...FiltW` below (hypothesis `BZPos`: the marked symbol is
    absolutely positive, or all symbols of the problem satisfy `FirstNonneg`, that is, `M_s[1,1] ≥ 0` or `c_s[1] ≥ 0`). An interpretation of the filtered
    signature that is absolutely positive gives, read on the original symbols, `FirstNonneg` for every symbol (`c_s[1] ≥ 0` for a symbol whose argument is dropped, and a collapsed symbol is
    the identity, with `M_s[1,1] = 0`). The proofs are in `DPFilterBZ.lean`.
* The usable rules `U_R(P, π)` use the same definition `NatQ5.W5.usableFilt` as the natural-number case (`Nat/BridgeDPFilter.lean`; a combinatorial
  definition that does not depend on the interpretation). So the meaning of these statements depends on the definition in `Nat/BridgeDPFilter.lean` (the Lean bundle of the paper needs
  the 11 modules of `Arctic/Nat` in its `import` closure). Moving the definition to the arctic side was considered, but not done.
* The argument of the marked root of the right-hand sides of the dependency pairs is assumed to be regarded. If the argument of the marked symbol is dropped (`M_{h#} = −∞`), the usable rules are empty,
  and both sides of every dependency pair become the same constant, so that trivially no pair is strictly oriented (`markConst_not_strict_arc`, `_arcZ` in `DPFilter.lean`,
  `markConst_not_strict_bzpos` in `DPFilterBZ.lean`).
* The strength of the comparisons (coefficientwise for the usable rules, in the first row for the dependency pairs), somewhere finiteness, absolute positivity and the lists of symbols
  (`lettersPB`, `lettersPDrev`) are as in the frozen statements.
* The usable rules are computed from `rulesST` (forward) and `NatQ5.rulesSTrev` (reversed) for 𝒯, and from `HTPDB.rulesHT` and
  `HTPDB.NonVacuityH.rulesHTrev` for ℋ (each the full set of 11 rules). Without a filter (`F = []`) they
  agree with the frozen `usableST`, `usableSTrev`, `HTPDB.usableHT`, `HTPDB.usableHTrev` (the table in `DPFilter.lean`).
-/
import CollatzProof.Arctic.Nat.BridgeDPFilter
import CollatzProof.Arctic.HTPDB.NonVacuity

namespace Collatz.Arctic.DPFilter

open Collatz.Arctic Letter DLetter

/-! ## 𝒯 -/

/-- **Theorem 3.3 (𝒯, forward, `𝔸_ℕ`) with an argument filter** (the form of Theorem 26 of Giesl et al. 2006): for every argument filter `F` (the set of the symbols whose
argument is dropped; their matrices are −∞), an interpretation that weakly orients the filtered usable rules `U(P_B, π)` coefficientwise and `P_B` in the first row
strictly orients no pair of `P_B` in the first row. -/
def ArcticBarrierDPFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SomewhereFinite hd J lettersPB →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt rulesST pairsPB F, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Theorem 3.3 (𝒯, reversed, `𝔸_ℕ`) with an argument filter**. -/
def ArcticBarrierDPrevFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SomewhereFinite hd J lettersPDrev →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt NatQ5.rulesSTrev pairsPDrev F, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Theorem 3.4 (𝒯, forward, below zero `𝔸_ℤ`) with an argument filter**. -/
def ArcticBarrierBZFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J lettersPB →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt rulesST pairsPB F, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Theorem 3.4 (𝒯, reversed, below zero `𝔸_ℤ`) with an argument filter**. -/
def ArcticBarrierBZrevFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J lettersPDrev →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt NatQ5.rulesSTrev pairsPDrev F, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-! ## ℋ -/

/-- **Theorem 3.3 (ℋ, forward, `𝔸_ℕ`) with an argument filter**. -/
def ArcticBarrierHDPFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SomewhereFinite hd J lettersPB →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt HTPDB.rulesHT pairsPB F, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Theorem 3.3 (ℋ, reversed, `𝔸_ℕ`) with an argument filter**. -/
def ArcticBarrierHDPrevFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SomewhereFinite hd J lettersPDrev →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt HTPDB.NonVacuityH.rulesHTrev HTPDB.pairsPDrevH F,
      WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ HTPDB.pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Theorem 3.4 (ℋ, forward, below zero `𝔸_ℤ`) with an argument filter**. -/
def ArcticBarrierHBZFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J lettersPB →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt HTPDB.rulesHT pairsPB F, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Theorem 3.4 (ℋ, reversed, below zero `𝔸_ℤ`) with an argument filter**. -/
def ArcticBarrierHBZrevFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J lettersPDrev →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt HTPDB.NonVacuityH.rulesHTrev HTPDB.pairsPDrevH F,
      WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ HTPDB.pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-! ## Weaker hypotheses for below zero (forms that include collapsing filters; internal review) -/

/-- The condition that keeps the first component non-negative (the condition for arctic integers of Yolcu–Aaronson–Heule, Section 2.3.2; the remark after Theorem 3.4 of the paper): every symbol of `S` has
`M_s[1,1] ≥ 0` or `c_s[1] ≥ 0`. It is weaker than absolute positivity, and the identity (a collapsed symbol) satisfies it. -/
def FirstNonneg {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (S : List DLetter) : Prop :=
  ∀ s ∈ S, ArcZ.fin 0 ≤ (J s).M ⟨0, hd⟩ ⟨0, hd⟩ ∨ ArcZ.fin 0 ≤ (J s).c ⟨0, hd⟩

/-- The condition on the values for below zero: the marked symbol `h#` is absolutely positive (the hypothesis of `ArcticBarrierBZw` in `DPWeak.lean`), or
all symbols of the problem satisfy `FirstNonneg`. In both cases the value `V(w) = ([h# w](x*))₁` is non-negative. -/
def BZPos {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (h : Letter) (S : List DLetter) : Prop :=
  AbsPositive hd J [mark h] ∨ FirstNonneg hd J S

/-- **Theorem 3.4 (𝒯, forward, below zero) with an argument filter, under the weaker hypothesis `BZPos`** (collapsing filters included). -/
def ArcticBarrierBZFiltW : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), BZPos hd J lft lettersPB →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt rulesST pairsPB F, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Theorem 3.4 (𝒯, reversed, below zero) with an argument filter, under the weaker hypothesis `BZPos`**. -/
def ArcticBarrierBZrevFiltW : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), BZPos hd J rgt lettersPDrev →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt NatQ5.rulesSTrev pairsPDrev F, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Theorem 3.4 (ℋ, forward, below zero) with an argument filter, under the weaker hypothesis `BZPos`**. -/
def ArcticBarrierHBZFiltW : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), BZPos hd J lft lettersPB →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt HTPDB.rulesHT pairsPB F, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Theorem 3.4 (ℋ, reversed, below zero) with an argument filter, under the weaker hypothesis `BZPos`**. -/
def ArcticBarrierHBZrevFiltW : Prop :=
  ∀ (F : List Letter) (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), BZPos hd J rgt lettersPDrev →
    (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ NatQ5.W5.usableFilt HTPDB.NonVacuityH.rulesHTrev HTPDB.pairsPDrevH F,
      WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ HTPDB.pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

end Collatz.Arctic.DPFilter
