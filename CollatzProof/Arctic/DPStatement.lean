/-
Statements of the main theorems in dependency pair form (the case of 𝒯 of Theorems 3.3 and 3.4 of the paper; the statements for ℋ are in
`HTPDB/DPStatement.lean`).
**The statements are frozen** (internal independent review).

* Arctic linear functions `x ↦ M ⊗ x ⊕ c` (Koprowski–Waldmann 2009, Definition 4.4), composition for strings, coefficientwise comparison (ibid., Definition 6.3 and Lemma 6.5).
* The dependency pair problem `(P_B, 𝒰)` (Section 2.3 of the paper): `P_B` consists of the 3 marked left-end rules, `𝒰 = D_T ∪ A` (8 rules).
  For the reversed system, the problem `(P_D^rev, A^rev ∪ B^rev)`.
* `ArcticBarrierDP` (Theorem 3.3, `𝔸_ℕ`, somewhere finite) and `ArcticBarrierBZ` (Theorem 3.4, `𝔸_ℤ`,
  absolutely positive), for the system and for its reversal.
* **Strength of the comparisons**: the rules of `𝒰` are all compared weakly and coefficientwise (`≥_λ` of Koprowski–Waldmann 2009). The pairs are compared **in the first row only**
  (both weakly and strictly). Since `≥_λ` and `≫_λ` of Koprowski–Waldmann 2009 (all rows) imply the first-row comparisons, the statements here are stronger than the forms with `≥_λ` and `≫_λ`
  (Theorems 7.1 and 8.3 there; see the remark on first-row comparison in Section 2.2). They also cover the form of tools that interpret marked letters by scalars (a row vector and a constant; AProVE)
  (an extension of the scope). This presumes that the tool imposes on the (row vector `v`, constant `c₀`) of a marked letter that `v_1` or `c₀`
  is finite (`c₀ ≥ 0` below zero); the condition in the implementations was not checked in the primary source (a remark of the review of the statements).
* Somewhere finiteness and absolute positivity are imposed on the letters occurring in the problem (`lettersPB`, `lettersPDrev`)
  (the interpretation of the other letters does not affect the values).
-/
import CollatzProof.Arctic.SemiringZ
import CollatzProof.Arctic.Statement

namespace Collatz.Arctic

open Matrix

/-- Arctic linear functions `x ↦ M ⊗ x ⊕ c` (Koprowski–Waldmann 2009, Definition 4.4; `c` is the absolute part). -/
structure AffFun (R : Type) (d : ℕ) where
  M : Matrix (Fin d) (Fin d) R
  c : Fin d → R

namespace AffFun

variable {R : Type} [CommSemiring R] {d : ℕ}

/-- The value `f(x) = M ⊗ x ⊕ c`. -/
def apply (f : AffFun R d) (x : Fin d → R) : Fin d → R := f.M *ᵥ x + f.c

/-- The composition `f ∘ g`: its coefficients are `f.M ⊗ g.M` and `f.M ⊗ g.c ⊕ f.c`. -/
def comp (f g : AffFun R d) : AffFun R d := ⟨f.M * g.M, f.M *ᵥ g.c + f.c⟩

/-- The identity (the identity matrix, absolute part −∞). -/
def id : AffFun R d := ⟨1, 0⟩

end AffFun

/-- Letters of dependency pair problems: marked letters `s^#` and unmarked letters. -/
inductive DLetter
  | mark (s : Letter)
  | plain (s : Letter)
  deriving DecidableEq, Repr

/-- Dependency pairs and rules (pairs of strings that may contain marked letters). -/
structure DRule where
  lhs : List DLetter
  rhs : List DLetter
  deriving DecidableEq, Repr

/-- An unmarked rule as a `DRule`. -/
def Rule.plain (ρ : Rule) : DRule := ⟨ρ.lhs.map DLetter.plain, ρ.rhs.map DLetter.plain⟩

/-- The interpretation of a string: the composition `[s_1] ∘ ⋯ ∘ [s_k]` of linear functions (the string `s_1 ⋯ s_k` is the term `s_1(⋯ s_k(x))`). -/
def evA {R : Type} [CommSemiring R] {d : ℕ} (J : DLetter → AffFun R d) (w : List DLetter) :
    AffFun R d :=
  w.foldr (fun s acc => (J s).comp acc) AffFun.id

/-- The coefficientwise weak comparison `f ≥_λ g` (Koprowski–Waldmann 2009, Definition 6.3 and Lemma 6.5). -/
def WeakA {R : Type} [LE R] {d : ℕ} (f g : AffFun R d) : Prop :=
  (∀ i j, g.M i j ≤ f.M i j) ∧ ∀ i, g.c i ≤ f.c i

/-- The weak comparison of the first row (index 0) only (implied by `f ≥_λ g`). -/
def WeakTop {R : Type} [LE R] {d : ℕ} (hd : 0 < d) (f g : AffFun R d) : Prop :=
  (∀ j, g.M ⟨0, hd⟩ j ≤ f.M ⟨0, hd⟩ j) ∧ g.c ⟨0, hd⟩ ≤ f.c ⟨0, hd⟩

/-- The arctic `a ≫ b`: `a > b`, or both are −∞ (Koprowski–Waldmann 2009, Section 4). -/
def GG {R : Type} [LT R] [Zero R] (a b : R) : Prop := b < a ∨ (a = 0 ∧ b = 0)

/-- The strict comparison of the first row only (implied by `f ≫_λ g` of Koprowski–Waldmann 2009). -/
def StrictTop {R : Type} [LT R] [Zero R] {d : ℕ} (hd : 0 < d) (f g : AffFun R d) : Prop :=
  (∀ j, GG (f.M ⟨0, hd⟩ j) (g.M ⟨0, hd⟩ j)) ∧ GG (f.c ⟨0, hd⟩) (g.c ⟨0, hd⟩)

/-- Somewhere finite (Koprowski–Waldmann 2009, Definition 6.1): for every letter of `S`, the first component of the absolute part or the (1,1) entry of the matrix is finite. -/
def SomewhereFinite {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun Arc d) (S : List DLetter) : Prop :=
  ∀ s ∈ S, (J s).c ⟨0, hd⟩ ≠ 0 ∨ (J s).M ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0

/-- Absolutely positive (Koprowski–Waldmann 2009, Definition 8.1): for every letter of `S`, the first component of the absolute part is at least 0 (in particular finite). -/
def AbsPositive {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (S : List DLetter) : Prop :=
  ∀ s ∈ S, ArcZ.fin 0 ≤ (J s).c ⟨0, hd⟩

open Letter DLetter

/-- The essential SCC `P_B` (the marked left-end rules `/#0 → /#t`, `/#1 → /#ff`, `/#2 → /#ft`). -/
def pairsPB : List DRule :=
  [ ⟨[mark lft, plain d0], [mark lft, plain t]⟩,
    ⟨[mark lft, plain d1], [mark lft, plain f, plain f]⟩,
    ⟨[mark lft, plain d2], [mark lft, plain f, plain t]⟩ ]

/-- The usable rules `𝒰 = D_T ∪ A` (the 2 dynamic rules and the 6 carry rules; the first 8 rules of `rulesST`). -/
def usableST : List Rule :=
  [ ⟨[f, rgt], [rgt]⟩, ⟨[t, rgt], [d2, rgt]⟩,
    ⟨[f, d0], [d0, f]⟩, ⟨[f, d1], [d0, t]⟩, ⟨[f, d2], [d1, f]⟩,
    ⟨[t, d0], [d1, t]⟩, ⟨[t, d1], [d2, f]⟩, ⟨[t, d2], [d2, t]⟩ ]

/-- The letters occurring in the problem of the system (not reversed). -/
def lettersPB : List DLetter :=
  [mark lft, plain f, plain t, plain d0, plain d1, plain d2, plain rgt]

/-- The essential SCC `P_D^rev` of the reversed system (the marked dynamic rules `.#f → .#`, `.#t → .#2`). -/
def pairsPDrev : List DRule :=
  [ ⟨[mark rgt, plain f], [mark rgt]⟩, ⟨[mark rgt, plain t], [mark rgt, plain d2]⟩ ]

/-- The usable rules `A^rev ∪ B^rev` of the reversed system (the carry rules and the left-end rules with both sides reversed). -/
def usableSTrev : List Rule :=
  [ ⟨[d0, f], [f, d0]⟩, ⟨[d1, f], [t, d0]⟩, ⟨[d2, f], [f, d1]⟩,
    ⟨[d0, t], [t, d1]⟩, ⟨[d1, t], [f, d2]⟩, ⟨[d2, t], [t, d2]⟩,
    ⟨[d0, lft], [t, lft]⟩, ⟨[d1, lft], [f, f, lft]⟩, ⟨[d2, lft], [t, f, lft]⟩ ]

/-- The letters occurring in the problem of the reversed system. -/
def lettersPDrev : List DLetter :=
  [mark rgt, plain f, plain t, plain d0, plain d1, plain d2, plain lft]

/-- **Statement of Theorem 3.3 (𝒯, `𝔸_ℕ`)**: an interpretation by arctic linear functions over `𝔸_ℕ` (of any dimension), somewhere finite on the letters
of the problem, that orients `𝒰` weakly and coefficientwise and `P_B` weakly in the first row orients no pair of `P_B`
strictly in the first row. -/
def ArcticBarrierDP : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SomewhereFinite hd J lettersPB →
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Statement of Theorem 3.3 (the reversal of 𝒯, `𝔸_ℕ`)**. -/
def ArcticBarrierDPrev : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SomewhereFinite hd J lettersPDrev →
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Statement of Theorem 3.4 (𝒯, below zero `𝔸_ℤ`)**: the same as `ArcticBarrierDP`, for interpretations by arctic linear functions
over `𝔸_ℤ` that are absolutely positive on the letters of the problem. -/
def ArcticBarrierBZ : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J lettersPB →
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Statement of Theorem 3.4 (the reversal of 𝒯, below zero `𝔸_ℤ`)**. -/
def ArcticBarrierBZrev : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J lettersPDrev →
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

end Collatz.Arctic
