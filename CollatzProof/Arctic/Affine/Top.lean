/-
**With somewhere finite interpretations by arctic linear functions (the class for top termination), the rules that cannot be strictly oriented are exactly the 3 left-end rules**
(Proposition 4.8 of the paper; both directions for `𝒯` and `𝓗`; for the reversed systems the protected rules are the dynamic rules).

The class: each letter is interpreted by an arctic linear function `x ↦ M_σ ⊗ x ⊕ c_σ` (any dimension, `𝔸_ℕ`), somewhere finite in the sense of Koprowski–Waldmann 2009 (`(M_σ)₀₀` or `(c_σ)₀`
finite, `Coef.SomeFin`); a string is interpreted by the composition (the leftmost letter is outermost, `Coef.evL_cons`), and rules are compared at every point (`PWeak`,
`PStrict`). Since letters with `(M_σ)₀₀ = −∞` are allowed, this class is larger than the class of rule removal in Theorem 3.1.

* The "only if" direction (`affBarrierTop_of`): the left-end rules (the rules beginning with `/`) are used only at the root, so
  with `[/^#] := [/]` their strict orientation becomes a strict orientation in the first row for the dependency pair problem `(P_B, 𝒰)`, which contradicts Theorem 3.3
  (`arcticBarrierDP`, `HTPDB.arcticBarrierHDP`). For the reversed systems, `arcticBarrierDPrev` and `arcticBarrierHDPrev`.
* The "if" direction (`Witness.nonleft_*`): examples of dimension 1. If `/` is a constant function, all rules beginning with `/` hold with equality, and
  the other rules are strictly oriented by weights (family W) or by constants of the first letter (family K).
* Summary (`someFinClass_iff_left_ST`, `_HT`, `_STrev`, `_HTrev`): for `ρ ∈ R`,
  `SomeFinOrientable R ρ ↔ ρ ∉ (the left-end rules)`.
* Reading the composition in the opposite order (the leftmost letter innermost), the protected rules become the dynamic rules (the theorems for the reversed systems).
-/
import CollatzProof.Arctic.Affine.Witness

namespace Collatz.Arctic.Affine

open Collatz.Arctic

/-- If a somewhere finite interpretation by arctic linear functions weakly orients all rules of `R` (at every point), then it strictly orients
no rule of `top`. -/
def AffBarrierTop (R top : List Rule) : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : Letter → AffFun Arc d), SomeFin hd J →
    (∀ ρ ∈ R, PWeak J ρ) → ∀ ρ ∈ top, ¬ PStrict J ρ

/-- **From the dependency pair barrier to the barrier for the rules used at the root.** `P` consists of the rules of `top` with their first letters marked. -/
theorem affBarrierTop_of {L : List DLetter} {U : List Rule} {P : List DRule}
    (hB : NonVacuity.BarrierDPFor L U P) {R top : List Rule} (hU : ∀ ρ ∈ U, ρ ∈ R)
    (htop : ∀ ρ ∈ top, ρ ∈ R) (hP : P = top.map markRule) : AffBarrierTop R top := by
  intro d hd J hs hweak ρ hρ hstr
  have hSF : SomewhereFinite hd (lift J) L := fun s _ => hs (base s)
  have hUw : ∀ ρ' ∈ U, WeakA (evA (lift J) ρ'.plain.lhs) (evA (lift J) ρ'.plain.rhs) :=
    fun ρ' h' => weakA_of_pweak J ρ' (hweak ρ' (hU ρ' h'))
  have hPw : ∀ π ∈ P, WeakTop hd (evA (lift J) π.lhs) (evA (lift J) π.rhs) := by
    intro π hπ
    rw [hP] at hπ
    obtain ⟨ρ', hρ', rfl⟩ := List.mem_map.mp hπ
    have hw := weakA_of_pweak J ρ' (hweak ρ' (htop ρ' hρ'))
    show WeakTop hd (evA (lift J) (markHead ρ'.lhs)) (evA (lift J) (markHead ρ'.rhs))
    rw [evA_markHead, evA_markHead]
    exact ⟨fun j => hw.1 _ j, hw.2 _⟩
  have hπ : markRule ρ ∈ P := hP ▸ List.mem_map_of_mem hρ
  apply hB d hd (lift J) hSF hUw hPw (markRule ρ) hπ
  have hs' := coefStrict_of_pstrict J ρ hstr
  show StrictTop hd (evA (lift J) (markHead ρ.lhs)) (evA (lift J) (markHead ρ.rhs))
  rw [evA_markHead, evA_markHead]
  exact ⟨fun j => hs'.1 _ j, hs'.2 _⟩

open Letter

/-- The 3 left-end rules (`/0 → /t`, `/1 → /ff`, `/2 → /ft`), common to `𝒯` and `𝓗`. -/
def leftST : List Rule :=
  [⟨[lft, d0], [lft, t]⟩, ⟨[lft, d1], [lft, f, f]⟩, ⟨[lft, d2], [lft, f, t]⟩]

/-- The dynamic rules of the reversed `𝒯` (`.f → .`, `.t → .2`). -/
def dynSTrev : List Rule := [⟨[rgt, f], [rgt]⟩, ⟨[rgt, t], [rgt, d2]⟩]

/-- The dynamic rules of the reversed `𝓗` (`.ff → .0`, `.ttt → .22`). -/
def dynHTrev : List Rule := [⟨[rgt, f, f], [rgt, d0]⟩, ⟨[rgt, t, t, t], [rgt, d2, d2]⟩]

/-! ## The "only if" direction -/

theorem affTop_ST : AffBarrierTop rulesST leftST :=
  affBarrierTop_of arcticBarrierDP (by decide) (by decide) (by decide)

theorem affTop_HT : AffBarrierTop HTPDB.rulesHT leftST :=
  affBarrierTop_of HTPDB.arcticBarrierHDP (by decide) (by decide) (by decide)

theorem affTop_STrev : AffBarrierTop NonVacuity.rulesSTrev dynSTrev :=
  affBarrierTop_of arcticBarrierDPrev (by decide) (by decide) (by decide)

theorem affTop_HTrev : AffBarrierTop HTPDB.NonVacuityH.rulesHTrev dynHTrev :=
  affBarrierTop_of HTPDB.arcticBarrierHDPrev (by decide) (by decide) (by decide)

/-! ## Summary (both directions) -/

lemma left_iff_ST : ∀ ρ ∈ rulesST, (ρ.lhs.head? = some lft ↔ ρ ∈ leftST) := by decide
lemma left_iff_HT : ∀ ρ ∈ HTPDB.rulesHT, (ρ.lhs.head? = some lft ↔ ρ ∈ leftST) := by decide
lemma dyn_iff_STrev : ∀ ρ ∈ NonVacuity.rulesSTrev, (ρ.lhs.head? = some rgt ↔ ρ ∈ dynSTrev) := by decide
lemma dyn_iff_HTrev :
    ∀ ρ ∈ HTPDB.NonVacuityH.rulesHTrev, (ρ.lhs.head? = some rgt ↔ ρ ∈ dynHTrev) := by decide

/-- The two directions combined into one equivalence. -/
lemma iff_of {R top : List Rule} {E : Letter} (hbar : AffBarrierTop R top)
    (hex : ∀ ρ ∈ R, ρ.lhs.head? ≠ some E → SomeFinOrientable R ρ)
    (htop : ∀ ρ ∈ R, (ρ.lhs.head? = some E ↔ ρ ∈ top)) (ρ : Rule) (hρ : ρ ∈ R) :
    SomeFinOrientable R ρ ↔ ρ ∉ top := by
  constructor
  · rintro ⟨d, hd, J, hs, hw, hst⟩ htρ
    exact hbar d hd J hs hw ρ htρ hst
  · intro hn
    exact hex ρ hρ (fun h => hn ((htop ρ hρ).mp h))

/-- **`𝒯`**: a somewhere finite interpretation by arctic linear functions (any dimension, `𝔸_ℕ`, comparison at every point) can weakly orient all rules of `𝒯` and
strictly orient the rule `ρ` if and only if `ρ` is none of the 3 left-end rules. -/
theorem someFinClass_iff_left_ST (ρ : Rule) (hρ : ρ ∈ rulesST) :
    SomeFinOrientable rulesST ρ ↔ ρ ∉ leftST :=
  iff_of affTop_ST nonleft_ST left_iff_ST ρ hρ

/-- **`𝓗`**: the same. -/
theorem someFinClass_iff_left_HT (ρ : Rule) (hρ : ρ ∈ HTPDB.rulesHT) :
    SomeFinOrientable HTPDB.rulesHT ρ ↔ ρ ∉ leftST :=
  iff_of affTop_HT nonleft_HT left_iff_HT ρ hρ

/-- **The reversed `𝒯`**: the protected rules are the dynamic rules. -/
theorem someFinClass_iff_dyn_STrev (ρ : Rule) (hρ : ρ ∈ NonVacuity.rulesSTrev) :
    SomeFinOrientable NonVacuity.rulesSTrev ρ ↔ ρ ∉ dynSTrev :=
  iff_of affTop_STrev nonleft_STrev dyn_iff_STrev ρ hρ

/-- **The reversed `𝓗`**: the protected rules are the dynamic rules. -/
theorem someFinClass_iff_dyn_HTrev (ρ : Rule) (hρ : ρ ∈ HTPDB.NonVacuityH.rulesHTrev) :
    SomeFinOrientable HTPDB.NonVacuityH.rulesHTrev ρ ↔ ρ ∉ dynHTrev :=
  iff_of affTop_HTrev nonleft_HTrev dyn_iff_HTrev ρ hρ

/-- In this class, rule removal for `𝒯` removes at least one rule (the dynamic rule `f. → .`), unlike the class of rule removal in Theorem 3.1. -/
theorem exists_someFinOrientable_ST : ∃ ρ ∈ rulesST, SomeFinOrientable rulesST ρ :=
  ⟨⟨[f, rgt], [rgt]⟩, by decide, (someFinClass_iff_left_ST _ (by decide)).mpr (by decide)⟩

end Collatz.Arctic.Affine
