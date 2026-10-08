/-
Checks of the non-vacuity of the main statements (continued; §6 to §8 of `NonVacuity.lean`): direction of strength (the forms of Koprowski–Waldmann 2009 follow from the main theorems),
recomputation of dependency pairs and usable rules, and rule removal for the reversed system.
-/
import CollatzProof.Arctic.NonVacuity3

namespace Collatz.Arctic

namespace NonVacuity

open Letter DLetter Matrix

/-! ## §6 Direction of strength (the forms of Koprowski–Waldmann 2009 follow from the main theorems) -/

theorem weak_of_strict {d : ℕ} (I : Interp d) (ρ : Rule) (h : Strict I ρ) : Weak I ρ := by
  intro i j
  rcases h i j with h | ⟨h1, h2⟩
  · exact le_of_lt h
  · rw [h1, h2]

theorem le_of_GG {R : Type} [Preorder R] [Zero R] {a b : R} (h : GG a b) : b ≤ a := by
  rcases h with h | ⟨h1, h2⟩
  · exact le_of_lt h
  · rw [h1, h2]

/-- `f ≫_λ g` of Koprowski–Waldmann 2009 (coefficientwise: all rows and the absolute part). -/
def StrictA {R : Type} [LT R] [Zero R] {d : ℕ} (f g : AffFun R d) : Prop :=
  (∀ i j, GG (f.M i j) (g.M i j)) ∧ ∀ i, GG (f.c i) (g.c i)

theorem strictTop_of_strictA {R : Type} [LT R] [Zero R] {d : ℕ} (hd : 0 < d) {f g : AffFun R d}
    (h : StrictA f g) : StrictTop hd f g := ⟨fun j => h.1 _ j, h.2 _⟩

theorem weakTop_of_weakA {R : Type} [LE R] {d : ℕ} (hd : 0 < d) {f g : AffFun R d}
    (h : WeakA f g) : WeakTop hd f g := ⟨fun j => h.1 _ j, h.2 _⟩

theorem weakTop_of_strictTop {R : Type} [Preorder R] [Zero R] {d : ℕ} (hd : 0 < d)
    {f g : AffFun R d} (h : StrictTop hd f g) : WeakTop hd f g :=
  ⟨fun j => le_of_GG (h.1 j), le_of_GG h.2⟩

/-- The form of Koprowski–Waldmann 2009, Theorem 6.7: no interpretation orients every rule weakly or strictly and some rule strictly. -/
theorem kw09_ST : ¬ ∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧
    (∀ ρ ∈ rulesST, Weak I ρ ∨ Strict I ρ) ∧ ∃ ρ ∈ rulesST, Strict I ρ := by
  rintro ⟨d, hd, I, hfin, hw, ρ, hρ, hs⟩
  exact arcticBarrierST d hd I hfin (fun σ hσ => (hw σ hσ).elim id (weak_of_strict I σ)) ρ hρ hs

/-- The form of Koprowski–Waldmann 2009, Theorem 7.1: there is no interpretation with all symbols somewhere finite, `U` oriented by `≥_λ`, `P_B` by `≥_λ` or `≫_λ`,
and some pair by `≫_λ`. -/
theorem kw09_DP : ¬ ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    (∀ s, (J s).c ⟨0, hd⟩ ≠ 0 ∨ (J s).M ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0) ∧
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakA (evA J π.lhs) (evA J π.rhs) ∨ StrictA (evA J π.lhs) (evA J π.rhs)) ∧
    ∃ π ∈ pairsPB, StrictA (evA J π.lhs) (evA J π.rhs) := by
  rintro ⟨d, hd, J, hsf, hU, hP, π, hπ, hs⟩
  exact arcticBarrierDP d hd J (fun s _ => hsf s) hU
    (fun σ hσ => (hP σ hσ).elim (weakTop_of_weakA hd)
      (fun h => weakTop_of_strictTop hd (strictTop_of_strictA hd h)))
    π hπ (strictTop_of_strictA hd hs)

theorem kw09_DPrev : ¬ ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    (∀ s, (J s).c ⟨0, hd⟩ ≠ 0 ∨ (J s).M ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0) ∧
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakA (evA J π.lhs) (evA J π.rhs) ∨ StrictA (evA J π.lhs) (evA J π.rhs)) ∧
    ∃ π ∈ pairsPDrev, StrictA (evA J π.lhs) (evA J π.rhs) := by
  rintro ⟨d, hd, J, hsf, hU, hP, π, hπ, hs⟩
  exact arcticBarrierDPrev d hd J (fun s _ => hsf s) hU
    (fun σ hσ => (hP σ hσ).elim (weakTop_of_weakA hd)
      (fun h => weakTop_of_strictTop hd (strictTop_of_strictA hd h)))
    π hπ (strictTop_of_strictA hd hs)

/-- The form of Koprowski–Waldmann 2009, Theorem 8.3 (below zero, all symbols absolutely positive). -/
theorem kw09_BZ : ¬ ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    (∀ s, ArcZ.fin 0 ≤ (J s).c ⟨0, hd⟩) ∧
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakA (evA J π.lhs) (evA J π.rhs) ∨ StrictA (evA J π.lhs) (evA J π.rhs)) ∧
    ∃ π ∈ pairsPB, StrictA (evA J π.lhs) (evA J π.rhs) := by
  rintro ⟨d, hd, J, hap, hU, hP, π, hπ, hs⟩
  exact arcticBarrierBZ d hd J (fun s _ => hap s) hU
    (fun σ hσ => (hP σ hσ).elim (weakTop_of_weakA hd)
      (fun h => weakTop_of_strictTop hd (strictTop_of_strictA hd h)))
    π hπ (strictTop_of_strictA hd hs)

theorem kw09_BZrev : ¬ ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    (∀ s, ArcZ.fin 0 ≤ (J s).c ⟨0, hd⟩) ∧
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakA (evA J π.lhs) (evA J π.rhs) ∨ StrictA (evA J π.lhs) (evA J π.rhs)) ∧
    ∃ π ∈ pairsPDrev, StrictA (evA J π.lhs) (evA J π.rhs) := by
  rintro ⟨d, hd, J, hap, hU, hP, π, hπ, hs⟩
  exact arcticBarrierBZrev d hd J (fun s _ => hap s) hU
    (fun σ hσ => (hP σ hσ).elim (weakTop_of_weakA hd)
      (fun h => weakTop_of_strictTop hd (strictTop_of_strictA hd h)))
    π hπ (strictTop_of_strictA hd hs)

/-! ## §7 Recomputation of dependency pairs and usable rules -/

/-- Defined symbols (the leftmost letters of the left-hand sides). -/
def definedSyms (R : List Rule) : List Letter := R.filterMap (fun ρ => ρ.lhs.head?)

/-- Mark the leftmost letter. -/
def markW : Word → List DLetter
  | [] => []
  | h :: tl => mark h :: tl.map plain

/-- Dependency pairs of a string rewriting system (Zantema 2005, TORPA, Section 5): for `ℓ → r` and each suffix `r'` of `r` whose leftmost letter is a defined symbol,
the pair `ℓ# → r'#`. -/
def dpsOf (R : List Rule) : List DRule :=
  R.flatMap fun ρ => ((List.range ρ.rhs.length).map (fun i => ρ.rhs.drop i)).filterMap fun r' =>
    match r'.head? with
    | some h => if h ∈ definedSyms R then some ⟨markW ρ.lhs, markW r'⟩ else none
    | none => none

/-- Reversal of a rule (both sides reversed). -/
def revRule (ρ : Rule) : Rule := ⟨ρ.lhs.reverse, ρ.rhs.reverse⟩

/-- The reversed system of $\mathcal T$. -/
def rulesSTrev : List Rule := rulesST.map revRule

theorem dps_ST_len : (dpsOf rulesST).length = 14 := by decide
theorem dps_STrev_len : (dpsOf rulesSTrev).length = 9 := by decide

/-- `P_B` consists exactly of the forward dependency pairs whose right-hand root is `/#` (their left-hand root is also `/#`). -/
theorem dps_ST_PB :
    (dpsOf rulesST).filter (fun π => π.rhs.head? = some (mark lft)) = pairsPB := by decide

/-- The dependency pairs entering `/#` all leave from `/#` (no edge from other components into `P_B`). -/
theorem dps_ST_into_PB : ∀ π ∈ dpsOf rulesST,
    π.rhs.head? = some (mark lft) → π.lhs.head? = some (mark lft) := by decide

theorem dps_STrev_PD :
    (dpsOf rulesSTrev).filter (fun π => π.rhs.head? = some (mark rgt)) = pairsPDrev := by decide

theorem dps_STrev_into_PD : ∀ π ∈ dpsOf rulesSTrev,
    π.rhs.head? = some (mark rgt) → π.lhs.head? = some (mark rgt) := by decide

/-- The unmarked symbols of a right-hand side. -/
def plainSyms (w : List DLetter) : List Letter :=
  w.filterMap fun s => match s with
    | plain x => some x
    | mark _ => none

/-- One step of the closure for usable rules (Giesl–Thiemann–Schneider-Kamp–Falke 2006, Definition 10): add to a set of symbols the symbols of the right-hand sides of the rules whose left-hand root is in the set
(without duplicates). -/
def closeStep (R : List Rule) (S : List Letter) : List Letter :=
  ((R.filter (fun ρ => match ρ.lhs.head? with
    | some h => decide (h ∈ S)
    | none => false)).flatMap Rule.rhs).foldl (fun acc x => acc.insert x) S

def closeIter (R : List Rule) (S : List Letter) : ℕ → List Letter
  | 0 => S
  | n + 1 => closeStep R (closeIter R S n)

/-- Usable rules (there are 7 symbols, so the closure is reached in 7 steps). -/
def usableOf (R : List Rule) (P : List DRule) : List Rule :=
  R.filter fun ρ => match ρ.lhs.head? with
    | some h => decide (h ∈ closeIter R (P.flatMap fun π => plainSyms π.rhs) 7)
    | none => false

theorem usable_ST : usableOf rulesST pairsPB = usableST := by decide
theorem usable_STrev : usableOf rulesSTrev pairsPDrev = usableSTrev := by decide

/-- The closure is stable after 7 steps (no new symbol appears at step 8). -/
theorem close_stable_ST : ∀ x ∈ closeIter rulesST (pairsPB.flatMap fun π => plainSyms π.rhs) 8,
    x ∈ closeIter rulesST (pairsPB.flatMap fun π => plainSyms π.rhs) 7 := by decide

theorem close_stable_STrev :
    ∀ x ∈ closeIter rulesSTrev (pairsPDrev.flatMap fun π => plainSyms π.rhs) 8,
      x ∈ closeIter rulesSTrev (pairsPDrev.flatMap fun π => plainSyms π.rhs) 7 := by decide

/-! ## §8 Rule removal for the reversed system (the mirror or reversal of tools) also follows from the main theorem -/

/-- Transpose of an interpretation. -/
def transI {d : ℕ} (I : Interp d) : Interp d := fun s => (I s)ᵀ

theorem ev_transI {d : ℕ} (I : Interp d) (w : Word) : ev (transI I) w = (ev I w.reverse)ᵀ := by
  induction w with
  | nil => simp [ev]
  | cons s w ih =>
    rw [ev_cons, ih, List.reverse_cons, ev_append, Matrix.transpose_mul]
    simp [ev, transI]

theorem weak_rev_iff {d : ℕ} (I : Interp d) (ρ : Rule) : Weak I (revRule ρ) ↔ Weak (transI I) ρ := by
  simp only [Weak, revRule, ev_transI, Matrix.transpose_apply]
  exact ⟨fun h i j => h j i, fun h i j => h j i⟩

theorem strict_rev_iff {d : ℕ} (I : Interp d) (ρ : Rule) :
    Strict I (revRule ρ) ↔ Strict (transI I) ρ := by
  simp only [Strict, revRule, ev_transI, Matrix.transpose_apply]
  exact ⟨fun h i j => h j i, fun h i j => h j i⟩

/-- The barrier for rule removal also holds for the 11 rules of the reversed system $\mathcal T^{\mathrm{rev}}$ (Theorem 3.1(i); reduced to `ArcticBarrierST` by transposition). -/
theorem barrier_STrev : BarrierFor rulesSTrev := by
  intro d hd I hfin hw ρ hρ hs
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hρ
  exact arcticBarrierST d hd (transI I) (fun s => hfin s)
    (fun τ hτ => (weak_rev_iff I τ).1 (hw _ (List.mem_map_of_mem hτ))) σ hσ
    ((strict_rev_iff I σ).1 hs)

end NonVacuity

end Collatz.Arctic
