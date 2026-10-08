/-
# Checks of the non-vacuity of the main statements (internal independent review)

For the statements (`Statement.lean`, `DPStatement.lean`, frozen) of the five unconditional main theorems of `Summary.lean` (`arcticBarrierST`, `arcticBarrierDP`, `arcticBarrierDPrev`,
`arcticBarrierBZ`, `arcticBarrierBZrev`), we look for errors on the side of the statements
(vacuous premises, conclusions trivial by definition, deviations from the definitions of Koprowski–Waldmann 2009, errors in the transcription of rules and dependency pairs).
Existing files are not changed. No `sorry`, `axiom` or `native_decide` is used.

* §0 Notation: in `Arc` and `ArcZ`, `0` is −∞ and `1` is the finite 0; the sum is max and the product is +. Matrix products are max-plus.
* §1 Agreement with the definitions of Koprowski–Waldmann 2009: `Weak` and `Strict` are the entrywise `≥` and `≫` (allowing `−∞ ≫ −∞`), `Fin00` says that `(M_s)₀₀`
  is finite, and `evA` is the composition of arctic linear functions (`x ↦ M ⊗ x ⊕ c`). Small examples by `decide`.
* §2 General forms with the set of rules as a parameter: the five statements are special cases (`Iff.rfl`).
* §3 The premises are satisfiable ((i)): for each of the five statements, an interpretation (dimension 1) satisfying all premises.
* §4 Is strict orientation possible by definition? ((ii)):
  - Dependency pairs: every pair of `P_B` and of `P_D^rev` is strictly oriented in the first row by some interpretation.
  - Rule removal: 9 of the 11 rules of $\mathcal T$ are strictly oriented by some interpretation. **The two commutation rules
    (`f d0 → d0 f`, `t d2 → d2 t`) are strictly oriented by no arctic interpretation (`Fin00`) of any dimension**
    (an argument with the max-plus trace, which does not use the orientation of the other rules). The part of the conclusion of the main theorem on these two rules is trivial.
* §5 Counterexamples for subsystems (a strong form of (ii)): for the terminating systems obtained from $\mathcal T$ by removing the dynamic rules (or the left-end rules),
  some interpretation weakly orients all rules and strictly orients some rule. Likewise for dependency pairs: after removing from `U` the dynamic rules (for the reversed problem,
  the left-end rules), all of `P` can be strictly oriented. Hence the truth of the statements is not decided by the definitions alone; it
  depends on the part encoding the Collatz dynamics (the dynamic and left-end rules).
* §6 Direction of strength: `Strict → Weak`, and `WeakTop`, `StrictTop` from `≥_λ`, `≫_λ` of Koprowski–Waldmann 2009 (coefficientwise, all rows).
  The barriers in the forms of Theorems 6.7, 7.1 and 8.3 of Koprowski–Waldmann 2009 follow from the main theorems.
* §7 Recomputation of dependency pairs and usable rules: from `rulesST` (and its reversal), compute the dependency pairs of string rewriting systems (Zantema 2005) and the usable rules of Giesl–Thiemann–Schneider-Kamp–Falke 2006, Definition 10
  (as a closure), and check by `decide` that they agree with `pairsPB`, `usableST`, `pairsPDrev`, `usableSTrev`.
* §8 The barrier for rule removal for the reversed system $\mathcal T^{\mathrm{rev}}$ follows from `arcticBarrierST` by transposition (`Weak`, `Strict`, `Fin00` are
  invariant under transposition). The convention on the order of matrix products does not affect the statement of rule removal.

This file contains §0 to §2; §3 is in `NonVacuity2.lean`, §4 and §5 in `NonVacuity3.lean`, §6 to §8 in `NonVacuity4.lean`.
-/
import CollatzProof.Arctic.Bridge
import CollatzProof.Arctic.Summary

namespace Collatz.Arctic

namespace NonVacuity

open Letter DLetter Matrix

/-! ## §0 Notation -/

example : (0 : Arc) = Arc.negInf := rfl
example : (1 : Arc) = Arc.fin 0 := rfl
example : (0 : ArcZ) = ArcZ.negInf := rfl
example : (1 : ArcZ) = ArcZ.fin 0 := rfl
example : Arc.fin 2 + Arc.fin 5 = Arc.fin 5 := by decide
example : Arc.fin 2 * Arc.fin 5 = Arc.fin 7 := by decide
example : Arc.fin 2 + 0 = Arc.fin 2 := by decide
example : Arc.fin 2 * 0 = 0 := by decide
example : (0 : Arc) < Arc.fin 0 := by decide
example : ArcZ.fin (-3) * ArcZ.fin 5 = ArcZ.fin 2 := by decide
example : ArcZ.fin (-3) + ArcZ.fin (-5) = ArcZ.fin (-3) := by decide
example : (0 : ArcZ) < ArcZ.fin (-7) := by decide

/-! ## §1 Agreement with the definitions of Koprowski–Waldmann 2009 -/

/-- Matrix products are max-plus: `[AB]_{ij} = max_k (A_{ik} + B_{kj})` (`⊥` is −∞). -/
theorem val_mul_apply {d : ℕ} (A B : AMat d) (i j : Fin d) :
    Arc.val ((A * B) i j) = Finset.univ.sup (fun k => Arc.val (A i k) + Arc.val (B k j)) := by
  rw [Matrix.mul_apply, Arc.val_sum]
  rfl

/-- `Weak` is the entrywise `≥` (the order of the carrier `WithBot ℕ`). -/
theorem weak_iff {d : ℕ} (I : Interp d) (ρ : Rule) :
    Weak I ρ ↔ ∀ i j, Arc.val (ev I ρ.rhs i j) ≤ Arc.val (ev I ρ.lhs i j) := Iff.rfl

/-- `Strict` is the entrywise `≫` of Koprowski–Waldmann 2009: `>`, or both −∞ (`⊥`). -/
theorem strict_iff {d : ℕ} (I : Interp d) (ρ : Rule) :
    Strict I ρ ↔ ∀ i j, Arc.val (ev I ρ.rhs i j) < Arc.val (ev I ρ.lhs i j) ∨
      (Arc.val (ev I ρ.lhs i j) = ⊥ ∧ Arc.val (ev I ρ.rhs i j) = ⊥) := Iff.rfl

/-- `Strict` is `GG` (the `≫` of Koprowski–Waldmann 2009) of the dependency pair forms, applied entrywise. -/
theorem strict_iff_GG {d : ℕ} (I : Interp d) (ρ : Rule) :
    Strict I ρ ↔ ∀ i j, GG (ev I ρ.lhs i j) (ev I ρ.rhs i j) := Iff.rfl

/-- `Fin00`: the `(0,0)` entry of the matrix of every symbol is finite (not `⊥`). -/
theorem fin00_iff {d : ℕ} (hd : 0 < d) (I : Interp d) :
    Fin00 hd I ↔ ∀ s, Arc.val (I s ⟨0, hd⟩ ⟨0, hd⟩) ≠ ⊥ := Iff.rfl

/-- Individual cases of `≫` (Koprowski–Waldmann 2009, Section 4). -/
example : GG (Arc.fin 1) (Arc.fin 0) := by unfold GG; decide
example : GG (0 : Arc) 0 := by unfold GG; decide
example : GG (Arc.fin 0) (0 : Arc) := by unfold GG; decide
example : ¬ GG (Arc.fin 0) (Arc.fin 0) := by unfold GG; decide
example : ¬ GG (0 : Arc) (Arc.fin 0) := by unfold GG; decide
example : GG (ArcZ.fin (-1)) (ArcZ.fin (-2)) := by unfold GG; decide
example : ¬ GG (ArcZ.fin (-2)) (ArcZ.fin (-2)) := by unfold GG; decide

/-- A 2 × 2 example: `f` has `(0,0)` entry 1, the other symbols have `(0,0)` entry 0. All other entries are −∞. -/
def I2 : Interp 2 := fun s =>
  if s = Letter.f then !![Arc.fin 1, 0; 0, 0] else !![Arc.fin 0, 0; 0, 0]

example : ev I2 [f, rgt] 0 0 = Arc.fin 1 := by decide
example : ev I2 [f, rgt] 0 1 = 0 := by decide
example : ev I2 [f, rgt] 1 1 = 0 := by decide

theorem I2_fin00 : Fin00 (by norm_num : 0 < 2) I2 := by
  intro s; cases s <;> decide

/-- `f . → .` is strictly oriented by `I2`. The entries other than `(0,0)` are −∞ on both sides, which uses `−∞ ≫ −∞` of Koprowski–Waldmann 2009. -/
theorem I2_strict : Strict I2 ⟨[f, rgt], [rgt]⟩ := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- In the form that does not allow `−∞ ≫ −∞` (only the entrywise `>`), the same example is not strictly oriented. -/
theorem I2_not_strict_without_inf : ¬ ∀ i j, ev I2 [rgt] i j < ev I2 [f, rgt] i j := by
  intro h
  have := h 0 1
  revert this
  decide

/-- Weak orientation is entrywise: for `. → f .`, `0 ≥ 1` fails at `(0,0)`. -/
theorem I2_not_weak : ¬ Weak I2 ⟨[rgt], [f, rgt]⟩ := by
  intro h
  have := h 0 0
  revert this
  decide

/-- If some symbol has `(0,0)` entry −∞, then `Fin00` fails. -/
theorem fin00_fails : ¬ Fin00 (by norm_num : 0 < 2)
    (fun _ => (!![0, Arc.fin 0; Arc.fin 0, Arc.fin 0] : AMat 2)) := by
  intro h
  exact h Letter.f rfl

/-- The value of a composition of linear functions: `(f ∘ g)(x) = f(g(x))` (the composition of Koprowski–Waldmann 2009, Definition 4.4). -/
theorem AffFun.apply_comp {R : Type} [CommSemiring R] {d : ℕ} (f g : AffFun R d) (x : Fin d → R) :
    (f.comp g).apply x = f.apply (g.apply x) := by
  simp only [AffFun.apply, AffFun.comp, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

theorem AffFun.apply_id {R : Type} [CommSemiring R] {d : ℕ} (x : Fin d → R) :
    (AffFun.id : AffFun R d).apply x = x := by
  simp [AffFun.apply, AffFun.id]

/-- `evA J (s₁ ⋯ s_k)` is the composition `[s₁] ∘ ⋯ ∘ [s_k]` (the string `s₁ ⋯ s_k` is the term `s₁(⋯ s_k(x))`). -/
theorem evA_apply {R : Type} [CommSemiring R] {d : ℕ} (J : DLetter → AffFun R d) (w : List DLetter)
    (x : Fin d → R) : (evA J w).apply x = w.foldr (fun s y => (J s).apply y) x := by
  induction w with
  | nil => exact AffFun.apply_id x
  | cons s w ih =>
    show ((J s).comp (evA J w)).apply x = (J s).apply (w.foldr (fun s y => (J s).apply y) x)
    rw [AffFun.apply_comp, ih]

/-! ## §2 General forms with the set of rules as a parameter -/

/-- The general form of the barrier for rule removal. -/
def BarrierFor (R : List Rule) : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I → (∀ ρ ∈ R, Weak I ρ) →
    ∀ ρ ∈ R, ¬ Strict I ρ

/-- The general form of the barrier for dependency pairs (`𝔸_ℕ`, somewhere finite). -/
def BarrierDPFor (L : List DLetter) (U : List Rule) (P : List DRule) : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SomewhereFinite hd J L →
    (∀ ρ ∈ U, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ P, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ P, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- The general form of the barrier for dependency pairs (below zero `𝔸_ℤ`, absolutely positive). -/
def BarrierBZFor (L : List DLetter) (U : List Rule) (P : List DRule) : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J L →
    (∀ ρ ∈ U, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ P, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ P, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

theorem ST_iff : ArcticBarrierST ↔ BarrierFor rulesST := Iff.rfl
theorem DP_iff : ArcticBarrierDP ↔ BarrierDPFor lettersPB usableST pairsPB := Iff.rfl
theorem DPrev_iff : ArcticBarrierDPrev ↔ BarrierDPFor lettersPDrev usableSTrev pairsPDrev := Iff.rfl
theorem BZ_iff : ArcticBarrierBZ ↔ BarrierBZFor lettersPB usableST pairsPB := Iff.rfl
theorem BZrev_iff : ArcticBarrierBZrev ↔ BarrierBZFor lettersPDrev usableSTrev pairsPDrev := Iff.rfl

end NonVacuity

end Collatz.Arctic
