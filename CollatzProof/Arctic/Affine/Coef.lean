/-
Interpretations by arctic linear functions with absolute parts (rules compared at every point), and the lemmas that extract the
coefficientwise comparison from the comparison at every point (the common part of Corollary 3.8 and Proposition 4.8 of the paper).

* Interpretation: each letter `σ` is interpreted by an arctic linear function `J σ : AffFun Arc d` (`x ↦ M_σ ⊗ x ⊕ c_σ`, Koprowski–Waldmann 2009, Definition 4.4). A string is interpreted by the composition
  `evL J (σ₁ ⋯ σ_k) = J σ₁ ∘ ⋯ ∘ J σ_k` (`DPStatement.evA` applied to unmarked letters; **the leftmost letter is outermost**:
  `evL_cons`, `evL_apply_cons`).
* Orientation (`PWeak`, `PStrict`): for **every** `x ∈ 𝔸_ℕ^d`, `[ℓ](x) ≥ [r](x)` (componentwise), respectively `[ℓ](x) ≫ [r](x)`
  (in every component `>`, or both −∞).
* Conditions on the class: `SomeFin` (somewhere finite, Koprowski–Waldmann 2009, Definition 6.1: `(M_σ)₀₀` or `(c_σ)₀` is finite; the class for top termination) and
  the stronger condition that every `(M_σ)₀₀` is finite (`Fin.lean`).
* Extraction of coefficients (`coef_weak`, `coef_strict`; the direction of Koprowski–Waldmann 2009, Lemma 6.5): from the weak (strict) comparison at every point, the coefficientwise
  `≥` (`≫`). The point `x = −∞` gives the absolute parts, and `x = N e_j` (`N` large) gives the column `j` of the matrices.
* The matrix part (`evL_M`): `(evL J w).M = ev (matOf J) w` (`Defs.ev` of the frozen statements).
-/
import CollatzProof.Arctic.NonVacuity

namespace Collatz.Arctic.Affine

open Collatz.Arctic DLetter

/-! ## Definitions -/

/-- The letter without its mark. -/
def base : DLetter → Letter
  | mark s => s
  | plain s => s

/-- Extends the interpretation of the letters to marked letters, by the same arctic linear function. -/
def lift {d : ℕ} (J : Letter → AffFun Arc d) : DLetter → AffFun Arc d := fun s => J (base s)

/-- The interpretation of a string: the composition of the arctic linear functions (`evA` applied to unmarked letters). -/
def evL {d : ℕ} (J : Letter → AffFun Arc d) (w : List Letter) : AffFun Arc d :=
  evA (lift J) (w.map plain)

/-- Weak orientation at every point: `[r](x) ≤ [ℓ](x)` for every `x` (componentwise). -/
def PWeak {d : ℕ} (J : Letter → AffFun Arc d) (ρ : Rule) : Prop :=
  ∀ x : Fin d → Arc, ∀ i, (evL J ρ.rhs).apply x i ≤ (evL J ρ.lhs).apply x i

/-- Strict orientation at every point: `[ℓ](x) ≫ [r](x)` for every `x` (componentwise). -/
def PStrict {d : ℕ} (J : Letter → AffFun Arc d) (ρ : Rule) : Prop :=
  ∀ x : Fin d → Arc, ∀ i, GG ((evL J ρ.lhs).apply x i) ((evL J ρ.rhs).apply x i)

/-- Somewhere finite (Koprowski–Waldmann 2009, Definition 6.1): for every letter, `(c_σ)₀` or `(M_σ)₀₀` is finite. -/
def SomeFin {d : ℕ} (hd : 0 < d) (J : Letter → AffFun Arc d) : Prop :=
  ∀ σ, (J σ).c ⟨0, hd⟩ ≠ 0 ∨ (J σ).M ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0

/-- **Some somewhere finite interpretation by arctic linear functions weakly orients all rules of `R` and strictly orients `ρ` (at every point).** -/
def SomeFinOrientable (R : List Rule) (ρ : Rule) : Prop :=
  ∃ (d : ℕ) (hd : 0 < d) (J : Letter → AffFun Arc d),
    SomeFin hd J ∧ (∀ ρ' ∈ R, PWeak J ρ') ∧ PStrict J ρ

/-- The matrix part (an `Interp` of the frozen statements). -/
def matOf {d : ℕ} (J : Letter → AffFun Arc d) : Interp d := fun σ => (J σ).M

/-! ## The order of composition -/

lemma evL_nil {d : ℕ} (J : Letter → AffFun Arc d) : evL J [] = AffFun.id := rfl

/-- The leftmost letter is outermost: `[σ w] = [σ] ∘ [w]`. -/
lemma evL_cons {d : ℕ} (J : Letter → AffFun Arc d) (σ : Letter) (w : List Letter) :
    evL J (σ :: w) = (J σ).comp (evL J w) := rfl

lemma evL_apply_cons {d : ℕ} (J : Letter → AffFun Arc d) (σ : Letter) (w : List Letter)
    (x : Fin d → Arc) : (evL J (σ :: w)).apply x = (J σ).apply ((evL J w).apply x) := by
  rw [evL_cons, NonVacuity.AffFun.apply_comp]

lemma evL_apply_nil {d : ℕ} (J : Letter → AffFun Arc d) (x : Fin d → Arc) :
    (evL J []).apply x = x := NonVacuity.AffFun.apply_id x

/-- The matrix part is `ev` of the frozen statements. -/
theorem evL_M {d : ℕ} (J : Letter → AffFun Arc d) (w : List Letter) : (evL J w).M = ev (matOf J) w := by
  induction w with
  | nil => rfl
  | cons σ w ih =>
    rw [evL_cons]
    show (J σ).M * (evL J w).M = _
    rw [ih]
    simp only [ev, List.map_cons, List.prod_cons]
    rfl

/-- The string with its first letter marked. -/
def markHead : List Letter → List DLetter
  | [] => []
  | s :: w => mark s :: w.map plain

/-- The pair with the first letters marked (`ℓ^# → r^#` from a rule `ℓ → r` applied at the root). -/
def markRule (ρ : Rule) : DRule := ⟨markHead ρ.lhs, markHead ρ.rhs⟩

lemma evA_markHead {d : ℕ} (J : Letter → AffFun Arc d) (w : List Letter) :
    evA (lift J) (markHead w) = evL J w := by
  cases w with
  | nil => rfl
  | cons s w => rfl

/-! ## Extraction of coefficients -/

/-- `≫` on `WithBot ℕ` (`b < a`, or both −∞). -/
def gtW (a b : WithBot ℕ) : Prop := b < a ∨ (a = ⊥ ∧ b = ⊥)

lemma GG_iff (a b : Arc) : GG a b ↔ gtW (Arc.val a) (Arc.val b) := Iff.rfl

lemma apply_zero {d : ℕ} (f : AffFun Arc d) : f.apply 0 = f.c := by
  simp [AffFun.apply]

lemma apply_single {d : ℕ} (f : AffFun Arc d) (j : Fin d) (a : Arc) (i : Fin d) :
    f.apply (Pi.single j a) i = f.M i j * a + f.c i := by
  simp only [AffFun.apply, Pi.add_apply, Matrix.mulVec, dotProduct_single]

lemma key_le (a b c c' : WithBot ℕ)
    (h : ∀ N : ℕ, max (b + (N : WithBot ℕ)) c' ≤ max (a + (N : WithBot ℕ)) c) : b ≤ a := by
  induction b using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe β =>
    have h1 := le_trans (le_max_left _ _) (h (WithBot.unbotD 0 c + 1))
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      induction c using WithBot.recBotCoe with
      | bot => simp at h1
      | coe γ =>
        simp only [WithBot.bot_add, WithBot.unbotD_coe, bot_le, max_eq_right] at h1
        simp only [Nat.cast_withBot, ← WithBot.coe_add, WithBot.coe_le_coe] at h1
        omega
    | coe α =>
      rw [WithBot.coe_le_coe]
      induction c using WithBot.recBotCoe with
      | bot =>
        simp only [WithBot.unbotD_bot, bot_le, max_eq_left] at h1
        simp only [Nat.cast_withBot, ← WithBot.coe_add, WithBot.coe_le_coe] at h1
        omega
      | coe γ =>
        simp only [WithBot.unbotD_coe] at h1
        simp only [Nat.cast_withBot, ← WithBot.coe_add, WithBot.coe_le_coe, le_max_iff] at h1
        omega

lemma key_gt (a b c c' : WithBot ℕ)
    (h : ∀ N : ℕ, gtW (max (a + (N : WithBot ℕ)) c) (max (b + (N : WithBot ℕ)) c')) : gtW a b := by
  induction b using WithBot.recBotCoe with
  | bot =>
    induction a using WithBot.recBotCoe with
    | bot => exact Or.inr ⟨rfl, rfl⟩
    | coe α => exact Or.inl (WithBot.bot_lt_coe α)
  | coe β =>
    left
    have hN := h (WithBot.unbotD 0 c + 1)
    have hfin : max ((β : WithBot ℕ) + ((WithBot.unbotD 0 c + 1 : ℕ) : WithBot ℕ)) c' ≠ ⊥ := by
      intro hb
      have h2 : (β : WithBot ℕ) + ((WithBot.unbotD 0 c + 1 : ℕ) : WithBot ℕ) ≤ ⊥ :=
        hb ▸ le_max_left _ _
      simp [Nat.cast_withBot] at h2
    have h1 : (β : WithBot ℕ) + ((WithBot.unbotD 0 c + 1 : ℕ) : WithBot ℕ) <
        max (a + ((WithBot.unbotD 0 c + 1 : ℕ) : WithBot ℕ)) c := by
      rcases hN with hlt | ⟨_, hb⟩
      · exact lt_of_le_of_lt (le_max_left _ _) hlt
      · exact absurd hb hfin
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      induction c using WithBot.recBotCoe with
      | bot => simp at h1
      | coe γ =>
        simp only [WithBot.bot_add, WithBot.unbotD_coe, bot_le, max_eq_right] at h1
        simp only [Nat.cast_withBot, ← WithBot.coe_add, WithBot.coe_lt_coe] at h1
        omega
    | coe α =>
      rw [WithBot.coe_lt_coe]
      induction c using WithBot.recBotCoe with
      | bot =>
        simp only [WithBot.unbotD_bot, bot_le, max_eq_left] at h1
        simp only [Nat.cast_withBot, ← WithBot.coe_add, WithBot.coe_lt_coe] at h1
        omega
      | coe γ =>
        simp only [WithBot.unbotD_coe] at h1
        simp only [Nat.cast_withBot, ← WithBot.coe_add, WithBot.coe_lt_coe, lt_max_iff] at h1
        omega

/-- **Weak comparison at every point ⇒ coefficientwise weak comparison** (`f ≥_λ g`). -/
theorem coef_weak {d : ℕ} (f g : AffFun Arc d) (h : ∀ y : Fin d → Arc, ∀ i, g.apply y i ≤ f.apply y i) :
    WeakA f g := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · show Arc.val (g.M i j) ≤ Arc.val (f.M i j)
    refine key_le _ _ (Arc.val (f.c i)) (Arc.val (g.c i)) (fun N => ?_)
    have := h (Pi.single j (Arc.fin N)) i
    rw [apply_single, apply_single, Arc.le_iff_val] at this
    simpa only [Arc.val_add, Arc.val_mul, Arc.val_fin] using this
  · have := h 0 i
    rwa [apply_zero, apply_zero] at this

/-- **Strict comparison at every point ⇒ coefficientwise `≫`** (`f ≫_λ g`). -/
theorem coef_strict {d : ℕ} (f g : AffFun Arc d) (h : ∀ y : Fin d → Arc, ∀ i, GG (f.apply y i) (g.apply y i)) :
    (∀ i j, GG (f.M i j) (g.M i j)) ∧ ∀ i, GG (f.c i) (g.c i) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [GG_iff]
    refine key_gt _ _ (Arc.val (f.c i)) (Arc.val (g.c i)) (fun N => ?_)
    have := h (Pi.single j (Arc.fin N)) i
    rw [apply_single, apply_single, GG_iff] at this
    simpa only [Arc.val_add, Arc.val_mul, Arc.val_fin] using this
  · have := h 0 i
    rwa [apply_zero, apply_zero] at this

/-! ## Application to the orientation of rules -/

theorem weakA_of_pweak {d : ℕ} (J : Letter → AffFun Arc d) (ρ : Rule) (h : PWeak J ρ) :
    WeakA (evL J ρ.lhs) (evL J ρ.rhs) :=
  coef_weak _ _ h

theorem coefStrict_of_pstrict {d : ℕ} (J : Letter → AffFun Arc d) (ρ : Rule) (h : PStrict J ρ) :
    (∀ i j, GG ((evL J ρ.lhs).M i j) ((evL J ρ.rhs).M i j)) ∧
      ∀ i, GG ((evL J ρ.lhs).c i) ((evL J ρ.rhs).c i) :=
  coef_strict _ _ h

/-- Weak orientation at every point ⇒ weak orientation by the matrix part (`Weak` of the frozen statements). -/
theorem weak_of_pweak {d : ℕ} (J : Letter → AffFun Arc d) (ρ : Rule) (h : PWeak J ρ) :
    Weak (matOf J) ρ := by
  intro i j
  have := (weakA_of_pweak J ρ h).1 i j
  rwa [evL_M, evL_M] at this

/-- Strict orientation at every point ⇒ strict orientation by the matrix part (`Strict` of the frozen statements). -/
theorem strict_of_pstrict {d : ℕ} (J : Letter → AffFun Arc d) (ρ : Rule) (h : PStrict J ρ) :
    Strict (matOf J) ρ := by
  intro i j
  have := (coefStrict_of_pstrict J ρ h).1 i j
  rwa [evL_M, evL_M] at this

end Collatz.Arctic.Affine
