/-
Lean foundation of Section 8 (Section 8.1): estimates of values along general dependency pair chains.

The first half of the proof of Lemma 5.6 (the parts of the proof of Theorem 3.3 on non-increase and on the decrease under strict orientation), written for chains `GDChain`
with the symbol type `α` as a parameter. Adapted from `DPBridge.lean` (`Vw_under`, `Vw_root_weak`, `Vw_root_strict`,
`Vw_chain`), `DPMain.lean` (`yvec_ne_zero`) and `BZMain.lean` (`Vw_nat`). The semiring is handled through `ArcticOrder`, common to `Arc` (`𝔸_ℕ`) and `ArcZ`
(below zero).

* `hom_gevA`, `hom_gevA_append`: the homogeneous coordinates of the interpretation of a string are the product of those of its symbols.
* `gV_under`: a step by a rule of `U` (coefficientwise weak) does not increase the value (at any position `p`; Koprowski–Waldmann 2009, Lemma 6.6).
* `gV_root_weak`, `gV_root_strict`: a root step by a dependency pair does not increase the value under the weak first-row comparison, and decreases it by the arctic
  number 1 under the strict comparison (the same argument as for Lemma 5.1).
* `gV_chain`: along a chain the value decreases by the number of root uses of `σ` (even if `σ` is in `U`, only the root steps are counted).
* `gV_ne_zero`: over `𝔸_ℕ`, if every symbol of the string is somewhere finite, the value is finite (Koprowski–Waldmann 2009, Lemma 6.2).
* `gV_ge_head`: the value is at least the first component of the absolute part of the first symbol (below zero, absolute positivity makes the value ≥ 0; Koprowski–Waldmann 2009,
  Lemma 8.2).
-/
import CollatzProof.Arctic.DPGen.Defs

namespace Collatz.Arctic.DPGen

open Collatz.Arctic Matrix

variable {α : Type}

/-! ## Homogeneous coordinates -/

section Alg

variable {R : Type} [CommSemiring R] {d : ℕ}

theorem gevA_nil (J : GLetter α → AffFun R d) : gevA J [] = AffFun.id := rfl

theorem gevA_cons (J : GLetter α → AffFun R d) (s : GLetter α) (w : List (GLetter α)) :
    gevA J (s :: w) = (J s).comp (gevA J w) := rfl

/-- The homogeneous coordinates of the interpretation of a string are the product of those of its symbols. -/
theorem hom_gevA (J : GLetter α → AffFun R d) (L : List (GLetter α)) :
    hom (gevA J L) = (L.map (fun s => hom (J s))).prod := by
  induction L with
  | nil => simp [gevA, hom_id]
  | cons s L ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    exact hom_comp _ _

theorem hom_gevA_append (J : GLetter α → AffFun R d) (u v : List (GLetter α)) :
    hom (gevA J (u ++ v)) = hom (gevA J u) * hom (gevA J v) := by
  rw [hom_gevA, hom_gevA, hom_gevA, List.map_append, List.prod_append]

/-- The last (homogeneous) component of the value vector is `1` (the unit of the semiring, i.e. the arctic number 0). -/
theorem gvec_last (hd : 0 < d) (J : GLetter α → AffFun R d) (w : List (GLetter α)) :
    (hom (gevA J w) *ᵥ xs hd) (Fin.last d) = 1 := by
  rw [hom_mulVec_last]
  simp [xs]

/-- Splitting the value into the first symbol and the rest. -/
theorem gV_cons (hd : 0 < d) (J : GLetter α → AffFun R d) (s : GLetter α) (w : List (GLetter α)) :
    gV hd J (s :: w) = (hom (J s) *ᵥ (hom (gevA J w) *ᵥ xs hd)) (c0 hd) := by
  rw [gV, gevA_cons, hom_comp, Matrix.mulVec_mulVec]

end Alg

/-! ## Estimates along chains -/

section Order

variable {R : Type} [CommSemiring R] [LinearOrder R] [ArcticOrder R] {d : ℕ}

/-- A step by a rule of `U` (a rule weakly oriented coefficientwise) does not increase the value. -/
theorem gV_under (hd : 0 < d) (J : GLetter α → AffFun R d) {ρ : GDRule α}
    (hw : WeakA (gevA J ρ.lhs) (gevA J ρ.rhs)) (p q : List (GLetter α)) :
    gV hd J (p ++ ρ.rhs ++ q) ≤ gV hd J (p ++ ρ.lhs ++ q) := by
  unfold gV
  rw [hom_gevA_append, hom_gevA_append, hom_gevA_append, hom_gevA_append]
  refine ao_mulVec_mono ?_ (fun _ => le_rfl) _
  exact ao_mul_mono (ao_mul_mono (fun _ _ => le_rfl) (hom_le_of_weakA hw)) (fun _ _ => le_rfl)

/-- A weak root step by a dependency pair (first-row comparison) does not increase the value. -/
theorem gV_root_weak (hd : 0 < d) (J : GLetter α → AffFun R d) {π : GDRule α}
    (hw : WeakTop hd (gevA J π.lhs) (gevA J π.rhs)) (q : List (GLetter α)) :
    gV hd J (π.rhs ++ q) ≤ gV hd J (π.lhs ++ q) := by
  have hle := hom_top_le_of_weakTop hd hw
  unfold gV
  rw [hom_gevA_append, hom_gevA_append, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  generalize hom (gevA J q) *ᵥ xs hd = y
  simp only [Matrix.mulVec, dotProduct]
  exact ao_sum_mono _ (fun j _ => ArcticOrder.mul_mono (hle j) le_rfl)

/-- A strict root step by a dependency pair (first-row `≫`) decreases the value by `e` (the arctic number 1). -/
theorem gV_root_strict (hd : 0 < d) (J : GLetter α → AffFun R d) (e : R)
    (he : ∀ l r : R, GG l r → r * e ≤ l) {π : GDRule α}
    (hs : StrictTop hd (gevA J π.lhs) (gevA J π.rhs)) (q : List (GLetter α)) :
    gV hd J (π.rhs ++ q) * e ≤ gV hd J (π.lhs ++ q) := by
  have hgg := hom_top_gg_of_strictTop hd hs
  unfold gV
  rw [hom_gevA_append, hom_gevA_append, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  generalize hom (gevA J q) *ᵥ xs hd = y
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  refine ao_sum_mono _ (fun j _ => ?_)
  rw [mul_right_comm]
  exact ArcticOrder.mul_mono (he _ _ (hgg j)) le_rfl

/-- **Estimate along a chain**: if `U` is weakly oriented coefficientwise, `P` weakly in the first row, and `σ` strictly in the first row,
then the value decreases by `e` for each root use of `σ` in the chain. -/
theorem gV_chain [DecidableEq α] (hd : 0 < d) (J : GLetter α → AffFun R d) (e : R)
    (he : ∀ l r : R, GG l r → r * e ≤ l) {U P : List (GDRule α)}
    (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π ∈ P, WeakTop hd (gevA J π.lhs) (gevA J π.rhs))
    {σ : GDRule α} (hσ : StrictTop hd (gevA J σ.lhs) (gevA J σ.rhs)) :
    ∀ {es : List (GLabel α)} {u v : List (GLetter α)}, GDChain U P es u v →
      gV hd J v * e ^ (es.count (GLabel.root σ)) ≤ gV hd J u := by
  intro es u v hc
  induction hc with
  | nil w => simp
  | @under ρ es v p q hρ _ ih =>
    rw [List.count_cons_of_ne (by simp)]
    exact ih.trans (gV_under hd J (hU ρ hρ) p q)
  | @root π es v q hπ _ ih =>
    by_cases hπσ : π = σ
    · subst hπσ
      rw [List.count_cons_self, pow_succ, ← mul_assoc]
      exact (ArcticOrder.mul_mono ih le_rfl).trans (gV_root_strict hd J e he hσ q)
    · rw [List.count_cons_of_ne (by simpa using hπσ)]
      exact ih.trans (gV_root_weak hd J (hP π hπ) q)

/-- The value is at least the first component of the absolute part of the first symbol (the form of Koprowski–Waldmann 2009, Lemma 8.2). -/
theorem gV_ge_head (hd : 0 < d) (J : GLetter α → AffFun R d) (s : GLetter α)
    (w : List (GLetter α)) : (J s).c ⟨0, hd⟩ ≤ gV hd J (s :: w) := by
  rw [gV_cons]
  have := hom_mulVec_ge_c hd (J s) (hom (gevA J w) *ᵥ xs hd)
  rwa [gvec_last, mul_one] at this

end Order

/-! ## Finiteness over `𝔸_ℕ` -/

/-- Over `𝔸_ℕ`, if every symbol of the string is somewhere finite, the value is finite (Koprowski–Waldmann 2009, Lemma 6.2). -/
theorem gV_ne_zero {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun Arc d) :
    ∀ w : List (GLetter α),
      (∀ s ∈ w, (J s).c ⟨0, hd⟩ ≠ 0 ∨ (J s).M ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0) → gV hd J w ≠ 0 := by
  intro w
  induction w with
  | nil =>
    intro _
    rw [gV, gevA_nil, hom_id, Matrix.one_mulVec]
    simp only [xs, c0, Fin.lastCases_castSucc, ↓reduceIte]
    rw [Arc.ne_zero_iff]; simp
  | cons s w ih =>
    intro hw
    have hrest := ih (fun s' hs' => hw s' (List.mem_cons_of_mem _ hs'))
    rcases hw s List.mem_cons_self with hc | hM
    · exact Arc.ne_zero_of_le (gV_ge_head hd J s w) hc
    · rw [gV_cons]
      refine Arc.ne_zero_of_le (hom_mulVec_ge_M hd _ _) (Arc.mul_ne_zero' hM ?_)
      exact hrest

end Collatz.Arctic.DPGen
