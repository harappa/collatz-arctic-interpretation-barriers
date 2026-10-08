/-
Lean foundation of Section 8 (Section 8.1): carrying the dependency pair problems of $\mathcal T$ over to the general form.

The translation used in `STCheck.lean` to re-derive the frozen dependency pair theorems for $\mathcal T$ (`DPStatement.ArcticBarrierDP` etc.) as instances
of the general lemma (`Sim.lean`).

* Symbols `ofD : DLetter → GLetter Letter` (inverse `toD`), dependency pairs `ofDR : DRule → GDRule Letter`, interpretations `liftJ J := J ∘ toD`.
  The interpretation of strings is unchanged by the translation (`gevA_map_ofD`), so the comparisons `WeakA`, `WeakTop`, `StrictTop` are unchanged too.
* Rules `plainR ρ := ofDR ρ.plain` (rules of `U`), dependency pairs `dpR h ρ := ofDR (dp h ρ)` (the dependency pair of a root rule).
* `gV_eq_Vw`: the general value `gV` equals `DPBridge.Vw` (of the string after the marked symbol `h#`).
* `gdchain_of_dchain`: from a `DPBridge.DChain` (a chain on the strings after `h#`) to a general chain `GDChain`. If `σ ∉ U`, the number of `σ` in the original
  sequence is at most the number of root uses of `dpR h σ` in the general chain.
-/
import CollatzProof.Arctic.DPGen.Value

namespace Collatz.Arctic.DPGen

open Collatz.Arctic Matrix

/-! ## Translation of symbols, rules and interpretations -/

/-- `DLetter` to `GLetter Letter`. -/
def ofD : DLetter → GLetter Letter
  | .mark s => .mark s
  | .plain s => .plain s

/-- `GLetter Letter` to `DLetter`. -/
def toD : GLetter Letter → DLetter
  | .mark s => .mark s
  | .plain s => .plain s

theorem toD_ofD (s : DLetter) : toD (ofD s) = s := by cases s <;> rfl

/-- Translation of dependency pairs and rules. -/
def ofDR (r : DRule) : GDRule Letter := ⟨r.lhs.map ofD, r.rhs.map ofD⟩

/-- Translation of interpretations. -/
def liftJ {R : Type} {d : ℕ} (J : DLetter → AffFun R d) : GLetter Letter → AffFun R d :=
  fun g => J (toD g)

/-- Rules of `U` (unmarked rules). -/
def plainR (ρ : Rule) : GDRule Letter := ofDR ρ.plain

/-- The dependency pair `h# ⋯` of a root rule `ρ`. -/
def dpR (h : Letter) (ρ : Rule) : GDRule Letter := ofDR (dp h ρ)

section Interp

variable {R : Type} [CommSemiring R] {d : ℕ}

/-- The interpretation of strings is unchanged by the translation. -/
theorem gevA_map_ofD (J : DLetter → AffFun R d) (w : List DLetter) :
    gevA (liftJ J) (w.map ofD) = evA J w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    show (liftJ J (ofD s)).comp (gevA (liftJ J) (w.map ofD)) = (J s).comp (evA J w)
    rw [ih]
    simp only [liftJ, toD_ofD]

theorem weakA_ofDR [LE R] (J : DLetter → AffFun R d) (r : DRule) :
    WeakA (gevA (liftJ J) (ofDR r).lhs) (gevA (liftJ J) (ofDR r).rhs) ↔
      WeakA (evA J r.lhs) (evA J r.rhs) := by
  simp only [ofDR, gevA_map_ofD]

theorem weakTop_ofDR [LE R] (hd : 0 < d) (J : DLetter → AffFun R d) (r : DRule) :
    WeakTop hd (gevA (liftJ J) (ofDR r).lhs) (gevA (liftJ J) (ofDR r).rhs) ↔
      WeakTop hd (evA J r.lhs) (evA J r.rhs) := by
  simp only [ofDR, gevA_map_ofD]

theorem strictTop_ofDR [LT R] (hd : 0 < d) (J : DLetter → AffFun R d) (r : DRule) :
    StrictTop hd (gevA (liftJ J) (ofDR r).lhs) (gevA (liftJ J) (ofDR r).rhs) ↔
      StrictTop hd (evA J r.lhs) (evA J r.rhs) := by
  simp only [ofDR, gevA_map_ofD]

/-- The homogeneous coordinates of an unmarked string are `evR (homL J)`. -/
theorem hom_gevA_plain (J : DLetter → AffFun R d) (w : Word) :
    hom (gevA (liftJ J) (w.map GLetter.plain)) = evR (homL J) w := by
  rw [hom_gevA, List.map_map]
  rfl

/-- The general value equals `Vw` (the value of the string after `h#`). -/
theorem gV_eq_Vw (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter) (w : Word) :
    gV hd (liftJ J) (GLetter.mark h :: w.map GLetter.plain) = Vw hd J h w := by
  rw [gV_cons, hom_gevA_plain, Vw_eq_mulVec]
  rfl

end Interp

/-! ## Translation of chains -/

theorem plainR_lhs (ρ : Rule) : (plainR ρ).lhs = ρ.lhs.map GLetter.plain := by
  simp [plainR, ofDR, Rule.plain, Function.comp_def, ofD]

theorem plainR_rhs (ρ : Rule) : (plainR ρ).rhs = ρ.rhs.map GLetter.plain := by
  simp [plainR, ofDR, Rule.plain, Function.comp_def, ofD]

theorem dpR_lhs (h : Letter) (ρ : Rule) :
    (dpR h ρ).lhs = GLetter.mark h :: ρ.lhs.tail.map GLetter.plain := by
  simp [dpR, ofDR, dp, Function.comp_def, ofD]

theorem dpR_rhs (h : Letter) (ρ : Rule) :
    (dpR h ρ).rhs = GLetter.mark h :: ρ.rhs.tail.map GLetter.plain := by
  simp [dpR, ofDR, dp, Function.comp_def, ofD]

/-- **Translation of chains**: from a `DChain U P` on the strings after `h#`, a general chain with `h#` in front. If `σ ∉ U`, the number of `σ` in the original sequence
is at most the number of root uses of `dpR h σ` in the general chain. -/
theorem gdchain_of_dchain {U P : List Rule} (h : Letter) {σ : Rule} (hσU : σ ∉ U) :
    ∀ {rs : List Rule} {u v : Word}, DChain U P rs u v →
      ∃ es, GDChain (U.map plainR) (P.map (dpR h)) es (GLetter.mark h :: u.map GLetter.plain)
        (GLetter.mark h :: v.map GLetter.plain) ∧
        rs.count σ ≤ es.count (GLabel.root (dpR h σ)) := by
  intro rs u v hc
  induction hc with
  | nil w => exact ⟨[], GDChain.nil _, by simp⟩
  | @under ρ rs u w v hρ hstep _ ih =>
    obtain ⟨es, hch, hle⟩ := ih
    obtain ⟨p, q, rfl, rfl⟩ := hstep
    refine ⟨GLabel.under (plainR ρ) :: es, ?_, ?_⟩
    · have e1 : GLetter.mark h :: (p ++ ρ.lhs ++ q).map GLetter.plain =
          (GLetter.mark h :: p.map GLetter.plain) ++ (plainR ρ).lhs ++ q.map GLetter.plain := by
        simp [plainR_lhs]
      have e2 : GLetter.mark h :: (p ++ ρ.rhs ++ q).map GLetter.plain =
          (GLetter.mark h :: p.map GLetter.plain) ++ (plainR ρ).rhs ++ q.map GLetter.plain := by
        simp [plainR_rhs]
      rw [e1]
      rw [e2] at hch
      exact GDChain.under _ _ (List.mem_map_of_mem hρ) hch
    · have hne : ρ ≠ σ := fun heq => hσU (heq ▸ hρ)
      rw [List.count_cons_of_ne hne, List.count_cons_of_ne (by simp)]
      exact hle
  | @root ρ rs q v hρ _ ih =>
    obtain ⟨es, hch, hle⟩ := ih
    refine ⟨GLabel.root (dpR h ρ) :: es, ?_, ?_⟩
    · have e1 : GLetter.mark h :: (ρ.lhs.tail ++ q).map GLetter.plain =
          (dpR h ρ).lhs ++ q.map GLetter.plain := by
        simp [dpR_lhs]
      have e2 : GLetter.mark h :: (ρ.rhs.tail ++ q).map GLetter.plain =
          (dpR h ρ).rhs ++ q.map GLetter.plain := by
        simp [dpR_rhs]
      rw [e1]
      rw [e2] at hch
      exact GDChain.root _ (List.mem_map_of_mem hρ) hch
    · by_cases hρσ : ρ = σ
      · subst hρσ
        rw [List.count_cons_self, List.count_cons_self]
        omega
      · rw [List.count_cons_of_ne hρσ]
        exact le_trans hle List.count_le_count_cons

end Collatz.Arctic.DPGen
