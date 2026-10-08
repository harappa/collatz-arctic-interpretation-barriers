/-
Lean foundation of Section 8 (Section 8.1): the general form of Corollary 8.1 (non-increase on the steps of the family only).

Corollary 8.1: the proof of Theorem 6.8 uses the non-increase of the value only on the steps from a family point `x₀` to `x₁`.
In the generic layer of the Lean code, the assembly `Gen.specAutoRule` (`SpecAutoRule` in the frozen `Gen/Spec.lean`) holds for every
`BlockModel`, so it suffices to apply it to **the model `famModel M` whose domain is restricted to the points of family orbits**.

* `FamOrbit M x`: `x` is a point of a family orbit (`x = f^[i] (R β + 2^m t)` for some `β`, `t ≥ 1`, `i < steps β`).
  `famDom M x := FamOrbit M x ∧ M.dom x`.
* `famModel M`: the model with only the domain changed to `famDom M`. The field `orbit_dom` (points of family orbits lie in the domain) holds by definition,
  and `f_pos` follows from `f_pos` of the original model.
* `autoRuleG_family`: from `specAutoRule (famModel M)`, the form of `AutoRuleG` with the slope hypothesis only at points of family orbits.
  The points of the orbit segment in the conclusion are also points of family orbits.
* `autoRuleG_of_family`: the restricted form implies the original form (`famDom M ⊆ M.dom`). So the restricted form is a statement that contains the original one,
  with a weaker hypothesis (on the slope). That the inclusion is proper (`2` for $T$ and `8` for $H$ are points of the domain but not of family orbits) is
  `two_not_famDom` and `eight_not_famDom_H` in `FamilyInst.lean`.
* Bridge to the forms with the counting function as a parameter (`AutoUseG`, `HUseC`): in the list of rules `cdOf cnt n := replicate (cnt n) σ₀`
  the number of `σ₀` is exactly `cnt n` (`usesOrbitG_cdOf`). `autoUseG_family` (Corollary 8.1 with the counting function as a parameter) and
  `autoCoreG_of_use`, which feeds the barrier of `Gen/SysBridge`.

**Note**: one could assume only that the value does not increase over the passage (through whole blocks) from a family point `x₀` to `x₁`; the hypothesis here is
that no single step of `f` at a point of a family orbit increases the value by more than the slope `κ`. The latter is stronger, but condition (a) of the simulation lemma is a rewrite sequence for one step at each point,
so this form suffices for Lemma 5.6 (`Sim.lean`).
-/
import CollatzProof.Arctic.DPGen.Defs
import CollatzProof.Arctic.Gen.Final

namespace Collatz.Arctic.DPGen

open Collatz.Arctic Collatz.Arctic.Gen

/-! ## The model restricted to points of family orbits -/

/-- Points of family orbits: `x = f^[i] (R β + 2^m t)` for some `β`, `t ≥ 1`, `i < steps β`. -/
def FamOrbit (M : BlockModel) (x : ℕ) : Prop :=
  ∃ (β : List Bool) (t i : ℕ), 1 ≤ t ∧ i < M.steps β ∧
    x = M.f^[i] (M.R β + 2 ^ (parityOf β).length * t)

/-- The restricted domain: points of family orbits that lie in the original domain (the points where canonical derivations are used). -/
def famDom (M : BlockModel) (x : ℕ) : Prop := FamOrbit M x ∧ M.dom x

theorem famDom_sub (M : BlockModel) : ∀ x, famDom M x → M.dom x := fun _ h => h.2

/-- The model with domain restricted to points of family orbits (the other fields as in the original model). -/
def famModel (M : BlockModel) : BlockModel where
  f := M.f
  dom := famDom M
  steps := M.steps
  R := M.R
  C := M.C
  R_lt := M.R_lt
  C_lt := M.C_lt
  R_prefix := M.R_prefix
  iter := M.iter
  orbit_dom := fun β t ht i hi => ⟨⟨β, t, i, ht, hi, rfl⟩, M.orbit_dom β t ht i hi⟩
  f_pos := fun n hn => M.f_pos n hn.2

/-! ## The general form of Corollary 8.1 -/

/-- **General form of Corollary 8.1**: from the window frequencies and the uses of the rule `ρ`, the form of
`AutoRuleG` with the slope hypothesis **only at points of family orbits** (the points of the orbit segment in the conclusion are also points of family orbits). Apply `specAutoRule` to the restricted model. -/
theorem autoRuleG_family (M : BlockModel) (cd : ℕ → List Rule) (ρ : Rule) (hSP : HSP)
    (hTW : HTerrasWinR M.R) (hU : HUseR M.f M.R M.steps cd ρ) :
    AutoRuleG M.f (famDom M) cd ρ :=
  specAutoRule (famModel M) cd ρ hSP hTW hU

/-- The restricted form implies the original form: since `famDom M ⊆ M.dom`, its slope hypothesis is weaker and its condition on the orbit in the conclusion is stronger. -/
theorem autoRuleG_of_family (M : BlockModel) (cd : ℕ → List Rule) (ρ : Rule)
    (h : AutoRuleG M.f (famDom M) cd ρ) : AutoRuleG M.f M.dom cd ρ :=
  (autoRuleG_iff_use _ _ _ _).mpr
    (AutoUseG.dom_mono (famDom_sub M) ((autoRuleG_iff_use _ _ _ _).mp h))

/-! ## Bridge to the forms with the counting function as a parameter -/

/-- A dummy rule used as a marker for counting (the empty rule; its content is not used). -/
def σ₀ : Rule := ⟨[], []⟩

/-- The list of `cnt n` copies of the dummy rule (the number of `σ₀` is exactly `cnt n`). -/
def cdOf (cnt : ℕ → ℕ) (n : ℕ) : List Rule := List.replicate (cnt n) σ₀

theorem usesOrbitG_cdOf (f : ℕ → ℕ) (cnt : ℕ → ℕ) : usesOrbitG f (cdOf cnt) σ₀ = usesG f cnt := by
  funext n m
  simp [usesOrbitG, usesG, cdOf]

theorem hUseR_cdOf {f : ℕ → ℕ} {R steps : List Bool → ℕ} {cnt : ℕ → ℕ}
    (h : HUseC f R steps cnt) : HUseR f R steps (cdOf cnt) σ₀ := by
  unfold HUseR
  rw [usesOrbitG_cdOf]
  exact h

theorem autoUseG_of_cdOf {f : ℕ → ℕ} {dom : ℕ → Prop} {cnt : ℕ → ℕ}
    (h : AutoRuleG f dom (cdOf cnt) σ₀) : AutoUseG f dom cnt := by
  unfold AutoRuleG at h
  rw [usesOrbitG_cdOf] at h
  exact h

theorem autoRuleG_cdOf {f : ℕ → ℕ} {dom : ℕ → Prop} {cnt : ℕ → ℕ}
    (h : AutoUseG f dom cnt) : AutoRuleG f dom (cdOf cnt) σ₀ := by
  unfold AutoRuleG
  rw [usesOrbitG_cdOf]
  exact h

/-- From `AutoUseG`, the `AutoCoreG` for the single dummy rule (the form passed to the barrier of `Gen/SysBridge`). -/
theorem autoCoreG_of_use {f : ℕ → ℕ} {dom : ℕ → Prop} {cnt : ℕ → ℕ}
    (h : AutoUseG f dom cnt) : AutoCoreG f dom [σ₀] (cdOf cnt) :=
  autoCoreG_of_rules (fun ρ hρ => by
    rw [List.mem_singleton] at hρ
    subst hρ
    exact autoRuleG_cdOf h)

theorem count_cdOf (cnt : ℕ → ℕ) (n : ℕ) : (cdOf cnt n).count σ₀ = cnt n := by
  simp [cdOf]

/-- **Corollary 8.1, with the counting function as a parameter**: from the window frequencies and the lower bound on the sum of `cnt` along family orbits (`HUseC`),
the form of `AutoUseG` with the slope hypothesis only at points of family orbits. -/
theorem autoUseG_family (M : BlockModel) (cnt : ℕ → ℕ) (hSP : HSP) (hTW : HTerrasWinR M.R)
    (hU : HUseC M.f M.R M.steps cnt) : AutoUseG M.f (famDom M) cnt :=
  autoUseG_of_cdOf (autoRuleG_family M (cdOf cnt) σ₀ hSP hTW (hUseR_cdOf hU))

end Collatz.Arctic.DPGen
