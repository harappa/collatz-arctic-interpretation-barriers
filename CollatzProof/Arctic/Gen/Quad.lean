/-
General form of deriving the conclusion of `AutoCore` from quadratic use of a carry rule: copies of `ARuleMain.autoCore_aRule`,
`ARuleFamily.family_bound` and `quad_of_family` for $T$, with the map `f`, the domain `dom` and the canonical derivation `cd`
as arguments.

* `Gen.autoRuleG_of_quad` (the proof `Gen.specQuadRule` of the frozen `Gen.SpecQuadRule`): from `QuadR f dom cd ρ` (there are orbit segments whose number of uses
  exceeds any linear function of the length of the starting point), `AutoRuleG f dom cd ρ`. The values of an automaton are bounded by a linear function of the length
  (`ARule.autoVal_le`, independent of the system), so neither the finiteness of values nor that values do not increase is used (the value side
  of Proposition 3.7).
* `Gen.Quad.quad_of_familyG` (the family framework): if a point family `R k` (points of `R (k+1)` move to `R k` in `s` steps, the intermediate points lie in
  the domain, and the canonical derivation of a point of `R (k+1)` uses `ρ` at least `k` times) has a point of length at most `a k + b` at each stage, then `QuadR`.
  The framework for $T$ fixed the length to `12 k + 12`. The families for $H$ (`HTPDB/ARule.lean`, `HTPDB/ARuleFive.lean`) have `a = b = 20`.
-/
import CollatzProof.Arctic.Gen.Spec
import CollatzProof.Arctic.ARuleMain

namespace Collatz.Arctic.Gen

open Collatz.Arctic

namespace Quad

/-! ## Number of uses on orbit segments -/

lemma usesOrbitG_zero (f : ℕ → ℕ) (cd : ℕ → List Rule) (ρ : Rule) (n : ℕ) :
    usesOrbitG f cd ρ n 0 = 0 := by
  simp [usesOrbitG]

/-- Split a segment into its first point and the rest (the general form of `Main.usesOrbit_succ`). -/
lemma usesOrbitG_succ (f : ℕ → ℕ) (cd : ℕ → List Rule) (ρ : Rule) (n m : ℕ) :
    usesOrbitG f cd ρ n (m + 1) = (cd n).count ρ + usesOrbitG f cd ρ (f n) m := by
  simp only [usesOrbitG, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  congr 2

/-- Concatenation of segments (the general form of `ARuleFamily.usesOrbit_add`). -/
lemma usesOrbitG_add (f : ℕ → ℕ) (cd : ℕ → List Rule) (ρ : Rule) : ∀ (a n b : ℕ),
    usesOrbitG f cd ρ n (a + b) = usesOrbitG f cd ρ n a + usesOrbitG f cd ρ (f^[a] n) b := by
  intro a
  induction a with
  | zero => intro n b; simp [usesOrbitG_zero]
  | succ a ih =>
    intro n b
    rw [show a + 1 + b = (a + b) + 1 by omega, usesOrbitG_succ, usesOrbitG_succ, ih,
      Function.iterate_succ_apply]
    ring

lemma count_le_usesOrbitG (f : ℕ → ℕ) (cd : ℕ → List Rule) (ρ : Rule) (n s : ℕ) (hs : 1 ≤ s) :
    (cd n).count ρ ≤ usesOrbitG f cd ρ n s := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [usesOrbitG_succ]; omega

/-- Concatenation of orbit segments lying in the domain. -/
lemma orbit_appendG {f : ℕ → ℕ} {dom : ℕ → Prop} {n a b : ℕ} (h1 : ∀ i < a, dom (f^[i] n))
    (h2 : ∀ i < b, dom (f^[i] (f^[a] n))) : ∀ i < a + b, dom (f^[i] n) := by
  intro i hi
  by_cases hia : i < a
  · exact h1 i hia
  · have := h2 (i - a) (by omega)
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)] at this

/-- The form of `orbit_appendG` taking the intermediate point as an equation (for the same reason as `ARuleFamily.orbit_append'`: rewriting the iterate with `rw`
may unfold the map in definitional comparisons and not terminate). -/
lemma orbit_appendG' {f : ℕ → ℕ} {dom : ℕ → Prop} {n a b m : ℕ} (h1 : ∀ i < a, dom (f^[i] n))
    (he : f^[a] n = m) (h2 : ∀ i < b, dom (f^[i] m)) : ∀ i < a + b, dom (f^[i] n) :=
  orbit_appendG h1 (fun i hi => he ▸ h2 i hi)

/-! ## The family framework -/

/-- Quadratic lower bound on the family (the general form of `ARuleFamily.family_bound`): the segment of `s k` steps from a point of `R k n` has all its points
in the domain and uses `ρ` at least `k(k-1)/2` times. -/
theorem family_boundG {f : ℕ → ℕ} {dom : ℕ → Prop} {cd : ℕ → List Rule} {ρ : Rule} {s : ℕ}
    {R : ℕ → ℕ → Prop} (hs : 1 ≤ s)
    (hstep : ∀ k n, R (k + 1) n → R k (f^[s] n))
    (horb : ∀ k n, R (k + 1) n → ∀ i < s, dom (f^[i] n))
    (huse : ∀ k n, R (k + 1) n → k ≤ (cd n).count ρ) :
    ∀ k n, R k n → (∀ i < s * k, dom (f^[i] n)) ∧ k * k ≤ 2 * usesOrbitG f cd ρ n (s * k) + k := by
  intro k
  induction k with
  | zero => intro n _; simp
  | succ k ih =>
    intro n hR
    obtain ⟨h1, h2⟩ := ih (f^[s] n) (hstep k n hR)
    rw [show s * (k + 1) = s + s * k by ring]
    refine ⟨orbit_appendG (horb k n hR) h1, ?_⟩
    rw [usesOrbitG_add]
    have := huse k n hR
    have := count_le_usesOrbitG f cd ρ n s hs
    nlinarith

/-- **The family framework** (the general form of `ARuleFamily.quad_of_family`): if each stage `k` of the family has a point `≥ k` of length at most `a k + b`,
then orbit segments in which the number of uses of `ρ` exceeds any linear function of the length of the starting point can be taken with starting points `≥ N`. -/
theorem quad_of_familyG {f : ℕ → ℕ} {dom : ℕ → Prop} {cd : ℕ → List Rule} {ρ : Rule} {s a b : ℕ}
    {R : ℕ → ℕ → Prop} (hs : 1 ≤ s)
    (hstep : ∀ k n, R (k + 1) n → R k (f^[s] n))
    (horb : ∀ k n, R (k + 1) n → ∀ i < s, dom (f^[i] n))
    (huse : ∀ k n, R (k + 1) n → k ≤ (cd n).count ρ)
    (hex : ∀ k, ∃ n, k ≤ n ∧ R k n ∧ lenT n ≤ a * k + b) : QuadR f dom cd ρ := by
  intro C N
  set k := N + 2 * (C * a) + 2 * (C * (b + 1)) + 2 with hk
  obtain ⟨n, hkn, hR, hlen⟩ := hex k
  obtain ⟨horb', huses⟩ := family_boundG hs hstep horb huse k n hR
  refine ⟨n, by omega, _, horb', ?_⟩
  set U := usesOrbitG f cd ρ n (s * k) with hU
  -- `C (lenT n + 1) ≤ C a k + C (b + 1)`
  have h1 : C * (lenT n + 1) ≤ C * a * k + C * (b + 1) := by
    have : C * (lenT n + 1) ≤ C * (a * k + b + 1) := Nat.mul_le_mul_left _ (by omega)
    calc C * (lenT n + 1) ≤ C * (a * k + b + 1) := this
      _ = C * a * k + C * (b + 1) := by ring
  -- `k² ≥ (2 C a + 2 C (b + 1) + 2) k`
  have h2 : (2 * (C * a) + 2 * (C * (b + 1)) + 2) * k ≤ k * k :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : C * (b + 1) ≤ C * (b + 1) * k := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : (2 * (C * a) + 2 * (C * (b + 1)) + 2) * k
      = 2 * (C * a * k) + 2 * (C * (b + 1) * k) + 2 * k := by ring
  omega

end Quad

/-! ## `AutoRuleG` from a linear upper bound for values and quadratic use -/

/-- **General form of the conclusion of `AutoCore` for carry rules** (a copy of `ARuleMain.autoCore_aRule`): if one can take orbit segments in which the number of uses of `ρ` exceeds any
linear function of the length of the starting point, the conclusion holds for every automaton `(u, A, c)` and every slope `κ`.
Values are bounded by a linear function of the length (`ARule.autoVal_le`), so the two hypotheses of `AutoRuleG` (finiteness of values, values do not increase)
are not used. -/
theorem autoRuleG_of_quad (f : ℕ → ℕ) (dom : ℕ → Prop) (cd : ℕ → List Rule) (ρ : Rule)
    (hq : QuadR f dom cd ρ) : AutoRuleG f dom cd ρ := by
  intro D u A c κ _ _ N
  set B := ARule.vecBound u + ARule.vecBound c + ARule.digBound A with hB
  obtain ⟨n, hN, m, horb, hlt⟩ := hq (B + 1) N
  refine ⟨n, hN, m, horb, lt_of_le_of_lt (ARule.autoVal_le u A c n) (Arc.fin_lt_fin.mpr ?_)⟩
  have h1 : ARule.digBound A * lenT n ≤ B * lenT n := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **Output for the carry rules (general part)**: the frozen `SpecQuadRule`. -/
theorem specQuadRule : SpecQuadRule :=
  fun f dom cd ρ hq => autoRuleG_of_quad f dom cd ρ hq

end Collatz.Arctic.Gen
