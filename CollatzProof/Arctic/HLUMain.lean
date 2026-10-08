/-
Proof of the hypothesis `HLeftUse` (Proposition B.9 (ii); the left-end rules in Proposition 6.7):
the log of the mantissa of the block boundary points is `{a_i log₂3 + log₂ t}`, and the random walk with steps `5 log₂3`, `7 log₂3`
enters each of the three arcs at least `c k` times, simultaneously for every `t`.
* Deterministic part: `HLUDet`, `HLUDetReal` (`left_use_ge_sum`: number of boundary points in an arc ≤ number of uses of the left-end rule).
* Probabilistic part: `HLUWalk`, `HLUWalk2` (`walk_equid`: simultaneously for every translation `φ`, at least `c k` visits to the arc).
-/
import CollatzProof.Arctic.HLUWalk2
import CollatzProof.Arctic.HLUDetReal
import CollatzProof.Arctic.CoreHelp
import CollatzProof.Arctic.CoreProb

namespace Collatz.Arctic

open Classical

/-- `Prσ` is monotone in the event (over the choices of the remaining `k` blocks). -/
theorem Prσ_mono (β₀ : List Bool) (k : ℕ) {E F : List Bool → Prop}
    (h : ∀ β ∈ blockChoices k, E (β₀ ++ β) → F (β₀ ++ β)) :
    Prσ β₀ k E ≤ Prσ β₀ k F := by
  unfold Prσ
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro β hβ
    simp only [Finset.mem_filter] at hβ ⊢
    exact ⟨hβ.1, h _ hβ.1 hβ.2⟩
  · intro β _ _
    exact fam_wt_nonneg β

/-- **Proof of the hypothesis `HLeftUse`**. -/
theorem hLeftUse : HLeftUse := by
  intro β₀
  set η : ℝ := 1 / 100 with hη
  have hη0 : 0 < η := by norm_num
  obtain ⟨m₀, hm₀⟩ := left_use_ge_sum η hη0
  -- equidistribution for each of the three arcs
  have harc : ∀ d ≤ 2, ∃ c : ℚ, 0 < c ∧ ∀ (β₀ : List Bool) (ε : ℚ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      1 - ε ≤ Prσ β₀ k (fun β => ∀ φ : ℝ, (c : ℝ) * k ≤
        (((Finset.range β.length).filter (fun i =>
          arcLo d η ≤ Int.fract ((oddPrefix β i : ℝ) * Real.logb 2 3 + φ) ∧
          Int.fract ((oddPrefix β i : ℝ) * Real.logb 2 3 + φ) < arcHi d η)).card : ℝ)) := by
    intro d hd
    exact walk_equid (arcLo d η) (arcHi d η) (hlu_arcLo_nonneg d η hη0.le)
      (hlu_arc_nonempty d hd η (by norm_num)) (hlu_arcHi_le_one d hd η hη0.le)
  obtain ⟨c0, hc0, h0⟩ := harc 0 (by norm_num)
  obtain ⟨c1, hc1, h1⟩ := harc 1 (by norm_num)
  obtain ⟨c2, hc2, h2⟩ := harc 2 (by norm_num)
  refine ⟨min c0 (min c1 c2), lt_min hc0 (lt_min hc1 hc2), fun ε hε => ?_⟩
  obtain ⟨k0, hk0⟩ := h0 β₀ ε hε
  obtain ⟨k1, hk1⟩ := h1 β₀ ε hε
  obtain ⟨k2, hk2⟩ := h2 β₀ ε hε
  refine ⟨max (max k0 k1) (max k2 m₀), fun k hk d hd => ?_⟩
  have hcd : ∃ cd : ℚ, min c0 (min c1 c2) ≤ cd ∧ 1 - ε ≤ Prσ β₀ k (fun β => ∀ φ : ℝ, (cd : ℝ) * k ≤
        (((Finset.range β.length).filter (fun i =>
          arcLo d η ≤ Int.fract ((oddPrefix β i : ℝ) * Real.logb 2 3 + φ) ∧
          Int.fract ((oddPrefix β i : ℝ) * Real.logb 2 3 + φ) < arcHi d η)).card : ℝ)) := by
    interval_cases d
    · exact ⟨c0, min_le_left _ _, hk0 k (by omega)⟩
    · exact ⟨c1, le_trans (min_le_right _ _) (min_le_left _ _), hk1 k (by omega)⟩
    · exact ⟨c2, le_trans (min_le_right _ _) (min_le_right _ _), hk2 k (by omega)⟩
  obtain ⟨cd, hcd, hpr⟩ := hcd
  refine le_trans hpr (Prσ_mono β₀ k (fun β hβk hβ t ht => ?_))
  -- lower bound on the length: `m ≥ 8 (|β₀| + k) ≥ m₀`
  have hlen : (β₀ ++ β).length = β₀.length + k := by
    rw [List.length_append, length_of_mem_blockChoices hβk]
  have hm8 := (parityOf_length_bounds (β₀ ++ β)).1
  have hm : m₀ ≤ (parityOf (β₀ ++ β)).length := by rw [hlen] at hm8; omega
  have hdet := hm₀ (β₀ ++ β) t d hm ht hd
  have hwalk := hβ (Real.logb 2 t)
  have hdet' : ((Finset.range (β₀ ++ β).length).filter (fun i =>
      arcLo d η ≤ Int.fract ((oddPrefix (β₀ ++ β) i : ℝ) * Real.logb 2 3 + Real.logb 2 t) ∧
      Int.fract ((oddPrefix (β₀ ++ β) i : ℝ) * Real.logb 2 3 + Real.logb 2 t) < arcHi d η)).card ≤
      usesOrbit (leftRule d) (terrasR (parityOf (β₀ ++ β)) + 2 ^ (parityOf (β₀ ++ β)).length * t)
        (parityOf (β₀ ++ β)).length := hdet
  have hcard := (Nat.cast_le (α := ℝ)).mpr hdet'
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hcdR : ((min c0 (min c1 c2) : ℚ) : ℝ) ≤ (cd : ℝ) := by exact_mod_cast hcd
  have hfin : ((min c0 (min c1 c2) : ℚ) : ℝ) * k ≤
      (usesOrbit (leftRule d) (terrasR (parityOf (β₀ ++ β)) + 2 ^ (parityOf (β₀ ++ β)).length * t)
        (parityOf (β₀ ++ β)).length : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hcdR hk0) (le_trans hwalk hcard)
  exact_mod_cast hfin

end Collatz.Arctic
