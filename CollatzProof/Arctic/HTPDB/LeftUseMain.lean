/-
Uses of the left-end rules of the system $\mathcal H$, part 3: the main theorem.
Proves **`specLeftUseH : SpecLeftUseH`** (the statement of the frozen `HTPDB/Spec.lean`).

Adapted from `HLUMain.lean` for $T$ (`hLeftUse`, `Prσ_mono`).

Correspondence with the paper: the $H$ version of the left-end part of the proof of Proposition 6.7 (ii) (Section 7). The logarithm of the mantissa of a block boundary point (a step $\mathsf a$) is
`{a_i log₂ 3 + log₂ t}`, where `a_i` is the sum of the exponents of 3 of the blocks ($X = \mathsf{abb}$: 5, $Y = \mathsf{abbb}$: 7; the same as the numbers of odd steps of
$X'$, $Y'$ for $T$). Hence the equidistribution of the random walk with steps `5 log₂ 3`, `7 log₂ 3`,
`HLUWalk2.walk_equid` (Proposition B.9, independent of the system), applies as it is, and the walk enters the arc `J_d` at least `c k` times, simultaneously for all `t`.
* Deterministic part: `LeftUse`, `LeftUseReal` (`left_use_ge_sumH`: the number of boundary points in the arc ≤ the number of uses of the left-end rule).
* Hypotheses: the interface statements `SpecHModel`, `SpecHClass`, `SpecHBoundary` of the model of $H$ (taken as hypotheses, independently of their proofs).
* Unlike `hLeftUse` for $T$, `HUseR` is stated rule by rule, so the constant `c` is chosen for each `d`.
-/
import CollatzProof.Arctic.HTPDB.LeftUseReal
import CollatzProof.Arctic.HLUWalk2

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel

open Classical in
/-- `Prσ` is monotone in the event (over the choices of the remaining `k` blocks; copied from `HLUMain.Prσ_mono` for $T$). -/
theorem hluH_Prσ_mono (β₀ : List Bool) (k : ℕ) {E F : List Bool → Prop}
    (h : ∀ β ∈ blockChoices k, E (β₀ ++ β) → F (β₀ ++ β)) :
    Prσ β₀ k E ≤ Prσ β₀ k F := by
  unfold Prσ
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro β hβ
    simp only [Finset.mem_filter] at hβ ⊢
    exact ⟨hβ.1, h _ hβ.1 hβ.2⟩
  · intro β _ _
    exact fam_wt_nonneg β

/-- The elements of `blockChoices k` have length `k` (copied from `CoreProb.length_of_mem_blockChoices`). -/
lemma hluH_length_of_mem_blockChoices {k : ℕ} {β : List Bool} (h : β ∈ blockChoices k) :
    β.length = k := by
  unfold blockChoices at h
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp h
  simp

/-- **Uses of the left-end rules** (the $H$ version of `hLeftUse` for $T$, rule by rule): under `SpecHModel`, `SpecHClass` and
`SpecHBoundary`, the left-end rule `leftRule d` (`d ≤ 2`) is used at least `c k` times along the orbits of the family with probability close to 1. -/
theorem hUse_left (hM : SpecHModel) (hC : SpecHClass) (hB : SpecHBoundary) (d : ℕ) (hd : d ≤ 2) :
    Gen.HUseR Hmap hR hSteps canDerivH (leftRule d) := by
  intro β₀
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / 100 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; norm_num
  obtain ⟨m₀, hm₀⟩ := left_use_ge_sumH hM hC hB η hη0
  -- Equidistribution in the arc `J_d` (simultaneously for all translations `φ`)
  obtain ⟨c, hc, hw⟩ := walk_equid (arcLo d η) (arcHi d η) (hlu_arcLo_nonneg d η hη0.le)
    (hlu_arc_nonempty d hd η (by rw [hηdef]; norm_num)) (hlu_arcHi_le_one d hd η hη0.le)
  refine ⟨c, hc, fun ε hε => ?_⟩
  obtain ⟨k₁, hk₁⟩ := hw β₀ ε hε
  refine ⟨max k₁ m₀, fun k hk => ?_⟩
  refine le_trans (hk₁ k (le_trans (le_max_left _ _) hk))
    (hluH_Prσ_mono β₀ k (fun β hβk hβ t ht => ?_))
  -- Lower bound for the length: `m ≥ 8 (|β₀| + k) ≥ m₀`
  have hlen : (β₀ ++ β).length = β₀.length + k := by
    rw [List.length_append, hluH_length_of_mem_blockChoices hβk]
  have hm8 := hlu_parityOf_length_ge (β₀ ++ β)
  have hkm : m₀ ≤ k := le_trans (le_max_right _ _) hk
  have hm : m₀ ≤ (parityOf (β₀ ++ β)).length := by rw [hlen] at hm8; omega
  have hdet := hm₀ (β₀ ++ β) t d hm ht hd
  have hwalk := hβ (Real.logb 2 t)
  have hdet' : ((Finset.range (β₀ ++ β).length).filter (fun i =>
      arcLo d η ≤ Int.fract ((oddPrefix (β₀ ++ β) i : ℝ) * Real.logb 2 3 + Real.logb 2 t) ∧
      Int.fract ((oddPrefix (β₀ ++ β) i : ℝ) * Real.logb 2 3 + Real.logb 2 t) < arcHi d η)).card ≤
      Gen.usesOrbitG Hmap canDerivH (leftRule d) (hR (β₀ ++ β) + 2 ^ (parityOf (β₀ ++ β)).length * t)
        (hSteps (β₀ ++ β)) := hdet
  have hcard := (Nat.cast_le (α := ℝ)).mpr hdet'
  have hfin : (c : ℝ) * k ≤
      (Gen.usesOrbitG Hmap canDerivH (leftRule d) (hR (β₀ ++ β) + 2 ^ (parityOf (β₀ ++ β)).length * t)
        (hSteps (β₀ ++ β)) : ℝ) :=
    le_trans hwalk hcard
  exact_mod_cast hfin

/-- **Output on the left-end rules** (the frozen statement `SpecLeftUseH`). -/
theorem specLeftUseH : SpecLeftUseH :=
  fun hM hC hB d hd => hUse_left hM hC hB d hd

end Collatz.Arctic.HTPDB
