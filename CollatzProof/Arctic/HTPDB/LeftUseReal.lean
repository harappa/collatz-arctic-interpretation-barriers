/-
Uses of the left-end rules of the system $\mathcal H$, part 2: the decision on the mantissa of the boundary points, and
the lower bound `left_use_geH` for the number of uses of the left-end rules. The combinatorial part is in `LeftUse.lean`.

Adapted from `HLUDetReal.lean` for $T$ (`hlu_crit`, `hlu_boundary_crit`, `left_use_ge`, `left_use_ge_sum`) and
`hlu_P_bounds` of `HLUDet.lean`.

Correspondence with the paper: the $H$ version of the left-end part of the proof of Proposition 6.7 (ii) (Section 7). The digit reaching the left end at a point `P` of a step $\mathsf a$ is
`⌊3 mant(P)⌋ - 3` (unlike for $T$, without the correction `+1`).
* `hluH_crit`: if `P ≡ 0 (mod 4)`, `L ≥ 2` and `(3+d) 2^L ≤ 3P + 1 < (4+d) 2^L`, then the top window of `y = P/4`,
  `3y / 2^{⌊log₂ y⌋}`, is `3 + d`. The real estimate `hlu_real` for $T$ (the decision for `3x + 1`) is used as it is; since `3P ≡ 0 (mod 4)`,
  the `+1` at the lower end has no effect (`(3+d) 2^L ≤ 3P + 1` gives `(3+d) 2^L ≤ 3P`). This gives the form of `hlu_real`
  without the `+1`.
* `hluH_P_bounds`: from `SpecHBoundary` and `SpecHModel.C_lt`, `3^{a_i} 2^{m-L_i} t ≤ P_i < 3^{a_i} 2^{m-L_i}(t+1)`
  (`L_i = blockEnd β i` is a number of bits, `m - L_i ≥ 8`).
* `hluH_boundary_crit`, **`left_use_geH`**: for `m ≥ m₀(η)` and `t ≥ 2^m`, the number of boundary indices `i` with `{a_i log₂ 3 + log₂ t} ∈ J_d`
  is at most the number of uses of `leftRule d` in the `hSteps β` steps from `x₀` (`left_use_ge_sumH` is the form with `a_i` written as the sum of the exponents
  of 3 of the blocks, `Σ (5 or 7)`, i.e. as `HLUWalk.oddPrefix`; the step sizes are the same as for $T$).
-/
import CollatzProof.Arctic.HTPDB.LeftUse
import CollatzProof.Arctic.HLUDetReal

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel

/-! ## Decision for natural numbers -/

/-- Decision for natural numbers (a step $\mathsf a$ of $H$): if `x ≡ 0 (mod 4)`, `L ≥ 2` and `(3+d) 2^L ≤ 3x + 1 < (4+d) 2^L`, then
`3 (x/4) / 2^{⌊log₂ (x/4)⌋} = 3 + d`. -/
lemma hluH_crit (x d L : ℕ) (hx : x % 4 = 0) (hd : d ≤ 2) (hL : 2 ≤ L)
    (h1 : (3 + d) * 2 ^ L ≤ 3 * x + 1) (h2 : 3 * x + 1 < (4 + d) * 2 ^ L) :
    3 * (x / 4) / 2 ^ Nat.log 2 (x / 4) = 3 + d := by
  have hP : 2 ^ L = 4 * 2 ^ (L - 2) := by
    obtain ⟨j, rfl⟩ : ∃ j, L = j + 2 := ⟨L - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]
    ring
  have hxy : x = 4 * (x / 4) := by omega
  generalize x / 4 = y at hxy ⊢
  generalize hQ : 2 ^ (L - 2) = Q at hP
  have hQ1 : 1 ≤ Q := by rw [← hQ]; exact Nat.one_le_two_pow
  rw [hP, hxy] at h1 h2
  have g1 : (3 + d) * Q ≤ 3 * y := by interval_cases d <;> omega
  have g2 : 3 * y < (4 + d) * Q := by interval_cases d <;> omega
  have hlog : Nat.log 2 y = L - 2 := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · rw [hQ]; interval_cases d <;> omega
    · rw [pow_succ, hQ]; interval_cases d <;> omega
  rw [hlog, hQ]
  exact Nat.div_eq_of_lt_le g1 (by rw [show 3 + d + 1 = 4 + d by omega]; exact g2)

/-! ## The form of the boundary points -/

/-- Bounds for the boundary points: `3^{a_i} 2^{m - L_i} t ≤ P_i < 3^{a_i} 2^{m - L_i} (t + 1)` (from `SpecHBoundary` and
`SpecHModel.C_lt`; the same as `hlu_P_bounds` for $T$). -/
theorem hluH_P_bounds (hM : SpecHModel) (hB : SpecHBoundary) (β : List Bool) (t i : ℕ)
    (hi : i < β.length) :
    3 ^ terrasA (parityOf (β.take i)) * 2 ^ ((parityOf β).length - blockEnd β i) * t
        ≤ Hmap^[hSteps (β.take i)] (hR β + 2 ^ (parityOf β).length * t) ∧
      Hmap^[hSteps (β.take i)] (hR β + 2 ^ (parityOf β).length * t)
        < 3 ^ terrasA (parityOf (β.take i)) * 2 ^ ((parityOf β).length - blockEnd β i) * (t + 1) := by
  obtain ⟨r', hr', hP⟩ := hB β t i hi
  rw [hP]
  have hc := hM.C_lt (β.take i)
  generalize hC (β.take i) = c at hc ⊢
  generalize 3 ^ terrasA (parityOf (β.take i)) = a at hc ⊢
  generalize 2 ^ ((parityOf β).length - blockEnd β i) = q at hr' ⊢
  have h1 : a * (r' + 1) ≤ a * q := Nat.mul_le_mul_left _ hr'
  constructor
  · nlinarith
  · nlinarith

/-! ## Decision at the boundary points, and the lower bound -/

/-- **Decision at the boundary points**: for `m ≥ m₀(η)` and `t ≥ 2^m`, at a boundary index `i` with `{a_i log₂ 3 + log₂ t} ∈ J_d`,
the top window of `y = P_i/4` for the boundary point `P_i` is `3 + d`. -/
theorem hluH_boundary_crit (hM : SpecHModel) (hC : SpecHClass) (hB : SpecHBoundary) (η : ℝ) (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ (β : List Bool) (t d i : ℕ),
    m₀ ≤ (parityOf β).length → 2 ^ (parityOf β).length ≤ t → d ≤ 2 → i < β.length →
    arcLo d η ≤ Int.fract ((terrasA (parityOf (β.take i)) : ℝ) * Real.logb 2 3 + Real.logb 2 t) →
    Int.fract ((terrasA (parityOf (β.take i)) : ℝ) * Real.logb 2 3 + Real.logb 2 t) < arcHi d η →
    3 * (Hmap^[hSteps (β.take i)] (hR β + 2 ^ (parityOf β).length * t) / 4)
      / 2 ^ Nat.log 2 (Hmap^[hSteps (β.take i)] (hR β + 2 ^ (parityOf β).length * t) / 4)
      = 3 + d := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / (1 - (2 : ℝ) ^ (-η))) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_⟩
  intro β t d i hm ht hd hi hlo hhi
  have ht1 : 1 ≤ t := le_trans Nat.one_le_two_pow ht
  have hεt : 2 / (1 - (2 : ℝ) ^ (-η)) ≤ (t : ℝ) := by
    have h1 : 2 ^ n ≤ t := le_trans (Nat.pow_le_pow_right (by norm_num) hm) ht
    have h2 : (2 : ℝ) ^ n ≤ (t : ℝ) := by exact_mod_cast h1
    linarith
  obtain ⟨hb1, hb2⟩ := hluH_P_bounds hM hB β t i hi
  have hk : 8 ≤ (parityOf β).length - blockEnd β i := by
    have := hlu_blockEnd_add_le β i hi; omega
  unfold arcLo at hlo
  unfold arcHi at hhi
  obtain ⟨h1, h2⟩ := hlu_real η hη _ _ _ t d hd ht1 hb1 hb2 hεt (by linarith) hhi
  exact hluH_crit _ d _ (hluH_P_mod4 hC β t i hi) hd (by omega) h1 h2

/-- **Lower bound for the number of uses of the left-end rules** (the deterministic part of `HUseR`; the $H$ version of `left_use_ge` for $T$): for `η > 0` there is `m₀`
such that, if `m ≥ m₀`, `t ≥ 2^m` and `d ≤ 2`, the number of indices `i < |β|` for which the logarithm of the mantissa of the boundary point, `{a_i log₂ 3 + log₂ t}`, lies in the arc `J_d`
is at most the number of uses of `leftRule d` in the canonical derivations along the `hSteps β` steps from `x₀ = r_β + 2^m t`. -/
theorem left_use_geH (hM : SpecHModel) (hC : SpecHClass) (hB : SpecHBoundary) (η : ℝ) (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ (β : List Bool) (t d : ℕ),
    m₀ ≤ (parityOf β).length → 2 ^ (parityOf β).length ≤ t → d ≤ 2 →
    (((Finset.range β.length).filter (fun i =>
        arcLo d η ≤ Int.fract ((terrasA (parityOf (β.take i)) : ℝ) * Real.logb 2 3 + Real.logb 2 t) ∧
        Int.fract ((terrasA (parityOf (β.take i)) : ℝ) * Real.logb 2 3 + Real.logb 2 t) < arcHi d η)).card) ≤
      Gen.usesOrbitG Hmap canDerivH (leftRule d) (hR β + 2 ^ (parityOf β).length * t) (hSteps β) := by
  obtain ⟨m₀, hm₀⟩ := hluH_boundary_crit hM hC hB η hη
  refine ⟨m₀, fun β t d hm ht hd => ?_⟩
  refine le_trans (Finset.card_le_card ?_)
    (hluH_usesOrbitG_ge_boundary hM hC β t d (le_trans Nat.one_le_two_pow ht) hd)
  apply Finset.monotone_filter_right
  intro i hi hp
  exact hm₀ β t d i hm ht hd (Finset.mem_range.mp hi) hp.1 hp.2

/-- The form of `left_use_geH` with `a_i` written as the sum of the exponents of 3 of the blocks (5 for $X$, 7 for $Y$) (`HLUWalk.oddPrefix β i`
is this sum by definition). -/
theorem left_use_ge_sumH (hM : SpecHModel) (hC : SpecHClass) (hB : SpecHBoundary) (η : ℝ) (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ (β : List Bool) (t d : ℕ),
    m₀ ≤ (parityOf β).length → 2 ^ (parityOf β).length ≤ t → d ≤ 2 →
    (((Finset.range β.length).filter (fun i =>
        arcLo d η ≤ Int.fract ((((β.take i).map (fun x => if x then 5 else 7)).sum : ℕ) * Real.logb 2 3
          + Real.logb 2 t) ∧
        Int.fract ((((β.take i).map (fun x => if x then 5 else 7)).sum : ℕ) * Real.logb 2 3
          + Real.logb 2 t) < arcHi d η)).card) ≤
      Gen.usesOrbitG Hmap canDerivH (leftRule d) (hR β + 2 ^ (parityOf β).length * t) (hSteps β) := by
  obtain ⟨m₀, hm₀⟩ := left_use_geH hM hC hB η hη
  refine ⟨m₀, fun β t d hm ht hd => ?_⟩
  have := hm₀ β t d hm ht hd
  simp only [hlu_terrasA_take] at this
  exact this

end Collatz.Arctic.HTPDB
