/-
The probabilistic part of deriving the window frequencies `HTerrasWinR` from `HKeyTopR`.
Adapted from `HTWProb.lean` (the version for $T$). The residue `R` is an argument, and the only fact about residues used is `R_lt`
(the size of the value of a chunk, `htwCutVal_lt`). The deterministic part is in `Gen/HTWCut.lean`, the main theorem in `Gen/HTWFromKey.lean`.
The probabilistic part of the proof of Theorem B.8.

* `htw_sum_split`: splits the weighted sum over choices of `a + m` blocks into a double sum over the first `a` blocks and the remaining `m`
  (the weight is a product; independent of the residue; copied from the version for $T$).
* `htw_bad_le`: fix the blocks `γ` of the chunk. If the law of the bits of the chunk is within total variation distance `τ` of uniform (`HKeyTopR`) and
  the proportion of bad uniform words (property `P`) is at most `η`, then the bits of the chunk are bad with probability at most `2τ + η`.
* `htw_cut_prob`: the chunk `[|β₀| + j, |β₀| + j + K)` (`j ≥ n₀`) is bad with probability at most `2τ + η`.
* `htw_markov`: Markov's inequality for the expectation (weighted counting; independent of the residue; copied from the version for $T$).
* `htw_prσ_mono`: `Prσ` is monotone in the event (a copy of `HLUMain.Prσ_mono`; `HLUMain` is the file of the left-end rules of $T$,
  which we keep out of the closure for $H$, so we copied it, prefixing `htw_` to avoid name clashes with copies in other files).
-/
import CollatzProof.Arctic.Gen.HTWCut
import CollatzProof.Arctic.HLUWalk2
import CollatzProof.Arctic.CoreProb

namespace Collatz.Arctic.Gen

open Collatz.Arctic
open Finset

/-- Splits the weighted sum over choices of `a + m` blocks into a double sum over the first `a` blocks and the remaining `m`. -/
theorem htw_sum_split (a m : ℕ) (H : List Bool → List Bool → ℚ) :
    ∑ β ∈ blockChoices (a + m), wtβ β * H (β.take a) (β.drop a) =
      ∑ β₁ ∈ blockChoices a, ∑ β₂ ∈ blockChoices m, wtβ β₁ * (wtβ β₂ * H β₁ β₂) := by
  induction a generalizing H with
  | zero =>
    have h0 : blockChoices 0 = {[]} := by
      ext β
      simp [fam_mem_blockChoices]
    rw [Nat.zero_add, h0, sum_singleton]
    refine sum_congr rfl (fun β _ => ?_)
    simp [wtβ]
  | succ a ih =>
    rw [show a + 1 + m = (a + m) + 1 by omega, fam_sum_succ, fam_sum_succ]
    have L : ∀ x : Bool, ∑ β ∈ blockChoices (a + m),
        wtβ (x :: β) * H ((x :: β).take (a + 1)) ((x :: β).drop (a + 1))
        = (if x then (3 / 10 : ℚ) else 7 / 10) *
          ∑ β₁ ∈ blockChoices a, ∑ β₂ ∈ blockChoices m, wtβ β₁ * (wtβ β₂ * H (x :: β₁) β₂) := by
      intro x
      rw [← ih (fun β₁ β₂ => H (x :: β₁) β₂), mul_sum]
      refine sum_congr rfl (fun β _ => ?_)
      rw [List.take_succ_cons, List.drop_succ_cons, fam_wt_cons]
      ring
    have R : ∀ x : Bool, ∑ β₁ ∈ blockChoices a, ∑ β₂ ∈ blockChoices m,
        wtβ (x :: β₁) * (wtβ β₂ * H (x :: β₁) β₂)
        = (if x then (3 / 10 : ℚ) else 7 / 10) *
          ∑ β₁ ∈ blockChoices a, ∑ β₂ ∈ blockChoices m, wtβ β₁ * (wtβ β₂ * H (x :: β₁) β₂) := by
      intro x
      rw [mul_sum]
      refine sum_congr rfl (fun β₁ _ => ?_)
      rw [mul_sum]
      refine sum_congr rfl (fun β₂ _ => ?_)
      rw [fam_wt_cons]
      ring
    rw [L true, L false, R true, R false]

section Prob

variable (R : List Bool → ℕ)

open Classical in
/-- **Probability that one chunk is bad** (the blocks `γ` of the chunk fixed): if the law of the bits of the chunk is within total variation distance `τ` of uniform and
the proportion of uniform words with property `P` is at most `η`, then the bits of the chunk have `P` with probability at most `2τ + η`. -/
theorem htw_bad_le (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    (β₀ γ : List Bool) (n : ℕ) (τ η : ℚ) (P : Word → Prop) [DecidablePred P]
    (hkey : ∑ u ∈ Finset.range (2 ^ (parityOf γ).length),
      |(∑ β ∈ (blockChoices n).filter (fun β =>
          R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length = u), wtβ β)
        - 1 / 2 ^ (parityOf γ).length| ≤ 2 * τ)
    (hP : (((Finset.range (2 ^ (parityOf γ).length)).filter
        (fun u => P (bitsMSB (parityOf γ).length u))).card : ℚ) ≤ η * 2 ^ (parityOf γ).length) :
    ∑ β ∈ blockChoices n,
      wtβ β * (if P (bitsMSB (parityOf γ).length (htwCutVal R β₀ β γ)) then 1 else 0) ≤
        2 * τ + η := by
  set ℓ := (parityOf γ).length with hℓ
  set q : ℕ → ℚ := fun u =>
    ∑ β ∈ (blockChoices n).filter (fun β => htwCutVal R β₀ β γ = u), wtβ β with hq
  have hfib : ∑ β ∈ blockChoices n,
      wtβ β * (if P (bitsMSB ℓ (htwCutVal R β₀ β γ)) then 1 else 0) =
      ∑ u ∈ range (2 ^ ℓ), (if P (bitsMSB ℓ u) then (1 : ℚ) else 0) * q u := by
    rw [← sum_fiberwise_of_maps_to (t := range (2 ^ ℓ)) (g := fun β => htwCutVal R β₀ β γ)
      (fun β _ => mem_range.mpr (htwCutVal_lt R hlt β₀ β γ))]
    refine sum_congr rfl (fun u _ => ?_)
    rw [hq, mul_sum]
    refine sum_congr rfl (fun β hβ => ?_)
    rw [(mem_filter.mp hβ).2]
    ring
  rw [hfib]
  have hterm : ∀ u ∈ range (2 ^ ℓ), (if P (bitsMSB ℓ u) then (1 : ℚ) else 0) * q u ≤
      |q u - 1 / 2 ^ ℓ| + (if P (bitsMSB ℓ u) then 1 / 2 ^ ℓ else 0) := by
    intro u _
    have hq0 : 0 ≤ q u := sum_nonneg (fun β _ => fam_wt_nonneg β)
    split_ifs
    · rw [one_mul]
      have := le_abs_self (q u - 1 / 2 ^ ℓ)
      linarith
    · rw [zero_mul, add_zero]
      exact abs_nonneg _
  have h1 : ∑ u ∈ range (2 ^ ℓ), |q u - 1 / 2 ^ ℓ| ≤ 2 * τ := hkey
  have h2 : ∑ u ∈ range (2 ^ ℓ), (if P (bitsMSB ℓ u) then (1 / 2 ^ ℓ : ℚ) else 0) ≤ η := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hpos : (0 : ℚ) < 2 ^ ℓ := by positivity
    calc (((range (2 ^ ℓ)).filter (fun u => P (bitsMSB ℓ u))).card : ℚ) * (1 / 2 ^ ℓ)
        ≤ η * 2 ^ ℓ * (1 / 2 ^ ℓ) := mul_le_mul_of_nonneg_right hP (by positivity)
      _ = η := by field_simp
  calc ∑ u ∈ range (2 ^ ℓ), (if P (bitsMSB ℓ u) then (1 : ℚ) else 0) * q u
      ≤ ∑ u ∈ range (2 ^ ℓ), (|q u - 1 / 2 ^ ℓ| + (if P (bitsMSB ℓ u) then 1 / 2 ^ ℓ else 0)) :=
        sum_le_sum hterm
    _ = ∑ u ∈ range (2 ^ ℓ), |q u - 1 / 2 ^ ℓ| +
          ∑ u ∈ range (2 ^ ℓ), (if P (bitsMSB ℓ u) then (1 / 2 ^ ℓ : ℚ) else 0) := sum_add_distrib
    _ ≤ 2 * τ + η := add_le_add h1 h2

open Classical in
/-- **Probability that a chunk is bad**: the chunk `[|β₀| + j, |β₀| + j + K)` (`n₀ ≤ j`, `j + K ≤ k`) is bad with probability at most `2τ + η`.
`hkey` is the conclusion of `HKeyTopR R` at `K`, `τ`, and `hbad` is the law of large numbers for window frequencies of uniform words. -/
theorem htw_cut_prob (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    (β₀ : List Bool) (K J : ℕ) (δ' τ η : ℚ) (n₀ : ℕ)
    (hkey : ∀ n ≥ n₀, ∀ (β₀ γ : List Bool), γ.length = K →
      ∑ u ∈ Finset.range (2 ^ (parityOf γ).length),
        |(∑ β ∈ (blockChoices n).filter (fun β =>
            R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length = u), wtβ β)
          - 1 / 2 ^ (parityOf γ).length| ≤ 2 * τ)
    (hbad : ∀ γ : List Bool, γ.length = K →
      (((Finset.range (2 ^ (parityOf γ).length)).filter (fun u =>
        ¬ WinClose (bitsMSB (parityOf γ).length u) 0 (parityOf γ).length J δ')).card : ℚ) ≤
        η * 2 ^ (parityOf γ).length)
    (k j : ℕ) (hj : n₀ ≤ j) (hjk : j + K ≤ k) :
    ∑ β ∈ blockChoices k,
      wtβ β * (if htwGood R K J δ' (β₀ ++ β) (β₀.length + j) then 0 else 1) ≤ 2 * τ + η := by
  set F : List Bool → ℚ := fun x => if htwGood R K J δ' (β₀ ++ x) (β₀.length + j) then 0 else 1
    with hF
  -- determined by the blocks up to the end of the chunk alone
  have hloc : ∀ β ∈ blockChoices k,
      (if htwGood R K J δ' (β₀ ++ β) (β₀.length + j) then (0 : ℚ) else 1) =
        F (β.take (j + K)) := by
    intro β _
    rw [hF]
    simp only
    have e : (β₀ ++ β).take (β₀.length + j + K) = β₀ ++ β.take (j + K) := by
      rw [show β₀.length + j + K = β₀.length + (j + K) by omega, List.take_length_add_append]
    have hg := htw_good_take R K J δ' (β₀ ++ β) (β₀.length + j)
    rw [e] at hg
    rw [hg]
  rw [sum_congr rfl (fun β hβ => by rw [hloc β hβ])]
  rw [show k = (j + K) + (k - (j + K)) by omega, walk_sum_take]
  -- split into the `j` blocks before the chunk and the `K` blocks of the chunk
  have hsplit := htw_sum_split j K (fun β₁ γ => F (β₁ ++ γ))
  simp only [List.take_append_drop] at hsplit
  rw [hsplit]
  -- write in terms of the value of the chunk
  have hcut : ∀ β₁ ∈ blockChoices j, ∀ γ ∈ blockChoices K,
      F (β₁ ++ γ) = if ¬ WinClose (bitsMSB (parityOf γ).length (htwCutVal R β₀ β₁ γ)) 0
        (parityOf γ).length J δ' then 1 else 0 := by
    intro β₁ hβ₁ γ hγ
    have hl₁ := length_of_mem_blockChoices hβ₁
    have hlγ := length_of_mem_blockChoices hγ
    have hg := htw_good_cut R K J δ' β₀ β₁ γ hlγ
    rw [List.length_append, hl₁] at hg
    rw [hF]
    simp only
    rw [← List.append_assoc, hg]
    split_ifs <;> simp_all
  rw [sum_congr rfl (fun β₁ hβ₁ => sum_congr rfl (fun γ hγ => by rw [hcut β₁ hβ₁ γ hγ]))]
  rw [sum_comm]
  calc ∑ γ ∈ blockChoices K, ∑ β₁ ∈ blockChoices j, wtβ β₁ * (wtβ γ *
        (if ¬ WinClose (bitsMSB (parityOf γ).length (htwCutVal R β₀ β₁ γ)) 0
          (parityOf γ).length J δ' then (1 : ℚ) else 0))
      = ∑ γ ∈ blockChoices K, wtβ γ * ∑ β₁ ∈ blockChoices j, wtβ β₁ *
        (if ¬ WinClose (bitsMSB (parityOf γ).length (htwCutVal R β₀ β₁ γ)) 0
          (parityOf γ).length J δ' then (1 : ℚ) else 0) := by
        refine sum_congr rfl (fun γ _ => ?_)
        rw [mul_sum]
        refine sum_congr rfl (fun β₁ _ => ?_)
        ring
    _ ≤ ∑ γ ∈ blockChoices K, wtβ γ * (2 * τ + η) := by
        refine sum_le_sum (fun γ hγ => mul_le_mul_of_nonneg_left ?_ (fam_wt_nonneg γ))
        have hlγ := length_of_mem_blockChoices hγ
        exact htw_bad_le R hlt β₀ γ j τ η
          (fun w => ¬ WinClose w 0 (parityOf γ).length J δ') (hkey j hj β₀ γ hlγ) (hbad γ hlγ)
    _ = 2 * τ + η := by rw [← sum_mul, (fam_moments K).1, one_mul]

end Prob

open Classical in
/-- **Markov's inequality** (weighted counting): if the expectation of `X` is at most `T c`, then `X ≤ θ T` with probability at least `1 - c/θ`. -/
theorem htw_markov (β₀ : List Bool) (k : ℕ) (X : List Bool → ℕ) (T : ℕ) (hT : 0 < T) (θ c : ℚ)
    (hθ : 0 < θ) (hsum : ∑ β ∈ blockChoices k, wtβ β * (X (β₀ ++ β) : ℚ) ≤ T * c) :
    1 - c / θ ≤ Prσ β₀ k (fun β => (X β : ℚ) ≤ θ * T) := by
  have hTq : (0 : ℚ) < T := by exact_mod_cast hT
  apply fam_pr_ge β₀ k _ (fun β => wtβ β * (X (β₀ ++ β) : ℚ) / (θ * T)) (c / θ)
  · intro β _
    have := fam_wt_nonneg β
    positivity
  · intro β _ hbad
    push Not at hbad
    rw [le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hbad.le (fam_wt_nonneg β)
  · rw [← sum_div, div_le_iff₀ (by positivity)]
    calc ∑ β ∈ blockChoices k, wtβ β * (X (β₀ ++ β) : ℚ) ≤ T * c := hsum
      _ = c / θ * (θ * T) := by field_simp

open Classical in
/-- `Prσ` is monotone in the event (over the choices of the remaining `k` blocks). A copy of `HLUMain.Prσ_mono`. -/
theorem htw_prσ_mono (β₀ : List Bool) (k : ℕ) {E F : List Bool → Prop}
    (h : ∀ β ∈ blockChoices k, E (β₀ ++ β) → F (β₀ ++ β)) :
    Prσ β₀ k E ≤ Prσ β₀ k F := by
  unfold Prσ
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro β hβ
    simp only [Finset.mem_filter] at hβ ⊢
    exact ⟨hβ.1, h _ hβ.1 hβ.2⟩
  · intro β _ _
    exact fam_wt_nonneg β

end Collatz.Arctic.Gen
