/-
**`HTerrasWinR R` follows from `HKeyTopR R`**. Adapted from `HTWFromKey.lean`
(the version for $T$, `hTerrasWin_of_key : HKeyTop → HTerrasWin`). The residue `R` is an argument, and the only facts about residues used are
the fields of `BlockModel` `R_lt` (`hlt`) and `R_prefix` (`hpre`). The form of Theorem B.8
(`HKeyTop` $\Rightarrow$ `HTerrasWin`) with the residue as an argument. We prove the frozen statement `SpecWinOfKey` of `Gen/Spec.lean`
as `specWinOfKey`.

Outline of the proof (the same as for $T$; only the number of bits `(parityOf β).length` and `blockEnd` appear, not the number of steps of the map):
1. **Chunks**: split the interval `[i₁, i₂)` of block indices into chunks of `K` blocks `[i₁ + tK, i₁ + (t+1)K)` (`t < T`,
   `T = ⌊(i₂ - i₁)/K⌋`) and discard the leftover at the end. The bits of a chunk are, by `R_prefix`, the expansion of the quotient of the residue up to the end of the chunk
   by `2^{L_a}` (`Gen.htw_bits_split`).
2. **Probability that a chunk is good**: if at least `n₀` random blocks precede the chunk, then by `HKeyTopR` the law of its bits is within
   `τ` of uniform, and the window frequencies of a uniform word are within `δ/2` with probability at least `1 - η` (`win_bad_count`). Hence a chunk is bad with probability
   at most `2τ + η` (`Gen.htw_cut_prob`). The chunks touching the first `n₀` blocks of the interval are counted as bad.
3. **Markov**: the expected number of bad chunks is at most `T(2τ + η)`; with `θ = δ/44`, it is at most `θT` with probability at least `1 - ε`.
4. **Deterministic part** (`htw_det`): if there are at most `n₀ + θT` bad chunks, the window frequencies of the whole interval are within `δ` of uniform
   (`Gen.htw_combine`).
5. Windows of length 0 (`J = 0`) are trivial (the only window is the empty word) and are treated separately.
-/
import CollatzProof.Arctic.Gen.HTWProb
import CollatzProof.Arctic.Gen.Spec
import CollatzProof.Arctic.CoreU

namespace Collatz.Arctic.Gen

open Collatz.Arctic
open Finset

section FromKey

variable (R : List Bool → ℕ)

open Classical in
/-- **Deterministic part** (assembly of chunks): split the interval `[i₁, i₂)` of block indices into chunks of `K` blocks
`[i₁ + tK, i₁ + (t+1)K)` (`t < T`, `TK ≤ i₂ - i₁ < (T+1)K`). If there are at most `B` bad chunks and
`11K + 11KB + TJ + 1 ≤ (δ/2)(8(i₂ - i₁) + 1 - J)`, then the window frequencies of the interval are within `δ` of uniform. -/
theorem htw_det (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    (hpre : ∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁)
    (β : List Bool) {K J T i₁ i₂ : ℕ} (hJ : 1 ≤ J) {δ : ℚ} (hδ : 0 < δ)
    (hT1 : T * K ≤ i₂ - i₁) (hT2 : i₂ - i₁ < T * K + K) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ β.length)
    (hJW : J ≤ 8 * (i₂ - i₁)) (B : ℚ)
    (hB : ((((range T).filter (fun t => ¬ htwGood R K J (δ / 2) β (i₁ + t * K))).card : ℕ) : ℚ) ≤ B)
    (harith : 11 * (K : ℚ) + 11 * K * B + T * J + 1 ≤
      δ / 2 * ((8 * (i₂ - i₁) + 1 - J : ℕ) : ℚ)) :
    WinClose (bitsMSB (parityOf β).length (R β))
      ((parityOf β).length - blockEnd β i₂) ((parityOf β).length - blockEnd β i₁) J δ := by
  set m := (parityOf β).length with hm
  set w := bitsMSB m (R β) with hw
  set p : ℕ → ℕ := fun t => m - blockEnd β (i₁ + t * K) with hp
  set A := m - blockEnd β i₂ with hA
  have hwlen : w.length = m := bitsMSB_length _ _
  have hLm : ∀ i, blockEnd β i ≤ m := fun i => blockEnd_le_full β i
  have hp0 : p 0 = m - blockEnd β i₁ := by simp [hp]
  have hpt : ∀ t, p (t + 1) = m - blockEnd β (i₁ + t * K + K) := fun t => by
    simp only [hp]; rw [show i₁ + (t + 1) * K = i₁ + t * K + K by ring]
  have hanti : ∀ t < T, p (t + 1) ≤ p t := by
    intro t _
    have := blockEnd_mono β (show i₁ + t * K ≤ i₁ + t * K + K by omega)
    rw [hpt]
    simp only [hp]
    omega
  have hTKi : i₁ + T * K ≤ i₂ := by omega
  have hAT : A ≤ p T := by
    have := blockEnd_mono β hTKi
    simp only [hp, hA]
    omega
  set G := (range T).filter (fun t => htwGood R K J (δ / 2) β (i₁ + t * K)) with hG
  have hGsub : G ⊆ range T := filter_subset _ _
  have hgood : ∀ t ∈ G, WinClose w (p (t + 1)) (p t) J (δ / 2) := by
    intro t ht
    have h := htw_good_win R hlt hpre (mem_filter.mp ht).2
    rw [hpt]
    exact h
  have hcomb := htw_combine w hJ (by positivity : (0 : ℚ) ≤ δ / 2) hanti hAT G hGsub hgood
  -- estimate of the remainder
  have hnonG : range T \ G =
      (range T).filter (fun t => ¬ htwGood R K J (δ / 2) β (i₁ + t * K)) := by
    rw [hG, filter_not]
  have hstepK : ∀ t ∈ range T \ G, p t - p (t + 1) ≤ 11 * K := by
    intro t _
    have h1 := blockEnd_sub_le β (i₁ + t * K) K
    have h2 := blockEnd_mono β (show i₁ + t * K ≤ i₁ + t * K + K by omega)
    rw [hpt]
    simp only [hp]
    omega
  have hsumG : ∑ t ∈ range T \ G, (p t - p (t + 1)) ≤ (range T \ G).card * (11 * K) := by
    have := sum_le_sum hstepK
    rwa [sum_const, smul_eq_mul] at this
  have hlast : p T - A ≤ 11 * K := by
    have h1 := blockEnd_sub_le β (i₁ + T * K) (i₂ - (i₁ + T * K))
    rw [show i₁ + T * K + (i₂ - (i₁ + T * K)) = i₂ by omega] at h1
    have h2 : i₂ - (i₁ + T * K) ≤ K := by omega
    have h3 : 11 * (i₂ - (i₁ + T * K)) ≤ 11 * K := Nat.mul_le_mul_left 11 h2
    have h4 := blockEnd_mono β hTKi
    simp only [hp, hA]
    omega
  have hcard : (((range T \ G).card : ℕ) : ℚ) ≤ B := by rw [hnonG]; exact hB
  -- lower bound for the number of windows
  have hL8 := htw_blockEnd_ge β i₁ (i₂ - i₁) (by omega)
  rw [show i₁ + (i₂ - i₁) = i₂ by omega] at hL8
  have hLi₂ := hLm i₂
  have hN : 8 * (i₂ - i₁) + 1 - J ≤ p 0 + 1 - J - A := by
    rw [hp0]; simp only [hA]; omega
  have hAJ : A + J ≤ p 0 := by
    rw [hp0]; simp only [hA]; omega
  rw [← hp0, htw_winClose_iff hAJ (by rw [hwlen, hp0]; omega)]
  refine hcomb.trans ?_
  have hrest : ((p T - A + ∑ t ∈ range T \ G, (p t - p (t + 1)) + T * J + 1 : ℕ) : ℚ) ≤
      11 * (K : ℚ) + 11 * K * B + T * J + 1 := by
    have h1 : p T - A + ∑ t ∈ range T \ G, (p t - p (t + 1)) + T * J + 1 ≤
        11 * K + (range T \ G).card * (11 * K) + T * J + 1 := by omega
    have h2 : ((p T - A + ∑ t ∈ range T \ G, (p t - p (t + 1)) + T * J + 1 : ℕ) : ℚ) ≤
        ((11 * K + (range T \ G).card * (11 * K) + T * J + 1 : ℕ) : ℚ) := by exact_mod_cast h1
    have h3 : (((range T \ G).card : ℕ) : ℚ) * (11 * K) ≤ B * (11 * K) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have h4 : ((11 * K + (range T \ G).card * (11 * K) + T * J + 1 : ℕ) : ℚ) =
        11 * (K : ℚ) + (((range T \ G).card : ℕ) : ℚ) * (11 * K) + T * J + 1 := by push_cast; ring
    rw [h4] at h2
    linarith
  have hNq : ((8 * (i₂ - i₁) + 1 - J : ℕ) : ℚ) ≤ ((p 0 + 1 - J - A : ℕ) : ℚ) := by
    exact_mod_cast hN
  have h5 := mul_le_mul_of_nonneg_left hNq (by positivity : (0 : ℚ) ≤ δ / 2)
  linarith

end FromKey

/-- The frequencies of windows of length 0 are uniform if the interval fits in the word (the only window is the empty word). -/
theorem htw_winClose_zero {w : Word} {a b : ℕ} {δ : ℚ} (hδ : 0 < δ) (hab : a ≤ b)
    (hb : b ≤ w.length) : WinClose w a b 0 δ := by
  rw [htw_winClose_iff (by omega) hb, htw_dev_zero]
  positivity

open Classical in
/-- **`HTerrasWinR R` follows from `HKeyTopR R`** (the form of `HTWFromKey.hTerrasWin_of_key` with the residue as an argument). The only facts about residues
used are `R_lt` (`hlt`) and `R_prefix` (`hpre`). -/
theorem hTerrasWinR_of_key (R : List Bool → ℕ) (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    (hpre : ∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁) :
    HKeyTopR R → HTerrasWinR R := by
  intro hkey β₀ J δ ε₀ ε hδ hε₀ hε
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ
  · -- windows of length 0: holds deterministically
    subst hJ0
    refine ⟨0, fun k _ i₁ i₂ _ hi₁₂ hi₂ => ?_⟩
    have hi : i₁ ≤ i₂ := by
      have : (0 : ℚ) ≤ ε₀ * k := by positivity
      exact_mod_cast (show (i₁ : ℚ) ≤ i₂ by linarith)
    have h := fam_pr_ge β₀ k (fun β => WinClose (bitsMSB (parityOf β).length (R β))
        ((parityOf β).length - blockEnd β i₂) ((parityOf β).length - blockEnd β i₁) 0 δ)
      (fun _ => 0) 0 (fun _ _ => le_rfl) (fun β _ hn => absurd (htw_winClose_zero hδ
        (by have := blockEnd_mono (β₀ ++ β) hi; omega)
        (by rw [bitsMSB_length]; omega)) hn) (by simp)
    linarith
  -- constants
  set θ : ℚ := δ / 44 with hθ
  set τ : ℚ := ε * θ / 4 with hτ
  set η : ℚ := ε * θ / 2 with hη
  have hθ0 : 0 < θ := by positivity
  have hτ0 : 0 < τ := by positivity
  have hη0 : 0 < η := by positivity
  obtain ⟨M₀, hM₀⟩ := win_bad_count J (δ / 2) η (by positivity) hη0
  set K : ℕ := M₀ + ⌈4 * (J : ℚ) / δ⌉₊ + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hKJ : 4 * (J : ℚ) ≤ δ * K := by
    have h1 := Nat.le_ceil (4 * (J : ℚ) / δ)
    have h2 : ((⌈4 * (J : ℚ) / δ⌉₊ : ℕ) : ℚ) ≤ K := by rw [hK]; push_cast; linarith
    have h3 : 4 * (J : ℚ) / δ ≤ K := h1.trans h2
    rw [div_le_iff₀ hδ] at h3
    linarith
  obtain ⟨n₀, hn₀⟩ := hkey K τ hτ0
  set C₀ : ℚ := 11 * K * (n₀ + 1) + 1 with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨⌈((J : ℚ) + K + C₀ / δ) / ε₀⌉₊, fun k hk i₁ i₂ hi₁ hi₁₂ hi₂ => ?_⟩
  -- width `W = i₂ - i₁ ≥ ε₀ k`
  have hWq0 : (J : ℚ) + K + C₀ / δ ≤ (i₂ : ℚ) - i₁ := by
    have h1 := Nat.le_ceil (((J : ℚ) + K + C₀ / δ) / ε₀)
    have h2 : ((⌈((J : ℚ) + K + C₀ / δ) / ε₀⌉₊ : ℕ) : ℚ) ≤ k := by exact_mod_cast hk
    have h3 := (div_le_iff₀ hε₀).mp (h1.trans h2)
    linarith
  have hCδ : 0 ≤ C₀ / δ := by positivity
  have hi : i₁ ≤ i₂ := by exact_mod_cast (show (i₁ : ℚ) ≤ i₂ by linarith)
  set W := i₂ - i₁ with hW
  have hWcast : (W : ℚ) = (i₂ : ℚ) - i₁ := by rw [hW, Nat.cast_sub hi]
  rw [← hWcast] at hWq0
  have hWK : K ≤ W := by exact_mod_cast (show (K : ℚ) ≤ W by linarith)
  have hWJ : J ≤ W := by exact_mod_cast (show (J : ℚ) ≤ W by linarith)
  set T := W / K with hT
  have hT1 : T * K ≤ W := Nat.div_mul_le_self W K
  have hT2 : W < T * K + K := Nat.lt_div_mul_add (by omega)
  have hTpos : 0 < T := Nat.div_pos hWK (by omega)
  -- the number of bad chunks (those preceded by at least `n₀` random blocks)
  set X : List Bool → ℕ := fun β => ((range T).filter (fun t =>
    β₀.length + n₀ ≤ i₁ + t * K ∧ ¬ htwGood R K J (δ / 2) β (i₁ + t * K))).card with hX
  -- window frequencies of a uniform word
  have hbad : ∀ γ : List Bool, γ.length = K →
      (((Finset.range (2 ^ (parityOf γ).length)).filter (fun u =>
        ¬ WinClose (bitsMSB (parityOf γ).length u) 0 (parityOf γ).length J (δ / 2))).card : ℚ) ≤
        η * 2 ^ (parityOf γ).length := by
    intro γ hγ
    have hl := (parityOf_length_bounds γ).1
    exact hM₀ (parityOf γ).length 0 (parityOf γ).length (Nat.zero_le _) le_rfl (by omega)
  -- expectation
  have hsum : ∑ β ∈ blockChoices k, wtβ β * (X (β₀ ++ β) : ℚ) ≤ T * (2 * τ + η) := by
    have e : ∀ β, (X (β₀ ++ β) : ℚ) = ∑ t ∈ range T, (if β₀.length + n₀ ≤ i₁ + t * K ∧
        ¬ htwGood R K J (δ / 2) (β₀ ++ β) (i₁ + t * K) then (1 : ℚ) else 0) := by
      intro β
      simp only [hX]
      rw [natCast_card_filter]
    simp_rw [e, mul_sum]
    rw [sum_comm]
    calc ∑ t ∈ range T, ∑ β ∈ blockChoices k, wtβ β * (if β₀.length + n₀ ≤ i₁ + t * K ∧
          ¬ htwGood R K J (δ / 2) (β₀ ++ β) (i₁ + t * K) then (1 : ℚ) else 0)
        ≤ ∑ _t ∈ range T, (2 * τ + η) := by
          refine sum_le_sum (fun t ht => ?_)
          have htT := mem_range.mp ht
          by_cases hc : β₀.length + n₀ ≤ i₁ + t * K
          · have hj : i₁ + t * K = β₀.length + (i₁ + t * K - β₀.length) := by omega
            have htK : (t + 1) * K ≤ T * K := Nat.mul_le_mul_right K htT
            rw [add_mul, one_mul] at htK
            have hlen := htw_cut_prob R hlt β₀ K J (δ / 2) τ η n₀ hn₀ hbad k
              (i₁ + t * K - β₀.length) (by omega) (by omega)
            refine le_trans (le_of_eq (sum_congr rfl (fun β _ => ?_))) hlen
            rw [← hj]
            by_cases hg : htwGood R K J (δ / 2) (β₀ ++ β) (i₁ + t * K) <;> simp [hc, hg]
          · have h0 : ∀ β, (if β₀.length + n₀ ≤ i₁ + t * K ∧
                ¬ htwGood R K J (δ / 2) (β₀ ++ β) (i₁ + t * K) then (1 : ℚ) else 0) = 0 :=
              fun β => by simp [hc]
            simp only [h0, mul_zero, sum_const_zero]
            positivity
      _ = T * (2 * τ + η) := by rw [sum_const, card_range, nsmul_eq_mul]
  have hmk := htw_markov β₀ k X T hTpos θ (2 * τ + η) hθ0 hsum
  have hεeq : (2 * τ + η) / θ = ε := by rw [hτ, hη]; field_simp; ring
  rw [hεeq] at hmk
  refine hmk.trans (htw_prσ_mono β₀ k (fun β hβ hXβ => ?_))
  -- deterministic part
  have hβlen : (β₀ ++ β).length = β₀.length + k := by
    rw [List.length_append, length_of_mem_blockChoices hβ]
  -- number of bad chunks ≤ n₀ + θT
  have hB : ((((range T).filter
      (fun t => ¬ htwGood R K J (δ / 2) (β₀ ++ β) (i₁ + t * K))).card : ℕ) : ℚ) ≤ n₀ + θ * T := by
    have hsub : (range T).filter (fun t => ¬ htwGood R K J (δ / 2) (β₀ ++ β) (i₁ + t * K)) ⊆
        range n₀ ∪ (range T).filter (fun t => β₀.length + n₀ ≤ i₁ + t * K ∧
          ¬ htwGood R K J (δ / 2) (β₀ ++ β) (i₁ + t * K)) := by
      intro t ht
      rw [mem_filter] at ht
      rw [mem_union, mem_range, mem_filter]
      by_cases hc : β₀.length + n₀ ≤ i₁ + t * K
      · exact Or.inr ⟨ht.1, hc, ht.2⟩
      · left
        have : t ≤ t * K := Nat.le_mul_of_pos_right t (by omega)
        omega
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_range] at h1
    have h2 : ((((range T).filter
        (fun t => ¬ htwGood R K J (δ / 2) (β₀ ++ β) (i₁ + t * K))).card : ℕ) : ℚ) ≤
          n₀ + (X (β₀ ++ β) : ℚ) := by exact_mod_cast h1
    have h3 : (X (β₀ ++ β) : ℚ) ≤ θ * T := hXβ
    linarith
  refine htw_det R hlt hpre (β₀ ++ β) hJ hδ hT1 hT2 hi (by omega) (by omega) (n₀ + θ * T) hB ?_
  -- arithmetic
  have hJWn : J ≤ 8 * W := by omega
  have hcast : ((8 * W + 1 - J : ℕ) : ℚ) = 8 * (W : ℚ) + 1 - J := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast]
  have hTKq : (T : ℚ) * K ≤ W := by exact_mod_cast hT1
  have hA1 : δ * ((T : ℚ) * K) ≤ δ * W := mul_le_mul_of_nonneg_left hTKq hδ.le
  have hA2 : (T : ℚ) * (4 * J) ≤ (T : ℚ) * (δ * K) :=
    mul_le_mul_of_nonneg_left hKJ (by positivity)
  have hA3 : δ * ((J : ℚ) + K + C₀ / δ) ≤ δ * W := mul_le_mul_of_nonneg_left hWq0 hδ.le
  rw [mul_add, mul_add, mul_div_cancel₀ _ hδ.ne'] at hA3
  have hδK : 0 ≤ δ * (K : ℚ) := by positivity
  have hδJ : 0 ≤ δ * (J : ℚ) := by positivity
  rw [hθ]
  rw [hC₀] at hA3
  nlinarith

/-- **Output of this file** (`SpecWinOfKey` of the frozen `Gen/Spec.lean`): from the uniformity of a single chunk `HKeyTopR R`,
the window frequencies `HTerrasWinR R` on intervals of block indices (for any residue `R` satisfying `R_lt` and `R_prefix`). -/
theorem specWinOfKey : SpecWinOfKey :=
  fun R hlt hpre => hTerrasWinR_of_key R hlt hpre

end Collatz.Arctic.Gen
