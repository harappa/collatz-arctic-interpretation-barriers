/-
**Proof of `MinRate`** (the conclusion of the proof of `MinRate` in the general case: Theorem B.3, Step 8). We prove the
expected-value form of the growth of the smallest finite entries without Kingman's theorem.

* `hsp_sprRate_zero`: if `C` is strongly connected and no digit word kills `C`, the spread rate `sprRate` is 0.
  By contradiction: suppose `s := sprRate > 0`. Join `n + 1` segments of length `L` by the junction words of realized permutations.
  The sum identity for the variance (`hsp_sV_var`) gives `Σ pvar (sV) ≤ (n+1) · (number of joined words) · r (M (L + |u|))²`. On the other hand, the lower tail of the spread
  (`hsp_spr_lower`, `κ = s/2`) and the abundance of good segments give `pvar (sV) ≥ s² (n+1)² L² / 128` on most joined words
  (`hsp_main_ineq`). Hence `s² (n + 1) ≤ 1024 r M²`, which contradicts the choice `n > 1024 r M² / s²`.
  The almost-sure argument "the lineages are permuted by the group and every lineage grows at rate `Λ_C`" is replaced by a second-order
  estimate in which averaging over the permutations removes the cross terms (the variance grows only linearly in the number of segments, but quadratically if the spread is linear).
* `minRate_holds`: **`MinRate` holds** (`hsp_minRateAt_of_sprRate`). Corollary `hsp_holds`: **`HSP` holds**.
-/
import CollatzProof.Arctic.HSPIneq

namespace Collatz.Arctic

open MinIdeal Matrix Arc Classical

variable {D : ℕ} {A : Interp D} {C : Finset (Fin D)}

lemma hsp_sprRate_le_digMax (A : Interp D) (C : Finset (Fin D)) : sprRate A C ≤ digMax A := by
  have h := ciInf_le (hsp_sprRate_bdd A C) 0
  refine h.trans ?_
  simp only [Nat.zero_add, Nat.cast_one, div_one]
  have : avgSp A C 1 ≤ digMax A := by
    unfold avgSp
    rw [div_le_iff₀ (by positivity)]
    have h1 : ∑ w ∈ wordsOfLen 1, (spr A C w : ℚ) ≤ ∑ _w ∈ wordsOfLen 1, (digMax A : ℚ) := by
      refine Finset.sum_le_sum (fun w hw => ?_)
      have := hsp_spr_le (A := A) (C := C) (WinLLN.bin_of_mem hw)
      rw [length_of_mem_wordsOfLen hw, mul_one] at this
      exact_mod_cast this
    rw [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul] at h1
    push_cast at h1 ⊢; linarith
  exact_mod_cast this

/-- **The spread rate is 0** (`C` strongly connected, no digit word kills `C`). -/
theorem hsp_sprRate_zero (hSC : StrongConnIn A C) (hND : NeverDies A C C) : sprRate A C = 0 := by
  by_contra hne
  have hs0 := hsp_sprRate_nonneg A C
  set s := sprRate A C with hsdef
  have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hne)
  have hsM := hsp_sprRate_le_digMax A C
  obtain ⟨S⟩ := hsp_exists_linSetup hSC
  have := hsp_cls_nonempty S hND
  set r : ℝ := (Fintype.card (Cls S.E S.hE) : ℝ) with hr
  have hr1 : (1 : ℝ) ≤ r := by rw [hr]; exact_mod_cast Fintype.card_pos
  set M : ℝ := (digMax A : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  set U : ℕ := S.u.length with hU
  have hU1 : 1 ≤ U := List.length_pos_of_ne_nil S.hu0
  set q : ℚ := 1 - 1 / 2 ^ U with hq
  have hq0 : 0 ≤ q := by
    have : (1 : ℚ) / 2 ^ U ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    linarith
  have hq1 : q < 1 := by have : (0 : ℚ) < 1 / 2 ^ U := by positivity
                         linarith
  -- choice of the constants
  set η : ℝ := s / (64 * (M + 1) * (r + 1)) with hη
  have hη0 : 0 < η := by positivity
  set n : ℕ := ⌈1024 * r * M ^ 2 / s ^ 2⌉₊ + 1 with hn
  set δ : ℚ := 1 / (4 * 2 ^ (n * jwMax S)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨n₁, hn₁⟩ := exists_pow_lt_of_lt_one (show (0 : ℚ) < 1 / (8 * (n + 1)) by positivity) hq1
  obtain ⟨L₀, hL₀⟩ := hsp_spr_lower hND (show 0 < s / 2 by positivity) hδ0
  set L : ℕ := L₀ + U + ⌈16 * M * U / s⌉₊ + ⌈(jwMax S + 3 * U : ℝ) / η⌉₊ +
    ⌈((U * n₁ : ℕ) + 1 : ℝ) / η⌉₊ + 1 with hL
  set h : ℕ := ⌊η * L⌋₊ with hh
  -- properties of the lengths
  have hLR : (0 : ℝ) < L := by rw [hL]; positivity
  have hh1 : (h : ℝ) ≤ η * L := Nat.floor_le (by positivity)
  have hh2 : η * L - 1 < h := by
    have := Nat.lt_floor_add_one (η * L)
    rw [← hh] at this; linarith
  clear_value h L δ n η q U M r s
  have hηM : M * η ≤ s / 64 := by
    rw [hη]
    have h1 : M * (s / (64 * (M + 1) * (r + 1))) = s / 64 * (M / ((M + 1) * (r + 1))) := by
      field_simp
    rw [h1]
    have h2 : M / ((M + 1) * (r + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : M + 1 ≤ (M + 1) * (r + 1) := le_mul_of_one_le_right (by positivity) (by linarith)
      linarith
    calc s / 64 * (M / ((M + 1) * (r + 1))) ≤ s / 64 * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = s / 64 := mul_one _
  have hηMr : M * η * (r + 1) ≤ s / 64 := by
    rw [hη]
    have h1 : M * (s / (64 * (M + 1) * (r + 1))) * (r + 1) = s / 64 * (M / (M + 1)) := by
      field_simp
    rw [h1]
    have h2 : M / (M + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc s / 64 * (M / (M + 1)) ≤ s / 64 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = s / 64 := mul_one _
  have hη64 : η ≤ 1 / 64 := by
    rw [hη, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hsM' : s ≤ M := by rw [hsdef]; exact hsM
    have h1 : M + 1 ≤ (M + 1) * (r + 1) := le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  have h2h : 2 * h ≤ L := by
    have h1 := mul_le_mul_of_nonneg_right hη64 hLR.le
    have : (2 * h : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hL₀L : L₀ ≤ L := by omega
  have hUL : (U : ℝ) ≤ L := by
    have : U ≤ L := by omega
    exact_mod_cast this
  have hL16 : 16 * M * U / s ≤ L := by
    have h1 := Nat.le_ceil (16 * M * U / s)
    have h2 : ((⌈16 * M * U / s⌉₊ : ℕ) : ℝ) ≤ L := Nat.cast_le.mpr (by omega)
    linarith
  have hLj : (jwMax S + 3 * U : ℝ) / η ≤ L := by
    have h1 := Nat.le_ceil ((jwMax S + 3 * U : ℝ) / η)
    have h2 : ((⌈(jwMax S + 3 * U : ℝ) / η⌉₊ : ℕ) : ℝ) ≤ L := Nat.cast_le.mpr (by omega)
    linarith
  have hLn : (((U * n₁ : ℕ) : ℝ) + 1) / η ≤ L := by
    have h1 := Nat.le_ceil ((((U * n₁ : ℕ) : ℝ) + 1) / η)
    have h2 : ((⌈(((U * n₁ : ℕ) : ℝ) + 1) / η⌉₊ : ℕ) : ℝ) ≤ L := Nat.cast_le.mpr (by omega)
    linarith
  have hLj' : (jwMax S + 3 * U : ℝ) ≤ η * L := by
    rw [div_le_iff₀ hη0] at hLj; linarith
  have hLn' : ((U * n₁ : ℕ) : ℝ) + 1 ≤ η * L := by
    rw [div_le_iff₀ hη0] at hLn; linarith
  have hL16' : 16 * M * U ≤ s * L := by
    rw [div_le_iff₀ hs] at hL16; linarith
  -- lower tail (`κ = s/2`)
  have hlow : ∀ N, L₀ ≤ N → ((((wordsOfLen N).filter
      (fun W => (spr A C W : ℝ) < s / 2 * N)).card : ℕ) : ℝ) ≤ (δ : ℝ) * 2 ^ N := by
    intro N hN
    have := hL₀ N hN
    rwa [show sprRate A C - s / 2 = s / 2 by rw [← hsdef]; ring] at this
  -- `T`
  set T : ℝ := s / 2 * (n + 1) * L - 2 * ((digMax A * h : ℕ) : ℝ) - 2 * ((digMax A * U : ℕ) : ℝ)
    with hT
  clear_value T
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hTlow : s / 4 * (n + 1) * L ≤ T := by
    rw [hT]; push_cast
    have h4 : 0 ≤ s * L := by positivity
    have e1 : 2 * (M * h) ≤ s / 32 * L := by
      have h1 : M * h ≤ M * (η * L) := mul_le_mul_of_nonneg_left hh1 hM0
      have h2 := mul_le_mul_of_nonneg_right hηM hLR.le
      have e : M * (η * L) = M * η * L := by ring
      linarith
    have e2 : 2 * (M * U) ≤ s / 8 * L := by linarith
    rw [← hM]
    have h3 : 0 ≤ s * L * n := by positivity
    linarith
  have hT0 : 0 ≤ T := le_trans (by positivity) hTlow
  -- error `J ≤ 3 M η L`
  have hJ : (junErr S h : ℝ) ≤ 3 * M * η * L := by
    unfold junErr
    push_cast
    rw [← hM, ← hU]
    have h1 : (2 * h + jwMax S + 3 * U : ℝ) ≤ 3 * (η * L) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hM0
    have e : M * (3 * (η * L)) = 3 * M * η * L := by ring
    linarith
  have hJ0 : (0 : ℝ) ≤ junErr S h := Nat.cast_nonneg _
  have hrJ : r * (n * (junErr S h : ℝ)) ^ 2 ≤ s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 128 := by
    have h1 : (n * (junErr S h : ℝ)) ^ 2 ≤ (n * (3 * M * η * L)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hJ hnR) 2
    have h2 : r * (n * (3 * M * η * L)) ^ 2 = 9 * n ^ 2 * L ^ 2 * (r * (M * η) ^ 2) := by ring
    have h3 : r * (M * η) ^ 2 ≤ s ^ 2 / 4096 := by
      have hMη0 : 0 ≤ M * η := by positivity
      have h31 : r * (M * η) ^ 2 ≤ (M * η) * (M * η * (r + 1)) := by
        have : (M * η) * (M * η * (r + 1)) = r * (M * η) ^ 2 + (M * η) ^ 2 := by ring
        rw [this]; linarith [sq_nonneg (M * η)]
      have h32 : (M * η) * (M * η * (r + 1)) ≤ (s / 64) * (s / 64) := by
        have h1 : (M * η) * (M * η * (r + 1)) ≤ (s / 64) * (M * η * (r + 1)) :=
          mul_le_mul_of_nonneg_right hηM (by positivity)
        have h2 : (s / 64) * (M * η * (r + 1)) ≤ (s / 64) * (s / 64) :=
          mul_le_mul_of_nonneg_left hηMr (by positivity)
        linarith
      have e : (s / 64) * (s / 64) = s ^ 2 / 4096 := by ring
      linarith
    have h4 : r * (n * (junErr S h : ℝ)) ^ 2 ≤ 9 * n ^ 2 * L ^ 2 * (s ^ 2 / 4096) := by
      calc r * (n * (junErr S h : ℝ)) ^ 2 ≤ r * (n * (3 * M * η * L)) ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 9 * n ^ 2 * L ^ 2 * (r * (M * η) ^ 2) := h2
        _ ≤ 9 * n ^ 2 * L ^ 2 * (s ^ 2 / 4096) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (n : ℝ) ^ 2 ≤ (n + 1) ^ 2 := pow_le_pow_left₀ hnR (by linarith) 2
    have h6 : (n : ℝ) ^ 2 * (L ^ 2 * s ^ 2) ≤ (n + 1) ^ 2 * (L ^ 2 * s ^ 2) :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    have h7 : 0 ≤ (n + 1 : ℝ) ^ 2 * (L ^ 2 * s ^ 2) := by positivity
    have e1 : 9 * n ^ 2 * L ^ 2 * (s ^ 2 / 4096) = 9 / 4096 * ((n : ℝ) ^ 2 * (L ^ 2 * s ^ 2)) := by ring
    have e2 : s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 128 = 1 / 128 * ((n + 1 : ℝ) ^ 2 * (L ^ 2 * s ^ 2)) := by ring
    rw [e2]
    linarith
  have hΦlow : s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 128 ≤
      T ^ 2 / 4 - r * (n * (junErr S h : ℝ)) ^ 2 := by
    have h1 : (s / 4 * (n + 1) * L) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by positivity) hTlow 2
    have e : (s / 4 * (n + 1) * L) ^ 2 = s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 16 := by ring
    rw [e] at h1
    linarith
  have hΦ0 : 0 ≤ T ^ 2 / 4 - r * (n * (junErr S h : ℝ)) ^ 2 := le_trans (by positivity) hΦlow
  -- fractions
  have hqh : ((q : ℚ) : ℝ) ^ (h / U) < 1 / (8 * (n + 1)) := by
    have hhU : n₁ ≤ h / U := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have : ((U * n₁ : ℕ) : ℝ) < h := by linarith
      have := (Nat.cast_lt (α := ℝ)).mp this
      rw [Nat.mul_comm] at this; omega
    have h1 : q ^ (h / U) ≤ q ^ n₁ := pow_le_pow_of_le_one hq0 hq1.le hhU
    have h2 : q ^ (h / U) < 1 / (8 * (n + 1)) := lt_of_le_of_lt h1 hn₁
    have := (Rat.cast_lt (K := ℝ)).mpr h2
    push_cast at this ⊢
    exact this
  have hδj : (δ : ℝ) * 2 ^ (n * jwMax S) = 1 / 4 := by
    rw [hδ]; push_cast; field_simp
  have hpre : 1 / 2 ≤ 1 - (n + 1) * (2 * ((1 - 1 / 2 ^ S.u.length : ℚ) : ℝ) ^ (h / S.u.length)) -
      (δ : ℝ) * 2 ^ (n * jwMax S) := by
    rw [hδj]
    have h1 : (n + 1 : ℝ) * (2 * ((q : ℚ) : ℝ) ^ (h / U)) ≤ 1 / 4 := by
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have := mul_lt_mul_of_pos_left hqh hn1
      have e : (n + 1 : ℝ) * (1 / (8 * (n + 1))) = 1 / 8 := by field_simp
      rw [e] at this
      linarith
    rw [hq] at h1
    rw [← hU]
    linarith
  -- the main inequality
  have hmain := hsp_main_ineq S hSC hND n L h L₀ h2h hL₀L (s / 2) (δ : ℝ) (by positivity)
    (by positivity) hlow T (by rw [hT, hU]) hT0 (by rw [← hr]; exact hΦ0)
  have hlhs : s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 256 ≤
      (T ^ 2 / 4 - r * (n * (junErr S h : ℝ)) ^ 2) *
        (1 - (n + 1) * (2 * ((1 - 1 / 2 ^ S.u.length : ℚ) : ℝ) ^ (h / S.u.length)) -
          (δ : ℝ) * 2 ^ (n * jwMax S)) := by
    have h1 := mul_le_mul_of_nonneg_left hpre hΦ0
    have h2 : s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 256 = s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 128 * (1 / 2) := by ring
    rw [h2]
    calc s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 128 * (1 / 2)
        ≤ (T ^ 2 / 4 - r * (n * (junErr S h : ℝ)) ^ 2) * (1 / 2) :=
          mul_le_mul_of_nonneg_right hΦlow (by norm_num)
      _ ≤ _ := h1
  have hrhs : (n + 1) * r * (M * (L + U)) ^ 2 ≤ 4 * (n + 1) * r * M ^ 2 * L ^ 2 := by
    have h1 : (M * (L + U)) ^ 2 ≤ (M * (2 * L)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hM0) 2
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (n + 1) * r)
    have e : (n + 1) * r * (M * (2 * L)) ^ 2 = 4 * (n + 1) * r * M ^ 2 * L ^ 2 := by ring
    linarith
  have hfin : s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 256 ≤ 4 * (n + 1) * r * M ^ 2 * L ^ 2 := by
    rw [← hr, ← hM, ← hU] at hmain
    rw [← hU] at hlhs
    linarith
  -- `s² (n + 1) ≤ 1024 r M²`
  have hfin' : s ^ 2 * (n + 1) ≤ 1024 * r * M ^ 2 := by
    have hpos : (0 : ℝ) < (n + 1) * L ^ 2 := by positivity
    have e1 : s ^ 2 * (n + 1) ^ 2 * L ^ 2 / 256 = (s ^ 2 * (n + 1)) * ((n + 1) * L ^ 2) / 256 := by ring
    have e2 : 4 * (n + 1) * r * M ^ 2 * L ^ 2 = (1024 * r * M ^ 2) * ((n + 1) * L ^ 2) / 256 := by ring
    rw [e1, e2, div_le_div_iff_of_pos_right (by norm_num)] at hfin
    exact le_of_mul_le_mul_right hfin hpos
  -- contradiction with the choice of `n`
  have hnbig : 1024 * r * M ^ 2 / s ^ 2 < n + 1 := by
    have := Nat.le_ceil (1024 * r * M ^ 2 / s ^ 2)
    rw [hn]; push_cast; linarith
  rw [div_lt_iff₀ (by positivity)] at hnbig
  linarith

/-- **`MinRate` holds** (Theorem B.3). -/
theorem minRate_holds : MinRate := fun _ _ _ hSC hND =>
  hsp_minRateAt_of_sprRate hND (hsp_sprRate_zero hSC hND)

/-- **`HSP` holds** (the hypothesis `HSP` is a theorem; Corollary B.4). -/
theorem hsp_holds : HSP := hsp_of_minRate minRate_holds

end Collatz.Arctic

#print axioms Collatz.Arctic.minRate_holds
#print axioms Collatz.Arctic.hsp_holds
