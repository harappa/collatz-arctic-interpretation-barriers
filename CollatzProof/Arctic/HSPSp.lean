/-
Concentration of the spread `spr := fmax - fmin` (a step of the proof of `MinRate` in the general case: Theorem B.3, Steps 1 and 2).

* If no digit word kills `C`, then `fmin ≤ fmax` on digit words, and the spread `spr w := fmax w - fmin w` is **subadditive**
  (`hsp_spr_append`: subadditivity of `fmax` and superadditivity of `fmin`). The average `avgSp L = avgMax L - avgMinCap L` is subadditive as well.
* The spread rate `sprRate := inf_L avgSp L / L` (`≥ 0`). `MinRateAt` follows from `sprRate = 0` (`hsp_minRateAt_of_sprRate`).
* **Upper tail** `hsp_spr_upper`: `spr ≤` the sum of `spr` over the blocks of length `K` + the rest, and Chebyshev for the block sum.
* **Lower tail** `hsp_spr_lower`: since the average is at least `sprRate · L`, together with the upper tail the fraction of words with `spr < (sprRate - ε) L` is small.
-/
import CollatzProof.Arctic.HSPRed

namespace Collatz.Arctic

open Arc

variable {D : ℕ}

/-! ### The spread -/

/-- The spread: the difference between the largest entry and the smallest finite entry. -/
def spr (A : Interp D) (C : Finset (Fin D)) (w : Word) : ℕ := fmax A C w - fmin A C w

/-- The average of the spread over uniform words of length `L`. -/
def avgSp (A : Interp D) (C : Finset (Fin D)) (L : ℕ) : ℚ :=
  (∑ w ∈ wordsOfLen L, (spr A C w : ℚ)) / 2 ^ L

lemma hsp_isDigits_append {x y : Word} (hx : IsDigits x) (hy : IsDigits y) : IsDigits (x ++ y) := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact hx s h
  · exact hy s h

/-- **Subadditivity of the spread** (no digit word kills `C`; digit words). -/
theorem hsp_spr_append {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C) {x y : Word}
    (hx : IsDigits x) (hy : IsDigits y) : spr A C (x ++ y) ≤ spr A C x + spr A C y := by
  unfold spr
  have h1 := fmax_append_le A C x y
  have h2 := hsp_fmin_append A C x y
  have h3 := hsp_fmin_le_fmax hND hx
  have h4 := hsp_fmin_le_fmax hND hy
  omega

lemma hsp_spr_le {A : Interp D} {C : Finset (Fin D)} {w : Word} (hw : IsDigits w) :
    spr A C w ≤ digMax A * w.length :=
  (Nat.sub_le _ _).trans (hsp_fmax_le_digits A C w hw)

lemma hsp_spr_cast {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C) {w : Word}
    (hw : IsDigits w) : (spr A C w : ℚ) = (fmax A C w : ℚ) - (fmin A C w : ℚ) := by
  unfold spr
  rw [Nat.cast_sub (hsp_fmin_le_fmax hND hw)]

lemma hsp_avgSp_eq {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C) (L : ℕ) :
    avgSp A C L = avgMax A C L - avgMinCap A C L := by
  unfold avgSp avgMax avgMinCap
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun w hw => hsp_spr_cast hND (WinLLN.bin_of_mem hw))

lemma hsp_avgSp_nonneg (A : Interp D) (C : Finset (Fin D)) (L : ℕ) : 0 ≤ avgSp A C L := by
  unfold avgSp; positivity

lemma hsp_avgSp_add {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C) (p q : ℕ) :
    avgSp A C (p + q) ≤ avgSp A C p + avgSp A C q := by
  rw [hsp_avgSp_eq hND, hsp_avgSp_eq hND, hsp_avgSp_eq hND]
  have h1 := hsp_avgMax_add A C p q
  have h2 := hsp_avgMinCap_add A C p q
  linarith

/-- The spread rate `inf_{L ≥ 1} avgSp L / L`. -/
noncomputable def sprRate (A : Interp D) (C : Finset (Fin D)) : ℝ :=
  ⨅ L : ℕ, ((avgSp A C (L + 1) : ℚ) : ℝ) / ((L + 1 : ℕ) : ℝ)

lemma hsp_sprRate_bdd (A : Interp D) (C : Finset (Fin D)) :
    BddBelow (Set.range fun L : ℕ => ((avgSp A C (L + 1) : ℚ) : ℝ) / ((L + 1 : ℕ) : ℝ)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨L, rfl⟩
  have := hsp_avgSp_nonneg A C (L + 1)
  positivity

lemma hsp_sprRate_nonneg (A : Interp D) (C : Finset (Fin D)) : 0 ≤ sprRate A C := by
  refine le_ciInf (fun L => ?_)
  have := hsp_avgSp_nonneg A C (L + 1)
  positivity

/-- `sprRate · L ≤ avgSp L` (`L ≥ 1`). -/
lemma hsp_sprRate_le {A : Interp D} {C : Finset (Fin D)} {L : ℕ} (hL : 1 ≤ L) :
    sprRate A C * L ≤ ((avgSp A C L : ℚ) : ℝ) := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have h := ciInf_le (hsp_sprRate_bdd A C) L'
  have hL0 : (0 : ℝ) < ((L' + 1 : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hL0] at h
  exact h

lemma hsp_exists_len_near_sprRate (A : Interp D) (C : Finset (Fin D)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 1 ≤ K ∧ ((avgSp A C K : ℚ) : ℝ) / K ≤ sprRate A C + ε := by
  obtain ⟨L, hL⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (sprRate A C) hε)
  exact ⟨L + 1, Nat.succ_pos L, hL.le⟩

/-- **`sprRate = 0` implies `MinRateAt`** (`avgMinCap K = avgMax K - avgSp K ≥ (rate - ε) K`). -/
theorem hsp_minRateAt_of_sprRate {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C)
    (h0 : sprRate A C = 0) : MinRateAt A C := by
  intro ε hε
  obtain ⟨K, hK1, hK⟩ := hsp_exists_len_near_sprRate A C hε
  refine ⟨K, hK1, ?_⟩
  rw [h0, zero_add] at hK
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK1
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hrate := rate_le A C K'
  have e := hsp_avgSp_eq hND (K' + 1)
  have e' : ((avgSp A C (K' + 1) : ℚ) : ℝ) =
      ((avgMax A C (K' + 1) : ℚ) : ℝ) - ((avgMinCap A C (K' + 1) : ℚ) : ℝ) := by
    rw [e]; push_cast; ring
  rw [e', sub_div] at hK
  linarith

/-! ### Upper tail -/

/-- **Chebyshev for the upper tail of the block sum**: if `n ≥ 1` and `η > 0`, the number of words of length `nK + r` with `blockSum n > nμ + nη`
is at most `2^(nK+r) B / (n η²)`. -/
theorem hsp_cheb_blockSum_up (g : Word → ℚ) (K r : ℕ) (μ B : ℚ)
    (hμ : ∑ u ∈ wordsOfLen K, (g u - μ) = 0)
    (hB : ∀ u ∈ wordsOfLen K, (g u - μ) ^ 2 ≤ B) (n : ℕ) (hn : 1 ≤ n) (η : ℚ) (hη : 0 < η) :
    (((wordsOfLen (n * K + r)).filter (fun w => n * μ + n * η < blockSum g K n w)).card : ℚ) *
      (n * η ^ 2) ≤ 2 ^ (n * K + r) * B := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hc : (0 : ℚ) < n * η := by positivity
  have h1 := WinLLN.cheb (wordsOfLen (n * K + r)) (fun w => blockSum g K n w - n * μ) (n * η) hc
  have h2 := hsp_var_blockSum g K r μ B hμ hB n
  have hsub : (wordsOfLen (n * K + r)).filter (fun w => n * μ + n * η < blockSum g K n w) ⊆
      (wordsOfLen (n * K + r)).filter (fun w => n * η < |blockSum g K n w - n * μ|) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, ?_⟩
    rw [lt_abs]
    left; linarith [hw.2]
  have h3 : (((wordsOfLen (n * K + r)).filter (fun w => n * μ + n * η < blockSum g K n w)).card : ℚ)
      ≤ (((wordsOfLen (n * K + r)).filter (fun w => n * η < |blockSum g K n w - n * μ|)).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℚ) ≤ (n * η) ^ 2)
  have h5 := (h4.trans h1).trans h2
  have e : ((((wordsOfLen (n * K + r)).filter
      (fun w => n * μ + n * η < blockSum g K n w)).card : ℚ)) * (n * η) ^ 2 =
      n * (((((wordsOfLen (n * K + r)).filter
      (fun w => n * μ + n * η < blockSum g K n w)).card : ℚ)) * (n * η ^ 2)) := by ring
  rw [e, mul_assoc] at h5
  exact le_of_mul_le_mul_left h5 hnq

/-- By subadditivity, `spr(w) ≤` the sum of `spr` over the leading blocks of length `K` + the `spr` of the rest. -/
lemma hsp_spr_le_blockSum {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C) (K : ℕ) :
    ∀ (n : ℕ) (w : Word), IsDigits w →
      (spr A C w : ℚ) ≤ blockSum (fun u => (spr A C u : ℚ)) K n w + spr A C (w.drop (n * K)) := by
  intro n
  induction n with
  | zero => intro w _; simp [blockSum]
  | succ n ih =>
    intro w hw
    simp only [blockSum]
    have hd : IsDigits (w.drop K) := fun s hs => hw s (List.mem_of_mem_drop hs)
    have ht : IsDigits (w.take K) := fun s hs => hw s (List.mem_of_mem_take hs)
    have h1 := ih (w.drop K) hd
    have h2 := hsp_spr_append hND ht hd
    rw [List.take_append_drop] at h2
    rw [List.drop_drop, show K + n * K = (n + 1) * K by ring] at h1
    have h2' : (spr A C w : ℚ) ≤ (spr A C (w.take K) : ℚ) + (spr A C (w.drop K) : ℚ) := by
      exact_mod_cast h2
    linarith

open Classical in
/-- **Upper tail**: for `ε > 0` and `δ > 0`, if `L` is large, the fraction of words with `spr > (sprRate + ε) L` is at most `δ`. -/
theorem hsp_spr_upper {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C) {ε : ℝ}
    (hε : 0 < ε) {δ : ℚ} (hδ : 0 < δ) : ∃ L₀ : ℕ, ∀ L ≥ L₀,
      ((((wordsOfLen L).filter (fun w => (sprRate A C + ε) * L < spr A C w)).card : ℕ) : ℝ) ≤
        (δ : ℝ) * 2 ^ L := by
  obtain ⟨K, hK1, hK⟩ := hsp_exists_len_near_sprRate A C (show 0 < ε / 4 by positivity)
  have hKpos : 0 < K := hK1
  obtain ⟨η, hη0, hη⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 4 by positivity)
  have hη0' : (0 : ℚ) < η := by exact_mod_cast hη0
  set M := digMax A with hMdef
  set μ : ℚ := avgSp A C K with hμdef
  set B : ℚ := ((M * K : ℕ) : ℚ) ^ 2 with hBdef
  set g : Word → ℚ := fun u => (spr A C u : ℚ) with hgdef
  have hμsum : ∑ u ∈ wordsOfLen K, (g u - μ) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, WinLLN.card_words, nsmul_eq_mul, hμdef, avgSp]
    push_cast; field_simp; ring
  have hBg : ∀ u ∈ wordsOfLen K, (g u - μ) ^ 2 ≤ B := by
    intro u hu
    have hg0 : (0 : ℚ) ≤ g u := Nat.cast_nonneg _
    have hg1 : g u ≤ ((M * K : ℕ) : ℚ) := by
      have := hsp_spr_le (A := A) (C := C) (WinLLN.bin_of_mem hu)
      rw [length_of_mem_wordsOfLen hu] at this
      simp only [hgdef]; exact_mod_cast this
    have hμ0 : 0 ≤ μ := hsp_avgSp_nonneg A C K
    have hμ1 : μ ≤ ((M * K : ℕ) : ℚ) := by
      rw [hμdef, avgSp, div_le_iff₀ (by positivity)]
      have h : ∑ w ∈ wordsOfLen K, (spr A C w : ℚ) ≤ ∑ _w ∈ wordsOfLen K, ((M * K : ℕ) : ℚ) := by
        refine Finset.sum_le_sum (fun w hw => ?_)
        have := hsp_spr_le (A := A) (C := C) (WinLLN.bin_of_mem hw)
        rw [length_of_mem_wordsOfLen hw] at this
        exact_mod_cast this
      rw [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul] at h
      push_cast at h ⊢; linarith
    exact sq_le_sq' (by linarith) (by linarith)
  set n₀ : ℕ := ⌈B / ((η * K) ^ 2 * δ)⌉₊ + ⌈2 * (M : ℝ) / ε⌉₊ + 1 with hn₀def
  refine ⟨n₀ * K, fun L hL => ?_⟩
  have hn₀ : n₀ ≤ L / K := (Nat.le_div_iff_mul_le hKpos).mpr hL
  have hLnr : L = L / K * K + L % K := (Nat.div_add_mod' L K).symm
  have hrK : L % K ≤ K := (Nat.mod_lt L hKpos).le
  generalize L / K = n at hn₀ hLnr
  generalize L % K = r at hLnr hrK
  subst hLnr
  have hn1 : 1 ≤ n := le_trans (by omega) hn₀
  have hcheb := hsp_cheb_blockSum_up g K r μ B hμsum hBg n hn1 (η * K) (by positivity)
  -- bad words have a large block sum
  have hsub : (wordsOfLen (n * K + r)).filter
      (fun w => (sprRate A C + ε) * ((n * K + r : ℕ) : ℝ) < spr A C w) ⊆
      (wordsOfLen (n * K + r)).filter (fun w => n * μ + n * (η * K) < blockSum g K n w) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, ?_⟩
    by_contra hc
    push Not at hc
    have hwd := WinLLN.bin_of_mem hw.1
    have h1 := hsp_spr_le_blockSum hND K n w hwd
    have h2 : spr A C (w.drop (n * K)) ≤ M * K := by
      have := hsp_spr_le (A := A) (C := C) (w := w.drop (n * K))
        (fun s hs => hwd s (List.mem_of_mem_drop hs))
      rw [List.length_drop, length_of_mem_wordsOfLen hw.1] at this
      exact this.trans (Nat.mul_le_mul_left _ (by omega))
    have h3 : (spr A C w : ℚ) ≤ n * μ + n * (η * K) + (M * K : ℕ) := by
      have : ((spr A C (w.drop (n * K)) : ℕ) : ℚ) ≤ ((M * K : ℕ) : ℚ) := by exact_mod_cast h2
      linarith
    have h3r : (spr A C w : ℝ) ≤ n * (μ : ℝ) + n * ((η : ℝ) * K) + (M : ℝ) * K := by
      have := (Rat.cast_le (K := ℝ)).mpr h3
      push_cast at this; linarith
    -- `μ ≤ (sprRate + ε/4) K`, `η < ε/4`, `n ≥ 2M/ε`
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hμR : (μ : ℝ) ≤ (sprRate A C + ε / 4) * K := by
      rw [div_le_iff₀ hKR] at hK; exact hK
    have hnM : 2 * (M : ℝ) / ε ≤ n := by
      have := Nat.le_ceil (2 * (M : ℝ) / ε)
      have h4 : ((⌈2 * (M : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (by omega)
      linarith
    have hnM' : 2 * (M : ℝ) ≤ n * ε := by rw [div_le_iff₀ hε] at hnM; linarith
    have hs0 := hsp_sprRate_nonneg A C
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 : (n : ℝ) * μ ≤ n * ((sprRate A C + ε / 4) * K) := mul_le_mul_of_nonneg_left hμR hn0
    have e2 : (n : ℝ) * ((η : ℝ) * K) ≤ n * (ε / 4 * K) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hη.le hKR.le) hn0
    have e3 : (M : ℝ) * K ≤ n * ε / 2 * K := by
      have := mul_le_mul_of_nonneg_right hnM' hKR.le
      linarith
    have e4 : (sprRate A C + ε) * ((n : ℝ) * K) ≤ (sprRate A C + ε) * ((n : ℝ) * K + r) :=
      mul_le_mul_of_nonneg_left (by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith) (by linarith)
    have hw2 := hw.2
    push_cast at hw2
    nlinarith
  have hpos : (0 : ℚ) < n * (η * K) ^ 2 := by
    have : (0 : ℚ) < n := by exact_mod_cast hn1
    have : (0 : ℚ) < K := by exact_mod_cast hKpos
    positivity
  have hcardq : ((((wordsOfLen (n * K + r)).filter
      (fun w => n * μ + n * (η * K) < blockSum g K n w)).card : ℕ) : ℚ) ≤ δ * 2 ^ (n * K + r) := by
    have hnB : B ≤ n * ((η * K) ^ 2 * δ) := by
      have h1 : B / ((η * K) ^ 2 * δ) ≤ n := by
        have := Nat.le_ceil (B / ((η * K) ^ 2 * δ))
        have h2 : ((⌈B / ((η * K) ^ 2 * δ)⌉₊ : ℕ) : ℚ) ≤ n := Nat.cast_le.mpr (by omega)
        linarith
      have : (0 : ℚ) < (η * K) ^ 2 * δ := by
        have : (0 : ℚ) < K := by exact_mod_cast hKpos
        positivity
      rw [div_le_iff₀ this] at h1; linarith
    have h2 : ((((wordsOfLen (n * K + r)).filter
        (fun w => n * μ + n * (η * K) < blockSum g K n w)).card : ℕ) : ℚ) * (n * (η * K) ^ 2) ≤
        δ * 2 ^ (n * K + r) * (n * (η * K) ^ 2) := by
      calc _ ≤ 2 ^ (n * K + r) * B := hcheb
        _ ≤ 2 ^ (n * K + r) * (n * ((η * K) ^ 2 * δ)) :=
            mul_le_mul_of_nonneg_left hnB (by positivity)
        _ = δ * 2 ^ (n * K + r) * (n * (η * K) ^ 2) := by ring
    exact le_of_mul_le_mul_right h2 hpos
  have hc := Finset.card_le_card hsub
  have hcR : ((((wordsOfLen (n * K + r)).filter
      (fun w => (sprRate A C + ε) * ((n * K + r : ℕ) : ℝ) < spr A C w)).card : ℕ) : ℝ) ≤
      ((((wordsOfLen (n * K + r)).filter
      (fun w => n * μ + n * (η * K) < blockSum g K n w)).card : ℕ) : ℝ) := by exact_mod_cast hc
  have hq := (Rat.cast_le (K := ℝ)).mpr hcardq
  push_cast at hq hcR ⊢
  linarith

/-! ### Lower tail -/

open Classical in
/-- **Lower tail**: for `ε > 0` and `δ > 0`, if `L` is large, the fraction of words with `spr < (sprRate - ε) L` is at most `δ`
(the average is at least `sprRate · L`, and the upper tail is small). -/
theorem hsp_spr_lower {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C) {ε : ℝ}
    (hε : 0 < ε) {δ : ℚ} (hδ : 0 < δ) : ∃ L₀ : ℕ, ∀ L ≥ L₀,
      ((((wordsOfLen L).filter (fun w => (spr A C w : ℝ) < (sprRate A C - ε) * L)).card : ℕ) : ℝ) ≤
        (δ : ℝ) * 2 ^ L := by
  set M := digMax A with hMdef
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨δ'', hδ''0, hδ''⟩ := exists_rat_btwn
    (show (0 : ℝ) < ε * δ / (2 * ((M : ℝ) + 1)) by positivity)
  have hδ''0' : (0 : ℚ) < δ'' := by exact_mod_cast hδ''0
  set ε' : ℝ := ε * δ / 2 with hε'def
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨L₀, hL₀⟩ := hsp_spr_upper hND hε'0 hδ''0'
  refine ⟨L₀ + 1, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := by omega
  have hup := hL₀ L (by omega)
  set s := sprRate A C with hsdef
  have hs0 : 0 ≤ s := hsp_sprRate_nonneg A C
  set low := (wordsOfLen L).filter (fun w => (spr A C w : ℝ) < (s - ε) * L) with hlow
  set high := (wordsOfLen L).filter (fun w => (s + ε') * L < spr A C w) with hhigh
  have hLR : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  -- estimate for each word
  have hpt : ∀ w ∈ wordsOfLen L, (spr A C w : ℝ) ≤ (s + ε') * L -
      (ε + ε') * L * (if (spr A C w : ℝ) < (s - ε) * L then 1 else 0) +
      (M : ℝ) * L * (if (s + ε') * L < spr A C w then 1 else 0) := by
    intro w hw
    have hML : (spr A C w : ℝ) ≤ (M : ℝ) * L := by
      have := hsp_spr_le (A := A) (C := C) (WinLLN.bin_of_mem hw)
      rw [length_of_mem_wordsOfLen hw] at this
      exact_mod_cast this
    by_cases h1 : (spr A C w : ℝ) < (s - ε) * L
    · have h2 : ¬ (s + ε') * L < spr A C w := by
        intro h2
        have : (s - ε) * L ≤ (s + ε') * L := mul_le_mul_of_nonneg_right (by linarith) hLR
        linarith
      simp only [h1, h2, ↓reduceIte]
      nlinarith
    · by_cases h2 : (s + ε') * L < spr A C w
      · simp only [h1, h2, ↓reduceIte]
        have : 0 ≤ (s + ε') * L := mul_nonneg (by linarith) hLR
        nlinarith
      · simp only [h1, h2, ↓reduceIte]
        push Not at h2
        linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, WinLLN.card_words,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole] at hsum
  -- the average is at least `s L`
  have hmean : s * L * 2 ^ L ≤ ∑ w ∈ wordsOfLen L, (spr A C w : ℝ) := by
    have h := hsp_sprRate_le (A := A) (C := C) hL1
    have e : ((avgSp A C L : ℚ) : ℝ) = (∑ w ∈ wordsOfLen L, (spr A C w : ℝ)) / 2 ^ L := by
      unfold avgSp; push_cast; ring
    rw [e, le_div_iff₀ (by positivity)] at h
    linarith
  have hcl := hup
  push_cast at hsum hcl
  -- `(ε + ε') L #low ≤ ε' L 2^L + M L #high`
  have hkey : (ε + ε') * L * (low.card : ℝ) ≤ ε' * L * 2 ^ L + (M : ℝ) * L * (high.card : ℝ) := by
    nlinarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hkey' : (ε + ε') * (low.card : ℝ) ≤ ε' * 2 ^ L + (M : ℝ) * (high.card : ℝ) := by
    have e1 : (ε + ε') * L * (low.card : ℝ) = L * ((ε + ε') * (low.card : ℝ)) := by ring
    have e2 : ε' * L * 2 ^ L + (M : ℝ) * L * (high.card : ℝ) =
        L * (ε' * 2 ^ L + (M : ℝ) * (high.card : ℝ)) := by ring
    rw [e1, e2] at hkey
    exact le_of_mul_le_mul_left hkey hLpos
  have hMh : (M : ℝ) * (high.card : ℝ) ≤ ε * δ / 2 * 2 ^ L := by
    have h1 : (M : ℝ) * (high.card : ℝ) ≤ (M : ℝ) * ((δ'' : ℝ) * 2 ^ L) :=
      mul_le_mul_of_nonneg_left hcl (Nat.cast_nonneg _)
    have h2 : (M : ℝ) * (δ'' : ℝ) ≤ ε * δ / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hδ''
      have : (M : ℝ) * δ'' ≤ ((M : ℝ) + 1) * δ'' := mul_le_mul_of_nonneg_right (by linarith) hδ''0.le
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 ^ L)
    linarith
  have hfin : ε * (low.card : ℝ) ≤ ε * (δ * 2 ^ L) := by
    have : ε' * (low.card : ℝ) ≥ 0 := mul_nonneg hε'0.le (Nat.cast_nonneg _)
    rw [hε'def] at hkey' this
    nlinarith
  exact le_of_mul_le_mul_left hfin hε

end Collatz.Arctic
