/-
Reduction of the hypothesis `HSP` (`CoreHyp.lean`; Corollary B.4) to the expected-value hypothesis `MinRate` (Theorem B.1).
The ingredients are in `HSPRedBase.lean`.

* **`MinRate`** (an expected-value form of the growth of the smallest finite entries): if `C` is strongly connected and no digit word kills `C`, then
  for every `ε > 0` there is `K ≥ 1` such that the average `avgMinCap K` of the smallest finite entry `fmin` over uniform words of length `K` is
  at least `(Λ_C - ε) K` (`Λ_C` is `RateDefs.rate`). The form for a single component is `MinRateAt`. The almost-sure version is equivalent to
  "all finite entries of `D_w` are at least `Λ_C t - o(t)`", and `MinRate` is its expected-value form.
* **Reduction** `hspAt_of_minRateAt`, `hsp_of_minRate`: finite values of `rowVal` are at least `fmin` (the set `S` of starting indices is not used).
  Since `fmin` is superadditive, on a word of length `L = nK + r` it is at least the sum of `fmin` over the blocks of length `K`. The blocks are independent and uniform,
  and each term lies between `0` and `digMax · K`, so by Chebyshev's inequality for the second moment the fraction of words whose sum is below `n (avgMinCap K - δK)`
  is at most `digMax² / (n δ²)`. Since `avgMinCap K / K ≥ Λ_C - ε/3` by `MinRate`, `δ < ε/3`, and `n` is large, the values are
  at least `(Λ_C - ε) L`. In `hsp_of_minRate`, `StrongConnIn` is passed to `MinRate` unchanged, and `S ⊆ C` and `NeverDies A C S`
  give the `NeverDies A C C` passed to `MinRate`. `S.Nonempty` is not used (the reduction for a single component assumes nothing about `S`).
* **Sharpness** `hsp_avgMinCap_le_rate` (Proposition B.2): if no digit word kills `C`, then `avgMinCap K / K ≤ Λ_C` for every `K ≥ 1` (superadditivity of the average
  `hsp_avgMinCap_add`, subadditivity `hsp_avgMax_add`, and `fmin ≤ fmax`). Hence `MinRateAt` is
  equivalent to `sup_K avgMinCap K / K = Λ_C`, and `MinRate` cannot be strengthened as an expected-value statement.
* **`MinRate` holds** (`minRate_holds` in `HSPMain.lean`; Theorem B.3). Hence `HSP` is a theorem as well (`hsp_holds`; Corollary B.4).
-/
import CollatzProof.Arctic.HSPRedBase

namespace Collatz.Arctic

/-! ### The hypothesis `MinRate` -/

/-- **`MinRate` for a single component**: for every `ε > 0` there is `K ≥ 1` with `Λ_C - ε ≤ avgMinCap K / K`. -/
def MinRateAt {D : ℕ} (A : Interp D) (C : Finset (Fin D)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, 1 ≤ K ∧ rate A C - ε ≤ ((avgMinCap A C K : ℚ) : ℝ) / K

/-- **The hypothesis MinRate** (an expected-value form of the growth of the smallest finite entries): every component `C` that is strongly connected
and that no digit word kills satisfies `MinRateAt A C`. -/
def MinRate : Prop :=
  ∀ (D : ℕ) (A : Interp D) (C : Finset (Fin D)), StrongConnIn A C → NeverDies A C C → MinRateAt A C

open Classical in
/-- The conclusion of `HSP` for a fixed component `C` and a fixed set `S` of starting indices. -/
def HSPAt {D : ℕ} (A : Interp D) (C S : Finset (Fin D)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀,
    (1 - ε) * 2 ^ L ≤ ((((wordsOfLen L).filter (fun w => ∀ j (v : ℕ), rowVal A C S w j = Arc.fin v →
      (rate A C - ε) * L ≤ v)).card : ℕ) : ℝ)

/-- The final arithmetic of the reduction: if `μ / K ≥ ρ - ε/3`, `δ < ε/3`, `n ≥ 3ρ/ε`, `r ≤ K` and `v ≥ nμ - nδK`, then
`(ρ - ε)(nK + r) ≤ v`. -/
lemma hsp_arith {ρ ε μ δ v : ℝ} {n K r : ℕ} (hK : 0 < K) (hr : r ≤ K) (hε : 0 < ε)
    (hμ : ρ - ε / 3 ≤ μ / K) (hδ : δ < ε / 3) (hn : 3 * ρ / ε ≤ n) (hv0 : 0 ≤ v)
    (hv : n * μ - n * (δ * K) ≤ v) : (ρ - ε) * ((n * K + r : ℕ) : ℝ) ≤ v := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hrK : (r : ℝ) ≤ K := by exact_mod_cast hr
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hμ' : K * (ρ - ε / 3) ≤ μ := by
    rw [le_div_iff₀ hKr] at hμ; linarith
  have hnρ : 3 * ρ ≤ n * ε := by
    rw [div_le_iff₀ hε] at hn; linarith
  push_cast
  by_cases hρ : ρ ≤ ε
  · have : (ρ - ε) * ((n : ℝ) * K + r) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  · push Not at hρ
    have h1 : (ρ - ε) * r ≤ ρ * K := by
      have : (ρ - ε) * r ≤ (ρ - ε) * K := mul_le_mul_of_nonneg_left hrK (by linarith)
      nlinarith
    have h2 : (n : ℝ) * μ ≥ n * (K * (ρ - ε / 3)) := mul_le_mul_of_nonneg_left hμ' hn0
    have h3 : (n : ℝ) * (δ * K) ≤ n * (ε / 3 * K) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδ.le hKr.le) hn0
    have h4 : ρ * K ≤ n * ε / 3 * K := by
      have : ρ ≤ n * ε / 3 := by linarith
      exact mul_le_mul_of_nonneg_right this hKr.le
    nlinarith

open Classical in
/-- **Reduction for a single component**: `MinRateAt A C` implies `HSPAt A C S` for every set `S` of starting indices.
Proof: finite values of `rowVal` are at least `fmin` (`hsp_fmin_le_rowVal`), `fmin` is at least the sum of `fmin` over the blocks of length `K`
(superadditivity, `hsp_blockSum_le_fmin`), and by Chebyshev's inequality for the second moment of the block sum (`hsp_cheb_blockSum`),
the fraction of words below `n μ - n δ K` is at most `ε`. -/
theorem hspAt_of_minRateAt {D : ℕ} (A : Interp D) (C S : Finset (Fin D)) (hMR : MinRateAt A C) :
    HSPAt A C S := by
  intro ε hε
  obtain ⟨K, hK1, hK⟩ := hMR (ε / 3) (by positivity)
  have hKpos : 0 < K := hK1
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 3 by positivity)
  obtain ⟨ε₁, hε₁0, hε₁⟩ := exists_rat_btwn hε
  have hδ0' : (0 : ℚ) < δ := by exact_mod_cast hδ0
  have hε₁0' : (0 : ℚ) < ε₁ := by exact_mod_cast hε₁0
  set μ : ℚ := avgMinCap A C K with hμdef
  set B : ℚ := ((digMax A * K : ℕ) : ℚ) ^ 2 with hBdef
  set g : Word → ℚ := fun u => (fmin A C u : ℚ) with hgdef
  set η : ℚ := δ * K with hηdef
  have hη : 0 < η := by positivity
  -- mean and variance
  have hμsum : ∑ u ∈ wordsOfLen K, (g u - μ) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, WinLLN.card_words, nsmul_eq_mul, hμdef,
      avgMinCap]
    push_cast
    field_simp
    ring
  have hBg : ∀ u ∈ wordsOfLen K, (g u - μ) ^ 2 ≤ B := by
    intro u hu
    have hg0 : (0 : ℚ) ≤ g u := Nat.cast_nonneg _
    have hg1 : g u ≤ ((digMax A * K : ℕ) : ℚ) := by
      have := hsp_fmin_le A C u
      rw [length_of_mem_wordsOfLen hu] at this
      simp only [hgdef]
      exact_mod_cast this
    have hμ0 := hsp_avgMinCap_nonneg A C K
    have hμ1 := hsp_avgMinCap_le A C K
    exact sq_le_sq' (by linarith) (by linarith)
  -- threshold for the length
  set n₀ : ℕ := ⌈B / (η ^ 2 * ε₁)⌉₊ + ⌈3 * rate A C / ε⌉₊ + 1 with hn₀def
  refine ⟨n₀ * K, fun L hL => ?_⟩
  have hn₀ : n₀ ≤ L / K := (Nat.le_div_iff_mul_le hKpos).mpr hL
  have hLnr : L = L / K * K + L % K := (Nat.div_add_mod' L K).symm
  have hrK : L % K ≤ K := (Nat.mod_lt L hKpos).le
  generalize L / K = n at hn₀ hLnr
  generalize L % K = r at hLnr hrK
  subst hLnr
  have hn1 : 1 ≤ n := le_trans (by omega) hn₀
  -- number of bad words
  set bad := (wordsOfLen (n * K + r)).filter (fun w => blockSum g K n w < n * μ - n * η) with hbad
  have hcheb := hsp_cheb_blockSum g K r μ B hμsum hBg n hn1 η hη
  have hbadq : (bad.card : ℚ) ≤ ε₁ * 2 ^ (n * K + r) := by
    have hnB : B ≤ n * (η ^ 2 * ε₁) := by
      have h1 : B / (η ^ 2 * ε₁) ≤ n := by
        have := Nat.le_ceil (B / (η ^ 2 * ε₁))
        have h2 : ((⌈B / (η ^ 2 * ε₁)⌉₊ : ℕ) : ℚ) ≤ n := by exact_mod_cast (by omega : _ ≤ n)
        linarith
      rw [div_le_iff₀ (by positivity)] at h1
      linarith
    have hpos : (0 : ℚ) < n * η ^ 2 := by
      have : (0 : ℚ) < n := by exact_mod_cast hn1
      positivity
    have h2 : (bad.card : ℚ) * (n * η ^ 2) ≤ ε₁ * 2 ^ (n * K + r) * (n * η ^ 2) := by
      calc (bad.card : ℚ) * (n * η ^ 2) ≤ 2 ^ (n * K + r) * B := hcheb
        _ ≤ 2 ^ (n * K + r) * (n * (η ^ 2 * ε₁)) :=
            mul_le_mul_of_nonneg_left hnB (by positivity)
        _ = ε₁ * 2 ^ (n * K + r) * (n * η ^ 2) := by ring
    exact le_of_mul_le_mul_right h2 hpos
  -- good words belong to the event of HSP
  have hgood : (wordsOfLen (n * K + r)).filter (fun w => ¬ blockSum g K n w < n * μ - n * η) ⊆
      (wordsOfLen (n * K + r)).filter (fun w => ∀ j (v : ℕ), rowVal A C S w j = Arc.fin v →
        (rate A C - ε) * ((n * K + r : ℕ) : ℝ) ≤ v) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, fun j v hv => ?_⟩
    have h1 := hsp_fmin_le_rowVal hv
    have h2 := hsp_blockSum_le_fmin A C K n w
    have h3 : (n : ℚ) * μ - n * η ≤ v := by
      have : ((fmin A C w : ℕ) : ℚ) ≤ (v : ℚ) := by exact_mod_cast h1
      push Not at hw
      linarith [hw.2]
    have h3r : (n : ℝ) * (μ : ℝ) - n * ((δ : ℝ) * K) ≤ (v : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h3
      push_cast [hηdef] at this
      linarith
    have hn3 : 3 * rate A C / ε ≤ n := by
      have := Nat.le_ceil (3 * rate A C / ε)
      have h4 : ((⌈3 * rate A C / ε⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : _ ≤ n)
      linarith
    exact hsp_arith hKpos hrK hε hK hδ hn3 (Nat.cast_nonneg v) h3r
  -- counting
  have htot := Finset.card_filter_add_card_filter_not (s := wordsOfLen (n * K + r))
    (fun w => blockSum g K n w < n * μ - n * η)
  rw [WinLLN.card_words] at htot
  have hc1 := Finset.card_le_card hgood
  have hgoodq : (2 : ℝ) ^ (n * K + r) - (ε₁ : ℝ) * 2 ^ (n * K + r) ≤
      (((wordsOfLen (n * K + r)).filter (fun w => ¬ blockSum g K n w < n * μ - n * η)).card : ℝ) := by
    have h1 : ((bad.card : ℕ) : ℝ) ≤ (ε₁ : ℝ) * 2 ^ (n * K + r) := by
      have := (Rat.cast_le (K := ℝ)).mpr hbadq
      push_cast at this
      exact this
    have h2 : ((bad.card : ℕ) : ℝ) + (((wordsOfLen (n * K + r)).filter
        (fun w => ¬ blockSum g K n w < n * μ - n * η)).card : ℝ) = 2 ^ (n * K + r) := by
      exact_mod_cast htot
    linarith
  have hc1r : (((wordsOfLen (n * K + r)).filter (fun w => ¬ blockSum g K n w < n * μ - n * η)).card : ℝ)
      ≤ (((wordsOfLen (n * K + r)).filter (fun w => ∀ j (v : ℕ), rowVal A C S w j = Arc.fin v →
        (rate A C - ε) * ((n * K + r : ℕ) : ℝ) ≤ v)).card : ℝ) := by exact_mod_cast hc1
  have hε₁r : (ε₁ : ℝ) * 2 ^ (n * K + r) ≤ ε * 2 ^ (n * K + r) :=
    mul_le_mul_of_nonneg_right hε₁.le (by positivity)
  push_cast at hc1r ⊢
  linarith

/-- **Reduction**: `MinRate` implies `HSP` (Theorem B.1). The set `S` of starting indices and `NeverDies` are used only to build the `NeverDies A C C` passed to `MinRate`. -/
theorem hsp_of_minRate (hMR : MinRate) : HSP := by
  intro D A C S hSC hSsub _hSne hND
  have hNDC : NeverDies A C C := fun w hw => by
    obtain ⟨i, hi, j, hij⟩ := hND w hw
    exact ⟨i, hSsub hi, j, hij⟩
  exact hspAt_of_minRateAt A C S (hMR D A C hSC hNDC)

/-! ### `MinRate` is sharp: `avgMinCap K / K ≤ Λ_C` -/

/-- Superadditivity of the average: `avgMinCap p + avgMinCap q ≤ avgMinCap (p + q)` (the concatenation bijection and superadditivity of `fmin`). -/
theorem hsp_avgMinCap_add {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (p q : ℕ) :
    avgMinCap A C p + avgMinCap A C q ≤ avgMinCap A C (p + q) := by
  have h1 : ∑ w ∈ wordsOfLen (p + q), ((fmin A C (w.take p) : ℚ) + fmin A C (w.drop p)) ≤
      ∑ w ∈ wordsOfLen (p + q), (fmin A C w : ℚ) := by
    refine Finset.sum_le_sum (fun w _ => ?_)
    have := hsp_fmin_append A C (w.take p) (w.drop p)
    rw [List.take_append_drop] at this
    exact_mod_cast this
  rw [hsp_sum_append p q (fun u v => (fmin A C u : ℚ) + fmin A C v)] at h1
  have e : ∑ u ∈ wordsOfLen p, ∑ v ∈ wordsOfLen q, ((fmin A C u : ℚ) + fmin A C v) =
      2 ^ q * ∑ u ∈ wordsOfLen p, (fmin A C u : ℚ) + 2 ^ p * ∑ v ∈ wordsOfLen q, (fmin A C v : ℚ) := by
    simp_rw [Finset.sum_add_distrib, Finset.sum_const, WinLLN.card_words, nsmul_eq_mul,
      ← Finset.mul_sum]
    push_cast; ring
  rw [e] at h1
  unfold avgMinCap
  rw [pow_add, div_add_div _ _ (by positivity) (by positivity)]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- Subadditivity of the average: `avgMax (p + q) ≤ avgMax p + avgMax q`. -/
theorem hsp_avgMax_add {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (p q : ℕ) :
    avgMax A C (p + q) ≤ avgMax A C p + avgMax A C q := by
  have h1 : ∑ w ∈ wordsOfLen (p + q), (fmax A C w : ℚ) ≤
      ∑ w ∈ wordsOfLen (p + q), ((fmax A C (w.take p) : ℚ) + fmax A C (w.drop p)) := by
    refine Finset.sum_le_sum (fun w _ => ?_)
    have := fmax_append_le A C (w.take p) (w.drop p)
    rw [List.take_append_drop] at this
    exact_mod_cast this
  rw [hsp_sum_append p q (fun u v => (fmax A C u : ℚ) + fmax A C v)] at h1
  have e : ∑ u ∈ wordsOfLen p, ∑ v ∈ wordsOfLen q, ((fmax A C u : ℚ) + fmax A C v) =
      2 ^ q * ∑ u ∈ wordsOfLen p, (fmax A C u : ℚ) + 2 ^ p * ∑ v ∈ wordsOfLen q, (fmax A C v : ℚ) := by
    simp_rw [Finset.sum_add_distrib, Finset.sum_const, WinLLN.card_words, nsmul_eq_mul,
      ← Finset.mul_sum]
    push_cast; ring
  rw [e] at h1
  unfold avgMax
  rw [pow_add, div_add_div _ _ (by positivity) (by positivity)]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- If no digit word kills `C`, then `fmin ≤ fmax` on digit words (there is a finite entry). -/
lemma hsp_fmin_le_fmax {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C)
    {w : Word} (hw : IsDigits w) : fmin A C w ≤ fmax A C w := by
  obtain ⟨i, -, j, hij⟩ := hND w hw
  obtain ⟨v, hv⟩ := hsp_ne_zero_iff_fin.mp hij
  exact (hsp_fmin_le_of hv).trans (hsp_le_fmax_of hv)

lemma hsp_avgMinCap_le_avgMax {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C)
    (K : ℕ) : avgMinCap A C K ≤ avgMax A C K := by
  unfold avgMinCap avgMax
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum (fun w hw => ?_)) (by positivity)
  exact_mod_cast hsp_fmin_le_fmax hND (WinLLN.bin_of_mem hw)

lemma hsp_avgMinCap_mul {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (K : ℕ) :
    ∀ n : ℕ, (n : ℚ) * avgMinCap A C K ≤ avgMinCap A C (n * K)
  | 0 => by
    simp only [Nat.cast_zero, zero_mul]
    exact hsp_avgMinCap_nonneg A C _
  | n + 1 => by
    have h := hsp_avgMinCap_add A C (n * K) K
    have ih := hsp_avgMinCap_mul A C K n
    rw [show (n + 1) * K = n * K + K by ring]
    push_cast
    linarith

lemma hsp_avgMax_mul {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (L : ℕ) :
    ∀ n : ℕ, avgMax A C (n * L) ≤ (n : ℚ) * avgMax A C L
  | 0 => by
    simp only [Nat.cast_zero, zero_mul]
    unfold avgMax
    rw [show wordsOfLen 0 = {[]} by
      ext v; constructor
      · intro hv; rw [Finset.mem_singleton]; exact List.eq_nil_of_length_eq_zero
          (length_of_mem_wordsOfLen hv)
      · intro hv; rw [Finset.mem_singleton] at hv; subst hv
        exact mem_wordsOfLen_of rfl (fun s hs => absurd hs List.not_mem_nil)]
    simp [fmax_nil]
  | n + 1 => by
    have h := hsp_avgMax_add A C (n * L) L
    have ih := hsp_avgMax_mul A C L n
    rw [show (n + 1) * L = n * L + L by ring]
    push_cast
    linarith

/-- **Sharpness** (Proposition B.2): if no digit word kills `C`, then `avgMinCap K / K ≤ Λ_C` for every `K ≥ 1`. Hence `MinRateAt` is
equivalent to `sup_K avgMinCap K / K = Λ_C` (by superadditivity `hsp_avgMinCap_add` and Fekete's lemma the `sup` equals the `lim`,
but this is not proved in Lean). Proof: for `L ≥ 1`,
`L · avgMinCap K ≤ avgMinCap (LK) ≤ avgMax (LK) ≤ K · avgMax L`. -/
theorem hsp_avgMinCap_le_rate {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C)
    {K : ℕ} (hK : 1 ≤ K) : ((avgMinCap A C K : ℚ) : ℝ) / K ≤ rate A C := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  refine le_ciInf (fun L => ?_)
  have h1 := hsp_avgMinCap_mul A C K (L + 1)
  have h2 := hsp_avgMinCap_le_avgMax hND ((L + 1) * K)
  have h3 := hsp_avgMax_mul A C (L + 1) K
  rw [show K * (L + 1) = (L + 1) * K by ring] at h3
  have h4 : ((L + 1 : ℕ) : ℚ) * avgMinCap A C K ≤ (K : ℚ) * avgMax A C (L + 1) := by linarith
  have h5 := (Rat.cast_le (K := ℝ)).mpr h4
  push_cast at h5 ⊢
  have hLR : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ hKR hLR]
  linarith

end Collatz.Arctic
