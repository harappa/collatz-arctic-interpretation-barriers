/-
The general form of **Theorem B.7 (KEY)**, including its final form `HKeyTopR`.
The output is `Gen.hKeyTopR_of_swap` and the proof `Gen.specKeyOfSwap` of the frozen statement `SpecKeyOfSwap`
of `Gen/Spec.lean`.

Adapted from `KeyMain4.lean`. Changes:
* The residue `terrasR (parityOf ·)` is replaced by the residue `R` of the block sequence. `R` is used only through its size `hlt` (`R_lt`) and the swap
  `hsw` (`SwapR R e₂ e₃`). `R_prefix` (`hpre`) is among the hypotheses of the statement but is not used.
* The constants $9 \to \nu_2$, $7 \to \nu_3$ (the swap exponents, `e₂`, `e₃` in the code). We use `ν₂ ≤ 13` where `kmExp ≤ V` is derived from the inequality `kmExp + ℓ + 8d + 16 ≤ V + ν₂` for the positions of the coins, and
  where the condition `ℓ + d + 3 ≤ v_j` of Proposition B.6 is derived (`Gen/KeyMain3Q.lean`). The value 9 is not used implicitly
  anywhere. The hypothesis `8 ≤ e₂` of `SpecKeyOfSwap` is not used.
* The choice of the constants (`d`, `t`, `I`, `R = d`, `n_L = 2I + d`, `V = 11 n_L + ℓ`, `λ`, `B`, `k_D`, `n₀`) is the same as for $T$.
  `km_doeblin_const` (independent of the model) is proved again here so that `KeyMain4` of $T$ stays out of the closure.

The analytic components (`SpecCells`, `SpecQavg`, `SpecNine`, `SpecDoeblin`) use the proofs in `KeyAnal*.lean` as they are
(`specCells`, `specQavg`, `specNine`, `specDoeblin`; independent of the system). See Appendix B.2.
-/
import CollatzProof.Arctic.Gen.KeyMain3Q
import CollatzProof.Arctic.Gen.Spec
import CollatzProof.Arctic.KeyAnal3
import CollatzProof.Arctic.KeyAnal4
import CollatzProof.Arctic.KeyAnal5

namespace Collatz.Arctic.Gen

open Collatz.Arctic Finset

/-- `N (3/10)^N ≤ 1` (`(10/3)^N ≥ 1 + 7N/3`). -/
lemma km_doeblin_const (N : ℕ) : (N : ℝ) * (3 / 10 : ℝ) ^ N ≤ 1 := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 7 / 3 by norm_num) N
  have h2 : (1 + 7 / 3 : ℝ) = 10 / 3 := by norm_num
  rw [h2] at h
  have h3 : (10 / 3 : ℝ) ^ N * (3 / 10) ^ N = 1 := by rw [← mul_pow]; norm_num
  have hp : (0 : ℝ) ≤ (3 / 10) ^ N := by positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [mul_le_mul_of_nonneg_right h hp]

/-- **General form of Theorem B.7 (KEY)** (`ℓ ≥ 1`): `n₀` depends only on `(ℓ, τ)`, uniformly in `B₀` and `γ`. -/
theorem km_key_pos {R : List Bool → ℕ} (hlt : ∀ β, R β < 2 ^ (parityOf β).length) {e₂ e₃ : ℕ}
    (he₂ : e₂ ≤ 13) (hsw : SwapR R e₂ e₃)
    (hC : SpecCells) (hQ : SpecQavg) (hN : SpecNine) (hD : SpecDoeblin)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ β₀ γ : List Bool, (parityOf γ).length = ℓ →
      ∑ u ∈ Finset.range (2 ^ ℓ),
        |∑ β ∈ (blockChoices n).filter (fun β =>
            R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length = u), (wtβ β : ℝ)
          - 1 / 2 ^ ℓ| ≤ 2 * τ := by
  -- constants
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < τ / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set d := k₁ + 1 with hd
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) / 2 ^ d ≤ τ / 2 := by
    have e : (2 : ℝ) / 2 ^ d = (1 / 2) ^ k₁ := by
      rw [hd, pow_succ, one_div_pow]; field_simp
    rw [e]; linarith
  set t : ℝ := τ / (2 * 2 ^ ℓ) with ht_def
  have ht : 0 < t := by positivity
  have ht2 : (2 : ℝ) ^ ℓ * t = τ / 2 := by rw [ht_def]; field_simp
  obtain ⟨I, hI⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < τ * t / (2 * (2 ^ d + 1)) by positivity)
    (show (79 / 100 : ℝ) < 1 by norm_num)
  set nL := 2 * I + d with hnL
  set V := 11 * nL + ℓ with hV
  set lamN : ℕ := 2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) with hlamN
  set sN : ℕ := 2 ^ (V - ℓ - d) with hsN
  set B : ℝ := 2 ^ V * (lamN : ℝ) ^ 2 with hB
  set N : ℕ := 2 ^ (V - 3) with hNdef
  have hNpos : 0 < N := by positivity
  set c : ℝ := 1 - (N : ℝ) * (3 / 10 : ℝ) ^ N with hc
  have hc0 : 0 ≤ c := by have := km_doeblin_const N; rw [hc]; linarith
  have hc1 : c < 1 := by
    have : 0 < (N : ℝ) * (3 / 10 : ℝ) ^ N := by
      have : (0 : ℝ) < N := by exact_mod_cast hNpos
      positivity
    rw [hc]; linarith
  have hBpos : 0 < B := by
    have : (0 : ℝ) < lamN := by rw [hlamN]; positivity
    positivity
  obtain ⟨kD, hkD⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < τ * t * ((sN : ℝ) + 1) / (4 * B) by positivity) hc1
  refine ⟨nL + N * kD + V, ?_⟩
  intro n hn β₀ γ hγ
  set ne := n - nL with hne
  have hn' : n = ne + nL := by omega
  have hneV : V ≤ ne := by omega
  have hkd : kD ≤ ne / N := by rw [Nat.le_div_iff_mul_le hNpos]; rw [mul_comm]; omega
  rw [hn']
  -- shape conditions
  have hℓV : (parityOf γ).length ≤ V := by omega
  have hVM : ∀ βe ∈ blockChoices ne, ∀ L ∈ blockChoices nL,
      V ≤ (parityOf (β₀ ++ βe ++ L ++ γ)).length := by
    intro βe hβe L _
    have := (km_parlen_bounds βe).1
    rw [(fam_mem_blockChoices βe ne).mp hβe] at this
    simp only [fam_parityOf_append, List.length_append]
    omega
  have hVL : ∀ L ∈ blockChoices nL, (parityOf L).length + (parityOf γ).length ≤ V := by
    intro L hL
    have := (km_parlen_bounds L).2
    rw [(fam_mem_blockChoices L nL).mp hL] at this
    omega
  have hexp : ∀ L ∈ blockChoices nL, ∀ j : Fin I, kmExp e₂ V L γ j ≤ V := by
    intro L hL j
    have h := km_exp_bounds e₂ V I d ℓ L γ ((fam_mem_blockChoices L nL).mp hL) hγ
      (by rw [← hγ]; exact hVL L hL) j j.isLt
    omega
  -- (a) decomposition of the probability
  have hdec : ∀ u ∈ Finset.range (2 ^ ℓ),
      ∑ β ∈ (blockChoices (ne + nL)).filter (fun β =>
          R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length = u), (wtβ β : ℝ) =
        ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices nL, (wtβ βe : ℝ) * (wtβ L : ℝ) *
          keyCell V ℓ (kmMu R e₂ e₃ V I β₀ βe L γ) u := by
    intro u hu
    have := km_prob_decomp hlt hsw V I ne nL β₀ γ (by omega) hℓV hVM hVL hexp u
      (by rw [hγ]; exact Finset.mem_range.mp hu)
    rw [hγ] at this
    exact this
  rw [Finset.sum_congr rfl (fun u hu => by rw [hdec u hu])]
  refine le_trans (km_tv_mix (blockChoices ne) (blockChoices nL) (fun x => (wtβ x : ℝ))
    (fun y => (wtβ y : ℝ)) km_wt_nonneg km_wt_nonneg (km_wt_sum2 ne nL) (Finset.range (2 ^ ℓ))
    (fun βe L u => keyCell V ℓ (kmMu R e₂ e₃ V I β₀ βe L γ) u) (1 / 2 ^ ℓ)) ?_
  -- (d) apply Proposition B.6 to each `(B_e, L)`
  have hcell : ∀ βe L : List Bool,
      ∑ u ∈ Finset.range (2 ^ ℓ), |keyCell V ℓ (kmMu R e₂ e₃ V I β₀ βe L γ) u - 1 / 2 ^ ℓ| ≤
        (2 / 2 ^ d + 2 ^ ℓ * t) +
          keyQ V lamN (kmMu R e₂ e₃ V I β₀ βe L γ) / (t * ((sN : ℝ) + 1)) := by
    intro βe L
    have h := hC V ℓ d hℓ hd1 (by omega) (kmMu R e₂ e₃ V I β₀ βe L γ)
      (km_law_nonneg _ _ _ _) (km_law_sum _ _ _ _) t ht
    have hs : ((sN : ℕ) : ℝ) = (2 : ℝ) ^ (V - ℓ - d) := by rw [hsN]; push_cast; ring
    rw [hs]
    linarith
  have hEQ := km_EQ R hQ hN hD e₂ e₃ V ℓ d I d ne he₂ hℓ hd1 le_rfl β₀ γ hγ (by omega) (by omega)
  -- conclusion
  set Doe : ℝ := 2 * (1 - ((2 ^ (V - 3) : ℕ) : ℝ) * (3 / 10 : ℝ) ^ (2 ^ (V - 3))) ^ (ne / 2 ^ (V - 3))
    with hDoe
  set EQ := ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices nL, (wtβ βe : ℝ) * (wtβ L : ℝ) *
      keyQ V lamN (kmMu R e₂ e₃ V I β₀ βe L γ) with hEQdef
  have hsum1 : ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices nL, (wtβ βe : ℝ) * (wtβ L : ℝ) *
      ∑ u ∈ Finset.range (2 ^ ℓ), |keyCell V ℓ (kmMu R e₂ e₃ V I β₀ βe L γ) u - 1 / 2 ^ ℓ| ≤
      (2 / 2 ^ d + 2 ^ ℓ * t) + EQ / (t * ((sN : ℝ) + 1)) := by
    calc _ ≤ ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices nL, (wtβ βe : ℝ) * (wtβ L : ℝ) *
          ((2 / 2 ^ d + 2 ^ ℓ * t) +
            keyQ V lamN (kmMu R e₂ e₃ V I β₀ βe L γ) / (t * ((sN : ℝ) + 1))) := by
          refine Finset.sum_le_sum (fun βe _ => Finset.sum_le_sum (fun L _ => ?_))
          exact mul_le_mul_of_nonneg_left (hcell βe L)
            (mul_nonneg (km_wt_nonneg βe) (km_wt_nonneg L))
      _ = (2 / 2 ^ d + 2 ^ ℓ * t) *
            (∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices nL, (wtβ βe : ℝ) * (wtβ L : ℝ)) +
          EQ / (t * ((sN : ℝ) + 1)) := by
          rw [hEQdef, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun βe _ => ?_)
          rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun L _ => ?_)
          ring
      _ = _ := by rw [km_wt_sum2, mul_one]
  refine le_trans hsum1 ?_
  -- numerical estimates
  have hDoe2 : Doe ≤ 2 * c ^ kD := by
    rw [hDoe]
    have := pow_le_pow_of_le_one hc0 hc1.le hkd
    have e : (1 - ((2 ^ (V - 3) : ℕ) : ℝ) * (3 / 10 : ℝ) ^ (2 ^ (V - 3))) = c := by rw [hc]
    rw [e]; linarith
  have hlam : (lamN : ℝ) ≤ (2 ^ d + 1) * ((sN : ℝ) + 1) := by
    have e : 2 ^ (V - ℓ) = 2 ^ d * 2 ^ (V - ℓ - d) := by
      rw [← pow_add]; congr 1; omega
    have : (lamN : ℝ) = (2 ^ d + 1) * (sN : ℝ) := by
      rw [hlamN, hsN, e]; push_cast; ring
    rw [this]
    have : (0 : ℝ) ≤ 2 ^ d + 1 := by positivity
    nlinarith
  have hs0 : (0 : ℝ) < (sN : ℝ) + 1 := by positivity
  have hEQ' : EQ ≤ τ * t * ((sN : ℝ) + 1) := by
    have h1 : (lamN : ℝ) * (79 / 100) ^ I ≤ τ * t * ((sN : ℝ) + 1) / 2 := by
      have hr : (79 / 100 : ℝ) ^ I * (2 * (2 ^ d + 1)) ≤ τ * t := by
        have := hI
        rw [lt_div_iff₀ (by positivity)] at this
        linarith
      have hr0 : (0 : ℝ) ≤ (79 / 100) ^ I := by positivity
      calc (lamN : ℝ) * (79 / 100) ^ I ≤ (2 ^ d + 1) * ((sN : ℝ) + 1) * (79 / 100) ^ I :=
            mul_le_mul_of_nonneg_right hlam hr0
        _ = ((79 / 100 : ℝ) ^ I * (2 * (2 ^ d + 1))) * (((sN : ℝ) + 1) / 2) := by ring
        _ ≤ τ * t * (((sN : ℝ) + 1) / 2) := mul_le_mul_of_nonneg_right hr (by positivity)
        _ = τ * t * ((sN : ℝ) + 1) / 2 := by ring
    have h2 : B * Doe ≤ τ * t * ((sN : ℝ) + 1) / 2 := by
      have hk : c ^ kD * (4 * B) ≤ τ * t * ((sN : ℝ) + 1) := by
        have := hkD
        rw [lt_div_iff₀ (by positivity)] at this
        linarith
      calc B * Doe ≤ B * (2 * c ^ kD) := mul_le_mul_of_nonneg_left hDoe2 hBpos.le
        _ = (c ^ kD * (4 * B)) / 2 := by ring
        _ ≤ τ * t * ((sN : ℝ) + 1) / 2 := by linarith
    have hEQ2 : EQ ≤ (lamN : ℝ) * (79 / 100) ^ I + B * Doe := hEQ
    linarith
  have hfin : EQ / (t * ((sN : ℝ) + 1)) ≤ τ := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith

/-- For `ℓ = 0` we have `U = 0`, so the left-hand side is 0 (uses only `R_lt`). -/
lemma km_key_zero {R : List Bool → ℕ} (hlt : ∀ β, R β < 2 ^ (parityOf β).length) (n : ℕ)
    (β₀ γ : List Bool) (hγ : (parityOf γ).length = 0) (τ : ℝ) (hτ : 0 < τ) :
    ∑ u ∈ Finset.range (2 ^ (parityOf γ).length),
      |∑ β ∈ (blockChoices n).filter (fun β =>
          R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length = u), (wtβ β : ℝ)
        - 1 / 2 ^ (parityOf γ).length| ≤ 2 * τ := by
  rw [hγ, pow_zero, Finset.sum_range_one]
  have hall : (blockChoices n).filter (fun β =>
      R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length = 0) = blockChoices n := by
    apply Finset.filter_true_of_mem
    intro β _
    apply Nat.div_eq_of_lt
    have := hlt (β₀ ++ β ++ γ)
    rwa [fam_parityOf_append (β₀ ++ β) γ, List.length_append, hγ, add_zero] at this
  rw [hall, km_wt_sum]
  norm_num
  linarith

/-- Theorem B.7 uniformly in `ℓ ≤ L₀` (`n₀` depends only on `L₀` and `τ`). -/
theorem km_key_upto {R : List Bool → ℕ} (hlt : ∀ β, R β < 2 ^ (parityOf β).length) {e₂ e₃ : ℕ}
    (he₂ : e₂ ≤ 13) (hsw : SwapR R e₂ e₃)
    (hC : SpecCells) (hQ : SpecQavg) (hN : SpecNine) (hD : SpecDoeblin)
    (τ : ℝ) (hτ : 0 < τ) (L₀ : ℕ) :
    ∃ n₀ : ℕ, ∀ ℓ ≤ L₀, ∀ n ≥ n₀, ∀ β₀ γ : List Bool, (parityOf γ).length = ℓ →
      ∑ u ∈ Finset.range (2 ^ ℓ),
        |∑ β ∈ (blockChoices n).filter (fun β =>
            R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length = u), (wtβ β : ℝ)
          - 1 / 2 ^ ℓ| ≤ 2 * τ := by
  induction L₀ with
  | zero =>
    refine ⟨0, fun ℓ hℓ n _ β₀ γ hγ => ?_⟩
    have hℓ0 : ℓ = 0 := by omega
    subst hℓ0
    have := km_key_zero hlt n β₀ γ hγ τ hτ
    rwa [hγ] at this
  | succ L₀ ih =>
    obtain ⟨n₁, h₁⟩ := ih
    obtain ⟨n₂, h₂⟩ := km_key_pos hlt he₂ hsw hC hQ hN hD (L₀ + 1) (by omega) τ hτ
    refine ⟨max n₁ n₂, fun ℓ hℓ n hn β₀ γ hγ => ?_⟩
    rcases Nat.lt_or_ge ℓ (L₀ + 1) with h | h
    · exact h₁ ℓ (by omega) n (le_trans (le_max_left _ _) hn) β₀ γ hγ
    · have hℓ' : ℓ = L₀ + 1 := by omega
      subst hℓ'
      exact h₂ n (le_trans (le_max_right _ _) hn) β₀ γ hγ

/-- **General form of Theorem B.7 in the form `HKeyTopR`**: assuming the analytic components, `HKeyTopR R` follows from `R_lt` and `SwapR R e₂ e₃` (`ν₂ ≤ 13`). -/
theorem hKeyTopR_of_specs {R : List Bool → ℕ} (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    {e₂ e₃ : ℕ} (he₂ : e₂ ≤ 13) (hsw : SwapR R e₂ e₃)
    (hC : SpecCells) (hQ : SpecQavg) (hN : SpecNine) (hD : SpecDoeblin) : HKeyTopR R := by
  intro K τ hτ
  obtain ⟨n₀, h⟩ := km_key_upto hlt he₂ hsw hC hQ hN hD (τ : ℝ) (by exact_mod_cast hτ) (11 * K)
  refine ⟨n₀, fun n hn β₀ γ hγK => ?_⟩
  have hℓ : (parityOf γ).length ≤ 11 * K := by
    have := (km_parlen_bounds γ).2; rwa [hγK] at this
  have h' := h (parityOf γ).length hℓ n hn β₀ γ rfl
  refine (Rat.cast_le (K := ℝ)).mp ?_
  push_cast
  exact h'

/-- **General form of the swap argument**: `HKeyTopR R` follows from the size of the residue `R` and the translation by swaps `SwapR R e₂ e₃`
(`ν₂ ≤ 13`; `ν₂ = 9` for $T$ and `ν₂ = 8` for $H$). `hpre` (`R_prefix`) is not used. -/
theorem hKeyTopR_of_swap (R : List Bool → ℕ) (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    (_hpre : ∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁)
    (e₂ e₃ : ℕ) (he₂ : e₂ ≤ 13) (hsw : SwapR R e₂ e₃) : HKeyTopR R :=
  hKeyTopR_of_specs hlt he₂ hsw specCells specQavg specNine specDoeblin

/-- **Output of this file** (the frozen statement `SpecKeyOfSwap`). -/
theorem specKeyOfSwap : SpecKeyOfSwap :=
  fun R hlt hpre e₂ e₃ _ he₂ hsw => hKeyTopR_of_swap R hlt hpre e₂ e₃ (by omega) hsw

end Collatz.Arctic.Gen
