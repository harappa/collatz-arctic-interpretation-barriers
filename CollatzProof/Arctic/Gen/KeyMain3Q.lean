/-
The general form of the expectation of `Q_λ` in the proof of Theorem B.7 (KEY).
The formula for a fixed `(B_e, L)` and the decomposition of the probability are in `Gen/KeyMain3.lean`.

Adapted from the second half of `KeyMain3.lean` (from `km_tv_mix` to `km_EQ`). Changes:
* The constants $9 \to \nu_2$, $7 \to \nu_3$ (arguments of `kmPhi`, `kmMu`; the swap exponents, `e₂`, `e₃` in the code). The lower bound `ℓ + d + 3 ≤ v_j` for the positions of the coins
  follows from `kmExp + ℓ + 8R + 16 ≤ V + ν₂` (`Gen.km_exp_bounds`), `d ≤ R` and `ν₂ ≤ 13` (for $T$, `ν₂ = 9`).
  That `v_j` strictly decreases also follows from `ν₂ ≤ 13`. The value 9 is not used implicitly anywhere.
* The number of tail blocks of the late part is written `nR` (`R` for $T$; renamed to distinguish it from the residue function `R`).
* `km_tv_mix` and `km_one_val` (independent of the model) are proved again here so that `KeyMain3` of $T$ stays out of the closure.
* `km_w_bound` and `km_coin_avg` of `KeyMain2` (`9 = 3^2`, and `79/100`, `7/10`) are used as they are.
-/
import CollatzProof.Arctic.Gen.KeyMain3

namespace Collatz.Arctic.Gen

open Collatz.Arctic Finset

/-- Mixing of total variation: if `P(u) = Σ_p W(p) c(p, u)` (`W ≥ 0`, `Σ W = 1`), then
`Σ_u |P(u) - a| ≤ Σ_p W(p) Σ_u |c(p, u) - a|`. -/
lemma km_tv_mix (S T : Finset (List Bool)) (W1 W2 : List Bool → ℝ) (hW1 : ∀ x, 0 ≤ W1 x)
    (hW2 : ∀ y, 0 ≤ W2 y) (hsum : ∑ x ∈ S, ∑ y ∈ T, W1 x * W2 y = 1) (U : Finset ℕ)
    (c : List Bool → List Bool → ℕ → ℝ) (a : ℝ) :
    ∑ u ∈ U, |∑ x ∈ S, ∑ y ∈ T, W1 x * W2 y * c x y u - a| ≤
      ∑ x ∈ S, ∑ y ∈ T, W1 x * W2 y * ∑ u ∈ U, |c x y u - a| := by
  have h1 : ∀ u ∈ U, |∑ x ∈ S, ∑ y ∈ T, W1 x * W2 y * c x y u - a| ≤
      ∑ x ∈ S, ∑ y ∈ T, W1 x * W2 y * |c x y u - a| := by
    intro u _
    have e : ∑ x ∈ S, ∑ y ∈ T, W1 x * W2 y * c x y u - a =
        ∑ x ∈ S, ∑ y ∈ T, W1 x * W2 y * (c x y u - a) := by
      conv_lhs => rw [← mul_one a, ← hsum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      ring
    rw [e]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun x _ => ?_))
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun y _ => ?_))
    rw [abs_mul, abs_of_nonneg (mul_nonneg (hW1 x) (hW2 y))]
  refine le_trans (Finset.sum_le_sum h1) (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.mul_sum]

lemma km_one_val (V : ℕ) (hV : 1 ≤ V) : (1 : ZMod (2 ^ V)).val = 1 := by
  apply ZMod.val_one''
  have : 2 ≤ 2 ^ V := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ V := Nat.pow_le_pow_right (by norm_num) hV
  omega

/-- **Application of Proposition B.6** in steps (b) and (c) of the proof of Theorem B.7: the average of `Φ_L` over the residue class `{w ≡ 1 (mod 8)}` is
`2^{-M(L)}(λ - λ^2 2^{-V})` (`ν₂ ≤ 13`). -/
theorem km_Qavg_apply (hQ : SpecQavg) (e₂ e₃ V ℓ d I nR : ℕ) (he₂ : e₂ ≤ 13) (hℓ : 1 ≤ ℓ)
    (hd : 1 ≤ d) (hdR : d ≤ nR) (β₀ : List Bool) (ne : ℕ) (L ζ : List Bool)
    (hL : L.length = 2 * I + nR) (hζ : (parityOf ζ).length = ℓ)
    (hVL : (parityOf L).length + ℓ ≤ V) (hV3 : ℓ + d + 3 ≤ V) :
    (∑ w ∈ Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1),
        kmPhi e₂ e₃ V ℓ d I β₀ ne L ζ w) /
        ((Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1)).card : ℝ) =
      (1 / 2 ^ (Finset.univ.filter (fun j : Fin I => kmOri L j ≠ 0)).card) *
        ((2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) - (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) ^ 2 / 2 ^ V) := by
  have ho : ∀ j : Fin I, kmOri L j = -1 ∨ kmOri L j = 0 ∨ kmOri L j = 1 := by
    intro j; unfold kmOri; split_ifs <;> simp
  have hω : ∀ j : Fin I, (kmOmega e₃ V β₀ ne L j).val % 2 = 1 := by
    intro j; unfold kmOmega; exact km_i3_pow_odd V (by omega) _
  have hb : ∀ j : Fin I, kmExp e₂ V L ζ j + ℓ + 8 * nR + 16 ≤ V + e₂ ∧
      kmExp e₂ V L ζ j = (kmPre L j).length + e₂ + (V - (parityOf L).length - ℓ) :=
    fun j => km_exp_bounds e₂ V I nR ℓ L ζ hL hζ hVL j j.isLt
  have hv : ∀ i j : Fin I, i < j → kmV e₂ V L ζ j < kmV e₂ V L ζ i := by
    intro i j hij
    have hm := km_pre_mono L i j hij (by have := j.isLt; omega)
    have hi := hb i
    have hj := hb j
    unfold kmV; omega
  have hvb : ∀ j : Fin I, ℓ + d + 3 ≤ kmV e₂ V L ζ j ∧ kmV e₂ V L ζ j ≤ V := by
    intro j
    have hj := hb j
    unfold kmV; omega
  have hw₀ : (1 : ZMod (2 ^ V)).val % 2 = 1 := by rw [km_one_val V (by omega)]
  have h := hQ V ℓ d I hℓ hd hV3 (fun j => kmOri L j) (fun j => kmOmega e₃ V β₀ ne L j)
    (fun j => kmV e₂ V L ζ j) (fun _ => 0) 1 ho hω hv hvb hw₀
  have h8 : (1 : ZMod (2 ^ V)).val % 8 = 1 := by rw [km_one_val V (by omega)]
  rw [h8] at h
  unfold kmPhi kmCoef
  exact h

/-- **Steps (c) and (d) of the proof of Theorem B.7**: `E_{(B_e, L)} Q_λ(μ_B) ≤ λ (79/100)^I + B · 2(1 - N(3/10)^N)^{⌊n_e/N⌋}`. -/
theorem km_EQ (R : List Bool → ℕ) (hQ : SpecQavg) (hN : SpecNine) (hD : SpecDoeblin)
    (e₂ e₃ V ℓ d I nR ne : ℕ) (he₂ : e₂ ≤ 13) (hℓ : 1 ≤ ℓ) (hd : 1 ≤ d) (hdR : d ≤ nR)
    (β₀ γ : List Bool) (hγ : (parityOf γ).length = ℓ)
    (hVL : 11 * (2 * I + nR) + ℓ ≤ V) (hV3 : ℓ + d + 3 ≤ V) :
    ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices (2 * I + nR), (wtβ βe : ℝ) * (wtβ L : ℝ) *
        keyQ V (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d)) (kmMu R e₂ e₃ V I β₀ βe L γ) ≤
      ((2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℕ) : ℝ) * (79 / 100) ^ I +
        2 ^ V * ((2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℕ) : ℝ) ^ 2 *
          (2 * (1 - ((2 ^ (V - 3) : ℕ) : ℝ) * (3 / 10 : ℝ) ^ (2 ^ (V - 3))) ^ (ne / 2 ^ (V - 3))) := by
  set lamN : ℕ := 2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) with hlamN
  set B : ℝ := 2 ^ V * (lamN : ℝ) ^ 2 with hB
  set Doe : ℝ := 2 * (1 - ((2 ^ (V - 3) : ℕ) : ℝ) * (3 / 10 : ℝ) ^ (2 ^ (V - 3))) ^ (ne / 2 ^ (V - 3))
    with hDoe
  -- `Q_λ(μ_B) = Φ_L(w)`
  have hQΦ : ∀ βe ∈ blockChoices ne, ∀ L : List Bool,
      keyQ V lamN (kmMu R e₂ e₃ V I β₀ βe L γ) =
        kmPhi e₂ e₃ V ℓ d I β₀ ne L γ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ βe.count false) := by
    intro βe hβe L
    unfold kmMu kmPhi
    rw [km_Q_shift, (fam_mem_blockChoices βe ne).mp hβe]
  have hΦ0 : ∀ L w, 0 ≤ kmPhi e₂ e₃ V ℓ d I β₀ ne L γ w := fun L w => km_Q_nonneg _ _ _
  have hΦB : ∀ L w, kmPhi e₂ e₃ V ℓ d I β₀ ne L γ w ≤ B := fun L w =>
    km_Q_le _ _ _ (km_law_nonneg _ _ _ _) (km_law_le_one _ _ _ _)
  calc ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices (2 * I + nR), (wtβ βe : ℝ) * (wtβ L : ℝ) *
        keyQ V lamN (kmMu R e₂ e₃ V I β₀ βe L γ)
      = ∑ L ∈ blockChoices (2 * I + nR), (wtβ L : ℝ) * ∑ βe ∈ blockChoices ne, (wtβ βe : ℝ) *
          kmPhi e₂ e₃ V ℓ d I β₀ ne L γ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ βe.count false) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun L _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun βe hβe => ?_)
        rw [hQΦ βe hβe L]; ring
    _ ≤ ∑ L ∈ blockChoices (2 * I + nR), (wtβ L : ℝ) *
          ((1 / 2 ^ (Finset.univ.filter (fun j : Fin I => kmOri L j ≠ 0)).card) * lamN + B * Doe) := by
        refine Finset.sum_le_sum (fun L hLm => mul_le_mul_of_nonneg_left ?_ (km_wt_nonneg L))
        have hLl : L.length = 2 * I + nR := (fam_mem_blockChoices L _).mp hLm
        have hpL : (parityOf L).length + ℓ ≤ V := by
          have := (km_parlen_bounds L).2; rw [hLl] at this; omega
        have hw := km_w_bound hN hD V (by omega) (kmPhi e₂ e₃ V ℓ d I β₀ ne L γ) B (hΦ0 L) (hΦB L) ne
        rw [km_Qavg_apply hQ e₂ e₃ V ℓ d I nR he₂ hℓ hd hdR β₀ ne L γ hLl hγ hpL hV3] at hw
        refine le_trans hw (add_le_add ?_ le_rfl)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hl : ((lamN : ℕ) : ℝ) = (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) := by
          rw [hlamN]; push_cast; ring
        rw [hl]
        have : 0 ≤ (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) ^ 2 / 2 ^ V := by positivity
        linarith
    _ = (lamN : ℝ) * (79 / 100) ^ I + B * Doe := by
        have hc := km_coin_avg nR I
        have hs := km_wt_sum (2 * I + nR)
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hs, one_mul]
        congr 1
        rw [← hc, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun L _ => ?_)
        ring

end Collatz.Arctic.Gen
