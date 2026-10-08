/-
Theorem B.7 (KEY) in the swap argument: the formula for a single `(β_e, L)` and the expectation.

Notation: the block sequence `β = β_e ++ L` (the early part `β_e` has `n_e` blocks, the late part `L` has `2I + R` blocks, the first `2I` of which form
`I` adjacent coins), `π = par(β₀ ++ β_e)`, `ζ = par Γ`, `ℓ = |ζ|`, `m = |π| + |par L| + ℓ`.
* `kmOmega` (`ω_j = 3^{-(a(β₀) + 5n_e + c_j + 7)}`), `kmV` (`v_j`), `kmCoef` (`a_j(w) = o_j ω_j 2^{V-v_j} w`),
  `kmRho` (the top `V` digits `ρ(β^e)`), `kmMu` (`μ_β`), `kmPhi` (`Φ_L(w) = Q_λ(μ_w)`, base point 0).
* `km_exp_bounds`, `km_pre_mono`: inequalities for the positions of the coins (`v_j` strictly decreasing, `ℓ + 8R + 7 ≤ v_j ≤ V`).
* `km_pair_shift`: Lemma B.5 (iii) written with `ω_j` and `w = 9^{-Y_e}` (`a(par β_e) = 5n_e + 2Y_e`).
* `km_U_eq`, `km_pair_cell`: the `U(β^e)` of the statement is the top `ℓ` digits of `ρ(β^e)`, and `μ_β(C_u)` is the proportion of swap choices with `U(β^e) = u`.
* `km_prob_decomp`: **step (a) of the proof of Theorem B.7**, `Pr(U = u) = E_{(β_e, L)} μ_β(C_u)`.
* `km_tv_mix`: the triangle inequality for total variation.
* `km_Qavg_apply`: **step (b) of the proof of Theorem B.7**. Apply Proposition B.6 (`SpecQavg`, `z₀ = 0`, `w₀ = 1`) to `Φ_L`.
* `km_EQ`: **steps (c), (d) of the proof of Theorem B.7**, `E Q_λ(μ_β) ≤ λ(79/100)^I + B · 2(1 - N(3/10)^N)^{⌊n_e/N⌋}`.
-/
import CollatzProof.Arctic.KeyMain2
import CollatzProof.Arctic.HTWCut

namespace Collatz.Arctic

open Finset

/-! ### Quantities of the early part and the late part -/

/-- `ω_j = 3^{-(a(β₀) + 5 n_e + c_j + 7)}` of coin `j` (`c_j` is the number of odd steps of the late part before coin `j`). -/
def kmOmega (V : ℕ) (β₀ : List Bool) (ne : ℕ) (L : List Bool) (j : ℕ) : ZMod (2 ^ V) :=
  ((3 : ZMod (2 ^ V))⁻¹) ^ (terrasA (parityOf β₀) + 5 * ne + terrasA (kmPre L j) + 7)

/-- `v_j` of coin `j` (`V - v_j` is the exponent of the power of 2 in the translation of the coin). -/
def kmV (V : ℕ) (L ζ : List Bool) (j : ℕ) : ℕ := V - kmExp V L ζ j

/-- The translation of a coin, `a_j(w) = o_j ω_j 2^{V - v_j} w` (the form of Proposition B.6). -/
def kmCoef (V I : ℕ) (β₀ : List Bool) (ne : ℕ) (L ζ : List Bool) (w : ZMod (2 ^ V)) (j : Fin I) :
    ZMod (2 ^ V) :=
  (kmOri L j : ZMod (2 ^ V)) * kmOmega V β₀ ne L j * 2 ^ (V - kmV V L ζ j) * w

/-- The top `V` digits `ρ(β^e)` (`π` is the parity word of the preceding part). -/
def kmRho (V I : ℕ) (π L ζ : List Bool) (e : Fin I → Bool) : ℕ :=
  terrasR (π ++ parityOf (kmSwap I e L) ++ ζ) / 2 ^ ((π ++ parityOf L ++ ζ).length - V)

/-- The law `μ_β` (modulo `2^V`) of `ρ(β^e)` for uniform swap choices `e`. -/
noncomputable def kmMu (V I : ℕ) (β₀ βe L ζ : List Bool) : ZMod (2 ^ V) → ℝ :=
  keyLaw V I ((kmRho V I (parityOf (β₀ ++ βe)) L ζ (fun _ => false) : ℕ) : ZMod (2 ^ V))
    (kmCoef V I β₀ βe.length L ζ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ βe.count false))

/-- `Φ_L(w) = Q_λ(μ_w)` (base point 0). -/
noncomputable def kmPhi (V ℓ d I : ℕ) (β₀ : List Bool) (ne : ℕ) (L ζ : List Bool) (w : ZMod (2 ^ V)) : ℝ :=
  keyQ V (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d)) (keyLaw V I 0 (kmCoef V I β₀ ne L ζ w))

/-! ### Positions of the coins of the late part -/

lemma km_pre_drop (L : List Bool) (j : ℕ) :
    (parityOf L).length = (kmPre L j).length + (parityOf (L.drop (2 * j))).length := by
  unfold kmPre
  rw [← List.length_append, ← fam_parityOf_append, List.take_append_drop]

lemma km_drop_ge (L : List Bool) (j : ℕ) :
    8 * (L.length - 2 * j) ≤ (parityOf (L.drop (2 * j))).length := by
  have := (parityOf_length_bounds (L.drop (2 * j))).1
  rw [List.length_drop] at this
  exact this

lemma km_pre_mono (L : List Bool) (i j : ℕ) (hij : i < j) (hj : 2 * j ≤ L.length) :
    (kmPre L i).length + 16 ≤ (kmPre L j).length := by
  have h := htw_blockEnd_ge L (2 * i) (2 * (j - i)) (by omega)
  unfold blockEnd at h
  unfold kmPre
  rw [show 2 * i + 2 * (j - i) = 2 * j by omega] at h
  omega

/-- Inequalities for the positions of the coins (the late part `L` has `2I + R` blocks, `V ≥ |par L| + ℓ`). -/
lemma km_exp_bounds (V I R ℓ : ℕ) (L ζ : List Bool) (hL : L.length = 2 * I + R) (hζ : ζ.length = ℓ)
    (hVL : (parityOf L).length + ℓ ≤ V) (j : ℕ) (hj : j < I) :
    kmExp V L ζ j + ℓ + 8 * R + 7 ≤ V ∧
      kmExp V L ζ j = (kmPre L j).length + 9 + (V - (parityOf L).length - ℓ) := by
  have h1 := km_pre_drop L j
  have h2 := km_drop_ge L j
  unfold kmExp
  rw [hζ]
  constructor <;> omega

/-! ### The formula for a single `(β_e, L)` -/

/-- `ρ(β^e) < 2^V`. -/
lemma km_rho_lt (V I : ℕ) (π L ζ : List Bool) (hVM : V ≤ (π ++ parityOf L ++ ζ).length)
    (e : Fin I → Bool) : kmRho V I π L ζ e < 2 ^ V := by
  unfold kmRho
  set M := (π ++ parityOf L ++ ζ).length with hM
  have hlt : terrasR (π ++ parityOf (kmSwap I e L) ++ ζ) < 2 ^ M := by
    have := terrasR_lt (π ++ parityOf (kmSwap I e L) ++ ζ)
    simp only [List.length_append, km_swap_parlen] at this
    rw [hM]; simpa only [List.length_append] using this
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hVM]
  exact hlt

/-- **Lemma B.5 (iii) written with `ω_j` and `w`**: `ρ(β^e) = ρ(β) + Σ_j e_j a_j(w)`, `w = 9^{-Y_e}`. -/
theorem km_pair_shift (V I : ℕ) (β₀ βe L ζ : List Bool) (hL : 2 * I ≤ L.length)
    (hVM : V ≤ (parityOf (β₀ ++ βe) ++ parityOf L ++ ζ).length)
    (hVL : (parityOf L).length + ζ.length ≤ V) (hexp : ∀ j : Fin I, kmExp V L ζ j ≤ V)
    (e : Fin I → Bool) :
    (kmRho V I (parityOf (β₀ ++ βe)) L ζ e : ZMod (2 ^ V)) =
      (kmRho V I (parityOf (β₀ ++ βe)) L ζ (fun _ => false) : ZMod (2 ^ V)) +
        ∑ j, (if e j then kmCoef V I β₀ βe.length L ζ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ βe.count false) j
          else 0) := by
  unfold kmRho
  rw [km_swap_false, km_rho_shift I V _ e _ L ζ hL rfl hVM (by omega)]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · unfold kmCoef kmOmega kmV
    rw [Nat.sub_sub_self (hexp j), fam_parityOf_append, terrasA_append,
      km_par_A_count βe, fam_length_eq_count βe]
    ring
  · rfl

/-- The `U` of the statement is the top `ℓ` digits of `ρ`. -/
lemma km_U_eq (V I : ℕ) (β₀ βe L γ : List Bool) (e : Fin I → Bool) (hℓV : (parityOf γ).length ≤ V)
    (hVM : V ≤ (parityOf (β₀ ++ βe) ++ parityOf L ++ parityOf γ).length) :
    terrasR (parityOf (β₀ ++ (βe ++ kmSwap I e L) ++ γ)) / 2 ^ (parityOf (β₀ ++ (βe ++ kmSwap I e L))).length =
      kmRho V I (parityOf (β₀ ++ βe)) L (parityOf γ) e / 2 ^ (V - (parityOf γ).length) := by
  unfold kmRho
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  have e1 : parityOf (β₀ ++ (βe ++ kmSwap I e L) ++ γ) =
      parityOf (β₀ ++ βe) ++ parityOf (kmSwap I e L) ++ parityOf γ := by
    simp only [fam_parityOf_append, List.append_assoc]
  have e2 : (parityOf (β₀ ++ (βe ++ kmSwap I e L))).length =
      (parityOf (β₀ ++ βe) ++ parityOf L ++ parityOf γ).length - V + (V - (parityOf γ).length) := by
    simp only [fam_parityOf_append, List.length_append, km_swap_parlen] at hVM ⊢
    omega
  rw [e1, e2]

/-- **The cells in step (a) of the proof of Theorem B.7**: `μ_β(C_u)` is the proportion of swap choices `e` for which the `U(β^e)` of the statement is `u`. -/
theorem km_pair_cell (V I : ℕ) (β₀ βe L γ : List Bool) (hL : 2 * I ≤ L.length)
    (hℓV : (parityOf γ).length ≤ V)
    (hVM : V ≤ (parityOf (β₀ ++ βe) ++ parityOf L ++ parityOf γ).length)
    (hVL : (parityOf L).length + (parityOf γ).length ≤ V)
    (hexp : ∀ j : Fin I, kmExp V L (parityOf γ) j ≤ V) (u : ℕ) (hu : u < 2 ^ (parityOf γ).length) :
    keyCell V (parityOf γ).length (kmMu V I β₀ βe L (parityOf γ)) u =
      (1 / 2 ^ I) * ∑ e : Fin I → Bool,
        (if terrasR (parityOf (β₀ ++ (βe ++ kmSwap I e L) ++ γ)) /
            2 ^ (parityOf (β₀ ++ (βe ++ kmSwap I e L))).length = u then (1 : ℝ) else 0) := by
  unfold kmMu
  rw [km_cell V _ I hℓV _ _ (fun e => kmRho V I (parityOf (β₀ ++ βe)) L (parityOf γ) e)
    (fun e => km_rho_lt V I _ L _ hVM e) (fun e => km_pair_shift V I β₀ βe L _ hL hVM hVL hexp e) u hu]
  congr 1
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [km_U_eq V I β₀ βe L γ e hℓV hVM]

/-- Decomposition of the probability: `Pr(U = u) = E_{(β_e, L)} μ_β(C_u)`. -/
theorem km_prob_decomp (V I ne nL : ℕ) (β₀ γ : List Bool) (hL : 2 * I ≤ nL)
    (hℓV : (parityOf γ).length ≤ V)
    (hVM : ∀ βe ∈ blockChoices ne, ∀ L ∈ blockChoices nL,
      V ≤ (parityOf (β₀ ++ βe) ++ parityOf L ++ parityOf γ).length)
    (hVL : ∀ L ∈ blockChoices nL, (parityOf L).length + (parityOf γ).length ≤ V)
    (hexp : ∀ L ∈ blockChoices nL, ∀ j : Fin I, kmExp V L (parityOf γ) j ≤ V)
    (u : ℕ) (hu : u < 2 ^ (parityOf γ).length) :
    ∑ β ∈ (blockChoices (ne + nL)).filter (fun β =>
        terrasR (parityOf (β₀ ++ β ++ γ)) / 2 ^ (parityOf (β₀ ++ β)).length = u), (wtβ β : ℝ) =
      ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices nL, (wtβ βe : ℝ) * (wtβ L : ℝ) *
        keyCell V (parityOf γ).length (kmMu V I β₀ βe L (parityOf γ)) u := by
  rw [Finset.sum_filter, km_sum_append ne nL]
  refine Finset.sum_congr rfl (fun βe hβe => ?_)
  have h1 : ∑ L ∈ blockChoices nL, (if terrasR (parityOf (β₀ ++ (βe ++ L) ++ γ)) /
        2 ^ (parityOf (β₀ ++ (βe ++ L))).length = u then (wtβ (βe ++ L) : ℝ) else 0) =
      (wtβ βe : ℝ) * ∑ L ∈ blockChoices nL, (wtβ L : ℝ) *
        (if terrasR (parityOf (β₀ ++ (βe ++ L) ++ γ)) /
          2 ^ (parityOf (β₀ ++ (βe ++ L))).length = u then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun L _ => ?_)
    rw [km_wt_append]; push_cast
    split_ifs <;> ring
  rw [h1, km_swap_avg I nL, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun L hLm => ?_)
  have hLl : L.length = nL := (fam_mem_blockChoices L nL).mp hLm
  rw [km_pair_cell V I β₀ βe L γ (by omega) hℓV (hVM βe hβe L hLm) (hVL L hLm) (hexp L hLm) u hu]
  ring

/-- Mixing in total variation: if `P(u) = Σ_p W(p) c(p, u)` (`W ≥ 0`, `Σ W = 1`), then
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

/-! ### The expectation of `Q_λ` -/

lemma km_one_val (V : ℕ) (hV : 1 ≤ V) : (1 : ZMod (2 ^ V)).val = 1 := by
  apply ZMod.val_one''
  have : 2 ≤ 2 ^ V := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ V := Nat.pow_le_pow_right (by norm_num) hV
  omega

/-- Application of Proposition B.6 in **steps (b), (c) of the proof of Theorem B.7**: the average of `Φ_L` over the residue class `{w ≡ 1 (mod 8)}` is
`2^{-M(L)}(λ - λ^2 2^{-V})`. -/
theorem km_Qavg_apply (hQ : SpecQavg) (V ℓ d I R : ℕ) (hℓ : 1 ≤ ℓ) (hd : 1 ≤ d) (hdR : d ≤ R)
    (β₀ : List Bool) (ne : ℕ) (L ζ : List Bool) (hL : L.length = 2 * I + R) (hζ : ζ.length = ℓ)
    (hVL : (parityOf L).length + ℓ ≤ V) (hV3 : ℓ + d + 3 ≤ V) :
    (∑ w ∈ Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1), kmPhi V ℓ d I β₀ ne L ζ w) /
        ((Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1)).card : ℝ) =
      (1 / 2 ^ (Finset.univ.filter (fun j : Fin I => kmOri L j ≠ 0)).card) *
        ((2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) - (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) ^ 2 / 2 ^ V) := by
  have ho : ∀ j : Fin I, kmOri L j = -1 ∨ kmOri L j = 0 ∨ kmOri L j = 1 := by
    intro j; unfold kmOri; split_ifs <;> simp
  have hω : ∀ j : Fin I, (kmOmega V β₀ ne L j).val % 2 = 1 := by
    intro j; unfold kmOmega; exact km_i3_pow_odd V (by omega) _
  have hb : ∀ j : Fin I, kmExp V L ζ j + ℓ + 8 * R + 7 ≤ V ∧
      kmExp V L ζ j = (kmPre L j).length + 9 + (V - (parityOf L).length - ℓ) :=
    fun j => km_exp_bounds V I R ℓ L ζ hL hζ hVL j j.isLt
  have hv : ∀ i j : Fin I, i < j → kmV V L ζ j < kmV V L ζ i := by
    intro i j hij
    have hm := km_pre_mono L i j hij (by have := j.isLt; omega)
    have hi := hb i
    have hj := hb j
    unfold kmV; omega
  have hvb : ∀ j : Fin I, ℓ + d + 3 ≤ kmV V L ζ j ∧ kmV V L ζ j ≤ V := by
    intro j
    have hj := hb j
    unfold kmV; omega
  have hw₀ : (1 : ZMod (2 ^ V)).val % 2 = 1 := by rw [km_one_val V (by omega)]
  have h := hQ V ℓ d I hℓ hd hV3 (fun j => kmOri L j) (fun j => kmOmega V β₀ ne L j)
    (fun j => kmV V L ζ j) (fun _ => 0) 1 ho hω hv hvb hw₀
  have h8 : (1 : ZMod (2 ^ V)).val % 8 = 1 := by rw [km_one_val V (by omega)]
  rw [h8] at h
  unfold kmPhi kmCoef
  exact h

/-- **Steps (c), (d) of the proof of Theorem B.7**: `E_{(β_e, L)} Q_λ(μ_β) ≤ λ (79/100)^I + B · 2(1 - N(3/10)^N)^{⌊n_e/N⌋}`. -/
theorem km_EQ (hQ : SpecQavg) (hN : SpecNine) (hD : SpecDoeblin) (V ℓ d I R ne : ℕ) (hℓ : 1 ≤ ℓ)
    (hd : 1 ≤ d) (hdR : d ≤ R) (β₀ γ : List Bool) (hγ : (parityOf γ).length = ℓ)
    (hVL : 11 * (2 * I + R) + ℓ ≤ V) (hV3 : ℓ + d + 3 ≤ V) :
    ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices (2 * I + R), (wtβ βe : ℝ) * (wtβ L : ℝ) *
        keyQ V (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d)) (kmMu V I β₀ βe L (parityOf γ)) ≤
      ((2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℕ) : ℝ) * (79 / 100) ^ I +
        2 ^ V * ((2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℕ) : ℝ) ^ 2 *
          (2 * (1 - ((2 ^ (V - 3) : ℕ) : ℝ) * (3 / 10 : ℝ) ^ (2 ^ (V - 3))) ^ (ne / 2 ^ (V - 3))) := by
  set lamN : ℕ := 2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) with hlamN
  set B : ℝ := 2 ^ V * (lamN : ℝ) ^ 2 with hB
  set Doe : ℝ := 2 * (1 - ((2 ^ (V - 3) : ℕ) : ℝ) * (3 / 10 : ℝ) ^ (2 ^ (V - 3))) ^ (ne / 2 ^ (V - 3))
    with hDoe
  set ζ := parityOf γ with hζ
  -- `Q_λ(μ_B) = Φ_L(w)`
  have hQΦ : ∀ βe ∈ blockChoices ne, ∀ L : List Bool,
      keyQ V lamN (kmMu V I β₀ βe L ζ) =
        kmPhi V ℓ d I β₀ ne L ζ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ βe.count false) := by
    intro βe hβe L
    unfold kmMu kmPhi
    rw [km_Q_shift, (fam_mem_blockChoices βe ne).mp hβe]
  have hΦ0 : ∀ L w, 0 ≤ kmPhi V ℓ d I β₀ ne L ζ w := fun L w => km_Q_nonneg _ _ _
  have hΦB : ∀ L w, kmPhi V ℓ d I β₀ ne L ζ w ≤ B := fun L w =>
    km_Q_le _ _ _ (km_law_nonneg _ _ _ _) (km_law_le_one _ _ _ _)
  calc ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices (2 * I + R), (wtβ βe : ℝ) * (wtβ L : ℝ) *
        keyQ V lamN (kmMu V I β₀ βe L ζ)
      = ∑ L ∈ blockChoices (2 * I + R), (wtβ L : ℝ) * ∑ βe ∈ blockChoices ne, (wtβ βe : ℝ) *
          kmPhi V ℓ d I β₀ ne L ζ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ βe.count false) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun L _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun βe hβe => ?_)
        rw [hQΦ βe hβe L]; ring
    _ ≤ ∑ L ∈ blockChoices (2 * I + R), (wtβ L : ℝ) *
          ((1 / 2 ^ (Finset.univ.filter (fun j : Fin I => kmOri L j ≠ 0)).card) * lamN + B * Doe) := by
        refine Finset.sum_le_sum (fun L hLm => mul_le_mul_of_nonneg_left ?_ (km_wt_nonneg L))
        have hLl : L.length = 2 * I + R := (fam_mem_blockChoices L _).mp hLm
        have hpL : (parityOf L).length + ℓ ≤ V := by
          have := (parityOf_length_bounds L).2; rw [hLl] at this; omega
        have hw := km_w_bound hN hD V (by omega) (kmPhi V ℓ d I β₀ ne L ζ) B (hΦ0 L) (hΦB L) ne
        rw [km_Qavg_apply hQ V ℓ d I R hℓ hd hdR β₀ ne L ζ hLl hγ hpL hV3] at hw
        refine le_trans hw (add_le_add ?_ le_rfl)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hl : ((lamN : ℕ) : ℝ) = (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) := by rw [hlamN]; push_cast; ring
        rw [hl]
        have : 0 ≤ (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) : ℝ) ^ 2 / 2 ^ V := by positivity
        linarith
    _ = (lamN : ℝ) * (79 / 100) ^ I + B * Doe := by
        have hc := km_coin_avg R I
        have hs := km_wt_sum (2 * I + R)
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hs, one_mul]
        congr 1
        rw [← hc, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun L _ => ?_)
        ring

end Collatz.Arctic
