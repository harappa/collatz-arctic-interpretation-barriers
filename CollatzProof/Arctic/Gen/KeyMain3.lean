/-
The general form of the formula for a fixed `(B_e, L)` and of the decomposition of the probability, in the proof of Theorem B.7 (KEY).
The expectation of `Q_λ` is in `Gen/KeyMain3Q.lean`, the assembly in `Gen/KeyMain4.lean`.

Adapted from the first half of `KeyMain3.lean` (from `kmOmega` to `km_prob_decomp`). Changes:
* The residue `terrasR (parity word)` is replaced by the residue `R` of the block sequence, and `π`, `ζ` are block sequences (`kmRho`, `kmMu`
  were quantified over parity words for $T$). `R` is used only through its size `hlt` (`R_lt`) and the swap
  `hsw` (`SwapR R e₂ e₃`).
* The constants $9 \to \nu_2$ (`kmExp`, `kmV`) and $7 \to \nu_3$ (`kmOmega`), where $(\nu_2, \nu_3)$ are the swap exponents (`e₂`, `e₃` in the code). The inequality for the positions of the coins
  `kmExp + ℓ + 8R + 7 ≤ V` of $T$ becomes `kmExp + ℓ + 8R + 16 ≤ V + ν₂` (of the form `8R + 16 - ν₂`).
* Small model-independent lemmas (`km_pre_drop`, `km_drop_ge`, `km_pre_mono`) are proved again here so that `KeyMain3` of $T$ (which
  imports `HTWCut`) stays out of the closure (using, instead of `htw_blockEnd_ge` and `parityOf_length_bounds`,
  `km_par_len_count` and `fam_length_eq_count`).

Notation: the block sequence `B = B_e ++ L` (the early part `B_e` has `n_e` blocks, the late part `L` has `2I + R` blocks, the first `2I` of which
form `I` adjacent coins), `π = B₀ ++ B_e`, `ζ = Γ` (a block sequence), `ℓ = |par Γ|`, `m = |par(π ++ L ++ ζ)|`.
-/
import CollatzProof.Arctic.Gen.KeyTerras2
import CollatzProof.Arctic.KeyMain2

namespace Collatz.Arctic.Gen

open Collatz.Arctic Finset

/-! ### Quantities of the early part and of the late part -/

/-- `ω_j = 3^{-(A(B₀) + 5 n_e + c_j + ν₃)}` of coin `j` (`c_j` is the number of odd steps in the late part before coin `j`). -/
def kmOmega (e₃ V : ℕ) (β₀ : List Bool) (ne : ℕ) (L : List Bool) (j : ℕ) : ZMod (2 ^ V) :=
  ((3 : ZMod (2 ^ V))⁻¹) ^ (terrasA (parityOf β₀) + 5 * ne + terrasA (kmPre L j) + e₃)

/-- `v_j` of coin `j` (`V - v_j` is the exponent of the power of 2 in the translation by the coin). -/
def kmV (e₂ V : ℕ) (L ζ : List Bool) (j : ℕ) : ℕ := V - kmExp e₂ V L ζ j

/-- The translation by a coin `a_j(w) = o_j ω_j 2^{V - v_j} w` (the form of Proposition B.6). -/
def kmCoef (e₂ e₃ V I : ℕ) (β₀ : List Bool) (ne : ℕ) (L ζ : List Bool) (w : ZMod (2 ^ V)) (j : Fin I) :
    ZMod (2 ^ V) :=
  (kmOri L j : ZMod (2 ^ V)) * kmOmega e₃ V β₀ ne L j * 2 ^ (V - kmV e₂ V L ζ j) * w

/-- The top `V` digits `ρ(B^e)` (`π`, `L`, `ζ` are block sequences). -/
def kmRho (R : List Bool → ℕ) (V I : ℕ) (π L ζ : List Bool) (e : Fin I → Bool) : ℕ :=
  R (π ++ kmSwap I e L ++ ζ) / 2 ^ ((parityOf (π ++ L ++ ζ)).length - V)

/-- The law `μ_B` of `ρ(B^e)` (mod `2^V`) when the coin variables `e` are uniform. -/
noncomputable def kmMu (R : List Bool → ℕ) (e₂ e₃ V I : ℕ) (β₀ βe L ζ : List Bool) :
    ZMod (2 ^ V) → ℝ :=
  keyLaw V I ((kmRho R V I (β₀ ++ βe) L ζ (fun _ => false) : ℕ) : ZMod (2 ^ V))
    (kmCoef e₂ e₃ V I β₀ βe.length L ζ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ βe.count false))

/-- `Φ_L(w) = Q_λ(μ_w)` (base point 0). -/
noncomputable def kmPhi (e₂ e₃ V ℓ d I : ℕ) (β₀ : List Bool) (ne : ℕ) (L ζ : List Bool)
    (w : ZMod (2 ^ V)) : ℝ :=
  keyQ V (2 ^ (V - ℓ) + 2 ^ (V - ℓ - d)) (keyLaw V I 0 (kmCoef e₂ e₃ V I β₀ ne L ζ w))

/-! ### Positions of the coins in the late part -/

/-- The length of a parity word is between 8 and 11 times the number of blocks (the same claim as `CoreHelp.parityOf_length_bounds`). -/
lemma km_parlen_bounds (β : List Bool) :
    8 * β.length ≤ (parityOf β).length ∧ (parityOf β).length ≤ 11 * β.length := by
  have h1 := km_par_len_count β
  have h2 := fam_length_eq_count β
  constructor <;> omega

lemma km_pre_drop (L : List Bool) (j : ℕ) :
    (parityOf L).length = (kmPre L j).length + (parityOf (L.drop (2 * j))).length := by
  unfold kmPre
  rw [← List.length_append, ← fam_parityOf_append, List.take_append_drop]

lemma km_drop_ge (L : List Bool) (j : ℕ) :
    8 * (L.length - 2 * j) ≤ (parityOf (L.drop (2 * j))).length := by
  have := (km_parlen_bounds (L.drop (2 * j))).1
  rw [List.length_drop] at this
  exact this

lemma km_pre_mono (L : List Bool) (i j : ℕ) (hij : i < j) (hj : 2 * j ≤ L.length) :
    (kmPre L i).length + 16 ≤ (kmPre L j).length := by
  unfold kmPre
  rw [show 2 * j = 2 * i + 2 * (j - i) by omega, List.take_add, fam_parityOf_append,
    List.length_append]
  have h := (km_parlen_bounds ((L.drop (2 * i)).take (2 * (j - i)))).1
  have h2 : ((L.drop (2 * i)).take (2 * (j - i))).length = 2 * (j - i) := by
    rw [List.length_take, List.length_drop]; omega
  rw [h2] at h
  omega

/-- Inequality for the positions of the coins (the late part `L` has `2I + R` blocks, `V ≥ |par L| + ℓ`):
`kmExp + ℓ + 8R + 16 ≤ V + ν₂` (the general form of `kmExp + ℓ + 8R + 7 ≤ V` of $T$). -/
lemma km_exp_bounds (e₂ V I nR ℓ : ℕ) (L ζ : List Bool) (hL : L.length = 2 * I + nR)
    (hζ : (parityOf ζ).length = ℓ) (hVL : (parityOf L).length + ℓ ≤ V) (j : ℕ) (hj : j < I) :
    kmExp e₂ V L ζ j + ℓ + 8 * nR + 16 ≤ V + e₂ ∧
      kmExp e₂ V L ζ j = (kmPre L j).length + e₂ + (V - (parityOf L).length - ℓ) := by
  have h1 := km_pre_drop L j
  have h2 := km_drop_ge L j
  unfold kmExp
  rw [hζ]
  constructor <;> omega

/-! ### The formula for a fixed `(B_e, L)` -/

/-- `ρ(B^e) < 2^V`. -/
lemma km_rho_lt {R : List Bool → ℕ} (hlt : ∀ β, R β < 2 ^ (parityOf β).length) (V I : ℕ)
    (π L ζ : List Bool) (hVM : V ≤ (parityOf (π ++ L ++ ζ)).length) (e : Fin I → Bool) :
    kmRho R V I π L ζ e < 2 ^ V := by
  unfold kmRho
  set M := (parityOf (π ++ L ++ ζ)).length with hM
  have hlt' : R (π ++ kmSwap I e L ++ ζ) < 2 ^ M := by
    have := hlt (π ++ kmSwap I e L ++ ζ)
    simp only [fam_parityOf_append, List.length_append, km_swap_parlen] at this
    rw [hM]; simpa only [fam_parityOf_append, List.length_append] using this
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hVM]
  exact hlt'

/-- **Lemma B.5 (iii) written with `ω_j` and `w`**: `ρ(B^e) = ρ(B) + Σ_j e_j a_j(w)`, `w = 9^{-Y_e}`. -/
theorem km_pair_shift {R : List Bool → ℕ} (hlt : ∀ β, R β < 2 ^ (parityOf β).length) {e₂ e₃ : ℕ}
    (hsw : SwapR R e₂ e₃) (V I : ℕ) (β₀ βe L ζ : List Bool) (hL : 2 * I ≤ L.length)
    (hVM : V ≤ (parityOf (β₀ ++ βe ++ L ++ ζ)).length)
    (hVL : (parityOf L).length + (parityOf ζ).length ≤ V) (hexp : ∀ j : Fin I, kmExp e₂ V L ζ j ≤ V)
    (e : Fin I → Bool) :
    (kmRho R V I (β₀ ++ βe) L ζ e : ZMod (2 ^ V)) =
      (kmRho R V I (β₀ ++ βe) L ζ (fun _ => false) : ZMod (2 ^ V)) +
        ∑ j, (if e j then
          kmCoef e₂ e₃ V I β₀ βe.length L ζ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ βe.count false) j
          else 0) := by
  unfold kmRho
  rw [km_swap_false, km_rho_shift hlt hsw I V _ e _ L ζ hL rfl hVM (by omega)]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · unfold kmCoef kmOmega kmV
    rw [Nat.sub_sub_self (hexp j), fam_parityOf_append, terrasA_append,
      km_par_A_count βe, fam_length_eq_count βe]
    ring
  · rfl

/-- The `U` of the statement is the top `ℓ` digits of `ρ`. -/
lemma km_U_eq (R : List Bool → ℕ) (V I : ℕ) (β₀ βe L γ : List Bool) (e : Fin I → Bool)
    (hℓV : (parityOf γ).length ≤ V) (hVM : V ≤ (parityOf (β₀ ++ βe ++ L ++ γ)).length) :
    R (β₀ ++ (βe ++ kmSwap I e L) ++ γ) / 2 ^ (parityOf (β₀ ++ (βe ++ kmSwap I e L))).length =
      kmRho R V I (β₀ ++ βe) L γ e / 2 ^ (V - (parityOf γ).length) := by
  unfold kmRho
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  have e1 : β₀ ++ (βe ++ kmSwap I e L) ++ γ = β₀ ++ βe ++ kmSwap I e L ++ γ := by simp
  have e2 : (parityOf (β₀ ++ (βe ++ kmSwap I e L))).length =
      (parityOf (β₀ ++ βe ++ L ++ γ)).length - V + (V - (parityOf γ).length) := by
    simp only [fam_parityOf_append, List.length_append, km_swap_parlen] at hVM ⊢
    omega
  rw [e1, e2]

/-- **The cells in step (a) of the proof of Theorem B.7**: `μ_B(C_u)` is the proportion of the coin variables `e` for which `U(B^e)` of the statement is `u`. -/
theorem km_pair_cell {R : List Bool → ℕ} (hlt : ∀ β, R β < 2 ^ (parityOf β).length) {e₂ e₃ : ℕ}
    (hsw : SwapR R e₂ e₃) (V I : ℕ) (β₀ βe L γ : List Bool) (hL : 2 * I ≤ L.length)
    (hℓV : (parityOf γ).length ≤ V) (hVM : V ≤ (parityOf (β₀ ++ βe ++ L ++ γ)).length)
    (hVL : (parityOf L).length + (parityOf γ).length ≤ V)
    (hexp : ∀ j : Fin I, kmExp e₂ V L γ j ≤ V) (u : ℕ) (hu : u < 2 ^ (parityOf γ).length) :
    keyCell V (parityOf γ).length (kmMu R e₂ e₃ V I β₀ βe L γ) u =
      (1 / 2 ^ I) * ∑ e : Fin I → Bool,
        (if R (β₀ ++ (βe ++ kmSwap I e L) ++ γ) /
            2 ^ (parityOf (β₀ ++ (βe ++ kmSwap I e L))).length = u then (1 : ℝ) else 0) := by
  unfold kmMu
  rw [km_cell V _ I hℓV _ _ (fun e => kmRho R V I (β₀ ++ βe) L γ e)
    (fun e => km_rho_lt hlt V I _ L _ hVM e)
    (fun e => km_pair_shift hlt hsw V I β₀ βe L _ hL hVM hVL hexp e) u hu]
  congr 1
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [km_U_eq R V I β₀ βe L γ e hℓV hVM]

/-- Decomposition of the probability: `Pr(U = u) = E_{(B_e, L)} μ_B(C_u)`. -/
theorem km_prob_decomp {R : List Bool → ℕ} (hlt : ∀ β, R β < 2 ^ (parityOf β).length) {e₂ e₃ : ℕ}
    (hsw : SwapR R e₂ e₃) (V I ne nL : ℕ) (β₀ γ : List Bool) (hL : 2 * I ≤ nL)
    (hℓV : (parityOf γ).length ≤ V)
    (hVM : ∀ βe ∈ blockChoices ne, ∀ L ∈ blockChoices nL,
      V ≤ (parityOf (β₀ ++ βe ++ L ++ γ)).length)
    (hVL : ∀ L ∈ blockChoices nL, (parityOf L).length + (parityOf γ).length ≤ V)
    (hexp : ∀ L ∈ blockChoices nL, ∀ j : Fin I, kmExp e₂ V L γ j ≤ V)
    (u : ℕ) (hu : u < 2 ^ (parityOf γ).length) :
    ∑ β ∈ (blockChoices (ne + nL)).filter (fun β =>
        R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length = u), (wtβ β : ℝ) =
      ∑ βe ∈ blockChoices ne, ∑ L ∈ blockChoices nL, (wtβ βe : ℝ) * (wtβ L : ℝ) *
        keyCell V (parityOf γ).length (kmMu R e₂ e₃ V I β₀ βe L γ) u := by
  rw [Finset.sum_filter, km_sum_append ne nL]
  refine Finset.sum_congr rfl (fun βe hβe => ?_)
  have h1 : ∑ L ∈ blockChoices nL, (if R (β₀ ++ (βe ++ L) ++ γ) /
        2 ^ (parityOf (β₀ ++ (βe ++ L))).length = u then (wtβ (βe ++ L) : ℝ) else 0) =
      (wtβ βe : ℝ) * ∑ L ∈ blockChoices nL, (wtβ L : ℝ) *
        (if R (β₀ ++ (βe ++ L) ++ γ) /
          2 ^ (parityOf (β₀ ++ (βe ++ L))).length = u then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun L _ => ?_)
    rw [km_wt_append]; push_cast
    split_ifs <;> ring
  rw [h1, km_swap_avg I nL, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun L hLm => ?_)
  have hLl : L.length = nL := (fam_mem_blockChoices L nL).mp hLm
  rw [km_pair_cell hlt hsw V I β₀ βe L γ (by omega) hℓV (hVM βe hβe L hLm) (hVL L hLm)
    (hexp L hLm) u hu]
  ring

end Collatz.Arctic.Gen
