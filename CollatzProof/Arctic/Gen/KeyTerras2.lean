/-
The general form of **Lemma B.5 (iii)** (the formula for the top `V` digits).
The first half (translation by swaps of coins) is in `Gen/KeySwap.lean`.

Adapted from `kmExp` and `km_rho_shift` in `KeyTerras2.lean`. Changes:
* The residue `terrasR (parity word)` is replaced by the residue `R (block sequence)` of the block sequence (`π`, `L`, `ζ` are block sequences).
  Only the size of `R` (`R_lt`) and the swap (`SwapR R e₂ e₃`) are used.
* The constants $9 \to \nu_2$, $7 \to \nu_3$ (the swap exponents, `e₂`, `e₃` in the code). The position of coin `j` is `v_j = |par(L from 2j on)| + ℓ - ν₂` (`- 9` for $T$).
* The condition `|par L| + |par ζ| ≤ V + ν₂` (`+ 9` for $T$).

`km_top` (translation of the top digits) and `km_cast_inv3` (reduction of the inverse of 3) are used from `KeyTerras2.lean` as they are
(independent of the model).
-/
import CollatzProof.Arctic.Gen.KeySwap
import CollatzProof.Arctic.KeyTerras2

namespace Collatz.Arctic.Gen

open Collatz.Arctic

/-- The exponent of the power of 2 for coin `j` (in the top digits modulo `2^V`): `V - v_j`, `v_j = |par(L from 2j on)| + |par ζ| - ν₂`
(the `9` of `KeyTerras2.kmExp` replaced by `e₂`, and `ζ.length` by `(parityOf ζ).length`). -/
def kmExp (e₂ V : ℕ) (L ζ : List Bool) (j : ℕ) : ℕ :=
  (kmPre L j).length + e₂ + V - (parityOf L).length - (parityOf ζ).length

/-- **General form of Lemma B.5 (iii)** (the formula for the top `V` digits):
`ρ(L^e) ≡ ρ(L) + Σ_j e_j o_j 2^{V-v_j} 3^{-(A_j+ν₃)}` (mod `2^V`). -/
theorem km_rho_shift {R : List Bool → ℕ} (hlt : ∀ β, R β < 2 ^ (parityOf β).length) {e₂ e₃ : ℕ}
    (hsw : SwapR R e₂ e₃) (I V M : ℕ) (e : Fin I → Bool) (π L ζ : List Bool) (hL : 2 * I ≤ L.length)
    (hM : (parityOf (π ++ L ++ ζ)).length = M) (hVM : V ≤ M)
    (hV9 : (parityOf L).length + (parityOf ζ).length ≤ V + e₂) :
    ((R (π ++ kmSwap I e L ++ ζ) / 2 ^ (M - V) : ℕ) : ZMod (2 ^ V)) =
      ((R (π ++ L ++ ζ) / 2 ^ (M - V) : ℕ) : ZMod (2 ^ V)) +
        ∑ j : Fin I, (if e j then (kmOri L j : ZMod (2 ^ V)) * 2 ^ kmExp e₂ V L ζ j *
          ((3 : ZMod (2 ^ V))⁻¹) ^ (terrasA (parityOf π) + terrasA (kmPre L j) + e₃) else 0) := by
  have hmul := km_swap_multi hsw I e π L ζ M hL hM
  have hlenM : M = (parityOf π).length + (parityOf L).length + (parityOf ζ).length := by
    rw [← hM]; simp only [fam_parityOf_append, List.length_append]
  set z : ZMod (2 ^ M) := ∑ j : Fin I, (if e j then (kmOri L j : ZMod (2 ^ M)) * 2 ^ kmExp e₂ V L ζ j *
    ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA (parityOf π) + terrasA (kmPre L j) + e₃) else 0) with hz
  have hfac : (∑ j : Fin I, (if e j then (kmOri L j : ZMod (2 ^ M)) *
          2 ^ ((parityOf π).length + (kmPre L j).length + e₂) *
          ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA (parityOf π) + terrasA (kmPre L j) + e₃) else 0)) =
      ((2 ^ (M - V) : ℕ) : ZMod (2 ^ M)) * z := by
    rw [hz, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hexp : (parityOf π).length + (kmPre L j).length + e₂ = (M - V) + kmExp e₂ V L ζ j := by
      unfold kmExp; omega
    split_ifs
    · rw [hexp, pow_add]; push_cast; ring
    · simp
  rw [hfac] at hmul
  have hlt' : R (π ++ kmSwap I e L ++ ζ) < 2 ^ M := by
    have := hlt (π ++ kmSwap I e L ++ ζ)
    simp only [fam_parityOf_append, List.length_append, km_swap_parlen] at this
    rw [hlenM]; exact this
  have hQ : 2 ^ (M - V) * 2 ^ V = 2 ^ M := by rw [← pow_add, Nat.sub_add_cancel hVM]
  rw [km_top _ _ (2 ^ (M - V)) (2 ^ V) (2 ^ M) (by positivity) hQ hlt' z hmul]
  congr 1
  have hdvd : 2 ^ V ∣ 2 ^ M := pow_dvd_pow 2 hVM
  rw [← ZMod.cast_eq_val]
  change ZMod.castHom hdvd (ZMod (2 ^ V)) z = _
  rw [hz, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [map_mul, map_mul, map_pow, map_pow, km_cast_inv3 V M hdvd, map_intCast, map_ofNat]
  · simp

end Collatz.Arctic.Gen
