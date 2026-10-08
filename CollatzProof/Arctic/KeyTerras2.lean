/-
**Lemma B.5 (iii)**, the formula for the top `V` digits, in the swap argument. The first half is in `KeyTerras.lean`.

* `km_top`: if `r' = r + D z` modulo `Q = D P`, then the quotient by `D` shifts by `z` modulo `P`.
* `km_cast_inv3`: `3^{-1}` modulo `2^M` reduces to `3^{-1}` modulo `2^V` (`V ≤ M`).
* `kmExp V L ζ j`: the exponent `V - v_j` of the power of 2 in the translation of coin `j` (the paper's `v_j` is `|par(L from position 2j on)| + ℓ - 9`).
* `km_rho_shift`: for `ρ(e) := r_{π L^e ζ} / 2^{m-V}`, modulo `2^V`,
  `ρ(e) = ρ(0) + Σ_j e_j o_j 2^{V - v_j} 3^{-(a_j+7)}`.
  The conditions are `V ≤ m` and `|par L| + |ζ| ≤ V + 9` (`v_j ≤ V` for every `j`). Lemma B.5 (iii) holds for every `V` with `v_1 ≤ V ≤ m`,
  so the assembly (`KeyMain4`) fixes `V := 11 n_L + ℓ`, which does not depend on `L`.
-/
import CollatzProof.Arctic.KeyTerras

namespace Collatz.Arctic

/-! ### Top digits -/

/-- Translation of the top digits: if `r' = r + D z` modulo `Q = D P`, then the quotient by `D` shifts by `z` modulo `P`. -/
theorem km_top (r r' D P Q : ℕ) [NeZero Q] (hD : 0 < D) (hQ : D * P = Q) (hr' : r' < Q) (z : ZMod Q)
    (h : (r' : ZMod Q) = r + (D : ZMod Q) * z) :
    ((r' / D : ℕ) : ZMod P) = ((r / D : ℕ) : ZMod P) + ((z.val : ℕ) : ZMod P) := by
  subst hQ
  rw [← ZMod.natCast_zmod_val z] at h
  have h2 : r' % (D * P) = (r + D * z.val) % (D * P) := by
    rw [← ZMod.natCast_eq_natCast_iff']; push_cast; exact h
  rw [Nat.mod_eq_of_lt hr'] at h2
  rw [h2, Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ hD, ZMod.natCast_mod]
  push_cast; ring

/-- Reducing to modulus `2^V`, the inverse of 3 modulo `2^M` maps to the inverse of 3 modulo `2^V`. -/
lemma km_cast_inv3 (V M : ℕ) (h : 2 ^ V ∣ 2 ^ M) :
    ZMod.castHom h (ZMod (2 ^ V)) ((3 : ZMod (2 ^ M))⁻¹) = (3 : ZMod (2 ^ V))⁻¹ := by
  set c := ZMod.castHom h (ZMod (2 ^ V)) ((3 : ZMod (2 ^ M))⁻¹) with hc
  have h1 : (3 : ZMod (2 ^ V)) * c = 1 := by
    have := congrArg (ZMod.castHom h (ZMod (2 ^ V))) (km_three_inv M)
    rw [map_mul, map_one, map_ofNat] at this
    exact this
  have h2 := km_three_inv V
  linear_combination ((3 : ZMod (2 ^ V))⁻¹) * h1 - c * h2

/-- The exponent of the power of 2 for coin `j` (in the top digits modulo `2^V`): `V - v_j`, `v_j = |par(L from position 2j on)| + ℓ - 9`. -/
def kmExp (V : ℕ) (L ζ : List Bool) (j : ℕ) : ℕ :=
  (kmPre L j).length + 9 + V - (parityOf L).length - ζ.length

/-- **Lemma B.5 (iii)** (formula for the top `V` digits): `ρ(L^e) ≡ ρ(L) + Σ_j e_j o_j 2^{V-v_j} 3^{-(a_j+7)}` (modulo `2^V`). -/
theorem km_rho_shift (I V M : ℕ) (e : Fin I → Bool) (π L ζ : List Bool) (hL : 2 * I ≤ L.length)
    (hM : (π ++ parityOf L ++ ζ).length = M) (hVM : V ≤ M)
    (hV9 : (parityOf L).length + ζ.length ≤ V + 9) :
    ((terrasR (π ++ parityOf (kmSwap I e L) ++ ζ) / 2 ^ (M - V) : ℕ) : ZMod (2 ^ V)) =
      ((terrasR (π ++ parityOf L ++ ζ) / 2 ^ (M - V) : ℕ) : ZMod (2 ^ V)) +
        ∑ j : Fin I, (if e j then (kmOri L j : ZMod (2 ^ V)) * 2 ^ kmExp V L ζ j *
          ((3 : ZMod (2 ^ V))⁻¹) ^ (terrasA π + terrasA (kmPre L j) + 7) else 0) := by
  have hmul := km_swap_multi I e π L ζ M hL hM
  have hlenM : M = π.length + (parityOf L).length + ζ.length := by
    rw [← hM]; simp only [List.length_append]
  set z : ZMod (2 ^ M) := ∑ j : Fin I, (if e j then (kmOri L j : ZMod (2 ^ M)) * 2 ^ kmExp V L ζ j *
    ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA π + terrasA (kmPre L j) + 7) else 0) with hz
  have hfac : (∑ j : Fin I, (if e j then (kmOri L j : ZMod (2 ^ M)) *
          2 ^ (π.length + (kmPre L j).length + 9) *
          ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA π + terrasA (kmPre L j) + 7) else 0)) =
      ((2 ^ (M - V) : ℕ) : ZMod (2 ^ M)) * z := by
    rw [hz, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hexp : π.length + (kmPre L j).length + 9 = (M - V) + kmExp V L ζ j := by
      unfold kmExp; omega
    split_ifs
    · rw [hexp, pow_add]; push_cast; ring
    · simp
  rw [hfac] at hmul
  have hlt : terrasR (π ++ parityOf (kmSwap I e L) ++ ζ) < 2 ^ M := by
    have := terrasR_lt (π ++ parityOf (kmSwap I e L) ++ ζ)
    simp only [List.length_append, km_swap_parlen] at this
    rw [hlenM]; exact this
  have hQ : 2 ^ (M - V) * 2 ^ V = 2 ^ M := by rw [← pow_add, Nat.sub_add_cancel hVM]
  rw [km_top _ _ (2 ^ (M - V)) (2 ^ V) (2 ^ M) (by positivity) hQ hlt z hmul]
  congr 1
  have hdvd : 2 ^ V ∣ 2 ^ M := pow_dvd_pow 2 hVM
  rw [← ZMod.cast_eq_val]
  change ZMod.castHom hdvd (ZMod (2 ^ V)) z = _
  rw [hz, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [map_mul, map_mul, map_pow, map_pow, km_cast_inv3 V M hdvd, map_intCast, map_ofNat]
  · simp

end Collatz.Arctic
