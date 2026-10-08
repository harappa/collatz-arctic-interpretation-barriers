/-
The translation by a swap for $H$. Proves the interface statement `SpecHSwap` (`Gen.SwapR hR 8 8`) of the frozen
`HModel/Defs.lean`.

* `hBeta`, the affine constant $\gamma_w$ ($\gamma_\emptyset = 0$, $\gamma_{w\mathsf a} = 3\gamma_w$, $\gamma_{w\mathsf b} = 9\gamma_w + 2^{m_w}$), and
  **the $H$ version of Lemma 6.1 (ii) and Lemma B.5 (i)**: `h_affine` ($3^{a_w} r_w + \gamma_w = 2^{m_w} c_w$), `hBeta_append`
  ($\gamma_{ww'} = 3^{a_{w'}}\gamma_w + 2^{m_w}\gamma_{w'}$), `hBeta_X`, `hBeta_Y` ($\gamma_X = 68$, $\gamma_Y = 868$, as in the
  proof of Proposition 7.2), `hBeta_XY` ($\gamma_{XY} - \gamma_{YX} = 20736 = 2^8 3^4$, as there; for $T$ it is
  $124416 = 2^9 3^5$).
* `h_r_zmod`: modulo $2^m$, $r_w = -\gamma_w 3^{-a_w}$ ($3^{-1}$ is the inverse in `ZMod (2^m)`).
* **The $H$ version of Lemma B.5 (ii)**, `specHSwap`: for block sequences $\varphi$, $\chi$, modulo $2^m$,
  $r_{\varphi XY\chi} = r_{\varphi YX\chi} - 2^{m_\varphi+8} 3^{-(a_\varphi+8)}$. The difference of the constants $\gamma$ is
  $2^{m_\varphi} 3^{a_\chi} \cdot 2^8 3^4$; with $a = a_\varphi + 12 + a_\chi$ it is multiplied by $-3^{-a}$.

**Adapted from**: the first half of `KeyTerras.lean` (`kmBeta`, `km_affine`, `km_beta_append`, `km_beta_XY`, `km_three_inv`,
`km_two_pow_self`, `km_r_zmod`, `km_swap_one`) and `tModel_swap` of `Gen/ModelT.lean` (how it is applied to block sequences).
For $T$ one step of a parity word was 1 bit; here we work with letter words ($\mathsf a$ is 2 bits, $\mathsf b$ is 3 bits).
The proof for $T$ (`KeyTerras`) is not imported (to keep the swap argument for $T$ out of the closure of the main theorem for $H$; `km_three_inv` and
`km_two_pow_self` are a few lines, so they were copied).

Numerical cross-check: the script `check_hmodel.py` of Appendix C.
-/
import CollatzProof.Arctic.HModel.Terras2

namespace Collatz.Arctic.HModel

open Collatz.Arctic

/-! ## The affine formula -/

/-- One step for $\gamma_w$ (state $(m, \gamma)$): $\gamma_{w\mathsf a} = 3\gamma_w$, $\gamma_{w\mathsf b} = 9\gamma_w + 2^{m_w}$. -/
def hBetaStep (s : ℕ × ℕ) (x : Bool) : ℕ × ℕ :=
  if x then (s.1 + 2, 3 * s.2) else (s.1 + 3, 9 * s.2 + 2 ^ s.1)

/-- The affine constant $\gamma_w$ of the $H$ version of Lemma 6.1 (ii). -/
def hBeta (w : List Bool) : ℕ := (w.foldl hBetaStep (0, 0)).2

lemma hBetaState_fst (w : List Bool) : (w.foldl hBetaStep (0, 0)).1 = wm w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
    rw [List.foldl_append, wm_snoc]
    cases x <;> simp [hBetaStep, ih, lbits]

lemma hBeta_snoc (w : List Bool) (x : Bool) :
    hBeta (w ++ [x]) = if x then 3 * hBeta w else 9 * hBeta w + 2 ^ wm w := by
  unfold hBeta
  rw [List.foldl_append, ← hBetaState_fst w]
  cases x <;> simp [hBetaStep]

/-- **The $H$ version of Lemma 6.1 (ii), first formula**: $3^{a_w} r_w + \gamma_w = 2^{m_w} c_w$. -/
theorem h_affine (w : List Bool) : 3 ^ wa w * wr w + hBeta w = 2 ^ wm w * wc w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
    rw [wr_snoc, wc_snoc, wa_snoc, wm_snoc, hBeta_snoc]
    cases x
    · have hs := tB_spec (wc w) (wa w)
      simp only [tNext, lthree, lbits, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      set y := wc w + 3 ^ wa w * tB (wc w) (wa w) with hy
      rw [Hmap_B _ hs]
      have hz : 8 * ((9 * y + 1) / 8) = 9 * y + 1 := by omega
      calc 3 ^ (wa w + 2) * (wr w + 2 ^ wm w * tB (wc w) (wa w)) + (9 * hBeta w + 2 ^ wm w)
          = 9 * (3 ^ wa w * wr w + hBeta w)
            + 2 ^ wm w * (9 * (3 ^ wa w * tB (wc w) (wa w)) + 1) := by ring
        _ = 2 ^ wm w * (9 * y + 1) := by rw [ih, hy]; ring
        _ = 2 ^ (wm w + 3) * ((9 * y + 1) / 8) := by
            conv_lhs => rw [← hz]
            rw [pow_add]; ring
    · have hs := tA_spec (wc w) (wa w)
      simp only [tNext, lthree, lbits, ↓reduceIte] at hs ⊢
      set y := wc w + 3 ^ wa w * tA (wc w) (wa w) with hy
      rw [Hmap_A _ hs]
      have hz : 4 * (y / 4) = y := by omega
      calc 3 ^ (wa w + 1) * (wr w + 2 ^ wm w * tA (wc w) (wa w)) + 3 * hBeta w
          = 3 * (3 ^ wa w * wr w + hBeta w) + 2 ^ wm w * (3 * (3 ^ wa w * tA (wc w) (wa w))) := by
            ring
        _ = 2 ^ wm w * (3 * y) := by rw [ih, hy]; ring
        _ = 2 ^ (wm w + 2) * (3 * (y / 4)) := by
            conv_lhs => rw [← hz]
            rw [pow_add]; ring

/-- **The $H$ version of Lemma 6.1 (ii), second formula**: $\gamma_{ww'} = 3^{a_{w'}}\gamma_w + 2^{m_w}\gamma_{w'}$. -/
theorem hBeta_append (w w' : List Bool) :
    hBeta (w ++ w') = 3 ^ wa w' * hBeta w + 2 ^ wm w * hBeta w' := by
  induction w' using List.reverseRecOn with
  | nil => simp [hBeta, wa_nil]
  | append_singleton w' x ih =>
    rw [← List.append_assoc, hBeta_snoc, hBeta_snoc, wa_snoc, ih, wm_append]
    cases x
    · simp only [lthree, Bool.false_eq_true, ↓reduceIte]; ring
    · simp only [lthree, ↓reduceIte]; ring

/-- The letter word $X = \mathsf{abb}$. -/
def lX : List Bool := [true, false, false]
/-- The letter word $Y = \mathsf{abbb}$. -/
def lY : List Bool := [true, false, false, false]

/-- **The $H$ version of Lemma B.5 (i)**: $\gamma_X = 68$, $\gamma_Y = 868$. -/
theorem hBeta_X : hBeta lX = 68 := by decide
theorem hBeta_Y : hBeta lY = 868 := by decide

lemma wa_lX : wa lX = 5 := by rw [wa_eq]; decide
lemma wa_lY : wa lY = 7 := by rw [wa_eq]; decide
lemma wm_lX : wm lX = 8 := by rw [wm_eq]; decide
lemma wm_lY : wm lY = 11 := by rw [wm_eq]; decide

/-- $\gamma_{XY} - \gamma_{YX} = 2^8 3^4 = 20736$. -/
theorem hBeta_XY : hBeta (lX ++ lY) = hBeta (lY ++ lX) + 20736 := by
  rw [hBeta_append, hBeta_append, hBeta_X, hBeta_Y, wa_lX, wa_lY, wm_lX, wm_lY]
  norm_num

/-! ## Formulas modulo $2^M$ -/

/-- The inverse of 3 modulo $2^M$ (copied from `KeyTerras.km_three_inv`). -/
lemma h_three_inv (M : ℕ) : (3 : ZMod (2 ^ M)) * (3 : ZMod (2 ^ M))⁻¹ = 1 := by
  have h := ZMod.coe_mul_inv_eq_one (n := 2 ^ M) 3 (Nat.Coprime.pow_right _ (by norm_num))
  exact_mod_cast h

lemma h_two_pow_self (M : ℕ) : (2 : ZMod (2 ^ M)) ^ M = 0 := by
  exact_mod_cast ZMod.natCast_self (2 ^ M)

/-- Lemma 6.1 (ii) modulo $2^m$: $r_w \equiv -\gamma_w 3^{-a_w}$. -/
theorem h_r_zmod (w : List Bool) (M : ℕ) (hM : wm w = M) :
    (wr w : ZMod (2 ^ M)) = -(hBeta w : ZMod (2 ^ M)) * ((3 : ZMod (2 ^ M))⁻¹) ^ wa w := by
  have h := congrArg (fun x : ℕ => (x : ZMod (2 ^ M))) (h_affine w)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hM, Nat.cast_ofNat, h_two_pow_self,
    zero_mul] at h
  have hu : (3 : ZMod (2 ^ M)) ^ wa w * ((3 : ZMod (2 ^ M))⁻¹) ^ wa w = 1 := by
    rw [← mul_pow, h_three_inv, one_pow]
  linear_combination (((3 : ZMod (2 ^ M))⁻¹) ^ wa w) * h - (wr w : ZMod (2 ^ M)) * hu

/-! ## Swaps -/

lemma lettersOf_swapXY (φ χ : List Bool) :
    lettersOf (φ ++ [true, false] ++ χ) = lettersOf φ ++ lX ++ lY ++ lettersOf χ := by
  simp [lettersOf_append, lettersOf_cons, lX, lY]

lemma lettersOf_swapYX (φ χ : List Bool) :
    lettersOf (φ ++ [false, true] ++ χ) = lettersOf φ ++ lY ++ lX ++ lettersOf χ := by
  simp [lettersOf_append, lettersOf_cons, lX, lY]

/-- The swap in terms of letter words: modulo $2^M$, $r_{\varphi XY\chi} = r_{\varphi YX\chi} - 2^{m_\varphi+8} 3^{-(a_\varphi+8)}$. -/
theorem h_swap_one (φ χ : List Bool) (M : ℕ) (hM : wm (φ ++ lX ++ lY ++ χ) = M) :
    (wr (φ ++ lX ++ lY ++ χ) : ZMod (2 ^ M)) =
      wr (φ ++ lY ++ lX ++ χ) - 2 ^ (wm φ + 8) * ((3 : ZMod (2 ^ M))⁻¹) ^ (wa φ + 8) := by
  have hM' : wm (φ ++ lY ++ lX ++ χ) = M := by
    simp only [wm_append, wm_lX, wm_lY] at hM ⊢; omega
  rw [h_r_zmod _ M hM, h_r_zmod _ M hM']
  have hA1 : wa (φ ++ lX ++ lY ++ χ) = wa φ + 12 + wa χ := by
    simp only [wa_append, wa_lX, wa_lY]
  have hA2 : wa (φ ++ lY ++ lX ++ χ) = wa φ + 12 + wa χ := by
    simp only [wa_append, wa_lX, wa_lY]
  have hB : hBeta (φ ++ lX ++ lY ++ χ) =
      hBeta (φ ++ lY ++ lX ++ χ) + 3 ^ wa χ * 2 ^ wm φ * 20736 := by
    rw [List.append_assoc φ lX lY, List.append_assoc φ lY lX, hBeta_append (φ ++ _),
      hBeta_append (φ ++ _), hBeta_append φ, hBeta_append φ, hBeta_XY]
    simp only [wm_append, wm_lX, wm_lY, wa_append, wa_lX, wa_lY]
    ring
  rw [hA1, hA2, hB]
  have hu : (3 : ZMod (2 ^ M)) ^ (wa χ + 4) * ((3 : ZMod (2 ^ M))⁻¹) ^ (wa χ + 4) = 1 := by
    rw [← mul_pow, h_three_inv, one_pow]
  push_cast
  linear_combination (-(2 : ZMod (2 ^ M)) ^ (wm φ + 8) * ((3 : ZMod (2 ^ M))⁻¹) ^ (wa φ + 8)) * hu

/-- **Interface statement**: the translation by a swap (the $H$ version of Lemma B.5 (ii), `e₂ = 8`, `e₃ = 8`). -/
theorem specHSwap : SpecHSwap := by
  intro φ χ
  have hM : wm (lettersOf φ ++ lX ++ lY ++ lettersOf χ) =
      (parityOf (φ ++ [true, false] ++ χ)).length := by
    rw [← lettersOf_swapXY, wm_lettersOf]
  rw [hR_eq, hR_eq, lettersOf_swapXY, lettersOf_swapYX, h_swap_one _ _ _ hM, wm_lettersOf,
    wa_lettersOf]

end Collatz.Arctic.HModel
