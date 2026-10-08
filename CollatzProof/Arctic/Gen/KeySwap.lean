/-
The translation by swaps of coins (Lemma B.5 (iii)), shown in general form from the residue `R` and the swap hypothesis `SwapR R e₂ e₃`
(the swap exponents $(\nu_2, \nu_3)$ are `e₂`, `e₃` in the code).

Adapted from `km_swap_head` and `km_swap_multi` in `KeyTerras.lean` (Lemma B.5 (iii)). Changes:
* For $T$, the single swap (`km_swap_one`, Lemma B.5 (ii)) was proved from the affine formula of Terras; here the translation by swaps
  `SwapR R e₂ e₃` (`ν₂ = 9`, `ν₃ = 7` for $T$; `ν₂ = ν₃ = 8` for $H$) is taken as a hypothesis (`swapR_at`).
* `km_swap_multi` for $T$ quantified the surrounding words `π`, `ζ` over arbitrary parity words; since `SwapR` is a claim about block sequences,
  `π` and `ζ` are block sequences here as well (every use in the assembly of the swap argument is
  aligned with block boundaries). The length of parity words and the number of odd steps are measured by `parityOf π`.
* Of the constants, only $9 \to \nu_2$ and $7 \to \nu_3$ are replaced.

The swap `kmSwap`, the sign `kmOri`, the prefix word `kmPre`, and their model-independent properties (`km_swap_perm`, `km_swap_parlen`,
`km_pre_cons2`, etc.) are used from `KeyTerras.lean` as they are.
-/
import CollatzProof.Arctic.Gen.Model
import CollatzProof.Arctic.KeyTerras

namespace Collatz.Arctic.Gen

open Collatz.Arctic

/-- Reading `SwapR` modulo `2^M` (`M` is the total number of bits). -/
lemma swapR_at {R : List Bool → ℕ} {e₂ e₃ : ℕ} (hsw : SwapR R e₂ e₃) (φ χ : List Bool) (M : ℕ)
    (hM : (parityOf (φ ++ [true, false] ++ χ)).length = M) :
    (R (φ ++ [true, false] ++ χ) : ZMod (2 ^ M)) =
      R (φ ++ [false, true] ++ χ) -
        2 ^ ((parityOf φ).length + e₂) * ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA (parityOf φ) + e₃) := by
  subst hM
  exact hsw φ χ

/-- Swapping two adjacent blocks does not change the length of the parity word. -/
lemma km_parlen_swap2 (π χ : List Bool) :
    (parityOf (π ++ [true, false] ++ χ)).length = (parityOf (π ++ [false, true] ++ χ)).length := by
  simp only [fam_parityOf_append, List.length_append]
  simp [parityOf, blkX, blkY]

/-- Translation by the swap of coin `0` (`SwapR` applied to one coin; the general form of `KeyTerras.km_swap_head`). -/
lemma km_swap_head {R : List Bool → ℕ} {e₂ e₃ : ℕ} (hsw : SwapR R e₂ e₃)
    (π χ : List Bool) (x y b : Bool) (M : ℕ)
    (hM : (parityOf (π ++ [x, y] ++ χ)).length = M) :
    (R (π ++ (if b then [y, x] else [x, y]) ++ χ) : ZMod (2 ^ M)) =
      R (π ++ [x, y] ++ χ) +
        (if b then (kmOri [x, y] 0 : ZMod (2 ^ M)) * 2 ^ ((parityOf π).length + e₂) *
          ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA (parityOf π) + e₃) else 0) := by
  cases b
  · simp
  · simp only [↓reduceIte]
    cases x <;> cases y
    · simp [kmOri]
    · -- (Y, X) → (X, Y): the sign is -1
      have h := swapR_at hsw π χ M (by rw [km_parlen_swap2]; exact hM)
      rw [h]
      simp [kmOri, sub_eq_add_neg]
    · -- (X, Y) → (Y, X): the sign is +1
      have h := swapR_at hsw π χ M hM
      rw [h]
      simp [kmOri]
    · simp [kmOri]

/-- **General form of Lemma B.5 (iii)** (the orbit of the coins): `π`, `L`, `ζ` are block sequences, and modulo `2^m`
`R(π L^e ζ) = R(π L ζ) + Σ_j e_j o_j 2^{m_j + ν₂} 3^{-(A_j + ν₃)}`,
`m_j = |par π| + |kmPre L j|`, `A_j = A(par π) + A(kmPre L j)`. -/
theorem km_swap_multi {R : List Bool → ℕ} {e₂ e₃ : ℕ} (hsw : SwapR R e₂ e₃) (I : ℕ) :
    ∀ (e : Fin I → Bool) (π L ζ : List Bool) (M : ℕ),
    2 * I ≤ L.length → (parityOf (π ++ L ++ ζ)).length = M →
    (R (π ++ kmSwap I e L ++ ζ) : ZMod (2 ^ M)) =
      R (π ++ L ++ ζ) +
        ∑ j : Fin I, (if e j then (kmOri L j : ZMod (2 ^ M)) *
          2 ^ ((parityOf π).length + (kmPre L j).length + e₂) *
          ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA (parityOf π) + terrasA (kmPre L j) + e₃) else 0) := by
  induction I with
  | zero => intro e π L ζ M _ _; simp [kmSwap]
  | succ I ih =>
    intro e π L ζ M hL hM
    rcases L with _ | ⟨x, _ | ⟨y, L⟩⟩
    · simp only [List.length_nil] at hL; omega
    · simp only [List.length_cons, List.length_nil] at hL; omega
    · set c : List Bool := if e 0 then [y, x] else [x, y] with hc
      have hcL : (parityOf c).length = (parityOf [x, y]).length := by
        rw [hc]; split_ifs <;> simp [parityOf, add_comm]
      have hcA : terrasA (parityOf c) = terrasA (parityOf [x, y]) := by
        rw [hc]; split_ifs <;> simp [parityOf, terrasA_append, add_comm]
      have hM2 : (parityOf ((π ++ c) ++ L ++ ζ)).length = M := by
        rw [← hM]
        simp only [fam_parityOf_append, List.length_append, hcL]
        rw [show x :: y :: L = [x, y] ++ L from rfl, fam_parityOf_append, List.length_append]
        omega
      have hunf : kmSwap (I + 1) e (x :: y :: L) = c ++ kmSwap I (fun j => e j.succ) L := by
        simp [kmSwap, hc]
      have e1 : π ++ (c ++ kmSwap I (fun j => e j.succ) L) ++ ζ =
          (π ++ c) ++ kmSwap I (fun j => e j.succ) L ++ ζ := by simp
      rw [hunf, e1, ih (fun j => e j.succ) (π ++ c) L ζ M (by simp at hL; omega) hM2]
      rw [Fin.sum_univ_succ]
      have hparL : π ++ (x :: y :: L) ++ ζ = π ++ [x, y] ++ (L ++ ζ) := by simp
      have hhead := km_swap_head hsw π (L ++ ζ) x y (e 0) M (by rw [← hM, hparL])
      have e3 : π ++ c ++ L ++ ζ = π ++ c ++ (L ++ ζ) := by simp
      have h0 : (if e 0 = true then (kmOri [x, y] 0 : ZMod (2 ^ M)) * 2 ^ ((parityOf π).length + e₂) *
            ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA (parityOf π) + e₃) else 0) =
          (if e 0 = true then (kmOri (x :: y :: L) ((0 : Fin (I + 1)) : ℕ) : ZMod (2 ^ M)) *
            2 ^ ((parityOf π).length + (kmPre (x :: y :: L) ((0 : Fin (I + 1)) : ℕ)).length + e₂) *
            ((3 : ZMod (2 ^ M))⁻¹) ^
              (terrasA (parityOf π) + terrasA (kmPre (x :: y :: L) ((0 : Fin (I + 1)) : ℕ)) + e₃)
            else 0) := by
        simp [kmOri, km_pre_zero, km_A_nil]
      have hs : ∀ j : Fin I, (if e j.succ = true then (kmOri L j : ZMod (2 ^ M)) *
            2 ^ ((parityOf (π ++ c)).length + (kmPre L j).length + e₂) *
            ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA (parityOf (π ++ c)) + terrasA (kmPre L j) + e₃) else 0) =
          (if e j.succ = true then (kmOri (x :: y :: L) (j.succ : ℕ) : ZMod (2 ^ M)) *
            2 ^ ((parityOf π).length + (kmPre (x :: y :: L) (j.succ : ℕ)).length + e₂) *
            ((3 : ZMod (2 ^ M))⁻¹) ^
              (terrasA (parityOf π) + terrasA (kmPre (x :: y :: L) (j.succ : ℕ)) + e₃)
            else 0) := by
        intro j
        rw [Fin.val_succ, km_ori_cons2, km_pre_cons2, List.length_append, terrasA_append,
          fam_parityOf_append, List.length_append, terrasA_append, hcL, hcA]
        simp only [add_assoc]
      rw [e3, hhead, ← hparL, add_assoc, h0, Finset.sum_congr rfl (fun j _ => hs j)]

end Collatz.Arctic.Gen
