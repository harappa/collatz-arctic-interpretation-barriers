/-
The affine formula for Terras residues and the translations given by swapping coins in the swap argument (Lemma 6.1 and Lemma B.5,
ingredients of the proof of Theorem B.7). The formula for the top digits is in `KeyTerras2.lean`, the probabilistic assembly in `KeyMain*.lean`.

Correspondence with the paper:
* `kmBeta`, the affine constant `γ_σ` (`γ_∅ = 0`, `γ_{σ0} = γ_σ`, `γ_{σ1} = 3γ_σ + 2^{m_σ}`), and **Lemma 6.1**: `km_affine`
  (`3^{a_σ} r_σ + γ_σ = 2^{m_σ} c_σ`), `km_beta_append` (`γ_{σσ'} = 3^{a_{σ'}} γ_σ + 2^{m_σ} γ_{σ'}`);
  **Lemma B.5 (i)**: `km_beta_X`, `km_beta_Y` (`γ_{X'} = 421`, `γ_{Y'} = 5069`, by `decide`), `km_beta_XY` (the difference is `2^9 3^5 = 124416`).
* `km_r_zmod`: `r_σ = -γ_σ 3^{-a_σ}` modulo `2^m` (`3^{-1}` is the inverse in `ZMod (2^m)`).
* **Lemma B.5 (ii)**: `km_swap_one` (`r_{φX'Y'χ} = r_{φY'X'χ} - 2^{m_φ+9} 3^{-(a_φ+7)}` modulo `2^m`).
* The coin swap `kmSwap I e L` (swap the positions `(2j, 2j+1)` of `L`, `j < I`, if `e j`), the sign `kmOri`
  (`+1` for `(X', Y')`, `-1` for `(Y', X')`, `0` if equal), and the word `kmPre` before coin `j`.
* **Lemma B.5 (iii)**, invariance: from `km_swap_perm` (a swap is a permutation), `km_swap_length`, `km_swap_wt` (weight),
  `km_swap_parlen`, `km_swap_parA` (`m` and `a`), `km_swap_invol` (involution).
* **Lemma B.5 (iii)**, translation: `km_swap_multi` (`r_{π L^e ζ} = r_{π L ζ} + Σ_j e_j o_j 2^{m_j+9} 3^{-(a_j+7)}` modulo `2^m`,
  `m_j = |π| + |kmPre L j|`, `a_j = a_π + a(kmPre L j)`; induction swapping one coin at a time in increasing order of `j`).
-/
import CollatzProof.Arctic.Family

namespace Collatz.Arctic

/-- One step of `γ_σ` (state `(m, γ)`): `γ_{σ0} = γ_σ`, `γ_{σ1} = 3γ_σ + 2^{m_σ}`. -/
def kmBetaStep (s : ℕ × ℕ) (b : Bool) : ℕ × ℕ := (s.1 + 1, if b then 3 * s.2 + 2 ^ s.1 else s.2)

/-- The affine constant `γ_σ` of Lemma 6.1. -/
def kmBeta (σ : List Bool) : ℕ := (σ.foldl kmBetaStep (0, 0)).2

lemma km_betaState_fst (σ : List Bool) : (σ.foldl kmBetaStep (0, 0)).1 = σ.length := by
  induction σ using List.reverseRecOn with
  | nil => rfl
  | append_singleton σ b ih => simp [List.foldl_append, kmBetaStep, ih]

lemma km_beta_snoc (σ : List Bool) (b : Bool) :
    kmBeta (σ ++ [b]) = if b then 3 * kmBeta σ + 2 ^ σ.length else kmBeta σ := by
  simp only [kmBeta, List.foldl_append, List.foldl_cons, List.foldl_nil, kmBetaStep,
    km_betaState_fst]

/-- **Lemma 6.1** (affine formula): `3^{a_σ} r_σ + γ_σ = 2^{m_σ} c_σ`. -/
theorem km_affine (σ : List Bool) :
    3 ^ terrasA σ * terrasR σ + kmBeta σ = 2 ^ σ.length * terrasC σ := by
  induction σ using List.reverseRecOn with
  | nil => simp [kmBeta, terrasA, terrasR, terrasC, terrasState]
  | append_singleton σ b ih =>
    have hp := terras_next_parity σ b
    rw [terrasR_snoc, terrasC_snoc, terrasA_snoc, km_beta_snoc, List.length_append,
      List.length_singleton]
    set y := terrasC σ + 3 ^ terrasA σ * terrasT0 σ b with hy
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hp ⊢
      rw [T_of_even _ hp]
      calc 3 ^ terrasA σ * (terrasR σ + 2 ^ σ.length * terrasT0 σ false) + kmBeta σ
          = (3 ^ terrasA σ * terrasR σ + kmBeta σ) + 2 ^ σ.length * (3 ^ terrasA σ * terrasT0 σ false) := by
            ring
        _ = 2 ^ σ.length * y := by rw [ih, hy]; ring
        _ = 2 ^ (σ.length + 1) * (y / 2) := by
            rw [pow_succ, mul_assoc]; congr 1; omega
    · simp only [↓reduceIte] at hp ⊢
      rw [T_of_odd _ hp]
      calc 3 ^ (terrasA σ + 1) * (terrasR σ + 2 ^ σ.length * terrasT0 σ true)
            + (3 * kmBeta σ + 2 ^ σ.length)
          = 3 * (3 ^ terrasA σ * terrasR σ + kmBeta σ)
            + 2 ^ σ.length * (3 * (3 ^ terrasA σ * terrasT0 σ true) + 1) := by ring
        _ = 2 ^ σ.length * (3 * y + 1) := by rw [ih, hy]; ring
        _ = 2 ^ (σ.length + 1) * ((3 * y + 1) / 2) := by
            rw [pow_succ, mul_assoc]; congr 1; omega

/-- **Lemma 6.1** (concatenation): `γ_{σσ'} = 3^{a_{σ'}} γ_σ + 2^{m_σ} γ_{σ'}`. -/
theorem km_beta_append (σ σ' : List Bool) :
    kmBeta (σ ++ σ') = 3 ^ terrasA σ' * kmBeta σ + 2 ^ σ.length * kmBeta σ' := by
  induction σ' using List.reverseRecOn with
  | nil => simp [kmBeta, terrasA, terrasState]
  | append_singleton σ' b ih =>
    rw [← List.append_assoc, km_beta_snoc, km_beta_snoc, terrasA_snoc, ih, List.length_append]
    cases b
    · simp
    · simp only [↓reduceIte]; ring

/-- **Lemma B.5 (i)**: `γ_{X'} = 421`, `γ_{Y'} = 5069`. -/
theorem km_beta_X : kmBeta blkX = 421 := by decide
theorem km_beta_Y : kmBeta blkY = 5069 := by decide

lemma km_A_X : terrasA blkX = 5 := by rw [terrasA_eq]; decide
lemma km_A_Y : terrasA blkY = 7 := by rw [terrasA_eq]; decide
lemma km_len_X : blkX.length = 8 := rfl
lemma km_len_Y : blkY.length = 11 := rfl

/-- `γ_{X'Y'} - γ_{Y'X'} = 2^9 3^5 = 124416`. -/
lemma km_beta_XY : kmBeta (blkX ++ blkY) = kmBeta (blkY ++ blkX) + 124416 := by
  rw [km_beta_append, km_beta_append, km_beta_X, km_beta_Y, km_A_X, km_A_Y, km_len_X, km_len_Y]
  norm_num


/-! ### Formulas modulo `2^M` -/

/-- The inverse of 3 modulo `2^M`. -/
lemma km_three_inv (M : ℕ) : (3 : ZMod (2 ^ M)) * (3 : ZMod (2 ^ M))⁻¹ = 1 := by
  have h := ZMod.coe_mul_inv_eq_one (n := 2 ^ M) 3 (Nat.Coprime.pow_right _ (by norm_num))
  exact_mod_cast h

lemma km_two_pow_self (M : ℕ) : (2 : ZMod (2 ^ M)) ^ M = 0 := by
  exact_mod_cast ZMod.natCast_self (2 ^ M)

/-- The affine formula modulo `2^m`: `r_σ ≡ -γ_σ 3^{-a_σ}`. -/
theorem km_r_zmod (σ : List Bool) (M : ℕ) (hM : σ.length = M) :
    (terrasR σ : ZMod (2 ^ M)) =
      -(kmBeta σ : ZMod (2 ^ M)) * ((3 : ZMod (2 ^ M))⁻¹) ^ terrasA σ := by
  have h := congrArg (fun x : ℕ => (x : ZMod (2 ^ M))) (km_affine σ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hM, Nat.cast_ofNat, km_two_pow_self,
    zero_mul] at h
  have hu : (3 : ZMod (2 ^ M)) ^ terrasA σ * ((3 : ZMod (2 ^ M))⁻¹) ^ terrasA σ = 1 := by
    rw [← mul_pow, km_three_inv, one_pow]
  linear_combination (((3 : ZMod (2 ^ M))⁻¹) ^ terrasA σ) * h - (terrasR σ : ZMod (2 ^ M)) * hu

/-- **Lemma B.5 (ii)** (swaps are translations): `r_{φX'Y'χ} = r_{φY'X'χ} - 2^{m_φ+9} 3^{-(a_φ+7)}` modulo `2^m`. -/
theorem km_swap_one (φ χ : List Bool) (M : ℕ) (hM : (φ ++ blkX ++ blkY ++ χ).length = M) :
    (terrasR (φ ++ blkX ++ blkY ++ χ) : ZMod (2 ^ M)) =
      terrasR (φ ++ blkY ++ blkX ++ χ) -
        2 ^ (φ.length + 9) * ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA φ + 7) := by
  have hM' : (φ ++ blkY ++ blkX ++ χ).length = M := by
    simp only [List.length_append, km_len_X, km_len_Y] at hM ⊢; omega
  rw [km_r_zmod _ M hM, km_r_zmod _ M hM']
  have hA1 : terrasA (φ ++ blkX ++ blkY ++ χ) = terrasA φ + 12 + terrasA χ := by
    simp only [terrasA_append, km_A_X, km_A_Y]
  have hA2 : terrasA (φ ++ blkY ++ blkX ++ χ) = terrasA φ + 12 + terrasA χ := by
    simp only [terrasA_append, km_A_X, km_A_Y]
  have hB : kmBeta (φ ++ blkX ++ blkY ++ χ) =
      kmBeta (φ ++ blkY ++ blkX ++ χ) + 3 ^ terrasA χ * 2 ^ φ.length * 124416 := by
    rw [List.append_assoc φ blkX blkY, List.append_assoc φ blkY blkX, km_beta_append (φ ++ _),
      km_beta_append (φ ++ _), km_beta_append φ, km_beta_append φ, km_beta_XY]
    simp only [List.length_append, km_len_X, km_len_Y, terrasA_append, km_A_X, km_A_Y]
    ring
  rw [hA1, hA2, hB]
  have hu : (3 : ZMod (2 ^ M)) ^ (terrasA χ + 5) * ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA χ + 5) = 1 := by
    rw [← mul_pow, km_three_inv, one_pow]
  push_cast
  linear_combination (-(2 : ZMod (2 ^ M)) ^ (φ.length + 9) * ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA φ + 7)) * hu

/-! ### Swapping coins -/

/-- Swapping coins: swap the two blocks at positions `(2j, 2j+1)` (`j < I`) of `L` if `e j`. -/
def kmSwap : (I : ℕ) → (Fin I → Bool) → List Bool → List Bool
  | 0, _, L => L
  | I + 1, e, x :: y :: L => (if e 0 then [y, x] else [x, y]) ++ kmSwap I (fun j => e j.succ) L
  | _ + 1, _, L => L

/-- The sign of coin `j`: `+1` for `(X', Y')`, `-1` for `(Y', X')`, `0` for equal blocks. -/
def kmOri (L : List Bool) (j : ℕ) : ℤ :=
  if L.getD (2 * j) false = L.getD (2 * j + 1) false then 0
  else if L.getD (2 * j) false then 1 else -1

/-- The parity word of the late part before coin `j`. -/
def kmPre (L : List Bool) (j : ℕ) : List Bool := parityOf (L.take (2 * j))

lemma km_parityOf_cons (x : Bool) (L : List Bool) :
    parityOf (x :: L) = (if x then blkX else blkY) ++ parityOf L := by
  simp [parityOf]

theorem km_swap_perm (I : ℕ) : ∀ (e : Fin I → Bool) (L : List Bool), (kmSwap I e L).Perm L := by
  induction I with
  | zero => intro e L; simp [kmSwap]
  | succ I ih =>
    intro e L
    rcases L with _ | ⟨x, _ | ⟨y, L⟩⟩
    · simp [kmSwap]
    · simp [kmSwap]
    · simp only [kmSwap]
      have h := ih (fun j => e j.succ) L
      split_ifs
      · exact (List.Perm.append (List.Perm.swap x y []) h)
      · exact (List.Perm.append (List.Perm.refl [x, y]) h)

theorem km_swap_invol (I : ℕ) : ∀ (e : Fin I → Bool) (L : List Bool),
    kmSwap I e (kmSwap I e L) = L := by
  induction I with
  | zero => intro e L; simp [kmSwap]
  | succ I ih =>
    intro e L
    rcases L with _ | ⟨x, _ | ⟨y, L⟩⟩
    · simp [kmSwap]
    · simp [kmSwap]
    · cases h : e 0 <;> simp [kmSwap, h, ih]

theorem km_swap_false (I : ℕ) : ∀ L : List Bool, kmSwap I (fun _ => false) L = L := by
  induction I with
  | zero => intro L; simp [kmSwap]
  | succ I ih =>
    intro L
    rcases L with _ | ⟨x, _ | ⟨y, L⟩⟩
    · simp [kmSwap]
    · simp [kmSwap]
    · simp [kmSwap, ih]

lemma km_swap_count (I : ℕ) (e : Fin I → Bool) (L : List Bool) (b : Bool) :
    (kmSwap I e L).count b = L.count b := (km_swap_perm I e L).count_eq b

lemma km_swap_length (I : ℕ) (e : Fin I → Bool) (L : List Bool) :
    (kmSwap I e L).length = L.length := (km_swap_perm I e L).length_eq

lemma km_swap_wt (I : ℕ) (e : Fin I → Bool) (L : List Bool) : wtβ (kmSwap I e L) = wtβ L := by
  unfold wtβ
  exact ((km_swap_perm I e L).map _).prod_eq

lemma km_par_len_count (L : List Bool) :
    (parityOf L).length = 8 * L.count true + 11 * L.count false := (fam_parityOf_counts L).1

lemma km_par_A_count (L : List Bool) :
    terrasA (parityOf L) = 5 * L.count true + 7 * L.count false := by
  rw [terrasA_eq]; exact (fam_parityOf_counts L).2.1

lemma km_swap_parlen (I : ℕ) (e : Fin I → Bool) (L : List Bool) :
    (parityOf (kmSwap I e L)).length = (parityOf L).length := by
  rw [km_par_len_count, km_par_len_count, km_swap_count, km_swap_count]

lemma km_swap_parA (I : ℕ) (e : Fin I → Bool) (L : List Bool) :
    terrasA (parityOf (kmSwap I e L)) = terrasA (parityOf L) := by
  rw [km_par_A_count, km_par_A_count, km_swap_count, km_swap_count]

lemma km_ori_cons2 (x y : Bool) (L : List Bool) (j : ℕ) : kmOri (x :: y :: L) (j + 1) = kmOri L j := by
  unfold kmOri
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, show 2 * j + 1 + 1 + 1 = 2 * j + 1 + 1 + 1 from rfl]
  simp only [List.getD_cons_succ]

lemma km_pre_cons2 (x y : Bool) (L : List Bool) (j : ℕ) :
    kmPre (x :: y :: L) (j + 1) = parityOf [x, y] ++ kmPre L j := by
  unfold kmPre
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.take_succ_cons, List.take_succ_cons,
    ← fam_parityOf_append]
  rfl

lemma km_pre_zero (L : List Bool) : kmPre L 0 = [] := by simp [kmPre, parityOf]

lemma km_A_nil : terrasA [] = 0 := rfl

/-- The translation from swapping coin `0` (Lemma B.5 (ii) applied to one coin). -/
lemma km_swap_head (π χ : List Bool) (x y b : Bool) (M : ℕ)
    (hM : (π ++ parityOf [x, y] ++ χ).length = M) :
    (terrasR (π ++ parityOf (if b then [y, x] else [x, y]) ++ χ) : ZMod (2 ^ M)) =
      terrasR (π ++ parityOf [x, y] ++ χ) +
        (if b then (kmOri [x, y] 0 : ZMod (2 ^ M)) * 2 ^ (π.length + 9) *
          ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA π + 7) else 0) := by
  cases b
  · simp
  · simp only [↓reduceIte]
    cases x <;> cases y
    · simp [kmOri]
    · -- (Y', X') → (X', Y'): sign -1
      have hM' : (π ++ blkY ++ blkX ++ χ).length = M := by
        rw [← hM]; simp [parityOf]
      have h := km_swap_one π χ M (by rw [← hM']; simp [km_len_X, km_len_Y]; omega)
      have e1 : π ++ parityOf [true, false] ++ χ = π ++ blkX ++ blkY ++ χ := by
        simp [parityOf]
      have e2 : π ++ parityOf [false, true] ++ χ = π ++ blkY ++ blkX ++ χ := by
        simp [parityOf]
      rw [e1, e2, h]
      simp [kmOri, sub_eq_add_neg]
    · -- (X', Y') → (Y', X'): sign +1
      have h := km_swap_one π χ M (by rw [← hM]; simp [parityOf])
      have e1 : π ++ parityOf [true, false] ++ χ = π ++ blkX ++ blkY ++ χ := by
        simp [parityOf]
      have e2 : π ++ parityOf [false, true] ++ χ = π ++ blkY ++ blkX ++ χ := by
        simp [parityOf]
      rw [e1, e2, h]
      simp [kmOri]
    · simp [kmOri]

/-- **Lemma B.5 (iii)** (the orbit of the coins): modulo `2^m`,
`r_{π (L^e) ζ} = r_{π L ζ} + Σ_j e_j o_j 2^{m_j+9} 3^{-(a_j+7)}`. -/
theorem km_swap_multi (I : ℕ) : ∀ (e : Fin I → Bool) (π L ζ : List Bool) (M : ℕ),
    2 * I ≤ L.length → (π ++ parityOf L ++ ζ).length = M →
    (terrasR (π ++ parityOf (kmSwap I e L) ++ ζ) : ZMod (2 ^ M)) =
      terrasR (π ++ parityOf L ++ ζ) +
        ∑ j : Fin I, (if e j then (kmOri L j : ZMod (2 ^ M)) *
          2 ^ (π.length + (kmPre L j).length + 9) *
          ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA π + terrasA (kmPre L j) + 7) else 0) := by
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
      have hpar : ∀ S : List Bool, π ++ parityOf (c ++ S) ++ ζ = (π ++ parityOf c) ++ parityOf S ++ ζ := by
        intro S; rw [fam_parityOf_append]; simp
      have hparL : π ++ parityOf (x :: y :: L) ++ ζ = π ++ parityOf [x, y] ++ (parityOf L ++ ζ) := by
        rw [show x :: y :: L = [x, y] ++ L from rfl, fam_parityOf_append]; simp
      have hM2 : ((π ++ parityOf c) ++ parityOf L ++ ζ).length = M := by
        rw [← hM, hparL]; simp only [List.length_append, hcL]; omega
      have hunf : kmSwap (I + 1) e (x :: y :: L) = c ++ kmSwap I (fun j => e j.succ) L := by
        simp [kmSwap, hc]
      rw [hunf, hpar, ih (fun j => e j.succ) (π ++ parityOf c) L ζ M (by simp at hL; omega) hM2]
      rw [Fin.sum_univ_succ]
      have hhead := km_swap_head π (parityOf L ++ ζ) x y (e 0) M (by rw [← hM, hparL])
      have e3 : π ++ parityOf c ++ parityOf L ++ ζ = π ++ parityOf c ++ (parityOf L ++ ζ) := by simp
      have h0 : (if e 0 = true then (kmOri [x, y] 0 : ZMod (2 ^ M)) * 2 ^ (π.length + 9) *
            ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA π + 7) else 0) =
          (if e 0 = true then (kmOri (x :: y :: L) ((0 : Fin (I + 1)) : ℕ) : ZMod (2 ^ M)) *
            2 ^ (π.length + (kmPre (x :: y :: L) ((0 : Fin (I + 1)) : ℕ)).length + 9) *
            ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA π + terrasA (kmPre (x :: y :: L) ((0 : Fin (I + 1)) : ℕ)) + 7)
            else 0) := by
        simp [kmOri, km_pre_zero, km_A_nil]
      have hs : ∀ j : Fin I, (if e j.succ = true then (kmOri L j : ZMod (2 ^ M)) *
            2 ^ ((π ++ parityOf c).length + (kmPre L j).length + 9) *
            ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA (π ++ parityOf c) + terrasA (kmPre L j) + 7) else 0) =
          (if e j.succ = true then (kmOri (x :: y :: L) (j.succ : ℕ) : ZMod (2 ^ M)) *
            2 ^ (π.length + (kmPre (x :: y :: L) (j.succ : ℕ)).length + 9) *
            ((3 : ZMod (2 ^ M))⁻¹) ^ (terrasA π + terrasA (kmPre (x :: y :: L) (j.succ : ℕ)) + 7)
            else 0) := by
        intro j
        rw [Fin.val_succ, km_ori_cons2, km_pre_cons2, List.length_append, terrasA_append,
          List.length_append, terrasA_append, hcL, hcA]
        simp only [add_assoc]
      rw [e3, hhead, ← hparL, add_assoc, h0, Finset.sum_congr rfl (fun j _ => hs j)]

end Collatz.Arctic
