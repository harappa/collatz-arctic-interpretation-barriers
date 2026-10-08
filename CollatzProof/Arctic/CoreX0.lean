/-
Partition of the digits of the starting point `x₀` (assembly of Theorem 6.8 of the paper). The partition `𝒫` for the upper bound at `x₀` in the proof of Theorem 6.8:
the top window `τ` (exceptional), `M'` intervals of the free bits, `ρ` (exceptional), `M` intervals of block indices of the Terras
part, and the shared part (exceptional).
-/
import CollatzProof.Arctic.CorePart
import CollatzProof.Arctic.CoreWindow
import CollatzProof.Arctic.Family

namespace Collatz.Arctic

/-! ## Properties of `blockEnd` -/

lemma length_blk (x : Bool) : (if x then blkX else blkY).length ≤ 11 := by
  cases x <;> simp [blkX, blkY]

lemma blockEnd_succ_le (β : List Bool) (i : ℕ) : blockEnd β (i + 1) ≤ blockEnd β i + 11 := by
  unfold blockEnd
  rcases Nat.lt_or_ge i β.length with h | h
  · rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, fam_parityOf_append,
      List.length_append]
    have : (parityOf [β[i]]).length ≤ 11 := by simpa [parityOf] using length_blk β[i]
    omega
  · rw [List.take_of_length_le (by omega), List.take_of_length_le h]; omega

lemma blockEnd_mono (β : List Bool) {i i' : ℕ} (h : i ≤ i') : blockEnd β i ≤ blockEnd β i' := by
  unfold blockEnd
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, fam_parityOf_append, List.length_append]; omega

lemma blockEnd_sub_le (β : List Bool) (i d : ℕ) : blockEnd β (i + d) ≤ blockEnd β i + 11 * d := by
  induction d with
  | zero => simp
  | succ d ih => have := blockEnd_succ_le β (i + d); rw [← add_assoc]; omega

lemma blockEnd_append_length (β₀ β : List Bool) :
    blockEnd (β₀ ++ β) β₀.length = (parityOf β₀).length := by
  simp [blockEnd]

lemma blockEnd_full (β : List Bool) : blockEnd β β.length = (parityOf β).length := by
  simp [blockEnd]

lemma blockEnd_le_full (β : List Bool) (i : ℕ) : blockEnd β i ≤ (parityOf β).length := by
  unfold blockEnd
  have := List.take_append_drop i β
  conv_rhs => rw [← this]
  rw [fam_parityOf_append, List.length_append]; omega

/-! ## Digits of the starting point -/

/-- `bin'(x₀) = bin'(τ) · u · ρ · r_σ` (`r_σ` written with `m` digits). -/
theorem binTail_X0_split {β₀ β : List Bool} (hpre : β₀ <+: β) {n K τ u : ℕ}
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    binTail (famX0 β₀ β n K τ u)
      = binTail τ ++ bitsMSB (n - K - (parityOf β₀).length) u
        ++ bitsMSB (parityOf β₀).length (famRho β₀ β)
        ++ bitsMSB (parityOf β).length (terrasR (parityOf β)) := by
  rw [fam_binTail_X0 hpre hKn hτ hu]
  have hsm := fam_s_le hpre
  have hr : bitsMSB (parityOf β).length (terrasR (parityOf β))
      = bitsMSB ((parityOf β).length - (parityOf β₀).length) (famRtop β₀ β) ++
        bitsMSB (parityOf β₀).length (terrasR (parityOf β₀)) := by
    rw [fam_terrasR_split hpre]
    have := bitsMSB_add_mul ((parityOf β).length - (parityOf β₀).length) (parityOf β₀).length
      (famRtop β₀ β) (terrasR (parityOf β₀)) (fam_rtop_lt hpre) (terrasR_lt _)
    rwa [Nat.sub_add_cancel hsm] at this
  rw [hr]
  simp only [List.append_assoc]

/-! ## Cut points at the starting point -/

/-- Cut points at the starting point: `τ` (`K-1` digits), `M'` pieces of the free bits, `ρ` (`s` digits), `M` pieces of the Terras part, the shared part.
`bE` converts block indices to numbers of bits (`blockEnd (β₀ ++ β)`). -/
def x0Cut (K F s m b₀ k M M' : ℕ) (bE : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 0
  else if i ≤ M' + 1 then (K - 1) + ((i - 1) * F) / M'
  else if i ≤ M' + M + 2 then (K - 1) + F + s + (m - bE (b₀ + ((M - (i - M' - 2)) * k) / M))
  else (K - 1) + F + s + m

/-- Exceptional intervals: `τ`, `ρ`, the shared part. -/
def x0Exc (M M' : ℕ) (i : ℕ) : Bool := decide (i = 0 ∨ i = M' + 1 ∨ i = M' + M + 2)

lemma add_div_le_succ (a b c : ℕ) (hc : 0 < c) : (a + b) / c ≤ a / c + b / c + 1 := by
  rw [Nat.add_div hc]; split_ifs <;> omega

lemma mul_div_mono (a a' F M : ℕ) (h : a ≤ a') : a * F / M ≤ a' * F / M :=
  Nat.div_le_div_right (Nat.mul_le_mul_right F h)

section Cuts

variable {K F s m b₀ k M M' : ℕ} {bE : ℕ → ℕ}

lemma x0Cut_zero : x0Cut K F s m b₀ k M M' bE 0 = 0 := by simp [x0Cut]

lemma x0Cut_free {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ M' + 1) :
    x0Cut K F s m b₀ k M M' bE i = (K - 1) + ((i - 1) * F) / M' := by
  unfold x0Cut; split_ifs <;> first | rfl | omega

lemma x0Cut_terras {i : ℕ} (h1 : M' + 2 ≤ i) (h2 : i ≤ M' + M + 2) :
    x0Cut K F s m b₀ k M M' bE i = (K - 1) + F + s + (m - bE (b₀ + ((M - (i - M' - 2)) * k) / M)) := by
  unfold x0Cut; split_ifs <;> first | rfl | omega

lemma x0Cut_last {i : ℕ} (h1 : M' + M + 3 ≤ i) :
    x0Cut K F s m b₀ k M M' bE i = (K - 1) + F + s + m := by
  unfold x0Cut; split_ifs <;> first | rfl | omega

variable (hM : 1 ≤ M) (hM' : 1 ≤ M') (hsm : s ≤ m)
  (hmono : ∀ i i', i ≤ i' → bE i ≤ bE i') (hb₀ : bE b₀ = s) (hbk : bE (b₀ + k) = m)
  (hstep : ∀ i d, bE (i + d) ≤ bE i + 11 * d)

include hM hmono hbk in
lemma x0_hle {j : ℕ} (hj : j ≤ M) : bE (b₀ + j * k / M) ≤ m := by
  rw [← hbk]
  apply hmono
  have : j * k / M ≤ M * k / M := mul_div_mono j M k M hj
  rw [Nat.mul_div_cancel_left _ (by omega)] at this
  omega

include hM hM' hsm hmono hb₀ hbk in
theorem x0Cut_mono : ∀ i < M' + M + 3,
    x0Cut K F s m b₀ k M M' bE i ≤ x0Cut K F s m b₀ k M M' bE (i + 1) := by
  intro i hi
  have hMk : M * k / M = k := Nat.mul_div_cancel_left _ (by omega)
  have hM'F : M' * F / M' = F := Nat.mul_div_cancel_left _ (by omega)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [x0Cut_zero]; exact Nat.zero_le _
  rcases Nat.lt_or_ge i (M' + 1) with h1 | h1
  · rw [x0Cut_free (by omega) (by omega), x0Cut_free (by omega) (by omega)]
    have := mul_div_mono (i - 1) (i + 1 - 1) F M' (by omega); omega
  rcases Nat.lt_or_ge i (M' + 2) with h2 | h2
  · -- `ρ` (i = M' + 1)
    rw [x0Cut_free (by omega) (by omega), x0Cut_terras (by omega) (by omega),
      show i - 1 = M' by omega, hM'F]
    omega
  rcases Nat.lt_or_ge i (M' + M + 2) with h3 | h3
  · rw [x0Cut_terras (by omega) (by omega), x0Cut_terras (by omega) (by omega)]
    have h4 := hmono (b₀ + (M - (i + 1 - M' - 2)) * k / M) (b₀ + (M - (i - M' - 2)) * k / M)
      (by have := mul_div_mono (M - (i + 1 - M' - 2)) (M - (i - M' - 2)) k M (by omega); omega)
    have := x0_hle hM hmono hbk (j := M - (i - M' - 2)) (by omega)
    have := x0_hle hM hmono hbk (j := M - (i + 1 - M' - 2)) (by omega)
    omega
  · rw [x0Cut_terras (by omega) (by omega), x0Cut_last (by omega)]
    omega

include hM hM' hsm hmono hb₀ hbk hstep in
theorem x0Cut_width : ∀ i < M' + M + 3,
    x0Cut K F s m b₀ k M M' bE (i + 1) ≤
      x0Cut K F s m b₀ k M M' bE i + ((K - 1) + s + (F / M' + 1) + 11 * (k / M + 1)) := by
  intro i hi
  have hMk : M * k / M = k := Nat.mul_div_cancel_left _ (by omega)
  have hM'F : M' * F / M' = F := Nat.mul_div_cancel_left _ (by omega)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [x0Cut_zero, x0Cut_free (i := 0 + 1) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel, Nat.sub_self, zero_mul, Nat.zero_div, add_zero, zero_add]
    generalize F / M' = qF at *
    generalize k / M = qk at *
    omega
  rcases Nat.lt_or_ge i (M' + 1) with h1 | h1
  · rw [x0Cut_free (i := i + 1) (by omega) (by omega), x0Cut_free (i := i) (by omega) (by omega)]
    have := add_div_le_succ ((i - 1) * F) F M' (by omega)
    rw [show (i - 1) * F + F = (i + 1 - 1) * F by
      rw [show i + 1 - 1 = (i - 1) + 1 by omega, add_mul, one_mul]] at this
    generalize (i + 1 - 1) * F / M' = a1 at *
    generalize (i - 1) * F / M' = a0 at *
    generalize F / M' = qF at *
    generalize k / M = qk at *
    omega
  rcases Nat.lt_or_ge i (M' + 2) with h2 | h2
  · rw [x0Cut_free (i := i) (by omega) (by omega), x0Cut_terras (i := i + 1) (by omega) (by omega),
      show i - 1 = M' by omega, hM'F, show M - (i + 1 - M' - 2) = M by omega, hMk, hbk]
    generalize F / M' = qF at *
    generalize k / M = qk at *
    omega
  rcases Nat.lt_or_ge i (M' + M + 2) with h3 | h3
  · rw [x0Cut_terras (i := i + 1) (by omega) (by omega), x0Cut_terras (i := i) (by omega) (by omega)]
    obtain ⟨j, hj, hj'⟩ : ∃ j, M - (i + 1 - M' - 2) = j ∧ M - (i - M' - 2) = j + 1 :=
      ⟨M - (i + 1 - M' - 2), rfl, by omega⟩
    rw [hj, hj']
    have hd := add_div_le_succ (j * k) k M (by omega)
    rw [show j * k + k = (j + 1) * k by ring] at hd
    have hmd := mul_div_mono j (j + 1) k M (by omega)
    have hs := hstep (b₀ + j * k / M) ((j + 1) * k / M - j * k / M)
    rw [show b₀ + j * k / M + ((j + 1) * k / M - j * k / M) = b₀ + (j + 1) * k / M by omega] at hs
    have h5 := x0_hle hM hmono hbk (j := j) (by omega)
    have h6 := x0_hle hM hmono hbk (j := j + 1) (by omega)
    have h7 := hmono (b₀ + j * k / M) (b₀ + (j + 1) * k / M) (by omega)
    have h8 : (j + 1) * k / M - j * k / M ≤ k / M + 1 := by omega
    have h9 : 11 * ((j + 1) * k / M - j * k / M) ≤ 11 * (k / M + 1) := Nat.mul_le_mul_left 11 h8
    generalize (j + 1) * k / M = b1 at *
    generalize j * k / M = b0 at *
    generalize F / M' = qF at *
    generalize k / M = qk at *
    omega
  · rw [x0Cut_terras (i := i) (by omega) (by omega), x0Cut_last (i := i + 1) (by omega),
      show M - (i - M' - 2) = 0 by omega, zero_mul, Nat.zero_div, add_zero, hb₀]
    generalize F / M' = qF at *
    generalize k / M = qk at *
    omega

include hM hM' hsm hmono hb₀ hbk in
theorem x0Cut_exc :
    (∑ i ∈ Finset.range (M' + M + 3), (if x0Exc M M' i then
      x0Cut K F s m b₀ k M M' bE (i + 1) - x0Cut K F s m b₀ k M M' bE i else 0)) = (K - 1) + s + s := by
  have hMk : M * k / M = k := Nat.mul_div_cancel_left _ (by omega)
  have hM'F : M' * F / M' = F := Nat.mul_div_cancel_left _ (by omega)
  rw [← Finset.sum_subset (s₁ := {0, M' + 1, M' + M + 2}) (s₂ := Finset.range (M' + M + 3))]
  · rw [Finset.sum_insert (by simp <;> omega), Finset.sum_insert (by simp <;> omega), Finset.sum_singleton]
    have e0 : x0Exc M M' 0 = true := by simp [x0Exc]
    have e1 : x0Exc M M' (M' + 1) = true := by simp [x0Exc]
    have e2 : x0Exc M M' (M' + M + 2) = true := by simp [x0Exc]
    simp only [e0, e1, e2, ↓reduceIte]
    rw [x0Cut_zero, x0Cut_free (i := 0 + 1) (by omega) (by omega),
      x0Cut_free (i := M' + 1) (by omega) (by omega), x0Cut_terras (i := M' + 1 + 1) (by omega) (by omega),
      x0Cut_terras (i := M' + M + 2) (by omega) (by omega), x0Cut_last (i := M' + M + 2 + 1) (by omega),
      show M' + 1 - 1 = M' by omega, hM'F, show M - (M' + 1 + 1 - M' - 2) = M by omega, hMk, hbk,
      show M - (M' + M + 2 - M' - 2) = 0 by omega, zero_mul, Nat.zero_div, add_zero, hb₀]
    simp only [Nat.add_sub_cancel, zero_mul, Nat.zero_div, add_zero]
    omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_range]
    omega
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have : x0Exc M M' x = false := by simp [x0Exc]; omega
    simp [this]

end Cuts


/-- **Partition at the starting point**: for `w = p₁ ++ U ++ P₂ ++ R` (`τ`, free bits, `ρ`, `r_σ`), the list of intervals of the cut points `x0Cut` is
an `Upper.GoodPartition` under the window conditions and the conditions on widths, number and exceptional length. -/
theorem x0_goodPartition (p₁ U P₂ R : Word) {K F s m b₀ k M M' : ℕ} {bE : ℕ → ℕ} (ε : ℝ) (J : ℕ) (δ : ℚ)
    (hp₁ : p₁.length = K - 1) (hU : U.length = F) (hP₂ : P₂.length = s) (hR : R.length = m)
    (hM : 1 ≤ M) (hM' : 1 ≤ M') (hsm : s ≤ m)
    (hmono : ∀ i i', i ≤ i' → bE i ≤ bE i') (hb₀ : bE b₀ = s) (hbk : bE (b₀ + k) = m)
    (hstep : ∀ i d, bE (i + d) ≤ bE i + 11 * d)
    (hwinU : ∀ t < M', WinClose U (t * F / M') ((t + 1) * F / M') J δ)
    (hwinR : ∀ j < M, WinClose R (m - bE (b₀ + (j + 1) * k / M)) (m - bE (b₀ + j * k / M)) J δ)
    (hW : (((K - 1) + s + (F / M' + 1) + 11 * (k / M + 1) : ℕ) : ℝ) ≤ ε * (p₁ ++ U ++ P₂ ++ R).length)
    (hcount : ((M' + M + 3 : ℕ) : ℝ) ≤ ε⁻¹ ^ 2)
    (hexc : (((K - 1) + s + s : ℕ) : ℝ) ≤ ε * (p₁ ++ U ++ P₂ ++ R).length) :
    Upper.GoodPartition (p₁ ++ U ++ P₂ ++ R)
      (cutSegs (x0Cut K F s m b₀ k M M' bE) (x0Exc M M') 0 (M' + M + 3)) ε J δ := by
  have hlen : (p₁ ++ U ++ P₂ ++ R).length = (K - 1) + F + s + m := by
    simp [hp₁, hU, hP₂, hR]; omega
  have hMk : M * k / M = k := Nat.mul_div_cancel_left _ (by omega)
  have hM'F : M' * F / M' = F := Nat.mul_div_cancel_left _ (by omega)
  apply goodPartition_of_cuts
  · exact x0Cut_mono (K := K) (F := F) hM hM' hsm hmono hb₀ hbk
  · exact x0Cut_zero
  · rw [x0Cut_last (by omega), hlen]
  · intro i hi
    have h := x0Cut_width (K := K) (F := F) hM hM' hsm hmono hb₀ hbk hstep i hi
    have h' : (x0Cut K F s m b₀ k M M' bE (i + 1) : ℝ) ≤ x0Cut K F s m b₀ k M M' bE i +
        (((K - 1) + s + (F / M' + 1) + 11 * (k / M + 1) : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  · exact hcount
  · rw [x0Cut_exc (K := K) (F := F) hM hM' hsm hmono hb₀ hbk]; exact hexc
  · intro i hi he
    have hne : ¬ (i = 0 ∨ i = M' + 1 ∨ i = M' + M + 2) := by simpa [x0Exc] using he
    rcases Nat.lt_or_ge i (M' + 1) with h1 | h1
    · -- free bits
      rw [x0Cut_free (i := i) (by omega) (by omega), x0Cut_free (i := i + 1) (by omega) (by omega)]
      have hw := hwinU (i - 1) (by omega)
      rw [show i - 1 + 1 = i + 1 - 1 by omega] at hw
      have hb : (i + 1 - 1) * F / M' ≤ U.length := by
        rw [hU]
        calc (i + 1 - 1) * F / M' ≤ M' * F / M' := mul_div_mono _ _ F M' (by omega)
          _ = F := hM'F
      have := (winClose_append_shift p₁ U (P₂ ++ R) hb δ).mpr hw
      rw [hp₁] at this
      simpa [List.append_assoc] using this
    · -- Terras part
      have h2 : M' + 2 ≤ i := by omega
      have h3 : i ≤ M' + M + 1 := by omega
      rw [x0Cut_terras (i := i) (by omega) (by omega), x0Cut_terras (i := i + 1) (by omega) (by omega)]
      obtain ⟨j, hj1, hj2⟩ : ∃ j, M - (i + 1 - M' - 2) = j ∧ M - (i - M' - 2) = j + 1 :=
        ⟨_, rfl, by omega⟩
      rw [hj1, hj2]
      have hw := hwinR j (by omega)
      have hb : m - bE (b₀ + j * k / M) ≤ R.length := by rw [hR]; omega
      have := (winClose_append_shift (p₁ ++ U ++ P₂) R [] hb δ).mpr hw
      simp only [List.append_nil, List.length_append, hp₁, hU, hP₂] at this
      convert this using 2 <;> simp [List.append_assoc] <;> omega

end Collatz.Arctic
