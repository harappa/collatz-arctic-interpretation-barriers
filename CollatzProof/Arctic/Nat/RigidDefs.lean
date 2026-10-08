/-
# Appendix D: the setting of rigidity of non-negative matrix families

The setting of Appendix D (Definition D.1) as Lean definitions.
Pure linear algebra, independent of the system $\mathcal T$ (`S_T`); only Mathlib is imported.

* A pair `D₀, D₁` of matrices with non-negative integer entries over a finite set `K` (`D : Fin 2 → Matrix K K ℕ`).
* The product of a word `x` (`List (Fin 2)`): `D_x := D_{x₁} ⋯ D_{x_n}` (the empty word gives the identity): `Dx` (real), `DxN` (natural).
* `E_x := g^{-|x|} D_x`: `Ex`.
* The matrix norm is the sum of the absolute values of the entries, `nrm` (submultiplicative; equivalent up to constants to the maximal row sum; the limit `Λ⁺` does not depend on the norm:
  `isRigid_iff_rowSum` in `RigidLower.lean`).
* **`g` is defined through the diagonal**: `gDiag D := sup_{w ≠ [], i} ((D_w)_{ii})^{1/|w|}`. With the spectral definition
  `g := sup_w ρ(D_w)^{1/|w|}`, the two notions of rigidity agree for strongly connected pairs, and then the two values of `g` are equal
  (`isRigid_iff_spectral` in `RigidSpec.lean`, Gelfand's formula). The only property of `g` that the chain of the main theorems uses is
  `(D_w)_{ii} ≤ g^{|w|}` (`diag_le_gDiag`).
* **`Λ⁺` is the limit of the averages**: `Λ⁺ = lim_n (1/n) 2^{-n} Σ_{|x|=n} log⁺ ‖D_x‖`. Rigidity `IsRigid D` means
  "`g > 1` and `(1/n) 2^{-n} Σ log⁺ ‖D_x‖ → log g`" (that is, `Λ⁺ = log g > 0`; the existence of the limit by subadditivity is not used).
* Strongly connected, `SC D`: for all `i, j` there is a word `c` with `(D_c)_{ij} ≥ 1` (the irreducibility of `D₀ + D₁`, written with words. The existence
  of an internal edge follows from `g > 1`, so it is not assumed).

Sums over the words of length `n` are handled by `wsum`, the same sum as over `Fin n → Fin 2` written recursively (`wsum_eq_sum`).
The sum over the sequences of `m` words of length `κ` is `bsum` (`wsum_mul_eq_bsum`).
-/
import Mathlib

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] [DecidableEq K]

/-! ## §1 Products of words -/

/-- The matrix of the letter `b`, cast to the reals. -/
noncomputable def DR (D : Fin 2 → Matrix K K ℕ) (b : Fin 2) : Matrix K K ℝ :=
  (D b).map (Nat.cast : ℕ → ℝ)

/-- The product of a word, `D_x = D_{x₁} ⋯ D_{x_n}` (real; the empty word gives the identity). -/
noncomputable def Dx (D : Fin 2 → Matrix K K ℕ) (x : List (Fin 2)) : Matrix K K ℝ :=
  (x.map (DR D)).prod

/-- The product of a word (natural numbers). -/
def DxN (D : Fin 2 → Matrix K K ℕ) (x : List (Fin 2)) : Matrix K K ℕ := (x.map D).prod

variable (D : Fin 2 → Matrix K K ℕ)

@[simp] theorem Dx_nil : Dx D [] = 1 := by simp [Dx]

theorem Dx_cons (b : Fin 2) (x : List (Fin 2)) : Dx D (b :: x) = DR D b * Dx D x := by
  simp [Dx]

theorem Dx_append (x y : List (Fin 2)) : Dx D (x ++ y) = Dx D x * Dx D y := by
  simp [Dx, List.prod_append]

theorem Dx_singleton (b : Fin 2) : Dx D [b] = DR D b := by simp [Dx]

theorem Dx_eq_map (x : List (Fin 2)) : Dx D x = (DxN D x).map (Nat.cast : ℕ → ℝ) := by
  induction x with
  | nil => simp [Dx, DxN]
  | cons b x ih =>
    have h := Matrix.map_mul (L := D b) (M := DxN D x) (f := Nat.castRingHom ℝ)
    simp only [Nat.coe_castRingHom] at h
    have e : DxN D (b :: x) = D b * DxN D x := by simp [DxN]
    rw [Dx_cons, ih, e, h]
    rfl

theorem Dx_apply (x : List (Fin 2)) (i j : K) : Dx D x i j = (DxN D x i j : ℝ) := by
  rw [Dx_eq_map]; rfl

theorem Dx_nonneg (x : List (Fin 2)) (i j : K) : 0 ≤ Dx D x i j := by
  rw [Dx_apply]; exact Nat.cast_nonneg _

/-- The entries of `D_x` are 0 or at least 1 (natural numbers). -/
theorem Dx_entry_zero_or_one_le (x : List (Fin 2)) (i j : K) :
    Dx D x i j = 0 ∨ 1 ≤ Dx D x i j := by
  rw [Dx_apply]
  rcases Nat.eq_zero_or_pos (DxN D x i j) with h | h
  · left; simp [h]
  · right; exact_mod_cast h

/-- `E_x := g^{-|x|} D_x`. -/
noncomputable def Ex (g : ℝ) (x : List (Fin 2)) : Matrix K K ℝ := (g ^ x.length)⁻¹ • Dx D x

@[simp] theorem Ex_nil (g : ℝ) : Ex D g [] = 1 := by simp [Ex]

theorem Ex_append (g : ℝ) (x y : List (Fin 2)) : Ex D g (x ++ y) = Ex D g x * Ex D g y := by
  simp only [Ex, Dx_append, List.length_append, pow_add, mul_inv, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, mul_comm]

theorem Ex_apply (g : ℝ) (x : List (Fin 2)) (i j : K) :
    Ex D g x i j = (g ^ x.length)⁻¹ * Dx D x i j := by
  simp [Ex]

theorem Ex_nonneg {g : ℝ} (hg : 0 ≤ g) (x : List (Fin 2)) (i j : K) : 0 ≤ Ex D g x i j := by
  rw [Ex_apply]
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hg _)) (Dx_nonneg D x i j)

theorem Dx_eq_smul_Ex {g : ℝ} (hg : g ≠ 0) (x : List (Fin 2)) :
    Dx D x = g ^ x.length • Ex D g x := by
  rw [Ex, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hg), one_smul]

/-! ## §2 The norm (the sum of the absolute values of the entries) -/

/-- The matrix norm `‖Y‖ := Σ_{i,j} |Y_{ij}|`. -/
noncomputable def nrm (Y : Matrix K K ℝ) : ℝ := ∑ i, ∑ j, |Y i j|

theorem nrm_nonneg (Y : Matrix K K ℝ) : 0 ≤ nrm Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_nrm (Y : Matrix K K ℝ) (i j : K) : |Y i j| ≤ nrm Y := by
  have h1 : |Y i j| ≤ ∑ j', |Y i j'| :=
    Finset.single_le_sum (f := fun j' => |Y i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', |Y i j'| ≤ nrm Y :=
    Finset.single_le_sum (f := fun i' => ∑ j', |Y i' j'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

theorem le_nrm (Y : Matrix K K ℝ) (i j : K) : Y i j ≤ nrm Y :=
  (le_abs_self _).trans (abs_le_nrm Y i j)

theorem nrm_mul_le (A B : Matrix K K ℝ) : nrm (A * B) ≤ nrm A * nrm B := by
  unfold nrm
  calc ∑ i, ∑ j, |(A * B) i j|
      ≤ ∑ i, ∑ j, ∑ k, |A i k| * |B k j| := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ = ∑ i, ∑ k, |A i k| * ∑ j, |B k j| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, ∑ k, |A i k| * ∑ k', ∑ j, |B k' j| := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact Finset.single_le_sum (f := fun k' => ∑ j, |B k' j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    _ = (∑ i, ∑ k, |A i k|) * ∑ k', ∑ j, |B k' j| := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm

theorem nrm_add_le (A B : Matrix K K ℝ) : nrm (A + B) ≤ nrm A + nrm B := by
  unfold nrm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => abs_add_le _ _

theorem nrm_smul (c : ℝ) (Y : Matrix K K ℝ) : nrm (c • Y) = |c| * nrm Y := by
  simp only [nrm, Matrix.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem nrm_neg (Y : Matrix K K ℝ) : nrm (-Y) = nrm Y := by
  simp [nrm]

theorem nrm_sub_comm (A B : Matrix K K ℝ) : nrm (A - B) = nrm (B - A) := by
  rw [← neg_sub, nrm_neg]

theorem nrm_sub_le (A B C : Matrix K K ℝ) : nrm (A - C) ≤ nrm (A - B) + nrm (B - C) := by
  have := nrm_add_le (A - B) (B - C)
  rwa [sub_add_sub_cancel] at this

theorem eq_of_nrm_sub_eq_zero {A B : Matrix K K ℝ} (h : nrm (A - B) = 0) : A = B := by
  ext i j
  have h1 := abs_le_nrm (A - B) i j
  rw [h] at h1
  have : (A - B) i j = 0 := abs_nonpos_iff.mp h1
  simpa [sub_eq_zero] using this

theorem nrm_pos_of_ne {A B : Matrix K K ℝ} (h : A ≠ B) : 0 < nrm (A - B) :=
  lt_of_le_of_ne (nrm_nonneg _) fun h0 => h (eq_of_nrm_sub_eq_zero h0.symm)

theorem continuous_nrm : Continuous (nrm : Matrix K K ℝ → ℝ) := by
  unfold nrm
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_abs.comp ((continuous_apply j).comp (continuous_apply i))

theorem nrm_one : nrm (1 : Matrix K K ℝ) = Fintype.card K := by
  simp only [nrm, Matrix.one_apply]
  have : ∀ i : K, ∑ j, |(if i = j then (1 : ℝ) else 0)| = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp [this]

/-- The norm of a non-negative matrix is the sum of its entries. -/
theorem nrm_of_nonneg {Y : Matrix K K ℝ} (h : ∀ i j, 0 ≤ Y i j) : nrm Y = ∑ i, ∑ j, Y i j := by
  simp only [nrm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => abs_of_nonneg (h i j)

theorem nrm_le_of_entry_le {Y : Matrix K K ℝ} {B : ℝ} (h : ∀ i j, |Y i j| ≤ B) :
    nrm Y ≤ (Fintype.card K : ℝ) ^ 2 * B := by
  unfold nrm
  calc ∑ i, ∑ j, |Y i j| ≤ ∑ _i : K, ∑ _j : K, B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = (Fintype.card K : ℝ) ^ 2 * B := by
        simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- If `D_x ≠ 0` then `‖D_x‖ ≥ 1` (the entries are natural numbers). -/
theorem one_le_nrm_Dx {x : List (Fin 2)} (h : Dx D x ≠ 0) : 1 ≤ nrm (Dx D x) := by
  obtain ⟨i, j, hij⟩ : ∃ i j, Dx D x i j ≠ 0 := by
    by_contra hc
    apply h
    ext i j
    by_contra hne
    exact hc ⟨i, j, hne⟩
  rcases Dx_entry_zero_or_one_le D x i j with h0 | h1
  · exact absurd h0 hij
  · exact h1.trans (le_nrm _ i j)

/-! ## §3 Sums over the words of length `n` -/

/-- The sum over the words of length `n` (equal to `Σ_{x : Fin n → Fin 2} F(ofFn x)` by `wsum_eq_sum`). -/
def wsum : ℕ → (List (Fin 2) → ℝ) → ℝ
  | 0, F => F []
  | n + 1, F => ∑ b : Fin 2, wsum n (fun w => F (b :: w))

theorem wsum_zero (F : List (Fin 2) → ℝ) : wsum 0 F = F [] := rfl

theorem wsum_succ (n : ℕ) (F : List (Fin 2) → ℝ) :
    wsum (n + 1) F = ∑ b : Fin 2, wsum n (fun w => F (b :: w)) := rfl

theorem wsum_eq_sum (n : ℕ) (F : List (Fin 2) → ℝ) :
    wsum n F = ∑ x : Fin n → Fin 2, F (List.ofFn x) := by
  induction n generalizing F with
  | zero => simp [wsum]
  | succ n ih =>
    rw [wsum_succ]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => ?_
    simp [Fin.consEquiv, List.ofFn_succ]

theorem wsum_append (m n : ℕ) (F : List (Fin 2) → ℝ) :
    wsum (m + n) F = wsum m (fun u => wsum n (fun v => F (u ++ v))) := by
  induction m generalizing F with
  | zero => simp [wsum]
  | succ m ih =>
    rw [Nat.succ_add, wsum_succ, wsum_succ]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ih]
    rfl

theorem wsum_mono {n : ℕ} {F G : List (Fin 2) → ℝ} (h : ∀ w, w.length = n → F w ≤ G w) :
    wsum n F ≤ wsum n G := by
  induction n generalizing F G with
  | zero => exact h [] rfl
  | succ n ih =>
    rw [wsum_succ, wsum_succ]
    refine Finset.sum_le_sum fun b _ => ih fun w hw => h (b :: w) (by simp [hw])

theorem wsum_congr {n : ℕ} {F G : List (Fin 2) → ℝ} (h : ∀ w, w.length = n → F w = G w) :
    wsum n F = wsum n G :=
  le_antisymm (wsum_mono fun w hw => (h w hw).le) (wsum_mono fun w hw => (h w hw).ge)

theorem wsum_const (n : ℕ) (c : ℝ) : wsum n (fun _ => c) = 2 ^ n * c := by
  induction n with
  | zero => simp [wsum]
  | succ n ih => rw [wsum_succ]; simp [ih, pow_succ]; ring

theorem wsum_add (n : ℕ) (F G : List (Fin 2) → ℝ) :
    wsum n (fun w => F w + G w) = wsum n F + wsum n G := by
  induction n generalizing F G with
  | zero => rfl
  | succ n ih =>
    rw [wsum_succ, wsum_succ, wsum_succ, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => ih _ _

theorem wsum_mul_left (n : ℕ) (c : ℝ) (F : List (Fin 2) → ℝ) :
    wsum n (fun w => c * F w) = c * wsum n F := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [wsum_succ, wsum_succ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => ih _

theorem wsum_nonneg {n : ℕ} {F : List (Fin 2) → ℝ} (h : ∀ w, w.length = n → 0 ≤ F w) :
    0 ≤ wsum n F := by
  have := wsum_mono (n := n) (F := fun _ => 0) (G := F) h
  rwa [wsum_const, mul_zero] at this

/-- The sum of the indicator function of a word `z` of length `n` is 1. -/
theorem wsum_indicator (z : List (Fin 2)) :
    wsum z.length (fun w => if w = z then (1 : ℝ) else 0) = 1 := by
  induction z with
  | nil => simp [wsum]
  | cons a z ih =>
    rw [List.length_cons, wsum_succ, Fintype.sum_eq_single a]
    · simpa using ih
    · intro b hb
      have : ∀ w : List (Fin 2), (if b :: w = a :: z then (1 : ℝ) else 0) = 0 := by
        intro w; simp [hb]
      simp only [this]
      rw [wsum_const, mul_zero]

/-! ## §4 Sums over sequences of `m` words of length `κ` -/

/-- The sum over the sequences of `m` words of length `κ`. -/
def bsum (κ : ℕ) : ℕ → (List (List (Fin 2)) → ℝ) → ℝ
  | 0, F => F []
  | m + 1, F => wsum κ (fun b => bsum κ m (fun bs => F (b :: bs)))

theorem wsum_mul_eq_bsum (κ m : ℕ) (F : List (Fin 2) → ℝ) :
    wsum (m * κ) F = bsum κ m (fun bs => F bs.flatten) := by
  induction m generalizing F with
  | zero => simp [wsum, bsum]
  | succ m ih =>
    rw [Nat.succ_mul, Nat.add_comm, wsum_append]
    simp only [bsum]
    congr 1
    funext b
    rw [ih]
    rfl

/-- Validity of a sequence: `m` words, each of length `κ`. -/
def Valid (κ m : ℕ) (bs : List (List (Fin 2))) : Prop := bs.length = m ∧ ∀ b ∈ bs, b.length = κ

theorem bsum_mono {κ m : ℕ} {F G : List (List (Fin 2)) → ℝ} (h : ∀ bs, Valid κ m bs → F bs ≤ G bs) :
    bsum κ m F ≤ bsum κ m G := by
  induction m generalizing F G with
  | zero => exact h [] ⟨rfl, by simp⟩
  | succ m ih =>
    simp only [bsum]
    refine wsum_mono fun b hb => ih fun bs hbs => h (b :: bs) ⟨by simp [hbs.1], ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hb
    · exact hbs.2 c hc

theorem Valid.flatten_length {κ m : ℕ} {bs : List (List (Fin 2))} (h : Valid κ m bs) :
    bs.flatten.length = m * κ := by
  obtain ⟨hl, hb⟩ := h
  induction bs generalizing m with
  | nil => simp at hl; simp [← hl]
  | cons b bs ih =>
    simp only [List.length_cons] at hl
    subst hl
    rw [List.flatten_cons, List.length_append, hb b (by simp),
      ih rfl (fun c hc => hb c (by simp [hc]))]
    ring

/-- The sum of the affine expression `a + c · (number of occurrences of z)`. -/
theorem bsum_affine_count (κ : ℕ) (z : List (Fin 2)) (hz : z.length = κ) (a c : ℝ) (m : ℕ) :
    bsum κ m (fun bs => a + c * (bs.count z : ℝ)) = 2 ^ (m * κ) * (a + c * m / 2 ^ κ) := by
  induction m generalizing a with
  | zero => simp [bsum]
  | succ m ih =>
    simp only [bsum]
    have hstep : ∀ b : List (Fin 2),
        bsum κ m (fun bs => a + c * ((b :: bs).count z : ℝ)) =
          2 ^ (m * κ) * ((a + c * (if b = z then 1 else 0)) + c * m / 2 ^ κ) := by
      intro b
      rw [← ih (a + c * (if b = z then 1 else 0))]
      congr 1
      funext bs
      rw [List.count_cons]
      by_cases hb : b = z
      · subst hb; simp; ring
      · simp [hb]
    simp_rw [hstep]
    rw [wsum_mul_left]
    have hsplit : wsum κ (fun b => (a + c * m / 2 ^ κ) + c * (if b = z then (1 : ℝ) else 0)) =
        2 ^ κ * (a + c * m / 2 ^ κ) + c := by
      rw [wsum_add, wsum_const, wsum_mul_left, ← hz, wsum_indicator, mul_one]
    have : (fun b : List (Fin 2) => (a + c * (if b = z then (1 : ℝ) else 0)) + c * m / 2 ^ κ) =
        fun b => (a + c * m / 2 ^ κ) + c * (if b = z then (1 : ℝ) else 0) := by
      funext b; ring
    rw [this, hsplit]
    have h2 : (2 : ℝ) ^ κ ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [Nat.succ_mul, pow_add]
    field_simp
    push_cast
    ring

/-! ## §5 Rigidity and `g` -/

/-- The average of `log⁺ ‖D_x‖` over the words of length `n`, `2^{-n} Σ_{|x|=n} log⁺ ‖D_x‖`. -/
noncomputable def bAvg (n : ℕ) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * ∑ x : Fin n → Fin 2, Real.posLog (nrm (Dx D (List.ofFn x)))

/-- The diagonal definition of `g`: `sup_{w ≠ [], i} ((D_w)_{ii})^{1/|w|}`. -/
noncomputable def gDiag : ℝ :=
  ⨆ p : {w : List (Fin 2) // w ≠ []} × K, (Dx D p.1.1 p.2 p.2) ^ ((p.1.1.length : ℝ)⁻¹)

/-- Rigidity (`Λ⁺ = log g > 0`): `g > 1` and `(1/n) 2^{-n} Σ_{|x|=n} log⁺ ‖D_x‖ → log g`. -/
def IsRigid : Prop :=
  1 < gDiag D ∧ Tendsto (fun n : ℕ => bAvg D n / n) atTop (𝓝 (Real.log (gDiag D)))

/-- Rigidity with `g` as an argument (used inside the proofs). -/
structure RigidAt (g : ℝ) : Prop where
  one_lt : 1 < g
  diag_le : ∀ (w : List (Fin 2)) (i : K), Dx D w i i ≤ g ^ w.length
  tendsto : Tendsto (fun n : ℕ => bAvg D n / n) atTop (𝓝 (Real.log g))

/-- Strongly connected: for all `i, j` there is a word `c` with `(D_c)_{ij} ≥ 1` (the irreducibility of `D₀ + D₁`). -/
def SC : Prop := ∀ i j : K, ∃ c : List (Fin 2), 1 ≤ Dx D c i j

end Collatz.Arctic.NatQ5.Rigid
