/-
# Case B: the deterministic parts (Proposition 12.31 of the paper)

The deterministic form of the step "contradiction" in the proof of Proposition 12.31 of the paper.

* `mono_iter`: if the value does not increase along steps of `T` on `3 ∤ n`, it does not increase along a segment of the orbit (all points at least 2).
* `up_bound`: the upper bound `V ≤ (C_lo + ε) N₀^{d_lo}` at the starting point (from the upper bound of the form of Proposition 12.27 (i), absorbing the terms of lower degree and the error).
* `low_bound`: the lower bound `(C_d - ε) N₁^d ≤ V` at the end point (from the lower bound of the form of Proposition 12.28 (i)).
* `compare`: `V(x₀) < V(x₁)` from the lexicographic minimum and the expansion of lengths `N₁ ≥ (1 + κ) N₀`.
-/
import CollatzProof.Arctic.Nat.W3hTailX0
import CollatzProof.Arctic.Nat.AutoCore

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

/-- Monotonicity of the value along a segment of the orbit. -/
theorem mono_iter {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (hmono : AutoMono3 B) :
    ∀ (m x : ℕ), (∀ i < m, 2 ≤ T^[i] x) → ¬ 3 ∣ x → aval B (binWord (T^[m] x)) ≤ aval B (binWord x) := by
  intro m
  induction m with
  | zero => intro x _ _; simp
  | succ m ih =>
    intro x horb h3
    have hx : 2 ≤ x := by simpa using horb 0 (Nat.succ_pos m)
    have h3' : ¬ 3 ∣ T x := fun h => h3 (three_dvd_of_three_dvd_T h)
    have horb' : ∀ i < m, 2 ≤ T^[i] (T x) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    rw [Function.iterate_succ_apply]
    exact le_trans (ih (T x) horb' h3') (hmono x hx h3)

/-- **Comparison** (an inequality of real numbers). -/
theorem compare {N₀ N₁ Clo C₁ cs ε κ V₀ V₁ : ℝ} {dlo d₁ : ℕ} (hN0 : 1 ≤ N₀) (hN01 : (1 + κ) * N₀ ≤ N₁)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hdlo : 1 ≤ dlo) (hClo : 0 < Clo) (hcs : 0 < cs) (hε0 : 0 < ε)
    (hεκ : ε ≤ Clo * κ / 4) (hεc : ε ≤ cs / 2) (hN1big : 2 * (Clo + ε) / cs < N₁)
    (hV0 : V₀ ≤ (Clo + ε) * N₀ ^ dlo) (hV1 : (C₁ - ε) * N₁ ^ d₁ ≤ V₁)
    (hcase : cs ≤ C₁ ∧ (dlo < d₁ ∨ (d₁ = dlo ∧ Clo ≤ C₁))) : V₀ < V₁ := by
  have hN1 : N₀ ≤ N₁ := by nlinarith
  have hN1' : 1 ≤ N₁ := le_trans hN0 hN1
  have hP0 : 0 < N₀ ^ dlo := by positivity
  rcases hcase with ⟨hcs1, hlt | ⟨heq, hge⟩⟩
  · -- the degree goes up
    have h1 : N₁ ^ (dlo + 1) ≤ N₁ ^ d₁ := pow_le_pow_right₀ hN1' hlt
    have h2 : N₀ ^ dlo ≤ N₁ ^ dlo := pow_le_pow_left₀ (by linarith) hN1 dlo
    have h3 : N₁ * N₀ ^ dlo ≤ N₁ ^ d₁ := by
      calc N₁ * N₀ ^ dlo ≤ N₁ * N₁ ^ dlo := mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = N₁ ^ (dlo + 1) := by ring
        _ ≤ _ := h1
    have hc2 : cs / 2 ≤ C₁ - ε := by linarith
    have hbig : Clo + ε < cs / 2 * N₁ := by
      rw [div_lt_iff₀ hcs] at hN1big; linarith
    calc V₀ ≤ (Clo + ε) * N₀ ^ dlo := hV0
      _ < cs / 2 * N₁ * N₀ ^ dlo := mul_lt_mul_of_pos_right hbig hP0
      _ = cs / 2 * (N₁ * N₀ ^ dlo) := by ring
      _ ≤ (C₁ - ε) * N₁ ^ d₁ := mul_le_mul hc2 h3 (by positivity) (by linarith)
      _ ≤ V₁ := hV1
  · -- the same degree, coefficient at least `C_lo`
    subst heq
    have hClo' : 0 < Clo - ε := by nlinarith
    have h1 : (1 + κ) * N₀ ^ d₁ ≤ N₁ ^ d₁ := by
      have h2 : (1 + κ) ≤ (1 + κ) ^ d₁ := le_self_pow₀ (by linarith) (by omega)
      calc (1 + κ) * N₀ ^ d₁ ≤ (1 + κ) ^ d₁ * N₀ ^ d₁ := mul_le_mul_of_nonneg_right h2 hP0.le
        _ = ((1 + κ) * N₀) ^ d₁ := (mul_pow _ _ _).symm
        _ ≤ N₁ ^ d₁ := pow_le_pow_left₀ (by positivity) hN01 d₁
    have hkey : Clo + ε < (Clo - ε) * (1 + κ) := by nlinarith
    calc V₀ ≤ (Clo + ε) * N₀ ^ d₁ := hV0
      _ < (Clo - ε) * (1 + κ) * N₀ ^ d₁ := mul_lt_mul_of_pos_right hkey hP0
      _ = (Clo - ε) * ((1 + κ) * N₀ ^ d₁) := by ring
      _ ≤ (C₁ - ε) * N₁ ^ d₁ := mul_le_mul (by linarith) h1 (by positivity) (by linarith)
      _ ≤ V₁ := hV1

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-- The constant `3^D (H_b + 2)^D`. -/
noncomputable def Cst : ℝ := 3 ^ S.Dm * (S.Hb + 1 + 1) ^ S.Dm

theorem Cst_pos : 0 < S.Cst := by have := S.Hb_nonneg; unfold Cst; positivity

/-- **The upper bound at the starting point**. -/
theorem up_bound (m : List (Fin 2)) {dlo : ℕ} {Clo ε η : ℝ}
    (hdeg : ∀ d, dlo < d → S.coef d (S.D.sT m) = 0) (hC : S.coef dlo (S.D.sT m) = Clo) (hdlo : 1 ≤ dlo)
    (hη : 0 ≤ η) (hN : 1 ≤ (fullW S.us [] S.y'' S.z m S.R).length)
    (hI : ∀ i : S.Item, W3a.IterHyp (S.Hb + 1) η (fullW S.us [] S.y'' S.z m S.R).length
      (S.XiHat i (fullW S.us [] S.y'' S.z m S.R)) (S.Qc i))
    (h1 : ∑ d ∈ Finset.range dlo, S.coef d (S.D.sT m) ≤ ε / 2 * (fullW S.us [] S.y'' S.z m S.R).length)
    (h2 : S.Ktot (S.D.sT m) * (S.Cst * (η + 1 / (fullW S.us [] S.y'' S.z m S.R).length)) ≤ ε / 2) :
    (aval B (fullW S.us [] S.y'' S.z m S.R) : ℝ) ≤
      (Clo + ε) * ((fullW S.us [] S.y'' S.z m S.R).length : ℝ) ^ dlo := by
  have hHb := S.Hb_nonneg
  have hup := S.aval_le_of_iterHyp m dlo hdeg (Bv := S.Hb + 1) (by linarith) hη hN hI
  generalize (fullW S.us [] S.y'' S.z m S.R).length = N at hN hup h1 h2 ⊢
  generalize S.D.sT m = s at hdeg hC hup h1 h2
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Finset.sum_range_succ, hC] at hup
  have hlow : ∑ d ∈ Finset.range dlo, S.coef d s * (N : ℝ) ^ d ≤ ε / 2 * (N : ℝ) ^ dlo := by
    calc ∑ d ∈ Finset.range dlo, S.coef d s * (N : ℝ) ^ d
        ≤ ∑ d ∈ Finset.range dlo, S.coef d s * (N : ℝ) ^ (dlo - 1) :=
          Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hNr (by have := Finset.mem_range.mp hd; omega)) (S.coef_nonneg d s))
      _ = (∑ d ∈ Finset.range dlo, S.coef d s) * (N : ℝ) ^ (dlo - 1) := by rw [Finset.sum_mul]
      _ ≤ ε / 2 * N * (N : ℝ) ^ (dlo - 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ε / 2 * (N : ℝ) ^ dlo := by
          rw [mul_assoc, ← pow_succ']; congr 2; omega
  have herr : S.Ktot s * (3 ^ S.Dm * (S.Hb + 1 + 1) ^ S.Dm * (η + 1 / N)) * (N : ℝ) ^ dlo ≤
      ε / 2 * (N : ℝ) ^ dlo := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold Cst at h2; linarith
  linarith

/-- **The lower bound at the end point**. -/
theorem low_bound (m : List (Fin 2)) (d M : ℕ) (hM : 1 ≤ M) {η ε : ℝ} (hη : 0 ≤ η) {N : ℕ} (hN : 1 ≤ N)
    (good : ℕ → Prop) [DecidablePred good]
    (hgood : ∀ p, good p → S.τ.length ≤ p ∧ p + M ≤ S.τ.length + m.length)
    (hI : ∀ i : S.Item, W3a.IterHyp (S.Hb + 1) η N
      (fun p => if good p then (S.XiJ i M (fullW S.us [] S.y'' S.z m S.R) p : ℝ) else 0) (S.QJ i M))
    (hdD : d ≤ S.Dm) (h1 : S.coef d (S.D.sT m) - ε / 3 ≤ S.coefM M d (S.D.sT m))
    (h2 : S.Ktot (S.D.sT m) * (S.Cst * (η + 1 / N)) ≤ ε / 3)
    (h3 : S.Ktot (S.D.sT m) * (S.Dm * ((M - 1 : ℕ) : ℝ) * (max (S.BJ M : ℝ) 1) ^ S.Dm) ≤ ε / 3 * N) :
    (S.coef d (S.D.sT m) - ε) * (N : ℝ) ^ d ≤ (aval B (fullW S.us [] S.y'' S.z m S.R) : ℝ) := by
  have hHb := S.Hb_nonneg
  have hlow := S.aval_ge_of_iterHyp m d M hM (Bv := S.Hb + 1) (B' := S.BJ M) (by linarith) hη
    (Nat.cast_nonneg _) hN good hgood hI (fun i p => by exact_mod_cast S.XiJ_le_BJ i M _ p)
  refine le_trans ?_ hlow
  generalize S.D.sT m = s at h1 h2 h3 ⊢
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 := S.Ktot_nonneg s
  have hPd : (0 : ℝ) ≤ (N : ℝ) ^ d := by positivity
  -- the first error term
  have he := W3a.epsIter_le (B := S.Hb + 1) (η := η) (N := N) (by linarith) hη hN d
  have hpow : (3 : ℝ) ^ d * (S.Hb + 1 + 1) ^ d ≤ S.Cst := by
    unfold Cst
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hdD) (pow_le_pow_right₀ (by linarith) hdD)
      (by positivity) (by positivity)
  have hE1 : S.Ktot s * W3a.epsIter (S.Hb + 1) η N d ≤ ε / 3 := by
    have : W3a.epsIter (S.Hb + 1) η N d ≤ S.Cst * (η + 1 / N) :=
      le_trans he (mul_le_mul_of_nonneg_right hpow (by positivity))
    nlinarith
  -- the second error term
  have hE2 : S.Ktot s * (((d - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * (S.BJ M : ℝ) ^ d * (N : ℝ) ^ (d - 1)) ≤
      ε / 3 * (N : ℝ) ^ d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      simp only [Nat.zero_sub, Nat.cast_zero, zero_mul, mul_zero, pow_zero, mul_one]
      have : 0 ≤ ε / 3 * N := le_trans (by positivity) h3
      nlinarith
    · have hd1 : ((d - 1 : ℕ) : ℝ) ≤ S.Dm := by exact_mod_cast (show d - 1 ≤ S.Dm by omega)
      have hBJ : (S.BJ M : ℝ) ^ d ≤ (max (S.BJ M : ℝ) 1) ^ S.Dm :=
        le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_left _ _) d)
          (pow_le_pow_right₀ (le_max_right _ _) hdD)
      have hM0 : (0 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hX : ((d - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * (S.BJ M : ℝ) ^ d ≤
          S.Dm * ((M - 1 : ℕ) : ℝ) * (max (S.BJ M : ℝ) 1) ^ S.Dm :=
        mul_le_mul (mul_le_mul_of_nonneg_right hd1 hM0) hBJ (by positivity) (by positivity)
      have hY : S.Ktot s * (((d - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * (S.BJ M : ℝ) ^ d) ≤ ε / 3 * N :=
        le_trans (mul_le_mul_of_nonneg_left hX hK0) h3
      have hNd : (N : ℝ) ^ d = N * (N : ℝ) ^ (d - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hNd]
      have hPd1 : (0 : ℝ) ≤ (N : ℝ) ^ (d - 1) := by positivity
      calc S.Ktot s * (((d - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * (S.BJ M : ℝ) ^ d * (N : ℝ) ^ (d - 1))
          = S.Ktot s * (((d - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * (S.BJ M : ℝ) ^ d) * (N : ℝ) ^ (d - 1) := by ring
        _ ≤ ε / 3 * N * (N : ℝ) ^ (d - 1) := mul_le_mul_of_nonneg_right hY hPd1
        _ = _ := by ring
  have h1' : (S.coef d s - ε / 3) * (N : ℝ) ^ d ≤ S.coefM M d s * (N : ℝ) ^ d :=
    mul_le_mul_of_nonneg_right h1 hPd
  have hE1' : S.Ktot s * W3a.epsIter (S.Hb + 1) η N d * (N : ℝ) ^ d ≤ ε / 3 * (N : ℝ) ^ d :=
    mul_le_mul_of_nonneg_right hE1 hPd
  nlinarith

end Setup

end Collatz.Arctic.NatQ5.W3h
