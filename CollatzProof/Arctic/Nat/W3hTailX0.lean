/-
# The tail of detours at the starting point (Proposition 12.26 of the paper)

For the word `τ0^8 · u · ρ · r' · y''(u♯)^R z` of the starting point `x₀`, the sum of the weights of the detours with range above `J` is bounded by the sum on the side of the free bits,
`FreeSum` (small by Markov's inequality over `u`), and the number of groups with `RunMiss` on the side of the Terras part (the event of `gap_twin` of `W3b`).
See Proposition 12.26 and Lemma 12.25 (iii) of the paper.

* `Lr_lin`: the range `R` is bounded linearly in the window length `Lr R` (the hypothesis `R ≤ κ K R + κ'` of `tail_small` and `gap_twin`).
* `sum_cntRun_free_le`, `free_markov`: the average number of windows over the free bits, and Markov's inequality.
* `tail_x0`: the sum of the tail ≤ `FreeSum + 22 g Σ_j Σ_r w(r) [RunMiss j]`.
-/
import CollatzProof.Arctic.Nat.W3hIterHyp

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-- The total length `C₀ = (K - 1) + 2 s'` of the zones of constant length of the word of the starting point (top and `0^8`, `ρ`, shared part). -/
def C0 : ℕ := S.Kc - 1 + 2 * S.s'

/-- The weight `c_P (r+1)^{d_P} (r+1)` of the range `r`. -/
noncomputable def wt (r : ℕ) : ℝ := ((S.D.cP * (r + 1) ^ S.D.dP : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ)

theorem wt_nonneg (r : ℕ) : 0 ≤ S.wt r := by unfold wt; positivity

theorem wt_eq (r : ℕ) : S.wt r = (S.D.cP : ℝ) * ((r : ℝ) + 1) ^ (S.D.dP + 1) := by
  unfold wt; push_cast; ring

/-- The range is bounded linearly in the window length. -/
theorem Lr_lin (C₀ D R : ℕ) (hD : 1 ≤ D) :
    R ≤ 2 * S.cW' * D * (S.Lr C₀ R / D) + S.cW' * (2 * D + C₀ + 3) := by
  have hc := S.cW'_pos
  have h1 : R < S.cW' * (R / S.cW' + 1) := Nat.lt_mul_div_succ R (by omega)
  have h2 : R / S.cW' ≤ S.ell0 R + 1 := by unfold ell0; omega
  have h3 : S.ell0 R ≤ C₀ + 2 * S.Lr C₀ R + 1 := by unfold Lr; omega
  have h4 : S.Lr C₀ R < D * (S.Lr C₀ R / D) + D := by
    have := Nat.lt_mul_div_succ (S.Lr C₀ R) (show 0 < D by omega)
    rw [mul_add, mul_one] at this; exact this
  have h5 : R / S.cW' + 1 ≤ 2 * (D * (S.Lr C₀ R / D)) + (2 * D + C₀ + 3) := by
    generalize D * (S.Lr C₀ R / D) = t at h4 ⊢
    generalize R / S.cW' = x at h2 ⊢
    omega
  calc R ≤ S.cW' * (R / S.cW' + 1) := h1.le
    _ ≤ S.cW' * (2 * (D * (S.Lr C₀ R / D)) + (2 * D + C₀ + 3)) := Nat.mul_le_mul_left _ h5
    _ = _ := by ring

/-! ## The side of the free bits -/

theorem q_nonneg : (0 : ℝ) ≤ 1 - 1 / 2 ^ S.us.length := by
  have : (1 : ℝ) / 2 ^ S.us.length ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  linarith

theorem q_lt_one : (1 : ℝ) - 1 / 2 ^ S.us.length < 1 := by
  have : (0 : ℝ) < 1 / 2 ^ S.us.length := by positivity
  linarith

open Classical in
/-- The sum of the numbers of windows over the free bits. -/
theorem sum_cntRun_free_le (F L : ℕ) :
    ∑ u ∈ Finset.range (2 ^ F), (S.cntRun L ((bitsMSB F u).map W3a.l2f) : ℝ) ≤
      (F + 1) * (2 ^ F * (1 - 1 / 2 ^ S.us.length) ^ (L / S.us.length)) := by
  have hlen : ∀ u, ((bitsMSB F u).map W3a.l2f).length = F := fun u => by
    rw [List.length_map, bitsMSB_length]
  have e : ∀ u, (S.cntRun L ((bitsMSB F u).map W3a.l2f) : ℝ) = ∑ y ∈ Finset.range (F + 1),
      if y + L ≤ F ∧ FreeW S.us y L ((bitsMSB F u).map W3a.l2f) then (1 : ℝ) else 0 := by
    intro u
    unfold cntRun
    rw [hlen u, Finset.sum_boole]
  simp only [e]
  rw [Finset.sum_comm]
  calc ∑ y ∈ Finset.range (F + 1), ∑ u ∈ Finset.range (2 ^ F),
        (if y + L ≤ F ∧ FreeW S.us y L ((bitsMSB F u).map W3a.l2f) then (1 : ℝ) else 0)
      ≤ ∑ _y ∈ Finset.range (F + 1), 2 ^ F * (1 - 1 / 2 ^ S.us.length) ^ (L / S.us.length) := by
        refine Finset.sum_le_sum (fun y _ => ?_)
        by_cases hy : y + L ≤ F
        · simp only [hy, true_and]
          rw [Finset.sum_boole]
          exact card_free_le S.us hy
        · simp only [hy, false_and, ↓reduceIte, Finset.sum_const_zero]
          exact mul_nonneg (by positivity) (pow_nonneg S.q_nonneg _)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

open Classical in
/-- **Markov's inequality**: at most `(ε_F/θ) 2^F` values `u` have a sum `Σ_r w(r) cntRun_{L_r}(u)` on the side of the free bits
above `θ (F + 1)` (if `Σ_r w(r) q^{⌊L_r/|u♯|⌋} ≤ ε_F`). -/
theorem free_markov (F : ℕ) (Rs : Finset ℕ) (Lf : ℕ → ℕ) {εF θ : ℝ} (hθ : 0 < θ)
    (hε : ∑ r ∈ Rs, S.wt r * (1 - 1 / 2 ^ S.us.length) ^ (Lf r / S.us.length) ≤ εF) :
    (((Finset.range (2 ^ F)).filter (fun u => θ * (F + 1) <
        ∑ r ∈ Rs, S.wt r * S.cntRun (Lf r) ((bitsMSB F u).map W3a.l2f))).card : ℝ) ≤ εF / θ * 2 ^ F := by
  set X : ℕ → ℝ := fun u => ∑ r ∈ Rs, S.wt r * S.cntRun (Lf r) ((bitsMSB F u).map W3a.l2f) with hX
  have hX0 : ∀ u, 0 ≤ X u := fun u => Finset.sum_nonneg (fun r _ => mul_nonneg (S.wt_nonneg r) (Nat.cast_nonneg _))
  have hsum : ∑ u ∈ Finset.range (2 ^ F), X u ≤ (F + 1) * 2 ^ F * εF := by
    simp only [hX]
    rw [Finset.sum_comm]
    calc ∑ r ∈ Rs, ∑ u ∈ Finset.range (2 ^ F), S.wt r * (S.cntRun (Lf r) ((bitsMSB F u).map W3a.l2f) : ℝ)
        = ∑ r ∈ Rs, S.wt r * ∑ u ∈ Finset.range (2 ^ F), (S.cntRun (Lf r) ((bitsMSB F u).map W3a.l2f) : ℝ) := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ r ∈ Rs, S.wt r * ((F + 1) * (2 ^ F * (1 - 1 / 2 ^ S.us.length) ^ (Lf r / S.us.length))) :=
          Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (S.sum_cntRun_free_le F (Lf r)) (S.wt_nonneg r))
      _ = (F + 1) * 2 ^ F * ∑ r ∈ Rs, S.wt r * (1 - 1 / 2 ^ S.us.length) ^ (Lf r / S.us.length) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun r _ => ?_); ring
      _ ≤ (F + 1) * 2 ^ F * εF := mul_le_mul_of_nonneg_left hε (by positivity)
  set bad := (Finset.range (2 ^ F)).filter (fun u => θ * (F + 1) < X u)
  have hF1 : (0 : ℝ) < θ * (F + 1) := by positivity
  have h1 : (bad.card : ℝ) * (θ * (F + 1)) ≤ ∑ u ∈ bad, X u := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun u hu => (Finset.mem_filter.mp hu).2.le)
  have h2 : ∑ u ∈ bad, X u ≤ ∑ u ∈ Finset.range (2 ^ F), X u :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun u _ _ => hX0 u)
  have h3 : (bad.card : ℝ) * (θ * (F + 1)) ≤ (F + 1) * 2 ^ F * εF := le_trans h1 (le_trans h2 hsum)
  have hF0 : (0 : ℝ) < F + 1 := by positivity
  have h4 : (bad.card * θ) * (F + 1) ≤ (εF * 2 ^ F) * (F + 1) := by linarith
  have h5 := le_of_mul_le_mul_right h4 hF0
  rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
  linarith

/-! ## The zones of the word of the starting point and the tail -/

/-- Splitting the word of the starting point into zones: `τ0^8 · u · ρ · r' · y''(u♯)^R z`. -/
theorem binWord_x0_split (β' : List Bool) {n u : ℕ} (hKn : S.Kc + S.s' ≤ n) (hu : u < 2 ^ S.Flen n) :
    binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u) =
      (S.τ ++ List.replicate 8 0) ++ (bitsMSB (S.Flen n) u).map W3a.l2f ++
        (bitsMSB S.s' (famRho S.β₀ (S.β₀ ++ β'))).map W3a.l2f ++ TwOf S.β₀ β' ++ (S.y'' ++ S.τ ++ S.z) := by
  rw [S.binWord_x0 β' hKn hu, S.fullW_eq, mid0]
  simp only [List.append_assoc, TwOf, s']

theorem tailLen : (S.y'' ++ S.τ ++ S.z).length = S.s' := by
  rw [← S.tailW_eq, ← S.hy, List.length_map, bitsMSB_length]; rfl

open Classical in
/-- **The tail at the starting point**: the sum of the weights of the detours with range above `J` is bounded by the sum on the side of the free bits and the sum of `RunMiss` on the Terras part. -/
theorem tail_x0 (β' : List Bool) {n u J Nmax n₁ a : ℕ} (KT : ℕ → ℕ) (hKn : S.Kc + S.s' ≤ n)
    (hu : u < 2 ^ S.Flen n) (hg : 1 ≤ n₁ + a)
    (hJ : ∀ r, J < r → 1 ≤ KT r ∧ 11 * (n₁ + a) * (KT r + 2) ≤ S.Lr S.C0 r)
    (hNmax : (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length ≤ Nmax) (i : S.Item) :
    ∑ p ∈ Finset.range (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
      ∑ r ∈ Finset.Ioc J (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
        (S.xiI i r (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) p : ℝ) ≤
      ∑ r ∈ Finset.Ioc J Nmax, S.wt r * S.cntRun (S.Lr S.C0 r) ((bitsMSB (S.Flen n) u).map W3a.l2f) +
      22 * (n₁ + a) * ∑ j ∈ Finset.range (β'.length / (n₁ + a)), ∑ r ∈ Finset.Ioc J Nmax,
        S.wt r * (if W3b.RunMiss (PU S.us) S.β₀.length n₁ a j (KT r) (KT r) (S.β₀ ++ β') then 1 else 0) := by
  have hω := S.binWord_x0_split β' hKn hu
  set X₀ := S.τ ++ List.replicate 8 (0 : Fin 2)
  set Fw := (bitsMSB (S.Flen n) u).map W3a.l2f
  set X₁ := (bitsMSB S.s' (famRho S.β₀ (S.β₀ ++ β'))).map W3a.l2f
  set Tw := TwOf S.β₀ β'
  set X₂ := S.y'' ++ S.τ ++ S.z
  have hC : X₀.length + X₁.length + X₂.length = S.C0 := by
    have h1 : X₀.length = S.Kc - 1 := by simp only [X₀, List.length_append, List.length_replicate, Kc, E]; omega
    have h2 : X₁.length = S.s' := by simp only [X₁, List.length_map, bitsMSB_length]
    have h3 : X₂.length = S.s' := S.tailLen
    unfold C0; omega
  rw [hω] at hNmax ⊢
  have hJ' : ∀ r, J < r → 1 ≤ S.Lr (X₀.length + X₁.length + X₂.length) r := by
    intro r hr; rw [hC]; have := hJ r hr; nlinarith
  refine le_trans (S.tail_sum_le i J X₀ Fw X₁ Tw X₂ hJ') ?_
  rw [hC]
  set ω := X₀ ++ Fw ++ X₁ ++ Tw ++ X₂
  -- for each range, bound the number of windows on the Terras side by the number of `RunMiss`
  have hT : ∀ r ∈ Finset.Ioc J ω.length, (S.cntRun (S.Lr S.C0 r) Tw : ℝ) ≤
      22 * (n₁ + a) * ∑ j ∈ Finset.range (β'.length / (n₁ + a)),
        (if W3b.RunMiss (PU S.us) S.β₀.length n₁ a j (KT r) (KT r) (S.β₀ ++ β') then (1 : ℝ) else 0) := by
    intro r hr
    obtain ⟨hK1, hL⟩ := hJ r (Finset.mem_Ioc.mp hr).1
    have h := card_run_le_runMiss S.us S.β₀ β' n₁ a hg hK1 hL
    rw [Finset.sum_boole]
    unfold cntRun
    exact_mod_cast h
  have hstep : ∑ r ∈ Finset.Ioc J ω.length,
      ((S.D.cP * (r + 1) ^ S.D.dP : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) *
        ((S.cntRun (S.Lr S.C0 r) Fw : ℝ) + (S.cntRun (S.Lr S.C0 r) Tw : ℝ)) ≤
      ∑ r ∈ Finset.Ioc J ω.length, (S.wt r * S.cntRun (S.Lr S.C0 r) Fw +
        22 * (n₁ + a) * ∑ j ∈ Finset.range (β'.length / (n₁ + a)),
          S.wt r * (if W3b.RunMiss (PU S.us) S.β₀.length n₁ a j (KT r) (KT r) (S.β₀ ++ β') then 1 else 0)) := by
    refine Finset.sum_le_sum (fun r hr => ?_)
    have := mul_le_mul_of_nonneg_left (hT r hr) (S.wt_nonneg r)
    have e : S.wt r * (22 * (n₁ + a) * ∑ j ∈ Finset.range (β'.length / (n₁ + a)),
        (if W3b.RunMiss (PU S.us) S.β₀.length n₁ a j (KT r) (KT r) (S.β₀ ++ β') then (1 : ℝ) else 0)) =
        22 * (n₁ + a) * ∑ j ∈ Finset.range (β'.length / (n₁ + a)),
          S.wt r * (if W3b.RunMiss (PU S.us) S.β₀.length n₁ a j (KT r) (KT r) (S.β₀ ++ β') then 1 else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
    unfold wt at this e ⊢
    nlinarith
  refine le_trans hstep ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  have hsub : Finset.Ioc J ω.length ⊆ Finset.Ioc J Nmax := Finset.Ioc_subset_Ioc_right hNmax
  have hg0 : (0 : ℝ) ≤ 22 * (n₁ + a) := by positivity
  refine add_le_add (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun r _ _ => mul_nonneg (S.wt_nonneg r) (Nat.cast_nonneg _))) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun r _ _ => mul_nonneg (S.wt_nonneg r) (by split_ifs <;> norm_num)))) hg0

end Setup

end Collatz.Arctic.NatQ5.W3h
