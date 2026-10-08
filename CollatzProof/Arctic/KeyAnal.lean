/-
Analytic ingredients of the swap argument (Appendix B.2), part 1: the `L²` identity (Q1) and
the passage from intervals to cells (Q3), `SpecCells` (both used for Proposition B.6 and Theorem B.7).

* `ka_sum_zmod`, `ka_sum_blocks`, `ka_sum_periodic`: sums over `ZMod n` and over `range`, sums split into pieces, sums of periodic sequences.
* `kaKappa`: `k_λ(δ) = #{(y, y') ∈ [0, λ)² : y + δ = y'}` (counted with multiplicity; for `λ ≤ 2^V` this is the paper's `#(J_λ ∩ (J_λ - δ))`).
* `ka_sumF`, `ka_sumF2`, `ka_keyQ_eq`, `ka_keyQ_shift`: (Q1) (`Σ_x F = λ`,
  `Q_λ = Σ_{z,z'} μ(z)μ(z')k_λ(z' - z) - λ²/2^V`, `Q_λ` is invariant under translations).
* `specCells`: (Q3). Average `F(· - s)` over `X_u + s = {uh, …, uh + s} ⊆ C_u`, and use `y ≤ y²/(2t) + t/2` and
  the fact that the sum of the positive parts is half the sum of the absolute values (`Σ_u (μ(C_u) - 2^{-ℓ}) = 0`).
-/
import CollatzProof.Arctic.KeySpec

namespace Collatz.Arctic

open Finset

/-! ## Rewriting sums -/

/-- A sum over `ZMod n` is a sum over `range n`. -/
theorem ka_sum_zmod {M : Type*} [AddCommMonoid M] (n : ℕ) [NeZero n] (f : ZMod n → M) :
    ∑ t ∈ range n, f (t : ZMod n) = ∑ x, f x := by
  apply Finset.sum_nbij' (fun t : ℕ => (t : ZMod n)) (fun x : ZMod n => x.val)
  · intro t _; exact mem_univ _
  · intro x _; simp [ZMod.val_lt]
  · intro t ht; rw [mem_range] at ht; exact ZMod.val_cast_of_lt ht
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro t _; rfl

/-- Split a sum of length `q b` into `q` pieces of length `b`. -/
theorem ka_sum_blocks {M : Type*} [AddCommMonoid M] (b q : ℕ) (f : ℕ → M) :
    ∑ n ∈ range (q * b), f n = ∑ u ∈ range q, ∑ y ∈ range b, f (u * b + y) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

/-- The sum of length `q m` of a sequence of period `m`. -/
theorem ka_sum_periodic {M : Type*} [AddCommMonoid M] (m q : ℕ) (g : ℕ → M)
    (hg : ∀ t, g (t + m) = g t) :
    ∑ t ∈ range (q * m), g t = q • ∑ t ∈ range m, g t := by
  have h : ∀ u y, g (u * m + y) = g y := by
    intro u
    induction u with
    | zero => intro y; simp
    | succ u ih => intro y; rw [show (u + 1) * m + y = (u * m + y) + m by ring, hg, ih]
  rw [ka_sum_blocks, sum_congr rfl (fun u _ => sum_congr rfl (fun y _ => h u y)), sum_const,
    card_range]

/-- The sum over the cells is the total sum (`ℓ ≤ V`). -/
theorem ka_cells_sum (V ℓ : ℕ) (hℓ : ℓ ≤ V) (f : ZMod (2 ^ V) → ℝ) :
    ∑ u ∈ range (2 ^ ℓ), ∑ y ∈ range (2 ^ (V - ℓ)), f ((u * 2 ^ (V - ℓ) + y : ℕ) : ZMod (2 ^ V)) =
      ∑ x, f x := by
  rw [← ka_sum_blocks (2 ^ (V - ℓ)) (2 ^ ℓ) (fun n => f (n : ZMod (2 ^ V))), ← pow_add,
    Nat.add_sub_cancel' hℓ, ka_sum_zmod]

/-! ## (Q1) -/

/-- `k_λ(δ) = #{(y, y') ∈ [0, λ)² : y + δ = y'}` (with multiplicity). -/
noncomputable def kaKappa (V lam : ℕ) (δ : ZMod (2 ^ V)) : ℝ :=
  ∑ y ∈ range lam, ∑ y' ∈ range lam, if (y : ZMod (2 ^ V)) + δ = y' then (1 : ℝ) else 0

/-- `Σ_x F_μ(x) = λ Σ_x μ(x)`. -/
theorem ka_sumF (V lam : ℕ) (μ : ZMod (2 ^ V) → ℝ) :
    ∑ x, keyF V lam μ x = lam * ∑ x, μ x := by
  unfold keyF
  rw [Finset.sum_comm]
  have : ∀ y ∈ range lam, ∑ x : ZMod (2 ^ V), μ (x + (y : ZMod (2 ^ V))) = ∑ x, μ x := by
    intro y _
    exact Fintype.sum_equiv (Equiv.addRight (y : ZMod (2 ^ V))) _ _ (fun x => rfl)
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]

/-- `Σ_x F_μ(x)² = Σ_{z,z'} μ(z)μ(z')k_λ(z' - z)`. -/
theorem ka_sumF2 (V lam : ℕ) (μ : ZMod (2 ^ V) → ℝ) :
    ∑ x, keyF V lam μ x ^ 2 = ∑ z, ∑ z', μ z * μ z' * kaKappa V lam (z' - z) := by
  -- rewrite both sides as `Σ_{y,y'} Σ_z μ(z) μ(z - y + y')`.
  have L : ∑ x, keyF V lam μ x ^ 2 = ∑ y ∈ range lam, ∑ y' ∈ range lam,
      ∑ z, μ z * μ (z - (y : ZMod (2 ^ V)) + y') := by
    simp only [keyF, sq, sum_mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_comm]
    refine sum_congr rfl (fun y' _ => ?_)
    exact Fintype.sum_equiv (Equiv.addRight (y : ZMod (2 ^ V))) _ _
      (fun x => by simp only [Equiv.coe_addRight, add_sub_cancel_right])
  have R : ∑ z, ∑ z', μ z * μ z' * kaKappa V lam (z' - z) = ∑ y ∈ range lam, ∑ y' ∈ range lam,
      ∑ z, μ z * μ (z - (y : ZMod (2 ^ V)) + y') := by
    have inner : ∀ z : ZMod (2 ^ V), ∀ y y' : ℕ,
        ∑ z', μ z * μ z' * (if (y : ZMod (2 ^ V)) + (z' - z) = y' then (1 : ℝ) else 0) =
          μ z * μ (z - y + y') := by
      intro z y y'
      have e : ∀ z' : ZMod (2 ^ V), ((y : ZMod (2 ^ V)) + (z' - z) = y') ↔ (z - y + y' = z') := by
        intro z'
        constructor <;> intro h <;> [rw [← h]; rw [← h]] <;> ring
      simp only [mul_ite, mul_one, mul_zero, e, sum_ite_eq, mem_univ, ite_true]
    calc ∑ z, ∑ z', μ z * μ z' * kaKappa V lam (z' - z)
        = ∑ z, ∑ y ∈ range lam, ∑ y' ∈ range lam, μ z * μ (z - (y : ZMod (2 ^ V)) + y') := by
          refine sum_congr rfl (fun z _ => ?_)
          simp only [kaKappa, mul_sum]
          rw [Finset.sum_comm]
          refine sum_congr rfl (fun y _ => ?_)
          rw [Finset.sum_comm]
          exact sum_congr rfl (fun y' _ => inner z y y')
      _ = ∑ y ∈ range lam, ∑ z, ∑ y' ∈ range lam, μ z * μ (z - (y : ZMod (2 ^ V)) + y') :=
          Finset.sum_comm
      _ = _ := sum_congr rfl (fun y _ => Finset.sum_comm)
  rw [L, R]

/-- `Q_λ(μ) = Σ_x F_μ(x)² - λ²/2^V` (`Σ μ = 1`). -/
theorem ka_keyQ_sq (V lam : ℕ) (μ : ZMod (2 ^ V) → ℝ) (hμ : ∑ x, μ x = 1) :
    keyQ V lam μ = ∑ x, keyF V lam μ x ^ 2 - (lam : ℝ) ^ 2 / 2 ^ V := by
  have hF := ka_sumF V lam μ
  rw [hμ, mul_one] at hF
  unfold keyQ
  have e : ∀ x, (keyF V lam μ x - lam / 2 ^ V) ^ 2
      = keyF V lam μ x ^ 2 - 2 * ((lam : ℝ) / 2 ^ V) * keyF V lam μ x + ((lam : ℝ) / 2 ^ V) ^ 2 := by
    intro x; ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hF, sum_const, card_univ, ZMod.card,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring

/-- (Q1): `Q_λ(μ) = Σ_{z,z'} μ(z)μ(z')k_λ(z' - z) - λ²/2^V` (`Σ μ = 1`). -/
theorem ka_keyQ_eq (V lam : ℕ) (μ : ZMod (2 ^ V) → ℝ) (hμ : ∑ x, μ x = 1) :
    keyQ V lam μ = ∑ z, ∑ z', μ z * μ z' * kaKappa V lam (z' - z) - (lam : ℝ) ^ 2 / 2 ^ V := by
  rw [ka_keyQ_sq V lam μ hμ, ka_sumF2]

/-- (Q1): `Q_λ` does not change under translations of `μ`. -/
theorem ka_keyQ_shift (V lam : ℕ) (μ : ZMod (2 ^ V) → ℝ) (a : ZMod (2 ^ V)) :
    keyQ V lam (fun x => μ (x + a)) = keyQ V lam μ := by
  unfold keyQ
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ (fun x => ?_)
  simp only [keyF, Equiv.coe_addRight]
  congr 2
  refine sum_congr rfl (fun y _ => ?_)
  congr 1
  ring

/-! ## (Q3) (`SpecCells`) -/

lemma ka_abs_eq (a : ℝ) : |a| = 2 * max a 0 - a := by
  rcases le_total a 0 with h | h
  · rw [abs_of_nonpos h, max_eq_right h]; ring
  · rw [abs_of_nonneg h, max_eq_left h]; ring

lemma ka_amgm (y t : ℝ) (ht : 0 < t) : y ≤ y ^ 2 / (2 * t) + t / 2 := by
  have e : y ^ 2 / (2 * t) + t / 2 - y = (y - t) ^ 2 / (2 * t) := by
    field_simp; ring
  have : 0 ≤ (y - t) ^ 2 / (2 * t) := div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- Lower bound by cells: if `i ≤ s`, then `μ(C_u) ≤ F_μ(uh + i - s)` (`λ = h + s`, `μ ≥ 0`). -/
lemma ka_cell_le (V lam h s u i : ℕ) (μ : ZMod (2 ^ V) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hlam : lam = h + s) (hi : i ≤ s) :
    ∑ y ∈ range h, μ ((u * h + y : ℕ) : ZMod (2 ^ V)) ≤
      keyF V lam μ (((u * h + i : ℕ) : ZMod (2 ^ V)) - (s : ZMod (2 ^ V))) := by
  unfold keyF
  have sub : Ico (s - i) (s - i + h) ⊆ range lam := by
    intro y hy
    rw [mem_Ico] at hy
    rw [mem_range]
    omega
  calc ∑ y ∈ range h, μ ((u * h + y : ℕ) : ZMod (2 ^ V))
      = ∑ y ∈ Ico (s - i) (s - i + h),
          μ (((u * h + i : ℕ) : ZMod (2 ^ V)) - (s : ZMod (2 ^ V)) + (y : ZMod (2 ^ V))) := by
        rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
        refine sum_congr rfl (fun y _ => ?_)
        congr 1
        push_cast [Nat.cast_sub hi]
        ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun y _ _ => hμ0 _)

theorem specCells : SpecCells := by
  intro V ℓ d hℓ hd hV μ hμ0 hμ1 t ht
  -- notation: `h = 2^{V-ℓ}`, `s = 2^{V-ℓ-d}`, `λ = h + s`.
  have hsh : 2 ^ (V - ℓ - d) + 1 ≤ 2 ^ (V - ℓ) := by
    have : 2 ^ (V - ℓ - d) < 2 ^ (V - ℓ) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hR1 : (2 : ℝ) ^ (V - ℓ) * 2 ^ ℓ = 2 ^ V := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hR2 : (2 : ℝ) ^ (V - ℓ - d) * 2 ^ ℓ * 2 ^ d = 2 ^ V := by
    rw [← pow_add, ← pow_add, show V - ℓ - d + ℓ + d = V by omega]
  set lam : ℕ := 2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) with hlam
  set sR : ℝ := (2 : ℝ) ^ (V - ℓ - d) with hsR
  -- `g(x) = (F(x - s) - λ/2^V)²`, `Σ_x g = Q`.
  set g : ZMod (2 ^ V) → ℝ := fun x =>
    (keyF V lam μ (x - ((2 ^ (V - ℓ - d) : ℕ) : ZMod (2 ^ V))) - (lam : ℝ) / 2 ^ V) ^ 2 with hg
  have hgQ : ∑ x, g x = keyQ V lam μ := by
    unfold keyQ
    exact Fintype.sum_equiv (Equiv.subRight ((2 ^ (V - ℓ - d) : ℕ) : ZMod (2 ^ V))) _ _
      (fun x => rfl)
  have hg0 : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  -- `a_u = μ(C_u) - 2^{-ℓ}`.
  set a : ℕ → ℝ := fun u => keyCell V ℓ μ u - 1 / 2 ^ ℓ with ha
  have hsum_a : ∑ u ∈ range (2 ^ ℓ), a u = 0 := by
    simp only [ha, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    have : ∑ u ∈ range (2 ^ ℓ), keyCell V ℓ μ u = 1 := by
      unfold keyCell
      rw [ka_cells_sum V ℓ (by omega) μ, hμ1]
    rw [this]
    push_cast
    field_simp
    ring
  -- bound for each `u`: `max(a_u, 0) ≤ s/2^V + t/2 + Σ_{i ≤ s} g(uh + i) / (2t(s+1))`.
  have hlamR : ((lam : ℕ) : ℝ) / 2 ^ V - 1 / 2 ^ ℓ = sR / 2 ^ V := by
    rw [hlam, hsR]
    push_cast
    rw [← hR1]
    field_simp
    ring
  have hu : ∀ u, max (a u) 0 ≤ sR / 2 ^ V + t / 2 +
      (∑ i ∈ range (2 ^ (V - ℓ - d) + 1), g ((u * 2 ^ (V - ℓ) + i : ℕ) : ZMod (2 ^ V))) /
        (2 * t * (sR + 1)) := by
    intro u
    have hi : ∀ i ∈ range (2 ^ (V - ℓ - d) + 1), a u ≤
        g ((u * 2 ^ (V - ℓ) + i : ℕ) : ZMod (2 ^ V)) / (2 * t) + t / 2 + sR / 2 ^ V := by
      intro i hi
      rw [mem_range] at hi
      have hc := ka_cell_le V lam (2 ^ (V - ℓ)) (2 ^ (V - ℓ - d)) u i μ hμ0 rfl (by omega)
      have hm := ka_amgm (keyF V lam μ (((u * 2 ^ (V - ℓ) + i : ℕ) : ZMod (2 ^ V)) -
        ((2 ^ (V - ℓ - d) : ℕ) : ZMod (2 ^ V))) - (lam : ℝ) / 2 ^ V) t ht
      simp only [ha, keyCell, hg]
      linarith only [hc, hm, hlamR]
    have hsum := sum_le_sum hi
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, card_range, ← sum_div,
      nsmul_eq_mul, nsmul_eq_mul, sum_const, card_range, nsmul_eq_mul] at hsum
    have hs1 : (0 : ℝ) < sR + 1 := by positivity
    have hcast : ((2 ^ (V - ℓ - d) + 1 : ℕ) : ℝ) = sR + 1 := by rw [hsR]; push_cast; ring
    rw [hcast] at hsum
    have hR0 : 0 ≤ sR / 2 ^ V + t / 2 +
        (∑ i ∈ range (2 ^ (V - ℓ - d) + 1), g ((u * 2 ^ (V - ℓ) + i : ℕ) : ZMod (2 ^ V))) /
          (2 * t * (sR + 1)) := by positivity
    refine max_le ?_ hR0
    set S := ∑ i ∈ range (2 ^ (V - ℓ - d) + 1), g ((u * 2 ^ (V - ℓ) + i : ℕ) : ZMod (2 ^ V))
    have e : (sR / 2 ^ V + t / 2 + S / (2 * t * (sR + 1))) * (sR + 1)
        = S / (2 * t) + (sR + 1) * (t / 2) + (sR + 1) * (sR / 2 ^ V) := by
      field_simp
      ring
    have key : a u * (sR + 1) ≤ (sR / 2 ^ V + t / 2 + S / (2 * t * (sR + 1))) * (sR + 1) := by
      rw [e]
      linarith only [hsum]
    exact le_of_mul_le_mul_right key hs1
  -- take the sum.
  set S : ℕ → ℝ := fun u =>
    ∑ i ∈ range (2 ^ (V - ℓ - d) + 1), g ((u * 2 ^ (V - ℓ) + i : ℕ) : ZMod (2 ^ V)) with hS
  have h1 : ∑ u ∈ range (2 ^ ℓ), |a u| = 2 * ∑ u ∈ range (2 ^ ℓ), max (a u) 0 := by
    rw [sum_congr rfl (fun u _ => ka_abs_eq (a u)), sum_sub_distrib, ← mul_sum, hsum_a, sub_zero]
  have h2 := sum_le_sum (fun u (_ : u ∈ range (2 ^ ℓ)) => hu u)
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div] at h2
  have h3 : ∑ u ∈ range (2 ^ ℓ), S u ≤ keyQ V lam μ := by
    rw [← hgQ, ← ka_cells_sum V ℓ (by omega) g]
    refine sum_le_sum (fun u _ => sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hg0 _))
    intro i
    simp only [mem_range]
    omega
  have h4 : (2 : ℝ) ^ ℓ * (sR / 2 ^ V) = 1 / 2 ^ d := by
    rw [← hR2, hsR]
    field_simp
  have hpos : (0 : ℝ) < t * (sR + 1) := by positivity
  have h5 : (∑ u ∈ range (2 ^ ℓ), S u) / (t * (sR + 1)) ≤ keyQ V lam μ / (t * (sR + 1)) :=
    div_le_div_of_nonneg_right h3 hpos.le
  have h6 : 2 * ((∑ u ∈ range (2 ^ ℓ), S u) / (2 * t * (sR + 1)))
      = (∑ u ∈ range (2 ^ ℓ), S u) / (t * (sR + 1)) := by
    field_simp
  have h7 : 2 * ((2 : ℝ) ^ ℓ * (sR / 2 ^ V + t / 2)) = 2 / 2 ^ d + 2 ^ ℓ * t := by
    rw [mul_add, h4]
    ring
  show ∑ u ∈ range (2 ^ ℓ), |a u| ≤ _
  rw [h1]
  have h2' : ∑ u ∈ range (2 ^ ℓ), max (a u) 0 ≤ (2 : ℝ) ^ ℓ * (sR / 2 ^ V + t / 2) +
      (∑ u ∈ range (2 ^ ℓ), S u) / (2 * t * (sR + 1)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    exact h2
  have : (2 : ℝ) * ∑ u ∈ range (2 ^ ℓ), max (a u) 0 ≤ 2 / 2 ^ d + 2 ^ ℓ * t +
      (∑ u ∈ range (2 ^ ℓ), S u) / (t * (sR + 1)) := by
    rw [← h7, ← h6]
    linarith only [h2']
  linarith only [this, h5]

end Collatz.Arctic
