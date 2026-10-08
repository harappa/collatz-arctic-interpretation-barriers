/-
# Lemma D.3 and the uniform lower bound

The parts of the theorem on rigid pairs that Appendix D and Section 11 actually use, proved **without extremal norms and without Fekete's lemma**.

* **Uniform lower bound** (`uniform_lower`): for a strongly connected rigid pair there is `c > 0` with `‖E_x‖ ≥ c`
  for **all words** `x` (equivalently `‖D_x‖ ≥ c g^{|x|}`; Lemma D.3).
* **Survivability** (`Dx_ne_zero`): `D_x ≠ 0` and `‖D_x‖ ≥ 1` for all words.

Pattern of the proof (`block_lower`, the abstract form): for a submultiplicative quantity `φ ≤ C` and `ψ` with `ψ(x) ≤ A g^{|x|} φ(x)`,
if the averages of `log⁺ ψ` grow like `log g`, then `C φ(y) ≥ 1` for all words. If some word `y` has `Cφ(y) < 1`, then on words made of
segments of length `κ` with a power `z` of `y`, `φ` decreases exponentially in "the number of segments equal to `z`", and the average number of such segments is `m 2^{-κ}` (only linearity,
no concentration estimate is needed), so the growth of the averages drops to `log g + (log θ)/(κ 2^κ) < log g`, a contradiction.
This is the mechanism of an earlier argument (Fekete's lemma applied to a subadditive sequence `α_n ≤ 0` for an extremal norm `𝒩`), run with
`‖·‖` and a constant `C` instead of `𝒩`. With `𝒩` the constant becomes 1 and one gets "`‖E_x‖_𝒩 = 1` for all words", but the rest of Appendix D
only uses `inf_x ‖E_x‖ > 0` (see §2 of `RigidIdem.lean`).

Changing the norm in `Λ⁺` (`posLog_avg_tendsto_iff`): the averages of `log⁺` of two quantities that agree up to constant factors have the same limit growth.
Rigidity for the maximal-row-sum norm `rowSum` and rigidity for `nrm` are equivalent (`isRigid_iff_rowSum`).
Rigidity is equivalent to a uniform lower bound, which involves no limit (`rigidAt_iff_uniform_lower`).
-/
import CollatzProof.Arctic.Nat.RigidBound

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix Filter Topology

set_option linter.unusedSectionVars false

/-! ## §1 The abstract form -/

section Abstract

variable {φ ψ : List (Fin 2) → ℝ} {A C g : ℝ}

/-- The word `y` repeated `j` times. -/
def rep (y : List (Fin 2)) (j : ℕ) : List (Fin 2) := (List.replicate j y).flatten

theorem rep_length (y : List (Fin 2)) (j : ℕ) : (rep y j).length = j * y.length := by
  induction j with
  | zero => simp [rep]
  | succ j ih =>
    simp only [rep, List.replicate_succ, List.flatten_cons, List.length_append] at ih ⊢
    rw [ih]; ring

theorem phi_rep_le (hφ0 : ∀ x, 0 ≤ φ x) (hφmul : ∀ x y, φ (x ++ y) ≤ φ x * φ y)
    (y : List (Fin 2)) (j : ℕ) : φ (rep y (j + 1)) ≤ φ y ^ (j + 1) := by
  induction j with
  | zero => simp [rep]
  | succ j ih =>
    have e : rep y (j + 1 + 1) = y ++ rep y (j + 1) := by
      simp [rep, List.replicate_succ]
    rw [e, pow_succ']
    exact (hφmul _ _).trans (mul_le_mul_of_nonneg_left ih (hφ0 y))

/-- The bound over segments: `φ(u ++ b₁ ⋯ b_m) ≤ C θ^{#\{i : b_i = z\}}`. -/
theorem phi_blocks_le (hφ0 : ∀ x, 0 ≤ φ x) (hφmul : ∀ x y, φ (x ++ y) ≤ φ x * φ y)
    (hφC : ∀ x, φ x ≤ C) {z : List (Fin 2)} {θ : ℝ} (hθ0 : 0 ≤ θ) (hz : C * φ z ≤ θ) :
    ∀ (bs : List (List (Fin 2))) (u : List (Fin 2)), φ (u ++ bs.flatten) ≤ C * θ ^ (bs.count z) := by
  intro bs
  induction bs with
  | nil => intro u; simpa using hφC u
  | cons b bs ih =>
    intro u
    rw [List.flatten_cons, List.count_cons]
    by_cases hb : b = z
    · subst hb
      have h1 : φ (u ++ (b ++ bs.flatten)) ≤ φ u * φ b * φ bs.flatten := by
        rw [← List.append_assoc]
        refine (hφmul _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (hφmul _ _) (hφ0 _)
      have h2 : φ bs.flatten ≤ C * θ ^ (bs.count b) := by simpa using ih []
      simp only [beq_self_eq_true, ite_true]
      calc φ (u ++ (b ++ bs.flatten)) ≤ φ u * φ b * φ bs.flatten := h1
        _ = φ u * (φ b * φ bs.flatten) := by ring
        _ ≤ C * (φ b * (C * θ ^ (bs.count b))) := by
            refine mul_le_mul (hφC u) ?_ (mul_nonneg (hφ0 _) (hφ0 _)) ?_
            · exact mul_le_mul_of_nonneg_left h2 (hφ0 _)
            · exact (hφ0 u).trans (hφC u)
        _ = (C * φ b) * (C * θ ^ (bs.count b)) := by ring
        _ ≤ θ * (C * θ ^ (bs.count b)) := by
            refine mul_le_mul_of_nonneg_right hz ?_
            exact mul_nonneg ((hφ0 u).trans (hφC u)) (pow_nonneg hθ0 _)
        _ = C * θ ^ (bs.count b + 1) := by ring
    · have hb' : (b == z) = false := by simpa using hb
      rw [hb']
      simp only [Bool.false_eq_true, ite_false, add_zero]
      rw [← List.append_assoc]
      exact ih (u ++ b)

/-- **The abstract form**: if `φ ≥ 0` is submultiplicative with `φ ≤ C` (`C ≥ 1`), `0 ≤ ψ(x) ≤ A g^{|x|} φ(x)` (`A ≥ 1`, `g > 1`), and
`(1/n) 2^{-n} Σ_{|x|=n} log⁺ ψ(x) → log g`, then `C φ(y) ≥ 1` for all words. -/
theorem block_lower (hφ0 : ∀ x, 0 ≤ φ x) (hφmul : ∀ x y, φ (x ++ y) ≤ φ x * φ y)
    (hφC : ∀ x, φ x ≤ C) (hC : 1 ≤ C) (hA : 1 ≤ A) (hg : 1 < g)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψ : ∀ x, ψ x ≤ A * g ^ x.length * φ x)
    (hT : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (ψ x)) / n) atTop
      (𝓝 (Real.log g))) :
    ∀ y, 1 ≤ C * φ y := by
  -- A non-empty word `y` with `C φ(y) < 1` gives a contradiction.
  have key : ∀ y : List (Fin 2), y ≠ [] → C * φ y < 1 → False := by
    intro y hyne hy
    have hC0 : 0 < C := by linarith
    have hφy1 : φ y ≤ 1 := by nlinarith [hφ0 y]
    -- `j ≥ 1` with `g^{|y| j} ≥ 2`
    have hgl : 1 < g ^ y.length := one_lt_pow₀ hg (by simpa [List.length_eq_zero_iff] using hyne)
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (2 : ℝ) hgl
    have hj0 : j ≠ 0 := by rintro rfl; norm_num at hj
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    set z := rep y (j' + 1) with hzdef
    set κ := z.length with hκdef
    have hκ : κ = (j' + 1) * y.length := rep_length y _
    have hκpos : 0 < κ := by
      rw [hκ]; exact Nat.mul_pos (Nat.succ_pos _) (List.length_pos_iff.mpr hyne)
    have hgκ : 2 ≤ g ^ κ := by
      rw [hκ, mul_comm, pow_mul]; exact hj.le
    have hφz : C * φ z < 1 := by
      have h1 : φ z ≤ φ y := (phi_rep_le hφ0 hφmul y j').trans
        (pow_le_of_le_one (hφ0 y) hφy1 (Nat.succ_ne_zero _))
      calc C * φ z ≤ C * φ y := mul_le_mul_of_nonneg_left h1 hC0.le
        _ < 1 := hy
    set θ := max (C * φ z) (1 / 2) with hθdef
    have hθ1 : θ < 1 := max_lt hφz (by norm_num)
    have hθh : 1 / 2 ≤ θ := le_max_right _ _
    have hθ0 : 0 < θ := by linarith
    have hzθ : C * φ z ≤ θ := le_max_left _ _
    -- The bound at each point for a valid sequence
    have hpt : ∀ (m : ℕ) (bs : List (List (Fin 2))), Valid κ m bs →
        Real.posLog (ψ bs.flatten) ≤
          (Real.log A + Real.log C + (m * κ : ℕ) * Real.log g) + Real.log θ * (bs.count z : ℝ) := by
      intro m bs hbs
      have hlen : bs.flatten.length = m * κ := hbs.flatten_length
      have hcnt : bs.count z ≤ m := hbs.1 ▸ List.count_le_length
      have hb1 : φ bs.flatten ≤ C * θ ^ (bs.count z) := by
        simpa using phi_blocks_le hφ0 hφmul hφC hθ0.le hzθ bs []
      set X := A * g ^ (m * κ) * (C * θ ^ (bs.count z)) with hX
      have hψX : ψ bs.flatten ≤ X := by
        refine (hψ _).trans ?_
        rw [hlen]
        exact mul_le_mul_of_nonneg_left hb1 (mul_nonneg (by linarith) (pow_nonneg (by linarith) _))
      have hX1 : 1 ≤ X := by
        have h1 : 1 ≤ g ^ κ * θ := by nlinarith
        have h2 : θ ^ m ≤ θ ^ (bs.count z) := pow_le_pow_of_le_one hθ0.le hθ1.le hcnt
        have h3 : 1 ≤ g ^ (m * κ) * θ ^ (bs.count z) := by
          calc (1 : ℝ) ≤ (g ^ κ * θ) ^ m := one_le_pow₀ h1
            _ = g ^ (m * κ) * θ ^ m := by rw [mul_pow, ← pow_mul, mul_comm κ m]
            _ ≤ g ^ (m * κ) * θ ^ (bs.count z) :=
                mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _)
        calc (1 : ℝ) ≤ A * C * (g ^ (m * κ) * θ ^ (bs.count z)) := by
              have : 1 ≤ A * C := one_le_mul_of_one_le_of_one_le hA hC
              nlinarith
          _ = X := by rw [hX]; ring
      have hXpos : 0 < X := by linarith
      have hlogX : Real.log X = Real.log A + Real.log C + (m * κ : ℕ) * Real.log g +
          Real.log θ * (bs.count z : ℝ) := by
        have hA0 : 0 < A := by linarith
        have hg0 : 0 < g := by linarith
        rw [hX, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        ring
      calc Real.posLog (ψ bs.flatten) ≤ Real.posLog X :=
            Real.posLog_le_posLog (by linarith [hψ0 bs.flatten]) hψX
        _ = Real.log X := Real.posLog_eq_log (by rw [abs_of_pos hXpos]; exact hX1)
        _ = _ := hlogX
    -- Upper bound for the average
    have havg : ∀ m : ℕ, 1 ≤ m →
        (2 ^ (m * κ) : ℝ)⁻¹ * wsum (m * κ) (fun x => Real.posLog (ψ x)) / ((m * κ : ℕ) : ℝ) ≤
          Real.log g + (Real.log A + Real.log C) / κ / m + Real.log θ / (κ * 2 ^ κ) := by
      intro m hm
      have hsum : wsum (m * κ) (fun x => Real.posLog (ψ x)) ≤
          2 ^ (m * κ) * ((Real.log A + Real.log C + (m * κ : ℕ) * Real.log g) +
            Real.log θ * m / 2 ^ κ) := by
        rw [wsum_mul_eq_bsum]
        refine (bsum_mono fun bs hbs => hpt m bs hbs).trans (le_of_eq ?_)
        exact bsum_affine_count κ z rfl _ _ m
      have h2pos : (0 : ℝ) < 2 ^ (m * κ) := by positivity
      have hmκ : (0 : ℝ) < ((m * κ : ℕ) : ℝ) := by
        have : 0 < m * κ := Nat.mul_pos hm hκpos
        exact_mod_cast this
      rw [div_le_iff₀ hmκ, inv_mul_le_iff₀ h2pos]
      refine hsum.trans (le_of_eq ?_)
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
      have hκ0 : (κ : ℝ) ≠ 0 := by exact_mod_cast hκpos.ne'
      have h2κ : (2 : ℝ) ^ κ ≠ 0 := pow_ne_zero _ two_ne_zero
      push_cast
      field_simp
      ring
    -- Compare in the limit
    have hsub : Tendsto (fun m : ℕ => m * κ) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b, fun m hm => hm.trans (Nat.le_mul_of_pos_right _ hκpos)⟩
    have hL := hT.comp hsub
    have hR : Tendsto (fun m : ℕ => Real.log g + (Real.log A + Real.log C) / κ / m +
        Real.log θ / (κ * 2 ^ κ)) atTop (𝓝 (Real.log g + 0 + Real.log θ / (κ * 2 ^ κ))) :=
      ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)).add tendsto_const_nhds)
    have hle := le_of_tendsto_of_tendsto hL hR
      (eventually_atTop.mpr ⟨1, fun m hm => havg m hm⟩)
    have hneg : Real.log θ / (κ * 2 ^ κ) < 0 :=
      div_neg_of_neg_of_pos (Real.log_neg hθ0 hθ1) (by positivity)
    linarith
  intro y
  by_contra hy
  push Not at hy
  rcases eq_or_ne y [] with rfl | hyne
  · -- If `y = []`, then `φ ≡ 0`, a contradiction for `[0]`.
    have hφ1 : φ [] < 1 := by nlinarith [hφ0 []]
    have h0 : φ [0] = 0 := by
      have h1 : φ [0] ≤ φ [] * φ [0] := by simpa using hφmul [] [0]
      nlinarith [hφ0 [0], hφ0 []]
    exact key [0] (by simp) (by rw [h0, mul_zero]; norm_num)
  · exact key y hyne hy

end Abstract

/-! ## §2 The uniform lower bound and survivability -/

variable {K : Type*} [Fintype K] [DecidableEq K] (D : Fin 2 → Matrix K K ℕ)

theorem Dx_rep (y : List (Fin 2)) (n : ℕ) : Dx D (rep y n) = Dx D y ^ n := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    have e : rep y (n + 1) = y ++ rep y n := by simp [rep, List.replicate_succ]
    rw [e, Dx_append, ih, pow_succ']

theorem nrm_Dx_eq (g : ℝ) (hg : 0 < g) (x : List (Fin 2)) :
    nrm (Dx D x) = g ^ x.length * nrm (Ex D g x) := by
  rw [Dx_eq_smul_Ex D hg.ne' x, nrm_smul, abs_of_pos (pow_pos hg _)]

theorem bAvg_eq_wsum (n : ℕ) :
    bAvg D n = (2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (nrm (Dx D x))) := by
  rw [bAvg, wsum_eq_sum]

/-- **Uniform lower bound**: for a strongly connected rigid pair there is `c > 0` with `‖E_x‖ ≥ c` for all words. -/
theorem uniform_lower (hSC : SC D) {g : ℝ} (hR : RigidAt D g) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ nrm (Ex D g x) := by
  have hg0 : 0 < g := by linarith [hR.one_lt]
  obtain ⟨L, hL⟩ := Ex_entry_bound D hSC hR.one_lt.le hR.diag_le
  set C : ℝ := max 1 ((Fintype.card K : ℝ) ^ 2 * g ^ L) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hφC : ∀ x, nrm (Ex D g x) ≤ C := by
    intro x
    refine (nrm_le_of_entry_le fun i j => ?_).trans (le_max_right _ _)
    rw [abs_of_nonneg (Ex_nonneg D hg0.le x i j)]
    exact hL x i j
  have hmain := block_lower (φ := fun x => nrm (Ex D g x)) (ψ := fun x => nrm (Dx D x)) (A := 1) (C := C)
    (g := g) (fun x => nrm_nonneg _) (fun x y => by rw [Ex_append]; exact nrm_mul_le _ _) hφC hC1
    le_rfl hR.one_lt (fun x => nrm_nonneg _) (fun x => by rw [nrm_Dx_eq D g hg0 x, one_mul])
    (by
      have := hR.tendsto
      simpa only [bAvg_eq_wsum] using this)
  refine ⟨1 / C, by positivity, fun x => ?_⟩
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < C), mul_comm]
  exact hmain x

/-- The uniform lower bound in terms of `D`: `‖D_x‖ ≥ c g^{|x|}`. -/
theorem uniform_lower_Dx (hSC : SC D) {g : ℝ} (hR : RigidAt D g) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * g ^ x.length ≤ nrm (Dx D x) := by
  obtain ⟨c, hc, h⟩ := uniform_lower D hSC hR
  have hg0 : 0 < g := by linarith [hR.one_lt]
  refine ⟨c, hc, fun x => ?_⟩
  rw [nrm_Dx_eq D g hg0 x, mul_comm c]
  exact mul_le_mul_of_nonneg_left (h x) (pow_nonneg hg0.le _)

/-- **Survivability**: `D_x ≠ 0` for all words. -/
theorem Dx_ne_zero (hSC : SC D) {g : ℝ} (hR : RigidAt D g) (x : List (Fin 2)) : Dx D x ≠ 0 := by
  obtain ⟨c, hc, h⟩ := uniform_lower_Dx D hSC hR
  intro h0
  have := h x
  rw [h0] at this
  have h1 : nrm (0 : Matrix K K ℝ) = 0 := by simp [nrm]
  rw [h1] at this
  have : 0 < c * g ^ x.length := mul_pos hc (pow_pos (by linarith [hR.one_lt]) _)
  linarith

/-- Survivability, second half: `‖D_x‖ ≥ 1`, hence `log⁺ ‖D_x‖ = log ‖D_x‖`. -/
theorem one_le_nrm_Dx_of_rigid (hSC : SC D) {g : ℝ} (hR : RigidAt D g) (x : List (Fin 2)) :
    1 ≤ nrm (Dx D x) :=
  one_le_nrm_Dx D (Dx_ne_zero D hSC hR x)

/-- The statement with `g := gDiag D`. -/
theorem IsRigid.uniform_lower (hSC : SC D) (hR : IsRigid D) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * gDiag D ^ x.length ≤ nrm (Dx D x) :=
  uniform_lower_Dx D hSC (hR.rigidAt D)

/-! ## §3 `Λ⁺` does not depend on the norm (comparison with the maximal row sum) -/

/-- The averages of `log⁺` of two quantities that agree up to constant factors have the same limit growth. -/
theorem posLog_avg_tendsto_iff {ψ₁ ψ₂ : List (Fin 2) → ℝ} {a : ℝ} (ha : 1 ≤ a)
    (h0₁ : ∀ x, 0 ≤ ψ₁ x) (h0₂ : ∀ x, 0 ≤ ψ₂ x)
    (h12 : ∀ x, ψ₁ x ≤ a * ψ₂ x) (h21 : ∀ x, ψ₂ x ≤ a * ψ₁ x) (l : ℝ) :
    Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (ψ₁ x)) / n) atTop (𝓝 l) ↔
      Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (ψ₂ x)) / n) atTop (𝓝 l) := by
  -- One direction suffices (symmetry).
  have one : ∀ {χ₁ χ₂ : List (Fin 2) → ℝ}, (∀ x, 0 ≤ χ₁ x) → (∀ x, 0 ≤ χ₂ x) →
      (∀ x, χ₁ x ≤ a * χ₂ x) → (∀ x, χ₂ x ≤ a * χ₁ x) →
      Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (χ₁ x)) / n) atTop (𝓝 l) →
      Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (χ₂ x)) / n) atTop (𝓝 l) := by
    intro χ₁ χ₂ h1 h2 h12' h21' hT
    have hla : Real.posLog a = Real.log a := Real.posLog_eq_log (by rw [abs_of_pos (by linarith)]; exact ha)
    have hpt : ∀ {f g : List (Fin 2) → ℝ}, (∀ x, 0 ≤ g x) → (∀ x, f x ≤ a * g x) → (∀ x, 0 ≤ f x) →
        ∀ x, Real.posLog (f x) ≤ Real.log a + Real.posLog (g x) := by
      intro f g hg hfg hf x
      calc Real.posLog (f x) ≤ Real.posLog (a * g x) :=
            Real.posLog_le_posLog (by linarith [hf x]) (hfg x)
        _ ≤ Real.posLog a + Real.posLog (g x) := Real.posLog_mul
        _ = Real.log a + Real.posLog (g x) := by rw [hla]
    -- The difference of the averages is at most `log a`
    have hdiff : ∀ n : ℕ, |(2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (χ₂ x)) -
        (2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (χ₁ x))| ≤ Real.log a := by
      intro n
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      have hu : wsum n (fun x => Real.posLog (χ₂ x)) ≤ wsum n (fun x => Real.posLog (χ₁ x)) +
          2 ^ n * Real.log a := by
        have := wsum_mono (n := n) (fun x _ => hpt h1 h21' h2 x)
        rw [wsum_add, wsum_const] at this; linarith
      have hd : wsum n (fun x => Real.posLog (χ₁ x)) ≤ wsum n (fun x => Real.posLog (χ₂ x)) +
          2 ^ n * Real.log a := by
        have := wsum_mono (n := n) (fun x _ => hpt h2 h12' h1 x)
        rw [wsum_add, wsum_const] at this; linarith
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr h2n), inv_mul_le_iff₀ h2n, abs_le]
      constructor <;> linarith
    have hz : Tendsto (fun n : ℕ => ((2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (χ₂ x)) -
        (2 ^ n : ℝ)⁻¹ * wsum n (fun x => Real.posLog (χ₁ x))) / n) atTop (𝓝 0) := by
      have hb := tendsto_const_div_atTop_nhds_zero_nat (Real.log a)
      have hb' := hb.neg
      rw [neg_zero] at hb'
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hb' hb ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [neg_div', div_le_div_iff_of_pos_right hn']
        exact neg_le_of_abs_le (hdiff n)
      · filter_upwards [eventually_gt_atTop 0] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [div_le_div_iff_of_pos_right hn']
        exact le_of_abs_le (hdiff n)
    have := hT.add hz
    rw [add_zero] at this
    refine this.congr fun n => ?_
    rw [sub_div]; ring
  exact ⟨one h0₁ h0₂ h12 h21, one h0₂ h0₁ h21 h12⟩

/-- The maximal-row-sum norm (the norm `‖·‖` of an earlier version of the argument). -/
noncomputable def rowSum (Y : Matrix K K ℝ) : ℝ := ⨆ i, ∑ j, |Y i j|

theorem rowSum_nonneg (Y : Matrix K K ℝ) : 0 ≤ rowSum Y :=
  Real.iSup_nonneg fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem rowSum_le_nrm (Y : Matrix K K ℝ) : rowSum Y ≤ nrm Y :=
  Real.iSup_le (fun i => Finset.single_le_sum (f := fun i' => ∑ j, |Y i' j|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)) (nrm_nonneg _)

theorem nrm_le_card_mul_rowSum (Y : Matrix K K ℝ) : nrm Y ≤ Fintype.card K * rowSum Y := by
  unfold nrm
  calc ∑ i, ∑ j, |Y i j| ≤ ∑ _i : K, rowSum Y :=
        Finset.sum_le_sum fun i _ =>
          le_ciSup (f := fun i' => ∑ j, |Y i' j|) (Set.finite_range _).bddAbove i
    _ = Fintype.card K * rowSum Y := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **Rigidity is equivalent to its form with the maximal-row-sum norm**. -/
theorem isRigid_iff_rowSum :
    IsRigid D ↔ 1 < gDiag D ∧ Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹ *
      (∑ x : Fin n → Fin 2, Real.posLog (rowSum (Dx D (List.ofFn x)))) / n) atTop
        (𝓝 (Real.log (gDiag D))) := by
  set a : ℝ := max 1 (Fintype.card K) with ha
  have ha1 : 1 ≤ a := le_max_left _ _
  have h := posLog_avg_tendsto_iff (ψ₁ := fun x => nrm (Dx D x)) (ψ₂ := fun x => rowSum (Dx D x))
    ha1 (fun x => nrm_nonneg _) (fun x => rowSum_nonneg _)
    (fun x => (nrm_le_card_mul_rowSum _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (rowSum_nonneg _)))
    (fun x => (rowSum_le_nrm _).trans (le_mul_of_one_le_left (nrm_nonneg _) ha1))
    (Real.log (gDiag D))
  simp only [IsRigid, bAvg_eq_wsum]
  simp only [wsum_eq_sum] at h ⊢
  rw [h]

/-! ## §4 Rigidity is equivalent to a uniform lower bound (a form without limits; Lemma D.3) -/

/-- **Rigidity ⟺ uniform lower bound** (Lemma D.3): if the pair is strongly connected, `g > 1` and `(D_w)_{ii} ≤ g^{|w|}`, then `Λ⁺ = log g` (the limit of the averages) and
"there is `c > 0` with `‖D_x‖ ≥ c g^{|x|}` for all words" are equivalent. The latter involves no limit. -/
theorem rigidAt_iff_uniform_lower (hSC : SC D) {g : ℝ} (hg : 1 < g)
    (hdiag : ∀ (w : List (Fin 2)) (i : K), Dx D w i i ≤ g ^ w.length) :
    RigidAt D g ↔ ∃ c : ℝ, 0 < c ∧ ∀ x, c * g ^ x.length ≤ nrm (Dx D x) := by
  constructor
  · intro hR; exact uniform_lower_Dx D hSC hR
  · rintro ⟨c, hc, hlow⟩
    refine ⟨hg, hdiag, ?_⟩
    have hg0 : 0 < g := by linarith
    obtain ⟨L, hL⟩ := entry_bound D hSC hg.le hdiag
    set U : ℝ := (Fintype.card K : ℝ) ^ 2 * g ^ L
    have hup : ∀ x, nrm (Dx D x) ≤ U * g ^ x.length := by
      intro x
      have h1 : nrm (Dx D x) ≤ (Fintype.card K : ℝ) ^ 2 * g ^ (x.length + L) :=
        nrm_le_of_entry_le fun i j => by rw [abs_of_nonneg (Dx_nonneg D x i j)]; exact hL x i j
      refine h1.trans (le_of_eq ?_)
      simp only [U, pow_add]; ring
    -- The bound for each word
    have hlo : ∀ x, Real.log c + x.length * Real.log g ≤ Real.posLog (nrm (Dx D x)) := by
      intro x
      have h1 : Real.log (c * g ^ x.length) ≤ Real.log (nrm (Dx D x)) :=
        Real.log_le_log (by positivity) (hlow x)
      rw [Real.log_mul hc.ne' (by positivity), Real.log_pow] at h1
      exact h1.trans (le_max_right _ _)
    have hhi : ∀ x, Real.posLog (nrm (Dx D x)) ≤ Real.posLog U + x.length * Real.log g := by
      intro x
      calc Real.posLog (nrm (Dx D x)) ≤ Real.posLog (U * g ^ x.length) :=
            Real.posLog_le_posLog (by linarith [nrm_nonneg (Dx D x)]) (hup x)
        _ ≤ Real.posLog U + Real.posLog (g ^ x.length) := Real.posLog_mul
        _ = Real.posLog U + x.length * Real.log g := by
            rw [Real.posLog_eq_log (x := g ^ x.length)
              (by rw [abs_of_pos (by positivity)]; exact one_le_pow₀ hg.le), Real.log_pow]
    have hbA : ∀ n : ℕ, Real.log c + n * Real.log g ≤ bAvg D n ∧
        bAvg D n ≤ Real.posLog U + n * Real.log g := by
      intro n
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      rw [bAvg_eq_wsum]
      constructor
      · rw [le_inv_mul_iff₀ h2n, mul_comm]
        have := wsum_mono (n := n) (F := fun _ => Real.log c + n * Real.log g)
          (G := fun x => Real.posLog (nrm (Dx D x))) (fun x hx => by rw [← hx]; exact hlo x)
        rwa [wsum_const, mul_comm] at this
      · rw [inv_mul_le_iff₀ h2n]
        have := wsum_mono (n := n) (G := fun _ => Real.posLog U + n * Real.log g)
          (F := fun x => Real.posLog (nrm (Dx D x))) (fun x hx => by rw [← hx]; exact hhi x)
        rwa [wsum_const] at this
    have hlo' : Tendsto (fun n : ℕ => Real.log c / n + Real.log g) atTop (𝓝 (0 + Real.log g)) :=
      (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds
    have hhi' : Tendsto (fun n : ℕ => Real.posLog U / n + Real.log g) atTop (𝓝 (0 + Real.log g)) :=
      (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds
    rw [zero_add] at hlo' hhi'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo' hhi' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
      linarith [(hbA n).1]
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
      linarith [(hbA n).2]

/-- A characterization of rigidity with `g := gDiag D`: rigidity ⟺ `g > 1` and a uniform lower bound. -/
theorem isRigid_iff_uniform_lower (hSC : SC D) :
    IsRigid D ↔ 1 < gDiag D ∧ ∃ c : ℝ, 0 < c ∧ ∀ x, c * gDiag D ^ x.length ≤ nrm (Dx D x) := by
  constructor
  · intro hR; exact ⟨hR.1, IsRigid.uniform_lower D hSC hR⟩
  · rintro ⟨hg, h⟩
    exact ((rigidAt_iff_uniform_lower D hSC hg (diag_le_gDiag D)).mpr h).tendsto |> fun t => ⟨hg, t⟩

end Collatz.Arctic.NatQ5.Rigid
