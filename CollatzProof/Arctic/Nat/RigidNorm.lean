/-
# The extremal norm (a supplement to Appendix D)

The statement: `𝒩(z) := sup_x g^{-|x|} ‖D_x z‖₁` is a norm, and in its operator norm `‖E_x‖_𝒩 = 1` for **all words** `x`.
(This is not a numbered result of the paper.)

The Lean form (`extremal_norm`): `𝒩` is a norm (equivalent to ℓ¹), and for all words `x`, `𝒩(E_x z) ≤ 𝒩(z)` and
`sup_{z ≠ 0} 𝒩(E_x z)/𝒩(z) = 1`.

As in the earlier written argument, the proof applies rigidity to the submultiplicative quantity `‖E_x‖_𝒩 ≤ 1`, but instead of Fekete's lemma it uses
`block_lower` of `RigidLower.lean` with `C = 1` (if some word has `‖E_x‖_𝒩 < 1`, the growth of the averages falls below `log g`).
Appendix D and Section 11 do not use this theorem (the uniform lower bound `uniform_lower` suffices). The companion statement `ρ(D_w) = g^{|w|}` is
`specRad_Dx` in `RigidSpec.lean` (Gelfand's formula; also not used downstream).
-/
import CollatzProof.Arctic.Nat.RigidLower

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] [DecidableEq K] (D : Fin 2 → Matrix K K ℕ)

/-- The ℓ¹ norm of a vector. -/
noncomputable def v1 (z : K → ℝ) : ℝ := ∑ i, |z i|

omit [DecidableEq K] in
theorem v1_nonneg (z : K → ℝ) : 0 ≤ v1 z := Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq K] in
theorem v1_add_le (z w : K → ℝ) : v1 (z + w) ≤ v1 z + v1 w := by
  unfold v1; rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le _ _

omit [DecidableEq K] in
theorem v1_smul (c : ℝ) (z : K → ℝ) : v1 (c • z) = |c| * v1 z := by
  simp [v1, abs_mul, Finset.mul_sum]

omit [DecidableEq K] in
theorem v1_eq_zero {z : K → ℝ} (h : v1 z = 0) : z = 0 := by
  funext i
  have h1 : |z i| ≤ v1 z :=
    Finset.single_le_sum (f := fun i => |z i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  rw [h] at h1
  exact abs_nonpos_iff.mp h1

omit [DecidableEq K] in
theorem v1_mulVec_le {Y : Matrix K K ℝ} {B : ℝ} (hY : ∀ i j, |Y i j| ≤ B) (z : K → ℝ) :
    v1 (Y *ᵥ z) ≤ Fintype.card K * B * v1 z := by
  unfold v1
  calc ∑ i, |(Y *ᵥ z) i| ≤ ∑ i, ∑ j, |Y i j| * |z j| := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Matrix.mulVec, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ _i : K, ∑ j, B * |z j| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hY i j) (abs_nonneg _)
    _ = Fintype.card K * B * ∑ j, |z j| := by
        simp [Finset.sum_const, Finset.mul_sum, mul_assoc]

/-- The extremal norm `𝒩(z) := sup_x ‖E_x z‖₁` (the supremum over all words, including the empty word). -/
noncomputable def NN (g : ℝ) (z : K → ℝ) : ℝ := ⨆ x : List (Fin 2), v1 (Ex D g x *ᵥ z)

section

variable {D} {g : ℝ} {L : ℕ} (hg : 1 ≤ g) (hL : ∀ x i j, Ex D g x i j ≤ g ^ L)
include hg hL

theorem Ex_abs_le (x : List (Fin 2)) (i j : K) : |Ex D g x i j| ≤ g ^ L := by
  rw [abs_of_nonneg (Ex_nonneg D (by linarith) x i j)]; exact hL x i j

theorem bdd_NN (z : K → ℝ) : BddAbove (Set.range fun x : List (Fin 2) => v1 (Ex D g x *ᵥ z)) :=
  ⟨Fintype.card K * g ^ L * v1 z, by
    rintro _ ⟨x, rfl⟩; exact v1_mulVec_le (Ex_abs_le hg hL x) z⟩

theorem le_NN (x : List (Fin 2)) (z : K → ℝ) : v1 (Ex D g x *ᵥ z) ≤ NN D g z :=
  le_ciSup (bdd_NN hg hL z) x

theorem v1_le_NN (z : K → ℝ) : v1 z ≤ NN D g z := by
  have := le_NN hg hL [] z
  simpa using this

theorem NN_le (z : K → ℝ) : NN D g z ≤ Fintype.card K * g ^ L * v1 z :=
  ciSup_le fun x => v1_mulVec_le (Ex_abs_le hg hL x) z

theorem NN_nonneg (z : K → ℝ) : 0 ≤ NN D g z := (v1_nonneg z).trans (v1_le_NN hg hL z)

theorem NN_eq_zero {z : K → ℝ} (h : NN D g z = 0) : z = 0 :=
  v1_eq_zero (le_antisymm (h ▸ v1_le_NN hg hL z) (v1_nonneg z))

theorem NN_pos {z : K → ℝ} (h : z ≠ 0) : 0 < NN D g z :=
  lt_of_le_of_ne (NN_nonneg hg hL z) fun h0 => h (NN_eq_zero hg hL h0.symm)

theorem NN_add_le (z w : K → ℝ) : NN D g (z + w) ≤ NN D g z + NN D g w :=
  ciSup_le fun x => by
    rw [Matrix.mulVec_add]
    exact (v1_add_le _ _).trans (add_le_add (le_NN hg hL x z) (le_NN hg hL x w))

theorem NN_smul (c : ℝ) (z : K → ℝ) : NN D g (c • z) = |c| * NN D g z := by
  unfold NN
  simp_rw [Matrix.mulVec_smul, v1_smul]
  exact (Real.mul_iSup_of_nonneg (abs_nonneg c) _).symm

/-- `𝒩(E_y z) ≤ 𝒩(z)`. -/
theorem NN_Ex_le (y : List (Fin 2)) (z : K → ℝ) : NN D g (Ex D g y *ᵥ z) ≤ NN D g z :=
  ciSup_le fun x => by
    rw [Matrix.mulVec_mulVec, ← Ex_append]
    exact le_NN hg hL _ z

/-- The operator norm `‖Y‖_𝒩 := sup_{z ≠ 0} 𝒩(Yz)/𝒩(z)`. -/
noncomputable def opN (Y : Matrix K K ℝ) : ℝ := ⨆ z : {z : K → ℝ // z ≠ 0}, NN D g (Y *ᵥ z.1) / NN D g z.1

omit hg hL in
theorem opN_def (Y : Matrix K K ℝ) :
    opN (D := D) (g := g) Y = ⨆ z : {z : K → ℝ // z ≠ 0}, NN D g (Y *ᵥ z.1) / NN D g z.1 := rfl

theorem bdd_opN (Y : Matrix K K ℝ) :
    BddAbove (Set.range fun z : {z : K → ℝ // z ≠ 0} => NN D g (Y *ᵥ z.1) / NN D g z.1) := by
  refine ⟨Fintype.card K * g ^ L * (Fintype.card K * (nrm Y)), ?_⟩
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  have hpos := NN_pos hg hL hz
  rw [div_le_iff₀ hpos]
  calc NN D g (Y *ᵥ z) ≤ Fintype.card K * g ^ L * v1 (Y *ᵥ z) := NN_le hg hL _
    _ ≤ Fintype.card K * g ^ L * (Fintype.card K * nrm Y * v1 z) := by
        refine mul_le_mul_of_nonneg_left (v1_mulVec_le (abs_le_nrm Y) z) (by positivity)
    _ ≤ Fintype.card K * g ^ L * (Fintype.card K * nrm Y * NN D g z) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (v1_le_NN hg hL z) (mul_nonneg (by positivity) (nrm_nonneg Y))
    _ = _ := by ring

theorem NN_mulVec_le_opN (Y : Matrix K K ℝ) (z : K → ℝ) :
    NN D g (Y *ᵥ z) ≤ opN (D := D) (g := g) Y * NN D g z := by
  by_cases hz : z = 0
  · subst hz
    have h0 : NN D g (0 : K → ℝ) = 0 := by
      have := NN_smul hg hL (0 : ℝ) (0 : K → ℝ); simpa using this
    simp [h0]
  · have hpos := NN_pos hg hL hz
    have := le_ciSup (bdd_opN hg hL Y) ⟨z, hz⟩
    rw [div_le_iff₀ hpos] at this
    exact this

theorem opN_nonneg [Nonempty K] (Y : Matrix K K ℝ) : 0 ≤ opN (D := D) (g := g) Y := by
  obtain ⟨i⟩ := ‹Nonempty K›
  have hz : (Pi.single i 1 : K → ℝ) ≠ 0 := by
    intro h; have := congrFun h i; simp at this
  refine le_trans ?_ (le_ciSup (bdd_opN hg hL Y) ⟨_, hz⟩)
  exact div_nonneg (NN_nonneg hg hL _) (NN_nonneg hg hL _)

theorem opN_mul_le [Nonempty K] (Y Z : Matrix K K ℝ) :
    opN (D := D) (g := g) (Y * Z) ≤ opN (D := D) (g := g) Y * opN (D := D) (g := g) Z := by
  have : Nonempty {z : K → ℝ // z ≠ 0} := by
    obtain ⟨i⟩ := ‹Nonempty K›
    exact ⟨⟨Pi.single i 1, fun h => by have := congrFun h i; simp at this⟩⟩
  refine ciSup_le fun ⟨z, hz⟩ => ?_
  have hpos := NN_pos hg hL hz
  rw [div_le_iff₀ hpos, ← Matrix.mulVec_mulVec]
  calc NN D g (Y *ᵥ (Z *ᵥ z)) ≤ opN (D := D) (g := g) Y * NN D g (Z *ᵥ z) := NN_mulVec_le_opN hg hL _ _
    _ ≤ opN (D := D) (g := g) Y * (opN (D := D) (g := g) Z * NN D g z) :=
        mul_le_mul_of_nonneg_left (NN_mulVec_le_opN hg hL _ _) (opN_nonneg hg hL Y)
    _ = _ := by ring

theorem opN_Ex_le [Nonempty K] (y : List (Fin 2)) : opN (D := D) (g := g) (Ex D g y) ≤ 1 := by
  have : Nonempty {z : K → ℝ // z ≠ 0} := by
    obtain ⟨i⟩ := ‹Nonempty K›
    exact ⟨⟨Pi.single i 1, fun h => by have := congrFun h i; simp at this⟩⟩
  refine ciSup_le fun ⟨z, hz⟩ => ?_
  rw [div_le_iff₀ (NN_pos hg hL hz), one_mul]
  exact NN_Ex_le hg hL y z

/-- For a non-negative matrix, `‖Y‖ ≤ |K|^2 g^L ‖Y‖_𝒩`. -/
theorem nrm_le_opN {Y : Matrix K K ℝ} (hY : ∀ i j, 0 ≤ Y i j) :
    nrm Y ≤ Fintype.card K * (Fintype.card K * g ^ L) * opN (D := D) (g := g) Y := by
  have e : ∑ i, ∑ j, Y i j = ∑ j, ∑ i, Y i j := Finset.sum_comm
  rw [nrm_of_nonneg hY, e]
  have hcol : ∀ j, ∑ i, Y i j ≤ opN (D := D) (g := g) Y * (Fintype.card K * g ^ L) := by
    intro j
    have e1 : ∑ i, Y i j = v1 (Y *ᵥ Pi.single j 1) := by
      simp [v1, abs_of_nonneg (hY _ _)]
    have h1 : v1 (Y *ᵥ Pi.single j 1) ≤ NN D g (Y *ᵥ Pi.single j 1) := v1_le_NN hg hL _
    have h2 := NN_mulVec_le_opN hg hL Y (Pi.single j 1)
    have h3 : NN D g (Pi.single j 1 : K → ℝ) ≤ Fintype.card K * g ^ L := by
      have := NN_le hg hL (Pi.single j (1 : ℝ))
      have hv : v1 (Pi.single j (1 : ℝ) : K → ℝ) = 1 := by
        simp only [v1]
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij; simp [hij]
        · intro h; exact absurd (Finset.mem_univ j) h
      rwa [hv, mul_one] at this
    have hop : 0 ≤ opN (D := D) (g := g) Y := by
      by_cases hK : Nonempty K
      · exact opN_nonneg hg hL Y
      · exact absurd ⟨j⟩ hK
    rw [e1]
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hop))
  calc ∑ j, ∑ i, Y i j ≤ ∑ _j : K, opN (D := D) (g := g) Y * (Fintype.card K * g ^ L) :=
        Finset.sum_le_sum fun j _ => hcol j
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

end

/-- If the pair is rigid, `K` is non-empty. -/
theorem nonempty_of_rigidAt {g : ℝ} (hR : RigidAt D g) : Nonempty K := by
  by_contra hK
  rw [not_nonempty_iff] at hK
  have h0 : ∀ n, bAvg D n / n = 0 := by
    intro n
    have : ∀ x : Fin n → Fin 2, nrm (Dx D (List.ofFn x)) = 0 := fun x => by simp [nrm]
    simp [bAvg, this]
  have := hR.tendsto
  simp_rw [h0] at this
  have hlog : Real.log g = 0 := tendsto_nhds_unique this tendsto_const_nhds
  have : 0 < Real.log g := Real.log_pos hR.one_lt
  linarith

/-- **The extremal norm**: `𝒩` is a norm equivalent to ℓ¹, and for all words `x`, `𝒩(E_x z) ≤ 𝒩(z)` and
`‖E_x‖_𝒩 = sup_{z ≠ 0} 𝒩(E_x z)/𝒩(z) = 1`. -/
theorem extremal_norm (hSC : SC D) {g : ℝ} (hR : RigidAt D g) :
    ∃ N : (K → ℝ) → ℝ, ∃ CN : ℝ,
      (∀ z, v1 z ≤ N z) ∧ (∀ z, N z ≤ CN * v1 z) ∧
      (∀ z, N z = 0 → z = 0) ∧ (∀ (c : ℝ) z, N (c • z) = |c| * N z) ∧ (∀ z w, N (z + w) ≤ N z + N w) ∧
      ∀ x : List (Fin 2), (∀ z, N (Ex D g x *ᵥ z) ≤ N z) ∧
        (⨆ z : {z : K → ℝ // z ≠ 0}, N (Ex D g x *ᵥ z.1) / N z.1) = 1 := by
  have hK := nonempty_of_rigidAt D hR
  have hg1 : 1 ≤ g := hR.one_lt.le
  have hg0 : 0 < g := by linarith
  obtain ⟨L, hL⟩ := Ex_entry_bound D hSC hg1 hR.diag_le
  refine ⟨NN D g, Fintype.card K * g ^ L, v1_le_NN hg1 hL, NN_le hg1 hL, fun z => NN_eq_zero hg1 hL,
    NN_smul hg1 hL, NN_add_le hg1 hL, fun x => ⟨NN_Ex_le hg1 hL x, ?_⟩⟩
  -- Apply `block_lower` with `φ := ‖E_·‖_𝒩` and `C := 1`.
  set A : ℝ := Fintype.card K * (Fintype.card K * g ^ L)
  have hA : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos
    have h2 : (1 : ℝ) ≤ g ^ L := one_le_pow₀ hg1
    have : 1 ≤ (Fintype.card K : ℝ) * g ^ L := one_le_mul_of_one_le_of_one_le h1 h2
    exact one_le_mul_of_one_le_of_one_le h1 this
  have hmain := block_lower (φ := fun x => opN (D := D) (g := g) (Ex D g x))
    (ψ := fun x => nrm (Dx D x)) (A := A) (C := 1) (g := g)
    (fun x => opN_nonneg hg1 hL _) (fun x y => by rw [Ex_append]; exact opN_mul_le hg1 hL _ _)
    (fun x => opN_Ex_le hg1 hL x) le_rfl hA hR.one_lt (fun x => nrm_nonneg _)
    (fun x => by
      rw [nrm_Dx_eq D g hg0 x]
      have := nrm_le_opN hg1 hL (Ex_nonneg D hg0.le x)
      calc g ^ x.length * nrm (Ex D g x) ≤ g ^ x.length * (A * opN (D := D) (g := g) (Ex D g x)) :=
            mul_le_mul_of_nonneg_left this (pow_nonneg hg0.le _)
        _ = A * g ^ x.length * opN (D := D) (g := g) (Ex D g x) := by ring)
    (by simpa only [bAvg_eq_wsum] using hR.tendsto)
  have h1 := hmain x
  rw [one_mul] at h1
  exact le_antisymm (opN_Ex_le hg1 hL x) h1

end Collatz.Arctic.NatQ5.Rigid
