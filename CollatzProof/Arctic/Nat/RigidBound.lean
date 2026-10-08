/-
# Lemma D.2 (no entrywise defect: entries bounded by the diagonal growth) and the diagonal `g`

Lemma D.2 as first stated: if `g ≥ 1`, then `‖D_x‖_max ≤ g^{|x|+|K|}` for all words `x`.

The Lean form (`entry_bound`): under strong connectivity `SC D`, `(D_w)_{ii} ≤ g^{|w|}` (for all `w, i`) and `g ≥ 1`, there is `L`
with `(D_x)_{ij} ≤ g^{|x|+L}` for all `x, i, j`. `L` is the largest length of the witnessing paths of strong connectivity, in place of `|K|`
(that shortest paths give `|K| - 1` is classical, but `L` is only used as a constant later, so the argument shortening paths is omitted).

On the diagonal `g` (`gDiag`): it is bounded above (`bddAbove_gDiag`), `(D_w)_{ii} ≤ gDiag^{|w|}` (`diag_le_gDiag`),
`gDiag ≥ 1` if there is an internal cycle (`one_le_gDiag`), and rigidity `IsRigid D` gives `RigidAt D (gDiag D)` (`IsRigid.rigidAt`).
-/
import CollatzProof.Arctic.Nat.RigidDefs

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] [DecidableEq K] (D : Fin 2 → Matrix K K ℕ)

/-! ## §1 The one-letter bound `W` and boundedness of the diagonal `g` -/

/-- `W := max(1, ‖D₀‖, ‖D₁‖)`. -/
noncomputable def Wd : ℝ := max 1 (max (nrm (DR D 0)) (nrm (DR D 1)))

theorem one_le_Wd : 1 ≤ Wd D := le_max_left _ _

theorem nrm_DR_le (b : Fin 2) : nrm (DR D b) ≤ Wd D := by
  unfold Wd
  fin_cases b
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- For a non-empty word, `‖D_w‖ ≤ W^{|w|}`. -/
theorem nrm_Dx_cons_le (b : Fin 2) (w : List (Fin 2)) :
    nrm (Dx D (b :: w)) ≤ Wd D ^ (w.length + 1) := by
  induction w generalizing b with
  | nil => simpa [Dx_singleton] using nrm_DR_le D b
  | cons c w ih =>
    rw [Dx_cons]
    calc nrm (DR D b * Dx D (c :: w)) ≤ nrm (DR D b) * nrm (Dx D (c :: w)) := nrm_mul_le _ _
      _ ≤ Wd D * Wd D ^ (w.length + 1) :=
          mul_le_mul (nrm_DR_le D b) (ih c) (nrm_nonneg _) (by linarith [one_le_Wd D])
      _ = Wd D ^ ((c :: w).length + 1) := by simp [pow_succ]; ring

theorem diag_rpow_le_Wd (w : List (Fin 2)) (hw : w ≠ []) (i : K) :
    (Dx D w i i) ^ ((w.length : ℝ)⁻¹) ≤ Wd D := by
  obtain ⟨b, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  have hn : (b :: w').length ≠ 0 := by simp
  have h1 : Dx D (b :: w') i i ≤ Wd D ^ (b :: w').length := by
    have := (le_nrm _ i i).trans (nrm_Dx_cons_le D b w')
    simpa using this
  calc (Dx D (b :: w') i i) ^ (((b :: w').length : ℝ)⁻¹)
      ≤ (Wd D ^ (b :: w').length) ^ (((b :: w').length : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Dx_nonneg D _ i i) h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = Wd D := Real.pow_rpow_inv_natCast (by linarith [one_le_Wd D]) hn

theorem bddAbove_gDiag :
    BddAbove (Set.range fun p : {w : List (Fin 2) // w ≠ []} × K =>
      (Dx D p.1.1 p.2 p.2) ^ ((p.1.1.length : ℝ)⁻¹)) := by
  refine ⟨Wd D, ?_⟩
  rintro _ ⟨⟨⟨w, hw⟩, i⟩, rfl⟩
  exact diag_rpow_le_Wd D w hw i

theorem gDiag_nonneg : 0 ≤ gDiag D :=
  Real.iSup_nonneg fun _ => Real.rpow_nonneg (Dx_nonneg D _ _ _) _

/-- `(D_w)_{ii} ≤ gDiag^{|w|}` (for all words). -/
theorem diag_le_gDiag (w : List (Fin 2)) (i : K) : Dx D w i i ≤ gDiag D ^ w.length := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  · have hn : w.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hw
    have h1 : (Dx D w i i) ^ ((w.length : ℝ)⁻¹) ≤ gDiag D :=
      le_ciSup (bddAbove_gDiag D) (⟨⟨w, hw⟩, i⟩ : {w : List (Fin 2) // w ≠ []} × K)
    calc Dx D w i i = ((Dx D w i i) ^ ((w.length : ℝ)⁻¹)) ^ w.length :=
          (Real.rpow_inv_natCast_pow (Dx_nonneg D w i i) hn).symm
      _ ≤ gDiag D ^ w.length :=
          pow_le_pow_left₀ (Real.rpow_nonneg (Dx_nonneg D w i i) _) h1 _

/-- If there is an internal cycle (a non-empty word `w` and `i` with `(D_w)_{ii} ≥ 1`), then `gDiag ≥ 1`. -/
theorem one_le_gDiag (h : ∃ w : List (Fin 2), w ≠ [] ∧ ∃ i : K, 1 ≤ Dx D w i i) : 1 ≤ gDiag D := by
  obtain ⟨w, hw, i, hi⟩ := h
  have h1 : (Dx D w i i) ^ ((w.length : ℝ)⁻¹) ≤ gDiag D :=
    le_ciSup (bddAbove_gDiag D) (⟨⟨w, hw⟩, i⟩ : {w : List (Fin 2) // w ≠ []} × K)
  exact (Real.one_le_rpow hi (inv_nonneg.mpr (Nat.cast_nonneg _))).trans h1

theorem IsRigid.rigidAt (h : IsRigid D) : RigidAt D (gDiag D) :=
  ⟨h.1, diag_le_gDiag D, h.2⟩

/-! ## §2 Lemma D.2 -/

/-- **Lemma D.2 (no entrywise defect)**: if the pair is strongly connected, `(D_w)_{ii} ≤ g^{|w|}` and `g ≥ 1`, then there is `L` with
`(D_x)_{ij} ≤ g^{|x|+L}` for all `x, i, j`. -/
theorem entry_bound (hSC : SC D) {g : ℝ} (hg : 1 ≤ g)
    (hdiag : ∀ (w : List (Fin 2)) (i : K), Dx D w i i ≤ g ^ w.length) :
    ∃ L : ℕ, ∀ (x : List (Fin 2)) (i j : K), Dx D x i j ≤ g ^ (x.length + L) := by
  choose c hc using hSC
  refine ⟨Finset.univ.sup fun p : K × K => (c p.1 p.2).length, fun x i j => ?_⟩
  have hcl : (c j i).length ≤ Finset.univ.sup fun p : K × K => (c p.1 p.2).length :=
    Finset.le_sup (f := fun p : K × K => (c p.1 p.2).length) (Finset.mem_univ (j, i))
  have h1 : Dx D x i j ≤ Dx D (x ++ c j i) i i := by
    rw [Dx_append, Matrix.mul_apply]
    calc Dx D x i j ≤ Dx D x i j * Dx D (c j i) j i :=
          le_mul_of_one_le_right (Dx_nonneg D x i j) (hc j i)
      _ ≤ ∑ k, Dx D x i k * Dx D (c j i) k i :=
          Finset.single_le_sum (f := fun k => Dx D x i k * Dx D (c j i) k i)
            (fun k _ => mul_nonneg (Dx_nonneg D x i k) (Dx_nonneg D _ k i)) (Finset.mem_univ j)
  calc Dx D x i j ≤ Dx D (x ++ c j i) i i := h1
    _ ≤ g ^ (x ++ c j i).length := hdiag _ i
    _ ≤ g ^ (x.length + Finset.univ.sup fun p : K × K => (c p.1 p.2).length) := by
        rw [List.length_append]
        exact pow_le_pow_right₀ hg (Nat.add_le_add_left hcl _)

/-- The form of Lemma D.2 for `E`: `0 ≤ (E_x)_{ij} ≤ g^L` and `‖E_x‖ ≤ |K|^2 g^L`. -/
theorem Ex_entry_bound (hSC : SC D) {g : ℝ} (hg : 1 ≤ g)
    (hdiag : ∀ (w : List (Fin 2)) (i : K), Dx D w i i ≤ g ^ w.length) :
    ∃ L : ℕ, ∀ (x : List (Fin 2)) (i j : K), Ex D g x i j ≤ g ^ L := by
  obtain ⟨L, hL⟩ := entry_bound D hSC hg hdiag
  refine ⟨L, fun x i j => ?_⟩
  have hgp : 0 < g ^ x.length := pow_pos (by linarith) _
  rw [Ex_apply, inv_mul_le_iff₀ hgp, ← pow_add]
  exact hL x i j

end Collatz.Arctic.NatQ5.Rigid
