/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for Lemma 11.1, Corollary 11.2 and Lemma 11.3 of the paper

The premises of `H2Path.lean` (`path_block_bound`, `poly_bound`, `poly_bound_of_diag`) and of `H2Top.lean` (`top_rigid`) can be satisfied, and
examples show that the conclusions are not trivial (outside the closure of the main theorems).

* **(a) The polynomial factor of the polynomial bound is needed** (`exJ_*`): the two-state automaton `B₀ = B₁ = [[1,1],[0,1]]` (a Jordan block,
  with the two components `{0}`, `{1}`) satisfies the diagonal bound with `G = 1`, and `poly_bound_of_diag` applies. The entry `(0,1)` is `|w|`
  (`exJ_DxN`), and there is no bound of the form `C G^{|w|}` (`exJ_no_const_bound`).
* **(b) The premises of `top_rigid` can be satisfied, and the choice of the component in its conclusion is not trivial** (`exA_*`): the two-state diagonal automaton
  `B₀ = diag(2,2)`, `B₁ = diag(2,1)` (components `{0}`, `{1}`, `G = 2`) satisfies the three hypotheses of `top_rigid`. The component `{1}` is
  not rigid (`exA_not_rigid_one`: `‖D^{\{1\}}_{1^n}‖ = 1`), so the conclusion of `top_rigid` gives the rigidity of the component `{0}`
  (`exA_rigid_zero`).
* **(c) A strongly connected rigid example** (`d3_top`): `D3` of `RigidExample.lean` (row sums 3, not a lane) satisfies the premises with `G = 3`.
* **(d) In an example where the conclusion is false, the hypothesis `hLC` fails** (`dJ_not_hLC`): for `DJ` of `RigidExample.lean` (`J` and `diag(2,1)`, strongly connected
  and not rigid, `exJ_not_rigid`), `∀ κ ≥ 1, κ log G ≤ bAvg_κ` does not hold with `G = gDiag DJ`. The contrapositive of `top_rigid`.
-/
import CollatzProof.Arctic.Nat.H2Top
import CollatzProof.Arctic.Nat.RigidExample

namespace Collatz.Arctic.NatQ5.W2b

open Collatz.Arctic Matrix

set_option linter.unusedSectionVars false

/-! ## §0 Common: the norm of a product on a component is at most the norm of the whole product -/

theorem nrm_Dx_compMat_le {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) (q : Q) (x : List (Fin 2)) :
    Rigid.nrm (Rigid.Dx (compMat A (sccOf A q)) x) ≤ Rigid.nrm (Rigid.Dx A.B x) := by
  unfold Rigid.nrm
  simp_rw [Dx_compMat_apply]
  rw [Finset.sum_coe_sort (sccOf A q) (fun a => ∑ b : sccOf A q, |Rigid.Dx A.B x a b.1|)]
  refine (Finset.sum_le_sum fun a _ => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ =>
      Finset.sum_nonneg fun b _ => abs_nonneg _)
  rw [Finset.sum_coe_sort (sccOf A q) (fun b => |Rigid.Dx A.B x a b|)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => abs_nonneg _

/-! ## §1 (a) A Jordan block: the polynomial factor is needed -/

/-- `B₀ = B₁ = [[1,1],[0,1]]`. -/
def exJB : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ := fun _ => !![1, 1; 0, 1]

/-- Start `e₀`, end `e₁` (the value is `|w|`). -/
def exJ : ValAuto (Fin 2) := ⟨exJB, ![1, 0], ![0, 1]⟩

theorem exJ_DxN (w : List (Fin 2)) : Rigid.DxN exJB w = !![1, w.length; 0, 1] := by
  induction w with
  | nil =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | cons b w ih =>
    rw [DxN_cons', ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [exJB, Matrix.mul_apply, Fin.sum_univ_two]

theorem exJ_diag (w : List (Fin 2)) (i : Fin 2) : Rigid.Dx exJ.B w i i ≤ (1 : ℝ) ^ w.length := by
  rw [Rigid.Dx_apply]
  show (Rigid.DxN exJB w i i : ℝ) ≤ _
  rw [exJ_DxN]
  fin_cases i <;> simp

/-- `poly_bound_of_diag` applies: `|w| ≤ C' (|w| + 1)^2`. -/
theorem exJ_poly : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ w : List (Fin 2),
    (w.length : ℝ) ≤ C' * ((w.length : ℝ) + 1) ^ 2 := by
  obtain ⟨C', hC', h⟩ := poly_bound_of_diag exJ (G := 1) le_rfl exJ_diag
  refine ⟨C', hC', fun w => ?_⟩
  have := h w 0 1
  have e : Rigid.DxN exJ.B w 0 1 = w.length := by
    show Rigid.DxN exJB w 0 1 = _
    rw [exJ_DxN]; simp
  rw [e, one_pow, mul_one, Fintype.card_fin] at this
  exact this

/-- There is no bound `C G^{|w|}` (`G = 1`) without a polynomial factor. -/
theorem exJ_no_const_bound : ¬ ∃ C : ℝ, ∀ w : List (Fin 2), (Rigid.DxN exJ.B w 0 1 : ℝ) ≤ C * 1 ^ w.length := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC (List.replicate n 0)
  have e : Rigid.DxN exJ.B (List.replicate n 0) 0 1 = n := by
    show Rigid.DxN exJB _ 0 1 = _
    rw [exJ_DxN]; simp
  rw [e, one_pow, mul_one] at this
  linarith

/-! ## §2 (b) A diagonal automaton: a rigid component and a component that is not rigid -/

/-- `B₀ = diag(2,2)`, `B₁ = diag(2,1)`. -/
def exAB : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ :=
  fun b => Matrix.diagonal fun i => if i = 0 then 2 else if b = 0 then 2 else 1

def exA : ValAuto (Fin 2) := ⟨exAB, fun _ => 1, fun _ => 1⟩

theorem exA_DxN (w : List (Fin 2)) :
    Rigid.DxN exAB w = Matrix.diagonal fun i => if i = 0 then 2 ^ w.length else 2 ^ w.count 0 := by
  induction w with
  | nil =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | cons b w ih =>
    rw [DxN_cons', ih]
    unfold exAB
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> fin_cases b <;> simp [pow_succ] <;> ring

theorem exA_Dx_apply (w : List (Fin 2)) (i j : Fin 2) :
    Rigid.Dx exA.B w i j =
      if i = j then (if i = 0 then (2 : ℝ) ^ w.length else (2 : ℝ) ^ w.count 0) else 0 := by
  rw [Rigid.Dx_apply]
  show (Rigid.DxN exAB w i j : ℝ) = _
  rw [exA_DxN]
  by_cases h : i = j
  · subst h; simp [Matrix.diagonal_apply_eq]
  · simp [h]

theorem exA_diag (w : List (Fin 2)) (i : Fin 2) : Rigid.Dx exA.B w i i ≤ (2 : ℝ) ^ w.length := by
  rw [exA_Dx_apply]
  split_ifs with h1 h2
  · exact le_rfl
  · exact pow_le_pow_right₀ (by norm_num) List.count_le_length
  · positivity

theorem exA_hLC (κ : ℕ) (_ : 1 ≤ κ) : (κ : ℝ) * Real.log 2 ≤ Rigid.bAvg exA.B κ := by
  rw [Rigid.bAvg_eq_wsum]
  have h2 : (0 : ℝ) < 2 ^ κ := by positivity
  rw [le_inv_mul_iff₀ h2]
  have hpt : ∀ w : List (Fin 2), w.length = κ → (κ : ℝ) * Real.log 2 ≤ Real.posLog (Rigid.nrm (Rigid.Dx exA.B w)) := by
    intro w hw
    have h1 : (2 : ℝ) ^ κ ≤ Rigid.nrm (Rigid.Dx exA.B w) := by
      have := Rigid.le_nrm (Rigid.Dx exA.B w) 0 0
      rw [exA_Dx_apply] at this
      simpa [hw] using this
    calc (κ : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ κ) := by rw [Real.log_pow]
      _ ≤ Real.log (Rigid.nrm (Rigid.Dx exA.B w)) := Real.log_le_log (by positivity) h1
      _ ≤ Real.posLog (Rigid.nrm (Rigid.Dx exA.B w)) := le_max_right _ _
  have := Rigid.wsum_mono (n := κ) (F := fun _ => (κ : ℝ) * Real.log 2)
    (G := fun w => Real.posLog (Rigid.nrm (Rigid.Dx exA.B w))) hpt
  rw [Rigid.wsum_const] at this
  linarith

theorem exA_scc_one : sccOf exA 1 = {1} := by
  ext x
  rw [mem_sccOf, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨w, hw⟩, _⟩
    by_contra hx
    have : Rigid.DxN exA.B w 1 x = 0 := by
      show Rigid.DxN exAB w 1 x = 0
      rw [exA_DxN, Matrix.diagonal_apply_ne _ (Ne.symm hx)]
    omega
  · rintro rfl; exact ⟨conn_refl exA 1, conn_refl exA 1⟩

/-- The component `{1}` is not rigid for `G = 2` (`‖D^{\{1\}}_{1^n}‖ = 1`). -/
theorem exA_not_rigid_one : ¬ Rigid.RigidAt (compMat exA (sccOf exA 1)) 2 := by
  intro hR
  obtain ⟨c, hc, hlow⟩ := Rigid.uniform_lower_Dx _ (sc_compMat exA 1) hR
  have hcard : Fintype.card (sccOf exA 1) = 1 := by rw [Fintype.card_coe, exA_scc_one]; rfl
  have hup : ∀ n : ℕ, Rigid.nrm (Rigid.Dx (compMat exA (sccOf exA 1)) (List.replicate n 1)) ≤ 1 := by
    intro n
    have h := Rigid.nrm_le_of_entry_le (Y := Rigid.Dx (compMat exA (sccOf exA 1)) (List.replicate n 1))
      (B := 1) fun a b => by
        rw [Dx_compMat_apply, exA_Dx_apply]
        have ha : a.1 = 1 := by
          have hmem : a.1 ∈ sccOf exA 1 := a.2
          have : a.1 ∈ ({1} : Finset (Fin 2)) := by rw [← exA_scc_one]; exact hmem
          simpa using this
        have hb : b.1 = 1 := by
          have hmem : b.1 ∈ sccOf exA 1 := b.2
          have : b.1 ∈ ({1} : Finset (Fin 2)) := by rw [← exA_scc_one]; exact hmem
          simpa using this
        rw [ha, hb]
        simp [List.count_replicate]
    rwa [hcard, Nat.cast_one, one_pow, one_mul] at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / c) (by norm_num : (1 : ℝ) < 2)
  have h1 := (hlow (List.replicate n 1)).trans (hup n)
  rw [List.length_replicate] at h1
  have : 1 < c * 2 ^ n := by
    rw [div_lt_iff₀ hc] at hn; linarith
  linarith

/-- The conclusion of `top_rigid` gives the rigidity of the component `{0}` (as the component `{1}` is not rigid). -/
theorem exA_rigid_zero : Rigid.RigidAt (compMat exA (sccOf exA 0)) 2 := by
  obtain ⟨q, hq⟩ := top_rigid exA (G := 2) one_lt_two exA_diag exA_hLC
  fin_cases q
  · exact hq
  · exact absurd hq exA_not_rigid_one

/-! ## §3 (c) A strongly connected rigid example (`D3` of `RigidExample.lean`) -/

def d3A : ValAuto (Fin 2) := ⟨Rigid.D3, fun _ => 1, fun _ => 1⟩

theorem d3_top : ∃ q, Rigid.RigidAt (compMat d3A (sccOf d3A q)) 3 := by
  refine top_rigid d3A (by norm_num) (fun w i => ?_) (fun κ _ => ?_)
  · have := Rigid.diag_le_gDiag Rigid.D3 w i
    rwa [Rigid.D3_gDiag] at this
  · rw [Rigid.bAvg_eq_wsum]
    have h2 : (0 : ℝ) < 2 ^ κ := by positivity
    rw [le_inv_mul_iff₀ h2]
    have hpt : ∀ w : List (Fin 2), w.length = κ →
        (κ : ℝ) * Real.log 3 ≤ Real.posLog (Rigid.nrm (Rigid.Dx d3A.B w)) := by
      intro w hw
      show (κ : ℝ) * Real.log 3 ≤ Real.posLog (Rigid.nrm (Rigid.Dx Rigid.D3 w))
      rw [Rigid.D3_nrm, hw]
      calc (κ : ℝ) * Real.log 3 = Real.log ((3 : ℝ) ^ κ) := by rw [Real.log_pow]
        _ ≤ Real.log (2 * (3 : ℝ) ^ κ) := Real.log_le_log (by positivity) (by linarith [pow_pos (by norm_num : (0:ℝ) < 3) κ])
        _ ≤ Real.posLog (2 * (3 : ℝ) ^ κ) := le_max_right _ _
    have := Rigid.wsum_mono (n := κ) (F := fun _ => (κ : ℝ) * Real.log 3)
      (G := fun w => Real.posLog (Rigid.nrm (Rigid.Dx d3A.B w))) hpt
    rw [Rigid.wsum_const] at this
    linarith

/-! ## §4 (d) In an example where the conclusion is false, `hLC` fails (`DJ` of `RigidExample.lean`) -/

def dJA : ValAuto (Fin 2) := ⟨Rigid.DJ, fun _ => 1, fun _ => 1⟩

/-- For `DJ` (strongly connected, not rigid), `κ log G ≤ bAvg_κ` with `G = gDiag DJ` does not hold for all `κ ≥ 1`. -/
theorem dJ_not_hLC :
    ¬ ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log (Rigid.gDiag Rigid.DJ) ≤ Rigid.bAvg Rigid.DJ κ := by
  intro hLC
  have hG : 1 < Rigid.gDiag Rigid.DJ := by linarith [Rigid.two_le_gDiag_DJ]
  obtain ⟨q, hq⟩ := top_rigid dJA hG (Rigid.diag_le_gDiag Rigid.DJ) hLC
  obtain ⟨c, hc, hlow⟩ := Rigid.uniform_lower_Dx _ (sc_compMat dJA q) hq
  have hlow' : ∃ c : ℝ, 0 < c ∧ ∀ x, c * Rigid.gDiag Rigid.DJ ^ x.length ≤ Rigid.nrm (Rigid.Dx Rigid.DJ x) :=
    ⟨c, hc, fun x => (hlow x).trans (nrm_Dx_compMat_le dJA q x)⟩
  have hR := (Rigid.rigidAt_iff_uniform_lower Rigid.DJ Rigid.DJ_SC hG (Rigid.diag_le_gDiag Rigid.DJ)).2 hlow'
  exact Rigid.exJ_not_rigid ⟨hG, hR.tendsto⟩

end Collatz.Arctic.NatQ5.W2b
