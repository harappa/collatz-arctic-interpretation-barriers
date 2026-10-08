/-
# Non-vacuity of the rigidity statements

Examples showing that rigidity `IsRigid` and strong connectivity `SC` of `RigidDefs.lean` are neither vacuous nor trivial (outside the closure of the main theorems).

* **(a) The hypotheses can be satisfied**:
  * one state, `D₀ = D₁ = (2)`: `SC` and `IsRigid` (`gDiag = 2`);
  * a two-state example (row sums 3 for both letters; not a lane, i.e. the rows are not functional with a constant weight), `D₀ = [[2,1],[0,3]]`, `D₁ = [[0,3],[1,2]]`:
    `SC` and `IsRigid` (`gDiag = 3`). `heavy_family` applies (`ex3_heavy`).
* **(b) Rigidity does not hold trivially**: the pair `D₀ = J = [[1,1],[1,1]]`, `D₁ = diag(2,1)` is not rigid
  (`exJ_not_rigid`). The proof is the contrapositive of the uniform lower bound `uniform_lower`: rigidity would give `‖E_{(10)^n}‖ ≥ c > 0`, but
  `(D₁D₀)^n = 3^{n-1}(D₁D₀)` and `g ≥ 2`, so `‖E_{(10)^n}‖ ≤ 2 (3/4)^n → 0`. This agrees with an earlier observation (the pair is not rigid
  since `ρ(D₁D₀) = 3 < 4`).
-/
import CollatzProof.Arctic.Nat.RigidSep

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix Filter Topology

/-! ## §0 A common lemma -/

/-- If the averages have the form `a + n b`, then `bAvg/n → b`. -/
theorem tendsto_avg_affine {f : ℕ → ℝ} {a b : ℝ} (h : ∀ n, f n = a + n * b) :
    Tendsto (fun n : ℕ => f n / n) atTop (𝓝 b) := by
  have h1 : Tendsto (fun n : ℕ => a / n + b) atTop (𝓝 (0 + b)) :=
    (tendsto_const_div_atTop_nhds_zero_nat a).add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  show a / n + b = f n / n
  rw [h n]; field_simp

/-! ## §1 The one-state example -/

/-- `D₀ = D₁ = (2)`. -/
def D1 : Fin 2 → Matrix (Fin 1) (Fin 1) ℕ := fun _ => !![2]

theorem D1_Dx (x : List (Fin 2)) : Dx D1 x 0 0 = 2 ^ x.length := by
  induction x with
  | nil => simp
  | cons b x ih =>
    rw [Dx_cons, Matrix.mul_apply, Fin.sum_univ_one, ih]
    simp [DR, D1, pow_succ, mul_comm]

theorem D1_nrm (x : List (Fin 2)) : nrm (Dx D1 x) = 2 ^ x.length := by
  simp [nrm, D1_Dx]

theorem D1_SC : SC D1 := fun i j => ⟨[], by fin_cases i; fin_cases j; simp⟩

theorem D1_gDiag : gDiag D1 = 2 := by
  have h : ∀ p : {w : List (Fin 2) // w ≠ []} × Fin 1,
      (Dx D1 p.1.1 p.2 p.2) ^ ((p.1.1.length : ℝ)⁻¹) = 2 := by
    rintro ⟨⟨w, hw⟩, i⟩
    fin_cases i
    have hn : w.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hw
    simp only [Fin.zero_eta, Fin.isValue, D1_Dx]
    exact Real.pow_rpow_inv_natCast (by norm_num) hn
  unfold gDiag
  simp_rw [h]
  have : Nonempty ({w : List (Fin 2) // w ≠ []} × Fin 1) := ⟨⟨⟨[0], by simp⟩, 0⟩⟩
  exact ciSup_const

theorem D1_rigid : IsRigid D1 := by
  refine ⟨by rw [D1_gDiag]; norm_num, ?_⟩
  rw [D1_gDiag]
  refine tendsto_avg_affine (a := 0) fun n => ?_
  rw [bAvg]
  simp_rw [D1_nrm, List.length_ofFn]
  rw [Real.posLog_eq_log (by rw [abs_of_pos (by positivity)]; exact one_le_pow₀ (by norm_num)),
    Real.log_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-! ## §2 A two-state example with row sums 3 (rigid, not a lane) -/

/-- `D₀ = [[2,1],[0,3]]`, `D₁ = [[0,3],[1,2]]`. -/
def D3 : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ := ![!![2, 1; 0, 3], !![0, 3; 1, 2]]

theorem D3_rowsum_DR (b : Fin 2) (i : Fin 2) : ∑ j, DR D3 b i j = 3 := by
  fin_cases b <;> fin_cases i <;> simp [DR, D3, Fin.sum_univ_two] <;> norm_num

theorem D3_rowsum (x : List (Fin 2)) (i : Fin 2) : ∑ j, Dx D3 x i j = 3 ^ x.length := by
  induction x generalizing i with
  | nil => simp [Matrix.one_apply]
  | cons b x ih =>
    rw [Dx_cons]
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ih, ← Finset.sum_mul, D3_rowsum_DR]
    simp [pow_succ, mul_comm]

theorem D3_nrm (x : List (Fin 2)) : nrm (Dx D3 x) = 2 * 3 ^ x.length := by
  rw [nrm_of_nonneg (Dx_nonneg D3 x)]
  simp_rw [D3_rowsum]
  simp

theorem D3_SC : SC D3 := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨[], by simp⟩
  · exact ⟨[0], by simp [Dx_singleton, DR, D3]⟩
  · exact ⟨[1], by simp [Dx_singleton, DR, D3]⟩
  · exact ⟨[], by simp⟩

theorem D3_gDiag : gDiag D3 = 3 := by
  apply le_antisymm
  · have : Nonempty ({w : List (Fin 2) // w ≠ []} × Fin 2) := ⟨⟨⟨[0], by simp⟩, 0⟩⟩
    refine ciSup_le fun p => ?_
    have hn : p.1.1.length ≠ 0 := by simpa [List.length_eq_zero_iff] using p.1.2
    have h1 : Dx D3 p.1.1 p.2 p.2 ≤ 3 ^ p.1.1.length := by
      rw [← D3_rowsum p.1.1 p.2]
      exact Finset.single_le_sum (f := fun j => Dx D3 p.1.1 p.2 j) (fun j _ => Dx_nonneg D3 _ _ _)
        (Finset.mem_univ _)
    calc (Dx D3 p.1.1 p.2 p.2) ^ ((p.1.1.length : ℝ)⁻¹)
        ≤ ((3 : ℝ) ^ p.1.1.length) ^ ((p.1.1.length : ℝ)⁻¹) :=
          Real.rpow_le_rpow (Dx_nonneg D3 _ _ _) h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = 3 := Real.pow_rpow_inv_natCast (by norm_num) hn
  · have h := le_ciSup (bddAbove_gDiag D3) (⟨⟨[0], by simp⟩, 1⟩ : {w : List (Fin 2) // w ≠ []} × Fin 2)
    have e : (Dx D3 [0] 1 1) ^ ((([0] : List (Fin 2)).length : ℝ)⁻¹) = 3 := by
      simp [Dx_singleton, DR, D3]
    calc (3 : ℝ) = _ := e.symm
      _ ≤ gDiag D3 := h

theorem D3_rigid : IsRigid D3 := by
  refine ⟨by rw [D3_gDiag]; norm_num, ?_⟩
  rw [D3_gDiag]
  refine tendsto_avg_affine (a := Real.log 2) fun n => ?_
  rw [bAvg]
  simp_rw [D3_nrm, List.length_ofFn]
  have h1 : 1 ≤ |(2 : ℝ) * 3 ^ n| := by
    rw [abs_of_pos (by positivity)]; nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) (n := n)]
  rw [Real.posLog_eq_log h1, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp

/-- The main theorem applies (a rigid example that is not a lane). -/
theorem ex3_heavy :
    ∃ (Ψ : List (Fin 2)) (h : ℕ) (a : Fin 2) (c : ℝ), 1 ≤ h ∧ 0 < c ∧
      ∀ ε : List (Fin 2), c * 3 ^ (heavyWord Ψ h ε).length ≤ Dx D3 (heavyWord Ψ h ε) a a := by
  have := IsRigid.heavy_family D3 D3_SC D3_rigid
  rwa [D3_gDiag] at this

/-! ## §3 A non-rigid example (`J` and `diag(2,1)`) -/

/-- `D₀ = J`, `D₁ = diag(2,1)`. -/
def DJ : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ := ![!![1, 1; 1, 1], !![2, 0; 0, 1]]

/-- `M := D₁ D₀ = [[2,2],[1,1]]`. -/
def MJ : Matrix (Fin 2) (Fin 2) ℝ := !![2, 2; 1, 1]

theorem DJ_10 : Dx DJ [1, 0] = MJ := by
  rw [Dx_cons, Dx_singleton]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [DR, DJ, MJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem MJ_sq : MJ * MJ = (3 : ℝ) • MJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [MJ, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem MJ_pow (n : ℕ) : MJ ^ (n + 1) = (3 : ℝ) ^ n • MJ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Matrix.smul_mul, MJ_sq, smul_smul, pow_succ]

theorem MJ_nrm : nrm MJ = 6 := by
  simp [nrm, MJ, Fin.sum_univ_two]; norm_num

theorem DJ_SC : SC DJ := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨[], by simp⟩
  · exact ⟨[0], by simp [Dx_singleton, DR, DJ]⟩
  · exact ⟨[0], by simp [Dx_singleton, DR, DJ]⟩
  · exact ⟨[], by simp⟩

theorem two_le_gDiag_DJ : 2 ≤ gDiag DJ := by
  have h := le_ciSup (bddAbove_gDiag DJ) (⟨⟨[1], by simp⟩, 0⟩ : {w : List (Fin 2) // w ≠ []} × Fin 2)
  have e : (Dx DJ [1] 0 0) ^ ((([1] : List (Fin 2)).length : ℝ)⁻¹) = 2 := by
    simp [Dx_singleton, DR, DJ]
  calc (2 : ℝ) = _ := e.symm
    _ ≤ gDiag DJ := h

/-- **`J` and `diag(2,1)` are not rigid** (the contrapositive of the uniform lower bound). -/
theorem exJ_not_rigid : ¬ IsRigid DJ := by
  intro hR
  set g := gDiag DJ
  have hg2 : 2 ≤ g := two_le_gDiag_DJ
  have hg0 : 0 < g := by linarith
  obtain ⟨c, hc, hlow⟩ := uniform_lower DJ DJ_SC (hR.rigidAt DJ)
  -- `‖E_{(10)^{n+1}}‖ ≤ 2 (3/4)^{n+1} · 2`
  have hbound : ∀ n : ℕ, nrm (Ex DJ g (rep [1, 0] (n + 1))) ≤ 2 * (3 / 4) ^ n := by
    intro n
    have hlen : (rep [1, 0] (n + 1)).length = 2 * (n + 1) := by rw [rep_length]; simp; ring
    rw [Ex, Dx_rep, DJ_10, MJ_pow, smul_smul, nrm_smul, MJ_nrm, hlen]
    have hg4 : (4 : ℝ) ^ (n + 1) ≤ g ^ (2 * (n + 1)) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith) _
    have hpos : (0 : ℝ) < g ^ (2 * (n + 1)) := by positivity
    rw [abs_of_pos (by positivity)]
    rw [inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ hpos]
    calc (3 : ℝ) ^ n * 6 = 2 * (3 / 4) ^ n * 4 ^ (n + 1) * (3 / 4) := by
          rw [div_pow, pow_succ]; field_simp; ring
      _ ≤ 2 * (3 / 4) ^ n * 4 ^ (n + 1) := by
          have : (0 : ℝ) ≤ 2 * (3 / 4) ^ n * 4 ^ (n + 1) := by positivity
          nlinarith
      _ ≤ 2 * (3 / 4) ^ n * g ^ (2 * (n + 1)) :=
          mul_le_mul_of_nonneg_left hg4 (by positivity)
  -- Contradiction with `(3/4)^n → 0`
  have ht : Tendsto (fun n : ℕ => 2 * ((3 : ℝ) / 4) ^ n) atTop (𝓝 (2 * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 2
  rw [mul_zero] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hc)).exists
  have := (hlow _).trans (hbound n)
  linarith

end Collatz.Arctic.NatQ5.Rigid
