/-
# Spectral radii of rigid pairs, and the equivalence of the diagonal `g` with the spectral `g` (a supplement to Appendix D, not used downstream)

The spectral definition: `g := sup_w ρ(D_w)^{1/|w|}` (spectral radius). The statement: for a rigid pair, `ρ(D_w) = g^{|w|}` for **all words** `w`.
(This is not a numbered result of the paper.)

* The spectral radius `specRad M` is Mathlib's `spectralRadius ℂ` (with values in `ℝ≥0∞`) of the real matrix `M` cast to a complex matrix.
  The matrix norm is Mathlib's `Matrix.linftyOpNormedRing` (the maximal row sum) as a local instance, and **Gelfand's formula**
  `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius` is used.
* **Spectral radii** (`specRad_Dx`): if `RigidAt D g`, then `ρ(D_w) = g^{|w|}` for all words. The uniform lower bound `uniform_lower` and
  Lemma D.2 give `‖D_w^k‖^{1/k} → g^{|w|}`.
* **Equivalence of the two definitions** (`isRigid_iff_spectral`): for a strongly connected pair, `IsRigid D` (with the diagonal `gDiag`) is equivalent to rigidity in the spectral form
  (`g > 1` and `Λ⁺ = log g` with `gSpec D := sup_{w ≠ []} ρ(D_w)^{1/|w|}`), and then `gDiag D = gSpec D`
  (`gSpec_eq_gDiag`). One direction is `(D_w)_{ii} ≤ ρ(D_w)` (`diag_le_specRad`; Gelfand and `(M^k)_{ii} ≥ (M_{ii})^k`),
  the other uses the spectral radii above and the construction of diagonal entries from the uniform lower bound (`le_gDiag_of_rigidAt`).
* **The converse** (`isRigid_of_specRad_eq`): if `gSpec > 1` and `ρ(D_w) = gSpec^{|w|}` for all words, then the pair is rigid.
-/
import CollatzProof.Arctic.Nat.RigidNorm

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra Matrix.linftyOpNormedSpace

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] [DecidableEq K]

instance completeSpace_matrix_complex : CompleteSpace (Matrix K K ℂ) := FiniteDimensional.complete ℂ _

/-! ## §1 Complexification and norms -/

/-- Cast a real matrix to a complex matrix. -/
noncomputable def cplx (M : Matrix K K ℝ) : Matrix K K ℂ := (Complex.ofRealHom).mapMatrix M

/-- The spectral radius (`spectralRadius ℂ` of the complexified matrix). -/
noncomputable def specRad (M : Matrix K K ℝ) : ENNReal := spectralRadius ℂ (cplx M)

theorem cplx_pow (M : Matrix K K ℝ) (k : ℕ) : cplx (M ^ k) = cplx M ^ k := by
  simp [cplx, map_pow]

theorem cplx_apply (M : Matrix K K ℝ) (i j : K) : cplx M i j = (M i j : ℂ) := rfl

theorem norm_cplx_eq (M : Matrix K K ℝ) :
    ‖cplx M‖ = ((Finset.univ.sup fun i => ∑ j, ‖M i j‖₊ : NNReal) : ℝ) := by
  rw [Matrix.linfty_opNorm_def]
  congr 2
  funext i
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cplx_apply, Complex.nnnorm_real]

theorem rowsum_le_norm_cplx (M : Matrix K K ℝ) (i : K) : ∑ j, |M i j| ≤ ‖cplx M‖ := by
  rw [norm_cplx_eq]
  have h := Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have h' : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ ((Finset.univ.sup fun i => ∑ j, ‖M i j‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa [NNReal.coe_sum, Real.norm_eq_abs] using h'

theorem abs_le_norm_cplx (M : Matrix K K ℝ) (i j : K) : |M i j| ≤ ‖cplx M‖ :=
  (Finset.single_le_sum (f := fun j' => |M i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
    (rowsum_le_norm_cplx M i)

theorem norm_cplx_le_nrm (M : Matrix K K ℝ) : ‖cplx M‖ ≤ nrm M := by
  rw [norm_cplx_eq]
  have h : (Finset.univ.sup fun i => ∑ j, ‖M i j‖₊ : NNReal) ≤ ⟨nrm M, nrm_nonneg M⟩ := by
    refine Finset.sup_le fun i _ => ?_
    have h : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ nrm M := by
      simp only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun i' => ∑ j, |M i' j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact (NNReal.coe_le_coe (r₁ := ∑ j, ‖M i j‖₊) (r₂ := ⟨nrm M, nrm_nonneg M⟩)).mp h
  exact NNReal.coe_le_coe.mpr h

theorem nrm_le_card_norm_cplx (M : Matrix K K ℝ) : nrm M ≤ Fintype.card K * ‖cplx M‖ := by
  unfold nrm
  calc ∑ i, ∑ j, |M i j| ≤ ∑ _i : K, ‖cplx M‖ := Finset.sum_le_sum fun i _ => rowsum_le_norm_cplx M i
    _ = Fintype.card K * ‖cplx M‖ := by simp [Finset.sum_const, nsmul_eq_mul]

/-! ## §2 Gelfand's formula and two inequalities -/

theorem specRad_tendsto (M : Matrix K K ℝ) :
    Tendsto (fun k : ℕ => ENNReal.ofReal (‖cplx M ^ k‖ ^ (1 / k : ℝ))) atTop (𝓝 (specRad M)) :=
  spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (cplx M)

theorem specRad_le_nrm (M : Matrix K K ℝ) : specRad M ≤ ENNReal.ofReal (nrm M) := by
  refine (spectralRadius_le_nnnorm (𝕜 := ℂ) (cplx M)).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  exact ENNReal.ofReal_le_ofReal (norm_cplx_le_nrm M)

theorem specRad_ne_top (M : Matrix K K ℝ) : specRad M ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (specRad_le_nrm M)

/-- If `c α^k ≤ a_k ≤ C α^k` (`c, C, α > 0`), then `a_k^{1/k} → α`. -/
theorem tendsto_root_of_sandwich {a : ℕ → ℝ} {c C α : ℝ} (hc : 0 < c) (hC : 0 < C) (hα : 0 < α)
    (hlo : ∀ k, c * α ^ k ≤ a k) (hhi : ∀ k, a k ≤ C * α ^ k) :
    Tendsto (fun k : ℕ => a k ^ (1 / k : ℝ)) atTop (𝓝 α) := by
  have hroot : ∀ {b : ℝ}, 0 < b → Tendsto (fun k : ℕ => (b * α ^ k) ^ (1 / k : ℝ)) atTop (𝓝 α) := by
    intro b hb
    have h1 : Tendsto (fun k : ℕ => b ^ (1 / k : ℝ)) atTop (𝓝 (b ^ (0 : ℝ))) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
      exact tendsto_const_nhds.rpow this (Or.inl hb.ne')
    rw [Real.rpow_zero] at h1
    have h2 := h1.mul_const α
    rw [one_mul] at h2
    refine h2.congr' (eventually_atTop.mpr ⟨1, fun k hk => ?_⟩)
    have hk' : k ≠ 0 := by omega
    show b ^ (1 / (k : ℝ)) * α = (b * α ^ k) ^ (1 / (k : ℝ))
    rw [Real.mul_rpow hb.le (pow_nonneg hα.le _), one_div, Real.pow_rpow_inv_natCast hα.le hk']
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hroot hc) (hroot hC) ?_ ?_
  · filter_upwards with k
    exact Real.rpow_le_rpow (by positivity) (hlo k) (by positivity)
  · filter_upwards with k
    exact Real.rpow_le_rpow ((by positivity : 0 ≤ c * α ^ k).trans (hlo k)) (hhi k) (by positivity)

theorem pow_diag_ge {M : Matrix K K ℝ} (hM : ∀ i j, 0 ≤ M i j) (i : K) (k : ℕ) :
    M i i ^ k ≤ (M ^ k) i i := by
  have hnn : ∀ k : ℕ, ∀ i j, 0 ≤ (M ^ k) i j := by
    intro k
    induction k with
    | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    | succ k ih =>
      intro i j; rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hM l j)
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply]
    calc M i i ^ k * M i i ≤ (M ^ k) i i * M i i := mul_le_mul_of_nonneg_right ih (hM i i)
      _ ≤ ∑ l, (M ^ k) i l * M l i :=
          Finset.single_le_sum (f := fun l => (M ^ k) i l * M l i)
            (fun l _ => mul_nonneg (hnn k i l) (hM l i)) (Finset.mem_univ i)

/-- For a non-negative matrix, `M_{ii} ≤ ρ(M)`. -/
theorem diag_le_specRad {M : Matrix K K ℝ} (hM : ∀ i j, 0 ≤ M i j) (i : K) :
    ENNReal.ofReal (M i i) ≤ specRad M := by
  refine ge_of_tendsto (specRad_tendsto M) (eventually_atTop.mpr ⟨1, fun k hk => ?_⟩)
  refine ENNReal.ofReal_le_ofReal ?_
  have hk' : k ≠ 0 := by omega
  have h1 : M i i ^ k ≤ ‖cplx M ^ k‖ := by
    rw [← cplx_pow]
    exact (pow_diag_ge hM i k).trans ((le_abs_self _).trans (abs_le_norm_cplx _ i i))
  calc M i i = (M i i ^ k) ^ (1 / k : ℝ) := by
        rw [one_div, Real.pow_rpow_inv_natCast (hM i i) hk']
    _ ≤ ‖cplx M ^ k‖ ^ (1 / k : ℝ) :=
        Real.rpow_le_rpow (pow_nonneg (hM i i) _) h1 (by positivity)

/-! ## §3 Spectral radii of products -/

variable (D : Fin 2 → Matrix K K ℕ)

/-- **Spectral radii**: for a strongly connected rigid pair, `ρ(D_w) = g^{|w|}` for all words. -/
theorem specRad_Dx (hSC : SC D) {g : ℝ} (hR : RigidAt D g) (w : List (Fin 2)) :
    specRad (Dx D w) = ENNReal.ofReal (g ^ w.length) := by
  have hK := nonempty_of_rigidAt D hR
  have hg0 : 0 < g := by linarith [hR.one_lt]
  obtain ⟨c, hc, hlow⟩ := uniform_lower_Dx D hSC hR
  obtain ⟨L, hL⟩ := entry_bound D hSC hR.one_lt.le hR.diag_le
  have hcard : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  set U : ℝ := (Fintype.card K : ℝ) ^ 2 * g ^ L
  have hU : 0 < U := by positivity
  set α := g ^ w.length
  have hα : 0 < α := pow_pos hg0 _
  have hlo : ∀ k : ℕ, (c / Fintype.card K) * α ^ k ≤ ‖cplx (Dx D w) ^ k‖ := by
    intro k
    rw [← cplx_pow, ← Dx_rep]
    have h1 := hlow (rep w k)
    rw [rep_length] at h1
    have h2 := nrm_le_card_norm_cplx (Dx D (rep w k))
    have e : α ^ k = g ^ (k * w.length) := by rw [← pow_mul, mul_comm]
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hcard]
    linarith
  have hhi : ∀ k : ℕ, ‖cplx (Dx D w) ^ k‖ ≤ U * α ^ k := by
    intro k
    rw [← cplx_pow, ← Dx_rep]
    refine (norm_cplx_le_nrm _).trans ?_
    have h1 : nrm (Dx D (rep w k)) ≤ (Fintype.card K : ℝ) ^ 2 * g ^ ((rep w k).length + L) :=
      nrm_le_of_entry_le fun i j => by rw [abs_of_nonneg (Dx_nonneg D _ i j)]; exact hL _ i j
    refine h1.trans (le_of_eq ?_)
    rw [rep_length, pow_add, ← pow_mul]
    simp only [U]; ring_nf
  have hT := tendsto_root_of_sandwich (by positivity) hU hα hlo hhi
  exact tendsto_nhds_unique (specRad_tendsto _) ((ENNReal.continuous_ofReal.tendsto _).comp hT)

/-! ## §4 Equivalence with the spectral `g` -/

/-- The spectral `g := sup_{w ≠ []} ρ(D_w)^{1/|w|}`. -/
noncomputable def gSpec : ℝ :=
  ⨆ p : {w : List (Fin 2) // w ≠ []}, (specRad (Dx D p.1)).toReal ^ ((p.1.length : ℝ)⁻¹)

theorem specRad_toReal_le (w : List (Fin 2)) : (specRad (Dx D w)).toReal ≤ nrm (Dx D w) :=
  ENNReal.toReal_le_of_le_ofReal (nrm_nonneg _) (specRad_le_nrm _)

theorem bddAbove_gSpec :
    BddAbove (Set.range fun p : {w : List (Fin 2) // w ≠ []} =>
      (specRad (Dx D p.1)).toReal ^ ((p.1.length : ℝ)⁻¹)) := by
  refine ⟨Wd D, ?_⟩
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨b, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  have hn : (b :: w').length ≠ 0 := by simp
  have h1 : (specRad (Dx D (b :: w'))).toReal ≤ Wd D ^ (b :: w').length := by
    have := (specRad_toReal_le D _).trans (nrm_Dx_cons_le D b w')
    simpa using this
  calc (specRad (Dx D (b :: w'))).toReal ^ (((b :: w').length : ℝ)⁻¹)
      ≤ (Wd D ^ (b :: w').length) ^ (((b :: w').length : ℝ)⁻¹) :=
        Real.rpow_le_rpow ENNReal.toReal_nonneg h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = Wd D := Real.pow_rpow_inv_natCast (by linarith [one_le_Wd D]) hn

theorem diag_le_specRad_toReal (w : List (Fin 2)) (i : K) : Dx D w i i ≤ (specRad (Dx D w)).toReal := by
  have h := diag_le_specRad (Dx_nonneg D w) i
  rw [← ENNReal.ofReal_toReal (specRad_ne_top (Dx D w))] at h
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h

/-- `gDiag ≤ gSpec` (if `K` is non-empty). -/
theorem gDiag_le_gSpec [Nonempty K] : gDiag D ≤ gSpec D := by
  have : Nonempty ({w : List (Fin 2) // w ≠ []} × K) := ⟨⟨⟨[0], by simp⟩, Classical.arbitrary K⟩⟩
  refine ciSup_le fun p => ?_
  calc (Dx D p.1.1 p.2 p.2) ^ ((p.1.1.length : ℝ)⁻¹)
      ≤ (specRad (Dx D p.1.1)).toReal ^ ((p.1.1.length : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Dx_nonneg D _ _ _) (diag_le_specRad_toReal D _ _)
          (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ gSpec D := le_ciSup (bddAbove_gSpec D) p.1

/-- `ρ(D_w) ≤ gSpec^{|w|}`. -/
theorem specRad_toReal_le_gSpec (w : List (Fin 2)) (hw : w ≠ []) :
    (specRad (Dx D w)).toReal ≤ gSpec D ^ w.length := by
  have hn : w.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hw
  have h1 : (specRad (Dx D w)).toReal ^ ((w.length : ℝ)⁻¹) ≤ gSpec D :=
    le_ciSup (bddAbove_gSpec D) (⟨w, hw⟩ : {w : List (Fin 2) // w ≠ []})
  calc (specRad (Dx D w)).toReal = ((specRad (Dx D w)).toReal ^ ((w.length : ℝ)⁻¹)) ^ w.length :=
        (Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg hn).symm
    _ ≤ gSpec D ^ w.length := pow_le_pow_left₀ (Real.rpow_nonneg ENNReal.toReal_nonneg _) h1 _

/-- For a rigid pair, `gSpec = g` (from `specRad_Dx`). -/
theorem gSpec_eq_of_rigidAt (hSC : SC D) {g : ℝ} (hR : RigidAt D g) : gSpec D = g := by
  have hg0 : 0 < g := by linarith [hR.one_lt]
  have h : ∀ p : {w : List (Fin 2) // w ≠ []}, (specRad (Dx D p.1)).toReal ^ ((p.1.length : ℝ)⁻¹) = g := by
    rintro ⟨w, hw⟩
    have hn : w.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hw
    rw [specRad_Dx D hSC hR w, ENNReal.toReal_ofReal (pow_nonneg hg0.le _)]
    exact Real.pow_rpow_inv_natCast hg0.le hn
  unfold gSpec
  simp_rw [h]
  have : Nonempty {w : List (Fin 2) // w ≠ []} := ⟨⟨[0], by simp⟩⟩
  exact ciSup_const

/-- Rigidity in the spectral form gives `RigidAt D gSpec` (`(D_w)_{ii} ≤ ρ(D_w) ≤ gSpec^{|w|}`). -/
theorem rigidAt_gSpec (h1 : 1 < gSpec D)
    (hT : Tendsto (fun n : ℕ => bAvg D n / n) atTop (𝓝 (Real.log (gSpec D)))) : RigidAt D (gSpec D) := by
  refine ⟨h1, fun w i => ?_, hT⟩
  rcases eq_or_ne w [] with rfl | hw
  · simp
  · exact (diag_le_specRad_toReal D w i).trans (specRad_toReal_le_gSpec D w hw)

/-- From the uniform lower bound and strong connectivity, the diagonal entries realize the growth `g`: `g ≤ gDiag`. -/
theorem le_gDiag_of_rigidAt (hSC : SC D) {g : ℝ} (hR : RigidAt D g) : g ≤ gDiag D := by
  have hK := nonempty_of_rigidAt D hR
  have hg1 := hR.one_lt
  have hg0 : 0 < g := by linarith
  obtain ⟨c, hc, hlow⟩ := uniform_lower_Dx D hSC hR
  choose cw hcw using hSC
  set L := Finset.univ.sup fun p : K × K => (cw p.1 p.2).length
  have hcard : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  by_contra hlt
  push Not at hlt
  set G' := max (gDiag D) 1
  have hG'1 : 1 ≤ G' := le_max_right _ _
  have hG' : G' < g := max_lt hlt hg1
  -- For each `n`, `c' g^n ≤ G'^{n+L}`
  have hkey : ∀ n : ℕ, c / (Fintype.card K) ^ 2 * g ^ n ≤ G' ^ (n + L) := by
    intro n
    set x : List (Fin 2) := List.replicate n 0
    have hxl : x.length = n := by simp [x]
    -- The largest entry
    obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (K × K))
      (fun p => Dx D x p.1 p.2) ⟨(Classical.arbitrary K, Classical.arbitrary K), Finset.mem_univ _⟩
    have hent : c / (Fintype.card K) ^ 2 * g ^ n ≤ Dx D x i j := by
      have h1 := hlow x
      rw [hxl] at h1
      have h2 : nrm (Dx D x) ≤ (Fintype.card K : ℝ) ^ 2 * Dx D x i j :=
        nrm_le_of_entry_le fun a b => by
          rw [abs_of_nonneg (Dx_nonneg D x a b)]; exact hmax (a, b) (Finset.mem_univ _)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
    -- A closing path
    have hdiag : Dx D x i j ≤ Dx D (x ++ cw j i) i i := by
      rw [Dx_append, Matrix.mul_apply]
      calc Dx D x i j ≤ Dx D x i j * Dx D (cw j i) j i :=
            le_mul_of_one_le_right (Dx_nonneg D x i j) (hcw j i)
        _ ≤ ∑ k, Dx D x i k * Dx D (cw j i) k i :=
            Finset.single_le_sum (f := fun k => Dx D x i k * Dx D (cw j i) k i)
              (fun k _ => mul_nonneg (Dx_nonneg D x i k) (Dx_nonneg D _ k i)) (Finset.mem_univ j)
    have hcl : (cw j i).length ≤ L :=
      Finset.le_sup (f := fun p : K × K => (cw p.1 p.2).length) (Finset.mem_univ (j, i))
    have hG : Dx D (x ++ cw j i) i i ≤ G' ^ (n + L) := by
      calc Dx D (x ++ cw j i) i i ≤ gDiag D ^ (x ++ cw j i).length := diag_le_gDiag D _ i
        _ ≤ G' ^ (x ++ cw j i).length := pow_le_pow_left₀ (gDiag_nonneg D) (le_max_left _ _) _
        _ ≤ G' ^ (n + L) := by
            rw [List.length_append, hxl]
            exact pow_le_pow_right₀ hG'1 (Nat.add_le_add_left hcl _)
    linarith
  -- `(g/G')^n` is unbounded
  have hratio : 1 < g / G' := by rw [one_lt_div (by linarith)]; exact hG'
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (G' ^ L / (c / (Fintype.card K) ^ 2)) hratio
  have h1 := hkey n
  have hc' : 0 < c / (Fintype.card K : ℝ) ^ 2 := by positivity
  have hG'0 : 0 < G' := by linarith
  rw [div_pow, lt_div_iff₀ (pow_pos hG'0 n), div_mul_eq_mul_div, div_lt_iff₀ hc'] at hn
  rw [pow_add] at h1
  nlinarith [pow_pos hG'0 n, pow_pos hG'0 L]

/-- For a rigid pair, `gSpec = gDiag`. -/
theorem gSpec_eq_gDiag (hSC : SC D) (hR : IsRigid D) : gSpec D = gDiag D :=
  gSpec_eq_of_rigidAt D hSC (hR.rigidAt D)

/-- **Equivalence of the two definitions**: for a strongly connected pair, rigidity `IsRigid` written with the diagonal `gDiag` is equivalent to rigidity
written with the spectral `g := sup_{w ≠ []} ρ(D_w)^{1/|w|}` (`g > 1` and `Λ⁺ = log g`). -/
theorem isRigid_iff_spectral (hSC : SC D) :
    IsRigid D ↔ 1 < gSpec D ∧ Tendsto (fun n : ℕ => bAvg D n / n) atTop (𝓝 (Real.log (gSpec D))) := by
  constructor
  · intro hR
    rw [gSpec_eq_gDiag D hSC hR]
    exact hR
  · rintro ⟨h1, hT⟩
    have hR := rigidAt_gSpec D h1 hT
    have hK := nonempty_of_rigidAt D hR
    have he : gDiag D = gSpec D := le_antisymm (gDiag_le_gSpec D) (le_gDiag_of_rigidAt D hSC hR)
    rw [IsRigid, he]
    exact ⟨h1, hT⟩

/-- **The converse**: if the pair is strongly connected, `g := gSpec D > 1` and `ρ(D_w) = g^{|w|}` for all words, then the pair is rigid. -/
theorem isRigid_of_specRad_eq (hSC : SC D) (h1 : 1 < gSpec D)
    (h : ∀ w : List (Fin 2), specRad (Dx D w) = ENNReal.ofReal (gSpec D ^ w.length)) : IsRigid D := by
  have hg0 : 0 < gSpec D := by linarith
  have hdiag : ∀ (w : List (Fin 2)) (i : K), Dx D w i i ≤ gSpec D ^ w.length := by
    intro w i
    rcases eq_or_ne w [] with rfl | hw
    · simp
    · exact (diag_le_specRad_toReal D w i).trans (specRad_toReal_le_gSpec D w hw)
  have hUB : ∃ c : ℝ, 0 < c ∧ ∀ x, c * gSpec D ^ x.length ≤ nrm (Dx D x) := by
    refine ⟨1, one_pos, fun x => ?_⟩
    have := specRad_toReal_le D x
    rw [h x, ENNReal.toReal_ofReal (pow_nonneg hg0.le _)] at this
    linarith
  have hR := (rigidAt_iff_uniform_lower D hSC h1 hdiag).mpr hUB
  exact (isRigid_iff_spectral D hSC).mpr ⟨h1, hR.tendsto⟩

end Collatz.Arctic.NatQ5.Rigid
