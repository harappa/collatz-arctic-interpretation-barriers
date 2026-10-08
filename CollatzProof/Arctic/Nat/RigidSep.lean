/-
# Proposition D.5: an exact product over a separating word, and uniformly heavy families of words

The content of Proposition D.5 and its proof:
* The separating word: with `γ(ω) := P E_ω P`, `γ(ω₁ Ψ ω₂) = γ(ω₁) γ(ω₂)` over the separating word `Ψ` (with no error).
* The heavy family: every word `ω := π_{ε₁} ⋯ π_{ε_r} Ψ`, a free sequence of `π_ε := (Ψ ε)^h`, satisfies `(D_ω)_{aa} ≥ (P_{aa}/2) g^{|ω|}`.

**Difference from an earlier argument**: there `Ψ := χ^{N'}` (with `E_χ = P + R`, `PR = RP = 0`, `ρ(R) < 1`); here
`Ψ := χ` is just a word with `‖E_χ - P‖` small (`exists_word_near`). The norm of `γ(ω₁ χ ω₂) - γ(ω₁)γ(ω₂) = P E_{ω₁}(E_χ - P)E_{ω₂} P`
is smaller than the minimal distance `d_H` of two distinct elements of `H_P`, and both sides lie in `H_P`, so they are equal. Hence neither the continuity of eigenvalues,
nor a spectral decomposition, nor `R` is needed. Instead of the order of `H_P`, `h` is an `h ≥ 1` with "`A^h = P` for all elements" (`HP_pow_eq`).

The conclusion of the main theorem (`heavy_family`) has the form of Proposition D.5 (the form of `ω`, `|ω| = r h(|Ψ|+1) + |Ψ|`, `a`, the constant `P_{aa}/2`).
Section 11 (Corollary 11.4, for Corollary 10.9) uses only this conclusion.
-/
import CollatzProof.Arctic.Nat.RigidIdem

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix Filter Topology Set

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] [DecidableEq K]

/-! ## §1 The form of the words -/

/-- The piece `π_e := (Ψ e)^h`. -/
def piBlock (Ψ : List (Fin 2)) (h : ℕ) (e : Fin 2) : List (Fin 2) := (List.replicate h (Ψ ++ [e])).flatten

/-- `ω(ε) := π_{ε₁} ⋯ π_{ε_r} Ψ`. -/
def heavyWord (Ψ : List (Fin 2)) (h : ℕ) (ε : List (Fin 2)) : List (Fin 2) :=
  (ε.map (piBlock Ψ h)).flatten ++ Ψ

theorem piBlock_length (Ψ : List (Fin 2)) (h : ℕ) (e : Fin 2) :
    (piBlock Ψ h e).length = h * (Ψ.length + 1) := by
  induction h with
  | zero => simp [piBlock]
  | succ h ih =>
    simp only [piBlock, List.replicate_succ, List.flatten_cons, List.length_append] at ih ⊢
    rw [ih]; simp; ring

/-- `|ω| = r h (|Ψ| + 1) + |Ψ|`. -/
theorem heavyWord_length (Ψ : List (Fin 2)) (h : ℕ) (ε : List (Fin 2)) :
    (heavyWord Ψ h ε).length = ε.length * (h * (Ψ.length + 1)) + Ψ.length := by
  induction ε with
  | nil => simp [heavyWord]
  | cons e ε ih =>
    simp only [heavyWord, List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      piBlock_length] at ih ⊢
    rw [add_mul, one_mul]
    linarith

theorem replicate_flatten_append (u v : List (Fin 2)) (h : ℕ) :
    (List.replicate h (u ++ v)).flatten ++ u = u ++ (List.replicate h (v ++ u)).flatten := by
  induction h with
  | zero => simp
  | succ h ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.append_assoc]
    rw [ih]

/-- Regrouping the pieces: `(Ψe₁)^h ⋯ (Ψe_r)^h Ψ = Ψ (e₁Ψ)^h ⋯ (e_rΨ)^h`. -/
theorem heavyWord_eq (Ψ : List (Fin 2)) (h : ℕ) (ε : List (Fin 2)) :
    heavyWord Ψ h ε = Ψ ++ (ε.map fun e => (List.replicate h ([e] ++ Ψ)).flatten).flatten := by
  induction ε with
  | nil => simp [heavyWord]
  | cons e ε ih =>
    simp only [heavyWord, List.map_cons, List.flatten_cons, List.append_assoc] at ih ⊢
    rw [ih, ← List.append_assoc, piBlock, replicate_flatten_append, List.append_assoc]

/-- If `r ≥ 1` and `h ≥ 1`, then `ω = Ψ m Ψ` for some `m`. -/
theorem heavyWord_sandwich (Ψ : List (Fin 2)) {h : ℕ} (hh : 1 ≤ h) (e : Fin 2) (ε : List (Fin 2)) :
    ∃ m, heavyWord Ψ h (e :: ε) = Ψ ++ m ++ Ψ := by
  obtain ⟨h', rfl⟩ := Nat.exists_eq_add_of_le' hh
  refine ⟨[e] ++ (List.replicate h' (Ψ ++ [e])).flatten ++ (ε.map (piBlock Ψ (h' + 1))).flatten, ?_⟩
  simp only [heavyWord, List.map_cons, List.flatten_cons, piBlock, List.replicate_succ,
    List.append_assoc]

/-! ## §2 The separating word and the heavy family -/

variable (D : Fin 2 → Matrix K K ℕ)

/-- `γ(ω) := P E_ω P`. -/
noncomputable def gam (P : Matrix K K ℝ) (g : ℝ) (ω : List (Fin 2)) : Matrix K K ℝ := P * Ex D g ω * P

theorem nrm_mul5_le (A B C E F : Matrix K K ℝ) :
    nrm (A * B * C * E * F) ≤ nrm A * nrm B * nrm C * nrm E * nrm F := by
  have h1 := nrm_mul_le (A * B * C * E) F
  have h2 := nrm_mul_le (A * B * C) E
  have h3 := nrm_mul_le (A * B) C
  have h4 := nrm_mul_le A B
  have nF := nrm_nonneg F
  have nE := nrm_nonneg E
  have nC := nrm_nonneg C
  calc nrm (A * B * C * E * F) ≤ nrm (A * B * C * E) * nrm F := h1
    _ ≤ nrm (A * B * C) * nrm E * nrm F := mul_le_mul_of_nonneg_right h2 nF
    _ ≤ nrm (A * B) * nrm C * nrm E * nrm F :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 nE) nF
    _ ≤ nrm A * nrm B * nrm C * nrm E * nrm F :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 nC) nE) nF

/-- The internal form of the main theorem, combining the separating word and the heavy family (Proposition D.5). -/
theorem sep_and_heavy (hSC : SC D) {g : ℝ} (hR : RigidAt D g) :
    ∃ (P : Matrix K K ℝ) (Ψ : List (Fin 2)) (h : ℕ) (a : K),
      P ∈ Sbar D g ∧ P * P = P ∧ (∀ Y ∈ Sbar D g, P.rank ≤ Y.rank) ∧ (HP P (Sbar D g)).Finite ∧
      1 ≤ h ∧ (∀ A ∈ HP P (Sbar D g), A ^ h = P) ∧ 0 < P a a ∧
      (∀ ω₁ ω₂, gam D P g (ω₁ ++ Ψ ++ ω₂) = gam D P g ω₁ * gam D P g ω₂) ∧
      (∀ ε, gam D P g (heavyWord Ψ h ε) = P) ∧
      (∀ ε, nrm (Ex D g (heavyWord Ψ h ε) - P) ≤ P a a / 2) := by
  classical
  have hg0 : 0 < g := by linarith [hR.one_lt]
  obtain ⟨L, hL⟩ := Ex_entry_bound D hSC hR.one_lt.le hR.diag_le
  set S := Sbar D g
  have hSc : IsCompact S := Sbar_isCompact hg0.le hL
  have hSm : ∀ Y ∈ S, ∀ Z ∈ S, Y * Z ∈ S := fun Y hY Z hZ => Sbar_mul_mem hY hZ
  have hS0 : ∀ Y ∈ S, ∀ i j, 0 ≤ Y i j := Sbar_nonneg hg0.le
  -- The bound `CS ≥ 1` on the norms on `S̄`
  set CS : ℝ := max 1 ((Fintype.card K : ℝ) ^ 2 * g ^ L)
  have hCS1 : 1 ≤ CS := le_max_left _ _
  have hCS : ∀ Y ∈ S, nrm Y ≤ CS := by
    intro Y hY
    refine (nrm_le_of_entry_le fun i j => ?_).trans (le_max_right _ _)
    rw [abs_of_nonneg (hS0 Y hY i j)]
    exact Sbar_entry_le hL Y hY i j
  obtain ⟨P, hPS, hPP, hPmin, hP0⟩ := exists_minRank_idem D hSC hR
  obtain ⟨a, ha⟩ := exists_diag_pos (hS0 P hPS) hPP hP0
  have hfin := HP_finite hSc hSm hS0 hPS hPP hPmin
  obtain ⟨h, hh1, hpow⟩ := HP_pow_eq hSc hSm hS0 hPS hPP hPmin
  obtain ⟨dH, hdH, hdisc⟩ := HP_discrete hSc hSm hS0 hPS hPP hPmin
  -- The separating word
  set ε0 : ℝ := min 1 (min (dH / (2 * CS ^ 4)) (P a a / (6 * CS ^ 2)))
  have hε0 : 0 < ε0 := lt_min one_pos (lt_min (by positivity) (by positivity))
  obtain ⟨Ψ, hΨ⟩ := exists_word_near (D := D) hPS hε0
  set Δ := Ex D g Ψ - P
  have hΔ1 : nrm Δ ≤ 1 := hΨ.le.trans (min_le_left _ _)
  have hΔd : CS ^ 4 * nrm Δ < dH := by
    have h1 : nrm Δ < dH / (2 * CS ^ 4) := hΨ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hC4 : 0 < CS ^ 4 := by positivity
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hΔa : 3 * CS ^ 2 * nrm Δ ≤ P a a / 2 := by
    have h1 : nrm Δ ≤ P a a / (6 * CS ^ 2) := hΨ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hgam_mem : ∀ ω, gam D P g ω ∈ HP P S := fun ω => ⟨Ex D g ω, Ex_mem_Sbar ω, rfl⟩
  -- The separating word: `γ(ω₁ Ψ ω₂) = γ(ω₁) γ(ω₂)`
  have hsep : ∀ ω₁ ω₂, gam D P g (ω₁ ++ Ψ ++ ω₂) = gam D P g ω₁ * gam D P g ω₂ := by
    intro ω₁ ω₂
    have hmem2 : gam D P g ω₁ * gam D P g ω₂ ∈ HP P S :=
      HP_mul_mem hSm hPS hPP (hgam_mem ω₁) (hgam_mem ω₂)
    refine hdisc _ (hgam_mem _) _ hmem2 ?_
    have e : gam D P g (ω₁ ++ Ψ ++ ω₂) - gam D P g ω₁ * gam D P g ω₂ =
        P * Ex D g ω₁ * Δ * Ex D g ω₂ * P := by
      simp only [gam, Ex_append, Δ]
      have : P * Ex D g ω₁ * P * (P * Ex D g ω₂ * P) = P * Ex D g ω₁ * P * Ex D g ω₂ * P := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc P P, hPP]
      rw [this]
      noncomm_ring
    rw [e]
    calc nrm (P * Ex D g ω₁ * Δ * Ex D g ω₂ * P)
        ≤ nrm P * nrm (Ex D g ω₁) * nrm Δ * nrm (Ex D g ω₂) * nrm P := nrm_mul5_le _ _ _ _ _
      _ ≤ CS * CS * nrm Δ * CS * CS := by
          have h1 := hCS P hPS
          have h2 := hCS _ (Ex_mem_Sbar (D := D) (g := g) ω₁)
          have h3 := hCS _ (Ex_mem_Sbar (D := D) (g := g) ω₂)
          have n1 := nrm_nonneg P
          have n2 := nrm_nonneg (Ex D g ω₁)
          have n3 := nrm_nonneg (Ex D g ω₂)
          have n4 := nrm_nonneg Δ
          gcongr
      _ = CS ^ 4 * nrm Δ := by ring
      _ < dH := hΔd
  have hgam_nil : gam D P g [] = P := by simp [gam, hPP]
  have hPgam : ∀ ω, P * gam D P g ω = gam D P g ω := fun ω => HP_left_P hPP (hgam_mem ω)
  have hgamP : ∀ ω, gam D P g ω * P = gam D P g ω := fun ω => HP_right_P hPP (hgam_mem ω)
  have hpre : ∀ w, gam D P g (Ψ ++ w) = gam D P g w := by
    intro w
    have := hsep [] w
    rw [List.nil_append, hgam_nil, hPgam] at this
    exact this
  have hpost : ∀ w, gam D P g (w ++ Ψ) = gam D P g w := by
    intro w
    have := hsep w []
    rw [List.append_nil, hgam_nil, hgamP] at this
    exact this
  -- The product of the pieces
  have hblk : ∀ (e : Fin 2) (k : ℕ) (w : List (Fin 2)),
      gam D P g ((List.replicate k ([e] ++ Ψ)).flatten ++ w) = gam D P g [e] ^ k * gam D P g w := by
    intro e k w
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc, hsep, ih, pow_succ',
        Matrix.mul_assoc]
  have hblocks : ∀ (ε w : List (Fin 2)),
      gam D P g ((ε.map fun e => (List.replicate h ([e] ++ Ψ)).flatten).flatten ++ w) = gam D P g w := by
    intro ε
    induction ε with
    | nil => intro w; simp
    | cons e ε ih =>
      intro w
      rw [List.map_cons, List.flatten_cons, List.append_assoc, hblk, ih, hpow _ (hgam_mem [e]), hPgam]
  have hγ : ∀ ε, gam D P g (heavyWord Ψ h ε) = P := by
    intro ε
    rw [heavyWord_eq, hpre]
    have := hblocks ε []
    rw [List.append_nil, hgam_nil] at this
    exact this
  -- The norm bound for the heavy family
  have hnear : ∀ ε, nrm (Ex D g (heavyWord Ψ h ε) - P) ≤ P a a / 2 := by
    intro ε
    cases ε with
    | nil =>
      have : heavyWord Ψ h [] = Ψ := by simp [heavyWord]
      rw [this]
      have : nrm Δ ≤ 3 * CS ^ 2 * nrm Δ := by
        have : (1 : ℝ) ≤ 3 * CS ^ 2 := by nlinarith
        nlinarith [nrm_nonneg Δ]
      linarith
    | cons e ε =>
      obtain ⟨m, hm⟩ := heavyWord_sandwich Ψ hh1 e ε
      have hγm : gam D P g m = P := by
        have := hγ (e :: ε)
        rw [hm, List.append_assoc, hpre, hpost] at this
        exact this
      rw [hm, Ex_append, Ex_append]
      have e1 : Ex D g Ψ * Ex D g m * Ex D g Ψ - P =
          Δ * Ex D g m * P + P * Ex D g m * Δ + Δ * Ex D g m * Δ := by
        have hEΨ : Ex D g Ψ = P + Δ := by simp [Δ]
        have hPmP : P * Ex D g m * P = P := hγm
        rw [hEΨ]
        calc (P + Δ) * Ex D g m * (P + Δ) - P
            = P * Ex D g m * P - P + Δ * Ex D g m * P + P * Ex D g m * Δ + Δ * Ex D g m * Δ := by
              noncomm_ring
          _ = _ := by rw [hPmP, sub_self, zero_add]
      rw [e1]
      have hm' := hCS _ (Ex_mem_Sbar (D := D) (g := g) m)
      have hP' := hCS P hPS
      have n1 := nrm_nonneg (Ex D g m)
      have n2 := nrm_nonneg P
      have n3 := nrm_nonneg Δ
      have t1 : nrm (Δ * Ex D g m * P) ≤ nrm Δ * CS * CS :=
        ((nrm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (nrm_mul_le _ _) n2)).trans
          (by gcongr)
      have t2 : nrm (P * Ex D g m * Δ) ≤ CS * CS * nrm Δ :=
        ((nrm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (nrm_mul_le _ _) n3)).trans
          (by gcongr)
      have t3 : nrm (Δ * Ex D g m * Δ) ≤ nrm Δ * CS * nrm Δ :=
        ((nrm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (nrm_mul_le _ _) n3)).trans
          (by gcongr)
      have s1 := nrm_add_le (Δ * Ex D g m * P + P * Ex D g m * Δ) (Δ * Ex D g m * Δ)
      have s2 := nrm_add_le (Δ * Ex D g m * P) (P * Ex D g m * Δ)
      have t4 : nrm Δ * CS * nrm Δ ≤ CS * CS * nrm Δ := by
        have : nrm Δ * (CS * nrm Δ) ≤ CS * (CS * nrm Δ) :=
          mul_le_mul_of_nonneg_right (hΔ1.trans hCS1) (mul_nonneg (zero_le_one.trans hCS1) n3)
        linarith [mul_assoc (nrm Δ) CS (nrm Δ), mul_assoc CS CS (nrm Δ)]
      have t5 : nrm Δ * CS * CS + CS * CS * nrm Δ + CS * CS * nrm Δ = 3 * CS ^ 2 * nrm Δ := by ring
      linarith
  exact ⟨P, Ψ, h, a, hPS, hPP, hPmin, hfin, hh1, hpow, ha, hsep, hγ, hnear⟩

/-- **Proposition D.5 (uniformly heavy families of words)**: a strongly connected rigid pair has a word `Ψ`, `h ≥ 1`, a state `a` and `c > 0` such that
every word `ω := π_{ε₁} ⋯ π_{ε_r} Ψ`, a free sequence of `π_ε := (Ψ ε)^h`, satisfies `(D_ω)_{aa} ≥ c g^{|ω|}`. -/
theorem heavy_family (hSC : SC D) {g : ℝ} (hR : RigidAt D g) :
    ∃ (Ψ : List (Fin 2)) (h : ℕ) (a : K) (c : ℝ), 1 ≤ h ∧ 0 < c ∧
      ∀ ε : List (Fin 2), c * g ^ (heavyWord Ψ h ε).length ≤ Dx D (heavyWord Ψ h ε) a a := by
  obtain ⟨P, Ψ, h, a, -, -, -, -, hh1, -, ha, -, -, hnear⟩ := sep_and_heavy D hSC hR
  have hg0 : 0 < g := by linarith [hR.one_lt]
  refine ⟨Ψ, h, a, P a a / 2, hh1, by positivity, fun ε => ?_⟩
  set ω := heavyWord Ψ h ε
  have h1 : P a a / 2 ≤ Ex D g ω a a := by
    have h2 : |(Ex D g ω - P) a a| ≤ P a a / 2 := (abs_le_nrm _ a a).trans (hnear ε)
    rw [Matrix.sub_apply, abs_le] at h2
    linarith
  rw [Dx_eq_smul_Ex D hg0.ne' ω, Matrix.smul_apply, smul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left h1 (pow_nonneg hg0.le _)

/-- Proposition D.5 with `g := gDiag D`. -/
theorem IsRigid.heavy_family (hSC : SC D) (hR : IsRigid D) :
    ∃ (Ψ : List (Fin 2)) (h : ℕ) (a : K) (c : ℝ), 1 ≤ h ∧ 0 < c ∧
      ∀ ε : List (Fin 2), c * gDiag D ^ (heavyWord Ψ h ε).length ≤ Dx D (heavyWord Ψ h ε) a a :=
  Collatz.Arctic.NatQ5.Rigid.heavy_family D hSC (hR.rigidAt D)

end Collatz.Arctic.NatQ5.Rigid
