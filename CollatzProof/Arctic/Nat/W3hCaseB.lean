/-
# Case B does not occur (Proposition 12.31 of the paper, `d(conf_lo) ≤ 0`)

`CaseBStmt`: every setting of an automaton whose value does not increase along steps of `T` on `3 ∤ n` has a configuration in `𝔎` whose coefficients of positive degree are all 0.
By contradiction: if every configuration has a positive coefficient of positive degree, take the configuration `conf_lo` with the lexicographically minimal `(d_lo, C_lo)`, choose the constants
in the order of quantifiers (Step 1 of the proof of Proposition 12.31), and construct a starting point `x₀` (with configuration `conf_lo`) and an end point `x₁ = T^m x₀` with `V(x₀) < V(x₁)`.
The steps are Steps 0–8 of the proof of Proposition 12.31 of the paper.

**Order of quantifiers**: `conf_lo, d_lo, C_lo, c_*` → `c_E` (expansion), `c_B, B` (top window), `L_c` (event (c)), period `P` →
`κ := min(c_E/34, 1)`, `ε := min(C_lo κ/4, c_*/2)` → `η₀` → `J` (closeness of `Q_J`, `gap_twin`, `tail_small`, `K_r ≥ 1`) →
`M` (closeness of `C^{(M)}`) → `η₁` → `J', δ', N₀'` (`lln_items`) → `η_u := 2^{-(L_c+4)}`, `Δ := L_c + 6` →
`M_low, M_mid, N_free`, `k_T, k_E` → `k` → `σ` (four events, probability at least `c_B/4`) → `F` (class `cls b`, `F ≥ 22(|β₀|+k) + F_c`),
`n := F + K + s'`, `b := ⌊log₂ 3^A⌋ - (Δ + K)` → `u` (at least `2^{F-L_c}` good `u`, at most `5.75 η_u 2^F` bad `u`).
-/
import CollatzProof.Arctic.Nat.W3hCaseBAux

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

/-- Non-divisibility by 3 is preserved along the orbit of `T`. -/
theorem not_dvd_iter : ∀ (m x : ℕ), ¬ 3 ∣ x → ¬ 3 ∣ T^[m] x := by
  intro m
  induction m with
  | zero => intro x h; simpa using h
  | succ m ih =>
    intro x h
    rw [Function.iterate_succ_apply]
    exact ih (T x) (fun h' => h (three_dvd_of_three_dvd_T h'))

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-- **Case B does not occur** (Proposition 12.31 of the paper). -/
theorem caseB_false (hmono : AutoMono3 B) (hB : ∀ c ∈ S.Kset, ∃ d, 1 ≤ d ∧ 0 < S.coef d c.1) : False := by
  classical
  -- the lexicographic minimum
  obtain ⟨clo, hclo, dlo, Clo, cs, hdlo, -, hClo_def, hClo, hcs, hdeg, hmin⟩ := S.exists_lo hB
  -- expansion, top window, event (c)
  obtain ⟨cE, hcE, hexp⟩ := fam_expansion_lln
  obtain ⟨cB, hcB, Btop, htopw⟩ := W3b.top_window S.E
  obtain ⟨Lc, hLc⟩ := S.eventC
  have hP0 : 0 < Dfa.period (stepP B) S.P1 := Dfa.period_pos _ _
  -- κ, ε
  have hcEr : (0 : ℝ) < cE := by exact_mod_cast hcE
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min ((cE : ℝ) / 34) 1 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; exact lt_min (by positivity) one_pos
  have hκ1 : κ ≤ 1 := by rw [hκdef]; exact min_le_right _ _
  have hκc : κ ≤ (cE : ℝ) / 34 := by rw [hκdef]; exact min_le_left _ _
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (Clo * κ / 4) (cs / 2) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by positivity) (by positivity)
  have hεκ : ε ≤ Clo * κ / 4 := by rw [hεdef]; exact min_le_left _ _
  have hεc : ε ≤ cs / 2 := by rw [hεdef]; exact min_le_right _ _
  -- the precision η₀ at the starting point
  have hKt₀ := S.Ktot_nonneg clo.1
  have hCs := S.Cst_pos
  obtain ⟨η₀, hη₀def⟩ : ∃ η₀ : ℝ, η₀ = min 1 (ε / (4 * (S.Ktot clo.1 + 1) * S.Cst)) := ⟨_, rfl⟩
  have hη₀ : 0 < η₀ := by rw [hη₀def]; exact lt_min one_pos (by positivity)
  have hη₀1 : η₀ ≤ 1 := by rw [hη₀def]; exact min_le_left _ _
  have hη₀K : S.Ktot clo.1 * S.Cst * η₀ ≤ ε / 4 := by
    have h := min_le_right (1 : ℝ) (ε / (4 * (S.Ktot clo.1 + 1) * S.Cst))
    rw [← hη₀def] at h
    have h1 : S.Ktot clo.1 * S.Cst * η₀ ≤ (S.Ktot clo.1 + 1) * S.Cst * η₀ := by nlinarith
    have h2 : (S.Ktot clo.1 + 1) * S.Cst * η₀ ≤ (S.Ktot clo.1 + 1) * S.Cst * (ε / (4 * (S.Ktot clo.1 + 1) * S.Cst)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : (S.Ktot clo.1 + 1) * S.Cst * (ε / (4 * (S.Ktot clo.1 + 1) * S.Cst)) = ε / 4 := by
      field_simp
    linarith
  -- the truncation J
  obtain ⟨Ja, hJa⟩ := S.exists_J_Q (η := η₀ / 4) (by positivity)
  have hus0 := S.us_length_pos
  have hPU : PU S.us = fun w => bitsMSB S.us.length (valW 0 S.us) <:+: w := by
    funext w; simp only [PU, bitsMSB_valW_eq]
  have hMF : W3b.MissFrac (PU S.us) S.us.length (1 - 1 / 2 ^ S.us.length) := by
    rw [hPU]; exact W3b.missFrac_infix (W2a.valW_lt _) (by omega)
  have hq1 : (1 : ℚ) - 1 / 2 ^ S.us.length < 1 := by
    have : (0 : ℚ) < 1 / 2 ^ S.us.length := by positivity
    linarith
  have hq0 : (0 : ℚ) ≤ 1 - 1 / 2 ^ S.us.length := by
    have : (1 : ℚ) / 2 ^ S.us.length ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    linarith
  obtain ⟨n₁, cg, -, -, hgap⟩ := W3b.gap_twin (PU S.us) S.us.length (1 - 1 / 2 ^ S.us.length) hq0 hq1 hMF
  have hg : 1 ≤ n₁ + S.us.length := by omega
  obtain ⟨εT, hεT0, hεT⟩ : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < η₀ / 8 := by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (0 : ℝ) < η₀ / 8 by positivity)
    exact ⟨q, by exact_mod_cast h1, h2⟩
  have hcB4 : (0 : ℚ) < cB / 4 := by positivity
  obtain ⟨Jb, hJb⟩ := hgap n₁ le_rfl ((22 * (n₁ + S.us.length) * S.D.cP : ℕ) : ℚ) (S.D.dP + 1) 1 0
    (2 * S.cW' * (11 * (n₁ + S.us.length)))
    (2 * (2 * S.cW' * (11 * (n₁ + S.us.length))) + S.cW' * (2 * (11 * (n₁ + S.us.length)) + S.C0 + 3))
    (S.KT (n₁ + S.us.length)) (S.KT (n₁ + S.us.length)) (by positivity) (by norm_num) le_rfl
    (by have := S.cW'_pos; nlinarith)
    (fun R => by
      have h : ((S.KT (n₁ + S.us.length) R : ℕ) : ℚ) ≤ R := by exact_mod_cast S.KT_le (n₁ + S.us.length) R
      linarith)
    (S.KT_lin hg) εT hεT0 (cB / 4) hcB4
  -- the tail of the free bits
  obtain ⟨εF, hεF0, hεF⟩ : ∃ q : ℚ, 0 < q ∧ (q : ℝ) ≤ η₀ / 8 * ((1 / 2 ^ (Lc + 4) : ℚ) : ℝ) := by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (0 : ℝ) < η₀ / 8 * ((1 / 2 ^ (Lc + 4) : ℚ) : ℝ) by
      push_cast; positivity)
    exact ⟨q, by exact_mod_cast h1, h2.le⟩
  obtain ⟨Jc, hJc⟩ := W3b.tail_small (S.D.cP : ℚ) (by positivity) (S.D.dP + 1) 0 0 le_rfl le_rfl
    (2 * S.cW' * S.us.length) (S.cW' * (2 * S.us.length + S.C0 + 3)) (by have := S.cW'_pos; nlinarith)
    (1 - 1 / 2 ^ S.us.length) hq0 hq1 (fun _ => 0) (fun R => S.Lr S.C0 R / S.us.length)
    (fun R => by simp) (fun R => S.Lr_lin S.C0 S.us.length R (by omega)) εF hεF0
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = Ja + Jb + Jc + S.cW' * (S.C0 + 66 * (n₁ + S.us.length) + 1) := ⟨_, rfl⟩
  have hJKT : ∀ r, J < r → 1 ≤ S.KT (n₁ + S.us.length) r ∧
      11 * (n₁ + S.us.length) * (S.KT (n₁ + S.us.length) r + 2) ≤ S.Lr S.C0 r :=
    fun r hr => S.KT_spec hg (by omega)
  -- the truncation M and η₁
  obtain ⟨M₀, hM₀⟩ := S.exists_M (ε := ε / 3) (by positivity)
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = M₀ + 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by omega
  obtain ⟨Kmax, hKmaxdef⟩ : ∃ Kmax : ℝ, Kmax = S.Kmax := ⟨_, rfl⟩
  have hKmax : ∀ c ∈ S.Kset, S.Ktot c.1 ≤ Kmax := fun c hc => hKmaxdef ▸ S.Ktot_le_Kmax hc
  have hKmax0 : 0 ≤ Kmax := le_trans (S.Ktot_nonneg clo.1) (hKmax clo hclo)
  obtain ⟨η₁, hη₁def⟩ : ∃ η₁ : ℝ, η₁ = min 1 (ε / (6 * (Kmax + 1) * S.Cst)) := ⟨_, rfl⟩
  have hη₁ : 0 < η₁ := by rw [hη₁def]; exact lt_min one_pos (by positivity)
  have hη₁1 : η₁ ≤ 1 := by rw [hη₁def]; exact min_le_left _ _
  have hη₁K : Kmax * S.Cst * η₁ ≤ ε / 6 := by
    have h := min_le_right (1 : ℝ) (ε / (6 * (Kmax + 1) * S.Cst))
    rw [← hη₁def] at h
    have h1 : Kmax * S.Cst * η₁ ≤ (Kmax + 1) * S.Cst * η₁ := by nlinarith
    have h2 : (Kmax + 1) * S.Cst * η₁ ≤ (Kmax + 1) * S.Cst * (ε / (6 * (Kmax + 1) * S.Cst)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : (Kmax + 1) * S.Cst * (ε / (6 * (Kmax + 1) * S.Cst)) = ε / 6 := by
      field_simp
    linarith
  -- the law of large numbers for the windows at the end point
  obtain ⟨J', δ', hδ', N₀', hlln⟩ := S.lln_items M (η₁ / 4) (by positivity)
  have hηu : (0 : ℚ) < 1 / 2 ^ (Lc + 4) := by positivity
  obtain ⟨Mlow, hMlow⟩ := card_bad_low J' δ' (1 / 2 ^ (Lc + 4)) hδ' hηu
  obtain ⟨Mmid, hMmid⟩ := card_bad_mid J' δ' (1 / 2 ^ (Lc + 4)) hδ' hηu
  -- the law of large numbers for the intervals at the starting point
  obtain ⟨Nfree, hNfree⟩ := W3a.lln_free_famX0 (φ := fun i : S.Item => S.phi i J) J S.e_recurrent
    (fun i x v => S.abs_phi_le i J x v) (η₀ / 4) (by positivity) (1 / 2 ^ (Lc + 4)) hηu
  obtain ⟨kT, hkT⟩ := W3a.lln_terras_famX0 (φ := fun i : S.Item => S.phi i J) J S.e_recurrent
    (fun i x v => S.abs_phi_le i J x v) (η₀ / 4) (by positivity) S.β₀ (1 / 2) (cB / 4) (by norm_num) hcB4
  obtain ⟨kE, hkE⟩ := hexp S.β₀ (cB / 4) hcB4
  -- the thresholds for `k`
  obtain ⟨k3, hk3⟩ := ev_ge (((S.BJ J : ℝ) + S.Hb) * S.C0) (η₀ / 4) (by positivity)
  obtain ⟨k4, hk4⟩ := ev_ge (∑ d ∈ Finset.range dlo, S.coef d clo.1) (ε / 2) (by positivity)
  obtain ⟨k5, hk5⟩ := ev_ge (S.Ktot clo.1 * S.Cst) (ε / 4) (by positivity)
  obtain ⟨k6, hk6⟩ := ev_ge (Kmax * S.Cst) (ε / 6) (by positivity)
  obtain ⟨k7, hk7⟩ := ev_ge (Kmax * (S.Dm * ((M - 1 : ℕ) : ℝ) * (max (S.BJ M : ℝ) 1) ^ S.Dm)) (ε / 3)
    (by positivity)
  obtain ⟨k8, hk8⟩ := ev_ge (((S.BJ M : ℝ) + S.Hb) * ((2 * S.Kc + (Lc + 6) + M + S.s' : ℕ) : ℝ)) (η₁ / 2)
    (by positivity)
  obtain ⟨k9, hk9⟩ := ev_ge (2 * (Clo + ε) / cs + 1) 1 one_pos
  obtain ⟨Fc, hFcdef⟩ : ∃ Fc : ℕ, Fc = Lc + 7 + Mmid + Nfree + N₀' + M := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = Btop + kT + kE + k3 + k4 + k5 + k6 + k7 + k8 + k9 +
      (Lc + 6 + S.Kc + Mlow + N₀' + 33 * S.β₀.length + Fc + Dfa.period (stepP B) S.P1 + S.Kc + S.s') + 1 :=
    ⟨_, rfl⟩
  have hkBtop : Btop ≤ k := by omega
  have hkkT : kT ≤ k := by omega
  have hkkE : kE ≤ k := by omega
  have hkk3 : k3 ≤ k := by omega
  have hkk4 : k4 ≤ k := by omega
  have hkk5 : k5 ≤ k := by omega
  have hkk6 : k6 ≤ k := by omega
  have hkk7 : k7 ≤ k := by omega
  have hkk8 : k8 ≤ k := by omega
  have hkk9 : k9 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hJaJ : Ja ≤ J := by omega
  have hM0M : M₀ ≤ M := by omega
  -- the events for σ
  have e1 := htopw S.β₀ k hkBtop
  have e2 := hkT k hkkT S.β₀.length (S.β₀.length + k) le_rfl (by push_cast; linarith) le_rfl
  have e3 := hkE k hkkE
  have e4' := hJb S.β₀ k (Finset.range (k / (n₁ + S.us.length))) (Finset.Ioc J (34 * k))
    (fun i hi => by
      have hi' := Finset.mem_range.mp hi
      have h1 : (i + 1) * (n₁ + S.us.length) ≤ k / (n₁ + S.us.length) * (n₁ + S.us.length) :=
        Nat.mul_le_mul_right _ hi'
      have h2 := Nat.div_mul_le_self k (n₁ + S.us.length)
      omega)
    (fun R hR => by have := (Finset.mem_Ioc.mp hR).1; omega)
  have e4 := prσ_not_ge e4'
  have hpr := prσ_four S.β₀ k _ _ _ _ e1 e2 e3 e4
  obtain ⟨β', hβ', ⟨⟨⟨E1, E2⟩, E3⟩, E4⟩⟩ := exists_of_Prσ_pos S.β₀ k _ (by linarith)
  have hlenβ' : β'.length = k := length_of_mem_blockChoices hβ'
  -- the quantities of σ
  have hm8 : 8 * k ≤ (parityOf (S.β₀ ++ β')).length := by
    have := (parityOf_length_bounds (S.β₀ ++ β')).1; rw [List.length_append, hlenβ'] at this; omega
  have hm11 : (parityOf (S.β₀ ++ β')).length ≤ 11 * (S.β₀.length + k) := by
    have := (parityOf_length_bounds (S.β₀ ++ β')).2; rw [List.length_append, hlenβ'] at this; exact this
  have hAm : terrasA (parityOf (S.β₀ ++ β')) ≤ (parityOf (S.β₀ ++ β')).length := fam_terrasA_le_length _
  have h3A : 3 ^ terrasA (parityOf (S.β₀ ++ β')) ≤ 2 ^ (2 * (parityOf (S.β₀ ++ β')).length) :=
    fam_three_pow_le _ _ hAm
  have h2m : 2 ^ (parityOf (S.β₀ ++ β')).length ≤ 3 ^ terrasA (parityOf (S.β₀ ++ β')) :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)) E3
  have hA1 : 1 ≤ terrasA (parityOf (S.β₀ ++ β')) := by
    by_contra h0; push Not at h0
    have h0' : terrasA (parityOf (S.β₀ ++ β')) = 0 := by omega
    rw [h0', pow_zero] at h2m
    have : 2 ≤ 2 ^ (parityOf (S.β₀ ++ β')).length := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  -- the event (c) and the length
  obtain ⟨bc, hbc, hcount⟩ := hLc clo hclo
    ((bitsMSB S.s' (famRho S.β₀ (S.β₀ ++ β'))).map W3a.l2f ++ TwOf S.β₀ β' ++ S.y'')
  obtain ⟨F, hF1, hF2, hFcls⟩ := Setup.exists_len_cls hP0 (Dfa.cls (stepP B) S.P1 bc) (22 * (S.β₀.length + k) + Fc)
  obtain ⟨n, hn⟩ : ∃ n, n = F + S.Kc + S.s' := ⟨_, rfl⟩
  have hFn : S.Flen n = F := by unfold Flen; omega
  have hKn : S.Kc + S.s' ≤ n := by omega
  have hnF : n - S.Kc - (parityOf S.β₀).length = F := hFn
  have hK1 : 1 ≤ S.Kc := by unfold Kc; omega
  obtain ⟨b, hbdef⟩ : ∃ b, b = Nat.log 2 (3 ^ terrasA (parityOf (S.β₀ ++ β'))) - (Lc + 6 + S.Kc) := ⟨_, rfl⟩
  have hlog : 8 * k ≤ Nat.log 2 (3 ^ terrasA (parityOf (S.β₀ ++ β'))) :=
    Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_right (by norm_num) hm8) h2m)
  have hb1 : 2 ^ (b + (Lc + 6) + S.Kc) ≤ 3 ^ terrasA (parityOf (S.β₀ ++ β')) := by
    have : b + (Lc + 6) + S.Kc = Nat.log 2 (3 ^ terrasA (parityOf (S.β₀ ++ β'))) := by omega
    rw [this]; exact Nat.pow_log_le_self 2 (pow_pos (by norm_num) _).ne'
  have hb2 : 3 ^ terrasA (parityOf (S.β₀ ++ β')) < 2 ^ (b + (S.Kc + (Lc + 6) + 1)) := by
    have : b + (S.Kc + (Lc + 6) + 1) = (Nat.log 2 (3 ^ terrasA (parityOf (S.β₀ ++ β')))).succ := by omega
    rw [this]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hN0b : N₀' ≤ b := by omega
  have hN0F : N₀' ≤ F := by omega
  have hMF : M ≤ F := by omega
  have hE9 : S.E + 9 + (parityOf S.β₀).length ≤ n := by
    have : S.s' = (parityOf S.β₀).length := rfl
    have : S.Kc = S.E + 9 := rfl
    omega
  -- the numbers of bad `u`
  have hB1 := hNfree S.β₀ (S.β₀ ++ β') n S.Kc S.T0 0 F hK1 hKn S.T0_bounds.1 S.T0_bounds.2 (Nat.zero_le _)
    hnF.ge (by omega)
  rw [hnF] at hB1
  have hfreeε : ∑ r ∈ Finset.Ioc J (34 * k), S.wt r * (1 - 1 / 2 ^ S.us.length) ^ (S.Lr S.C0 r / S.us.length) ≤
      (εF : ℝ) := by
    have h := hJc (Finset.Ioc J (34 * k)) (fun R hR => by have := (Finset.mem_Ioc.mp hR).1; omega)
    simp only [Nat.cast_zero, zero_add, one_mul] at h
    have hR : ((∑ R ∈ Finset.Ioc J (34 * k), (S.D.cP : ℚ) * ((R : ℚ) + 1) ^ (S.D.dP + 1) *
        (1 - 1 / 2 ^ S.us.length) ^ (S.Lr S.C0 R / S.us.length) : ℚ) : ℝ) ≤ εF := by exact_mod_cast h
    refine le_trans (le_of_eq ?_) hR
    push_cast
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [S.wt_eq]
  have hB2 := S.free_markov F (Finset.Ioc J (34 * k)) (fun r => S.Lr S.C0 r) (εF := εF) (θ := η₀ / 8)
    (by positivity) hfreeε
  have hB3 := hMmid S.β₀ (S.β₀ ++ β') n S.Kc S.T0 hKn (by rw [hnF]; omega)
  rw [hnF] at hB3
  have hB4 := hMlow S.β₀ (S.β₀ ++ β') n S.Kc S.T0 b (Lc + 6) hKn (by omega) hb1
  rw [hnF] at hB4
  have hTV : (2 : ℚ) ^ ((parityOf S.β₀).length + 2) * ((3 ^ terrasA (parityOf (S.β₀ ++ β')) : ℕ) : ℚ) / 2 ^ n ≤
      1 / 2 ^ (Lc + 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h1 : 2 ^ ((parityOf S.β₀).length + 2) * 3 ^ terrasA (parityOf (S.β₀ ++ β')) * 2 ^ (Lc + 4) ≤ 2 ^ n := by
      calc 2 ^ ((parityOf S.β₀).length + 2) * 3 ^ terrasA (parityOf (S.β₀ ++ β')) * 2 ^ (Lc + 4)
          ≤ 2 ^ ((parityOf S.β₀).length + 2) * 2 ^ (2 * (parityOf (S.β₀ ++ β')).length) * 2 ^ (Lc + 4) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3A)
        _ = 2 ^ ((parityOf S.β₀).length + 2 + 2 * (parityOf (S.β₀ ++ β')).length + (Lc + 4)) := by
            rw [← pow_add, ← pow_add]
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by
            have : S.s' = (parityOf S.β₀).length := rfl
            omega)
    exact_mod_cast h1
  -- a good `u`
  have hG := hcount F (by omega) hFcls
  obtain ⟨u, huG, hu1, hu2, hu3, hu4⟩ := exists_avoid' (x := (2 : ℝ) ^ (F - Lc)) (by exact_mod_cast hG)
    hB1 hB2 hB3 hB4 (bad_sum F Lc (by omega) hη₀ (by push_cast at hεF; exact hεF) hTV)
  clear hG
  -- the properties of `u`
  have huF : u < 2 ^ F := Finset.mem_range.mp (Finset.mem_filter.mp huG).1
  have huFold : ((bitsMSB F u).map W3a.l2f).foldl (stepF B) S.P1 = bc := (Finset.mem_filter.mp huG).2
  have hu : u < 2 ^ S.Flen n := by rw [hFn]; exact huF
  have hU1 := not_not.mp (fun h => hu1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huF, h⟩))
  have hU2 := not_lt.mp (fun h => hu2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huF, h⟩))
  have hU3 := not_not.mp (fun h => hu3 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huF, h⟩))
  have hU4 := not_not.mp (fun h => hu4 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huF, h⟩))
  -- the configuration of the starting point, and non-divisibility by 3
  have hconf : S.conf (S.mid0 (S.β₀ ++ β') n u) = clo := by
    rw [S.conf_mid0_split, hFn, huFold]; exact hbc
  have hx0w := S.binWord_x0 β' hKn hu
  have hx01 : 1 ≤ famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u := by
    have ht := fam_T_pos (β₀ := S.β₀) (β := S.β₀ ++ β') (n := n) (K := S.Kc) u S.T0_pos
    have h2 : 1 ≤ 2 ^ (parityOf (S.β₀ ++ β')).length * famT S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u :=
      le_trans (by norm_num) (Nat.mul_le_mul Nat.one_le_two_pow ht)
    unfold famX0; omega
  have hx03 : ¬ 3 ∣ famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u := by
    have h := S.not_dvd_of_conf _ (hconf ▸ hclo)
    rwa [← hx0w, valW_binWord _ hx01] at h
  have hiter := fam_iter S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u
  have hx13 : ¬ 3 ∣ famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u := by
    rw [hiter]; exact not_dvd_iter _ _ hx03
  -- lengths
  obtain ⟨hN0eq, -⟩ := S.N0_ge β' hKn hu
  have hN0le : (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length ≤ 34 * k := by
    rw [hN0eq]; omega
  have hN0ge : 8 * k ≤ (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by
    rw [hN0eq]; omega
  have hexpand := fam_lenT_expand S.β₀ (S.β₀ ++ β') (n := n) (K := S.Kc) (τ := S.T0) (u := u) ⌈cE * k⌉₊ hK1 hKn
    S.T0_bounds.1 S.T0_bounds.2 (by rw [hnF]; exact huF) E3
  rw [← W3a.length_binWord, ← W3a.length_binWord] at hexpand
  -- the law of large numbers for the Terras part at the starting point
  have hFam : W3a.FamOK S.β₀ n S.Kc S.T0 u := ⟨hK1, hKn, S.T0_bounds.1, S.T0_bounds.2, by rw [hnF]; exact huF⟩
  have hterm := E2 n S.Kc S.T0 u hFam
  have hA_ : W3a.terA (S.β₀ ++ β') n (S.β₀.length + k) = n - 1 := by
    unfold W3a.terA; rw [← hlenβ', blockEnd_full]; omega
  have hB_ : W3a.terB (S.β₀ ++ β') n S.β₀.length = n - 1 + ((parityOf (S.β₀ ++ β')).length - S.s') := by
    unfold W3a.terB; rw [blockEnd_b0]; rfl
  rw [hA_, hB_, Nat.add_sub_cancel_left] at hterm
  -- the upper bound at the starting point
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hV0 := S.x0_upper β' n u J hKn hu (θF := η₀ / 8) (εT := (εT : ℝ)) hconf hdeg hClo_def.symm hdlo hε0 hη₀ hη₀1
    (by rw [hFn]; intro i x hx p h1 h2; exact hU1 i x hx p h1 h2)
    (fun i x hx p h1 h2 => hterm i x hx p h1 h2)
    (fun i => by
      have ht := S.tail_x0 β' (S.KT (n₁ + S.us.length)) hKn hu hg hJKT hN0le i
      refine le_trans ht ?_
      rw [hFn, hlenβ']
      have hgs := S.runMiss_cast (Finset.range (k / (n₁ + S.us.length))) (Finset.Ioc J (34 * k)) (n₁ + S.us.length)
        (fun j r => W3b.RunMiss (PU S.us) S.β₀.length n₁ S.us.length j (S.KT (n₁ + S.us.length) r)
          (S.KT (n₁ + S.us.length) r) (S.β₀ ++ β'))
      have hE4 := not_lt.mp E4
      have hE4r : ((∑ j ∈ Finset.range (k / (n₁ + S.us.length)), ∑ r ∈ Finset.Ioc J (34 * k),
          ((22 * (n₁ + S.us.length) * S.D.cP : ℕ) : ℚ) * ((r : ℚ) + 1) ^ (S.D.dP + 1) *
            (if W3b.RunMiss (PU S.us) S.β₀.length n₁ S.us.length j (S.KT (n₁ + S.us.length) r)
              (S.KT (n₁ + S.us.length) r) (S.β₀ ++ β') then 1 else 0) : ℚ) : ℝ) ≤
          ((εT * (Finset.range (k / (n₁ + S.us.length))).card : ℚ) : ℝ) := by exact_mod_cast hE4
      rw [Finset.card_range] at hE4r
      have hkg : ((k / (n₁ + S.us.length) : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.div_le_self k _
      have hεT0r : (0 : ℝ) ≤ εT := by exact_mod_cast hεT0.le
      push_cast at hE4r
      have : (εT : ℝ) * ((k / (n₁ + S.us.length) : ℕ) : ℝ) ≤ εT * k := mul_le_mul_of_nonneg_left hkg hεT0r
      push_cast at hgs
      linarith)
    le_rfl hεT.le (fun i => hJa J hJaJ i)
    (by rw [hlenβ']; exact hk1) (by rw [hlenβ']; exact hk3 k hkk3) (by rw [hlenβ']; exact hk4 k hkk4)
    (by rw [hlenβ']; exact le_of_le_of_eq (err_k hk1 hη₀K (hk5 k hkk5)) (by ring))
  -- the top window and the lower bound at the end point
  have hKcE : S.Kc = S.E + 9 := rfl
  have htop : (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).take S.E = S.τ :=
    E1 S.τ rfl n u hE9 (by
      have : n - (S.E + 9) - (parityOf S.β₀).length = F := by rw [← hKcE]; exact hnF
      rw [this]; exact huF)
  have hNk : k ≤ (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by omega
  have hV1 := S.x1_lower β' n u b M (Lc + 6) k hKn hu hx13 hA1 hb1 hb2 htop hlln hN0b (by rw [hFn]; exact hN0F)
    hU4 (by rw [hnF]; exact hU3) hη₁ hη₁1 hM1 (by rw [hFn]; exact hMF) hKmax
    (fun c hc d hd => hM₀ M hM0M c hc d hd) hk1 hNk
    (le_of_le_of_eq (err_k hk1 hη₁K (hk6 k hkk6)) (by ring))
    (hk7 k hkk7) (hk8 k hkk8)
  obtain ⟨c₁, hc₁, hlow⟩ := hV1
  obtain ⟨hcs1, hcase⟩ := hmin c₁ hc₁
  -- comparison
  have hN0r : (1 : ℝ) ≤ (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by
    exact_mod_cast (le_trans (le_trans hk1 (Nat.le_mul_of_pos_left k (by norm_num))) hN0ge)
  have hceil : ((cE : ℝ) * k) ≤ (⌈cE * k⌉₊ : ℕ) := by
    have := Nat.le_ceil (cE * k)
    exact_mod_cast this
  have hN01 := len_ratio hexpand hceil hN0le hκc hκ0.le
  have hN1big : 2 * (Clo + ε) / cs < (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by
    have h9 := hk9 k hkk9
    have : (k : ℝ) ≤ (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by exact_mod_cast hNk
    linarith only [h9, this]
  have hlt := compare hN0r hN01 hκ0 hκ1 hdlo hClo hcs hε0 hεκ hεc hN1big hV0 hlow
    ⟨hcs1, by
      rcases hcase with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by rw [h1]; exact h2⟩⟩
  -- monotonicity
  have hmon := mono_iter hmono (parityOf (S.β₀ ++ β')).length _ (fam_orbit_two_le S.β₀ (S.β₀ ++ β') u S.T0_pos) hx03
  rw [← hiter] at hmon
  have : (aval B (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) : ℝ) ≤
      aval B (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) := by exact_mod_cast hmon
  exact absurd hlt (not_lt.mpr this)

end Setup

end Collatz.Arctic.NatQ5.W3h
