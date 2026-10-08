/-
Conclusion of the assembly: `AutoCore` from the three hypotheses `HSP`, `HTerrasWin`, `HLeftUse` (Theorem 6.8 of the paper).
Theorem 6.8 (Theorem 5.5 for `T`), with the slope `κ` of Definition 5.4 (which absorbs the translation of Lemma 5.3), and the numbers of uses of the rules on the point family.
* Carry rules: `autoCore_aRule` (no hypotheses).
* Dynamic rules and left-end rules: at the point of `good_point`, if `α_lo ≤ κ` the value is smaller than the number of uses, and if `α_lo > κ` this contradicts
  the hypothesis on the slope.
-/
import CollatzProof.Arctic.CoreGoodPoint
import CollatzProof.Arctic.CoreProb
import CollatzProof.Arctic.ARuleMain

namespace Collatz.Arctic

open MinIdeal Matrix Classical

/-- Classification of the 11 rules of the system 𝒯 (`rulesST`). -/
theorem rulesST_cases (ρ : Rule) (h : ρ ∈ rulesST) :
    (∃ b d, b < 2 ∧ d ≤ 2 ∧ ρ = aRule b d) ∨ ρ = ⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩ ∨
      ρ = ⟨[Letter.t, Letter.rgt], [Letter.d2, Letter.rgt]⟩ ∨ ∃ d ≤ 2, ρ = leftRule d := by
  simp only [rulesST, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl ⟨0, 0, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨0, 1, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨0, 2, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 0, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 1, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 2, by norm_num, by norm_num, by decide⟩
  · exact Or.inr (Or.inr (Or.inr ⟨0, by norm_num, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨1, by norm_num, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨2, by norm_num, by decide⟩))

/-- Final estimate (1): if `α_lo ≤ κ`, the value is smaller than `κ N₀ + cU k`. -/
theorem endgame_le {V N0 αlo κ C₁ ε Cε cU k : ℝ} (hV : V ≤ (αlo + C₁ * ε) * N0 + Cε)
    (hακ : αlo ≤ κ) (hN0 : 0 ≤ N0) (hN0k : N0 ≤ 50 * k + Cε) (hC₁ : 0 ≤ C₁) (hε : 0 ≤ ε)
    (hεc : C₁ * ε * 50 ≤ cU / 4) (hk : C₁ * ε * Cε + Cε < cU * k / 2) (hcUk : 0 < cU * k) :
    V < κ * N0 + cU * k := by
  have h1 : αlo * N0 ≤ κ * N0 := mul_le_mul_of_nonneg_right hακ hN0
  have h2 : C₁ * ε * N0 ≤ C₁ * ε * (50 * k + Cε) := mul_le_mul_of_nonneg_left hN0k (by positivity)
  have h3 : C₁ * ε * (50 * k) ≤ cU / 4 * k := by
    have hk0 : 0 ≤ k := by
      by_contra hneg; push Not at hneg
      have : C₁ * ε * (50 * k) ≤ 0 := by
        have := mul_nonneg hC₁ hε
        nlinarith
      nlinarith
    calc C₁ * ε * (50 * k) = C₁ * ε * 50 * k := by ring
      _ ≤ cU / 4 * k := mul_le_mul_of_nonneg_right hεc hk0
  nlinarith

/-- Final estimate (2): if `α_lo > κ`, the expansion, the upper bound, the lower bound and the slope are incompatible (for large `k`). -/
theorem endgame_gt {V0 V1 N0 N1 αlo κ C₁ ε Cε Cst ce k : ℝ}
    (hslope : V1 + κ * N0 ≤ V0 + κ * N1) (hup : V0 ≤ (αlo + C₁ * ε) * N0 + Cε)
    (hlow : (αlo - ε) * N1 - Cst ≤ V1) (hexp : N0 + ce * k ≤ N1) (hN1 : N1 ≤ 50 * k + Cε)
    (hN0 : 0 ≤ N0) (hC₁ : 0 ≤ C₁) (hε : 0 ≤ ε) (hακ : κ < αlo) (hce : 0 < ce) (hk0 : 0 ≤ k)
    (hεc : ε * (1 + C₁) * 50 ≤ (αlo - κ) * ce / 4)
    (hk : ε * (1 + C₁) * Cε + Cst + Cε < (αlo - κ) * ce * k / 2) : False := by
  have hN01 : N0 ≤ N1 := by nlinarith [mul_nonneg hce.le hk0]
  have hmain : (αlo - κ) * (N1 - N0) ≤ ε * N1 + C₁ * ε * N0 + Cst + Cε := by nlinarith
  have hA : (αlo - κ) * (ce * k) ≤ (αlo - κ) * (N1 - N0) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hB : ε * N1 + C₁ * ε * N0 ≤ ε * (1 + C₁) * N1 := by
    have : C₁ * ε * N0 ≤ C₁ * ε * N1 := mul_le_mul_of_nonneg_left hN01 (by positivity)
    nlinarith
  have hC : ε * (1 + C₁) * N1 ≤ ε * (1 + C₁) * (50 * k + Cε) :=
    mul_le_mul_of_nonneg_left hN1 (by positivity)
  have hD : ε * (1 + C₁) * (50 * k) ≤ (αlo - κ) * ce / 4 * k := by
    calc ε * (1 + C₁) * (50 * k) = ε * (1 + C₁) * 50 * k := by ring
      _ ≤ (αlo - κ) * ce / 4 * k := mul_le_mul_of_nonneg_right hεc hk0
  nlinarith

/-- If all points of the orbit are at least 2, then `T^m x₀ ≥ 1`. -/
theorem iter_pos_of_orbit (x0 m : ℕ) (hx0 : 1 ≤ x0) (horb : ∀ i < m, 2 ≤ T^[i] x0) : 1 ≤ T^[m] x0 := by
  cases m with
  | zero => simpa using hx0
  | succ m =>
    have h := horb m (by omega)
    rw [Function.iterate_succ_apply']
    generalize T^[m] x0 = y at h ⊢
    unfold T; split_ifs <;> omega

/-- **Theorem 6.8 (assembly)**: `AutoCore` follows from the three hypotheses. -/
theorem autoCore_of_hyps (hSP : HSP) (hTW : HTerrasWin) (hLU : HLeftUse) : AutoCore := by
  intro D u₀ A c κ hfin hslope ρ hρ N
  rcases rulesST_cases ρ hρ with ⟨b, d, hb, hd, rfl⟩ | hdyn
  · exact autoCore_aRule D u₀ A c κ b d hb hd N
  -- algebraic structure
  obtain ⟨K₀, hK, E, hEK, hE⟩ := exists_minIdeal_idem (B0 A) (B1 A)
  have hEM : E ∈ Mon (B0 A) (B1 A) := hK.1.2.1 hEK
  obtain ⟨us, hus, hEus⟩ := exists_ustar A hEM
  obtain ⟨wstar, hw⟩ := Dfa.exists_wstar (supDelta A)
  obtain ⟨w₀', hw₀'⟩ := Dfa.exists_absorbing (supDelta A)
  have hw₀ : ∀ q, Dfa.Recurrent (supDelta A) (Dfa.run (supDelta A) q (w₀' ++ [false])) := by
    intro q; rw [Dfa.run_append]; exact (hw₀' q).after [false]
  have hw₀ne : w₀' ++ [false] ≠ [] := by simp
  -- shared part: the initial block sequence `β₀` in whose Terras residue `w* u*` occurs
  have hvvd : IsDigits (wstar.map ofBool ++ us) := isDigits_append (isDigits_ofBool wstar) hus
  obtain ⟨_cL0, _hcL0, _ce0, _hce0, hsig0⟩ := sigma_good hTW hLU []
  have hδ0 : (0 : ℚ) < 1 / (4 * 2 ^ (wstar.map ofBool ++ us).length) := by positivity
  obtain ⟨k₁, -, β₀, hβ₀, hwin0, -, -⟩ := hsig0 (wstar.map ofBool ++ us).length
    (1 / (4 * 2 ^ (wstar.map ofBool ++ us).length)) hδ0 1 le_rfl 1
  have hwin := hwin0 0 (by norm_num)
  simp only [List.nil_append, List.length_nil, zero_add, one_mul, Nat.div_one, zero_mul] at hwin
  rw [← hβ₀, blockEnd_full, Nat.sub_self] at hwin
  have hbe0 : blockEnd β₀ 0 = 0 := by simp [blockEnd, parityOf]
  rw [hbe0, Nat.sub_zero] at hwin
  obtain ⟨i, -, hiJ, hwi⟩ := Upper.occ_of_winClose hvvd le_rfl (by
    have : (0 : ℚ) < 1 / 2 ^ (wstar.map ofBool ++ us).length := by positivity
    rw [show (2 : ℚ) * (1 / (4 * 2 ^ (wstar.map ofBool ++ us).length)) =
      1 / 2 ^ (wstar.map ofBool ++ us).length / 2 by field_simp; ring]
    linarith) hwin
  set S := bitsMSB (parityOf β₀).length (terrasR (parityOf β₀)) with hSdef
  have hSlen : S.length = (parityOf β₀).length := bitsMSB_length _ _
  set S₁ := S.take i with hS₁def
  set z := S.drop (i + (wstar.map ofBool ++ us).length) with hzdef
  have hS : S = S₁ ++ wstar.map ofBool ++ us ++ z := by
    unfold window at hwi
    conv_lhs => rw [← List.take_append_drop i S]
    rw [← List.take_append_drop (wstar.map ofBool ++ us).length (S.drop i), hwi, List.drop_drop]
    simp only [List.append_assoc]
    rfl
  have hS₁ : IsDigits S₁ := fun s hs => bitsMSB_isDigits _ _ s (List.mem_of_mem_take hs)
  have hz : IsDigits z := fun s hs => bitsMSB_isDigits _ _ s (List.mem_of_mem_drop hs)
  -- the state that attains the minimal configuration rate
  set Rset := (Finset.univ : Finset (Finset (Fin D))).filter (fun X =>
    Dfa.Reach (supDelta A) (suppF u₀) X ∧ Dfa.Recurrent (supDelta A) X) with hRset
  have hRne : Rset.Nonempty :=
    ⟨Dfa.run (supDelta A) (suppF u₀) (w₀' ++ [false]),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨_, rfl⟩, hw₀ _⟩⟩
  obtain ⟨Xlo, hXlo, hminR⟩ := Finset.exists_min_image Rset
    (fun X => alphaZ hE A c z (cfgOf A hE (S₁ ++ wstar.map ofBool) X)) hRne
  obtain ⟨⟨wlo, hwlo⟩, hrecXlo⟩ := (Finset.mem_filter.mp hXlo).2
  have hmin : ∀ X, Dfa.Reach (supDelta A) (suppF u₀) X → Dfa.Recurrent (supDelta A) X →
      alphaZ hE A c z (cfgOf A hE (S₁ ++ wstar.map ofBool) Xlo) ≤
        alphaZ hE A c z (cfgOf A hE (S₁ ++ wstar.map ofBool) X) :=
    fun X h1 h2 => hminR X (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)
  obtain ⟨C₁, Cst, cU, ce, hC₁, hCst, hcU, hce, hgood⟩ := good_point hSP hTW hLU A u₀ c hK hEK hE
    us hus hEus wstar hw (w₀' ++ [false]) hw₀ hw₀ne β₀ S₁ z hS₁ hz hS wlo Xlo hwlo hrecXlo _ rfl hmin
  set αlo := alphaZ hE A c z (cfgOf A hE (S₁ ++ wstar.map ofBool) Xlo) with hαlo
  have hcUpos : 0 < cU := hcU
  by_cases hcase : αlo ≤ (κ : ℝ)
  · -- `α_lo ≤ κ`: the value is smaller than the number of uses
    set ε := min (1 / 16 : ℝ) (cU / (4 * 50 * (C₁ + 1))) with hεdef
    have hε : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε16 : ε ≤ 1 / 16 := min_le_left _ _
    have hεc : C₁ * ε * 50 ≤ cU / 4 := by
      have h1 : ε ≤ cU / (4 * 50 * (C₁ + 1)) := min_le_right _ _
      have h2 : C₁ * ε ≤ (C₁ + 1) * ε := by nlinarith
      have h3 : (C₁ + 1) * ε ≤ (C₁ + 1) * (cU / (4 * 50 * (C₁ + 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : (C₁ + 1) * (cU / (4 * 50 * (C₁ + 1))) = cU / 200 := by field_simp; ring
      nlinarith
    obtain ⟨Cε, hpt⟩ := hgood ε hε hε16
    obtain ⟨x0, m, k, hNk, hNx, horb, hup, -, hexp, hlen1, hd0, hd1, hl⟩ :=
      hpt (N + ⌈2 * (C₁ * ε * Cε + Cε) / cU⌉₊ + 1)
    refine ⟨x0, by omega, m, horb, ?_⟩
    have hx0 : 1 ≤ x0 := by omega
    obtain ⟨V, hV⟩ := (Arc.val_ne_bot_iff _).mp ((Arc.ne_zero_iff_val _).mp (hfin x0 hx0))
    rw [hV, Arc.fin_lt_fin]
    have huse : cU * k ≤ usesOrbit ρ x0 m := by
      rcases hdyn with rfl | rfl | ⟨d, hd, rfl⟩
      · exact hd0
      · exact hd1
      · exact hl d hd
    have hVle := hup V hV
    have hN0 : (0 : ℝ) ≤ lenT x0 := Nat.cast_nonneg _
    have hN0k : (lenT x0 : ℝ) ≤ 50 * k + Cε := by
      have : (0 : ℝ) ≤ ce * k := mul_nonneg hce.le (Nat.cast_nonneg _)
      linarith
    have hk : C₁ * ε * Cε + Cε < cU * k / 2 := by
      have hc : 2 * (C₁ * ε * Cε + Cε) / cU ≤ (⌈2 * (C₁ * ε * Cε + Cε) / cU⌉₊ : ℝ) := Nat.le_ceil _
      have hk' : ((⌈2 * (C₁ * ε * Cε + Cε) / cU⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega :
        ⌈2 * (C₁ * ε * Cε + Cε) / cU⌉₊ + 1 ≤ k)
      push_cast at hk'
      rw [div_le_iff₀ hcUpos] at hc
      nlinarith
    have hcUk : 0 < cU * k := mul_pos hcUpos (by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      linarith)
    have hlt := endgame_le hVle hcase hN0 hN0k hC₁ hε.le hεc hk hcUk
    have hfinal : (V : ℝ) < (κ * lenT x0 + usesOrbit ρ x0 m : ℕ) := by push_cast; linarith
    exact_mod_cast hfinal
  · -- `α_lo > κ`: contradiction with the hypothesis on the slope
    push Not at hcase
    have hgap : 0 < (αlo - κ) * ce := mul_pos (by linarith) hce
    set ε := min (1 / 16 : ℝ) ((αlo - κ) * ce / (4 * 50 * (1 + C₁))) with hεdef
    have hε : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε16 : ε ≤ 1 / 16 := min_le_left _ _
    have hεc : ε * (1 + C₁) * 50 ≤ (αlo - κ) * ce / 4 := by
      have h1 : ε ≤ (αlo - κ) * ce / (4 * 50 * (1 + C₁)) := min_le_right _ _
      have h3 : ε * (1 + C₁) ≤ (αlo - κ) * ce / (4 * 50 * (1 + C₁)) * (1 + C₁) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h4 : (αlo - κ) * ce / (4 * 50 * (1 + C₁)) * (1 + C₁) = (αlo - κ) * ce / 200 := by
        field_simp; ring
      nlinarith
    obtain ⟨Cε, hpt⟩ := hgood ε hε hε16
    obtain ⟨x0, m, k, hNk, hNx, horb, hup, hlow, hexp, hlen1, -, -, -⟩ :=
      hpt (N + ⌈2 * (ε * (1 + C₁) * Cε + Cst + Cε) / ((αlo - κ) * ce)⌉₊ + 1)
    exfalso
    have hx0 : 1 ≤ x0 := by omega
    have hx1 : 1 ≤ T^[m] x0 := iter_pos_of_orbit x0 m hx0 horb
    obtain ⟨V0, hV0⟩ := (Arc.val_ne_bot_iff _).mp ((Arc.ne_zero_iff_val _).mp (hfin x0 hx0))
    obtain ⟨V1, hV1⟩ := (Arc.val_ne_bot_iff _).mp ((Arc.ne_zero_iff_val _).mp (hfin _ hx1))
    have hsl := slope_orbit u₀ A c κ hfin hslope m x0 horb V0 V1 hV0 hV1
    have hslR : (V1 : ℝ) + κ * lenT x0 ≤ V0 + κ * lenT (T^[m] x0) := by exact_mod_cast hsl
    have hk : ε * (1 + C₁) * Cε + Cst + Cε < (αlo - κ) * ce * k / 2 := by
      have hc : 2 * (ε * (1 + C₁) * Cε + Cst + Cε) / ((αlo - κ) * ce) ≤
          (⌈2 * (ε * (1 + C₁) * Cε + Cst + Cε) / ((αlo - κ) * ce)⌉₊ : ℝ) := Nat.le_ceil _
      have hk' : ((⌈2 * (ε * (1 + C₁) * Cε + Cst + Cε) / ((αlo - κ) * ce)⌉₊ + 1 : ℕ) : ℝ) ≤ k := by
        exact_mod_cast (by omega :
          ⌈2 * (ε * (1 + C₁) * Cε + Cst + Cε) / ((αlo - κ) * ce)⌉₊ + 1 ≤ k)
      push_cast at hk'
      rw [div_le_iff₀ hgap] at hc
      nlinarith
    exact endgame_gt hslR (hup V0 hV0) (hlow V1 hV1) hexp hlen1 (Nat.cast_nonneg _) hC₁ hε.le
      hcase hce (Nat.cast_nonneg _) hεc hk

end Collatz.Arctic
