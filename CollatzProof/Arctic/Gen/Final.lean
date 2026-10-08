/-
Conclusion of the assembly of the generic layer: from the hypotheses on window frequencies and on the uses of one rule, the conclusion of `AutoCore` for that rule
(`Gen.autoRuleG_of_hyps`; it proves the frozen statement
`SpecAutoRule` of `Gen/Spec.lean`).

Adapted from `autoCore_of_hyps` in `CoreFinal.lean` for $T$ (Theorem 6.8, with the slope of Definition 5.4 and Lemma 5.3), in the case of
a dynamic rule or a left-end rule. The classification of the rules (`rulesST_cases`) and the carry rules (`autoCore_aRule`) were moved to the side of the systems,
so here the claim is about a single rule `ρ`. At the point given by `good_point` (`Gen/GoodPoint.lean`), if `α_lo ≤ κ` then
the value is smaller than the number of uses, and if `α_lo > κ` this contradicts the slope hypothesis.

* `endgame_le`, `endgame_gt`: inequalities of reals only (copied from the source; we do not import `CoreFinal`, since it imports
  the carry rules of $T$).
* `iter_pos_of_orbitG`: if all points of the orbit lie in the domain, the end point is at least 1 (the case split on `T` in the source is replaced by
  the model's `f_pos`).
* `autoRuleG_of_hyps`, `specAutoRule`: the main part. Holds for every `BlockModel`, every canonical derivation `cd`, and every rule `ρ`.
-/
import CollatzProof.Arctic.Gen.GoodPoint
import CollatzProof.Arctic.Gen.Spec

namespace Collatz.Arctic.Gen

open Collatz.Arctic MinIdeal Matrix Classical

/-- Endgame estimate (1): if `α_lo ≤ κ` then the value is smaller than `κ N₀ + cU k`. -/
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

/-- Endgame estimate (2): if `α_lo > κ` then expansion, upper bound, lower bound and slope are incompatible (for large `k`). -/
theorem endgame_gt {V0 V1 N0 N1 αlo κ C₁ ε Cε Cst ce k : ℝ}
    (hslope : V1 + κ * N0 ≤ V0 + κ * N1) (hup : V0 ≤ (αlo + C₁ * ε) * N0 + Cε)
    (hlow : (αlo - ε) * N1 - Cst ≤ V1) (hexp : N0 + ce * k ≤ N1) (hN1 : N1 ≤ 50 * k + Cε)
    (_hN0 : 0 ≤ N0) (hC₁ : 0 ≤ C₁) (hε : 0 ≤ ε) (hακ : κ < αlo) (hce : 0 < ce) (hk0 : 0 ≤ k)
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

/-- If all points of the orbit lie in the domain then `f^[m] x₀ ≥ 1` (images of points of the domain are at least 1). -/
theorem iter_pos_of_orbitG (f : ℕ → ℕ) (dom : ℕ → Prop) (hpos : ∀ n, dom n → 1 ≤ f n)
    (x0 m : ℕ) (hx0 : 1 ≤ x0) (horb : ∀ i < m, dom (f^[i] x0)) : 1 ≤ f^[m] x0 := by
  cases m with
  | zero => simpa using hx0
  | succ m =>
    rw [Function.iterate_succ_apply']
    exact hpos _ (horb m (by omega))

/-- **Assembly of the generic layer** (the one-rule form of `CoreFinal.autoCore_of_hyps`): from window frequencies `HTerrasWinR BM.R` and
the uses `HUseR` of the rule `ρ`, the conclusion of `AutoCore` for `ρ` (`HSP` does not depend on Collatz). -/
theorem autoRuleG_of_hyps (BM : BlockModel) (cd : ℕ → List Rule) (hSP : HSP)
    (hTW : HTerrasWinR BM.R) (ρ : Rule) (hU : HUseR BM.f BM.R BM.steps cd ρ) :
    AutoRuleG BM.f BM.dom cd ρ := by
  intro D u₀ A c κ hfin hslope N
  -- the algebraic structure
  obtain ⟨K₀, hK, E, hEK, hE⟩ := exists_minIdeal_idem (B0 A) (B1 A)
  have hEM : E ∈ Mon (B0 A) (B1 A) := hK.1.2.1 hEK
  obtain ⟨us, hus, hEus⟩ := exists_ustar A hEM
  obtain ⟨wstar, hw⟩ := Dfa.exists_wstar (supDelta A)
  obtain ⟨w₀', hw₀'⟩ := Dfa.exists_absorbing (supDelta A)
  have hw₀ : ∀ q, Dfa.Recurrent (supDelta A) (Dfa.run (supDelta A) q (w₀' ++ [false])) := by
    intro q; rw [Dfa.run_append]; exact (hw₀' q).after [false]
  have hw₀ne : w₀' ++ [false] ≠ [] := by simp
  -- the shared part: the first block `β₀` in which `w* u*` appears
  have hvvd : IsDigits (wstar.map ofBool ++ us) := isDigits_append (isDigits_ofBool wstar) hus
  obtain ⟨_cL0, _hcL0, _ce0, _hce0, hsig0⟩ := sigma_good BM cd ρ hTW hU []
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
  set S := bitsMSB (parityOf β₀).length (BM.R β₀) with hSdef
  set S₁ := S.take i with hS₁def
  set z := S.drop (i + (wstar.map ofBool ++ us).length) with hzdef
  have hS : S = S₁ ++ wstar.map ofBool ++ us ++ z := by
    unfold window at hwi
    conv_lhs => rw [← List.take_append_drop i S]
    rw [← List.take_append_drop (wstar.map ofBool ++ us).length (S.drop i), hwi, List.drop_drop]
    simp only [List.append_assoc]
    rfl
  have hS₁ : IsDigits S₁ := fun s hs => bitsMSB_isDigits _ _ s (List.mem_of_mem_take hs)
  -- the state giving the minimal configuration
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
  obtain ⟨C₁, Cst, cU, ce, hC₁, hCst, hcU, hce, hgood⟩ := good_point BM cd ρ hSP hTW hU A u₀ c hK
    hEK hE us hus hEus wstar hw (w₀' ++ [false]) hw₀ hw₀ne β₀ S₁ z hS₁ hS wlo Xlo hwlo hrecXlo _ rfl
    hmin
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
    obtain ⟨x0, m, k, hNk, hNx, horb, hup, -, hexp, hlen1, huse⟩ :=
      hpt (N + ⌈2 * (C₁ * ε * Cε + Cε) / cU⌉₊ + 1)
    refine ⟨x0, by omega, m, horb, ?_⟩
    have hx0 : 1 ≤ x0 := by omega
    obtain ⟨V, hV⟩ := (Arc.val_ne_bot_iff _).mp ((Arc.ne_zero_iff_val _).mp (hfin x0 hx0))
    rw [hV, Arc.fin_lt_fin]
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
    have hfinal : (V : ℝ) < (κ * lenT x0 + usesOrbitG BM.f cd ρ x0 m : ℕ) := by
      push_cast; linarith
    exact_mod_cast hfinal
  · -- `α_lo > κ`: contradiction with the slope hypothesis
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
    obtain ⟨x0, m, k, hNk, hNx, horb, hup, hlow, hexp, hlen1, -⟩ :=
      hpt (N + ⌈2 * (ε * (1 + C₁) * Cε + Cst + Cε) / ((αlo - κ) * ce)⌉₊ + 1)
    exfalso
    have hx0 : 1 ≤ x0 := by omega
    have hx1 : 1 ≤ BM.f^[m] x0 := iter_pos_of_orbitG BM.f BM.dom BM.f_pos x0 m hx0 horb
    obtain ⟨V0, hV0⟩ := (Arc.val_ne_bot_iff _).mp ((Arc.ne_zero_iff_val _).mp (hfin x0 hx0))
    obtain ⟨V1, hV1⟩ := (Arc.val_ne_bot_iff _).mp ((Arc.ne_zero_iff_val _).mp (hfin _ hx1))
    have hsl := slope_orbitG BM.f BM.dom BM.f_pos u₀ A c κ hfin hslope m x0 horb V0 V1 hV0 hV1
    have hslR : (V1 : ℝ) + κ * lenT x0 ≤ V0 + κ * lenT (BM.f^[m] x0) := by exact_mod_cast hsl
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

/-- **Output of the generic layer** (`SpecAutoRule` of the frozen `Gen/Spec.lean`): for every model, canonical derivation and rule,
from `HSP`, window frequencies and the uses of the rule, the conclusion of `AutoCore` for that rule. -/
theorem specAutoRule : SpecAutoRule :=
  fun BM cd ρ hSP hTW hU => autoRuleG_of_hyps BM cd hSP hTW ρ hU

end Collatz.Arctic.Gen
