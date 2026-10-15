/-
Conclusion of the assembly: `AutoCore` from the three hypotheses `HSP`, `HTerrasWin`, `HLeftUse` (Theorem 6.8 of the paper).
Theorem 6.8 (Theorem 5.5 for `T`), with the slope `κ` of Definition 5.4 (which absorbs the translation of Lemma 5.3), and the numbers of uses of the rules on the point family.

Since revision r5 the proof goes through the general layer: `AutoCore` is `Gen.AutoCoreG T (2 ≤ ·) rulesST canDeriv` by `Gen.autoCore_iff`
(definitionally the same), and the block-model results are applied rule by rule to the model `Gen.tModel` of `T` (the same assembly as
`autoCoreH_of_specs` in `HTPDB/Spec.lean`).
* Carry rules: `Gen.specQuadRule` (a linear upper bound for the values and quadratic uses) with `Gen.tModel_quad` (`ARule.aRule_quad`).
* Dynamic rules and left-end rules: `Gen.autoRuleG_of_hyps` (at the point of `good_point`, if `α_lo ≤ κ` the value is smaller than the number of uses,
  and if `α_lo > κ` this contradicts the hypothesis on the slope; `Gen/Final.lean`), given the window frequencies `HTerrasWin` (`Gen.hTerrasWin_iff`)
  and the uses `Gen.HUseR`. The uses of the left-end rules are `Gen.hUseR_of_hLeftUse`, those of the dynamic rules `hUseR_dyn_even` and
  `hUseR_dyn_odd` below (counting parities along the orbits of the family, `FamilyUses.lean`; they hold for every `t`, so with probability 1).

The proof of `T` before this change (`good_point` in `CoreGoodPoint.lean`, cited in the paper) is not used here; the root module `Paper.lean`
keeps it in its import closure. The end estimates `endgame_le`, `endgame_gt` are thin theorems for the copies in `Gen`.
-/
import CollatzProof.Arctic.Gen.Final
import CollatzProof.Arctic.Gen.Quad
import CollatzProof.Arctic.Gen.ModelT
import CollatzProof.Arctic.FamilyUses
import CollatzProof.Arctic.FamilyExp
import CollatzProof.Arctic.CoreProb

namespace Collatz.Arctic

open Classical

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

/-- End estimate (1): if `α_lo ≤ κ`, the value is smaller than `κ N₀ + cU k` (`Gen.endgame_le`). -/
theorem endgame_le {V N0 αlo κ C₁ ε Cε cU k : ℝ} (hV : V ≤ (αlo + C₁ * ε) * N0 + Cε)
    (hακ : αlo ≤ κ) (hN0 : 0 ≤ N0) (hN0k : N0 ≤ 50 * k + Cε) (hC₁ : 0 ≤ C₁) (hε : 0 ≤ ε)
    (hεc : C₁ * ε * 50 ≤ cU / 4) (hk : C₁ * ε * Cε + Cε < cU * k / 2) (hcUk : 0 < cU * k) :
    V < κ * N0 + cU * k :=
  Gen.endgame_le hV hακ hN0 hN0k hC₁ hε hεc hk hcUk

/-- End estimate (2): if `α_lo > κ`, expansion, the upper bound, the lower bound and the slope are incompatible (for large `k`; `Gen.endgame_gt`). -/
theorem endgame_gt {V0 V1 N0 N1 αlo κ C₁ ε Cε Cst ce k : ℝ}
    (hslope : V1 + κ * N0 ≤ V0 + κ * N1) (hup : V0 ≤ (αlo + C₁ * ε) * N0 + Cε)
    (hlow : (αlo - ε) * N1 - Cst ≤ V1) (hexp : N0 + ce * k ≤ N1) (hN1 : N1 ≤ 50 * k + Cε)
    (_hN0 : 0 ≤ N0) (hC₁ : 0 ≤ C₁) (hε : 0 ≤ ε) (hακ : κ < αlo) (hce : 0 < ce) (hk0 : 0 ≤ k)
    (hεc : ε * (1 + C₁) * 50 ≤ (αlo - κ) * ce / 4)
    (hk : ε * (1 + C₁) * Cε + Cst + Cε < (αlo - κ) * ce * k / 2) : False :=
  Gen.endgame_gt hslope hup hlow hexp hN1 _hN0 hC₁ hε hακ hce hk0 hεc hk

/-! ## Uses of the dynamic rules (in the form `Gen.HUseR`) -/

/-- An event that holds for every choice of length `k` has probability 1. -/
lemma prσ_eq_one_T (β₀ : List Bool) (k : ℕ) {E : List Bool → Prop}
    (h : ∀ β ∈ blockChoices k, E (β₀ ++ β)) : Prσ β₀ k E = 1 := by
  unfold Prσ
  rw [Finset.filter_true_of_mem h]
  exact (fam_moments k).1

/-- Along an orbit of the family (`m` steps from `r_β + 2^m s`), the rule `ρ` of the steps of parity `c` is used at least `3 |β|` times. -/
lemma usesOrbitG_dyn_ge (ρ : Rule) (c : Bool)
    (hρ : ∀ x, uses ρ x = if x % 2 = (if c then 1 else 0) then 1 else 0) (β : List Bool) (s : ℕ) :
    3 * β.length ≤ Gen.usesOrbitG T canDeriv ρ (Gen.tModel.R β + 2 ^ (parityOf β).length * s)
      (Gen.tModel.steps β) := by
  have h : Gen.usesOrbitG T canDeriv ρ (Gen.tModel.R β + 2 ^ (parityOf β).length * s)
      (Gen.tModel.steps β) = (parityOf β).count c := fam_usesOrbit_parity ρ (parityOf β) s c hρ
  have hc := fam_parityOf_counts β
  have hl := fam_length_eq_count β
  rw [h]
  cases c <;> simp only [hc.2.1, hc.2.2] <;> omega

/-- If the rule `ρ` is always used at least `3 |β|` times along the orbits of the family, then `Gen.HUseR` holds (`c = 1`, probability 1). -/
lemma hUseR_of_ge (ρ : Rule)
    (hge : ∀ β s, 3 * β.length ≤ Gen.usesOrbitG T canDeriv ρ
      (Gen.tModel.R β + 2 ^ (parityOf β).length * s) (Gen.tModel.steps β)) :
    Gen.HUseR T Gen.tModel.R Gen.tModel.steps canDeriv ρ := by
  intro β₀
  refine ⟨1, one_pos, fun ε hε => ⟨0, fun k _ => ?_⟩⟩
  have h1 := prσ_eq_one_T β₀ k (E := fun β => ∀ s : ℕ, 2 ^ (parityOf β).length ≤ s →
      (1 : ℚ) * k ≤ (Gen.usesOrbitG T canDeriv ρ (Gen.tModel.R β + 2 ^ (parityOf β).length * s)
        (Gen.tModel.steps β) : ℚ)) (fun β hβ s _ => by
      have h2 := hge (β₀ ++ β) s
      rw [List.length_append, (fam_mem_blockChoices β k).mp hβ] at h2
      have h3 : (k : ℚ) ≤ (Gen.usesOrbitG T canDeriv ρ
          (Gen.tModel.R (β₀ ++ β) + 2 ^ (parityOf (β₀ ++ β)).length * s)
          (Gen.tModel.steps (β₀ ++ β)) : ℚ) := by
        exact_mod_cast (show k ≤ _ by omega)
      linarith)
  linarith

open Letter in
/-- Uses of the rule `f. → .` of the even steps along the orbits of the family (at least `3 |β|`, `fam_uses_even`). -/
theorem hUseR_dyn_even : Gen.HUseR T Gen.tModel.R Gen.tModel.steps canDeriv ⟨[f, rgt], [rgt]⟩ :=
  hUseR_of_ge _ (fun β s => usesOrbitG_dyn_ge _ false (fun x => by rw [fam_uses_even]; simp) β s)

open Letter in
/-- Uses of the rule `t. → 2.` of the odd steps along the orbits of the family (at least `3 |β|`, `fam_uses_odd`). -/
theorem hUseR_dyn_odd : Gen.HUseR T Gen.tModel.R Gen.tModel.steps canDeriv ⟨[t, rgt], [d2, rgt]⟩ :=
  hUseR_of_ge _ (fun β s => usesOrbitG_dyn_ge _ true
    (fun x => by rw [fam_uses_odd]; simp only [ite_true]; split_ifs <;> omega) β s)

/-! ## Assembly -/

/-- **Conclusion of the assembly**: `AutoCore` follows from the three hypotheses (the rule-by-rule conclusions of the general layer applied to `Gen.tModel`). -/
theorem autoCore_of_hyps (hSP : HSP) (hTW : HTerrasWin) (hLU : HLeftUse) : AutoCore := by
  have hTW' : Gen.HTerrasWinR Gen.tModel.R := Gen.hTerrasWin_iff.mp hTW
  refine Gen.autoCore_iff.mpr (Gen.autoCoreG_of_rules (fun ρ hρ => ?_))
  rcases rulesST_cases ρ hρ with ⟨b, d, hb, hd, rfl⟩ | rfl | rfl | ⟨d, hd, rfl⟩
  · exact Gen.specQuadRule _ _ _ _ (Gen.tModel_quad b d hb hd)
  · exact Gen.autoRuleG_of_hyps Gen.tModel canDeriv hSP hTW' _ hUseR_dyn_even
  · exact Gen.autoRuleG_of_hyps Gen.tModel canDeriv hSP hTW' _ hUseR_dyn_odd
  · exact Gen.autoRuleG_of_hyps Gen.tModel canDeriv hSP hTW' _ (Gen.hUseR_of_hLeftUse hLU d hd)

end Collatz.Arctic
