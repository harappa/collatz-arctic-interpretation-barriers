/-
Lean foundation of Section 8 (Section 8.1): the instances of Corollary 8.1 for $T$ and $H$.

Apply `autoRuleG_family` of `Family.lean` to the model `Gen.tModel` of $T$ (Lemma 6.1) and the model
`HModel.modelOf HModel.specHModel` of $H$ (Proposition 7.2). The hypotheses (window frequencies, uses of the rules, `HSP`) are supplied by existing theorems, so
the conclusions hold without hypotheses. The rules covered are those handled through `specAutoRule` (for $T$ the three left-end rules, for $H$ the three left-end rules and the two dynamic rules).
The carry rules $A$ are handled through quadratic uses (`Gen.QuadR`, another family with alternating parities), so the form restricted to points of family orbits does not apply to them.

* `autoRuleG_family_T`: the left-end rules of $T$, with the slope hypothesis only at points of family orbits.
* `autoRuleG_family_H_left`, `autoRuleG_family_H_ff`, `autoRuleG_family_H_ttt`: the left-end and dynamic rules of $H$.
* `two_not_famDom`: for $T$ the restricted domain is strictly smaller (`2` is a point of `tModel.dom` but not of a family orbit: the orbit of
  `2` under `T` stays in `{1, 2}` and does not reach the end point `c_β + 3^{a_β} t ≥ 3^5` of the family). So the slope hypothesis of the restricted form is
  strictly weaker than that of the original form (and by `Family.autoRuleG_of_family` the restricted form contains the original one).
* `eight_not_famDom_H`: the same for $H$ (`8` is a point of `HDom` but not of a family orbit; its orbit stops after `8 ↦ 6`).
-/
import CollatzProof.Arctic.DPGen.Family
import CollatzProof.Arctic.HSPMain
import CollatzProof.Arctic.HTWFromKey
import CollatzProof.Arctic.KeyFinal
import CollatzProof.Arctic.HLUMain
import CollatzProof.Arctic.Gen.KeyMain4
import CollatzProof.Arctic.Gen.HTWFromKey
import CollatzProof.Arctic.HModel.Swap
import CollatzProof.Arctic.HTPDB.LeftUseMain
import CollatzProof.Arctic.HTPDB.Uses

namespace Collatz.Arctic.DPGen

open Collatz.Arctic Collatz.Arctic.Gen

/-! ## The instance for $T$ -/

/-- The window frequencies for $T$ (the frozen `HTerrasWin`, from `HKeyTop`). -/
theorem hTerrasWinR_T : HTerrasWinR tModel.R := hTerrasWin_iff.mp (hTerrasWin_of_key hKeyTop)

/-- **Corollary 8.1, $T$**: for the left-end rules, `AutoRuleG` with the slope hypothesis only at points of family orbits. -/
theorem autoRuleG_family_T (d : ℕ) (hd : d ≤ 2) :
    AutoRuleG T (famDom tModel) canDeriv (leftRule d) :=
  autoRuleG_family tModel canDeriv (leftRule d) hsp_holds hTerrasWinR_T
    (hUseR_of_hLeftUse hLeftUse d hd)

/-- The orbit of `2` under `T` is `{1, 2}`. -/
theorem T_iter_two (k : ℕ) : T^[k] 2 = 2 ∨ T^[k] 2 = 1 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h]
    · right; decide
    · left; decide

/-- `2` is a point of the domain of `T` (`2 ≤ n`). -/
theorem two_tDom : tModel.dom 2 := le_refl 2

/-- **The restricted domain is strictly smaller** ($T$): `2` is not a point of a family orbit. -/
theorem two_not_famDom : ¬ famDom tModel 2 := by
  rintro ⟨⟨β, t, i, ht, hi, hx⟩, -⟩
  have hiter := tModel.iter β t
  have hsplit : tModel.steps β = (tModel.steps β - i) + i := by omega
  rw [hsplit, Function.iterate_add_apply, ← hx] at hiter
  have hβ : 1 ≤ β.length := by
    rcases β with _ | ⟨b, β⟩
    · exact absurd hi (by simp [tModel, parityOf])
    · simp
  have hA : 5 ≤ terrasA (parityOf β) := le_trans (by omega) (fam_terrasA_ge β)
  have hpow : 3 ^ 5 ≤ 3 ^ terrasA (parityOf β) := Nat.pow_le_pow_right (by norm_num) hA
  have hle : 3 ^ terrasA (parityOf β) ≤ 3 ^ terrasA (parityOf β) * t :=
    Nat.le_mul_of_pos_right _ ht
  have h2 : T^[tModel.steps β - i] 2 ≤ 2 := by
    rcases T_iter_two (tModel.steps β - i) with h | h <;> omega
  change T^[tModel.steps β - i] 2 = terrasC (parityOf β) + 3 ^ terrasA (parityOf β) * t at hiter
  norm_num at hpow
  generalize 3 ^ terrasA (parityOf β) = P at hpow hle hiter
  generalize T^[tModel.steps β - i] 2 = Q at h2 hiter
  generalize 3 ^ terrasA (parityOf β) * t = P' at *
  omega

/-! ## The instances for $H$ -/

open HModel HTPDB in
/-- The window frequencies for $H$ (the swap argument, with swap exponents `e₂ = e₃ = 8`). -/
theorem hTerrasWinR_H : HTerrasWinR hR :=
  specWinOfKey hR specHModel.R_lt specHModel.R_prefix
    (specKeyOfSwap hR specHModel.R_lt specHModel.R_prefix 8 8 le_rfl (by norm_num) specHSwap)

open HModel HTPDB in
/-- **Corollary 8.1, $H$**: the left-end rules. -/
theorem autoRuleG_family_H_left (d : ℕ) (hd : d ≤ 2) :
    AutoRuleG Hmap (famDom (modelOf specHModel)) canDerivH (leftRule d) :=
  autoRuleG_family (modelOf specHModel) canDerivH (leftRule d) hsp_holds hTerrasWinR_H
    (specLeftUseH specHModel specHClass specHBoundary d hd)

open HModel HTPDB in
/-- **Corollary 8.1, $H$**: the dynamic rule `ff. → 0.`. -/
theorem autoRuleG_family_H_ff :
    AutoRuleG Hmap (famDom (modelOf specHModel)) canDerivH ffRule :=
  autoRuleG_family (modelOf specHModel) canDerivH ffRule hsp_holds hTerrasWinR_H
    (specDynUseH specHModel specHClass).1

open HModel HTPDB in
/-- **Corollary 8.1, $H$**: the dynamic rule `ttt. → 22.`. -/
theorem autoRuleG_family_H_ttt :
    AutoRuleG Hmap (famDom (modelOf specHModel)) canDerivH tttRule :=
  autoRuleG_family (modelOf specHModel) canDerivH tttRule hsp_holds hTerrasWinR_H
    (specDynUseH specHModel specHClass).2

open HModel in
/-- The orbit of `8` under `Hmap` is `{8, 6}` (`8 ↦ 6`, and `6` lies outside the domain and is fixed). -/
theorem Hmap_iter_eight (k : ℕ) : Hmap^[k] 8 = 8 ∨ Hmap^[k] 8 = 6 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h]
    · right; decide
    · right; decide

open HModel in
/-- `8` is a point of the domain of $H$ (`HDom`). -/
theorem eight_HDom : HDom 8 := ⟨le_refl 8, Or.inl rfl⟩

open HModel in
/-- **The restricted domain is strictly smaller** ($H$): `8` is not a point of a family orbit (it does not reach the end point `c_β + 3^{a_β} t ≥ 3^5`). -/
theorem eight_not_famDom_H : ¬ famDom (modelOf specHModel) 8 := by
  rintro ⟨⟨β, t, i, ht, hi, hx⟩, -⟩
  have hiter := (modelOf specHModel).iter β t
  have hsplit : (modelOf specHModel).steps β = ((modelOf specHModel).steps β - i) + i := by omega
  rw [hsplit, Function.iterate_add_apply, ← hx] at hiter
  have hβ : 1 ≤ β.length := by
    rcases β with _ | ⟨b, β⟩
    · exact absurd hi (by simp [modelOf, hSteps, lettersOf])
    · simp
  have hA : 5 ≤ terrasA (parityOf β) := le_trans (by omega) (fam_terrasA_ge β)
  have hpow : 3 ^ 5 ≤ 3 ^ terrasA (parityOf β) := Nat.pow_le_pow_right (by norm_num) hA
  have hle : 3 ^ terrasA (parityOf β) ≤ 3 ^ terrasA (parityOf β) * t :=
    Nat.le_mul_of_pos_right _ ht
  have h8 : Hmap^[(modelOf specHModel).steps β - i] 8 ≤ 8 := by
    rcases Hmap_iter_eight ((modelOf specHModel).steps β - i) with h | h <;> omega
  change Hmap^[(modelOf specHModel).steps β - i] 8 = hC β + 3 ^ terrasA (parityOf β) * t at hiter
  norm_num at hpow
  generalize 3 ^ terrasA (parityOf β) = P at hpow hle hiter
  generalize Hmap^[(modelOf specHModel).steps β - i] 8 = Q at h8 hiter
  omega

end Collatz.Arctic.DPGen
