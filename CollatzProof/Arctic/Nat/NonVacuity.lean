/-
# Checks of the statement `NatBarrierST` (Theorem 9.2 (i) of the paper, $\mathcal T$), part 1: conventions, the rules used, satisfiable premises

Of the type of the arctic `NonVacuity*.lean`. We look for errors on the side of the statement (`Statement.lean`, written while it was a candidate for freezing; it is now frozen): vacuous premises, conclusions trivial by definition,
deviations from the definitions of the primary sources, errors in the transcription of rules. Existing files are not changed. No `sorry`, `axiom` declaration or `native_decide` is used
(computations by `decide +kernel`).

* §1 Agreement with the conventions of Yolcu–Aaronson–Heule (arXiv:2105.14697v3):
  - Formula (2) (Lemma 4 of Endrullis–Waldmann–Zantema 2008): `NWeak` and `NStrict` are equivalent to the orders `≳` and `>` of vectors of Yolcu–Aaronson–Heule, §2.3.1, at all `y ∈ ℕ^d`
    (`>` is strict in the first component and `≥` in the others) (`nweak_iff_forall`, `nstrict_iff_forall`).
  - Extended monotone algebras (Yolcu–Aaronson–Heule, Definition 2.14 and §2.3.1): weakly monotone with respect to `≳` (for every interpretation), monotone with respect to `>` if `NMono`,
    `> · ≳ ⊆ >`, and `>` is well-founded. So the class of interpretations of the statement contains the natural-number matrix interpretations of Yolcu–Aaronson–Heule (`(M_σ)_{1,1} = 1`).
  - Converse (internal review): monotonicity with respect to `>` implies `(M)₀₀ ≥ 1` (`one_le_M00_of_mono_gt`). So
    in this class (natural-number matrix interpretations with the order of Yolcu–Aaronson–Heule, §2.3.1), `NMono` is equivalent to extended monotonicity (`nmono_iff_extMono`).
    The monotonicity premise of the statement is thus self-contained, independently of the source of the condition of Endrullis–Waldmann–Zantema 2008 (not checked in the primary source).
  - Direction of composition: the values `[f.]`, `[.]`, `[t.]`, `[2.]`, printed in Example 4.3 of Yolcu–Aaronson–Heule (an interpretation of dimension 2 for $\mathcal T$ without `f1 → 0t`), and
    `[f0]`, `[0f]` are recomputed with `evN` and agree (with composition in the opposite direction the matrix of `[f.]` differs).
* §2 "The rules used": for each of the 11 rules there is `n ≥ 2` such that the rule occurs in `canDeriv n` (`rulesST_used`). Conversely, the rules of `canDeriv n`
  are among the 11 rules (`used_mem`). The statement `NatBarrierSTUsed`, written with "the rules used", is equivalent to `NatBarrierST`.
* §3 (a) The premises are satisfiable: the identity interpretation in every dimension `d ≥ 1`; the example of dimension 4 of Proposition 9.5 of the paper (`Φ(can n)`
  grows with the length on `3 ∣ n`); and a further example EX1, found by a SAT search (an interpretation of dimension 4 with a heavy
  component). All three are also consistent with the conclusion of the main theorem (they strictly orient no rule).

(b) to (d) are in `NonVacuity2.lean`.
-/
import CollatzProof.Arctic.Nat.Bridge

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter

variable {d : ℕ}

/-! ## §1 Agreement with the conventions of Yolcu–Aaronson–Heule -/

/-- The order `≳` of vectors of Yolcu–Aaronson–Heule, §2.3.1: `≥` in every component. -/
def VGe (x y : Fin d → ℕ) : Prop := ∀ i, y i ≤ x i

/-- The order `>` of vectors of Yolcu–Aaronson–Heule, §2.3.1: strictly larger in the first component (index 0) and `≥` in the other components. -/
def VGt [NeZero d] (x y : Fin d → ℕ) : Prop := y 0 < x 0 ∧ ∀ i : Fin d, i ≠ 0 → y i ≤ x i

/-- **The second line of formula (2) of Yolcu–Aaronson–Heule**: `NWeak` is equivalent to "`[ℓ](y) ≳ [r](y)` for all `y`". -/
theorem nweak_iff_forall (I : Letter → NAff d) (ρ : Rule) :
    NWeak I ρ ↔ ∀ y, VGe ((evN I ρ.lhs).app y) ((evN I ρ.rhs).app y) := by
  constructor
  · intro h y i
    exact app_le_of_weak h y i
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · by_contra hle
      have hlt := Nat.lt_of_not_le hle
      -- `y = N e_j` with `N = (v_ℓ)_i + 1` gives a contradiction
      have hy := h (Pi.single j ((evN I ρ.lhs).v i + 1)) i
      simp only [NAff.app, Pi.add_apply, mulVec, dotProduct_single] at hy
      have hm : ((evN I ρ.lhs).M i j + 1) * ((evN I ρ.lhs).v i + 1) ≤
          (evN I ρ.rhs).M i j * ((evN I ρ.lhs).v i + 1) := Nat.mul_le_mul_right _ hlt
      rw [Nat.succ_mul] at hm
      omega
    · simpa [NAff.app] using h 0 i

/-- **The first line of formula (2) of Yolcu–Aaronson–Heule**: `NStrict` is equivalent to "`[ℓ](y) > [r](y)` for all `y`". -/
theorem nstrict_iff_forall [NeZero d] (I : Letter → NAff d) (ρ : Rule) :
    NStrict I ρ ↔ ∀ y, VGt ((evN I ρ.lhs).app y) ((evN I ρ.rhs).app y) := by
  constructor
  · intro h y
    exact ⟨app0_lt_of_strict h y, fun i _ => app_le_of_weak h.1 y i⟩
  · intro h
    refine ⟨(nweak_iff_forall I ρ).2 fun y i => ?_, ?_⟩
    · by_cases hi : i = 0
      · subst hi; exact (h y).1.le
      · exact (h y).2 i hi
    · simpa [NAff.app] using (h 0).1

/-- The dot product with non-negative coefficients is monotone. -/
theorem dot_le_dot (a x z : Fin d → ℕ) (h : ∀ i, z i ≤ x i) : a ⬝ᵥ z ≤ a ⬝ᵥ x :=
  Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (h i)

/-- If component 0 increases by at least 1, the dot product increases by at least `a 0`. -/
theorem dot_add_le [NeZero d] (a x z : Fin d → ℕ) (h : ∀ i, z i ≤ x i) (h0 : z 0 + 1 ≤ x 0) :
    a ⬝ᵥ z + a 0 ≤ a ⬝ᵥ x := by
  unfold dotProduct
  rw [← Finset.add_sum_erase _ (fun i => a i * x i) (Finset.mem_univ 0),
    ← Finset.add_sum_erase _ (fun i => a i * z i) (Finset.mem_univ 0)]
  have hs : ∑ i ∈ Finset.univ.erase 0, a i * z i ≤ ∑ i ∈ Finset.univ.erase 0, a i * x i :=
    Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (h i)
  have h1 : a 0 * (z 0 + 1) ≤ a 0 * x 0 := Nat.mul_le_mul_left _ h0
  rw [Nat.mul_succ] at h1
  omega

/-- Extended monotone algebras (Yolcu–Aaronson–Heule, Definition 2.14): every interpretation is monotone with respect to `≳`. -/
theorem app_mono_ge (F : NAff d) {x y : Fin d → ℕ} (h : VGe x y) : VGe (F.app x) (F.app y) := by
  intro i
  simp only [NAff.app, Pi.add_apply, mulVec]
  exact Nat.add_le_add_right (dot_le_dot _ _ _ h) _

/-- Extended monotone algebras (Yolcu–Aaronson–Heule, Definition 2.14): monotone with respect to `>` if `(M)₀₀ ≥ 1`. -/
theorem app_mono_gt [NeZero d] (F : NAff d) (hF : 1 ≤ F.M 0 0) {x y : Fin d → ℕ} (h : VGt x y) :
    VGt (F.app x) (F.app y) := by
  have hge : ∀ i, y i ≤ x i := fun i => by
    by_cases hi : i = 0
    · subst hi; exact h.1.le
    · exact h.2 i hi
  refine ⟨?_, fun i _ => app_mono_ge F hge i⟩
  simp only [NAff.app, Pi.add_apply, mulVec]
  have h1 := dot_add_le (fun j => F.M 0 j) x y hge h.1
  have h2 : (fun j => F.M 0 j) 0 = F.M 0 0 := rfl
  omega

/-- `> · ≳ ⊆ >` (the compatibility condition of Yolcu–Aaronson–Heule, Definition 2.14). -/
theorem vgt_of_vgt_vge [NeZero d] {x y z : Fin d → ℕ} (h1 : VGt x y) (h2 : VGe y z) : VGt x z :=
  ⟨lt_of_le_of_lt (h2 0) h1.1, fun i hi => (h2 i).trans (h1.2 i hi)⟩

/-- `>` is well-founded (a descending sequence strictly decreases in component 0). -/
theorem vgt_wf [NeZero d] : WellFounded (fun x y : Fin d → ℕ => VGt y x) :=
  Subrelation.wf (fun {x y} (h : VGt y x) => (show x 0 < y 0 from h.1))
    (InvImage.wf (fun x : Fin d → ℕ => x 0) wellFounded_lt)

/-- **Converse** (internal review): monotonicity with respect to `>` implies `(M)₀₀ ≥ 1`. If `(M)₀₀ = 0`, then `x = e₀`, `y = 0` is a counterexample
(`x > y`, but `F(x)₀ = (M)₀₀ + v₀ = v₀ = F(y)₀`). -/
theorem one_le_M00_of_mono_gt [NeZero d] (F : NAff d)
    (hF : ∀ x y : Fin d → ℕ, VGt x y → VGt (F.app x) (F.app y)) : 1 ≤ F.M 0 0 := by
  by_contra h
  have h0 : F.M 0 0 = 0 := by omega
  have hxy : VGt (Pi.single 0 1) (0 : Fin d → ℕ) := ⟨by simp, fun i _ => Nat.zero_le _⟩
  have := (hF _ _ hxy).1
  simp [NAff.app, h0] at this

/-- For one letter: monotone with respect to `>` ⟺ `(M)₀₀ ≥ 1`. -/
theorem app_mono_gt_iff [NeZero d] (F : NAff d) :
    (∀ x y : Fin d → ℕ, VGt x y → VGt (F.app x) (F.app y)) ↔ 1 ≤ F.M 0 0 :=
  ⟨one_le_M00_of_mono_gt F, fun hF _ _ h => app_mono_gt F hF h⟩

/-- The condition on the letters of an extended monotone algebra (Yolcu–Aaronson–Heule, Definition 2.14): the interpretation of every letter is monotone with respect to both `≳` and `>`. The conditions on the orders
(`>` is well-founded, `> · ≳ ⊆ >`) hold in this class for every interpretation (`vgt_wf`, `vgt_of_vgt_vge`). -/
def ExtMono [NeZero d] (I : Letter → NAff d) : Prop :=
  ∀ s, (∀ x y : Fin d → ℕ, VGe x y → VGe ((I s).app x) ((I s).app y)) ∧
    (∀ x y : Fin d → ℕ, VGt x y → VGt ((I s).app x) ((I s).app y))

/-- **The monotonicity premise is self-contained**: in the class of natural-number matrix interpretations, `NMono` (`(M_s)₀₀ ≥ 1` for all letters) is equivalent to
extended monotonicity. -/
theorem nmono_iff_extMono [NeZero d] (I : Letter → NAff d) : NMono I ↔ ExtMono I :=
  ⟨fun h s => ⟨fun _ _ hxy => app_mono_ge (I s) hxy, fun _ _ hxy => app_mono_gt (I s) (h s) hxy⟩,
    fun h s => one_le_M00_of_mono_gt (I s) (h s).2⟩

/-- The interpretation of dimension 2 of Example 4.3 of Yolcu–Aaronson–Heule (a termination proof in one step for $\mathcal T$ without `f1 → 0t`). -/
def IYAH : Letter → NAff 2
  | .f => ⟨!![1, 1; 1, 0], ![0, 0]⟩
  | .t => ⟨!![1, 3; 3, 4], ![1, 1]⟩
  | .lft => ⟨!![1, 5; 0, 0], ![0, 0]⟩
  | .rgt => ⟨!![1, 0; 1, 0], ![1, 1]⟩
  | .d0 => ⟨!![7, 2; 2, 5], ![2, 1]⟩
  | .d1 => ⟨!![2, 1; 1, 1], ![1, 0]⟩
  | .d2 => ⟨!![2, 2; 2, 4], ![0, 2]⟩

/-- Check of the direction of composition: agreement with the values printed in Example 4.3 of Yolcu–Aaronson–Heule. -/
theorem yah_ex43_values :
    ((evN IYAH [f, rgt]).M = !![2, 0; 1, 0] ∧ (evN IYAH [f, rgt]).v = ![2, 1]) ∧
    ((evN IYAH [rgt]).M = !![1, 0; 1, 0] ∧ (evN IYAH [rgt]).v = ![1, 1]) ∧
    ((evN IYAH [t, rgt]).M = !![4, 0; 7, 0] ∧ (evN IYAH [t, rgt]).v = ![5, 8]) ∧
    ((evN IYAH [d2, rgt]).M = !![4, 0; 6, 0] ∧ (evN IYAH [d2, rgt]).v = ![4, 8]) ∧
    ((evN IYAH [f, d0]).M = !![9, 7; 7, 2] ∧ (evN IYAH [f, d0]).v = ![3, 2]) ∧
    ((evN IYAH [d0, f]).M = !![9, 7; 7, 2] ∧ (evN IYAH [d0, f]).v = ![2, 1]) := by
  decide +kernel

/-- With composition in the opposite direction (`[s₁ ⋯ sₙ] = [sₙ] ∘ ⋯ ∘ [s₁]`) the matrix of `[f.]` is `M_. M_f`, which differs from the value of Yolcu–Aaronson–Heule. -/
theorem yah_ex43_reversed_differs : (IYAH rgt).M * (IYAH f).M ≠ !![2, 0; 1, 0] := by
  decide +kernel

/-! ## §2 "The rules used" -/

/-- Each of the 11 rules is used by the canonical derivations (witnesses `n`: 2 for `f.→.`, 3 for `t.→2.` and `/2→/ft`, 5 for `f2→1f` and `/1→/ff`,
7 for `t2→2t`, 9 for `f1→0t` and `/0→/t`, 13 for `t1→2f`, 17 for `f0→0f`, 25 for `t0→1t`). -/
theorem rulesST_used : ∀ ρ ∈ rulesST, UsedST ρ := by
  intro ρ hρ
  simp only [rulesST, List.mem_cons, List.mem_nil_iff, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, le_refl _, by decide +kernel⟩
  · exact ⟨3, by norm_num, by decide +kernel⟩
  · exact ⟨17, by norm_num, by decide +kernel⟩
  · exact ⟨9, by norm_num, by decide +kernel⟩
  · exact ⟨5, by norm_num, by decide +kernel⟩
  · exact ⟨25, by norm_num, by decide +kernel⟩
  · exact ⟨13, by norm_num, by decide +kernel⟩
  · exact ⟨7, by norm_num, by decide +kernel⟩
  · exact ⟨9, by norm_num, by decide +kernel⟩
  · exact ⟨5, by norm_num, by decide +kernel⟩
  · exact ⟨3, by norm_num, by decide +kernel⟩

/-- The rules used by the canonical derivations are among the 11 rules. -/
theorem used_mem {ρ : Rule} (h : UsedST ρ) : ρ ∈ rulesST := by
  obtain ⟨n, -, hn⟩ := h
  exact canDeriv_sub n ρ hn

theorem usedST_iff (ρ : Rule) : UsedST ρ ↔ ρ ∈ rulesST := ⟨used_mem, rulesST_used ρ⟩

/-- The statement written with "the rules used" is equivalent to `NatBarrierST`. -/
theorem natBarrierST_iff_used : NatBarrierST ↔ NatBarrierSTUsed := by
  constructor
  · intro h d _ I hmono hweak ρ hρ
    exact h d I hmono (fun σ hσ => hweak σ (rulesST_used σ hσ)) ρ (used_mem hρ)
  · intro h d _ I hmono hweak ρ hρ
    exact h d I hmono (fun σ hσ => hweak σ (used_mem hσ)) ρ (rulesST_used ρ hρ)

/-! ## §3 (a) The premises are satisfiable -/

/-- Under the identity interpretation every word is interpreted by the identity. -/
theorem evN_idI (d : ℕ) : ∀ w : Word, evN (fun _ => NAff.id d) w = NAff.id d
  | [] => rfl
  | s :: w => by
    show (NAff.id d).comp (evN (fun _ => NAff.id d) w) = NAff.id d
    rw [evN_idI d w, NAff.id_comp]

/-- In every dimension `d ≥ 1` the identity interpretation is monotone and weakly orients all 11 rules. -/
theorem premises_id (d : ℕ) [NeZero d] :
    NMono (fun _ : Letter => NAff.id d) ∧ ∀ ρ ∈ rulesST, NWeak (fun _ : Letter => NAff.id d) ρ := by
  refine ⟨fun _ => by simp [NAff.id], fun ρ _ => ?_⟩
  rw [NWeak, evN_idI, evN_idI]
  exact ⟨fun _ _ => le_rfl, fun _ => le_rfl⟩

/-- The example of dimension 4 of Proposition 9.5 of the paper for $\mathcal T$ (the matrices of `NatExample.IT = interp 1 0` written out). -/
def IP3 : Letter → NAff 4
  | .f => ⟨!![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0], 0⟩
  | .t => ⟨!![1, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 2], 0⟩
  | .d0 => ⟨!![1, 0, 0, 0; 0, 4, 0, 0; 0, 4, 0, 0; 0, 4, 0, 0], 0⟩
  | .d1 => ⟨!![1, 0, 0, 0; 0, 0, 4, 0; 0, 0, 4, 0; 0, 0, 4, 0], 0⟩
  | .d2 => ⟨!![1, 0, 0, 0; 0, 0, 0, 4; 0, 0, 0, 4; 0, 0, 0, 4], 0⟩
  | .lft => ⟨!![1, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], 0⟩
  | .rgt => ⟨!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], ![1, 1, 0, 0]⟩

theorem IP3_mono : NMono IP3 := fun s => by cases s <;> decide

theorem IP3_weak : ∀ ρ ∈ rulesST, NWeak IP3 ρ := by decide +kernel

theorem IP3_not_strict : ∀ ρ ∈ rulesST, ¬ NStrict IP3 ρ := by decide +kernel

/-- Small values of `Φ(can n) = 1 + 2^{ℓ(n)-1}[3 ∣ n]` (`NatExample.phi_can_T`): on `3 ∣ n` they grow with the length. -/
theorem IP3_phi_values :
    PhiN IP3 (can 3) = 3 ∧ PhiN IP3 (can 6) = 5 ∧ PhiN IP3 (can 12) = 9 ∧ PhiN IP3 (can 24) = 17 ∧
    PhiN IP3 (can 5) = 1 ∧ PhiN IP3 (can 7) = 1 := by
  decide +kernel

/-- A further example EX1, found by a SAT search (the letters as in the TPDB: `b0` = `f`, `b1` = `t`,
`t0..t2` = `d0..d2`, `&` = `lft`, `$` = `rgt`; matrices row by row). It has a heavy component (relevant, not survivable, `ρ ≥ 2`). -/
def IEX1 : Letter → NAff 4
  | .f => ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 0], ![0, 0, 0, 0]⟩
  | .t => ⟨!![1, 0, 1, 0; 0, 0, 0, 2; 0, 0, 2, 0; 0, 1, 0, 0], ![0, 0, 0, 0]⟩
  | .d0 => ⟨!![1, 0, 0, 0; 0, 0, 0, 0; 0, 1, 3, 0; 0, 0, 0, 0], ![0, 0, 0, 0]⟩
  | .d1 => ⟨!![1, 0, 1, 0; 0, 0, 0, 0; 0, 0, 3, 1; 0, 0, 0, 0], ![0, 0, 0, 0]⟩
  | .d2 => ⟨!![1, 0, 2, 0; 0, 0, 0, 0; 0, 0, 3, 0; 0, 0, 0, 0], ![0, 0, 0, 0]⟩
  | .lft => ⟨!![2, 0, 2, 2; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], ![1, 0, 0, 0]⟩
  | .rgt => ⟨!![3, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], ![1, 1, 0, 0]⟩

theorem IEX1_mono : NMono IEX1 := fun s => by cases s <;> decide

theorem IEX1_weak : ∀ ρ ∈ rulesST, NWeak IEX1 ρ := by decide +kernel

theorem IEX1_not_strict : ∀ ρ ∈ rulesST, ¬ NStrict IEX1 ρ := by decide +kernel

end Collatz.Arctic.NatQ5
