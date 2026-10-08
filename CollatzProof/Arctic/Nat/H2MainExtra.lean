/-
# Supplements to Section 11: components without internal edges, the pointwise form, the remark in Section 11.5, the value-level core for automata

Outside the closure of the main theorem (`allBarriers_final` does not use this file).

* **§1 Components without internal edges are 0/1 as well** (a point of internal review. **Source**: copied from `zeroOne_all_scc` of a scratch file
  `AllScc.lean` written in that review): under the hypotheses of Theorem 10.8 (`zeroOne_of_T_mono`), all strongly connected components of relevant indices are
  0/1, with or without internal edges. This matches literally the phrase "all components of `Q'`" (`IsComp` requires an internal edge).
  On a component without internal edges, products of non-empty words are 0 and the product of the empty word is the identity, so 0/1 is trivial.
* **§2 The pointwise form** (the same point of review. **Source**: `h2Prod_pointwise` of the same scratch file): (H2^prod) written without `IsComp`,
  as `(\tilde B_w)_{xy} ≤ 1` for any two points `x, y` of the component of a point `p` of `Q'` (`QPrime A`).
* **§3 The remark at the end of Section 11.5** (a point of internal review; matched to the wording of that remark): if the value automaton
  `A` satisfies `V(T n) ≤ V(n)` only for `n ≥ 2` not divisible by 3 (`AutoMono3 A`, condition (M) weakened to numbers not divisible by 3), then
  (1) all components of the lift `\tilde A := liftT A` are 0/1 (`H2Prod A`), and (2) there is `C` with, for all `n ≥ 1`,
  `Ṽ(n) ≤ C (ℓ(n) + 1)^{|\mathcal R(\tilde A)|}` (`ℓ(n) = ⌊log₂ n⌋`, `|\mathcal R(\tilde A)| = |Q'|`). In particular, for `n` not divisible
  by 3, `V(n)` grows at most polynomially in `ℓ(n)` (`cor86_5_2_not_dvd`).
  - Parts: `liftT_mono3_of_mono3`, the version of `liftT_mono3` for numbers not divisible by 3 (the proof of `liftT_mono3` uses (M) only for `n` not divisible
    by 3), Theorem 10.8 (`zeroOne_of_T_mono`), `gDiag_restrictRel_le_one` (the diagonal of the restriction is at most `1^{|x|}`),
    `aval_poly_bound`, the Lean form of Corollary 11.2 (`G = 1`), `aval_restrictRel` (the value does not change under the restriction), and
    `W3a.length_binWord`, `fam_lenT_eq_log` (`|bin'(n)| = ⌊log₂ n⌋`).
* **§4 The value-level core for automata** (resolving the concern of lines 75–77 of the frozen `Statement.lean`; Theorem 10.11):
  the form `AutoValueCore` (`AutoCore.lean`) that assumes only the value-level monotonicity `AutoMono` and the sufficient condition `AutoG2` for (G2) also holds
  without hypotheses (just pass `h2Core` (Section 11) and `caseACore` (Section 12) to the assembly `autoValueCore_of_W2_W3`; `allBarriers_final`
  goes through this assembly). Also the form without `AutoG2` (`autoValueCore_iff_noG2`).
-/
import CollatzProof.Arctic.Nat.Final

namespace Collatz.Arctic.NatQ5.W4a

open Collatz.Arctic Collatz.Arctic.NatQ5

set_option linter.unusedSectionVars false

/-! ## §1 Components without internal edges are 0/1 as well -/

/-- **All strongly connected components of relevant indices are 0/1** (including those without internal edges; the example of the internal review). -/
theorem zeroOne_all_scc {Q : Type*} [Fintype Q] [DecidableEq Q] (L : ValAuto Q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0) :
    ∀ q, Rel L q → ZeroOne L (sccOf L q) := by
  intro q hq
  by_cases hE : HasEdge L (sccOf L q)
  · exact zeroOne_of_T_mono L hT h3 _ ⟨⟨q, hq, rfl⟩, hE⟩
  · intro w x y
    cases w with
    | nil =>
      show Rigid.DxN (compMat L (sccOf L q)) [] x y ≤ 1
      rw [DxN_nil', Matrix.one_apply]; split_ifs <;> simp
    | cons b w =>
      show Rigid.DxN (compMat L (sccOf L q)) (b :: w) x y ≤ 1
      rw [DxN_cons', compMat_eq_zero_of_not_hasEdge L q hE b, zero_mul]; simp

/-! ## §2 The pointwise form -/

/-- **The pointwise form of (H2^prod)** (the example of the internal review): for an automaton `A` whose value does not increase along steps of `T`, for any two points `x, y` of the component
of a point `p` of `Q'` and any word `w`, `(\tilde B_w)_{xy} ≤ 1`. -/
theorem h2Prod_pointwise {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) (hA : AutoMono A) :
    ∀ p ∈ QPrime A, ∀ (w : List (Fin 2)) (x y : Q × ZMod 3), x ∈ sccOf (liftT A) p → y ∈ sccOf (liftT A) p →
      Rigid.DxN (liftT A).B w x y ≤ 1 := by
  intro p hp w x y hx hy
  have hrel : Rel (liftT A) p := (mem_QPrime A p).1 hp
  have h := zeroOne_all_scc (liftT A) (liftT_mono3 hA) (aval_liftT_three_dvd A) p hrel w ⟨x, hx⟩ ⟨y, hy⟩
  rwa [DC_apply] at h

/-! ## §3 The remark at the end of Section 11.5 -/

/-- **The version of `liftT_mono3` for numbers not divisible by 3**: if the monotonicity of the base values is weakened to numbers not divisible by 3, the lift is still monotone
on the numbers not divisible by 3. -/
theorem liftT_mono3_of_mono3 {Q : Type*} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} (h : AutoMono3 A) :
    AutoMono3 (liftT A) := by
  intro n hn h3
  have h3' : ¬ 3 ∣ Collatz.Arctic.T n := fun h' => h3 (three_dvd_of_three_dvd_T h')
  rw [aval_liftT_of_not_dvd _ (one_le_T hn) h3', aval_liftT_of_not_dvd _ (by omega) h3]
  exact h n hn h3

/-- **The remark at the end of Section 11.5**: if the base value does not increase along steps of `T` only for `n ≥ 2` not divisible by 3 (`AutoMono3 A`), then (1) all components of the lift
are 0/1 (`H2Prod A`), and (2) there is `C ≥ 0` with, for all `n ≥ 1`,
`Ṽ(n) ≤ C (⌊log₂ n⌋ + 1)^{|Q'|}` (`|Q'| = |\mathcal R(\tilde A)|`). -/
theorem cor86_5_2 {Q : Type*} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} (h : AutoMono3 A) :
    H2Prod A ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n, 1 ≤ n →
      (aval (liftT A) (binWord n) : ℝ) ≤ C * ((Nat.log 2 n : ℝ) + 1) ^ (QPrime A).card := by
  have hT := liftT_mono3_of_mono3 h
  refine ⟨zeroOne_of_T_mono (liftT A) hT (aval_liftT_three_dvd A), ?_⟩
  have hG := gDiag_restrictRel_le_one (liftT A) hT (aval_liftT_three_dvd A)
  have hdiag : ∀ (w : List (Fin 2)) (i : relSet (liftT A)),
      Rigid.Dx (restrictRel (liftT A)).B w i i ≤ (1 : ℝ) ^ w.length := fun w i =>
    (Rigid.diag_le_gDiag _ w i).trans (pow_le_pow_left₀ (Rigid.gDiag_nonneg _) hG _)
  obtain ⟨C, hC, hb⟩ := aval_poly_bound (restrictRel (liftT A)) le_rfl hdiag
  refine ⟨C, hC, fun n _ => ?_⟩
  have hn := hb (binWord n)
  rw [aval_restrictRel, one_pow, mul_one, W3a.length_binWord, fam_lenT_eq_log, Fintype.card_coe] at hn
  exact hn

/-- **"In particular" of the remark**: `V(n) ≤ C (⌊log₂ n⌋ + 1)^{|Q'|}` for `n ≥ 1` not divisible by 3. -/
theorem cor86_5_2_not_dvd {Q : Type*} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} (h : AutoMono3 A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, 1 ≤ n → ¬ 3 ∣ n →
      (aval A (binWord n) : ℝ) ≤ C * ((Nat.log 2 n : ℝ) + 1) ^ (QPrime A).card := by
  obtain ⟨-, C, hC, hb⟩ := cor86_5_2 h
  exact ⟨C, hC, fun n hn h3 => by rw [← aval_liftT_of_not_dvd A hn h3]; exact hb n hn⟩

/-! ## §4 The value-level core for automata -/

/-- **The value-level core for automata** (`AutoValueCore` of `AutoCore.lean`, assuming only `AutoG2` and the monotonicity of values `AutoMono`),
without hypotheses. The concern of lines 75–77 of the frozen `Statement.lean`, "whether the form that assumes only value-level monotonicity … holds has not
been checked", is resolved by this form. -/
theorem autoValueCore : AutoValueCore := autoValueCore_of_W2_W3 h2Core caseACore

/-- The form without `AutoG2` as well (`autoValueCore_iff_noG2`: adding isolated indices does not change the values). -/
theorem autoValueCoreNoG2 : AutoValueCoreNoG2 := autoValueCore_iff_noG2.1 autoValueCore

end Collatz.Arctic.NatQ5.W4a
