/-
# 𝒯: the value-level core at the level of automata (Section 10.4 of the paper)

An audit of what an earlier, longer written argument uses about the interpretation found that it uses only
(i) that the value is a sum over paths of an automaton `(u, N₀, N₁, c)` (`ValAuto`) with non-negative integer weights, read from the most significant digit; (ii) that the support monoid does not contain
zero (condition (G2) of the written argument, on the whole set of indices; the Lean `AutoG2` (at some index the diagonal entries of both binary digit matrices are at least 1) is
a sufficient condition for it, `zeroFree_of_g2`); and (iii) value-level monotonicity
`V(T n) ≤ V(n)` (`n ≥ 2`) (an audit by a reader commissioned in the internal review; an assessment, not a proof; some parts were checked against the reports of
other readers). The matrix inequality `A^k S ≥ S A^k` and a related lemma of that argument are outside the proof closure.

We introduce the value-level core of this form, `AutoValueCore` (it assumes no inequalities between rules, only value-level monotonicity), and
show `AutoValueCore → NatValueCore'` (hence also `NatValueCore` and `GenValueCore`) (`natValueCore'_of_autoValueCore`).
`AutoValueCore` has weaker premises than `NatValueCore` (it is a stronger claim). Whether they are equivalent was not checked (it is not known whether every automaton with monotone values
is realized by a weakly orienting interpretation). **Addendum**: by `h2Core` of `H2Main.lean` and
`caseACore` of `Final.lean`, `AutoValueCore` itself holds without hypotheses (`W4a.autoValueCore` of
`H2MainExtra.lean`; `allBarriers_final` passes through the assembly `natBarrierST_of_W2_W3` of §4).

(G2) is free at the level of automata: adding an isolated index (with only a self-loop of weight 1; its components of `u` and `v` are 0) does not change the values
(`addLoop`, `autoValueCore_iff_noG2`). The two premises of the core statement `W3CoreStmt` (Theorem 10.10 of the paper) do not change under `addLoop` either
(`W4a.h2Prod_addLoop_iff`, `W4a.autoMono3_liftT_addLoop_iff` of `AddLoopLift.lean`).

**A name clash** (a remark of the internal review): the relevant indices `Rel` of `Compartment.lean` (`Collatz.Arctic.NatQ5.Rel`) have the same name as Mathlib's
`Rel` (`Mathlib/Basic/Rel.lean`, `_root_.Rel α β := α → β → Prop`). Inside the namespace `Collatz.Arctic.NatQ5`
(including the namespaces below it) it resolves to `NatQ5.Rel`. Writing `Rel` from outside after `open Collatz.Arctic.NatQ5` gives an overloading with two
candidates, which is decided by the type of the argument (`ValAuto` or a type). Where the type does not decide (such as `#check @Rel`), it is an ambiguity error
(this was checked). From outside, it is better to write `NatQ5.Rel`.
-/
import CollatzProof.Arctic.Nat.Embed
import CollatzProof.Arctic.Nat.Lift
import CollatzProof.Arctic.Nat.CompartmentPi

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix

set_option linter.unusedSectionVars false

section Defs

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **A sufficient condition for (G2)**: at some index, the diagonal entries of the matrices of both binary digits are at least 1. Condition (G2) of the written argument is that
"the support monoid does not contain zero" (`ZeroFree` of §3); it follows from this condition (`zeroFree_of_g2`), but not conversely (the lift preserves `ZeroFree`
but not this diagonal form; see the note on `zeroFree_lift`; a remark of the internal review). -/
def AutoG2 (A : ValAuto Q) : Prop := ∃ q, ∀ b, 1 ≤ A.B b q q

/-- Monotonicity of values (condition (M) of the paper; the form of Lemma 10.2 (iii)): `V(T n) ≤ V(n)` for `n ≥ 2`. -/
def AutoMono (A : ValAuto Q) : Prop := ∀ n, 2 ≤ n → aval A (binWord (T n)) ≤ aval A (binWord n)

end Defs

/-- **The value-level core at the level of automata**: for an automaton that satisfies (G2) and whose values do not increase along steps of `T`, for every rule `ρ` and every `K` there are `n ≥ K` and
a segment `n → T^m n` of an orbit (all points at least 2) on which the number of uses of `ρ` exceeds the value `u^T B_{bin'(n)} v`. -/
def AutoValueCore : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : ValAuto Q), AutoG2 A → AutoMono A →
    ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ aval A (binWord n) < usesOrbit ρ n m

/-- The form without the premise (G2). -/
def AutoValueCoreNoG2 : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : ValAuto Q), AutoMono A →
    ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ aval A (binWord n) < usesOrbit ρ n m

/-! ## §1 The automata of natural-number matrix interpretations satisfy (G2) and monotonicity of values -/

theorem natAuto_g2 {d : ℕ} [NeZero d] (I : Letter → NAff d) : AutoG2 (natAuto I) :=
  ⟨none, fun b => (natAuto_diag I b).ge⟩

theorem natAuto_mono {d : ℕ} [NeZero d] {I : Letter → NAff d} (hweak : ∀ ρ ∈ rulesST, NWeak I ρ) :
    AutoMono (natAuto I) := fun n hn => by
  rw [← phiN_can_eq_aval, ← phiN_can_eq_aval]
  exact phiN_can_T_le hweak n hn

/-- The automata of general families satisfy monotonicity of values ((G2) need not hold). -/
theorem genAuto_mono {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Letter → Matrix ι ι ℕ}
    (hweak : ∀ ρ ∈ rulesST, GWeak N ρ) (a z : ι) : AutoMono (genAuto N a z) := fun n hn => by
  rw [← nw_can_eq_aval, ← nw_can_eq_aval]
  exact gnw_can_T_le hweak n hn a z

/-- **From the value-level core at the level of automata to the value-level core for natural-number matrix interpretations without monotonicity**. -/
theorem natValueCore'_of_autoValueCore (h : AutoValueCore) : NatValueCore' := by
  intro d _ I hweak ρ hρ K
  obtain ⟨n, hn, m, horb, hlt⟩ := h (Option (Fin d)) (natAuto I) (natAuto_g2 I) (natAuto_mono hweak) ρ hρ K
  exact ⟨n, hn, m, horb, by rwa [phiN_can_eq_aval]⟩

theorem natValueCore_of_autoValueCore (h : AutoValueCore) : NatValueCore :=
  natValueCore_of_core' (natValueCore'_of_autoValueCore h)

theorem genValueCore_of_autoValueCore (h : AutoValueCore) : GenValueCore :=
  genValueCore_iff.2 (natValueCore_of_autoValueCore h)

/-! ## §2 (G2) is free at the level of automata -/

section AddLoop

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The automaton with an isolated index `none` added (only a self-loop of weight 1; its components of `u` and `v` are 0). -/
def addLoop (A : ValAuto Q) : ValAuto (Option Q) where
  B b p q := match p, q with
    | some i, some j => A.B b i j
    | none, none => 1
    | _, _ => 0
  u p := match p with
    | some i => A.u i
    | none => 0
  v p := match p with
    | some i => A.v i
    | none => 0

@[simp] theorem addLoop_B_ss (A : ValAuto Q) (b : Fin 2) (i j : Q) : (addLoop A).B b (some i) (some j) = A.B b i j := rfl
@[simp] theorem addLoop_B_sn (A : ValAuto Q) (b : Fin 2) (i : Q) : (addLoop A).B b (some i) none = 0 := rfl
@[simp] theorem addLoop_B_nn (A : ValAuto Q) (b : Fin 2) : (addLoop A).B b none none = 1 := rfl
@[simp] theorem addLoop_u_s (A : ValAuto Q) (i : Q) : (addLoop A).u (some i) = A.u i := rfl
@[simp] theorem addLoop_u_n (A : ValAuto Q) : (addLoop A).u none = 0 := rfl
@[simp] theorem addLoop_v_s (A : ValAuto Q) (i : Q) : (addLoop A).v (some i) = A.v i := rfl
@[simp] theorem addLoop_v_n (A : ValAuto Q) : (addLoop A).v none = 0 := rfl

theorem DxN_addLoop (A : ValAuto Q) (w : List (Fin 2)) (i j : Q) :
    Rigid.DxN (addLoop A).B w (some i) (some j) = Rigid.DxN A.B w i j := by
  induction w generalizing i with
  | nil => simp [Matrix.one_apply]
  | cons b w ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_option, DxN_cons', Matrix.mul_apply]
    simp only [addLoop_B_sn, zero_mul, zero_add, addLoop_B_ss, ih]

theorem aval_addLoop (A : ValAuto Q) (ω : List (Fin 2)) : aval (addLoop A) ω = aval A ω := by
  rw [aval_eq_sum, aval_eq_sum, Fintype.sum_option]
  simp only [Fintype.sum_option, addLoop_u_n, addLoop_u_s, addLoop_v_n, addLoop_v_s, zero_mul, mul_zero,
    Finset.sum_const_zero, zero_add, DxN_addLoop]

theorem addLoop_g2 (A : ValAuto Q) : AutoG2 (addLoop A) := by
  exact ⟨none, fun b => (addLoop_B_nn A b).ge⟩

theorem addLoop_mono {A : ValAuto Q} (h : AutoMono A) : AutoMono (addLoop A) := fun n hn => by
  rw [aval_addLoop, aval_addLoop]; exact h n hn

end AddLoop

/-! ## §3 Zero-freeness (a premise of an earlier written argument) and the lift -/

section ZeroFree

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The support monoid does not contain zero: `B_w ≠ 0` for every word (a premise of an earlier written argument, used there on the whole set of indices). -/
def ZeroFree (A : ValAuto Q) : Prop := ∀ w, Rigid.DxN A.B w ≠ 0

theorem zeroFree_of_g2 {A : ValAuto Q} (h : AutoG2 A) : ZeroFree A := by
  obtain ⟨q, hq⟩ := h
  have hdiag : ∀ w, 1 ≤ Rigid.DxN A.B w q q := by
    intro w
    induction w with
    | nil => simp
    | cons b w ih =>
      have := one_le_DxN_append (w := [b]) (w' := w) (by simpa [Rigid.DxN] using hq b) ih
      simpa using this
  intro w hw
  have := hdiag w
  rw [hw] at this
  simp at this

/-- The lift preserves zero-freeness (the residue coordinate is moved by a permutation). It does not preserve the diagonal form of (G2)
(the self-loop `(q, r) → (q, 2r + b)` occurs only for `r ≡ -b`). -/
theorem zeroFree_lift {M : ℕ} [NeZero M] {A : ValAuto Q} (h : ZeroFree A) (Pc : Finset (ZMod M)) :
    ZeroFree (lift A M Pc) := by
  intro w hw
  apply h w
  ext k k'
  have := congrFun (congrFun hw (k, 0)) (k', 2 ^ w.length * 0 + ((valW 0 w : ℕ) : ZMod M))
  rw [Matrix.zero_apply] at this
  change Rigid.DxN (liftB A M) w _ _ = 0 at this
  rw [DxN_lift] at this
  simpa using this

/-- Monotonicity of values on numbers not divisible by 3 (condition (M₃) of the paper). -/
def AutoMono3 (A : ValAuto Q) : Prop :=
  ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval A (binWord (T n)) ≤ aval A (binWord n)

/-- The lift `\tilde V` of an automaton with monotone values is monotone on numbers not divisible by 3 (it is not monotone on multiples of 3:
`\tilde V(3) = 0` but `\tilde V(T 3) = \tilde V(5) = V(5)`). -/
theorem liftT_mono3 {A : ValAuto Q} (h : AutoMono A) : AutoMono3 (liftT A) := by
  intro n hn h3
  have h3' : ¬ 3 ∣ T n := fun h' => h3 (three_dvd_of_three_dvd_T h')
  rw [aval_liftT_of_not_dvd _ (one_le_T hn) h3', aval_liftT_of_not_dvd _ (by omega) h3]
  exact h n hn

end ZeroFree

/-- (G2) is free in the value-level core at the level of automata. -/
theorem autoValueCore_iff_noG2 : AutoValueCore ↔ AutoValueCoreNoG2 := by
  constructor
  · intro h Q _ _ A hmono ρ hρ K
    obtain ⟨n, hn, m, horb, hlt⟩ := h (Option Q) (addLoop A) (addLoop_g2 A) (addLoop_mono hmono) ρ hρ K
    exact ⟨n, hn, m, horb, by rwa [aval_addLoop] at hlt⟩
  · intro h Q _ _ A _ hmono
    exact h Q A hmono

/-! ## §4 The two targets and the assembly (the first proved without hypotheses in `H2Main.lean`, the second in `W3hCore.lean` and `Final.lean`) -/

/-- **(H2^prod) in its strong form** (condition (H2^prod) of the paper; the form of the conclusion of Corollary 10.9): all components of the relevant indices `Q'` of the lift `liftT A`
are 0/1 (including those that are not survivable). This is stronger than the (H2^prod) of an earlier written argument (every **survivable** relevant component is
0/1), which was shown there to be equivalent to (H2). Lean treats neither that equivalence nor (H2) itself (remarks of the internal reviews). -/
def H2Prod {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) : Prop :=
  ∀ C, IsComp (liftT A) C → ZeroOne (liftT A) C

/-- **The first target** (Corollary 10.9 (1) of the paper, the form at the level of automata): an automaton whose values do not increase along steps of `T` satisfies (H2^prod) in its strong form.
Proved without hypotheses as `h2Core : H2Core` in `H2Main.lean` (the three standard axioms). The only premise is value-level monotonicity `AutoMono`; inequalities between the matrices of
rules were not needed (so the fallback considered during the proof was not triggered). The proof applies the form for general automata (Theorem 10.8, `zeroOne_of_T_mono`) to the lift,
using its monotonicity on numbers not divisible by 3 (`liftT_mono3`). -/
def H2Core : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : ValAuto Q), AutoMono A → H2Prod A

/-- **The second target** (the value-level core at the level of automata, in the form used for Theorems 10.10 and 10.11 of the paper; proved without hypotheses as `caseACore` in `Final.lean`): for an automaton whose values do not
increase along steps of `T`, which is zero-free and satisfies (H2^prod), the conclusion of the value-level core holds. (A^rel) follows from (H2^prod)
(`aRel_of_zeroOne`). (H2^prod) is stronger than (A^rel), and is what a simplification of the proof needs (the components of the lift are 0/1, so a hypothesis of an earlier argument
becomes trivial and a window bound follows). -/
def CaseACore : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : ValAuto Q), AutoMono A → ZeroFree A → H2Prod A →
    ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ aval A (binWord n) < usesOrbit ρ n m

/-- (A^rel) from (H2^prod) (a step in the assembly of an earlier written proof of Theorem 9.2 (i)). -/
theorem aRel_of_h2Prod {Q : Type*} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} (h : H2Prod A) : ARel (liftT A) :=
  aRel_of_zeroOne _ h

/-- **Assembly**: the value-level core at the level of automata from the two targets. -/
theorem autoValueCore_of_W2_W3 (h2 : H2Core) (h3 : CaseACore) : AutoValueCore := by
  intro Q _ _ A hg2 hmono
  exact h3 Q A hmono (zeroFree_of_g2 hg2) (h2 Q A hmono)

/-- The statement `w3_core` of the plan of the proof of Theorem 10.10 (the premises are only (H2^prod) and monotonicity of the lift
on `3 ∤ n`; Theorem 10.10 of the paper). Its premises are weaker than those of `CaseACore`. -/
def W3CoreStmt : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : ValAuto Q), H2Prod A → AutoMono3 (liftT A) →
    ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ aval A (binWord n) < usesOrbit ρ n m

theorem caseACore_of_w3CoreStmt (h : W3CoreStmt) : CaseACore :=
  fun Q _ _ A hmono _ h01 => h Q A h01 (liftT_mono3 hmono)

/-- The form `zeroOne_liftNat` required in the plan of the proof (`liftNat I = liftT (natAuto I)`) follows from `H2Core`. -/
theorem zeroOne_liftNat_of_h2Core (h : H2Core) : ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d),
    (∀ ρ ∈ rulesST, NWeak I ρ) → ∀ C, IsComp (liftNat I) C → ZeroOne (liftNat I) C :=
  fun d _ I hweak => h (Option (Fin d)) (natAuto I) (natAuto_mono hweak)

/-- **Assembly of the main theorem**: from the two targets, the frozen statements `NatBarrierST` and `NatBarrierSTB`, and the value-level core for general families. -/
theorem natBarrierST_of_W2_W3 (h2 : H2Core) (h3 : CaseACore) :
    NatBarrierST ∧ NatBarrierSTB ∧ GenValueCore := by
  have hc := natValueCore'_of_autoValueCore (autoValueCore_of_W2_W3 h2 h3)
  exact ⟨natBarrierST_of_core' hc, natBarrierSTB_of_core' hc, genValueCore_iff.2 (natValueCore_of_core' hc)⟩

end Collatz.Arctic.NatQ5
