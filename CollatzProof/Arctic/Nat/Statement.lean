/-
# The barrier for natural-number matrix interpretations of the system 𝒯: the statement of the main theorem

Theorem 9.2 (i) of the paper (the part for 𝒯): a natural-number matrix interpretation of any finite dimension
in which the matrix of every letter is monotone (`(M_s)₀₀ ≥ 1`) and which weakly orients all used rules of 𝒯 (collatz-T of the TPDB, 11 rules)
strictly orients none of the used rules. This is the statement chosen in response to the question raised by YAH (CADE 2021, §7; WST 2021, §4).
**This statement is frozen** (after an internal independent review, which found no serious problem; its remarks have been taken in).

## Sources of the definitions

`NAff`, `NAff.app`, `NAff.comp`, `NAff.id`, `evN`, `NWeak`, `NStrict`, `PhiN` and the decidability instances are
copied from the definitions of `CollatzProof/Arctic/NatExample.lean` (Proposition 9.5 of the paper) (only the namespace differs; the bodies are the same).
Since `NatExample.lean` imports `RH.Defs` and `HModel.Defs`, they were copied to keep the closure of the statement small.
The letters `Letter`, the rules `Rule`, the 11 rules `rulesST`, `can` and `T` are those of `Defs.lean`; the canonical derivation `canDeriv` and the number of uses `usesOrbit` are
those of the arctic `Statement.lean` (frozen), used as they are.

## Conventions (checked against the primary sources)

YAH = Yolcu–Aaronson–Heule, arXiv:2105.14697v3 (J. Autom. Reasoning 2023). The places checked are §2.2, §2.3.1, equation (2),
Thm 2.6, Def 2.14, Thm 2.15, the table of the 11 rules in §3.2 (after equation (8)) and Example 4.3 (the text of the arXiv PDF).
EWZ08 = Endrullis–Waldmann–Zantema, J. Autom. Reasoning 40 (2008) (Thm 2.15 of YAH is cited as Thm 2 of EWZ08, and equation (2) as
Lemma 4 of EWZ08. The text of EWZ08 was not checked for this file; only what the restatement in YAH provides is used. This note predates the check of EWZ08 in the primary source).

1. **Dimension** `d ≥ 1` (`d ∈ ℕ⁺` of YAH §2.3.1): `[NeZero d]`.
2. **Interpretation of a letter** `[s](y) = M_s y + v_s` (`M_s ∈ ℕ^{d×d}`, `v_s ∈ ℕ^d`; YAH §2.3.1): `NAff d`.
3. **The interpretation of a word** is the composition `[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]` (YAH §2.2; the empty word is the identity): `evN`. This is the same direction as reading
   the term `(b0 ($ x1))` of the TPDB `.ari` file as `[b0]([$](x))` (`evN_app` of `Bridge.lean`). The computation of Example 4.3 of YAH
   (`[f.] = M_f M_. x + M_f v_.`) also has this direction, and §1 of `NonVacuity.lean` recomputes the same values (`yah_ex43_values`). **Note**: the reading of
   values in YAH §3.2 (equation (8), `Val(/0f1.) = .(1(f(0(/(x)))))`) composes in the opposite direction and is not the convention for matrix interpretations.
4. **Monotonicity**: `(M_s)₀₀ ≥ 1` for every letter (the index `o` is `0` in Lean, the index 1 in the paper and in YAH): `NMono`.
   The only facts checked about the sources are these. YAH §2.3.1 restates that "setting `(M_σ)_{1,1} = 1` gives an extended monotone algebra",
   that is, `= 1` **as a sufficient condition** for extended monotonicity. That the condition of EWZ08 is "the upper left entry is positive" is
   hearsay, since the text of EWZ08 was not seen (this note predates the check of [EWZ08, §4, p. 201], where this condition is stated). The statement treats all of `≥ 1` and includes the `= 1` of YAH
   (a stronger claim than the form of YAH). That `≥ 1` is **equivalent** to extended monotonicity (Def 2.14 of YAH) in this class (natural-number matrix interpretations with the order `≳`, `>`
   of YAH §2.3.1) is shown in Lean, independently of the sources (§1 of `NonVacuity.lean`): `≥ 1` gives extended monotonicity
   (`app_mono_ge`, `app_mono_gt`, `vgt_of_vgt_vge`, `vgt_wf`), and conversely monotonicity with respect to `>` gives `≥ 1`
   (`one_le_M00_of_mono_gt`: if `(M)₀₀ = 0`, then `x = e₀` and `y = 0` satisfy `x > y` but `F(x)₀ = F(y)₀`); together
   `nmono_iff_extMono`. That any index `k` of monotonicity gives the same statement is shown in `Nat/Coord.lean` (permutation of coordinates).
5. **Weak orientation** `[ℓ] ≳ [r]`: `M_ℓ ≥ M_r` and `v_ℓ ≥ v_r` (entrywise; the second line of equation (2) of YAH): `NWeak`.
6. **Strict orientation** `[ℓ] > [r]`: `M_ℓ ≥ M_r` and `v_ℓ > v_r`. For vectors, `>` means "strictly larger in the first component and `≥` in the
   other components" (YAH §2.3.1, the first line of equation (2)): `NStrict` (weak orientation together with the strict inequality in the first component (index 0) of `v`).
   The equivalence of equation (2) (with the order at every `y ∈ ℕ^d`) is proved in §1 of `NonVacuity.lean`.
7. **Rule removal** (Thm 2.6 of YAH (Zantema 2005) and Thm 2.15 (Thm 2 of EWZ08)): one step for `SN(R)` weakly orients all rules of `R` and
   strictly orients a nonempty `R' ⊆ R` by an extended monotone algebra, which gives `SN(R'/R)`. The conclusion of the statement is that in the first step with `R = 𝒯`
   no rule can be removed (so rule removal on 𝒯 in its own direction cannot show termination of 𝒯 in any number of steps).
   "In any number of steps" refers only to removing rules step by step by monotone natural-number matrix interpretations of 𝒯 in its own direction. Other forms that YAH itself
   uses for `T` (the reversed system, the top forms) are outside this statement, as listed under "Scope" below.

## Scope

`NatBarrierST` covers only rule removal on 𝒯 in its own direction (one step by a monotone natural-number matrix interpretation, item 7 above).
The following are outside this statement (as noted in the internal review):

* **Removal by interpretations of the reversed system 𝒯^rev** (`SN(R'/𝒯) ⟺ SN(R'^rev/𝒯^rev)` by Lemma 2.8 of YAH; Lemma 3.15 of YAH
  uses this form). Unlike the arctic case, the class of natural-number matrix interpretations is not closed under transposition (the transpose of a homogeneous matrix is not of the same form), so
  it does not follow directly from this statement (this note predates `StatementRev.lean`: its statement `NatBarrierSTrev` covers this form).
* **Removal in the top form by weakly monotone algebras (no monotonicity condition)** (Lemma 3.18 of YAH: (1) removes left-end rules `B` of 𝒯
  in the form `SN(R_top/𝒯)` (`R ⊆ B`), and (2) removes the dynamic rules `D_T` of the reversed system in the form `SN(Q^rev_top/𝒯^rev)`).
  The natural-number form of (1) is covered by the separate statement `NatBarrierSTB` of §4 (no monotonicity premise; proved from the value-level core
  without monotonicity `NatValueCore'`, `BridgeTop.lean`). (2) is not covered (this note predates `StatementRev.lean`: its statement `NatBarrierSTrevTop` covers (2)).
* **The core form of Hofbauer–Waldmann and the dependency pair framework** (this note predates `StatementDP.lean`, whose statements `NatBarrierDP` and `NatBarrierDPrev` cover the dependency pair forms of Theorem 9.2 (iii)).

## The used rules

The used rules are the rules that occur in the canonical derivation `can n →* can (T n)` (`n ≥ 2`; `canDeriv` of the arctic `Statement.lean`, the canonical-derivation lemma of Paper II,
proved correct by `canDeriv_chain` of `Canon.lean`; Lemma 2.3 of the paper). In 𝒯 all 11 rules
are used. Like the frozen arctic statement `ArcticBarrierST`, the statement is written with all 11 rules `rulesST`.
That the two agree is proved in §2 of `NonVacuity.lean` (`rulesST_used`: for each rule, a witness `n ≥ 2` such that the rule occurs in `canDeriv n`;
`used_mem`: the rules of `canDeriv n` belong to `rulesST`; `natBarrierST_iff_used`: equivalence with the statement
`NatBarrierSTUsed` written with the used rules).

## `NatValueCore` (a proposed form of the value-level hypothesis; proved later)

It corresponds to the arctic `ValueCore`. There are two differences: (i) the class of interpretations is that of monotone natural-number matrix interpretations; (ii) the premise is not only value-level monotonicity
(`Φ(can (T n)) ≤ Φ(can n)`) but **the weak orientation of the 11 rules itself**. The earlier written chain (an earlier, longer argument; for instance, the matrix inequality `A^k S ≥ S A^k` from the weak
orientation of the rules `A`) uses weak orientation at the level of matrices, so
a form assuming only value-level monotonicity is stronger than what the chain shows, and whether it holds was not checked (this note predates the proof: those steps are not used, and the form of Theorem 10.11 for value automata, `AutoValueCoreNoG2` of `AutoCore.lean`, whose premise is value-level monotonicity, is proved without hypotheses). With the stronger premise (the weaker
claim) of this form, `NatBarrierST` still follows (`natBarrierST_of_core` of `Bridge.lean`). The conclusion has the same form as in the arctic case: for every rule
`ρ` and every `K` there is a segment `n → T^m n` of a `T`-orbit (all points of the segment at least 2) on which the number of uses of `ρ` exceeds `Φ(can n)`.
In the earlier written argument (not used here), `Φ(can x₀)` equals a constant at starting points of the point family of positive probability, and the numbers of uses of the used rules
tend to infinity with the size of the family.

## `NatValueCore'` and `NatBarrierSTB` (§4, added after the internal review)

`NatValueCore'` is `NatValueCore` without the monotonicity premise (the premise is only the weak orientation of the 11 rules; the conclusion is the same; this note predates Lemma 10.5 of the paper, by which the two are equivalent: `natValueCore_iff_natValueCore'` of `Embed.lean`). The written chain
uses monotonicity only at the step where strict orientation decreases `Φ` by at least 1 (Lemma 10.2 of the paper).
In the Lean bridge (`Bridge.lean`) monotonicity is also used only at that step (`evN_M00_pos`, `stepTerm_ge_one`,
`phiN_step_strict`, `phiN_chain_count`, `orbit_bound_nat`), and `Φ(can (T n)) ≤ Φ(can n)` (`phiN_can_T_le`) does
not use monotonicity. So the value-level core can be stated without monotonicity (the form that is proved later). From it,
(i) for monotone interpretations, `NatBarrierST` (`natBarrierST_of_core'` of `BridgeTop.lean`); (ii) without monotonicity, no left-end rule `B` is strictly
oriented, `NatBarrierSTB` (`natBarrierSTB_of_core'`). The reason for (ii): in the canonical derivation the rules of `B` are used only at positions with empty left context
(the top; `/` occurs only at the left end of the string), and in the case `p = []` of the one-step identity (Lemma 10.2 of the paper) the decrease is at least
`(M_[])₀₀ = (identity matrix)₀₀ = 1`, so without monotonicity `Φ` decreases by at least 1 at each use.
-/
import CollatzProof.Arctic.Statement

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix

/-! ## §1 Natural-number matrix interpretations (a copy of §1 of `NatExample.lean`) -/

/-- The affine map `y ↦ M y + v` of dimension `d` with natural-number entries. -/
structure NAff (d : ℕ) where
  M : Matrix (Fin d) (Fin d) ℕ
  v : Fin d → ℕ

/-- Application as a map: `F(y) = M y + v`. -/
def NAff.app {d : ℕ} (F : NAff d) (y : Fin d → ℕ) : Fin d → ℕ := F.M *ᵥ y + F.v

/-- The composition `F ∘ G`. -/
def NAff.comp {d : ℕ} (F G : NAff d) : NAff d := ⟨F.M * G.M, F.M *ᵥ G.v + F.v⟩

/-- The identity map. -/
def NAff.id (d : ℕ) : NAff d := ⟨1, 0⟩

/-- The interpretation of a string (`[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]`; the empty string is the identity). -/
def evN {d : ℕ} (I : Letter → NAff d) : Word → NAff d
  | [] => NAff.id d
  | s :: w => (I s).comp (evN I w)

/-- Weak orientation: `M_ℓ ≥ M_r` and `v_ℓ ≥ v_r`, entrywise. -/
def NWeak {d : ℕ} (I : Letter → NAff d) (ρ : Rule) : Prop :=
  (∀ i j, (evN I ρ.rhs).M i j ≤ (evN I ρ.lhs).M i j) ∧ ∀ i, (evN I ρ.rhs).v i ≤ (evN I ρ.lhs).v i

/-- Strict orientation (YAH, equation (2)): weak orientation, and the first component of `v` (index 0) is strictly larger. -/
def NStrict {d : ℕ} [NeZero d] (I : Letter → NAff d) (ρ : Rule) : Prop :=
  NWeak I ρ ∧ (evN I ρ.rhs).v 0 < (evN I ρ.lhs).v 0

/-- `Φ(w) = ([w](0))₁` (index 0). -/
def PhiN {d : ℕ} [NeZero d] (I : Letter → NAff d) (w : Word) : ℕ := (evN I w).app 0 0

/-- Monotonicity: `(M_s)₀₀ ≥ 1` for every letter (this includes the sufficient condition `(M_σ)_{1,1} = 1` of YAH §2.3.1; equivalent to extended monotonicity in this class:
`nmono_iff_extMono` of `NonVacuity.lean`). -/
def NMono {d : ℕ} [NeZero d] (I : Letter → NAff d) : Prop := ∀ s, 1 ≤ (I s).M 0 0

instance {d : ℕ} (I : Letter → NAff d) (ρ : Rule) : Decidable (NWeak I ρ) :=
  @instDecidableAnd _ _
    (@Fintype.decidableForallFintype _ _
      (fun i => (inferInstance : Decidable (∀ j, (evN I ρ.rhs).M i j ≤ (evN I ρ.lhs).M i j))) _)
    inferInstance

instance {d : ℕ} [NeZero d] (I : Letter → NAff d) (ρ : Rule) : Decidable (NStrict I ρ) :=
  instDecidableAnd

/-! ## §2 The statement of the main theorem -/

/-- **The statement of the main theorem** (Theorem 9.2 (i) of the paper, 𝒯): a natural-number matrix interpretation of any dimension `d ≥ 1` that is monotone (`(M_s)₀₀ ≥ 1` for
every letter) and weakly orients all 11 rules of 𝒯 (each of them is used by the canonical derivations) strictly orients
none of the rules. -/
def NatBarrierST : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), NMono I → (∀ ρ ∈ rulesST, NWeak I ρ) →
    ∀ ρ ∈ rulesST, ¬ NStrict I ρ

/-- The rules used by the canonical derivation `can n →* can (T n)` (`n ≥ 2`). -/
def UsedST (ρ : Rule) : Prop := ∃ n, 2 ≤ n ∧ ρ ∈ canDeriv n

/-- The statement written with the used rules (equivalent to `NatBarrierST` by `natBarrierST_iff_used` of `NonVacuity.lean`). -/
def NatBarrierSTUsed : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), NMono I → (∀ ρ, UsedST ρ → NWeak I ρ) →
    ∀ ρ, UsedST ρ → ¬ NStrict I ρ

/-! ## §3 The form of the value-level hypothesis (a proposal; proved later) -/

/-- **The value-level hypothesis** (a proposal): for a monotone natural-number matrix interpretation that weakly orients all 11 rules, for every rule `ρ` and every `K`
there is a segment `n → T^m n` of a `T`-orbit (all points of the segment at least 2) on which the number of uses of `ρ` exceeds `Φ(can n)`.
`natBarrierST_of_core : NatValueCore → NatBarrierST` of `Bridge.lean`. -/
def NatValueCore : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), NMono I → (∀ ρ ∈ rulesST, NWeak I ρ) →
    ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ PhiN I (can n) < usesOrbit ρ n m

/-! ## §4 The left-end rules `B` and the value-level core without monotonicity (added after the internal review; the existing definitions are unchanged) -/

open Letter in
/-- The left-end rules `B` (the division of YAH §3.2): `/0 → /t`, `/1 → /ff`, `/2 → /ft` (entries 8 to 10 of `rulesST`; the same as the arctic
`leftRule 0`, `leftRule 1`, `leftRule 2`). -/
def rulesSTB : List Rule :=
  [⟨[lft, d0], [lft, t]⟩, ⟨[lft, d1], [lft, f, f]⟩, ⟨[lft, d2], [lft, f, t]⟩]

/-- **The statement for the left-end rules** (no monotonicity premise): a natural-number matrix interpretation of any dimension `d ≥ 1` (not necessarily monotone)
that weakly orients all 11 rules of 𝒯 strictly orients none of the left-end rules `B`.

It covers the natural-number form of Lemma 3.18 (1) of YAH (the route that removes `B` in the top form `SN(R_top/𝒯)`, `R ⊆ B`, by a weakly monotone algebra).
**Weakly monotone algebras and the top form**: in one step in the top form, the rules of `R` apply only at positions with empty left context (the root of the term), so
monotonicity with respect to `>` is not needed, and an algebra monotone with respect to `≳` (a weakly monotone algebra) suffices. Every natural-number matrix interpretation is monotone
with respect to `≳` (`app_mono_ge` of `NonVacuity.lean`), so the weakly monotone algebras of this class are all of `NAff`, and the statement has no monotonicity
premise. A word is interpreted by the composition `[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]`, so the left end of a string is the root (top) of the unary term. Strict orientation is
`NStrict` (`[ℓ](y) > [r](y)` for all `y`, `nstrict_iff_forall`), exactly the form used at the top without a context (restricting `>` to
"strict in the first component" gives the same condition together with the weak orientation of the rule itself). The weak orientation of the 11 rules corresponds to
the requirement that one step `SN(R_top/𝒯)` weakly orients the rules of 𝒯 (at any position). For the rules other than `B`
the statement is false without monotonicity (`not_barrier_noMono` of `NonVacuity2.lean`, `noMono_strict_nonB` of `NonVacuity3.lean`). -/
def NatBarrierSTB : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), (∀ ρ ∈ rulesST, NWeak I ρ) →
    ∀ ρ ∈ rulesSTB, ¬ NStrict I ρ

/-- **The value-level core (without monotonicity)**: `NatValueCore` without the premise `NMono I` (the conclusion is the same). For a natural-number matrix interpretation
(not necessarily monotone) that weakly orients all 11 rules, for every rule `ρ` and every `K` there is a segment `n → T^m n` of a `T`-orbit
(all points of the segment at least 2) on which the number of uses of `ρ` exceeds `Φ(can n)`. Proved later (Theorem 10.11 of the paper).
`BridgeTop.lean`: `natValueCore_of_core'`, `natBarrierST_of_core'`, `natBarrierSTB_of_core'`. -/
def NatValueCore' : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), (∀ ρ ∈ rulesST, NWeak I ρ) →
    ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ PhiN I (can n) < usesOrbit ρ n m

end Collatz.Arctic.NatQ5
