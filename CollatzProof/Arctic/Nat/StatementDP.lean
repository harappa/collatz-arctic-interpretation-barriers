/-
# The dependency pair forms (of the type of Thm 3.10 and footnote 8 of YAH): the statements for reduction pairs of natural-number matrix interpretations

For the essential strongly connected components (SCCs) of the dependency pairs of 𝒯 and of its reversed system 𝒯^rev, a reduction pair of natural-number matrix interpretations
(any dimension, no monotonicity condition) that weakly orients the usable rules entrywise and all dependency pairs of the SCC in the first component
strictly orients no dependency pair of the SCC in the first component (`NatBarrierDP`, `NatBarrierDPrev`). This is the natural-number version of the arctic version (Theorem 3.3 of the paper,
`ArcticBarrierDP`, `ArcticBarrierDPrev` of `DPStatement.lean`); the dependency pair problems, the usable rules and the letters are those of
the frozen arctic statements, used as they are. **An internal independent review of the statement** (no serious finding) judged that "the definitions can be frozen".
The comments were revised to take in its remarks (the definitions were not changed).

## Sources of the definitions

* The marked letters `DLetter` (`mark s`, `plain s`), the dependency pairs and rules `DRule`, `Rule.plain`, and the dependency pair problems `pairsPB`
  (`/#0 → /#t`, `/#1 → /#ff`, `/#2 → /#ft`) with `usableST` (`U = D_T ∪ A`, the first 8 rules of `rulesST`) and `pairsPDrev`
  (`.#f → .#`, `.#t → .#2`) with `usableSTrev` (`A^rev ∪ B^rev`) are those of the frozen arctic `DPStatement.lean` (Theorem 3.3 of the paper). That these are
  the essential SCCs of the dependency pairs of 𝒯 and 𝒯^rev (Arts–Giesl; for SRSs in the form of Zantema's TORPA, the same as Def 2 of GTSF06 and EWZ08 §5) and
  the usable rules of GTSF06 (Def 10) was computed in the arctic `NonVacuity4.lean` (`dps_ST_PB`, `dps_STrev_PD`, `usable_ST`,
  `usable_STrev`; the SCC that carries the carries has no usable rules and is removed by the subterm criterion).
* **The SCCs do not split**: `P_B` has the cycle `/#0 → /#2 → /#1 → /#0` through all three dependency pairs (edges 0 → 2, 2 → 1, 1 → 0; also 0 → 1 and
  2 → 0), and `P_D^rev` has all four edges (`pB_cycle`, `pDrev_edges` of `NonVacuityDP.lean` give the derivations that create the edges; the absence of edges
  is not in Lean). So however the dependency graph is approximated, `P_B` and `P_D^rev` do not split, and methods that treat cycles one by one also require, for this cycle,
  the weak orientation of all dependency pairs.
* The class of interpretations and the comparisons are those of `NAff` (`[s](y) = M_s y + v_s`) of the frozen `Nat/Statement.lean`. The interpretation `evND` of strings
  of marked letters is the composition `[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]` in the same direction as `evN` (YAH §2.2, the same as the arctic `evA`). The correspondence of letters is
  `◁` = `/` = `lft` and `▷` = `.` = `rgt` of YAH.

## Correspondence with Thm 3.10 of YAH

YAH = Yolcu–Aaronson–Heule, arXiv:2105.14697v3. Thm 3.10 in §3.1 (the dependency pair form for Zantema's system 𝒵, p.16) is printed as saying that there is no weakly monotone algebra over the letters with a marked
blank `◇#` added (a natural-number matrix interpretation, with the order of §2.3.1) that orients (i) at least one of the rules of `I = {◇#s → ◇#h, ◇#t → ◇#h} ⊆ DP(𝒵)`
as `[ℓ](x) > [r](x)` (for all `x`) and (ii) all rules of 𝒵 as `[ℓ'](x) ≳ [r'](x)`
(Lemma 3.9: `SN(DP(𝒵)_top / 𝒵) ⟺ SN(I_top / 𝒵)`). There is no condition on the other rule of `I`. Footnote 8 is its version for 𝒵^rev.
§6 counts these among the results "there is no matrix interpretation".

**The printed statement holds neither for 𝒵 nor for 𝒵^rev**: there is a natural-number matrix interpretation of dimension 2 that weakly orients all 7 rules of 𝒵 entrywise,
strictly orients `◇#s → ◇#h` in the order of YAH, and does not even weakly orient `◇#t → ◇#h`. The same holds for the version for 𝒵^rev of footnote 8
(`ZYah.Z_literal_false`, `ZYah.Zrev_literal_false` of `NonVacuityDP.lean`; examples from the internal independent review of the dependency pair statements). The proof of YAH
uses the derivation `◇#h1^{8n+1}◇ →* ◇#h1^{9n+2}◇`, which uses both rules of `I`, and what the proof shows is the form with the additional premise "the other rule of `I` is also `≳`".
This is the same form as required by one step of removal (Thm 3 (2) of EWZ08, p.199: `R ∪ S` weakly, a part of `R` strictly) and by the reduction pair
processor for dependency pairs (EWZ08 §5, Thm 17 (a) of GTSF06: `P_≻ ∪ P_≿ = P`). Thm 2.15 of YAH (= Thm 2 of EWZ08) is
the equivalent form in which all of `R` is strictly oriented. This statement follows this form and transfers it to 𝒯 and 𝒯^rev. Compared with the form shown by the proof:

| Thm 3.10 of YAH (the form shown by the proof) | this statement | strength |
|---|---|---|
| letters with a marked blank `◇#` added | `DLetter` (only `/#` is used in the forward case and `.#` in the reversed case) | same |
| weakly monotone algebra, natural-number matrix interpretation | `NAff`, no monotonicity premise (every natural-number matrix interpretation is monotone with respect to `≳`) | same |
| `I` (the pairs that remain from `DP(𝒵)` after rule removal) | the essential SCCs `P_B`, `P_D^rev` (the pairs that remain from `DP(𝒯)`, `DP(𝒯^rev)` after the SCC decomposition) | corresponding |
| all rules of 𝒵 `≳` | the usable rules `U`, `A^rev ∪ B^rev` `≳` entrywise (`NWeakD`) | fewer premises |
| the other rule of `I` `≳` | all dependency pairs of the SCC `≥` in the first component (`NWeakTopD`; follows from `≳`) | fewer premises |
| one of `I` with the `>` of YAH (strict in the first component, `≥` in the others) | one of the SCC strict in the first component (`NStrictTopD`; follows from the `>` of YAH) | stronger conclusion |

The forms transferred to 𝒯 and 𝒯^rev with the strength of the printed form (no condition on the other dependency pairs) do not hold either (`not_literalRev`, `not_literal` of
`NonVacuityDP.lean`: a non-monotone interpretation of dimension 1).

## The choice of comparisons

* The usable rules are compared weakly, entrywise (`≳` of YAH, the arctic `WeakA`). The dependency pairs are compared in the first component (index 0) only (the same as the arctic
  `WeakTop`, `StrictTop`). In terms of values: `([ℓ](y))₀ ≥ ([r](y))₀` and `>` for all `y` (`nweakTopD_iff_forall`,
  `nstrictTopD_iff_forall` of `BridgeDPForms.lean`). Forms that follow from this statement (shown in Lean; Proposition 13.3 of the paper):
  - (a) comparison in the order of YAH (`≳` entrywise; `>` strict in the first component and `≥` in the others) (`natBarrierDPrev_full`,
    `natBarrierDP_full` of `BridgeDP.lean`).
  - (b) the form that interprets the marked letters by scalar values (a row vector `u` and a constant `c`, `[h#](x) = u ⬝ x + c`) and compares the dependency pairs by `≥` in the coefficients and
    by `>` in the constant (the two-sorted form of EWZ08 §5, p.205; `natBarrierDPrev_scalar`, `natBarrierDP_scalar` of `BridgeDPForms.lean`).
  - (c) the form that compares the dependency pairs in some component `k` (the one-sorted form of EWZ08 p.206, a proper part of `≥`; the same holds for the top form with `>` taken to be the order
    of the `k`-th component only; `natBarrierDPrev_row`, `natBarrierDP_row` of `BridgeDPForms.lean`).
* The form that weakly orients only the usable rules requires, by Thm 17 (b) of GTSF06 (p.15), that the reduction pair be `C_ε`-compatible (Def 13, p.11).
  Natural-number matrix interpretations satisfy this with `[c](x, y) = x + y` (the note on polynomials on p.12 of GTSF06; for matrices, `I x + I y` in the matrix interpretations of terms of EWZ08).
  Since the premises are fewer than all rules, the statement applies to both forms.

## Scope

Covered: the reduction pair processor with natural-number matrix interpretations (monotone or not) for the essential SCCs of the dependency pairs of 𝒯 and 𝒯^rev.
By `BridgeDP.lean`, they are equivalent to the top statements `NatBarrierSTB` and `NatBarrierSTrevTop`, respectively (in one direction truncating `[h#]` to row 0, in the other
putting it back at the position of `h`). So they follow from the value-level core.

**Argument filters** (Def 20, Def 21 and Thm 26 of GTSF06; for natural-number matrix interpretations, dropping an argument means `M_s = 0`):
* Forward: for every filter the usable rules `U(P_B, π)` remain the 8 rules of `U` (`usableFilt_fwd` of `BridgeDPFilter.lean`; directly below `/#` are
  `f`, `t`, and the rules of `f`, `t` are all of `U`). So `NatBarrierDP` also covers the forms with filters (`natBarrierDPFilt_of_DP`).
* Reversed: dropping `f` shrinks the usable rules to 3 rules (`2f → f1`, `2t → t2`, `2/ → tf/`), dropping only `t` to 6 rules (the rules of `1`, `2`)
  (`usableFilt_rev`), which is outside the premises of `NatBarrierDPrev`. The conclusion still holds (Lean theorems that do not use the value-level core):
  for `f`, the weak orientation of `.#f → .#` in the first component makes the first row of `[.#]` zero (`dpRev_filt_f`); for `t`, `[t]` is a constant, so the values of odd numbers are
  constant, which contradicts the mirrored canonical derivation `13 → 20 → 10 → 5` (`dpRev_filt_t`). Together: `natBarrierDPrevFilt_of_DPrev`.
* Dropping the argument of `/#` or `.#` makes `[h#]` a constant; both sides of a dependency pair then have the same value, and strict orientation trivially does not occur (`markConst_not_strict`).

Not covered: other processors of the dependency pair framework, interpretations after preprocessing (root labelling, tiling, innermost, narrowing), the form of Hofbauer–Waldmann (HW06) comparing corners of linear
interpretations monotone on both sides and the core form, other semirings and polynomial interpretations, the systems for `H`.
-/
import CollatzProof.Arctic.Nat.Statement
import CollatzProof.Arctic.DPStatement

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Letter DLetter

/-! ## §1 The interpretation of strings of marked letters, and the comparisons -/

/-- The interpretation of strings that may contain marked letters: the composition `[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]` (the same direction as `evN`; the empty string is the identity). -/
def evND {d : ℕ} (J : DLetter → NAff d) : List DLetter → NAff d
  | [] => NAff.id d
  | s :: w => (J s).comp (evND J w)

/-- Entrywise weak comparison (for the usable rules; `≳` of YAH, the same form as `NWeak`). -/
def NWeakD {d : ℕ} (J : DLetter → NAff d) (π : DRule) : Prop :=
  (∀ i j, (evND J π.rhs).M i j ≤ (evND J π.lhs).M i j) ∧ ∀ i, (evND J π.rhs).v i ≤ (evND J π.lhs).v i

/-- Weak comparison in the first component (index 0) only (for the dependency pairs; equivalent to `([ℓ](y))₀ ≥ ([r](y))₀` for all `y`). -/
def NWeakTopD {d : ℕ} [NeZero d] (J : DLetter → NAff d) (π : DRule) : Prop :=
  (∀ j, (evND J π.rhs).M 0 j ≤ (evND J π.lhs).M 0 j) ∧ (evND J π.rhs).v 0 ≤ (evND J π.lhs).v 0

/-- Strict comparison in the first component only (for the dependency pairs; equivalent to `([ℓ](y))₀ > ([r](y))₀` for all `y`). -/
def NStrictTopD {d : ℕ} [NeZero d] (J : DLetter → NAff d) (π : DRule) : Prop :=
  (∀ j, (evND J π.rhs).M 0 j ≤ (evND J π.lhs).M 0 j) ∧ (evND J π.rhs).v 0 < (evND J π.lhs).v 0

instance {d : ℕ} (J : DLetter → NAff d) (π : DRule) : Decidable (NWeakD J π) :=
  @instDecidableAnd _ _
    (@Fintype.decidableForallFintype _ _
      (fun i => (inferInstance : Decidable (∀ j, (evND J π.rhs).M i j ≤ (evND J π.lhs).M i j))) _)
    inferInstance

instance {d : ℕ} [NeZero d] (J : DLetter → NAff d) (π : DRule) : Decidable (NWeakTopD J π) :=
  instDecidableAnd

instance {d : ℕ} [NeZero d] (J : DLetter → NAff d) (π : DRule) : Decidable (NStrictTopD J π) :=
  instDecidableAnd

/-! ## §2 The statements of the main theorem -/

/-- **The forward dependency pair form** (`(P_B, U)`): a natural-number matrix interpretation of any dimension `d ≥ 1` (including the marked letters, not necessarily monotone)
that weakly orients the usable rules `U = D_T ∪ A` entrywise and all dependency pairs of `P_B` in the first component strictly orients
no dependency pair of `P_B` in the first component. -/
def NatBarrierDP : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : DLetter → NAff d), (∀ ρ ∈ usableST, NWeakD J ρ.plain) →
    (∀ π ∈ pairsPB, NWeakTopD J π) → ∀ π ∈ pairsPB, ¬ NStrictTopD J π

/-- **The reversed dependency pair form** (`(P_D^rev, A^rev ∪ B^rev)`, of the type of footnote 8 of YAH): a natural-number matrix interpretation of any dimension `d ≥ 1`
(not necessarily monotone) that weakly orients the usable rules `A^rev ∪ B^rev` entrywise and all dependency pairs of `P_D^rev` in the first component
strictly orients neither `.#f → .#` nor `.#t → .#2` in the first component. -/
def NatBarrierDPrev : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : DLetter → NAff d), (∀ ρ ∈ usableSTrev, NWeakD J ρ.plain) →
    (∀ π ∈ pairsPDrev, NWeakTopD J π) → ∀ π ∈ pairsPDrev, ¬ NStrictTopD J π

end Collatz.Arctic.NatQ5
