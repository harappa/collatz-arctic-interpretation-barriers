/-
# The barrier for natural-number matrix interpretations of the reversed system 𝒯^rev: the statement of the main theorem

Theorem 9.2 (i) and (ii) of the paper (the parts for 𝒯^rev): a natural-number matrix interpretation of any finite dimension
that weakly orients all 11 rules of the reversed system 𝒯^rev of 𝒯 (the system obtained by reversing both sides of the 11 rules)
(i) strictly orients none of the rules if it is monotone (`(M_s)₀₀ ≥ 1`) (`NatBarrierSTrev`);
(ii) strictly orients neither of the two reversed top rules `.f → .`, `.t → .2`, even if it is not monotone (`NatBarrierSTrevTop`).
**An internal independent review of the statement** (no serious finding) judged that "the definitions can be frozen". The comments and the notes on scope were revised to take in
its remarks (the definitions were not changed). The frozen forward statement
`Statement.lean` is not changed.

## Sources of the definitions

The class of interpretations and the comparisons (`NAff`, `evN`, `NWeak`, `NStrict`, `NMono`, `PhiN`) are those of the frozen forward statement `Nat/Statement.lean`,
used **as they are** (the definitions are not changed; the reversed system is just treated as another rewriting system). The letters `Letter`, the rules `Rule`, the 11 rules
`rulesST`, `can` and `T` are those of `Defs.lean`, and the canonical derivation `canDeriv` is that of the frozen arctic `Statement.lean`. To keep the closure of the statement small,
the only import is `Nat/Statement.lean` (the reversal is written without giving it a name). That it agrees with three existing definitions of the same reversal
is checked by `rfl`: `Collatz.Arctic.NatQ5.ruleRev` of `Nat/Embed.lean` (`rulesSTrev_eq_map` of `BridgeRev.lean`),
the arctic `Collatz.Arctic.NonVacuity.revRule` and `Collatz.Arctic.NonVacuity.rulesSTrev` (`Arctic/NonVacuity4.lean`), and
`Collatz.Arctic.Rule.rev` (`Arctic/DPBridge.lean`) (§1 of `NonVacuityRev.lean`). **A note on names**: the name
`Collatz.Arctic.NatQ5.rulesSTrev` of this statement has the same short name as the arctic `Collatz.Arctic.NonVacuity.rulesSTrev`, and the same value.
Files that `open` both namespaces need to qualify it.

## Conventions (checked against the primary sources)

YAH = Yolcu–Aaronson–Heule, arXiv:2105.14697v3 (J. Autom. Reasoning 2023). Conventions 1 to 7 of `Nat/Statement.lean` are taken over
as they are (dimension `d ≥ 1`, interpretation of a letter `[s](y) = M_s y + v_s`, interpretation of a word by the composition `[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]`, monotonicity
`(M_s)₀₀ ≥ 1` (equivalent to extended monotonicity in this class, `nmono_iff_extMono` of `NonVacuity.lean`), weak and strict orientation as in
equation (2) of YAH). **Correspondence of letters**: `◁` = `/` = `lft` and `▷` = `.` = `rgt` of YAH; `f`, `t` are the binary digits; `0`, `1`, `2` = `d0`, `d1`, `d2`.
For the reversed system only the following are added.

1. **The reversed system** (Def 2.7 of YAH): `R^rev := {rev(ℓ) → rev(r) | ℓ → r ∈ R}` (`rev` is the reversal of strings).
   `rulesSTrev := rulesST.map (ℓ → r ↦ rev ℓ → rev r)`, in the order of `rulesST` (numbered 0 to 10).
   It has no rule in common with 𝒯. The 9 rules of `X^rev` written by YAH on p.24 agree with `rulesSTrev.drop 2` (checked in the internal review).
2. **Words are interpreted in the same direction as in the forward case**: a string `s₁ ⋯ sₙ` of 𝒯^rev is also read as the unary term `s₁(s₂(⋯ sₙ(x)))`, and
   `[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]` (`evN`). 𝒯^rev is another string rewriting system over the same letters as 𝒯, and
   Thm 2.6 (rule removal) and Thm 2.15 of YAH apply to it as they are. Example: the left-hand side of `.t → .2` is interpreted by `[.] ∘ [t]` (`evN I [rgt, t]`).
   **Checked directly against YAH's own interpretation of a reversed system**: the 20 printed composed values of the 2-dimensional interpretation of `W'^rev` in Thm 4.1 (pp.23–24) are
   reproduced by `evN`, and not reproduced with the opposite direction of composition (`I41_printed`, `I41_other_order_fails` of `NonVacuityRev.lean`; the counterpart of the forward
   `yah_ex43_values`). The two interpretations of Lemma 3.15 (p.20) (with the printed values, including `[▷] = x`) also work only in this direction
   (`IL315`, `IL315b`).
3. **Reversal and rule removal** (Lemma 2.8 of YAH, Lemma 2 of [Zan05]): `SN(R/S) ⟺ SN(R^rev/S^rev)`. So a proof of termination of 𝒯
   may remove rules by interpretations of 𝒯^rev. The conclusion of `NatBarrierSTrev` is that in the first step for 𝒯^rev (the step that weakly orients all 11 rules
   and strictly orients a nonempty part, Thm 2.6 and Thm 2.15 of YAH) no rule can be removed by a monotone natural-number matrix interpretation.
   Together with the forward `NatBarrierST` (frozen): whichever direction is taken, and even if the direction is changed at each step, there is no first step.
4. **The top form** (Lemma 3.18 (2) of YAH): the route that removes the dynamic rules `D_T^rev = {.f → ., .t → .2}` of the reversed system by a weakly monotone algebra (no monotonicity
   condition) in the top form `SN(Q^rev_top / 𝒯^rev)` (`Q ⊆ D_T`). In one step in the top form the rules of `Q^rev` apply only at the root of the term
   (the left end of the string, Def 2.9 of YAH), so monotonicity with respect to `>` is not needed (for the same reason as in the comment on `NatBarrierSTB`
   in `Nat/Statement.lean`). Every natural-number matrix interpretation is monotone with respect to `≳` (`app_mono_ge` of `NonVacuity.lean`), so the
   weakly monotone algebras of this class are all of `NAff`, and `NatBarrierSTrevTop` has no monotonicity premise. Strict orientation is `NStrict` (`[ℓ](y) > [r](y)`
   for all `y`, `nstrict_iff_forall`), exactly the form used at the top. In the top form `>` may be taken to be the order "strict in the first component" only,
   but **since the base system is 𝒯^rev (which contains `Q^rev`)**, together with the entrywise weak orientation of the rules of `Q^rev` themselves this gives
   the same condition `NStrict`. The variant with base system `X^rev = A^rev ∪ B^rev`, which compares the top rules in the first component only, reduces to `NatBarrierSTrevTop`
   by truncating `[.]` to row 0 (`top_variant_rev` of `BridgeDP.lean`, after `top_variant` of the internal review; Lemma 13.2 of the paper).
   The weak orientation of the 11 rules corresponds to the requirement that one step `SN(Q^rev_top / 𝒯^rev)` weakly orients the rules of 𝒯^rev (at any position).
   In the strings of 𝒯^rev that occur in the mirror images of the canonical derivations (`rev (can n) = . bin'(n)^rev /`), `.` occurs only at the left end, and
   `.f → .` and `.t → .2` are used only at the left end.
5. **Lemma 3.15 of YAH** shows termination of `𝒯 \ B` and `𝒯 \ D_T` by interpretations of the reversed systems `(𝒯 \ B)^rev`, `(𝒯 \ D_T)^rev`.
   These are proofs of termination of subsystems and do not include the weak orientation of the 11 rules of 𝒯^rev, so they are not the subject of this statement (such
   interpretations do exist: `IL315`, `IL315b` of `NonVacuityRev.lean`).

## Scope

`NatBarrierSTrev` covers only rule removal on 𝒯^rev in its direction (one step by a monotone natural-number matrix interpretation, item 3 above), and
`NatBarrierSTrevTop` covers only the natural-number form of item 4 above.

**All readings**: the four readings of the two systems 𝒯, 𝒯^rev, each with the two directions of composition (`[s₁] ∘ ⋯ ∘ [sₙ]` and `[sₙ] ∘ ⋯ ∘ [s₁]`),
are covered by the two pairs of statements. Reading 𝒯^rev in the opposite direction is the same as reading 𝒯 by `evN` (reading `rev ℓ` in the opposite direction
gives the same value as reading `ℓ` by `evN`), which is covered by the frozen `NatBarrierST`, `NatBarrierSTB`. Reading 𝒯 in the opposite direction is
the same as reading 𝒯^rev by `evN`, which is covered by the statements `NatBarrierSTrev`, `NatBarrierSTrevTop` of this file. The co-affine form obtained by transposing the homogeneous
matrices (Lemma 10.4 of the paper) is also covered by `NatBarrierSTrev` (transposition is the correspondence between interpretations of 𝒯^rev and co-affine families for 𝒯,
`nweak_rev_iff_transpose`, `nstrict_rev_iff_transpose` of `BridgeRev.lean`).

The following are outside this statement:

* Strictly orienting rules other than `.f → .`, `.t → .2` without monotonicity (false: in §5 of `NonVacuityRev.lean` a non-monotone interpretation of dimension 1
  weakly orients the 11 rules and strictly orients the rules that are not top rules).
* **The dependency pair framework**: in §6, YAH also counts Thm 3.10 on Zantema's system 𝒵 (a dependency pair form with marked symbols, weakly monotone) and footnote 8
  (its version for 𝒵^rev) among the results "there is no matrix interpretation". Reduction pairs of natural-number matrix interpretations for the essential SCCs `(P_B, U)` and
  `(P_D^rev, A^rev ∪ B^rev)` of 𝒯 and 𝒯^rev are covered by the separate statements `NatBarrierDP` and
  `NatBarrierDPrev` of `StatementDP.lean`. Truncating `[/#]` and `[.#]` to row 0, they are equivalent to `NatBarrierSTB` and `NatBarrierSTrevTop`, respectively
  (`natBarrierDP_iff_STB`, `natBarrierDPrev_iff_top` of `BridgeDP.lean`). Transferring Thm 3.10 of YAH with the strength of its printed form (which does not assume the weak orientation of the other
  dependency pairs) gives a false statement (`not_literalRev`, `not_literal` of `NonVacuityDP.lean`).
* The form of Hofbauer–Waldmann (HW06) comparing corner entries of linear interpretations that are monotone on both sides (now covered by Corollary 10.12 (`Nat/HWCorner.lean`); outside
  the statements of this file), and the core form of Hofbauer–Waldmann (Property 1 of their FSCD 2026 paper).
* Interpretations after preprocessing (root labelling, tiling, innermost, narrowing), other semirings (rationals, reals) and polynomial interpretations, and the reversal
  of the system for `H`.
* The statements are derived as corollaries of the value-level core (`NatValueCore`, `NatValueCore'` of `Statement.lean`) (`BridgeRev.lean`). They do not follow from the frozen forward
  statement `NatBarrierST` (the value embedding does not preserve strict orientation: Lemma 10.5 of the paper, `embInterp_not_strict` of `Embed.lean`).
  An exception is a subclass with condition (U) (not used in the paper; `natBarrierSTrevU_of_natBarrierST` of `NonVacuityRev.lean`).

**Cross-reference to the frozen `Statement.lean`**: the note in its scope that "(2) (Lemma 3.18 (2) of YAH) is not covered" is still correct for the statements of that file
(`NatBarrierST`, `NatBarrierSTB`). The natural-number form of (2) is covered by `NatBarrierSTrevTop` of this file.
"Removal by interpretations of the reversed system 𝒯^rev" in the same note is covered by `NatBarrierSTrev` of this file.

## The used rules

The canonical derivation of 𝒯^rev is the mirror image of the canonical derivation `can n →* can (T n)` of 𝒯 (`canDeriv n`, `n ≥ 2`),
`rev (can n) →* rev (can (T n))`; its `j`-th step applies the reversal of the `j`-th rule of `canDeriv n` at the mirrored position
(Lemma 13.1 of the paper; proved correct by `canDerivRev_chain` of `BridgeRev.lean`). That list of rules is `canDerivRev n`.
As for 𝒯, all 11 rules are used. The statement is written with all 11 rules `rulesSTrev`, and its equivalence with the form
`NatBarrierSTrevUsed` written with the used rules is proved in §2 of `NonVacuityRev.lean`.
-/
import CollatzProof.Arctic.Nat.Statement

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Letter

/-! ## §1 The reversed system -/

/-- **The 11 rules of 𝒯^rev** (Def 2.7 of YAH): the rules of `rulesST` with both sides reversed (in the order of `rulesST`).
`.f → .`, `.t → .2`, `0f → f0`, `1f → t0`, `2f → f1`, `0t → t1`, `1t → f2`, `2t → t2`, `0/ → t/`, `1/ → ff/`,
`2/ → tf/` (`rulesSTrev_eq_table` of `NonVacuityRev.lean`). -/
def rulesSTrev : List Rule := rulesST.map fun ρ => ⟨ρ.lhs.reverse, ρ.rhs.reverse⟩

/-- **The reversed top rules** `D_T^rev`: `.f → .`, `.t → .2` (entries 0 and 1 of `rulesSTrev`; the reversals of the dynamic rules of 𝒯). -/
def rulesSTrevTop : List Rule := [⟨[rgt, f], [rgt]⟩, ⟨[rgt, t], [rgt, d2]⟩]

/-! ## §2 The statement of the main theorem -/

/-- **The statement of the main theorem** (Theorem 9.2 (i) of the paper, 𝒯^rev): a natural-number matrix interpretation of any dimension `d ≥ 1` that is monotone (`(M_s)₀₀ ≥ 1` for
every letter) and weakly orients all 11 rules of 𝒯^rev (each of them is used by the mirrored canonical derivations) strictly orients
none of the rules. -/
def NatBarrierSTrev : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), NMono I → (∀ ρ ∈ rulesSTrev, NWeak I ρ) →
    ∀ ρ ∈ rulesSTrev, ¬ NStrict I ρ

/-- **The statement for the reversed top rules** (Theorem 9.2 (ii) of the paper, 𝒯^rev; no monotonicity premise): a natural-number matrix interpretation of any dimension `d ≥ 1`
(not necessarily monotone) that weakly orients all 11 rules of 𝒯^rev strictly orients neither `.f → .` nor `.t → .2`.
It covers the natural-number form of Lemma 3.18 (2) of YAH (the route that removes `D_T^rev` by a weakly monotone algebra in the top form
`SN(Q^rev_top / 𝒯^rev)`). -/
def NatBarrierSTrevTop : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), (∀ ρ ∈ rulesSTrev, NWeak I ρ) →
    ∀ ρ ∈ rulesSTrevTop, ¬ NStrict I ρ

/-! ## §3 The form written with the used rules -/

/-- The list of rules of the mirrored canonical derivation `rev (can n) →* rev (can (T n))` (`n ≥ 2`): the rules of `canDeriv n` with both sides reversed
(`canDerivRev_chain` of `BridgeRev.lean`). -/
def canDerivRev (n : ℕ) : List Rule := (canDeriv n).map fun ρ => ⟨ρ.lhs.reverse, ρ.rhs.reverse⟩

/-- The rules used by the mirrored canonical derivations. -/
def UsedSTrev (ρ : Rule) : Prop := ∃ n, 2 ≤ n ∧ ρ ∈ canDerivRev n

/-- The statement written with the used rules (equivalent to `NatBarrierSTrev` by `natBarrierSTrev_iff_used` of `NonVacuityRev.lean`). -/
def NatBarrierSTrevUsed : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), NMono I → (∀ ρ, UsedSTrev ρ → NWeak I ρ) →
    ∀ ρ, UsedSTrev ρ → ¬ NStrict I ρ

end Collatz.Arctic.NatQ5
