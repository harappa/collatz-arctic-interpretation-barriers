/-
# Checks of the dependency pair forms `NatBarrierDP` and `NatBarrierDPrev` (Theorem 9.2 (iii) of the paper): non-vacuity, and the printed form does not hold

We look for errors on the side of `StatementDP.lean` (written while it was a draft; it is now frozen). Outside the closure of the main theorem. Existing files are not changed. No `sorry`, `axiom` declaration or `native_decide` is used (computations by `decide +kernel`).

* §1 Check of the dependency pair problems: `P_D^rev` and `A^rev ∪ B^rev` are the essential SCC of the dependency pairs of $\mathcal T^{\mathrm{rev}}$ (`rulesSTrev` of `StatementRev.lean`) and
  its usable rules (the computation of the arctic `NonVacuity4.lean`, carried over to `rulesSTrev`). Likewise for `P_B` and `U`. The dependency pairs are the top rules with their leftmost letter
  marked (`pairsPDrev_eq`, `pairsPB_eq` of `BridgeDP.lean`).
* §2 The premises are satisfiable: the identity interpretation, the extensions (`liftD`) of the monotone `IP3rev` and `IP3`, and those of the non-monotone `INoMonoRev` and `INoMono`. Consistent with the conclusion.
* §3 Each dependency pair alone can be strictly oriented in the first component (dimension 1).
* §4 **The printed form does not hold** (an example of an internal review of the reversed statement): Theorem 3.10 of Yolcu–Aaronson–Heule with its printed
  strength (all 11 rules of the base system weakly oriented entrywise, one dependency pair strictly oriented in the order of Yolcu–Aaronson–Heule, no condition on the other pairs), carried over to $\mathcal T^{\mathrm{rev}}$ and $\mathcal T$,
  fails for a non-monotone interpretation of dimension 1. In that interpretation another dependency pair is not weakly oriented even in the first component.
* §5 Dropping even one usable rule breaks the statement: `A^rev` alone (dropping `B^rev`), and `U` without `t. → 2.`.
* §6 Negative controls: `JLitRev` does not weakly orient the pairs of `P_D^rev` (`ctrl_JLitRev_not_pairsWeak`), `IL315` does not weakly orient the usable rules (`ctrl_IL315_not_usable`), and `IP3rev` strictly orients no pair (`ctrl_IP3rev_not_strict_pair`).
* §7 As printed, Theorem 3.10 of Yolcu–Aaronson–Heule does not hold for Zantema's system $\mathcal Z$, nor its version in footnote 8 for $\mathcal Z^{\mathrm{rev}}$ (examples of an internal independent review of the
  dependency pair statements). The proof establishes the form in which the other rule of `I` is also oriented by `≳`.
* §8 The SCCs do not split: `P_B` has the cycle 0 → 2 → 1 → 0 through all three dependency pairs, and `P_D^rev` has all four edges (the edges are built from derivations
  with the usable rules; internal review of the dependency pair statements).
* §9 Argument filters (internal review; `BridgeDPFilter.lean`): an interpretation with `[t]` constant that weakly orients the usable rules for the filter dropping the argument of `t` (6 rules) and the dependency pairs,
  and does not weakly orient the rules with leftmost letter `0` (outside the premises of `NatBarrierDPrev`; `dpRev_filt_t` applies). If `[t]` is not constant,
  weak orientation of the same 6 rules and of the dependency pairs allows a dependency pair to be strictly oriented (an example of dimension 2 from the review). Also an example for dropping the argument of `f`.
-/
import CollatzProof.Arctic.Nat.BridgeDPFilter
import CollatzProof.Arctic.Nat.BridgeDPForms
import CollatzProof.Arctic.Nat.NonVacuityRev

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter DLetter

namespace W5

/-! ## §1 Check of the dependency pair problems -/

/-- The dependency pairs of $\mathcal T^{\mathrm{rev}}$ whose right-hand side has the root `.#` are exactly `P_D^rev` (the arctic `dps_STrev_PD`, carried over to `rulesSTrev`). -/
theorem dps_rulesSTrev_PD :
    (NonVacuity.dpsOf rulesSTrev).filter (fun π => π.rhs.head? = some (mark rgt)) = pairsPDrev := by
  rw [rulesSTrev_eq_arctic]; exact NonVacuity.dps_STrev_PD

/-- The only dependency pairs that enter `.#` are those that leave `.#` (`P_D^rev` is an SCC). -/
theorem dps_rulesSTrev_into_PD : ∀ π ∈ NonVacuity.dpsOf rulesSTrev,
    π.rhs.head? = some (mark rgt) → π.lhs.head? = some (mark rgt) := by
  rw [rulesSTrev_eq_arctic]; exact NonVacuity.dps_STrev_into_PD

/-- The usable rules of `P_D^rev` are `A^rev ∪ B^rev`. -/
theorem usable_rulesSTrev : NonVacuity.usableOf rulesSTrev pairsPDrev = usableSTrev := by
  rw [rulesSTrev_eq_arctic]; exact NonVacuity.usable_STrev

/-- Forward direction: `P_B` and `U` (the arctic computation itself). -/
theorem dps_rulesST_PB_U :
    (NonVacuity.dpsOf rulesST).filter (fun π => π.rhs.head? = some (mark lft)) = pairsPB ∧
      NonVacuity.usableOf rulesST pairsPB = usableST :=
  ⟨NonVacuity.dps_ST_PB, NonVacuity.usable_ST⟩

/-! ## §2 The premises are satisfiable -/

variable {d : ℕ}

theorem evND_idJ (d : ℕ) : ∀ w : List DLetter, evND (fun _ => NAff.id d) w = NAff.id d
  | [] => rfl
  | s :: w => by
    show (NAff.id d).comp (evND (fun _ => NAff.id d) w) = NAff.id d
    rw [evND_idJ d w, NAff.id_comp]

/-- In every dimension the identity interpretation satisfies the premises of the two dependency pair problems. -/
theorem premisesDP_id (d : ℕ) [NeZero d] :
    (∀ ρ ∈ usableSTrev, NWeakD (fun _ => NAff.id d) ρ.plain) ∧ (∀ π ∈ pairsPDrev, NWeakTopD (fun _ => NAff.id d) π) ∧
    (∀ ρ ∈ usableST, NWeakD (fun _ => NAff.id d) ρ.plain) ∧ (∀ π ∈ pairsPB, NWeakTopD (fun _ => NAff.id d) π) := by
  refine ⟨fun ρ _ => ?_, fun π _ => ?_, fun ρ _ => ?_, fun π _ => ?_⟩
  · simp only [NWeakD, evND_idJ]; exact ⟨fun _ _ => le_rfl, fun _ => le_rfl⟩
  · simp only [NWeakTopD, evND_idJ]; exact ⟨fun _ => le_rfl, le_rfl⟩
  · simp only [NWeakD, evND_idJ]; exact ⟨fun _ _ => le_rfl, fun _ => le_rfl⟩
  · simp only [NWeakTopD, evND_idJ]; exact ⟨fun _ => le_rfl, le_rfl⟩

/-- The extension of the monotone `IP3rev` (`[.#] := [.]`): it satisfies the premises and strictly orients no dependency pair. -/
theorem IP3rev_DP : (∀ ρ ∈ usableSTrev, NWeakD (liftD IP3rev) ρ.plain) ∧
    (∀ π ∈ pairsPDrev, NWeakTopD (liftD IP3rev) π) ∧ ∀ π ∈ pairsPDrev, ¬ NStrictTopD (liftD IP3rev) π := by
  decide +kernel

/-- The extension of the monotone `IP3` (`[/#] := [/]`): it satisfies the premises of the forward direction and strictly orients no dependency pair. -/
theorem IP3_DP : (∀ ρ ∈ usableST, NWeakD (liftD IP3) ρ.plain) ∧
    (∀ π ∈ pairsPB, NWeakTopD (liftD IP3) π) ∧ ∀ π ∈ pairsPB, ¬ NStrictTopD (liftD IP3) π := by
  decide +kernel

/-- The extensions of the non-monotone `INoMonoRev` and `INoMono` also satisfy the premises (the statements have no monotonicity premise). Consistent with the conclusion. -/
theorem noMono_DP : (∀ ρ ∈ usableSTrev, NWeakD (liftD INoMonoRev) ρ.plain) ∧
    (∀ π ∈ pairsPDrev, NWeakTopD (liftD INoMonoRev) π) ∧ (∀ π ∈ pairsPDrev, ¬ NStrictTopD (liftD INoMonoRev) π) ∧
    (∀ ρ ∈ usableST, NWeakD (liftD INoMono) ρ.plain) ∧
    (∀ π ∈ pairsPB, NWeakTopD (liftD INoMono) π) ∧ ∀ π ∈ pairsPB, ¬ NStrictTopD (liftD INoMono) π := by
  decide +kernel

/-! ## §3 Each dependency pair alone can be strictly oriented -/

/-- For each dependency pair there is an interpretation of dimension 1 that strictly orients it in the first component (no other condition is required). -/
theorem strict_each_pair :
    (∀ π ∈ pairsPDrev, ∃ J : DLetter → NAff 1, NStrictTopD J π) ∧
      ∀ π ∈ pairsPB, ∃ J : DLetter → NAff 1, NStrictTopD J π := by
  refine ⟨fun π hπ => ?_, fun π hπ => ?_⟩
  · simp only [pairsPDrev, List.mem_cons, List.mem_nil_iff, or_false] at hπ
    rcases hπ with rfl | rfl
    · exact ⟨liftD (wI1 (fun _ => 1) (ind f)), by decide +kernel⟩
    · exact ⟨liftD (wI1 (fun _ => 1) (ind t)), by decide +kernel⟩
  · simp only [pairsPB, List.mem_cons, List.mem_nil_iff, or_false] at hπ
    rcases hπ with rfl | rfl | rfl
    · exact ⟨liftD (wI1 (fun _ => 1) (ind d0)), by decide +kernel⟩
    · exact ⟨liftD (wI1 (fun _ => 1) (ind d1)), by decide +kernel⟩
    · exact ⟨liftD (wI1 (fun _ => 1) (ind d2)), by decide +kernel⟩

/-! ## §4 The printed form of Theorem 3.10 of Yolcu–Aaronson–Heule, carried over to $\mathcal T^{\mathrm{rev}}$ and $\mathcal T$, does not hold -/

/-- **The printed form (reversed)**: if all 11 (unmarked) rules of the base system $\mathcal T^{\mathrm{rev}}$ are weakly oriented entrywise, then no dependency pair
of `P_D^rev` is strictly oriented in the order of Yolcu–Aaronson–Heule (no condition on the other pairs). Its premise is stronger, and its conclusion weaker, than those of the statement. -/
def LiteralDPrev : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : DLetter → NAff d), (∀ ρ ∈ rulesSTrev, NWeakD J ρ.plain) →
    ∀ π ∈ pairsPDrev, ¬ NStrictD J π

/-- **The printed form (forward)**. -/
def LiteralDP : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : DLetter → NAff d), (∀ ρ ∈ rulesST, NWeakD J ρ.plain) →
    ∀ π ∈ pairsPB, ¬ NStrictD J π

/-- The identity map of dimension 1 (for the marked letter). -/
def idN1 : NAff 1 := ⟨1, 0⟩

/-- The counterexample for the reversed form (the same as `IHash` of an internal review of the statement): the unmarked letters as in `INoMonoRev` (`[.] = 0`), `[.#] = y`. -/
def JLitRev : DLetter → NAff 1
  | mark _ => idN1
  | plain s => INoMonoRev s

/-- The counterexample for the forward form (found by an exhaustive search in dimension 1): all unmarked letters are constant maps (`[t] = [2] = 1`, the others 0), `[/#] = y`. -/
def JLit : DLetter → NAff 1
  | mark _ => idN1
  | plain s => wI1 (fun _ => 0) (fun s => if s = t ∨ s = d2 then 1 else 0) s

theorem JLitRev_facts : (∀ ρ ∈ rulesSTrev, NWeakD JLitRev ρ.plain) ∧
    NStrictD JLitRev ⟨[mark rgt, plain f], [mark rgt]⟩ ∧ ¬ NWeakTopD JLitRev ⟨[mark rgt, plain t], [mark rgt, plain d2]⟩ := by
  decide +kernel

theorem JLit_facts : (∀ ρ ∈ rulesST, NWeakD JLit ρ.plain) ∧
    NStrictD JLit ⟨[mark lft, plain d2], [mark lft, plain f, plain t]⟩ ∧
    ¬ NWeakTopD JLit ⟨[mark lft, plain d0], [mark lft, plain t]⟩ := by
  decide +kernel

/-- **Theorem 3.10 of Yolcu–Aaronson–Heule, carried over to $\mathcal T^{\mathrm{rev}}$ with its printed strength, does not hold**. -/
theorem not_literalRev : ¬ LiteralDPrev := fun h =>
  h 1 JLitRev JLitRev_facts.1 _ (by decide) JLitRev_facts.2.1

/-- **Theorem 3.10 of Yolcu–Aaronson–Heule, carried over to $\mathcal T$ with its printed strength, does not hold**. -/
theorem not_literal : ¬ LiteralDP := fun h =>
  h 1 JLit JLit_facts.1 _ (by decide) JLit_facts.2.1

/-- With the weak orientation of the other dependency pairs added to the premises, the printed form follows from the statement (the usable rules of the premises of the statement are among the 11 rules). -/
theorem literalRev_of_pairsWeak (hdp : NatBarrierDPrev) (d : ℕ) [NeZero d] (J : DLetter → NAff d)
    (hR : ∀ ρ ∈ rulesSTrev, NWeakD J ρ.plain) (hP : ∀ π ∈ pairsPDrev, NWeakD J π ∨ NStrictD J π) :
    ∀ π ∈ pairsPDrev, ¬ NStrictD J π :=
  natBarrierDPrev_full hdp d J (fun ρ hρ => hR ρ (by rw [usableSTrev_eq] at hρ; exact List.mem_of_mem_drop hρ)) hP

/-! ## §5 Dropping usable rules breaks the statement -/

/-- The general form with the set of rules and the set of dependency pairs as parameters. -/
def NatBarrierDPFor (U : List Rule) (P : List DRule) : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : DLetter → NAff d), (∀ ρ ∈ U, NWeakD J ρ.plain) →
    (∀ π ∈ P, NWeakTopD J π) → ∀ π ∈ P, ¬ NStrictTopD J π

theorem natBarrierDPrev_iff_for : NatBarrierDPrev ↔ NatBarrierDPFor usableSTrev pairsPDrev := Iff.rfl

theorem natBarrierDP_iff_for : NatBarrierDP ↔ NatBarrierDPFor usableST pairsPB := Iff.rfl

/-- Dropping `B^rev` breaks it: the extension of `IL315`, of the type of Lemma 3.15 of Yolcu–Aaronson–Heule, weakly orients `A^rev` and strictly orients `P_D^rev`. -/
theorem IL315_DP : (∀ ρ ∈ usableSTrev.take 6, NWeakD (liftD IL315) ρ.plain) ∧
    ∀ π ∈ pairsPDrev, NStrictTopD (liftD IL315) π := by
  decide +kernel

theorem not_barrierDPrev_dropB : ¬ NatBarrierDPFor (usableSTrev.take 6) pairsPDrev := fun h =>
  h 1 (liftD IL315) IL315_DP.1 (fun π hπ => ⟨(IL315_DP.2 π hπ).1, (IL315_DP.2 π hπ).2.le⟩)
    ⟨[mark rgt, plain f], [mark rgt]⟩ (by decide) (IL315_DP.2 _ (by decide))

/-- Dropping `t. → 2.` breaks it: the extension of the length interpretation `ILen` weakly orients `U` without `t. → 2.` and `P_B`, and strictly orients `/#0 → /#t`. -/
theorem ILen_DP : (∀ ρ ∈ usableST.erase rTdot, NWeakD (liftD ILen) ρ.plain) ∧
    (∀ π ∈ pairsPB, NWeakTopD (liftD ILen) π) ∧ NStrictTopD (liftD ILen) ⟨[mark lft, plain d0], [mark lft, plain t]⟩ := by
  decide +kernel

theorem not_barrierDP_dropTdot : ¬ NatBarrierDPFor (usableST.erase rTdot) pairsPB := fun h =>
  h 1 (liftD ILen) ILen_DP.1 ILen_DP.2.1 _ (by decide) ILen_DP.2.2

/-! ## §6 Negative controls -/

theorem ctrl_JLitRev_not_pairsWeak : ¬ ∀ π ∈ pairsPDrev, NWeakTopD JLitRev π := by decide +kernel

theorem ctrl_IL315_not_usable : ¬ ∀ ρ ∈ usableSTrev, NWeakD (liftD IL315) ρ.plain := by decide +kernel

theorem ctrl_IP3rev_not_strict_pair : ¬ ∃ π ∈ pairsPDrev, NStrictTopD (liftD IP3rev) π := by decide +kernel

/-! ## §7 As printed, Theorem 3.10 of Yolcu–Aaronson–Heule does not hold for $\mathcal Z$ and $\mathcal Z^{\mathrm{rev}}$ either (examples of an internal independent review) -/

namespace ZYah

/-- The letters of Zantema's system $\mathcal Z$ (Example 3.1 of Yolcu–Aaronson–Heule, p. 13): `1`, the blank `◇`, `h`, `s`, `t`, and the marked blank `◇#` (`H`). -/
inductive ZL | one | dia | h | s | t | H
  deriving DecidableEq, Repr

open ZL

/-- The interpretation of strings (composition in the same direction as `evN`). -/
def evZ {d : ℕ} (I : ZL → NAff d) : List ZL → NAff d
  | [] => NAff.id d
  | c :: w => (I c).comp (evZ I w)

/-- Entrywise weak comparison (`≳` of Yolcu–Aaronson–Heule). -/
def ZW {d : ℕ} (I : ZL → NAff d) (l r : List ZL) : Prop :=
  (∀ i j, (evZ I r).M i j ≤ (evZ I l).M i j) ∧ ∀ i, (evZ I r).v i ≤ (evZ I l).v i

instance {d : ℕ} (I : ZL → NAff d) (l r : List ZL) : Decidable (ZW I l r) :=
  @instDecidableAnd _ _ (@Fintype.decidableForallFintype _ _
      (fun i => (inferInstance : Decidable (∀ j, (evZ I r).M i j ≤ (evZ I l).M i j))) _) inferInstance

/-- Strict comparison in the order of Yolcu–Aaronson–Heule (formula (2): `M_ℓ ≳ M_r ∧ v_ℓ > v_r`). -/
def ZS {d : ℕ} [NeZero d] (I : ZL → NAff d) (l r : List ZL) : Prop := ZW I l r ∧ (evZ I r).v 0 < (evZ I l).v 0

instance {d : ℕ} [NeZero d] (I : ZL → NAff d) (l r : List ZL) : Decidable (ZS I l r) := instDecidableAnd

/-- The 7 rules of $\mathcal Z$ (Example 3.1 of Yolcu–Aaronson–Heule). -/
def rulesZ : List (List ZL × List ZL) :=
  [([h, ZL.one, ZL.one], [ZL.one, h]), ([ZL.one, ZL.one, h, dia], [ZL.one, ZL.one, s, dia]), ([h, ZL.one, dia], [t, ZL.one, ZL.one, dia]),
   ([ZL.one, s], [s, ZL.one]), ([ZL.one, t], [t, ZL.one, ZL.one, ZL.one]), ([dia, s], [dia, h]), ([dia, t], [dia, h])]

/-- A natural-number matrix interpretation of dimension 2 (an example of an internal independent review of the dependency pair statements). -/
def IZ : ZL → NAff 2
  | .one => ⟨!![3, 3; 3, 3], ![3, 3]⟩
  | .dia => ⟨!![0, 0; 0, 0], ![3, 3]⟩
  | .h => ⟨!![3, 0; 3, 2], ![2, 0]⟩
  | .s => ⟨!![3, 0; 0, 3], ![3, 3]⟩
  | .t => ⟨!![0, 0; 0, 0], ![0, 3]⟩
  | .H => ⟨!![1, 0; 3, 0], ![2, 3]⟩

/-- **As printed, Theorem 3.10 of Yolcu–Aaronson–Heule does not hold for $\mathcal Z$**: there is an interpretation of dimension 2 that weakly orients all 7 rules of $\mathcal Z$ entrywise,
strictly orients the pair `◇#s → ◇#h` of `I` in the order of Yolcu–Aaronson–Heule, and does not even weakly orient the other pair `◇#t → ◇#h` of `I`
(natural-number matrix interpretations are weakly monotone algebras; Yolcu–Aaronson–Heule, §2.3.1). -/
theorem Z_literal_false :
    (∀ p ∈ rulesZ, ZW IZ p.1 p.2) ∧ ZS IZ [H, s] [H, h] ∧ ¬ ZW IZ [H, t] [H, h] := by
  decide +kernel

/-- $\mathcal Z^{\mathrm{rev}}$ (both sides of each rule of $\mathcal Z$ reversed). -/
def rulesZrev : List (List ZL × List ZL) := rulesZ.map fun p => (p.1.reverse, p.2.reverse)

/-- A natural-number matrix interpretation of dimension 2 (an example of an internal independent review of the dependency pair statements). -/
def IZr : ZL → NAff 2
  | .one => ⟨!![0, 2; 0, 1], ![2, 2]⟩
  | .dia => ⟨!![0, 0; 0, 0], ![0, 0]⟩
  | .h => ⟨!![0, 2; 0, 1], ![2, 0]⟩
  | .s => ⟨!![1, 0; 0, 1], ![2, 0]⟩
  | .t => ⟨!![3, 1; 0, 3], ![2, 0]⟩
  | .H => ⟨!![2, 3; 0, 0], ![3, 0]⟩

/-- **As printed, the version of footnote 8 for $\mathcal Z^{\mathrm{rev}}$ does not hold either**: there is an interpretation of dimension 2 that strictly orients the first pair of
`J = {◇#h11 → ◇#s11, ◇#1h → ◇#11t}` in the order of Yolcu–Aaronson–Heule, does not even weakly orient the second, and weakly orients all 7 rules of $\mathcal Z^{\mathrm{rev}}$. -/
theorem Zrev_literal_false :
    (∀ p ∈ rulesZrev, ZW IZr p.1 p.2) ∧ ZS IZr [H, h, ZL.one, ZL.one] [H, s, ZL.one, ZL.one] ∧
      ¬ ZW IZr [H, ZL.one, h] [H, ZL.one, ZL.one, t] := by
  decide +kernel

end ZYah

/-! ## §8 The SCCs do not split (edges built from derivations with the usable rules) -/

/-- **The cycle 0 → 2 → 1 → 0 of `P_B`** (`0 : /#0 → /#t`, `1 : /#1 → /#ff`, `2 : /#2 → /#ft`): from the part below `/#` of the right-hand side of the pair `i`,
a derivation with rules of `U` reaches the form of the part below `/#` of the left-hand side of the pair `j`. -/
theorem pB_cycle :
    Chain [⟨[t, rgt], [d2, rgt]⟩] ([t] ++ [rgt]) ([d2] ++ [rgt]) ∧
    Chain [⟨[t, rgt], [d2, rgt]⟩, ⟨[f, d2], [d1, f]⟩] ([f, t] ++ [rgt]) ([d1] ++ [f, rgt]) ∧
    Chain [⟨[f, d2], [d1, f]⟩, ⟨[f, d1], [d0, t]⟩] ([f, f] ++ [d2, rgt]) ([d0] ++ [t, f, rgt]) ∧
    (∀ σ ∈ [(⟨[t, rgt], [d2, rgt]⟩ : Rule), ⟨[f, d2], [d1, f]⟩, ⟨[f, d1], [d0, t]⟩], σ ∈ usableST) := by
  refine ⟨Chain.cons ⟨[], [], rfl, rfl⟩ (Chain.nil _), Chain.cons ⟨[f], [], rfl, rfl⟩
    (Chain.cons ⟨[], [rgt], rfl, rfl⟩ (Chain.nil _)), Chain.cons ⟨[f], [rgt], rfl, rfl⟩
    (Chain.cons ⟨[], [f, rgt], rfl, rfl⟩ (Chain.nil _)), by decide⟩

/-- The two other edges of `P_B`: 0 → 1 (`t0 → 1t`) and 2 → 0 (`t0 → 1t`, `f1 → 0t`). -/
theorem pB_edges_more :
    Chain [⟨[t, d0], [d1, t]⟩] ([t] ++ [d0]) ([d1] ++ [t]) ∧
    Chain [⟨[t, d0], [d1, t]⟩, ⟨[f, d1], [d0, t]⟩] ([f, t] ++ [d0]) ([d0] ++ [t, t]) ∧
    (∀ σ ∈ [(⟨[t, d0], [d1, t]⟩ : Rule), ⟨[f, d1], [d0, t]⟩], σ ∈ usableST) := by
  refine ⟨Chain.cons ⟨[], [], rfl, rfl⟩ (Chain.nil _), Chain.cons ⟨[f], [], rfl, rfl⟩
    (Chain.cons ⟨[], [t], rfl, rfl⟩ (Chain.nil _)), by decide⟩

/-- **The four edges of `P_D^rev`** (`0 : .#f → .#`, `1 : .#t → .#2`). -/
theorem pDrev_edges :
    Chain [] ([] ++ [f]) ([f] ++ []) ∧ Chain [] ([] ++ [t]) ([t] ++ []) ∧
    Chain [⟨[d2, f], [f, d1]⟩] ([d2] ++ [f]) ([f] ++ [d1]) ∧
    Chain [⟨[d2, t], [t, d2]⟩] ([d2] ++ [t]) ([t] ++ [d2]) ∧
    (∀ σ ∈ [(⟨[d2, f], [f, d1]⟩ : Rule), ⟨[d2, t], [t, d2]⟩], σ ∈ usableSTrev) := by
  refine ⟨Chain.nil _, Chain.nil _, Chain.cons ⟨[], [], rfl, rfl⟩ (Chain.nil _),
    Chain.cons ⟨[], [], rfl, rfl⟩ (Chain.nil _), by decide⟩

/-! ## §9 Examples for argument filters -/

/-- `[t] = 1` (constant), `[f] = y`, `[1] = [2] = 1`, the other unmarked letters 0, `[.#] = y` (found by an exhaustive search in dimension 1). -/
def JFiltT : DLetter → NAff 1
  | mark _ => idN1
  | plain s => wI1 (fun s => if s = f then 1 else 0) (fun s => if s = t ∨ s = d1 ∨ s = d2 then 1 else 0) s

/-- It satisfies the premises for the filter that drops the argument of `t`, and does not weakly orient the rule `0t → t1` with leftmost letter `0` (outside the premises of `NatBarrierDPrev`;
`dpRev_filt_t` applies). Consistent with the conclusion. -/
theorem JFiltT_facts : (JFiltT (plain t)).M = 0 ∧ (∀ ρ ∈ usableRevT, NWeakD JFiltT ρ.plain) ∧
    (∀ π ∈ pairsPDrev, NWeakTopD JFiltT π) ∧ ¬ NWeakD JFiltT (⟨[d0, t], [t, d1]⟩ : Rule).plain ∧
    ∀ π ∈ pairsPDrev, ¬ NStrictTopD JFiltT π := by
  decide +kernel

/-- An interpretation of dimension 2 in which `[t]` is not constant (an example of an internal independent review of the dependency pair statements): it weakly orients the 6 rules for the filter dropping the argument of `t` and the dependency pairs,
and strictly orients `.#f → .#`. So the premise `M_t = 0` of `dpRev_filt_t` cannot be dropped. -/
def JDrop0 : DLetter → NAff 2
  | mark _ => ⟨!![0, 2; 0, 0], ![0, 0]⟩
  | plain f => ⟨!![0, 0; 0, 1], ![0, 1]⟩
  | plain t => ⟨!![2, 0; 2, 2], ![2, 2]⟩
  | plain d0 => ⟨0, 0⟩
  | plain d1 => ⟨!![1, 0; 0, 2], ![2, 0]⟩
  | plain d2 => ⟨!![2, 0; 2, 2], ![1, 0]⟩
  | plain lft => ⟨!![3, 3; 3, 3], ![3, 3]⟩
  | plain rgt => ⟨0, 0⟩

theorem JDrop0_facts : (∀ ρ ∈ usableRevT, NWeakD JDrop0 ρ.plain) ∧ (∀ π ∈ pairsPDrev, NWeakTopD JDrop0 π) ∧
    NStrictTopD JDrop0 ⟨[mark rgt, plain f], [mark rgt]⟩ ∧ (JDrop0 (plain t)).M ≠ 0 := by
  decide +kernel

/-- `[f] = 0` (constant), `[0] = y + 1`, the other unmarked letters the identity, `[.#] = 0` (dimension 1). It satisfies the premises for the filter that drops the argument of `f`, and
does not weakly orient `1f → t0` (outside the premises of `NatBarrierDPrev`; `dpRev_filt_f` applies). -/
def JFiltF : DLetter → NAff 1
  | mark _ => ⟨0, 0⟩
  | plain s => wI1 (fun s => if s = f then 0 else 1) (fun s => if s = d0 then 1 else 0) s

theorem JFiltF_facts : (JFiltF (plain f)).M = 0 ∧ (∀ ρ ∈ usableRevF, NWeakD JFiltF ρ.plain) ∧
    (∀ π ∈ pairsPDrev, NWeakTopD JFiltF π) ∧ ¬ NWeakD JFiltF (⟨[d1, f], [t, d0]⟩ : Rule).plain ∧
    ∀ π ∈ pairsPDrev, ¬ NStrictTopD JFiltF π := by
  decide +kernel

end W5

end Collatz.Arctic.NatQ5
