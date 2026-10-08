/-
# 𝒯^rev and the dependency pair forms: assembly from the narrow entrance `CaseACore`

Passing the `GenValueCore` returned by `natBarrierST_of_caseACore` (`H2Main.lean`; (H2) is proved in Lean without hypotheses) to
`natBarrierSTrev_of_genCore` and `natBarrierSTrevTop_of_genCore` of `BridgeRev.lean`, the only hypothesis left in the two reversed statements is also `CaseACore`
(or `W3CoreStmt`, Theorem 10.10 of the paper). This is the same entrance as in the forward case.

**Relation to a fallback considered during the proof**: `CaseACore` is a form for general value automata, and the automaton of the transposed family of the reversed system
(`genAuto (transFam I) none (some 0)`) is not of the form `natAuto` of a natural-number matrix interpretation. Even if the proof had fallen back to the form specialized to `natAuto I`
(a narrower entrance), the reversed statements would follow from `natBarrierSTrev_of_core : NatValueCore → …` of `BridgeRev.lean`
(the transposed family is carried to a monotone natural-number matrix interpretation by the value embedding `embInterp`, Lemma 10.5). The reversed system adds nothing
to the form of the target proved in Section 12.
-/
import CollatzProof.Arctic.Nat.BridgeRev
import CollatzProof.Arctic.Nat.BridgeDP
import CollatzProof.Arctic.Nat.H2Main

namespace Collatz.Arctic.NatQ5

/-- **Assembly**: from `CaseACore`, the reversed statement `NatBarrierSTrev` and the top statement `NatBarrierSTrevTop`. -/
theorem natBarrierSTrev_of_caseACore (h3 : CaseACore) : NatBarrierSTrev ∧ NatBarrierSTrevTop :=
  ⟨natBarrierSTrev_of_genCore (natBarrierST_of_caseACore h3).2.2,
    natBarrierSTrevTop_of_genCore (natBarrierST_of_caseACore h3).2.2⟩

/-- The form from the statement `W3CoreStmt` (Theorem 10.10 of the paper). -/
theorem natBarrierSTrev_of_w3CoreStmt (h3 : W3CoreStmt) : NatBarrierSTrev ∧ NatBarrierSTrevTop :=
  natBarrierSTrev_of_caseACore (caseACore_of_w3CoreStmt h3)

/-- The four statements together: from `CaseACore`, the forward and reversed barriers, and the statements for the forward left-end rules and the reversed top rules. -/
theorem allBarriers_of_caseACore (h3 : CaseACore) :
    NatBarrierST ∧ NatBarrierSTB ∧ NatBarrierSTrev ∧ NatBarrierSTrevTop :=
  ⟨(natBarrierST_of_caseACore h3).1, (natBarrierST_of_caseACore h3).2.1, (natBarrierSTrev_of_caseACore h3).1,
    (natBarrierSTrev_of_caseACore h3).2⟩

/-- The two dependency pair forms (`StatementDP.lean`) also follow from `CaseACore` (by the equivalence with the top statements, `BridgeDP.lean`). -/
theorem natBarrierDP_of_caseACore (h3 : CaseACore) : NatBarrierDP ∧ NatBarrierDPrev :=
  ⟨natBarrierDP_of_STB (natBarrierST_of_caseACore h3).2.1,
    natBarrierDPrev_of_top (natBarrierSTrev_of_caseACore h3).2⟩

/-- The six statements together: from `CaseACore`. -/
theorem allBarriersDP_of_caseACore (h3 : CaseACore) :
    NatBarrierST ∧ NatBarrierSTB ∧ NatBarrierSTrev ∧ NatBarrierSTrevTop ∧ NatBarrierDP ∧ NatBarrierDPrev :=
  ⟨(allBarriers_of_caseACore h3).1, (allBarriers_of_caseACore h3).2.1, (allBarriers_of_caseACore h3).2.2.1,
    (allBarriers_of_caseACore h3).2.2.2, (natBarrierDP_of_caseACore h3).1, (natBarrierDP_of_caseACore h3).2⟩

end Collatz.Arctic.NatQ5
