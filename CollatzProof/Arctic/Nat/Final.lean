/-
# The six frozen statements without hypotheses

The core statement `w3CoreStmt : W3CoreStmt` (Theorem 10.10 of the paper; `W3hCore.lean`, without hypotheses) is carried to `CaseACore` by the bridge `caseACore_of_w3CoreStmt`,
and passed to the assembly with Corollary 10.9 and with the reversed and dependency pair forms (`allBarriersDP_of_caseACore` of `BridgeRevW3.lean`; the forward case is
`natBarrierST_of_caseACore` of `H2Main.lean`). The frozen statements (`Statement.lean`, `StatementRev.lean`, `StatementDP.lean`) are not changed.

* `allBarriers_final`: `NatBarrierST ∧ NatBarrierSTB ∧ NatBarrierSTrev ∧ NatBarrierSTrevTop ∧ NatBarrierDP ∧ NatBarrierDPrev`.
* The individual statements: `natBarrierST_final`, `natBarrierSTB_final`, `natBarrierSTrev_final`, `natBarrierSTrevTop_final`,
  `natBarrierDP_final`, `natBarrierDPrev_final`.

Together they are Theorem 9.2 of the paper.
-/
import CollatzProof.Arctic.Nat.W3hCore
import CollatzProof.Arctic.Nat.BridgeRevW3

namespace Collatz.Arctic.NatQ5

/-- `CaseACore` from the core statement of Theorem 10.10 (without hypotheses). -/
theorem caseACore : CaseACore := caseACore_of_w3CoreStmt w3CoreStmt

/-- **The six frozen statements without hypotheses**. -/
theorem allBarriers_final :
    NatBarrierST ∧ NatBarrierSTB ∧ NatBarrierSTrev ∧ NatBarrierSTrevTop ∧ NatBarrierDP ∧ NatBarrierDPrev :=
  allBarriersDP_of_caseACore caseACore

theorem natBarrierST_final : NatBarrierST := allBarriers_final.1

theorem natBarrierSTB_final : NatBarrierSTB := allBarriers_final.2.1

theorem natBarrierSTrev_final : NatBarrierSTrev := allBarriers_final.2.2.1

theorem natBarrierSTrevTop_final : NatBarrierSTrevTop := allBarriers_final.2.2.2.1

theorem natBarrierDP_final : NatBarrierDP := allBarriers_final.2.2.2.2.1

theorem natBarrierDPrev_final : NatBarrierDPrev := allBarriers_final.2.2.2.2.2

end Collatz.Arctic.NatQ5
