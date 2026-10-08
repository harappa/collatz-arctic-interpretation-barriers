/-
# The core statement `W3CoreStmt` (Theorem 10.10 of the paper) without hypotheses

* **`caseB : CaseBStmt`** (Proposition 12.31 of the paper; the conclusion `d(conf_lo) ≤ 0`): by contradiction, `caseB_false` of `W3hCaseB.lean`.
* **`decompStmtT0 : DecompStmtT0`**: in the decomposition data `W3c.decompData` (`Nat/W3DecompProof8.lean`; Proposition 12.11 of the paper) the first long sojourn
  starts at `t₀ γ = |τ'| + γ₁ |u♯| + |u♯| ≥ |τ'| + |u♯|`.
* **`w3CoreStmt_of_decompT0 : DecompStmtT0 → W3CoreStmt`** (the assembly of Section 12.9 of the paper; the frozen `DecompStmt` alone does not suffice,
  so the hypothesis is `DecompStmtT0`, which adds the lower bound for `t₀`).
* **`w3CoreStmt : W3CoreStmt`** (without hypotheses).

The written proof is Section 12.9 of the paper.
-/
import CollatzProof.Arctic.Nat.W3hCaseB
import CollatzProof.Arctic.Nat.W3hMain
import CollatzProof.Arctic.Nat.W3DecompProof8

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Collatz.Arctic.NatQ5.W3c Collatz.Arctic.NatQ5.W3h

/-- **Case B does not occur** (Proposition 12.31 of the paper). -/
theorem caseB : CaseBStmt := by
  intro Q _ _ B S hmono
  by_contra hcon
  push Not at hcon
  exact S.caseB_false hmono (fun c hc => by
    obtain ⟨d, hd, hne⟩ := hcon c hc
    exact ⟨d, hd, lt_of_le_of_ne (S.coef_nonneg d c.1) (Ne.symm hne)⟩)

/-- **The decomposition data `W3c.decompData` satisfy `t₀ ≥ |τ'| + |u♯|`** (Proposition 12.11 of the paper). -/
theorem decompStmtT0 : DecompStmtT0 := by
  intro Q _ _ A h01 K u e hS R hR τ' y'' z
  refine ⟨W3c.decompData h01 hS hR τ' y'' z, fun γ => ?_⟩
  show τ'.length + u.length ≤ τ'.length + γ.1.val * u.length + u.length
  omega

/-- **The assembly** (Section 12.9 of the paper): the core statement from `DecompStmtT0`. -/
theorem w3CoreStmt_of_decompT0 (hD : DecompStmtT0) : W3CoreStmt :=
  w3CoreStmt_of_decompT0_caseB hD caseB

/-- **The core statement** (`W3CoreStmt`, unchanged; Theorem 10.10 of the paper) without hypotheses. -/
theorem w3CoreStmt : W3CoreStmt := w3CoreStmt_of_decompT0 decompStmtT0

end Collatz.Arctic.NatQ5
