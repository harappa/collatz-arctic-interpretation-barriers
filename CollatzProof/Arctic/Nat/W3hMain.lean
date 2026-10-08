/-
# Natural-number matrix interpretations ($\mathcal T$): the assembly (Section 12.9 of the paper)

The core statement `W3CoreStmt` (Theorem 10.10 of the paper; unchanged, as stated in `AutoCore.lean`) is assembled in the order of
quantifiers below (the written proof is Section 12.9 of the paper).

* **`DecompStmtT0`**: the frozen statement `DecompStmt` (Proposition 12.11 of the paper) with, in addition, the lower bound
  `t₀ ≥ |τ'| + |u♯|` for the position of the first long sojourn of the decomposition data. It holds for the construction of the decomposition data (`t₀` is the end of an unbroken copy of the top `(u♯)^R`).
  With the frozen statement `DecompData` alone, the detours at positions inside the first top copy (positions where the forward state does not lie in the class of $\mathcal K_{\mathrm s}$)
  cannot be removed by the degeneration lemma (Lemma 12.22 of the paper).
* **`CaseBStmt`** (case B does not occur): for a setting `S`, if the value is monotone on `3 ∤ n`, then `𝔎` contains a configuration whose coefficients of positive degree
  are all 0 (Proposition 12.31 of the paper; the conclusion `d(\mathrm{conf}_{\mathrm{lo}}) ≤ 0`). Proved in `W3hCaseB.lean`.
* **`core_of_setup`**: from a setting and `CaseBStmt`, the conclusion of the core statement (case A, Lemma 12.30 of the paper, `caseA`).
* **`w3CoreStmt_of_decompT0_caseB`**: `DecompStmtT0 → CaseBStmt → W3CoreStmt`. The order of quantifiers is
  `A → \tilde A := liftT A → Q_{\mathrm s}, \mathcal M_{\mathrm s}, \mathcal K_{\mathrm s}, e, u♯ (exists_sharp) → R := |\tilde Q| + 1 →
  σ₀ (exists_beta0: the word of r_{σ₀} contains (u♯)^R) → decomposition data D → 𝔎, coefficients → … → k → σ → n → u`.
-/
import CollatzProof.Arctic.Nat.W3hCaseA
import CollatzProof.Arctic.Nat.AutoCore

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Collatz.Arctic.NatQ5.W3c Collatz.Arctic.NatQ5.W3h
open Collatz.Arctic.MinIdeal (BRel)

/-- **The statement `DecompStmt` with the lower bound for `t₀`**: if all components are 0/1, `u♯` is `Sharp` and `R ≥ |Q|`, then for all `τ'`, `y''`, `z`
there are decomposition data in which every first long sojourn starts at a position at least `|τ'| + |u♯|`. -/
def DecompStmtT0 : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : ValAuto Q), (∀ C, IsComp A C → ZeroOne A C) →
    ∀ (K : Set (BRel (ZIdx A))) (u : List (Fin 2)) (e : BRel (ZIdx A)), Sharp A K u e →
      ∀ R, Fintype.card Q ≤ R → ∀ τ' y'' z : List (Fin 2),
        ∃ D : DecompData A u τ' y'' z R, ∀ γ, τ'.length + u.length ≤ D.t0 γ

/-- `DecompStmtT0` implies `DecompStmt`. -/
theorem decompStmt_of_T0 (h : DecompStmtT0) : DecompStmt := by
  intro Q _ _ A h01 K u e hS R hR τ' y'' z
  obtain ⟨D, -⟩ := h Q A h01 K u e hS R hR τ' y'' z
  exact ⟨D⟩

/-- **Case B does not occur** (Proposition 12.31 of the paper; the form of the conclusion `d(conf_lo) ≤ 0`): every setting of an automaton whose value
does not increase along steps of `T` on `3 ∤ n` has a configuration in `𝔎` whose coefficients of positive degree are all 0. -/
def CaseBStmt : Prop :=
  ∀ {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : W3h.Setup B), AutoMono3 B →
    ∃ c ∈ S.Kset, ∀ d, 1 ≤ d → S.coef d c.1 = 0

/-- From a setting and the statement that case B does not occur, the conclusion of the core statement. -/
theorem W3h.core_of_setup (hB : CaseBStmt) {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q}
    (S : W3h.Setup B) (hmono : AutoMono3 B) :
    ∀ ρ ∈ rulesST, ∀ K₀ : ℕ, ∃ n, K₀ ≤ n ∧ ¬ 3 ∣ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ aval B (binWord n) < usesOrbit ρ n m := by
  obtain ⟨c, hc, hcoef⟩ := hB S hmono
  exact S.caseA hc hcoef

/-- A setting of the automaton exists (the first step of the assembly in Section 12.9 of the paper). -/
theorem W3h.exists_setup (hD : DecompStmtT0) {Q : Type} [Fintype Q] [DecidableEq Q] (B : ValAuto Q)
    (h01 : ∀ C, IsComp B C → ZeroOne B C) : Nonempty (W3h.Setup B) := by
  obtain ⟨K, us, e, hS⟩ := exists_sharp B
  set R := Fintype.card Q + 1
  obtain ⟨β₀, y'', z, hy⟩ := W3h.Setup.exists_beta0 ((List.replicate R us).flatten)
  obtain ⟨D, hD0⟩ := hD Q B h01 K us e hS R (by omega) [] y'' z
  exact ⟨⟨h01, K, us, e, hS, R, by omega, by omega, β₀, y'', z, hy, D,
    fun γ => by simpa using hD0 γ⟩⟩

/-- **The core statement** (`W3CoreStmt`, unchanged; Theorem 10.10 of the paper) from `DecompStmtT0` and the statement that case B does not occur. -/
theorem w3CoreStmt_of_decompT0_caseB (hD : DecompStmtT0) (hB : CaseBStmt) : W3CoreStmt := by
  intro Q _ _ A h01 hmono ρ hρ K₀
  obtain ⟨S⟩ := W3h.exists_setup hD (liftT A) h01
  obtain ⟨n, hn, h3, m, horb, hlt⟩ := W3h.core_of_setup hB S hmono ρ hρ K₀
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (h0 ▸ dvd_zero 3) h3
    · exact h0
  refine ⟨n, hn, m, horb, ?_⟩
  rwa [aval_liftT_of_not_dvd A hn1 h3] at hlt

end Collatz.Arctic.NatQ5
