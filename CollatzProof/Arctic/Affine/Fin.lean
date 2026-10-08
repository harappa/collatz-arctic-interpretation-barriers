/-
**Absolute parts do not change the barrier if every `(M_σ)₀₀` is finite** (Corollary 3.8 of the paper).

Interpret each letter by an arctic linear function `x ↦ M_σ ⊗ x ⊕ c_σ` (any dimension, `𝔸_ℕ`, arbitrary absolute parts `c_σ`) with every `(M_σ)₀₀`
finite. If the interpretation weakly orients all rules of a set of rules (at every point), then it strictly orients none of them (at every point).

* Proof (`affBarrierFin_of`): the comparison at every point gives the coefficientwise comparison (`Coef.coef_weak`, `coef_strict`). In particular the matrix part
  `σ ↦ M_σ` alone orients the rules weakly, respectively strictly (`weak_of_pweak`, `strict_of_pstrict`), and since every `(M_σ)₀₀` is finite it lies in the class of the frozen
  statements (the class of Theorem 3.1). The absolute parts are not used.
* Instances: `𝒯` (`affFin_ST`), the reversed `𝒯`, `𝓗`, the reversed `𝓗`, the 10 used rules of `R_H` and their reversal,
  and the form for subsystems of `R_H` (`affFin_RHSub`: only `L0 → L` and `Lf → L` can be strictly oriented).
* Allowing `(M_/)₀₀ = −∞` for the single letter `/` already breaks this (`nonleft_*` in `Witness.lean`: examples of dimension 1 in which `/` is a constant function).
-/
import CollatzProof.Arctic.Affine.Coef
import CollatzProof.Arctic.NonVacuity4
import CollatzProof.Arctic.HTPDB.NonVacuity
import CollatzProof.Arctic.HTPDB.Final
import CollatzProof.Arctic.RH.Rev

namespace Collatz.Arctic.Affine

open Collatz.Arctic

/-- The barrier for rule removal with interpretations by arctic linear functions whose entries `(M_σ)₀₀` are all finite (comparison at every point). -/
def AffBarrierFin (R : List Rule) : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : Letter → AffFun Arc d), (∀ σ, (J σ).M ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0) →
    (∀ ρ ∈ R, PWeak J ρ) → ∀ ρ ∈ R, ¬ PStrict J ρ

lemma fin00_matOf {d : ℕ} (hd : 0 < d) (J : Letter → AffFun Arc d)
    (h : ∀ σ, (J σ).M ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0) : Fin00 hd (matOf J) := h

/-- **From the barrier for matrices to the barrier with absolute parts.** -/
theorem affBarrierFin_of {R : List Rule} (hR : NonVacuity.BarrierFor R) : AffBarrierFin R :=
  fun d hd J hfin hweak ρ hρ hstr =>
    hR d hd (matOf J) (fin00_matOf hd J hfin) (fun ρ' h' => weak_of_pweak J ρ' (hweak ρ' h')) ρ hρ
      (strict_of_pstrict J ρ hstr)

/-- `𝒯` (Theorem 3.1 (i)). -/
theorem affFin_ST : AffBarrierFin rulesST := affBarrierFin_of arcticBarrierST

/-- The reversed `𝒯`. -/
theorem affFin_STrev : AffBarrierFin NonVacuity.rulesSTrev := affBarrierFin_of NonVacuity.barrier_STrev

/-- `𝓗` (collatz-T-5or7mod8). -/
theorem affFin_HT : AffBarrierFin HTPDB.rulesHT := affBarrierFin_of HTPDB.arcticBarrierHT

/-- The reversed `𝓗`. -/
theorem affFin_HTrev : AffBarrierFin HTPDB.NonVacuityH.rulesHTrev :=
  affBarrierFin_of (HTPDB.NonVacuityH.barrier_HTrev_of HTPDB.arcticBarrierHT)

/-- The 10 used rules of `R_H` (Theorem 3.1 (ii)). -/
theorem affFin_RH : AffBarrierFin RH.usedRH := affBarrierFin_of RH.arcticBarrierRH

/-- The reversed 10 used rules of `R_H`. -/
theorem affFin_RHrev : AffBarrierFin (RH.usedRH.map NonVacuity.revRule) :=
  affBarrierFin_of RH.arcticBarrierRHrev

/-- The form for subsystems of `R_H`: an interpretation by arctic linear functions with all `(M_σ)₀₀` finite that weakly orients all rules of
some `R'` with `usedRH ⊆ R' ⊆ rulesRH` strictly orients no rule of `R'` other than `L0 → L` and `Lf → L`. -/
theorem affFin_RHSub (R' : List Rule) (hused : ∀ ρ ∈ RH.usedRH, ρ ∈ R') (hsub : ∀ ρ ∈ R', ρ ∈ RH.rulesRH)
    (d : ℕ) (hd : 0 < d) (J : Letter → AffFun Arc d) (hfin : ∀ σ, (J σ).M ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0)
    (hweak : ∀ ρ ∈ R', PWeak J ρ) : ∀ ρ ∈ R', PStrict J ρ → ρ = RH.l0Rule ∨ ρ = RH.lfRule :=
  fun ρ hρ hstr =>
    RH.arcticBarrierRHSub R' hused hsub d hd (matOf J) (fin00_matOf hd J hfin)
      (fun ρ' h' => weak_of_pweak J ρ' (hweak ρ' h')) ρ hρ (strict_of_pstrict J ρ hstr)

end Collatz.Arctic.Affine
