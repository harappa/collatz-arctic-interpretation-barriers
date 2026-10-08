/-
The statement of the main theorem on rule removal for the system $\mathcal H$ (collatz-T-5or7mod8), and the intermediate statement `AutoCoreH`.
**The statements are frozen** (after an independent review).

* `ArcticBarrierHT` (Theorem 3.1 for $\mathcal H$): an arctic interpretation (of any dimension) that weakly orients all 11 rules and has all
  entries `(M_s)₀₀` finite strictly orients no rule. It differs from `Statement.ArcticBarrierST`
  only in the set of rules (it is the same as `NonVacuity.BarrierFor rulesHT` by definition; `HTPDB/NonVacuity.lean`).
* `AutoCoreH`: the intermediate statement on values and numbers of uses (Definition 5.4 with $f = H$; proved as Theorem 5.5 for $H$).
  It is `Gen.AutoCoreG` applied to the map, domain, rules and canonical derivations of $H$. The `AutoCore` of $T$ is
  the same as `Gen.AutoCoreG T (2 ≤ ·) rulesST canDeriv` by definition (`Gen.autoCore_iff`).
  - The values of `Hmap` (the identity) outside the domain `HModel.HDom` ($n \ge 8$ and $n \equiv 0 \bmod 4$ or $n \equiv 7 \bmod 8$)
    play no role: the slope hypothesis concerns only points of `HDom`, and all orbit points in the conclusion lie in `HDom`.
  - Since $n < 8$ is not in `HDom`, the only orbit in the conclusion is then the empty one (`m = 0`), with 0 uses.
-/
import CollatzProof.Arctic.Gen.Model
import CollatzProof.Arctic.HModel.Defs
import CollatzProof.Arctic.HTPDB.Defs

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic

/-- **Statement of the main theorem** (Theorem 3.1, the system $\mathcal H$, rule removal). -/
def ArcticBarrierHT : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I → (∀ ρ ∈ rulesHT, Weak I ρ) →
    ∀ ρ ∈ rulesHT, ¬ Strict I ρ

/-- **Intermediate statement** (values and numbers of uses, for the map, domain, rules and canonical derivations of $H$). -/
def AutoCoreH : Prop := Gen.AutoCoreG HModel.Hmap HModel.HDom rulesHT canDerivH

end Collatz.Arctic.HTPDB
