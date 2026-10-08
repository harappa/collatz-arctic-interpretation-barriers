/-
The barrier for arctic rule removal for $R_H$ (the 12-rule system of Section 6 of Paper II), without hypotheses
(Theorem 3.1(ii), proved at the end of Section 7).

Applies the frozen assembly `rh_of_specs`, `rhSub_of_specs` of `RH/Spec.lean` to the theorems of the three units.
* `RH/Canon.lean`: `specCanonRH` (the canonical derivations `canRH n →* canRH (Hmap n)`, whose rules are used rules).
* `RH/Bridge.lean`: `specBridgeRH` (`Φ(canRH n)` is the automaton value with `u` = row 0 of `(I L ⊗ I t)`).
* `RH/Count.lean`: `specCountRH` (comparison of numbers of uses, from `canDerivRH n = (canDerivH n).flatMap liftRH`).
* The rest are the theorems for $\mathcal H$ (unconditional): `autoCoreH_holds` in `RH/Spec.lean` obtains the intermediate statement `AutoCoreH` of $\mathcal H$
  from `HTPDB.autoCoreH_of_specs` and `hsp_holds`, `HModel.specH*`, `Gen.spec*`, `HTPDB.spec*`.
  `AutoCoreRH` follows from it by the comparison of numbers of uses alone (`autoCoreRH_of_autoCoreH`, logic only).

**The formal proof and a direct proof** (an observation of the internal independent review; the paper gives only the formal route, Lemma 7.4 and Proposition 7.5):
* A direct proof for $R_H$ would show that the left-end rules `L1 → Lt` and `L2 → Ltf` of $R_H$
  are used by windows specific to $R_H$: `L1` if the leading three bits of a block boundary point are `100`,
  `L2` if they are `111`.
* The Lean proof does not use these windows. The canonical derivations of $R_H$ are those of $\mathcal H$ with each left-end rule `/d` replaced by two steps
  (`aRule 1 d` and `L((3 + d)/2)`) (`canDerivRH_eq`), so the number of uses of `L1 → Lt` is at least that of `/0 → /t`, and
  that of `L2 → Ltf` is at least that of `/1 → /ff` (`specCountRH`). The uses of the left-end rules of $\mathcal H$
  (`HTPDB.specLeftUseH`: the arcs `𝒜_0`, `𝒜_1` of the proof of Proposition B.9 for the left-end digit `d = ⌊3 mant(P)⌋ - 3` of an $\mathsf a$-step; Section 7) are transferred by this comparison
  to `L1` and `L2`. `L2` comes not from the window `111` (`d = 2`) of the direct proof but from the arc `d = 1` (mantissa in `[4/3, 5/3)`).
  Both windows occur with positive frequency, so the conclusion (the number of uses is at least `c k` with probability close to 1) is the same.
* The dynamic and carry rules are likewise transferred from the numbers of uses for $\mathcal H$ (the numbers of uses of the dynamic rules are equal, and those of the carry rules are
  at least those for $\mathcal H$).

The closure of the main theorem consists of the closure of `AutoCoreH` for $\mathcal H$ (block model, swap argument, window frequencies, `HSP`, left-end rules, carry families) and
the six files of `RH/` (`Defs`, `Statement`, `Spec`, `Canon`, `Bridge`, `Count`). `RH/NonVacuity.lean` and
`RH/Check.lean` serve only as checks and are not in the closure.
-/
import CollatzProof.Arctic.RH.Canon
import CollatzProof.Arctic.RH.Bridge
import CollatzProof.Arctic.RH.Count

namespace Collatz.Arctic.RH

open Collatz.Arctic

/-- **Theorem 3.1(ii)** ($R_H$, rule removal): an arctic interpretation (of any dimension) with all `(M_s)₀₀` finite that weakly orients all ten used rules
strictly orients none of the used rules. Unconditional. -/
theorem arcticBarrierRH : ArcticBarrierRH :=
  rh_of_specs specCanonRH specBridgeRH specCountRH

/-- **The last sentence of Theorem 3.1(ii)** ($R_H$, without the hypothesis (CF)): for an interpretation that weakly orients all rules of `R'`, `usedRH ⊆ R' ⊆ rulesRH`,
the only strictly oriented rules are `L0 → L` and `Lf → L`. Unconditional. -/
theorem arcticBarrierRHSub : ArcticBarrierRHSub :=
  rhSub_of_specs specCanonRH specBridgeRH specCountRH

end Collatz.Arctic.RH
