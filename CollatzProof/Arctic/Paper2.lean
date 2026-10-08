/-
Names following the numbering of the paper (the arctic barrier), part 2: Section 4, the boundary of the barrier. Imported by `Paper.lean`.
Names of the form described in Appendix A of the paper. All are aliases of existing theorems, and their types are copies of the statements
of the existing theorems.

* Proposition 4.1 (`DPWeak2`), Proposition 4.2 (`DPWeak3`), Proposition 4.3 (`RH/NonVacuity`, interpretation `RH.NonVacuityRH.ILeft`),
  Proposition 4.6 (`DPWeak4`, also the contrapositives).
* For Proposition 4.5, every Lean theorem on which it rests is given an alias (more than the formal status line of Proposition 4.5 names one by one). The names are
  `paper_prop_4_5_<X>` for $\mathcal T$, `paper_prop_4_5_H_<X>` for $\mathcal H$, and `paper_prop_4_5_RH_<X>` for $R_H$.
-/
import CollatzProof.Arctic.DPWeak4
import CollatzProof.Arctic.HTPDB.NonVacuity
import CollatzProof.Arctic.RH.NonVacuity

namespace Collatz.Arctic.Paper

open Collatz.Arctic

/-! ## Section 4: The boundary of the barrier -/

/-- **Proposition 4.1** (weakened-premise forms, $\mathcal T$). -/
theorem paper_prop_4_1_DPw : ArcticBarrierDPw := arcticBarrierDPw
theorem paper_prop_4_1_DPrevw : ArcticBarrierDPrevw := arcticBarrierDPrevw
theorem paper_prop_4_1_BZf : ArcticBarrierBZf := arcticBarrierBZf
theorem paper_prop_4_1_BZrevf : ArcticBarrierBZrevf := arcticBarrierBZrevf
theorem paper_prop_4_1_BZw : ArcticBarrierBZw := arcticBarrierBZw
theorem paper_prop_4_1_BZrevw : ArcticBarrierBZrevw := arcticBarrierBZrevw

section Boundary

open NonVacuity

/-- **Proposition 4.2** (the premises cannot be weakened further). -/
theorem paper_prop_4_2_markOnly : ¬ BarrierDPFor [DLetter.mark Letter.lft] usableST pairsPB :=
  dw_not_DP_markOnly
theorem paper_prop_4_2_markOnly_rev :
    ¬ BarrierDPFor [DLetter.mark Letter.rgt] usableSTrev pairsPDrev := dw_not_DPrev_markOnly
theorem paper_prop_4_2_noMark : ¬ BarrierDPFor lettersPB.tail usableST pairsPB := dw_not_DP_noMark
theorem paper_prop_4_2_noMark_rev : ¬ BarrierDPFor lettersPDrev.tail usableSTrev pairsPDrev :=
  dw_not_DPrev_noMark
theorem paper_prop_4_2_noMark_BZ : ¬ BarrierBZFor lettersPB.tail usableST pairsPB :=
  dw_not_BZ_noMark
theorem paper_prop_4_2_noMark_BZrev : ¬ BarrierBZFor lettersPDrev.tail usableSTrev pairsPDrev :=
  dw_not_BZrev_noMark

/-- **Proposition 4.3** (false for all 12 rules of $R_H$, and for the used rules with one of `L0`, `Lf` added; the interpretation is `ILeft`). -/
theorem paper_prop_4_3 : ¬ BarrierFor RH.rulesRH := RH.NonVacuityRH.not_barrier_rulesRH
theorem paper_prop_4_3_l0 : ¬ BarrierFor (RH.usedRH ++ [RH.l0Rule]) :=
  RH.NonVacuityRH.not_barrier_used_l0
theorem paper_prop_4_3_lf : ¬ BarrierFor (RH.usedRH ++ [RH.lfRule]) :=
  RH.NonVacuityRH.not_barrier_used_lf

/-- **Proposition 4.5** ($\mathcal T$: counterexamples for subsystems, the two commutation rules, strict orientation of single rules is possible by the definitions). -/
theorem paper_prop_4_5_AB : ¬ BarrierFor rulesAB := not_barrier_AB
theorem paper_prop_4_5_DA : ¬ BarrierFor rulesDA := not_barrier_DA
theorem paper_prop_4_5_DP_A : ¬ BarrierDPFor lettersPB usableA pairsPB := not_barrierDP_A
theorem paper_prop_4_5_DPrev_A : ¬ BarrierDPFor lettersPDrev usableArev pairsPDrev :=
  not_barrierDPrev_A
theorem paper_prop_4_5_BZ_A : ¬ BarrierBZFor lettersPB usableA pairsPB := not_barrierBZ_A
theorem paper_prop_4_5_BZrev_A : ¬ BarrierBZFor lettersPDrev usableArev pairsPDrev :=
  not_barrierBZrev_A
theorem paper_prop_4_5_DPrev_one : ¬ BarrierDPFor lettersPDrev usableSTrev
    [⟨[DLetter.mark Letter.rgt, DLetter.plain Letter.f], [DLetter.mark Letter.rgt]⟩] :=
  not_barrierDPrev_one
theorem paper_prop_4_5_swap {d : ℕ} (hd : 0 < d) (I : Interp d) (hfin : Fin00 hd I)
    (a b : Letter) : ¬ Strict I ⟨[a, b], [b, a]⟩ := not_strict_swap hd I hfin a b
theorem paper_prop_4_5_strict_ST : ∀ ρ ∈ rulesST,
    ρ ≠ ⟨[Letter.f, Letter.d0], [Letter.d0, Letter.f]⟩ →
    ρ ≠ ⟨[Letter.t, Letter.d2], [Letter.d2, Letter.t]⟩ →
      ∃ I : Interp 1, Fin00 Nat.one_pos I ∧ Strict I ρ := strict_possible_ST
theorem paper_prop_4_5_strict_DP : ∀ π ∈ pairsPB, ∃ J : DLetter → AffFun Arc 1,
    SomewhereFinite Nat.one_pos J lettersPB ∧ StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) :=
  strict_possible_DP
theorem paper_prop_4_5_strict_DPrev : ∀ π ∈ pairsPDrev, ∃ J : DLetter → AffFun Arc 1,
    SomewhereFinite Nat.one_pos J lettersPDrev ∧
      StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := strict_possible_DPrev
theorem paper_prop_4_5_strict_BZ : ∀ π ∈ pairsPB, ∃ J : DLetter → AffFun ArcZ 1,
    AbsPositive Nat.one_pos J lettersPB ∧ StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) :=
  strict_possible_BZ
theorem paper_prop_4_5_strict_BZrev : ∀ π ∈ pairsPDrev, ∃ J : DLetter → AffFun ArcZ 1,
    AbsPositive Nat.one_pos J lettersPDrev ∧
      StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := strict_possible_BZrev

/-- **Proposition 4.5** ($\mathcal H$). -/
theorem paper_prop_4_5_H_AB : ¬ BarrierFor (HTPDB.rulesHT.drop 2) :=
  HTPDB.NonVacuityH.not_barrier_HT_AB
theorem paper_prop_4_5_H_DA : ¬ BarrierFor HTPDB.NonVacuityH.rulesDAH :=
  HTPDB.NonVacuityH.not_barrier_DAH
theorem paper_prop_4_5_H_DP_A : ¬ BarrierDPFor lettersPB (HTPDB.usableHT.drop 2) pairsPB :=
  HTPDB.NonVacuityH.not_barrierHDP_A
theorem paper_prop_4_5_H_BZ_A : ¬ BarrierBZFor lettersPB (HTPDB.usableHT.drop 2) pairsPB :=
  HTPDB.NonVacuityH.not_barrierHBZ_A
theorem paper_prop_4_5_H_DPrev_A : ¬ BarrierDPFor lettersPDrev usableArev HTPDB.pairsPDrevH :=
  HTPDB.NonVacuityH.not_barrierHDPrev_A
theorem paper_prop_4_5_H_BZrev_A : ¬ BarrierBZFor lettersPDrev usableArev HTPDB.pairsPDrevH :=
  HTPDB.NonVacuityH.not_barrierHBZrev_A
theorem paper_prop_4_5_H_strict : ∀ ρ ∈ HTPDB.rulesHT,
    (∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧ Strict I ρ) ↔
      (ρ ≠ ⟨[Letter.f, Letter.d0], [Letter.d0, Letter.f]⟩ ∧
        ρ ≠ ⟨[Letter.t, Letter.d2], [Letter.d2, Letter.t]⟩) :=
  HTPDB.NonVacuityH.strict_possible_iff_HT
theorem paper_prop_4_5_H_strict_DP : ∀ π ∈ pairsPB, ∃ J : DLetter → AffFun Arc 1,
    SomewhereFinite Nat.one_pos J lettersPB ∧ StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) :=
  HTPDB.NonVacuityH.strict_possible_HDP
theorem paper_prop_4_5_H_strict_DPrev : ∀ π ∈ HTPDB.pairsPDrevH, ∃ J : DLetter → AffFun Arc 1,
    SomewhereFinite Nat.one_pos J lettersPDrev ∧
      StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := HTPDB.NonVacuityH.strict_possible_HDPrev
theorem paper_prop_4_5_H_strict_BZ : ∀ π ∈ pairsPB, ∃ J : DLetter → AffFun ArcZ 1,
    AbsPositive Nat.one_pos J lettersPB ∧ StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) :=
  HTPDB.NonVacuityH.strict_possible_HBZ
theorem paper_prop_4_5_H_strict_BZrev : ∀ π ∈ HTPDB.pairsPDrevH, ∃ J : DLetter → AffFun ArcZ 1,
    AbsPositive Nat.one_pos J lettersPDrev ∧
      StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := HTPDB.NonVacuityH.strict_possible_HBZrev

/-- **Proposition 4.5** ($R_H$). -/
theorem paper_prop_4_5_RH_noDyn : ¬ BarrierFor (RH.usedRH.take 8) :=
  RH.NonVacuityRH.not_barrier_noDyn
theorem paper_prop_4_5_RH_X : ¬ BarrierFor (RH.rulesRH.take 10) := RH.NonVacuityRH.not_barrier_X
theorem paper_prop_4_5_RH_noLeft : ¬ BarrierFor RH.NonVacuityRH.usedDA :=
  RH.NonVacuityRH.not_barrier_noLeft
theorem paper_prop_4_5_RH_strict : ∀ ρ ∈ RH.rulesRH,
    (∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧ Strict I ρ) ↔
      (ρ ≠ ⟨[Letter.f, Letter.d0], [Letter.d0, Letter.f]⟩ ∧
        ρ ≠ ⟨[Letter.t, Letter.d2], [Letter.d2, Letter.t]⟩) :=
  RH.NonVacuityRH.strict_possible_iff_RH

end Boundary

/-- **Proposition 4.6** (the form without the conditions on `f` and `t` follows from Collatz reachability; also the contrapositives). -/
theorem paper_prop_4_6 : CollatzReachT → ArcticBarrierDPmin := dw_barrier_DPmin_of_reach
theorem paper_prop_4_6_rev : CollatzReachT → ArcticBarrierDPrevmin := dw_barrier_DPrevmin_of_reach
theorem paper_prop_4_6_contra : ¬ ArcticBarrierDPmin → ¬ CollatzReachT :=
  dw_not_reach_of_not_DPmin
theorem paper_prop_4_6_rev_contra : ¬ ArcticBarrierDPrevmin → ¬ CollatzReachT :=
  dw_not_reach_of_not_DPrevmin

end Collatz.Arctic.Paper
