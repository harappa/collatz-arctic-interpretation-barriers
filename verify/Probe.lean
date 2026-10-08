import CollatzProof.Arctic.Paper

/-!
# Statements and axioms of the results cited in the paper

Run from the root of the release after `lake build`:

    lake env lean verify/Probe.lean

This file is not part of any library. It prints the frozen statements of the main theorems and the definitions they
use (Appendix A of the paper), for arctic interpretations (Theorems 3.1, 3.3 and 3.4) and for natural-number matrix
interpretations (Theorem 9.2), the other frozen definitions, the statements of argument filters, the definitions used
by Proposition 9.5, by the value automata of Sections 10-12 and by Corollary 10.12, and the axioms of `NatQ5.allBarriers_final` (the six
statements of Theorem 9.2 together). Then, for every theorem `paper_*` of the module `CollatzProof.Arctic.Paper` (the
results of the paper under their numbers, with names `paper_<kind>_<section>_<number>[_<target>]`; files
`Paper.lean`, ..., `Paper5.lean`), it prints the statement and the axioms on which it depends. Every `#print axioms`
below should report `[propext, Classical.choice, Quot.sound]` or a subset of these three. The script
`verify/check_axioms.py` checks this mechanically on the output of this file:

    lake env lean verify/Probe.lean > probe.txt && python3 verify/check_axioms.py probe.txt
-/

/-! ## Frozen statements of the main theorems for arctic interpretations (Theorems 3.1, 3.3 and 3.4) -/

#print Collatz.Arctic.ArcticBarrierST
#print Collatz.Arctic.HTPDB.ArcticBarrierHT
#print Collatz.Arctic.RH.ArcticBarrierRH
#print Collatz.Arctic.RH.ArcticBarrierRHSub
#print Collatz.Arctic.NonVacuity.BarrierFor
#print Collatz.Arctic.ArcticBarrierDP
#print Collatz.Arctic.ArcticBarrierDPrev
#print Collatz.Arctic.HTPDB.ArcticBarrierHDP
#print Collatz.Arctic.HTPDB.ArcticBarrierHDPrev
#print Collatz.Arctic.ArcticBarrierBZ
#print Collatz.Arctic.ArcticBarrierBZrev
#print Collatz.Arctic.HTPDB.ArcticBarrierHBZ
#print Collatz.Arctic.HTPDB.ArcticBarrierHBZrev

/-! ## Definitions used by these statements -/

#print Collatz.Arctic.ev
#print Collatz.Arctic.Weak
#print Collatz.Arctic.Strict
#print Collatz.Arctic.Fin00
#print Collatz.Arctic.rulesST
#print Collatz.Arctic.HTPDB.rulesHT
#print Collatz.Arctic.RH.rulesRH
#print Collatz.Arctic.RH.usedRH
#print Collatz.Arctic.NonVacuity.revRule
#print Collatz.Arctic.NonVacuity.rulesSTrev
#print Collatz.Arctic.HTPDB.NonVacuityH.rulesHTrev
#print Collatz.Arctic.evA
#print Collatz.Arctic.WeakA
#print Collatz.Arctic.WeakTop
#print Collatz.Arctic.StrictTop
#print Collatz.Arctic.SomewhereFinite
#print Collatz.Arctic.AbsPositive
#print Collatz.Arctic.pairsPB
#print Collatz.Arctic.usableST
#print Collatz.Arctic.lettersPB
#print Collatz.Arctic.pairsPDrev
#print Collatz.Arctic.usableSTrev
#print Collatz.Arctic.lettersPDrev
#print Collatz.Arctic.HTPDB.usableHT
#print Collatz.Arctic.HTPDB.pairsPDrevH
#print Collatz.Arctic.HTPDB.usableHTrev

/-! ## Definitions used by Corollary 3.8 and Proposition 4.8 (arctic linear functions with absolute parts) -/

#print Collatz.Arctic.AffFun
#print Collatz.Arctic.Affine.evL
#print Collatz.Arctic.Affine.PWeak
#print Collatz.Arctic.Affine.PStrict
#print Collatz.Arctic.GG
#print Collatz.Arctic.Affine.SomeFin
#print Collatz.Arctic.Affine.AffBarrierFin
#print Collatz.Arctic.Affine.SomeFinOrientable
#print Collatz.Arctic.Affine.leftST

/-! ## Definitions used by Proposition 9.5 (natural-number affine interpretations, the conventions of Paper II) -/

#print Collatz.Arctic.NatExample.NAff
#print Collatz.Arctic.NatExample.NAff.app
#print Collatz.Arctic.NatExample.NAff.comp
#print Collatz.Arctic.NatExample.NAff.id
#print Collatz.Arctic.NatExample.evN
#check @Collatz.Arctic.NatExample.evN_app   -- `evN` is the composition of the maps of the letters
#print Collatz.Arctic.NatExample.NWeak
#print Collatz.Arctic.NatExample.NStrict
#print Collatz.Arctic.NatExample.PhiN
#print Collatz.Arctic.NatExample.resIdx
#print Collatz.Arctic.NatExample.matB
#print Collatz.Arctic.NatExample.matD
#print Collatz.Arctic.NatExample.matL
#print Collatz.Arctic.NatExample.matR
#print Collatz.Arctic.NatExample.vecR
#print Collatz.Arctic.NatExample.interp
#print Collatz.Arctic.NatExample.IT
#print Collatz.Arctic.NatExample.IH
#print Collatz.Arctic.NatExample.IRH
#print Collatz.Arctic.NatExample.resPart
#print Collatz.Arctic.NatExample.digitL
#print Collatz.Arctic.NatExample.resProd
#print Collatz.Arctic.NatExample.ResidueComponent
#print Collatz.Arctic.NatExample.phiI
#print Collatz.Arctic.binTail
#print Collatz.Arctic.can
#print Collatz.Arctic.T
#print Collatz.Arctic.RH.canRH
#print Collatz.Arctic.HModel.Hmap
#print Collatz.Arctic.HModel.HDom

/-! ## Frozen statements of Theorem 9.2 (natural-number matrix interpretations; `Nat/Statement.lean`, `Nat/StatementRev.lean`, `Nat/StatementDP.lean`) -/

#print Collatz.Arctic.NatQ5.NatBarrierST
#print Collatz.Arctic.NatQ5.NatBarrierSTrev
#print Collatz.Arctic.NatQ5.NatBarrierSTB
#print Collatz.Arctic.NatQ5.NatBarrierSTrevTop
#print Collatz.Arctic.NatQ5.NatBarrierDP
#print Collatz.Arctic.NatQ5.NatBarrierDPrev

#check @Collatz.Arctic.NatQ5.allBarriers_final   -- the six statements together
#print axioms Collatz.Arctic.NatQ5.allBarriers_final

/-! ## Definitions used by these statements (frozen) -/

#print Collatz.Arctic.NatQ5.NAff
#print Collatz.Arctic.NatQ5.NAff.app
#print Collatz.Arctic.NatQ5.NAff.comp
#print Collatz.Arctic.NatQ5.NAff.id
#print Collatz.Arctic.NatQ5.evN
#print Collatz.Arctic.NatQ5.NWeak
#print Collatz.Arctic.NatQ5.NStrict
#print Collatz.Arctic.NatQ5.NMono
#print Collatz.Arctic.NatQ5.PhiN
#print Collatz.Arctic.NatQ5.rulesSTB
#print Collatz.Arctic.NatQ5.rulesSTrev
#print Collatz.Arctic.NatQ5.rulesSTrevTop
#print Collatz.Arctic.NatQ5.evND
#print Collatz.Arctic.NatQ5.NWeakD
#print Collatz.Arctic.NatQ5.NWeakTopD
#print Collatz.Arctic.NatQ5.NStrictTopD
#print Collatz.Arctic.DLetter
#print Collatz.Arctic.DRule
#print Collatz.Arctic.Rule.plain

/-! ## The other frozen statements of these files: the forms for the used rules (equivalent to `NatBarrierST` and `NatBarrierSTrev`) and the value-level statements -/

#print Collatz.Arctic.NatQ5.UsedST
#print Collatz.Arctic.NatQ5.NatBarrierSTUsed
#print Collatz.Arctic.NatQ5.canDerivRev
#print Collatz.Arctic.NatQ5.UsedSTrev
#print Collatz.Arctic.NatQ5.NatBarrierSTrevUsed
#print Collatz.Arctic.NatQ5.NatValueCore
#print Collatz.Arctic.NatQ5.NatValueCore'
#print Collatz.Arctic.canDeriv
#print Collatz.Arctic.uses
#print Collatz.Arctic.usesOrbit

/-! ## The frozen decomposition data (Definition 12.9 and Proposition 12.11; `Nat/W3Decomp.lean`) -/

#print Collatz.Arctic.NatQ5.W3c.DecompStmt
#print Collatz.Arctic.NatQ5.W3c.DecompData
#print Collatz.Arctic.NatQ5.W3c.topW
#print Collatz.Arctic.NatQ5.W3c.tailW
#print Collatz.Arctic.NatQ5.W3c.fullW
#print Collatz.Arctic.NatQ5.W3c.posT
#print Collatz.Arctic.NatQ5.W3c.Adm
#print Collatz.Arctic.NatQ5.W3c.admSet
#print Collatz.Arctic.NatQ5.W3c.ind
#print Collatz.Arctic.NatQ5.W3c.xiOf
#print Collatz.Arctic.NatQ5.W3c.termOf
#print Collatz.Arctic.NatQ5.W3c.Sharp
#print Collatz.Arctic.NatQ5.W3c.ZIdx
#print Collatz.Arctic.NatQ5.W3c.muZ
#print Collatz.Arctic.NatQ5.IsComp
#print Collatz.Arctic.NatQ5.ZeroOne

/-! ## Definitions used by Theorems 10.10 and 10.11 (value automata) and Corollary 10.12 (`Nat/HWCorner.lean`); not frozen -/

#print Collatz.Arctic.NatQ5.ValAuto
#print Collatz.Arctic.NatQ5.aval
#print Collatz.Arctic.NatQ5.binWord
#print Collatz.Arctic.NatQ5.AutoMono
#print Collatz.Arctic.NatQ5.AutoMono3
#print Collatz.Arctic.NatQ5.H2Prod
#print Collatz.Arctic.NatQ5.lift
#print Collatz.Arctic.NatQ5.PcT
#print Collatz.Arctic.NatQ5.liftT
#print Collatz.Arctic.NatQ5.W3CoreStmt
#print Collatz.Arctic.NatQ5.AutoValueCoreNoG2
#print Collatz.Arctic.NatQ5.NW
#print Collatz.Arctic.NatQ5.GWeak
#print Collatz.Arctic.NatQ5.GenValueCore
#print Collatz.Arctic.NatQ5.HW.HWBarrierST
#print Collatz.Arctic.NatQ5.HW.HWBarrierSTrev

/-! ## Argument filters (the remark after Theorem 3.4 and Proposition 13.4; `DPFilterStatement.lean`, `Nat/BridgeDPFilter.lean`) -/

#print Collatz.Arctic.DPFilter.ArcticBarrierDPFilt
#print Collatz.Arctic.DPFilter.ArcticBarrierDPrevFilt
#print Collatz.Arctic.DPFilter.ArcticBarrierBZFilt
#print Collatz.Arctic.DPFilter.ArcticBarrierBZrevFilt
#print Collatz.Arctic.DPFilter.ArcticBarrierHDPFilt
#print Collatz.Arctic.DPFilter.ArcticBarrierHDPrevFilt
#print Collatz.Arctic.DPFilter.ArcticBarrierHBZFilt
#print Collatz.Arctic.DPFilter.ArcticBarrierHBZrevFilt
#print Collatz.Arctic.DPFilter.FirstNonneg
#print Collatz.Arctic.DPFilter.BZPos
#print Collatz.Arctic.DPFilter.ArcticBarrierBZFiltW
#print Collatz.Arctic.DPFilter.ArcticBarrierBZrevFiltW
#print Collatz.Arctic.DPFilter.ArcticBarrierHBZFiltW
#print Collatz.Arctic.DPFilter.ArcticBarrierHBZrevFiltW
#print Collatz.Arctic.NatQ5.W5.usableFilt   -- not frozen (`Nat/BridgeDPFilter.lean`); with the auxiliary definitions below
#print Collatz.Arctic.NatQ5.W5.usableWith
#print Collatz.Arctic.NatQ5.W5.regPrefix
#print Collatz.Arctic.NatQ5.W5.dpTail
#print Collatz.Arctic.NatQ5.W5.filtStep
#print Collatz.Arctic.NatQ5.W5.filtIter
-- `DPFilterStatement.lean` also uses `NatQ5.rulesSTrev` (frozen) and `HTPDB.NonVacuityH.rulesHTrev` (not frozen), both printed above
#print Collatz.Arctic.NatQ5.NatBarrierDPFilt
#print Collatz.Arctic.NatQ5.NatBarrierDPrevFilt

/-! ## Zantema's system and the printed form of [YAH, Theorem 3.10] (Proposition 9.4 (iii) and the remark in Section 13.2) -/

#print Collatz.Arctic.NatQ5.W5.ZYah.ZL
#print Collatz.Arctic.NatQ5.W5.ZYah.evZ
#print Collatz.Arctic.NatQ5.W5.ZYah.ZW
#print Collatz.Arctic.NatQ5.W5.ZYah.ZS
#print Collatz.Arctic.NatQ5.W5.ZYah.rulesZ
#print Collatz.Arctic.NatQ5.W5.ZYah.IZ
#print Collatz.Arctic.NatQ5.W5.ZYah.rulesZrev
#print Collatz.Arctic.NatQ5.W5.ZYah.IZr
#print Collatz.Arctic.NatQ5.W5.LiteralDP
#print Collatz.Arctic.NatQ5.W5.LiteralDPrev

/-! ## Section 2: Preliminaries -/

#check @Collatz.Arctic.Paper.paper_lem_2_3_T
#print axioms Collatz.Arctic.Paper.paper_lem_2_3_T

#check @Collatz.Arctic.Paper.paper_lem_2_3_H
#print axioms Collatz.Arctic.Paper.paper_lem_2_3_H

#check @Collatz.Arctic.Paper.paper_lem_2_3_RH
#print axioms Collatz.Arctic.Paper.paper_lem_2_3_RH

/-! ## Section 3: Main results for arctic interpretations -/

#check @Collatz.Arctic.Paper.paper_thm_3_1_T
#print axioms Collatz.Arctic.Paper.paper_thm_3_1_T

#check @Collatz.Arctic.Paper.paper_thm_3_1_H
#print axioms Collatz.Arctic.Paper.paper_thm_3_1_H

#check @Collatz.Arctic.Paper.paper_thm_3_1_RH
#print axioms Collatz.Arctic.Paper.paper_thm_3_1_RH

#check @Collatz.Arctic.Paper.paper_thm_3_1_RHsub
#print axioms Collatz.Arctic.Paper.paper_thm_3_1_RHsub

#check @Collatz.Arctic.Paper.paper_thm_3_1_Trev
#print axioms Collatz.Arctic.Paper.paper_thm_3_1_Trev

#check @Collatz.Arctic.Paper.paper_thm_3_1_Hrev
#print axioms Collatz.Arctic.Paper.paper_thm_3_1_Hrev

#check @Collatz.Arctic.Paper.paper_thm_3_1_RHrev
#print axioms Collatz.Arctic.Paper.paper_thm_3_1_RHrev

#check @Collatz.Arctic.Paper.paper_thm_3_3_T
#print axioms Collatz.Arctic.Paper.paper_thm_3_3_T

#check @Collatz.Arctic.Paper.paper_thm_3_3_Trev
#print axioms Collatz.Arctic.Paper.paper_thm_3_3_Trev

#check @Collatz.Arctic.Paper.paper_thm_3_3_H
#print axioms Collatz.Arctic.Paper.paper_thm_3_3_H

#check @Collatz.Arctic.Paper.paper_thm_3_3_Hrev
#print axioms Collatz.Arctic.Paper.paper_thm_3_3_Hrev

#check @Collatz.Arctic.Paper.paper_thm_3_4_T
#print axioms Collatz.Arctic.Paper.paper_thm_3_4_T

#check @Collatz.Arctic.Paper.paper_thm_3_4_Trev
#print axioms Collatz.Arctic.Paper.paper_thm_3_4_Trev

#check @Collatz.Arctic.Paper.paper_thm_3_4_H
#print axioms Collatz.Arctic.Paper.paper_thm_3_4_H

#check @Collatz.Arctic.Paper.paper_thm_3_4_Hrev
#print axioms Collatz.Arctic.Paper.paper_thm_3_4_Hrev

#check @Collatz.Arctic.Paper.paper_thm_3_6_T
#print axioms Collatz.Arctic.Paper.paper_thm_3_6_T

#check @Collatz.Arctic.Paper.paper_thm_3_6_H
#print axioms Collatz.Arctic.Paper.paper_thm_3_6_H

#check @Collatz.Arctic.Paper.paper_thm_3_6_T_Z
#print axioms Collatz.Arctic.Paper.paper_thm_3_6_T_Z

#check @Collatz.Arctic.Paper.paper_thm_3_6_H_Z
#print axioms Collatz.Arctic.Paper.paper_thm_3_6_H_Z

#check @Collatz.Arctic.Paper.paper_thm_3_6_T_Zlsb
#print axioms Collatz.Arctic.Paper.paper_thm_3_6_T_Zlsb

#check @Collatz.Arctic.Paper.paper_thm_3_6_H_Zlsb
#print axioms Collatz.Arctic.Paper.paper_thm_3_6_H_Zlsb

#check @Collatz.Arctic.Paper.paper_prop_3_7_T
#print axioms Collatz.Arctic.Paper.paper_prop_3_7_T

#check @Collatz.Arctic.Paper.paper_prop_3_7_H
#print axioms Collatz.Arctic.Paper.paper_prop_3_7_H

#check @Collatz.Arctic.Paper.paper_cor_3_8_T
#print axioms Collatz.Arctic.Paper.paper_cor_3_8_T

#check @Collatz.Arctic.Paper.paper_cor_3_8_Trev
#print axioms Collatz.Arctic.Paper.paper_cor_3_8_Trev

#check @Collatz.Arctic.Paper.paper_cor_3_8_H
#print axioms Collatz.Arctic.Paper.paper_cor_3_8_H

#check @Collatz.Arctic.Paper.paper_cor_3_8_Hrev
#print axioms Collatz.Arctic.Paper.paper_cor_3_8_Hrev

#check @Collatz.Arctic.Paper.paper_cor_3_8_RH
#print axioms Collatz.Arctic.Paper.paper_cor_3_8_RH

/-! ### The remark on argument filters after Theorem 3.4 -/

#check @Collatz.Arctic.Paper.paper_rem_3_4_filt
#print axioms Collatz.Arctic.Paper.paper_rem_3_4_filt

#check @Collatz.Arctic.Paper.paper_rem_3_4_filtW
#print axioms Collatz.Arctic.Paper.paper_rem_3_4_filtW

#check @Collatz.Arctic.Paper.paper_rem_3_4_bzpos_T
#print axioms Collatz.Arctic.Paper.paper_rem_3_4_bzpos_T

#check @Collatz.Arctic.Paper.paper_rem_3_4_bzpos_Trev
#print axioms Collatz.Arctic.Paper.paper_rem_3_4_bzpos_Trev

/-! ## Section 4: The boundary of the barrier -/

#check @Collatz.Arctic.Paper.paper_prop_4_1_DPw
#print axioms Collatz.Arctic.Paper.paper_prop_4_1_DPw

#check @Collatz.Arctic.Paper.paper_prop_4_1_DPrevw
#print axioms Collatz.Arctic.Paper.paper_prop_4_1_DPrevw

#check @Collatz.Arctic.Paper.paper_prop_4_1_BZf
#print axioms Collatz.Arctic.Paper.paper_prop_4_1_BZf

#check @Collatz.Arctic.Paper.paper_prop_4_1_BZrevf
#print axioms Collatz.Arctic.Paper.paper_prop_4_1_BZrevf

#check @Collatz.Arctic.Paper.paper_prop_4_1_BZw
#print axioms Collatz.Arctic.Paper.paper_prop_4_1_BZw

#check @Collatz.Arctic.Paper.paper_prop_4_1_BZrevw
#print axioms Collatz.Arctic.Paper.paper_prop_4_1_BZrevw

#check @Collatz.Arctic.Paper.paper_prop_4_2_markOnly
#print axioms Collatz.Arctic.Paper.paper_prop_4_2_markOnly

#check @Collatz.Arctic.Paper.paper_prop_4_2_markOnly_rev
#print axioms Collatz.Arctic.Paper.paper_prop_4_2_markOnly_rev

#check @Collatz.Arctic.Paper.paper_prop_4_2_noMark
#print axioms Collatz.Arctic.Paper.paper_prop_4_2_noMark

#check @Collatz.Arctic.Paper.paper_prop_4_2_noMark_rev
#print axioms Collatz.Arctic.Paper.paper_prop_4_2_noMark_rev

#check @Collatz.Arctic.Paper.paper_prop_4_2_noMark_BZ
#print axioms Collatz.Arctic.Paper.paper_prop_4_2_noMark_BZ

#check @Collatz.Arctic.Paper.paper_prop_4_2_noMark_BZrev
#print axioms Collatz.Arctic.Paper.paper_prop_4_2_noMark_BZrev

#check @Collatz.Arctic.Paper.paper_prop_4_3
#print axioms Collatz.Arctic.Paper.paper_prop_4_3

#check @Collatz.Arctic.Paper.paper_prop_4_3_l0
#print axioms Collatz.Arctic.Paper.paper_prop_4_3_l0

#check @Collatz.Arctic.Paper.paper_prop_4_3_lf
#print axioms Collatz.Arctic.Paper.paper_prop_4_3_lf

#check @Collatz.Arctic.Paper.paper_prop_4_5_AB
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_AB

#check @Collatz.Arctic.Paper.paper_prop_4_5_DA
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_DA

#check @Collatz.Arctic.Paper.paper_prop_4_5_DP_A
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_DP_A

#check @Collatz.Arctic.Paper.paper_prop_4_5_DPrev_A
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_DPrev_A

#check @Collatz.Arctic.Paper.paper_prop_4_5_BZ_A
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_BZ_A

#check @Collatz.Arctic.Paper.paper_prop_4_5_BZrev_A
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_BZrev_A

#check @Collatz.Arctic.Paper.paper_prop_4_5_DPrev_one
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_DPrev_one

#check @Collatz.Arctic.Paper.paper_prop_4_5_swap
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_swap

#check @Collatz.Arctic.Paper.paper_prop_4_5_strict_ST
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_strict_ST

#check @Collatz.Arctic.Paper.paper_prop_4_5_strict_DP
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_strict_DP

#check @Collatz.Arctic.Paper.paper_prop_4_5_strict_DPrev
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_strict_DPrev

#check @Collatz.Arctic.Paper.paper_prop_4_5_strict_BZ
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_strict_BZ

#check @Collatz.Arctic.Paper.paper_prop_4_5_strict_BZrev
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_strict_BZrev

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_AB
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_AB

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_DA
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_DA

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_DP_A
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_DP_A

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_BZ_A
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_BZ_A

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_DPrev_A
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_DPrev_A

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_BZrev_A
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_BZrev_A

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_strict
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_strict

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_strict_DP
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_strict_DP

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_strict_DPrev
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_strict_DPrev

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_strict_BZ
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_strict_BZ

#check @Collatz.Arctic.Paper.paper_prop_4_5_H_strict_BZrev
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_H_strict_BZrev

#check @Collatz.Arctic.Paper.paper_prop_4_5_RH_noDyn
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_RH_noDyn

#check @Collatz.Arctic.Paper.paper_prop_4_5_RH_X
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_RH_X

#check @Collatz.Arctic.Paper.paper_prop_4_5_RH_noLeft
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_RH_noLeft

#check @Collatz.Arctic.Paper.paper_prop_4_5_RH_strict
#print axioms Collatz.Arctic.Paper.paper_prop_4_5_RH_strict

#check @Collatz.Arctic.Paper.paper_prop_4_6
#print axioms Collatz.Arctic.Paper.paper_prop_4_6

#check @Collatz.Arctic.Paper.paper_prop_4_6_rev
#print axioms Collatz.Arctic.Paper.paper_prop_4_6_rev

#check @Collatz.Arctic.Paper.paper_prop_4_6_contra
#print axioms Collatz.Arctic.Paper.paper_prop_4_6_contra

#check @Collatz.Arctic.Paper.paper_prop_4_6_rev_contra
#print axioms Collatz.Arctic.Paper.paper_prop_4_6_rev_contra

#check @Collatz.Arctic.Paper.paper_prop_4_8_T
#print axioms Collatz.Arctic.Paper.paper_prop_4_8_T

#check @Collatz.Arctic.Paper.paper_prop_4_8_H
#print axioms Collatz.Arctic.Paper.paper_prop_4_8_H

/-! ## Section 5: From rewriting to values -/

#check @Collatz.Arctic.Paper.paper_lem_5_1_weak
#print axioms Collatz.Arctic.Paper.paper_lem_5_1_weak

#check @Collatz.Arctic.Paper.paper_lem_5_1_strict
#print axioms Collatz.Arctic.Paper.paper_lem_5_1_strict

#check @Collatz.Arctic.Paper.paper_thm_5_5_T
#print axioms Collatz.Arctic.Paper.paper_thm_5_5_T

#check @Collatz.Arctic.Paper.paper_thm_5_5_H
#print axioms Collatz.Arctic.Paper.paper_thm_5_5_H

#check @Collatz.Arctic.Paper.paper_lem_5_6
#print axioms Collatz.Arctic.Paper.paper_lem_5_6

#check @Collatz.Arctic.Paper.paper_lem_5_6_Z
#print axioms Collatz.Arctic.Paper.paper_lem_5_6_Z

#check @Collatz.Arctic.Paper.paper_lem_5_6_family
#print axioms Collatz.Arctic.Paper.paper_lem_5_6_family

#check @Collatz.Arctic.Paper.paper_lem_5_6_familyZ
#print axioms Collatz.Arctic.Paper.paper_lem_5_6_familyZ

/-! ## Section 6: The value-level core -/

#check @Collatz.Arctic.Paper.paper_lem_6_2
#print axioms Collatz.Arctic.Paper.paper_lem_6_2

#check @Collatz.Arctic.Paper.paper_lem_6_2_exists
#print axioms Collatz.Arctic.Paper.paper_lem_6_2_exists

#check @Collatz.Arctic.Paper.paper_lem_6_3
#print axioms Collatz.Arctic.Paper.paper_lem_6_3

#check @Collatz.Arctic.Paper.paper_lem_6_3_stay
#print axioms Collatz.Arctic.Paper.paper_lem_6_3_stay

#check @Collatz.Arctic.Paper.paper_lem_6_5
#print axioms Collatz.Arctic.Paper.paper_lem_6_5

#check @Collatz.Arctic.Paper.paper_lem_6_6
#print axioms Collatz.Arctic.Paper.paper_lem_6_6

#check @Collatz.Arctic.Paper.paper_prop_6_7_left
#print axioms Collatz.Arctic.Paper.paper_prop_6_7_left

#check @Collatz.Arctic.Paper.paper_thm_6_8
#print axioms Collatz.Arctic.Paper.paper_thm_6_8

/-! ## Section 7: Transfer to H and R_H -/

#check @Collatz.Arctic.Paper.paper_lem_7_4
#print axioms Collatz.Arctic.Paper.paper_lem_7_4

#check @Collatz.Arctic.Paper.paper_lem_7_4_count
#print axioms Collatz.Arctic.Paper.paper_lem_7_4_count

#check @Collatz.Arctic.Paper.paper_prop_7_5
#print axioms Collatz.Arctic.Paper.paper_prop_7_5

/-! ## Section 8: Transformations before arctic reduction pairs -/

#check @Collatz.Arctic.Paper.paper_cor_8_1
#print axioms Collatz.Arctic.Paper.paper_cor_8_1

/-! ## Section 9: Natural-number matrix interpretations (Theorem 9.2, Proposition 9.4, Proposition 9.5 and the remark after it) -/

#check @Collatz.Arctic.Paper.paper_thm_9_2_T
#print axioms Collatz.Arctic.Paper.paper_thm_9_2_T

#check @Collatz.Arctic.Paper.paper_thm_9_2_Trev
#print axioms Collatz.Arctic.Paper.paper_thm_9_2_Trev

#check @Collatz.Arctic.Paper.paper_thm_9_2_B
#print axioms Collatz.Arctic.Paper.paper_thm_9_2_B

#check @Collatz.Arctic.Paper.paper_thm_9_2_revTop
#print axioms Collatz.Arctic.Paper.paper_thm_9_2_revTop

#check @Collatz.Arctic.Paper.paper_thm_9_2_DP
#print axioms Collatz.Arctic.Paper.paper_thm_9_2_DP

#check @Collatz.Arctic.Paper.paper_thm_9_2_DPrev
#print axioms Collatz.Arctic.Paper.paper_thm_9_2_DPrev

#check @Collatz.Arctic.Paper.paper_thm_9_2
#print axioms Collatz.Arctic.Paper.paper_thm_9_2

#check @Collatz.Arctic.Paper.paper_prop_9_4_drop
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_drop

#check @Collatz.Arctic.Paper.paper_prop_9_4_drop_rev
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_drop_rev

#check @Collatz.Arctic.Paper.paper_prop_9_4_noMono
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_noMono

#check @Collatz.Arctic.Paper.paper_prop_9_4_noMono_nonB
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_noMono_nonB

#check @Collatz.Arctic.Paper.paper_prop_9_4_noMono_rev
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_noMono_rev

#check @Collatz.Arctic.Paper.paper_prop_9_4_noMono_nonTop
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_noMono_nonTop

#check @Collatz.Arctic.Paper.paper_prop_9_4_pair
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_pair

#check @Collatz.Arctic.Paper.paper_prop_9_4_literal
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_literal

#check @Collatz.Arctic.Paper.paper_prop_9_4_literal_rev
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_literal_rev

#check @Collatz.Arctic.Paper.paper_prop_9_4_dropU
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_dropU

#check @Collatz.Arctic.Paper.paper_prop_9_4_dropU_rev
#print axioms Collatz.Arctic.Paper.paper_prop_9_4_dropU_rev

#check @Collatz.Arctic.Paper.paper_prop_9_5_T
#print axioms Collatz.Arctic.Paper.paper_prop_9_5_T

#check @Collatz.Arctic.Paper.paper_prop_9_5_H
#print axioms Collatz.Arctic.Paper.paper_prop_9_5_H

#check @Collatz.Arctic.Paper.paper_prop_9_5_RH
#print axioms Collatz.Arctic.Paper.paper_prop_9_5_RH

#check @Collatz.Arctic.Paper.paper_prop_9_5_remark
#print axioms Collatz.Arctic.Paper.paper_prop_9_5_remark

/-! ## Section 10: From rewriting to automata -/

#check @Collatz.Arctic.Paper.paper_lem_10_2_step
#print axioms Collatz.Arctic.Paper.paper_lem_10_2_step

#check @Collatz.Arctic.Paper.paper_lem_10_2_T
#print axioms Collatz.Arctic.Paper.paper_lem_10_2_T

#check @Collatz.Arctic.Paper.paper_lem_10_2_orbit
#print axioms Collatz.Arctic.Paper.paper_lem_10_2_orbit

#check @Collatz.Arctic.Paper.paper_lem_10_3
#print axioms Collatz.Arctic.Paper.paper_lem_10_3

#check @Collatz.Arctic.Paper.paper_lem_10_4
#print axioms Collatz.Arctic.Paper.paper_lem_10_4

#check @Collatz.Arctic.Paper.paper_lem_10_4_weak
#print axioms Collatz.Arctic.Paper.paper_lem_10_4_weak

#check @Collatz.Arctic.Paper.paper_lem_10_4_strict
#print axioms Collatz.Arctic.Paper.paper_lem_10_4_strict

#check @Collatz.Arctic.Paper.paper_lem_10_5_mono
#print axioms Collatz.Arctic.Paper.paper_lem_10_5_mono

#check @Collatz.Arctic.Paper.paper_lem_10_5_weak
#print axioms Collatz.Arctic.Paper.paper_lem_10_5_weak

#check @Collatz.Arctic.Paper.paper_lem_10_5_phi
#print axioms Collatz.Arctic.Paper.paper_lem_10_5_phi

#check @Collatz.Arctic.Paper.paper_lem_10_5_not_strict
#print axioms Collatz.Arctic.Paper.paper_lem_10_5_not_strict

#check @Collatz.Arctic.Paper.paper_lem_10_6
#print axioms Collatz.Arctic.Paper.paper_lem_10_6

#check @Collatz.Arctic.Paper.paper_lem_10_6_mono3
#print axioms Collatz.Arctic.Paper.paper_lem_10_6_mono3

#check @Collatz.Arctic.Paper.paper_lem_10_7
#print axioms Collatz.Arctic.Paper.paper_lem_10_7

#check @Collatz.Arctic.Paper.paper_thm_10_8
#print axioms Collatz.Arctic.Paper.paper_thm_10_8

#check @Collatz.Arctic.Paper.paper_thm_10_8_gdiag
#print axioms Collatz.Arctic.Paper.paper_thm_10_8_gdiag

#check @Collatz.Arctic.Paper.paper_cor_10_9
#print axioms Collatz.Arctic.Paper.paper_cor_10_9

#check @Collatz.Arctic.Paper.paper_cor_10_9_gen
#print axioms Collatz.Arctic.Paper.paper_cor_10_9_gen

#check @Collatz.Arctic.Paper.paper_cor_10_9_nat
#print axioms Collatz.Arctic.Paper.paper_cor_10_9_nat

#check @Collatz.Arctic.Paper.paper_thm_10_10
#print axioms Collatz.Arctic.Paper.paper_thm_10_10

#check @Collatz.Arctic.Paper.paper_thm_10_11
#print axioms Collatz.Arctic.Paper.paper_thm_10_11

#check @Collatz.Arctic.Paper.paper_thm_10_11_nat
#print axioms Collatz.Arctic.Paper.paper_thm_10_11_nat

#check @Collatz.Arctic.Paper.paper_thm_10_11_gen
#print axioms Collatz.Arctic.Paper.paper_thm_10_11_gen

#check @Collatz.Arctic.Paper.paper_cor_10_12
#print axioms Collatz.Arctic.Paper.paper_cor_10_12

#check @Collatz.Arctic.Paper.paper_cor_10_12_rev
#print axioms Collatz.Arctic.Paper.paper_cor_10_12_rev

/-! ## Section 11: Diagonal growth at most one -/

#check @Collatz.Arctic.Paper.paper_lem_11_1
#print axioms Collatz.Arctic.Paper.paper_lem_11_1

#check @Collatz.Arctic.Paper.paper_cor_11_2
#print axioms Collatz.Arctic.Paper.paper_cor_11_2

#check @Collatz.Arctic.Paper.paper_lem_11_3
#print axioms Collatz.Arctic.Paper.paper_lem_11_3

#check @Collatz.Arctic.Paper.paper_cor_11_4
#print axioms Collatz.Arctic.Paper.paper_cor_11_4

#check @Collatz.Arctic.Paper.paper_thm_11_8
#print axioms Collatz.Arctic.Paper.paper_thm_11_8

#check @Collatz.Arctic.Paper.paper_prop_11_12
#print axioms Collatz.Arctic.Paper.paper_prop_11_12

#check @Collatz.Arctic.Paper.paper_prop_11_13
#print axioms Collatz.Arctic.Paper.paper_prop_11_13

/-! ## Section 12: Values and uses on 0/1 automata -/

#check @Collatz.Arctic.Paper.paper_lem_12_3
#print axioms Collatz.Arctic.Paper.paper_lem_12_3

#check @Collatz.Arctic.Paper.paper_prop_12_11
#print axioms Collatz.Arctic.Paper.paper_prop_12_11

#check @Collatz.Arctic.Paper.paper_prop_12_11_T0
#print axioms Collatz.Arctic.Paper.paper_prop_12_11_T0

#check @Collatz.Arctic.Paper.paper_thm_12_13_mean
#print axioms Collatz.Arctic.Paper.paper_thm_12_13_mean

#check @Collatz.Arctic.Paper.paper_thm_12_13_win
#print axioms Collatz.Arctic.Paper.paper_thm_12_13_win

#check @Collatz.Arctic.Paper.paper_cor_12_18
#print axioms Collatz.Arctic.Paper.paper_cor_12_18

#check @Collatz.Arctic.Paper.paper_prop_12_19
#print axioms Collatz.Arctic.Paper.paper_prop_12_19

#check @Collatz.Arctic.Paper.paper_prop_12_24
#print axioms Collatz.Arctic.Paper.paper_prop_12_24

#check @Collatz.Arctic.Paper.paper_prop_12_26
#print axioms Collatz.Arctic.Paper.paper_prop_12_26

#check @Collatz.Arctic.Paper.paper_prop_12_27
#print axioms Collatz.Arctic.Paper.paper_prop_12_27

#check @Collatz.Arctic.Paper.paper_prop_12_28
#print axioms Collatz.Arctic.Paper.paper_prop_12_28

#check @Collatz.Arctic.Paper.paper_lem_12_30
#print axioms Collatz.Arctic.Paper.paper_lem_12_30

#check @Collatz.Arctic.Paper.paper_prop_12_31
#print axioms Collatz.Arctic.Paper.paper_prop_12_31

/-! ## Section 13: Reversal, top forms and dependency pairs -/

#check @Collatz.Arctic.Paper.paper_lem_13_1_rev
#print axioms Collatz.Arctic.Paper.paper_lem_13_1_rev

#check @Collatz.Arctic.Paper.paper_lem_13_1_top
#print axioms Collatz.Arctic.Paper.paper_lem_13_1_top

#check @Collatz.Arctic.Paper.paper_lem_13_1_revTop
#print axioms Collatz.Arctic.Paper.paper_lem_13_1_revTop

#check @Collatz.Arctic.Paper.paper_lem_13_2
#print axioms Collatz.Arctic.Paper.paper_lem_13_2

#check @Collatz.Arctic.Paper.paper_lem_13_2_rev
#print axioms Collatz.Arctic.Paper.paper_lem_13_2_rev

#check @Collatz.Arctic.Paper.paper_prop_13_3_full
#print axioms Collatz.Arctic.Paper.paper_prop_13_3_full

#check @Collatz.Arctic.Paper.paper_prop_13_3_full_rev
#print axioms Collatz.Arctic.Paper.paper_prop_13_3_full_rev

#check @Collatz.Arctic.Paper.paper_prop_13_3_scalar
#print axioms Collatz.Arctic.Paper.paper_prop_13_3_scalar

#check @Collatz.Arctic.Paper.paper_prop_13_3_scalar_rev
#print axioms Collatz.Arctic.Paper.paper_prop_13_3_scalar_rev

#check @Collatz.Arctic.Paper.paper_prop_13_3_row
#print axioms Collatz.Arctic.Paper.paper_prop_13_3_row

#check @Collatz.Arctic.Paper.paper_prop_13_3_row_rev
#print axioms Collatz.Arctic.Paper.paper_prop_13_3_row_rev

#check @Collatz.Arctic.Paper.paper_prop_13_4
#print axioms Collatz.Arctic.Paper.paper_prop_13_4

#check @Collatz.Arctic.Paper.paper_prop_13_4_rev
#print axioms Collatz.Arctic.Paper.paper_prop_13_4_rev

/-! ### The remark on the printed form of [YAH, Theorem 3.10] (Section 13.2) -/

#check @Collatz.Arctic.Paper.paper_rem_yah310_Z
#print axioms Collatz.Arctic.Paper.paper_rem_yah310_Z

#check @Collatz.Arctic.Paper.paper_rem_yah310_Zrev
#print axioms Collatz.Arctic.Paper.paper_rem_yah310_Zrev

#check @Collatz.Arctic.Paper.paper_rem_yah310_T
#print axioms Collatz.Arctic.Paper.paper_rem_yah310_T

#check @Collatz.Arctic.Paper.paper_rem_yah310_Trev
#print axioms Collatz.Arctic.Paper.paper_rem_yah310_Trev

/-! ## Appendix B: Probabilistic tools -/

#check @Collatz.Arctic.Paper.paper_thm_B_1
#print axioms Collatz.Arctic.Paper.paper_thm_B_1

#check @Collatz.Arctic.Paper.paper_thm_B_1_at
#print axioms Collatz.Arctic.Paper.paper_thm_B_1_at

#check @Collatz.Arctic.Paper.paper_prop_B_2
#print axioms Collatz.Arctic.Paper.paper_prop_B_2

#check @Collatz.Arctic.Paper.paper_thm_B_3
#print axioms Collatz.Arctic.Paper.paper_thm_B_3

#check @Collatz.Arctic.Paper.paper_thm_B_3_spr
#print axioms Collatz.Arctic.Paper.paper_thm_B_3_spr

#check @Collatz.Arctic.Paper.paper_cor_B_4
#print axioms Collatz.Arctic.Paper.paper_cor_B_4

#check @Collatz.Arctic.Paper.paper_thm_B_7
#print axioms Collatz.Arctic.Paper.paper_thm_B_7

#check @Collatz.Arctic.Paper.paper_thm_B_8
#print axioms Collatz.Arctic.Paper.paper_thm_B_8

#check @Collatz.Arctic.Paper.paper_thm_B_8_of_key
#print axioms Collatz.Arctic.Paper.paper_thm_B_8_of_key

#check @Collatz.Arctic.Paper.paper_prop_B_9
#print axioms Collatz.Arctic.Paper.paper_prop_B_9

/-! ## Appendix D: Rigidity of non-negative matrix families -/

#check @Collatz.Arctic.Paper.paper_lem_D_2
#print axioms Collatz.Arctic.Paper.paper_lem_D_2

#check @Collatz.Arctic.Paper.paper_lem_D_3
#print axioms Collatz.Arctic.Paper.paper_lem_D_3

#check @Collatz.Arctic.Paper.paper_lem_D_4
#print axioms Collatz.Arctic.Paper.paper_lem_D_4

#check @Collatz.Arctic.Paper.paper_lem_D_4_finite
#print axioms Collatz.Arctic.Paper.paper_lem_D_4_finite

#check @Collatz.Arctic.Paper.paper_prop_D_5
#print axioms Collatz.Arctic.Paper.paper_prop_D_5

#check @Collatz.Arctic.Paper.paper_lem_D_6
#print axioms Collatz.Arctic.Paper.paper_lem_D_6
