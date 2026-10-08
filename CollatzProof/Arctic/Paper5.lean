/-
Names following the numbering of the paper (the arctic barrier), part 5: Sections 9–13 (natural-number matrix
interpretations), Appendix D (rigidity of non-negative matrix families), and two unnumbered remarks: argument filters
after Theorem 3.4, and the printed form of [YAH, Theorem 3.10] in Section 13.2. Imported by the root module `Paper.lean`.

* Names have the form `paper_<kind>_<section>_<number>[_<target>]` (Appendix A of the paper); Appendix D uses `D` as the
  section, and unnumbered remarks use the kind `rem`: `paper_rem_3_4_*` (after Theorem 3.4) and `paper_rem_yah310_*`.
* All are aliases of existing theorems (`theorem paper_… : <existing statement> := <existing theorem>`); the types are
  copies of the existing statements, and Lean checks that they agree with the type of the right-hand side of `:=`.
  The frozen statements (`Nat/Statement.lean`, `Nat/StatementRev.lean`, `Nat/StatementDP.lean`, `Nat/W3Decomp.lean`) are
  used as they are.
* Combinations of existing theorems (one line each, no new proof):
  - `paper_thm_10_11`, `paper_thm_10_11_nat`, `paper_thm_10_11_gen` (Theorem 10.11): the value-level core
    `NatQ5.W4a.autoValueCore` passed through `NatQ5.autoValueCore_iff_noG2`, `NatQ5.natValueCore'_of_autoValueCore` and
    `NatQ5.genValueCore_of_autoValueCore`.
  - `paper_prop_13_3_*` (Proposition 13.3): the implications `NatQ5.natBarrierDP_full`, `NatQ5.natBarrierDPrev_full`,
    `NatQ5.W5.natBarrierDP_scalar`, `NatQ5.W5.natBarrierDPrev_scalar`, `NatQ5.W5.natBarrierDP_row` and
    `NatQ5.W5.natBarrierDPrev_row` applied to Theorem 9.2 (iii) (`NatQ5.natBarrierDP_final`,
    `NatQ5.natBarrierDPrev_final`).
  - `paper_prop_13_4`, `paper_prop_13_4_rev` (Proposition 13.4): `NatQ5.natBarrierDPFilt_of_DP` and
    `NatQ5.natBarrierDPrevFilt_of_DPrev` applied to the same two theorems.
* `paper_cor_10_12`, `paper_cor_10_12_rev` (Corollary 10.12, the corner form of [HW06]) are aliases of
  `NatQ5.HW.hwBarrierST` and `NatQ5.HW.hwBarrierSTrev` (`Nat/HWCorner.lean`), which apply
  `NatQ5.HW.hwBarrierST_of_genCore` to the term of `paper_thm_10_11_gen` and transpose for the reversed system
  (`NatQ5.HW.hwBarrierSTrev_of_ST`); the statements are `NatQ5.HW.HWBarrierST` and `NatQ5.HW.HWBarrierSTrev`.
* Root: this file imports the remaining files of `Nat/` and the files `DPFilter*.lean`, so that the import closure of
  `Paper.lean` contains every file of `Arctic/` (the probe files of the working repository, which only print axioms, are
  not released; the axiom checks are in `verify/Probe.lean`).
* As in the paper, indices run from 1 there and from 0 in Lean. The relevant indices are written `NatQ5.Rel`
  (an unqualified `Rel` would be ambiguous with Mathlib's `Rel`).
-/
import CollatzProof.Arctic.Nat.Final
import CollatzProof.Arctic.Nat.H2MainExtra
import CollatzProof.Arctic.Nat.AddLoopLift
import CollatzProof.Arctic.Nat.Coord
import CollatzProof.Arctic.Nat.NonVacuityDP
import CollatzProof.Arctic.Nat.NonVacuityW2a
import CollatzProof.Arctic.Nat.NonVacuityW2b
import CollatzProof.Arctic.Nat.NonVacuityW2c
import CollatzProof.Arctic.Nat.NonVacuityW2d
import CollatzProof.Arctic.Nat.NonVacuityW3a
import CollatzProof.Arctic.Nat.NonVacuityW3b
import CollatzProof.Arctic.Nat.NonVacuityW3h
import CollatzProof.Arctic.Nat.NonVacuityW3h2
import CollatzProof.Arctic.Nat.HWCorner
import CollatzProof.Arctic.Nat.NonVacuityHW
import CollatzProof.Arctic.Nat.BridgeDPFilter
import CollatzProof.Arctic.Nat.BridgeDPForms
import CollatzProof.Arctic.Nat.DfaLlnExample
import CollatzProof.Arctic.Nat.RigidExample
import CollatzProof.Arctic.Nat.RigidNorm
import CollatzProof.Arctic.Nat.RigidOrder
import CollatzProof.Arctic.Nat.RigidSpec
import CollatzProof.Arctic.DPFilter
import CollatzProof.Arctic.DPFilterBZ
import CollatzProof.Arctic.DPFilterCtrl

namespace Collatz.Arctic.Paper

open Collatz.Arctic

/-! ## Section 9: Natural-number matrix interpretations -/

/-- **Theorem 9.2 (i)** ($\mathcal T$, rule removal): a monotone natural-number matrix interpretation that weakly orients
all 11 rules strictly orients none of them. -/
theorem paper_thm_9_2_T : NatQ5.NatBarrierST := NatQ5.natBarrierST_final

/-- **Theorem 9.2 (i)** ($\mathcal T^{\mathrm{rev}}$, rule removal). -/
theorem paper_thm_9_2_Trev : NatQ5.NatBarrierSTrev := NatQ5.natBarrierSTrev_final

/-- **Theorem 9.2 (ii)** ($\mathcal T$, top forms): without monotonicity, none of the three left-end rules is strictly
oriented. -/
theorem paper_thm_9_2_B : NatQ5.NatBarrierSTB := NatQ5.natBarrierSTB_final

/-- **Theorem 9.2 (ii)** ($\mathcal T^{\mathrm{rev}}$, top forms): without monotonicity, neither `.f -> .` nor
`.t -> .2` is strictly oriented. -/
theorem paper_thm_9_2_revTop : NatQ5.NatBarrierSTrevTop := NatQ5.natBarrierSTrevTop_final

/-- **Theorem 9.2 (iii)** ($\mathcal T$, dependency pairs): the essential SCC $P_B$ is not strictly oriented in the
first component. -/
theorem paper_thm_9_2_DP : NatQ5.NatBarrierDP := NatQ5.natBarrierDP_final

/-- **Theorem 9.2 (iii)** ($\mathcal T^{\mathrm{rev}}$, dependency pairs, the essential SCC
$P^{\mathrm{rev}}_{\mathcal T}$ with usable rules $A^{\mathrm{rev}} \cup B^{\mathrm{rev}}$). -/
theorem paper_thm_9_2_DPrev : NatQ5.NatBarrierDPrev := NatQ5.natBarrierDPrev_final

/-- **Theorem 9.2**, all six statements together. -/
theorem paper_thm_9_2 :
    NatQ5.NatBarrierST ∧ NatQ5.NatBarrierSTB ∧ NatQ5.NatBarrierSTrev ∧ NatQ5.NatBarrierSTrevTop ∧
      NatQ5.NatBarrierDP ∧ NatQ5.NatBarrierDPrev :=
  NatQ5.allBarriers_final

/-- **Proposition 9.4 (i)** ($\mathcal T$): every rule `ρ` is strictly oriented by a monotone interpretation of
dimension 2 that weakly orients all rules but one other rule `σ` (and does not weakly orient `σ`). -/
theorem paper_prop_9_4_drop : ∀ ρ ∈ rulesST, ∃ σ ∈ rulesST, σ ≠ ρ ∧ ∃ I : Letter → NatQ5.NAff 2,
    NatQ5.NMono I ∧ (∀ τ ∈ rulesST.erase σ, NatQ5.NWeak I τ) ∧ ¬ NatQ5.NWeak I σ ∧ NatQ5.NStrict I ρ :=
  NatQ5.strict_each_drop

/-- **Proposition 9.4 (i)** ($\mathcal T^{\mathrm{rev}}$): the statement of Theorem 9.2 (i) fails for the system with
one rule removed (three such rules). -/
theorem paper_prop_9_4_drop_rev :
    ¬ NatQ5.NatBarrierFor (NatQ5.rulesSTrev.erase ⟨[Letter.rgt, Letter.t], [Letter.rgt, Letter.d2]⟩) ∧
      ¬ NatQ5.NatBarrierFor (NatQ5.rulesSTrev.erase ⟨[Letter.d1, Letter.f], [Letter.t, Letter.d0]⟩) ∧
      ¬ NatQ5.NatBarrierFor (NatQ5.rulesSTrev.erase ⟨[Letter.d2, Letter.f], [Letter.f, Letter.d1]⟩) :=
  NatQ5.W5.not_barrierRev_drop

/-- **Proposition 9.4 (ii)** ($\mathcal T$): without monotonicity, the form of Theorem 9.2 (i) fails. -/
theorem paper_prop_9_4_noMono : ¬ NatQ5.NatBarrierForNoMono rulesST := NatQ5.not_barrier_noMono

/-- **Proposition 9.4 (ii)** ($\mathcal T$): a non-monotone interpretation of dimension 1 that weakly orients all
11 rules strictly orients every rule except the three left-end rules. -/
theorem paper_prop_9_4_noMono_nonB : ∀ ρ ∈ rulesST, ρ ∉ NatQ5.rulesSTB → NatQ5.NStrict NatQ5.INoMono ρ :=
  NatQ5.noMono_strict_nonB

/-- **Proposition 9.4 (ii)** ($\mathcal T^{\mathrm{rev}}$): without monotonicity, the form of Theorem 9.2 (i) fails. -/
theorem paper_prop_9_4_noMono_rev : ¬ NatQ5.NatBarrierForNoMono NatQ5.rulesSTrev := NatQ5.not_barrierRev_noMono

/-- **Proposition 9.4 (ii)** ($\mathcal T^{\mathrm{rev}}$): a non-monotone interpretation of dimension 1 that weakly
orients all 11 rules strictly orients every rule except the two top rules. -/
theorem paper_prop_9_4_noMono_nonTop :
    ∀ ρ ∈ NatQ5.rulesSTrev, ρ ∉ NatQ5.rulesSTrevTop → NatQ5.NStrict NatQ5.W5.INoMonoRev ρ :=
  NatQ5.W5.noMono_strict_nonTop

/-- **Proposition 9.4 (iii)**: each dependency pair of $P^{\mathrm{rev}}_{\mathcal T}$ and of $P_B$ alone is strictly
oriented in the first component by an interpretation of dimension 1. -/
theorem paper_prop_9_4_pair :
    (∀ π ∈ pairsPDrev, ∃ J : DLetter → NatQ5.NAff 1, NatQ5.NStrictTopD J π) ∧
      ∀ π ∈ pairsPB, ∃ J : DLetter → NatQ5.NAff 1, NatQ5.NStrictTopD J π :=
  NatQ5.W5.strict_each_pair

/-- **Proposition 9.4 (iii)** ($\mathcal T$): the form of Theorem 9.2 (iii) without the weak orientation of the other
pairs (the printed form of [YAH, Theorem 3.10]) fails. -/
theorem paper_prop_9_4_literal : ¬ NatQ5.W5.LiteralDP := NatQ5.W5.not_literal

/-- **Proposition 9.4 (iii)** ($\mathcal T^{\mathrm{rev}}$): the same. -/
theorem paper_prop_9_4_literal_rev : ¬ NatQ5.W5.LiteralDPrev := NatQ5.W5.not_literalRev

/-- **Proposition 9.4 (iii)** ($\mathcal T$): the form of Theorem 9.2 (iii) fails if the usable rule `t. -> 2.`
(`NatQ5.rTdot`) is dropped. -/
theorem paper_prop_9_4_dropU : ¬ NatQ5.W5.NatBarrierDPFor (usableST.erase NatQ5.rTdot) pairsPB :=
  NatQ5.W5.not_barrierDP_dropTdot

/-- **Proposition 9.4 (iii)** ($\mathcal T^{\mathrm{rev}}$): the form of Theorem 9.2 (iii) fails if the usable rules are
cut down to the first six (the rules of $B^{\mathrm{rev}}$ are dropped). -/
theorem paper_prop_9_4_dropU_rev : ¬ NatQ5.W5.NatBarrierDPFor (usableSTrev.take 6) pairsPDrev :=
  NatQ5.W5.not_barrierDPrev_dropB

/-! ## Section 10: From rewriting to automata -/

/-- **Lemma 10.2** (the identity for one step: the decrease of `Φ` in a context is the step term). -/
theorem paper_lem_10_2_step {d : ℕ} [NeZero d] (I : Letter → NatQ5.NAff d) (p q : Word) (ρ : Rule) :
    (NatQ5.PhiN I (p ++ ρ.lhs ++ q) : ℤ) - NatQ5.PhiN I (p ++ ρ.rhs ++ q) = NatQ5.stepTerm I p ρ q :=
  NatQ5.lemma_66_1_1 I p q ρ

/-- **Lemma 10.2** (if the 11 rules are weakly oriented, the value does not increase along a step of $T$; no
monotonicity). -/
theorem paper_lem_10_2_T {d : ℕ} [NeZero d] {I : Letter → NatQ5.NAff d}
    (hweak : ∀ ρ ∈ rulesST, NatQ5.NWeak I ρ) (n : ℕ) (hn : 2 ≤ n) :
    NatQ5.PhiN I (can (T n)) ≤ NatQ5.PhiN I (can n) :=
  NatQ5.phiN_can_T_le hweak n hn

/-- **Lemma 10.2** (the orbit bound: with monotonicity, each use of a strictly oriented rule decreases the value by at
least 1). -/
theorem paper_lem_10_2_orbit {d : ℕ} [NeZero d] {I : Letter → NatQ5.NAff d} (hmono : NatQ5.NMono I)
    (hweak : ∀ ρ ∈ rulesST, NatQ5.NWeak I ρ) {ρ : Rule} (hρ : NatQ5.NStrict I ρ) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) →
      NatQ5.PhiN I (can (T^[m] n)) + usesOrbit ρ n m ≤ NatQ5.PhiN I (can n) :=
  NatQ5.orbit_bound_nat hmono hweak hρ

/-- **Lemma 10.3** (the value of a canonical string is the value of the value automaton). -/
theorem paper_lem_10_3 {d : ℕ} [NeZero d] (I : Letter → NatQ5.NAff d) (n : ℕ) :
    NatQ5.PhiN I (can n) = NatQ5.aval (NatQ5.natAuto I) (NatQ5.binWord n) :=
  NatQ5.phiN_can_eq_aval I n

/-- **Lemma 10.4** (transposition: the value of $\mathcal T^{\mathrm{rev}}$ is a value of the transposed homogeneous
matrices). -/
theorem paper_lem_10_4 {d : ℕ} [NeZero d] (I : Letter → NatQ5.NAff d) (n : ℕ) :
    NatQ5.PhiN I (can n).reverse = NatQ5.NW (fun s => (NatQ5.homFam I s).transpose) (can n) none (some 0) :=
  NatQ5.phiN_rev_eq_transpose I n

/-- **Lemma 10.4** (weak orientation of a reversed rule by transposition). -/
theorem paper_lem_10_4_weak {d : ℕ} (I : Letter → NatQ5.NAff d) (ρ : Rule) :
    NatQ5.NWeak I (NatQ5.ruleRev ρ) ↔ NatQ5.GWeak (NatQ5.W5.transFam I) ρ :=
  NatQ5.W5.nweak_rev_iff_transpose I ρ

/-- **Lemma 10.4** (strict orientation of a reversed rule by transposition). -/
theorem paper_lem_10_4_strict {d : ℕ} [NeZero d] (I : Letter → NatQ5.NAff d) (ρ : Rule) :
    NatQ5.NStrict I (NatQ5.ruleRev ρ) ↔
      NatQ5.GWeak (NatQ5.W5.transFam I) ρ ∧
        NatQ5.NW (NatQ5.W5.transFam I) ρ.rhs none (some 0) < NatQ5.NW (NatQ5.W5.transFam I) ρ.lhs none (some 0) :=
  NatQ5.W5.nstrict_rev_iff_transpose I ρ

/-- **Lemma 10.5** (value embedding: adding a source and a sink gives a monotone interpretation). -/
theorem paper_lem_10_5_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι) :
    NatQ5.NMono (NatQ5.embInterp N a z) :=
  NatQ5.embInterp_mono N a z

/-- **Lemma 10.5** (weak orientation of the 11 rules from (G1)). -/
theorem paper_lem_10_5_weak {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι)
    (hweak : ∀ ρ ∈ rulesST, NatQ5.GWeak N ρ) : ∀ ρ ∈ rulesST, NatQ5.NWeak (NatQ5.embInterp N a z) ρ :=
  NatQ5.embInterp_weak N a z hweak

/-- **Lemma 10.5** (the value is the entry `(N_{can(n)})_{az}`). -/
theorem paper_lem_10_5_phi {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι) (n : ℕ) :
    NatQ5.PhiN (NatQ5.embInterp N a z) (can n) = NatQ5.NW N (can n) a z :=
  NatQ5.embInterp_phi N a z n

/-- **Lemma 10.5** (the embedded interpretation strictly orients no rule). -/
theorem paper_lem_10_5_not_strict {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι) :
    ∀ ρ ∈ rulesST, ¬ NatQ5.NStrict (NatQ5.embInterp N a z) ρ :=
  NatQ5.embInterp_not_strict N a z

/-- **Lemma 10.6** (the lift modulo 3: the value identity `Φ̃(n) = Φ(n) [3 ∤ n]`). -/
theorem paper_lem_10_6 {Q : Type*} [Fintype Q] [DecidableEq Q] (A : NatQ5.ValAuto Q) (n : ℕ) (hn : 1 ≤ n) :
    NatQ5.aval (NatQ5.liftT A) (NatQ5.binWord n) = NatQ5.aval A (NatQ5.binWord n) * if 3 ∣ n then 0 else 1 :=
  NatQ5.aval_liftT A n hn

/-- **Lemma 10.6** (from (M) to (M$_3$) for the lift). -/
theorem paper_lem_10_6_mono3 {Q : Type*} [Fintype Q] [DecidableEq Q] {A : NatQ5.ValAuto Q}
    (h : NatQ5.AutoMono A) : NatQ5.AutoMono3 (NatQ5.liftT A) :=
  NatQ5.liftT_mono3 h

/-- **Lemma 10.7** (a component with a killing word is killed by `u*`). -/
theorem paper_lem_10_7 {Q : Type*} [Fintype Q] [DecidableEq Q] (A : NatQ5.ValAuto Q) {u : List (Fin 2)}
    (hu : NatQ5.IsUStar A u) (q : Q) {z : List (Fin 2)} (hz : NatQ5.Kills A (NatQ5.sccOf A q) z) :
    NatQ5.DC A (NatQ5.sccOf A q) u = 0 :=
  NatQ5.ustar_kills A hu q hz

/-- **Theorem 10.8** (under (M$_3$) and (Z$_3$), all components are 0/1). -/
theorem paper_thm_10_8 {Q : Type*} [Fintype Q] [DecidableEq Q] (L : NatQ5.ValAuto Q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → NatQ5.aval L (NatQ5.binWord (T n)) ≤ NatQ5.aval L (NatQ5.binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → NatQ5.aval L (NatQ5.binWord n) = 0) :
    ∀ C, NatQ5.IsComp L C → NatQ5.ZeroOne L C :=
  NatQ5.zeroOne_of_T_mono L hT h3

/-- **Theorem 10.8** (the diagonal growth on the relevant indices is at most 1). -/
theorem paper_thm_10_8_gdiag {Q : Type*} [Fintype Q] [DecidableEq Q] (L : NatQ5.ValAuto Q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → NatQ5.aval L (NatQ5.binWord (T n)) ≤ NatQ5.aval L (NatQ5.binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → NatQ5.aval L (NatQ5.binWord n) = 0) :
    NatQ5.Rigid.gDiag (NatQ5.restrictRel L).B ≤ 1 :=
  NatQ5.gDiag_restrictRel_le_one L hT h3

/-- **Corollary 10.9 (1)** (the lift of a value automaton with (M) has only 0/1 components, (H2$^{\mathrm{prod}}$)). -/
theorem paper_cor_10_9 : NatQ5.H2Core := NatQ5.h2Core

/-- **Corollary 10.9 (2)** (families of matrices with (G1)). -/
theorem paper_cor_10_9_gen {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι)
    (hw : ∀ ρ ∈ rulesST, NatQ5.GWeak N ρ) :
    ∀ C, NatQ5.IsComp (NatQ5.liftT (NatQ5.genAuto N a z)) C → NatQ5.ZeroOne (NatQ5.liftT (NatQ5.genAuto N a z)) C :=
  NatQ5.h2_gen N a z hw

/-- **Corollary 10.9 (3)** (natural-number interpretations that weakly orient the 11 rules, no monotonicity). -/
theorem paper_cor_10_9_nat {d : ℕ} [NeZero d] (I : Letter → NatQ5.NAff d) (hweak : ∀ ρ ∈ rulesST, NatQ5.NWeak I ρ) :
    ∀ C, NatQ5.IsComp (NatQ5.liftNat I) C → NatQ5.ZeroOne (NatQ5.liftNat I) C :=
  NatQ5.zeroOne_liftNat I hweak

/-- **Theorem 10.10** (values and uses on 0/1 automata). -/
theorem paper_thm_10_10 : NatQ5.W3CoreStmt := NatQ5.w3CoreStmt

/-- **Theorem 10.11** (the value-level core for value automata with (M), without (G2)). Combination:
`NatQ5.autoValueCore_iff_noG2` applied to `NatQ5.W4a.autoValueCore`. -/
theorem paper_thm_10_11 : NatQ5.AutoValueCoreNoG2 := NatQ5.autoValueCore_iff_noG2.mp NatQ5.W4a.autoValueCore

/-- **Theorem 10.11** (natural-number interpretations that weakly orient the 11 rules, no monotonicity). Combination:
`NatQ5.natValueCore'_of_autoValueCore` applied to `NatQ5.W4a.autoValueCore`. -/
theorem paper_thm_10_11_nat : NatQ5.NatValueCore' :=
  NatQ5.natValueCore'_of_autoValueCore NatQ5.W4a.autoValueCore

/-- **Theorem 10.11** (families of matrices with (G1)). Combination: `NatQ5.genValueCore_of_autoValueCore` applied to
`NatQ5.W4a.autoValueCore`. -/
theorem paper_thm_10_11_gen : NatQ5.GenValueCore :=
  NatQ5.genValueCore_of_autoValueCore NatQ5.W4a.autoValueCore

/-- **Corollary 10.12** ($\mathcal T$, the corner form of [HW06]): let `N` be a family of natural-number matrices on a
finite index set and `J` a set of indices with `(N_s)_{ii} ≥ 1` for every letter `s` and every `i ∈ J`. If `N` weakly
orients all 11 rules entrywise, then no rule decreases strictly at an entry `(i, j)` with `i, j ∈ J`. The form
`E_{\{1,d\}}` of [HW06] is the case `J = {1, d}`. -/
theorem paper_cor_10_12 : NatQ5.HW.HWBarrierST := NatQ5.HW.hwBarrierST

/-- **Corollary 10.12** ($\mathcal T^{\mathrm{rev}}$, the corner form of [HW06]; products of matrices in the order of
the letters, as for `NatQ5.NatBarrierSTrev`). -/
theorem paper_cor_10_12_rev : NatQ5.HW.HWBarrierSTrev := NatQ5.HW.hwBarrierSTrev

/-! ## Section 11: Diagonal growth at most one -/

/-- **Lemma 11.1** (splitting paths into blocks of length `κ`). -/
theorem paper_lem_11_1 {Q : Type*} [Fintype Q] [DecidableEq Q] (A : NatQ5.ValAuto Q) {G θ C : ℝ} {κ : ℕ}
    {z : List (Fin 2)} (hG : 1 ≤ G) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hS : ∀ q (bs : List (List (Fin 2))), (∀ b ∈ bs, b.length = κ) → ∀ x y : NatQ5.sccOf A q,
      (NatQ5.DC A (NatQ5.sccOf A q) bs.flatten x y : ℝ) ≤ C * G ^ bs.flatten.length * θ ^ bs.count z) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ bs : List (List (Fin 2)), (∀ b ∈ bs, b.length = κ) → ∀ i j,
      θ ^ Fintype.card Q * (NatQ5.Rigid.DxN A.B bs.flatten i j : ℝ) ≤
        C' * ((bs.length : ℝ) + 1) ^ Fintype.card Q * G ^ bs.flatten.length * θ ^ bs.count z :=
  NatQ5.path_block_bound A hG hθ0 hθ1 hS

/-- **Corollary 11.2** (a polynomial bound for the values when the diagonal growth is at most `G`). -/
theorem paper_cor_11_2 {Q : Type*} [Fintype Q] [DecidableEq Q] (A : NatQ5.ValAuto Q) {G : ℝ} (hG : 1 ≤ G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), NatQ5.Rigid.Dx A.B w i i ≤ G ^ w.length) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : List (Fin 2),
      (NatQ5.aval A w : ℝ) ≤ C * ((w.length : ℝ) + 1) ^ Fintype.card Q * G ^ w.length :=
  NatQ5.aval_poly_bound A hG hdiag

/-- **Lemma 11.3** (if `G > 1`, some set `S = scc(q)` has a uniform lower bound `c G^{|x|} ≤ ‖N^S_x‖` with
`c > 0`; hence the pair on `S` is strongly connected and rigid at `G`; the set `S` also has an internal edge). -/
theorem paper_lem_11_3 {Q : Type*} [Fintype Q] [DecidableEq Q] (A : NatQ5.ValAuto Q) {G : ℝ} (hG : 1 < G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), NatQ5.Rigid.Dx A.B w i i ≤ G ^ w.length)
    (hLC : ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log G ≤ NatQ5.Rigid.bAvg A.B κ) :
    ∃ q, NatQ5.Rigid.SC (NatQ5.compMat A (NatQ5.sccOf A q)) ∧
      NatQ5.Rigid.RigidAt (NatQ5.compMat A (NatQ5.sccOf A q)) G ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x,
        c * G ^ x.length ≤ NatQ5.Rigid.nrm (NatQ5.Rigid.Dx (NatQ5.compMat A (NatQ5.sccOf A q)) x)) ∧
      NatQ5.HasEdge A (NatQ5.sccOf A q) :=
  NatQ5.top_rigid' A hG hdiag hLC

/-- **Corollary 11.4** (a heavy family of words `ω(ε)`). -/
theorem paper_cor_11_4 {Q : Type*} [Fintype Q] [DecidableEq Q] (A : NatQ5.ValAuto Q) {G : ℝ} (hG : 1 < G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), NatQ5.Rigid.Dx A.B w i i ≤ G ^ w.length)
    (hLC : ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log G ≤ NatQ5.Rigid.bAvg A.B κ) :
    ∃ (a : Q) (Ψ : List (Fin 2)) (h : ℕ) (c : ℝ), 1 ≤ h ∧ 0 < c ∧
      ∀ ε : List (Fin 2),
        c * G ^ (NatQ5.Rigid.heavyWord Ψ h ε).length ≤ NatQ5.Rigid.Dx A.B (NatQ5.Rigid.heavyWord Ψ h ε) a a :=
  NatQ5.top_heavy A hG hdiag hLC

/-- **Theorem 11.8** (diagonal Lyapunov comparison: under (R), (M$_3$) and (Z$_3$), `q log G ≤ bAvg_q` for all
`q ≥ 1`). -/
theorem paper_thm_11_8 {Q : Type*} [Fintype Q] [DecidableEq Q] (L : NatQ5.ValAuto Q) (hall : ∀ q, NatQ5.Rel L q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → NatQ5.aval L (NatQ5.binWord (T n)) ≤ NatQ5.aval L (NatQ5.binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → NatQ5.aval L (NatQ5.binWord n) = 0) :
    ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log (NatQ5.Rigid.gDiag L.B) ≤ NatQ5.Rigid.bAvg L.B κ :=
  NatQ5.lyap_compare L hall hT h3

/-- **Proposition 11.12** (comparison along shrinking chains: the four conditions do not hold together). -/
theorem paper_prop_11_12 (V : ℕ → ℝ) (Ψ p₀ s : List (Fin 2)) {h : ℕ} (hh : 1 ≤ h) {G c C : ℝ} {p : ℕ}
    (hG : 1 < G) (hc : 0 < c)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → V (T n) ≤ V n)
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → V n ≤ 0)
    (hup : ∀ n, 1 ≤ n → ¬ 3 ∣ n →
      V n ≤ C * (((NatQ5.binWord n).length : ℝ) + 1) ^ p * G ^ (NatQ5.binWord n).length)
    (hlow : ∀ ε, c * G ^ (NatQ5.Rigid.heavyWord Ψ h ε).length ≤
      V (NatQ5.valW 1 (p₀ ++ NatQ5.Rigid.heavyWord Ψ h ε ++ s))) :
    False :=
  NatQ5.shrink_contra V Ψ p₀ s hh hG hc hT h3 hup hlow

/-- **Proposition 11.13** (under (R), (M$_3$) and (Z$_3$), the diagonal growth is at most 1). -/
theorem paper_prop_11_13 {Q : Type*} [Fintype Q] [DecidableEq Q] (L : NatQ5.ValAuto Q) (hall : ∀ q, NatQ5.Rel L q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → NatQ5.aval L (NatQ5.binWord (T n)) ≤ NatQ5.aval L (NatQ5.binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → NatQ5.aval L (NatQ5.binWord n) = 0) :
    NatQ5.Rigid.gDiag L.B ≤ 1 :=
  NatQ5.gDiag_le_one_of_T_mono L hall hT h3

/-! ## Section 12: Values and uses on 0/1 automata -/

/-- **Lemma 12.3** (killing, part (i): `u♯` kills `scc(q)` for every relevant index `q` outside $Q_{\mathrm s}$). -/
theorem paper_lem_12_3 {Q : Type*} [Fintype Q] [DecidableEq Q] (A : NatQ5.ValAuto Q)
    (h01 : ∀ C, NatQ5.IsComp A C → NatQ5.ZeroOne A C) {K : Set (MinIdeal.BRel (NatQ5.W3c.ZIdx A))}
    {u : List (Fin 2)} {e : MinIdeal.BRel (NatQ5.W3c.ZIdx A)} (hS : NatQ5.W3c.Sharp A K u e) {q : Q}
    (hq : NatQ5.Rel A q) (hz : ¬ NatQ5.W3c.InZ A q) :
    NatQ5.DC A (NatQ5.sccOf A q) u = 0 :=
  NatQ5.W3c.Sharp.kills A h01 hS hq hz

/-- **Proposition 12.11** (existence of decomposition data). -/
theorem paper_prop_12_11 : NatQ5.W3c.DecompStmt := NatQ5.W3c.decompStmt

/-- **Proposition 12.11** (existence of decomposition data with the lower bound for `t₀`). -/
theorem paper_prop_12_11_T0 : NatQ5.DecompStmtT0 := NatQ5.decompStmtT0

/-- **Theorem 12.13** (law of large numbers for a finite DFA: uniform closeness to the stationary mean on average). -/
theorem paper_thm_12_13_mean {S : Type*} [Fintype S] [DecidableEq S] {δ : S → Bool → S} (J : ℕ)
    {φ : S → List Bool → ℝ} {q₀ : S} (hrec : Dfa.Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) :
    ∀ ε > 0, ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ x, Dfa.Reach δ q₀ x →
      NatQ5.W3d.avg (L + J)
        (fun w => |NatQ5.W3d.wsum δ J φ x w L - NatQ5.W3d.statMean δ J φ q₀ * L|) ≤ ε * L :=
  NatQ5.W3d.stat_mean J hrec hC

/-- **Theorem 12.13** (deterministic form: window frequencies give sums over intervals). -/
theorem paper_thm_12_13_win {S : Type*} [Fintype S] [DecidableEq S] {δ : S → Bool → S} (J : ℕ)
    {φ : S → List Bool → ℝ} {q₀ : S} (hrec : Dfa.Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∃ δ' : ℚ, 0 < δ' ∧ ∀ J', J₀ ≤ J' → ∃ N₀ : ℕ, ∀ (ω : List Bool) (a b : ℕ),
      WinClose (ω.map NatQ5.W3d.ofB) a b J' δ' → N₀ ≤ b - a → ∀ x, Dfa.Reach δ q₀ x → ∀ k, a ≤ k → k ≤ b →
        |NatQ5.W3d.wsum δ J φ x (ω.drop a) (k - a) - NatQ5.W3d.statMean δ J φ q₀ * ((k - a : ℕ) : ℝ)| ≤
          ε * ((b - a : ℕ) : ℝ) :=
  NatQ5.W3d.lln_of_winClose J hrec hC ε hε

/-- **Corollary 12.18** (the event for the numbers of uses of the 11 rules). -/
theorem paper_cor_12_18 (β₀ : List Bool) : ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ∀ L : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (1 - ε ≤ Prσ β₀ k (NatQ5.W3a.EvLeft c k)) ∧
    ∀ β : List Bool, NatQ5.W3a.EvLeft c k β → k ≤ β.length → ∀ n K τ : ℕ, 1 ≤ K →
      K + (parityOf β₀).length ≤ n → 2 ^ (K - 1) ≤ τ → (parityOf β).length < n →
      k ≤ n - K - (parityOf β₀).length →
      ∀ (P : ℕ → Prop) (s : Finset ℕ), (∀ u ∈ s, u < 2 ^ (n - K - (parityOf β₀).length) ∧ P u) →
        2 ^ (n - K - (parityOf β₀).length - L) ≤ s.card →
        ∃ u < 2 ^ (n - K - (parityOf β₀).length), P u ∧
          NatQ5.W3a.UsesGood c k (famX0 β₀ β n K τ u) (parityOf β).length :=
  NatQ5.W3a.uses_family_inter β₀

/-- **Proposition 12.19** (the top window of the end point). -/
theorem paper_prop_12_19 (E : ℕ) : ∃ c : ℚ, 0 < c ∧ ∃ B : ℕ, ∀ (β₀ : List Bool) (k : ℕ), B ≤ k →
    c ≤ Prσ β₀ k (fun β => ∀ τ : List (Fin 2), τ.length = E → ∀ n u : ℕ,
      E + 9 + (parityOf β₀).length ≤ n → u < 2 ^ (n - (E + 9) - (parityOf β₀).length) →
      (NatQ5.binWord (famX1 β₀ β n (E + 9) (NatQ5.W3b.topT0 τ) u)).take E = τ) :=
  NatQ5.W3b.top_window E

open Classical in
/-- **Proposition 12.24** (few long runs of misses: the weighted number of long runs is at most `ε |I|` with probability
at least `1 - η'`). -/
theorem paper_prop_12_24 (P : Word → Prop) (a : ℕ) (η : ℚ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hP : NatQ5.W3b.MissFrac P a η) :
    ∃ n₀ : ℕ, ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ ∀ n₁ ≥ n₀,
      ∀ (C : ℚ) (d : ℕ) (α α' : ℚ) (κ κ' : ℕ) (A K : ℕ → ℕ),
        0 ≤ C → 0 ≤ α → 0 ≤ α' → 1 ≤ κ → (∀ R, (A R : ℚ) ≤ α * R + α') →
        (∀ R, R ≤ κ * K R + κ') →
      ∀ ε : ℚ, 0 < ε → ∀ η' : ℚ, 0 < η' → ∃ J : ℕ, ∀ (β₀ : List Bool) (k : ℕ) (I S : Finset ℕ),
        (∀ i ∈ I, (i + 1) * (n₁ + a) ≤ k) → (∀ R ∈ S, J < R) →
        Prσ β₀ k (fun β => ε * I.card < ∑ i ∈ I, ∑ R ∈ S,
          C * ((R : ℚ) + 1) ^ d *
            (if NatQ5.W3b.RunMiss P β₀.length n₁ a i (A R) (K R) β then 1 else 0)) ≤ η' :=
  NatQ5.W3b.gap_twin P a η hη0 hη1 hP

open Classical in
/-- **Proposition 12.26** (the tail at the starting point). -/
theorem paper_prop_12_26 {Q : Type} [Fintype Q] [DecidableEq Q] {B : NatQ5.ValAuto Q} (S : NatQ5.W3h.Setup B)
    (β' : List Bool) {n u J Nmax n₁ a : ℕ} (KT : ℕ → ℕ) (hKn : S.Kc + S.s' ≤ n)
    (hu : u < 2 ^ S.Flen n) (hg : 1 ≤ n₁ + a)
    (hJ : ∀ r, J < r → 1 ≤ KT r ∧ 11 * (n₁ + a) * (KT r + 2) ≤ S.Lr S.C0 r)
    (hNmax : (NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length ≤ Nmax) (i : S.Item) :
    ∑ p ∈ Finset.range (NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
      ∑ r ∈ Finset.Ioc J (NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
        (S.xiI i r (NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) p : ℝ) ≤
      ∑ r ∈ Finset.Ioc J Nmax, S.wt r * S.cntRun (S.Lr S.C0 r) ((bitsMSB (S.Flen n) u).map NatQ5.W3a.l2f) +
      22 * (n₁ + a) * ∑ j ∈ Finset.range (β'.length / (n₁ + a)), ∑ r ∈ Finset.Ioc J Nmax,
        S.wt r * (if NatQ5.W3b.RunMiss (NatQ5.W3h.PU S.us) S.β₀.length n₁ a j (KT r) (KT r) (S.β₀ ++ β')
          then 1 else 0) :=
  S.tail_x0 β' KT hKn hu hg hJ hNmax i

/-- **Proposition 12.27** (an upper bound at the starting point, part (iii): on the events). -/
theorem paper_prop_12_27 {Q : Type} [Fintype Q] [DecidableEq Q] {B : NatQ5.ValAuto Q} (S : NatQ5.W3h.Setup B)
    (β' : List Bool) (n u J : ℕ) (hKn : S.Kc + S.s' ≤ n) (hu : u < 2 ^ S.Flen n)
    {clo : NatQ5.W3h.PSt B} {dlo : ℕ} {Clo ε η₀ θF εT : ℝ}
    (hconf : S.conf (S.mid0 (S.β₀ ++ β') n u) = clo)
    (hdeg : ∀ d, dlo < d → S.coef d clo.1 = 0) (hC : S.coef dlo clo.1 = Clo) (hdlo : 1 ≤ dlo)
    (hε0 : 0 < ε) (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1)
    (hfree : ∀ (i : S.Item) x, Dfa.Reach (NatQ5.W3c.muStepB B) S.e x →
      ∀ p, S.Kc - 1 ≤ p → p ≤ S.Kc - 1 + S.Flen n →
      |NatQ5.W3d.wsum (NatQ5.W3c.muStepB B) J (S.phi i J) x
        ((NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).map NatQ5.W3d.f2b |>.drop (S.Kc - 1))
        (p - (S.Kc - 1)) - S.QJ i J * ((p - (S.Kc - 1) : ℕ) : ℝ)| ≤ η₀ / 4 * (S.Flen n : ℝ))
    (hter : ∀ (i : S.Item) x, Dfa.Reach (NatQ5.W3c.muStepB B) S.e x →
      ∀ p, n - 1 ≤ p → p ≤ n - 1 + ((parityOf (S.β₀ ++ β')).length - S.s') →
      |NatQ5.W3d.wsum (NatQ5.W3c.muStepB B) J (S.phi i J) x
        ((NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).map NatQ5.W3d.f2b |>.drop (n - 1))
        (p - (n - 1)) - S.QJ i J * ((p - (n - 1) : ℕ) : ℝ)| ≤
        η₀ / 4 * (((parityOf (S.β₀ ++ β')).length - S.s' : ℕ) : ℝ))
    (htail : ∀ i : S.Item, ∑ p ∈ Finset.range (NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
      ∑ r ∈ Finset.Ioc J (NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
        (S.xiI i r (NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) p : ℝ) ≤
          θF * (S.Flen n + 1) + εT * β'.length)
    (hθ : θF ≤ η₀ / 8) (hεT : εT ≤ η₀ / 8)
    (hQ : ∀ i : S.Item, S.Qc i - S.QJ i J ≤ η₀ / 4)
    (hk0 : 1 ≤ β'.length)
    (hk1 : ((S.BJ J : ℝ) + S.Hb) * (S.C0 : ℝ) ≤ η₀ / 4 * β'.length)
    (hk2 : ∑ d ∈ Finset.range dlo, S.coef d clo.1 ≤ ε / 2 * β'.length)
    (hk3 : S.Ktot clo.1 * (S.Cst * (η₀ + 1 / β'.length)) ≤ ε / 2) :
    (NatQ5.aval B (NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) : ℝ) ≤
      (Clo + ε) * ((NatQ5.binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length : ℝ) ^ dlo :=
  S.x0_upper β' n u J hKn hu hconf hdeg hC hdlo hε0 hη₀ hη₀1 hfree hter htail hθ hεT hQ hk0 hk1 hk2 hk3

/-- **Proposition 12.28** (a lower bound at the end point, part (iii): on the events). -/
theorem paper_prop_12_28 {Q : Type} [Fintype Q] [DecidableEq Q] {B : NatQ5.ValAuto Q} (S : NatQ5.W3h.Setup B)
    (β' : List Bool) (n u b M Δ k : ℕ) (hKn : S.Kc + S.s' ≤ n) (hu : u < 2 ^ S.Flen n)
    (h3 : ¬ 3 ∣ famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)
    (hA : 1 ≤ terrasA (parityOf (S.β₀ ++ β')))
    (hb1 : 2 ^ (b + Δ + S.Kc) ≤ 3 ^ terrasA (parityOf (S.β₀ ++ β')))
    (hb2 : 3 ^ terrasA (parityOf (S.β₀ ++ β')) < 2 ^ (b + (S.Kc + Δ + 1)))
    (htop : (NatQ5.binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).take S.E = S.τ)
    {J' : ℕ} {δ' : ℚ} {N₀' : ℕ} {η₁ ε Kmax : ℝ}
    (hlln : ∀ (ω : List Bool) (a b : ℕ), WinClose (ω.map NatQ5.W3d.ofB) a b J' δ' → N₀' ≤ b - a →
      ∀ i : S.Item, ∀ x, Dfa.Reach (NatQ5.W3c.muStepB B) S.e x → ∀ k, a ≤ k → k ≤ b →
        |NatQ5.W3d.wsum (NatQ5.W3c.muStepB B) M (S.phi i M) x (ω.drop a) (k - a) -
            S.QJ i M * ((k - a : ℕ) : ℝ)| ≤
          η₁ / 4 * ((b - a : ℕ) : ℝ))
    (hN₀'b : N₀' ≤ b) (hN₀'F : N₀' ≤ S.Flen n)
    (hlow : WinClose (bitsMSB b (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n % 2 ^ b)) 0 b J' δ')
    (hmid : WinClose (bitsMSB (n - S.Kc - (parityOf S.β₀).length)
      (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u % 2 ^ n % 2 ^ (n - S.Kc) / 2 ^ (parityOf S.β₀).length)) 0
        (n - S.Kc - (parityOf S.β₀).length) J' δ')
    (hη₁ : 0 < η₁) (hη₁1 : η₁ ≤ 1) (hM : 1 ≤ M) (hMF : M ≤ S.Flen n)
    (hKmax : ∀ c ∈ S.Kset, S.Ktot c.1 ≤ Kmax)
    (hcoefM : ∀ c ∈ S.Kset, ∀ d ≤ S.Dm, S.coef d c.1 - ε / 3 ≤ S.coefM M d c.1)
    (hk : 1 ≤ k) (hNk : k ≤ (NatQ5.binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length)
    (hK1 : Kmax * (S.Cst * (η₁ + 1 / k)) ≤ ε / 3)
    (hK2 : Kmax * (S.Dm * ((M - 1 : ℕ) : ℝ) * (max (S.BJ M : ℝ) 1) ^ S.Dm) ≤ ε / 3 * k)
    (hK3 : ((S.BJ M : ℝ) + S.Hb) * ((2 * S.Kc + Δ + M + S.s' : ℕ) : ℝ) ≤ η₁ / 2 * k) :
    ∃ c₁ ∈ S.Kset, (S.coef (S.degF c₁.1) c₁.1 - ε) *
        ((NatQ5.binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length : ℝ) ^ (S.degF c₁.1) ≤
      (NatQ5.aval B (NatQ5.binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) : ℝ) :=
  S.x1_lower β' n u b M Δ k hKn hu h3 hA hb1 hb2 htop hlln hN₀'b hN₀'F hlow hmid hη₁ hη₁1 hM hMF hKmax hcoefM
    hk hNk hK1 hK2 hK3

/-- **Lemma 12.30** (case A: a configuration whose coefficients of positive degree all vanish gives the conclusion of
Theorem 10.10). -/
theorem paper_lem_12_30 {Q : Type} [Fintype Q] [DecidableEq Q] {B : NatQ5.ValAuto Q} (S : NatQ5.W3h.Setup B)
    {c : NatQ5.W3h.PSt B} (hc : c ∈ S.Kset) (hcoef : ∀ d, 1 ≤ d → S.coef d c.1 = 0) :
    ∀ ρ ∈ rulesST, ∀ K₀ : ℕ, ∃ n, K₀ ≤ n ∧ ¬ 3 ∣ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ NatQ5.aval B (NatQ5.binWord n) < usesOrbit ρ n m :=
  S.caseA hc hcoef

/-- **Proposition 12.31** (case B does not occur: under (M$_3$) some configuration has all coefficients of positive
degree equal to 0). -/
theorem paper_prop_12_31 : NatQ5.CaseBStmt := NatQ5.caseB

/-! ## Section 13: Reversal, top forms and dependency pairs -/

/-- **Lemma 13.1** (the mirrored canonical derivation of $\mathcal T^{\mathrm{rev}}$). -/
theorem paper_lem_13_1_rev (n : ℕ) (hn : 2 ≤ n) :
    Chain (NatQ5.canDerivRev n) (can n).reverse (can (T n)).reverse :=
  NatQ5.W5.canDerivRev_chain n hn

/-- **Lemma 13.1** ($\mathcal T$: a strictly oriented left-end rule decreases the value by at least 1 at each use; no
monotonicity). -/
theorem paper_lem_13_1_top {d : ℕ} [NeZero d] {I : Letter → NatQ5.NAff d}
    (hweak : ∀ ρ ∈ rulesST, NatQ5.NWeak I ρ) {ρ : Rule} (hρB : ρ ∈ NatQ5.rulesSTB) (hρ : NatQ5.NStrict I ρ) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) →
      NatQ5.PhiN I (can (T^[m] n)) + usesOrbit ρ n m ≤ NatQ5.PhiN I (can n) :=
  NatQ5.orbit_bound_top hweak hρB hρ

/-- **Lemma 13.1** ($\mathcal T^{\mathrm{rev}}$: the same for the two top rules). -/
theorem paper_lem_13_1_revTop {d : ℕ} [NeZero d] {I : Letter → NatQ5.NAff d}
    (hweak : ∀ ρ ∈ NatQ5.rulesSTrev, NatQ5.NWeak I ρ) {ρ : Rule} (hρB : NatQ5.ruleRev ρ ∈ NatQ5.rulesSTrevTop)
    (hρ : NatQ5.NStrict I (NatQ5.ruleRev ρ)) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) →
      NatQ5.PhiN I (can (T^[m] n)).reverse + usesOrbit ρ n m ≤ NatQ5.PhiN I (can n).reverse :=
  NatQ5.W5.orbit_bound_revTop hweak hρB hρ

/-- **Lemma 13.2** ($\mathcal T$: Theorem 9.2 (iii) is equivalent to (ii)). -/
theorem paper_lem_13_2 : NatQ5.NatBarrierDP ↔ NatQ5.NatBarrierSTB := NatQ5.natBarrierDP_iff_STB

/-- **Lemma 13.2** ($\mathcal T^{\mathrm{rev}}$). -/
theorem paper_lem_13_2_rev : NatQ5.NatBarrierDPrev ↔ NatQ5.NatBarrierSTrevTop := NatQ5.natBarrierDPrev_iff_top

/-- **Proposition 13.3** ($\mathcal T$, the order of [YAH]: entrywise weak and strict in the first component).
Combination: `NatQ5.natBarrierDP_full` applied to `NatQ5.natBarrierDP_final`. -/
theorem paper_prop_13_3_full (d : ℕ) [NeZero d] (J : DLetter → NatQ5.NAff d)
    (hU : ∀ ρ ∈ usableST, NatQ5.NWeakD J ρ.plain)
    (hP : ∀ π ∈ pairsPB, NatQ5.NWeakD J π ∨ NatQ5.NStrictD J π) :
    ∀ π ∈ pairsPB, ¬ NatQ5.NStrictD J π :=
  NatQ5.natBarrierDP_full NatQ5.natBarrierDP_final d J hU hP

/-- **Proposition 13.3** ($\mathcal T^{\mathrm{rev}}$, the order of [YAH]). Combination:
`NatQ5.natBarrierDPrev_full` applied to `NatQ5.natBarrierDPrev_final`. -/
theorem paper_prop_13_3_full_rev (d : ℕ) [NeZero d] (J : DLetter → NatQ5.NAff d)
    (hU : ∀ ρ ∈ usableSTrev, NatQ5.NWeakD J ρ.plain)
    (hP : ∀ π ∈ pairsPDrev, NatQ5.NWeakD J π ∨ NatQ5.NStrictD J π) :
    ∀ π ∈ pairsPDrev, ¬ NatQ5.NStrictD J π :=
  NatQ5.natBarrierDPrev_full NatQ5.natBarrierDPrev_final d J hU hP

/-- **Proposition 13.3** ($\mathcal T$, the scalar form of [EWZ08, §5]). Combination:
`NatQ5.W5.natBarrierDP_scalar` applied to `NatQ5.natBarrierDP_final`. -/
theorem paper_prop_13_3_scalar (d : ℕ) [NeZero d] (Jp : Letter → NatQ5.NAff d) (H : NatQ5.W5.SAff d)
    (hU : ∀ ρ ∈ usableST, NatQ5.NWeak Jp ρ) (hP : ∀ ρ ∈ NatQ5.rulesSTB, NatQ5.W5.SWeak H Jp ρ) :
    ∀ ρ ∈ NatQ5.rulesSTB, ¬ NatQ5.W5.SStrict H Jp ρ :=
  NatQ5.W5.natBarrierDP_scalar NatQ5.natBarrierDP_final d Jp H hU hP

/-- **Proposition 13.3** ($\mathcal T^{\mathrm{rev}}$, the scalar form). Combination:
`NatQ5.W5.natBarrierDPrev_scalar` applied to `NatQ5.natBarrierDPrev_final`. -/
theorem paper_prop_13_3_scalar_rev (d : ℕ) [NeZero d] (Jp : Letter → NatQ5.NAff d) (H : NatQ5.W5.SAff d)
    (hU : ∀ ρ ∈ usableSTrev, NatQ5.NWeak Jp ρ) (hP : ∀ ρ ∈ NatQ5.rulesSTrevTop, NatQ5.W5.SWeak H Jp ρ) :
    ∀ ρ ∈ NatQ5.rulesSTrevTop, ¬ NatQ5.W5.SStrict H Jp ρ :=
  NatQ5.W5.natBarrierDPrev_scalar NatQ5.natBarrierDPrev_final d Jp H hU hP

/-- **Proposition 13.3** ($\mathcal T$, comparison in a component `k`). Combination: `NatQ5.W5.natBarrierDP_row` applied
to `NatQ5.natBarrierDP_final`. -/
theorem paper_prop_13_3_row (d : ℕ) [NeZero d] (k : Fin d) (J : DLetter → NatQ5.NAff d)
    (hU : ∀ ρ ∈ usableST, NatQ5.NWeakD J ρ.plain) (hP : ∀ π ∈ pairsPB, NatQ5.W5.RowWeakD k J π) :
    ∀ π ∈ pairsPB, ¬ NatQ5.W5.RowStrictD k J π :=
  NatQ5.W5.natBarrierDP_row NatQ5.natBarrierDP_final d k J hU hP

/-- **Proposition 13.3** ($\mathcal T^{\mathrm{rev}}$, comparison in a component `k`). Combination:
`NatQ5.W5.natBarrierDPrev_row` applied to `NatQ5.natBarrierDPrev_final`. -/
theorem paper_prop_13_3_row_rev (d : ℕ) [NeZero d] (k : Fin d) (J : DLetter → NatQ5.NAff d)
    (hU : ∀ ρ ∈ usableSTrev, NatQ5.NWeakD J ρ.plain) (hP : ∀ π ∈ pairsPDrev, NatQ5.W5.RowWeakD k J π) :
    ∀ π ∈ pairsPDrev, ¬ NatQ5.W5.RowStrictD k J π :=
  NatQ5.W5.natBarrierDPrev_row NatQ5.natBarrierDPrev_final d k J hU hP

/-- **Proposition 13.4** ($\mathcal T$, argument filters). Combination: `NatQ5.natBarrierDPFilt_of_DP` applied to
`NatQ5.natBarrierDP_final`. -/
theorem paper_prop_13_4 : NatQ5.NatBarrierDPFilt := NatQ5.natBarrierDPFilt_of_DP NatQ5.natBarrierDP_final

/-- **Proposition 13.4** ($\mathcal T^{\mathrm{rev}}$, argument filters). Combination:
`NatQ5.natBarrierDPrevFilt_of_DPrev` applied to `NatQ5.natBarrierDPrev_final`. -/
theorem paper_prop_13_4_rev : NatQ5.NatBarrierDPrevFilt :=
  NatQ5.natBarrierDPrevFilt_of_DPrev NatQ5.natBarrierDPrev_final

section YAH310

open Collatz.Arctic.NatQ5.W5.ZYah

/-- **Remark on the printed form of [YAH, Theorem 3.10]** (Zantema's system $\mathcal Z$): an interpretation of
dimension 2 weakly orients all rules of $\mathcal Z$ and strictly orients one pair of `I` without weakly orienting the
other. -/
theorem paper_rem_yah310_Z :
    (∀ p ∈ rulesZ, ZW IZ p.1 p.2) ∧ ZS IZ [ZL.H, ZL.s] [ZL.H, ZL.h] ∧ ¬ ZW IZ [ZL.H, ZL.t] [ZL.H, ZL.h] :=
  Z_literal_false

/-- **Remark on the printed form of [YAH, Theorem 3.10]** ($\mathcal Z^{\mathrm{rev}}$). -/
theorem paper_rem_yah310_Zrev :
    (∀ p ∈ rulesZrev, ZW IZr p.1 p.2) ∧ ZS IZr [ZL.H, ZL.h, ZL.one, ZL.one] [ZL.H, ZL.s, ZL.one, ZL.one] ∧
      ¬ ZW IZr [ZL.H, ZL.one, ZL.h] [ZL.H, ZL.one, ZL.one, ZL.t] :=
  Zrev_literal_false

end YAH310

/-- **Remark on the printed form of [YAH, Theorem 3.10]** ($\mathcal T$; the same theorem as `paper_prop_9_4_literal`). -/
theorem paper_rem_yah310_T : ¬ NatQ5.W5.LiteralDP := NatQ5.W5.not_literal

/-- **Remark on the printed form of [YAH, Theorem 3.10]** ($\mathcal T^{\mathrm{rev}}$; the same theorem as
`paper_prop_9_4_literal_rev`). -/
theorem paper_rem_yah310_Trev : ¬ NatQ5.W5.LiteralDPrev := NatQ5.W5.not_literalRev

/-! ## Appendix D: Rigidity of non-negative matrix families -/

/-- **Lemma D.2** (for a strongly connected family, the entries are bounded by `g^(|x| + L)`). -/
theorem paper_lem_D_2 {K : Type*} [Fintype K] [DecidableEq K] (D : Fin 2 → Matrix K K ℕ)
    (hSC : NatQ5.Rigid.SC D) {g : ℝ} (hg : 1 ≤ g)
    (hdiag : ∀ (w : List (Fin 2)) (i : K), NatQ5.Rigid.Dx D w i i ≤ g ^ w.length) :
    ∃ L : ℕ, ∀ (x : List (Fin 2)) (i j : K), NatQ5.Rigid.Dx D x i j ≤ g ^ (x.length + L) :=
  NatQ5.Rigid.entry_bound D hSC hg hdiag

/-- **Lemma D.3** (rigidity is equivalent to a uniform lower bound). -/
theorem paper_lem_D_3 {K : Type*} [Fintype K] [DecidableEq K] (D : Fin 2 → Matrix K K ℕ)
    (hSC : NatQ5.Rigid.SC D) {g : ℝ} (hg : 1 < g)
    (hdiag : ∀ (w : List (Fin 2)) (i : K), NatQ5.Rigid.Dx D w i i ≤ g ^ w.length) :
    NatQ5.Rigid.RigidAt D g ↔
      ∃ c : ℝ, 0 < c ∧ ∀ x, c * g ^ x.length ≤ NatQ5.Rigid.nrm (NatQ5.Rigid.Dx D x) :=
  NatQ5.Rigid.rigidAt_iff_uniform_lower D hSC hg hdiag

/-- **Lemma D.4** (an idempotent of minimal rank in the closure). -/
theorem paper_lem_D_4 {K : Type*} [Fintype K] [DecidableEq K] (D : Fin 2 → Matrix K K ℕ)
    (hSC : NatQ5.Rigid.SC D) {g : ℝ} (hR : NatQ5.Rigid.RigidAt D g) :
    ∃ P ∈ NatQ5.Rigid.Sbar D g, P * P = P ∧ (∀ Y ∈ NatQ5.Rigid.Sbar D g, P.rank ≤ Y.rank) ∧ P ≠ 0 :=
  NatQ5.Rigid.exists_minRank_idem D hSC hR

/-- **Lemma D.4** (the group `𝒢_P` is finite). -/
theorem paper_lem_D_4_finite {K : Type*} [Fintype K] [DecidableEq K] {S : Set (Matrix K K ℝ)}
    {P : Matrix K K ℝ} (hSc : IsCompact S) (hSm : ∀ Y ∈ S, ∀ Z ∈ S, Y * Z ∈ S)
    (hS0 : ∀ Y ∈ S, ∀ (i j : K), 0 ≤ Y i j) (hPS : P ∈ S) (hPP : P * P = P)
    (hPmin : ∀ Y ∈ S, P.rank ≤ Y.rank) : (NatQ5.Rigid.HP P S).Finite :=
  NatQ5.Rigid.HP_finite hSc hSm hS0 hPS hPP hPmin

/-- **Proposition D.5** (a uniformly heavy family of words). -/
theorem paper_prop_D_5 {K : Type*} [Fintype K] [DecidableEq K] (D : Fin 2 → Matrix K K ℕ)
    (hSC : NatQ5.Rigid.SC D) {g : ℝ} (hR : NatQ5.Rigid.RigidAt D g) :
    ∃ (Ψ : List (Fin 2)) (h : ℕ) (a : K) (c : ℝ), 1 ≤ h ∧ 0 < c ∧
      ∀ ε : List (Fin 2),
        c * g ^ (NatQ5.Rigid.heavyWord Ψ h ε).length ≤ NatQ5.Rigid.Dx D (NatQ5.Rigid.heavyWord Ψ h ε) a a :=
  NatQ5.Rigid.heavy_family D hSC hR

/-- **Lemma D.6** (if `r ≥ 8 μ² M²`, the sums of distinct powers `μ^m`, `m < r`, cover all residues modulo `3^M`). -/
theorem paper_lem_D_6 {μ M : ℕ} (hμ : 2 ≤ μ) (hμ3 : Nat.Coprime μ 3) (hM : 1 ≤ M) {r : ℕ}
    (hr : 8 * μ ^ 2 * M ^ 2 ≤ r) (t : ZMod (3 ^ M)) :
    ∃ J ⊆ Finset.range r, ∑ m ∈ J, (μ : ZMod (3 ^ M)) ^ m = t :=
  NatQ5.Rigid.cover hμ hμ3 hM hr t

/-! ## Remark on argument filters after Theorem 3.4 (arctic interpretations) -/

/-- **Remark after Theorem 3.4** (argument filters): the eight forms of Theorems 3.3 and 3.4 with argument filters. -/
theorem paper_rem_3_4_filt :
    DPFilter.ArcticBarrierDPFilt ∧ DPFilter.ArcticBarrierDPrevFilt ∧ DPFilter.ArcticBarrierBZFilt ∧
      DPFilter.ArcticBarrierBZrevFilt ∧ DPFilter.ArcticBarrierHDPFilt ∧ DPFilter.ArcticBarrierHDPrevFilt ∧
      DPFilter.ArcticBarrierHBZFilt ∧ DPFilter.ArcticBarrierHBZrevFilt :=
  DPFilter.arcticBarrierFilt_all

/-- **Remark after Theorem 3.4** (argument filters, below zero, with the weak premise on the pairs). -/
theorem paper_rem_3_4_filtW :
    DPFilter.ArcticBarrierBZFiltW ∧ DPFilter.ArcticBarrierBZrevFiltW ∧ DPFilter.ArcticBarrierHBZFiltW ∧
      DPFilter.ArcticBarrierHBZrevFiltW :=
  DPFilter.arcticBarrierBZFiltW_all

/-- **Remark after Theorem 3.4** ($\mathcal T$, below zero, with the premise `DPFilter.BZPos` on the marked letters). -/
theorem paper_rem_3_4_bzpos_T {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d)
    (hB : DPFilter.BZPos hd J Letter.lft lettersPB)
    (hU : ∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) :=
  DPFilter.bz_fwd_bzpos hd J hB hU hP

/-- **Remark after Theorem 3.4** ($\mathcal T^{\mathrm{rev}}$, below zero, with the premise `DPFilter.BZPos`). -/
theorem paper_rem_3_4_bzpos_Trev {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d)
    (hB : DPFilter.BZPos hd J Letter.rgt lettersPDrev)
    (hU : ∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) :=
  DPFilter.bz_rev_bzpos hd J hB hU hP

end Collatz.Arctic.Paper
