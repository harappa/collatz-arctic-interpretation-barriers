# Natural-number and arctic matrix interpretations alone make no progress, in any dimension, on the Collatz rewriting system

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23147025.svg)](https://doi.org/10.5281/zenodo.23147025)

**The paper continues** *Dimension-free barriers for matrix interpretations of the Collatz rewriting system, and the maximal one-class weakenings of the modulo-8 conjectures of Yolcu, Aaronson and Heule provable by finite abstractions* (Part II of two companion papers; Zenodo, doi:[10.5281/zenodo.23081491](https://doi.org/10.5281/zenodo.23081491); Lean code and computations at https://github.com/harappa/collatz-matrix-interpretation-barriers) **and cites Part I**, *Expanding cycles are not enough: a dichotomy for termination certificates of generalized Collatz maps* (Zenodo, doi:[10.5281/zenodo.23081447](https://doi.org/10.5281/zenodo.23081447); Lean code at https://github.com/harappa/collatz-termination-certificate-dichotomy). Its proofs use neither paper, and this formalization depends on Mathlib only.

This repository contains the Lean 4 formalization and the computations accompanying the preprint *Natural-number and
arctic matrix interpretations alone make no progress, in any dimension, on the Collatz rewriting system* by Hiroyuki
Nashida (Zenodo, 2026, doi:[10.5281/zenodo.23147025](https://doi.org/10.5281/zenodo.23147025)). It formalizes the
main barrier theorems of the paper (the results on transformations of Section 8.2 are computer-assisted): for
natural-number matrix interpretations in the form of Endrullis, Waldmann and Zantema, and in the corner form of
Hofbauer and Waldmann, of the string rewriting system $\mathcal T$ (`collatz-T` of the Termination Problem Database)
and its reversal; and for arctic interpretations, of $\mathcal T$ and $\mathcal H$ (`collatz-T-5or7mod8`, for the map
`H(n) = 3n/4` for `n = 0 mod 4`, `H(n) = (9n+1)/8` for `n = 7 mod 8`), their reversals, and a 12-rule system $R_H$
for the map $H$. It also contains the value-level cores of the proofs (max-plus automata for arctic interpretations,
automata over the natural numbers for natural-number interpretations), the probabilistic tools, the rigidity of
non-negative matrix families, the boundary cases, argument filters, the checks of non-vacuity and the natural-number
example of Proposition 9.5. The theorems use only Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), with no project-specific axioms or unproved hypotheses. The only dependency is Mathlib.

## Paper

- **Author:** Hiroyuki Nashida
- **Title:** Natural-number and arctic matrix interpretations alone make no progress, in any dimension, on the
  Collatz rewriting system
- **Preprint:** Zenodo, 2026
- **DOI:** [10.5281/zenodo.23147025](https://doi.org/10.5281/zenodo.23147025)
- **Lean formalization and computations:** this repository (Section 14, Appendix A "Lean statements" and Appendix C
  "Computations" of the paper)
- **Continues (Part II of two companion papers):** *Dimension-free barriers for matrix interpretations of the Collatz rewriting system, and the maximal one-class weakenings of the modulo-8 conjectures of Yolcu, Aaronson and Heule provable by finite abstractions*, Zenodo, 2026, doi:[10.5281/zenodo.23081491](https://doi.org/10.5281/zenodo.23081491); Lean code and computations: https://github.com/harappa/collatz-matrix-interpretation-barriers
- **Cites (Part I of two companion papers):** *Expanding cycles are not enough: a dichotomy for termination certificates of generalized Collatz maps*, Zenodo, 2026, doi:[10.5281/zenodo.23081447](https://doi.org/10.5281/zenodo.23081447); Lean code: https://github.com/harappa/collatz-termination-certificate-dichotomy
- **Dependence:** none; the proofs of the paper use neither companion paper, and this formalization does not use
  their Lean code.

Revision r3 (October 7, 2026). This repository accompanies revision r3 of the paper; the revision number is
incremented with every revision of the paper and of this repository (revisions r1 and r2 were not published).
The files were prepared from the author's working repository (not public) at commit `e80eea2b10`; the Lean code
there is identical to the code here after removing comments.

## Abstract

Yolcu, Aaronson and Heule encoded the Collatz map as an $11$-rule string rewriting system, the problem collatz-T of
the Termination Problem Database; they suggested proving that no matrix or arctic interpretation establishes its
termination, and proved such a barrier for natural-number matrix interpretations of Zantema's unary encoding. We show
that natural-number matrix interpretations in the form of Endrullis, Waldmann and Zantema, and arctic interpretations,
applied on their own, make no progress on collatz-T in any dimension. A natural-number matrix interpretation of
collatz-T with all top-left entries at least $1$ that weakly orients all rules strictly orients none of them, and so
does an arctic interpretation over $\mathbb N \cup \{-\infty\}$ with finite top-left entries, for collatz-T and also
for the system of their modulo-$8$ conjecture; hence rule removal with these interpretations alone removes no rule at
any stage. The same holds for the reversed systems and, for collatz-T, for the corner form of Hofbauer and Waldmann.
Without the condition on the top-left entries, natural-number interpretations in the form of Endrullis, Waldmann and
Zantema remove no rule in the top forms of Yolcu, Aaronson and Heule, and neither natural-number reduction pairs nor
arctic reduction pairs over the natural numbers or below zero remove a pair of the essential strongly connected
component of the dependency pair problems; for collatz-T the arctic barrier persists after root labelling, full tiling
of widths $2$ and $3$, and one step of narrowing. The proofs reduce everything to automata reading binary digits along
orbits; for natural numbers, weak orientation forces their lifts modulo $3$ to have only $0/1$ components. The main
theorems are formalized in Lean 4, using only its three standard axioms; the results on transformations are
computer-assisted. The general core form of matrix interpretations, lexicographic comparisons, other semirings, and
pipelines in which other techniques act first are not covered. No result here settles the Collatz conjecture.

*What is verified in Lean.* Kernel-checked are Lemma 2.3, the results of Sections 3-7 (including the boundary results
of Section 4), Theorem 9.2, Propositions 9.4 and 9.5, the numbered results of Sections 10-13 (including Corollary
10.12), the remark on [YAH, Theorem 3.10] in Section 13.2, Appendix B (probabilistic tools) and Appendix D
(rigidity), with these exceptions: Corollaries 3.2, 3.5 and 9.3, the remark after Theorem 3.6, the parts of the
remarks after Theorem 3.4 that have no Lean name, real entries (Section 4), Lemma 5.3, the remark on many-sorted
interpretations (Section 9), Lemma 12.15 (iii) in its general form, and the observations after Propositions 13.3 and
13.4 are derived in a few lines from kernel-checked results, and Example 4.7 and Question 4.4 are computations.
Corollary 8.1 is also derived in a few lines from kernel-checked results. The results of Section 8.2 (the transformed
systems) are computer-assisted: the general lemmas (Lemma 5.6 and Corollary 8.1) are in Lean, and their conditions
for the transformed systems rest on written proofs and on the computations in `computations/`; they are not
kernel-checked as a whole. See "Scope of the verification" below.

## Changes from revision r2 (not published)

- New: natural-number matrix interpretations (Sections 9-13 and Appendix D of the paper), in the files
  `CollatzProof/Arctic/Nat/` and `CollatzProof/Arctic/Paper5.lean`; argument filters for the arctic reduction pairs of
  Theorems 3.3 and 3.4 (the remarks after Theorem 3.4), in the files `CollatzProof/Arctic/DPFilter*.lean`.
- New: Corollary 10.12, the corner form of Hofbauer and Waldmann for $\mathcal T$ and its reversal
  (`paper_cor_10_12`, `paper_cor_10_12_rev`; files `CollatzProof/Arctic/Nat/HWCorner.lean` and `Nat/NonVacuityHW.lean`).
- Renumbering: Sections 9 (Formalization) and 10 (Related work and open problems) of revision r2 are Sections 14 and
  15, Proposition 10.1 is Proposition 9.5, and Tables 2-6 are Tables 3-7. The Lean names `paper_prop_10_1_*` are now
  `paper_prop_9_5_*`; the theorems they restate keep their names `NatExample.prop_10_1_*`.
- The verification class "kernel-checked" now says precisely which Mathlib declarations the kernel re-check replays:
  those of the Mathlib modules imported by the root module.

## The main statements

The arctic semiring $\mathbb A_{\mathbb N}$ is the type `Arc`, a copy of `WithBot ℕ` with addition `max` and
multiplication `+`; its zero `0` is $-\infty$ and its one `1` is the finite value $0$, and `Arc.fin k` is the finite
value $k$. Letters are `f`, `t` (binary digits), `d0`, `d1`, `d2` (ternary digits), `lft` and `rgt` (the left and right
end markers). An interpretation `I : Interp d` assigns a `d × d` matrix to every letter, and `ev I w` is the product
of the matrices of the letters of `w`. Output of `#print` in `verify/Probe.lean`:

```lean
def Collatz.Arctic.Weak : {d : ℕ} → Collatz.Arctic.Interp d → Collatz.Arctic.Rule → Prop :=
fun {d} I ρ => ∀ (i j : Fin d), Collatz.Arctic.ev I ρ.rhs i j ≤ Collatz.Arctic.ev I ρ.lhs i j
def Collatz.Arctic.Strict : {d : ℕ} → Collatz.Arctic.Interp d → Collatz.Arctic.Rule → Prop :=
fun {d} I ρ =>
  ∀ (i j : Fin d),
    Collatz.Arctic.ev I ρ.rhs i j < Collatz.Arctic.ev I ρ.lhs i j ∨
      Collatz.Arctic.ev I ρ.lhs i j = 0 ∧ Collatz.Arctic.ev I ρ.rhs i j = 0
def Collatz.Arctic.Fin00 : {d : ℕ} → 0 < d → Collatz.Arctic.Interp d → Prop :=
fun {d} hd I => ∀ (s : Collatz.Arctic.Letter), I s ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0
def Collatz.Arctic.ArcticBarrierST : Prop :=
∀ (d : ℕ) (hd : 0 < d) (I : Collatz.Arctic.Interp d),
  Collatz.Arctic.Fin00 hd I →
    (∀ ρ ∈ Collatz.Arctic.rulesST, Collatz.Arctic.Weak I ρ) → ∀ ρ ∈ Collatz.Arctic.rulesST, ¬Collatz.Arctic.Strict I ρ
```

In words, `ArcticBarrierST` (Theorem 3.1 for $\mathcal T$, proved as `Collatz.Arctic.Paper.paper_thm_3_1_T`): for
every dimension `d` and every arctic interpretation whose top-left entries are all finite, if it weakly orients all 11
rules `rulesST` of `collatz-T` (entrywise $\ge$), then it strictly orients none of them (entrywise $\gg$: greater, or
both $-\infty$). The statements for $\mathcal H$ (`HTPDB.ArcticBarrierHT`) and $R_H$ (`RH.ArcticBarrierRH`, for the ten
used rules `RH.usedRH`) have the same form. The dependency pair statements (`ArcticBarrierDP`, `ArcticBarrierBZ` and
their analogues) use arctic linear functions `AffFun` and compare first rows (`WeakTop`, `StrictTop`) on the pairs
and all coefficients (`WeakA`) on the usable rules; they are printed in full by `verify/Probe.lean`, together with
the rule lists, the pairs and the usable rules. Corollary 3.8 extends the rule removal statements to arctic linear
functions `x ↦ M_s ⊗ x ⊕ c_s` with arbitrary absolute parts, compared at every point (`Affine.AffBarrierFin`), when all
top-left entries `(M_s)₀₀` are finite; Proposition 4.8 shows that this finiteness cannot be weakened to somewhere
finiteness (`Affine.SomeFinOrientable`). Appendix A of the paper reproduces these definitions. The frozen
statements depend only on the rules, the pairs, the usable rules, the type of letters and the arctic definitions; the
models of the maps occur only inside the proofs.

**Natural-number matrix interpretations** (Theorem 9.2). An interpretation `I : Letter → NAff d` assigns to every
letter $s$ a matrix $M_s$ over $\mathbb N$ and a vector $v_s$, the map $y \mapsto M_s y + v_s$; a string is
interpreted by the composition of the maps of its letters. From the frozen file `Nat/Statement.lean` (namespace
`Collatz.Arctic.NatQ5`; the code without comments and without the decidability instances; `verify/Probe.lean` prints
these definitions):

```lean
structure NAff (d : ℕ) where
  M : Matrix (Fin d) (Fin d) ℕ
  v : Fin d → ℕ
def NAff.app {d : ℕ} (F : NAff d) (y : Fin d → ℕ) : Fin d → ℕ := F.M *ᵥ y + F.v
def NAff.comp {d : ℕ} (F G : NAff d) : NAff d := ⟨F.M * G.M, F.M *ᵥ G.v + F.v⟩
def NAff.id (d : ℕ) : NAff d := ⟨1, 0⟩
def evN {d : ℕ} (I : Letter → NAff d) : Word → NAff d
  | [] => NAff.id d
  | s :: w => (I s).comp (evN I w)
def NWeak {d : ℕ} (I : Letter → NAff d) (ρ : Rule) : Prop :=
  (∀ i j, (evN I ρ.rhs).M i j ≤ (evN I ρ.lhs).M i j) ∧ ∀ i, (evN I ρ.rhs).v i ≤ (evN I ρ.lhs).v i
def NStrict {d : ℕ} [NeZero d] (I : Letter → NAff d) (ρ : Rule) : Prop :=
  NWeak I ρ ∧ (evN I ρ.rhs).v 0 < (evN I ρ.lhs).v 0
def NMono {d : ℕ} [NeZero d] (I : Letter → NAff d) : Prop := ∀ s, 1 ≤ (I s).M 0 0
def NatBarrierST : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), NMono I → (∀ ρ ∈ rulesST, NWeak I ρ) →
    ∀ ρ ∈ rulesST, ¬ NStrict I ρ
```

In words, `NatBarrierST` (Theorem 9.2 (i) for $\mathcal T$, proved as `Collatz.Arctic.Paper.paper_thm_9_2_T`): for
every dimension `d ≥ 1` (`[NeZero d]`) and every natural-number matrix interpretation with all top-left entries
`(M_s)₀₀ ≥ 1` (monotone), if it weakly orients all 11 rules (matrices and vectors entrywise $\ge$), then it strictly
orients none of them (strictly: in addition a larger first component of the vector). The indices run from 1 in the
paper and from 0 in Lean. The six statements of Theorem 9.2 are in the frozen files `Nat/Statement.lean`,
`Nat/StatementRev.lean` and `Nat/StatementDP.lean`:

| Statement (namespace `Collatz.Arctic.NatQ5`) | Theorem 9.2 | Premises | Conclusion |
|---|---|---|---|
| `NatBarrierST` | (i), $\mathcal T$ | `NMono`; all 11 rules `rulesST` weakly oriented | no rule of `rulesST` strictly oriented |
| `NatBarrierSTrev` | (i), $\mathcal T^{\mathrm{rev}}$ | `NMono`; all rules of `rulesSTrev` weakly oriented | no rule of `rulesSTrev` strictly oriented |
| `NatBarrierSTB` | (ii), $\mathcal T$ | all rules of `rulesST` weakly oriented (no monotonicity) | none of the three left-end rules `rulesSTB` strictly oriented |
| `NatBarrierSTrevTop` | (ii), $\mathcal T^{\mathrm{rev}}$ | all rules of `rulesSTrev` weakly oriented (no monotonicity) | neither `.f -> .` nor `.t -> .2` (`rulesSTrevTop`) strictly oriented |
| `NatBarrierDP` | (iii), $\mathcal T$ | `J : DLetter → NAff d` (marked letters too, no monotonicity); the usable rules `usableST` entrywise and the pairs `pairsPB` in the first component (`NWeakTopD`) weakly oriented | no pair of `pairsPB` strictly oriented in the first component (`NStrictTopD`) |
| `NatBarrierDPrev` | (iii), $\mathcal T^{\mathrm{rev}}$ | the same with `usableSTrev` and `pairsPDrev` | no pair of `pairsPDrev` strictly oriented in the first component |

All six are proved without hypotheses (`NatQ5.allBarriers_final`, and `NatQ5.natBarrierST_final` and its five
analogues), and restated as `paper_thm_9_2_T`, `paper_thm_9_2_Trev`, `paper_thm_9_2_B`, `paper_thm_9_2_revTop`,
`paper_thm_9_2_DP`, `paper_thm_9_2_DPrev` and, together, `paper_thm_9_2`. The comparisons agree with the order of
Yolcu, Aaronson and Heule, and `NMono` is equivalent to their extended monotonicity (`NatQ5.nweak_iff_forall`,
`NatQ5.nstrict_iff_forall`, `NatQ5.nmono_iff_extMono`). Like the arctic statements, these statements depend only on
the rules, the pairs, the usable rules, the type of letters and the definitions above. The decomposition data of
Definition 12.9 and the statement of Proposition 12.11 (`Nat/W3Decomp.lean`) were also fixed before their proof, and
their code was not changed afterwards.

Corollary 10.12 (the corner form of Hofbauer and Waldmann) is stated for families of natural-number matrices on a
finite type of indices with a set `J` of indices whose diagonal entries are at least 1 for every letter
(`NatQ5.HW.HWBarrierST`, `NatQ5.HW.HWBarrierSTrev` in `Nat/HWCorner.lean`): if all 11 rules are weakly oriented
entrywise, no rule decreases an entry of `J × J`. These statements are not frozen; `verify/Probe.lean` prints them.
The frozen `NatBarrierST` and `NatBarrierSTrev` are special cases (`NatQ5.HW.natBarrierST_of_hw`,
`NatQ5.HW.natBarrierSTrev_of_hw`).

Proposition 9.5 uses natural-number affine interpretations in the conventions of Paper II (`NatExample.NAff`, a
matrix over $\mathbb N$ and a vector for every letter, composed along a string by `NatExample.evN`; weak orientation
`NatExample.NWeak` compares matrices and vectors entrywise, and strict orientation `NatExample.NStrict` asks in
addition for a strictly larger first component of the vector), with the same definitions as above in the namespace
`NatExample`. Its statements `paper_prop_9_5_*` mention the interpretation `NatExample.interp` itself, the canonical strings and the
maps $T$ and $H$; `verify/Probe.lean` prints all of these definitions.

The statements with argument filters (`DPFilterStatement.lean`, namespace `Collatz.Arctic.DPFilter`; the remarks
after Theorem 3.4) were written later, as separate definitions, without changing the frozen arctic statements: an
argument filter drops arguments of unmarked letters, whose matrices are then zero (all entries $-\infty$), and the
usable rules are those of the filter (`NatQ5.W5.usableFilt`). After an internal independent review the file
`DPFilterStatement.lean` was frozen as well, and its code was not changed afterwards. Its meaning also depends on
definitions that are not frozen: `NatQ5.W5.usableFilt` (`Nat/BridgeDPFilter.lean`) and the reversed rules
`HTPDB.NonVacuityH.rulesHTrev`; `verify/Probe.lean` prints them, with the auxiliary definitions of `usableFilt`. The
natural-number forms of Proposition 13.4 (`NatQ5.NatBarrierDPFilt`, `NatQ5.NatBarrierDPrevFilt`) use the same
`usableFilt`.

In the frozen files, as in all files, only the comments were translated; in revision r3 some translated comments of
the frozen files were corrected after an internal review. Their code is identical to that of the originals, and the
originals have not changed since they were frozen.

## Results of the paper and their names in Lean

The module `CollatzProof.Arctic.Paper` (files `Paper.lean`, `Paper2.lean`, `Paper3.lean`, `Paper4.lean`,
`Paper5.lean`) restates the results of the paper under names of the form
`paper_<kind>_<section>_<number>[_<target>]`, where the target is `T` ($\mathcal T$), `H` ($\mathcal H$), `RH`
($R_H$), or one of these with `rev` (the reversal) or `sub`; unnumbered remarks have the kind `rem`
(`paper_rem_3_4_*` after Theorem 3.4, `paper_rem_yah310_*` in Section 13.2). Most of these theorems are aliases of
theorems elsewhere in `CollatzProof/Arctic/`, with the type written out; `paper_thm_3_1_Hrev` and the six theorems
`paper_thm_3_6_*` are proved there by combining theorems of other files, and `paper_thm_10_11`,
`paper_thm_10_11_nat`, `paper_thm_10_11_gen`, the six theorems `paper_prop_13_3_*`, `paper_prop_13_4` and
`paper_prop_13_4_rev` apply one theorem to another in one line. The other numbered results of Sections 10-13 and
Appendix D are kernel-checked under their own names, which the formal status lines of the paper give (Lemma 12.15
(iii) only in the setting where it is used; see "Scope of the verification"). The
verification classes in the last column are those of Table 5 of the paper, explained in the section "Scope of the
verification". [YAH], [EWZ08] and [HW06] are the papers of Yolcu, Aaronson and Heule (J. Automat. Reason. 67 (2023)),
of Endrullis, Waldmann and Zantema (J. Automat. Reason. 40 (2008)) and of Hofbauer and Waldmann (RTA 2006) cited in
the paper.

| Paper | Content | Lean (namespace `Collatz.Arctic.Paper`) | Verification class |
|---|---|---|---|
| Lemma 2.3 | Canonical derivations of T, H and R_H | `paper_lem_2_3_T`, `paper_lem_2_3_H`, `paper_lem_2_3_RH` | kernel-checked |
| Theorem 3.1 | Rule removal: no arctic interpretation that weakly orients all rules (for R_H: the used rules) strictly orients one of them; T, H, R_H, subsystems of R_H; reversed T, H, R_H | `paper_thm_3_1_T`, `paper_thm_3_1_H`, `paper_thm_3_1_RH`, `paper_thm_3_1_RHsub`, `paper_thm_3_1_Trev`, `paper_thm_3_1_Hrev`, `paper_thm_3_1_RHrev` | kernel-checked |
| Theorem 3.3 | Dependency pairs, reduction pairs over the arctic naturals: T, H and their reversals | `paper_thm_3_3_T`, `paper_thm_3_3_Trev`, `paper_thm_3_3_H`, `paper_thm_3_3_Hrev` | kernel-checked |
| Theorem 3.4 | Dependency pairs, reduction pairs below zero: T, H and their reversals | `paper_thm_3_4_T`, `paper_thm_3_4_Trev`, `paper_thm_3_4_H`, `paper_thm_3_4_Hrev` | kernel-checked |
| Remarks after Theorem 3.4 | Argument filters: the eight forms of Theorems 3.3 and 3.4 with argument filters (T, H and their reversals), and the four below-zero forms under the weaker premise `DPFilter.BZPos`; Theorem 3.4 for T and its reversal under the premise `DPFilter.BZPos` | `paper_rem_3_4_filt`, `paper_rem_3_4_filtW`, `paper_rem_3_4_bzpos_T`, `paper_rem_3_4_bzpos_Trev` | kernel-checked (filters that keep the argument of the marked symbol); the rest of the remarks is derived in a few lines from kernel-checked results |
| Theorem 3.6 | No ranking function computed by an arctic automaton with entries in the arctic integers from the binary digits (T, H): `_Z` reading from the most significant end, `_Zlsb` from the least significant end; `paper_thm_3_6_T`, `paper_thm_3_6_H`: the special case of weights in the arctic naturals | `paper_thm_3_6_T_Z`, `paper_thm_3_6_H_Z`, `paper_thm_3_6_T_Zlsb`, `paper_thm_3_6_H_Zlsb`, `paper_thm_3_6_T`, `paper_thm_3_6_H` | kernel-checked |
| Proposition 3.7 | The carry rules are used quadratically often | `paper_prop_3_7_T`, `paper_prop_3_7_H` | kernel-checked |
| Corollary 3.8 | Absolute parts: arctic linear functions with arbitrary absolute parts and all top-left entries finite, compared at every point, strictly orient no rule if they weakly orient all rules (T, H, the used rules of R_H, and the reversals) | `paper_cor_3_8_T`, `paper_cor_3_8_Trev`, `paper_cor_3_8_H`, `paper_cor_3_8_Hrev`, `paper_cor_3_8_RH` | kernel-checked |
| Proposition 4.1 | The dependency pair theorems under weaker premises (T) | `paper_prop_4_1_DPw`, `paper_prop_4_1_DPrevw`, `paper_prop_4_1_BZf`, `paper_prop_4_1_BZrevf`, `paper_prop_4_1_BZw`, `paper_prop_4_1_BZrevw` | kernel-checked |
| Proposition 4.2 | The premises cannot be weakened further | `paper_prop_4_2_markOnly`, `paper_prop_4_2_markOnly_rev`, `paper_prop_4_2_noMark`, `paper_prop_4_2_noMark_rev`, `paper_prop_4_2_noMark_BZ`, `paper_prop_4_2_noMark_BZrev` | kernel-checked |
| Proposition 4.3 | For all 12 rules of R_H (and for the used rules with L0 -> L or Lf -> L) the barrier fails | `paper_prop_4_3`, `paper_prop_4_3_l0`, `paper_prop_4_3_lf` | kernel-checked |
| Proposition 4.5 | The barrier depends on the dynamics: counterexamples for subsystems, the two commutation rules, strict orientation is possible otherwise (T, H, R_H) | `paper_prop_4_5_AB`, `paper_prop_4_5_DA`, `paper_prop_4_5_DP_A`, `paper_prop_4_5_DPrev_A`, `paper_prop_4_5_BZ_A`, `paper_prop_4_5_BZrev_A`, `paper_prop_4_5_DPrev_one`, `paper_prop_4_5_swap`, `paper_prop_4_5_strict_ST`, `paper_prop_4_5_strict_DP`, `paper_prop_4_5_strict_DPrev`, `paper_prop_4_5_strict_BZ`, `paper_prop_4_5_strict_BZrev`, `paper_prop_4_5_H_AB`, `paper_prop_4_5_H_DA`, `paper_prop_4_5_H_DP_A`, `paper_prop_4_5_H_BZ_A`, `paper_prop_4_5_H_DPrev_A`, `paper_prop_4_5_H_BZrev_A`, `paper_prop_4_5_H_strict`, `paper_prop_4_5_H_strict_DP`, `paper_prop_4_5_H_strict_DPrev`, `paper_prop_4_5_H_strict_BZ`, `paper_prop_4_5_H_strict_BZrev`, `paper_prop_4_5_RH_noDyn`, `paper_prop_4_5_RH_X`, `paper_prop_4_5_RH_noLeft`, `paper_prop_4_5_RH_strict` | kernel-checked |
| Proposition 4.6 | The form (DP_min) without conditions on f and t, and Collatz reachability | `paper_prop_4_6`, `paper_prop_4_6_rev`, `paper_prop_4_6_contra`, `paper_prop_4_6_rev_contra` | kernel-checked |
| Proposition 4.8 | Somewhere finite arctic linear functions with absolute parts can strictly orient a rule of T or H, the others weakly oriented, if and only if it is not a left-end rule | `paper_prop_4_8_T`, `paper_prop_4_8_H` | kernel-checked |
| Lemma 5.1 | Weak orientation does not increase Phi in context; strict orientation decreases it by at least 1 | `paper_lem_5_1_weak`, `paper_lem_5_1_strict` | kernel-checked |
| Theorem 5.5 | The value-level statement AutoCore holds for T and for H | `paper_thm_5_5_T`, `paper_thm_5_5_H` | kernel-checked |
| Lemma 5.6 | The simulation lemma (arctic naturals and below zero; family forms) | `paper_lem_5_6`, `paper_lem_5_6_Z`, `paper_lem_5_6_family`, `paper_lem_5_6_familyZ` | kernel-checked |
| Lemma 6.2 | Idempotents of the minimal ideal of a Boolean matrix semigroup | `paper_lem_6_2`, `paper_lem_6_2_exists` | kernel-checked |
| Lemma 6.3 | Carry-over and stay | `paper_lem_6_3`, `paper_lem_6_3_stay` | kernel-checked |
| Lemma 6.5 | Upper bound from window frequencies | `paper_lem_6_5` | kernel-checked |
| Lemma 6.6 | Lower bound for sequences of nearly uniform segments | `paper_lem_6_6` | kernel-checked |
| Proposition 6.7 | Uses of the left-end rules | `paper_prop_6_7_left` | kernel-checked |
| Theorem 6.8 | Assembly: AutoCore from the three finite statements | `paper_thm_6_8` | kernel-checked |
| Lemma 7.4 | The canonical derivations of R_H are lifts of those of H | `paper_lem_7_4`, `paper_lem_7_4_count` | kernel-checked |
| Proposition 7.5 | AutoCore for R_H from AutoCore for H | `paper_prop_7_5` | kernel-checked |
| Corollary 8.1 | Non-increase along the family suffices | `paper_cor_8_1` | derived in a few lines from kernel-checked results: `paper_cor_8_1` (one rule) is kernel-checked, and the form of the paper combines it with the minimal rates and window frequencies |
| Theorem 9.2 | Natural-number matrix interpretations: (i) rule removal, monotone (T, reversed T); (ii) top forms, without monotonicity (the left-end rules of T; `.f -> .` and `.t -> .2` of reversed T); (iii) dependency pairs, the essential SCC in the first component (T, reversed T); all six together | `paper_thm_9_2_T`, `paper_thm_9_2_Trev`, `paper_thm_9_2_B`, `paper_thm_9_2_revTop`, `paper_thm_9_2_DP`, `paper_thm_9_2_DPrev`; together `paper_thm_9_2` | kernel-checked |
| Proposition 9.4 | The boundary of Theorem 9.2: (i) every rule is strictly oriented, in dimension 2, if one other rule need not be weakly oriented, and the statement for reversed T fails without one rule; (ii) without monotonicity the form (i) fails, and in dimension 1 every rule except the top rules is strictly oriented; (iii) every pair alone is strictly oriented, and the conclusion fails without the weak orientation of the other pairs (the printed form of [YAH, Theorem 3.10]) or of one usable rule | `paper_prop_9_4_drop`, `paper_prop_9_4_drop_rev`, `paper_prop_9_4_noMono`, `paper_prop_9_4_noMono_nonB`, `paper_prop_9_4_noMono_rev`, `paper_prop_9_4_noMono_nonTop`, `paper_prop_9_4_pair`, `paper_prop_9_4_literal`, `paper_prop_9_4_literal_rev`, `paper_prop_9_4_dropU`, `paper_prop_9_4_dropU_rev` | kernel-checked |
| Proposition 9.5 | A natural-number affine interpretation of dimension 4 weakly orients all rules of T, H and R_H, strictly orients none, has values that do not increase along T and H, and has a residue component of growth rate log 2 violating the primitivity hypothesis (P) of Paper II; the remark after it (the form of Paper I) | `paper_prop_9_5_T`, `paper_prop_9_5_H`, `paper_prop_9_5_RH`; remark: `paper_prop_9_5_remark` | kernel-checked |
| Lemma 10.2 | The identity for one step; with the 11 rules weakly oriented the value does not increase along a step of T; with monotonicity, each use of a strictly oriented rule decreases it by at least 1 | `paper_lem_10_2_step`, `paper_lem_10_2_T`, `paper_lem_10_2_orbit` | kernel-checked |
| Lemma 10.3 | The value of a canonical string is the value of the value automaton | `paper_lem_10_3` | kernel-checked |
| Lemma 10.4 | Transposition: values and orientations for reversed T through the transposed homogeneous matrices | `paper_lem_10_4`, `paper_lem_10_4_weak`, `paper_lem_10_4_strict` | kernel-checked |
| Lemma 10.5 | Value embedding: a source and a sink give a monotone interpretation that weakly orients the 11 rules and strictly orients none | `paper_lem_10_5_mono`, `paper_lem_10_5_weak`, `paper_lem_10_5_phi`, `paper_lem_10_5_not_strict` | kernel-checked |
| Lemma 10.6 | The lift modulo 3: the value identity, and (M) gives (M_3) | `paper_lem_10_6`, `paper_lem_10_6_mono3` | kernel-checked |
| Lemma 10.7 | A component with a killing word is killed by u* | `paper_lem_10_7` | kernel-checked |
| Theorem 10.8 | Under (M_3) and (Z_3), the diagonal growth on the relevant indices is at most 1 and all components are 0/1 | `paper_thm_10_8`, `paper_thm_10_8_gdiag` | kernel-checked |
| Corollary 10.9 | Only 0/1 components: lifts of value automata with (M), families of matrices with (G1), natural-number interpretations that weakly orient the 11 rules | `paper_cor_10_9`, `paper_cor_10_9_gen`, `paper_cor_10_9_nat` | kernel-checked |
| Theorem 10.10 | Values and uses on 0/1 automata | `paper_thm_10_10` | kernel-checked |
| Theorem 10.11 | The value-level core for value automata with (M); for families with (G1) and for natural-number interpretations without monotonicity | `paper_thm_10_11`, `paper_thm_10_11_nat`, `paper_thm_10_11_gen` | kernel-checked |
| Corollary 10.12 | The corner form of [HW06]: a family of natural-number matrices whose diagonal entries at a set J of indices are at least 1 and that weakly orients all 11 rules entrywise decreases no rule at an entry of J × J (T, reversed T) | `paper_cor_10_12`, `paper_cor_10_12_rev` | kernel-checked |
| Lemma 11.1 | Splitting paths into segments of length q | `paper_lem_11_1` | kernel-checked |
| Corollary 11.2 | A polynomial bound for the values when the diagonal growth is at most G | `paper_cor_11_2` | kernel-checked |
| Lemma 11.3 | If G > 1, some set S = scc(i) has a uniform lower bound ‖N^S_x‖ ≥ c_0 G^\|x\| with c_0 > 0; hence it is strongly connected and rigid at G, and it has an internal edge | `paper_lem_11_3` | kernel-checked |
| Corollary 11.4 | A heavy family of words | `paper_cor_11_4` | kernel-checked |
| Theorem 11.8 | Diagonal Lyapunov comparison | `paper_thm_11_8` | kernel-checked |
| Proposition 11.12 | Comparison along shrinking chains | `paper_prop_11_12` | kernel-checked |
| Proposition 11.13 | Under (R), (M_3) and (Z_3), the diagonal growth is at most 1 | `paper_prop_11_13` | kernel-checked |
| Lemma 12.3 | Part (i): an admissible idempotent word kills scc(q) for every relevant index q outside Q_s | `paper_lem_12_3` | kernel-checked |
| Proposition 12.11 | Existence of decomposition data, and the lower bound for t_0 | `paper_prop_12_11`, `paper_prop_12_11_T0` | kernel-checked |
| Theorem 12.13 | Law of large numbers for a finite DFA: closeness to the stationary mean on average, and sums over intervals from window frequencies | `paper_thm_12_13_mean`, `paper_thm_12_13_win` | kernel-checked |
| Corollary 12.18 | The event for the numbers of uses of the 11 rules | `paper_cor_12_18` | kernel-checked |
| Proposition 12.19 | The top window of the end point | `paper_prop_12_19` | kernel-checked |
| Proposition 12.24 | Few long runs of misses | `paper_prop_12_24` | kernel-checked |
| Proposition 12.26 | The tail at the starting point | `paper_prop_12_26` | kernel-checked |
| Proposition 12.27 | An upper bound at the starting point | `paper_prop_12_27` | kernel-checked |
| Proposition 12.28 | A lower bound at the end point | `paper_prop_12_28` | kernel-checked |
| Lemma 12.30 | Case A gives the conclusion of Theorem 10.10 | `paper_lem_12_30` | kernel-checked |
| Proposition 12.31 | Case B does not occur | `paper_prop_12_31` | kernel-checked |
| Lemma 13.1 | The mirrored canonical derivation of reversed T; strictly oriented top rules decrease the value at each use, without monotonicity (T, reversed T) | `paper_lem_13_1_rev`, `paper_lem_13_1_top`, `paper_lem_13_1_revTop` | kernel-checked |
| Lemma 13.2 | Theorem 9.2 (iii) is equivalent to (ii) (T, reversed T) | `paper_lem_13_2`, `paper_lem_13_2_rev` | kernel-checked |
| Proposition 13.3 | Forms of comparison that follow from Theorem 9.2 (iii): the order of [YAH], the scalar form of [EWZ08, §5], comparison in one component (T, reversed T) | `paper_prop_13_3_full`, `paper_prop_13_3_full_rev`, `paper_prop_13_3_scalar`, `paper_prop_13_3_scalar_rev`, `paper_prop_13_3_row`, `paper_prop_13_3_row_rev` | kernel-checked |
| Proposition 13.4 | Argument filters for natural-number reduction pairs (T, reversed T) | `paper_prop_13_4`, `paper_prop_13_4_rev` | kernel-checked |
| Remark in Section 13.2 | The printed form of [YAH, Theorem 3.10]: an interpretation of dimension 2 weakly orients all rules of Zantema's system and strictly orients one pair without weakly orienting the other (also for the reversed system); for T and reversed T the printed form fails as well | `paper_rem_yah310_Z`, `paper_rem_yah310_Zrev`, `paper_rem_yah310_T`, `paper_rem_yah310_Trev` | kernel-checked |
| Theorem B.1 | Reduction to minimal expected rates | `paper_thm_B_1`, `paper_thm_B_1_at` | kernel-checked |
| Proposition B.2 | Sharpness | `paper_prop_B_2` | kernel-checked |
| Theorem B.3 | MinRate, without Kingman's theorem | `paper_thm_B_3`, `paper_thm_B_3_spr` | kernel-checked |
| Corollary B.4 | HSP, the finite form used in Section 6 | `paper_cor_B_4` | kernel-checked |
| Theorem B.7 | Top digits of Terras residues (HKeyTop) | `paper_thm_B_7` | kernel-checked |
| Theorem B.8 | Window frequencies (HTerrasWin) | `paper_thm_B_8`, `paper_thm_B_8_of_key` | kernel-checked |
| Proposition B.9 | Equidistribution of the walk of block boundaries | `paper_prop_B_9` | kernel-checked |
| Lemma D.2 | For a strongly connected family, the entries are bounded by g^(\|x\| + L) | `paper_lem_D_2` | kernel-checked |
| Lemma D.3 | Rigidity is equivalent to a uniform lower bound | `paper_lem_D_3` | kernel-checked |
| Lemma D.4 | An idempotent of minimal rank in the closure; the group G_P is finite | `paper_lem_D_4`, `paper_lem_D_4_finite` | kernel-checked |
| Proposition D.5 | A uniformly heavy family of words | `paper_prop_D_5` | kernel-checked |
| Lemma D.6 | Sums of distinct powers cover all residues modulo 3^M | `paper_lem_D_6` | kernel-checked |

## Scope

The paper treats the forms in which Yolcu, Aaronson and Heule [YAH] use interpretations for $\mathcal T$, and their
barriers for Zantema's unary system $\mathcal Z$ (Table 2 of the paper). The arctic column refers to arctic
interpretations over $\mathbb A_{\mathbb N}$ and, for top forms and reduction pairs, also below zero.

| Use in [YAH] | Form | Natural-number matrix interpretations | Arctic interpretations |
|---|---|---|---|
| Theorems 2.6, 2.15; §4.3(2) | rule removal $\mathrm{SN}(R'/\mathcal T)$, any number of stages | Theorem 9.2(i), Corollary 9.3(i) | Theorem 3.1, Corollary 3.2(i) |
| Lemma 2.8 | rule removal through $\mathcal T^{\mathrm{rev}}$ | Theorem 9.2(i) | Theorem 3.1(i) |
| Lemma 3.18(1) | $\mathrm{SN}(R_{\mathrm{top}}/\mathcal T)$, $R \subseteq B$ | Theorem 9.2(ii), Corollary 9.3(ii) | Corollary 3.2(ii) |
| Lemma 3.18(2) | $\mathrm{SN}(Q^{\mathrm{rev}}_{\mathrm{top}}/\mathcal T^{\mathrm{rev}})$, $Q \subseteq D_T$ | Theorem 9.2(ii), Corollary 9.3(ii) | Corollary 3.2(ii) |
| Theorem 3.8 (barrier for $\mathcal Z$ and $\mathcal Z^{\mathrm{rev}}$) | first stage of rule removal | Theorem 9.2(i), for $\mathcal T$ and $\mathcal T^{\mathrm{rev}}$ | Theorem 3.1 |
| Theorem 3.10, footnote 8 (barrier for $\mathcal Z$, $\mathcal Z^{\mathrm{rev}}$) | the pairs that remain after the dependency pair transformation and rule removal (Lemma 3.9); for $\mathcal T$: the essential SCC | Theorem 9.2(iii), in the form of the remark in Section 13.2 | Theorems 3.3, 3.4 |
| Theorem 3.7 ([EWZ08, Theorem 6]) | affine to linear interpretations, a tool of the proofs in [YAH] | - | - |
| Lemma 3.15, Theorem 4.1, §4.3 (subsystems) | termination proofs of subsystems and of other systems | not concerned | not concerned |

The matrix interpretations of Hofbauer and Waldmann (RTA 2006) that compare corner entries of products of matrices
are covered for rule removal on $\mathcal T$ and $\mathcal T^{\mathrm{rev}}$ by Corollary 10.12. Not covered: the core matrix interpretations of Thiemann, Hofbauer, Le Huitouze and Waldmann (FSCD 2026) with the
domain $M_I$ of their Corollary 14 or with only their Property 1 (with the domain $E_I$ they are the form of
Corollary 10.12), and lexicographic comparisons of vectors; natural-number interpretations of $\mathcal H$ and $R_H$; rational, real and polynomial
interpretations (for arctic interpretations over $\mathbb Q$ and $\mathbb R$ see Section 4 of the paper); proof
pipelines in which other techniques act first. For both classes, "any number of stages" and "at every stage" refer
to stages that use these interpretations only: once the left-end rules or the dynamic rules have been removed by
other means, arctic interpretations of dimension 1 strictly orient rules of the remaining systems (Proposition
4.5 (i)), and natural-number matrix interpretations of the reversed remaining systems prove termination ([YAH, Lemma
3.15]).

## Scope of the verification

The verification classes are those of Table 5 in Section 14 of the paper, with the same wording.

| Verification class | Meaning | Results |
|---|---|---|
| kernel-checked | a theorem of the Lean formalization; it uses only the axioms `propext`, `Classical.choice` and `Quot.sound`, with no project-specific axioms or unproved hypotheses, and every declaration in the import closure of the root module, including the declarations of the Mathlib modules that it imports, has been replayed in the kernel by `leanchecker --fresh` | Lemma 2.3; Theorem 3.1 in all its forms; Theorems 3.3, 3.4 and 3.6; the remarks after Theorem 3.4 in their main forms; Proposition 3.7; Corollary 3.8; Propositions 4.1-4.3, 4.5, 4.6, and 4.8 for $\mathcal T$, $\mathcal H$; Section 5 except Lemma 5.3, in particular Theorem 5.5 and Lemma 5.6; Sections 6 and 7; Theorem 9.2; Propositions 9.4 and 9.5; Sections 10-13 except the general form of Lemma 12.15 (iii), including Corollary 10.12 and the remark on [YAH, Theorem 3.10]; Appendices B and D; the checks of Section 14 |
| derived in a few lines from kernel-checked results | a short written argument that is not itself a Lean theorem: it combines kernel-checked theorems, or it is carried out inside kernel-checked proofs without a separate statement | Corollaries 3.2, 3.5, 8.1 and 9.3; the remark after Theorem 3.6 and the rest of the remarks after Theorem 3.4; real entries (Section 4); Lemma 5.3, which is used inside kernel-checked proofs; the remark on many-sorted interpretations; Lemma 12.15 (iii) in its general form; the observations after Propositions 13.3 and 13.4 |
| written proof and finite computation | a computer-assisted proof in two layers: the general lemmas (Lemma 5.6, Corollary 8.1) are kernel-checked, and their conditions for the transformed systems are verified by a written proof and by finite computations of the accompanying script; not kernel-checked as a whole | Propositions 8.2 and 8.4; Theorems 8.3 and 8.5 |
| computation, not used in proofs | a computation or an exhaustive search that no proof of a theorem uses | Example 4.7; the search in Question 4.4; the transcription of the rules (Appendix C, `computations/`) |
| open | not settled | Question 4.4; the left-end rules of $R_H$ in Proposition 4.8; Problems Q1-Q9 of Section 15 |

The theorems for natural-number matrix interpretations are in the import closure of the module
`CollatzProof.Arctic.Nat.Final`, and those for arctic interpretations of $\mathcal T$, $\mathcal H$ and $R_H$ in the
import closures of `CollatzProof.Arctic.Summary`, `CollatzProof.Arctic.HTPDB.Final` and `CollatzProof.Arctic.RH.Final`;
the other files contain the boundary results, the reversed and affine forms, argument filters, the foundation of
Section 8, Proposition 9.5 and the checks. The root module `CollatzProof.Arctic.Paper` imports all files (through
`Paper5.lean` also those of `Nat/` and `DPFilter*.lean`), so the kernel re-check of the root module covers every
declaration, and every result called kernel-checked has the same status, in whichever module it lies.

### Checked by the Lean kernel

Every theorem `paper_*` of the table above, and everything they depend on. Finite checks are closed by `decide`,
which the kernel re-evaluates (no `native_decide`).

### Reproduction from a clean copy

On 2026-10-07 the files of this repository alone (revision r3), copied to an empty directory, were checked as
follows; the logs are in `verify/logs/`.

- `sha256sum -c MANIFEST.sha256`: all 303 files listed in the manifest matched (before the logs were added).
- `lake exe cache get && lake build` (Lean v4.34.1, Mathlib v4.34.1; Mathlib cloned from GitHub at the commit in
  `lake-manifest.json`, its compiled files from the Mathlib cache): `Build completed successfully (9209 jobs)` in about
  8 minutes, with 16 warnings in five files (linter warnings and one deprecated lemma) and no error.
- `lake env lean verify/Probe.lean` and `python3 verify/check_axioms.py verify/logs/probe.txt`: 205 reports of
  `#print axioms` (the 204 theorems `paper_*` and `NatQ5.allBarriers_final`), all
  `[propext, Classical.choice, Quot.sound]`, no error; `ALL OK`.
- `lake env lean verify/Closure.lean`: 285 modules, 10037 declared constants, 68753 reachable constants, axioms
  `Classical.choice`, `Quot.sound` and `propext` only.
- `lake env leanchecker --fresh CollatzProof.Arctic.Paper`: accepted (exit status 0, no message) in about 35 minutes,
  single-threaded. The root module imports all files, so every declaration in its import closure, which contains all
  files of this repository and the Mathlib modules they import, was replayed in the kernel.

The logs of revision r2 do not apply to revision r3 and are not included.

### Verification logs

The directory `verify/logs/` contains the logs of the runs in a clean copy of this repository (the files of this
repository alone, copied to an empty directory): `lake-build.log`, the output of `lake exe cache get && lake build`;
`probe.txt`, the output of `lake env lean verify/Probe.lean`; `check_axioms.txt`, the output of
`python3 verify/check_axioms.py verify/logs/probe.txt`; `closure.txt`, the output of `lake env lean verify/Closure.lean`;
`leanchecker.log`, the output of
`lake env leanchecker --fresh CollatzProof.Arctic.Paper`; and `manifest-check.txt`, the output of
`sha256sum -c MANIFEST.sha256` in the clean copy. The logs were added after these runs, and `MANIFEST.sha256` was
then rewritten to include them.
Lean is not run in continuous integration; these logs record the runs instead, and anyone can repeat them with the
commands in "Building and checking".

### Axioms

`#print axioms` in `verify/Probe.lean` reports `[propext, Classical.choice, Quot.sound]` for every theorem
`paper_*`. The script `verify/check_axioms.py` (Python 3, standard library only) checks this mechanically on the output
of `verify/Probe.lean`: it finds the theorems `paper_*` by scanning `CollatzProof/Arctic/Paper*.lean` (204 theorems),
and it requires, for each of them, exactly one report of `#print axioms` whose axioms are among `propext`,
`Classical.choice` and `Quot.sound` (so `sorryAx` or any other axiom fails the check), and no error message of Lean.
`python3 verify/check_axioms.py --self-test` runs the script on synthetic outputs, good and bad. `verify/Probe.lean`
also prints the axioms of `NatQ5.allBarriers_final`, the six statements of Theorem 9.2 together. Beyond the theorems
`paper_*`, `verify/Closure.lean` counts the constants declared in the modules `CollatzProof.Arctic.*`, traverses every
constant reachable from them, including those of Mathlib and of the Lean core, and prints the axioms met on the way;
it reports 285 modules, 10037 declared constants, 68753 reachable constants and the axioms `Classical.choice`,
`Quot.sound` and `propext` only (`verify/logs/closure.txt`). There is no `sorry`, no `admit`, no `axiom` declaration
and no `native_decide` in the sources of this repository, and no result from the literature is assumed as a
hypothesis.

### What rests on the paper, on computation or on reading

- **Section 8.2** (the systems after flat context closure with root labelling, full tiling, the switch to innermost
  rewriting, and narrowing) is computer-assisted: it rests on written proofs that apply the simulation lemma (Lemma 5.6,
  kernel-checked) and Corollary 8.1, and on the finite computations in `computations/check_transforms.py`. The
  transformed systems are not represented in Lean, and the results are not kernel-checked as a whole.
- **Corollaries 3.2, 3.5 and 8.1, the parts of the remarks after Theorem 3.4 without a Lean name, the remark after
  Theorem 3.6, and Lemma 5.3** are short written arguments from kernel-checked theorems; Lemma 5.3 is carried out
  inside the proofs of the kernel-checked theorems `barrier_of_auto_arcZ` and `Gen.barrier_of_auto_arcZG`, without a
  separate statement.
- **Corollary 9.3** (any number of stages, top forms, the dependency pair framework) is a short written argument from
  Theorem 9.2 and Propositions 13.3 and 13.4; the minimal chains that it uses for SCC decomposition are checked in Lean
  (`NatQ5.W5.pB_cycle`, `NatQ5.W5.pDrev_edges`).
- **Real entries (Section 4), the remark on many-sorted interpretations (Section 9), Lemma 12.15 (iii) in its general
  form, and the observations after Propositions 13.3 and 13.4** are short written arguments from kernel-checked
  theorems. For Lemma 12.15 (iii), Lean has the two steps (`NatQ5.W3h.prefix_two`,
  `NatQ5.W3h.Setup.iterHyp_of_parts`) in the setting of Definition 12.20, the only place where it is used.
- **Unnumbered remarks without a Lean name** are short written arguments; the formal status line of each remark in the
  paper says what it rests on.
- **Proposition 9.5.** For part (iii), the growth rate and the relevance of the residue component in the sense of
  Paper II are read off the kernel-checked facts. The consequences for the companion papers (the remark after the
  proposition: the hypothesis (P) cannot be dropped from Theorem 4.1 and Proposition 6.1 of Paper II and from Theorem
  8.1(ii) of Paper I) are written arguments, since the theorems of the companion papers are not part of this
  formalization.
- **The meaning of the statements.** That the frozen statements say what the theorems of the paper say rests on
  reading them (Appendix A of the paper and `verify/Probe.lean`) and on the checks of non-vacuity in Lean (satisfiable
  premises, strict orientation possible by definition, failure for subsystems and without monotonicity (Proposition
  9.4), agreement with the definitions of Koprowski and Waldmann and with the order of Yolcu, Aaronson and Heule,
  dependency pairs and usable rules recomputed by `decide`). The transcription of the rules from the Termination
  Problem Database and from Paper II is checked by `computations/check_systems.py`.

### Review status

The work has not yet been reviewed by independent human experts; no human mathematician has reviewed the proofs.
Formal verification does not replace independent review of the exposition or of the correspondence between the
informal and formal statements.

## Repository layout

| Path | Content |
|---|---|
| `CollatzProof/Arctic/Semiring.lean`, `SemiringZ.lean` | The arctic semirings over $\mathbb N$ (`Arc`) and $\mathbb Z$ (`ArcZ`). |
| `CollatzProof/Arctic/Defs.lean`, `Statement.lean`, `DPStatement.lean`, `AutoStatement.lean`, `CoreHyp.lean` | Letters, rules, interpretations, the rules of $\mathcal T$, canonical strings and derivations, and the frozen statements for $\mathcal T$ (rule removal, dependency pairs, the value-level statement `AutoCore` and the three finite statements `HSP`, `HTerrasWin`, `HLeftUse`). |
| `CollatzProof/Arctic/Bridge.lean`, `Canon.lean`, `Main.lean`, `DPAlg.lean`, `DPBridge.lean`, `DPCanon.lean`, `DPMain.lean`, `BZMain.lean`, `BZShift.lean`, `AutoBridge.lean`, `Summary.lean` | From rewriting to values: canonical derivations, dependency pair chains, the translation below zero, and the main theorems for $\mathcal T$ (`Summary`). |
| `CollatzProof/Arctic/TModel.lean`, `Family*.lean`, `EndDigits*.lean`, `ARule*.lean` | The model of $T$, the point family, end digits, and the carry rules. |
| `CollatzProof/Arctic/MinIdeal*.lean`, `Transport*.lean`, `Dfa*.lean`, `SupportDfa.lean`, `Window*.lean`, `Rate*.lean`, `Config*.lean` | Boolean matrix semigroups, the support automaton, windows and configurations (Section 6). |
| `CollatzProof/Arctic/Upper*.lean`, `Lower*.lean`, `Core*.lean` | Upper and lower bounds, and the assembly (Section 6). |
| `CollatzProof/Arctic/HSP*.lean` | Minimal rates without Kingman's theorem (Appendix B.1). |
| `CollatzProof/Arctic/Key*.lean`, `HTW*.lean`, `HLU*.lean` | Swaps, the $L^2$ identity, window frequencies (Appendix B.2) and the walk of block boundaries (Appendix B.3). |
| `CollatzProof/Arctic/Gen/` | The generic layer for block models (Section 7), with the instance for $T$ as a check (`Gen/ModelT.lean`, `Gen/TCheck.lean`). |
| `CollatzProof/Arctic/HModel/`, `CollatzProof/Arctic/HTPDB/` | The block model of $H$ and the system $\mathcal H$ (`collatz-T-5or7mod8`): statements, canonical derivations, uses of rules, main theorems (`HTPDB/Final.lean`). |
| `CollatzProof/Arctic/RH/` | The system $R_H$: statements, lifts of the derivations of $\mathcal H$, main theorems (`RH/Final.lean`), the reversal (`RH/Rev.lean`) and checks. |
| `CollatzProof/Arctic/Affine/` | Arctic linear functions with absolute parts, compared at every point: extraction of coefficients (`Coef.lean`), Corollary 3.8 (`Fin.lean`), the examples of dimension 1 (`Witness.lean`) and Proposition 4.8 (`Top.lean`). |
| `CollatzProof/Arctic/DPGen/` | The foundation of Section 8: the simulation lemma over an arbitrary alphabet and its instances. |
| `CollatzProof/Arctic/NonVacuity*.lean`, `DPWeak*.lean` | Checks of non-vacuity and the results of Section 4. |
| `CollatzProof/Arctic/DPFilterStatement.lean`, `DPFilter.lean`, `DPFilterBZ.lean`, `DPFilterCtrl.lean` | Argument filters for arctic reduction pairs (the remarks after Theorem 3.4): the statements, their proofs, the below-zero forms under `BZPos`, and controls in dimension 1. |
| `CollatzProof/Arctic/NatExample.lean`, `NatExample2.lean` | Proposition 9.5: the natural-number affine interpretation of dimension 4, its orientation, its values and its residue component, and the remark after it. |
| `CollatzProof/Arctic/Nat/Statement.lean`, `Nat/StatementRev.lean`, `Nat/StatementDP.lean` | The frozen definitions and statements of Theorem 9.2 (natural-number matrix interpretations; $\mathcal T$, its reversal, top forms, dependency pairs). |
| `CollatzProof/Arctic/Nat/Bridge.lean`, `BridgeTop.lean`, `ValueAuto.lean`, `Embed.lean`, `Lift.lean`, `Compartment.lean`, `CompartmentPi.lean`, `AutoCore.lean`, `Coord.lean`, `AddLoopLift.lean`, `HWCorner.lean` | From rewriting to automata (Section 10): values and their decrease, value automata, transposition and the value embedding, the lift modulo 3, components, the word u*, the statements of Theorems 10.10 and 10.11, and Corollary 10.12 (the corner form of Hofbauer and Waldmann, `HWCorner.lean`). |
| `CollatzProof/Arctic/Nat/H2*.lean` | Diagonal growth at most one (Section 11). |
| `CollatzProof/Arctic/Nat/DfaLln*.lean`, `Nat/W3*.lean` | Values and uses on 0/1 automata (Section 12): laws of large numbers for finite automata, idempotent words and sojourns, the frozen decomposition data (`Nat/W3Decomp.lean`) and its proof, the point family, runs of misses, configurations, and the two ends. |
| `CollatzProof/Arctic/Nat/BridgeRev.lean`, `BridgeRevW3.lean`, `BridgeDP.lean`, `BridgeDPFilter.lean`, `BridgeDPForms.lean` | Reversal, top forms and dependency pairs (Section 13), with forms of comparison and argument filters. |
| `CollatzProof/Arctic/Nat/Rigid*.lean` | Rigidity of non-negative matrix families (Appendix D). |
| `CollatzProof/Arctic/Nat/Final.lean` | The six statements of Theorem 9.2 without hypotheses (`allBarriers_final`). |
| `CollatzProof/Arctic/Nat/NonVacuity*.lean` | Checks of non-vacuity of the natural-number statements (including Corollary 10.12, `NonVacuityHW.lean`), Proposition 9.4, and Zantema's system (the remark in Section 13.2). |
| `CollatzProof/Arctic/Paper.lean`, `Paper2.lean`, `Paper3.lean`, `Paper4.lean`, `Paper5.lean` | The root module: the results of the paper under their numbers. |
| `verify/Probe.lean` | Prints the frozen statements and the definitions they use (arctic and natural-number), the statements of argument filters and the definitions they use, the definitions used by Proposition 9.5, by the value automata and by Corollary 10.12, and the statement and axioms of every theorem `paper_*` (not part of any library). |
| `verify/Closure.lean` | Counts the constants declared in `CollatzProof/Arctic`, traverses all constants reachable from them and prints the axioms met (not part of any library). |
| `verify/check_axioms.py` | Checks the output of `verify/Probe.lean`: every theorem `paper_*` depends on `propext`, `Classical.choice` and `Quot.sound` at most (Python 3, standard library only). |
| `verify/logs/` | The logs of the build, of `verify/Probe.lean`, of the axiom check, of `verify/Closure.lean`, of the kernel re-check and of the manifest check in a clean copy (see "Verification logs"). |
| `computations/` | The programs of Appendix C (Python 3 with the standard library, and one C program) and the log of the C program. |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake project (Lean v4.34.1, Mathlib v4.34.1). |
| `MANIFEST.sha256` | SHA-256 of every file in this repository except itself. |
| `README.md`, `LICENSE`, `NOTICE` | This file; the Apache License, Version 2.0; the copyright and third-party notice. |

The directory and namespace names (`Arctic`, `Nat`, `NatQ5`, `HTPDB`, `RH`, `HModel`, `Gen`, `DPGen`, `DPFilter`,
`NonVacuity`, `DPWeak`, and the sub-namespaces `NatQ5.W2a`-`W2e`, `NatQ5.W3a`-`W3d`, `NatQ5.W3h`, `NatQ5.W4a`,
`NatQ5.W5`, `NatQ5.Rigid`) are labels of the source repository; `HTPDB` refers to the system $\mathcal H$ of the
Termination Problem Database, and `NatQ5` to natural-number matrix interpretations.

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain in `lean-toolchain`, Lean v4.34.1, is
installed automatically) and `git`. In the root directory of a clone of this repository:

```sh
sha256sum -c MANIFEST.sha256      # optional: compare every file with its SHA-256 in the manifest
lake exe cache get                # Mathlib v4.34.1 and its build cache
lake build                        # builds all modules of CollatzProof/Arctic
lake env lean verify/Probe.lean > probe.txt   # statements, definitions and axioms
python3 verify/check_axioms.py probe.txt      # every theorem paper_* uses the three standard axioms at most
lake env lean verify/Closure.lean             # constants of CollatzProof/Arctic and all axioms they reach
lake env leanchecker --fresh CollatzProof.Arctic.Paper   # re-check every declaration in the kernel
```

`verify/check_axioms.py` prints `ALL OK` and exits with status 0 if the check passes. `leanchecker --fresh` replays,
single-threaded and without the compiled files, every declaration in the import closure of the root module
`CollatzProof.Arctic.Paper`, which contains all files of `CollatzProof/Arctic` and the Mathlib modules that they
import; the run in a clean copy is recorded in `verify/logs/leanchecker.log`. On the author's machine the closures of
`Summary`, `HTPDB.Final` and `RH.Final` alone took about 29, 34 and 34 minutes (2026-10-04), and that of `Nat.Final`
about 34 minutes (2026-10-07).

## Computations (Appendix C)

These programs are not part of the Lean development. The Python programs use only the standard library of Python 3;
each prints `ALL OK` and exits with status 0 if all its comparisons succeed, and stops with a message and a nonzero
exit status at the first failure. Where a program compares with the formalization, it parses the Lean sources of this
repository. Run them from the root of the repository:

```sh
python3 computations/check_systems.py      # optionally: --tpdb DIR (see below)
python3 computations/check_canonical.py
python3 computations/check_hmodel.py
python3 computations/check_rh.py
python3 computations/check_mod3.py
python3 computations/check_transforms.py
gcc -O2 -o rh_cf_search computations/rh_cf_search.c && ./rh_cf_search 1 cf
```

| Program | What it checks | Time |
|---|---|---|
| `check_systems.py` | Table 3 and Section 2.3: the rules of the Lean sources against the TPDB files and against Paper II, including the order; values; the dependency pairs, the SCCs of the estimated dependency graph, the subterm criterion and the usable rules of $\mathcal T$, $\mathcal H$ and their reversals against Section 2.3 and the lists of the frozen statements; the root steps by pairs of $P_B$ along canonical chains | 1 s |
| `check_canonical.py` | Lemma 2.3 by string rewriting ($\mathcal T$ for $2 \le n < 2^{13}$; $\mathcal H$ and $R_H$ for the 6141 integers of the domain of $H$ below $2^{14}$); the rules used; Lemma 7.4 (lifts) | 1 s |
| `check_hmodel.py` | Proposition 7.2 and Lemma 7.3: the Terras correspondence of the blocks of $H$, the affine constants, the translation by a swap, left-end digits, boundary points, the carry families; the dependency pair chains of $\mathcal H$ | 3 s |
| `check_rh.py` | Propositions 4.3 and 4.5 for $R_H$: the interpretation `RH.NonVacuityRH.ILeft` and condition (CF), the subsystems, Lemma 5.2 for $R_H$ on random interpretations, the left-end rules, mutation tests | 1 s |
| `check_mod3.py` | Example 4.7, Proposition 9.5 and the remark after it, by exact computation | 7 s |
| `check_transforms.py` | Section 8.2: the transformed systems, the sets $P_{\mathcal E}$ and $R_{\mathcal E}$, their dependency graphs, usable rules and usable symbols, the symbols of $\mathcal E(n)$ (in $P_{\mathcal E} \cup R_{\mathcal E}$ for the $n$ that define $P_{\mathcal E}$ and along the family), innermost chains, the processors of Proposition 8.4 and Theorem 8.5 | 34 s |
| `rh_cf_search.c` | Question 4.4: exhaustive search in dimension 2 (C, one thread); the runs are recorded in `rh_cf_search-2026-10-05.log` | $K=1$: under 1 s; $K=2$: 1.5 min |

The times were measured on one core of an Intel Xeon Gold 6254 (3.1 GHz) with Python 3.12 and gcc 13.3 (`-O2`).
The results on natural-number matrix interpretations of Sections 9-13 use no program of this directory except
`check_mod3.py` (Proposition 9.5): their finite checks are closed by `decide` in Lean.

**The rules of the Termination Problem Database.** The rules of $\mathcal T$ and $\mathcal H$ are written in
`check_systems.py` verbatim, as the lines `(rule ...)` of the files `collatz-T.ari` and `collatz-T-5or7mod8.ari` of the
directory `SRS_Standard/Yolcu_21` of [TPDB-ARI](https://github.com/TermCOMP/TPDB-ARI) at commit
`183f29db5ec7702215c6aabe12732bf3e836fced`; the files themselves are not part of this repository. To compare with the
files, download them from that commit into a directory `DIR` and run
`python3 computations/check_systems.py --tpdb DIR`, which also checks their SHA-256.

**The search of Question 4.4.** `rh_cf_search.c` enumerates the arctic interpretations of $R_H$ of dimension 2 with
entries in $\{-\infty, 0, 1, \dots, K\}$ and finite top-left entries, and counts those that weakly orient the ten used
rules, strictly orient `L0 -> L` or `Lf -> L`, and satisfy condition (CF) (mode `cf`), a weaker form (`cfnou`), or the
necessary condition that the first columns of $M_{\mathtt f}$ and $M_{\mathtt t}$ have no finite entry other than the
top-left one (`col0`). For $K = 1$ and $K = 2$ it finds none in each of these three modes (six runs, all recorded in
the log); as a control, without (CF) (`none`) and for $K = 1$ it finds 34820 interpretations, among them that of
Proposition 4.3. This is a numerical observation about dimension 2 and entries at most 2; it does not decide
Question 4.4.

**SAT searches.** The SAT encodings mentioned in Appendix C of the paper are not part of this repository.

## Versions

Lean v4.34.1 (`lean-toolchain`) and Mathlib tag v4.34.1, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (pinned by
`lake-manifest.json`).

## License

The Lean code and the programs in `computations/` are licensed under the Apache License, Version 2.0 (see `LICENSE`).
See `NOTICE` for the copyright and the third-party notice.

| Component | Use in this repository | Copyright | License |
|---|---|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4), tag v4.34.1, with the Lean packages it requires (pinned in `lake-manifest.json`) | Dependency, fetched at build time by Lake; not included | The Mathlib authors (named in each file) | Apache-2.0 (Mathlib); the other packages under their own licenses |

No file in this repository is derived from third-party code. The program `computations/check_systems.py` quotes the
22 rule lines of two problems of the Termination Problem Database (see "Computations"). The paper itself is not part of
this repository.

## How to cite

```bibtex
@misc{nashida2026arctic,
  author    = {Hiroyuki Nashida},
  title     = {Natural-number and arctic matrix interpretations alone make no progress, in any dimension, on the
               {Collatz} rewriting system},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23147025},
  url       = {https://doi.org/10.5281/zenodo.23147025},
  note      = {Preprint, revision r3}
}
```

The paper continues Part II of two companion papers and cites Part I:

```bibtex
@misc{nashida2026matrix,
  author    = {Hiroyuki Nashida},
  title     = {Dimension-free barriers for matrix interpretations of the {Collatz} rewriting system, and the maximal
               one-class weakenings of the modulo-8 conjectures of {Yolcu}, {Aaronson} and {Heule} provable by finite
               abstractions},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23081491},
  url       = {https://doi.org/10.5281/zenodo.23081491},
  note      = {Preprint, revision r3; Part II of two companion papers}
}

@misc{nashida2026dichotomy,
  author    = {Hiroyuki Nashida},
  title     = {Expanding cycles are not enough: a dichotomy for termination certificates of generalized {Collatz} maps},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23081447},
  url       = {https://doi.org/10.5281/zenodo.23081447},
  note      = {Preprint, revision r3; Part I of two companion papers}
}
```

## Attribution and the role of AI

- No file in this repository is derived from third-party code.
- All code of this project (the Lean sources in `CollatzProof/` and `verify/`, and the programs in
  `computations/` and `verify/check_axioms.py`) was written with Anthropic's Claude models through Claude Code, directed by the author. The Lean
  proofs are checked by the Lean kernel, and this check does not depend on how the code was produced. No human
  mathematician has reviewed the proofs.
- The comments were translated from Japanese. The code is identical to the checked originals: a script in the source
  repository (`check_lean_bundle.py`, in the directory of the paper) confirms that, after removing comments, every
  Lean file except `verify/Probe.lean` and `verify/Closure.lean` (which exist only here) is byte-for-byte identical to
  its original, that the frozen files of the source repository have not changed (their SHA-256 are pinned in the
  script), and that the code of `computations/rh_cf_search.c` is identical to its original. The source repository
  also has 16 probe files that only print axioms (`#print axioms`) and are imported by no other file; they are not
  part of this repository. The Python programs in `computations/` were rewritten for this release, in English and
  without dependencies, from the checking scripts of the source repository; `verify/check_axioms.py` was written for
  this release.
