/-
# The dependency pair forms: equivalence with the top statements, and corollaries of the value-level core

We show that `NatBarrierDP` and `NatBarrierDPrev` of `StatementDP.lean` are equivalent to the top statements `NatBarrierSTB` (§4 of `Statement.lean`) and
`NatBarrierSTrevTop` (`StatementRev.lean`), and derive them from the value-level core (Lemma 13.2 of the paper).

* §1 Truncation (after `top_variant`, suggested in the internal review of the statements; rewritten in a general form): the interpretation of the letter `h` is
  truncated to row 0 (`truncAt h`). For rules that begin with `h` and contain no other `h` (`HeadRule h`), entrywise weak and strict orientation by the truncated interpretation
  is equivalent to the weak and strict comparison of the original interpretation in the first component only (`Row0Weak`, `Row0Strict`)
  (`trunc0_comp`: truncation commutes with composition from the left). For rules that do not contain `h` nothing changes. So the top statements imply
  the variants that compare the top rules in the first component only (the forms that drop the entrywise comparison of the top rules from the base system) (`top_variant_rev`,
  `top_variant_fwd`).
* §2 Interpretations of dependency pair problems and interpretations of letters: `ofDP h J` (`J (h#)` at the position of `h`, `J (plain s)` for the other letters). The interpretation of a
  dependency pair `h# ℓ' → h# r'` (`dp h ρ`, `ρ = h ℓ' → h r'`) is that of `ρ` under `ofDP h J` (`evND_dp_lhs`). The same holds for the usable rules
  (which do not contain `h`). Conversely, from an interpretation `I` of letters we form `liftD I` (ignoring marks), and `ofDP h (liftD I) = I`.
* §3 Equivalence: `natBarrierDPrev_iff_top : NatBarrierDPrev ↔ NatBarrierSTrevTop`, `natBarrierDP_iff_STB : NatBarrierDP ↔ NatBarrierSTB`.
  From the value-level core: `natBarrierDPrev_of_core'`, `natBarrierDP_of_core'`. The forms with comparison in the order of YAH (`≳` entrywise and `>` strict in the first component):
  `natBarrierDPrev_full`, `natBarrierDP_full` (Proposition 13.3 (a) of the paper).
-/
import CollatzProof.Arctic.Nat.StatementDP
import CollatzProof.Arctic.Nat.BridgeRev
import CollatzProof.Arctic.DPBridge

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter DLetter

namespace W5

variable {d : ℕ}

/-! ## §1 Truncation to row 0 -/

/-- Keep row 0 only (the other rows and the other components of the constant term are 0). -/
def trunc0 [NeZero d] (F : NAff d) : NAff d :=
  ⟨Matrix.of fun i j => if i = 0 then F.M i j else 0, fun i => if i = 0 then F.v i else 0⟩

/-- Truncation commutes with composition from the left: `trunc0 F ∘ G = trunc0 (F ∘ G)`. -/
theorem trunc0_comp [NeZero d] (F G : NAff d) : (trunc0 F).comp G = trunc0 (F.comp G) := by
  unfold trunc0 NAff.comp
  congr 1
  · ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply]
    split_ifs <;> simp
  · ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.of_apply]
    split_ifs <;> simp

/-- Truncate the interpretation of the letter `h` only to row 0. -/
def truncAt [NeZero d] (h : Letter) (I : Letter → NAff d) : Letter → NAff d :=
  fun s => if s = h then trunc0 (I s) else I s

theorem evN_truncAt_of_not_mem [NeZero d] (h : Letter) (I : Letter → NAff d) :
    ∀ w : Word, h ∉ w → evN (truncAt h I) w = evN I w
  | [], _ => rfl
  | s :: w, hw => by
    simp only [List.mem_cons, not_or] at hw
    have hs : s ≠ h := fun e => hw.1 e.symm
    show (truncAt h I s).comp (evN (truncAt h I) w) = (I s).comp (evN I w)
    rw [evN_truncAt_of_not_mem h I w hw.2]
    simp [truncAt, hs]

theorem evN_truncAt_head [NeZero d] (h : Letter) (I : Letter → NAff d) (w : Word) (hw : h ∉ w) :
    evN (truncAt h I) (h :: w) = trunc0 (evN I (h :: w)) := by
  show (truncAt h I h).comp (evN (truncAt h I) w) = trunc0 ((I h).comp (evN I w))
  rw [evN_truncAt_of_not_mem h I w hw, ← trunc0_comp]
  simp [truncAt]

/-- Weak comparison in the first component only (for rules). -/
def Row0Weak [NeZero d] (I : Letter → NAff d) (ρ : Rule) : Prop :=
  (∀ j, (evN I ρ.rhs).M 0 j ≤ (evN I ρ.lhs).M 0 j) ∧ (evN I ρ.rhs).v 0 ≤ (evN I ρ.lhs).v 0

/-- Strict comparison in the first component only (for rules). -/
def Row0Strict [NeZero d] (I : Letter → NAff d) (ρ : Rule) : Prop :=
  (∀ j, (evN I ρ.rhs).M 0 j ≤ (evN I ρ.lhs).M 0 j) ∧ (evN I ρ.rhs).v 0 < (evN I ρ.lhs).v 0

theorem row0Weak_of_nweak [NeZero d] {I : Letter → NAff d} {ρ : Rule} (h : NWeak I ρ) : Row0Weak I ρ :=
  ⟨fun j => h.1 0 j, h.2 0⟩

theorem row0Strict_of_nstrict [NeZero d] {I : Letter → NAff d} {ρ : Rule} (h : NStrict I ρ) : Row0Strict I ρ :=
  ⟨fun j => h.1.1 0 j, h.2⟩

theorem trunc0_weak_iff [NeZero d] (F G : NAff d) :
    ((∀ i j, (trunc0 G).M i j ≤ (trunc0 F).M i j) ∧ ∀ i, (trunc0 G).v i ≤ (trunc0 F).v i) ↔
      ((∀ j, G.M 0 j ≤ F.M 0 j) ∧ G.v 0 ≤ F.v 0) := by
  simp only [trunc0, Matrix.of_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j => by simpa using h1 0 j, by simpa using h2 0⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · split_ifs with hi
      · subst hi; exact h1 j
      · exact le_rfl
    · split_ifs with hi
      · subst hi; exact h2
      · exact le_rfl

/-- Rules that begin with `h` and contain no other `h` (the form of top rules). -/
def HeadRule (h : Letter) (ρ : Rule) : Prop := ∃ l r : Word, ρ.lhs = h :: l ∧ ρ.rhs = h :: r ∧ h ∉ l ∧ h ∉ r

theorem nweak_truncAt_head [NeZero d] (h : Letter) (I : Letter → NAff d) {ρ : Rule} (hρ : HeadRule h ρ) :
    NWeak (truncAt h I) ρ ↔ Row0Weak I ρ := by
  obtain ⟨l, r, hl, hr, hl', hr'⟩ := hρ
  unfold NWeak Row0Weak
  rw [hl, hr, evN_truncAt_head h I l hl', evN_truncAt_head h I r hr']
  exact trunc0_weak_iff _ _

theorem nstrict_truncAt_head [NeZero d] (h : Letter) (I : Letter → NAff d) {ρ : Rule} (hρ : HeadRule h ρ) :
    NStrict (truncAt h I) ρ ↔ Row0Strict I ρ := by
  have hw := nweak_truncAt_head h I hρ
  obtain ⟨l, r, hl, hr, hl', hr'⟩ := hρ
  unfold NStrict Row0Strict
  unfold Row0Weak at hw
  rw [hw, hl, hr, evN_truncAt_head h I l hl', evN_truncAt_head h I r hr']
  simp only [trunc0, ↓reduceIte]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.le⟩, h3⟩

theorem nweak_truncAt_free [NeZero d] (h : Letter) (I : Letter → NAff d) {ρ : Rule} (hl : h ∉ ρ.lhs)
    (hr : h ∉ ρ.rhs) : NWeak (truncAt h I) ρ ↔ NWeak I ρ := by
  unfold NWeak
  rw [evN_truncAt_of_not_mem h I _ hl, evN_truncAt_of_not_mem h I _ hr]

/-- **The variant of top statements (general form)**: suppose the set of rules `R` splits into top rules `Rtop` beginning with `h` and rules `Rrest` not containing `h`,
and no interpretation that weakly orients `R` entrywise strictly orients a rule of `Rtop`. Then an interpretation that weakly orients `Rrest` entrywise and
`Rtop` in the first component does not strictly orient `Rtop` in the first component either. -/
theorem top_variant_gen {R Rtop Rrest : List Rule} (h : Letter)
    (hsplit : ∀ ρ ∈ R, ρ ∈ Rtop ∨ ρ ∈ Rrest) (htop : ∀ ρ ∈ Rtop, HeadRule h ρ)
    (hrest : ∀ ρ ∈ Rrest, h ∉ ρ.lhs ∧ h ∉ ρ.rhs)
    (hbar : ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), (∀ ρ ∈ R, NWeak I ρ) → ∀ ρ ∈ Rtop, ¬ NStrict I ρ)
    (d : ℕ) [NeZero d] (I : Letter → NAff d) (hX : ∀ ρ ∈ Rrest, NWeak I ρ) (hQ : ∀ ρ ∈ Rtop, Row0Weak I ρ) :
    ∀ ρ ∈ Rtop, ¬ Row0Strict I ρ := by
  intro ρ hρ hs
  refine hbar d (truncAt h I) (fun σ hσ => ?_) ρ hρ ((nstrict_truncAt_head h I (htop ρ hρ)).2 hs)
  rcases hsplit σ hσ with h1 | h2
  · exact (nweak_truncAt_head h I (htop σ h1)).2 (hQ σ h1)
  · exact (nweak_truncAt_free h I (hrest σ h2).1 (hrest σ h2).2).2 (hX σ h2)

theorem rulesSTrev_split : ∀ ρ ∈ rulesSTrev, ρ ∈ rulesSTrevTop ∨ ρ ∈ rulesSTrev.drop 2 := by decide

theorem rulesSTrev_drop_free : ∀ ρ ∈ rulesSTrev.drop 2, rgt ∉ ρ.lhs ∧ rgt ∉ ρ.rhs := by decide

theorem rulesSTrevTop_head : ∀ ρ ∈ rulesSTrevTop, HeadRule rgt ρ := rulesSTrevTop_form

theorem rulesST_split : ∀ ρ ∈ rulesST, ρ ∈ rulesSTB ∨ ρ ∈ rulesST.take 8 := by decide

theorem rulesST_take_free : ∀ ρ ∈ rulesST.take 8, lft ∉ ρ.lhs ∧ lft ∉ ρ.rhs := by decide

theorem rulesSTB_head : ∀ ρ ∈ rulesSTB, HeadRule lft ρ := rulesSTB_form

/-- **The reversed top variant** (`top_variant` of the internal review of the statements): if `NatBarrierSTrevTop`, then an interpretation (not necessarily monotone) that weakly orients
`X^rev = A^rev ∪ B^rev` entrywise and the two top rules in the first component does not strictly orient the top rules in the first component either.
It covers the form that takes `>` in the top form to be the order of the first component only, and the form with base system `X^rev`. -/
theorem top_variant_rev (hbar : NatBarrierSTrevTop) (d : ℕ) [NeZero d] (I : Letter → NAff d)
    (hX : ∀ ρ ∈ rulesSTrev.drop 2, NWeak I ρ) (hQ : ∀ ρ ∈ rulesSTrevTop, Row0Weak I ρ) :
    ∀ ρ ∈ rulesSTrevTop, ¬ Row0Strict I ρ :=
  top_variant_gen rgt rulesSTrev_split rulesSTrevTop_head rulesSTrev_drop_free
    (fun d _ I hw => hbar d I hw) d I hX hQ

/-- **The forward left-end variant**: if `NatBarrierSTB`, then an interpretation that weakly orients `U = D_T ∪ A` entrywise and the three left-end rules
in the first component does not strictly orient the left-end rules in the first component either. -/
theorem top_variant_fwd (hbar : NatBarrierSTB) (d : ℕ) [NeZero d] (I : Letter → NAff d)
    (hX : ∀ ρ ∈ rulesST.take 8, NWeak I ρ) (hQ : ∀ ρ ∈ rulesSTB, Row0Weak I ρ) :
    ∀ ρ ∈ rulesSTB, ¬ Row0Strict I ρ :=
  top_variant_gen lft rulesST_split rulesSTB_head rulesST_take_free
    (fun d _ I hw => hbar d I hw) d I hX hQ

/-! ## §2 Interpretations of dependency pair problems and interpretations of letters -/

/-- From an interpretation of a dependency pair problem to an interpretation of letters: `J (h#)` at the position of `h`, `J (plain s)` for the other letters. -/
def ofDP (h : Letter) (J : DLetter → NAff d) : Letter → NAff d :=
  fun s => if s = h then J (mark h) else J (plain s)

/-- From an interpretation of letters to an interpretation of a dependency pair problem (ignoring marks). -/
def liftD (I : Letter → NAff d) : DLetter → NAff d
  | mark s => I s
  | plain s => I s

theorem ofDP_liftD (h : Letter) (I : Letter → NAff d) : ofDP h (liftD I) = I := by
  funext s
  by_cases hs : s = h
  · subst hs; simp [ofDP, liftD]
  · simp [ofDP, liftD, hs]

/-- The interpretation of an unmarked string is `evN` of the interpretation of the unmarked letters. -/
theorem evND_plain (J : DLetter → NAff d) : ∀ w : Word, evND J (w.map plain) = evN (fun s => J (plain s)) w
  | [] => rfl
  | s :: w => by
    show (J (plain s)).comp (evND J (w.map plain)) = (J (plain s)).comp (evN (fun s => J (plain s)) w)
    rw [evND_plain J w]

theorem evN_ofDP_free (h : Letter) (J : DLetter → NAff d) :
    ∀ w : Word, h ∉ w → evN (ofDP h J) w = evN (fun s => J (plain s)) w
  | [], _ => rfl
  | s :: w, hw => by
    simp only [List.mem_cons, not_or] at hw
    have hs : s ≠ h := fun e => hw.1 e.symm
    show (ofDP h J s).comp (evN (ofDP h J) w) = (J (plain s)).comp (evN (fun s => J (plain s)) w)
    rw [evN_ofDP_free h J w hw.2]
    simp [ofDP, hs]

theorem evND_markHead (h : Letter) (J : DLetter → NAff d) (l : Word) (hl : h ∉ l) :
    evND J (mark h :: l.map plain) = evN (ofDP h J) (h :: l) := by
  show (J (mark h)).comp (evND J (l.map plain)) = (ofDP h J h).comp (evN (ofDP h J) l)
  rw [evND_plain, evN_ofDP_free h J l hl]
  simp [ofDP]

theorem evND_dp_lhs (h : Letter) (J : DLetter → NAff d) {ρ : Rule} (hρ : HeadRule h ρ) :
    evND J (dp h ρ).lhs = evN (ofDP h J) ρ.lhs := by
  obtain ⟨l, r, hl, hr, hl', hr'⟩ := hρ
  show evND J (mark h :: ρ.lhs.tail.map plain) = _
  rw [hl, List.tail_cons, evND_markHead h J l hl']

theorem evND_dp_rhs (h : Letter) (J : DLetter → NAff d) {ρ : Rule} (hρ : HeadRule h ρ) :
    evND J (dp h ρ).rhs = evN (ofDP h J) ρ.rhs := by
  obtain ⟨l, r, hl, hr, hl', hr'⟩ := hρ
  show evND J (mark h :: ρ.rhs.tail.map plain) = _
  rw [hr, List.tail_cons, evND_markHead h J r hr']

theorem nweakTopD_dp_iff [NeZero d] (h : Letter) (J : DLetter → NAff d) {ρ : Rule} (hρ : HeadRule h ρ) :
    NWeakTopD J (dp h ρ) ↔ Row0Weak (ofDP h J) ρ := by
  unfold NWeakTopD Row0Weak
  rw [evND_dp_lhs h J hρ, evND_dp_rhs h J hρ]

theorem nstrictTopD_dp_iff [NeZero d] (h : Letter) (J : DLetter → NAff d) {ρ : Rule} (hρ : HeadRule h ρ) :
    NStrictTopD J (dp h ρ) ↔ Row0Strict (ofDP h J) ρ := by
  unfold NStrictTopD Row0Strict
  rw [evND_dp_lhs h J hρ, evND_dp_rhs h J hρ]

theorem nweakD_plain_iff (J : DLetter → NAff d) (ρ : Rule) : NWeakD J ρ.plain ↔ NWeak (fun s => J (plain s)) ρ := by
  unfold NWeakD NWeak Rule.plain
  simp only
  rw [evND_plain, evND_plain]

theorem nweakD_plain_iff_ofDP (h : Letter) (J : DLetter → NAff d) {ρ : Rule} (hl : h ∉ ρ.lhs) (hr : h ∉ ρ.rhs) :
    NWeakD J ρ.plain ↔ NWeak (ofDP h J) ρ := by
  rw [nweakD_plain_iff]
  unfold NWeak
  rw [evN_ofDP_free h J _ hl, evN_ofDP_free h J _ hr]

/-! ### Correspondence between the dependency pair problems and the rules (from the frozen arctic definitions) -/

theorem pairsPDrev_eq : pairsPDrev = rulesSTrevTop.map (dp rgt) := by decide

theorem usableSTrev_eq : usableSTrev = rulesSTrev.drop 2 := by decide

theorem pairsPB_eq : pairsPB = rulesSTB.map (dp lft) := by decide

theorem usableST_eq : usableST = rulesST.take 8 := by decide

end W5

/-! ## §3 Equivalence, and corollaries of the value-level core -/

open W5

/-- **Reversed**: from the top statement to the dependency pair form (truncating `[.#]` to row 0). -/
theorem natBarrierDPrev_of_top (hbar : NatBarrierSTrevTop) : NatBarrierDPrev := by
  intro d _ J hU hP π hπ hs
  rw [pairsPDrev_eq] at hπ
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hπ
  have hX : ∀ σ ∈ rulesSTrev.drop 2, NWeak (ofDP rgt J) σ := fun σ hσ =>
    (nweakD_plain_iff_ofDP rgt J (rulesSTrev_drop_free σ hσ).1 (rulesSTrev_drop_free σ hσ).2).1
      (hU σ (usableSTrev_eq ▸ hσ))
  have hQ : ∀ σ ∈ rulesSTrevTop, Row0Weak (ofDP rgt J) σ := fun σ hσ =>
    (nweakTopD_dp_iff rgt J (rulesSTrevTop_head σ hσ)).1 (hP _ (pairsPDrev_eq ▸ List.mem_map_of_mem hσ))
  exact top_variant_rev hbar d (ofDP rgt J) hX hQ ρ hρ
    ((nstrictTopD_dp_iff rgt J (rulesSTrevTop_head ρ hρ)).1 hs)

/-- **Reversed**: from the dependency pair form to the top statement (putting the interpretation of `.` back as `[.#]`). -/
theorem natBarrierSTrevTop_of_DPrev (hdp : NatBarrierDPrev) : NatBarrierSTrevTop := by
  intro d _ I hweak ρ hρ hs
  have hI := ofDP_liftD rgt I
  refine hdp d (liftD I) (fun σ hσ => ?_) (fun π hπ => ?_) (dp rgt ρ)
    (pairsPDrev_eq ▸ List.mem_map_of_mem hρ) ?_
  · rw [usableSTrev_eq] at hσ
    rw [nweakD_plain_iff_ofDP rgt _ (rulesSTrev_drop_free σ hσ).1 (rulesSTrev_drop_free σ hσ).2, hI]
    exact hweak σ (List.mem_of_mem_drop hσ)
  · rw [pairsPDrev_eq] at hπ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hπ
    rw [nweakTopD_dp_iff rgt _ (rulesSTrevTop_head σ hσ), hI]
    exact row0Weak_of_nweak (hweak σ (rulesSTrevTop_sub σ hσ))
  · rw [nstrictTopD_dp_iff rgt _ (rulesSTrevTop_head ρ hρ), hI]
    exact row0Strict_of_nstrict hs

/-- **The reversed dependency pair form is equivalent to the top statement.** -/
theorem natBarrierDPrev_iff_top : NatBarrierDPrev ↔ NatBarrierSTrevTop :=
  ⟨natBarrierSTrevTop_of_DPrev, natBarrierDPrev_of_top⟩

/-- **Forward**: from the left-end statement to the dependency pair form (truncating `[/#]` to row 0). -/
theorem natBarrierDP_of_STB (hbar : NatBarrierSTB) : NatBarrierDP := by
  intro d _ J hU hP π hπ hs
  rw [pairsPB_eq] at hπ
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hπ
  have hX : ∀ σ ∈ rulesST.take 8, NWeak (ofDP lft J) σ := fun σ hσ =>
    (nweakD_plain_iff_ofDP lft J (rulesST_take_free σ hσ).1 (rulesST_take_free σ hσ).2).1
      (hU σ (usableST_eq ▸ hσ))
  have hQ : ∀ σ ∈ rulesSTB, Row0Weak (ofDP lft J) σ := fun σ hσ =>
    (nweakTopD_dp_iff lft J (rulesSTB_head σ hσ)).1 (hP _ (pairsPB_eq ▸ List.mem_map_of_mem hσ))
  exact top_variant_fwd hbar d (ofDP lft J) hX hQ ρ hρ
    ((nstrictTopD_dp_iff lft J (rulesSTB_head ρ hρ)).1 hs)

/-- **Forward**: from the dependency pair form to the left-end statement (putting the interpretation of `/` back as `[/#]`). -/
theorem natBarrierSTB_of_DP (hdp : NatBarrierDP) : NatBarrierSTB := by
  intro d _ I hweak ρ hρ hs
  have hI := ofDP_liftD lft I
  refine hdp d (liftD I) (fun σ hσ => ?_) (fun π hπ => ?_) (dp lft ρ)
    (pairsPB_eq ▸ List.mem_map_of_mem hρ) ?_
  · rw [usableST_eq] at hσ
    rw [nweakD_plain_iff_ofDP lft _ (rulesST_take_free σ hσ).1 (rulesST_take_free σ hσ).2, hI]
    exact hweak σ (List.mem_of_mem_take hσ)
  · rw [pairsPB_eq] at hπ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hπ
    rw [nweakTopD_dp_iff lft _ (rulesSTB_head σ hσ), hI]
    exact row0Weak_of_nweak (hweak σ (rulesSTB_sub σ hσ))
  · rw [nstrictTopD_dp_iff lft _ (rulesSTB_head ρ hρ), hI]
    exact row0Strict_of_nstrict hs

/-- **The forward dependency pair form is equivalent to the left-end statement.** -/
theorem natBarrierDP_iff_STB : NatBarrierDP ↔ NatBarrierSTB :=
  ⟨natBarrierSTB_of_DP, natBarrierDP_of_STB⟩

/-- The reversed dependency pair form from the value-level core (without monotonicity). -/
theorem natBarrierDPrev_of_core' (hcore : NatValueCore') : NatBarrierDPrev :=
  natBarrierDPrev_of_top (natBarrierSTrevTop_of_core' hcore)

/-- The forward dependency pair form from the value-level core (without monotonicity). -/
theorem natBarrierDP_of_core' (hcore : NatValueCore') : NatBarrierDP :=
  natBarrierDP_of_STB (natBarrierSTB_of_core' hcore)

/-- From the value-level core: the forward and reversed barriers, the left-end and top statements, and the two dependency pair forms. -/
theorem allBarriersDP_of_core' (hcore : NatValueCore') :
    NatBarrierST ∧ NatBarrierSTB ∧ NatBarrierSTrev ∧ NatBarrierSTrevTop ∧ NatBarrierDP ∧ NatBarrierDPrev :=
  ⟨natBarrierST_of_core' hcore, natBarrierSTB_of_core' hcore, natBarrierSTrev_of_core' hcore,
    natBarrierSTrevTop_of_core' hcore, natBarrierDP_of_core' hcore, natBarrierDPrev_of_core' hcore⟩

/-! ### The forms with comparison in the order of YAH (they follow from the statements) -/

/-- Strict comparison in the order of YAH (§2.3.1): `≳` entrywise, and strict in the first component. -/
def NStrictD {d : ℕ} [NeZero d] (J : DLetter → NAff d) (π : DRule) : Prop :=
  NWeakD J π ∧ (evND J π.rhs).v 0 < (evND J π.lhs).v 0

instance {d : ℕ} [NeZero d] (J : DLetter → NAff d) (π : DRule) : Decidable (NStrictD J π) :=
  instDecidableAnd

/-- **Reversed, in the order of YAH**: an interpretation that weakly orients the usable rules and `P_D^rev` entrywise does not strictly orient a pair of `P_D^rev` (with the `>` of YAH)
(the form of the reduction pair processor for dependency pairs: every pair `≳` or `>`, and some pair `>`; for natural-number matrix interpretations, Thm 17 (a) of GTSF06 and
EWZ08 §5). -/
theorem natBarrierDPrev_full (hdp : NatBarrierDPrev) (d : ℕ) [NeZero d] (J : DLetter → NAff d)
    (hU : ∀ ρ ∈ usableSTrev, NWeakD J ρ.plain) (hP : ∀ π ∈ pairsPDrev, NWeakD J π ∨ NStrictD J π) :
    ∀ π ∈ pairsPDrev, ¬ NStrictD J π := by
  intro π hπ hs
  refine hdp d J hU (fun σ hσ => ?_) π hπ ⟨fun j => hs.1.1 0 j, hs.2⟩
  rcases hP σ hσ with h | h
  · exact ⟨fun j => h.1 0 j, h.2 0⟩
  · exact ⟨fun j => h.1.1 0 j, h.1.2 0⟩

/-- **Forward, in the order of YAH**. -/
theorem natBarrierDP_full (hdp : NatBarrierDP) (d : ℕ) [NeZero d] (J : DLetter → NAff d)
    (hU : ∀ ρ ∈ usableST, NWeakD J ρ.plain) (hP : ∀ π ∈ pairsPB, NWeakD J π ∨ NStrictD J π) :
    ∀ π ∈ pairsPB, ¬ NStrictD J π := by
  intro π hπ hs
  refine hdp d J hU (fun σ hσ => ?_) π hπ ⟨fun j => hs.1.1 0 j, hs.2⟩
  rcases hP σ hσ with h | h
  · exact ⟨fun j => h.1 0 j, h.2 0⟩
  · exact ⟨fun j => h.1.1 0 j, h.1.2 0⟩

end Collatz.Arctic.NatQ5
