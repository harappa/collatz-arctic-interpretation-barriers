/-
# The dependency pair forms: restating the forms of comparison (remarks of the internal review of the dependency pair statements; Proposition 13.3 of the paper)

* §1 Equivalence with values: `NWeakD`, `NWeakTopD` and `NStrictTopD` are equivalent to the comparison of values at every `y ∈ ℕ^d`
  (`nweakD_iff_forall`, `nweakTopD_iff_forall`, `nstrictTopD_iff_forall`; of the type of `nweak_iff_forall`,
  `nstrict_iff_forall` of `NonVacuity.lean`). Dependency pairs are used only at the root, so this is exactly the comparison of values without a context.
* §2 The form comparing in some component `k` (the one-sorted form of EWZ08 p.206, "a proper part of `≥`, strict in some component"): the form that compares dependency pairs
  weakly and strictly in the `k`-th component reduces to the statements by moving row `k` of `[h#]` to row 0 (`natBarrierDPrev_row`, `natBarrierDP_row`).
* §3 Marked letters with scalar values (the two-sorted form of EWZ08 §5, p.205): `[h#](x) = u ⬝ x + c` (`u ∈ ℕ^d`, `c ∈ ℕ`); dependency pairs are compared
  by `≥` in the coefficients, and strictly by `>` in the constant. Putting the row vector in row 0 reduces it to the statements (`natBarrierDPrev_scalar`, `natBarrierDP_scalar`).
-/
import CollatzProof.Arctic.Nat.BridgeDP

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter DLetter

namespace W5

variable {d : ℕ}

/-! ## §1 Equivalence with values -/

/-- Entrywise weak comparison is equivalent to the entrywise comparison of values at every `y`. -/
theorem nweakD_iff_forall (J : DLetter → NAff d) (π : DRule) :
    NWeakD J π ↔ ∀ y i, ((evND J π.rhs).app y) i ≤ ((evND J π.lhs).app y) i := by
  constructor
  · intro h y i
    simp only [NAff.app, Pi.add_apply, mulVec, dotProduct]
    exact add_le_add (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (h.1 i j)) (h.2 i)
  · intro h
    refine ⟨fun i j => ?_, fun i => by simpa [NAff.app] using h 0 i⟩
    by_contra hle
    have hlt := Nat.lt_of_not_le hle
    have hy := h (Pi.single j ((evND J π.lhs).v i + 1)) i
    simp only [NAff.app, Pi.add_apply, mulVec, dotProduct_single] at hy
    have hm : ((evND J π.lhs).M i j + 1) * ((evND J π.lhs).v i + 1) ≤
        (evND J π.rhs).M i j * ((evND J π.lhs).v i + 1) := Nat.mul_le_mul_right _ hlt
    rw [Nat.succ_mul] at hm
    omega

/-- Weak comparison in the first component is equivalent to the comparison of the 0-th components of the values at every `y`. -/
theorem nweakTopD_iff_forall [NeZero d] (J : DLetter → NAff d) (π : DRule) :
    NWeakTopD J π ↔ ∀ y, ((evND J π.rhs).app y) 0 ≤ ((evND J π.lhs).app y) 0 := by
  constructor
  · intro h y
    simp only [NAff.app, Pi.add_apply, mulVec, dotProduct]
    exact add_le_add (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (h.1 j)) h.2
  · intro h
    refine ⟨fun j => ?_, by simpa [NAff.app] using h 0⟩
    by_contra hle
    have hlt := Nat.lt_of_not_le hle
    have hy := h (Pi.single j ((evND J π.lhs).v 0 + 1))
    simp only [NAff.app, Pi.add_apply, mulVec, dotProduct_single] at hy
    have hm : ((evND J π.lhs).M 0 j + 1) * ((evND J π.lhs).v 0 + 1) ≤
        (evND J π.rhs).M 0 j * ((evND J π.lhs).v 0 + 1) := Nat.mul_le_mul_right _ hlt
    rw [Nat.succ_mul] at hm
    omega

/-- Strict comparison in the first component is equivalent to the strict comparison of the 0-th components of the values at every `y`. -/
theorem nstrictTopD_iff_forall [NeZero d] (J : DLetter → NAff d) (π : DRule) :
    NStrictTopD J π ↔ ∀ y, ((evND J π.rhs).app y) 0 < ((evND J π.lhs).app y) 0 := by
  constructor
  · intro h y
    simp only [NAff.app, Pi.add_apply, mulVec, dotProduct]
    have := Finset.sum_le_sum (s := Finset.univ) fun j (_ : j ∈ Finset.univ) => Nat.mul_le_mul_right (y j) (h.1 j)
    have h2 := h.2
    omega
  · intro h
    have hw : NWeakTopD J π := (nweakTopD_iff_forall J π).2 fun y => (h y).le
    exact ⟨hw.1, by simpa [NAff.app] using h 0⟩

/-! ## §2 The form comparing in some component `k` -/

/-- Move row `k` to row 0 and make the other rows zero. -/
def rowSel [NeZero d] (k : Fin d) (F : NAff d) : NAff d :=
  ⟨Matrix.of fun i j => if i = 0 then F.M k j else 0, fun i => if i = 0 then F.v k else 0⟩

theorem rowSel_comp [NeZero d] (k : Fin d) (F G : NAff d) : (rowSel k F).comp G = rowSel k (F.comp G) := by
  unfold rowSel NAff.comp
  congr 1
  · ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply]
    split_ifs <;> simp
  · ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.of_apply]
    split_ifs <;> simp

/-- Replace only the interpretations of the marked letters by `rowSel k`. -/
def selD [NeZero d] (k : Fin d) (J : DLetter → NAff d) : DLetter → NAff d
  | mark s => rowSel k (J (mark s))
  | plain s => J (plain s)

theorem evND_selD_plain [NeZero d] (k : Fin d) (J : DLetter → NAff d) (l : Word) :
    evND (selD k J) (l.map plain) = evND J (l.map plain) := by
  rw [evND_plain, evND_plain]
  rfl

theorem evND_selD_head [NeZero d] (k : Fin d) (J : DLetter → NAff d) (h : Letter) (l : Word) :
    evND (selD k J) (mark h :: l.map plain) = rowSel k (evND J (mark h :: l.map plain)) := by
  show (rowSel k (J (mark h))).comp (evND (selD k J) (l.map plain)) = rowSel k ((J (mark h)).comp (evND J (l.map plain)))
  rw [evND_selD_plain, rowSel_comp]

/-- Weak comparison in the `k`-th component (for the dependency pairs). -/
def RowWeakD (k : Fin d) (J : DLetter → NAff d) (π : DRule) : Prop :=
  (∀ j, (evND J π.rhs).M k j ≤ (evND J π.lhs).M k j) ∧ (evND J π.rhs).v k ≤ (evND J π.lhs).v k

/-- Strict comparison in the `k`-th component (for the dependency pairs). -/
def RowStrictD (k : Fin d) (J : DLetter → NAff d) (π : DRule) : Prop :=
  (∀ j, (evND J π.rhs).M k j ≤ (evND J π.lhs).M k j) ∧ (evND J π.rhs).v k < (evND J π.lhs).v k

theorem selD_dp_iff [NeZero d] (k : Fin d) (J : DLetter → NAff d) (h : Letter) (ρ : Rule) :
    (NWeakTopD (selD k J) (dp h ρ) ↔ RowWeakD k J (dp h ρ)) ∧
      (NStrictTopD (selD k J) (dp h ρ) ↔ RowStrictD k J (dp h ρ)) := by
  have hl : evND (selD k J) (dp h ρ).lhs = rowSel k (evND J (dp h ρ).lhs) := evND_selD_head k J h _
  have hr : evND (selD k J) (dp h ρ).rhs = rowSel k (evND J (dp h ρ).rhs) := evND_selD_head k J h _
  unfold NWeakTopD NStrictTopD RowWeakD RowStrictD
  rw [hl, hr]
  simp [rowSel]

theorem nweakD_selD_plain [NeZero d] (k : Fin d) (J : DLetter → NAff d) (ρ : Rule) :
    NWeakD (selD k J) ρ.plain ↔ NWeakD J ρ.plain := by
  unfold NWeakD Rule.plain
  simp only
  rw [evND_selD_plain, evND_selD_plain]

/-- **Reversed, comparing in the `k`-th component**: if `NatBarrierDPrev`, then an interpretation that weakly orients the usable rules entrywise and `P_D^rev` in the `k`-th component
does not strictly orient a pair of `P_D^rev` in the `k`-th component. -/
theorem natBarrierDPrev_row (hdp : NatBarrierDPrev) (d : ℕ) [NeZero d] (k : Fin d) (J : DLetter → NAff d)
    (hU : ∀ ρ ∈ usableSTrev, NWeakD J ρ.plain) (hP : ∀ π ∈ pairsPDrev, RowWeakD k J π) :
    ∀ π ∈ pairsPDrev, ¬ RowStrictD k J π := by
  intro π hπ hs
  rw [pairsPDrev_eq] at hπ hP
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hπ
  refine hdp d (selD k J) (fun σ hσ => (nweakD_selD_plain k J σ).2 (hU σ hσ)) (fun π' hπ' => ?_)
    (dp rgt ρ) (pairsPDrev_eq ▸ List.mem_map_of_mem hρ) ((selD_dp_iff k J rgt ρ).2.2 hs)
  rw [pairsPDrev_eq] at hπ'
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hπ'
  exact (selD_dp_iff k J rgt σ).1.2 (hP _ (List.mem_map_of_mem hσ))

/-- **Forward, comparing in the `k`-th component**. -/
theorem natBarrierDP_row (hdp : NatBarrierDP) (d : ℕ) [NeZero d] (k : Fin d) (J : DLetter → NAff d)
    (hU : ∀ ρ ∈ usableST, NWeakD J ρ.plain) (hP : ∀ π ∈ pairsPB, RowWeakD k J π) :
    ∀ π ∈ pairsPB, ¬ RowStrictD k J π := by
  intro π hπ hs
  rw [pairsPB_eq] at hπ hP
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hπ
  refine hdp d (selD k J) (fun σ hσ => (nweakD_selD_plain k J σ).2 (hU σ hσ)) (fun π' hπ' => ?_)
    (dp lft ρ) (pairsPB_eq ▸ List.mem_map_of_mem hρ) ((selD_dp_iff k J lft ρ).2.2 hs)
  rw [pairsPB_eq] at hπ'
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hπ'
  exact (selD_dp_iff k J lft σ).1.2 (hP _ (List.mem_map_of_mem hσ))

/-! ## §3 Marked letters with scalar values -/

/-- The interpretation `x ↦ u ⬝ x + c` of a marked letter with scalar values (the two-sorted form of EWZ08 §5). -/
structure SAff (d : ℕ) where
  u : Fin d → ℕ
  c : ℕ

/-- Weak comparison of a dependency pair `h# ℓ' → h# r'` (`ρ = h ℓ' → h r'`) with scalar values: `≥` in the coefficients, `≥` in the constant. -/
def SWeak (H : SAff d) (Jp : Letter → NAff d) (ρ : Rule) : Prop :=
  (∀ j, (H.u ᵥ* (evN Jp ρ.rhs.tail).M) j ≤ (H.u ᵥ* (evN Jp ρ.lhs.tail).M) j) ∧
    H.u ⬝ᵥ (evN Jp ρ.rhs.tail).v + H.c ≤ H.u ⬝ᵥ (evN Jp ρ.lhs.tail).v + H.c

/-- Strict comparison of a dependency pair with scalar values: `≥` in the coefficients, `>` in the constant (`l ≥ r ∧ c_l > c_r` of EWZ08 §5). -/
def SStrict (H : SAff d) (Jp : Letter → NAff d) (ρ : Rule) : Prop :=
  (∀ j, (H.u ᵥ* (evN Jp ρ.rhs.tail).M) j ≤ (H.u ᵥ* (evN Jp ρ.lhs.tail).M) j) ∧
    H.u ⬝ᵥ (evN Jp ρ.rhs.tail).v + H.c < H.u ⬝ᵥ (evN Jp ρ.lhs.tail).v + H.c

/-- The affine map with the row vector in row 0. -/
def embS [NeZero d] (H : SAff d) : NAff d :=
  ⟨Matrix.of fun i j => if i = 0 then H.u j else 0, fun i => if i = 0 then H.c else 0⟩

theorem embS_comp_M0 [NeZero d] (H : SAff d) (G : NAff d) (j : Fin d) :
    ((embS H).comp G).M 0 j = (H.u ᵥ* G.M) j := by
  simp [embS, NAff.comp, Matrix.mul_apply, vecMul, dotProduct]

theorem embS_comp_v0 [NeZero d] (H : SAff d) (G : NAff d) :
    ((embS H).comp G).v 0 = H.u ⬝ᵥ G.v + H.c := by
  simp [embS, NAff.comp, mulVec, dotProduct]

/-- The interpretation of the dependency pair problem built from an interpretation `Jp` of the unmarked letters and a scalar-valued interpretation `H` of the marked letters. -/
def scalarD [NeZero d] (Jp : Letter → NAff d) (H : SAff d) : DLetter → NAff d
  | mark _ => embS H
  | plain s => Jp s

theorem scalarD_dp_iff [NeZero d] (Jp : Letter → NAff d) (H : SAff d) (h : Letter) {ρ : Rule}
    (hρ : HeadRule h ρ) :
    (NWeakTopD (scalarD Jp H) (dp h ρ) ↔ SWeak H Jp ρ) ∧ (NStrictTopD (scalarD Jp H) (dp h ρ) ↔ SStrict H Jp ρ) := by
  have key : ∀ w : Word, evND (scalarD Jp H) (mark h :: w.map plain) = (embS H).comp (evN Jp w) := by
    intro w
    show (embS H).comp (evND (scalarD Jp H) (w.map plain)) = _
    rw [evND_plain]
    rfl
  obtain ⟨l, r, hl, hr, -, -⟩ := hρ
  have hL : evND (scalarD Jp H) (dp h ρ).lhs = (embS H).comp (evN Jp ρ.lhs.tail) := by
    show evND (scalarD Jp H) (mark h :: ρ.lhs.tail.map plain) = _
    exact key _
  have hR : evND (scalarD Jp H) (dp h ρ).rhs = (embS H).comp (evN Jp ρ.rhs.tail) := by
    show evND (scalarD Jp H) (mark h :: ρ.rhs.tail.map plain) = _
    exact key _
  unfold NWeakTopD NStrictTopD SWeak SStrict
  simp only [hL, hR, embS_comp_M0, embS_comp_v0, iff_self, and_self]

theorem nweakD_scalarD_plain [NeZero d] (Jp : Letter → NAff d) (H : SAff d) (ρ : Rule) :
    NWeakD (scalarD Jp H) ρ.plain ↔ NWeak Jp ρ := by
  rw [nweakD_plain_iff]
  rfl

/-- **Reversed, marked letters with scalar values** (the form of EWZ08 §5): if `NatBarrierDPrev`, then an interpretation that weakly orients `A^rev ∪ B^rev` entrywise and
the dependency pairs of the two top rules with scalar values does not strictly orient them with scalar values. -/
theorem natBarrierDPrev_scalar (hdp : NatBarrierDPrev) (d : ℕ) [NeZero d] (Jp : Letter → NAff d) (H : SAff d)
    (hU : ∀ ρ ∈ usableSTrev, NWeak Jp ρ) (hP : ∀ ρ ∈ rulesSTrevTop, SWeak H Jp ρ) :
    ∀ ρ ∈ rulesSTrevTop, ¬ SStrict H Jp ρ := by
  intro ρ hρ hs
  refine hdp d (scalarD Jp H) (fun σ hσ => (nweakD_scalarD_plain Jp H σ).2 (hU σ hσ)) (fun π hπ => ?_)
    (dp rgt ρ) (pairsPDrev_eq ▸ List.mem_map_of_mem hρ)
    ((scalarD_dp_iff Jp H rgt (rulesSTrevTop_head ρ hρ)).2.2 hs)
  rw [pairsPDrev_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hπ
  exact (scalarD_dp_iff Jp H rgt (rulesSTrevTop_head σ hσ)).1.2 (hP σ hσ)

/-- **Forward, marked letters with scalar values**. -/
theorem natBarrierDP_scalar (hdp : NatBarrierDP) (d : ℕ) [NeZero d] (Jp : Letter → NAff d) (H : SAff d)
    (hU : ∀ ρ ∈ usableST, NWeak Jp ρ) (hP : ∀ ρ ∈ rulesSTB, SWeak H Jp ρ) :
    ∀ ρ ∈ rulesSTB, ¬ SStrict H Jp ρ := by
  intro ρ hρ hs
  refine hdp d (scalarD Jp H) (fun σ hσ => (nweakD_scalarD_plain Jp H σ).2 (hU σ hσ)) (fun π hπ => ?_)
    (dp lft ρ) (pairsPB_eq ▸ List.mem_map_of_mem hρ)
    ((scalarD_dp_iff Jp H lft (rulesSTB_head ρ hρ)).2.2 hs)
  rw [pairsPB_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hπ
  exact (scalarD_dp_iff Jp H lft (rulesSTB_head σ hσ)).1.2 (hP σ hσ)

end W5

end Collatz.Arctic.NatQ5
