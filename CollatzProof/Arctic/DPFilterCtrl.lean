/-
Controls for the forms with argument filters (`DPFilter.lean`, `DPFilterBZ.lean`; the remark on argument filters after Theorem 3.4 of the paper) and examples outside the hypotheses.
Namespace `Collatz.Arctic.DPFilter`. All solutions have dimension 1 (solutions found by SAT or exhaustive search are checked in the kernel; the searches themselves
are not part of this bundle).

* §2 Controls: with the shrunk usable rules alone the barrier fails. The condition "the matrix of a symbol whose argument is dropped is −∞ (a constant)" is essential.
  - The 3 rules of $\mathcal T^{\mathrm{rev}}$ (argument of `f` dropped): if `[f]` is not required to be constant, `.#f → .#` can be strictly oriented (`not_barrier_revF`).
  - The 6 rules of $\mathcal T^{\mathrm{rev}}$ (argument of `t` dropped): if `[t]` is not required to be constant, `.#f → .#` can be strictly oriented (`not_barrier_revT`).
  - The 6 rules of $\mathcal H^{\mathrm{rev}}$ (arguments of `f` and `t` dropped): if `[f]` and `[t]` are not required to be constant, `.#ff → .#0` can be strictly oriented
    (`not_barrier_revHFT`).
  In all of them the first components of the absolute parts are finite and non-negative, so they are controls both for somewhere finiteness over `𝔸_ℕ` (the general form `NonVacuity.BarrierDPFor`) and
  for absolute positivity below zero (`NonVacuity.BarrierBZFor`; the three with the suffix `_Z`).
* §3 Examples outside the hypotheses: interpretations that satisfy the hypotheses with a filter but do not weakly orient some of the frozen usable rules (`outside_revT` and
  `outside_revHFT` over `𝔸_ℕ`; those with the suffix `_Z` below zero and absolutely positive). Hence in the cases (b) and (c) the frozen statements cannot be applied
  directly.
-/
import CollatzProof.Arctic.DPFilterBZ

namespace Collatz.Arctic.DPFilter

open Collatz.Arctic Matrix Letter DLetter
open Collatz.Arctic.NatQ5.W5 (usableRevF usableRevT)

/-! ## §1 Interpretations of dimension 1 (general commutative semiring) -/

section Gen

variable {R : Type} [CommSemiring R]

/-- The interpretation of dimension 1 that assigns `x ↦ m(s) ⊗ x ⊕ c(s)` to the symbol `s` (`w s = (m(s), c(s))`). -/
def aff1J (w : DLetter → R × R) : DLetter → AffFun R 1 := fun s => ⟨fun _ _ => (w s).1, fun _ => (w s).2⟩

/-- The coefficients of compositions in dimension 1: `(m, c) ∘ (m', c') = (m ⊗ m', m ⊗ c' ⊕ c)`. -/
def ev1 (w : DLetter → R × R) : List DLetter → R × R
  | [] => (1, 0)
  | s :: x => ((w s).1 * (ev1 w x).1, (w s).1 * (ev1 w x).2 + (w s).2)

theorem evA_aff1J (w : DLetter → R × R) (x : List DLetter) :
    (∀ i j, (evA (aff1J w) x).M i j = (ev1 w x).1) ∧ ∀ i, (evA (aff1J w) x).c i = (ev1 w x).2 := by
  induction x with
  | nil =>
    refine ⟨fun i j => ?_, fun i => rfl⟩
    have hij : i = j := Subsingleton.elim i j
    subst hij
    show (1 : Matrix (Fin 1) (Fin 1) R) i i = _
    rw [Matrix.one_apply_eq]
    rfl
  | cons s x ih =>
    obtain ⟨ihM, ihc⟩ := ih
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · show ((aff1J w s).M * (evA (aff1J w) x).M) i j = _
      rw [Matrix.mul_apply, Fin.sum_univ_one, ihM]
      rfl
    · show ((aff1J w s).M *ᵥ (evA (aff1J w) x).c + (aff1J w s).c) i = _
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, ihc]
      rfl

theorem aff1J_M_zero (w : DLetter → R × R) (s : DLetter) (hs : (w s).1 = 0) : (aff1J w s).M = 0 := by
  funext i j
  show (w s).1 = 0
  exact hs

variable [LinearOrder R]

theorem weakA_aff1J (w : DLetter → R × R) (u v : List DLetter)
    (h : (ev1 w v).1 ≤ (ev1 w u).1 ∧ (ev1 w v).2 ≤ (ev1 w u).2) :
    WeakA (evA (aff1J w) u) (evA (aff1J w) v) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [(evA_aff1J w u).1, (evA_aff1J w v).1]; exact h.1
  · rw [(evA_aff1J w u).2, (evA_aff1J w v).2]; exact h.2

theorem weakA_aff1J_imp (w : DLetter → R × R) (u v : List DLetter)
    (h : WeakA (evA (aff1J w) u) (evA (aff1J w) v)) :
    (ev1 w v).1 ≤ (ev1 w u).1 ∧ (ev1 w v).2 ≤ (ev1 w u).2 := by
  have h1 := h.1 0 0
  have h2 := h.2 0
  rw [(evA_aff1J w u).1, (evA_aff1J w v).1] at h1
  rw [(evA_aff1J w u).2, (evA_aff1J w v).2] at h2
  exact ⟨h1, h2⟩

theorem weakTop_aff1J (w : DLetter → R × R) (u v : List DLetter)
    (h : (ev1 w v).1 ≤ (ev1 w u).1 ∧ (ev1 w v).2 ≤ (ev1 w u).2) :
    WeakTop Nat.one_pos (evA (aff1J w) u) (evA (aff1J w) v) := by
  refine ⟨fun j => ?_, ?_⟩
  · rw [(evA_aff1J w u).1, (evA_aff1J w v).1]; exact h.1
  · rw [(evA_aff1J w u).2, (evA_aff1J w v).2]; exact h.2

theorem strictTop_aff1J (w : DLetter → R × R) (u v : List DLetter)
    (h : GG (ev1 w u).1 (ev1 w v).1 ∧ GG (ev1 w u).2 (ev1 w v).2) :
    StrictTop Nat.one_pos (evA (aff1J w) u) (evA (aff1J w) v) := by
  refine ⟨fun j => ?_, ?_⟩
  · rw [(evA_aff1J w u).1, (evA_aff1J w v).1]; exact h.1
  · rw [(evA_aff1J w u).2, (evA_aff1J w v).2]; exact h.2

end Gen

/-! ## §2 Controls (the condition of constancy cannot be dropped) -/

/-- Building a counterexample to the general form (`𝔸_ℕ`, dimension 1): all absolute parts finite, `U` weakly oriented coefficientwise, `P` weakly, and `π₀ ∈ P` strictly. -/
theorem not_barrierDPFor_of_aff1 (w : DLetter → Arc × Arc) (L : List DLetter) (U : List Rule) (P : List DRule)
    (hSF : ∀ s ∈ L, (w s).2 ≠ 0)
    (hU : ∀ ρ ∈ U, (ev1 w ρ.plain.rhs).1 ≤ (ev1 w ρ.plain.lhs).1 ∧ (ev1 w ρ.plain.rhs).2 ≤ (ev1 w ρ.plain.lhs).2)
    (hP : ∀ π ∈ P, (ev1 w π.rhs).1 ≤ (ev1 w π.lhs).1 ∧ (ev1 w π.rhs).2 ≤ (ev1 w π.lhs).2)
    (π₀ : DRule) (h₀ : π₀ ∈ P) (hS : GG (ev1 w π₀.lhs).1 (ev1 w π₀.rhs).1 ∧ GG (ev1 w π₀.lhs).2 (ev1 w π₀.rhs).2) :
    ¬ NonVacuity.BarrierDPFor L U P := fun h =>
  h 1 Nat.one_pos (aff1J w) (fun s hs => Or.inl (hSF s hs))
    (fun ρ hρ => weakA_aff1J w _ _ (hU ρ hρ)) (fun π hπ => weakTop_aff1J w _ _ (hP π hπ)) π₀ h₀
    (strictTop_aff1J w _ _ hS)

/-- Building a counterexample to the general form (below zero, dimension 1): all absolute parts non-negative. -/
theorem not_barrierBZFor_of_aff1 (w : DLetter → ArcZ × ArcZ) (L : List DLetter) (U : List Rule) (P : List DRule)
    (hAP : ∀ s ∈ L, ArcZ.fin 0 ≤ (w s).2)
    (hU : ∀ ρ ∈ U, (ev1 w ρ.plain.rhs).1 ≤ (ev1 w ρ.plain.lhs).1 ∧ (ev1 w ρ.plain.rhs).2 ≤ (ev1 w ρ.plain.lhs).2)
    (hP : ∀ π ∈ P, (ev1 w π.rhs).1 ≤ (ev1 w π.lhs).1 ∧ (ev1 w π.rhs).2 ≤ (ev1 w π.lhs).2)
    (π₀ : DRule) (h₀ : π₀ ∈ P) (hS : GG (ev1 w π₀.lhs).1 (ev1 w π₀.rhs).1 ∧ GG (ev1 w π₀.lhs).2 (ev1 w π₀.rhs).2) :
    ¬ NonVacuity.BarrierBZFor L U P := fun h =>
  h 1 Nat.one_pos (aff1J w) (fun s hs => hAP s hs)
    (fun ρ hρ => weakA_aff1J w _ _ (hU ρ hρ)) (fun π hπ => weakTop_aff1J w _ _ (hP π hπ)) π₀ h₀
    (strictTop_aff1J w _ _ hS)

/-- The control solution (the 3 rules of $\mathcal T^{\mathrm{rev}}$; `[f]` is not constant), as pairs `(m, c)`. -/
def wCtrlF : DLetter → Arc × Arc
  | mark _ => (Arc.fin 0, Arc.fin 1)
  | plain lft => (0, Arc.fin 0)
  | plain d0 => (Arc.fin 3, Arc.fin 3)
  | plain d1 => (0, Arc.fin 0)
  | plain d2 => (Arc.fin 0, Arc.fin 3)
  | plain f => (Arc.fin 1, Arc.fin 2)
  | plain t => (Arc.fin 0, Arc.fin 3)
  | plain rgt => (Arc.fin 0, Arc.fin 0)

/-- The control solution (the 6 rules of $\mathcal T^{\mathrm{rev}}$; `[t]` is not constant). -/
def wCtrlT : DLetter → Arc × Arc
  | mark _ => (Arc.fin 0, Arc.fin 0)
  | plain lft => (0, Arc.fin 0)
  | plain d0 => (0, Arc.fin 0)
  | plain d1 => (Arc.fin 2, Arc.fin 2)
  | plain d2 => (Arc.fin 2, Arc.fin 3)
  | plain f => (Arc.fin 1, Arc.fin 1)
  | plain t => (Arc.fin 2, Arc.fin 3)
  | plain rgt => (Arc.fin 0, Arc.fin 0)

/-- The control solution (the 6 rules of $\mathcal H^{\mathrm{rev}}$; `[f]` and `[t]` are not constant). -/
def wCtrlH : DLetter → Arc × Arc
  | mark _ => (Arc.fin 0, Arc.fin 1)
  | plain lft => (0, Arc.fin 0)
  | plain d0 => (Arc.fin 3, Arc.fin 1)
  | plain d1 => (0, Arc.fin 0)
  | plain d2 => (Arc.fin 1, Arc.fin 3)
  | plain f => (Arc.fin 2, Arc.fin 1)
  | plain t => (Arc.fin 1, Arc.fin 3)
  | plain rgt => (Arc.fin 0, Arc.fin 0)

/-- **Control ($\mathcal T^{\mathrm{rev}}$, 3 rules, `𝔸_ℕ`)**: if `[f]` is not required to be constant, there is a somewhere finite interpretation (dimension 1) that weakly orients the 3 rules and `P_D^rev`
and strictly orients `.#f → .#`. -/
theorem not_barrier_revF : ¬ NonVacuity.BarrierDPFor lettersPDrev usableRevF pairsPDrev :=
  not_barrierDPFor_of_aff1 wCtrlF _ _ _ (by decide) (by decide) (by decide) _ List.mem_cons_self
    (by unfold GG; decide)

/-- **Control ($\mathcal T^{\mathrm{rev}}$, 6 rules, `𝔸_ℕ`)**: if `[t]` is not required to be constant, there is a somewhere finite interpretation (dimension 1) that weakly orients the 6 rules and `P_D^rev`
and strictly orients `.#f → .#`. -/
theorem not_barrier_revT : ¬ NonVacuity.BarrierDPFor lettersPDrev usableRevT pairsPDrev :=
  not_barrierDPFor_of_aff1 wCtrlT _ _ _ (by decide) (by decide) (by decide) _ List.mem_cons_self
    (by unfold GG; decide)

/-- **Control ($\mathcal H^{\mathrm{rev}}$, 6 rules, `𝔸_ℕ`)**: if `[f]` and `[t]` are not required to be constant, there is a somewhere finite interpretation (dimension 1) that weakly orients the 6 rules and `P_D^rev`
and strictly orients `.#ff → .#0`. -/
theorem not_barrier_revHFT : ¬ NonVacuity.BarrierDPFor lettersPDrev usableRevHFT HTPDB.pairsPDrevH :=
  not_barrierDPFor_of_aff1 wCtrlH _ _ _ (by decide) (by decide) (by decide) _ List.mem_cons_self
    (by unfold GG; decide)

/-- Maps weights over `𝔸_ℕ` to `𝔸_ℤ` (finite values are kept, −∞ goes to −∞). -/
def toZ (w : DLetter → Arc × Arc) : DLetter → ArcZ × ArcZ := fun s => (ArcZ.ofArc (w s).1, ArcZ.ofArc (w s).2)

/-- **Controls (below zero, the three cases)**: the same solutions have all absolute parts non-negative, so they are also absolutely positive interpretations below zero. -/
theorem not_barrierBZ_revF : ¬ NonVacuity.BarrierBZFor lettersPDrev usableRevF pairsPDrev :=
  not_barrierBZFor_of_aff1 (toZ wCtrlF) _ _ _ (by decide) (by decide) (by decide) _ List.mem_cons_self
    (by unfold GG; decide)

theorem not_barrierBZ_revT : ¬ NonVacuity.BarrierBZFor lettersPDrev usableRevT pairsPDrev :=
  not_barrierBZFor_of_aff1 (toZ wCtrlT) _ _ _ (by decide) (by decide) (by decide) _ List.mem_cons_self
    (by unfold GG; decide)

theorem not_barrierBZ_revHFT : ¬ NonVacuity.BarrierBZFor lettersPDrev usableRevHFT HTPDB.pairsPDrevH :=
  not_barrierBZFor_of_aff1 (toZ wCtrlH) _ _ _ (by decide) (by decide) (by decide) _ List.mem_cons_self
    (by unfold GG; decide)

/-! ## §3 Examples outside the hypotheses: the forms with filters are strictly wider than the frozen statements -/

/-- The solution of the example outside the hypotheses ($\mathcal T^{\mathrm{rev}}$, argument of `t` dropped): `.#` and `f` are `x ↦ x ⊕ 0`, `t`, `1`, `2` the constant 1, `0` and `/` the constant 0.
All absolute parts are non-negative. -/
def wOutT : DLetter → Arc × Arc
  | mark _ => (Arc.fin 0, Arc.fin 0)
  | plain f => (Arc.fin 0, Arc.fin 0)
  | plain t => (0, Arc.fin 1)
  | plain d0 => (0, Arc.fin 0)
  | plain d1 => (0, Arc.fin 1)
  | plain d2 => (0, Arc.fin 1)
  | plain lft => (0, Arc.fin 0)
  | plain rgt => (Arc.fin 0, Arc.fin 0)

/-- The solution of the example outside the hypotheses ($\mathcal H^{\mathrm{rev}}$, arguments of `f` and `t` dropped): `.#` is `x ↦ x ⊕ 0`, `f`, `t`, `0`, `2` the constant 1, `1` and `/` the constant 0. -/
def wOutH : DLetter → Arc × Arc
  | mark _ => (Arc.fin 0, Arc.fin 0)
  | plain f => (0, Arc.fin 1)
  | plain t => (0, Arc.fin 1)
  | plain d0 => (0, Arc.fin 1)
  | plain d1 => (0, Arc.fin 0)
  | plain d2 => (0, Arc.fin 1)
  | plain lft => (0, Arc.fin 0)
  | plain rgt => (Arc.fin 0, Arc.fin 0)

/-- **Example outside the hypotheses ($\mathcal T^{\mathrm{rev}}$, argument of `t` dropped, `𝔸_ℕ`)**: a somewhere finite interpretation (dimension 1) in which `[t]` is constant and which weakly orients the 6 rules and `P_D^rev` but not
`0t → t1`. The frozen `ArcticBarrierDPrev` does not apply to it directly;
`dprev_filt_t_arc` does. -/
theorem outside_revT : ∃ J : DLetter → AffFun Arc 1, SomewhereFinite Nat.one_pos J lettersPDrev ∧
    (J (plain t)).M = 0 ∧ (∀ ρ ∈ usableRevT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakTop Nat.one_pos (evA J π.lhs) (evA J π.rhs)) ∧
    ¬ ∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs) := by
  have hSF : ∀ s ∈ lettersPDrev, (wOutT s).2 ≠ 0 := by decide
  have hU : ∀ ρ ∈ usableRevT, (ev1 wOutT ρ.plain.rhs).1 ≤ (ev1 wOutT ρ.plain.lhs).1 ∧
      (ev1 wOutT ρ.plain.rhs).2 ≤ (ev1 wOutT ρ.plain.lhs).2 := by decide
  have hP : ∀ π ∈ pairsPDrev, (ev1 wOutT π.rhs).1 ≤ (ev1 wOutT π.lhs).1 ∧
      (ev1 wOutT π.rhs).2 ≤ (ev1 wOutT π.lhs).2 := by decide
  have hN : ¬ ((ev1 wOutT [plain t, plain d1]).1 ≤ (ev1 wOutT [plain d0, plain t]).1 ∧
      (ev1 wOutT [plain t, plain d1]).2 ≤ (ev1 wOutT [plain d0, plain t]).2) := by decide
  refine ⟨aff1J wOutT, fun s hs => Or.inl (hSF s hs), aff1J_M_zero wOutT _ rfl,
    fun ρ hρ => weakA_aff1J wOutT _ _ (hU ρ hρ), fun π hπ => weakTop_aff1J wOutT _ _ (hP π hπ), fun h => ?_⟩
  exact hN (weakA_aff1J_imp wOutT _ _ (h ⟨[d0, t], [t, d1]⟩ (by decide)))

/-- **Example outside the hypotheses ($\mathcal H^{\mathrm{rev}}$, arguments of `f` and `t` dropped, `𝔸_ℕ`)**: a somewhere finite interpretation (dimension 1) in which `[f]` and `[t]` are constant and which weakly orients the 6 rules and `P_D^rev`,
but not `1f → t0`. -/
theorem outside_revHFT : ∃ J : DLetter → AffFun Arc 1, SomewhereFinite Nat.one_pos J lettersPDrev ∧
    (J (plain f)).M = 0 ∧ (J (plain t)).M = 0 ∧
    (∀ ρ ∈ usableRevHFT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ HTPDB.pairsPDrevH, WeakTop Nat.one_pos (evA J π.lhs) (evA J π.rhs)) ∧
    ¬ ∀ ρ ∈ HTPDB.usableHTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs) := by
  have hSF : ∀ s ∈ lettersPDrev, (wOutH s).2 ≠ 0 := by decide
  have hU : ∀ ρ ∈ usableRevHFT, (ev1 wOutH ρ.plain.rhs).1 ≤ (ev1 wOutH ρ.plain.lhs).1 ∧
      (ev1 wOutH ρ.plain.rhs).2 ≤ (ev1 wOutH ρ.plain.lhs).2 := by decide
  have hP : ∀ π ∈ HTPDB.pairsPDrevH, (ev1 wOutH π.rhs).1 ≤ (ev1 wOutH π.lhs).1 ∧
      (ev1 wOutH π.rhs).2 ≤ (ev1 wOutH π.lhs).2 := by decide
  have hN : ¬ ((ev1 wOutH [plain t, plain d0]).1 ≤ (ev1 wOutH [plain d1, plain f]).1 ∧
      (ev1 wOutH [plain t, plain d0]).2 ≤ (ev1 wOutH [plain d1, plain f]).2) := by decide
  refine ⟨aff1J wOutH, fun s hs => Or.inl (hSF s hs), aff1J_M_zero wOutH _ rfl, aff1J_M_zero wOutH _ rfl,
    fun ρ hρ => weakA_aff1J wOutH _ _ (hU ρ hρ), fun π hπ => weakTop_aff1J wOutH _ _ (hP π hπ), fun h => ?_⟩
  exact hN (weakA_aff1J_imp wOutH _ _ (h ⟨[d1, f], [t, d0]⟩ (by decide)))

/-- **Example outside the hypotheses ($\mathcal T^{\mathrm{rev}}$, argument of `t` dropped, below zero)**: the same solution is absolutely positive. The frozen `ArcticBarrierBZrev` does not
apply to it directly. -/
theorem outside_revT_Z : ∃ J : DLetter → AffFun ArcZ 1, AbsPositive Nat.one_pos J lettersPDrev ∧
    (J (plain t)).M = 0 ∧ (∀ ρ ∈ usableRevT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakTop Nat.one_pos (evA J π.lhs) (evA J π.rhs)) ∧
    ¬ ∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs) := by
  have hAP : ∀ s ∈ lettersPDrev, ArcZ.fin 0 ≤ (toZ wOutT s).2 := by decide
  have hU : ∀ ρ ∈ usableRevT, (ev1 (toZ wOutT) ρ.plain.rhs).1 ≤ (ev1 (toZ wOutT) ρ.plain.lhs).1 ∧
      (ev1 (toZ wOutT) ρ.plain.rhs).2 ≤ (ev1 (toZ wOutT) ρ.plain.lhs).2 := by decide
  have hP : ∀ π ∈ pairsPDrev, (ev1 (toZ wOutT) π.rhs).1 ≤ (ev1 (toZ wOutT) π.lhs).1 ∧
      (ev1 (toZ wOutT) π.rhs).2 ≤ (ev1 (toZ wOutT) π.lhs).2 := by decide
  have hN : ¬ ((ev1 (toZ wOutT) [plain t, plain d1]).1 ≤ (ev1 (toZ wOutT) [plain d0, plain t]).1 ∧
      (ev1 (toZ wOutT) [plain t, plain d1]).2 ≤ (ev1 (toZ wOutT) [plain d0, plain t]).2) := by decide
  refine ⟨aff1J (toZ wOutT), fun s hs => hAP s hs, aff1J_M_zero (toZ wOutT) _ rfl,
    fun ρ hρ => weakA_aff1J _ _ _ (hU ρ hρ), fun π hπ => weakTop_aff1J _ _ _ (hP π hπ), fun h => ?_⟩
  exact hN (weakA_aff1J_imp _ _ _ (h ⟨[d0, t], [t, d1]⟩ (by decide)))

/-- **Example outside the hypotheses ($\mathcal H^{\mathrm{rev}}$, arguments of `f` and `t` dropped, below zero)**. -/
theorem outside_revHFT_Z : ∃ J : DLetter → AffFun ArcZ 1, AbsPositive Nat.one_pos J lettersPDrev ∧
    (J (plain f)).M = 0 ∧ (J (plain t)).M = 0 ∧
    (∀ ρ ∈ usableRevHFT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ HTPDB.pairsPDrevH, WeakTop Nat.one_pos (evA J π.lhs) (evA J π.rhs)) ∧
    ¬ ∀ ρ ∈ HTPDB.usableHTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs) := by
  have hAP : ∀ s ∈ lettersPDrev, ArcZ.fin 0 ≤ (toZ wOutH s).2 := by decide
  have hU : ∀ ρ ∈ usableRevHFT, (ev1 (toZ wOutH) ρ.plain.rhs).1 ≤ (ev1 (toZ wOutH) ρ.plain.lhs).1 ∧
      (ev1 (toZ wOutH) ρ.plain.rhs).2 ≤ (ev1 (toZ wOutH) ρ.plain.lhs).2 := by decide
  have hP : ∀ π ∈ HTPDB.pairsPDrevH, (ev1 (toZ wOutH) π.rhs).1 ≤ (ev1 (toZ wOutH) π.lhs).1 ∧
      (ev1 (toZ wOutH) π.rhs).2 ≤ (ev1 (toZ wOutH) π.lhs).2 := by decide
  have hN : ¬ ((ev1 (toZ wOutH) [plain t, plain d0]).1 ≤ (ev1 (toZ wOutH) [plain d1, plain f]).1 ∧
      (ev1 (toZ wOutH) [plain t, plain d0]).2 ≤ (ev1 (toZ wOutH) [plain d1, plain f]).2) := by decide
  refine ⟨aff1J (toZ wOutH), fun s hs => hAP s hs, aff1J_M_zero (toZ wOutH) _ rfl, aff1J_M_zero (toZ wOutH) _ rfl,
    fun ρ hρ => weakA_aff1J _ _ _ (hU ρ hρ), fun π hπ => weakTop_aff1J _ _ _ (hP π hπ), fun h => ?_⟩
  exact hN (weakA_aff1J_imp _ _ _ (h ⟨[d1, f], [t, d0]⟩ (by decide)))

end Collatz.Arctic.DPFilter
