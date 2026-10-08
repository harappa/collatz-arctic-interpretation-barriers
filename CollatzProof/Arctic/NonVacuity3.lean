/-
Checks of the non-vacuity of the main statements (continued; §4 and §5 of `NonVacuity.lean`): whether strict orientation is possible by definition ((ii)),
the fact that the two commutation rules are never strictly oriented, and counterexamples for subsystems.
-/
import CollatzProof.Arctic.NonVacuity2

namespace Collatz.Arctic

namespace NonVacuity

open Letter DLetter Matrix

/-! ## §4 (ii) Is strict orientation possible by definition? -/

/-- The weight counting the occurrences of the symbol `x`. -/
def ind (x : Letter) : Letter → ℕ := fun s => if s = x then 1 else 0

/-- The version including marked symbols. -/
def indD (x : DLetter) : DLetter → ℕ := fun s => if s = x then 1 else 0

/-- The list of symbols for dependency pairs. -/
def dletters : List DLetter :=
  [mark lft, mark rgt, plain f, plain t, plain d0, plain d1, plain d2, plain lft, plain rgt]

/-- Each of the 9 rules other than the two commutation rules strictly decreases the number of occurrences of some symbol. -/
theorem strict_ST_ind : ∀ ρ ∈ rulesST, ρ ≠ ⟨[f, d0], [d0, f]⟩ → ρ ≠ ⟨[t, d2], [d2, t]⟩ →
    ∃ x ∈ [f, t, d0, d1, d2, lft, rgt], (ρ.rhs.map (ind x)).sum < (ρ.lhs.map (ind x)).sum := by
  decide

/-- Each of the 9 rules that are not commutation rules is strictly oriented by some interpretation (dimension 1, `Fin00`). -/
theorem strict_possible_ST : ∀ ρ ∈ rulesST, ρ ≠ ⟨[f, d0], [d0, f]⟩ → ρ ≠ ⟨[t, d2], [d2, t]⟩ →
    ∃ I : Interp 1, Fin00 Nat.one_pos I ∧ Strict I ρ := by
  intro ρ hρ h1 h2
  obtain ⟨x, -, hx⟩ := strict_ST_ind ρ hρ h1 h2
  exact ⟨wI (ind x), fin00_wI _, (strict_wI _ _).2 hx⟩

/-- **A commutation rule `a b → b a` is strictly oriented by no arctic interpretation (`Fin00`) of any dimension.**
The max-plus trace `max_{i,k} (A_{ik} + B_{ki})` is common to `AB` and `BA`, and it is finite since it is at least `A₀₀ + B₀₀`.
At a maximizing `(i, k)`, `(BA)_{kk} ≥ A_{ik} + B_{ki} ≥ (AB)_{kk}`, which is incompatible with `(AB)_{kk} ≫ (BA)_{kk}`.
The orientation of other rules is not used (the conclusion of the main theorem for `f d0 → d0 f` and `t d2 → d2 t` of $\mathcal T$ is trivial). -/
theorem not_strict_swap {d : ℕ} (hd : 0 < d) (I : Interp d) (hfin : Fin00 hd I) (a b : Letter) :
    ¬ Strict I ⟨[a, b], [b, a]⟩ := by
  intro hs
  set A := I a with hA
  set B := I b with hB
  have hl : ev I [a, b] = A * B := by simp [ev, hA, hB]
  have hr : ev I [b, a] = B * A := by simp [ev, hA, hB]
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  obtain ⟨⟨i, k⟩, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun p : Fin d × Fin d => A p.1 p.2 * B p.2 p.1) hne
  have h00 : A ⟨0, hd⟩ ⟨0, hd⟩ * B ⟨0, hd⟩ ⟨0, hd⟩ ≤ A i k * B k i :=
    hmax (⟨0, hd⟩, ⟨0, hd⟩) (Finset.mem_univ _)
  have hf00 : Arc.val (A ⟨0, hd⟩ ⟨0, hd⟩ * B ⟨0, hd⟩ ⟨0, hd⟩) ≠ ⊥ :=
    Arc.mul_ne_zero_of (hfin a) (hfin b)
  have hlow : A i k * B k i ≤ (B * A) k k := by
    rw [Matrix.mul_apply, mul_comm]
    exact Arc.le_sum_of_mem (fun m => B k m * A m k) (Finset.mem_univ i)
  have hup : (A * B) k k ≤ A i k * B k i := by
    rw [Matrix.mul_apply, Arc.le_iff_val, Arc.val_sum]
    exact Finset.sup_le (fun m _ => hmax (k, m) (Finset.mem_univ _))
  have hst := hs k k
  dsimp only at hst
  rw [hl, hr] at hst
  rcases hst with h | ⟨_, h0⟩
  · exact absurd (lt_of_le_of_lt hlow (lt_of_lt_of_le h hup)) (lt_irrefl _)
  · apply hf00
    have : A ⟨0, hd⟩ ⟨0, hd⟩ * B ⟨0, hd⟩ ⟨0, hd⟩ ≤ 0 := h0 ▸ h00.trans hlow
    exact le_bot_iff.mp this

/-- Complete classification of the strict orientability of the rules of $\mathcal T$: the rules strictly oriented by some interpretation are exactly the
9 rules other than the two commutation rules. -/
theorem strict_possible_iff_ST : ∀ ρ ∈ rulesST,
    (∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧ Strict I ρ) ↔
      (ρ ≠ ⟨[f, d0], [d0, f]⟩ ∧ ρ ≠ ⟨[t, d2], [d2, t]⟩) := by
  intro ρ hρ
  constructor
  · rintro ⟨d, hd, I, hfin, hs⟩
    refine ⟨?_, ?_⟩
    · rintro rfl; exact not_strict_swap hd I hfin f d0 hs
    · rintro rfl; exact not_strict_swap hd I hfin t d2 hs
  · rintro ⟨h1, h2⟩
    obtain ⟨I, hfin, hs⟩ := strict_possible_ST ρ hρ h1 h2
    exact ⟨1, Nat.one_pos, I, hfin, hs⟩

/-- Every dependency pair of `P_B` is strictly oriented in the first row by some interpretation (`𝔸_ℕ` and below zero). -/
theorem strict_PB_ind : ∀ π ∈ pairsPB, ∃ x ∈ dletters,
    (π.rhs.map (indD x)).sum < (π.lhs.map (indD x)).sum := by decide

theorem strict_PDrev_ind : ∀ π ∈ pairsPDrev, ∃ x ∈ dletters,
    (π.rhs.map (indD x)).sum < (π.lhs.map (indD x)).sum := by decide

theorem strict_possible_DP : ∀ π ∈ pairsPB, ∃ J : DLetter → AffFun Arc 1,
    SomewhereFinite Nat.one_pos J lettersPB ∧ StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ
  obtain ⟨x, -, hx⟩ := strict_PB_ind π hπ
  exact ⟨wJ (indD x), sf_wJ _ _, (strictTop_wJ _ _ _).2 hx⟩

theorem strict_possible_DPrev : ∀ π ∈ pairsPDrev, ∃ J : DLetter → AffFun Arc 1,
    SomewhereFinite Nat.one_pos J lettersPDrev ∧
      StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ
  obtain ⟨x, -, hx⟩ := strict_PDrev_ind π hπ
  exact ⟨wJ (indD x), sf_wJ _ _, (strictTop_wJ _ _ _).2 hx⟩

theorem strict_possible_BZ : ∀ π ∈ pairsPB, ∃ J : DLetter → AffFun ArcZ 1,
    AbsPositive Nat.one_pos J lettersPB ∧ StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ
  obtain ⟨x, -, hx⟩ := strict_PB_ind π hπ
  exact ⟨wJZ (indD x), ap_wJZ _ _,
    (strictTop_wJZ _ (pairsPB_ne π hπ).1 (pairsPB_ne π hπ).2).2 hx⟩

theorem strict_possible_BZrev : ∀ π ∈ pairsPDrev, ∃ J : DLetter → AffFun ArcZ 1,
    AbsPositive Nat.one_pos J lettersPDrev ∧
      StrictTop Nat.one_pos (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ
  obtain ⟨x, -, hx⟩ := strict_PDrev_ind π hπ
  exact ⟨wJZ (indD x), ap_wJZ _ _,
    (strictTop_wJZ _ (pairsPDrev_ne π hπ).1 (pairsPDrev_ne π hπ).2).2 hx⟩

/-! ## §5 Counterexamples for subsystems (all rules weakly, some rule strictly) -/

/-- The number of ternary digits. -/
def wDig : Letter → ℕ
  | d0 => 1
  | d1 => 1
  | d2 => 1
  | _ => 0

/-- The number of binary digits. -/
def wBit : Letter → ℕ
  | f => 1
  | t => 1
  | _ => 0

/-- The terminating system `A ∪ B` obtained from $\mathcal T$ by removing the dynamic rules (9 rules). -/
def rulesAB : List Rule := rulesST.drop 2

/-- The terminating system `D_T ∪ A` obtained from $\mathcal T$ by removing the left-end rules (8 rules, the same as `usableST`). -/
def rulesDA : List Rule := rulesST.take 8

theorem rulesDA_eq : rulesDA = usableST := by decide

/-- `A ∪ B`: the number of ternary digits weakly orients A and strictly orients the three left-end rules. -/
theorem AB_oriented : Fin00 Nat.one_pos (wI wDig) ∧ (∀ ρ ∈ rulesAB, Weak (wI wDig) ρ) ∧
    ∀ ρ ∈ rulesST.drop 8, Strict (wI wDig) ρ :=
  ⟨fin00_wI _, fun ρ hρ => (weak_wI _ ρ).2 (by revert ρ; decide),
    fun ρ hρ => (strict_wI _ ρ).2 (by revert ρ; decide)⟩

theorem not_barrier_AB : ¬ BarrierFor rulesAB := fun h =>
  h 1 Nat.one_pos (wI wDig) AB_oriented.1 AB_oriented.2.1 ⟨[lft, d0], [lft, t]⟩ (by decide)
    (AB_oriented.2.2 _ (by decide))

/-- `D_T ∪ A`: the number of binary digits weakly orients A and strictly orients the two dynamic rules. -/
theorem DA_oriented : Fin00 Nat.one_pos (wI wBit) ∧ (∀ ρ ∈ rulesDA, Weak (wI wBit) ρ) ∧
    ∀ ρ ∈ rulesST.take 2, Strict (wI wBit) ρ :=
  ⟨fin00_wI _, fun ρ hρ => (weak_wI _ ρ).2 (by revert ρ; decide),
    fun ρ hρ => (strict_wI _ ρ).2 (by revert ρ; decide)⟩

theorem not_barrier_DA : ¬ BarrierFor rulesDA := fun h =>
  h 1 Nat.one_pos (wI wBit) DA_oriented.1 DA_oriented.2.1 ⟨[f, rgt], [rgt]⟩ (by decide)
    (DA_oriented.2.2 _ (by decide))

/-- A weight for dependency pairs: the number of unmarked ternary digits. -/
def wDigD : DLetter → ℕ
  | plain d0 => 1
  | plain d1 => 1
  | plain d2 => 1
  | _ => 0

/-- A weight for dependency pairs: the number of unmarked binary digits. -/
def wBitD : DLetter → ℕ
  | plain f => 1
  | plain t => 1
  | _ => 0

/-- `U` without the dynamic rules (the six carry rules A). -/
def usableA : List Rule := usableST.drop 2

/-- The reversed `U` without the left-end rules (the six rules of `A^rev`). -/
def usableArev : List Rule := usableSTrev.take 6

theorem usableA_ne : ∀ ρ ∈ usableA, ρ.plain.lhs ≠ [] ∧ ρ.plain.rhs ≠ [] := by decide
theorem usableArev_ne : ∀ ρ ∈ usableArev, ρ.plain.lhs ≠ [] ∧ ρ.plain.rhs ≠ [] := by decide

/-- Forward (`𝔸_ℕ`): for `(P_B, A)`, the number of ternary digits weakly orients `A` and strictly orients all of `P_B`. -/
theorem not_barrierDP_A : ¬ BarrierDPFor lettersPB usableA pairsPB := by
  intro h
  have hU : ∀ ρ ∈ usableA, (ρ.plain.rhs.map wDigD).sum ≤ (ρ.plain.lhs.map wDigD).sum := by decide
  have hS : ∀ π ∈ pairsPB, (π.rhs.map wDigD).sum < (π.lhs.map wDigD).sum := by decide
  exact h 1 Nat.one_pos (wJ wDigD) (sf_wJ _ _) (fun ρ hρ => (weakA_wJ _ _ _).2 (hU ρ hρ))
    (fun π hπ => (weakTop_wJ _ _ _).2 (le_of_lt (hS π hπ))) _ (List.mem_cons_self ..)
    ((strictTop_wJ _ _ _).2 (hS _ (List.mem_cons_self ..)))

/-- Reversed (`𝔸_ℕ`): for `(P_D^rev, A^rev)`, the number of binary digits weakly orients `A^rev` and strictly orients all of `P_D^rev`. -/
theorem not_barrierDPrev_A : ¬ BarrierDPFor lettersPDrev usableArev pairsPDrev := by
  intro h
  have hU : ∀ ρ ∈ usableArev, (ρ.plain.rhs.map wBitD).sum ≤ (ρ.plain.lhs.map wBitD).sum := by decide
  have hS : ∀ π ∈ pairsPDrev, (π.rhs.map wBitD).sum < (π.lhs.map wBitD).sum := by decide
  exact h 1 Nat.one_pos (wJ wBitD) (sf_wJ _ _) (fun ρ hρ => (weakA_wJ _ _ _).2 (hU ρ hρ))
    (fun π hπ => (weakTop_wJ _ _ _).2 (le_of_lt (hS π hπ))) _ (List.mem_cons_self ..)
    ((strictTop_wJ _ _ _).2 (hS _ (List.mem_cons_self ..)))

/-- Forward (below zero): the same. -/
theorem not_barrierBZ_A : ¬ BarrierBZFor lettersPB usableA pairsPB := by
  intro h
  have hU : ∀ ρ ∈ usableA, (ρ.plain.rhs.map wDigD).sum ≤ (ρ.plain.lhs.map wDigD).sum := by decide
  have hS : ∀ π ∈ pairsPB, (π.rhs.map wDigD).sum < (π.lhs.map wDigD).sum := by decide
  have hP := List.mem_cons_self (a := (⟨[mark lft, plain d0], [mark lft, plain t]⟩ : DRule))
    (l := pairsPB.tail)
  exact h 1 Nat.one_pos (wJZ wDigD) (ap_wJZ _ _)
    (fun ρ hρ => (weakA_wJZ _ (usableA_ne ρ hρ).1 (usableA_ne ρ hρ).2).2 (hU ρ hρ))
    (fun π hπ => (weakTop_wJZ _ (pairsPB_ne π hπ).1 (pairsPB_ne π hπ).2).2 (le_of_lt (hS π hπ)))
    _ hP ((strictTop_wJZ _ (pairsPB_ne _ hP).1 (pairsPB_ne _ hP).2).2 (hS _ hP))

/-- Reversed (below zero): the same. -/
theorem not_barrierBZrev_A : ¬ BarrierBZFor lettersPDrev usableArev pairsPDrev := by
  intro h
  have hU : ∀ ρ ∈ usableArev, (ρ.plain.rhs.map wBitD).sum ≤ (ρ.plain.lhs.map wBitD).sum := by decide
  have hS : ∀ π ∈ pairsPDrev, (π.rhs.map wBitD).sum < (π.lhs.map wBitD).sum := by decide
  have hP := List.mem_cons_self (a := (⟨[mark rgt, plain f], [mark rgt]⟩ : DRule))
    (l := pairsPDrev.tail)
  exact h 1 Nat.one_pos (wJZ wBitD) (ap_wJZ _ _)
    (fun ρ hρ => (weakA_wJZ _ (usableArev_ne ρ hρ).1 (usableArev_ne ρ hρ).2).2 (hU ρ hρ))
    (fun π hπ => (weakTop_wJZ _ (pairsPDrev_ne π hπ).1 (pairsPDrev_ne π hπ).2).2
      (le_of_lt (hS π hπ)))
    _ hP ((strictTop_wJZ _ (pairsPDrev_ne _ hP).1 (pairsPDrev_ne _ hP).2).2 (hS _ hP))

/-- The reversed problem with `U` unchanged and `P` reduced to `.#f → .#`: the weights 1 on `f`, `t` and 2 on the ternary digits
weakly orient `U` and strictly orient this pair (the barrier needs `.#t → .#2` in `P`). -/
def wRevOne : DLetter → ℕ
  | plain f => 1
  | plain t => 1
  | plain d0 => 2
  | plain d1 => 2
  | plain d2 => 2
  | _ => 0

theorem not_barrierDPrev_one :
    ¬ BarrierDPFor lettersPDrev usableSTrev [⟨[mark rgt, plain f], [mark rgt]⟩] := by
  intro h
  have hU : ∀ ρ ∈ usableSTrev, (ρ.plain.rhs.map wRevOne).sum ≤ (ρ.plain.lhs.map wRevOne).sum := by
    decide
  have hS : ∀ π ∈ ([⟨[mark rgt, plain f], [mark rgt]⟩] : List DRule),
      (π.rhs.map wRevOne).sum < (π.lhs.map wRevOne).sum := by decide
  exact h 1 Nat.one_pos (wJ wRevOne) (sf_wJ _ _) (fun ρ hρ => (weakA_wJ _ _ _).2 (hU ρ hρ))
    (fun π hπ => (weakTop_wJ _ _ _).2 (le_of_lt (hS π hπ))) _ (List.mem_cons_self ..)
    ((strictTop_wJ _ _ _).2 (hS _ (List.mem_cons_self ..)))

end NonVacuity

end Collatz.Arctic
