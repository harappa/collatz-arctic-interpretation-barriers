/-
# The dependency pair forms: when argument filters shrink the usable rules (a remark of the internal review of the dependency pair statements; Proposition 13.4 of the paper)

The form of Def 20 and Def 21 (the usable rules `U_R(P, π)` for an argument filter `π`) and Thm 26 (the reduction pair processor with filters) of
GTSF06 (Giesl–Thiemann–Schneider-Kamp–Falke, JAR 37 (2006)). In a string rewriting system the letters are unary, and there are two cases: `π(s) = []` (the argument is dropped)
or the argument is kept (`[1]`, or collapsed, `1`). For natural-number matrix interpretations, dropping the argument corresponds to `M_s = 0` (`[s]` is a constant)
(collapsing means taking `[s]` to be the identity, a special case of `NAff`).

* §1 The usable rules with a filter, `usableFilt R P F` (`F` is the set of letters whose argument is dropped): as in Def 21, the rules of the root letter of a term `s₁(s₂(⋯))`
  are always included, and those of a letter below it only if all letters above it keep their argument (`regPrefix`). The marked root of the right-hand side of a dependency pair is
  assumed to keep its argument (dropping it makes `[h#]` a constant, and strict orientation trivially does not occur: `markConst_not_strict` of §2).
  - Forward: `U(P_B, π) = U = D_T ∪ A` for every `F` (`usableFilt_fwd`; directly below `/#` are `f`, `t`, and the rules of `f`, `t` are all of `U`).
  - Reversed: 3 rules (`2f → f1`, `2t → t2`, `2/ → tf/`) if `f ∈ F`; 6 rules (the rules of `1`, `2`) if `f ∉ F` and `t ∈ F`; otherwise
    `A^rev ∪ B^rev` (`usableFilt_rev`). The first two are outside the premises of `NatBarrierDPrev`.
* §2 In the reversed cases of `f` and `t`, the conclusion holds even though the usable rules shrink (**without the value-level core, without hypotheses**):
  - `f ∈ F` (`[f]` is a constant): the weak orientation of `.#f → .#` in the first component makes the first row of `[.#]` zero, and the first component of the value of every dependency pair is `(v_.#)₀`
    on both sides (`dpRev_filt_f`).
  - `t ∈ F` (`[t]` is a constant): the value of `rev (can n) = . t ⋯` for odd `n` does not depend on `n`. The mirrored canonical derivation `13 → 20 → 10 → 5`
    uses only the 6 rules and the two top rules, so a strictly oriented top rule decreases the value by at least 1, and `Φ^rev(5) < Φ^rev(13) = Φ^rev(5)` is a contradiction
    (`dpRev_filt_t`). The written argument of the reviewer of the statements (the rules of `d0` are used only below `t`) was formalized in Lean with a single chain.
* §3 The forms with filters `NatBarrierDPFilt`, `NatBarrierDPrevFilt` (for every filter: if the `M` of the dropped letters is 0 and the interpretation weakly orients the usable rules
  with the filter entrywise and the dependency pairs in the first component, then it strictly orients no dependency pair in the first component) follow from `NatBarrierDP` and
  `NatBarrierDPrev`, respectively (`natBarrierDPFilt_of_DP`, `natBarrierDPrevFilt_of_DPrev`).
-/
import CollatzProof.Arctic.Nat.BridgeDP

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter DLetter

namespace W5

/-! ## §1 The usable rules with a filter (Def 20 and Def 21 of GTSF06) -/

/-- The part that is kept: the letters of a term `s₁(s₂(⋯))` up to the first letter whose argument is dropped (including that letter). -/
def regPrefix (F : List Letter) : Word → Word
  | [] => []
  | s :: w => if s ∈ F then [s] else s :: regPrefix F w

/-- The unmarked letters below the marked root letter of the right-hand side of a dependency pair. -/
def dpTail (π : DRule) : Word := π.rhs.tail.filterMap fun s => match s with
  | plain x => some x
  | mark _ => none

/-- One step of the closure: add to a set of letters the letters of the kept parts of the right-hand sides of the rules whose left-hand root is in the set. -/
def filtStep (R : List Rule) (pre : Word → Word) (S : List Letter) : List Letter :=
  ((R.filter (fun ρ => match ρ.lhs.head? with
    | some h => decide (h ∈ S)
    | none => false)).flatMap (fun ρ => pre ρ.rhs)).foldl (fun acc x => acc.insert x) S

def filtIter (R : List Rule) (pre : Word → Word) (S : List Letter) : ℕ → List Letter
  | 0 => S
  | n + 1 => filtStep R pre (filtIter R pre S n)

/-- The usable rules for the function `pre` of kept parts (there are 7 letters, so the closure is reached in 7 steps: `filtIter_stable_*`). -/
def usableWith (R : List Rule) (P : List DRule) (pre : Word → Word) : List Rule :=
  R.filter fun ρ => match ρ.lhs.head? with
    | some h => decide (h ∈ filtIter R pre (P.flatMap fun π => pre (dpTail π)) 7)
    | none => false

/-- **The usable rules `U_R(P, π)` of Def 21 of GTSF06** (`F` is the set of letters whose argument is dropped). -/
def usableFilt (R : List Rule) (P : List DRule) (F : List Letter) : List Rule := usableWith R P (regPrefix F)

theorem regPrefix_congr {F F' : List Letter} (h : ∀ s, s ∈ F ↔ s ∈ F') : ∀ w, regPrefix F w = regPrefix F' w
  | [] => rfl
  | s :: w => by
    simp only [regPrefix, regPrefix_congr h w]
    by_cases hs : s ∈ F
    · simp [hs, (h s).1 hs]
    · have hs' : s ∉ F' := fun e => hs ((h s).2 e)
      simp [hs, hs']

/-- The usable rules depend only on the set of dropped letters (not on the order or on repetitions). -/
theorem usableFilt_congr (R : List Rule) (P : List DRule) {F F' : List Letter} (h : ∀ s, s ∈ F ↔ s ∈ F') :
    usableFilt R P F = usableFilt R P F' := by
  unfold usableFilt
  rw [show regPrefix F = regPrefix F' from funext (regPrefix_congr h)]

/-- The 7 letters. -/
def lettersAll : List Letter := [f, t, d0, d1, d2, lft, rgt]

theorem mem_lettersAll (s : Letter) : s ∈ lettersAll := by cases s <;> decide

theorem filter_mem_iff (F : List Letter) (s : Letter) : s ∈ F ↔ s ∈ lettersAll.filter (fun x => decide (x ∈ F)) := by
  simp [mem_lettersAll]

theorem filter_mem_sublists (F : List Letter) : lettersAll.filter (fun x => decide (x ∈ F)) ∈ lettersAll.sublists :=
  List.mem_sublists.2 List.filter_sublist

/-- The reversed usable rules when `f` is dropped (3 rules). -/
def usableRevF : List Rule := [⟨[d2, f], [f, d1]⟩, ⟨[d2, t], [t, d2]⟩, ⟨[d2, lft], [t, f, lft]⟩]

/-- The reversed usable rules when `t` is dropped and `f` is kept (6 rules: the rules of `1`, `2`). -/
def usableRevT : List Rule :=
  [⟨[d1, f], [t, d0]⟩, ⟨[d2, f], [f, d1]⟩, ⟨[d1, t], [f, d2]⟩, ⟨[d2, t], [t, d2]⟩,
    ⟨[d1, lft], [f, f, lft]⟩, ⟨[d2, lft], [t, f, lft]⟩]

theorem usableFilt_rev_table : ∀ G ∈ lettersAll.sublists, usableFilt rulesSTrev pairsPDrev G =
    if f ∈ G then usableRevF else if t ∈ G then usableRevT else usableSTrev := by
  decide +kernel

theorem usableFilt_fwd_table : ∀ G ∈ lettersAll.sublists, usableFilt rulesST pairsPB G = usableST := by
  decide +kernel

/-- The closure is stable after 7 steps (for every filter, no new letter is added at the 8th step). -/
theorem filtIter_stable : ∀ G ∈ lettersAll.sublists,
    (∀ x ∈ filtIter rulesSTrev (regPrefix G) (pairsPDrev.flatMap fun π => regPrefix G (dpTail π)) 8,
      x ∈ filtIter rulesSTrev (regPrefix G) (pairsPDrev.flatMap fun π => regPrefix G (dpTail π)) 7) ∧
    (∀ x ∈ filtIter rulesST (regPrefix G) (pairsPB.flatMap fun π => regPrefix G (dpTail π)) 8,
      x ∈ filtIter rulesST (regPrefix G) (pairsPB.flatMap fun π => regPrefix G (dpTail π)) 7) := by
  decide +kernel

/-- **The reversed usable rules with a filter**: 3 rules if `f` is dropped, 6 rules if only `t` is dropped, `A^rev ∪ B^rev` otherwise. -/
theorem usableFilt_rev (F : List Letter) : usableFilt rulesSTrev pairsPDrev F =
    if f ∈ F then usableRevF else if t ∈ F then usableRevT else usableSTrev := by
  rw [usableFilt_congr _ _ (filter_mem_iff F), usableFilt_rev_table _ (filter_mem_sublists F)]
  simp only [← filter_mem_iff]

/-- **The forward usable rules with a filter**: `U = D_T ∪ A` for every filter. -/
theorem usableFilt_fwd (F : List Letter) : usableFilt rulesST pairsPB F = usableST := by
  rw [usableFilt_congr _ _ (filter_mem_iff F), usableFilt_fwd_table _ (filter_mem_sublists F)]

theorem usableFilt_rev_none : usableFilt rulesSTrev pairsPDrev [] = usableSTrev := by decide +kernel

/-! ## §2 The reversed cases of `f` and `t` -/

variable {d : ℕ}

theorem comp_of_M_zero (F G : NAff d) (hF : F.M = 0) : F.comp G = ⟨0, F.v⟩ := by
  simp [NAff.comp, hF]

/-- If the first row of a marked letter is zero, the 0-th component of the value of a string beginning with that letter is `(v_{h#})₀`. -/
theorem evND_mark_v0 [NeZero d] (J : DLetter → NAff d) (h : Letter) (hrow : ∀ j, (J (mark h)).M 0 j = 0)
    (w : List DLetter) : (evND J (mark h :: w)).v 0 = (J (mark h)).v 0 := by
  show ((J (mark h)).comp (evND J w)).v 0 = _
  simp [NAff.comp, mulVec, dotProduct, hrow]

theorem pairsPDrev_head : ∀ π ∈ pairsPDrev, ∃ l r, π.lhs = mark rgt :: l ∧ π.rhs = mark rgt :: r := by
  intro π hπ
  simp only [pairsPDrev, List.mem_cons, List.mem_nil_iff, or_false] at hπ
  rcases hπ with rfl | rfl <;> exact ⟨_, _, rfl, rfl⟩

theorem pairsPB_head : ∀ π ∈ pairsPB, ∃ l r, π.lhs = mark lft :: l ∧ π.rhs = mark lft :: r := by
  intro π hπ
  simp only [pairsPB, List.mem_cons, List.mem_nil_iff, or_false] at hπ
  rcases hπ with rfl | rfl | rfl <;> exact ⟨_, _, rfl, rfl⟩

/-- A dependency pair beginning with a marked letter whose first row is zero cannot be strictly oriented in the first component. -/
theorem not_strict_of_row0_zero [NeZero d] (J : DLetter → NAff d) (h : Letter) (hrow : ∀ j, (J (mark h)).M 0 j = 0)
    {π : DRule} (hl : ∃ l, π.lhs = mark h :: l) (hr : ∃ r, π.rhs = mark h :: r) : ¬ NStrictTopD J π := by
  rintro ⟨-, hs⟩
  obtain ⟨l, hl⟩ := hl
  obtain ⟨r, hr⟩ := hr
  rw [hl, hr, evND_mark_v0 J h hrow, evND_mark_v0 J h hrow] at hs
  exact lt_irrefl _ hs

/-- **When the argument of the marked letter is dropped** (`M_{h#} = 0`, `[h#]` is a constant): no dependency pair can be strictly oriented in the first component (trivial). -/
theorem markConst_not_strict [NeZero d] (J : DLetter → NAff d) :
    ((J (mark rgt)).M = 0 → ∀ π ∈ pairsPDrev, ¬ NStrictTopD J π) ∧
      ((J (mark lft)).M = 0 → ∀ π ∈ pairsPB, ¬ NStrictTopD J π) := by
  refine ⟨fun h0 π hπ => ?_, fun h0 π hπ => ?_⟩
  · obtain ⟨l, r, hl, hr⟩ := pairsPDrev_head π hπ
    exact not_strict_of_row0_zero J rgt (fun j => by simp [h0]) ⟨l, hl⟩ ⟨r, hr⟩
  · obtain ⟨l, r, hl, hr⟩ := pairsPB_head π hπ
    exact not_strict_of_row0_zero J lft (fun j => by simp [h0]) ⟨l, hl⟩ ⟨r, hr⟩

/-- **Reversed, `f` dropped** (`[f]` is a constant): weakly orienting `.#f → .#` in the first component already implies that no dependency pair can be strictly oriented
in the first component (the premise on the usable rules is not needed either). -/
theorem dpRev_filt_f [NeZero d] (J : DLetter → NAff d) (hf : (J (plain f)).M = 0)
    (hP0 : NWeakTopD J ⟨[mark rgt, plain f], [mark rgt]⟩) : ∀ π ∈ pairsPDrev, ¬ NStrictTopD J π := by
  have hrow : ∀ j, (J (mark rgt)).M 0 j = 0 := by
    intro j
    have := hP0.1 j
    simp [evND, NAff.comp, NAff.id, hf] at this
    omega
  intro π hπ
  obtain ⟨l, r, hl, hr⟩ := pairsPDrev_head π hπ
  exact not_strict_of_row0_zero J rgt hrow ⟨l, hl⟩ ⟨r, hr⟩

/-- One step at the top by a rule weakly oriented in the first component only does not increase the value. -/
theorem phiN_top_row0_le [NeZero d] {I : Letter → NAff d} {ρ : Rule} (h : Row0Weak I ρ) (q : Word) :
    PhiN I (ρ.rhs ++ q) ≤ PhiN I (ρ.lhs ++ q) := by
  rw [phiN_eq, phiN_eq, evN_append, evN_append]
  simp only [NAff.comp, Pi.add_apply, mulVec, dotProduct]
  exact add_le_add (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (h.1 j)) h.2

/-- One step at the top by a rule strictly oriented in the first component decreases the value by at least 1. -/
theorem phiN_top_row0_lt [NeZero d] {I : Letter → NAff d} {ρ : Rule} (h : Row0Strict I ρ) (q : Word) :
    PhiN I (ρ.rhs ++ q) + 1 ≤ PhiN I (ρ.lhs ++ q) := by
  rw [phiN_eq, phiN_eq, evN_append, evN_append]
  simp only [NAff.comp, Pi.add_apply, mulVec, dotProduct]
  have := Finset.sum_le_sum (s := Finset.univ) fun j (_ : j ∈ Finset.univ) =>
    Nat.mul_le_mul_right ((evN I q).v j) (h.1 j)
  have h2 := h.2
  omega

/-- Along derivations of 𝒯^rev that start in top form, if the top rules used are weakly oriented in the first component and the other rules used are weakly oriented entrywise, then
the value does not increase, and it decreases by at least the number of uses of a top rule `ρ0` strictly oriented in the first component (nothing is required of rules that are not used). -/
theorem chain_count_row0 [NeZero d] {I : Letter → NAff d} {ρ0 : Rule} (hρ0 : ρ0 ∈ rulesSTrevTop)
    (hs : Row0Strict I ρ0) :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v → (∀ σ ∈ rs, σ ∈ rulesSTrev) →
      (∀ σ ∈ rs, σ ∈ rulesSTrevTop → Row0Weak I σ) → (∀ σ ∈ rs, σ ∉ rulesSTrevTop → NWeak I σ) →
      TopWordR u → PhiN I v + rs.count ρ0 ≤ PhiN I u := by
  intro rs u v hc
  induction hc with
  | nil u => intro _ _ _ _; simp
  | @cons σ rs u w v hstep _ ih =>
    intro hmem htop hrest hu
    obtain ⟨hw, hB⟩ := topWordR_step (hmem σ List.mem_cons_self) hstep hu
    have hr := ih (fun τ hτ => hmem τ (List.mem_cons_of_mem _ hτ)) (fun τ hτ => htop τ (List.mem_cons_of_mem _ hτ))
      (fun τ hτ => hrest τ (List.mem_cons_of_mem _ hτ)) hw
    by_cases hσ : σ = ρ0
    · subst hσ
      obtain ⟨q, rfl, rfl⟩ := hB hρ0
      have h1 := phiN_top_row0_lt hs q
      rw [List.count_cons_self]
      omega
    · rw [List.count_cons_of_ne hσ]
      by_cases hT : σ ∈ rulesSTrevTop
      · obtain ⟨q, rfl, rfl⟩ := hB hT
        have h1 := phiN_top_row0_le (htop σ List.mem_cons_self hT) q
        omega
      · obtain ⟨p, q, rfl, rfl⟩ := hstep
        have h1 := phiN_step_le (hrest σ List.mem_cons_self hT) p q
        omega

theorem usableRevT_free : ∀ ρ ∈ usableRevT, rgt ∉ ρ.lhs ∧ rgt ∉ ρ.rhs := by decide

/-- The mirrored canonical derivation `13 → 20 → 10 → 5` uses only the two top rules and the rules of `usableRevT`. -/
theorem canDerivRev_13_20_10 :
    (∀ σ ∈ canDerivRev 13 ++ canDerivRev 20 ++ canDerivRev 10, σ ∉ rulesSTrevTop → σ ∈ usableRevT) ∧
    T 13 = 20 ∧ T 20 = 10 ∧ T 10 = 5 ∧
    (∀ ρ0 ∈ rulesSTrevTop, 1 ≤ (canDerivRev 13).count ρ0 + (canDerivRev 20).count ρ0 + (canDerivRev 10).count ρ0) ∧
    (can 13).reverse = [rgt, t, f, t, lft] ∧ (can 5).reverse = [rgt, t, f, lft] := by
  decide +kernel

/-- **Reversed, only `t` dropped** (`[t]` is a constant): even though the usable rules shrink to the 6 rules of `1`, `2`, no dependency pair can be strictly oriented
in the first component (without the value-level core). -/
theorem dpRev_filt_t [NeZero d] (J : DLetter → NAff d) (ht : (J (plain t)).M = 0)
    (hU : ∀ ρ ∈ usableRevT, NWeakD J ρ.plain) (hP : ∀ π ∈ pairsPDrev, NWeakTopD J π) :
    ∀ π ∈ pairsPDrev, ¬ NStrictTopD J π := by
  intro π hπ hs
  rw [pairsPDrev_eq] at hπ
  obtain ⟨ρ0, hρ0, rfl⟩ := List.mem_map.1 hπ
  set I := ofDP rgt J with hIdef
  have hs' : Row0Strict I ρ0 := (nstrictTopD_dp_iff rgt J (rulesSTrevTop_head ρ0 hρ0)).1 hs
  have hQ : ∀ σ ∈ rulesSTrevTop, Row0Weak I σ := fun σ hσ =>
    (nweakTopD_dp_iff rgt J (rulesSTrevTop_head σ hσ)).1 (hP _ (pairsPDrev_eq ▸ List.mem_map_of_mem hσ))
  have hX : ∀ σ ∈ usableRevT, NWeak I σ := fun σ hσ =>
    (nweakD_plain_iff_ofDP rgt J (usableRevT_free σ hσ).1 (usableRevT_free σ hσ).2).1 (hU σ hσ)
  obtain ⟨hsub, hT13, hT20, hT10, hcnt, hc13, hc5⟩ := canDerivRev_13_20_10
  have step : ∀ n, n = 13 ∨ n = 20 ∨ n = 10 →
      PhiN I (can (T n)).reverse + (canDerivRev n).count ρ0 ≤ PhiN I (can n).reverse := by
    intro n hn
    have h2 : 2 ≤ n := by omega
    refine chain_count_row0 hρ0 hs' (canDerivRev_chain n h2) (canDerivRev_sub n)
      (fun σ _ hσ => hQ σ hσ) (fun σ hσ hσ' => hX σ (hsub σ ?_ hσ')) (topWordR_can n)
    rcases hn with rfl | rfl | rfl <;> simp [hσ]
  have e1 := step 13 (Or.inl rfl)
  have e2 := step 20 (Or.inr (Or.inl rfl))
  have e3 := step 10 (Or.inr (Or.inr rfl))
  rw [hT13] at e1
  rw [hT20] at e2
  rw [hT10] at e3
  have hItI : I t = J (plain t) := by simp [hIdef, ofDP]
  have hconst : ∀ w : Word, evN I (rgt :: t :: w) = (I rgt).comp ⟨0, (J (plain t)).v⟩ := by
    intro w
    show (I rgt).comp ((I t).comp (evN I w)) = _
    rw [hItI, comp_of_M_zero _ _ ht]
  have h135 : PhiN I (can 13).reverse = PhiN I (can 5).reverse := by
    rw [hc13, hc5, phiN_eq, phiN_eq, hconst, hconst]
  have := hcnt ρ0 hρ0
  omega

/-! ## §3 The forms with filters -/

end W5

open W5

/-- **The forward dependency pair form with filters** (the form of Thm 26 of GTSF06): for every argument filter `F` (the set of letters whose argument is dropped; their
`M` is 0), if the interpretation weakly orients the usable rules with the filter entrywise and `P_B` in the first component, then it strictly orients no pair of `P_B`
in the first component. -/
def NatBarrierDPFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) [NeZero d] (J : DLetter → NAff d), (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ usableFilt rulesST pairsPB F, NWeakD J ρ.plain) →
    (∀ π ∈ pairsPB, NWeakTopD J π) → ∀ π ∈ pairsPB, ¬ NStrictTopD J π

/-- **The reversed dependency pair form with filters**. -/
def NatBarrierDPrevFilt : Prop :=
  ∀ (F : List Letter) (d : ℕ) [NeZero d] (J : DLetter → NAff d), (∀ s ∈ F, (J (plain s)).M = 0) →
    (∀ ρ ∈ usableFilt rulesSTrev pairsPDrev F, NWeakD J ρ.plain) →
    (∀ π ∈ pairsPDrev, NWeakTopD J π) → ∀ π ∈ pairsPDrev, ¬ NStrictTopD J π

/-- Forward: the usable rules do not shrink under filters, so this follows from `NatBarrierDP`. -/
theorem natBarrierDPFilt_of_DP (hdp : NatBarrierDP) : NatBarrierDPFilt := by
  intro F d _ J _ hU hP
  rw [usableFilt_fwd] at hU
  exact hdp d J hU hP

/-- Reversed: when `f` or `t` is dropped, by §2 (without hypotheses); otherwise from `NatBarrierDPrev`. -/
theorem natBarrierDPrevFilt_of_DPrev (hdp : NatBarrierDPrev) : NatBarrierDPrevFilt := by
  intro F d _ J hF hU hP
  rw [usableFilt_rev] at hU
  by_cases hf : f ∈ F
  · exact dpRev_filt_f J (hF f hf) (hP _ (by decide))
  · by_cases ht : t ∈ F
    · exact dpRev_filt_t J (hF t ht) (by simpa [hf, ht] using hU) hP
    · exact hdp d J (by simpa [hf, ht] using hU) hP

/-- From the value-level core: the two forms with filters. -/
theorem natBarrierDPFilt_of_core' (hcore : NatValueCore') : NatBarrierDPFilt ∧ NatBarrierDPrevFilt :=
  ⟨natBarrierDPFilt_of_DP (natBarrierDP_of_core' hcore), natBarrierDPrevFilt_of_DPrev (natBarrierDPrev_of_core' hcore)⟩

end Collatz.Arctic.NatQ5
