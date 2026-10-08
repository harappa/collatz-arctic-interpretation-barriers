/-
# 𝒯: the bridge for the left-end rules `B` (without monotonicity) and the value-level core without monotonicity

From `NatValueCore'` of §4 of `Statement.lean` (`NatValueCore` without the premise `NMono`) we derive
(i) `NatBarrierST` (for monotone interpretations, `natBarrierST_of_core'`) and (ii) `NatBarrierSTB` (the left-end rules `B` cannot be strictly
oriented, without monotonicity, `natBarrierSTB_of_core'`).

* The reason for (ii): every string of the canonical derivations has the form "`/` (`lft`) first, and no other `/`" (`TopWord`), and the rules of 𝒯
  preserve this form (`topWord_step`). The left-hand sides of the rules of `B` begin with `/`, so in strings of this form they apply only at positions with empty left context `p`
  (the top). In the case `p = []` of Lemma 10.2 (ii) (`stepTerm_ge` does not use monotonicity) the decrease is at least
  `(M_[])₀₀ = (identity matrix)₀₀ = 1` (`phiN_step_strict_top`). So `Φ` decreases by at least 1 at each use.
* Where monotonicity is used (a remark of the internal review): in `Bridge.lean` the premise `NMono` is taken only by `evN_M00_pos`,
  `stepTerm_ge_one`, `phiN_step_strict`, `phiN_chain_count`, `orbit_bound_nat` and `natBarrierST_of_core`, all of which are
  the step "one use of a strictly oriented rule decreases `Φ` by at least 1" (the last part of Lemma 10.2 (ii)) and its accumulation. The identities
  `lemma_66_1_1`, `lemma_66_1_1_chain`, the bounds `stepTerm_nonneg`, `stepTerm_ge`, `phiN_step_le`, `phiN_chain_le`, and
  the natural-number version `phiN_can_T_le`, `phiN_can_iterate_le` of the bridge for canonical strings (Lemma 10.2 (iii)) do not use monotonicity.
-/
import CollatzProof.Arctic.Nat.Bridge

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter

variable {d : ℕ}

/-! ## §1 Left-end rules and strings in top form -/

theorem rulesSTB_sub : ∀ ρ ∈ rulesSTB, ρ ∈ rulesST := by decide

/-- The form of the rules of `B`: both sides begin with `/` and contain no other `/`. -/
theorem rulesSTB_form : ∀ ρ ∈ rulesSTB,
    ∃ l r : Word, ρ.lhs = lft :: l ∧ ρ.rhs = lft :: r ∧ lft ∉ l ∧ lft ∉ r := by
  intro ρ hρ
  simp only [rulesSTB, List.mem_cons, List.mem_nil_iff, or_false] at hρ
  rcases hρ with rfl | rfl | rfl <;> exact ⟨_, _, rfl, rfl, by decide, by decide⟩

/-- The rules other than `B` contain no `/`, and their left-hand sides are non-empty. -/
theorem rulesST_nonB : ∀ ρ ∈ rulesST, ρ ∉ rulesSTB → ρ.lhs ≠ [] ∧ lft ∉ ρ.lhs ∧ lft ∉ ρ.rhs := by
  decide

/-- Strings in top form: `/` first, and no other `/`. -/
def TopWord (u : Word) : Prop := ∃ w, u = lft :: w ∧ lft ∉ w

theorem lft_not_mem_binTail (n : ℕ) : lft ∉ binTail n := by
  simp only [binTail, List.mem_map, not_exists, not_and]
  intro b _ h
  split_ifs at h

theorem topWord_can (n : ℕ) : TopWord (can n) :=
  ⟨binTail n ++ [rgt], rfl, by simp [lft_not_mem_binTail]⟩

/-- One step by a rule of 𝒯 preserves the top form, and the rules of `B` apply only at positions with empty left context (the top). -/
theorem topWord_step {σ : Rule} (hσ : σ ∈ rulesST) {u v : Word} (hst : Step σ u v) (hu : TopWord u) :
    TopWord v ∧ (σ ∈ rulesSTB → ∃ q, u = σ.lhs ++ q ∧ v = σ.rhs ++ q) := by
  obtain ⟨p, q, rfl, rfl⟩ := hst
  obtain ⟨w, hw, hlw⟩ := hu
  by_cases hB : σ ∈ rulesSTB
  · obtain ⟨l, r, hl, hr, hl', hr'⟩ := rulesSTB_form σ hB
    cases p with
    | nil =>
      rw [List.nil_append, hl, List.cons_append, List.cons.injEq] at hw
      obtain ⟨-, rfl⟩ := hw
      refine ⟨⟨r ++ q, by rw [List.nil_append, hr, List.cons_append], ?_⟩, fun _ => ⟨q, by simp, by simp⟩⟩
      simp only [List.mem_append, not_or] at hlw ⊢
      exact ⟨hr', hlw.2⟩
    | cons a p' =>
      exfalso
      rw [hl, List.cons_append, List.cons_append, List.cons.injEq] at hw
      obtain ⟨-, rfl⟩ := hw
      exact hlw (by simp)
  · obtain ⟨hne, hl, hr⟩ := rulesST_nonB σ hσ hB
    refine ⟨?_, fun h => absurd h hB⟩
    cases p with
    | nil =>
      exfalso
      rw [List.nil_append] at hw
      obtain ⟨a, l', hal⟩ := List.exists_cons_of_ne_nil hne
      rw [hal, List.cons_append, List.cons.injEq] at hw
      exact hl (by rw [hal, hw.1]; exact List.mem_cons_self)
    | cons a p' =>
      rw [List.cons_append, List.cons_append, List.cons.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨p' ++ σ.rhs ++ q, by simp, ?_⟩
      simp only [List.mem_append, not_or] at hlw ⊢
      exact ⟨⟨hlw.1.1, hr⟩, hlw.2⟩

/-! ## §2 The decrease at one use at the top (without monotonicity) -/

/-- **The case `p = []` of Lemma 10.2 (ii)**: using a strictly oriented rule at the top decreases `Φ` by at least 1, without monotonicity
(the decrease is at least `(M_[])₀₀ = 1`). -/
theorem phiN_step_strict_top [NeZero d] {I : Letter → NAff d} {ρ : Rule} (hs : NStrict I ρ) (q : Word) :
    PhiN I (ρ.rhs ++ q) + 1 ≤ PhiN I (ρ.lhs ++ q) := by
  have h1 := lemma_66_1_1 I [] q ρ
  have h2 := stepTerm_ge hs [] q
  have h3 : ((evN I []).M 0 0 : ℤ) = 1 := by simp [evN, NAff.id]
  simp only [List.nil_append] at h1
  omega

/-- Along derivations of 𝒯 that start in top form, `Φ` decreases by at least the number of uses of the strictly oriented rule `ρ` of `B` (without monotonicity). -/
theorem phiN_chain_count_top [NeZero d] {I : Letter → NAff d} {ρ : Rule} (hρB : ρ ∈ rulesSTB)
    (hρ : NStrict I ρ) :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v → (∀ σ ∈ rs, σ ∈ rulesST) → (∀ σ ∈ rs, NWeak I σ) →
      TopWord u → PhiN I v + rs.count ρ ≤ PhiN I u := by
  intro rs u v hc
  induction hc with
  | nil u => intro _ _ _; simp
  | @cons σ rs u w v hstep _ ih =>
    intro hmem hw htop
    obtain ⟨htop', hB⟩ := topWord_step (hmem σ List.mem_cons_self) hstep htop
    have hrest := ih (fun τ hτ => hmem τ (List.mem_cons_of_mem _ hτ))
      (fun τ hτ => hw τ (List.mem_cons_of_mem _ hτ)) htop'
    by_cases hσ : σ = ρ
    · subst hσ
      obtain ⟨q, rfl, rfl⟩ := hB hρB
      have h1 := phiN_step_strict_top hρ q
      rw [List.count_cons_self]
      omega
    · obtain ⟨p, q, rfl, rfl⟩ := hstep
      have h1 := phiN_step_le (hw σ List.mem_cons_self) p q
      rw [List.count_cons_of_ne hσ]
      omega

/-- A bound along orbits (without monotonicity): if the interpretation weakly orients the 11 rules and strictly orients the rule `ρ` of `B`, then
`Φ(can (T^m n)) + (the number of uses of ρ) ≤ Φ(can n)`. -/
theorem orbit_bound_top [NeZero d] {I : Letter → NAff d} (hweak : ∀ ρ ∈ rulesST, NWeak I ρ) {ρ : Rule}
    (hρB : ρ ∈ rulesSTB) (hρ : NStrict I ρ) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) → PhiN I (can (T^[m] n)) + usesOrbit ρ n m ≤ PhiN I (can n) := by
  intro m
  induction m with
  | zero => intro n _; simp [usesOrbit_zero]
  | succ m ih =>
    intro n horb
    have hn : 2 ≤ n := by simpa using horb 0 (Nat.succ_pos m)
    have hstep := phiN_chain_count_top hρB hρ (canDeriv_chain n hn) (fun σ hσ => canDeriv_sub n σ hσ)
      (fun σ hσ => hweak σ (canDeriv_sub n σ hσ)) (topWord_can n)
    have horb' : ∀ i < m, 2 ≤ T^[i] (T n) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hrest := ih (T n) horb'
    rw [Function.iterate_succ_apply, usesOrbit_succ]
    unfold uses
    omega

/-! ## §3 From the value-level core without monotonicity -/

/-- The value-level core with the weakened premise implies the original value-level core. -/
theorem natValueCore_of_core' (hcore : NatValueCore') : NatValueCore := by
  intro d _ I _ hweak
  exact hcore d I hweak

/-- **(i)**: the statement `NatBarrierST` of the main theorem from the value-level core without monotonicity. -/
theorem natBarrierST_of_core' (hcore : NatValueCore') : NatBarrierST :=
  natBarrierST_of_core (natValueCore_of_core' hcore)

/-- **(ii)**: the statement `NatBarrierSTB` for the left-end rules (without monotonicity) from the value-level core without monotonicity. -/
theorem natBarrierSTB_of_core' (hcore : NatValueCore') : NatBarrierSTB := by
  intro d _ I hweak ρ hρB hρ
  obtain ⟨n, -, m, horb, hlt⟩ := hcore d I hweak ρ (rulesSTB_sub ρ hρB) 0
  have := orbit_bound_top hweak hρB hρ m n horb
  omega

end Collatz.Arctic.NatQ5
