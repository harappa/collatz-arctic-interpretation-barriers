/-
# Windows of the Terras part and runs of groups `RunMiss`; counting windows of the free bits (Lemma 12.25 of the paper)

Counting by group indices (Section 12.7 of the paper). A window of the Terras part without `u♯` covers entirely the cut words of the `K` consecutive groups
below the group in which it begins (the groups after `β₀` are `[b₀ + i g, b₀ + (i+1) g)`, `g = n₁ + a`, `a` being $n_2$ of the paper), so `RunMiss i K K` holds.
A window beginning in the incomplete top group (the remainder of `k` modulo `g`) is charged to the last complete group `G - 1`. Windows do not extend below group 0
(into `β₀`, the shared part): the windows lie inside the Terras part `TwOf`. The written proof is Lemma 12.25 (ii) of the paper.

* `runMiss_of_group`, `runMiss_of_partial`: if a window begins in the range of bits of group `i` (or in the incomplete top group), `RunMiss` holds.
* `card_run_le_runMiss`: the number of beginnings of windows of length `L ≥ 11g(K+2)` is at most `22 g #{i < G : RunMiss i K K}`.
* `card_free_le`, `sum_cntRun_free_le`: over the free bits `u < 2^F`, the sum of the numbers of windows of length `L` is at most
  `(F + 1) 2^F (1 - 2^{-|u♯|})^{⌊L/|u♯|⌋}`.
-/
import CollatzProof.Arctic.Nat.W3hTail

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

section Group

variable (us : List (Fin 2)) (β₀ β' : List Bool) (n₁ a : ℕ)

/-- The bit position of the beginning of group `j` (from the top of the Terras part): `A_j := m - L_{b₀ + j g}`. -/
def Apos (j : ℕ) : ℕ := (parityOf (β₀ ++ β')).length - blockEnd (β₀ ++ β') (β₀.length + j * (n₁ + a))

theorem blockEnd_add_le (j d : ℕ) :
    blockEnd (β₀ ++ β') (β₀.length + (j + d) * (n₁ + a)) ≤
      blockEnd (β₀ ++ β') (β₀.length + j * (n₁ + a)) + 11 * (d * (n₁ + a)) := by
  have h := blockEnd_sub_le (β₀ ++ β') (i₁ := β₀.length + j * (n₁ + a)) (i₂ := β₀.length + (j + d) * (n₁ + a))
    (by nlinarith)
  have e : β₀.length + (j + d) * (n₁ + a) - (β₀.length + j * (n₁ + a)) = d * (n₁ + a) := by
    rw [add_mul]; omega
  rw [e] at h; exact h

theorem Apos_anti {j j' : ℕ} (h : j ≤ j') : Apos β₀ β' n₁ a j' ≤ Apos β₀ β' n₁ a j := by
  unfold Apos
  have := blockEnd_mono (β₀ ++ β') (i₁ := β₀.length + j * (n₁ + a)) (i₂ := β₀.length + j' * (n₁ + a))
    (by nlinarith)
  omega

theorem Apos_zero : Apos β₀ β' n₁ a 0 = (TwOf β₀ β').length := by
  unfold Apos; rw [TwOf_length, zero_mul, add_zero, blockEnd_b0]

/-- **A window at the position of a group ⇒ `RunMiss`**. -/
theorem runMiss_of_group {y L K i : ℕ} (hg : 1 ≤ n₁ + a) (_hK : 1 ≤ K)
    (hL : 11 * (n₁ + a) * (K + 2) ≤ L) (hfree : FreeW us y L (TwOf β₀ β'))
    (hyL : y + L ≤ (TwOf β₀ β').length) (_hi : (i + 1) * (n₁ + a) ≤ β'.length)
    (hy1 : Apos β₀ β' n₁ a (i + 1) ≤ y) (hy2 : y < Apos β₀ β' n₁ a i) :
    W3b.RunMiss (PU us) β₀.length n₁ a i K K (β₀ ++ β') := by
  have hTw := TwOf_length β₀ β'
  have hb0 := blockEnd_b0 β₀ β'
  -- `K + 1 ≤ i`
  have hLi : L ≤ 11 * ((i + 1) * (n₁ + a)) := by
    have h1 := blockEnd_add_le β₀ β' n₁ a 0 (i + 1)
    simp only [zero_mul, add_zero, zero_add] at h1
    rw [hb0] at h1
    unfold Apos at hy1
    have := blockEnd_le_full (β₀ ++ β') (β₀.length + (i + 1) * (n₁ + a))
    omega
  have h3 : (n₁ + a) * (K + 2) ≤ (n₁ + a) * (i + 1) := by
    have e1 : 11 * ((n₁ + a) * (K + 2)) = 11 * (n₁ + a) * (K + 2) := by ring
    have e2 : 11 * ((i + 1) * (n₁ + a)) = 11 * ((n₁ + a) * (i + 1)) := by ring
    omega
  have hKi : K + 2 ≤ i + 1 := Nat.le_of_mul_le_mul_left h3 (by omega)
  refine ⟨i - K, by omega, by omega, fun i' hi'1 hi'2 => ?_⟩
  apply not_gHit_of_cover us β₀ β' n₁ a hfree
  · -- `y ≤ A_{i'+1}`
    have := Apos_anti β₀ β' n₁ a (j := i' + 1) (j' := i) (by omega)
    unfold Apos at this hy2
    omega
  · -- `A_{i'} ≤ y + L`
    have h1 := blockEnd_add_le β₀ β' n₁ a i' (i + 1 - i')
    rw [show i' + (i + 1 - i') = i + 1 by omega] at h1
    have h2 : (i + 1 - i') * (n₁ + a) ≤ (K + 1) * (n₁ + a) := Nat.mul_le_mul_right _ (by omega)
    have h4 : 11 * ((K + 1) * (n₁ + a)) ≤ 11 * (n₁ + a) * (K + 2) := by nlinarith
    unfold Apos at hy1
    have := blockEnd_le_full (β₀ ++ β') (β₀.length + (i + 1) * (n₁ + a))
    have := blockEnd_le_full (β₀ ++ β') (β₀.length + i' * (n₁ + a))
    omega

/-- The number of groups and the incomplete top group: `k < (G + 1) g`. -/
theorem lt_succ_div_mul (k g : ℕ) (hg : 1 ≤ g) : k < (k / g) * g + g := by
  have := Nat.lt_div_mul_add (a := k) (b := g) (by omega)
  exact this

/-- **A window at the position of the incomplete top group ⇒ `RunMiss` of the last complete group `G - 1`** (`G = k / g`). -/
theorem runMiss_of_partial {y L K : ℕ} (hg : 1 ≤ n₁ + a) (hK : 1 ≤ K)
    (hL : 11 * (n₁ + a) * (K + 2) ≤ L) (hfree : FreeW us y L (TwOf β₀ β'))
    (hyL : y + L ≤ (TwOf β₀ β').length)
    (hy : y < Apos β₀ β' n₁ a (β'.length / (n₁ + a))) :
    W3b.RunMiss (PU us) β₀.length n₁ a (β'.length / (n₁ + a) - 1) K K (β₀ ++ β') := by
  have hTw := TwOf_length β₀ β'
  have hb0 := blockEnd_b0 β₀ β'
  have hfull := blockEnd_full β₀ β'
  have hGk : β'.length / (n₁ + a) * (n₁ + a) ≤ β'.length := Nat.div_mul_le_self _ _
  have hkG := lt_succ_div_mul β'.length (n₁ + a) hg
  -- the total number of bits
  have hall : (parityOf (β₀ ++ β')).length ≤ (parityOf β₀).length + 11 * β'.length := by
    have h := blockEnd_sub_le (β₀ ++ β') (i₁ := β₀.length) (i₂ := β₀.length + β'.length) (by omega)
    rw [hb0, hfull, Nat.add_sub_cancel_left] at h; exact h
  -- `K + 1 ≤ G`
  have hKG : K + 1 ≤ β'.length / (n₁ + a) := by
    have h2 : L ≤ 11 * β'.length := by omega
    have h3 : (n₁ + a) * (K + 2) < (n₁ + a) * (β'.length / (n₁ + a) + 1) := by
      have e1 : 11 * ((n₁ + a) * (K + 2)) = 11 * (n₁ + a) * (K + 2) := by ring
      have e2 : (n₁ + a) * (β'.length / (n₁ + a) + 1) = β'.length / (n₁ + a) * (n₁ + a) + (n₁ + a) := by ring
      omega
    have := Nat.lt_of_mul_lt_mul_left h3
    omega
  refine ⟨β'.length / (n₁ + a) - K, by omega, by omega, fun i' hi'1 hi'2 => ?_⟩
  apply not_gHit_of_cover us β₀ β' n₁ a hfree
  · have := Apos_anti β₀ β' n₁ a (j := i' + 1) (j' := β'.length / (n₁ + a)) (by omega)
    unfold Apos at this hy
    omega
  · -- `A_{i'} = m - L_{b₀+i'g} ≤ 11(k - i'g) ≤ 11 g (K + 1)`
    have hi'g : i' * (n₁ + a) ≤ β'.length := by
      have : i' * (n₁ + a) ≤ β'.length / (n₁ + a) * (n₁ + a) := Nat.mul_le_mul_right _ (by omega)
      omega
    have h1 := blockEnd_sub_le (β₀ ++ β') (i₁ := β₀.length + i' * (n₁ + a)) (i₂ := β₀.length + β'.length)
      (by omega)
    rw [hfull] at h1
    have h2 : β'.length - i' * (n₁ + a) ≤ (K + 1) * (n₁ + a) := by
      have : (β'.length / (n₁ + a)) * (n₁ + a) ≤ (i' + K) * (n₁ + a) := Nat.mul_le_mul_right _ (by omega)
      have e : (i' + K) * (n₁ + a) + (n₁ + a) = i' * (n₁ + a) + (K + 1) * (n₁ + a) := by ring
      omega
    have h4 : 11 * ((K + 1) * (n₁ + a)) ≤ 11 * (n₁ + a) * (K + 2) := by nlinarith
    omega

open Classical in
/-- **Number of windows ⇒ number of groups with `RunMiss`**: the number of beginnings of windows of length `L ≥ 11g(K+2)` without `u♯` is at most
`22 g #{i < G : RunMiss i K K}` (`K ≥ 1`; Lemma 12.25 (ii) of the paper). -/
theorem card_run_le_runMiss {L K : ℕ} (hg : 1 ≤ n₁ + a) (hK : 1 ≤ K) (hL : 11 * (n₁ + a) * (K + 2) ≤ L) :
    ((Finset.range ((TwOf β₀ β').length + 1)).filter
      (fun y => y + L ≤ (TwOf β₀ β').length ∧ FreeW us y L (TwOf β₀ β'))).card ≤
    22 * (n₁ + a) * ((Finset.range (β'.length / (n₁ + a))).filter
      (fun i => W3b.RunMiss (PU us) β₀.length n₁ a i K K (β₀ ++ β'))).card := by
  set f : ℕ → Prop := fun y => y + L ≤ (TwOf β₀ β').length ∧ FreeW us y L (TwOf β₀ β')
  set Rm := (Finset.range (β'.length / (n₁ + a))).filter
    (fun i => W3b.RunMiss (PU us) β₀.length n₁ a i K K (β₀ ++ β'))
  have hA0 := Apos_zero β₀ β' n₁ a
  have hL1 : 1 ≤ L := by nlinarith
  -- the width of the range of a group is at most `11 g`
  have hwidth : ∀ j, Apos β₀ β' n₁ a j - Apos β₀ β' n₁ a (j + 1) ≤ 11 * (n₁ + a) := by
    intro j
    have h1 := blockEnd_add_le β₀ β' n₁ a j 1
    simp only [one_mul] at h1
    unfold Apos
    omega
  -- the beginnings of the windows lie in `[0, A_0)`
  have hsub : (Finset.range ((TwOf β₀ β').length + 1)).filter f ⊆
      (Finset.Ico 0 (Apos β₀ β' n₁ a 0)).filter f := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_Ico.mpr ⟨Nat.zero_le _, ?_⟩, hy.2⟩
    rw [hA0]; have := hy.2.1; omega
  -- split into the ranges of the groups
  have htel : ∀ G' ≤ β'.length / (n₁ + a), ((Finset.Ico (Apos β₀ β' n₁ a G') (Apos β₀ β' n₁ a 0)).filter f).card =
      ∑ j ∈ Finset.range G', ((Finset.Ico (Apos β₀ β' n₁ a (j + 1)) (Apos β₀ β' n₁ a j)).filter f).card := by
    intro G'
    induction G' with
    | zero => intro _; simp
    | succ G' ih =>
      intro hG'
      rw [Finset.sum_range_succ, ← ih (by omega)]
      have h1 : Apos β₀ β' n₁ a (G' + 1) ≤ Apos β₀ β' n₁ a G' := Apos_anti β₀ β' n₁ a (by omega)
      have h2 : Apos β₀ β' n₁ a G' ≤ Apos β₀ β' n₁ a 0 := Apos_anti β₀ β' n₁ a (by omega)
      rw [← Finset.Ico_union_Ico_eq_Ico h1 h2, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
        add_comm]
  have hblock : ∀ j ∈ Finset.range (β'.length / (n₁ + a)),
      ((Finset.Ico (Apos β₀ β' n₁ a (j + 1)) (Apos β₀ β' n₁ a j)).filter f).card ≤
      11 * (n₁ + a) * (if W3b.RunMiss (PU us) β₀.length n₁ a j K K (β₀ ++ β') then 1 else 0) := by
    intro j hj
    by_cases hex : ∃ y ∈ (Finset.Ico (Apos β₀ β' n₁ a (j + 1)) (Apos β₀ β' n₁ a j)).filter f, True
    · obtain ⟨y, hy, -⟩ := hex
      rw [Finset.mem_filter, Finset.mem_Ico] at hy
      have hjk : (j + 1) * (n₁ + a) ≤ β'.length := by
        have hj' := Finset.mem_range.mp hj
        have h1 : (j + 1) * (n₁ + a) ≤ β'.length / (n₁ + a) * (n₁ + a) :=
          Nat.mul_le_mul_right (n₁ + a) (show j + 1 ≤ β'.length / (n₁ + a) from hj')
        have h2 := Nat.div_mul_le_self β'.length (n₁ + a)
        omega
      have hrm := runMiss_of_group us β₀ β' n₁ a hg hK hL hy.2.2 hy.2.1 hjk hy.1.1 hy.1.2
      simp only [hrm, ↓reduceIte, mul_one]
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Ico]
      exact hwidth j
    · push Not at hex
      have : (Finset.Ico (Apos β₀ β' n₁ a (j + 1)) (Apos β₀ β' n₁ a j)).filter f = ∅ :=
        Finset.eq_empty_of_forall_notMem (fun y hy => hex y hy)
      rw [this]; simp
  -- the incomplete top group
  have htop : ((Finset.Ico 0 (Apos β₀ β' n₁ a (β'.length / (n₁ + a)))).filter f).card ≤ 11 * (n₁ + a) * Rm.card := by
    by_cases hex : ∃ y ∈ (Finset.Ico 0 (Apos β₀ β' n₁ a (β'.length / (n₁ + a)))).filter f, True
    · obtain ⟨y, hy, -⟩ := hex
      rw [Finset.mem_filter, Finset.mem_Ico] at hy
      have hrm := runMiss_of_partial us β₀ β' n₁ a hg hK hL hy.2.2 hy.2.1 hy.1.2
      have hKG : 1 ≤ β'.length / (n₁ + a) := by
        -- `G ≥ 1` from the length of the window
        by_contra h0; push Not at h0
        have hG0 : β'.length / (n₁ + a) = 0 := Nat.lt_one_iff.mp h0
        have hk := lt_succ_div_mul β'.length (n₁ + a) hg
        rw [hG0, zero_mul, zero_add] at hk
        have hlen : (TwOf β₀ β').length ≤ 11 * β'.length := by
          rw [TwOf_length]
          have h := blockEnd_sub_le (β₀ ++ β') (i₁ := β₀.length) (i₂ := β₀.length + β'.length) (by omega)
          rw [blockEnd_b0, blockEnd_full, Nat.add_sub_cancel_left] at h
          omega
        have : 11 * (n₁ + a) * (K + 2) ≤ 11 * β'.length := by have := hy.2.1; omega
        nlinarith
      have hmem : β'.length / (n₁ + a) - 1 ∈ Rm := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hrm⟩
      have hpos : 1 ≤ Rm.card := Finset.card_pos.mpr ⟨_, hmem⟩
      have hpart : Apos β₀ β' n₁ a (β'.length / (n₁ + a)) ≤ 11 * (n₁ + a) := by
        have hfull := blockEnd_full β₀ β'
        have hGk := Nat.div_mul_le_self β'.length (n₁ + a)
        have hk := lt_succ_div_mul β'.length (n₁ + a) hg
        have h1 := blockEnd_sub_le (β₀ ++ β') (i₁ := β₀.length + β'.length / (n₁ + a) * (n₁ + a))
          (i₂ := β₀.length + β'.length) (by omega)
        rw [hfull] at h1
        unfold Apos
        omega
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Ico]
      calc _ ≤ 11 * (n₁ + a) := by omega
        _ ≤ 11 * (n₁ + a) * Rm.card := Nat.le_mul_of_pos_right _ hpos
    · push Not at hex
      have : (Finset.Ico 0 (Apos β₀ β' n₁ a (β'.length / (n₁ + a)))).filter f = ∅ :=
        Finset.eq_empty_of_forall_notMem (fun y hy => hex y hy)
      rw [this]; simp
  -- summing up
  have hsplit : ((Finset.Ico 0 (Apos β₀ β' n₁ a 0)).filter f).card =
      ((Finset.Ico 0 (Apos β₀ β' n₁ a (β'.length / (n₁ + a)))).filter f).card +
        ((Finset.Ico (Apos β₀ β' n₁ a (β'.length / (n₁ + a))) (Apos β₀ β' n₁ a 0)).filter f).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (Apos_anti β₀ β' n₁ a (Nat.zero_le _))]
  have hsum : ∑ j ∈ Finset.range (β'.length / (n₁ + a)),
      ((Finset.Ico (Apos β₀ β' n₁ a (j + 1)) (Apos β₀ β' n₁ a j)).filter f).card ≤ 11 * (n₁ + a) * Rm.card := by
    refine le_trans (Finset.sum_le_sum hblock) ?_
    rw [← Finset.mul_sum, Finset.sum_boole, Nat.cast_id]
  calc _ ≤ ((Finset.Ico 0 (Apos β₀ β' n₁ a 0)).filter f).card := Finset.card_le_card hsub
    _ = _ := hsplit
    _ ≤ 11 * (n₁ + a) * Rm.card + 11 * (n₁ + a) * Rm.card := by
        have := htel (β'.length / (n₁ + a)) le_rfl
        linarith [htop, hsum]
    _ = 22 * (n₁ + a) * Rm.card := by ring

end Group

/-! ## The side of the free bits -/

open Classical in
/-- The number of free bits `u < 2^F` whose positions `[y, y + L)` (`y + L ≤ F`) do not contain `u♯` (Lemma 12.25 (iii) of the paper). -/
theorem card_free_le (us : List (Fin 2)) {F y L : ℕ} (h : y + L ≤ F) :
    (((Finset.range (2 ^ F)).filter (fun u => FreeW us y L ((bitsMSB F u).map W3a.l2f))).card : ℝ) ≤
      2 ^ F * (1 - 1 / 2 ^ us.length) ^ (L / us.length) := by
  have e : (Finset.range (2 ^ F)).filter (fun u => FreeW us y L ((bitsMSB F u).map W3a.l2f)) =
      (Finset.range (2 ^ F)).filter (fun u => (fun l : List Bool => FreeW us y L (l.map W3d.b2f))
        ((bitsMSB F u).map W3d.toB)) := by
    apply Finset.filter_congr
    intro u _
    simp only
    rw [map_toB_map_b2f]
  rw [e, card_range_bits F (fun l : List Bool => FreeW us y L (l.map W3d.b2f))]
  exact card_noOcc_fin us h

end Collatz.Arctic.NatQ5.W3h
