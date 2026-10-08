/-
# Natural-number interpretations of 𝒯 (proof of Proposition 12.11, part 2): expansion into chains of long sojourns

The recursion of `LFp` (`LFp_rec`) of `W3DecompProof.lean` is unfolded into a sum over the number `s` of detours.

* **Chains** `LFs s x i` (recursion on `s`, without tuples of positions; the indices at both ends of a detour are summed over at each step):
  * `LFs 0 x i = [i ∈ Q_s] (D_{(x,t₁]})_{i j₁}` (the last long sojourn),
  * `LFs (s+1) x i = Σ_{q ∈ [x, t_m)} Σ_k Σ_{x' ∈ [q+1, t_m]} Σ_{i'} [i ∈ Q_s ∧ u♯ ⊑ ω_{(x,q]} ∧ k, i' relevant]`
    `(D_{(x,q]})_{i k} (detW_{(q,x']})_{k i'} LFs s x' i'`.
* **Expansion** `LFp_flat`: `LFp x i = Σ_{s < |Q|} LFs s x i` (for relevant `i`, `j₁`).
* **Bound on the degree** `LFs_reach`: if `LFs s x i ≠ 0`, then `s + 1 ≤ reachCnt i` (the long sojourns lie in different components). Hence chains with `s ≥ |Q|` vanish.
-/
import CollatzProof.Arctic.Nat.W3DecompProof

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

section SumTools

/-- Turn a sum with an indicator into a sum over a subset. -/
theorem sum_ind_eq {β : Type*} {s t : Finset β} {P : β → Prop} (f : β → ℕ) (hst : s ⊆ t)
    (hP : ∀ a ∈ t, P a ↔ a ∈ s) : ∑ a ∈ t, ind (P a) * f a = ∑ a ∈ s, f a := by
  rw [← Finset.sum_subset hst (f := fun a => ind (P a) * f a)]
  · exact Finset.sum_congr rfl fun a ha => by rw [ind_pos ((hP a (hst ha)).2 ha), one_mul]
  · intro a ha hna
    rw [ind_neg (fun h => hna ((hP a ha).1 h)), zero_mul]

/-- Move the innermost sum to the outside (fourfold sums). -/
theorem sum4_comm_out {α β γ δ ε M : Type*} [AddCommMonoid M] (S : Finset α) (T : Finset β) (U : α → Finset γ)
    (V : Finset δ) (W : Finset ε) (f : α → β → γ → δ → ε → M) :
    ∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U a, ∑ d ∈ V, ∑ e ∈ W, f a b c d e =
      ∑ e ∈ W, ∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U a, ∑ d ∈ V, f a b c d e := by
  calc ∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U a, ∑ d ∈ V, ∑ e ∈ W, f a b c d e
      = ∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U a, ∑ e ∈ W, ∑ d ∈ V, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_comm
    _ = ∑ a ∈ S, ∑ b ∈ T, ∑ e ∈ W, ∑ c ∈ U a, ∑ d ∈ V, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ e ∈ W, ∑ b ∈ T, ∑ c ∈ U a, ∑ d ∈ V, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ e ∈ W, ∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U a, ∑ d ∈ V, f a b c d e := Finset.sum_comm

end SumTools

section Chain

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) (u : List (Fin 2))
variable (ω : List (Fin 2)) (tm : ℕ) (j1 : Q)

/-- **Chains**: the weight of the chains of long sojourns with `s` detours. -/
noncomputable def LFs : ℕ → ℕ → Q → ℕ
  | 0, x, i => ind (InZ A i) * Rigid.DxN (Dp A) (seg ω x (tm + u.length)) i j1
  | s + 1, x, i => ∑ q ∈ Finset.Ico x tm, ∑ k, ∑ x' ∈ Finset.Icc (q + 1) tm, ∑ i',
      ind (InZ A i ∧ u <:+: seg ω x q ∧ Rel A k ∧ Rel A i') *
        (Rigid.DxN (Dp A) (seg ω x q) i k * detW A u (seg ω q x') k i' * LFs s x' i')

theorem LFs_zero (x : ℕ) (i : Q) :
    LFs A u ω tm j1 0 x i = ind (InZ A i) * Rigid.DxN (Dp A) (seg ω x (tm + u.length)) i j1 := rfl

theorem LFs_succ (s x : ℕ) (i : Q) :
    LFs A u ω tm j1 (s + 1) x i = ∑ q ∈ Finset.Ico x tm, ∑ k, ∑ x' ∈ Finset.Icc (q + 1) tm, ∑ i',
      ind (InZ A i ∧ u <:+: seg ω x q ∧ Rel A k ∧ Rel A i') *
        (Rigid.DxN (Dp A) (seg ω x q) i k * detW A u (seg ω q x') k i' * LFs A u ω tm j1 s x' i') := rfl

variable {A u ω tm j1}

/-- **Bound on the degree**: if a chain does not vanish, then `s + 1 ≤ reachCnt i` (each detour crosses to another component, and `reachCnt` decreases). -/
theorem LFs_reach : ∀ (s x : ℕ) (i : Q), LFs A u ω tm j1 s x i ≠ 0 → s + 1 ≤ reachCnt A i := by
  intro s
  induction s with
  | zero => intro _ i _; exact one_le_reachCnt A i
  | succ s ih =>
    intro x i h
    rw [LFs_succ] at h
    obtain ⟨q, _, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    obtain ⟨x', _, hx'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    obtain ⟨i', _, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
    have h1 : Rigid.DxN (Dp A) (seg ω x q) i k ≠ 0 := fun h0 => hi' (by simp [h0])
    have h2 : detW A u (seg ω q x') k i' ≠ 0 := fun h0 => hi' (by simp [h0])
    have h3 : LFs A u ω tm j1 s x' i' ≠ 0 := fun h0 => hi' (by simp [h0])
    have hk' := reachCnt_eq_of_mem A (DxN_Dp_pos A (Nat.one_le_iff_ne_zero.2 h1)).1
    have hd := detW_reach A u (Nat.one_le_iff_ne_zero.2 h2)
    have := ih _ _ h3
    omega

theorem LFs_eq_zero_of_card {s : ℕ} (hs : Fintype.card Q ≤ s) (x : ℕ) (i : Q) : LFs A u ω tm j1 s x i = 0 := by
  by_contra h
  have := LFs_reach s x i h
  have := reachCnt_le_card A i
  omega

section Flat

variable (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (BRel (ZIdx A))} {e : BRel (ZIdx A)}
  (hS : Sharp A K u e) (hcopy : seg ω tm (tm + u.length) = u) (hN : tm + u.length ≤ ω.length) (hj1 : Rel A j1)
include h01 hS hcopy hN hj1

/-- **Expansion**: `LFp x i = Σ_{s < |Q|} LFs s x i` (for relevant `i`). -/
theorem LFp_flat : ∀ x, x ≤ tm → ∀ i, Rel A i → LFp A u ω tm j1 x i =
    ∑ s ∈ Finset.range (Fintype.card Q), LFs A u ω tm j1 s x i := by
  intro x
  induction' hn : tm - x using Nat.strong_induction_on with n ih generalizing x
  intro hx i hi
  obtain ⟨c, hc⟩ : ∃ c, Fintype.card Q = c + 1 := ⟨Fintype.card Q - 1, by
    have := Fintype.card_pos_iff.2 ⟨i⟩; omega⟩
  -- right-hand side: split into `s = 0` and `s + 1`; the term with `s = |Q|` vanishes
  have hR : ∑ s ∈ Finset.range (Fintype.card Q), LFs A u ω tm j1 s x i =
      LFs A u ω tm j1 0 x i + ∑ s ∈ Finset.range (Fintype.card Q), LFs A u ω tm j1 (s + 1) x i := by
    rw [hc, Finset.sum_range_succ', Finset.sum_range_succ (fun s => LFs A u ω tm j1 (s + 1) x i) c,
      LFs_eq_zero_of_card (show Fintype.card Q ≤ c + 1 by omega) x i]
    ring
  rw [hR, LFp_rec h01 hS hcopy hN hj1 x i, LFs_zero, mul_add]
  congr 1
  -- each term: terms with indices that are not relevant vanish; for relevant indices use the induction hypothesis
  have hterm : ∀ q ∈ Finset.Ico x tm, ∀ k, ∀ x' ∈ Finset.Icc (q + 1) tm, ∀ i',
      ind (InZ A i) * (ind (u <:+: seg ω x q) * (Rigid.DxN (Dp A) (seg ω x q) i k *
        (detW A u (seg ω q x') k i' * LFp A u ω tm j1 x' i'))) =
      ∑ s ∈ Finset.range (Fintype.card Q), ind (InZ A i ∧ u <:+: seg ω x q ∧ Rel A k ∧ Rel A i') *
          (Rigid.DxN (Dp A) (seg ω x q) i k * detW A u (seg ω q x') k i' * LFs A u ω tm j1 s x' i') := by
    intro q hq k x' hx' i'
    have hq' := Finset.mem_Ico.1 hq
    have hx'' := Finset.mem_Icc.1 hx'
    by_cases hz : Rigid.DxN (Dp A) (seg ω x q) i k * detW A u (seg ω q x') k i' * LFp A u ω tm j1 x' i' = 0
    · have hL : ind (InZ A i) * (ind (u <:+: seg ω x q) * (Rigid.DxN (Dp A) (seg ω x q) i k *
          (detW A u (seg ω q x') k i' * LFp A u ω tm j1 x' i'))) = 0 := by
        rw [← mul_assoc (Rigid.DxN (Dp A) (seg ω x q) i k), hz]; simp
      rw [hL]
      symm
      refine Finset.sum_eq_zero fun s hs => ?_
      rcases Nat.eq_zero_or_pos (Rigid.DxN (Dp A) (seg ω x q) i k * detW A u (seg ω q x') k i') with h0 | hpos
      · rw [h0]; simp
      · have hLF : LFp A u ω tm j1 x' i' = 0 := (Nat.mul_eq_zero.1 hz).resolve_left (by omega)
        by_cases hr : Rel A i'
        · have := ih (tm - x') (by omega) x' rfl hx''.2 i' hr
          rw [hLF] at this
          rw [(Finset.sum_eq_zero_iff.1 this.symm) s hs]; simp
        · rw [ind_neg (fun h => hr h.2.2.2), zero_mul]
    · have h1 : 1 ≤ Rigid.DxN (Dp A) (seg ω x q) i k := Nat.one_le_iff_ne_zero.2 fun h => hz (by simp [h])
      have h2 : 1 ≤ detW A u (seg ω q x') k i' := Nat.one_le_iff_ne_zero.2 fun h => hz (by simp [h])
      have h3 : 1 ≤ LFp A u ω tm j1 x' i' := Nat.one_le_iff_ne_zero.2 fun h => hz (by simp [h])
      have hcik : Conn A i k := conn_of_DxN A (le_trans h1 (DxN_Dp_le A _ i k))
      have hcki : Conn A k i' := conn_of_detW A u h2
      have hcij : Conn A i' j1 :=
        conn_of_Fp h01 hS hcopy hN (le_trans h3 (LFp_le h01 hS hcopy hN hx''.2 i'))
      have hrk : Rel A k := rel_of_between A hi hj1 hcik (conn_trans A hcki hcij)
      have hri : Rel A i' := rel_of_between A hi hj1 (conn_trans A hcik hcki) hcij
      rw [ih (tm - x') (by omega) x' rfl hx''.2 i' hri]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ind_and, ind_and, ind_and, ind_pos hrk, ind_pos hri]
      ring
  have hLHS : ind (InZ A i) * ∑ q ∈ Finset.Ico x tm, ind (u <:+: seg ω x q) * ∑ k, Rigid.DxN (Dp A) (seg ω x q) i k *
        ∑ x' ∈ Finset.Icc (q + 1) tm, ∑ i', detW A u (seg ω q x') k i' * LFp A u ω tm j1 x' i' =
      ∑ q ∈ Finset.Ico x tm, ∑ k, ∑ x' ∈ Finset.Icc (q + 1) tm, ∑ i',
        ind (InZ A i) * (ind (u <:+: seg ω x q) * (Rigid.DxN (Dp A) (seg ω x q) i k *
          (detW A u (seg ω q x') k i' * LFp A u ω tm j1 x' i'))) := by
    simp only [Finset.mul_sum]
  rw [hLHS, Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x' hx' =>
    Finset.sum_congr rfl fun i' _ => hterm q hq k x' hx' i']
  rw [sum4_comm_out]
  rfl

end Flat

end Chain

end Collatz.Arctic.NatQ5.W3c
