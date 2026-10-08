/-
# Natural-number interpretations of 𝒯 (proof of Proposition 12.11, part 6): properties of the detour weight `gfun`

The contents of the fields `g_len`, `g_poly`, `g_free` of `DecompData`.

* `Pre_free`: if an entry of the prefix kernel is positive, the word consists of parts without `u♯` (short sojourns) and of as many crossing steps as the difference of `reachCnt`, so
  there is a window of length `ℓ` without `u♯` with `|w| ≤ (reachCnt k − reachCnt i')(ℓ + 1)`.
* `gfun_len`, `gfun_poly` (`c_P = (|Q|^2 W + 1)^{|Q|}` with `W = Wmax`, the sum of the entries, `M_Σ` in the paper; `d_P = |Q| + 1`), `gfun_free` (`c_W = |Q| + 2`).
-/
import CollatzProof.Arctic.Nat.W3DecompProof5

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

section Free

variable {Q : Type} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} {u : List (Fin 2)} {K : Set (BRel (ZIdx A))}
  {e : BRel (ZIdx A)} (h01 : ∀ C, IsComp A C → ZeroOne A C) (hS : Sharp A K u e)
include h01 hS

/-- If an entry of the prefix kernel is positive, there is a long window without `u♯`. -/
theorem Pre_free : ∀ (w : List (Fin 2)) (k i' : Q), Rel A k → Rel A i' → 1 ≤ Pre A u w k i' →
    ∃ b ℓ, b + ℓ ≤ w.length ∧ w.length ≤ (reachCnt A k - reachCnt A i') * (ℓ + 1) ∧
      ¬ u <:+: (w.drop b).take ℓ := by
  have hunil : ¬ u <:+: ([] : List (Fin 2)) := fun h => by
    have h1 := h.length_le
    have h2 := List.length_pos_iff.2 hS.ne_nil
    rw [List.length_nil] at h1
    omega
  intro w
  induction' hn : w.length using Nat.strong_induction_on with n ih generalizing w
  intro k i' hk hi' hpos
  rcases w with _ | ⟨b0, w0⟩
  · exact ⟨0, 0, by simp, by simp at hn; simp [← hn], by simpa using hunil⟩
  set w := b0 :: w0 with hw
  rw [Pre_eq, Matrix.add_apply, Matrix.sum_apply] at hpos
  simp only [show w ≠ [] from List.cons_ne_nil b0 w0, ↓reduceIte, Matrix.zero_apply, zero_add] at hpos
  obtain ⟨q, hq, hqpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.one_le_iff_ne_zero.1 hpos)
  have hq' := Finset.mem_range.1 hq
  obtain ⟨m', hm'1, hm'2⟩ := exists_mid_mul (Nat.one_le_iff_ne_zero.2 hqpos)
  obtain ⟨m, hm1, hm2⟩ := exists_mid_mul hm'1
  -- a short sojourn
  have hshort : ¬ (InZ A k ∧ u <:+: w.take q) := by
    intro h; unfold SSt at hm1; simp only [h, and_self, ↓reduceIte] at hm1; omega
  have hD : 1 ≤ Rigid.DxN (Dp A) (w.take q) k m := le_trans hm1 (SSt_le A u _ k m)
  obtain ⟨hmk, hB⟩ := DxN_Dp_pos A hD
  have hfree1 : ¬ u <:+: w.take q := fun h => hshort ⟨inZ_of_stay A h01 hS hk hmk hB h, h⟩
  have hrm := reachCnt_eq_of_mem A hmk
  have hrm' := reachCnt_lt_of_Ep A hm2
  have hcm' : Conn A m' i' := conn_of_DxN A (le_trans hm'2 (Pre_le A u _ m' i'))
  have hcmm' : Conn A k m' := conn_trans A (conn_of_DxN A hB) (conn_of_edge A (le_trans hm2 (Ep_le A _ m m')))
  have hrel : Rel A m' := rel_of_between A hk hi' hcmm' hcm'
  have hri := reachCnt_le_of_conn A hcm'
  obtain ⟨b', ℓ', hb', hlen', hfree'⟩ := ih (w.drop (q + 1)).length (by rw [← hn, List.length_drop]; omega)
    (w.drop (q + 1)) rfl m' i' hrel hi' hm'2
  rw [List.length_drop] at hb' hlen'
  set n' := reachCnt A m' - reachCnt A i'
  have hnn : n' + 1 ≤ reachCnt A k - reachCnt A i' := by omega
  rw [← hn]
  by_cases hql : ℓ' ≤ q
  · refine ⟨0, q, by omega, ?_, by simpa using hfree1⟩
    calc w.length = (q + 1) + (w.length - (q + 1)) := by omega
      _ ≤ (q + 1) + n' * (ℓ' + 1) := by omega
      _ ≤ (q + 1) + n' * (q + 1) := Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
      _ = (n' + 1) * (q + 1) := by ring
      _ ≤ (reachCnt A k - reachCnt A i') * (q + 1) := Nat.mul_le_mul_right _ hnn
  · refine ⟨q + 1 + b', ℓ', by omega, ?_, ?_⟩
    · calc w.length = (q + 1) + (w.length - (q + 1)) := by omega
        _ ≤ (ℓ' + 1) + n' * (ℓ' + 1) := by omega
        _ = (n' + 1) * (ℓ' + 1) := by ring
        _ ≤ (reachCnt A k - reachCnt A i') * (ℓ' + 1) := Nat.mul_le_mul_right _ hnn
    · rw [← List.drop_drop]; exact hfree'

end Free

section G

variable {Q : Type} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) (u : List (Fin 2))

theorem gfun_len (l : LabT A) (r : ℕ) (v : List (Fin 2)) (h : gfun A u l r v ≠ 0) : v.length = r := by
  unfold gfun at h
  by_contra hne
  rw [ind_neg (fun hc => hne hc.1), zero_mul] at h
  exact h rfl

/-- An upper bound for the entries of the digit matrices. -/
def Wmax : ℕ := ∑ b, ∑ i, ∑ j, A.B b i j

theorem le_Wmax (b : Fin 2) (i j : Q) : A.B b i j ≤ Wmax A := by
  unfold Wmax
  calc A.B b i j ≤ ∑ j', A.B b i j' := Finset.single_le_sum (f := fun j' => A.B b i j') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A.B b i' j' := Finset.single_le_sum (f := fun i' => ∑ j', A.B b i' j')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ ∑ b', ∑ i', ∑ j', A.B b' i' j' := Finset.single_le_sum (f := fun b' => ∑ i', ∑ j', A.B b' i' j')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

variable {A u}

/-- **Polynomial bound**. -/
theorem gfun_poly (h01 : ∀ C, IsComp A C → ZeroOne A C) (l : LabT A) (r : ℕ) (v : List (Fin 2)) :
    gfun A u l r v ≤ (Fintype.card Q ^ 2 * Wmax A + 1) ^ Fintype.card Q * (r + 1) ^ (Fintype.card Q + 1) := by
  set C := (Fintype.card Q ^ 2 * Wmax A + 1) ^ Fintype.card Q
  unfold gfun
  by_cases hc : v.length = r ∧ Rel A l.2.2.2.1 ∧ Rel A l.2.2.2.2
  · rw [ind_pos hc, one_mul]
    calc ∑ a ∈ Finset.range r, ind (1 ≤ a ∧ l.2.1 = muZ A (v.take a) ∧ l.2.2.1 = muZ A (v.drop a) ∧
          firstEnd u v a) * detW A u (v.take a) l.2.2.2.1 l.2.2.2.2
        ≤ ∑ _a ∈ Finset.range r, C * (r + 1) ^ Fintype.card Q := by
          refine Finset.sum_le_sum fun a ha => ?_
          have ha' := Finset.mem_range.1 ha
          calc ind (1 ≤ a ∧ l.2.1 = muZ A (v.take a) ∧ l.2.2.1 = muZ A (v.drop a) ∧ firstEnd u v a) *
                detW A u (v.take a) l.2.2.2.1 l.2.2.2.2
              ≤ 1 * Rigid.DxN A.B (v.take a) l.2.2.2.1 l.2.2.2.2 :=
                Nat.mul_le_mul (ind_le_one _) (detW_le A u _ _ _)
            _ ≤ C * ((v.take a).length + 1) ^ Fintype.card Q := by
                rw [one_mul]; exact entry_poly A h01 (le_Wmax A) hc.2.1 hc.2.2 _
            _ ≤ C * (r + 1) ^ Fintype.card Q := by
                refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
                simp; omega
      _ = r * (C * (r + 1) ^ Fintype.card Q) := by simp
      _ ≤ (r + 1) * (C * (r + 1) ^ Fintype.card Q) := Nat.mul_le_mul_right _ (by omega)
      _ = C * (r + 1) ^ (Fintype.card Q + 1) := by ring
  · rw [ind_neg hc, zero_mul]; exact Nat.zero_le _

/-- **A long window without `u♯`** (`c_W = |Q| + 2`). -/
theorem gfun_free (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (BRel (ZIdx A))} {e : BRel (ZIdx A)}
    (hS : Sharp A K u e) (l : LabT A) (r : ℕ) (v : List (Fin 2)) (h : gfun A u l r v ≠ 0) :
    ∃ a ℓ, a + ℓ ≤ r ∧ r ≤ (Fintype.card Q + 2) * (ℓ + 1) ∧ ¬ u <:+: (v.drop a).take ℓ := by
  unfold gfun at h
  have hc : v.length = r ∧ Rel A l.2.2.2.1 ∧ Rel A l.2.2.2.2 := by
    by_contra hc; rw [ind_neg hc, zero_mul] at h; exact h rfl
  rw [ind_pos hc, one_mul] at h
  obtain ⟨a, ha, hapos⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have ha' := Finset.mem_range.1 ha
  have hind : 1 ≤ a ∧ l.2.1 = muZ A (v.take a) ∧ l.2.2.1 = muZ A (v.drop a) ∧ firstEnd u v a := by
    by_contra hn; rw [ind_neg hn, zero_mul] at hapos; exact hapos rfl
  have hdet : 1 ≤ detW A u (v.take a) l.2.2.2.1 l.2.2.2.2 :=
    Nat.one_le_iff_ne_zero.2 fun h0 => hapos (by rw [h0, mul_zero])
  obtain ⟨ha1, -, -, hfe⟩ := hind
  -- the detour word `v_{<a} = b₀ :: w'`
  have hvl := hc.1
  obtain ⟨b0, w', hw⟩ : ∃ b0 w', v.take a = b0 :: w' := List.exists_cons_of_ne_nil (by
    intro h0; have := congrArg List.length h0; rw [List.length_take, List.length_nil] at this; omega)
  have hw'len : w'.length = a - 1 := by
    have := congrArg List.length hw; rw [List.length_take, List.length_cons] at this; omega
  rw [hw, detW] at hdet
  obtain ⟨m, hm1, hm2⟩ := exists_mid_mul hdet
  have hcm : Conn A m l.2.2.2.2 := conn_of_DxN A (le_trans hm2 (Pre_le A u _ _ _))
  have hrel : Rel A m := rel_of_between A hc.2.1 hc.2.2 (conn_of_edge A (le_trans hm1 (Ep_le A _ _ _))) hcm
  obtain ⟨b, ℓ, hbℓ, hlen, hfree⟩ := Pre_free h01 hS w' m l.2.2.2.2 hrel hc.2.2 hm2
  have hn : reachCnt A m - reachCnt A l.2.2.2.2 ≤ Fintype.card Q := by
    have := reachCnt_le_card A m; omega
  have hlen' : a - 1 ≤ Fintype.card Q * (ℓ + 1) :=
    le_trans (by rw [← hw'len]; exact hlen) (Nat.mul_le_mul_right _ hn)
  by_cases hℓ : r - a - 1 ≤ ℓ
  · refine ⟨1 + b, ℓ, by omega, ?_, ?_⟩
    · calc r ≤ 2 + Fintype.card Q * (ℓ + 1) + ℓ := by omega
        _ ≤ (Fintype.card Q + 2) * (ℓ + 1) := by nlinarith
    · have heq : (w'.drop b).take ℓ = (v.drop (1 + b)).take ℓ := by
        have hw' : w' = (v.take a).drop 1 := by rw [hw]; rfl
        rw [hw', List.drop_drop, List.drop_take, List.take_take]
        congr 1; omega
      rw [← heq]; exact hfree
  · refine ⟨a, r - a - 1, by omega, ?_, ?_⟩
    · calc r ≤ 2 + Fintype.card Q * (ℓ + 1) + (r - a - 1) := by omega
        _ ≤ 2 + Fintype.card Q * (r - a - 1 + 1) + (r - a - 1) :=
            Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) _
        _ ≤ (Fintype.card Q + 2) * (r - a - 1 + 1) := by nlinarith
    · have := hfe.2; rw [hc.1] at this; exact this

end G

end Collatz.Arctic.NatQ5.W3c
