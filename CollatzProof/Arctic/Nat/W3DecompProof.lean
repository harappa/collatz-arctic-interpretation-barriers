/-
# Natural-number interpretations of 𝒯 (proof of Proposition 12.11, part 1): splitting on the side of paths

The first part of the proof of `DecompStmt` (`W3Decomp.lean`). The splitting of the main identity of Definition 12.9 is written, without handling
paths one by one, as identities of products of digit matrices (all components 0/1, `Sharp`). `D_w`, `E_b`, `B_w` are `Dp`, `Ep`, `A.B` (`N^in`, `N^out`, `N` in the paper).

* **§1 Interval words** `seg ω a b := ω_{(a,b]}`, with lemmas on their splitting, their length and their first letter.
* **§2 Short sojourns and the kernels**: short sojourns `SSt w` (`D_w` with the rows of the indices in `Q_s` replaced by 0 if `w` contains `u♯`),
  the prefix kernel `Pre w` (the sum over the paths all of whose sojourns are short; the last step is a crossing step; well-founded recursion on `|w|`),
  the detour kernel `detW (b :: w) := E_b · Pre w` (the sum over the paths that start with a crossing step, pass through short sojourns and enter the next long sojourn by a crossing step).
  `Pre ≤ B`, `detW ≤ B`, and an edge of `detW` strictly decreases `reachCnt` (`rc` in the paper).
* **§3 Splitting on the side of paths** (with the word `ω`, the last copy `ω_{(t_m, t_m+|u♯|]} = u♯` and the final index `j₁` fixed):
  * `Fp x := B_{ω_{(x,t_m]}} · D_{u♯}` (paths that do not cross within the last copy), `LFp x i` (those among them whose first sojourn is long).
  * **The first splitting** `Fp_decomp`: `(Fp x)_{i j₁} = Σ_{x' ∈ [x, t_m]} Σ_{i'} Pre(ω_{(x,x']})_{i i'} · LFp x' i'` (cut at the first long sojourn).
  * **The recursion over long sojourns** `LFp_rec`: `LFp x i = [i ∈ Q_s](D_{(x,t₁]} + Σ_{q} [u♯ ⊑ ω_{(x,q]}] Σ_k D_{(x,q]} detW_{(q,x']} LFp x')`.
  * **The middle factor** `mid_eq_LFp`: `(D_{u♯} B_{(t₀,t_m]} D_{u♯})_{j₀ j₁} = LFp a₀ j₀` (`ω_{(a₀,t₀]} = u♯`).
-/
import CollatzProof.Arctic.Nat.W3Decomp

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

/-! ## §1 Interval words -/

section Seg

/-- The word `ω_{(a,b]}` of the interval `(a, b]` (the letters `a, …, b − 1`). -/
def seg (ω : List (Fin 2)) (a b : ℕ) : List (Fin 2) := (ω.drop a).take (b - a)

variable (ω : List (Fin 2))

theorem seg_append {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) : seg ω a c = seg ω a b ++ seg ω b c :=
  seg_split ω hab hbc

theorem length_seg {a b : ℕ} (hb : b ≤ ω.length) : (seg ω a b).length = b - a := by
  simp only [seg, List.length_take, List.length_drop]; omega

theorem seg_self (a : ℕ) : seg ω a a = [] := by simp [seg]

theorem seg_take (a b n : ℕ) (h : n ≤ b - a) : (seg ω a b).take n = seg ω a (a + n) := by
  simp only [seg, List.take_take]
  congr 1; omega

theorem seg_drop (a b n : ℕ) : (seg ω a b).drop n = seg ω (a + n) b := by
  simp only [seg, List.drop_take, List.drop_drop]
  congr 1; omega

theorem seg_getD (a b n : ℕ) (h : n < b - a) : (seg ω a b).getD n 0 = ω.getD (a + n) 0 := by
  simp only [seg, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, h, ↓reduceIte]

theorem seg_single {a : ℕ} (ha : a < ω.length) : seg ω a (a + 1) = [ω.getD a 0] := by
  simp only [seg, Nat.add_sub_cancel_left, List.drop_eq_getElem_cons ha, List.take_one, List.head?_cons,
    Option.toList_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]

theorem seg_cons {a b : ℕ} (hab : a < b) (hb : b ≤ ω.length) : seg ω a b = ω.getD a 0 :: seg ω (a + 1) b := by
  rw [seg_append ω (show a ≤ a + 1 by omega) hab, seg_single ω (by omega)]; rfl

theorem seg_eq_nil_iff {a b : ℕ} (hb : b ≤ ω.length) : seg ω a b = [] ↔ b ≤ a := by
  rw [← List.length_eq_zero_iff, length_seg ω hb]; omega

/-- A prefix is `take`. -/
theorem take_eq_seg (p : ℕ) : ω.take p = seg ω 0 p := by simp [seg]

end Seg

/-! ## §2 Short sojourns and the kernels -/

section Kernel

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) (u : List (Fin 2))

open Classical in
/-- The weight of **short sojourns**: `(D_w)_{ij}`, except that it is 0 if `i ∈ Q_s` and `w` contains `u♯` (a long sojourn). -/
noncomputable def SSt (w : List (Fin 2)) : Matrix Q Q ℕ := fun i j =>
  if InZ A i ∧ u <:+: w then 0 else Rigid.DxN (Dp A) w i j

/-- **The prefix kernel**: the sum over the paths all of whose sojourns are short (the identity matrix for the empty word; otherwise the last step is a crossing step). -/
noncomputable def Pre (w : List (Fin 2)) : Matrix Q Q ℕ :=
  (if w = [] then 1 else 0) +
    ∑ q : Fin w.length, SSt A u (w.take q) * Ep A (w.getD q 0) * Pre (w.drop (q + 1))
termination_by w.length
decreasing_by
  simp only [List.length_drop]
  have := q.isLt
  omega

theorem Pre_eq (w : List (Fin 2)) :
    Pre A u w = (if w = [] then 1 else 0) +
      ∑ q ∈ Finset.range w.length, SSt A u (w.take q) * Ep A (w.getD q 0) * Pre A u (w.drop (q + 1)) := by
  rw [Pre, Fin.sum_univ_eq_sum_range
    (fun q => SSt A u (w.take q) * Ep A (w.getD q 0) * Pre A u (w.drop (q + 1))) w.length]

/-- **The detour kernel**: the sum over the paths that start with a crossing step `E_b` and enter the next long sojourn through the prefix kernel. -/
noncomputable def detW : List (Fin 2) → Matrix Q Q ℕ
  | [] => 0
  | b :: w => Ep A b * Pre A u w

theorem SSt_le (w : List (Fin 2)) (i j : Q) : SSt A u w i j ≤ Rigid.DxN (Dp A) w i j := by
  unfold SSt; split_ifs <;> simp

theorem DxN_Dp_le (w : List (Fin 2)) (i j : Q) : Rigid.DxN (Dp A) w i j ≤ Rigid.DxN A.B w i j := by
  rw [DxN_Dp]; split_ifs <;> simp

/-- Entrywise monotonicity of products (three factors). -/
theorem mul3_le {X X' Y Y' Z Z' : Matrix Q Q ℕ} (hX : ∀ i j, X i j ≤ X' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (i j : Q) : (X * Y * Z) i j ≤ (X' * Y' * Z') i j := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_le_sum fun l _ => Nat.mul_le_mul (Finset.sum_le_sum fun k _ => Nat.mul_le_mul (hX _ _) (hY _ _))
    (hZ _ _)

theorem Pre_le : ∀ (w : List (Fin 2)) (i j : Q), Pre A u w i j ≤ Rigid.DxN A.B w i j := by
  intro w
  induction' hn : w.length using Nat.strong_induction_on with n ih generalizing w
  intro i j
  rw [Pre_eq, Matrix.add_apply, Matrix.sum_apply]
  have hfirst := DxN_first (Dp A) (Ep A) w
  rw [← B_eq_Dp_add_Ep A] at hfirst
  rw [hfirst, Matrix.add_apply, Matrix.sum_apply]
  refine Nat.add_le_add ?_ (Finset.sum_le_sum fun q hq => ?_)
  · split_ifs with hw
    · subst hw; simp
    · simp
  · have hq' := Finset.mem_range.1 hq
    refine mul3_le (SSt_le A u _) (fun _ _ => le_rfl) (fun a b => ?_) i j
    exact ih _ (by rw [← hn, List.length_drop]; omega) _ rfl a b

theorem detW_le (w : List (Fin 2)) (i j : Q) : detW A u w i j ≤ Rigid.DxN A.B w i j := by
  rcases w with _ | ⟨b, w⟩
  · simp [detW]
  · rw [detW, DxN_cons', Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_le_sum fun k _ => Nat.mul_le_mul (Ep_le A b i k) (Pre_le A u w k j)

/-- Between reachable indices, `reachCnt` does not increase. -/
theorem reachCnt_le_of_conn {i j : Q} (h : Conn A i j) : reachCnt A j ≤ reachCnt A i := by
  classical
  unfold reachCnt
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact conn_trans A h hx

/-- An edge of a detour strictly decreases `reachCnt`. -/
theorem detW_reach {w : List (Fin 2)} {i j : Q} (h : 1 ≤ detW A u w i j) : reachCnt A j < reachCnt A i := by
  rcases w with _ | ⟨b, w⟩
  · simp [detW] at h
  · rw [detW] at h
    obtain ⟨k, hk1, hk2⟩ := exists_mid_mul h
    have h1 := reachCnt_lt_of_Ep A hk1
    have h2 := reachCnt_le_of_conn A (conn_of_DxN A (le_trans hk2 (Pre_le A u w k j)))
    omega

theorem conn_of_detW {w : List (Fin 2)} {i j : Q} (h : 1 ≤ detW A u w i j) : Conn A i j :=
  conn_of_DxN A (le_trans h (detW_le A u w i j))

end Kernel

/-! ## §3 Splitting on the side of paths -/

section Path

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) (u : List (Fin 2))
variable (ω : List (Fin 2)) (tm : ℕ) (j1 : Q)

/-- `Fp x := B_{ω_{(x,t_m]}} · D_{u♯}`: the paths from time `x` to the end of the last copy that do not cross within the last copy. -/
noncomputable def Fp (x : ℕ) : Matrix Q Q ℕ := Rigid.DxN A.B (seg ω x tm) * Rigid.DxN (Dp A) u

/-- `LFp x i`: the sum over the paths that start with a long sojourn at time `x` at the index `i` (`i ∈ Q_s`, and the first sojourn contains `u♯`)
and reach `(t_m + |u♯|, j₁)` without crossing within the last copy. -/
noncomputable def LFp (x : ℕ) (i : Q) : ℕ :=
  ind (InZ A i) * (Rigid.DxN (Dp A) (seg ω x (tm + u.length)) i j1 +
    ∑ q ∈ Finset.Ico x tm, ind (u <:+: seg ω x q) *
      (Rigid.DxN (Dp A) (seg ω x q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) i j1)

theorem ind_pos {P : Prop} (h : P) : ind P = 1 := by unfold ind; simp [h]

theorem ind_neg {P : Prop} (h : ¬ P) : ind P = 0 := by unfold ind; simp [h]

theorem ind_and (P R : Prop) : ind (P ∧ R) = ind P * ind R := by
  by_cases hP : P <;> by_cases hR : R <;> simp [ind_pos, ind_neg, hP, hR]

variable {A u ω tm j1}

section Hyp

variable (hcopy : seg ω tm (tm + u.length) = u) (hN : tm + u.length ≤ ω.length)
include hcopy hN

/-- The decomposition at the first crossing position (absolute positions). -/
theorem Fp_first {x : ℕ} (hx : x ≤ tm) :
    Fp A u ω tm x = Rigid.DxN (Dp A) (seg ω x (tm + u.length)) +
      ∑ q ∈ Finset.Ico x tm, Rigid.DxN (Dp A) (seg ω x q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1) := by
  have h := DxN_first (Dp A) (Ep A) (seg ω x tm)
  rw [← B_eq_Dp_add_Ep A] at h
  unfold Fp
  rw [h, add_mul, Finset.sum_mul]
  congr 1
  · rw [← DxN_append', seg_append ω hx (show tm ≤ tm + u.length by omega), hcopy]
  · rw [length_seg ω (by omega), Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [seg_take ω x tm k (by omega), seg_getD ω x tm k (by omega), seg_drop, mul_assoc,
      show x + (k + 1) = x + k + 1 by omega]

/-- The recursion of the prefix kernel (absolute positions). -/
theorem Pre_seg {x x' : ℕ} (hxx : x ≤ x') (hx' : x' ≤ ω.length) :
    Pre A u (seg ω x x') = (if x = x' then 1 else 0) +
      ∑ q ∈ Finset.Ico x x', SSt A u (seg ω x q) * Ep A (ω.getD q 0) * Pre A u (seg ω (q + 1) x') := by
  rw [Pre_eq]
  congr 1
  · have : seg ω x x' = [] ↔ x = x' := by rw [seg_eq_nil_iff ω hx']; omega
    simp only [this]
  · rw [length_seg ω hx', Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [seg_take ω x x' k (by omega), seg_getD ω x x' k (by omega), seg_drop,
      show x + (k + 1) = x + k + 1 by omega]

end Hyp

/-- Splitting the rows: `(D_w Y)_{ij} = [i ∈ Q_s ∧ u♯ ⊑ w] (D_w Y)_{ij} + (SSt_w Y)_{ij}`. -/
theorem row_split (w : List (Fin 2)) (Y : Matrix Q Q ℕ) (i j : Q) :
    (Rigid.DxN (Dp A) w * Y) i j = ind (InZ A i ∧ u <:+: w) * (Rigid.DxN (Dp A) w * Y) i j + (SSt A u w * Y) i j := by
  by_cases h : InZ A i ∧ u <:+: w
  · rw [ind_pos h, one_mul]
    have : (SSt A u w * Y) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [SSt, h]
    rw [this, add_zero]
  · rw [ind_neg h, zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [SSt, h]

/-- For a relevant `j₁`, a sojourn from an `i` not in `Q_s` that contains `u♯` has weight 0 (the killing property). -/
theorem stay_zero_of_not_inZ (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (BRel (ZIdx A))}
    {e : BRel (ZIdx A)} (hS : Sharp A K u e) {w : List (Fin 2)} (hw : u <:+: w) {i j : Q} (hj : Rel A j)
    (hi : ¬ InZ A i) : Rigid.DxN (Dp A) w i j = 0 := by
  by_contra hne
  have hpos := Nat.one_le_iff_ne_zero.2 hne
  obtain ⟨hji, hB⟩ := DxN_Dp_pos A hpos
  have hij : i ∈ sccOf A j := by rw [mem_sccOf] at hji ⊢; exact ⟨hji.2, hji.1⟩
  have hrel : Rel A i := rel_of_mem_sccOf A hj hij
  exact hi (inZ_of_stay A h01 hS hrel hji hB hw)

theorem mul3_apply (X Y Z : Matrix Q Q ℕ) (i j : Q) :
    (X * Y * Z) i j = ∑ l, (∑ k, X i k * Y k l) * Z l j := by
  simp only [Matrix.mul_apply]

section Main

variable (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (BRel (ZIdx A))} {e : BRel (ZIdx A)}
  (hS : Sharp A K u e) (hcopy : seg ω tm (tm + u.length) = u) (hN : tm + u.length ≤ ω.length) (hj1 : Rel A j1)
include h01 hS hcopy hN hj1

/-- **The first splitting** (cut at the first long sojourn): `(Fp x)_{i j₁} = Σ_{x' ∈ [x, t_m]} Σ_{i'} Pre(ω_{(x,x']})_{i i'} LFp x' i'`. -/
theorem Fp_decomp : ∀ x, x ≤ tm → ∀ i, Fp A u ω tm x i j1 =
    ∑ x' ∈ Finset.Icc x tm, ∑ i', Pre A u (seg ω x x') i i' * LFp A u ω tm j1 x' i' := by
  intro x
  induction' hn : tm - x using Nat.strong_induction_on with n ih generalizing x
  intro hx i
  -- left-hand side: split at the first crossing position, and by whether the first sojourn is long or short
  have hL : Fp A u ω tm x i j1 = LFp A u ω tm j1 x i +
      ∑ q ∈ Finset.Ico x tm, (SSt A u (seg ω x q) * (Ep A (ω.getD q 0) * Fp A u ω tm (q + 1))) i j1 := by
    rw [Fp_first hcopy hN hx, Matrix.add_apply, Matrix.sum_apply]
    have hstay : Rigid.DxN (Dp A) (seg ω x (tm + u.length)) i j1 =
        ind (InZ A i) * Rigid.DxN (Dp A) (seg ω x (tm + u.length)) i j1 := by
      by_cases hi : InZ A i
      · rw [ind_pos hi, one_mul]
      · have hw : u <:+: seg ω x (tm + u.length) := by
          rw [seg_append ω hx (show tm ≤ tm + u.length by omega), hcopy]
          exact (List.suffix_append _ _).isInfix
        rw [ind_neg hi, zero_mul, stay_zero_of_not_inZ h01 hS hw hj1 hi]
    have hsplit : ∀ q ∈ Finset.Ico x tm,
        (Rigid.DxN (Dp A) (seg ω x q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) i j1 =
          ind (InZ A i) * (ind (u <:+: seg ω x q) *
            (Rigid.DxN (Dp A) (seg ω x q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) i j1) +
          (SSt A u (seg ω x q) * (Ep A (ω.getD q 0) * Fp A u ω tm (q + 1))) i j1 := by
      intro q _
      have h := row_split (A := A) (u := u) (seg ω x q) (Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) i j1
      rw [← Matrix.mul_assoc (Rigid.DxN (Dp A) (seg ω x q))] at h
      conv_lhs => rw [h]
      rw [ind_and]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hstay, LFp, mul_add]
    ring
  rw [hL]
  -- right-hand side: unfold the prefix kernel by one step
  have hR : ∑ x' ∈ Finset.Icc x tm, ∑ i', Pre A u (seg ω x x') i i' * LFp A u ω tm j1 x' i' =
      LFp A u ω tm j1 x i + ∑ x' ∈ Finset.Icc x tm, ∑ q ∈ Finset.Ico x x', ∑ i',
        (SSt A u (seg ω x q) * Ep A (ω.getD q 0) * Pre A u (seg ω (q + 1) x')) i i' * LFp A u ω tm j1 x' i' := by
    have e1 : ∀ x' ∈ Finset.Icc x tm, ∑ i', Pre A u (seg ω x x') i i' * LFp A u ω tm j1 x' i' =
        (if x = x' then LFp A u ω tm j1 x' i else 0) + ∑ q ∈ Finset.Ico x x', ∑ i',
          (SSt A u (seg ω x q) * Ep A (ω.getD q 0) * Pre A u (seg ω (q + 1) x')) i i' * LFp A u ω tm j1 x' i' := by
      intro x' hx'
      have hx'' := Finset.mem_Icc.1 hx'
      rw [Pre_seg hcopy hN hx''.1 (by omega)]
      simp only [Matrix.add_apply, Matrix.sum_apply, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      · split_ifs with hxx
        · simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        · simp
      · rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq]
    simp [hx]
  rw [hR]
  congr 1
  -- exchange the double sum and use the induction hypothesis
  rw [Finset.sum_comm' (t' := Finset.Ico x tm) (s' := fun q => Finset.Icc (q + 1) tm)
    (fun x' q => by simp only [Finset.mem_Icc, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' := Finset.mem_Ico.1 hq
  have hih := ih (tm - (q + 1)) (by omega) (q + 1) rfl (by omega)
  rw [← Matrix.mul_assoc]
  symm
  calc ∑ x' ∈ Finset.Icc (q + 1) tm, ∑ i',
        (SSt A u (seg ω x q) * Ep A (ω.getD q 0) * Pre A u (seg ω (q + 1) x')) i i' * LFp A u ω tm j1 x' i'
      = ∑ x' ∈ Finset.Icc (q + 1) tm, ∑ i', ∑ l, (SSt A u (seg ω x q) * Ep A (ω.getD q 0)) i l *
          (Pre A u (seg ω (q + 1) x') l i' * LFp A u ω tm j1 x' i') := by
        refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun i' _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ l, (SSt A u (seg ω x q) * Ep A (ω.getD q 0)) i l *
          ∑ x' ∈ Finset.Icc (q + 1) tm, ∑ i', Pre A u (seg ω (q + 1) x') l i' * LFp A u ω tm j1 x' i' := by
        simp only [Finset.mul_sum]
        exact (Finset.sum_congr rfl fun x' _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ l, (SSt A u (seg ω x q) * Ep A (ω.getD q 0)) i l * Fp A u ω tm (q + 1) l j1 := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hih l]
    _ = (SSt A u (seg ω x q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) i j1 := (Matrix.mul_apply).symm

/-- **The recursion over long sojourns**: `LFp x i = [i ∈ Q_s](D_{(x,t₁]} + Σ_{q} [u♯ ⊑ ω_{(x,q]}] Σ_k D_{(x,q]} Σ_{x'} Σ_{i'} detW_{(q,x']} LFp x')`. -/
theorem LFp_rec (x : ℕ) (i : Q) : LFp A u ω tm j1 x i =
    ind (InZ A i) * (Rigid.DxN (Dp A) (seg ω x (tm + u.length)) i j1 +
      ∑ q ∈ Finset.Ico x tm, ind (u <:+: seg ω x q) * ∑ k, Rigid.DxN (Dp A) (seg ω x q) i k *
        ∑ x' ∈ Finset.Icc (q + 1) tm, ∑ i', detW A u (seg ω q x') k i' * LFp A u ω tm j1 x' i') := by
  conv_lhs => rw [LFp]
  congr 2
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' := Finset.mem_Ico.1 hq
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Matrix.mul_apply]
  simp_rw [Fp_decomp h01 hS hcopy hN hj1 (q + 1) (by omega)]
  have hdet : ∀ x' ∈ Finset.Icc (q + 1) tm, ∀ i', detW A u (seg ω q x') k i' =
      ∑ l, Ep A (ω.getD q 0) k l * Pre A u (seg ω (q + 1) x') l i' := by
    intro x' hx' i'
    have hx'' := Finset.mem_Icc.1 hx'
    rw [seg_cons ω (show q < x' by omega) (by omega), detW, Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun x' hx' => Finset.sum_congr rfl fun i' _ => by rw [hdet x' hx' i']]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun l _ => by ring

end Main

section Mid

/-- If a relevant `i` is not in `Q_s`, a sojourn that contains `u♯` has weight 0. -/
theorem stay_zero_of_not_inZ' (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (BRel (ZIdx A))}
    {e : BRel (ZIdx A)} (hS : Sharp A K u e) {w : List (Fin 2)} (hw : u <:+: w) {i j : Q} (hi : Rel A i)
    (hz : ¬ InZ A i) : Rigid.DxN (Dp A) w i j = 0 := by
  by_contra hne
  obtain ⟨hji, hB⟩ := DxN_Dp_pos A (Nat.one_le_iff_ne_zero.2 hne)
  exact hz (inZ_of_stay A h01 hS hi hji hB hw)

variable (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (BRel (ZIdx A))} {e : BRel (ZIdx A)}
  (hS : Sharp A K u e) (hcopy : seg ω tm (tm + u.length) = u) (hN : tm + u.length ≤ ω.length)
include h01 hS hcopy hN

/-- **The middle factor**: the sum over the paths from the first copy `ω_{(a₀,t₀]} = u♯` to the last copy that do not cross within the two copies is `LFp a₀ j₀`. -/
theorem mid_eq_LFp {a0 : ℕ} (ha0 : seg ω a0 (a0 + u.length) = u) (hat : a0 + u.length ≤ tm) {j0 : Q}
    (hj0 : Rel A j0) :
    (Rigid.DxN (Dp A) u * Rigid.DxN A.B (seg ω (a0 + u.length) tm) * Rigid.DxN (Dp A) u) j0 j1 =
      LFp A u ω tm j1 a0 j0 := by
  set t0 := a0 + u.length
  have hL : 1 ≤ u.length := List.length_pos_iff.2 hS.ne_nil
  rw [Matrix.mul_assoc, show Rigid.DxN A.B (seg ω t0 tm) * Rigid.DxN (Dp A) u = Fp A u ω tm t0 from rfl,
    Fp_first hcopy hN hat]
  have hexp : Rigid.DxN (Dp A) u * (Rigid.DxN (Dp A) (seg ω t0 (tm + u.length)) +
      ∑ q ∈ Finset.Ico t0 tm, Rigid.DxN (Dp A) (seg ω t0 q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) =
      Rigid.DxN (Dp A) (seg ω a0 (tm + u.length)) +
        ∑ q ∈ Finset.Ico t0 tm, Rigid.DxN (Dp A) (seg ω a0 q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · rw [← DxN_append', ← ha0, ← seg_append ω (show a0 ≤ t0 by omega) (by omega)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      have hq' := Finset.mem_Ico.1 hq
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← DxN_append', ← ha0,
        ← seg_append ω (show a0 ≤ t0 by omega) hq'.1]
  rw [hexp, Matrix.add_apply, Matrix.sum_apply, LFp]
  -- the condition for a long sojourn is `q ≥ t₀`
  have hsum : ∑ q ∈ Finset.Ico a0 tm, ind (u <:+: seg ω a0 q) *
      (Rigid.DxN (Dp A) (seg ω a0 q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) j0 j1 =
      ∑ q ∈ Finset.Ico t0 tm, (Rigid.DxN (Dp A) (seg ω a0 q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) j0 j1 := by
    rw [← Finset.sum_Ico_consecutive _ (show a0 ≤ t0 by omega) hat]
    have h1 : ∑ q ∈ Finset.Ico a0 t0, ind (u <:+: seg ω a0 q) *
        (Rigid.DxN (Dp A) (seg ω a0 q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) j0 j1 = 0 := by
      refine Finset.sum_eq_zero fun q hq => ?_
      have hq' := Finset.mem_Ico.1 hq
      rw [ind_neg, zero_mul]
      intro hin
      have := hin.length_le
      rw [length_seg ω (by omega)] at this
      omega
    rw [h1, zero_add]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_Ico.1 hq
    rw [ind_pos, one_mul]
    rw [seg_append ω (show a0 ≤ t0 by omega) hq'.1, ha0]
    exact (List.prefix_append _ _).isInfix
  rw [hsum]
  by_cases hz : InZ A j0
  · rw [ind_pos hz, one_mul]
  · rw [ind_neg hz, zero_mul]
    have h0 : ∀ q, t0 ≤ q → ∀ k, Rigid.DxN (Dp A) (seg ω a0 q) j0 k = 0 := by
      intro q hq k
      refine stay_zero_of_not_inZ' h01 hS ?_ hj0 hz
      rw [seg_append ω (show a0 ≤ t0 by omega) hq, ha0]
      exact (List.prefix_append _ _).isInfix
    rw [h0 (tm + u.length) (by omega) j1, zero_add]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [h0 q (Finset.mem_Ico.1 hq).1 k, zero_mul]

/-- `LFp ≤ Fp` (the paths whose first sojourn is long form a partial sum of the paths). -/
theorem LFp_le {x : ℕ} (hx : x ≤ tm) (i : Q) : LFp A u ω tm j1 x i ≤ Fp A u ω tm x i j1 := by
  rw [Fp_first hcopy hN hx, Matrix.add_apply, Matrix.sum_apply, LFp]
  have h1 := ind_le_one (InZ A i)
  calc ind (InZ A i) * (Rigid.DxN (Dp A) (seg ω x (tm + u.length)) i j1 +
        ∑ q ∈ Finset.Ico x tm, ind (u <:+: seg ω x q) *
          (Rigid.DxN (Dp A) (seg ω x q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) i j1)
      ≤ 1 * (Rigid.DxN (Dp A) (seg ω x (tm + u.length)) i j1 +
        ∑ q ∈ Finset.Ico x tm, 1 *
          (Rigid.DxN (Dp A) (seg ω x q) * Ep A (ω.getD q 0) * Fp A u ω tm (q + 1)) i j1) := by
        refine Nat.mul_le_mul h1 (Nat.add_le_add le_rfl (Finset.sum_le_sum fun q _ => ?_))
        exact Nat.mul_le_mul (ind_le_one _) le_rfl
    _ = _ := by simp

/-- If an entry of `Fp` is positive, then `j₁` is reachable from `i`. -/
theorem conn_of_Fp {x : ℕ} {i : Q} (h : 1 ≤ Fp A u ω tm x i j1) : Conn A i j1 := by
  unfold Fp at h
  obtain ⟨k, h1, h2⟩ := exists_mid_mul h
  exact conn_trans A (conn_of_DxN A h1) (conn_of_DxN A (le_trans h2 (DxN_Dp_le A u k j1)))

end Mid

end Path

end Collatz.Arctic.NatQ5.W3c
