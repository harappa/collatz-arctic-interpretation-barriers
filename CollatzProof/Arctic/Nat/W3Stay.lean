/-
# Natural-number interpretations of 𝒯 (Section 12.2): itineraries and sojourns

Lemmas 12.5 (itineraries), 12.6 and 12.7 (sojourns, pigeonhole) and 12.8 (polynomial bound for detour weights), in the case where
**all components are 0/1** and for any occurrence of `u♯` (after internal review). As a way around a risk noted in the design, **paths are
not handled one by one**: the expansion is algebraic, with the digit matrices split as `B_b = D_b + E_b` (the part inside components and the
part crossing components; `N_b = N^in_b + N^out_b` in the paper).

* **§1 The decomposition into `D` and `E`**: `Dp A b` (`(B_b)_{ij}`, only when `j ∈ sccOf i`) and `Ep A b` (the entries crossing components).
  `B_eq_Dp_add_Ep`. The product of a word of `D` alone is the diagonal block of `B_w` on the components (`DxN_Dp`, the weight of a sojourn). An
  edge of `E` strictly decreases the number `reachCnt` of reachable indices (`reachCnt_lt_of_Ep`).
* **§2 Decomposition at the first crossing position** (the recursive form of Lemma 12.5): `B_w = D_w + Σ_p D_{w_{<p}} E_{w_p} B_{w_{>p}}`
  (`DxN_first`, for general `D, E`).
* **§3 Sums over sets of crossing positions** (the expansion of Lemma 12.5): `mixAux D E P t w` (`E` for the letter at position `t + k` if it is in `P`, `D` otherwise).
  `B_w = Σ_{P ⊆ [t, t+|w|)} mixAux P t w` (`DxN_add_eq_sum`), the form for concatenation `mixAux_append`; in a term with a positive entry
  the number of crossing positions is at most the difference of `reachCnt` (`mixAux_pos_card`), and terms with at least `|Q|` crossings are 0 (`mixAux_eq_zero`).
* **§4 Classification of sojourns** (Lemma 12.6; after internal review): if all components are 0/1, a sojourn containing an occurrence of `u♯` is in `Q_s`
  (`inZ_of_stay`). A sojourn outside `Q_s` has length 0 in a trivial component (`stay_nil_of_not_hasEdge`) and does not contain `u*` in a non-survivable
  0/1 component (`stay_not_ustar`). **Long sojourn** `IsLong`: a sojourn in `Q_s` that contains a whole occurrence of `u♯` (any one).
  The classification is summarized in `stay_cases`.
* **§5 First occurrence**: `firstOcc u ω a` (the position of the first occurrence that starts at or after `a`). The interval `(a, b]` contains an occurrence ⟺
  `firstOcc + |u| ≤ b` (`infix_seg_iff_firstOcc`). "The next sojourn is long ⟺ `p_{k+1} ≥ r_k`" takes this form.
* **§6 Pigeonhole** (Lemma 12.7; after internal review): among the disjoint copies of `u♯` written in `(u♯)^R`, there is one containing no crossing position
  (`Unbroken`; `exists_unbroken`: a crossing position breaks at most one copy). There are a first and a last one
  (`exists_first_unbroken`, `exists_last_unbroken`; the type of `t₀`, `t₁`). In a term of positive weight, the sojourn over an unbroken copy is
  in `Q_s` (`unbroken_inZ`). If `R ≥ |Q|`, every positive term has an unbroken copy (`exists_long_copy`).
  If `Q_s = ∅`, the value is 0 (`aval_eq_zero_of_noZ`; after internal review).
* **§7 Polynomial bound** (Lemma 12.8; after internal review): if all components are 0/1, then `(B_w)_{ij}` between relevant indices is at most
  `(|Q|^2 W + 1)^{|Q|} (|w| + 1)^{|Q|}` (`entry_poly`). Detour weights are partial sums of it, so the condition (H_<) of an earlier written form holds trivially.
-/
import CollatzProof.Arctic.Nat.W3Mon

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix

set_option linter.unusedSectionVars false

/-! ## §1 The decomposition into `D` and `E` -/

section DE

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- The part inside components `D_b`: `(B_b)_{ij}` (if `j ∈ sccOf i`), and 0 otherwise. -/
noncomputable def Dp (b : Fin 2) : Matrix Q Q ℕ := fun i j => if j ∈ sccOf A i then A.B b i j else 0

/-- The part crossing components `E_b`: `(B_b)_{ij}` (if `j ∉ sccOf i`), and 0 otherwise. -/
noncomputable def Ep (b : Fin 2) : Matrix Q Q ℕ := fun i j => if j ∈ sccOf A i then 0 else A.B b i j

theorem B_eq_Dp_add_Ep : A.B = Dp A + Ep A := by
  funext b; ext i j
  simp only [Pi.add_apply, Matrix.add_apply, Dp, Ep]
  split_ifs <;> simp

theorem Dp_le (b : Fin 2) (i j : Q) : Dp A b i j ≤ A.B b i j := by
  unfold Dp; split_ifs <;> simp

theorem Ep_le (b : Fin 2) (i j : Q) : Ep A b i j ≤ A.B b i j := by
  unfold Ep; split_ifs <;> simp

/-- Indices in the same strongly connected component have the same number of reachable indices. -/
theorem reachCnt_eq_of_mem {i k : Q} (hk : k ∈ sccOf A i) : reachCnt A k = reachCnt A i := by
  classical
  unfold reachCnt
  rw [mem_sccOf] at hk
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => conn_trans A hk.1 h, fun h => conn_trans A hk.2 h⟩

theorem one_le_reachCnt (i : Q) : 1 ≤ reachCnt A i := by
  classical
  unfold reachCnt
  exact Finset.card_pos.2 ⟨i, by simp [conn_refl]⟩

theorem reachCnt_le_card (i : Q) : reachCnt A i ≤ Fintype.card Q := by
  classical
  unfold reachCnt
  exact Finset.card_filter_le _ _

/-- An edge of `E` crosses components and strictly decreases the number of reachable indices. -/
theorem reachCnt_lt_of_Ep {b : Fin 2} {i j : Q} (h : 1 ≤ Ep A b i j) : reachCnt A j < reachCnt A i := by
  unfold Ep at h
  split_ifs at h with hj
  · omega
  · exact reachCnt_lt A (conn_of_edge A h) hj

theorem Dp_pos {b : Fin 2} {i j : Q} (h : 1 ≤ Dp A b i j) : j ∈ sccOf A i ∧ 1 ≤ A.B b i j := by
  unfold Dp at h
  split_ifs at h with hj
  · exact ⟨hj, h⟩
  · omega

/-- **Weight of a sojourn**: the product of a word of `D` alone is the diagonal block of `B_w` on the components. -/
theorem DxN_Dp (w : List (Fin 2)) (i j : Q) :
    Rigid.DxN (Dp A) w i j = if j ∈ sccOf A i then Rigid.DxN A.B w i j else 0 := by
  induction w generalizing i with
  | nil =>
    simp only [DxN_nil', Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp [self_mem_sccOf]
    · simp [h]
  | cons b w ih =>
    rw [DxN_apply_cons, DxN_apply_cons]
    simp_rw [ih]
    by_cases hj : j ∈ sccOf A i
    · simp only [hj, ↓reduceIte]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Dp]
      by_cases hk : k ∈ sccOf A i
      · have : j ∈ sccOf A k := by rw [sccOf_eq_of_mem A hk]; exact hj
        simp [hk, this]
      · simp only [hk, ↓reduceIte, zero_mul]
        by_contra hne
        have h1 : 1 ≤ A.B b i k := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
        have h2 : 1 ≤ Rigid.DxN A.B w k j := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
        exact hk (sccOf_convex A i i (self_mem_sccOf A i) j hj k (conn_of_edge A h1) (conn_of_DxN A h2))
    · simp only [hj, ↓reduceIte]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp only [Dp]
      by_cases hk : k ∈ sccOf A i
      · have : j ∉ sccOf A k := by rw [sccOf_eq_of_mem A hk]; exact hj
        simp [this]
      · simp [hk]

theorem DxN_Dp_pos {w : List (Fin 2)} {i j : Q} (h : 1 ≤ Rigid.DxN (Dp A) w i j) :
    j ∈ sccOf A i ∧ 1 ≤ Rigid.DxN A.B w i j := by
  rw [DxN_Dp] at h
  split_ifs at h with hj
  · exact ⟨hj, h⟩
  · omega

end DE

/-! ## §2 Decomposition at the first crossing position -/

section First

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **Decomposition at the first crossing position**: `(D + E)_w = D_w + Σ_{p < |w|} D_{w_{<p}} E_{w_p} (D + E)_{w_{>p}}`. -/
theorem DxN_first (D E : Fin 2 → Matrix Q Q ℕ) (w : List (Fin 2)) :
    Rigid.DxN (D + E) w = Rigid.DxN D w +
      ∑ p ∈ Finset.range w.length,
        Rigid.DxN D (w.take p) * E (w.getD p 0) * Rigid.DxN (D + E) (w.drop (p + 1)) := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [DxN_cons', ih, Pi.add_apply, List.length_cons, Finset.sum_range_succ', DxN_cons']
    simp only [List.take_succ_cons, List.getD_cons_succ, List.drop_succ_cons, List.take_zero,
      List.getD_cons_zero, List.drop_zero, DxN_nil', one_mul, DxN_cons', DxN_cons', ih]
    rw [add_mul, mul_add, Finset.mul_sum]
    simp only [mul_assoc]
    abel

end First

/-! ## §3 Sums over sets of crossing positions (the expansion of Lemma 12.5) -/

section Mix

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The term for a fixed set `P` of crossing positions: the `k`-th letter of the word `w` (absolute position `t + k`) gives `E` if `t + k ∈ P` and `D` otherwise. -/
def mixAux (D E : Fin 2 → Matrix Q Q ℕ) (P : Finset ℕ) : ℕ → List (Fin 2) → Matrix Q Q ℕ
  | _, [] => 1
  | t, b :: w => (if t ∈ P then E b else D b) * mixAux D E P (t + 1) w

variable (D E : Fin 2 → Matrix Q Q ℕ)

@[simp] theorem mixAux_nil (P : Finset ℕ) (t : ℕ) : mixAux D E P t [] = 1 := rfl

theorem mixAux_cons (P : Finset ℕ) (t : ℕ) (b : Fin 2) (w : List (Fin 2)) :
    mixAux D E P t (b :: w) = (if t ∈ P then E b else D b) * mixAux D E P (t + 1) w := rfl

/-- The form for concatenation: `mixAux P t (w w') = mixAux P t w · mixAux P (t + |w|) w'`. -/
theorem mixAux_append (P : Finset ℕ) (w w' : List (Fin 2)) :
    ∀ t, mixAux D E P t (w ++ w') = mixAux D E P t w * mixAux D E P (t + w.length) w' := by
  induction w with
  | nil => intro t; simp
  | cons b w ih =>
    intro t
    rw [List.cons_append, mixAux_cons, ih, mixAux_cons, mul_assoc, List.length_cons,
      show t + 1 + w.length = t + (w.length + 1) by omega]

/-- `mixAux` does not change if `P` is the same on the range `[t, t + |w|)` of the word. -/
theorem mixAux_congr {P P' : Finset ℕ} (w : List (Fin 2)) :
    ∀ t, (∀ x, t ≤ x → x < t + w.length → (x ∈ P ↔ x ∈ P')) → mixAux D E P t w = mixAux D E P' t w := by
  induction w with
  | nil => intro t _; rfl
  | cons b w ih =>
    intro t h
    rw [mixAux_cons, mixAux_cons, ih (t + 1) (fun x h1 h2 => h x (by omega) (by simp at h2 ⊢; omega))]
    have ht : t ∈ P ↔ t ∈ P' := h t le_rfl (by simp)
    by_cases h1 : t ∈ P
    · simp only [h1, ht.1 h1, ↓reduceIte]
    · simp only [h1, (not_congr ht).1 h1, ↓reduceIte]

/-- If `P` has no element in the range `[t, t + |w|)`, the term is `D_w`. -/
theorem mixAux_of_disjoint {P : Finset ℕ} (w : List (Fin 2)) :
    ∀ t, (∀ x ∈ P, ¬ (t ≤ x ∧ x < t + w.length)) → mixAux D E P t w = Rigid.DxN D w := by
  induction w with
  | nil => intro t _; rfl
  | cons b w ih =>
    intro t h
    have ht : t ∉ P := fun ht => h t ht ⟨le_rfl, by simp⟩
    rw [mixAux_cons, ih (t + 1) (fun x hx hx' => h x hx ⟨by omega, by simp at hx' ⊢; omega⟩), DxN_cons']
    simp only [ht, ↓reduceIte]

theorem Ico_succ_eq_insert (t n : ℕ) : Finset.Ico t (t + (n + 1)) = insert t (Finset.Ico (t + 1) (t + 1 + n)) := by
  ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega

/-- **Sum over sets of crossing positions** (the expansion of Lemma 12.5): `(D + E)_w = Σ_{P ⊆ [t, t + |w|)} mixAux P t w`. -/
theorem DxN_add_eq_sum (w : List (Fin 2)) :
    ∀ t, Rigid.DxN (D + E) w = ∑ P ∈ (Finset.Ico t (t + w.length)).powerset, mixAux D E P t w := by
  induction w with
  | nil => intro t; simp
  | cons b w ih =>
    intro t
    set s := Finset.Ico (t + 1) (t + 1 + w.length)
    have hts : t ∉ s := by simp [s]
    rw [List.length_cons, Ico_succ_eq_insert, Finset.powerset_insert]
    rw [Finset.sum_union]
    · rw [Finset.sum_image]
      · have e1 : ∀ P ∈ s.powerset, mixAux D E P t (b :: w) = D b * mixAux D E P (t + 1) w := by
          intro P hP
          have : t ∉ P := fun h => hts (Finset.mem_powerset.1 hP h)
          rw [mixAux_cons]
          simp only [this, ↓reduceIte]
        have e2 : ∀ P ∈ s.powerset, mixAux D E (insert t P) t (b :: w) = E b * mixAux D E P (t + 1) w := by
          intro P _
          rw [mixAux_cons]
          simp only [Finset.mem_insert_self, ↓reduceIte]
          congr 1
          refine mixAux_congr D E w (t + 1) fun x hx _ => ?_
          simp only [Finset.mem_insert]
          constructor
          · rintro (h | h)
            · omega
            · exact h
          · exact Or.inr
        rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum, ← ih (t + 1),
          DxN_cons', Pi.add_apply, add_mul]
      · intro P hP P' hP' h
        have h1 : t ∉ P := fun h' => hts (Finset.mem_powerset.1 hP h')
        have h2 : t ∉ P' := fun h' => hts (Finset.mem_powerset.1 hP' h')
        have := congrArg (fun X => X.erase t) h
        simp only [Finset.erase_insert h1, Finset.erase_insert h2] at this
        exact this
    · rw [Finset.disjoint_left]
      intro P hP hP'
      obtain ⟨P', hP'', rfl⟩ := Finset.mem_image.1 hP'
      exact hts (Finset.mem_powerset.1 hP (Finset.mem_insert_self t P'))

/-- The number of elements of `P` in the range `[t, t + n)`. -/
def cntIn (P : Finset ℕ) (t n : ℕ) : ℕ := (P.filter (fun x => t ≤ x ∧ x < t + n)).card

theorem cntIn_zero (P : Finset ℕ) (t : ℕ) : cntIn P t 0 = 0 := by
  unfold cntIn
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _; omega

theorem cntIn_succ (P : Finset ℕ) (t n : ℕ) :
    cntIn P t (n + 1) = (if t ∈ P then 1 else 0) + cntIn P (t + 1) n := by
  unfold cntIn
  by_cases ht : t ∈ P
  · simp only [ht, ↓reduceIte]
    have : P.filter (fun x => t ≤ x ∧ x < t + (n + 1)) = insert t (P.filter (fun x => t + 1 ≤ x ∧ x < t + 1 + n)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hx, h1, h2⟩
        by_cases hxt : x = t
        · exact Or.inl hxt
        · exact Or.inr ⟨hx, by omega, by omega⟩
      · rintro (rfl | ⟨hx, h1, h2⟩)
        · exact ⟨ht, le_rfl, by omega⟩
        · exact ⟨hx, by omega, by omega⟩
    rw [this, Finset.card_insert_of_notMem (by simp)]
    omega
  · simp only [ht, ↓reduceIte, zero_add]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, h1, h2⟩
      have : x ≠ t := fun h => ht (h ▸ hx)
      exact ⟨hx, by omega, by omega⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨hx, by omega, by omega⟩

variable (A : ValAuto Q)

/-- In a term with a positive entry, the number of crossing positions is at most the difference of `reachCnt` (each edge of `E` decreases `reachCnt` by at least 1, and edges of `D` keep it). -/
theorem mixAux_pos_card {P : Finset ℕ} (w : List (Fin 2)) :
    ∀ t i j, 1 ≤ mixAux (Dp A) (Ep A) P t w i j → cntIn P t w.length + reachCnt A j ≤ reachCnt A i := by
  induction w with
  | nil =>
    intro t i j h
    simp only [mixAux_nil, Matrix.one_apply] at h
    split_ifs at h with hij
    · subst hij; rw [List.length_nil, cntIn_zero]; omega
    · omega
  | cons b w ih =>
    intro t i j h
    rw [mixAux_cons] at h
    obtain ⟨k, hk1, hk2⟩ := (by
      rw [Matrix.mul_apply] at h
      by_contra hc
      push Not at hc
      have : ∑ k, (if t ∈ P then Ep A b else Dp A b) i k * mixAux (Dp A) (Ep A) P (t + 1) w k j = 0 :=
        Finset.sum_eq_zero fun k _ => by
          rcases Nat.lt_or_ge ((if t ∈ P then Ep A b else Dp A b) i k) 1 with h1 | h1
          · simp [Nat.lt_one_iff.1 h1]
          · simp [Nat.lt_one_iff.1 (hc k h1)]
      omega : ∃ k, 1 ≤ (if t ∈ P then Ep A b else Dp A b) i k ∧ 1 ≤ mixAux (Dp A) (Ep A) P (t + 1) w k j)
    have hih := ih (t + 1) k j hk2
    rw [List.length_cons, cntIn_succ]
    by_cases ht : t ∈ P
    · simp only [ht, ↓reduceIte] at hk1 ⊢
      have := reachCnt_lt_of_Ep A hk1
      omega
    · simp only [ht, ↓reduceIte] at hk1 ⊢
      have := reachCnt_eq_of_mem A (Dp_pos A hk1).1
      omega

/-- A term with at least `|Q|` crossings is 0. -/
theorem mixAux_eq_zero {P : Finset ℕ} {t : ℕ} {w : List (Fin 2)} (h : Fintype.card Q ≤ cntIn P t w.length) :
    mixAux (Dp A) (Ep A) P t w = 0 := by
  ext i j
  by_contra hne
  have := mixAux_pos_card A w t i j (Nat.one_le_iff_ne_zero.2 hne)
  have h1 := one_le_reachCnt A j
  have h2 := reachCnt_le_card A i
  omega

/-- The term is at most `B_w` (entrywise). -/
theorem mixAux_le (P : Finset ℕ) (w : List (Fin 2)) :
    ∀ t i j, mixAux (Dp A) (Ep A) P t w i j ≤ Rigid.DxN A.B w i j := by
  induction w with
  | nil => intro t i j; simp
  | cons b w ih =>
    intro t i j
    rw [mixAux_cons, DxN_cons', Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_le_sum fun k _ => Nat.mul_le_mul ?_ (ih (t + 1) k j)
    split_ifs
    · exact Ep_le A b i k
    · exact Dp_le A b i k

/-- **Sum over sets of fewer than `|Q|` crossing positions**: `B_w = Σ_{P ⊆ [0, |w|), |P| < |Q|} mixAux P 0 w`. -/
theorem DxN_eq_sum_small (w : List (Fin 2)) :
    Rigid.DxN A.B w = ∑ P ∈ ((Finset.range w.length).powerset.filter (fun P => P.card < Fintype.card Q)),
      mixAux (Dp A) (Ep A) P 0 w := by
  have h := DxN_add_eq_sum (Dp A) (Ep A) w 0
  rw [← B_eq_Dp_add_Ep A, zero_add, ← Finset.range_eq_Ico] at h
  rw [h, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P hP => ?_
  split_ifs with hc
  · rfl
  · refine mixAux_eq_zero A ?_
    have hsub := Finset.mem_powerset.1 hP
    have : cntIn P 0 w.length = P.card := by
      unfold cntIn
      congr 1
      rw [Finset.filter_true_of_mem]
      intro x hx
      have := Finset.mem_range.1 (hsub hx)
      omega
    omega

end Mix

/-! ## §4 Classification of sojourns (after internal review) -/

section Stay

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- **Long sojourn** (any occurrence; after internal review): a path that stays in the component `sccOf x` while it reads the word `w` of an interval, with
`x ∈ Q_s`, where `w` contains a whole occurrence of `u♯` (any one). -/
def IsLong (u : List (Fin 2)) (x : Q) (w : List (Fin 2)) : Prop := InZ A x ∧ u <:+: w

/-- **A sojourn containing an occurrence of `u♯` is in `Q_s`** (when all components are 0/1; after internal review). -/
theorem inZ_of_stay (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (MinIdeal.BRel (ZIdx A))}
    {u : List (Fin 2)} {e : MinIdeal.BRel (ZIdx A)} (hS : Sharp A K u e) {x y : Q} (hx : Rel A x)
    (hy : y ∈ sccOf A x) {w : List (Fin 2)} (hw : 1 ≤ Rigid.DxN A.B w x y) (hu : u <:+: w) : InZ A x := by
  by_contra hz
  have h0 := hS.kills_infix A h01 hx hz hu
  have h1 : DC A (sccOf A x) w ⟨x, self_mem_sccOf A x⟩ ⟨y, hy⟩ = 0 := by rw [h0]; rfl
  rw [DC_apply] at h1
  have h2 : Rigid.DxN A.B w x y = 0 := h1
  omega

/-- A sojourn in a trivial component (without internal edge) has length 0. -/
theorem stay_nil_of_not_hasEdge {x y : Q} (hE : ¬ HasEdge A (sccOf A x)) (hy : y ∈ sccOf A x)
    {w : List (Fin 2)} (hw : 1 ≤ Rigid.DxN A.B w x y) : w = [] := by
  rcases w with _ | ⟨b, w⟩
  · rfl
  · exfalso
    have h0 := compMat_eq_zero_of_not_hasEdge A x hE b
    have h1 : DC A (sccOf A x) (b :: w) ⟨x, self_mem_sccOf A x⟩ ⟨y, hy⟩ = 0 := by
      show Rigid.DxN (compMat A (sccOf A x)) (b :: w) _ _ = 0
      rw [DxN_cons', h0, zero_mul]; rfl
    rw [DC_apply] at h1
    have h2 : Rigid.DxN A.B (b :: w) x y = 0 := h1
    omega

/-- A sojourn in a non-survivable component does not contain `u*` (`ustar_kills`, `DC_eq_zero_of_infix` of `CompartmentPi.lean`). -/
theorem stay_not_ustar {x y : Q} (hns : ¬ Survivable A (sccOf A x)) {v : List (Fin 2)} (hv : IsUStar A v)
    (hy : y ∈ sccOf A x) {w : List (Fin 2)} (hw : 1 ≤ Rigid.DxN A.B w x y) : ¬ v <:+: w := by
  intro hvw
  obtain ⟨z, hz⟩ := (not_survivable_iff A _).1 hns
  have h0 := DC_eq_zero_of_infix A (ustar_kills A hv x hz) hvw
  have h1 : DC A (sccOf A x) w ⟨x, self_mem_sccOf A x⟩ ⟨y, hy⟩ = 0 := by rw [h0]; rfl
  rw [DC_apply] at h1
  have h2 : Rigid.DxN A.B w x y = 0 := h1
  omega

/-- **Classification of sojourns** (after internal review): if all components are 0/1, a sojourn `w` of positive weight from a relevant index `x` to an index `y`
of the same component is (i) long, (ii) a short sojourn in `Q_s` (not containing `u♯`), or (iii) a sojourn outside `Q_s` (not containing `u♯`;
of length 0 for a trivial component, and not containing `u*` for a non-survivable component). -/
theorem stay_cases (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (MinIdeal.BRel (ZIdx A))}
    {u : List (Fin 2)} {e : MinIdeal.BRel (ZIdx A)} (hS : Sharp A K u e) {x y : Q} (hx : Rel A x)
    (hy : y ∈ sccOf A x) {w : List (Fin 2)} (hw : 1 ≤ Rigid.DxN A.B w x y) :
    IsLong A u x w ∨ (InZ A x ∧ ¬ u <:+: w) ∨
      (¬ InZ A x ∧ ¬ u <:+: w ∧ (¬ HasEdge A (sccOf A x) → w = []) ∧
        (HasEdge A (sccOf A x) → ∀ v, IsUStar A v → ¬ v <:+: w)) := by
  by_cases hz : InZ A x
  · by_cases hu : u <:+: w
    · exact Or.inl ⟨hz, hu⟩
    · exact Or.inr (Or.inl ⟨hz, hu⟩)
  · refine Or.inr (Or.inr ⟨hz, fun hu => hz (inZ_of_stay A h01 hS hx hy hw hu),
      fun hE => stay_nil_of_not_hasEdge A hE hy hw, fun hE v hv => ?_⟩)
    have hns : ¬ Survivable A (sccOf A x) := fun hs =>
      hz ⟨hx, hE, hs, h01 _ ⟨⟨x, hx, rfl⟩, hE⟩⟩
    exact stay_not_ustar A hns hv hy hw

end Stay

/-! ## §5 The first occurrence -/

section FirstOcc

theorem infix_seg_iff (u ω : List (Fin 2)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ ω.length) :
    u <:+: (ω.drop a).take (b - a) ↔ ∃ i, a ≤ i ∧ i + u.length ≤ b ∧ occAt u ω i := by
  constructor
  · rintro ⟨s, t, h⟩
    have hlen := congrArg List.length h
    simp only [List.length_append, List.length_take, List.length_drop] at hlen
    refine ⟨a + s.length, by omega, by omega, by omega, ?_⟩
    have hd : ((s ++ u ++ t).drop s.length).take u.length = u := by simp
    rw [h, List.drop_take, List.take_take, List.drop_drop,
      show min u.length (b - a - s.length) = u.length by omega] at hd
    exact hd
  · rintro ⟨i, hai, hib, hocc⟩
    rw [seg_split ω hai (show i ≤ b by omega),
      seg_split ω (show i ≤ i + u.length by omega) hib, show i + u.length - i = u.length by omega, hocc.2]
    exact ⟨List.take (i - a) (List.drop a ω), List.take (b - (i + u.length)) (List.drop (i + u.length) ω),
      by rw [List.append_assoc]⟩

open Classical in
/-- **First occurrence**: the position of the first occurrence of `u` that starts at or after position `a` (`|ω| + 1` if there is none). The `r_k` of an earlier written form is `firstOcc + |u♯|`. -/
noncomputable def firstOcc (u ω : List (Fin 2)) (a : ℕ) : ℕ :=
  if h : ∃ i, a ≤ i ∧ occAt u ω i then Nat.find h else ω.length + 1

theorem firstOcc_spec {u ω : List (Fin 2)} {a : ℕ} (h : ∃ i, a ≤ i ∧ occAt u ω i) :
    a ≤ firstOcc u ω a ∧ occAt u ω (firstOcc u ω a) := by
  classical
  unfold firstOcc
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Nat.find_spec h

theorem firstOcc_le {u ω : List (Fin 2)} {a i : ℕ} (hai : a ≤ i) (hi : occAt u ω i) : firstOcc u ω a ≤ i := by
  classical
  have h : ∃ i, a ≤ i ∧ occAt u ω i := ⟨i, hai, hi⟩
  unfold firstOcc
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Nat.find_min' h ⟨hai, hi⟩

/-- The interval `(a, b]` contains an occurrence of `u` starting at a position `≥ a` ⟺ `firstOcc + |u| ≤ b`. -/
theorem exists_occ_iff_firstOcc (u ω : List (Fin 2)) (a b : ℕ) (hb : b ≤ ω.length) :
    (∃ i, a ≤ i ∧ i + u.length ≤ b ∧ occAt u ω i) ↔ firstOcc u ω a + u.length ≤ b := by
  constructor
  · rintro ⟨i, hai, hib, hi⟩
    have := firstOcc_le hai hi
    omega
  · intro h
    by_cases hex : ∃ i, a ≤ i ∧ occAt u ω i
    · obtain ⟨h1, h2⟩ := firstOcc_spec hex
      exact ⟨_, h1, h, h2⟩
    · exfalso
      have : firstOcc u ω a = ω.length + 1 := by
        classical
        unfold firstOcc
        rw [dite_eq_right_of_eq_false (eq_false hex)]
      omega

/-- **"The next sojourn is long ⟺ `p_{k+1} ≥ r_k`"**: the word of the interval `(a, b]` contains `u` ⟺ `firstOcc u ω a + |u| ≤ b`. -/
theorem infix_seg_iff_firstOcc (u ω : List (Fin 2)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ ω.length) :
    u <:+: (ω.drop a).take (b - a) ↔ firstOcc u ω a + u.length ≤ b := by
  rw [infix_seg_iff u ω hab hb, exists_occ_iff_firstOcc u ω a b hb]

/-- An interval before the first occurrence does not contain `u` (the window of the tail of the range of a detour; material for `g_free`). -/
theorem not_infix_before_firstOcc (u ω : List (Fin 2)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ ω.length)
    (h : b < firstOcc u ω a + u.length) : ¬ u <:+: (ω.drop a).take (b - a) := by
  rw [infix_seg_iff_firstOcc u ω hab hb]; omega

end FirstOcc

/-! ## §6 Pigeonhole (Lemma 12.7; after internal review) -/

section Pigeon

/-- The copy `c` (of length `L` from position `c₀ + cL`) is not broken by the set `P` of crossing positions. -/
def Unbroken (P : Finset ℕ) (c₀ L c : ℕ) : Prop := ∀ p ∈ P, ¬ (c₀ + c * L ≤ p ∧ p < c₀ + (c + 1) * L)

instance (P : Finset ℕ) (c₀ L c : ℕ) : Decidable (Unbroken P c₀ L c) := by unfold Unbroken; infer_instance

/-- **Pigeonhole**: a crossing position breaks at most one copy, so if `|P| < R`, one of `R` disjoint copies is unbroken. -/
theorem exists_unbroken (P : Finset ℕ) (c₀ L R : ℕ) (hL : 1 ≤ L) (hP : P.card < R) :
    ∃ c < R, Unbroken P c₀ L c := by
  have hlt : (P.image (fun p => (p - c₀) / L)).card < (Finset.range R).card := by
    rw [Finset.card_range]; exact lt_of_le_of_lt Finset.card_image_le hP
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, Finset.mem_range.1 hc, fun p hp hpc => hcn (Finset.mem_image.2 ⟨p, hp, ?_⟩)⟩
  apply Nat.div_eq_of_lt_le
  · have := hpc.1
    rw [Nat.mul_comm] at this ⊢
    omega
  · have := hpc.2
    have h2 : (c + 1) * L = c * L + L := by ring
    omega

/-- The first unbroken copy (the type of `t₀`: the first copy in the `(u♯)^R` of the top part that lies entirely in a sojourn of the path). -/
theorem exists_first_unbroken (P : Finset ℕ) (c₀ L R : ℕ) (hL : 1 ≤ L) (hP : P.card < R) :
    ∃ c < R, Unbroken P c₀ L c ∧ ∀ c' < c, ¬ Unbroken P c₀ L c' := by
  obtain ⟨c, hc, hu⟩ := exists_unbroken P c₀ L R hL hP
  have hne : ((Finset.range R).filter (Unbroken P c₀ L)).Nonempty := ⟨c, by simp [hc, hu]⟩
  set m := ((Finset.range R).filter (Unbroken P c₀ L)).min' hne
  have hm := Finset.mem_filter.1 (Finset.min'_mem _ hne)
  refine ⟨m, Finset.mem_range.1 hm.1, hm.2, fun c' hc' hu' => ?_⟩
  have : m ≤ c' := Finset.min'_le _ c' (by simp [hu']; have := Finset.mem_range.1 hm.1; omega)
  omega

/-- The last unbroken copy (the type of `t₁`: the last copy in the `(u♯)^R` of the shared low part that lies entirely in a sojourn). -/
theorem exists_last_unbroken (P : Finset ℕ) (c₀ L R : ℕ) (hL : 1 ≤ L) (hP : P.card < R) :
    ∃ c < R, Unbroken P c₀ L c ∧ ∀ c', c < c' → c' < R → ¬ Unbroken P c₀ L c' := by
  obtain ⟨c, hc, hu⟩ := exists_unbroken P c₀ L R hL hP
  have hne : ((Finset.range R).filter (Unbroken P c₀ L)).Nonempty := ⟨c, by simp [hc, hu]⟩
  set m := ((Finset.range R).filter (Unbroken P c₀ L)).max' hne
  have hm := Finset.mem_filter.1 (Finset.max'_mem _ hne)
  refine ⟨m, Finset.mem_range.1 hm.1, hm.2, fun c' hc' hc'R hu' => ?_⟩
  have : c' ≤ m := Finset.le_max' _ c' (by simp [hu', hc'R])
  omega

/-- Split the word into three at the copy `c` of `(u)^R`: `τ' (u)^R ρ = (τ' u^c) u (u^{R-c-1} ρ)`. -/
theorem block_split (τ' ρ u : List (Fin 2)) {R c : ℕ} (hc : c < R) :
    τ' ++ (List.replicate R u).flatten ++ ρ =
      (τ' ++ (List.replicate c u).flatten) ++ u ++ ((List.replicate (R - c - 1) u).flatten ++ ρ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hc
  rw [show c + d + 1 - c - 1 = d by omega, show c + d + 1 = c + (1 + d) by omega, List.replicate_add,
    List.replicate_add, List.flatten_append, List.flatten_append]
  simp

theorem length_block_pre (τ' u : List (Fin 2)) (c : ℕ) :
    (τ' ++ (List.replicate c u).flatten).length = τ'.length + c * u.length := by
  simp [List.length_flatten, List.map_replicate, List.sum_replicate]

end Pigeon

section PigeonAuto

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

theorem exists_mid_mul {X Y : Matrix Q Q ℕ} {i j : Q} (h : 1 ≤ (X * Y) i j) : ∃ k, 1 ≤ X i k ∧ 1 ≤ Y k j := by
  rw [Matrix.mul_apply] at h
  by_contra hc
  push Not at hc
  have : ∑ k, X i k * Y k j = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rcases Nat.lt_or_ge (X i k) 1 with h1 | h1
      · simp [Nat.lt_one_iff.1 h1]
      · simp [Nat.lt_one_iff.1 (hc k h1)]
  omega

/-- **The sojourn over an unbroken copy is in `Q_s`** (when all components are 0/1): in a term of positive weight with fixed crossing positions `P` (starting
in the support of `A.u` and ending in that of `A.v`), if the copy of `u♯` (letter positions `[|w₁|, |w₁| + |u♯|)`) contains no element of `P`, then
the indices `x, y` at the two ends of the copy lie in the same component of `Q_s`, and `(B_{u♯})_{xy} ≥ 1`. -/
theorem unbroken_inZ (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (MinIdeal.BRel (ZIdx A))}
    {u : List (Fin 2)} {e : MinIdeal.BRel (ZIdx A)} (hS : Sharp A K u e) {P : Finset ℕ}
    {w₁ w₂ : List (Fin 2)} {i j : Q}
    (hP : ∀ p ∈ P, ¬ (w₁.length ≤ p ∧ p < w₁.length + u.length)) (hi : 1 ≤ A.u i) (hj : 1 ≤ A.v j)
    (h : 1 ≤ mixAux (Dp A) (Ep A) P 0 (w₁ ++ u ++ w₂) i j) :
    ∃ x y, InZ A x ∧ y ∈ sccOf A x ∧ 1 ≤ mixAux (Dp A) (Ep A) P 0 w₁ i x ∧ 1 ≤ Rigid.DxN A.B u x y ∧
      1 ≤ mixAux (Dp A) (Ep A) P (w₁.length + u.length) w₂ y j := by
  rw [mixAux_append, mixAux_append, zero_add, mixAux_of_disjoint (Dp A) (Ep A) u w₁.length hP] at h
  obtain ⟨y, hxy, hyj⟩ := exists_mid_mul h
  obtain ⟨x, hix, hxy'⟩ := exists_mid_mul hxy
  obtain ⟨hy, hB⟩ := DxN_Dp_pos A hxy'
  have hrel : Rel A x := by
    refine ⟨⟨i, hi, conn_of_DxN A (le_trans hix (mixAux_le A P w₁ 0 i x))⟩, ⟨j, ?_, hj⟩⟩
    exact conn_trans A (conn_of_DxN A hB)
      (conn_of_DxN A (le_trans (by simpa using hyj) (mixAux_le A P w₂ _ y j)))
  refine ⟨x, y, inZ_of_stay A h01 hS hrel hy hB (List.infix_refl u), hy, hix, hB, by simpa using hyj⟩

/-- **Existence of `t₀`, `t₁`** (Lemma 12.7): if `R ≥ |Q|`, every term of positive weight with crossing positions `P` on `τ'(u♯)^R ρ` has an
unbroken copy, and its sojourn is in `Q_s` (it is long). The first and the last such copy are given by `exists_first_unbroken` and
`exists_last_unbroken` (since `P` has fewer than `|Q|` elements). -/
theorem exists_long_copy (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (MinIdeal.BRel (ZIdx A))}
    {u : List (Fin 2)} {e : MinIdeal.BRel (ZIdx A)} (hS : Sharp A K u e) {R : ℕ} (hR : Fintype.card Q ≤ R)
    (τ' ρ : List (Fin 2)) {P : Finset ℕ} {i j : Q} (hi : 1 ≤ A.u i) (hj : 1 ≤ A.v j)
    (h : 1 ≤ mixAux (Dp A) (Ep A) P 0 (τ' ++ (List.replicate R u).flatten ++ ρ) i j) :
    ∃ c < R, Unbroken P τ'.length u.length c ∧ ∃ x y, InZ A x ∧ y ∈ sccOf A x ∧ 1 ≤ Rigid.DxN A.B u x y := by
  set ω := τ' ++ (List.replicate R u).flatten ++ ρ
  set P' := P.filter (fun x => 0 ≤ x ∧ x < 0 + ω.length)
  have hcard : P'.card < R := by
    have := mixAux_pos_card A ω 0 i j h
    have h1 := one_le_reachCnt A j
    have h2 := reachCnt_le_card A i
    have h3 : cntIn P 0 ω.length = P'.card := rfl
    omega
  have hL : 1 ≤ u.length := List.length_pos_iff.2 hS.ne_nil
  obtain ⟨c, hc, hun⟩ := exists_unbroken P' τ'.length u.length R hL hcard
  have hunP : Unbroken P τ'.length u.length c := by
    intro p hp hpc
    refine hun p (Finset.mem_filter.2 ⟨hp, Nat.zero_le _, ?_⟩) hpc
    have h1 := hpc.2
    have h2 : (c + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ (by omega)
    have h3 : ω.length = τ'.length + R * u.length + ρ.length := by
      simp [ω, List.length_flatten, List.map_replicate, List.sum_replicate]; omega
    omega
  refine ⟨c, hc, hunP, ?_⟩
  have hsplit := block_split τ' ρ u hc
  rw [show τ' ++ (List.replicate R u).flatten ++ ρ = ω from rfl] at hsplit
  rw [hsplit] at h
  have hP2 : ∀ p ∈ P, ¬ ((τ' ++ (List.replicate c u).flatten).length ≤ p ∧
      p < (τ' ++ (List.replicate c u).flatten).length + u.length) := by
    intro p hp hpc
    rw [length_block_pre] at hpc
    have h2 : (c + 1) * u.length = c * u.length + u.length := by ring
    exact hunP p hp ⟨hpc.1, by omega⟩
  obtain ⟨x, y, hx, hy, -, hB, -⟩ := unbroken_inZ A h01 hS hP2 hi hj h
  exact ⟨x, y, hx, hy, hB⟩

/-- **If `Q_s = ∅`, the value is 0** (after internal review): if `R ≥ |Q|` and the word contains `(u♯)^R`, no path of positive weight reaches an exit. -/
theorem aval_eq_zero_of_noZ (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (MinIdeal.BRel (ZIdx A))}
    {u : List (Fin 2)} {e : MinIdeal.BRel (ZIdx A)} (hS : Sharp A K u e) (hZ : ∀ q, ¬ InZ A q) {R : ℕ}
    (hR : Fintype.card Q ≤ R) (τ' ρ : List (Fin 2)) :
    aval A (τ' ++ (List.replicate R u).flatten ++ ρ) = 0 := by
  rw [aval_eq_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_contra hne
  have hi : 1 ≤ A.u i := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
  have hj : 1 ≤ A.v j := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
  have hB : 1 ≤ Rigid.DxN A.B (τ' ++ (List.replicate R u).flatten ++ ρ) i j :=
    Nat.one_le_iff_ne_zero.2 fun h => hne (by rw [h]; simp)
  rw [DxN_eq_sum_small A, Matrix.sum_apply] at hB
  obtain ⟨P, -, hP⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.one_le_iff_ne_zero.1 hB)
  obtain ⟨c, -, -, x, -, hx, -⟩ := exists_long_copy A h01 hS hR τ' ρ hi hj (Nat.one_le_iff_ne_zero.2 hP)
  exact hZ x hx

end PigeonAuto

/-! ## §7 Polynomial bound (after internal review) -/

section Poly

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- The entries of products of words of `D` alone from a relevant index are 0/1 (all components are 0/1; a trivial component is positive only for length 0). -/
theorem DxN_Dp_le_one (h01 : ∀ C, IsComp A C → ZeroOne A C) {i : Q} (hi : Rel A i) (w : List (Fin 2)) (j : Q) :
    Rigid.DxN (Dp A) w i j ≤ 1 := by
  rw [DxN_Dp]
  split_ifs with hj
  · by_cases hE : HasEdge A (sccOf A i)
    · have := h01 _ ⟨⟨i, hi, rfl⟩, hE⟩ w ⟨i, self_mem_sccOf A i⟩ ⟨j, hj⟩
      rwa [DC_apply] at this
    · by_contra hlt
      have hw := stay_nil_of_not_hasEdge A hE hj (by omega : 1 ≤ Rigid.DxN A.B w i j)
      subst hw
      simp only [DxN_nil', Matrix.one_apply] at hlt
      split_ifs at hlt <;> omega
  · exact Nat.zero_le _

/-- **Polynomial bound** (after internal review): if all components are 0/1 and the entries of the digit matrices are at most `W`, then for relevant indices `i, j`,
`(B_w)_{ij} ≤ (|Q|^2 W + 1)^{r} (|w| + 1)^{r}` (`r = reachCnt i ≤ |Q|`). By the decomposition at the first crossing position (`DxN_first`) and
induction on `reachCnt`. -/
theorem entry_poly_reach (h01 : ∀ C, IsComp A C → ZeroOne A C) {W : ℕ} (hW : ∀ b i j, A.B b i j ≤ W) :
    ∀ n, ∀ i j : Q, reachCnt A i ≤ n → Rel A i → Rel A j → ∀ w : List (Fin 2),
      Rigid.DxN A.B w i j ≤ (Fintype.card Q ^ 2 * W + 1) ^ n * (w.length + 1) ^ n := by
  intro n
  induction n with
  | zero =>
    intro i j hr
    have := one_le_reachCnt A i
    omega
  | succ n ih =>
    intro i j hr hi hj w
    set c := Fintype.card Q ^ 2 * W + 1
    set Mb := c ^ n * (w.length + 1) ^ n
    have hMb : 1 ≤ Mb := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hfirst := DxN_first (Dp A) (Ep A) w
    rw [← B_eq_Dp_add_Ep A] at hfirst
    rw [hfirst, Matrix.add_apply, Matrix.sum_apply]
    have h1 : Rigid.DxN (Dp A) w i j ≤ 1 := DxN_Dp_le_one A h01 hi w j
    have hterm : ∀ p ∈ Finset.range w.length,
        (Rigid.DxN (Dp A) (w.take p) * Ep A (w.getD p 0) * Rigid.DxN A.B (w.drop (p + 1))) i j ≤
          Fintype.card Q ^ 2 * (W * Mb) := by
      intro p _
      rw [Matrix.mul_apply]
      calc ∑ l, (Rigid.DxN (Dp A) (w.take p) * Ep A (w.getD p 0)) i l * Rigid.DxN A.B (w.drop (p + 1)) l j
          ≤ ∑ _l : Q, Fintype.card Q * (W * Mb) := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [Matrix.mul_apply, Finset.sum_mul]
            calc ∑ k, Rigid.DxN (Dp A) (w.take p) i k * Ep A (w.getD p 0) k l * Rigid.DxN A.B (w.drop (p + 1)) l j
                ≤ ∑ _k : Q, W * Mb := by
                  refine Finset.sum_le_sum fun k _ => ?_
                  by_cases hX : 1 ≤ Rigid.DxN (Dp A) (w.take p) i k
                  · by_cases hY : 1 ≤ Ep A (w.getD p 0) k l
                    · by_cases hZ : 1 ≤ Rigid.DxN A.B (w.drop (p + 1)) l j
                      · have hk := (DxN_Dp_pos A hX).1
                        have hrk := reachCnt_eq_of_mem A hk
                        have hrl := reachCnt_lt_of_Ep A hY
                        have hcik : Conn A i k := ((mem_sccOf A).1 hk).1
                        have hckl : Conn A k l :=
                          conn_of_edge A (le_trans hY (Ep_le A _ k l))
                        have hrel : Rel A l :=
                          rel_of_between A hi hj (conn_trans A hcik hckl) (conn_of_DxN A hZ)
                        have hZb := ih l j (by omega) hrel hj (w.drop (p + 1))
                        have hlen : (w.drop (p + 1)).length + 1 ≤ w.length + 1 := by simp
                        have hZb' : Rigid.DxN A.B (w.drop (p + 1)) l j ≤ Mb :=
                          hZb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen n))
                        have hX1 := DxN_Dp_le_one A h01 hi (w.take p) k
                        have hY1 : Ep A (w.getD p 0) k l ≤ W := (Ep_le A _ k l).trans (hW _ k l)
                        calc Rigid.DxN (Dp A) (w.take p) i k * Ep A (w.getD p 0) k l *
                              Rigid.DxN A.B (w.drop (p + 1)) l j ≤ 1 * W * Mb :=
                              Nat.mul_le_mul (Nat.mul_le_mul hX1 hY1) hZb'
                          _ = W * Mb := by ring
                      · rw [Nat.lt_one_iff.1 (Nat.lt_of_not_le hZ), mul_zero]; exact Nat.zero_le _
                    · rw [Nat.lt_one_iff.1 (Nat.lt_of_not_le hY), mul_zero, zero_mul]; exact Nat.zero_le _
                  · rw [Nat.lt_one_iff.1 (Nat.lt_of_not_le hX), zero_mul, zero_mul]; exact Nat.zero_le _
              _ = Fintype.card Q * (W * Mb) := by simp
        _ = Fintype.card Q ^ 2 * (W * Mb) := by simp; ring
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
    calc Rigid.DxN (Dp A) w i j + ∑ p ∈ Finset.range w.length,
          (Rigid.DxN (Dp A) (w.take p) * Ep A (w.getD p 0) * Rigid.DxN A.B (w.drop (p + 1))) i j
        ≤ 1 + w.length * (Fintype.card Q ^ 2 * (W * Mb)) := Nat.add_le_add h1 hsum
      _ ≤ c * (w.length + 1) * Mb := by
          have e : c * (w.length + 1) * Mb = w.length * (Fintype.card Q ^ 2 * (W * Mb)) +
              (Fintype.card Q ^ 2 * W * Mb + w.length * Mb + Mb) := by simp only [c]; ring
          rw [e]
          have := Nat.zero_le (Fintype.card Q ^ 2 * W * Mb)
          have := Nat.zero_le (w.length * Mb)
          linarith
      _ = c ^ (n + 1) * (w.length + 1) ^ (n + 1) := by simp only [Mb]; ring

/-- **Polynomial bound** (in the form with powers `|Q|`): `(B_w)_{ij} ≤ (|Q|^2 W + 1)^{|Q|} (|w| + 1)^{|Q|}` (relevant `i, j`). -/
theorem entry_poly (h01 : ∀ C, IsComp A C → ZeroOne A C) {W : ℕ} (hW : ∀ b i j, A.B b i j ≤ W)
    {i j : Q} (hi : Rel A i) (hj : Rel A j) (w : List (Fin 2)) :
    Rigid.DxN A.B w i j ≤ (Fintype.card Q ^ 2 * W + 1) ^ Fintype.card Q * (w.length + 1) ^ Fintype.card Q := by
  have h := entry_poly_reach A h01 hW (reachCnt A i) i j le_rfl hi hj w
  have hr := reachCnt_le_card A i
  exact h.trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hr) (Nat.pow_le_pow_right (by omega) hr))

/-- Polynomial bound for the value: `V(ω) ≤ (Σ A.u)(Σ A.v) (|Q|^2 W + 1)^{|Q|} (|ω| + 1)^{|Q|}`. -/
theorem aval_poly (h01 : ∀ C, IsComp A C → ZeroOne A C) {W : ℕ} (hW : ∀ b i j, A.B b i j ≤ W)
    (ω : List (Fin 2)) :
    aval A ω ≤ (∑ i, A.u i) * (∑ j, A.v j) *
      ((Fintype.card Q ^ 2 * W + 1) ^ Fintype.card Q * (ω.length + 1) ^ Fintype.card Q) := by
  set P := (Fintype.card Q ^ 2 * W + 1) ^ Fintype.card Q * (ω.length + 1) ^ Fintype.card Q
  rw [aval_eq_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hne : A.u i * Rigid.DxN A.B ω i j * A.v j = 0
  · rw [hne]; exact Nat.zero_le _
  · have hi : 1 ≤ A.u i := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    have hj : 1 ≤ A.v j := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    have hB : 1 ≤ Rigid.DxN A.B ω i j := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
    have hri : Rel A i := ⟨⟨i, hi, conn_refl A i⟩, ⟨j, conn_of_DxN A hB, hj⟩⟩
    have hrj : Rel A j := ⟨⟨i, hi, conn_of_DxN A hB⟩, ⟨j, conn_refl A j, hj⟩⟩
    calc A.u i * Rigid.DxN A.B ω i j * A.v j ≤ A.u i * P * A.v j :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (entry_poly A h01 hW hri hrj ω))
      _ = A.u i * A.v j * P := by ring

end Poly

end Collatz.Arctic.NatQ5.W3c
