/-
# Iterated sums and prefix sums (for Propositions 12.27 and 12.28 of the paper)

The deterministic part of the proofs of Propositions 12.27 and 12.28. It connects the decomposition data (`DecompData`, sums over tuples of positions `Fin s → ℕ`) with the iterated sums
of Lemma 12.15 (`W3a.gsum`, `isum`, recursion over lists), and derives the hypothesis of Lemma 12.15 (on prefix sums) from laws of large numbers on two intervals.
The written proof is Section 12.8 of the paper.

* **Sum over tuples of positions** `tupSum s M n f := Σ_{q : gaps ≥ M, q_k < n} Π_k f_k(q_k)`, and `gsum_ofFn` (it equals the value of `W3a.gsum` for the list
  `[(f_{s-1}, M), …, (f_0, M)]`).
* **The upper form (a')** (`termOf_le_upper1`): a term of the decomposition data is at most the sum over strictly increasing tuples of the sum of the weights of detours
  `XiP := Σ_{r=1}^{N} ξ(r, ·)` over the ranges `r ∈ [1, N]` (the frozen (a) uses `Σ_{r ≤ N}`, which includes `r = 0`, and does not match the stationary means of the
  coefficients (`r ≥ 1`), so the form with `r ≥ 1` is proved here). `incrSet_le_tupSum`.
* **The lower form** (`tupSum_le_gapSet`): the sum over tuples of a sequence restricted to the good positions is at most the sum over `gapSet` of the frozen (b).
* **Prefix sums on two intervals** (`prefix_two`): if the prefix sums on two intervals are close to `Q·length`, and the values at the other positions are bounded,
  then the prefix sums of the whole are close to `Q n` (the ingredient of the hypothesis `IterHyp` of Lemma 12.15).
-/
import CollatzProof.Arctic.Nat.W3hCoef
import CollatzProof.Arctic.Nat.W3Iter

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

/-! ## §1 Sums over tuples of positions and `gsum` -/

/-- The gaps between adjacent positions are at least `M`. -/
def GapM {s : ℕ} (M : ℕ) (q : Fin s → ℕ) : Prop := ∀ k k' : Fin s, k'.val = k.val + 1 → q k + M ≤ q k'

open Classical in
/-- The sum over tuples of positions `Σ_{q : gaps ≥ M, q_k < n} Π_k f_k(q_k)`. -/
noncomputable def tupSum (s M n : ℕ) (f : Fin s → ℕ → ℝ) : ℝ :=
  ∑ q ∈ (Fintype.piFinset (fun _ : Fin s => Finset.range n)).filter (GapM M), ∏ k, f k (q k)

open Classical in
theorem tupSum_zero (M n : ℕ) (f : Fin 0 → ℕ → ℝ) : tupSum 0 M n f = 1 := by
  unfold tupSum
  have : (Fintype.piFinset (fun _ : Fin 0 => Finset.range n)).filter (GapM M) = {fun k => absurd k.2 (by omega)} := by
    ext q
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · intro _; funext k; exact absurd k.2 (by omega)
    · rintro rfl; exact ⟨fun k => absurd k.2 (by omega), fun k => absurd k.2 (by omega)⟩
  rw [this, Finset.sum_singleton]
  simp

open Classical in
/-- Splitting at the last position: `tupSum (s+1) = Σ_{p<n} f_last(p) tupSum s (p + 1 - M)`. -/
theorem tupSum_succ (s M n : ℕ) (f : Fin (s + 1) → ℕ → ℝ) :
    tupSum (s + 1) M n f =
      ∑ p ∈ Finset.range n, f (Fin.last s) p * tupSum s M (p + 1 - M) (fun k => f k.castSucc) := by
  unfold tupSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun q _ => ⟨q (Fin.last s), Fin.init q⟩) (fun x _ => Fin.snoc x.2 x.1) ?_ ?_ ?_ ?_ ?_
  · -- the image lies in the target
    intro q hq
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hq
    obtain ⟨hlt, hgap⟩ := hq
    rw [Finset.mem_sigma, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨hlt _, fun k => ?_, fun k k' hk => hgap k.castSucc k'.castSucc (by simpa using hk)⟩
    -- `q k + M ≤ q last`
    have key : ∀ j : ℕ, ∀ k : Fin (s + 1), k.val + j = s → q k + M ≤ q (Fin.last s) ∨ j = 0 := by
      intro j
      induction j with
      | zero => intro _ _; right; rfl
      | succ j ih =>
        intro k hk
        left
        have hk1 : k.val + 1 < s + 1 := by omega
        have h1 := hgap k ⟨k.val + 1, hk1⟩ rfl
        rcases ih ⟨k.val + 1, hk1⟩ (by simp; omega) with h2 | h2
        · have : M ≤ M + M := Nat.le_add_right _ _
          have hq := (hgap k ⟨k.val + 1, hk1⟩ rfl)
          omega
        · subst h2
          have : (⟨k.val + 1, hk1⟩ : Fin (s + 1)) = Fin.last s := Fin.ext (by simp; omega)
          rw [this] at h1; exact h1
    rcases key (s - k.val) k.castSucc (by rw [Fin.val_castSucc]; omega) with h | h
    · rw [Finset.mem_range]
      simp only [Fin.init]; omega
    · exact absurd h (by have := k.2; omega)
  · -- the inverse image lies in the source
    intro x hx
    rw [Finset.mem_sigma, Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hp, hlt, hgap⟩ := hx
    rw [Finset.mem_range] at hp
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun k => ?_, fun k k' hk => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · simp [hp]
      · simp only [Fin.snoc_castSucc]
        have := Finset.mem_range.mp (hlt j)
        exact Finset.mem_range.mpr (by omega)
    · by_cases hk' : k'.val = s
      · have hk'last : k' = Fin.last s := Fin.ext (by simp [hk'])
        have hks : k.val < s := by omega
        have hkc : k = (⟨k.val, hks⟩ : Fin s).castSucc := Fin.ext rfl
        rw [hk'last, hkc, Fin.snoc_castSucc, Fin.snoc_last]
        have := Finset.mem_range.mp (hlt ⟨k.val, hks⟩)
        omega
      · have hk's : k'.val < s := by omega
        have hks : k.val < s := by omega
        have hkc : k = (⟨k.val, hks⟩ : Fin s).castSucc := Fin.ext rfl
        have hk'c : k' = (⟨k'.val, hk's⟩ : Fin s).castSucc := Fin.ext rfl
        rw [hkc, hk'c, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hgap _ _ (by simp [hk])
  · intro q _; simp
  · intro x _; simp
  · intro q _
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.init]
    ring

/-- **`gsum` and sums over tuples of positions**: `W3a.gsum [(f_{s-1}, M), …, (f_0, M)] n = tupSum s M n f`. -/
theorem gsum_ofFn (M : ℕ) : ∀ (s : ℕ) (f : Fin s → ℕ → ℝ) (n : ℕ),
    W3a.gsum (List.ofFn (fun j : Fin s => (f j.rev, M))) n = tupSum s M n f
  | 0, f, n => by simp [tupSum_zero]
  | s + 1, f, n => by
    rw [List.ofFn_succ, W3a.gsum_cons, tupSum_succ]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [Fin.rev_zero]
    congr 1
    have e : (fun j : Fin s => (f j.succ.rev, M)) = (fun j : Fin s => ((fun k : Fin s => f k.castSucc) j.rev, M)) := by
      funext j; simp [Fin.rev_succ]
    rw [e]
    exact gsum_ofFn M s (fun k => f k.castSucc) (p + 1 - M)

/-! ## §2 The upper bound (a') and the lower bound for the terms of the decomposition data -/

section Bounds

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- The sum of the weights of detours over the ranges `r ∈ [1, N]`, `Ξ⁺(p) := Σ_{r=1}^{N} ξ(r, p)` (`N = |ω|`). -/
noncomputable def XiP {Lab : Type} (labS : Lab → BRel (ZIdx A)) (g : Lab → ℕ → List (Fin 2) → ℕ) (l : Lab)
    (ω : List (Fin 2)) (p : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 ω.length, xiOf A labS g l r ω p

open Classical in
/-- **The upper bound (a')**: a term is at most `Σ_λ κ Σ_{p ∈ incrSet} Π_k Ξ⁺_{λ_k}(p_k)` (ranges `r ≥ 1`; Lemma 12.10 of the paper). -/
theorem termOf_le_upper1 {Lab : Type} [Fintype Lab] (labS : Lab → BRel (ZIdx A)) (s : ℕ)
    (κ : BRel (ZIdx A) → (Fin s → Lab) → ℕ) (g : Fin s → Lab → ℕ → List (Fin 2) → ℕ) (t0 t1 : ℕ)
    (sT : BRel (ZIdx A)) (ω : List (Fin 2)) :
    termOf A labS s κ g t0 t1 sT ω ≤
      ∑ l : Fin s → Lab, κ sT l * ∑ p ∈ incrSet s t0 t1, ∏ k : Fin s, XiP A labS (g k) (l k) ω (p k) := by
  unfold termOf
  refine Finset.sum_le_sum fun l _ => Nat.mul_le_mul_left _ ?_
  have hexp : ∀ p : Fin s → ℕ, ∏ k : Fin s, XiP A labS (g k) (l k) ω (p k) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 ω.length),
        ∏ k : Fin s, xiOf A labS (g k) (l k) (r k) ω (p k) := by
    intro p
    unfold XiP
    exact Finset.prod_univ_sum (fun _ => Finset.Icc 1 ω.length) (fun k r => xiOf A labS (g k) (l k) r ω (p k))
  simp_rw [hexp]
  rw [← Finset.sum_product']
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  intro pr hpr
  unfold admSet at hpr
  rw [Finset.mem_filter, Finset.mem_product] at hpr
  obtain ⟨⟨_, hr⟩, hadm⟩ := hpr
  rw [Finset.mem_product]
  refine ⟨?_, ?_⟩
  · unfold incrSet
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun k => Finset.mem_range.2 (adm_lt hadm k), adm_strictMono hadm, adm_ge hadm⟩
  · rw [Fintype.mem_piFinset] at hr ⊢
    exact fun k => Finset.mem_Icc.mpr ⟨hadm.1 k, Nat.lt_succ_iff.mp (Finset.mem_range.mp (hr k))⟩

end Bounds

open Classical in
/-- The sum over strictly increasing tuples is at most the sum over tuples of positions with gap 1 (`t₁ ≤ N`, values non-negative). -/
theorem incrSet_le_tupSum {s t0 t1 N : ℕ} (h : t1 ≤ N) (f : Fin s → ℕ → ℝ) (hf : ∀ k p, 0 ≤ f k p) :
    ∑ p ∈ incrSet s t0 t1, ∏ k, f k (p k) ≤ tupSum s 1 N f := by
  unfold tupSum
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun q _ _ => Finset.prod_nonneg fun k _ => hf k _)
  unfold incrSet at hp
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hp
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun k => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp (hp.1 k)) h), fun k k' hk => ?_⟩
  have : k < k' := by rw [Fin.lt_def]; omega
  exact hp.2.1 this

open Classical in
/-- **The lower form**: the sum over tuples of positions of a sequence `f' ≤ f` that is positive only at the good positions (`t₀ ≤ p`, `p + M ≤ t₁`) is at most the sum over `gapSet`. -/
theorem tupSum_le_gapSet {s t0 t1 M n : ℕ} (hM : 1 ≤ M) (f f' : Fin s → ℕ → ℝ)
    (hf : ∀ k p, 0 ≤ f k p) (hf' : ∀ k p, 0 ≤ f' k p) (hle : ∀ k p, f' k p ≤ f k p)
    (hgood : ∀ k p, f' k p ≠ 0 → t0 ≤ p ∧ p + M ≤ t1) :
    tupSum s M n f' ≤ ∑ q ∈ gapSet s t0 t1 M, ∏ k, f k (q k) := by
  unfold tupSum
  calc ∑ q ∈ (Fintype.piFinset (fun _ : Fin s => Finset.range n)).filter (GapM M), ∏ k, f' k (q k)
      = ∑ q ∈ ((Fintype.piFinset (fun _ : Fin s => Finset.range n)).filter (GapM M)).filter
          (fun q => ∏ k, f' k (q k) ≠ 0), ∏ k, f' k (q k) :=
        (Finset.sum_filter_of_ne (fun q _ hq => hq)).symm
    _ ≤ ∑ q ∈ ((Fintype.piFinset (fun _ : Fin s => Finset.range n)).filter (GapM M)).filter
          (fun q => ∏ k, f' k (q k) ≠ 0), ∏ k, f k (q k) :=
        Finset.sum_le_sum (fun q _ => Finset.prod_le_prod₀ (fun k _ => hf' k _) (fun k _ => hle k _))
    _ ≤ ∑ q ∈ gapSet s t0 t1 M, ∏ k, f k (q k) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) (fun q _ _ => Finset.prod_nonneg fun k _ => hf k _)
        rw [Finset.mem_filter, Finset.mem_filter] at hq
        obtain ⟨⟨_, hgap⟩, hne⟩ := hq
        have hgk : ∀ k, t0 ≤ q k ∧ q k + M ≤ t1 := fun k =>
          hgood k (q k) (fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ k) h0))
        unfold gapSet
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun k => Finset.mem_range.mpr (by have := hgk k; omega), fun k _ => (hgk k).1,
          fun k k' hk => hgap k k' hk, fun k _ => (hgk k).2⟩

/-! ## §3 Prefix sums on two intervals -/

/-- If `|f - Q| ≤ c` on the interval `[u, v)`, then `|Σ (f - Q)| ≤ (v - u) c`. -/
theorem abs_sum_Ico_sub_le {f : ℕ → ℝ} {Q c : ℝ} (u v : ℕ) (h : ∀ p, |f p - Q| ≤ c) :
    |∑ p ∈ Finset.Ico u v, f p - Q * (v - u : ℕ)| ≤ (v - u : ℕ) * c := by
  have e : ∑ p ∈ Finset.Ico u v, f p - Q * (v - u : ℕ) = ∑ p ∈ Finset.Ico u v, (f p - Q) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_comm]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ Finset.Ico u v, |f p - Q| ≤ ∑ _p ∈ Finset.Ico u v, c := Finset.sum_le_sum (fun p _ => h p)
    _ = (v - u : ℕ) * c := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- From the bound on the prefix sums of the interval `[a, b)`, the bound on the sum over `[a, min n b)`. -/
theorem good_piece {f : ℕ → ℝ} {Q E : ℝ} {a b : ℕ} (hab : a ≤ b) (hE : 0 ≤ E)
    (hI : ∀ q, a ≤ q → q ≤ b → |∑ p ∈ Finset.Ico a q, f p - Q * (q - a : ℕ)| ≤ E) (n : ℕ) :
    |∑ p ∈ Finset.Ico (min n a) (min n b), f p - Q * (min n b - min n a : ℕ)| ≤ E := by
  by_cases hn : n ≤ a
  · rw [min_eq_left hn, min_eq_left (le_trans hn hab)]; simp [hE]
  · rw [min_eq_right (by omega : a ≤ n)]
    exact hI _ (le_min (by omega) hab) (min_le_right _ _)

/-- **Prefix sums on two intervals**: if on the intervals `[a₁, b₁)`, `[a₂, b₂)` the prefix sums are within `E₁`, `E₂` of `Q·length`, and `|f - Q| ≤ c` at the other
positions, then for all `n ≤ N`, `|Σ_{p<n} f - Q n| ≤ E₁ + E₂ + c·(the number of positions outside the intervals)`. -/
theorem prefix_two {f : ℕ → ℝ} {Q c E₁ E₂ : ℝ} {a₁ b₁ a₂ b₂ N : ℕ}
    (h1 : a₁ ≤ b₁) (h2 : b₁ ≤ a₂) (h3 : a₂ ≤ b₂) (h4 : b₂ ≤ N) (hc : ∀ p, |f p - Q| ≤ c)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hI₁ : ∀ q, a₁ ≤ q → q ≤ b₁ → |∑ p ∈ Finset.Ico a₁ q, f p - Q * (q - a₁ : ℕ)| ≤ E₁)
    (hI₂ : ∀ q, a₂ ≤ q → q ≤ b₂ → |∑ p ∈ Finset.Ico a₂ q, f p - Q * (q - a₂ : ℕ)| ≤ E₂) :
    ∀ n ≤ N, |∑ p ∈ Finset.range n, f p - Q * n| ≤ E₁ + E₂ + c * ((a₁ + (a₂ - b₁) + (N - b₂) : ℕ) : ℝ) := by
  intro n hn
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hc 0)
  -- split points
  set c₁ := min n a₁; set c₂ := min n b₁; set c₃ := min n a₂; set c₄ := min n b₂
  have o1 : c₁ ≤ c₂ := min_le_min_left _ h1
  have o2 : c₂ ≤ c₃ := min_le_min_left _ h2
  have o3 : c₃ ≤ c₄ := min_le_min_left _ h3
  have o4 : c₄ ≤ n := min_le_left _ _
  have hsplit : ∑ p ∈ Finset.range n, f p = ∑ p ∈ Finset.Ico 0 c₁, f p + ∑ p ∈ Finset.Ico c₁ c₂, f p +
      ∑ p ∈ Finset.Ico c₂ c₃, f p + ∑ p ∈ Finset.Ico c₃ c₄, f p + ∑ p ∈ Finset.Ico c₄ n, f p := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) o1,
      Finset.sum_Ico_consecutive _ (le_trans (Nat.zero_le _) o1) o2,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) o3, Finset.sum_Ico_consecutive _ (Nat.zero_le _) o4]
  have hnN : n = (c₁ - 0) + (c₂ - c₁) + (c₃ - c₂) + (c₄ - c₃) + (n - c₄) := by omega
  have hn' : (n : ℝ) = (c₁ - 0 : ℕ) + (c₂ - c₁ : ℕ) + (c₃ - c₂ : ℕ) + (c₄ - c₃ : ℕ) + (n - c₄ : ℕ) := by
    conv_lhs => rw [hnN]
    simp only [Nat.cast_add]
  have b1 := abs_sum_Ico_sub_le (f := f) (Q := Q) 0 c₁ hc
  have b2 := good_piece (f := f) (Q := Q) h1 hE₁ hI₁ n
  have b3 := abs_sum_Ico_sub_le (f := f) (Q := Q) c₂ c₃ hc
  have b4 := good_piece (f := f) (Q := Q) h3 hE₂ hI₂ n
  have b5 := abs_sum_Ico_sub_le (f := f) (Q := Q) c₄ n hc
  have hcnt : ((c₁ - 0 : ℕ) : ℝ) + (c₃ - c₂ : ℕ) + (n - c₄ : ℕ) ≤ ((a₁ + (a₂ - b₁) + (N - b₂) : ℕ) : ℝ) := by
    have : (c₁ - 0) + (c₃ - c₂) + (n - c₄) ≤ a₁ + (a₂ - b₁) + (N - b₂) := by
      simp only [c₁, c₂, c₃, c₄]
      rcases le_total n a₁ with h | h <;> rcases le_total n b₁ with h' | h' <;>
        rcases le_total n a₂ with h'' | h'' <;> rcases le_total n b₂ with h''' | h''' <;>
        simp only [min_eq_left, min_eq_right, h, h', h'', h'''] <;> omega
    exact_mod_cast this
  rw [hsplit, hn']
  have e : ∑ p ∈ Finset.Ico 0 c₁, f p + ∑ p ∈ Finset.Ico c₁ c₂, f p + ∑ p ∈ Finset.Ico c₂ c₃, f p +
      ∑ p ∈ Finset.Ico c₃ c₄, f p + ∑ p ∈ Finset.Ico c₄ n, f p -
      Q * ((c₁ - 0 : ℕ) + (c₂ - c₁ : ℕ) + (c₃ - c₂ : ℕ) + (c₄ - c₃ : ℕ) + (n - c₄ : ℕ)) =
      (∑ p ∈ Finset.Ico 0 c₁, f p - Q * (c₁ - 0 : ℕ)) + (∑ p ∈ Finset.Ico c₁ c₂, f p - Q * (c₂ - c₁ : ℕ)) +
      (∑ p ∈ Finset.Ico c₂ c₃, f p - Q * (c₃ - c₂ : ℕ)) + (∑ p ∈ Finset.Ico c₃ c₄, f p - Q * (c₄ - c₃ : ℕ)) +
      (∑ p ∈ Finset.Ico c₄ n, f p - Q * (n - c₄ : ℕ)) := by ring
  rw [e]
  calc _ ≤ |∑ p ∈ Finset.Ico 0 c₁, f p - Q * (c₁ - 0 : ℕ)| + |∑ p ∈ Finset.Ico c₁ c₂, f p - Q * (c₂ - c₁ : ℕ)| +
        |∑ p ∈ Finset.Ico c₂ c₃, f p - Q * (c₃ - c₂ : ℕ)| + |∑ p ∈ Finset.Ico c₃ c₄, f p - Q * (c₄ - c₃ : ℕ)| +
        |∑ p ∈ Finset.Ico c₄ n, f p - Q * (n - c₄ : ℕ)| := by
        refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
        refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
        refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ (c₁ - 0 : ℕ) * c + E₁ + (c₃ - c₂ : ℕ) * c + E₂ + (n - c₄ : ℕ) * c := by
        gcongr
    _ ≤ E₁ + E₂ + c * ((a₁ + (a₂ - b₁) + (N - b₂) : ℕ) : ℝ) := by nlinarith

end Collatz.Arctic.NatQ5.W3h
