/-
Lean proof of Lemma 6.5 of the paper (upper bound from window frequencies), Section 6.3.
The parts are in `UpperPath.lean` (windows, paths) and `UpperCarry.lean` (transport).
The block bound for each component is `block_upper` in `RateUpper.lean`, and the marginalization of window frequencies is `winClose_marginal` in
`WindowLLN3.lean` (neither is a hypothesis).

* Partitions `List Seg` (intervals `[lo, hi)` with an exceptional mark) and the condition `GoodPartition` (covers `[0, N)` in order, each width `≤ εN`,
  number `≤ ε⁻²`, total length of the exceptional intervals `≤ εN`, window frequencies of length `J` within `δ` of uniform on the non-exceptional intervals).
* Main theorem `lemma_56_11_1`: `v ≤ (Λ_{I_T}(b) + C₁ε)T + C_u`, `C₁ = 1 + 2(D + 2)M` (`M` is an upper bound for the finite entries of the matrices,
  `D` the number of indices; it depends only on the automaton).

**Remark on the method** (the statement is the same or stronger: `T` need not be a greedily chosen occurrence, and `u*` may be empty):
* Instead of cutting the path into stays in components, separating long stays (containing the chosen occurrences) from short stays (not containing `u*`) and counting
  the short ones by window frequencies of length `G`, we account **per interval of the partition**. Since `δ < 2^{-J}/2` and `J ≥ 2|u*|`, every non-exceptional
  interval contains an occurrence of `u*` (`occ_of_winClose`). Hence, for a non-exceptional interval `[lo, hi)` (`hi ≤ T`):
  - if the path stays in one component on that interval, it is a long stay (`stay_long` and `block_upper`; marginalization lowers `J` to the `J_C` of the
    component; short intervals (of length `< L₀`) are bounded by `M L₀` and multiplied by the number `≤ ε⁻²`);
  - if the path leaves a component, the number `reachCard` of reachable indices drops by at least 1 (at most `D` such intervals, each of weight `≤ MεN`).
  Exceptional intervals contribute `M ×` (length), and the interval containing `T` contributes `MεN`. These are combined by the telescoping sum of the potential
  `Ψ(t) = F(t ∧ T) - (ρ + ε)(t ∧ T) + MεN·reachCard(t ∧ T) + MεN·[t < T]`, where `ρ = Λ_{I_T}(b)`.
* The greedy choice of occurrences and the window count for short stays are not needed.
-/
import CollatzProof.Arctic.UpperCarry
import CollatzProof.Arctic.WindowLLN3

namespace Collatz.Arctic.Upper

open Collatz.Arctic Collatz.Arctic.MinIdeal Arc

variable {D : ℕ}

/-! ### Partitions -/

/-- An interval `[lo, hi)` of a partition. `exc = true` marks an exceptional interval (no window frequencies are assumed on it). -/
structure Seg where
  lo : ℕ
  hi : ℕ
  exc : Bool

/-- The list of intervals covers `[a, e)` from left to right without gaps. -/
def SegChain : List Seg → ℕ → ℕ → Prop
  | [], a, e => a = e
  | s :: P, a, e => s.lo = a ∧ s.lo ≤ s.hi ∧ SegChain P s.hi e

/-- Total length of the exceptional intervals. -/
def excLen : List Seg → ℕ
  | [] => 0
  | s :: P => (if s.exc then s.hi - s.lo else 0) + excLen P

/-- The condition on the partition in Lemma 6.5: it covers `[0, N)` (`N = |w|`), each width is `≤ εN`, the number is `≤ ε⁻²`, the total length of the exceptional intervals
is `≤ εN`, and on the non-exceptional intervals the window frequencies of length `J` are within `δ` of uniform. -/
def GoodPartition (w : Word) (P : List Seg) (ε : ℝ) (J : ℕ) (δ : ℚ) : Prop :=
  SegChain P 0 w.length ∧
  (∀ s ∈ P, (s.hi : ℝ) ≤ s.lo + ε * w.length) ∧
  (P.length : ℝ) ≤ ε⁻¹ ^ 2 ∧
  (excLen P : ℝ) ≤ ε * w.length ∧
  (∀ s ∈ P, s.exc = false → WinClose w s.lo s.hi J δ)

lemma SegChain.lo_le_hi {P : List Seg} : ∀ {a e : ℕ}, SegChain P a e → ∀ s ∈ P, s.lo ≤ s.hi := by
  induction P with
  | nil => intro a e _ s hs; simp at hs
  | cons t P ih =>
    rintro a e ⟨-, h1, h2⟩ s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h1
    · exact ih h2 s hs

/-- Telescoping sum: if `Ψ hi - Ψ lo ≤ g` on each interval, then `Ψ e - Ψ a ≤ ∑ g`. -/
lemma chain_telescope (Ψ : ℕ → ℝ) (g : Seg → ℝ) :
    ∀ (P : List Seg) (a e : ℕ), SegChain P a e → (∀ s ∈ P, Ψ s.hi - Ψ s.lo ≤ g s) →
      Ψ e - Ψ a ≤ (P.map g).sum
  | [], a, e, h, _ => by
    simp only [SegChain] at h
    subst h; simp
  | s :: P, a, e, ⟨hlo, _, hP⟩, hg => by
    have h1 := chain_telescope Ψ g P s.hi e hP (fun t ht => hg t (List.mem_cons_of_mem _ ht))
    have h2 := hg s List.mem_cons_self
    rw [hlo] at h2
    rw [List.map_cons, List.sum_cons]
    linarith

lemma sum_map_segBound (K₀ M : ℝ) : ∀ P : List Seg,
    (P.map (fun s => K₀ + M * ((if s.exc then s.hi - s.lo else 0 : ℕ) : ℝ))).sum =
      K₀ * P.length + M * (excLen P : ℝ)
  | [] => by simp [excLen]
  | s :: P => by
    rw [List.map_cons, List.sum_cons, sum_map_segBound K₀ M P, excLen, List.length_cons]
    push_cast
    ring

/-! ### Constants -/

/-- An upper bound `M` for the finite entries of the matrices (all 7 symbols). -/
def upperM (A : Interp D) : ℕ :=
  ([Letter.f, Letter.t, Letter.d0, Letter.d1, Letter.d2, Letter.lft, Letter.rgt].map
    (fun s => ∑ i, ∑ j, natOr0 (A s i j))).sum

lemma upperM_spec (A : Interp D) : ∀ s i j v, A s i j = Arc.fin v → v ≤ upperM A := by
  intro s i j v h
  have h1 : natOr0 (A s i j) ≤ ∑ i, ∑ j, natOr0 (A s i j) :=
    (Finset.single_le_sum (f := fun j => natOr0 (A s i j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, natOr0 (A s i j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))
  have h2 : (∑ i, ∑ j, natOr0 (A s i j)) ≤ upperM A :=
    List.le_sum_of_mem (by cases s <;> simp)
  rw [h, natOr0_fin] at h1
  exact h1.trans h2


/-! ### Lemma 6.5 -/

/-- **Lemma 6.5 (upper bound from window frequencies)**. For an automaton `A`, an initial row vector `u`, an idempotent `E` of the minimal
ideal `K` of `Mon (B0 A) (B1 A)` and a digit word `u*` of type `E`, there is `C₁` (depending only on the automaton) such that for every `ε > 0` there are
`J`, `δ > 0` and `C_u` with the following property: for a digit word `w` (of length `N`), a partition `P` satisfying `GoodPartition` and the end
`T` of an occurrence of `u*` (`N ≤ 2T`, `T ≤ N`), the value `v` of an index `b` at time `T` satisfies
`v ≤ (Λ_{I_T}(b) + C₁ ε) T + C_u`. Here `I_T` is the set of classes hit by the support at time `T - |u*|` (the support at time `T` is `⋃_{i ∈ I_T} β_i`).
`C₁ = 1 + 2(D + 2)M` (`M` is an upper bound for the finite entries, `D` the number of indices). -/
theorem lemma_56_11_1 (A : Interp D) (u : Fin D → Arc) {K : Set (BRel (Fin D))}
    (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) {E : BRel (Fin D)} (hEK : E ∈ K) (hE : E * E = E)
    (us : Word) (hus : IsDigits us) (hEus : suppRel (ev A us) = E) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∃ δ : ℚ, 0 < δ ∧ ∃ Cu : ℝ,
      ∀ (w : Word) (P : List Seg) (T : ℕ), IsDigits w → GoodPartition w P ε J δ →
        w.length ≤ 2 * T → T ≤ w.length → us.length ≤ T →
        window w (T - us.length) us.length = us →
        ∀ (b : Fin D) (v : ℕ), vecAfter u A (w.take T) b = Arc.fin v →
          (v : ℝ) ≤ (rhoB hE A (hitSet hE (suppV (vecAfter u A (w.take (T - us.length))))) b
            + C₁ * ε) * T + Cu := by
  classical
  set M := upperM A with hMdef
  have hM := upperM_spec A
  refine ⟨1 + 2 * ((D : ℝ) + 2) * M, by positivity, fun ε hε => ?_⟩
  choose Jf δf hJf hδf Cf hCf using fun C : Finset (Fin D) => block_upper A C M hM ε hε
  set m := us.length with hm
  set J : ℕ := 2 * m + ∑ C, Jf C with hJdef
  have hJC : ∀ C, Jf C ≤ J := fun C => by
    have := Finset.single_le_sum (f := Jf) (fun _ _ => Nat.zero_le _) (Finset.mem_univ C)
    omega
  have hmJ : 2 * m ≤ J := by omega
  set δmin : ℚ := Finset.univ.inf' Finset.univ_nonempty δf with hδmindef
  have hδmin : 0 < δmin := (Finset.lt_inf'_iff _).2 (fun C _ => hδf C)
  have hδminC : ∀ C, δmin ≤ δf C := fun C => Finset.inf'_le _ (Finset.mem_univ C)
  set δ : ℚ := min (δmin / 2) (1 / 2 ^ (J + 2)) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  set L₀ : ℕ := J + ⌈2 * (J : ℚ) / δmin⌉₊ with hL₀
  set CstMax : ℝ := ∑ C, max 0 (Cf C) with hCstdef
  have hCst0 : 0 ≤ CstMax := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hCst : ∀ C, Cf C ≤ CstMax := fun C => (le_max_right 0 (Cf C)).trans
    (Finset.single_le_sum (f := fun C => max 0 (Cf C)) (fun _ _ => le_max_left _ _)
      (Finset.mem_univ C))
  set K₀ : ℝ := CstMax + M * L₀ with hK₀def
  have hK₀ : 0 ≤ K₀ := by positivity
  have hKC : CstMax ≤ K₀ := by
    have : (0 : ℝ) ≤ M * L₀ := by positivity
    rw [hK₀def]; linarith
  set Umax : ℕ := ∑ i, natOr0 (u i) with hUdef
  refine ⟨J, δ, hδpos, (Umax : ℝ) + K₀ * ε⁻¹ ^ 2, ?_⟩
  intro w P T hw hP hNT hTN hmT hocc b v hv
  obtain ⟨hchain, hwidth, hcount, hexc, hgood⟩ := hP
  -- the path
  obtain ⟨q, g, v0, hq0, hqT, hstep, hvsum⟩ := path_of_vecAfter u A (w.take T) b v hv
  have hlenT : (w.take T).length = T := by rw [List.length_take]; omega
  rw [hlenT] at hqT hvsum hstep
  have hg : ∀ k < T, A (w.getD k Letter.f) (q k) (q (k + 1)) = Arc.fin (g k) := fun k hk => by
    rw [← getD_take hk]; exact hstep k hk
  have hp : IsPath u A w T q :=
    ⟨by rw [hq0]; exact fin_ne_zero _, fun k hk => by rw [hg k hk]; exact fin_ne_zero _⟩
  have hgM : ∀ k < T, g k ≤ M := fun k hk => hM _ _ _ _ (hg k hk)
  have hv0 : v0 ≤ Umax := by
    have := Finset.single_le_sum (f := fun i => natOr0 (u i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (q 0))
    rwa [hq0, natOr0_fin] at this
  set I := hitSet hE (suppV (vecAfter u A (w.take (T - m)))) with hIdef
  set r := rhoB hE A I b with hrdef
  have hr0 : 0 ≤ r := rhoB_nonneg hE A I b
  set N : ℝ := (w.length : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set X : ℝ := (M : ℝ) * ε * N with hXdef
  have hX0 : 0 ≤ X := by positivity
  -- sum of the weights
  set F : ℕ → ℝ := fun t => ∑ k ∈ Finset.range t, (g k : ℝ) with hFdef
  have hFadd : ∀ t n, F (t + n) = F t + ∑ k ∈ Finset.range n, (g (t + k) : ℝ) :=
    fun t n => Finset.sum_range_add _ _ _
  have hFle : ∀ t n, t + n ≤ T → F (t + n) - F t ≤ M * n := by
    intro t n h
    rw [hFadd]
    have : ∑ k ∈ Finset.range n, (g (t + k) : ℝ) ≤ ∑ _k ∈ Finset.range n, (M : ℝ) :=
      Finset.sum_le_sum (fun k hk => by
        have := Finset.mem_range.mp hk
        exact_mod_cast hgM (t + k) (by omega))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  -- potential (number of reachable indices)
  set φ : ℕ → ℝ := fun t => (reachCard A (q t) : ℝ) with hφdef
  have hφmono : ∀ t t', t ≤ t' → t' ≤ T → φ t' ≤ φ t := fun t t' h1 h2 => by
    simp only [hφdef]; exact_mod_cast reachCard_mono (reach_path hw hp h1 h2)
  have hφD : ∀ t, φ t ≤ D := fun t => by
    simp only [hφdef]; exact_mod_cast reachCard_le A (q t)
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => Nat.cast_nonneg _
  set Ψ : ℕ → ℝ := fun t => F (min t T) - (r + ε) * ((min t T : ℕ) : ℝ) + X * φ (min t T) +
    X * (if t < T then 1 else 0) with hΨdef
  -- estimate on each interval
  have hseg : ∀ s ∈ P, Ψ s.hi - Ψ s.lo ≤ K₀ + M * ((if s.exc then s.hi - s.lo else 0 : ℕ) : ℝ) := by
    rintro ⟨lo, hi, ex⟩ hs
    have hlohi : lo ≤ hi := hchain.lo_le_hi _ hs
    have hwid : (hi : ℝ) ≤ lo + ε * N := hwidth _ hs
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hlohi
    have hnε : (n : ℝ) ≤ ε * N := by push_cast at hwid; linarith
    have hMn : (M : ℝ) * n ≤ X := by
      rw [hXdef, mul_assoc]; exact mul_le_mul_of_nonneg_left hnε (Nat.cast_nonneg _)
    have hRHS : 0 ≤ (M : ℝ) * ((if ex then lo + n - lo else 0 : ℕ) : ℝ) := by positivity
    by_cases hA : T ≤ lo
    · have e1 : min (lo + n) T = T := min_eq_right (by omega)
      have e2 : min lo T = T := min_eq_right hA
      simp only [hΨdef, e1, e2, show ¬ (lo + n < T) by omega, show ¬ lo < T by omega, ite_false]
      linarith
    by_cases hB : T < lo + n
    · have e1 : min (lo + n) T = T := min_eq_right (by omega)
      have e2 : min lo T = lo := min_eq_left (by omega)
      simp only [hΨdef, e1, e2, show ¬ (lo + n < T) by omega, show lo < T by omega, ite_false,
        ite_true]
      obtain ⟨n', hn'⟩ := Nat.exists_eq_add_of_le (show lo ≤ T by omega)
      have h1 := hFle lo n' (by omega)
      rw [← hn'] at h1
      have h2 := mul_le_mul_of_nonneg_left (hφmono lo T (by omega) le_rfl) hX0
      have h3 : (M : ℝ) * n' ≤ M * n :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast (show n' ≤ n by omega)) (Nat.cast_nonneg _)
      have hT' : ((T : ℕ) : ℝ) = lo + n' := by rw [hn']; push_cast; ring
      have h4 : 0 ≤ (r + ε) * (n' : ℝ) := by positivity
      rw [hT']
      linarith
    -- the interval lies before T
    have e1 : min (lo + n) T = lo + n := min_eq_left (by omega)
    have e2 : min lo T = lo := min_eq_left (by omega)
    have hind : (if lo + n < T then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    simp only [hΨdef, e1, e2, show lo < T by omega, ite_true]
    have hF1 := hFle lo n (by omega)
    have hφ1 := mul_le_mul_of_nonneg_left (hφmono lo (lo + n) (by omega) (by omega)) hX0
    have hind' := mul_le_mul_of_nonneg_left hind hX0
    have hcast : ((lo + n : ℕ) : ℝ) = lo + n := by push_cast; ring
    rw [hcast]
    have hrn : 0 ≤ (r + ε) * (n : ℝ) := by positivity
    -- Δ := difference of the weights − (r+ε)n + X(difference of φ)
    suffices hΔ : F (lo + n) - F lo - (r + ε) * n + X * φ (lo + n) - X * φ lo ≤
        K₀ + M * ((if ex then lo + n - lo else 0 : ℕ) : ℝ) by linarith
    cases ex with
    | true =>
      simp only [ite_true, Nat.add_sub_cancel_left]
      linarith
    | false =>
      simp only [Bool.false_eq_true, ite_false, Nat.cast_zero, mul_zero, add_zero]
      by_cases hshort : n < L₀
      · have : (M : ℝ) * n ≤ M * L₀ :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hshort.le) (Nat.cast_nonneg _)
        have : (M : ℝ) * L₀ ≤ K₀ := by rw [hK₀def]; linarith
        linarith
      by_cases hre : Reach (B0 A) (B1 A) (q (lo + n)) (q lo)
      · -- component of a long stay
        have hwc : WinClose w lo (lo + n) J δ := hgood _ hs rfl
        have hδ2 : 2 * δ < 1 / 2 ^ J := by
          have : δ ≤ 1 / 2 ^ (J + 2) := min_le_right _ _
          have h2 : (1 : ℚ) / 2 ^ (J + 2) = 1 / 2 ^ J / 4 := by rw [pow_add]; ring
          have h3 : (0 : ℚ) < 1 / 2 ^ J := by positivity
          linarith
        obtain ⟨i, hi1, hi2, hwin⟩ := occ_of_winClose hus (by omega) hδ2 hwc
        obtain ⟨C, hCr, hCw⟩ := stay_long A u hK hEK hE hEus hw hTN hmT hocc hp hg
          (lo := lo) (n := n) (by omega) hre hi1 (by omega) hwin
        rw [hqT] at hCr
        -- marginalization
        have hwc' : WinClose w lo (lo + n) (Jf C) (δf C) := by
          refine winClose_mono (winClose_marginal hw (hJC C) hwc) ?_
          have hδh : δ ≤ δmin / 2 := min_le_left _ _
          set N' := lo + n + 1 - Jf C - lo with hN'
          have hceil := Nat.le_ceil (2 * (J : ℚ) / δmin)
          have hN'ge : (⌈2 * (J : ℚ) / δmin⌉₊ : ℚ) ≤ N' := by
            have : ⌈2 * (J : ℚ) / δmin⌉₊ ≤ N' := by
              have := hJC C
              omega
            exact_mod_cast this
          have hN'pos : (0 : ℚ) < N' := by
            have : 0 < N' := by have := hJC C; omega
            exact_mod_cast this
          have hdJ : ((J - Jf C : ℕ) : ℚ) ≤ J := by exact_mod_cast Nat.sub_le J (Jf C)
          have hfrac : ((J - Jf C : ℕ) : ℚ) / N' ≤ δmin / 2 := by
            rw [div_le_iff₀ hN'pos]
            have h1 : 2 * (J : ℚ) / δmin ≤ N' := hceil.trans hN'ge
            rw [div_le_iff₀ hδmin] at h1
            linarith
          linarith [hδminC C]
        have hblk := hCf C w lo (lo + n) hw hwc'
        rw [Nat.add_sub_cancel_left] at hblk
        have hFC : F (lo + n) - F lo ≤ (fmax A C (window w lo n) : ℝ) := by
          rw [hFadd]
          have : ((∑ k ∈ Finset.range n, g (lo + k) : ℕ) : ℝ) ≤ (fmax A C (window w lo n) : ℝ) := by
            exact_mod_cast hCw
          push_cast at this
          linarith
        have h5 : (rate A C + ε) * n ≤ (r + ε) * n :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        have h6 := hCst C
        linarith
      · -- interval that leaves a component: the number of reachable indices drops
        have hlt := reachCard_lt (reach_path hw hp (show lo ≤ lo + n by omega) (by omega)) hre
        have hφlt : φ (lo + n) + 1 ≤ φ lo := by
          simp only [hφdef]; exact_mod_cast hlt
        have := mul_le_mul_of_nonneg_left hφlt hX0
        linarith
  -- telescoping sum
  have htel := chain_telescope Ψ _ P 0 w.length hchain hseg
  rw [sum_map_segBound] at htel
  have eN : min w.length T = T := min_eq_right hTN
  have e0 : min 0 T = 0 := Nat.zero_min T
  have hind0 : (if 0 < T then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  simp only [hΨdef, eN, e0, show ¬ w.length < T by omega, ite_false] at htel
  have hF0 : F 0 = 0 := by simp [hFdef]
  rw [hF0] at htel
  have h1 := mul_le_mul_of_nonneg_left hcount hK₀
  have h2 : (M : ℝ) * (excLen P : ℝ) ≤ X := by
    rw [hXdef, mul_assoc]; exact mul_le_mul_of_nonneg_left hexc (Nat.cast_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left (hφD 0) hX0
  have h4 := mul_le_mul_of_nonneg_left (hφ0 T) hX0
  have h5 := mul_le_mul_of_nonneg_left hind0 hX0
  have hFT : F T ≤ (r + ε) * T + K₀ * ε⁻¹ ^ 2 + X * (D + 2) := by
    push_cast at htel
    linarith
  have hvR : (v : ℝ) = v0 + F T := by rw [hvsum]; push_cast; rfl
  have hv0R : (v0 : ℝ) ≤ Umax := by exact_mod_cast hv0
  have hN2 : N ≤ 2 * T := by rw [hNdef]; exact_mod_cast hNT
  have hX2 : X * (D + 2) ≤ 2 * ((D : ℝ) + 2) * M * ε * T := by
    have : X ≤ M * ε * (2 * T) := by
      rw [hXdef]; exact mul_le_mul_of_nonneg_left hN2 (by positivity)
    have hD2 : (0 : ℝ) ≤ D + 2 := by positivity
    have := mul_le_mul_of_nonneg_right this hD2
    linarith
  rw [hvR]
  linarith

end Collatz.Arctic.Upper

#print axioms Collatz.Arctic.Upper.lemma_56_11_1
