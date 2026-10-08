/-
# Natural-number interpretations of 𝒯 (Section 12.4), part (4): the law of large numbers for finite DFAs from window frequencies

The main theorem of Section 12.4. The "first-order frequencies" of Theorem 12.13 are given by the
**deterministic lemma** `lln_of_winClose`: if the windows of length `J'` on an interval `[a, b)` have frequencies close to uniform
(`Window.WinClose`), then, read from any starting state of the class, all prefix sums of the interval are within `ε (b - a)` of
`statMean · (length)`. An earlier written argument for part (iii) used a finite form of Agafonov's theorem and the compactness of empirical
measures; neither is used here:

* Cut the interval into blocks of length `M = J' - J`. Averaged over the offsets `r < M` of the cut, the starts of the blocks run through the starts
  of the windows of the interval once each (`Finset.sum_fiberwise_of_maps_to`).
* The difference between the sum over a block and `statMean · M` is bounded by a function of the window `v` of the block (of length `M + J`) only,
  `D v = ∑_{z ∈ class} |wsum z v M - statMean · M|` (independent of the starting state).
* The empirical mean of `D` over the windows is close to the uniform mean `𝔼 D` by the window frequencies (total variation distance `δ'`), and `𝔼 D ≤ |S| ε₀ M` is `stat_mean`.

Corollary `lln_uniform`: on an interval of uniform digits (counted by `wordsOfLen`), the same bound holds with probability at least `1 - η`
(combined with `WindowLLN2.winClose_lln_interval`; Theorem 12.13 (iv)). The variant in which the law of the digits is within total variation distance `δ` of uniform
follows in the same way, lowering the probability of the event "the window frequencies are close to uniform" by `δ` (left to the users downstream).
-/
import CollatzProof.Arctic.Nat.DfaLlnConc

namespace Collatz.Arctic.NatQ5.W3d

open Collatz.Arctic Collatz.Arctic.Dfa Filter Topology

/-! ## Lemmas on the encoding of windows -/

theorem window_map_ofB (ω : List Bool) (p J' : ℕ) :
    window (ω.map ofB) p J' = ((ω.drop p).take J').map ofB := by
  unfold window
  rw [List.map_take, List.map_drop]

/-- The window frequencies of an interval are those of the word with the part before the interval removed. -/
theorem winClose_drop {w : Word} {a b J' : ℕ} {δ' : ℚ} (h : WinClose w a b J' δ') :
    WinClose (w.drop a) 0 (b - a) J' δ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by rw [List.length_drop]; omega, ?_⟩
  have e : ∀ v, winCount (w.drop a) 0 (b - a) J' v = winCount w a b J' v := by
    intro v
    rw [winCount_eq_card, winCount_eq_card, show b - a + 1 - J' - 0 = b + 1 - J' - a by omega]
    congr 1
    apply Finset.filter_congr
    intro i _
    rw [WinLLN.window_drop, zero_add]
  simp_rw [e]
  rw [show b - a + 1 - J' - 0 = b + 1 - J' - a by omega]
  exact h3

/-- Prepending a word shifts the interval of window frequencies by its length (to move from the word of `r_σ` in `HTerrasWin` to the point word). -/
theorem winClose_append_left {w : Word} {a b J' : ℕ} {δ' : ℚ} (u : Word) (h : WinClose w a b J' δ') :
    WinClose (u ++ w) (u.length + a) (u.length + b) J' δ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by rw [List.length_append]; omega, ?_⟩
  have e : ∀ v, winCount (u ++ w) (u.length + a) (u.length + b) J' v = winCount w a b J' v := by
    intro v
    rw [winCount_eq_card, winCount_eq_card,
      show u.length + b + 1 - J' - (u.length + a) = b + 1 - J' - a by omega]
    congr 1
    apply Finset.filter_congr
    intro i _
    unfold window
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show u.length + a + i - u.length = a + i by omega]
  simp_rw [e]
  rw [show u.length + b + 1 - J' - (u.length + a) = b + 1 - J' - a by omega]
  exact h3

/-- Appending a word does not change the condition on window frequencies (the interval lies in the original word). -/
theorem winClose_append_right {w : Word} {a b J' : ℕ} {δ' : ℚ} (v : Word) (h : WinClose w a b J' δ') :
    WinClose (w ++ v) a b J' δ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, by rw [List.length_append]; omega, ?_⟩
  have e : ∀ v', winCount (w ++ v) a b J' v' = winCount w a b J' v' := by
    intro v'
    rw [winCount_eq_card, winCount_eq_card]
    congr 1
    apply Finset.filter_congr
    intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold window
    rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  simp_rw [e]
  exact h3

/-- The condition on window frequencies is preserved when `δ'` is increased. -/
theorem winClose_mono {w : Word} {a b J' : ℕ} {δ₁ δ₂ : ℚ} (h : WinClose w a b J' δ₁) (h12 : δ₁ ≤ δ₂) :
    WinClose w a b J' δ₂ :=
  ⟨h.1, h.2.1, h.2.2.trans (by linarith)⟩

/-- If the empirical distribution is within `2δ` of `p` (in the sum of absolute differences), the weighted sum with weights `0 ≤ h ≤ B` is at most `N (∑ p h + 2 δ B)`
(the real version of `RateUpperBase.freq_sum_le`). -/
theorem freq_sum_le_real (s : Finset Word) (c h : Word → ℝ) (N p δ B : ℝ) (hN : 0 < N) (hBn : 0 ≤ B)
    (h0 : ∀ v ∈ s, 0 ≤ h v) (hB : ∀ v ∈ s, h v ≤ B) (hTV : ∑ v ∈ s, |c v / N - p| ≤ 2 * δ) :
    ∑ v ∈ s, c v * h v ≤ N * (∑ v ∈ s, p * h v + 2 * δ * B) := by
  have hB0 : ∀ v ∈ s, (c v / N - p) * h v ≤ |c v / N - p| * B := fun v hv =>
    (mul_le_mul_of_nonneg_right (le_abs_self _) (h0 v hv)).trans
      (mul_le_mul_of_nonneg_left (hB v hv) (abs_nonneg _))
  have e : ∑ v ∈ s, c v * h v = N * (∑ v ∈ s, p * h v + ∑ v ∈ s, (c v / N - p) * h v) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    field_simp
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hN.le
  have h1 := Finset.sum_le_sum hB0
  rw [← Finset.sum_mul] at h1
  have h2 : (∑ v ∈ s, |c v / N - p|) * B ≤ 2 * δ * B := mul_le_mul_of_nonneg_right hTV hBn
  linarith

/-! ## The bound for one offset -/

section Offset

variable {S : Type*} {δ : S → Bool → S} (J : ℕ) {φ : S → List Bool → ℝ}

theorem abs_wsum_sub_le {C Q : ℝ} (hC : ∀ x v, |φ x v| ≤ C) (hQ : |Q| ≤ C) (x : S) (w : List Bool)
    (L : ℕ) : |wsum δ J φ x w L - Q * L| ≤ 2 * C * L := by
  have h1 := abs_le.mp (abs_wsum_le (δ := δ) (J := J) hC x w L)
  have h2 : |Q * L| ≤ C * L := by
    rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg L)
  have h3 := abs_le.mp h2
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith

/-- **The bound for one cut**: cutting `k = s + nM + t` (`s < M`, `t < M + J`), the difference between the prefix sum and `Q k` is bounded by
`2C(2M + J)` for the two ends plus the sum of `D` over the windows of the blocks. -/
theorem split_bound {q₀ : S} {C Q : ℝ} (hC : ∀ x v, |φ x v| ≤ C) (hQ : |Q| ≤ C) {M : ℕ}
    (D : List Bool → ℝ) (hD : ∀ z, Reach δ q₀ z → ∀ v, |wsum δ J φ z v M - Q * M| ≤ D v)
    (ω : List Bool) {x : S} (hx : Reach δ q₀ x) {k s n : ℕ} (hs : s < M) (h1 : s + n * M ≤ k)
    (h2 : k < s + n * M + M + J) :
    |wsum δ J φ x ω k - Q * k| ≤
      2 * C * (2 * M + J) + ∑ j ∈ Finset.range n, D ((ω.drop (s + j * M)).take (M + J)) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hQ
  obtain ⟨t, rfl⟩ : ∃ t, k = s + n * M + t := ⟨k - (s + n * M), by omega⟩
  set y := run δ x (ω.take s) with hy
  have hyR : Reach δ q₀ y := hx.trans (reach_run x _)
  have e1 : wsum δ J φ x ω (s + n * M + t) = wsum δ J φ x ω s +
      ∑ j ∈ Finset.range n, wsum δ J φ (run δ y ((ω.drop s).take (j * M))) (ω.drop (s + j * M)) M +
        wsum δ J φ (run δ x (ω.take (s + n * M))) (ω.drop (s + n * M)) t := by
    rw [wsum_add, wsum_add, wsum_blocks]
    simp only [List.drop_drop, hy]
  have e2 : Q * ((s + n * M + t : ℕ) : ℝ) =
      Q * s + ∑ _j ∈ Finset.range n, Q * M + Q * t := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  rw [e1, e2]
  have hb : ∀ j ∈ Finset.range n,
      |wsum δ J φ (run δ y ((ω.drop s).take (j * M))) (ω.drop (s + j * M)) M - Q * M| ≤
        D ((ω.drop (s + j * M)).take (M + J)) := by
    intro j _
    rw [← wsum_take (run δ y ((ω.drop s).take (j * M))) (ω.drop (s + j * M)) (le_refl (M + J))]
    exact hD _ (hyR.trans (reach_run y _)) _
  have hsum : |∑ j ∈ Finset.range n, wsum δ J φ (run δ y ((ω.drop s).take (j * M))) (ω.drop (s + j * M)) M -
      ∑ _j ∈ Finset.range n, Q * M| ≤ ∑ j ∈ Finset.range n, D ((ω.drop (s + j * M)).take (M + J)) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
  have ha := abs_wsum_sub_le (δ := δ) J hC hQ x ω s
  have hc := abs_wsum_sub_le (δ := δ) J hC hQ (run δ x (ω.take (s + n * M))) (ω.drop (s + n * M)) t
  have hsR : (s : ℝ) ≤ M := by exact_mod_cast hs.le
  have htR : (t : ℝ) ≤ M + J := by exact_mod_cast (show t ≤ M + J by omega)
  have ha' := abs_le.mp ha
  have hc' := abs_le.mp hc
  have hsum' := abs_le.mp hsum
  have hs2 : 2 * C * s ≤ 2 * C * M := mul_le_mul_of_nonneg_left hsR (by positivity)
  have ht2 : 2 * C * t ≤ 2 * C * (M + J) := mul_le_mul_of_nonneg_left htR (by positivity)
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith

end Offset

/-! ## The deterministic law of large numbers -/

section Core

variable {S : Type*} [Fintype S] [DecidableEq S] {δ : S → Bool → S} (J : ℕ) {φ : S → List Bool → ℝ}

/-- **The core bound** (with the interval starting at 0): if the bound of `stat_mean` for the block length `M` is `ε₀`, then on an interval `[0, b)` whose
window frequencies (window length `M + J`) are within `δ'` of uniform, for every starting state `x` of the class and every prefix `k ≤ b`,
`|wsum − statMean · k| ≤ 2C(2M + J) + b |S| (ε₀ + 4 δ' C)`. -/
theorem lln_core {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    {M : ℕ} (hM : 1 ≤ M) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    (hstat : ∀ z, Reach δ q₀ z →
      avg (M + J) (fun w => |wsum δ J φ z w M - statMean δ J φ q₀ * M|) ≤ ε₀ * M)
    {δ' : ℚ} (ω : List Bool) {b : ℕ} (hwin : WinClose (ω.map ofB) 0 b (M + J) δ')
    {x : S} (hx : Reach δ q₀ x) {k : ℕ} (hk : k ≤ b) :
    |wsum δ J φ x ω k - statMean δ J φ q₀ * k| ≤
      2 * C * (2 * M + J) + b * Fintype.card S * (ε₀ + 4 * δ' * C) := by
  classical
  set Q := statMean δ J φ q₀ with hQdef
  have hQ : |Q| ≤ C := abs_statMean_le J hrec hC
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hQ
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨hJb, hbl, hTV⟩ := hwin
  have hJb' : M + J ≤ b := by omega
  set Bs := Finset.univ.filter (fun z => Reach δ q₀ z) with hBs
  set D : List Bool → ℝ := fun v => ∑ z ∈ Bs, |wsum δ J φ z v M - Q * M| with hDdef
  have hD : ∀ z, Reach δ q₀ z → ∀ v, |wsum δ J φ z v M - Q * M| ≤ D v := by
    intro z hz v
    exact Finset.single_le_sum (f := fun z => |wsum δ J φ z v M - Q * M|)
      (fun _ _ => abs_nonneg _) (by simp [hBs, hz])
  have hD0 : ∀ v, 0 ≤ D v := fun v => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set N := b + 1 - (M + J) - 0 with hN
  have hNpos : 0 < N := by omega
  set bw : ℕ → List Bool := fun i => (ω.drop i).take (M + J) with hbw
  -- the bound for one offset `r`
  set Kp := min k (b - J) with hKp
  have hoff : ∀ r ∈ Finset.range M, |wsum δ J φ x ω k - Q * k| ≤
      2 * C * (2 * M + J) + ∑ i ∈ (Finset.range N).filter (fun i => i % M = r), D (bw i) := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    set s := min r Kp with hs
    set n := (Kp - s) / M with hn
    have hnM : n * M ≤ Kp - s := Nat.div_mul_le_self _ _
    have hmod : Kp - s < n * M + M := by
      have := Nat.div_add_mod (Kp - s) M
      have := Nat.mod_lt (Kp - s) (show 0 < M by omega)
      rw [hn]; nlinarith
    have hsp := split_bound (δ := δ) (q₀ := q₀) J hC hQ D hD ω hx (k := k) (s := s) (n := n)
      (by omega) (by omega) (by omega)
    refine hsp.trans ?_
    suffices hkey : ∑ j ∈ Finset.range n, D ((ω.drop (s + j * M)).take (M + J)) ≤
        ∑ i ∈ (Finset.range N).filter (fun i => i % M = r), D (bw i) by linarith
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, Finset.range_zero, Finset.sum_empty]
      exact Finset.sum_nonneg (fun i _ => hD0 _)
    · have hsr : s = r := by
        have : M ≤ Kp - s := by nlinarith
        omega
      rw [hsr]
      have hinj : Set.InjOn (fun j => r + j * M) (Finset.range n : Set ℕ) := by
        intro j _ j' _ hjj
        have := Nat.eq_of_mul_eq_mul_right (show 0 < M by omega) (Nat.add_left_cancel hjj)
        exact this
      rw [← Finset.sum_image (f := fun i => D (bw i)) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hD0 _)
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hj' := Finset.mem_range.mp hj
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr']⟩
      have : (j + 1) * M ≤ n * M := Nat.mul_le_mul_right M (by omega)
      rw [Nat.succ_mul] at this
      omega
  -- sum over the offsets
  have hsumr : (M : ℝ) * |wsum δ J φ x ω k - Q * k| ≤
      M * (2 * C * (2 * M + J)) + ∑ i ∈ Finset.range N, D (bw i) := by
    have h1 := Finset.sum_le_sum hoff
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul,
      Finset.sum_fiberwise_of_maps_to (g := fun i => i % M)
        (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i (by omega)))] at h1
    exact h1
  -- the sum over windows, by the window frequencies
  have hwinsum : ∑ i ∈ Finset.range N, D (bw i) =
      ∑ v ∈ wordsOfLen (M + J), (winCount (ω.map ofB) 0 b (M + J) v : ℝ) * D (v.map toB) := by
    rw [← sum_windows_eq (R := ℝ) (fun v => D (v.map toB)) (ω.map ofB) 0 b (M + J) (wordsOfLen (M + J))]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [zero_add, window_map_ofB, map_toB_map_ofB]
    · intro i hi
      refine window_mem_wordsOfLen (map_ofB_bin ω) ?_
      omega
  have hBmax : ∀ v, D v ≤ Fintype.card S * (2 * C * M) := by
    intro v
    calc D v ≤ ∑ _z ∈ Bs, 2 * C * M := Finset.sum_le_sum (fun z _ => abs_wsum_sub_le (δ := δ) J hC hQ z v M)
      _ = Bs.card * (2 * C * M) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card S * (2 * C * M) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ Bs) (by positivity)
  have hTV' : ∑ v ∈ wordsOfLen (M + J),
      |(winCount (ω.map ofB) 0 b (M + J) v : ℝ) / (N : ℝ) - 1 / 2 ^ (M + J)| ≤ 2 * (δ' : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hTV
    push_cast at this
    exact this
  have hfreq := freq_sum_le_real (wordsOfLen (M + J)) (fun v => (winCount (ω.map ofB) 0 b (M + J) v : ℝ))
    (fun v => D (v.map toB)) N (1 / 2 ^ (M + J)) δ' (Fintype.card S * (2 * C * M))
    (by exact_mod_cast hNpos) (by positivity) (fun v _ => hD0 _) (fun v _ => hBmax _) hTV'
  have hmean : ∑ v ∈ wordsOfLen (M + J), 1 / 2 ^ (M + J) * D (v.map toB) = avg (M + J) D := by
    rw [← Finset.mul_sum, sum_wordsOfLen_eq]
    field_simp
  have hED : avg (M + J) D ≤ Fintype.card S * (ε₀ * M) := by
    rw [hDdef, avg_sum]
    calc ∑ z ∈ Bs, avg (M + J) (fun w => |wsum δ J φ z w M - Q * M|) ≤ ∑ _z ∈ Bs, ε₀ * M :=
          Finset.sum_le_sum (fun z hz => hstat z (by simpa [hBs] using hz))
      _ = Bs.card * (ε₀ * M) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card S * (ε₀ * M) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ Bs) (by positivity)
  have hδ0 : (0 : ℝ) ≤ δ' := by
    have : (0 : ℝ) ≤ ∑ v ∈ wordsOfLen (M + J),
        |(winCount (ω.map ofB) 0 b (M + J) v : ℝ) / (N : ℝ) - 1 / 2 ^ (M + J)| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hNb : (N : ℝ) ≤ b := by exact_mod_cast (show N ≤ b by omega)
  have hS0 : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _
  -- conclusion
  have htot : (M : ℝ) * |wsum δ J φ x ω k - Q * k| ≤
      M * (2 * C * (2 * M + J) + b * Fintype.card S * (ε₀ + 4 * δ' * C)) := by
    have h1 : ∑ i ∈ Finset.range N, D (bw i) ≤ N * (Fintype.card S * (ε₀ * M) + 2 * δ' *
        (Fintype.card S * (2 * C * M))) := by
      rw [hwinsum]; rw [hmean] at hfreq
      refine hfreq.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N))
      linarith
    have h2 : (N : ℝ) * (Fintype.card S * (ε₀ * M) + 2 * δ' * (Fintype.card S * (2 * C * M))) ≤
        b * (Fintype.card S * (ε₀ * M) + 2 * δ' * (Fintype.card S * (2 * C * M))) :=
      mul_le_mul_of_nonneg_right hNb (by positivity)
    have e : (M : ℝ) * (2 * C * (2 * M + J) + b * Fintype.card S * (ε₀ + 4 * δ' * C)) =
        M * (2 * C * (2 * M + J)) +
          b * (Fintype.card S * (ε₀ * M) + 2 * δ' * (Fintype.card S * (2 * C * M))) := by ring
    rw [e]
    linarith
  exact le_of_mul_le_mul_left htot hMpos

/-- **`lln_of_winClose` (the deterministic law of large numbers, Theorem 12.13 (iii))**: if `q₀` is recurrent and `|φ| ≤ C`,
then for every `ε > 0` there are `J₀` and `δ' > 0` such that for every window length `J' ≥ J₀` there is `N₀` with the following property:
if the windows of length `J'` on an interval `[a, b)` (`b - a ≥ N₀`) of a word `ω` have frequencies within `δ'` of uniform, then, reading from any state `x` of
the class starting at the position `a`, for all `k ∈ [a, b]`
`|wsum δ J φ x (ω.drop a) (k - a) − statMean δ J φ q₀ · (k - a)| ≤ ε (b - a)`.
`J₀` and `δ'` depend only on `ε`, the automaton and `φ`, and `N₀` in addition only on `J'` (not on the interval, the word or the starting state). -/
theorem lln_of_winClose {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∃ δ' : ℚ, 0 < δ' ∧ ∀ J', J₀ ≤ J' → ∃ N₀ : ℕ, ∀ (ω : List Bool) (a b : ℕ),
      WinClose (ω.map ofB) a b J' δ' → N₀ ≤ b - a → ∀ x, Reach δ q₀ x → ∀ k, a ≤ k → k ≤ b →
        |wsum δ J φ x (ω.drop a) (k - a) - statMean δ J φ q₀ * ((k - a : ℕ) : ℝ)| ≤
          ε * ((b - a : ℕ) : ℝ) := by
  have hC0 : 0 ≤ C := nonneg_of_bound (q₀ := q₀) hC
  set s : ℝ := (Fintype.card S : ℝ) with hsdef
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  set ε₀ : ℝ := ε / (3 * (s + 1)) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  obtain ⟨L₀, hL₀⟩ := stat_mean J hrec hC ε₀ hε₀pos
  obtain ⟨δ', hδ'0, hδ'⟩ := exists_pos_rat_lt (show (0 : ℝ) < ε / (12 * (C + 1) * (s + 1)) by positivity)
  refine ⟨max L₀ 1 + J, δ', hδ'0, fun J' hJ' => ?_⟩
  set M := J' - J with hM
  have hM1 : 1 ≤ M := by omega
  have hML₀ : L₀ ≤ M := by omega
  refine ⟨⌈6 * C * (2 * (M : ℝ) + J) / ε⌉₊, fun ω a b hwin hN₀ x hx k hak hkb => ?_⟩
  have hw0 := winClose_drop hwin
  rw [← List.map_drop, show J' = M + J by omega] at hw0
  have hcore := lln_core J hrec hC hM1 hε₀pos.le (fun z hz => hL₀ M hML₀ z hz) (ω.drop a) hw0 hx
    (k := k - a) (by omega)
  refine hcore.trans ?_
  set ba : ℝ := ((b - a : ℕ) : ℝ) with hba
  have hba0 : 0 ≤ ba := Nat.cast_nonneg _
  have h1 : 2 * C * (2 * M + J) ≤ ε * ba / 3 := by
    have := Nat.le_ceil (6 * C * (2 * (M : ℝ) + J) / ε)
    have h2 : (⌈6 * C * (2 * (M : ℝ) + J) / ε⌉₊ : ℝ) ≤ ba := by rw [hba]; exact_mod_cast hN₀
    rw [div_le_iff₀ hε] at this
    nlinarith
  have h2 : ba * s * ε₀ ≤ ε * ba / 3 := by
    have e : ba * s * ε₀ = ε * ba / 3 * (s / (s + 1)) := by rw [hε₀]; field_simp
    rw [e]
    have : s / (s + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hpos : 0 ≤ ε * ba / 3 := by positivity
    nlinarith
  have h3 : ba * s * (4 * δ' * C) ≤ ε * ba / 3 := by
    have hδC : (δ' : ℝ) * C ≤ ε / (12 * (s + 1)) := by
      have hlt := hδ'.le
      have e : ε / (12 * (C + 1) * (s + 1)) * C ≤ ε / (12 * (s + 1)) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : ε * C * (12 * (s + 1)) ≤ ε * (12 * (s + 1)) * (C + 1) := by nlinarith [hε.le]
        nlinarith
      calc (δ' : ℝ) * C ≤ ε / (12 * (C + 1) * (s + 1)) * C := mul_le_mul_of_nonneg_right hlt hC0
        _ ≤ _ := e
    have e2 : ba * s * (4 * δ' * C) = 4 * ba * s * (δ' * C) := by ring
    rw [e2]
    have h4 : 4 * ba * s * (δ' * C) ≤ 4 * ba * s * (ε / (12 * (s + 1))) :=
      mul_le_mul_of_nonneg_left hδC (by positivity)
    have e3 : 4 * ba * s * (ε / (12 * (s + 1))) = ε * ba / 3 * (s / (s + 1)) := by field_simp; ring
    have : s / (s + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hpos : 0 ≤ ε * ba / 3 := by positivity
    nlinarith
  have e : ((b - a : ℕ) : ℝ) * (s * (ε₀ + 4 * δ' * C)) = ba * s * ε₀ + ba * s * (4 * δ' * C) := by
    rw [hba]; ring
  calc 2 * C * (2 * M + J) + ((b - a : ℕ) : ℝ) * Fintype.card S * (ε₀ + 4 * δ' * C)
      = 2 * C * (2 * M + J) + (ba * s * ε₀ + ba * s * (4 * δ' * C)) := by rw [← e, hsdef]; ring
    _ ≤ ε * ba := by linarith

open Classical in
/-- **`lln_uniform` (Theorem 12.13 (iv))**: on an interval `[a, b)` of uniform digits (`b - a ≥ N₀`), for a proportion at least `1 - η` of the words of
length `L`, the bound of `lln_of_winClose` holds for every starting state of the class and every prefix (uniformly in `L`, `a` and `b`).
The words are counted by `Window.wordsOfLen` (words in `f`, `t`), and the DFA reads them through `toB`. -/
theorem lln_uniform {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    (ε : ℝ) (hε : 0 < ε) (η : ℚ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ L a b : ℕ, a ≤ b → b ≤ L → N₀ ≤ b - a →
      (1 - η) * 2 ^ L ≤ (((wordsOfLen L).filter (fun w => ∀ x, Reach δ q₀ x → ∀ k, a ≤ k → k ≤ b →
        |wsum δ J φ x ((w.map toB).drop a) (k - a) - statMean δ J φ q₀ * ((k - a : ℕ) : ℝ)| ≤
          ε * ((b - a : ℕ) : ℝ))).card : ℚ) := by
  obtain ⟨J₀, δ', hδ', hJ⟩ := lln_of_winClose J hrec hC ε hε
  obtain ⟨N₁, hN₁⟩ := hJ J₀ le_rfl
  obtain ⟨M₀, hM₀⟩ := winClose_lln_interval J₀ δ' η hδ' hη
  refine ⟨max N₁ M₀, fun L a b hab hbL hN => ?_⟩
  refine (hM₀ L a b hab hbL (by omega)).trans ?_
  have hsub : (wordsOfLen L).filter (fun w => WinClose w a b J₀ δ') ⊆
      (wordsOfLen L).filter (fun w => ∀ x, Reach δ q₀ x → ∀ k, a ≤ k → k ≤ b →
        |wsum δ J φ x ((w.map toB).drop a) (k - a) - statMean δ J φ q₀ * ((k - a : ℕ) : ℝ)| ≤
          ε * ((b - a : ℕ) : ℝ)) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, fun x hx k hak hkb => ?_⟩
    have hbin := WinLLN.bin_of_mem hw.1
    have hw' : WinClose ((w.map toB).map ofB) a b J₀ δ' := by rw [map_ofB_map_toB hbin]; exact hw.2
    exact hN₁ (w.map toB) a b hw' (by omega) x hx k hak hkb
  exact_mod_cast Finset.card_le_card hsub

end Core

end Collatz.Arctic.NatQ5.W3d
