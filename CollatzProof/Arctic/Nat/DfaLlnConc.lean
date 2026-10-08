/-
# Natural-number interpretations of 𝒯 (Section 12.4), part (3): the mean form `stat_mean` of the law of large numbers for finite DFAs

`stat_mean` (Theorem 12.13 (ii)): uniformly over all starting states of the class, over the uniform words of length `L`,
`𝔼|wsum − statMean · L| ≤ ε L` (for `L` large). This is the mean form of the statement that a probability tends to `1`
(Markov's inequality turns it into the probability form; downstream uses it through the deterministic form for window frequencies, `lln_of_winClose` in `DfaLln.lean`).

Proof: split into blocks of length `M ≥ J`; the block sums minus their expectations, `blockDev` (their conditional mean given the state at the start of the
block is 0, `blockDev_orth`), add up to `gsum`, whose second moment is bounded by `12 n (MC)^2` (`gsum_sq_le`;
neighboring blocks are not orthogonal, since their windows overlap in `J` digits, but blocks at least two apart are). The expectation of a block and
`statMean · M` differ by at most `K` by `mexp_near`. Neither Kingman's theorem, nor pointwise ergodic theorems, nor stationary distributions are used.
-/
import CollatzProof.Arctic.Nat.DfaLlnMean

namespace Collatz.Arctic.NatQ5.W3d

open Collatz.Arctic Collatz.Arctic.Dfa Filter Topology

section Blocks

variable {S : Type*} (δ : S → Bool → S) (J : ℕ) (φ : S → List Bool → ℝ)

/-- The difference between the sum over block `j` (positions `[jM, (j+1)M)`) and its expectation seen from the state at the start of the block. -/
noncomputable def blockDev (x : S) (M j : ℕ) (w : List Bool) : ℝ :=
  wsum δ J φ (run δ x (w.take (j * M))) (w.drop (j * M)) M - mexp δ J φ (run δ x (w.take (j * M))) M

/-- The sum of `blockDev` over the first `n` blocks. -/
noncomputable def gsum (x : S) (M n : ℕ) (w : List Bool) : ℝ :=
  ∑ j ∈ Finset.range n, blockDev δ J φ x M j w

variable {δ J φ}

theorem abs_blockDev_le {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) (x : S) (M j : ℕ) (w : List Bool) :
    |blockDev δ J φ x M j w| ≤ 2 * (M * C) := by
  unfold blockDev
  have h1 := abs_le.mp (abs_wsum_le (δ := δ) (J := J) hC (run δ x (w.take (j * M))) (w.drop (j * M)) M)
  have h2 := abs_le.mp (abs_mexp_le (δ := δ) (J := J) hC (run δ x (w.take (j * M))) M)
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- Decomposition into block sums. -/
theorem wsum_blocks (x : S) (w : List Bool) (M n : ℕ) :
    wsum δ J φ x w (n * M) =
      ∑ j ∈ Finset.range n, wsum δ J φ (run δ x (w.take (j * M))) (w.drop (j * M)) M := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_mul, wsum_add, ih, Finset.sum_range_succ]

/-- The sum minus its stationary mean, split into `gsum`, the deviations of the block expectations, and the remainder. -/
theorem wsum_decomp (x : S) (w : List Bool) (M n r : ℕ) (Q : ℝ) :
    wsum δ J φ x w (n * M + r) - Q * ((n * M + r : ℕ) : ℝ) =
      gsum δ J φ x M n w +
        ∑ j ∈ Finset.range n, (mexp δ J φ (run δ x (w.take (j * M))) M - Q * M) +
        (wsum δ J φ (run δ x (w.take (n * M))) (w.drop (n * M)) r - Q * r) := by
  rw [wsum_add, wsum_blocks]
  simp only [gsum, blockDev, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- `blockDev x M j` depends only on the first `k` letters if `(j+1)M + J ≤ k`. -/
theorem blockDev_take (x : S) {M j k : ℕ} (hk : (j + 1) * M + J ≤ k) (w : List Bool) :
    blockDev δ J φ x M j (w.take k) = blockDev δ J φ x M j w := by
  have hjk : j * M ≤ k := by nlinarith
  unfold blockDev
  have e1 : (w.take k).take (j * M) = w.take (j * M) := by
    rw [List.take_take, Nat.min_eq_left hjk]
  have e2 : (w.take k).drop (j * M) = (w.drop (j * M)).take (k - j * M) := List.drop_take
  rw [e1, e2, wsum_take _ _ (by rw [Nat.succ_mul] at hk; omega)]

theorem gsum_take (x : S) {M n k : ℕ} (hk : n * M + J ≤ k) (w : List Bool) :
    gsum δ J φ x M n (w.take k) = gsum δ J φ x M n w := by
  unfold gsum
  refine Finset.sum_congr rfl (fun j hj => blockDev_take x ?_ w)
  have := Finset.mem_range.mp hj
  have : (j + 1) * M ≤ n * M := Nat.mul_le_mul_right M (by omega)
  omega

/-- **Orthogonality of blocks**: if `(j+1)M ≤ L`, the average of the product of `blockDev x M j` and a function `H` of the first `jM` letters is 0
(the conditional mean given the state at the start of the block is 0). -/
theorem blockDev_orth (x : S) {M j L : ℕ} (hjL : (j + 1) * M ≤ L) (H : List Bool → ℝ) :
    avg (L + J) (fun w => H (w.take (j * M)) * blockDev δ J φ x M j w) = 0 := by
  have hj : j * M ≤ L := by nlinarith
  rw [show L + J = j * M + (L + J - j * M) by omega, avg_append]
  have : ∀ u : List Bool, u.length = j * M →
      avg (L + J - j * M) (fun v => H ((u ++ v).take (j * M)) * blockDev δ J φ x M j (u ++ v)) = 0 := by
    intro u hu
    have e : ∀ v : List Bool, H ((u ++ v).take (j * M)) * blockDev δ J φ x M j (u ++ v) =
        H u * (wsum δ J φ (run δ x u) v M - mexp δ J φ (run δ x u) M) := by
      intro v
      unfold blockDev
      rw [List.take_left' hu, List.drop_left' hu]
    simp_rw [e]
    rw [avg_mul_left, avg_sub, avg_const, avg_wsum (run δ x u) (by rw [Nat.succ_mul] at hjL; omega),
      sub_self, mul_zero]
  rw [avg_congr this, avg_const]

/-- **Second moment**: if `M ≥ J` and `nM ≤ L`, then `𝔼[gsum²] ≤ 12 n (MC)²`. -/
theorem gsum_sq_le {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) (x : S) {M L : ℕ} (hMJ : J ≤ M) :
    ∀ n, n * M ≤ L → avg (L + J) (fun w => (gsum δ J φ x M n w) ^ 2) ≤ 12 * n * (M * C) ^ 2 := by
  have hb : ∀ j w, |blockDev δ J φ x M j w| ≤ 2 * (M * C) := fun j w => abs_blockDev_le hC x M j w
  have hprod : ∀ i j w, blockDev δ J φ x M i w * blockDev δ J φ x M j w ≤ 4 * (M * C) ^ 2 := by
    intro i j w
    have := abs_mul (blockDev δ J φ x M i w) (blockDev δ J φ x M j w)
    have h2 : |blockDev δ J φ x M i w| * |blockDev δ J φ x M j w| ≤ (2 * (M * C)) * (2 * (M * C)) :=
      mul_le_mul (hb i w) (hb j w) (abs_nonneg _) (le_trans (abs_nonneg _) (hb i w))
    have h3 := le_abs_self (blockDev δ J φ x M i w * blockDev δ J φ x M j w)
    nlinarith
  -- cross terms: `𝔼[gsum n · blockDev n] ≤ 4 (MC)²`
  have hcross : ∀ n, (n + 1) * M ≤ L →
      avg (L + J) (fun w => gsum δ J φ x M n w * blockDev δ J φ x M n w) ≤ 4 * (M * C) ^ 2 := by
    intro n hn
    rcases n with _ | m
    · simp only [gsum, Finset.range_zero, Finset.sum_empty, zero_mul, avg_const]
      positivity
    · have e : ∀ w, gsum δ J φ x M (m + 1) w * blockDev δ J φ x M (m + 1) w =
          gsum δ J φ x M m (w.take ((m + 1) * M)) * blockDev δ J φ x M (m + 1) w +
            blockDev δ J φ x M m w * blockDev δ J φ x M (m + 1) w := by
        intro w
        rw [gsum_take x (by rw [Nat.succ_mul]; omega) w]
        unfold gsum
        rw [Finset.sum_range_succ]
        ring
      simp_rw [e]
      rw [avg_add, blockDev_orth x hn (fun u => gsum δ J φ x M m u), zero_add]
      have := avg_mono (n := L + J) (G := fun w => blockDev δ J φ x M m w * blockDev δ J φ x M (m + 1) w)
        (H := fun _ => 4 * (M * C) ^ 2) (fun w _ => hprod m (m + 1) w)
      rwa [avg_const] at this
  intro n
  induction n with
  | zero =>
    intro _
    simp only [gsum, Finset.range_zero, Finset.sum_empty]
    rw [show (fun _ : List Bool => (0 : ℝ) ^ 2) = fun _ => 0 by funext; ring, avg_const]
    simp
  | succ n ih =>
    intro hn
    have e : ∀ w, (gsum δ J φ x M (n + 1) w) ^ 2 = (gsum δ J φ x M n w) ^ 2 +
        2 * (gsum δ J φ x M n w * blockDev δ J φ x M n w) +
          blockDev δ J φ x M n w * blockDev δ J φ x M n w := by
      intro w
      unfold gsum
      rw [Finset.sum_range_succ]
      ring
    simp_rw [e]
    rw [avg_add, avg_add, avg_mul_left]
    have h1 := ih (by nlinarith)
    have h2 := hcross n hn
    have h3 : avg (L + J) (fun w => blockDev δ J φ x M n w * blockDev δ J φ x M n w) ≤ 4 * (M * C) ^ 2 := by
      have := avg_mono (n := L + J) (G := fun w => blockDev δ J φ x M n w * blockDev δ J φ x M n w)
        (H := fun _ => 4 * (M * C) ^ 2) (fun w _ => hprod n n w)
      rwa [avg_const] at this
    push_cast
    nlinarith

end Blocks

/-! ## The mean form of the law of large numbers -/

section StatMean

variable {S : Type*} [Fintype S] [DecidableEq S] {δ : S → Bool → S} (J : ℕ) {φ : S → List Bool → ℝ}

/-- If `t > 0`, then `|g| ≤ t + g²/t`. -/
theorem abs_le_add_sq_div {g t : ℝ} (ht : 0 < t) : |g| ≤ t + g ^ 2 / t := by
  have h1 : |g| * t ≤ t ^ 2 + g ^ 2 := by
    have h := sq_nonneg (|g| - t)
    rw [← sq_abs g]
    nlinarith [abs_nonneg g]
  have e : t + g ^ 2 / t = (t ^ 2 + g ^ 2) / t := by field_simp
  rw [e, le_div_iff₀ ht]
  exact h1

/-- **`stat_mean` (the mean form of the law of large numbers for finite DFAs)**: if `q₀` is recurrent and `|φ| ≤ C`, then for every `ε > 0` there is
`L₀` such that, for `L ≥ L₀` and all starting states `x` of the class,
`𝔼_{w : length L + J}|wsum δ J φ x w L − statMean δ J φ q₀ · L| ≤ ε L`. -/
theorem stat_mean {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) :
    ∀ ε > 0, ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ x, Reach δ q₀ x →
      avg (L + J) (fun w => |wsum δ J φ x w L - statMean δ J φ q₀ * L|) ≤ ε * L := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := mexp_near J hrec hC
  have hC0 : 0 ≤ C := nonneg_of_bound (q₀ := q₀) hC
  have hQ := abs_le.mp (abs_statMean_le J hrec hC)
  set Q := statMean δ J φ q₀ with hQdef
  set M : ℕ := J + 1 + ⌈4 * K / ε⌉₊ with hMdef
  have hMJ : J ≤ M := by omega
  have hM1 : 1 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hKM : K ≤ ε * M / 4 := by
    have h1 : 4 * K / ε ≤ (M : ℝ) := by
      have := Nat.le_ceil (4 * K / ε)
      have h2 : (⌈4 * K / ε⌉₊ : ℝ) ≤ M := by exact_mod_cast (show ⌈4 * K / ε⌉₊ ≤ M by omega)
      linarith
    rw [div_le_iff₀ hε] at h1
    linarith
  set B : ℝ := (96 * M * C ^ 2 / ε + 4 * M * C) / ε with hBdef
  refine ⟨⌈B⌉₊ + 1, fun L hL x hx => ?_⟩
  have hL1 : 1 ≤ L := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hLB : B ≤ L := by
    have := Nat.le_ceil B
    have h2 : ((⌈B⌉₊ : ℕ) : ℝ) ≤ L := by exact_mod_cast (show ⌈B⌉₊ ≤ L by omega)
    linarith
  set n := L / M with hn
  set r := L % M with hr
  have hLnr : n * M + r = L := Nat.div_add_mod' L M
  have hnM : n * M ≤ L := by omega
  have hrM : r < M := Nat.mod_lt L (by omega)
  have hnMR : (n : ℝ) * M ≤ L := by exact_mod_cast hnM
  -- pointwise bound
  have hpt : ∀ w : List Bool, w.length = L + J →
      |wsum δ J φ x w L - Q * L| ≤ |gsum δ J φ x M n w| + n * K + 2 * (M * C) := by
    intro w _
    have e := wsum_decomp (δ := δ) (J := J) (φ := φ) x w M n r Q
    rw [hLnr] at e
    rw [e]
    have hs : |∑ j ∈ Finset.range n, (mexp δ J φ (run δ x (w.take (j * M))) M - Q * M)| ≤ n * K := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range n) =>
        hK M (run δ x (w.take (j * M))) (hx.trans (reach_run x _)))
      simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
    have ht : |wsum δ J φ (run δ x (w.take (n * M))) (w.drop (n * M)) r - Q * r| ≤ 2 * (M * C) := by
      have h1 := abs_le.mp (abs_wsum_le (δ := δ) (J := J) hC (run δ x (w.take (n * M))) (w.drop (n * M)) r)
      have hrR : (r : ℝ) ≤ M := by exact_mod_cast hrM.le
      have h3 : |Q * r| ≤ C * r := by
        rw [abs_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_right (abs_le.mpr hQ) (Nat.cast_nonneg r)
      have h4 := abs_le.mp h3
      have h5 : (r : ℝ) * C ≤ M * C := mul_le_mul_of_nonneg_right hrR hC0
      refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith
    calc |gsum δ J φ x M n w + ∑ j ∈ Finset.range n, (mexp δ J φ (run δ x (w.take (j * M))) M - Q * M) +
          (wsum δ J φ (run δ x (w.take (n * M))) (w.drop (n * M)) r - Q * r)|
        ≤ |gsum δ J φ x M n w + ∑ j ∈ Finset.range n, (mexp δ J φ (run δ x (w.take (j * M))) M - Q * M)| +
          |wsum δ J φ (run δ x (w.take (n * M))) (w.drop (n * M)) r - Q * r| := abs_add_le _ _
      _ ≤ |gsum δ J φ x M n w| + |∑ j ∈ Finset.range n, (mexp δ J φ (run δ x (w.take (j * M))) M - Q * M)| +
          |wsum δ J φ (run δ x (w.take (n * M))) (w.drop (n * M)) r - Q * r| := by
          gcongr; exact abs_add_le _ _
      _ ≤ |gsum δ J φ x M n w| + n * K + 2 * (M * C) := by linarith
  -- `|gsum| ≤ t + gsum²/t`, `t = εL/4`
  set t : ℝ := ε * L / 4 with htdef
  have htpos : 0 < t := by positivity
  have hmain : avg (L + J) (fun w => |wsum δ J φ x w L - Q * L|) ≤
      t + avg (L + J) (fun w => (gsum δ J φ x M n w) ^ 2) / t + n * K + 2 * (M * C) := by
    have := avg_mono (n := L + J) (G := fun w => |wsum δ J φ x w L - Q * L|)
      (H := fun w => t + (gsum δ J φ x M n w) ^ 2 / t + n * K + 2 * (M * C))
      (fun w hw => (hpt w hw).trans (by linarith [abs_le_add_sq_div (g := gsum δ J φ x M n w) htpos]))
    refine this.trans (le_of_eq ?_)
    rw [avg_add, avg_add, avg_add, avg_const, avg_const, avg_const, avg_div]
  have hvar := gsum_sq_le (δ := δ) (J := J) (φ := φ) hC x (L := L) hMJ n hnM
  -- `12 n (MC)² / t ≤ 48 M C² / ε`
  have hv2 : avg (L + J) (fun w => (gsum δ J φ x M n w) ^ 2) / t ≤ 48 * M * C ^ 2 / ε := by
    rw [div_le_div_iff₀ htpos hε]
    have h1 : 12 * (n : ℝ) * (M * C) ^ 2 ≤ 12 * L * M * C ^ 2 := by
      have : (12 : ℝ) * n * (M * C) ^ 2 = 12 * (n * M) * M * C ^ 2 := by ring
      rw [this]
      have hMC : (0 : ℝ) ≤ M * C ^ 2 := by positivity
      nlinarith
    calc avg (L + J) (fun w => (gsum δ J φ x M n w) ^ 2) * ε ≤ 12 * L * M * C ^ 2 * ε :=
          mul_le_mul_of_nonneg_right (hvar.trans h1) hε.le
      _ = 48 * M * C ^ 2 * t := by rw [htdef]; ring
  have hnK : (n : ℝ) * K ≤ ε * L / 4 := by
    calc (n : ℝ) * K ≤ n * (ε * M / 4) := mul_le_mul_of_nonneg_left hKM (Nat.cast_nonneg n)
      _ = ε * (n * M) / 4 := by ring
      _ ≤ ε * L / 4 := by gcongr
  have hBL : 48 * M * C ^ 2 / ε + 2 * (M * C) ≤ ε * L / 2 := by
    have := mul_le_mul_of_nonneg_left hLB hε.le
    rw [hBdef, mul_div_cancel₀ _ hε.ne'] at this
    have e : 96 * (M : ℝ) * C ^ 2 / ε = 2 * (48 * M * C ^ 2 / ε) := by ring
    linarith
  linarith

end StatMean

end Collatz.Arctic.NatQ5.W3d
