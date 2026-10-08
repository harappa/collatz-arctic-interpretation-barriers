/-
The block bound for each component, from the proof of Lemma 6.5 (step "Block bound"):
on a non-exceptional interval, the weight in a component `C'` where the path stays long is at most `(Λ_{C'} + ε)(length of the interval) + constant`.
The ingredients (subadditivity, windows, averaging over shifts, counting) are in `RateUpperBase.lean`.

* The rate `rate` (`RateDefs.lean`) is nonnegative (`rate_nonneg`), and for `ε > 0` there is `K ≥ 1` with `avgMax K / K ≤ rate + ε`
  (`exists_len_near_rate`, from the definition of the infimum).
* `block_upper_of` (deterministic form with explicit constants): if the finite entries are at most `M` and the windows of length
  `K` on an interval `[a, b)` of a word in `f` and `t` only are `δ`-close to uniform, then `fmax(interval) ≤ (avgMax K / K + 2δM)(b - a) + 2MK`.
  Proof: `block_sum_le` (subadditivity and averaging over shifts) gives `K · fmax(interval) ≤ Σ_window fmax(window) + 2MK²`; the sum over windows is recounted
  by the number of occurrences of each word (`sum_windows_eq`); since the empirical distribution of the windows is within total variation distance `δ` of uniform and `0 ≤ fmax(window) ≤ MK`,
  `Σ_window fmax(window) ≤ N(avgMax K + 2δMK)` (`N` is the number of windows, at most `b - a`).
* `block_upper` (the main statement): with `J := K` (`avgMax K / K ≤ rate + ε/2`), `δ < ε/(4(M+1))` and `Cst := 2MK`,
  `fmax(interval) ≤ (rate + ε)(b - a) + Cst`. `J`, `δ` and `Cst` depend only on `A, C, M, ε`.
* `fmax` reads `-∞` as 0 instead of cutting at a negative constant
  (see the remark at the beginning of `RateDefs.lean`).
-/
import CollatzProof.Arctic.RateUpperBase

namespace Collatz.Arctic

/-! ### Rates -/

lemma avgMax_nonneg {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (L : ℕ) : 0 ≤ avgMax A C L := by
  unfold avgMax; positivity

/-- The average is the sum of `fmax` divided by `2^L` (uniform weights on words). -/
lemma avgMax_eq_sum {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (L : ℕ) :
    avgMax A C L = ∑ v ∈ wordsOfLen L, 1 / 2 ^ L * (fmax A C v : ℚ) := by
  unfold avgMax
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun v _ => by ring)

lemma rate_bddBelow {D : ℕ} (A : Interp D) (C : Finset (Fin D)) :
    BddBelow (Set.range fun L : ℕ => ((avgMax A C (L + 1) : ℚ) : ℝ) / ((L + 1 : ℕ) : ℝ)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨L, rfl⟩
  have := avgMax_nonneg A C (L + 1)
  positivity

/-- The rate is nonnegative (bounded below). -/
theorem rate_nonneg {D : ℕ} (A : Interp D) (C : Finset (Fin D)) : 0 ≤ rate A C := by
  refine le_ciInf (fun L => ?_)
  have := avgMax_nonneg A C (L + 1)
  positivity

lemma rate_le {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (L : ℕ) :
    rate A C ≤ ((avgMax A C (L + 1) : ℚ) : ℝ) / ((L + 1 : ℕ) : ℝ) :=
  ciInf_le (rate_bddBelow A C) L

/-- **Word length for the upper bound on the rate**: for `ε > 0` there is `K ≥ 1` with `avgMax K / K ≤ rate + ε` (`rate` is an infimum). -/
theorem exists_len_near_rate {D : ℕ} (A : Interp D) (C : Finset (Fin D)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 1 ≤ K ∧ ((avgMax A C K : ℚ) : ℝ) / (K : ℝ) ≤ rate A C + ε := by
  obtain ⟨L, hL⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (rate A C) hε)
  exact ⟨L + 1, Nat.succ_pos L, hL.le⟩

/-! ### Block bound -/

/-- **Block bound (deterministic form with explicit constants)**: if the finite entries of the digit matrices are at most `M` and the windows
of length `K ≥ 1` on the interval `[a, b)` of a word `w` in `f` and `t` only are `δ`-close to uniform, then the largest entry of the product restricted to `C` over the interval
is at most `(avgMax K / K + 2δM)(b - a) + 2MK`. -/
theorem block_upper_of {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (M : ℕ)
    (hM : ∀ s i j v, A s i j = Arc.fin v → v ≤ M) {K : ℕ} (hK1 : 1 ≤ K) {δ : ℚ} {w : Word} {a b : ℕ}
    (hw : ∀ s ∈ w, s = Letter.f ∨ s = Letter.t) (hc : WinClose w a b K δ) :
    ((fmax A C (window w a (b - a)) : ℕ) : ℝ) ≤
      (((avgMax A C K : ℚ) : ℝ) / K + 2 * (δ : ℝ) * M) * ((b - a : ℕ) : ℝ) + 2 * (M : ℝ) * K := by
  obtain ⟨hab, hbw, hTV⟩ := hc
  set n := b - a with hn
  set N := b + 1 - K - a with hNdef
  have hKn : K ≤ n := by omega
  have hNn : N = n + 1 - K := by omega
  have hN1 : 1 ≤ N := by omega
  have hNle : N ≤ n := by omega
  have hδ0 : (0 : ℚ) ≤ δ := by
    have : (0 : ℚ) ≤ ∑ v ∈ wordsOfLen K,
        |((winCount w a b K v : ℚ) / ((b + 1 - K - a : ℕ) : ℚ)) - 1 / 2 ^ K| :=
      Finset.sum_nonneg (fun v _ => abs_nonneg _)
    linarith
  -- subadditivity and averaging over shifts
  have hblock := block_sum_le A C M hM w a n K hKn
  rw [← hNn] at hblock
  -- recount the windows by word (all windows lie in `wordsOfLen K`)
  have hmem : ∀ i < N, window w (a + i) K ∈ wordsOfLen K := fun i hi =>
    window_mem_wordsOfLen hw (by omega)
  have hreg := sum_windows_eq (R := ℚ) (fun v => (fmax A C v : ℚ)) w a b K (wordsOfLen K) hmem
  -- window frequencies (`0 ≤ fmax ≤ MK`)
  have hfreq := freq_sum_le (wordsOfLen K) (fun v => (winCount w a b K v : ℚ))
    (fun v => (fmax A C v : ℚ)) (N : ℚ) (1 / 2 ^ K) δ ((M : ℚ) * K) (by exact_mod_cast hN1)
    (by positivity) (fun v _ => by positivity)
    (fun v hv => by
      have := fmax_le_length A C M hM v
      rw [length_of_mem_wordsOfLen hv] at this
      exact_mod_cast this)
    hTV
  rw [← avgMax_eq_sum] at hfreq
  -- combine (over the rationals)
  have H1q : (K : ℚ) * (fmax A C (window w a n) : ℚ) ≤
      (N : ℚ) * (avgMax A C K + 2 * δ * ((M : ℚ) * K)) + 2 * ((M : ℚ) * K * K) := by
    have h1 : ((K * fmax A C (window w a n) : ℕ) : ℚ) ≤
        ((∑ i ∈ Finset.range N, fmax A C (window w (a + i) K) + 2 * (M * K * K) : ℕ) : ℚ) := by
      exact_mod_cast hblock
    push_cast at h1
    rw [hreg] at h1
    linarith
  -- to the reals
  have H1 : (K : ℝ) * (fmax A C (window w a n) : ℝ) ≤
      (N : ℝ) * ((avgMax A C K : ℚ) : ℝ) + 2 * (δ : ℝ) * M * N * K + 2 * ((M : ℝ) * K * K) := by
    have := (Rat.cast_le (K := ℝ)).mpr H1q
    push_cast at this
    linarith
  -- divide by `K`
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  set avg : ℝ := ((avgMax A C K : ℚ) : ℝ) with havg
  set x : ℝ := avg / K with hx
  have hx0 : 0 ≤ x := by
    have : (0 : ℝ) ≤ avg := by rw [havg]; exact_mod_cast avgMax_nonneg A C K
    positivity
  have hF : (fmax A C (window w a n) : ℝ) ≤ N * x + 2 * (δ : ℝ) * M * N + 2 * (M : ℝ) * K := by
    have e : (N : ℝ) * avg = K * (N * x) := by rw [hx]; field_simp
    refine le_of_mul_le_mul_left ?_ hKpos
    nlinarith
  -- `N ≤ n`
  have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNle
  have hc0 : 0 ≤ x + 2 * (δ : ℝ) * M := by
    have : (0 : ℝ) ≤ δ := by exact_mod_cast hδ0
    positivity
  have h1 : (x + 2 * (δ : ℝ) * M) * N ≤ (x + 2 * (δ : ℝ) * M) * n :=
    mul_le_mul_of_nonneg_left hNn' hc0
  linarith

/-- **Block bound** (the step "Block bound" of the proof of Lemma 6.5): if the finite entries of the digit matrices are at most `M`, then
for `ε > 0` there are `J`, `δ`, `Cst` (depending only on `A, C, M, ε`) such that, whenever the windows of length `J` on the interval `[a, b)` of a word `w` in `f` and `t` only
are `δ`-close to uniform, the largest entry of the product restricted to `C` over the interval is at most
`(rate + ε)(b - a) + Cst`. `J := K` (`avgMax K / K ≤ rate + ε/2`), `δ < ε/(4(M+1))`, `Cst := 2MK`. -/
theorem block_upper {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (M : ℕ)
    (hM : ∀ s i j v, A s i j = Arc.fin v → v ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ δ : ℚ, 0 < J ∧ 0 < δ ∧ ∃ Cst : ℝ, ∀ (w : Word) (a b : ℕ),
      (∀ s ∈ w, s = Letter.f ∨ s = Letter.t) → WinClose w a b J δ →
      ((fmax A C (window w a (b - a)) : ℕ) : ℝ) ≤ (rate A C + ε) * ((b - a : ℕ) : ℝ) + Cst := by
  obtain ⟨K, hK1, hKr⟩ := exists_len_near_rate A C (half_pos hε)
  have hpos : (0 : ℝ) < ε / (4 * ((M : ℝ) + 1)) := by positivity
  obtain ⟨δ, hδ0, hδε⟩ := exists_rat_btwn hpos
  have hδ0' : (0 : ℚ) < δ := by exact_mod_cast hδ0
  refine ⟨K, δ, hK1, hδ0', 2 * (M : ℝ) * K, fun w a b hw hc => ?_⟩
  have h := block_upper_of A C M hM hK1 hw hc
  -- `2δM ≤ ε/2`
  have hδM : 2 * (δ : ℝ) * M ≤ ε / 2 := by
    have : (δ : ℝ) * ((M : ℝ) + 1) < ε / 4 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((M : ℝ) + 1))] at hδε
      linarith
    have hδr : (0 : ℝ) ≤ δ := hδ0.le
    nlinarith
  have hn0 : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (((avgMax A C K : ℚ) : ℝ) / K + 2 * (δ : ℝ) * M) * ((b - a : ℕ) : ℝ) ≤
      (rate A C + ε) * ((b - a : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hn0
  linarith

end Collatz.Arctic

#print axioms Collatz.Arctic.fmax_append_le
#print axioms Collatz.Arctic.rate_nonneg
#print axioms Collatz.Arctic.exists_len_near_rate
#print axioms Collatz.Arctic.block_upper_of
#print axioms Collatz.Arctic.block_upper
