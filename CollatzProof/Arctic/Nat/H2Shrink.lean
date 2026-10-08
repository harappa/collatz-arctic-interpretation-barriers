/-
# Section 11.4: shrinking chains, values along a heavy family, hitting a residue, comparison of lengths

Section 11.4 (Lemmas 11.9–11.11 and Proposition 11.12): the shrinking chains of Lemma 11.9,
and the steps "values", "hitting a residue", "shrinking chains" and "comparison" of the proof of Proposition 11.12.
Arithmetic independent of interpretations; `T` is always `Collatz.Arctic.T`.
(Section 11.4.)

* **Shrinking chains** (`shrink_iterate`, `shrink_chain`; Lemma 11.9 (i)): if `z ≥ 1`, then `T^j(2^j z - 1) = 3^j z - 1`.
  If `3^j z = 2^e y + 1` and `2^j z ≥ 3`, then `T^{j+e}(2^j z - 1) = y` with intermediate points at least 2, and the starting point is not divisible by 3 if `3 ∣ z`.
  `W2d.mono_iterate` carries the monotonicity of values along the chain.
* **Values** (`heavy_val`, `heavy_val_sum`; Lemma 11.10): for `ω(ε) = π_{ε₁} ⋯ π_{ε_r} Ψ` (`Rigid.heavyWord`),
  `y(ε) := val(1 p₀ ω(ε) s)` satisfies `y(ε) = Y_r + δ Σ_{i<r} ε_i μ^{r-1-i}` with `Y_r := y(0^r)`, `μ := 2^{h(|Ψ|+1)}`,
  `δ := S_h 2^{|Ψ|+|s|}`, `S_h := Σ_{t<h} 2^{t(|Ψ|+1)} = val(π₁) - val(π₀)` (`W2d.valW_piBlock_one`).
* **Hitting a residue** (`target_hit`; Lemma 11.11 (ii)): the target class is only `ξ = 0` (`3^{j+1} ∣ 2^e y + 1`). With `M := j + 1 - v_3(δ)` and
  `r ≥ 8μ²M²`, apply `Rigid.cover` (Lemma D.6), and put `ε_i := [r-1-i ∈ J]` (`W2d.epsOf`). The case `v_3(δ) = 0` goes through
  with the same formula (no case distinction is needed).
* **Comparison of lengths** (`shrink_length`; Lemma 11.9 (ii)): for `j = 2j'`, `ℓ(n) + j' ≤ ℓ(y) + e` (only `9^{j'} ≥ 8^{j'}` is used).
* **Assembly** (`shrink_target`): if no `Y_r` is divisible by 3, then with `E`, `K₀` independent of `j'`, for every `j'`:
  `|p₀ ω(ε) s| ≤ K₀ (j'+1)²`, a chain `T^m(n) = y(ε)`, and `ℓ(n) + j' ≤ |p₀ ω(ε) s| + E`.
* **Comparison** (`shrink_contra`; Proposition 11.12): the comparison step of Proposition 11.13, with the value `V : ℕ → ℝ` abstract.
  `W2d.not_exp_le_poly` (`G^j ≤ K (j+1)^p` does not hold for all `j`).

Auxiliary declarations (§1–§4) are in the namespace `Collatz.Arctic.NatQ5.W2d`, the main theorems (§5) in `Collatz.Arctic.NatQ5`.
`sorry`, `axiom` and `native_decide` are not used.
-/
import CollatzProof.Arctic.Nat.H2Chain
import CollatzProof.Arctic.Nat.RigidSep
import CollatzProof.Arctic.Nat.RigidCover

namespace Collatz.Arctic.NatQ5.W2d

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W2a

/-! ## §1 Shrinking chains (auxiliary) -/

/-- A shrinking step: if `c ≥ 1`, then `T(2^{a+1} c - 1) = 2^a (3c) - 1` (an odd step). -/
theorem T_shrink_step (a c : ℕ) (hc : 1 ≤ c) :
    Collatz.Arctic.T (2 ^ (a + 1) * c - 1) = 2 ^ a * (3 * c) - 1 := by
  have h1 : 0 < 2 ^ a * c := Nat.mul_pos (by positivity) hc
  have e1 : 2 ^ (a + 1) * c = 2 * (2 ^ a * c) := by rw [pow_succ]; ring
  have e2 : 2 ^ a * (3 * c) = 3 * (2 ^ a * c) := by ring
  rw [e1, e2, W2a.T_of_odd' (by omega)]
  omega

/-- The middle of a shrinking chain: if `z ≥ 1`, then `T^i(2^{i+k} z - 1) = 2^k 3^i z - 1`. -/
theorem T_iterate_shrink (i k z : ℕ) (hz : 1 ≤ z) :
    Collatz.Arctic.T^[i] (2 ^ (i + k) * z - 1) = 2 ^ k * (3 ^ i * z) - 1 := by
  induction i generalizing z with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, show i + 1 + k = (i + k) + 1 by ring, T_shrink_step _ _ hz,
      ih (3 * z) (by omega), pow_succ 3 i]
    congr 1
    ring


/-- The intermediate points of a shrinking chain are at least 2: if `2^j z ≥ 3` and `i ≤ j`, then `T^i(2^j z - 1) ≥ 2`. -/
theorem shrink_ge_two {i j z : ℕ} (hi : i ≤ j) (h3 : 3 ≤ 2 ^ j * z) :
    2 ≤ Collatz.Arctic.T^[i] (2 ^ j * z - 1) := by
  have hz : 1 ≤ z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · subst h; simp at h3
    · exact h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [T_iterate_shrink i k z hz]
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0; simp at h3 ⊢; omega
  · have h3i : 3 ≤ 3 ^ i * z := by
      calc 3 = 3 ^ 1 * 1 := by norm_num
        _ ≤ 3 ^ i * z := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hpos) hz
    have : 3 ≤ 2 ^ k * (3 ^ i * z) :=
      h3i.trans (Nat.le_mul_of_pos_left _ (by positivity))
    omega

/-- If `3 ∣ z`, then `2^j z - 1` is not divisible by 3 (`2^j z ≥ 1`). -/
theorem shrink_not_dvd {j z : ℕ} (hz3 : 3 ∣ z) (h1 : 1 ≤ 2 ^ j * z) : ¬ 3 ∣ 2 ^ j * z - 1 := by
  obtain ⟨w, rfl⟩ := hz3
  have e : 2 ^ j * (3 * w) = 3 * (2 ^ j * w) := by ring
  rw [e] at h1 ⊢
  omega

/-- **Monotonicity of values along a chain**: if `V` does not increase along steps of `T` from numbers `n ≥ 2` not divisible by 3, then for a chain of `m` steps from `n` not divisible by 3
with intermediate points at least 2, `V(T^m n) ≤ V(n)`. -/
theorem mono_iterate {α : Type*} [Preorder α] (V : ℕ → α)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → V (Collatz.Arctic.T n) ≤ V n) :
    ∀ (m n : ℕ), ¬ 3 ∣ n → (∀ i < m, 2 ≤ Collatz.Arctic.T^[i] n) → V (Collatz.Arctic.T^[m] n) ≤ V n := by
  intro m
  induction m with
  | zero => intro n _ _; exact le_rfl
  | succ m ih =>
    intro n hn horb
    have h2 : 2 ≤ n := by simpa using horb 0 (Nat.succ_pos m)
    have hTn : ¬ 3 ∣ Collatz.Arctic.T n := fun h => hn (three_dvd_of_three_dvd_T h)
    have horb' : ∀ i < m, 2 ≤ Collatz.Arctic.T^[i] (Collatz.Arctic.T n) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    rw [Function.iterate_succ_apply]
    exact (ih _ hTn horb').trans (hT n h2 hn)


/-! ## §2 Values along a heavy family of words (auxiliary) -/

/-- The Horner value in base `μ` (most significant first): `valB μ r (b :: w) = valB μ (μ r + b) w`.
`valB μ 0 ε = Σ_i ε_i μ^{|ε|-1-i}` (`valB_eq_sum`). -/
def valB (μ : ℕ) : ℕ → List (Fin 2) → ℕ
  | r, [] => r
  | r, b :: w => valB μ (μ * r + b) w

theorem valB_eq (μ r : ℕ) (w : List (Fin 2)) : valB μ r w = r * μ ^ w.length + valB μ 0 w := by
  induction w generalizing r with
  | nil => simp [valB]
  | cons b w ih =>
    simp only [valB, List.length_cons]
    rw [ih, ih (μ * 0 + b)]
    ring

theorem valB_cons (μ : ℕ) (b : Fin 2) (w : List (Fin 2)) :
    valB μ 0 (b :: w) = (b : ℕ) * μ ^ w.length + valB μ 0 w := by
  rw [valB, valB_eq]; simp

/-- `valB μ 0 ε = Σ_{i<|ε|} ε_i μ^{|ε|-1-i}` (`ε_i` is the `i`th digit from the most significant one, counted from 0). -/
theorem valB_eq_sum (μ : ℕ) (ε : List (Fin 2)) :
    valB μ 0 ε = ∑ i ∈ Finset.range ε.length, ((ε.getD i 0 : Fin 2) : ℕ) * μ ^ (ε.length - 1 - i) := by
  induction ε with
  | nil => simp [valB]
  | cons b w ih =>
    rw [valB_cons, ih, List.length_cons, Finset.sum_range_succ', add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_sub_cancel, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [show w.length - (i + 1) = w.length - 1 - i by omega]

/-- `S_h := Σ_{t<h} 2^{t(|Ψ|+1)}` (the quantity `S`, `val(π₁) - val(π₀)`). -/
def sBlock (Ψ : List (Fin 2)) (h : ℕ) : ℕ := ∑ t ∈ Finset.range h, 2 ^ (t * (Ψ.length + 1))

theorem one_le_sBlock (Ψ : List (Fin 2)) {h : ℕ} (hh : 1 ≤ h) : 1 ≤ sBlock Ψ h := by
  obtain ⟨h', rfl⟩ := Nat.exists_eq_add_of_le' hh
  unfold sBlock
  rw [Finset.sum_range_succ']
  simp

theorem piBlock_succ (Ψ : List (Fin 2)) (h : ℕ) (e : Fin 2) :
    Rigid.piBlock Ψ (h + 1) e = (Ψ ++ [e]) ++ Rigid.piBlock Ψ h e := by
  simp [Rigid.piBlock, List.replicate_succ, List.flatten_cons]

/-- `valW r (u ++ v) = valW r u · 2^{|v|} + valW 0 v`. -/
theorem valW_app (r : ℕ) (u v : List (Fin 2)) : valW r (u ++ v) = valW r u * 2 ^ v.length + valW 0 v := by
  rw [valW_append, valW_eq]

/-- **The difference of the values of the pieces**: `val(π_e) = val(π₀) + e S_h` (`val(π₁) - val(π₀) = S`). -/
theorem valW_piBlock (Ψ : List (Fin 2)) (h : ℕ) (e : Fin 2) :
    valW 0 (Rigid.piBlock Ψ h e) = valW 0 (Rigid.piBlock Ψ h 0) + (e : ℕ) * sBlock Ψ h := by
  induction h with
  | zero => simp [Rigid.piBlock, sBlock]
  | succ h ih =>
    simp only [piBlock_succ, valW_app, Rigid.piBlock_length, List.length_singleton]
    rw [ih]
    unfold sBlock
    rw [Finset.sum_range_succ]
    simp [valW]
    ring

/-- `|π₀| = |π₁|`. -/
theorem piBlock_length_eq (Ψ : List (Fin 2)) (h : ℕ) :
    (Rigid.piBlock Ψ h 0).length = (Rigid.piBlock Ψ h 1).length := by
  rw [Rigid.piBlock_length, Rigid.piBlock_length]

/-- **`val(π₁) - val(π₀) = S_h`** (the quantity `S`). -/
theorem valW_piBlock_one (Ψ : List (Fin 2)) (h : ℕ) :
    valW 0 (Rigid.piBlock Ψ h 1) = valW 0 (Rigid.piBlock Ψ h 0) + sBlock Ψ h := by
  rw [valW_piBlock]; simp

theorem flatten_piBlock_length (Ψ : List (Fin 2)) (h : ℕ) (ε : List (Fin 2)) :
    (ε.map (Rigid.piBlock Ψ h)).flatten.length = ε.length * (h * (Ψ.length + 1)) := by
  induction ε with
  | nil => simp
  | cons e ε ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, Rigid.piBlock_length,
      List.length_cons]
    ring

/-- The value of a sequence of pieces: `val(π_{ε₁} ⋯ π_{ε_r}) = val(π₀^r) + S_h · valB μ 0 ε` (`μ := 2^{h(|Ψ|+1)}`). -/
theorem valW_flatten (Ψ : List (Fin 2)) (h : ℕ) (ε : List (Fin 2)) :
    valW 0 (ε.map (Rigid.piBlock Ψ h)).flatten =
      valW 0 ((List.replicate ε.length (0 : Fin 2)).map (Rigid.piBlock Ψ h)).flatten +
        sBlock Ψ h * valB (2 ^ (h * (Ψ.length + 1))) 0 ε := by
  induction ε with
  | nil => simp [valB]
  | cons e ε ih =>
    rw [List.length_cons, List.replicate_succ, List.map_cons, List.map_cons, List.flatten_cons,
      List.flatten_cons, valW_app, valW_app, ih, valW_piBlock Ψ h e, valB_cons, flatten_piBlock_length,
      flatten_piBlock_length, List.length_replicate, mul_comm ε.length, pow_mul]
    ring


/-! ## §3 Hitting a residue (auxiliary) -/

/-- The indicator word of a set of indices `J ⊆ {0, …, r-1}` (most significant first): `ε_i := [r-1-i ∈ J]` (`epsOf_getD`). -/
def epsOf (J : Finset ℕ) : ℕ → List (Fin 2)
  | 0 => []
  | r + 1 => (if r ∈ J then 1 else 0) :: epsOf J r

@[simp] theorem epsOf_length (J : Finset ℕ) (r : ℕ) : (epsOf J r).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [epsOf, ih]

theorem epsOf_getD (J : Finset ℕ) (r i : ℕ) :
    (epsOf J r).getD i 0 = if i < r ∧ r - 1 - i ∈ J then 1 else 0 := by
  induction r generalizing i with
  | zero => simp [epsOf]
  | succ r ih =>
    rcases i with _ | i
    · simp [epsOf]
    · simp only [epsOf, List.getD_cons_succ, ih]
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, by rwa [show r + 1 - 1 - (i + 1) = r - 1 - i by omega]⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, by rwa [show r + 1 - 1 - (i + 1) = r - 1 - i by omega] at h2⟩

/-- The value in base `μ` of the indicator word is a partial sum: `valB μ 0 (epsOf J r) = Σ_{m ∈ J, m < r} μ^m`. -/
theorem valB_epsOf (μ : ℕ) (J : Finset ℕ) (r : ℕ) :
    valB μ 0 (epsOf J r) = ∑ m ∈ (Finset.range r).filter (· ∈ J), μ ^ m := by
  induction r with
  | zero => simp [epsOf, valB]
  | succ r ih =>
    rw [epsOf, valB_cons, epsOf_length, ih, Finset.sum_filter, Finset.sum_filter, Finset.sum_range_succ,
      add_comm]
    congr 1
    split_ifs <;> simp

theorem valB_epsOf_of_subset (μ : ℕ) {J : Finset ℕ} {r : ℕ} (hJ : J ⊆ Finset.range r) :
    valB μ 0 (epsOf J r) = ∑ m ∈ J, μ ^ m := by
  rw [valB_epsOf]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (hJ h), h⟩⟩


/-! ## §4 Exponentials and polynomials (auxiliary) -/

/-- **Exponentials beat polynomials**: if `G > 1`, then for no `K`, `p` does "`G^j ≤ K (j + 1)^p` for all `j`" hold
(`tendsto_pow_const_div_const_pow_of_one_lt`). -/
theorem not_exp_le_poly {G : ℝ} (hG : 1 < G) (K : ℝ) (p : ℕ) :
    ¬ ∀ j : ℕ, G ^ j ≤ K * ((j : ℝ) + 1) ^ p := by
  intro H
  have hG0 : 0 < G := by linarith
  have ht := tendsto_pow_const_div_const_pow_of_one_lt p hG
  have ht1 : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ p / G ^ (n + 1)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (n : ℝ) ^ p / G ^ n) 1).2 ht
  have ht2 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ p / G ^ n) Filter.atTop (nhds 0) := by
    have := ht1.const_mul G
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    push_cast
    rw [pow_succ]
    field_simp
  set ε : ℝ := 1 / (|K| + 1) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨n, hn⟩ := (ht2.eventually (gt_mem_nhds hεpos)).exists
  have hGn : 0 < G ^ n := pow_pos hG0 n
  have hP : 0 < ((n : ℝ) + 1) ^ p := by positivity
  have h1 : ((n : ℝ) + 1) ^ p < ε * G ^ n := (div_lt_iff₀ hGn).1 hn
  have h2 : G ^ n ≤ |K| * ((n : ℝ) + 1) ^ p :=
    (H n).trans (mul_le_mul_of_nonneg_right (le_abs_self K) hP.le)
  have h3 : |K| * ((n : ℝ) + 1) ^ p ≤ |K| * (ε * G ^ n) := mul_le_mul_of_nonneg_left h1.le (abs_nonneg K)
  have h4 : |K| * ε < 1 := by
    rw [hε, mul_one_div, div_lt_one (by positivity)]; linarith
  have h5 : |K| * ε * G ^ n < 1 * G ^ n := mul_lt_mul_of_pos_right h4 hGn
  have h6 : |K| * (ε * G ^ n) = |K| * ε * G ^ n := by ring
  linarith

end Collatz.Arctic.NatQ5.W2d

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Collatz.Arctic.NatQ5.W2a Collatz.Arctic.NatQ5.W2d

/-! ## §5 The main theorems -/

/-- **Shrinking chains** (Lemma 11.9 (i)): if `z ≥ 1`, then `T^j(2^j z - 1) = 3^j z - 1`. -/
theorem shrink_iterate (j z : ℕ) (hz : 1 ≤ z) :
    Collatz.Arctic.T^[j] (2 ^ j * z - 1) = 3 ^ j * z - 1 := by
  simpa using T_iterate_shrink j 0 z hz


/-- **The whole shrinking chain** (Lemma 11.9 (i)): if `3^j z = 2^e y + 1`, `y ≥ 1` and `2^j z ≥ 3`, then
`n := 2^j z - 1` satisfies `T^{j+e}(n) = y` (`j` odd steps followed by `e` even steps), and the intermediate points (`i < j + e`)
are all at least 2. -/
theorem shrink_chain {j e y z : ℕ} (hy : 1 ≤ y) (hz : 3 ^ j * z = 2 ^ e * y + 1) (h3 : 3 ≤ 2 ^ j * z) :
    Collatz.Arctic.T^[j + e] (2 ^ j * z - 1) = y ∧
      ∀ i < j + e, 2 ≤ Collatz.Arctic.T^[i] (2 ^ j * z - 1) := by
  have hz1 : 1 ≤ z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · subst h; simp at h3
    · exact h
  have hj : Collatz.Arctic.T^[j] (2 ^ j * z - 1) = 2 ^ e * y := by
    rw [shrink_iterate j z hz1, hz]; omega
  have hk : ∀ k, k ≤ e → Collatz.Arctic.T^[j + k] (2 ^ j * z - 1) = 2 ^ (e - k) * y := by
    intro k hk
    rw [add_comm j k, Function.iterate_add_apply, hj]
    have := W2a.T_iterate_two_pow k (e - k) y
    rwa [show k + (e - k) = e by omega] at this
  refine ⟨by simpa using hk e le_rfl, fun i hi => ?_⟩
  rcases le_or_gt i j with hij | hij
  · exact shrink_ge_two hij h3
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    rw [show j + k + 1 = j + (k + 1) by ring, hk (k + 1) (by omega)]
    have hd : 2 ≤ 2 ^ (e - (k + 1)) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (e - (k + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact hd.trans (Nat.le_mul_of_pos_right _ hy)


/-- **Values** (Lemma 11.10): for `ω(ε) := π_{ε₁} ⋯ π_{ε_r} Ψ` (`Rigid.heavyWord`) and
`y(ε) := val(1 p₀ ω(ε) s)`,
`y(ε) = Y_r + δ · valB μ 0 ε` with `Y_r := y(0^r)`, `δ := S_h 2^{|Ψ|+|s|}`, `μ := 2^{h(|Ψ|+1)}`, `r := |ε|`. -/
theorem heavy_val (p₀ s Ψ : List (Fin 2)) (h : ℕ) (ε : List (Fin 2)) :
    valW 1 (p₀ ++ Rigid.heavyWord Ψ h ε ++ s) =
      valW 1 (p₀ ++ Rigid.heavyWord Ψ h (List.replicate ε.length 0) ++ s) +
        sBlock Ψ h * 2 ^ (Ψ.length + s.length) * valB (2 ^ (h * (Ψ.length + 1))) 0 ε := by
  simp only [Rigid.heavyWord, valW_app, List.length_append, flatten_piBlock_length, List.length_replicate]
  rw [valW_flatten Ψ h ε, pow_add]
  ring

/-- The values as a sum: `y(ε) = Y_r + δ Σ_{i<r} ε_i μ^{r-1-i}` (the version of `Y_r + δ Σ_{i:ε_i=1} μ^{r-i}` counted from 0). -/
theorem heavy_val_sum (p₀ s Ψ : List (Fin 2)) (h : ℕ) (ε : List (Fin 2)) :
    valW 1 (p₀ ++ Rigid.heavyWord Ψ h ε ++ s) =
      valW 1 (p₀ ++ Rigid.heavyWord Ψ h (List.replicate ε.length 0) ++ s) +
        sBlock Ψ h * 2 ^ (Ψ.length + s.length) *
          ∑ i ∈ Finset.range ε.length,
            ((ε.getD i 0 : Fin 2) : ℕ) * (2 ^ (h * (Ψ.length + 1))) ^ (ε.length - 1 - i) := by
  rw [heavy_val, valB_eq_sum]


/-- **Hitting a residue** (Lemma 11.11 (ii); the target class is only `ξ = 0`): if `μ ≥ 2` is prime to 3, `δ ≥ 1`, `t := v_3(δ)`, `3^t ∣ 2^e Y + 1`,
`t ≤ j` and `r ≥ 8μ²M²` (`M := j + 1 - t`), then for some `J ⊆ {0, …, r-1}`
`3^{j+1} ∣ 2^e (Y + δ Σ_{m∈J} μ^m) + 1`. The covering applies `Rigid.cover` (Lemma D.6) modulo `3^M`
to the target class `-(2^e Y + 1)/3^t · (2^e δ/3^t)^{-1}`. -/
theorem target_hit {μ δ Y e j r : ℕ} (hμ : 2 ≤ μ) (hμ3 : Nat.Coprime μ 3) (hδ : 0 < δ)
    (hY : 3 ^ padicValNat 3 δ ∣ 2 ^ e * Y + 1) (hj : padicValNat 3 δ ≤ j)
    (hr : 8 * μ ^ 2 * (j + 1 - padicValNat 3 δ) ^ 2 ≤ r) :
    ∃ J ⊆ Finset.range r, 3 ^ (j + 1) ∣ 2 ^ e * (Y + δ * ∑ m ∈ J, μ ^ m) + 1 := by
  set t := padicValNat 3 δ with ht
  set M := j + 1 - t with hM
  have hM1 : 1 ≤ M := by omega
  -- `δ = 3^t δ'`, `3 ∤ δ'`
  obtain ⟨δ', hδ'⟩ : 3 ^ t ∣ δ := pow_padicValNat_dvd
  have hδ'3 : ¬ 3 ∣ δ' := by
    rintro ⟨u, rfl⟩
    have : 3 ^ (t + 1) ∣ δ := ⟨u, by rw [hδ', pow_succ]; ring⟩
    exact pow_succ_padicValNat_not_dvd (p := 3) hδ.ne' this
  obtain ⟨q, hq⟩ := hY
  -- The unit `a := 2^e δ'` (modulo `3^M`)
  have hcop : Nat.Coprime (2 ^ e * δ') (3 ^ M) := by
    refine Nat.Coprime.pow_right _ ?_
    rw [Nat.coprime_mul_iff_left]
    exact ⟨Nat.Coprime.pow_left _ (by norm_num), (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hδ'3 |>.symm⟩
  set u : (ZMod (3 ^ M))ˣ := ZMod.unitOfCoprime (2 ^ e * δ') hcop with hu
  obtain ⟨J, hJ, hsum⟩ := Rigid.cover hμ hμ3 hM1 hr (-(q : ZMod (3 ^ M)) * ((u⁻¹ : (ZMod (3 ^ M))ˣ) : ZMod (3 ^ M)))
  refine ⟨J, hJ, ?_⟩
  set σ := ∑ m ∈ J, μ ^ m with hσ
  have hdiv : 3 ^ M ∣ q + 2 ^ e * δ' * σ := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hσc : ((σ : ℕ) : ZMod (3 ^ M)) = ∑ m ∈ J, (μ : ZMod (3 ^ M)) ^ m := by
      rw [hσ]; push_cast; rfl
    have hac : ((2 ^ e * δ' : ℕ) : ZMod (3 ^ M)) = (u : ZMod (3 ^ M)) := by
      rw [hu, ZMod.coe_unitOfCoprime]
    rw [Nat.cast_add, Nat.cast_mul, hac, hσc, hsum]
    rw [← mul_assoc, mul_comm (u : ZMod (3 ^ M)), mul_assoc, Units.mul_inv, mul_one]
    ring
  obtain ⟨w, hw⟩ := hdiv
  refine ⟨w, ?_⟩
  have h3j : 3 ^ (j + 1) = 3 ^ t * 3 ^ M := by rw [← pow_add]; congr 1; omega
  calc 2 ^ e * (Y + δ * σ) + 1 = (2 ^ e * Y + 1) + 3 ^ t * (2 ^ e * δ' * σ) := by rw [hδ']; ring
    _ = 3 ^ t * (q + 2 ^ e * δ' * σ) := by rw [hq]; ring
    _ = 3 ^ (j + 1) * w := by rw [hw, h3j]; ring


/-- **Comparison of lengths** (Lemma 11.9 (ii)): if `j = 2j'`, `3^{2j'} z = 2^e y + 1`, `y ≥ 1` and `2^{2j'} z ≥ 2`, then `n := 2^{2j'} z - 1` satisfies
`ℓ(n) + j' ≤ ℓ(y) + e` (`ℓ := |bin'(·)|`). Only `9^{j'} ≥ 8^{j'}` is used, neither `rpow` nor `log₂ 3`
(an integer version of `ℓ(n) ≤ ℓ(y) + e + 1 - (log₂ 3 - 1) j`; stronger by 1 than `ℓ(y) - ℓ(n) ≥ j' - e - 1` of an earlier plan). -/
theorem shrink_length {j' e y z : ℕ} (hy : 1 ≤ y) (hz : 3 ^ (2 * j') * z = 2 ^ e * y + 1)
    (h2 : 2 ≤ 2 ^ (2 * j') * z) :
    (binWord (2 ^ (2 * j') * z - 1)).length + j' ≤ (binWord y).length + e := by
  set n := 2 ^ (2 * j') * z - 1 with hn
  have hn1 : 1 ≤ n := by omega
  set ln := (binWord n).length
  set ly := (binWord y).length
  have hlo := (binWord_length_bounds n hn1).1
  have hhi := (binWord_length_bounds y hy).2
  have key : 2 ^ (ln + 3 * j') < 2 ^ (2 * j' + e + ly + 1) := by
    calc 2 ^ (ln + 3 * j') = 2 ^ ln * 8 ^ j' := by rw [pow_add, pow_mul]; norm_num
      _ ≤ n * 9 ^ j' := Nat.mul_le_mul hlo (Nat.pow_le_pow_left (by norm_num) j')
      _ < (n + 1) * 9 ^ j' := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self n) (by positivity)
      _ = 2 ^ (2 * j') * (2 ^ e * y + 1) := by
          rw [show n + 1 = 2 ^ (2 * j') * z by omega, ← hz, show (9 : ℕ) ^ j' = 3 ^ (2 * j') by
            rw [pow_mul]; norm_num]
          ring
      _ ≤ 2 ^ (2 * j') * (2 ^ e * 2 ^ (ly + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
          have : 2 ^ e * (y + 1) ≤ 2 ^ e * 2 ^ (ly + 1) := Nat.mul_le_mul_left _ hhi
          nlinarith
      _ = 2 ^ (2 * j' + e + ly + 1) := by rw [← pow_add, ← pow_add]; congr 1; ring
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 key
  omega


/-- **Assembly of shrinking chains and hitting** (the steps "values", "hitting a residue" and "shrinking chains" of the proof of Proposition 11.12, the form used by Proposition 11.13):
let `h ≥ 1`, and suppose that `Y_r := val(1 p₀ ω(0^r) s)` is not divisible by 3 for any `r`. Then there are `E`, `K₀` independent of `j'`
such that for every `j'` there are a word `ε` and `n ≥ 1` not divisible by 3 with, for `w := p₀ ω(ε) s` and `y := val(1 w)`,
* `|w| ≤ K₀ (j' + 1)²` (the length of the covering is `r = 8μ²M²`, `M ≤ 2j' + 1`),
* `T^m(n) = y`, with intermediate points at least 2 (the shrinking chain),
* `ℓ(n) + j' ≤ |w| + E` (comparison of lengths; `E = 2·3^{v_3(δ)}` is an upper bound for `e`).

`J' := max(j', v_3(δ))`, `j := 2J'`, `M := j + 1 - v_3(δ)`, `r := 8μ²M²`; `e` is the `e < 2·3^{v_3(δ)}` with `3^{v_3(δ)+1} ∣ 2^e Y_r + 1`
(`exists_two_pow_mul_add_one_dvd`), `ε := epsOf J r` (`ε_i = [r-1-i ∈ J]`), `z := (2^e y + 1)/3^j`
(a multiple of 3), and `n := 2^j z - 1`. -/
theorem shrink_target (Ψ p₀ s : List (Fin 2)) {h : ℕ} (hh : 1 ≤ h)
    (hY : ∀ r, ¬ 3 ∣ valW 1 (p₀ ++ Rigid.heavyWord Ψ h (List.replicate r 0) ++ s)) :
    ∃ E K₀ : ℕ, ∀ j' : ℕ, ∃ (ε : List (Fin 2)) (n m : ℕ),
      (p₀ ++ Rigid.heavyWord Ψ h ε ++ s).length ≤ K₀ * (j' + 1) ^ 2 ∧
      1 ≤ n ∧ ¬ 3 ∣ n ∧
      Collatz.Arctic.T^[m] n = valW 1 (p₀ ++ Rigid.heavyWord Ψ h ε ++ s) ∧
      (∀ i < m, 2 ≤ Collatz.Arctic.T^[i] n) ∧
      (binWord n).length + j' ≤ (p₀ ++ Rigid.heavyWord Ψ h ε ++ s).length + E := by
  set Lπ := h * (Ψ.length + 1) with hLπ
  set μ := 2 ^ Lπ with hμdef
  have hLπ1 : 1 ≤ Lπ := Nat.mul_pos hh (Nat.succ_pos _)
  have hμ2 : 2 ≤ μ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ μ := Nat.pow_le_pow_right (by norm_num) hLπ1
  have hμ3 : Nat.Coprime μ 3 := Nat.Coprime.pow_left _ (by norm_num)
  set δ := sBlock Ψ h * 2 ^ (Ψ.length + s.length) with hδdef
  have hδ : 0 < δ := Nat.mul_pos (one_le_sBlock Ψ hh) (by positivity)
  set t := padicValNat 3 δ with ht
  refine ⟨2 * 3 ^ t, p₀.length + Ψ.length + s.length + 32 * μ ^ 2 * Lπ * (t + 1) ^ 2, fun j' => ?_⟩
  set J' := max j' t with hJ'
  set j := 2 * J' with hj
  set M := j + 1 - t with hM
  set r := 8 * μ ^ 2 * M ^ 2 with hr
  set Y := valW 1 (p₀ ++ Rigid.heavyWord Ψ h (List.replicate r 0) ++ s) with hYdef
  obtain ⟨e, he, hed⟩ := exists_two_pow_mul_add_one_dvd t Y (hY r)
  have hed' : 3 ^ t ∣ 2 ^ e * Y + 1 := (pow_dvd_pow 3 (Nat.le_succ t)).trans hed
  have htj : t ≤ j := by omega
  obtain ⟨J, hJ, hJd⟩ := target_hit hμ2 hμ3 hδ hed' htj le_rfl
  set ε := epsOf J r with hε
  have hεl : ε.length = r := epsOf_length J r
  set w := p₀ ++ Rigid.heavyWord Ψ h ε ++ s with hw
  have hyval : valW 1 w = Y + δ * ∑ m ∈ J, μ ^ m := by
    rw [hw, heavy_val, hεl, valB_epsOf_of_subset _ hJ]
  have hy1 : 1 ≤ valW 1 w := le_trans Nat.one_le_two_pow (two_pow_le_valW_one w)
  obtain ⟨u, hu⟩ := hJd
  rw [← hyval] at hu
  have hz3 : 3 ^ j * (3 * u) = 2 ^ e * valW 1 w + 1 := by rw [hu, pow_succ]; ring
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0] at hu; simp at hu
    · exact h0
  have h3z : 3 ≤ 2 ^ j * (3 * u) := by
    have : 3 ≤ 3 * u := by omega
    exact this.trans (Nat.le_mul_of_pos_left _ (by positivity))
  obtain ⟨hTm, horb⟩ := shrink_chain hy1 hz3 h3z
  refine ⟨ε, 2 ^ j * (3 * u) - 1, j + e, ?_, by omega, shrink_not_dvd ⟨u, rfl⟩ (by omega), hTm, horb, ?_⟩
  · -- Length: `|w| = |p₀| + r Lπ + |Ψ| + |s|`, `M ≤ 2 (t + 1)(j' + 1)`
    have hwl : w.length = p₀.length + Ψ.length + s.length + r * Lπ := by
      rw [hw, List.length_append, List.length_append, Rigid.heavyWord_length, hεl]; ring
    have hJ'le : J' ≤ j' + t := max_le (by omega) (by omega)
    have hM2 : M ≤ 2 * ((t + 1) * (j' + 1)) := by
      have : M ≤ 2 * J' + 1 := by omega
      nlinarith
    have hMsq : M ^ 2 ≤ 4 * ((t + 1) ^ 2 * (j' + 1) ^ 2) := by
      calc M ^ 2 ≤ (2 * ((t + 1) * (j' + 1))) ^ 2 := Nat.pow_le_pow_left hM2 2
        _ = 4 * ((t + 1) ^ 2 * (j' + 1) ^ 2) := by ring
    have hrL : r * Lπ ≤ 32 * μ ^ 2 * Lπ * (t + 1) ^ 2 * (j' + 1) ^ 2 := by
      calc r * Lπ = 8 * μ ^ 2 * Lπ * M ^ 2 := by rw [hr]; ring
        _ ≤ 8 * μ ^ 2 * Lπ * (4 * ((t + 1) ^ 2 * (j' + 1) ^ 2)) := Nat.mul_le_mul_left _ hMsq
        _ = 32 * μ ^ 2 * Lπ * (t + 1) ^ 2 * (j' + 1) ^ 2 := by ring
    have hX : 1 ≤ (j' + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hA : p₀.length + Ψ.length + s.length ≤ (p₀.length + Ψ.length + s.length) * (j' + 1) ^ 2 :=
      Nat.le_mul_of_pos_right _ hX
    rw [hwl, add_mul]
    linarith
  · -- Comparison of lengths
    change (binWord (2 ^ j * (3 * u) - 1)).length + j' ≤ w.length + 2 * 3 ^ t
    have hl : (binWord (2 ^ j * (3 * u) - 1)).length + J' ≤ w.length + e := by
      have := shrink_length (j' := J') hy1 hz3 (le_trans (by norm_num : 2 ≤ 3) h3z)
      rw [binWord_valW] at this
      exact this
    have : e ≤ 2 * 3 ^ t := he.le
    have : j' ≤ J' := le_max_left _ _
    omega


/-- **The comparison step** (Proposition 11.12; an abstract form independent of interpretations): `V : ℕ → ℝ` (in Proposition 11.13,
`V n := aval L (bin'(n))`) cannot satisfy all of the following.
* `hT`: `V(T n) ≤ V(n)` for `n ≥ 2` not divisible by 3 (the form of Lemma 10.2).
* `h3`: `V(n) ≤ 0` for multiples `n ≥ 1` of 3.
* `hup`: `V(n) ≤ C (ℓ(n) + 1)^p G^{ℓ(n)}` for `n ≥ 1` not divisible by 3 (the polynomial bound, the form of `aval_poly_bound`).
* `hlow`: `c G^{|ω(ε)|} ≤ V(val(1 p₀ ω(ε) s))` along the heavy family `ω(ε) = π_{ε₁} ⋯ π_{ε_r} Ψ` (`h ≥ 1`), with `c > 0` and `G > 1`.

By `h3` and `hlow` no `Y_r` is divisible by 3, and for each `j'` of `shrink_target`, `c G^{j'} ≤ C ((K₀ + E + 1)(j' + 1)²)^p G^{|p₀|+|s|+E}`,
which contradicts `not_exp_le_poly`. -/
theorem shrink_contra (V : ℕ → ℝ) (Ψ p₀ s : List (Fin 2)) {h : ℕ} (hh : 1 ≤ h) {G c C : ℝ} {p : ℕ}
    (hG : 1 < G) (hc : 0 < c)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → V (Collatz.Arctic.T n) ≤ V n)
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → V n ≤ 0)
    (hup : ∀ n, 1 ≤ n → ¬ 3 ∣ n →
      V n ≤ C * (((binWord n).length : ℝ) + 1) ^ p * G ^ (binWord n).length)
    (hlow : ∀ ε, c * G ^ (Rigid.heavyWord Ψ h ε).length ≤ V (valW 1 (p₀ ++ Rigid.heavyWord Ψ h ε ++ s))) :
    False := by
  have hG0 : 0 < G := by linarith
  have hY : ∀ r, ¬ 3 ∣ valW 1 (p₀ ++ Rigid.heavyWord Ψ h (List.replicate r 0) ++ s) := by
    intro r hdvd
    have h1 := h3 _ (le_trans Nat.one_le_two_pow (two_pow_le_valW_one _)) hdvd
    have h2 := hlow (List.replicate r 0)
    have : 0 < c * G ^ (Rigid.heavyWord Ψ h (List.replicate r 0)).length := by positivity
    linarith
  obtain ⟨E, K₀, hsh⟩ := shrink_target Ψ p₀ s hh hY
  set P := p₀.length + s.length + E with hP
  have key : ∀ j' : ℕ, c * G ^ j' ≤ C * ((K₀ + E + 1 : ℝ) * ((j' : ℝ) + 1) ^ 2) ^ p * G ^ P := by
    intro j'
    obtain ⟨ε, n, m, hwl, hn1, hn3, hTm, horb, hlen⟩ := hsh j'
    set ω := Rigid.heavyWord Ψ h ε with hω
    set w := p₀ ++ ω ++ s with hw
    have hwlen : w.length = p₀.length + ω.length + s.length := by simp only [hw, List.length_append]
    have hmono := W2d.mono_iterate V hT m n hn3 horb
    rw [hTm] at hmono
    set ln := (binWord n).length with hln
    have h1 : c * G ^ ω.length ≤ C * ((ln : ℝ) + 1) ^ p * G ^ ln := (hlow ε).trans (hmono.trans (hup n hn1 hn3))
    have hX : 0 < ((ln : ℝ) + 1) ^ p * G ^ ln := by positivity
    have hC : 0 < C := by
      by_contra hC
      push Not at hC
      have : C * (((ln : ℝ) + 1) ^ p * G ^ ln) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC hX.le
      have : 0 < c * G ^ ω.length := by positivity
      rw [mul_assoc] at h1
      linarith
    -- Length: `ℓ(n) + 1 ≤ (K₀ + E + 1)(j' + 1)²`, `G^{ℓ(n) + j'} ≤ G^{|ω| + P}`
    have hbaseN : ln + 1 ≤ (K₀ + E + 1) * (j' + 1) ^ 2 := by
      have hX1 : 1 ≤ (j' + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have : E + 1 ≤ (E + 1) * (j' + 1) ^ 2 := Nat.le_mul_of_pos_right _ hX1
      nlinarith
    have hbase : (ln : ℝ) + 1 ≤ (K₀ + E + 1 : ℝ) * ((j' : ℝ) + 1) ^ 2 := by exact_mod_cast hbaseN
    have hpow : ((ln : ℝ) + 1) ^ p ≤ ((K₀ + E + 1 : ℝ) * ((j' : ℝ) + 1) ^ 2) ^ p :=
      pow_le_pow_left₀ (by positivity) hbase p
    have hexp : G ^ (ln + j') ≤ G ^ (ω.length + P) := by
      refine pow_le_pow_right₀ hG.le ?_
      have : ln + j' ≤ w.length + E := hlen
      omega
    have hmain : G ^ ω.length * (c * G ^ j') ≤
        G ^ ω.length * (C * ((K₀ + E + 1 : ℝ) * ((j' : ℝ) + 1) ^ 2) ^ p * G ^ P) := by
      calc G ^ ω.length * (c * G ^ j') = G ^ j' * (c * G ^ ω.length) := by ring
        _ ≤ G ^ j' * (C * ((ln : ℝ) + 1) ^ p * G ^ ln) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = C * ((ln : ℝ) + 1) ^ p * G ^ (ln + j') := by rw [pow_add]; ring
        _ ≤ C * ((K₀ + E + 1 : ℝ) * ((j' : ℝ) + 1) ^ 2) ^ p * G ^ (ω.length + P) := by
            gcongr
        _ = G ^ ω.length * (C * ((K₀ + E + 1 : ℝ) * ((j' : ℝ) + 1) ^ 2) ^ p * G ^ P) := by
            rw [pow_add]; ring
    exact le_of_mul_le_mul_left hmain (by positivity)
  -- Rewrite as `G^{j'} ≤ K (j' + 1)^{2p}` for a contradiction
  refine W2d.not_exp_le_poly hG (C * (K₀ + E + 1 : ℝ) ^ p * G ^ P / c) (2 * p) fun j' => ?_
  have := key j'
  calc G ^ j' = (c * G ^ j') / c := by field_simp
    _ ≤ (C * ((K₀ + E + 1 : ℝ) * ((j' : ℝ) + 1) ^ 2) ^ p * G ^ P) / c := by gcongr
    _ = C * (K₀ + E + 1 : ℝ) ^ p * G ^ P / c * ((j' : ℝ) + 1) ^ (2 * p) := by
        rw [mul_pow, ← pow_mul, mul_comm 2 p]; ring

end Collatz.Arctic.NatQ5
