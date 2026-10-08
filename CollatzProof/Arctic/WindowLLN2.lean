/-
The law of large numbers for window frequencies (paragraph "Window frequencies" of Section 6.3, the case of uniform words) and its interval form.
The foundations (product structure of words, variance bound) are in `WindowLLN.lean`.

* `winClose_lln`: for `J`, `δ > 0` and `ε > 0`, if `L ≥ J + ⌈J 4^J/(δ² ε)⌉`, then at least `(1 - ε) 2^L` words of length `L`
  have windows of length `J` on `[0, L)` that are `δ`-close to uniform (`WinClose w 0 L J δ`).
  The proof is a counting form of Chebyshev's inequality (`cheb`) and a union bound over the words `v` (`2^J` of them).
* `card_winClose_interval`: if `a ≤ b ≤ L`, the number of words of length `L` whose windows on `[a, b)` are close to uniform is
  the product of `2^(L - (b - a))` and the number of words of length `b - a` whose windows on the whole word are close to uniform (an equality).
* `winClose_lln_interval`: the interval form combining the two (proportion at least `1 - ε` if `b - a` is large, uniformly in `L`, `a`, `b`).
* Decidability for the `Finset.filter` by `WinClose` is provided by `open Classical in` (as for `HSP` in `CoreHyp.lean`).
-/
import CollatzProof.Arctic.WindowLLN

namespace Collatz.Arctic

namespace WinLLN

/-- Chebyshev's inequality in counting form. -/
lemma cheb {α : Type*} (s : Finset α) (f : α → ℚ) (c : ℚ) (hc : 0 < c) :
    ((s.filter (fun x => c < |f x|)).card : ℚ) * c ^ 2 ≤ ∑ x ∈ s, f x ^ 2 := by
  calc ((s.filter (fun x => c < |f x|)).card : ℚ) * c ^ 2
      = ∑ x ∈ s.filter (fun x => c < |f x|), c ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ s.filter (fun x => c < |f x|), f x ^ 2 := by
        refine Finset.sum_le_sum (fun x hx => ?_)
        have h := (Finset.mem_filter.mp hx).2
        rw [← sq_abs (f x)]
        exact pow_le_pow_left₀ hc.le h.le 2
    _ ≤ ∑ x ∈ s, f x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)

/-- Arithmetic for the bound on the number of bad words. -/
lemma bad_arith (B δ ε N J T q : ℚ) (hq : 0 < q) (hN : 0 < N) (hδ : 0 < δ) (hε : 0 < ε) (hT : 0 < T)
    (hbig : J * q ^ 2 < N * (δ ^ 2 * ε))
    (h : B * (2 * δ * N * (1 / q)) ^ 2 ≤ N * (2 * J) * (T / q)) : B ≤ ε * T / q := by
  have e1 : B * (2 * δ * N * (1 / q)) ^ 2 = (B * (2 * δ ^ 2 * N)) * (2 * N) / q ^ 2 := by
    field_simp
  have e2 : N * (2 * J) * (T / q) = (J * T * q) * (2 * N) / q ^ 2 := by
    field_simp
  rw [e1, e2, div_le_div_iff_of_pos_right (by positivity),
    mul_le_mul_iff_left₀ (by positivity)] at h
  -- `B q (2 δ² N) ≤ J T q² < N δ² ε T`
  have h3 : B * q * (2 * δ ^ 2 * N) ≤ J * q ^ 2 * T := by nlinarith
  have h4 : J * q ^ 2 * T ≤ N * (δ ^ 2 * ε) * T := mul_le_mul_of_nonneg_right hbig.le hT.le
  have h5 : B * q ≤ ε * T := by
    have hpos : 0 < 2 * δ ^ 2 * N := by positivity
    by_contra hc
    have hc' := lt_of_not_ge hc
    have h6 : ε * T * (2 * δ ^ 2 * N) < B * q * (2 * δ ^ 2 * N) := mul_lt_mul_of_pos_right hc' hpos
    have h7 : ε * T * (2 * δ ^ 2 * N) = 2 * (N * (δ ^ 2 * ε) * T) := by ring
    have h8 : 0 < N * (δ ^ 2 * ε) * T := by positivity
    linarith
  rw [le_div_iff₀ hq]
  exact h5
end WinLLN

open WinLLN in
open Classical in
/-- **Law of large numbers for window frequencies** (paragraph "Window frequencies" of Section 6.3, the case of uniform words): for a length `J`, `δ > 0` and `ε > 0`,
if `L` is large, then the proportion of binary words of length `L` whose windows of length `J` on the whole `[0, L)` are `δ`-close to uniform
is at least `1 - ε`. -/
theorem winClose_lln (J : ℕ) (δ ε : ℚ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀,
      (1 - ε) * 2 ^ L ≤ (((wordsOfLen L).filter (fun w => WinClose w 0 L J δ)).card : ℚ) := by
  refine ⟨J + ⌈(J : ℚ) * 4 ^ J / (δ ^ 2 * ε)⌉₊, fun L hL => ?_⟩
  set N := L + 1 - J with hN
  have hJL : J ≤ L := by omega
  have hNpos : (0 : ℚ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq : (0 : ℚ) < 2 ^ J := by positivity
  have hq2 : ((2 : ℚ) ^ J) ^ 2 = 4 ^ J := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hbig : (J : ℚ) * ((2 : ℚ) ^ J) ^ 2 < N * (δ ^ 2 * ε) := by
    have h1 : ⌈(J : ℚ) * 4 ^ J / (δ ^ 2 * ε)⌉₊ < N := by omega
    have h2 := Nat.lt_of_ceil_lt h1
    rw [div_lt_iff₀ (by positivity)] at h2
    rw [hq2]; exact h2
  set c : ℚ := 2 * δ * N * (1 / 2 ^ J) with hc
  have hcpos : 0 < c := by positivity
  set bad : Word → Finset Word := fun v => (wordsOfLen L).filter
    (fun w => c < |(winCount w 0 L J v : ℚ) - (N : ℚ) / 2 ^ J|) with hbad_def
  -- the number of bad words for each `v`
  have hbad : ∀ v ∈ wordsOfLen J, ((bad v).card : ℚ) ≤ ε * 2 ^ L / 2 ^ J := by
    intro v hv
    have h1 := cheb (wordsOfLen L) (fun w => (winCount w 0 L J v : ℚ) - (N : ℚ) / 2 ^ J) c hcpos
    have h2 := (var_le L J hJL hv)
    exact bad_arith _ δ ε N J (2 ^ L) (2 ^ J) hq hNpos hδ hε (by positivity) hbig (h1.trans h2)
  -- words that are not bad have window frequencies close to uniform
  have hgood : ∀ w ∈ wordsOfLen L, w ∉ (wordsOfLen J).biUnion bad → WinClose w 0 L J δ := by
    intro w hw hnot
    refine ⟨by omega, by rw [length_of_mem_wordsOfLen hw], ?_⟩
    have hle : ∀ v ∈ wordsOfLen J,
        |(winCount w 0 L J v : ℚ) / ((L + 1 - J - 0 : ℕ) : ℚ) - 1 / 2 ^ J| ≤ 2 * δ * (1 / 2 ^ J) := by
      intro v hv
      have hv' : ¬ c < |(winCount w 0 L J v : ℚ) - (N : ℚ) / 2 ^ J| := by
        intro hlt
        exact hnot (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨hw, hlt⟩⟩)
      replace hv' := le_of_not_gt hv'
      rw [Nat.sub_zero, ← hN]
      have e : (winCount w 0 L J v : ℚ) / N - 1 / 2 ^ J =
          ((winCount w 0 L J v : ℚ) - (N : ℚ) / 2 ^ J) / N := by field_simp
      rw [e, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
      calc |(winCount w 0 L J v : ℚ) - (N : ℚ) / 2 ^ J| ≤ c := hv'
        _ = 2 * δ * (1 / 2 ^ J) * N := by rw [hc]; ring
    calc ∑ v ∈ wordsOfLen J,
          |(winCount w 0 L J v : ℚ) / ((L + 1 - J - 0 : ℕ) : ℚ) - 1 / 2 ^ J|
        ≤ ∑ v ∈ wordsOfLen J, 2 * δ * (1 / 2 ^ J) := Finset.sum_le_sum hle
      _ = 2 * δ := by
          rw [Finset.sum_const, card_words, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
          field_simp
  -- counting
  have hsub : (wordsOfLen L).filter (fun w => ¬ WinClose w 0 L J δ) ⊆
      (wordsOfLen J).biUnion bad := by
    intro w hw
    rw [Finset.mem_filter] at hw
    by_contra hn
    exact hw.2 (hgood w hw.1 hn)
  have hsum : (((wordsOfLen J).biUnion bad).card : ℚ) ≤ ε * 2 ^ L := by
    have h1 : (((wordsOfLen J).biUnion bad).card : ℚ) ≤ ∑ v ∈ wordsOfLen J, ((bad v).card : ℚ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∑ v ∈ wordsOfLen J, ((bad v).card : ℚ) ≤ ∑ v ∈ wordsOfLen J, ε * 2 ^ L / 2 ^ J :=
      Finset.sum_le_sum hbad
    rw [Finset.sum_const, card_words, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h2
    have e : (2 : ℚ) ^ J * (ε * 2 ^ L / 2 ^ J) = ε * 2 ^ L := by field_simp
    linarith
  have htot := Finset.card_filter_add_card_filter_not (s := wordsOfLen L)
    (fun w => WinClose w 0 L J δ)
  rw [card_words] at htot
  have h3 : (((wordsOfLen L).filter (fun w => ¬ WinClose w 0 L J δ)).card : ℚ) ≤ ε * 2 ^ L :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub) hsum
  have h4 : ((((wordsOfLen L).filter (fun w => WinClose w 0 L J δ)).card : ℕ) : ℚ) +
      (((wordsOfLen L).filter (fun w => ¬ WinClose w 0 L J δ)).card : ℚ) = 2 ^ L := by
    exact_mod_cast htot
  linarith

namespace WinLLN

/-! ### Interval form -/

/-- The number of windows on the interval `[a, b)` equals the number of windows of the word cut out on the interval. -/
lemma winCount_cut (w : Word) {a b : ℕ} (hab : a ≤ b) (J : ℕ) (v : Word) :
    winCount w a b J v = winCount (window w a (b - a)) 0 (b - a) J v := by
  rw [winCount_eq_card, winCount_eq_card, show b - a + 1 - J - 0 = b + 1 - J - a by omega]
  apply congrArg
  apply Finset.filter_congr
  intro i hi
  rw [Finset.mem_range] at hi
  rw [zero_add, show window w a (b - a) = (w.drop a).take (b - a) from rfl,
    window_take (by omega), window_drop]

/-- `WinClose` is equivalent to `WinClose` for the word cut out on the interval. -/
lemma winClose_cut {w : Word} {a b J : ℕ} {δ : ℚ} (hab : a ≤ b) (hb : b ≤ w.length) :
    WinClose w a b J δ ↔ WinClose (window w a (b - a)) 0 (b - a) J δ := by
  unfold WinClose
  have hl : (window w a (b - a)).length = b - a := length_window w (by omega)
  simp_rw [winCount_cut w hab J, hl, show b - a + 1 - J - 0 = b + 1 - J - a by omega]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨by omega, le_refl _, h3⟩
  · rintro ⟨h1, -, h3⟩; exact ⟨by omega, hb, h3⟩

end WinLLN

open WinLLN in
open Classical in
/-- **Interval form**: if `a ≤ b ≤ L`, the number of words of length `L` whose windows on `[a, b)` are close to uniform is
the product of `2^(L - (b - a))` and the number of words of length `b - a` whose windows on the whole word are close to uniform. -/
theorem card_winClose_interval (L a b J : ℕ) (δ : ℚ) (hab : a ≤ b) (hbL : b ≤ L) :
    ((wordsOfLen L).filter (fun w => WinClose w a b J δ)).card =
      2 ^ (L - (b - a)) *
        ((wordsOfLen (b - a)).filter (fun v => WinClose v 0 (b - a) J δ)).card := by
  refine Eq.trans ?_ (card_filter_window L a (b - a) (by omega)
    (fun v => WinClose v 0 (b - a) J δ))
  apply congrArg
  apply Finset.filter_congr
  intro w hw
  exact winClose_cut hab (by rw [length_of_mem_wordsOfLen hw]; exact hbL)

open Classical in
/-- **Law of large numbers, interval form**: if `b - a` is large, the proportion of words of length `L` whose windows on `[a, b)` are close to uniform
is at least `1 - ε` (uniformly in `L`, `a`, `b`). -/
theorem winClose_lln_interval (J : ℕ) (δ ε : ℚ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ L a b : ℕ, a ≤ b → b ≤ L → M₀ ≤ b - a →
      (1 - ε) * 2 ^ L ≤ (((wordsOfLen L).filter (fun w => WinClose w a b J δ)).card : ℚ) := by
  obtain ⟨M₀, hM⟩ := winClose_lln J δ ε hδ hε
  refine ⟨M₀, fun L a b hab hbL hM₀ => ?_⟩
  rw [card_winClose_interval L a b J δ hab hbL, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have h := mul_le_mul_of_nonneg_left (hM (b - a) hM₀) (by positivity : (0 : ℚ) ≤ 2 ^ (L - (b - a)))
  have e : (2 : ℚ) ^ (L - (b - a)) * ((1 - ε) * 2 ^ (b - a)) = (1 - ε) * 2 ^ L := by
    rw [mul_left_comm, ← pow_add, show L - (b - a) + (b - a) = L by omega]
  linarith

end Collatz.Arctic
