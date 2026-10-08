/-
Foundations of the law of large numbers for window frequencies of uniform binary words (paragraph "Window frequencies" of Section 6.3):
the product structure of words and second moments. The law of large numbers and its interval form are in `WindowLLN2.lean`, occurrences of words and marginalization in `WindowLLN3.lean`.

* No probability is used; everything is counting over `wordsOfLen L` (the `2^L` words of length `L` in `f` and `t`).
* **Product structure of words** `card_filter_append`: concatenation `(u, v) ↦ u ++ v` is a bijection from `wordsOfLen p × wordsOfLen q` to
  `wordsOfLen (p + q)`, so the number of words satisfying a condition that splits into the first `p` letters and the rest is a product.
* **Marginal on a window** `card_filter_window`: the number of words of length `L` satisfying a condition that depends only on the window at positions `[a, a + m)` is
  the product of `2^(L - m)` and the number of words of length `m` satisfying the condition. Corollary: `2^(L - J)` words have a window equal to a given word, and for two
  disjoint windows `2^(L - 2J)` words (independence, `card_window_pair`).
* **Variance bound** `var_le`: the sum of the squared deviations of the number of windows equal to a word `v` of length `J` from the mean `N/2^J` (`N = L + 1 - J`) is
  at most `N · 2J · 2^L/2^J` (pairs of windows whose starts are at least `J` apart have covariance 0, and there are at most `2JN` close pairs).
* The lemmas are placed in `Collatz.Arctic.WinLLN` (to avoid name clashes with the window lemmas of `RateUpperBase.lean`).
-/
import CollatzProof.Arctic.RateUpperBase

namespace Collatz.Arctic

namespace WinLLN

open Finset

/-- Elements of `wordsOfLen` consist of `f` and `t` only. -/
lemma bin_of_mem {J : ℕ} {v : Word} (h : v ∈ wordsOfLen J) :
    ∀ s ∈ v, s = Letter.f ∨ s = Letter.t := by
  unfold wordsOfLen at h
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp h
  intro s hs
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  by_cases hg : g i <;> simp [hg]

lemma mem_iff {J : ℕ} {v : Word} :
    v ∈ wordsOfLen J ↔ v.length = J ∧ ∀ s ∈ v, s = Letter.f ∨ s = Letter.t :=
  ⟨fun h => ⟨length_of_mem_wordsOfLen h, bin_of_mem h⟩, fun h => mem_wordsOfLen_of h.1 h.2⟩

/-- The number of words of length `n` is `2^n`. -/
lemma card_words (n : ℕ) : (wordsOfLen n).card = 2 ^ n := by
  unfold wordsOfLen
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  intro g h hgh
  have h1 := List.ofFn_injective hgh
  funext i
  have h2 := congrFun h1 i
  cases hg : g i <;> cases hh : h i <;> simp_all

lemma take_mem {p q : ℕ} {w : Word} (hw : w ∈ wordsOfLen (p + q)) : w.take p ∈ wordsOfLen p := by
  rw [mem_iff] at hw ⊢
  exact ⟨by rw [List.length_take]; omega, fun s hs => hw.2 s (List.mem_of_mem_take hs)⟩

lemma drop_mem {p q : ℕ} {w : Word} (hw : w ∈ wordsOfLen (p + q)) : w.drop p ∈ wordsOfLen q := by
  rw [mem_iff] at hw ⊢
  exact ⟨by rw [List.length_drop]; omega, fun s hs => hw.2 s (List.mem_of_mem_drop hs)⟩

lemma append_mem {p q : ℕ} {u v : Word} (hu : u ∈ wordsOfLen p) (hv : v ∈ wordsOfLen q) :
    u ++ v ∈ wordsOfLen (p + q) := by
  rw [mem_iff] at hu hv ⊢
  refine ⟨by rw [List.length_append, hu.1, hv.1], fun s hs => ?_⟩
  rcases List.mem_append.mp hs with h | h
  · exact hu.2 s h
  · exact hv.2 s h

/-- **Product structure of words**: splitting words of length `p + q` into the first `p` letters and the rest, the number of words satisfying a condition that splits into
the front and the back is a product (concatenation `(u, v) ↦ u ++ v` is a bijection from `wordsOfLen p × wordsOfLen q` to `wordsOfLen (p + q)`). -/
theorem card_filter_append (p q : ℕ) (A B : Word → Prop) [DecidablePred A] [DecidablePred B] :
    ((wordsOfLen (p + q)).filter (fun w => A (w.take p) ∧ B (w.drop p))).card =
      ((wordsOfLen p).filter A).card * ((wordsOfLen q).filter B).card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij' (fun x _ => x.1 ++ x.2) (fun w _ => (w.take p, w.drop p)) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hx
    simp only [Finset.mem_product, Finset.mem_filter] at hx ⊢
    have hu := length_of_mem_wordsOfLen hx.1.1
    refine ⟨append_mem hx.1.1 hx.2.1, ?_, ?_⟩
    · rw [List.take_left' hu]; exact hx.1.2
    · rw [List.drop_left' hu]; exact hx.2.2
  · intro w hw
    simp only [Finset.mem_product, Finset.mem_filter] at hw ⊢
    exact ⟨⟨take_mem hw.1, hw.2.1⟩, drop_mem hw.1, hw.2.2⟩
  · rintro ⟨u, v⟩ hx
    simp only [Finset.mem_product, Finset.mem_filter] at hx
    have hu := length_of_mem_wordsOfLen hx.1.1
    simp [← hu]
  · intro w _
    simp

/-- A condition on the first `p` letters only. -/
lemma card_filter_take (p q : ℕ) (A : Word → Prop) [DecidablePred A] :
    ((wordsOfLen (p + q)).filter (fun w => A (w.take p))).card =
      ((wordsOfLen p).filter A).card * 2 ^ q := by
  have h := card_filter_append p q A (fun _ => True)
  simp only [and_true, Finset.filter_true] at h
  rw [h, card_words]

/-- A condition on the last `q` letters only. -/
lemma card_filter_drop (p q : ℕ) (B : Word → Prop) [DecidablePred B] :
    ((wordsOfLen (p + q)).filter (fun w => B (w.drop p))).card =
      2 ^ p * ((wordsOfLen q).filter B).card := by
  have h := card_filter_append p q (fun _ => True) B
  simp only [true_and, Finset.filter_true] at h
  rw [h, card_words]

/-- **Marginal on a window**: if `a + m ≤ L`, the number of words of length `L` satisfying a condition that depends only on the window at positions `[a, a + m)` is
the product of `2^(L - m)` and the number of words of length `m` satisfying the condition. -/
theorem card_filter_window (L a m : ℕ) (h : a + m ≤ L) (P : Word → Prop) [DecidablePred P] :
    ((wordsOfLen L).filter (fun w => P (window w a m))).card =
      2 ^ (L - m) * ((wordsOfLen m).filter P).card := by
  obtain ⟨r, rfl⟩ : ∃ r, L = a + (m + r) := ⟨L - a - m, by omega⟩
  have h1 := card_filter_drop a (m + r) (fun y => P (y.take m))
  have h2 := card_filter_take m r P
  rw [show a + (m + r) - m = a + r by omega, pow_add]
  refine h1.trans ?_
  rw [h2]
  ring

/-- The number of words whose window equals a given word. -/
lemma card_window_eq (L a J : ℕ) (h : a + J ≤ L) {v : Word} (hv : v ∈ wordsOfLen J) :
    ((wordsOfLen L).filter (fun w => window w a J = v)).card = 2 ^ (L - J) := by
  refine (card_filter_window L a J h (fun y => y = v)).trans ?_
  simp [Finset.filter_eq', hv]

lemma window_take {w : Word} {i J j : ℕ} (h : i + J ≤ j) : window (w.take j) i J = window w i J := by
  unfold window
  rw [List.drop_take, List.take_take]
  congr 1
  omega

lemma window_drop (w : Word) (a i J : ℕ) : window (w.drop a) i J = window w (a + i) J := by
  unfold window
  rw [List.drop_drop]

/-- The number of words whose two disjoint windows (`i + J ≤ j`) equal a given word (independence). -/
lemma card_window_pair (L i j J : ℕ) (hij : i + J ≤ j) (hj : j + J ≤ L) {v v' : Word}
    (hv : v ∈ wordsOfLen J) (hv' : v' ∈ wordsOfLen J) :
    ((wordsOfLen L).filter (fun w => window w i J = v ∧ window w j J = v')).card =
      2 ^ (L - J - J) := by
  obtain ⟨r, rfl⟩ : ∃ r, L = j + r := ⟨L - j, by omega⟩
  have h := card_filter_append j r (fun u => window u i J = v) (fun u => window u 0 J = v')
  rw [card_window_eq j i J hij hv, card_window_eq r 0 J (by omega) hv', ← pow_add] at h
  rw [show j + r - J - J = j - J + (r - J) by omega, ← h]
  congr 1
  apply Finset.filter_congr
  intro w _
  rw [window_take hij, window_drop, Nat.add_zero]

/-! ### Second moments -/

/-- Indicator of a window: 1 if the window of length `J` at position `i` equals `v`, 0 otherwise. -/
def ind (v : Word) (J i : ℕ) (w : Word) : ℚ := if window w i J = v then 1 else 0

lemma sum_ind (L i J : ℕ) (h : i + J ≤ L) {v : Word} (hv : v ∈ wordsOfLen J) :
    ∑ w ∈ wordsOfLen L, ind v J i w = 2 ^ L / 2 ^ J := by
  unfold ind
  rw [Finset.sum_boole, card_window_eq L i J h hv, Nat.cast_pow, Nat.cast_ofNat,
    pow_sub₀ _ two_ne_zero (by omega : J ≤ L), div_eq_mul_inv]

lemma ind_mul (v : Word) (J i j : ℕ) (w : Word) :
    ind v J i w * ind v J j w = if window w i J = v ∧ window w j J = v then 1 else 0 := by
  unfold ind; rw [ite_zero_mul_ite_zero, mul_one]

/-- The sum of the product of the indicators of two disjoint windows. -/
lemma sum_ind_mul_disj (L i j J : ℕ) (hij : i + J ≤ j) (hj : j + J ≤ L) {v : Word}
    (hv : v ∈ wordsOfLen J) :
    ∑ w ∈ wordsOfLen L, ind v J i w * ind v J j w = 2 ^ L / 2 ^ J / 2 ^ J := by
  simp_rw [ind_mul]
  rw [Finset.sum_boole, card_window_pair L i j J hij hj hv hv, Nat.cast_pow, Nat.cast_ofNat,
    pow_sub₀ _ two_ne_zero (by omega : J ≤ L - J), pow_sub₀ _ two_ne_zero (by omega : J ≤ L)]
  ring

/-- The covariance of two windows (times `2^L`): 0 if they are disjoint, at most `2^L / 2^J` if they overlap. -/
lemma cov_le (L i j J : ℕ) (hi : i + J ≤ L) (hj : j + J ≤ L) {v : Word} (hv : v ∈ wordsOfLen J) :
    ∑ w ∈ wordsOfLen L, (ind v J i w - 1 / 2 ^ J) * (ind v J j w - 1 / 2 ^ J) ≤
      if j < i + J ∧ i < j + J then 2 ^ L / 2 ^ J else 0 := by
  have e : ∀ w, (ind v J i w - 1 / 2 ^ J) * (ind v J j w - 1 / 2 ^ J) =
      ind v J i w * ind v J j w - 1 / 2 ^ J * ind v J j w - 1 / 2 ^ J * ind v J i w +
        (1 / 2 ^ J) ^ 2 := fun w => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_ind L i J hi hv, sum_ind L j J hj hv, Finset.sum_const, card_words,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs with hn
  · have h1 : ∑ w ∈ wordsOfLen L, ind v J i w * ind v J j w ≤ ∑ w ∈ wordsOfLen L, ind v J i w := by
      apply Finset.sum_le_sum
      intro w _
      unfold ind; split_ifs <;> norm_num
    rw [sum_ind L i J hi hv] at h1
    have h2 : (0 : ℚ) ≤ 2 ^ L * (1 / 2 ^ J) ^ 2 := by positivity
    have h3 : (1 : ℚ) / 2 ^ J * (2 ^ L / 2 ^ J) = 2 ^ L * (1 / 2 ^ J) ^ 2 := by ring
    linarith
  · have hd : i + J ≤ j ∨ j + J ≤ i := by omega
    rcases hd with hd | hd
    · rw [sum_ind_mul_disj L i j J hd hj hv]; ring_nf; rfl
    · simp_rw [mul_comm (ind v J i _)]
      rw [sum_ind_mul_disj L j i J hd hi hv]; ring_nf; rfl

/-- The number of close starts: at most `2J` indices `j` satisfy `|i - j| < J`. -/
lemma sum_near_le (N i J : ℕ) (c : ℚ) (hc : 0 ≤ c) :
    ∑ j ∈ Finset.range N, (if j < i + J ∧ i < j + J then c else 0) ≤ 2 * J * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hc
  have hsub : (Finset.range N).filter (fun j => j < i + J ∧ i < j + J) ⊆
      Finset.Ico (i + 1 - J) (i + J) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Ico] at hj ⊢
    omega
  have := (Finset.card_le_card hsub).trans (le_of_eq (Nat.card_Ico _ _))
  have h2 : i + J - (i + 1 - J) ≤ 2 * J := by omega
  exact_mod_cast this.trans h2

/-- **Variance bound**: for uniform words of length `L`, the sum of the squared deviations of the number of windows equal to a word `v` of length `J` from the mean `N / 2^J` (`N = L + 1 - J`)
is at most `N · 2J · 2^L / 2^J`. -/
theorem var_le (L J : ℕ) (hJ : J ≤ L) {v : Word} (hv : v ∈ wordsOfLen J) :
    ∑ w ∈ wordsOfLen L, ((winCount w 0 L J v : ℚ) - ((L + 1 - J : ℕ) : ℚ) / 2 ^ J) ^ 2 ≤
      ((L + 1 - J : ℕ) : ℚ) * (2 * J) * (2 ^ L / 2 ^ J) := by
  set N := L + 1 - J with hN
  have hX : ∀ w, (winCount w 0 L J v : ℚ) - (N : ℚ) / 2 ^ J =
      ∑ i ∈ Finset.range N, (ind v J i w - 1 / 2 ^ J) := by
    intro w
    rw [winCount_eq_card, Finset.natCast_card_filter, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Nat.sub_zero, ← hN]
    simp only [ind, zero_add]
    ring
  simp_rw [hX, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  calc ∑ i ∈ Finset.range N, ∑ w ∈ wordsOfLen L, ∑ j ∈ Finset.range N,
        (ind v J i w - 1 / 2 ^ J) * (ind v J j w - 1 / 2 ^ J)
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ w ∈ wordsOfLen L,
        (ind v J i w - 1 / 2 ^ J) * (ind v J j w - 1 / 2 ^ J) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (if j < i + J ∧ i < j + J then (2 : ℚ) ^ L / 2 ^ J else 0) := by
        refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
        have hi' := Finset.mem_range.mp hi
        have hj' := Finset.mem_range.mp hj
        exact cov_le L i j J (by omega) (by omega) hv
    _ ≤ ∑ i ∈ Finset.range N, 2 * J * ((2 : ℚ) ^ L / 2 ^ J) :=
        Finset.sum_le_sum (fun i _ => sum_near_le N i J _ (by positivity))
    _ = (N : ℚ) * (2 * J) * (2 ^ L / 2 ^ J) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end WinLLN

end Collatz.Arctic
