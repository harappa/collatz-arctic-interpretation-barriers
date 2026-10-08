/-
Occurrences of words and marginalization in the window length (paragraph "Window frequencies" of Section 6.3). Foundations in `WindowLLN.lean` and
`WindowLLN2.lean`.

* `card_noOcc_le`: at most `2^L (1 - 2^{-m})^{⌊(b-a)/m⌋}` words of length `L` have no occurrence of a binary word `v` (of length `m`) inside the positions `[a, b)` (`b ≤ L`)
  (disjoint aligned segments of length `m` are independent; `card_aligned` is an equality).
  Corollary `noOcc_small`: if `v ≠ []` and `b - a` is large, the proportion is at most `ε` (uniformly in `L`, `a`, `b`).
* `winClose_marginal`: for a binary word `w` with `WinClose w a b J δ` and `G ≤ J`, `WinClose w a b G (δ + (J - G)/N_G)`
  (`N_G = b + 1 - G - a` is the number of windows of length `G`).
* `noOcc_window_frac`: if `WinClose w a b G δ`, then at most `((1 - 2^{-m})^{⌊G/m⌋} + 2δ) N_G` of the windows of length `G` on `[a, b)` do not contain `v`
  as an infix (the assumption that `w` is binary is not needed).
-/
import CollatzProof.Arctic.WindowLLN2

namespace Collatz.Arctic

namespace WinLLN

/-! ### Occurrences of words -/

/-- The number of words in which `v` occurs in none of the `K` disjoint segments `[a + k m, a + (k+1) m)` (independence). -/
lemma card_aligned (m : ℕ) {v : Word} (hv : v ∈ wordsOfLen m) :
    ∀ K a L : ℕ, a + K * m ≤ L →
      ((wordsOfLen L).filter (fun w => ∀ k < K, window w (a + k * m) m ≠ v)).card =
        2 ^ (L - K * m) * (2 ^ m - 1) ^ K := by
  intro K
  induction K with
  | zero =>
    intro a L _
    simp [card_words]
  | succ K ih =>
    intro a L h
    rw [Nat.succ_mul] at h ⊢
    obtain ⟨r, rfl⟩ : ∃ r, L = (a + m) + r := ⟨L - (a + m), by omega⟩
    have h1 := card_filter_append (a + m) r (fun u => window u a m ≠ v)
      (fun u => ∀ k < K, window u (0 + k * m) m ≠ v)
    rw [ih 0 r (by omega)] at h1
    have h2 : ((wordsOfLen (a + m)).filter (fun u => window u a m ≠ v)).card =
        2 ^ a * (2 ^ m - 1) := by
      refine (card_filter_window (a + m) a m le_rfl (fun y => y ≠ v)).trans ?_
      rw [Finset.filter_ne', Finset.card_erase_of_mem hv, card_words, show a + m - m = a by omega]
    rw [h2] at h1
    rw [show a + m + r - (K * m + m) = a + (r - K * m) by omega, pow_add, pow_succ]
    refine Eq.trans ?_ (h1.trans (by ring))
    apply congrArg
    apply Finset.filter_congr
    intro w _
    rw [Nat.forall_lt_succ_left', window_take (by omega), zero_mul, add_zero]
    refine and_congr Iff.rfl ?_
    refine forall_congr' (fun k => imp_congr_right (fun _ => ?_))
    rw [window_drop, show a + m + (0 + k * m) = a + (k + 1) * m by ring]

end WinLLN

open WinLLN in
open Classical in
/-- **Occurrences of words**: for a binary word `v` (of length `m`), the number of words of length `L` with
no occurrence of `v` inside the positions `[a, b)` (`b ≤ L`) is at most `2^L (1 - 2^{-m})^{⌊(b-a)/m⌋}`
(disjoint segments of length `m` are independent). For `v = []` the exponent is 0 and the bound is trivial. -/
theorem card_noOcc_le (L a b : ℕ) {v : Word} (hv : v ∈ wordsOfLen v.length) (hbL : b ≤ L) :
    (((wordsOfLen L).filter
        (fun w => ∀ i, a ≤ i → i + v.length ≤ b → window w i v.length ≠ v)).card : ℚ) ≤
      2 ^ L * (1 - 1 / 2 ^ v.length) ^ ((b - a) / v.length) := by
  set m := v.length with hm
  set K := (b - a) / m with hK
  have hKm : K * m ≤ b - a := Nat.div_mul_le_self _ _
  by_cases hab : a ≤ b
  · have hsub : (wordsOfLen L).filter (fun w => ∀ i, a ≤ i → i + m ≤ b → window w i m ≠ v) ⊆
        (wordsOfLen L).filter (fun w => ∀ k < K, window w (a + k * m) m ≠ v) := by
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨hw.1, fun k hk => hw.2 _ (by omega) ?_⟩
      have : (k + 1) * m ≤ K * m := Nat.mul_le_mul_right m hk
      rw [Nat.succ_mul] at this
      omega
    have h1 := Finset.card_le_card hsub
    rw [card_aligned m hv K a L (by omega)] at h1
    have h2 : ((2 ^ (L - K * m) * (2 ^ m - 1) ^ K : ℕ) : ℚ) = 2 ^ L * (1 - 1 / 2 ^ m) ^ K := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_one, pow_sub₀ _ two_ne_zero (by omega : K * m ≤ L), pow_mul']
      have : (1 : ℚ) - 1 / 2 ^ m = (2 ^ m - 1) / 2 ^ m := by field_simp
      rw [this, div_pow]
      field_simp
    calc _ ≤ ((2 ^ (L - K * m) * (2 ^ m - 1) ^ K : ℕ) : ℚ) := by exact_mod_cast h1
      _ = _ := h2
  · have hK0 : K = 0 := by rw [hK, show b - a = 0 by omega, Nat.zero_div]
    rw [hK0, pow_zero, mul_one]
    calc _ ≤ ((wordsOfLen L).card : ℚ) := by exact_mod_cast Finset.card_filter_le _ _
      _ = 2 ^ L := by rw [card_words]; push_cast; rfl

open Classical in
/-- **Corollary on occurrences**: for a nonempty binary word `v` and `ε > 0` there is `D` such that, if `b - a ≥ D`, the proportion of words of length `L`
with no occurrence of `v` inside `[a, b)` is at most `ε` (uniformly in `L`, `a`, `b`). -/
theorem noOcc_small {v : Word} (hv : v ∈ wordsOfLen v.length) (hne : v ≠ []) (ε : ℚ)
    (hε : 0 < ε) :
    ∃ D : ℕ, ∀ L a b : ℕ, b ≤ L → a + D ≤ b →
      (((wordsOfLen L).filter
        (fun w => ∀ i, a ≤ i → i + v.length ≤ b → window w i v.length ≠ v)).card : ℚ) ≤
        ε * 2 ^ L := by
  have hm : 0 < v.length := List.length_pos_iff.mpr hne
  have hx0 : (0 : ℚ) ≤ 1 - 1 / 2 ^ v.length := by
    have : (1 : ℚ) / 2 ^ v.length ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    linarith
  have hx1 : (1 : ℚ) - 1 / 2 ^ v.length < 1 := by
    have : (0 : ℚ) < 1 / 2 ^ v.length := by positivity
    linarith
  obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one hε hx1
  refine ⟨K₀ * v.length, fun L a b hbL hD => ?_⟩
  have hK : K₀ ≤ (b - a) / v.length := (Nat.le_div_iff_mul_le hm).mpr (by omega)
  have h1 := card_noOcc_le L a b hv hbL
  have h2 := pow_le_pow_of_le_one hx0 hx1.le hK
  calc _ ≤ _ := h1
    _ ≤ (2 : ℚ) ^ L * (1 - 1 / 2 ^ v.length) ^ K₀ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 ^ L * ε := mul_le_mul_of_nonneg_left hK₀.le (by positivity)
    _ = ε * 2 ^ L := mul_comm _ _

namespace WinLLN

/-! ### Marginalization -/

/-- For a binary word, summing the numbers of occurrences of the windows of length `K` on the interval `[a, b)` over all words gives the number of windows. -/
lemma sum_winCount {w : Word} (hw : ∀ s ∈ w, s = Letter.f ∨ s = Letter.t) (a b K : ℕ)
    (hb : b ≤ w.length) :
    ∑ v ∈ wordsOfLen K, winCount w a b K v = b + 1 - K - a := by
  have h := Finset.card_eq_sum_card_fiberwise (f := fun i => window w (a + i) K)
    (s := Finset.range (b + 1 - K - a)) (t := wordsOfLen K) (fun i hi =>
      window_mem_wordsOfLen hw (by rw [Finset.mem_coe, Finset.mem_range] at hi; omega))
  rw [Finset.card_range] at h
  rw [h]
  exact Finset.sum_congr rfl (fun v _ => winCount_eq_card w a b K v)

lemma take_mem_of_le {G J : ℕ} (hGJ : G ≤ J) {v : Word} (hv : v ∈ wordsOfLen J) :
    v.take G ∈ wordsOfLen G := by
  rw [mem_iff] at hv ⊢
  exact ⟨by rw [List.length_take]; omega, fun s hs => hv.2 s (List.mem_of_mem_take hs)⟩

/-- The number of words of length `J` that begin with a word `u` of length `G` is `2^(J - G)`. -/
lemma card_fiber_take {G J : ℕ} (hGJ : G ≤ J) {u : Word} (hu : u ∈ wordsOfLen G) :
    ((wordsOfLen J).filter (fun v => v.take G = u)).card = 2 ^ (J - G) :=
  card_window_eq J 0 G (by omega) hu

/-- The number of windows of length `J` that begin with `u` is at most the number of windows of length `G` equal to `u`. -/
lemma sum_fiber_le {w : Word} (hw : ∀ s ∈ w, s = Letter.f ∨ s = Letter.t) {a b J G : ℕ}
    (hGJ : G ≤ J) (hb : b ≤ w.length) (u : Word) :
    ∑ v ∈ (wordsOfLen J).filter (fun v => v.take G = u), winCount w a b J v ≤
      winCount w a b G u := by
  set s := (Finset.range (b + 1 - J - a)).filter (fun i => (window w (a + i) J).take G = u)
  have h1 := Finset.card_eq_sum_card_fiberwise (f := fun i => window w (a + i) J) (s := s)
    (t := (wordsOfLen J).filter (fun v => v.take G = u)) (by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨window_mem_wordsOfLen hw (by omega), hi.2⟩)
  have h2 : ∑ v ∈ (wordsOfLen J).filter (fun v => v.take G = u), winCount w a b J v =
      s.card := by
    rw [h1]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [Finset.mem_filter] at hv
    rw [winCount_eq_card, Finset.filter_filter]
    apply congrArg
    apply Finset.filter_congr
    intro i _
    exact ⟨fun h => ⟨by rw [h]; exact hv.2, h⟩, fun h => h.2⟩
  rw [h2, winCount_eq_card]
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
  refine ⟨by omega, ?_⟩
  rw [← hi.2]
  unfold window
  rw [List.take_take, min_eq_left hGJ]

end WinLLN

open WinLLN in
/-- **Marginalization**: if the windows of length `J` on `[a, b)` of a binary word `w` are `δ`-close to uniform, then for `G ≤ J` the windows of length `G`
are `(δ + (J - G)/N_G)`-close to uniform (`N_G = b + 1 - G - a` is the number of windows of length `G`; the windows of length `J` begin with windows of length `G`,
and the deviation comes from the `J - G` additional windows at the end). -/
theorem winClose_marginal {w : Word} (hw : ∀ s ∈ w, s = Letter.f ∨ s = Letter.t) {a b J G : ℕ}
    {δ : ℚ} (hGJ : G ≤ J) (h : WinClose w a b J δ) :
    WinClose w a b G (δ + ((J - G : ℕ) : ℚ) / ((b + 1 - G - a : ℕ) : ℚ)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, h2, ?_⟩
  set NJ := b + 1 - J - a with hNJ
  set NG := b + 1 - G - a with hNG
  have hNJpos : (0 : ℚ) < NJ := by exact_mod_cast (show 0 < NJ by omega)
  have hNGpos : (0 : ℚ) < NG := by exact_mod_cast (show 0 < NG by omega)
  have hdiff : ((J - G : ℕ) : ℚ) = NG - NJ := by
    rw [show NG = NJ + (J - G) by omega]; push_cast; ring
  have hNle : (NJ : ℚ) ≤ NG := by exact_mod_cast (show NJ ≤ NG by omega)
  set F : Word → Finset Word := fun u => (wordsOfLen J).filter (fun v => v.take G = u) with hF
  set S : Word → ℚ := fun u => ∑ v ∈ F u, (winCount w a b J v : ℚ) with hS
  have hmaps : ∀ v ∈ wordsOfLen J, v.take G ∈ wordsOfLen G := fun v hv => take_mem_of_le hGJ hv
  have F1 : ∑ u ∈ wordsOfLen G, S u = NJ := by
    simp only [hS, hF]
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
    exact_mod_cast sum_winCount hw a b J h2
  have F2 : ∀ u, S u ≤ (winCount w a b G u : ℚ) := fun u => by
    simp only [hS, hF]; exact_mod_cast sum_fiber_le hw hGJ h2 u
  have F3 : ∑ u ∈ wordsOfLen G, (winCount w a b G u : ℚ) = NG := by
    exact_mod_cast sum_winCount hw a b G h2
  have F4 : ∀ u ∈ wordsOfLen G, |S u / NJ - 1 / 2 ^ G| ≤
      ∑ v ∈ F u, |(winCount w a b J v : ℚ) / NJ - 1 / 2 ^ J| := by
    intro u hu
    have e : S u / NJ - 1 / 2 ^ G =
        ∑ v ∈ F u, ((winCount w a b J v : ℚ) / NJ - 1 / 2 ^ J) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_fiber_take hGJ hu, ← Finset.sum_div,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ _ two_ne_zero hGJ]
      field_simp
      simp only [hS]
      ring
    rw [e]
    exact Finset.abs_sum_le_sum_abs _ _
  have F5 : ∑ u ∈ wordsOfLen G, ∑ v ∈ F u, |(winCount w a b J v : ℚ) / NJ - 1 / 2 ^ J| ≤
      2 * δ := by
    simp only [hF]; rw [Finset.sum_fiberwise_of_maps_to hmaps]; exact h3
  have P : ∀ u ∈ wordsOfLen G, |(winCount w a b G u : ℚ) / NG - 1 / 2 ^ G| ≤
      |S u / NJ - 1 / 2 ^ G| + ((winCount w a b G u : ℚ) - S u) / NG +
        S u * (1 / NJ - 1 / NG) := by
    intro u _
    have hS0 : 0 ≤ S u := Finset.sum_nonneg (fun _ _ => by positivity)
    have hy : 0 ≤ ((winCount w a b G u : ℚ) - S u) / NG :=
      div_nonneg (by linarith [F2 u]) hNGpos.le
    have hz : 0 ≤ S u * (1 / NJ - 1 / NG) :=
      mul_nonneg hS0 (by rw [sub_nonneg]; exact one_div_le_one_div_of_le hNJpos hNle)
    have e : (winCount w a b G u : ℚ) / NG - 1 / 2 ^ G = (S u / NJ - 1 / 2 ^ G) +
        ((winCount w a b G u : ℚ) - S u) / NG - S u * (1 / NJ - 1 / NG) := by
      field_simp; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hz]
    have := abs_add_le (S u / NJ - 1 / 2 ^ G) (((winCount w a b G u : ℚ) - S u) / NG)
    rw [abs_of_nonneg hy] at this
    linarith
  have hsumF4 := (Finset.sum_le_sum F4).trans F5
  calc ∑ u ∈ wordsOfLen G, |(winCount w a b G u : ℚ) / NG - 1 / 2 ^ G|
      ≤ ∑ u ∈ wordsOfLen G, (|S u / NJ - 1 / 2 ^ G| +
          ((winCount w a b G u : ℚ) - S u) / NG + S u * (1 / NJ - 1 / NG)) :=
        Finset.sum_le_sum P
    _ = ∑ u ∈ wordsOfLen G, |S u / NJ - 1 / 2 ^ G| +
          (∑ u ∈ wordsOfLen G, (winCount w a b G u : ℚ) - ∑ u ∈ wordsOfLen G, S u) / NG +
          (∑ u ∈ wordsOfLen G, S u) * (1 / NJ - 1 / NG) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
          Finset.sum_sub_distrib]
    _ ≤ 2 * δ + (NG - NJ) / NG + NJ * (1 / NJ - 1 / NG) := by
        rw [F3, F1]; linarith
    _ = 2 * (δ + ((J - G : ℕ) : ℚ) / NG) := by
        rw [hdiff]; field_simp; ring

namespace WinLLN

/-- A window is an infix of the original word. -/
lemma window_infix (u : Word) (i m : ℕ) : window u i m <:+: u :=
  (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

end WinLLN

open WinLLN in
/-- **Occurrences inside windows of length `G`**: if the windows of length `G` on `[a, b)` are `δ`-close to uniform, then the proportion of these windows that do not contain the binary word
`v` (of length `m`) as an infix is at most `(1 - 2^{-m})^{⌊G/m⌋} + 2δ` (for uniform windows the bound is `card_noOcc_le`,
and the difference from the empirical distribution is bounded by the total variation distance; the assumption that `w` is binary is not needed). -/
theorem noOcc_window_frac {w : Word} {a b G : ℕ} {δ : ℚ} {v : Word}
    (hv : v ∈ wordsOfLen v.length) (h : WinClose w a b G δ) :
    (((Finset.range (b + 1 - G - a)).filter (fun i => ¬ v <:+: window w (a + i) G)).card : ℚ) ≤
      ((1 - 1 / 2 ^ v.length) ^ (G / v.length) + 2 * δ) * ((b + 1 - G - a : ℕ) : ℚ) := by
  obtain ⟨h1, -, h3⟩ := h
  set N := b + 1 - G - a with hN
  have hNpos : (0 : ℚ) < N := by exact_mod_cast (show 0 < N by omega)
  set A := (wordsOfLen G).filter (fun u => ¬ v <:+: u) with hA
  set B := (wordsOfLen G).filter (fun u => v <:+: u) with hB
  set bad := (Finset.range N).filter (fun i => ¬ v <:+: window w (a + i) G) with hbad
  set good := (Finset.range N).filter (fun i => window w (a + i) G ∈ B) with hgood
  -- bad starts and good starts are disjoint
  have hdisj : Disjoint bad good := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [hbad, Finset.mem_filter] at hi
    rw [hgood, Finset.mem_filter, hB, Finset.mem_filter] at hi'
    exact hi.2 hi'.2.2
  have hunion : bad.card + good.card ≤ N := by
    rw [← Finset.card_union_of_disjoint hdisj]
    refine (Finset.card_le_card ?_).trans (Finset.card_range N).le
    exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  -- the number of good starts is the sum of the numbers of occurrences of the words of `B`
  have hgood_eq : good.card = ∑ u ∈ B, winCount w a b G u := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun i => window w (a + i) G) (t := B) (by
      intro i hi
      rw [Finset.mem_coe, hgood, Finset.mem_filter] at hi
      exact hi.2)]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [winCount_eq_card, hgood, Finset.filter_filter]
    apply congrArg
    apply Finset.filter_congr
    intro i _
    exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hu, h⟩⟩
  -- restrict the total variation distance to `B`
  have hTVB : ∑ u ∈ B, (1 / 2 ^ G - (winCount w a b G u : ℚ) / N) ≤ 2 * δ := by
    refine le_trans ?_ h3
    refine (Finset.sum_le_sum (fun u _ => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _))
    rw [abs_sub_comm]
    exact le_abs_self _
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div] at hTVB
  -- `#A + #B = 2^G` and `#A ≤ 2^G (1 - 2^{-m})^{⌊G/m⌋}`
  have hAB : (A.card : ℚ) + B.card = 2 ^ G := by
    have := Finset.card_filter_add_card_filter_not (s := wordsOfLen G) (fun u => ¬ v <:+: u)
    rw [card_words] at this
    simp only [not_not] at this
    exact_mod_cast this
  have hAle : (A.card : ℚ) ≤ 2 ^ G * (1 - 1 / 2 ^ v.length) ^ (G / v.length) := by
    classical
    have hsub : A ⊆ (wordsOfLen G).filter
        (fun u => ∀ i, 0 ≤ i → i + v.length ≤ G → window u i v.length ≠ v) := by
      intro u hu
      rw [hA, Finset.mem_filter] at hu
      rw [Finset.mem_filter]
      refine ⟨hu.1, fun i _ _ heq => hu.2 ?_⟩
      rw [← heq]
      exact window_infix u i v.length
    have h2 := card_noOcc_le G 0 G hv le_rfl
    rw [Nat.sub_zero] at h2
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) h2
  -- conclusion
  have hgoodQ : (good.card : ℚ) = ∑ u ∈ B, (winCount w a b G u : ℚ) := by
    rw [hgood_eq, Nat.cast_sum]
  have hunionQ : (bad.card : ℚ) + good.card ≤ N := by exact_mod_cast hunion
  have hsumB : (B.card : ℚ) / 2 ^ G * N - 2 * δ * N ≤ ∑ u ∈ B, (winCount w a b G u : ℚ) := by
    have e := mul_le_mul_of_nonneg_right hTVB hNpos.le
    rw [sub_mul, div_mul_cancel₀ _ hNpos.ne'] at e
    have : (B.card : ℚ) / 2 ^ G * N = B.card * (1 / 2 ^ G) * N := by ring
    linarith
  have hfin : (A.card : ℚ) / 2 ^ G ≤ (1 - 1 / 2 ^ v.length) ^ (G / v.length) := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hBA : (B.card : ℚ) / 2 ^ G = 1 - A.card / 2 ^ G := by
    field_simp; linarith
  rw [hBA] at hsumB
  nlinarith

end Collatz.Arctic
