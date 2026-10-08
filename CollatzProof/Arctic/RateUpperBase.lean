/-
Ingredients of the block bound for each component: deterministic lemmas used in the step "Block bound" of the proof of
Lemma 6.5. The definitions (`fmax`, `window`, `winCount`, `WinClose`) are in `Window.lean` and
`RateDefs.lean`. The main statement (`block_upper`) is in `RateUpper.lean`.

* Properties of `natOr0`: monotone, commutes with sums (max), and a product (+) is at most the sum.
* **Subadditivity** `fmax_append_le`: `fmax(uv) ≤ fmax(u) + fmax(v)` (the largest entry of a max-plus product is at most the sum of the largest entries
  of the factors; since `-∞` is read as 0, this also holds when the product is `-∞`). `fmax_le_length`: `fmax(w) ≤ M |w|`.
* Windows: `window_add` (concatenation), lengths of windows, windows of a word in `f` and `t` only lie in `wordsOfLen J` (`window_mem_wordsOfLen`).
* Averaging over shifts `shift_sum_le` (a telescoping sum) and its consequence `block_sum_le`: `K` times the `fmax` of an interval of length `n` is at most
  the sum of the `fmax` of the windows of length `K` inside the interval plus `2MK²` (the averaging over the offsets `r ∈ [0, K)`,
  written as a telescoping sum of `F(i) ≤ fmax(window i) + F(i + K)`; no bijection is used).
* Counting windows `sum_windows_eq` (recount a sum over windows by the number of occurrences of each word) and the bound `freq_sum_le` from the total variation distance.
-/
import CollatzProof.Arctic.RateDefs
import CollatzProof.Arctic.Bridge

namespace Collatz.Arctic

open Arc

/-! ### Properties of `natOr0` -/

lemma unbotD0_mono {x y : WithBot ℕ} (h : x ≤ y) : x.unbotD 0 ≤ y.unbotD 0 := by
  induction x using WithBot.recBotCoe with
  | bot => simp
  | coe m =>
    induction y using WithBot.recBotCoe with
    | bot => simp at h
    | coe n => simpa using h

lemma natOr0_mono {a b : Arc} (h : a ≤ b) : natOr0 a ≤ natOr0 b := unbotD0_mono h

lemma natOr0_zero : natOr0 (0 : Arc) = 0 := rfl

lemma natOr0_fin (v : ℕ) : natOr0 (fin v) = v := rfl

lemma natOr0_add (a b : Arc) : natOr0 (a + b) = max (natOr0 a) (natOr0 b) := by
  unfold natOr0
  rw [val_add]
  induction (val a) using WithBot.recBotCoe with
  | bot => simp
  | coe m =>
    induction (val b) using WithBot.recBotCoe with
    | bot => simp
    | coe n =>
      rw [← WithBot.coe_max, WithBot.unbotD_coe, WithBot.unbotD_coe, WithBot.unbotD_coe]

lemma natOr0_mul_le (a b : Arc) : natOr0 (a * b) ≤ natOr0 a + natOr0 b := by
  unfold natOr0
  rw [val_mul]
  induction (val a) using WithBot.recBotCoe with
  | bot => simp
  | coe m =>
    induction (val b) using WithBot.recBotCoe with
    | bot => simp
    | coe n => simp [← WithBot.coe_add]

/-- If the finite values are at most `M`, then `natOr0 ≤ M` (`-∞` as 0). -/
lemma natOr0_le_of {a : Arc} {M : ℕ} (h : ∀ v, a = fin v → v ≤ M) : natOr0 a ≤ M := by
  by_cases hb : val a = ⊥
  · unfold natOr0; rw [hb]; simp
  · obtain ⟨v, rfl⟩ := (val_ne_bot_iff a).mp hb
    rw [natOr0_fin]; exact h v rfl

lemma natOr0_sum_le {ι : Type*} (s : Finset ι) (f : ι → Arc) {n : ℕ}
    (h : ∀ i ∈ s, natOr0 (f i) ≤ n) : natOr0 (∑ i ∈ s, f i) ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [natOr0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, natOr0_add]
    exact max_le (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma natOr0_entry_le {D : ℕ} (P : AMat D) (i j : Fin D) : natOr0 (P i j) ≤ natOr0 (maxEnt P) :=
  natOr0_mono ((le_sum_of_mem (s := Finset.univ) (fun j => P i j) (Finset.mem_univ j)).trans
    (le_sum_of_mem (s := Finset.univ) (fun i => ∑ j, P i j) (Finset.mem_univ i)))

lemma natOr0_maxEnt_le {D : ℕ} (P : AMat D) {n : ℕ} (h : ∀ i j, natOr0 (P i j) ≤ n) :
    natOr0 (maxEnt P) ≤ n :=
  natOr0_sum_le _ _ (fun i _ => natOr0_sum_le _ _ (fun j _ => h i j))

/-- The largest entry of a max-plus product is at most the sum of the largest entries of the factors (`-∞` read as 0). -/
lemma maxEnt_mul_le {D : ℕ} (P Q : AMat D) :
    natOr0 (maxEnt (P * Q)) ≤ natOr0 (maxEnt P) + natOr0 (maxEnt Q) := by
  refine natOr0_maxEnt_le _ (fun i j => ?_)
  rw [Matrix.mul_apply]
  exact natOr0_sum_le _ _ (fun k _ => (natOr0_mul_le _ _).trans
    (add_le_add (natOr0_entry_le P i k) (natOr0_entry_le Q k j)))

/-! ### Subadditivity of `fmax` -/

/-- **Subadditivity**: `fmax(uv) ≤ fmax(u) + fmax(v)`. -/
theorem fmax_append_le {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (u v : Word) :
    fmax A C (u ++ v) ≤ fmax A C u + fmax A C v := by
  unfold fmax
  rw [ev_append]
  exact maxEnt_mul_le _ _

lemma fmax_nil {D : ℕ} (A : Interp D) (C : Finset (Fin D)) : fmax A C [] = 0 := by
  refine Nat.le_zero.mp (natOr0_maxEnt_le _ (fun i j => ?_))
  simp only [ev, List.map_nil, List.prod_nil, Matrix.one_apply]
  split_ifs <;> rfl

lemma fmax_singleton_le {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (M : ℕ)
    (hM : ∀ s i j v, A s i j = Arc.fin v → v ≤ M) (s : Letter) : fmax A C [s] ≤ M := by
  refine natOr0_maxEnt_le _ (fun i j => ?_)
  simp only [ev, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, restrictI]
  split_ifs
  · exact natOr0_le_of (hM s i j)
  · rw [natOr0_zero]; exact Nat.zero_le _

/-- If the finite entries are at most `M`, then `fmax(w) ≤ M |w|`. -/
lemma fmax_le_length {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (M : ℕ)
    (hM : ∀ s i j v, A s i j = Arc.fin v → v ≤ M) (w : Word) : fmax A C w ≤ M * w.length := by
  induction w with
  | nil => rw [fmax_nil]; exact Nat.zero_le _
  | cons s w ih =>
    have h := fmax_append_le A C [s] w
    have h1 := fmax_singleton_le A C M hM s
    rw [List.singleton_append] at h
    rw [List.length_cons, Nat.mul_succ]
    omega

/-! ### Windows -/

lemma window_add (w : Word) (a i j : ℕ) :
    window w a (i + j) = window w a i ++ window w (a + i) j := by
  unfold window
  rw [List.take_add, List.drop_drop]

lemma length_window_le (w : Word) (a J : ℕ) : (window w a J).length ≤ J := by
  unfold window; rw [List.length_take]; exact min_le_left _ _

lemma length_window (w : Word) {a J : ℕ} (h : a + J ≤ w.length) : (window w a J).length = J := by
  unfold window; rw [List.length_take, List.length_drop]; omega

lemma mem_of_mem_window {w : Word} {a J : ℕ} {s : Letter} (h : s ∈ window w a J) : s ∈ w :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

lemma mem_wordsOfLen_of {J : ℕ} {v : Word} (hl : v.length = J)
    (hv : ∀ s ∈ v, s = Letter.f ∨ s = Letter.t) : v ∈ wordsOfLen J := by
  subst hl
  unfold wordsOfLen
  rw [Finset.mem_image]
  refine ⟨fun i => decide (v.get i = Letter.t), Finset.mem_univ _, ?_⟩
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn, List.get_eq_getElem]
  rcases hv (v[n]) (List.getElem_mem h2) with h | h <;> simp [h]

lemma length_of_mem_wordsOfLen {J : ℕ} {v : Word} (h : v ∈ wordsOfLen J) : v.length = J := by
  unfold wordsOfLen at h
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp h
  simp

lemma window_mem_wordsOfLen {w : Word} (hw : ∀ s ∈ w, s = Letter.f ∨ s = Letter.t) {a J : ℕ}
    (h : a + J ≤ w.length) : window w a J ∈ wordsOfLen J :=
  mem_wordsOfLen_of (length_window w h) (fun s hs => hw s (mem_of_mem_window hs))

/-! ### Averaging over shifts -/

/-- Averaging over shifts (telescoping sum): if `F i ≤ g i + F (i + K)` (`i < N`), then
`∑_{i<K} F i ≤ ∑_{i<N} g i + ∑_{i<K} F (N + i)`. -/
lemma shift_sum_le (F g : ℕ → ℕ) (K N : ℕ) (h : ∀ i < N, F i ≤ g i + F (i + K)) :
    ∑ i ∈ Finset.range K, F i ≤
      ∑ i ∈ Finset.range N, g i + ∑ i ∈ Finset.range K, F (N + i) := by
  have h1 := Finset.sum_range_add F K N
  have h2 := Finset.sum_range_add F N K
  have h3 : ∑ i ∈ Finset.range N, F i ≤ ∑ i ∈ Finset.range N, (g i + F (i + K)) :=
    Finset.sum_le_sum (fun i hi => h i (Finset.mem_range.mp hi))
  rw [Finset.sum_add_distrib] at h3
  have h4 : ∑ i ∈ Finset.range N, F (i + K) = ∑ i ∈ Finset.range N, F (K + i) :=
    Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])
  rw [Nat.add_comm K N] at h1
  omega

/-- **Block sum of an interval**: if `K ≤ n`, then `K` times the `fmax` of an interval of length `n` is at most the sum of the `fmax` of the windows
of length `K` inside the interval (starting at `a, …, a + n - K`) plus `2 M K²`. -/
lemma block_sum_le {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (M : ℕ)
    (hM : ∀ s i j v, A s i j = Arc.fin v → v ≤ M) (w : Word) (a n K : ℕ) (hK : K ≤ n) :
    K * fmax A C (window w a n) ≤
      ∑ i ∈ Finset.range (n + 1 - K), fmax A C (window w (a + i) K) + 2 * (M * K * K) := by
  set F : ℕ → ℕ := fun i => fmax A C (window w (a + i) (n - i)) with hF
  set N := n + 1 - K with hN
  -- subadditivity: `F i ≤ fmax(window i) + F (i + K)`
  have hstep : ∀ i < N, F i ≤ fmax A C (window w (a + i) K) + F (i + K) := by
    intro i hi
    have e1 : n - i = K + (n - (i + K)) := by omega
    have e2 : a + i + K = a + (i + K) := by omega
    simp only [hF]
    rw [e1, window_add, e2]
    exact fmax_append_le A C _ _
  have hsh := shift_sum_le F (fun i => fmax A C (window w (a + i) K)) K N hstep
  -- the leftover piece at the left end: `F 0 ≤ MK + F i` (`i < K`)
  have hlo : ∀ i ∈ Finset.range K, F 0 ≤ M * K + F i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have e1 : n - 0 = i + (n - i) := by omega
    have := fmax_append_le A C (window w a i) (window w (a + i) (n - i))
    have h2 := (fmax_le_length A C M hM (window w a i)).trans
      (Nat.mul_le_mul_left M ((length_window_le w a i).trans hi'.le))
    simp only [hF, Nat.add_zero]
    rw [e1, window_add]
    omega
  -- the leftover piece at the right end: `F (N + i) ≤ MK`
  have hhi : ∀ i ∈ Finset.range K, F (N + i) ≤ M * K := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact (fmax_le_length A C M hM _).trans (Nat.mul_le_mul_left M
      ((length_window_le w _ _).trans (by omega)))
  have s1 : K * F 0 ≤ ∑ i ∈ Finset.range K, (M * K + F i) := by
    have e : ∑ _i ∈ Finset.range K, F 0 = K * F 0 := by simp
    rw [← e]
    exact Finset.sum_le_sum hlo
  have s2 : ∑ i ∈ Finset.range K, F (N + i) ≤ ∑ i ∈ Finset.range K, M * K :=
    Finset.sum_le_sum hhi
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at s1
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at s2
  have e0 : F 0 = fmax A C (window w a n) := by simp [hF]
  rw [← e0]
  nlinarith

/-! ### Counting windows -/

lemma length_winStarts (a b J : ℕ) : (winStarts a b J).length = b + 1 - J - a := by
  simp [winStarts]

lemma mem_winStarts {a b J i : ℕ} : i ∈ winStarts a b J ↔ a ≤ i ∧ i + J ≤ b ∧ a + J ≤ b := by
  simp only [winStarts, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · rintro ⟨h1, h2, -⟩; exact ⟨i - a, by omega, by omega⟩

/-- The number of occurrences of a window is the cardinality of a finite set of start indices (offsets from `a`). -/
lemma winCount_eq_card (w : Word) (a b J : ℕ) (v : Word) :
    winCount w a b J v =
      ((Finset.range (b + 1 - J - a)).filter (fun i => window w (a + i) J = v)).card := by
  unfold winCount winStarts
  rw [List.filter_map, List.length_map, Finset.card_def, Finset.filter_val, Finset.range_val,
    ← Multiset.coe_range, Multiset.filter_coe, Multiset.coe_card]
  rfl

/-- Recount a sum over the windows of an interval by the number of occurrences of each word (when all windows lie in `S`). -/
lemma sum_windows_eq {R : Type*} [CommSemiring R] (h : Word → R) (w : Word) (a b J : ℕ)
    (S : Finset Word) (hS : ∀ i < b + 1 - J - a, window w (a + i) J ∈ S) :
    ∑ i ∈ Finset.range (b + 1 - J - a), h (window w (a + i) J) =
      ∑ v ∈ S, (winCount w a b J v : R) * h v := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := S) (g := fun i => window w (a + i) J)
    (fun i hi => hS i (Finset.mem_range.mp hi))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const,
    nsmul_eq_mul, winCount_eq_card]

/-- If the empirical distribution is within `2δ` of `p` (in the sum of absolute differences), then the weighted sum with `0 ≤ h ≤ B` is at most
`N (∑ p h + 2 δ B)`. -/
lemma freq_sum_le (S : Finset Word) (c h : Word → ℚ) (N p δ B : ℚ) (hN : 0 < N) (hB0 : 0 ≤ B)
    (h0 : ∀ v ∈ S, 0 ≤ h v) (hB : ∀ v ∈ S, h v ≤ B)
    (hTV : ∑ v ∈ S, |c v / N - p| ≤ 2 * δ) :
    ∑ v ∈ S, c v * h v ≤ N * (∑ v ∈ S, p * h v + 2 * δ * B) := by
  have e : ∀ v, c v * h v = N * (p * h v) + N * ((c v / N - p) * h v) := by
    intro v; field_simp; ring
  have hle : ∀ v ∈ S, (c v / N - p) * h v ≤ |c v / N - p| * B := fun v hv =>
    (mul_le_mul_of_nonneg_right (le_abs_self _) (h0 v hv)).trans
      (mul_le_mul_of_nonneg_left (hB v hv) (abs_nonneg _))
  have s1 : ∑ v ∈ S, (c v / N - p) * h v ≤ 2 * δ * B := by
    calc ∑ v ∈ S, (c v / N - p) * h v ≤ ∑ v ∈ S, |c v / N - p| * B := Finset.sum_le_sum hle
      _ = (∑ v ∈ S, |c v / N - p|) * B := by rw [Finset.sum_mul]
      _ ≤ 2 * δ * B := mul_le_mul_of_nonneg_right hTV hB0
  calc ∑ v ∈ S, c v * h v
      = ∑ v ∈ S, (N * (p * h v) + N * ((c v / N - p) * h v)) := Finset.sum_congr rfl (fun v _ => e v)
    _ = N * ∑ v ∈ S, p * h v + N * ∑ v ∈ S, (c v / N - p) * h v := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ N * ∑ v ∈ S, p * h v + N * (2 * δ * B) :=
        add_le_add_right (mul_le_mul_of_nonneg_left s1 hN.le) _
    _ = N * (∑ v ∈ S, p * h v + 2 * δ * B) := by ring

end Collatz.Arctic
