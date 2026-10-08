/-
Parts of the proof of Lemma 6.5 of the paper (upper bound from window frequencies), (1): windows and paths.
Section 6.3. The main theorem is in `Upper.lean`, the transport in `UpperCarry.lean`.

* Windows: `winClose_mono` (monotone in `δ`), `occ_of_winClose` (**occurrence**: if the window frequencies of length `J ≥ |u*|` are closer than
  `2^{-J}/2` to uniform, the interval contains an occurrence of `u*`; if no window of length `J` begins with `u*`, the term of such a word
  alone makes the total variation distance `2^{-J}/2`). The marginalization of window frequencies is `winClose_marginal` in `WindowLLN3.lean`.
* **Path lemma** (the path of maximal weight that ends at `b`, in the proof of Lemma 6.5): `path_of_vecAfter` (a finite value of the index `b` in `u ⊗ A_y`
  is attained by the sum of the weights of a path that starts at a finite entry of `u` and whose steps have finite entries), `sum_le_ev`, `sum_le_ev_window`
  (the sum of the weights of a path is at most the entry of the product over the window; applied to `restrictI C A`, the weight of a path that stays in the component `C` is at most `fmax`).
* The support along a path `supp_path`, reachability `reach_path`, and the number `reachCard` of reachable indices (it does not increase along the path and
  strictly decreases when the path leaves a component; a potential used instead of the DAG of components).
-/
import CollatzProof.Arctic.RateUpper
import CollatzProof.Arctic.ConfigLemmas

namespace Collatz.Arctic.Upper

open Collatz.Arctic Collatz.Arctic.MinIdeal Arc

variable {D : ℕ}



/-! ### Digit words of length `J` -/

lemma digits_of_mem_wordsOfLen {J : ℕ} {v : Word} (h : v ∈ wordsOfLen J) : IsDigits v := by
  unfold wordsOfLen at h
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp h
  intro s hs
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  by_cases hg : g i <;> simp [hg]

lemma mem_wordsOfLen_iff {J : ℕ} {v : Word} : v ∈ wordsOfLen J ↔ v.length = J ∧ IsDigits v :=
  ⟨fun h => ⟨length_of_mem_wordsOfLen h, digits_of_mem_wordsOfLen h⟩,
    fun h => mem_wordsOfLen_of h.1 h.2⟩

/-- The hypothesis on window frequencies is monotone in `δ`. -/
lemma winClose_mono {w : Word} {a b J : ℕ} {δ δ' : ℚ} (h : WinClose w a b J δ) (hδ : δ ≤ δ') :
    WinClose w a b J δ' :=
  ⟨h.1, h.2.1, h.2.2.trans (by linarith)⟩

/-- **Occurrence**: if the window frequencies of length `J ≥ |u*|` are closer than `2^{-J}/2` to uniform, the interval contains an occurrence of `u*`
(if no window of length `J` begins with `u*`, the term of such a word alone makes the total variation distance `2^{-J}/2`). -/
theorem occ_of_winClose {w : Word} {a b J : ℕ} {δ : ℚ} {us : Word} (hus : IsDigits us)
    (hJ : us.length ≤ J) (hδ : 2 * δ < 1 / 2 ^ J) (hc : WinClose w a b J δ) :
    ∃ i, a ≤ i ∧ i + J ≤ b ∧ window w i us.length = us := by
  obtain ⟨hab, hbw, hTV⟩ := hc
  set v₀ := us ++ List.replicate (J - us.length) Letter.f
  have hv₀ : v₀ ∈ wordsOfLen J := by
    rw [mem_wordsOfLen_iff]
    refine ⟨by simp [v₀]; omega, fun s hs => ?_⟩
    rcases List.mem_append.mp hs with h | h
    · exact hus s h
    · exact Or.inl (List.eq_of_mem_replicate h)
  by_contra hno
  push Not at hno
  have h0 : winCount w a b J v₀ = 0 := by
    unfold winCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro i hi hwi
    obtain ⟨h1, h2, -⟩ := mem_winStarts.mp hi
    have hwi' : window w i J = v₀ := by simpa using hwi
    apply hno i h1 h2
    have : window w i us.length = (window w i J).take us.length := by
      unfold window; rw [List.take_take, min_eq_left hJ]
    rw [this, hwi', List.take_left' rfl]
  have hle := Finset.single_le_sum (f := fun v =>
    |((winCount w a b J v : ℚ) / ((b + 1 - J - a : ℕ) : ℚ)) - 1 / 2 ^ J|)
    (fun v _ => abs_nonneg _) hv₀
  simp only [h0, Nat.cast_zero, zero_div, zero_sub, abs_neg] at hle
  rw [abs_of_pos (by positivity)] at hle
  linarith



open Collatz.Arctic Collatz.Arctic.MinIdeal Arc

variable {D : ℕ}

lemma fin_inj {m n : ℕ} (h : Arc.fin m = Arc.fin n) : m = n := by
  have := congrArg Arc.val h
  simp only [val_fin] at this
  exact_mod_cast this

lemma fin_ne_zero (n : ℕ) : Arc.fin n ≠ 0 := by
  intro h
  have := congrArg Arc.val h
  simp at this

lemma eq_fin_of_ne_zero {a : Arc} (h : a ≠ 0) : a = Arc.fin (natOr0 a) := by
  obtain ⟨n, rfl⟩ := (val_ne_bot_iff a).mp ((Arc.ne_zero_iff_val a).mp h)
  rfl

/-! ### Paths -/

/-- The sum of the weights of a path is at most the entry of the product of the word (each step of the path has a finite entry). -/
lemma sum_le_ev (B : Interp D) : ∀ (y : Word) (p : ℕ → Fin D) (g : ℕ → ℕ),
    (∀ i < y.length, B (y.getD i Letter.f) (p i) (p (i + 1)) = Arc.fin (g i)) →
    Arc.fin (∑ i ∈ Finset.range y.length, g i) ≤ ev B y (p 0) (p y.length)
  | [], p, g, _ => by
    simp only [List.length_nil, Finset.range_zero, Finset.sum_empty]
    simp [ev]; rfl
  | s :: y, p, g, h => by
    rw [ev_cons, Matrix.mul_apply]
    have h0 : B s (p 0) (p 1) = Arc.fin (g 0) := by simpa using h 0 (by simp)
    have ih := sum_le_ev B y (fun n => p (n + 1)) (fun n => g (n + 1)) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa using this)
    simp only [List.length_cons] at ih ⊢
    calc Arc.fin (∑ i ∈ Finset.range (y.length + 1), g i)
        = Arc.fin (g 0) * Arc.fin (∑ i ∈ Finset.range y.length, g (i + 1)) := by
          rw [fin_mul_fin, Finset.sum_range_succ', Nat.add_comm]
      _ ≤ B s (p 0) (p 1) * ev B y (p 1) (p (y.length + 1)) := mul_le_mul_of_le (le_of_eq h0.symm) ih
      _ ≤ ∑ k, B s (p 0) k * ev B y k (p (y.length + 1)) :=
          le_sum_of_mem (fun k => B s (p 0) k * ev B y k (p (y.length + 1))) (Finset.mem_univ _)

/-- A finite entry of the product of a word is attained by the sum of the weights of some path. -/
lemma path_of_ev (B : Interp D) : ∀ (y : Word) (i j : Fin D), ev B y i j ≠ 0 →
    ∃ p : ℕ → Fin D, ∃ g : ℕ → ℕ, p 0 = i ∧ p y.length = j ∧
      (∀ k < y.length, B (y.getD k Letter.f) (p k) (p (k + 1)) = Arc.fin (g k)) ∧
      ev B y i j = Arc.fin (∑ k ∈ Finset.range y.length, g k)
  | [], i, j, h => by
    have hij : i = j := by
      by_contra hne
      apply h
      simp [ev, hne]
    subst hij
    refine ⟨fun _ => i, fun _ => 0, rfl, rfl, fun k hk => by simp at hk, ?_⟩
    simp [ev]; rfl
  | s :: y, i, j, h => by
    rw [ev_cons, Matrix.mul_apply] at h ⊢
    obtain ⟨k0, -, hk0⟩ := (Arc.sum_ne_zero_iff _ _).mp h
    obtain ⟨k, -, hk⟩ := exists_eq_sum ⟨k0, Finset.mem_univ _⟩
      (fun k => B s i k * ev B y k j)
    rw [← hk] at h ⊢
    have h2 := (Arc.mul_ne_zero_iff _ _).mp h
    obtain ⟨p', g', hp0, hpl, hstep, hval⟩ := path_of_ev B y k j h2.2
    set x := natOr0 (B s i k) with hxdef
    have hx : B s i k = Arc.fin x := eq_fin_of_ne_zero h2.1
    refine ⟨fun n => Nat.casesOn n i p', fun n => Nat.casesOn n x g',
      rfl, by simpa using hpl, ?_, ?_⟩
    · intro n hn
      cases n with
      | zero => simpa [hp0] using hx
      | succ n =>
        have := hstep n (by simp at hn; omega)
        simpa using this
    · simp only [List.length_cons]
      rw [hval, hx, fin_mul_fin, Finset.sum_range_succ']
      congr 1
      exact Nat.add_comm _ _

/-- **Path lemma**: if the value of the index `b` in `u ⊗ A_y` is a finite `v`, there is a path that starts at a finite entry of `u`, whose steps have finite entries,
and whose sum of weights is `v`. -/
theorem path_of_vecAfter (u : Fin D → Arc) (B : Interp D) (y : Word) (b : Fin D) (v : ℕ)
    (h : vecAfter u B y b = Arc.fin v) :
    ∃ p : ℕ → Fin D, ∃ g : ℕ → ℕ, ∃ v0 : ℕ, u (p 0) = Arc.fin v0 ∧ p y.length = b ∧
      (∀ k < y.length, B (y.getD k Letter.f) (p k) (p (k + 1)) = Arc.fin (g k)) ∧
      v = v0 + ∑ k ∈ Finset.range y.length, g k := by
  unfold vecAfter at h
  rw [Matrix.vecMul, dotProduct] at h
  have hne : (∑ i, u i * ev B y i b) ≠ 0 := by rw [h]; exact fin_ne_zero v
  obtain ⟨i0, -, hi0⟩ := (Arc.sum_ne_zero_iff _ _).mp hne
  obtain ⟨i, -, hi⟩ := exists_eq_sum ⟨i0, Finset.mem_univ _⟩ (fun i => u i * ev B y i b)
  rw [← hi] at h hne
  have h2 := (Arc.mul_ne_zero_iff _ _).mp hne
  obtain ⟨p, g, hp0, hpl, hstep, hval⟩ := path_of_ev B y i b h2.2
  refine ⟨p, g, natOr0 (u i), by rw [hp0]; exact eq_fin_of_ne_zero h2.1, hpl, hstep, ?_⟩
  rw [hval, eq_fin_of_ne_zero h2.1, fin_mul_fin] at h
  exact (fin_inj h).symm

/-! ### Letters of words and windows -/

lemma getD_take {w : Word} {T k : ℕ} (hk : k < T) : (w.take T).getD k Letter.f = w.getD k Letter.f := by
  simp [List.getD_eq_getElem?_getD, hk]

lemma getD_window {w : Word} {a n k : ℕ} (hk : k < n) :
    (window w a n).getD k Letter.f = w.getD (a + k) Letter.f := by
  simp [window, List.getD_eq_getElem?_getD, hk, List.getElem?_drop]

lemma getD_digit {w : Word} (hw : IsDigits w) (k : ℕ) :
    w.getD k Letter.f = Letter.f ∨ w.getD k Letter.f = Letter.t := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hk : k < w.length
  · rw [List.getElem?_eq_getElem hk, Option.getD_some]
    exact hw _ (List.getElem_mem hk)
  · rw [List.getElem?_eq_none (by omega)]
    exact Or.inl rfl

lemma take_add_window (w : Word) (i n : ℕ) : w.take (i + n) = w.take i ++ window w i n :=
  List.take_add

/-- Weight of a path over a window: if each step in the interval `[i, i + n)` has a finite entry of `B`, the sum is at most the entry of the product over the window. -/
lemma sum_le_ev_window (B : Interp D) (w : Word) (p : ℕ → Fin D) (g : ℕ → ℕ) {i n : ℕ}
    (hn : i + n ≤ w.length)
    (h : ∀ k < n, B (w.getD (i + k) Letter.f) (p (i + k)) (p (i + k + 1)) = Arc.fin (g (i + k))) :
    Arc.fin (∑ k ∈ Finset.range n, g (i + k)) ≤ ev B (window w i n) (p i) (p (i + n)) := by
  have hl : (window w i n).length = n := length_window w hn
  have := sum_le_ev B (window w i n) (fun k => p (i + k)) (fun k => g (i + k)) (fun k hk => by
    rw [hl] at hk
    rw [getD_window hk]
    exact h k hk)
  simpa [hl] using this


/-! ### Supports and reachability along a path -/

lemma ne_zero_of_fin_le {n : ℕ} {a : Arc} (h : Arc.fin n ≤ a) : a ≠ 0 := by
  intro ha
  rw [ha, le_iff_val] at h
  simp at h

/-- A path that starts at a finite entry of `u` and whose steps in `[0, T)` have finite entries. -/
def IsPath (u : Fin D → Arc) (A : Interp D) (w : Word) (T : ℕ) (p : ℕ → Fin D) : Prop :=
  u (p 0) ≠ 0 ∧ ∀ k < T, A (w.getD k Letter.f) (p k) (p (k + 1)) ≠ 0

lemma path_ev_ne {u : Fin D → Arc} {A : Interp D} {w : Word} {T : ℕ} {p : ℕ → Fin D}
    (hp : IsPath u A w T p) (hT : T ≤ w.length) {i n : ℕ} (hin : i + n ≤ T) :
    ev A (window w i n) (p i) (p (i + n)) ≠ 0 :=
  ne_zero_of_fin_le (sum_le_ev_window A w p (fun k => natOr0 (A (w.getD k Letter.f) (p k) (p (k + 1))))
    (by omega) (fun k hk => eq_fin_of_ne_zero (hp.2 (i + k) (by omega))))

/-- At each time, the index of the path lies in the support of the value vector at that time. -/
lemma supp_path {u : Fin D → Arc} {A : Interp D} {w : Word} {T : ℕ} {p : ℕ → Fin D}
    (hp : IsPath u A w T p) (hT : T ≤ w.length) : ∀ i ≤ T, p i ∈ suppV (vecAfter u A (w.take i))
  | 0, _ => by
    have : vecAfter u A (w.take 0) = u := by simp [vecAfter, ev]
    rw [this]; exact hp.1
  | i + 1, hi => by
    rw [take_add_window, vecAfter_append, suppV_vecAfter]
    exact ⟨p i, supp_path hp hT i (by omega), path_ev_ne hp hT (i := i) (n := 1) (by omega)⟩

/-- A path over a digit word gives reachability in the graph of the letters. -/
lemma reach_path {u : Fin D → Arc} {A : Interp D} {w : Word} {T : ℕ} {p : ℕ → Fin D}
    (hw : IsDigits w) (hp : IsPath u A w T p) {i j : ℕ} (hij : i ≤ j) (hjT : j ≤ T) :
    Reach (B0 A) (B1 A) (p i) (p j) := by
  induction j, hij using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ j hij ih =>
    refine Relation.ReflTransGen.tail (ih (by omega)) ?_
    have hs := hp.2 j (by omega)
    rcases getD_digit hw j with h | h
    · left; show A Letter.f (p j) (p (j + 1)) ≠ 0; rwa [← h]
    · right; show A Letter.t (p j) (p (j + 1)) ≠ 0; rwa [← h]

open Classical in
/-- The number of indices reachable from the index `x` (it does not increase along a path and strictly decreases when the path leaves a component). -/
noncomputable def reachCard (A : Interp D) (x : Fin D) : ℕ :=
  (Finset.univ.filter (fun k => Reach (B0 A) (B1 A) x k)).card

open Classical in
lemma reachCard_le (A : Interp D) (x : Fin D) : reachCard A x ≤ D := by
  unfold reachCard
  exact (Finset.card_filter_le _ _).trans (by simp)

open Classical in
lemma reachCard_mono {A : Interp D} {x y : Fin D} (h : Reach (B0 A) (B1 A) x y) :
    reachCard A y ≤ reachCard A x := by
  unfold reachCard
  exact Finset.card_le_card (fun k hk => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact h.trans hk)

open Classical in
lemma reachCard_lt {A : Interp D} {x y : Fin D} (h : Reach (B0 A) (B1 A) x y)
    (hn : ¬ Reach (B0 A) (B1 A) y x) : reachCard A y < reachCard A x := by
  unfold reachCard
  refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => hn ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact h.trans hk
  · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ x, Relation.ReflTransGen.refl⟩)
    simpa using this

end Collatz.Arctic.Upper
