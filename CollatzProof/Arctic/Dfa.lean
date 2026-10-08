/-
General lemmas on deterministic finite automata (DFA), used in the assembly (proof of Theorem 6.8, Section 6.5).
Independent of Collatz and of arctic interpretations (imports only Mathlib).

* `run δ q w`: the state after reading the word `w` from the state `q`. `Reach`: reachability. `Recurrent`: lies in an absorbing component.
* Fact (A1) in the proof of Theorem 6.8: the **absorbing word** `exists_absorbing` (one word that leads from every state into an absorbing component).
  Absorbing components are closed: `Recurrent.after`.
* **Periods and cyclic classes** (for (A3) in the proof of Theorem 6.8). The period `period δ q₀` (the eventual minimal period of the sequence of layers `layer δ q₀ n`, `period_pos`) and
  the class `cls δ q₀ : S → ZMod (period δ q₀)`. (a) `cls_run`, (b) `cls_self`, (c) where uniform words lead:
  `uniform_word` (every length at least `L`), `uniform_word_len` (length exactly `L`), and the counting form `count_words`
  (`Dfa2.lean`).
  (d) Taking another recurrent state of the same component as base gives the same period and the same class differences: `period_eq_of_reach`, `cls_add_iff_of_reach`.
* The aligning word `w*` of (A2) in the proof of Theorem 6.8: `exists_wstar` (`Dfa2.lean`; a word whose image is minimal for each class, simultaneously for all recurrent states and
  all classes).

Design: the period is defined without gcd, as the minimal period of the sequence of sets `layer δ q n` of states reachable by words of length `n` (a sequence of finite sets, hence
eventually periodic by pigeonhole). Lengths of return words are multiples of this period (`period_dvd_ret`),
which determines the classes. `w*` is built by adaptively appending, for each pair (component, class), a word that minimizes the image under the current word
(`exists_good_all`; merely concatenating words chosen in advance can fail).
-/
import Mathlib

namespace Collatz.Arctic.Dfa

variable {S : Type*} (δ : S → Bool → S)

/-! ### Definitions -/

/-- The state after reading a word. -/
def run (q : S) (w : List Bool) : S := w.foldl δ q

/-- Reachability. -/
def Reach (q q' : S) : Prop := ∃ w, run δ q w = q'

/-- Recurrent (lies in an absorbing component): one can always return from every reachable state. -/
def Recurrent (q : S) : Prop := ∀ q', Reach δ q q' → Reach δ q' q

/-- Layer: the set of states reachable from `q` by words of length `n`. -/
def layer (q : S) (n : ℕ) : Set S := {s | ∃ w : List Bool, w.length = n ∧ run δ q w = s}

/-- The sequence of layers has period `p` from `N` on. -/
def IsPer (q : S) (N p : ℕ) : Prop := ∀ n, N ≤ n → layer δ q (n + p) = layer δ q n

/-- **Period**: the eventual minimal period of the sequence of layers (positive by `period_pos`). -/
noncomputable def period (q : S) : ℕ := sInf {p | 0 < p ∧ ∃ N, IsPer δ q N p}

open Classical in
/-- **Cyclic class**: the length of the (chosen) word from `q₀` to `q`, modulo `period δ q₀` (0 outside the component). -/
noncomputable def cls (q₀ q : S) : ZMod (period δ q₀) :=
  if h : Reach δ q₀ q then ((Classical.choose h).length : ZMod (period δ q₀)) else 0

/-! ### Basic lemmas on `run`, reachability and layers -/

section Basic
variable {δ}

@[simp] theorem run_nil (q : S) : run δ q [] = q := rfl

@[simp] theorem run_cons (q : S) (b : Bool) (w : List Bool) :
    run δ q (b :: w) = run δ (δ q b) w := rfl

theorem run_append (q : S) (u v : List Bool) : run δ q (u ++ v) = run δ (run δ q u) v :=
  List.foldl_append

theorem run_singleton (q : S) (b : Bool) : run δ q [b] = δ q b := rfl

theorem Reach.refl (q : S) : Reach δ q q := ⟨[], rfl⟩

theorem reach_run (q : S) (w : List Bool) : Reach δ q (run δ q w) := ⟨w, rfl⟩

theorem Reach.trans {a b c : S} (h₁ : Reach δ a b) (h₂ : Reach δ b c) : Reach δ a c := by
  obtain ⟨u, rfl⟩ := h₁
  obtain ⟨v, rfl⟩ := h₂
  exact ⟨u ++ v, run_append _ _ _⟩

/-- Absorbing components are closed: once entered, never left. -/
theorem Recurrent.after {q : S} (h : Recurrent δ q) (w : List Bool) : Recurrent δ (run δ q w) := by
  intro q' hq'
  exact (h q' ((reach_run q w).trans hq')).trans (reach_run q w)

/-- States reachable from a recurrent state are recurrent. -/
theorem Recurrent.of_reach {q q' : S} (h : Recurrent δ q) (hq : Reach δ q q') : Recurrent δ q' := by
  obtain ⟨w, rfl⟩ := hq
  exact h.after w

theorem mem_layer_add (q s : S) (m n : ℕ) :
    s ∈ layer δ q (m + n) ↔ ∃ t ∈ layer δ q m, s ∈ layer δ t n := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨run δ q (w.take m), ⟨w.take m, ?_, rfl⟩, w.drop m, ?_, ?_⟩
    · rw [List.length_take, hw]; omega
    · rw [List.length_drop, hw]; omega
    · rw [← run_append, List.take_append_drop]
  · rintro ⟨t, ⟨u, hu, rfl⟩, v, hv, rfl⟩
    exact ⟨u ++ v, by rw [List.length_append, hu, hv], run_append _ _ _⟩

theorem layer_shift (q : S) {i j : ℕ} (h : layer δ q i = layer δ q j) (t : ℕ) :
    layer δ q (i + t) = layer δ q (j + t) := by
  ext s
  rw [mem_layer_add, mem_layer_add, h]

theorem IsPer.iter {q : S} {N p : ℕ} (h : IsPer δ q N p) {n : ℕ} (hn : N ≤ n) (j : ℕ) :
    layer δ q (n + p * j) = layer δ q n := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, ← Nat.add_assoc, h _ (by omega), ih]

theorem IsPer.layer_eq {q : S} {N p : ℕ} (h : IsPer δ q N p) {m n : ℕ} (hm : N ≤ m) (hn : N ≤ n)
    (hmn : m % p = n % p) : layer δ q m = layer δ q n := by
  have e : m + p * (n / p) = n + p * (m / p) := by
    have h1 := Nat.mod_add_div m p
    have h2 := Nat.mod_add_div n p
    omega
  rw [← h.iter hm (n / p), e, h.iter hn]

/-- Shifting by multiples of the length of a return word enlarges the layer. -/
theorem layer_subset_ret {q : S} {u : List Bool} (hu : run δ q u = q) (n j : ℕ) :
    layer δ q n ⊆ layer δ q (n + u.length * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    refine ih.trans ?_
    rintro s ⟨w, hw, rfl⟩
    refine ⟨u ++ w, ?_, ?_⟩
    · rw [List.length_append, hw, Nat.mul_succ]; ring
    · rw [run_append, hu]

/-- The length of a return word is also a period (from the same `N` on). -/
theorem IsPer.of_ret {q : S} {N p : ℕ} (hp : 0 < p) (h : IsPer δ q N p) {u : List Bool}
    (hu : run δ q u = q) : IsPer δ q N u.length := by
  intro n hn
  apply Set.Subset.antisymm
  · have h1 := layer_subset_ret hu (n + u.length) (p - 1)
    have h2 : n + u.length + u.length * (p - 1) = n + p * u.length := by
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [Nat.add_sub_cancel]; ring
    rw [h2, h.iter hn] at h1
    exact h1
  · simpa using layer_subset_ret hu n 1

theorem natCast_period_eq_zero {q : S} {k : ℕ} (h : period δ q ∣ k) :
    (k : ZMod (period δ q)) = 0 :=
  (CharP.cast_eq_zero_iff (ZMod (period δ q)) (period δ q) k).mpr h

end Basic

variable [Fintype S]

/-! ### 1. The absorbing word ((A1) in the proof of Theorem 6.8) -/

/-- From every state some word leads into a recurrent state (induction on the size of the reachable set). -/
theorem exists_run_recurrent (q : S) : ∃ w, Recurrent δ (run δ q w) := by
  classical
  -- the set of reachable states
  let A : S → Finset S := fun q => Finset.univ.filter (fun s => Reach δ q s)
  suffices h : ∀ n, ∀ q, (A q).card = n → ∃ w, Recurrent δ (run δ q w) from h _ q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q hn
    by_cases hq : Recurrent δ q
    · exact ⟨[], hq⟩
    · simp only [Recurrent, not_forall] at hq
      obtain ⟨q', hqq', hback⟩ := hq
      have hsub : A q' ⊂ A q := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨q, by simp [A, Reach.refl], by simpa [A] using hback⟩
        · intro s hs
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          exact hqq'.trans hs
      obtain ⟨w', hw'⟩ := ih _ (hn ▸ Finset.card_lt_card hsub) q' rfl
      obtain ⟨u, rfl⟩ := hqq'
      exact ⟨u ++ w', by rw [run_append]; exact hw'⟩

/-- **Absorbing word**: one word that leads from every state into an absorbing component (absorb the states one by one and concatenate). -/
theorem exists_absorbing : ∃ w₀ : List Bool, ∀ q, Recurrent δ (run δ q w₀) := by
  suffices h : ∀ l : List S, ∃ w : List Bool, ∀ q ∈ l, Recurrent δ (run δ q w) by
    obtain ⟨w, hw⟩ := h Finset.univ.toList
    exact ⟨w, fun q => hw q (Finset.mem_toList.mpr (Finset.mem_univ q))⟩
  intro l
  induction l with
  | nil => exact ⟨[], by simp⟩
  | cons a l ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨u, hu⟩ := exists_run_recurrent δ (run δ a w)
    refine ⟨w ++ u, fun q hq => ?_⟩
    rw [run_append]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hu
    · exact (hw q hq).after u

/-! ### 2. Periods -/

/-- The sequence of layers is eventually periodic (pigeonhole). -/
theorem exists_per (q : S) : ∃ p, 0 < p ∧ ∃ N, IsPer δ q N p := by
  obtain ⟨x, y, hne, hxy⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => layer δ q n)
  wlog hlt : x < y generalizing x y
  · exact this y x hne.symm hxy.symm (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
  refine ⟨y - x, by omega, x, fun n hn => ?_⟩
  have := layer_shift q hxy (n - x)
  rw [show x + (n - x) = n by omega, show y + (n - x) = n + (y - x) by omega] at this
  exact this.symm

theorem period_spec (q : S) : 0 < period δ q ∧ ∃ N, IsPer δ q N (period δ q) :=
  Nat.sInf_mem (exists_per δ q)

theorem period_pos (q : S) : 0 < period δ q := (period_spec δ q).1

section Period
variable {δ}

theorem period_dvd_of_isPer {q : S} {N k : ℕ} (hN : IsPer δ q N (period δ q))
    (hk : IsPer δ q N k) : period δ q ∣ k := by
  have hpos : 0 < period δ q := period_pos δ q
  -- `k % period` is also a period
  have hmod : IsPer δ q N (k % period δ q) := by
    intro n hn
    have e : n + k % period δ q + period δ q * (k / period δ q) = n + k := by
      rw [Nat.add_assoc, Nat.mod_add_div]
    rw [← hN.iter (show N ≤ n + k % period δ q by omega) (k / period δ q), e, hk n hn]
  by_contra hndvd
  have hpos' : 0 < k % period δ q :=
    Nat.pos_of_ne_zero (fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0))
  have hle : period δ q ≤ k % period δ q := Nat.sInf_le ⟨hpos', N, hmod⟩
  exact absurd (Nat.mod_lt k hpos) (not_lt.mpr hle)

/-- **The length of a return word is a multiple of the period.** -/
theorem period_dvd_ret {q : S} {u : List Bool} (hu : run δ q u = q) : period δ q ∣ u.length := by
  obtain ⟨hpos, N, hN⟩ := period_spec δ q
  exact period_dvd_of_isPer hN (hN.of_ret hpos hu)

/-! ### Cyclic classes -/

/-- For recurrent `q₀`, the length of every word from `q₀` to `s` equals `cls δ q₀ s` modulo `period δ q₀`. -/
theorem cls_eq {q₀ : S} (hrec : Recurrent δ q₀) {w : List Bool} {s : S} (hw : run δ q₀ w = s) :
    cls δ q₀ s = w.length := by
  have hs : Reach δ q₀ s := ⟨w, hw⟩
  rw [cls, dite_eq_left hs]
  have h1 := Classical.choose_spec hs
  obtain ⟨c, hc⟩ := hrec s hs
  have e1 := natCast_period_eq_zero (period_dvd_ret (δ := δ) (q := q₀)
    (u := Classical.choose hs ++ c) (by rw [run_append, h1, hc]))
  have e2 := natCast_period_eq_zero (period_dvd_ret (δ := δ) (q := q₀) (u := w ++ c)
    (by rw [run_append, hw, hc]))
  simp only [List.length_append, Nat.cast_add] at e1 e2
  exact add_right_cancel (e1.trans e2.symm)

/-- **(a)** Inside the component, reading a word advances the class by the length of the word. -/
theorem cls_run {q₀ q : S} (hrec : Recurrent δ q₀) (hq : Reach δ q₀ q) (w : List Bool) :
    cls δ q₀ (run δ q w) = cls δ q₀ q + w.length := by
  obtain ⟨w₁, rfl⟩ := hq
  rw [← run_append, cls_eq hrec (w := w₁ ++ w) rfl, cls_eq hrec (w := w₁) rfl,
    List.length_append, Nat.cast_add]

/-- **(b)** The base state has class 0. -/
theorem cls_self {q₀ : S} (hrec : Recurrent δ q₀) : cls δ q₀ q₀ = 0 := by
  simpa using cls_eq hrec (w := []) (s := q₀) rfl

/-- Beyond the threshold of periodicity the layer is determined by the class: a state of class `n` is reachable from `q₀` by a word of length `n`. -/
theorem mem_layer_of_cls {q₀ : S} (hrec : Recurrent δ q₀) {N : ℕ}
    (hN : IsPer δ q₀ N (period δ q₀)) {n : ℕ} (hn : N ≤ n) {s : S} (hs : Reach δ q₀ s)
    (hcls : cls δ q₀ s = n) : s ∈ layer δ q₀ n := by
  obtain ⟨w₁, rfl⟩ := hs
  -- a return word `false :: c` of length at least 1
  obtain ⟨c, hc⟩ := hrec (δ q₀ false) ⟨[false], rfl⟩
  have hu : run δ q₀ (false :: c) = q₀ := hc
  have hk : 0 < (false :: c).length := by simp
  have hmem := layer_subset_ret hu w₁.length N ⟨w₁, rfl, rfl⟩
  have hge : N ≤ w₁.length + (false :: c).length * N :=
    (Nat.le_mul_of_pos_left N hk).trans (Nat.le_add_left _ _)
  rw [hN.layer_eq hge hn ?_] at hmem
  · exact hmem
  · rw [cls_eq hrec rfl] at hcls
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_add, Nat.cast_mul,
      natCast_period_eq_zero (period_dvd_ret hu), zero_mul, add_zero]
    exact hcls

/-- **(c)** Where uniform words lead: there is `L` such that for every length `n ≥ L`, any two states of the component whose classes differ by `n`
are joined by a word of length `n`. -/
theorem uniform_word {q₀ : S} (hrec : Recurrent δ q₀) :
    ∃ L : ℕ, ∀ n, L ≤ n → ∀ q q', Reach δ q₀ q → Reach δ q₀ q' →
      cls δ q₀ q' = cls δ q₀ q + n → ∃ w : List Bool, w.length = n ∧ run δ q w = q' := by
  classical
  obtain ⟨-, N, hN⟩ := period_spec δ q₀
  -- the length of a word from each state back to `q₀`
  let c : S → ℕ := fun q => if h : Reach δ q q₀ then (Classical.choose h).length else 0
  refine ⟨N + Finset.univ.sup c, fun n hn q q' hq hq' hcls => ?_⟩
  have hq0 : Reach δ q q₀ := hrec q hq
  have hu : run δ q (Classical.choose hq0) = q₀ := Classical.choose_spec hq0
  have hle : (Classical.choose hq0).length ≤ Finset.univ.sup c := by
    have : c q = (Classical.choose hq0).length := by simp only [c, dite_eq_left hq0]
    rw [← this]
    exact Finset.le_sup (Finset.mem_univ q)
  have h0 : cls δ q₀ q + (Classical.choose hq0).length = 0 := by
    rw [← cls_run hrec hq, hu, cls_self hrec]
  have hcls' : cls δ q₀ q' = ((n - (Classical.choose hq0).length : ℕ) : ZMod (period δ q₀)) := by
    rw [hcls, Nat.cast_sub (by omega)]
    linear_combination h0
  obtain ⟨w₂, hw₂, hrun⟩ := mem_layer_of_cls hrec hN (by omega) hq' hcls'
  exact ⟨Classical.choose hq0 ++ w₂, by rw [List.length_append, hw₂]; omega,
    by rw [run_append, hu, hrun]⟩

/-- **(c)** The form with length exactly `L` (the combinatorial form). -/
theorem uniform_word_len {q₀ : S} (hrec : Recurrent δ q₀) :
    ∃ L : ℕ, ∀ q q', Reach δ q₀ q → Reach δ q₀ q' → cls δ q₀ q' = cls δ q₀ q + L →
      ∃ w : List Bool, w.length = L ∧ run δ q w = q' := by
  obtain ⟨L, hL⟩ := uniform_word hrec
  exact ⟨L, hL L le_rfl⟩

/-- Class differences restated: inside the component, `cls q' = cls q + n` holds iff some word from `q` to `q'` has length congruent to `n`
modulo `period`. -/
theorem cls_add_iff {q₀ q q' : S} (hrec : Recurrent δ q₀) (hq : Reach δ q₀ q)
    (hq' : Reach δ q₀ q') (n : ℕ) :
    cls δ q₀ q' = cls δ q₀ q + n ↔
      ∃ w : List Bool, run δ q w = q' ∧ w.length % period δ q₀ = n % period δ q₀ := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := (hrec q hq).trans hq'
    refine ⟨w, hw, (ZMod.natCast_eq_natCast_iff' _ _ _).mp ?_⟩
    rw [← hw, cls_run hrec hq] at h
    exact add_left_cancel h
  · rintro ⟨w, rfl, hmod⟩
    rw [cls_run hrec hq, (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod]

/-- The period of a state `q₁` of the component divides `period δ q₀`. -/
theorem period_dvd_of_reach {q₀ q₁ : S} (hrec : Recurrent δ q₀) (h : Reach δ q₀ q₁) :
    period δ q₁ ∣ period δ q₀ := by
  obtain ⟨L, hL⟩ := uniform_word hrec
  obtain ⟨b, hb⟩ := h
  obtain ⟨c, hc⟩ := hrec q₁ ⟨b, hb⟩
  -- from a return word at `q₀` of length `n` (a multiple of `period δ q₀`, at least `L`), build a return word at `q₁`
  have ret : ∀ n, L ≤ n → period δ q₀ ∣ n → period δ q₁ ∣ c.length + n + b.length := by
    intro n hn hpn
    obtain ⟨u, hu, hru⟩ := hL n hn q₀ q₀ (Reach.refl _) (Reach.refl _)
      (by rw [natCast_period_eq_zero hpn, add_zero])
    have := period_dvd_ret (δ := δ) (q := q₁) (u := c ++ u ++ b)
      (by rw [run_append, run_append, hc, hru, hb])
    simpa [hu, Nat.add_assoc] using this
  have hpos := period_pos δ q₀
  have hL1 : L ≤ period δ q₀ * (L + 1) := (Nat.le_succ L).trans (Nat.le_mul_of_pos_left _ hpos)
  have h1 := ret _ hL1 (dvd_mul_right _ _)
  have h2 := ret (period δ q₀ * (L + 1) + period δ q₀) (by omega)
    (dvd_add (dvd_mul_right _ _) dvd_rfl)
  have := Nat.dvd_sub h2 h1
  rwa [show c.length + (period δ q₀ * (L + 1) + period δ q₀) + b.length
      - (c.length + period δ q₀ * (L + 1) + b.length) = period δ q₀ by omega] at this

/-- **(d)** Taking a state of the same component as base gives the same period. -/
theorem period_eq_of_reach {q₀ q₁ : S} (hrec : Recurrent δ q₀) (h : Reach δ q₀ q₁) :
    period δ q₁ = period δ q₀ :=
  Nat.dvd_antisymm (period_dvd_of_reach hrec h)
    (period_dvd_of_reach (hrec.of_reach h) (hrec q₁ h))

omit [Fintype S] in
/-- Taking a state of the same component as base gives the same component. -/
theorem reach_iff_of_reach {q₀ q₁ : S} (hrec : Recurrent δ q₀) (h : Reach δ q₀ q₁) (q : S) :
    Reach δ q₁ q ↔ Reach δ q₀ q :=
  ⟨fun hq => h.trans hq, fun hq => (hrec q₁ h).trans hq⟩

/-- **(d)** Taking a state of the same component as base gives the same class differences (classes are unique up to a constant shift). -/
theorem cls_add_iff_of_reach {q₀ q₁ q q' : S} (hrec : Recurrent δ q₀) (h : Reach δ q₀ q₁)
    (hq : Reach δ q₀ q) (hq' : Reach δ q₀ q') (n : ℕ) :
    cls δ q₀ q' = cls δ q₀ q + n ↔ cls δ q₁ q' = cls δ q₁ q + n := by
  have h₁₀ := hrec q₁ h
  rw [cls_add_iff hrec hq hq', cls_add_iff (hrec.of_reach h) (h₁₀.trans hq) (h₁₀.trans hq'),
    period_eq_of_reach hrec h]

end Period

end Collatz.Arctic.Dfa
