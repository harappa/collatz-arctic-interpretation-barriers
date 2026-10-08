/-
General lemmas on deterministic finite automata (DFA), continued (used in the assembly, proof of Theorem 6.8).
Definitions and the lemmas on periods and classes are in `Dfa.lean`. Independent of Collatz and of arctic interpretations.

* The counting form of (c): `count_words` (for every length `n ≥ L`, at least `2^(n - L)` words of length `n` join a pair
  whose classes differ by `n`; this is (A3) in the proof of Theorem 6.8).
* The aligning word `w*` of (A2) in the proof of Theorem 6.8: `exists_wstar`. The minimal size of the image of a class does not depend on the class (`card_shift`), so
  for each pair (component, class) we append a word that minimizes the image under the current word (`exists_good_all`; appending words keeps
  the minimum: the definition of `Good` and `Finset.card_image_le`). Merely concatenating words chosen in advance can fail, so the word is extended adaptively.
-/
import CollatzProof.Arctic.Dfa

namespace Collatz.Arctic.Dfa

variable {S : Type*} (δ : S → Bool → S) [Fintype S] [DecidableEq S]

/-! ### The counting form of (c) -/

/-- The number of words of length `n` that lead from `q` to `q'`. -/
def wordCount (q q' : S) (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Bool)).filter (fun g => run δ q (List.ofFn g) = q')).card

section Count
variable {δ}

omit [Fintype S] in
/-- Split by the first letter. -/
theorem wordCount_succ (q q' : S) (n : ℕ) :
    wordCount δ q q' (n + 1) = wordCount δ (δ q false) q' n + wordCount δ (δ q true) q' n := by
  simp only [wordCount, Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  simp [Fin.consEquiv_apply]

omit [Fintype S] in
theorem one_le_wordCount {q q' : S} {n : ℕ} {w : List Bool} (hw : w.length = n)
    (hrun : run δ q w = q') : 1 ≤ wordCount δ q q' n := by
  subst hw
  exact Finset.card_pos.mpr ⟨w.get, by simp [List.ofFn_get, hrun]⟩

/-- **Corollary of (c)**: for every length `n ≥ L`, at least `2^(n - L)` words of length `n` join a pair whose classes differ by `n`
(the first `n - L` letters can be chosen freely). -/
theorem count_words {q₀ : S} (hrec : Recurrent δ q₀) :
    ∃ L : ℕ, ∀ n, L ≤ n → ∀ q q', Reach δ q₀ q → Reach δ q₀ q' →
      cls δ q₀ q' = cls δ q₀ q + n →
        2 ^ (n - L) ≤ ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun g => run δ q (List.ofFn g) = q')).card := by
  obtain ⟨L, hL⟩ := uniform_word hrec
  refine ⟨L, fun n hn q q' hq hq' hcls => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + L := ⟨n - L, by omega⟩
  rw [Nat.add_sub_cancel]
  change 2 ^ m ≤ wordCount δ q q' (m + L)
  clear hn
  induction m generalizing q with
  | zero =>
    obtain ⟨w, hw, hrun⟩ := hL (0 + L) (by omega) q q' hq hq' hcls
    simpa using one_le_wordCount hw hrun
  | succ m ih =>
    have key : ∀ b, cls δ q₀ q' = cls δ q₀ (δ q b) + ((m + L : ℕ) : ZMod (period δ q₀)) := by
      intro b
      have := cls_run hrec hq [b]
      rw [run_singleton] at this
      rw [this, hcls, List.length_singleton]
      push_cast
      ring
    rw [show m + 1 + L = (m + L) + 1 by omega, wordCount_succ, pow_succ, mul_two]
    exact Nat.add_le_add (ih _ (hq.trans (reach_run q [false])) (key false))
      (ih _ (hq.trans (reach_run q [true])) (key true))

end Count

/-! ### 3. The word `w*` whose image is minimal for each class (the aligning word of (A2)) -/

open Classical in
/-- The class set: the states of the component `{q | Reach δ q₀ q}` of class `i`. -/
noncomputable def classSet (q₀ : S) (i : ZMod (period δ q₀)) : Finset S :=
  Finset.univ.filter (fun q => Reach δ q₀ q ∧ cls δ q₀ q = i)

/-- The image under the word `w`. -/
def img (w : List Bool) (X : Finset S) : Finset S := X.image (fun q => run δ q w)

/-- `w` minimizes the size of the image of `X`. -/
def Good (X : Finset S) (w : List Bool) : Prop := ∀ u, (img δ w X).card ≤ (img δ u X).card

/-- After every word one can append a word that minimizes the image of `X`. -/
def Extendable (X : Finset S) : Prop := ∀ w, ∃ u, Good δ X (w ++ u)

section Wstar
variable {δ}

omit [Fintype S] in
theorem img_append (v u : List Bool) (X : Finset S) : img δ (v ++ u) X = img δ u (img δ v X) := by
  simp only [img, Finset.image_image]
  congr 1
  funext q
  simp [run_append]

omit [DecidableEq S] in
theorem mem_classSet {q₀ q : S} {i : ZMod (period δ q₀)} :
    q ∈ classSet δ q₀ i ↔ Reach δ q₀ q ∧ cls δ q₀ q = i := by
  simp [classSet]

/-- The image of the class `i` lies in the class `i + |v|`. -/
theorem img_classSet_subset {q₀ : S} (hrec : Recurrent δ q₀) (i : ZMod (period δ q₀))
    (v : List Bool) : img δ v (classSet δ q₀ i) ⊆ classSet δ q₀ (i + v.length) := by
  intro s hs
  simp only [img, Finset.mem_image] at hs
  obtain ⟨q, hq, rfl⟩ := hs
  rw [mem_classSet] at hq ⊢
  exact ⟨hq.1.trans (reach_run q v), by rw [cls_run hrec hq.1, hq.2]⟩

end Wstar

omit [Fintype S] in
theorem exists_good (X : Finset S) : ∃ w, Good δ X w := by
  obtain ⟨w, hw⟩ := Nat.sInf_mem (s := {k | ∃ w, (img δ w X).card = k}) ⟨_, [], rfl⟩
  exact ⟨w, fun u => by rw [hw]; exact Nat.sInf_le ⟨u, rfl⟩⟩

omit [Fintype S] in
/-- For finitely many sets, a word that minimizes the images of all extendable ones simultaneously (extended adaptively). -/
theorem exists_good_all (l : List (Finset S)) :
    ∃ w, ∀ X ∈ l, Extendable δ X → Good δ X w := by
  induction l with
  | nil => exact ⟨[], by simp⟩
  | cons X l ih =>
    obtain ⟨w, hw⟩ := ih
    by_cases hX : Extendable δ X
    · obtain ⟨u, hu⟩ := hX w
      refine ⟨w ++ u, fun Y hY hYe => ?_⟩
      rcases List.mem_cons.mp hY with rfl | hY
      · exact hu
      · intro u'
        calc (img δ (w ++ u) Y).card = (img δ u (img δ w Y)).card := by rw [img_append]
          _ ≤ (img δ w Y).card := Finset.card_image_le
          _ ≤ (img δ u' Y).card := hw Y hY hYe u'
    · refine ⟨w, fun Y hY hYe => ?_⟩
      rcases List.mem_cons.mp hY with rfl | hY
      · exact absurd hYe hX
      · exact hw Y hY hYe

section Wstar2
variable {δ}

theorem exists_natCast_add_eq {n : ℕ} (hn : 0 < n) (i j : ZMod n) : ∃ ℓ : ℕ, j + ℓ = i := by
  have : NeZero n := ⟨hn.ne'⟩
  exact ⟨(i - j).val, by rw [ZMod.natCast_zmod_val]; ring⟩

/-- The minimum for the class `j` is at most the minimum for the class `i` (prepend a word to move the class). -/
theorem card_shift {q₀ : S} (hrec : Recurrent δ q₀) (i j : ZMod (period δ q₀)) (u : List Bool) :
    ∃ v : List Bool,
      (img δ (v ++ u) (classSet δ q₀ j)).card ≤ (img δ u (classSet δ q₀ i)).card := by
  obtain ⟨ℓ, hℓ⟩ := exists_natCast_add_eq (period_pos δ q₀) i j
  refine ⟨List.replicate ℓ false, Finset.card_le_card ?_⟩
  rw [img_append]
  have := img_classSet_subset hrec j (List.replicate ℓ false)
  rw [List.length_replicate, hℓ] at this
  exact Finset.image_subset_image this

theorem extendable_classSet {q₀ : S} (hrec : Recurrent δ q₀) (i : ZMod (period δ q₀)) :
    Extendable δ (classSet δ q₀ i) := by
  intro w
  obtain ⟨u, hu⟩ := exists_good δ (classSet δ q₀ (i + w.length))
  refine ⟨u, fun u'' => ?_⟩
  obtain ⟨v, hv⟩ := card_shift hrec i (i + w.length) u''
  calc (img δ (w ++ u) (classSet δ q₀ i)).card
      ≤ (img δ u (classSet δ q₀ (i + w.length))).card := by
        rw [img_append]
        exact Finset.card_le_card (Finset.image_subset_image (img_classSet_subset hrec i w))
    _ ≤ (img δ (v ++ u'') (classSet δ q₀ (i + w.length))).card := hu _
    _ ≤ (img δ u'' (classSet δ q₀ i)).card := hv

end Wstar2

/-- **`w*`**: simultaneously for all recurrent states `q₀`, classes `i` and words `v`,
`img (v ++ w*) (C_i) = img w* (C_{i+|v|})`. -/
theorem exists_wstar : ∃ wstar : List Bool, ∀ q₀, Recurrent δ q₀ →
    ∀ (i : ZMod (period δ q₀)) (v : List Bool),
      img δ (v ++ wstar) (classSet δ q₀ i) = img δ wstar (classSet δ q₀ (i + v.length)) := by
  obtain ⟨ws, hws⟩ := exists_good_all δ (Finset.univ : Finset (Finset S)).toList
  refine ⟨ws, fun q₀ hrec i v => ?_⟩
  have hgood : Good δ (classSet δ q₀ (i + v.length)) ws :=
    hws _ (Finset.mem_toList.mpr (Finset.mem_univ _)) (extendable_classSet hrec _)
  apply Finset.eq_of_subset_of_card_le
  · rw [img_append]
    exact Finset.image_subset_image (img_classSet_subset hrec i v)
  · obtain ⟨v', hv'⟩ := card_shift hrec i (i + v.length) (v ++ ws)
    exact (hgood _).trans hv'

end Collatz.Arctic.Dfa
