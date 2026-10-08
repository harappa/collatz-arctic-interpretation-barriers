/-
The partition of Lemma 6.5 of the paper built from a sequence of cut points (assembly of Theorem 6.8).
From cut points `c a ≤ c (a+1) ≤ ⋯ ≤ c (a+r)` and exceptional marks `e i` we build the list of intervals `cutSegs c e a r`,
and restate the five conditions of `Upper.GoodPartition` as conditions on the cut points (`goodPartition_of_cuts`).
-/
import CollatzProof.Arctic.Upper

namespace Collatz.Arctic

open Upper

/-- The list of intervals with cut points `c a, c (a+1), …, c (a+r)`. -/
def cutSegs (c : ℕ → ℕ) (e : ℕ → Bool) : ℕ → ℕ → List Seg
  | _, 0 => []
  | a, r + 1 => ⟨c a, c (a + 1), e a⟩ :: cutSegs c e (a + 1) r

theorem cutSegs_length (c : ℕ → ℕ) (e : ℕ → Bool) : ∀ a r, (cutSegs c e a r).length = r
  | _, 0 => rfl
  | a, r + 1 => by simp [cutSegs, cutSegs_length c e (a + 1) r]

theorem mem_cutSegs (c : ℕ → ℕ) (e : ℕ → Bool) :
    ∀ a r (s : Seg), s ∈ cutSegs c e a r → ∃ i, a ≤ i ∧ i < a + r ∧ s = ⟨c i, c (i + 1), e i⟩
  | _, 0, s, h => by simp [cutSegs] at h
  | a, r + 1, s, h => by
    simp only [cutSegs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, le_rfl, by omega, rfl⟩
    · obtain ⟨i, h1, h2, rfl⟩ := mem_cutSegs c e (a + 1) r s h
      exact ⟨i, by omega, by omega, rfl⟩

theorem cutSegs_chain (c : ℕ → ℕ) (e : ℕ → Bool) :
    ∀ a r, (∀ i, a ≤ i → i < a + r → c i ≤ c (i + 1)) → SegChain (cutSegs c e a r) (c a) (c (a + r))
  | a, 0, _ => by simp [cutSegs, SegChain]
  | a, r + 1, h => by
    refine ⟨rfl, h a le_rfl (by omega), ?_⟩
    have := cutSegs_chain c e (a + 1) r (fun i h1 h2 => h i (by omega) (by omega))
    rwa [show a + 1 + r = a + (r + 1) by omega] at this

theorem cutSegs_excLen (c : ℕ → ℕ) (e : ℕ → Bool) :
    ∀ a r, excLen (cutSegs c e a r) = ∑ i ∈ Finset.range r, (if e (a + i) then c (a + i + 1) - c (a + i) else 0)
  | _, 0 => by simp [cutSegs, excLen]
  | a, r + 1 => by
    rw [Finset.sum_range_succ', cutSegs, excLen, cutSegs_excLen c e (a + 1) r]
    simp only [add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show a + (i + 1) = a + 1 + i by omega]

/-- **Restatement of the conditions on the partition.** -/
theorem goodPartition_of_cuts (w : Word) (ε : ℝ) (J : ℕ) (δ : ℚ) (r : ℕ) (c : ℕ → ℕ) (e : ℕ → Bool)
    (hmono : ∀ i < r, c i ≤ c (i + 1)) (h0 : c 0 = 0) (hr : c r = w.length)
    (hwidth : ∀ i < r, (c (i + 1) : ℝ) ≤ c i + ε * w.length)
    (hcount : (r : ℝ) ≤ ε⁻¹ ^ 2)
    (hexc : ((∑ i ∈ Finset.range r, (if e i then c (i + 1) - c i else 0) : ℕ) : ℝ) ≤ ε * w.length)
    (hwin : ∀ i < r, e i = false → WinClose w (c i) (c (i + 1)) J δ) :
    GoodPartition w (cutSegs c e 0 r) ε J δ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := cutSegs_chain c e 0 r (fun i _ h2 => hmono i (by omega))
    rwa [h0, zero_add, hr] at this
  · intro s hs
    obtain ⟨i, -, hi, rfl⟩ := mem_cutSegs c e 0 r s hs
    exact hwidth i (by omega)
  · rw [cutSegs_length]; exact hcount
  · rw [cutSegs_excLen]
    simpa using hexc
  · intro s hs hexc'
    obtain ⟨i, -, hi, rfl⟩ := mem_cutSegs c e 0 r s hs
    exact hwin i (by omega) hexc'

end Collatz.Arctic
